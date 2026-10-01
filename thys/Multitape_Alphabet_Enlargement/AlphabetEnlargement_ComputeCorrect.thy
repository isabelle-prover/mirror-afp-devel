theory AlphabetEnlargement_ComputeCorrect
  imports AlphabetEnlargement_ValidationBound
begin

text \<open>Entry point of the \<open>alphabet_enlarge\<close>
  forward-simulation chain (the combinator is defined in
  \<open>AlphabetEnlargement_Simulation\<close>).  The chain establishes
  that \<open>M' = alphabet_enlarge M\<close> simulates \<open>M\<close>, and
  culminates in the three top-level theorems characterising the
  combinator — well-formedness preservation
  (\<open>alphabet_enlarge_wf\<close>), forward language preservation
  modulo input encoding
  (\<open>alphabet_enlarge_language_forward\<close>), and the linear
  time bound (\<open>alphabet_enlarge_time\<close>) — which are proved
  in theory \<open>AlphabetEnlargement\<close> at the end of the chain.
  The construction follows the linear-speedup theorem of
  Hartmanis and Stearns
  \<^cite>\<open>\<open>Theorem 2\<close> in "Hartmanis1965:computational"\<close>,
  modernised in Hopcroft and Ullman
  \<^cite>\<open>\<open>Theorem 12.3\<close> in "Hopcroft1979:introduction"\<close>.

  The forward chain is split across theories in dependency
  order, each importing the previous:
  \<^item> \<open>AlphabetEnlargement_ComputeCorrect\<close> (this theory):
    per-substep state shape and invariant preservation, the
    \<open>mttm_step\<close> lift, and buffered c-fold compute
    correctness.
  \<^item> \<open>AlphabetEnlargement_SS4\<close>: SS4 trace-existence and
    the buffer characterisations at SS4 entry.
  \<^item> \<open>AlphabetEnlargement_OutputWF\<close>: home classification
    and output well-formedness.
  \<^item> \<open>AlphabetEnlargement_ForwardStage\<close>: the per-tape
    unified forward stage
    \<open>ae_simulates_forward_stage_general\<close>.
  \<^item> \<open>AlphabetEnlargement_Acceptance\<close>: acceptance
    correspondence and the step-count / chunked simulation
    engine.
  \<^item> \<open>AlphabetEnlargement\<close>: the three top-level
    theorems.\<close>

subsection \<open>Forward simulation chain\<close>

subsubsection \<open>Per-substep state shape and invariant preservation\<close>

text \<open>Per-substep mid-stage invariant preservation lemmas.
  Eight in total, one per simulation substep transition
  SS\<open>n\<close>\<open>\<rightarrow>\<close>SS\<open>n+1\<close> (with SS9 \<open>\<equiv>\<close> SS1 by
  wrap-around).\<close>

text \<open>Common skeleton: each per-substep delta is a set of
  tuples whose post-state component fixes \<open>idx\<close> at the target
  substep and constrains \<open>q\<close> via \<open>q \<in> Q_tm M\<close>.
  This helper packages the \<open>mttm_step\<close>-elimination plus the
  set-comprehension destructuring once, reducing each per-substep
  proof to a one-line shape obligation discharged by \<open>auto\<close> on
  the relevant \<open>ae_delta_ss<N>_ss<N+1>_def\<close>.

  The helper does not apply to \<open>ae_step_ss8_ss1_invariant\<close>:
  that substep's halting branch lands at \<open>idx = VFwd\<close>, not
  \<open>idx = SS1\<close>, so the post-state's \<open>idx\<close> is not uniformly
  fixed.\<close>

lemma ae_substep_state_shape:
  fixes M :: "('q, 'a) mttm"
    and \<delta> :: "(('q \<times> ('a, 'c :: enum) ae_stage)
              \<times> (nat \<Rightarrow> ('c \<Rightarrow> 'a))
              \<times> ('q \<times> ('a, 'c) ae_stage)
              \<times> (nat \<Rightarrow> ('c \<Rightarrow> 'a))
              \<times> (nat \<Rightarrow> dir)) set"
    and c' c'' :: "('c :: enum \<Rightarrow> 'a,
                    'q \<times> ('a, 'c) ae_stage) mt_config"
    and tgt :: substep_idx
  assumes step: "(c', c'') \<in> mttm_step \<delta>"
      and shape: "\<And>s a s' a' d.
                    (s, a, s', a', d) \<in> \<delta>
                      \<Longrightarrow> \<exists>q ofs buf dest.
                            s' = (q, ofs, buf, dest, tgt)
                            \<and> q \<in> Q_tm M"
  shows "case mt_state c'' of (qM', _, _, _, idx) \<Rightarrow>
            idx = tgt \<and> qM' \<in> Q_tm M"
proof -
  from step obtain s ts n s' a' d where
      c''_eq: "c'' = Config\<^sub>M s' (\<lambda>k. (ts k)(n k := a' k))
                                (\<lambda>k. go_dir (d k) (n k))"
      and rel: "(s, (\<lambda>k. ts k (n k)), s', a', d) \<in> \<delta>"
    by (auto elim: mttm_step.cases)
  from shape[OF rel] obtain q ofs buf dest where
      s'_eq: "s' = (q, ofs, buf, dest, tgt)"
      and q_in: "q \<in> Q_tm M"
    by blast
  show ?thesis using c''_eq s'_eq q_in by simp
qed

lemma ae_step_ss1_ss2_invariant:
  fixes M :: "('q, 'a) mttm"
    and c' c'' :: "('c :: enum \<Rightarrow> 'a,
                    'q \<times> ('a, 'c) ae_stage) mt_config"
  assumes "valid_mttm M"
      and "ae_inv_ss1 M c'"
      and "(c', c'') \<in> mttm_step (ae_delta_ss1_ss2 M)"
    shows "ae_inv_ss2 M c''"
proof -
  have shape: "\<And>s a s' a' d.
                  (s, a, s', a', d) \<in> ae_delta_ss1_ss2 M
                    \<Longrightarrow> \<exists>q ofs buf dest.
                          s' = (q, ofs, buf, dest, SS2)
                          \<and> q \<in> Q_tm M"
    by (force simp: ae_delta_ss1_ss2_def)
  show "ae_inv_ss2 M c''"
    unfolding ae_inv_ss2_def
    using ae_substep_state_shape[OF assms(3) shape] .
qed

lemma ae_step_ss2_ss3_invariant:
  fixes M :: "('q, 'a) mttm"
    and c' c'' :: "('c :: enum \<Rightarrow> 'a,
                    'q \<times> ('a, 'c) ae_stage) mt_config"
  assumes "valid_mttm M"
      and "ae_inv_ss2 M c'"
      and "(c', c'') \<in> mttm_step (ae_delta_ss2_ss3 M)"
    shows "ae_inv_ss3 M c''"
proof -
  have shape: "\<And>s a s' a' d.
                  (s, a, s', a', d) \<in> ae_delta_ss2_ss3 M
                    \<Longrightarrow> \<exists>q ofs buf dest.
                          s' = (q, ofs, buf, dest, SS3)
                          \<and> q \<in> Q_tm M"
    by (force simp: ae_delta_ss2_ss3_def)
  show "ae_inv_ss3 M c''"
    unfolding ae_inv_ss3_def
    using ae_substep_state_shape[OF assms(3) shape] .
qed

lemma ae_step_ss3_ss4_invariant:
  fixes M :: "('q, 'a) mttm"
    and c' c'' :: "('c :: enum \<Rightarrow> 'a,
                    'q \<times> ('a, 'c) ae_stage) mt_config"
  assumes "valid_mttm M"
      and "ae_inv_ss3 M c'"
      and "(c', c'') \<in> mttm_step (ae_delta_ss3_ss4 M)"
    shows "ae_inv_ss4 M c''"
proof -
  have shape: "\<And>s a s' a' d.
                  (s, a, s', a', d) \<in> ae_delta_ss3_ss4 M
                    \<Longrightarrow> \<exists>q ofs buf dest.
                          s' = (q, ofs, buf, dest, SS4)
                          \<and> q \<in> Q_tm M"
    by (force simp: ae_delta_ss3_ss4_def)
  show "ae_inv_ss4 M c''"
    unfolding ae_inv_ss4_def
    using ae_substep_state_shape[OF assms(3) shape] .
qed

lemma ae_step_ss4_ss5_invariant:
  fixes M :: "('q, 'a) mttm"
    and c' c'' :: "('c :: enum \<Rightarrow> 'a,
                    'q \<times> ('a, 'c) ae_stage) mt_config"
  assumes valM: "valid_mttm M"
      and "ae_inv_ss4 M c'"
      and step: "(c', c'') \<in> mttm_step (ae_delta_ss4_ss5 M)"
    shows "ae_inv_ss5 M c''"
proof -
  \<comment> \<open>Unlike the template substeps, ss4 \<open>\<rightarrow>\<close>
      ss5 advances the \<open>q\<close>-component via
      \<open>m_steps_buffered\<close>; \<open>Q_tm\<close>-membership is preserved
      through the chain by
      \<open>m_steps_buffered_state_preservation\<close>.  The
      \<open>ae_substep_state_shape\<close> helper does not apply directly
      because its uniform shape obligation can't pull in
      \<open>valM\<close> at the right scope; we instead inline the
      \<open>mttm_step\<close>-elimination.\<close>
  from step obtain s ts n s' a' d where
      c''_eq: "c'' = Config\<^sub>M s' (\<lambda>k. (ts k)(n k := a' k))
                                (\<lambda>k. go_dir (d k) (n k))"
      and rel: "(s, (\<lambda>k. ts k (n k)), s', a', d) \<in> ae_delta_ss4_ss5 M"
    by (auto elim: mttm_step.cases)
  from rel[unfolded ae_delta_ss4_ss5_def mem_Collect_eq]
  obtain q ofs buf dest_old q' ofs' buf' dest'
         buf_full end_pos bufC
    where s_eq: "s = (q, ofs, buf, dest_old, SS4)"
      and s'_eq: "s' = (q', ofs', buf', dest', SS5)"
      and q_Q: "q \<in> Q_tm M"
      and m_steps: "((q, buf_full, \<lambda>k. (AE_Home, ofs k)),
                      (q', bufC, end_pos))
                        \<in> m_steps_buffered M"
    by auto
  from m_steps_buffered_state_preservation[OF valM m_steps q_Q]
  have q'_in_Q: "q' \<in> Q_tm M" .
  show "ae_inv_ss5 M c''"
    unfolding ae_inv_ss5_def using c''_eq s'_eq q'_in_Q by simp
qed

lemma ae_step_ss5_ss6_invariant:
  fixes M :: "('q, 'a) mttm"
    and c' c'' :: "('c :: enum \<Rightarrow> 'a,
                    'q \<times> ('a, 'c) ae_stage) mt_config"
  assumes "valid_mttm M"
      and "ae_inv_ss5 M c'"
      and "(c', c'') \<in> mttm_step (ae_delta_ss5_ss6 M)"
    shows "ae_inv_ss6 M c''"
proof -
  have shape: "\<And>s a s' a' d.
                  (s, a, s', a', d) \<in> ae_delta_ss5_ss6 M
                    \<Longrightarrow> \<exists>q ofs buf dest.
                          s' = (q, ofs, buf, dest, SS6)
                          \<and> q \<in> Q_tm M"
    by (force simp: ae_delta_ss5_ss6_def)
  show "ae_inv_ss6 M c''"
    unfolding ae_inv_ss6_def
    using ae_substep_state_shape[OF assms(3) shape] .
qed

lemma ae_step_ss6_ss7_invariant:
  fixes M :: "('q, 'a) mttm"
    and c' c'' :: "('c :: enum \<Rightarrow> 'a,
                    'q \<times> ('a, 'c) ae_stage) mt_config"
  assumes "valid_mttm M"
      and "ae_inv_ss6 M c'"
      and "(c', c'') \<in> mttm_step (ae_delta_ss6_ss7 M)"
    shows "ae_inv_ss7 M c''"
proof -
  have shape: "\<And>s a s' a' d.
                  (s, a, s', a', d) \<in> ae_delta_ss6_ss7 M
                    \<Longrightarrow> \<exists>q ofs buf dest.
                          s' = (q, ofs, buf, dest, SS7)
                          \<and> q \<in> Q_tm M"
    by (force simp: ae_delta_ss6_ss7_def)
  show "ae_inv_ss7 M c''"
    unfolding ae_inv_ss7_def
    using ae_substep_state_shape[OF assms(3) shape] .
qed

lemma ae_step_ss7_ss8_invariant:
  fixes M :: "('q, 'a) mttm"
    and c' c'' :: "('c :: enum \<Rightarrow> 'a,
                    'q \<times> ('a, 'c) ae_stage) mt_config"
  assumes "valid_mttm M"
      and "ae_inv_ss7 M c'"
      and "(c', c'') \<in> mttm_step (ae_delta_ss7_ss8 M)"
    shows "ae_inv_ss8 M c''"
proof -
  have shape: "\<And>s a s' a' d.
                  (s, a, s', a', d) \<in> ae_delta_ss7_ss8 M
                    \<Longrightarrow> \<exists>q ofs buf dest.
                          s' = (q, ofs, buf, dest, SS8)
                          \<and> q \<in> Q_tm M"
    by (force simp: ae_delta_ss7_ss8_def)
  show "ae_inv_ss8 M c''"
    unfolding ae_inv_ss8_def
    using ae_substep_state_shape[OF assms(3) shape] .
qed

lemma ae_step_ss8_ss1_invariant:
  fixes M :: "('q, 'a) mttm"
    and c' c'' :: "('c :: enum \<Rightarrow> 'a,
                    'q \<times> ('a, 'c) ae_stage) mt_config"
  assumes "valid_mttm M"
      and "ae_inv_ss8 M c'"
      and non_halt: "case mt_state c' of (qM', _, _, _, _) \<Rightarrow>
                        qM' \<noteq> t_tm M \<and> qM' \<noteq> r_tm M"
      and step: "(c', c'') \<in> mttm_step (ae_delta_ss8_ss1 M)"
    shows "ae_inv_ss1 M c''"
proof -
  \<comment> \<open>The cycle-closure substep has a halting branch
      (\<open>q \<in> {t_tm M, r_tm M}\<close>) that lands at \<open>idx = VFwd\<close>,
      not \<open>idx = SS1\<close>; the \<open>non_halt\<close> assumption forces
      the steady-state branch.\<close>
  from step obtain s ts n s' a' d where
      c'_eq: "c' = Config\<^sub>M s ts n"
      and c''_eq: "c'' = Config\<^sub>M s' (\<lambda>k. (ts k)(n k := a' k))
                                    (\<lambda>k. go_dir (d k) (n k))"
      and rel: "(s, (\<lambda>k. ts k (n k)), s', a', d) \<in> ae_delta_ss8_ss1 M"
    by (auto elim: mttm_step.cases)
  from rel obtain q ofs buf dest stage' where
      s_eq: "s = (q, ofs, buf, dest, SS8)"
      and s'_eq: "s' = (q, stage')"
      and q_in: "q \<in> Q_tm M"
      and stage'_eq: "stage' = (if q \<in> {t_tm M, r_tm M}
                                  then init_stage (le_tm M)
                                  else (ofs, buf, init_dest, SS1))"
    by (auto simp: ae_delta_ss8_ss1_def)
  from non_halt c'_eq s_eq have q_non_halt: "q \<noteq> t_tm M \<and> q \<noteq> r_tm M"
    by simp
  with stage'_eq have stage'_resolved:
      "stage' = (ofs, buf, init_dest, SS1)" by simp
  show "ae_inv_ss1 M c''"
    unfolding ae_inv_ss1_def
    using c''_eq s'_eq stage'_resolved q_in by simp
qed

text \<open>Halt-branch invariant for SS8\<open>\<rightarrow>\<close>SS1: when
  \<open>M\<close>'s simulated state at SS8 is halting
  (\<open>qM' \<in> {t_tm M, r_tm M}\<close>), the SS8\<open>\<rightarrow>\<close>SS1
  step routes to \<open>init_stage le\<close> (post-idx is \<open>VFwd\<close>, not
  \<open>SS1\<close>) and preserves the halt-state \<open>q\<close>.  Companion to
  \<open>ae_step_ss8_ss1_invariant\<close> (non-halt branch).  The chain
  proof in \<open>ae_simulates_forward_stage\<close> case-splits on whether
  \<open>M\<close>'s state is halting at SS8 and applies one of these two
  lemmas accordingly; the halt branch lands in the simulation's
  halt disjunct (\<open>qM' \<in> {t_tm M, r_tm M}\<close>), the non-halt
  branch in the SS1 disjunct.\<close>

lemma ae_step_ss8_ss1_invariant_halt:
  fixes M :: "('q, 'a) mttm"
    and c' c'' :: "('c :: enum \<Rightarrow> 'a,
                    'q \<times> ('a, 'c) ae_stage) mt_config"
  assumes inv: "ae_inv_ss8 M c'"
      and halt: "case mt_state c' of (qM', _, _, _, _) \<Rightarrow>
                    qM' \<in> {t_tm M, r_tm M}"
      and step: "(c', c'') \<in> mttm_step (ae_delta_ss8_ss1 M)"
    shows "(case mt_state c'' of (qM', _, _, _, idx) \<Rightarrow>
              qM' \<in> {t_tm M, r_tm M} \<and> idx = VFwd)"
proof -
  from step obtain s ts n s' a' d where
      c'_eq: "c' = Config\<^sub>M s ts n"
      and c''_eq: "c'' = Config\<^sub>M s' (\<lambda>k. (ts k)(n k := a' k))
                                    (\<lambda>k. go_dir (d k) (n k))"
      and rel: "(s, (\<lambda>k. ts k (n k)), s', a', d) \<in> ae_delta_ss8_ss1 M"
    by (auto elim: mttm_step.cases)
  from rel obtain q ofs buf dest stage' where
      s_eq: "s = (q, ofs, buf, dest, SS8)"
      and s'_eq: "s' = (q, stage')"
      and q_in: "q \<in> Q_tm M"
      and stage'_eq: "stage' = (if q \<in> {t_tm M, r_tm M}
                                  then init_stage (le_tm M)
                                  else (ofs, buf, init_dest, SS1))"
    by (auto simp: ae_delta_ss8_ss1_def)
  from halt c'_eq s_eq have q_halt: "q \<in> {t_tm M, r_tm M}"
    by simp
  with stage'_eq have stage'_resolved:
      "stage' = init_stage (le_tm M)" by simp
  show ?thesis
    using c''_eq s'_eq stage'_resolved q_halt
    unfolding init_stage_def by simp
qed

subsubsection \<open>\<open>mttm_step\<close> lifts of cross-phase exclusions\<close>

text \<open>\<open>mttm_step\<close>-level lifts of the cross-phase exclusion
  lemmas \<open>ae_delta_ssN_only\<close>: when a substrate-level step
  in the alphabet-enlarged combinator's union has source
  \<open>substep_idx\<close> \<open>SSN\<close>, the step is in the canonical
  \<open>ae_delta_ssN_ssM\<close> substep relation.  Used by the reverse
  arm to commit each peeled \<open>\<delta>'\<close>-step to its canonical
  substep before invoking the per-substep invariant
  propagation.\<close>

lemma mttm_step_ae_delta_ss1_only:
  fixes M :: "('q, 'a) mttm"
    and c c' :: "('c :: enum \<Rightarrow> 'a,
                  'q \<times> ('a, 'c) ae_stage) mt_config"
  assumes step: "(c, c') \<in> mttm_step (alphabet_enlarge_delta M)"
      and ss1: "snd (snd (snd (snd (mt_state c)))) = SS1"
    shows "(c, c') \<in> mttm_step (ae_delta_ss1_ss2 M)"
proof -
  from step obtain s ts n s' a' d where
      c_eq: "c = Config\<^sub>M s ts n"
      and c'_eq: "c' = Config\<^sub>M s' (\<lambda>k. (ts k)(n k := a' k))
                                    (\<lambda>k. go_dir (d k) (n k))"
      and rel: "(s, (\<lambda>k. ts k (n k)), s', a', d)
                  \<in> alphabet_enlarge_delta M"
    by (auto elim: mttm_step.cases)
  from ss1 c_eq have s_ss1: "snd (snd (snd (snd s))) = SS1"
    by simp
  have rel_sub: "(s, (\<lambda>k. ts k (n k)), s', a', d)
                    \<in> ae_delta_ss1_ss2 M"
    by (rule ae_delta_ss1_only[OF rel s_ss1])
  show ?thesis
    unfolding c_eq c'_eq
    by (rule mttm_step.step[where ts = ts and n = n and a = a' and dir = d,
                            OF rel_sub])
qed

lemma mttm_step_ae_delta_ss2_only:
  fixes M :: "('q, 'a) mttm"
    and c c' :: "('c :: enum \<Rightarrow> 'a,
                  'q \<times> ('a, 'c) ae_stage) mt_config"
  assumes step: "(c, c') \<in> mttm_step (alphabet_enlarge_delta M)"
      and ss2: "snd (snd (snd (snd (mt_state c)))) = SS2"
    shows "(c, c') \<in> mttm_step (ae_delta_ss2_ss3 M)"
proof -
  from step obtain s ts n s' a' d where
      c_eq: "c = Config\<^sub>M s ts n"
      and c'_eq: "c' = Config\<^sub>M s' (\<lambda>k. (ts k)(n k := a' k))
                                    (\<lambda>k. go_dir (d k) (n k))"
      and rel: "(s, (\<lambda>k. ts k (n k)), s', a', d)
                  \<in> alphabet_enlarge_delta M"
    by (auto elim: mttm_step.cases)
  from ss2 c_eq have s_ss2: "snd (snd (snd (snd s))) = SS2"
    by simp
  have rel_sub: "(s, (\<lambda>k. ts k (n k)), s', a', d)
                    \<in> ae_delta_ss2_ss3 M"
    by (rule ae_delta_ss2_only[OF rel s_ss2])
  show ?thesis
    unfolding c_eq c'_eq
    by (rule mttm_step.step[where ts = ts and n = n and a = a' and dir = d,
                            OF rel_sub])
qed

lemma mttm_step_ae_delta_ss3_only:
  fixes M :: "('q, 'a) mttm"
    and c c' :: "('c :: enum \<Rightarrow> 'a,
                  'q \<times> ('a, 'c) ae_stage) mt_config"
  assumes step: "(c, c') \<in> mttm_step (alphabet_enlarge_delta M)"
      and ss3: "snd (snd (snd (snd (mt_state c)))) = SS3"
    shows "(c, c') \<in> mttm_step (ae_delta_ss3_ss4 M)"
proof -
  from step obtain s ts n s' a' d where
      c_eq: "c = Config\<^sub>M s ts n"
      and c'_eq: "c' = Config\<^sub>M s' (\<lambda>k. (ts k)(n k := a' k))
                                    (\<lambda>k. go_dir (d k) (n k))"
      and rel: "(s, (\<lambda>k. ts k (n k)), s', a', d)
                  \<in> alphabet_enlarge_delta M"
    by (auto elim: mttm_step.cases)
  from ss3 c_eq have s_ss3: "snd (snd (snd (snd s))) = SS3"
    by simp
  have rel_sub: "(s, (\<lambda>k. ts k (n k)), s', a', d)
                    \<in> ae_delta_ss3_ss4 M"
    by (rule ae_delta_ss3_only[OF rel s_ss3])
  show ?thesis
    unfolding c_eq c'_eq
    by (rule mttm_step.step[where ts = ts and n = n and a = a' and dir = d,
                            OF rel_sub])
qed

lemma mttm_step_ae_delta_ss4_only:
  fixes M :: "('q, 'a) mttm"
    and c c' :: "('c :: enum \<Rightarrow> 'a,
                  'q \<times> ('a, 'c) ae_stage) mt_config"
  assumes step: "(c, c') \<in> mttm_step (alphabet_enlarge_delta M)"
      and ss4: "snd (snd (snd (snd (mt_state c)))) = SS4"
    shows "(c, c') \<in> mttm_step (ae_delta_ss4_ss5 M)"
proof -
  from step obtain s ts n s' a' d where
      c_eq: "c = Config\<^sub>M s ts n"
      and c'_eq: "c' = Config\<^sub>M s' (\<lambda>k. (ts k)(n k := a' k))
                                    (\<lambda>k. go_dir (d k) (n k))"
      and rel: "(s, (\<lambda>k. ts k (n k)), s', a', d)
                  \<in> alphabet_enlarge_delta M"
    by (auto elim: mttm_step.cases)
  from ss4 c_eq have s_ss4: "snd (snd (snd (snd s))) = SS4"
    by simp
  have rel_sub: "(s, (\<lambda>k. ts k (n k)), s', a', d)
                    \<in> ae_delta_ss4_ss5 M"
    by (rule ae_delta_ss4_only[OF rel s_ss4])
  show ?thesis
    unfolding c_eq c'_eq
    by (rule mttm_step.step[where ts = ts and n = n and a = a' and dir = d,
                            OF rel_sub])
qed

lemma mttm_step_ae_delta_ss5_only:
  fixes M :: "('q, 'a) mttm"
    and c c' :: "('c :: enum \<Rightarrow> 'a,
                  'q \<times> ('a, 'c) ae_stage) mt_config"
  assumes step: "(c, c') \<in> mttm_step (alphabet_enlarge_delta M)"
      and ss5: "snd (snd (snd (snd (mt_state c)))) = SS5"
    shows "(c, c') \<in> mttm_step (ae_delta_ss5_ss6 M)"
proof -
  from step obtain s ts n s' a' d where
      c_eq: "c = Config\<^sub>M s ts n"
      and c'_eq: "c' = Config\<^sub>M s' (\<lambda>k. (ts k)(n k := a' k))
                                    (\<lambda>k. go_dir (d k) (n k))"
      and rel: "(s, (\<lambda>k. ts k (n k)), s', a', d)
                  \<in> alphabet_enlarge_delta M"
    by (auto elim: mttm_step.cases)
  from ss5 c_eq have s_ss5: "snd (snd (snd (snd s))) = SS5"
    by simp
  have rel_sub: "(s, (\<lambda>k. ts k (n k)), s', a', d)
                    \<in> ae_delta_ss5_ss6 M"
    by (rule ae_delta_ss5_only[OF rel s_ss5])
  show ?thesis
    unfolding c_eq c'_eq
    by (rule mttm_step.step[where ts = ts and n = n and a = a' and dir = d,
                            OF rel_sub])
qed

lemma mttm_step_ae_delta_ss6_only:
  fixes M :: "('q, 'a) mttm"
    and c c' :: "('c :: enum \<Rightarrow> 'a,
                  'q \<times> ('a, 'c) ae_stage) mt_config"
  assumes step: "(c, c') \<in> mttm_step (alphabet_enlarge_delta M)"
      and ss6: "snd (snd (snd (snd (mt_state c)))) = SS6"
    shows "(c, c') \<in> mttm_step (ae_delta_ss6_ss7 M)"
proof -
  from step obtain s ts n s' a' d where
      c_eq: "c = Config\<^sub>M s ts n"
      and c'_eq: "c' = Config\<^sub>M s' (\<lambda>k. (ts k)(n k := a' k))
                                    (\<lambda>k. go_dir (d k) (n k))"
      and rel: "(s, (\<lambda>k. ts k (n k)), s', a', d)
                  \<in> alphabet_enlarge_delta M"
    by (auto elim: mttm_step.cases)
  from ss6 c_eq have s_ss6: "snd (snd (snd (snd s))) = SS6"
    by simp
  have rel_sub: "(s, (\<lambda>k. ts k (n k)), s', a', d)
                    \<in> ae_delta_ss6_ss7 M"
    by (rule ae_delta_ss6_only[OF rel s_ss6])
  show ?thesis
    unfolding c_eq c'_eq
    by (rule mttm_step.step[where ts = ts and n = n and a = a' and dir = d,
                            OF rel_sub])
qed

lemma mttm_step_ae_delta_ss7_only:
  fixes M :: "('q, 'a) mttm"
    and c c' :: "('c :: enum \<Rightarrow> 'a,
                  'q \<times> ('a, 'c) ae_stage) mt_config"
  assumes step: "(c, c') \<in> mttm_step (alphabet_enlarge_delta M)"
      and ss7: "snd (snd (snd (snd (mt_state c)))) = SS7"
    shows "(c, c') \<in> mttm_step (ae_delta_ss7_ss8 M)"
proof -
  from step obtain s ts n s' a' d where
      c_eq: "c = Config\<^sub>M s ts n"
      and c'_eq: "c' = Config\<^sub>M s' (\<lambda>k. (ts k)(n k := a' k))
                                    (\<lambda>k. go_dir (d k) (n k))"
      and rel: "(s, (\<lambda>k. ts k (n k)), s', a', d)
                  \<in> alphabet_enlarge_delta M"
    by (auto elim: mttm_step.cases)
  from ss7 c_eq have s_ss7: "snd (snd (snd (snd s))) = SS7"
    by simp
  have rel_sub: "(s, (\<lambda>k. ts k (n k)), s', a', d)
                    \<in> ae_delta_ss7_ss8 M"
    by (rule ae_delta_ss7_only[OF rel s_ss7])
  show ?thesis
    unfolding c_eq c'_eq
    by (rule mttm_step.step[where ts = ts and n = n and a = a' and dir = d,
                            OF rel_sub])
qed

lemma mttm_step_ae_delta_ss8_only:
  fixes M :: "('q, 'a) mttm"
    and c c' :: "('c :: enum \<Rightarrow> 'a,
                  'q \<times> ('a, 'c) ae_stage) mt_config"
  assumes step: "(c, c') \<in> mttm_step (alphabet_enlarge_delta M)"
      and ss8: "snd (snd (snd (snd (mt_state c)))) = SS8"
    shows "(c, c') \<in> mttm_step (ae_delta_ss8_ss1 M)"
proof -
  from step obtain s ts n s' a' d where
      c_eq: "c = Config\<^sub>M s ts n"
      and c'_eq: "c' = Config\<^sub>M s' (\<lambda>k. (ts k)(n k := a' k))
                                    (\<lambda>k. go_dir (d k) (n k))"
      and rel: "(s, (\<lambda>k. ts k (n k)), s', a', d)
                  \<in> alphabet_enlarge_delta M"
    by (auto elim: mttm_step.cases)
  from ss8 c_eq have s_ss8: "snd (snd (snd (snd s))) = SS8"
    by simp
  have rel_sub: "(s, (\<lambda>k. ts k (n k)), s', a', d)
                    \<in> ae_delta_ss8_ss1 M"
    by (rule ae_delta_ss8_only[OF rel s_ss8])
  show ?thesis
    unfolding c_eq c'_eq
    by (rule mttm_step.step[where ts = ts and n = n and a = a' and dir = d,
                            OF rel_sub])
qed

subsubsection \<open>Buffered c-fold compute correctness\<close>

text \<open>Algebraic correctness of the buffered c-fold compute:
  starting from a 3-block buffer matching a 3c-cell window of
  the M-tape, with M's head at the home block and within the
  non-LE region, the buffered compute simulates M's actual
  c-step trace.  The conclusion exhibits a buffered-compute
  trajectory and a matching M-trace, with the post-state buffer
  / head still satisfying the window invariant.

  Proof skeleton:

  Induction on a step counter \<open>i \<in> [0, c]\<close>.

  Base case (\<open>i = 0\<close>): pre-state matches itself by the
  \<open>window\<close> hypothesis.

  Step case (\<open>i \<le> c\<close>): assume the IH holds at step \<open>i\<close>.
  Either M halts at \<open>i\<close> (early-stop branch fires;
  \<open>q_i \<in> {t, r}\<close>; done), or M takes an \<open>(i + 1)\<close>-st step.
  In the second sub-case:

  1. Read symbol from the buffer at IH's \<open>bp_i\<close> via
     \<open>read_bp\<close>; the window invariant gives this equals
     \<open>tsM_i (nM_i)\<close>.
  2. Apply M's \<open>\<delta>\<close> (total on non-halting states by
     \<open>valid_mttm\<close>) to get \<open>(q_{i+1}, a', d)\<close>.
  3. Write \<open>a' k\<close> back to the buffer via \<open>write_bp\<close>.
  4. Advance \<open>bp_i\<close> via \<open>bp_advance_le\<close>.  The load-bearing
     claim is that this returns \<open>Some bp_{i+1}\<close> (i.e., the
     head doesn't walk off the buffer).  This holds because
     displacement after \<open>i + 1\<close> steps is at most \<open>i + 1
     \<le> c\<close>, and the buffer covers 3c positions with the
     head starting at home (linearised positions
     \<open>[c, 2c-1]\<close>), so the head stays within
     \<open>[1, 3c-2] \<subset> [0, 3c-1]\<close>.
  5. Verify the post-state still satisfies the window
     invariant: same \<open>p_start\<close>; new \<open>bp_{i+1}\<close>;
     buffer's linearised reading at position
     \<open>bp_linear bp_{i+1}\<close> agrees with \<open>tsM_{i+1}\<close> at
     \<open>nM_{i+1}\<close>.

  The step case's load-bearing arithmetic (item 4) is a
  \<open>bp_advance_le\<close>-vs-tape-position commutation lemma:
  \<open>bp_linear\<close> of the advanced \<open>bp\<close> equals the
  linearised tape position relative to \<open>p_start\<close>.  This
  sub-lemma is non-trivial but standalone — it doesn't depend
  on M's \<open>\<delta>\<close>, only on the encoding's arithmetic.

  The \<open>delta_total\<close> precondition rules out the
  stuck-non-halt case: the substrate's \<open>\<delta>_set\<close> axiom
  permits non-halting states with no \<open>\<delta>\<close>-successor
  (\<open>\<delta> \<subseteq> (Q - {t,r}) \<times> ...\<close> is a subset, not an
  equality).  Without this hypothesis the conclusion is
  unprovable: a stuck \<open>qM\<close> has no buffered run and is
  non-halt, so neither disjunct of the final claim can hold.
  Hartmanis and Stearns's Theorem 2 implicitly assumes \<open>\<delta>\<close> is
  total on \<open>Q - {t,r}\<close>; a caller whose machines are total by
  construction discharges this precondition trivially.\<close>


text \<open>Per-tape unified companion of \<open>ae_coupled_run_aux\<close>,
  \<open>_le0\<close>, and \<open>_le1\<close>.  Takes a per-tape regime
  selector \<open>pos :: nat \<Rightarrow> nat\<close> (= \<open>mt_pos c' k\<close>
  at the SS4 entry) and the per-tape hybrid window-invariant
  predicate \<open>ae_window_invariant_general\<close>, which
  dispatches internally on each tape's regime.  The buffered
  run is the same simultaneous \<open>m_step_buffered M\<close>
  relation as the three siblings — the regime selector is
  frozen per tape during the run (\<open>m_step_buffered\<close>
  has no \<open>c'\<close> in scope), so per-tape regime case-splits
  commute with the induction on \<open>n\<close>.

  The no-LE hypothesis is per-tape regime-aware: width
  \<open>c\<close> for \<open>pos = 0\<close>, \<open>2c\<close> for
  \<open>pos = 1\<close>, \<open>3c\<close> for \<open>pos \<ge> 2\<close>.
  Uniform \<open>p_start = (pos - 2) * c + 1\<close> simplifies to
  \<open>1\<close> on \<open>pos \<in> {0, 1}\<close> by nat arithmetic,
  matching the three siblings' \<open>Suc i\<close> shape.

  The post-compute left-slot guard
  (\<open>fst (buf' k) \<noteq> LE_block\<close>) is preserved on
  \<open>pos = 0\<close> tapes (the generalisation of the le0 chain
  strengthening); le1 tapes have \<open>fst (buf k) = LE_block\<close>
  on entry, and steady tapes do not need this property at the
  SS4\<open>\<rightarrow>\<close>SS5 boundary.

  It sits alongside
  \<open>ae_coupled_run_aux_le0\<close> and \<open>_le1\<close> as
  load-bearing inductive helpers.  Consumer:
  \<open>ae_m_steps_buffered_correct_trace_general\<close>, feeding
  \<open>ae_step_ss4_ss5_exists_general_trace\<close>, which closes
  the SS4\<open>\<rightarrow>\<close>SS5 trace in
  \<open>ae_simulates_forward_stage_general\<close>'s body.\<close>

lemma ae_coupled_run_aux_general:
  fixes M :: "('q, 'a) mttm"
    and qM :: 'q
    and tsM :: "nat \<Rightarrow> nat \<Rightarrow> 'a"
    and nM :: "nat \<Rightarrow> nat"
    and ofs :: "nat \<Rightarrow> ('c :: enum)"
    and buf_full :: "nat \<Rightarrow> (('c \<Rightarrow> 'a) \<times> ('c \<Rightarrow> 'a) \<times> ('c \<Rightarrow> 'a))"
    and pos :: "nat \<Rightarrow> nat"
    and n :: nat
    and cM_n :: "('a, 'q) mt_config"
  assumes vM:        "valid_mttm M"
      and lu:        "le_unique M"
      and qM_in:     "qM \<in> Q_tm M"
      and window:    "\<forall>k<k_tm M. ae_window_invariant_general (tsM k) (nM k)
                            (AE_Home, ofs k) (buf_full k) (pos k) (le_tm M)"
      and pad_home:  "\<forall>k\<ge>k_tm M. fst (snd (buf_full k)) = bl_block (bl_tm M)"
      and trace:     "(Config\<^sub>M qM tsM nM, cM_n)
                        \<in> mttm_step (delta_tm M) ^^ n"
      and n_bound:   "n \<le> card (UNIV :: 'c set)"
      and no_le:
            "\<forall>k. (pos k = 0
                    \<longrightarrow> (\<forall>i. i < card (UNIV :: 'c set)
                              \<longrightarrow> tsM k (Suc i) \<noteq> le_tm M))
                 \<and> (pos k = 1
                      \<longrightarrow> (\<forall>i. i < 2 * card (UNIV :: 'c set)
                                \<longrightarrow> tsM k (Suc i) \<noteq> le_tm M))
                 \<and> (pos k \<ge> 2
                      \<longrightarrow> (\<forall>i. i < 3 * card (UNIV :: 'c set)
                                \<longrightarrow> tsM k
                                      ((pos k - 2) * card (UNIV :: 'c set)
                                        + 1 + i)
                                    \<noteq> le_tm M))"
      and left_not_le_pos0:
            "\<forall>k<k_tm M. pos k = 0 \<longrightarrow> fst (buf_full k) \<noteq> LE_block (le_tm M)"
  shows "\<exists>buf' end_pos.
            ((qM, buf_full, \<lambda>k. (AE_Home, ofs k)),
             (mt_state cM_n, buf', end_pos))
                \<in> (m_step_buffered M) ^^ n
          \<and> (\<forall>k<k_tm M. ae_window_invariant_general
                    (mt_tape cM_n k) (mt_pos cM_n k)
                    (end_pos k) (buf' k) (pos k) (le_tm M))
          \<and> (\<forall>k. (pos k = 0
                    \<longrightarrow> (\<forall>i. i < card (UNIV :: 'c set)
                              \<longrightarrow> mt_tape cM_n k (Suc i) \<noteq> le_tm M))
                 \<and> (pos k = 1
                      \<longrightarrow> (\<forall>i. i < 2 * card (UNIV :: 'c set)
                                \<longrightarrow> mt_tape cM_n k (Suc i) \<noteq> le_tm M))
                 \<and> (pos k \<ge> 2
                      \<longrightarrow> (\<forall>i. i < 3 * card (UNIV :: 'c set)
                                \<longrightarrow> mt_tape cM_n k
                                      ((pos k - 2) * card (UNIV :: 'c set)
                                        + 1 + i)
                                    \<noteq> le_tm M)))
          \<and> (\<forall>k<k_tm M. pos k = 0
                    \<longrightarrow> fst (buf' k) \<noteq> LE_block (le_tm M))
          \<and> (\<forall>k. card (UNIV :: 'c set) \<le> bp_linear (end_pos k) + n
                  \<and> bp_linear (end_pos k)
                        < 2 * card (UNIV :: 'c set) + n)
          \<and> (\<forall>k\<ge>k_tm M. fst (snd (buf' k)) = bl_block (bl_tm M)
                  \<and> end_pos k = (AE_Home, ofs k))"
  using trace n_bound
proof (induction n arbitrary: cM_n)
  case 0
  \<comment> \<open>Base case: zero \<open>M\<close>-steps means \<open>cM_n\<close> is the
    initial config, the buffered run is empty, and the four
    output conjuncts hold by direct lifting of the lemma's input
    hypotheses (\<open>window\<close>, \<open>no_le\<close>,
    \<open>left_not_le_pos0\<close>) at the unchanged buffered state.
    Witnesses: \<open>buf' = buf_full\<close>,
    \<open>end_pos = \<lambda>k. (AE_Home, ofs k)\<close>.\<close>
  from \<open>(Config\<^sub>M qM tsM nM, cM_n)
            \<in> mttm_step (delta_tm M) ^^ 0\<close>
  have cM_eq: "cM_n = Config\<^sub>M qM tsM nM" by simp
  hence st: "mt_state cM_n = qM"
    and tp: "mt_tape cM_n = tsM"
    and ps: "mt_pos cM_n = nM" by auto
  show ?case
  proof (intro exI [where x = buf_full]
                exI [where x = "\<lambda>k. (AE_Home, ofs k)"]
                conjI)
    show "((qM, buf_full, \<lambda>k. (AE_Home, ofs k)),
            (mt_state cM_n, buf_full, \<lambda>k. (AE_Home, ofs k)))
              \<in> (m_step_buffered M) ^^ 0"
      using st by simp
    show "\<forall>k<k_tm M. ae_window_invariant_general
                (mt_tape cM_n k) (mt_pos cM_n k)
                ((\<lambda>k. (AE_Home, ofs k)) k)
                (buf_full k) (pos k) (le_tm M)"
      using window tp ps by simp
    show "\<forall>k. (pos k = 0
                \<longrightarrow> (\<forall>i. i < card (UNIV :: 'c set)
                          \<longrightarrow> mt_tape cM_n k (Suc i) \<noteq> le_tm M))
             \<and> (pos k = 1
                  \<longrightarrow> (\<forall>i. i < 2 * card (UNIV :: 'c set)
                            \<longrightarrow> mt_tape cM_n k (Suc i) \<noteq> le_tm M))
             \<and> (pos k \<ge> 2
                  \<longrightarrow> (\<forall>i. i < 3 * card (UNIV :: 'c set)
                            \<longrightarrow> mt_tape cM_n k
                                  ((pos k - 2) * card (UNIV :: 'c set)
                                    + 1 + i)
                                \<noteq> le_tm M))"
      using no_le tp by simp
    show "\<forall>k<k_tm M. pos k = 0
                \<longrightarrow> fst (buf_full k) \<noteq> LE_block (le_tm M)"
      using left_not_le_pos0 .
    show "\<forall>k. card (UNIV :: 'c set)
                \<le> bp_linear ((\<lambda>k. (AE_Home, ofs k)) k) + 0
              \<and> bp_linear ((\<lambda>k. (AE_Home, ofs k)) k)
                    < 2 * card (UNIV :: 'c set) + 0"
    proof (intro allI conjI)
      fix k
      have lin: "bp_linear ((\<lambda>k. (AE_Home, ofs k)) k)
                    = card (UNIV :: 'c set) + c_idx (ofs k)"
        unfolding bp_linear_def by simp
      show "card (UNIV :: 'c set)
              \<le> bp_linear ((\<lambda>k. (AE_Home, ofs k)) k) + 0"
        using lin by simp
      show "bp_linear ((\<lambda>k. (AE_Home, ofs k)) k)
              < 2 * card (UNIV :: 'c set) + 0"
        using lin c_idx_lt_card[where x = "ofs k"] by simp
    qed
    show "\<forall>k\<ge>k_tm M. fst (snd (buf_full k)) = bl_block (bl_tm M)
                \<and> (\<lambda>k. (AE_Home, ofs k)) k = (AE_Home, ofs k)"
      using pad_home by simp
  qed
next
  case (Suc n')
  \<comment> \<open>Inductive step: peel the last \<open>M\<close>-side step via
    \<open>relpow_Suc_E\<close> to obtain an intermediate config
    \<open>cM_n'\<close>; apply the IH at \<open>n'\<close> to obtain a
    coupled buffered run of length \<open>n'\<close>; extend it by one
    \<open>m_step_buffered\<close> step mirroring the M-side
    transition; re-establish the four output conjuncts at
    \<open>n = Suc n'\<close>.

    The four ingredients are: (i) buffered read matches M-side
    read via window-invariant buf-linearisation; (ii) same
    \<open>\<delta>\<close>-tuple drives both sides; (iii)
    \<open>bp_advance_le\<close> is total at every reached head
    position (\<open>no_le\<close> rules out the only None case);
    (iv) window invariant preserved by parallel writes and
    head advances.\<close>
  have n'_bound: "n' \<le> card (UNIV :: 'c set)"
    using Suc.prems(2) by simp
  from Suc.prems(1) obtain cM_n' where
      trace_n': "(Config\<^sub>M qM tsM nM, cM_n')
                    \<in> mttm_step (delta_tm M) ^^ n'"
    and last_step: "(cM_n', cM_n) \<in> mttm_step (delta_tm M)"
    by (rule relpow_Suc_E)
  from Suc.IH[OF trace_n' n'_bound]
  obtain buf_n' end_pos_n' where
      coupled_n':
        "((qM, buf_full, \<lambda>k. (AE_Home, ofs k)),
          (mt_state cM_n', buf_n', end_pos_n'))
            \<in> (m_step_buffered M) ^^ n'"
    and window_n':
        "\<forall>k<k_tm M. ae_window_invariant_general
                (mt_tape cM_n' k) (mt_pos cM_n' k)
                (end_pos_n' k) (buf_n' k) (pos k) (le_tm M)"
    and no_le_n':
        "\<forall>k. (pos k = 0
                \<longrightarrow> (\<forall>i. i < card (UNIV :: 'c set)
                          \<longrightarrow> mt_tape cM_n' k (Suc i)
                                \<noteq> le_tm M))
             \<and> (pos k = 1
                  \<longrightarrow> (\<forall>i. i < 2 * card (UNIV :: 'c set)
                            \<longrightarrow> mt_tape cM_n' k (Suc i)
                                  \<noteq> le_tm M))
             \<and> (pos k \<ge> 2
                  \<longrightarrow> (\<forall>i. i < 3 * card (UNIV :: 'c set)
                            \<longrightarrow> mt_tape cM_n' k
                                  ((pos k - 2)
                                      * card (UNIV :: 'c set)
                                    + 1 + i)
                                \<noteq> le_tm M))"
    and left_n':
        "\<forall>k<k_tm M. pos k = 0
              \<longrightarrow> fst (buf_n' k) \<noteq> LE_block (le_tm M)"
    and bp_bound_n':
        "\<forall>k. card (UNIV :: 'c set) \<le> bp_linear (end_pos_n' k) + n'
              \<and> bp_linear (end_pos_n' k)
                    < 2 * card (UNIV :: 'c set) + n'"
    and pad_n':
        "\<forall>k\<ge>k_tm M. fst (snd (buf_n' k)) = bl_block (bl_tm M)
              \<and> end_pos_n' k = (AE_Home, ofs k)"
    by blast
  \<comment> \<open>Unpack \<open>last_step\<close> via \<open>mttm_step.cases\<close>
    into its \<open>\<delta>\<close>-tuple ingredients: a state shape
    \<open>cM_n' = Config q_pre ts_pre n_pre\<close>, the resulting
    \<open>cM_n\<close> as the M-side write + head-advance, and the
    \<open>(q_pre, read, q_post, a_step, dir_step)\<close>
    \<open>\<delta>\<close>-membership.\<close>
  from last_step obtain q_pre ts_pre n_pre q_post a_step dir_step where
      cM_n'_eq: "cM_n' = Config\<^sub>M q_pre ts_pre n_pre"
    and cM_n_eq:
        "cM_n = Config\<^sub>M q_post
                  (\<lambda>k. (ts_pre k)(n_pre k := a_step k))
                  (\<lambda>k. go_dir (dir_step k) (n_pre k))"
    and delta_mem:
        "(q_pre, \<lambda>k. ts_pre k (n_pre k),
            q_post, a_step, dir_step) \<in> delta_tm M"
    by (rule mttm_step.cases)
  \<comment> \<open>Derived closed forms on \<open>cM_n'\<close> /
    \<open>cM_n\<close>'s components — convenient handles for the
    buffered-side construction in the next increment.\<close>
  have st_n': "mt_state cM_n' = q_pre"
   and tp_n': "mt_tape cM_n' = ts_pre"
   and ps_n': "mt_pos cM_n' = n_pre"
    using cM_n'_eq by auto
  have st_n: "mt_state cM_n = q_post"
   and tp_n: "\<forall>k. mt_tape cM_n k
                    = (ts_pre k)(n_pre k := a_step k)"
   and ps_n: "\<forall>k. mt_pos cM_n k
                    = go_dir (dir_step k) (n_pre k)"
    using cM_n_eq by auto
  \<comment> \<open>At this point we have:
    (a) the coupled buffered run of length \<open>n'\<close> ending at
        \<open>(q_pre, buf_n', end_pos_n')\<close>;
    (b) the four invariants at \<open>cM_n'\<close>;
    (c) the M-side \<open>\<delta>\<close>-tuple
        \<open>(q_pre, read, q_post, a_step, dir_step)\<close>;
    (d) closed forms for \<open>cM_n\<close>'s state / tape / pos.\<close>
  \<comment> \<open>Ingredient (i) of the inductive step: per-tape
    read-match.  The buffered read at \<open>end_pos_n' k\<close>
    equals the M-side read at \<open>n_pre k\<close>, via the unified
    \<open>read_bp_via_window_general\<close>.\<close>
  have read_match:
      "\<forall>k. read_bp (buf_n' k) (end_pos_n' k) = ts_pre k (n_pre k)"
  proof (intro allI)
    fix k
    show "read_bp (buf_n' k) (end_pos_n' k) = ts_pre k (n_pre k)"
    proof (cases "k < k_tm M")
      case True
      \<comment> \<open>Active tape: the read-match is the window invariant's
          buf-linearisation clause projected at the head offset.\<close>
      from window_n'[rule_format, OF True] have wi_k:
          "ae_window_invariant_general
              (mt_tape cM_n' k) (mt_pos cM_n' k)
              (end_pos_n' k) (buf_n' k) (pos k) (le_tm M)" .
      hence wi_k':
          "ae_window_invariant_general
              (ts_pre k) (n_pre k)
              (end_pos_n' k) (buf_n' k) (pos k) (le_tm M)"
        using tp_n' ps_n' by simp
      show ?thesis
        by (rule read_bp_via_window_general[OF wi_k'])
    next
      case False
      \<comment> \<open>Padding tape \<open>k \<ge> k_tm M\<close>: M reads blank
          (\<open>valid_mttm_delta_support\<close>) and the buffered home block is
          blank with the head parked at home (\<open>pad_n'\<close>), so both
          sides read \<open>bl_tm M\<close>.\<close>
      hence kge: "k_tm M \<le> k" by simp
      from pad_n'[rule_format, OF kge]
      have ph: "fst (snd (buf_n' k)) = bl_block (bl_tm M)"
        and ep: "end_pos_n' k = (AE_Home, ofs k)" by simp_all
      have rd: "ts_pre k (n_pre k) = bl_tm M"
        using valid_mttm_delta_support[OF vM delta_mem kge] by simp
      obtain l h r where blk: "buf_n' k = (l, h, r)"
        by (cases "buf_n' k") auto
      from ph blk have h_eq: "h = bl_block (bl_tm M)" by simp
      have "read_bp (buf_n' k) (end_pos_n' k) = bl_tm M"
        using blk ep h_eq by (simp add: read_bp_def bl_block_def)
      thus ?thesis using rd by simp
    qed
  qed
  \<comment> \<open>Per-tape position bounds at step \<open>n'\<close>: the fifth
    output conjunct of the IH (\<open>bp_bound_n'\<close>) plus the
    bound \<open>Suc n' \<le> c\<close> (giving \<open>n' < c\<close>) yields
    strict bounds \<open>bp_linear < 3c - 1\<close> and
    \<open>0 < bp_linear\<close> per tape, excluding both None
    configurations of \<open>bp_advance\<close>.\<close>
  have c_pos: "1 \<le> card (UNIV :: 'c set)"
    using Suc.prems(2) by linarith
  have bp_lt_max:
      "\<forall>k. bp_linear (end_pos_n' k)
              < 3 * card (UNIV :: 'c set) - 1"
  proof (intro allI)
    fix k
    have lin_lt: "bp_linear (end_pos_n' k) < 2 * card (UNIV :: 'c set) + n'"
      using bp_bound_n' by blast
    show "bp_linear (end_pos_n' k) < 3 * card (UNIV :: 'c set) - 1"
      using lin_lt Suc.prems(2) c_pos by linarith
  qed
  have bp_gt_zero:
      "\<forall>k. 0 < bp_linear (end_pos_n' k)"
  proof (intro allI)
    fix k
    have low: "card (UNIV :: 'c set) \<le> bp_linear (end_pos_n' k) + n'"
      using bp_bound_n' by blast
    show "0 < bp_linear (end_pos_n' k)"
      using low Suc.prems(2) c_pos by linarith
  qed
  \<comment> \<open>Ingredient (iii): per-tape \<open>bp_advance_le\<close> totality
    at step \<open>n'\<close>.  Apply \<open>bp_advance_le_total\<close> per tape
    with \<open>bp_lt_max\<close>, \<open>bp_gt_zero\<close>; lift across tapes
    via choice to obtain the new per-tape head position function
    \<open>end_pos_n :: nat \<Rightarrow> 'c bp\<close>.\<close>
  have per_tape_total:
      "\<forall>k. \<exists>p'. bp_advance_le (le_tm M)
                    (ts_pre k (n_pre k))
                    (end_pos_n' k) (dir_step k)
                = Some p'"
  proof (intro allI)
    fix k
    show "\<exists>p'. bp_advance_le (le_tm M)
                  (ts_pre k (n_pre k))
                  (end_pos_n' k) (dir_step k)
              = Some p'"
      by (rule bp_advance_le_total[OF bp_lt_max[rule_format]
                                       bp_gt_zero[rule_format]])
  qed
  from per_tape_total
  have "\<exists>end_pos_n.
            \<forall>k. bp_advance_le (le_tm M)
                    (ts_pre k (n_pre k))
                    (end_pos_n' k) (dir_step k)
                  = Some (end_pos_n k)"
    by (rule choice)
  then obtain end_pos_n where
      end_pos_n_eq:
        "\<forall>k. bp_advance_le (le_tm M)
                (ts_pre k (n_pre k))
                (end_pos_n' k) (dir_step k)
              = Some (end_pos_n k)"
    by blast
  \<comment> \<open>Ingredient (ii): assemble the buffered last step's
    membership in \<open>m_step_buffered M\<close>.  Define the new
    buffer \<open>buf_n\<close> as the per-tape write-back of
    \<open>buf_n'\<close> at \<open>end_pos_n'\<close> with \<open>a_step\<close>;
    apply the intro rule \<open>m_step_bufferedI\<close> with the four
    ingredients (\<open>delta_mem\<close>, \<open>read_match\<close>'s
    reverse, \<open>buf_n\<close>'s definitional read-back, and
    \<open>end_pos_n_eq\<close>).\<close>
  define buf_n where
    "buf_n = (\<lambda>k. write_bp (buf_n' k) (end_pos_n' k) (a_step k))"
  have read_match_sym:
      "\<forall>k. ts_pre k (n_pre k) = read_bp (buf_n' k) (end_pos_n' k)"
    using read_match by auto
  have buf_n_def_forall:
      "\<forall>k. buf_n k = write_bp (buf_n' k) (end_pos_n' k) (a_step k)"
    using buf_n_def by simp
  have m_step_last:
      "((q_pre, buf_n', end_pos_n'),
        (q_post, buf_n, end_pos_n))
            \<in> m_step_buffered M"
    by (rule m_step_bufferedI[OF delta_mem read_match_sym
                                  buf_n_def_forall end_pos_n_eq])
  \<comment> \<open>Chain extension: bridge \<open>coupled_n'\<close>'s endpoint
    \<open>(mt_state cM_n', buf_n', end_pos_n')\<close> through
    \<open>st_n'\<close> (\<open>mt_state cM_n' = q_pre\<close>) to match
    \<open>m_step_last\<close>'s start, then compose via
    \<open>relpow_Suc_I\<close> for a \<open>Suc n'\<close>-step buffered run
    ending at \<open>(q_post, buf_n, end_pos_n)\<close>.\<close>
  have coupled_n_pre:
      "((qM, buf_full, \<lambda>k. (AE_Home, ofs k)),
        (q_pre, buf_n', end_pos_n'))
            \<in> (m_step_buffered M) ^^ n'"
    using coupled_n' st_n' by simp
  have coupled_n:
      "((qM, buf_full, \<lambda>k. (AE_Home, ofs k)),
        (q_post, buf_n, end_pos_n))
            \<in> (m_step_buffered M) ^^ Suc n'"
    using coupled_n_pre m_step_last by (rule relpow_Suc_I)
  \<comment> \<open>Conjunct 5 (\<open>bp_linear\<close> bound at step Suc n'): apply
    the helper \<open>bp_advance_le_lin_bounded\<close> per tape.
    Given the IH's conjunct (\<open>bp_bound_n'\<close>) plus the
    position bounds (\<open>bp_gt_zero\<close>) plus the advance
    \<open>end_pos_n_eq\<close>, the helper closes both bound
    components.\<close>
  have bp_bound_n:
      "\<forall>k. card (UNIV :: 'c set) \<le> bp_linear (end_pos_n k) + Suc n'
            \<and> bp_linear (end_pos_n k)
                  < 2 * card (UNIV :: 'c set) + Suc n'"
  proof (intro allI)
    fix k
    show "card (UNIV :: 'c set) \<le> bp_linear (end_pos_n k) + Suc n'
          \<and> bp_linear (end_pos_n k)
                < 2 * card (UNIV :: 'c set) + Suc n'"
      by (rule bp_advance_le_lin_bounded
                  [OF end_pos_n_eq[rule_format, of k]
                      bp_gt_zero[rule_format, of k]
                      conjunct2[OF bp_bound_n'[rule_format, of k]]
                      conjunct1[OF bp_bound_n'[rule_format, of k]]])
  qed
  \<comment> \<open>Conjunct 4 (\<open>left_not_le_pos0\<close> at step Suc n'):
    in \<open>pos k = 0\<close> regime, the window invariant excludes
    \<open>fst (end_pos_n' k) = AE_Left\<close>, so \<open>write_bp\<close>'s
    update doesn't touch the left slot.  Hence
    \<open>fst (buf_n k) = fst (buf_n' k)\<close>, and the IH's
    \<open>left_n'\<close> closes the goal.\<close>
  have left_n:
      "\<forall>k<k_tm M. pos k = 0
              \<longrightarrow> fst (buf_n k) \<noteq> LE_block (le_tm M)"
  proof (intro allI impI)
    fix k
    assume klt: "k < k_tm M"
    assume pos_0: "pos k = 0"
    from window_n'[rule_format, OF klt] have wi_k:
        "ae_window_invariant_general (mt_tape cM_n' k) (mt_pos cM_n' k)
            (end_pos_n' k) (buf_n' k) (pos k) (le_tm M)" .
    with pos_0 have wi_le0:
        "ae_window_invariant_le0 (mt_tape cM_n' k) (mt_pos cM_n' k)
            (end_pos_n' k) (buf_n' k) (le_tm M)"
      unfolding ae_window_invariant_general_def by simp
    have fst_bp_not_left: "fst (end_pos_n' k) \<noteq> AE_Left"
    proof (rule ccontr)
      assume "\<not> fst (end_pos_n' k) \<noteq> AE_Left"
      hence "fst (end_pos_n' k) = AE_Left" by simp
      with wi_le0 show False
        unfolding ae_window_invariant_le0_def by simp
    qed
    have fst_buf_n: "fst (buf_n k) = fst (buf_n' k)"
    proof -
      obtain l h r where blocks_eq: "buf_n' k = (l, h, r)"
        by (cases "buf_n' k") auto
      obtain b off where bp_eq: "end_pos_n' k = (b, off)"
        by (cases "end_pos_n' k") auto
      from fst_bp_not_left bp_eq have "b \<noteq> AE_Left" by simp
      thus ?thesis
        unfolding buf_n_def
        using blocks_eq bp_eq
        by (cases b) (auto simp: write_bp_def)
    qed
    have "fst (buf_n' k) \<noteq> LE_block (le_tm M)"
      using left_n' pos_0 klt by blast
    thus "fst (buf_n k) \<noteq> LE_block (le_tm M)"
      using fst_buf_n by simp
  qed
  \<comment> \<open>Conjunct 1 (coupled run with \<open>mt_state cM_n\<close>
    witness at step Suc n'): re-express \<open>coupled_n\<close>'s
    endpoint state from \<open>q_post\<close> to \<open>mt_state cM_n\<close>
    via \<open>st_n\<close>.\<close>
  have coupled_chain:
      "((qM, buf_full, \<lambda>k. (AE_Home, ofs k)),
        (mt_state cM_n, buf_n, end_pos_n))
            \<in> (m_step_buffered M) ^^ Suc n'"
    using coupled_n st_n by simp
  \<comment> \<open>Contrapositive of the substrate axiom
    \<open>valid_mttm_deltaLE_no_write\<close>: if M reads non-LE on tape \<open>k\<close>
    cell \<open>n_pre k\<close>, then it does not write LE on tape \<open>k\<close>.
    This is what powers the \<open>j = n_pre k\<close> case of conjunct 3:
    the new tape value at the updated cell is \<open>a_step k\<close>, and
    we need to show \<open>a_step k \<noteq> le\<close> when the read value was
    in a no-LE window.\<close>
  have no_le_contra:
      "\<forall>k. ts_pre k (n_pre k) \<noteq> le_tm M
              \<longrightarrow> a_step k \<noteq> le_tm M"
  proof (intro allI impI)
    fix k
    assume rd_not_le: "ts_pre k (n_pre k) \<noteq> le_tm M"
    show "a_step k \<noteq> le_tm M"
    proof
      assume a_le: "a_step k = le_tm M"
      have "(\<lambda>k. ts_pre k (n_pre k)) k = le_tm M"
        by (rule valid_mttm_deltaLE_no_write[OF lu delta_mem a_le])
      hence "ts_pre k (n_pre k) = le_tm M" by simp
      with rd_not_le show False ..
    qed
  qed
  \<comment> \<open>Conjunct 3 regime \<open>pos k = 0\<close> (no LE in cells
    \<open>Suc 0 .. card UNIV\<close>): for each cell \<open>Suc i\<close> in
    the window, case-split on whether the M-step's update site
    \<open>n_pre k\<close> coincides with \<open>Suc i\<close>.

    \<open>\<bullet>\<close> If not, the fun-update leaves \<open>mt_tape cM_n k (Suc i)\<close>
    equal to \<open>ts_pre k (Suc i) = mt_tape cM_n' k (Suc i)\<close>;
    the IH (\<open>no_le_n'\<close>) closes the goal.

    \<open>\<bullet>\<close> If yes, the new value is \<open>a_step k\<close>; the IH gives
    \<open>ts_pre k (n_pre k) = ts_pre k (Suc i) \<noteq> le_tm M\<close>;
    the contrapositive \<open>no_le_contra\<close> gives
    \<open>a_step k \<noteq> le_tm M\<close>.\<close>
  have no_le0_n:
      "\<forall>k. pos k = 0
              \<longrightarrow> (\<forall>i. i < card (UNIV :: 'c set)
                        \<longrightarrow> mt_tape cM_n k (Suc i) \<noteq> le_tm M)"
  proof (intro allI impI allI impI)
    fix k i
    assume pos_0: "pos k = 0"
       and i_bd: "i < card (UNIV :: 'c set)"
    have ih_at: "ts_pre k (Suc i) \<noteq> le_tm M"
    proof -
      from no_le_n' pos_0 i_bd
      have "mt_tape cM_n' k (Suc i) \<noteq> le_tm M" by blast
      thus ?thesis using tp_n' by simp
    qed
    show "mt_tape cM_n k (Suc i) \<noteq> le_tm M"
    proof (cases "Suc i = n_pre k")
      case False
      hence "mt_tape cM_n k (Suc i) = ts_pre k (Suc i)"
        using tp_n by simp
      thus ?thesis using ih_at by simp
    next
      case True
      hence tape_eq: "mt_tape cM_n k (Suc i) = a_step k"
        using tp_n by simp
      from True have "ts_pre k (n_pre k) = ts_pre k (Suc i)"
        by simp
      with ih_at have "ts_pre k (n_pre k) \<noteq> le_tm M" by simp
      hence "a_step k \<noteq> le_tm M" using no_le_contra by blast
      thus ?thesis using tape_eq by simp
    qed
  qed
  \<comment> \<open>Conjunct 3 regime \<open>pos k = 1\<close>: same window shape
    \<open>Suc i\<close> as \<open>pos = 0\<close>, but the bound is doubled to
    \<open>2 * card UNIV\<close>.  The proof shape is identical;
    only the bound on \<open>i\<close> changes.\<close>
  have no_le1_n:
      "\<forall>k. pos k = 1
              \<longrightarrow> (\<forall>i. i < 2 * card (UNIV :: 'c set)
                        \<longrightarrow> mt_tape cM_n k (Suc i) \<noteq> le_tm M)"
  proof (intro allI impI allI impI)
    fix k i
    assume pos_1: "pos k = 1"
       and i_bd: "i < 2 * card (UNIV :: 'c set)"
    have ih_at: "ts_pre k (Suc i) \<noteq> le_tm M"
    proof -
      from no_le_n' pos_1 i_bd
      have "mt_tape cM_n' k (Suc i) \<noteq> le_tm M" by blast
      thus ?thesis using tp_n' by simp
    qed
    show "mt_tape cM_n k (Suc i) \<noteq> le_tm M"
    proof (cases "Suc i = n_pre k")
      case False
      hence "mt_tape cM_n k (Suc i) = ts_pre k (Suc i)"
        using tp_n by simp
      thus ?thesis using ih_at by simp
    next
      case True
      hence tape_eq: "mt_tape cM_n k (Suc i) = a_step k"
        using tp_n by simp
      from True have "ts_pre k (n_pre k) = ts_pre k (Suc i)"
        by simp
      with ih_at have "ts_pre k (n_pre k) \<noteq> le_tm M" by simp
      hence "a_step k \<noteq> le_tm M" using no_le_contra by blast
      thus ?thesis using tape_eq by simp
    qed
  qed
  \<comment> \<open>Conjunct 3 regime \<open>pos k \<ge> 2\<close> (steady regime): the
    no-LE window spans \<open>3 * card UNIV\<close> cells starting at
    offset \<open>(pos k - 2) * card UNIV + 1\<close>.  The proof shape
    is identical to the \<open>pos = 0\<close>/\<open>pos = 1\<close> cases; only
    the cell expression changes.\<close>
  have no_le2_n:
      "\<forall>k. pos k \<ge> 2
              \<longrightarrow> (\<forall>i. i < 3 * card (UNIV :: 'c set)
                        \<longrightarrow> mt_tape cM_n k
                              ((pos k - 2) * card (UNIV :: 'c set) + 1 + i)
                            \<noteq> le_tm M)"
  proof (intro allI impI allI impI)
    fix k i
    assume pos_ge: "pos k \<ge> 2"
       and i_bd: "i < 3 * card (UNIV :: 'c set)"
    let ?j = "(pos k - 2) * card (UNIV :: 'c set) + 1 + i"
    have ih_at: "ts_pre k ?j \<noteq> le_tm M"
    proof -
      from no_le_n' pos_ge i_bd
      have "mt_tape cM_n' k ?j \<noteq> le_tm M" by blast
      thus ?thesis using tp_n' by simp
    qed
    show "mt_tape cM_n k ?j \<noteq> le_tm M"
    proof (cases "?j = n_pre k")
      case False
      hence "mt_tape cM_n k ?j = ts_pre k ?j"
        using tp_n by simp
      thus ?thesis using ih_at by simp
    next
      case True
      hence tape_eq: "mt_tape cM_n k ?j = a_step k"
        using tp_n by simp
      from True have "ts_pre k (n_pre k) = ts_pre k ?j"
        by simp
      with ih_at have "ts_pre k (n_pre k) \<noteq> le_tm M" by simp
      hence "a_step k \<noteq> le_tm M" using no_le_contra by blast
      thus ?thesis using tape_eq by simp
    qed
  qed
  \<comment> \<open>Conjunct 3 (no-LE invariant at \<open>cM_n\<close>): assemble the
    three regime sub-lemmas \<open>no_le0_n\<close>, \<open>no_le1_n\<close>,
    \<open>no_le2_n\<close> into the dispatch-on-\<open>pos\<close> shape that
    matches the lemma statement.\<close>
  have no_le_n:
      "\<forall>k. (pos k = 0
              \<longrightarrow> (\<forall>i. i < card (UNIV :: 'c set)
                        \<longrightarrow> mt_tape cM_n k (Suc i) \<noteq> le_tm M))
           \<and> (pos k = 1
                \<longrightarrow> (\<forall>i. i < 2 * card (UNIV :: 'c set)
                          \<longrightarrow> mt_tape cM_n k (Suc i) \<noteq> le_tm M))
           \<and> (pos k \<ge> 2
                \<longrightarrow> (\<forall>i. i < 3 * card (UNIV :: 'c set)
                          \<longrightarrow> mt_tape cM_n k
                                ((pos k - 2) * card (UNIV :: 'c set)
                                  + 1 + i)
                              \<noteq> le_tm M))"
    using no_le0_n no_le1_n no_le2_n by blast
  \<comment> \<open>Conjunct 2 regime \<open>pos k \<ge> 2\<close> (steady regime): apply
    \<open>ae_window_invariant_step\<close> per tape.  Five ingredients:
    the IH-side invariant from \<open>window_n'\<close>; the
    \<open>bp_advance_le\<close> step from \<open>end_pos_n_eq\<close>; the position
    bounds from \<open>bp_lt_max\<close> and \<open>bp_gt_zero\<close>; and the
    no-LE-at-head fact derived from the IH's \<open>no_le_n'\<close>
    instantiated at the buffered-head's linearised offset
    (which lies inside the regime's no-LE window).\<close>
  have win2_n:
      "\<forall>k<k_tm M. pos k \<ge> 2
              \<longrightarrow> ae_window_invariant
                    (mt_tape cM_n k) (mt_pos cM_n k)
                    (end_pos_n k) (buf_n k)
                    ((pos k - 2) * card (UNIV :: 'c set) + 1)"
  proof (intro allI impI)
    fix k
    assume klt: "k < k_tm M"
    assume pos_ge: "pos k \<ge> 2"
    from window_n'[rule_format, OF klt] pos_ge have wi_k:
        "ae_window_invariant (mt_tape cM_n' k) (mt_pos cM_n' k)
              (end_pos_n' k) (buf_n' k)
              ((pos k - 2) * card (UNIV :: 'c set) + 1)"
      unfolding ae_window_invariant_general_def by simp
    hence wi_k': "ae_window_invariant (ts_pre k) (n_pre k)
                    (end_pos_n' k) (buf_n' k)
                    ((pos k - 2) * card (UNIV :: 'c set) + 1)"
      using tp_n' ps_n' by simp
    have adv_k: "bp_advance_le (le_tm M) (ts_pre k (n_pre k))
                    (end_pos_n' k) (dir_step k) = Some (end_pos_n k)"
      using end_pos_n_eq by blast
    have bp_lt_k: "bp_linear (end_pos_n' k)
                      < 3 * card (UNIV :: 'c set) - 1"
      using bp_lt_max by blast
    have bp_pos_k: "0 < bp_linear (end_pos_n' k)"
      using bp_gt_zero by blast
    \<comment> \<open>No-LE-at-head: \<open>n_pre k = (pos k - 2)*c + 1 + j\<close> where
      \<open>j = bp_linear (end_pos_n' k) < 3c\<close>; instantiate the
      IH's no-LE window at this \<open>j\<close>.\<close>
    have no_le_k: "ts_pre k (n_pre k) \<noteq> le_tm M"
    proof -
      let ?j = "bp_linear (end_pos_n' k)"
      from wi_k' have head_corr:
          "n_pre k = (pos k - 2) * card (UNIV :: 'c set) + 1 + ?j"
        unfolding ae_window_invariant_def by simp
      have j_lt: "?j < 3 * card (UNIV :: 'c set)"
        by (rule bp_linear_lt_3c)
      from no_le_n' pos_ge j_lt have
          "mt_tape cM_n' k
              ((pos k - 2) * card (UNIV :: 'c set) + 1 + ?j)
            \<noteq> le_tm M" by blast
      hence "ts_pre k
              ((pos k - 2) * card (UNIV :: 'c set) + 1 + ?j)
            \<noteq> le_tm M" using tp_n' by simp
      thus ?thesis using head_corr by simp
    qed
    have wi_step:
        "ae_window_invariant
              ((ts_pre k)(n_pre k := a_step k))
              (go_dir (dir_step k) (n_pre k))
              (end_pos_n k)
              (write_bp (buf_n' k) (end_pos_n' k) (a_step k))
              ((pos k - 2) * card (UNIV :: 'c set) + 1)"
      by (rule ae_window_invariant_step
                [OF wi_k' adv_k bp_lt_k bp_pos_k no_le_k])
    show "ae_window_invariant
              (mt_tape cM_n k) (mt_pos cM_n k)
              (end_pos_n k) (buf_n k)
              ((pos k - 2) * card (UNIV :: 'c set) + 1)"
      using wi_step tp_n ps_n buf_n_def by simp
  qed
  \<comment> \<open>Conjunct 2 regime \<open>pos k = 1\<close> (LE-edge \<open>le1\<close>): apply
    \<open>ae_window_invariant_le1_step\<close> per tape.  The two LE-aware
    preconditions:

    \<open>\<bullet>\<close> \<open>a_le_k\<close> (\<open>tM nM = le \<Longrightarrow> a_step k = le \<and> dir_step k \<in> {N, R}\<close>):
    derived from \<open>valid_mttm_deltaLE\<close> applied to \<open>delta_mem\<close> at tape \<open>k\<close>.

    \<open>\<bullet>\<close> \<open>a_not_le_k\<close> (\<open>tM nM \<noteq> le \<Longrightarrow> a_step k \<noteq> le\<close>):
    a per-tape instance of \<open>no_le_contra\<close> already in scope.

    The \<open>no_le_win_k\<close> precondition (no LE in cells \<open>1..2c\<close>)
    follows from \<open>no_le_n'\<close>'s \<open>pos = 1\<close> branch via \<open>tp_n'\<close>.\<close>
  have win1_n:
      "\<forall>k<k_tm M. pos k = 1
              \<longrightarrow> ae_window_invariant_le1
                    (mt_tape cM_n k) (mt_pos cM_n k)
                    (end_pos_n k) (buf_n k) (le_tm M)"
  proof (intro allI impI)
    fix k
    assume klt: "k < k_tm M"
    assume pos_1: "pos k = 1"
    from window_n'[rule_format, OF klt] pos_1 have wi_k:
        "ae_window_invariant_le1 (mt_tape cM_n' k) (mt_pos cM_n' k)
              (end_pos_n' k) (buf_n' k) (le_tm M)"
      unfolding ae_window_invariant_general_def by simp
    hence wi_k': "ae_window_invariant_le1 (ts_pre k) (n_pre k)
                    (end_pos_n' k) (buf_n' k) (le_tm M)"
      using tp_n' ps_n' by simp
    have adv_k: "bp_advance_le (le_tm M) (ts_pre k (n_pre k))
                    (end_pos_n' k) (dir_step k) = Some (end_pos_n k)"
      using end_pos_n_eq by blast
    have bp_lt_k: "bp_linear (end_pos_n' k)
                      < 3 * card (UNIV :: 'c set) - 1"
      using bp_lt_max by blast
    have bp_pos_k: "0 < bp_linear (end_pos_n' k)"
      using bp_gt_zero by blast
    have a_le_k:
        "ts_pre k (n_pre k) = le_tm M
            \<Longrightarrow> a_step k = le_tm M \<and> dir_step k \<in> {dir.N, dir.R}"
    proof -
      assume rd_le: "ts_pre k (n_pre k) = le_tm M"
      have "a_step k = le_tm M \<and> dir_step k \<in> {dir.N, dir.R}"
        by (rule valid_mttm_deltaLE[OF vM delta_mem, of k, OF rd_le])
      thus "a_step k = le_tm M \<and> dir_step k \<in> {dir.N, dir.R}" .
    qed
    have a_not_le_k:
        "ts_pre k (n_pre k) \<noteq> le_tm M \<Longrightarrow> a_step k \<noteq> le_tm M"
      using no_le_contra by blast
    have no_le_win_k:
        "\<forall>i. 0 < i \<and> i \<le> 2 * card (UNIV :: 'c set)
                  \<longrightarrow> ts_pre k i \<noteq> le_tm M"
    proof (intro allI impI)
      fix i
      assume i_bd: "0 < i \<and> i \<le> 2 * card (UNIV :: 'c set)"
      obtain j where j_eq: "i = Suc j" using i_bd by (cases i) auto
      have j_lt: "j < 2 * card (UNIV :: 'c set)"
        using i_bd j_eq by simp
      from no_le_n' pos_1 j_lt
      have "mt_tape cM_n' k (Suc j) \<noteq> le_tm M" by blast
      thus "ts_pre k i \<noteq> le_tm M" using tp_n' j_eq by simp
    qed
    have wi_step:
        "ae_window_invariant_le1
              ((ts_pre k)(n_pre k := a_step k))
              (go_dir (dir_step k) (n_pre k))
              (end_pos_n k)
              (write_bp (buf_n' k) (end_pos_n' k) (a_step k))
              (le_tm M)"
      by (rule ae_window_invariant_le1_step
                [OF wi_k' adv_k bp_lt_k bp_pos_k
                    a_le_k a_not_le_k no_le_win_k])
    show "ae_window_invariant_le1
              (mt_tape cM_n k) (mt_pos cM_n k)
              (end_pos_n k) (buf_n k) (le_tm M)"
      using wi_step tp_n ps_n buf_n_def by simp
  qed
  \<comment> \<open>Conjunct 2 regime \<open>pos k = 0\<close> (LE-edge \<open>le0\<close>): apply
    \<open>ae_window_invariant_le0_step\<close> per tape.  Pattern identical
    to the \<open>pos = 1\<close> call; only the lemma and the no-LE
    window range (cells \<open>1..c\<close>) differ.\<close>
  have win0_n:
      "\<forall>k<k_tm M. pos k = 0
              \<longrightarrow> ae_window_invariant_le0
                    (mt_tape cM_n k) (mt_pos cM_n k)
                    (end_pos_n k) (buf_n k) (le_tm M)"
  proof (intro allI impI)
    fix k
    assume klt: "k < k_tm M"
    assume pos_0: "pos k = 0"
    from window_n'[rule_format, OF klt] pos_0 have wi_k:
        "ae_window_invariant_le0 (mt_tape cM_n' k) (mt_pos cM_n' k)
              (end_pos_n' k) (buf_n' k) (le_tm M)"
      unfolding ae_window_invariant_general_def by simp
    hence wi_k': "ae_window_invariant_le0 (ts_pre k) (n_pre k)
                    (end_pos_n' k) (buf_n' k) (le_tm M)"
      using tp_n' ps_n' by simp
    have adv_k: "bp_advance_le (le_tm M) (ts_pre k (n_pre k))
                    (end_pos_n' k) (dir_step k) = Some (end_pos_n k)"
      using end_pos_n_eq by blast
    have bp_lt_k: "bp_linear (end_pos_n' k)
                      < 3 * card (UNIV :: 'c set) - 1"
      using bp_lt_max by blast
    have bp_pos_k: "0 < bp_linear (end_pos_n' k)"
      using bp_gt_zero by blast
    have a_le_k:
        "ts_pre k (n_pre k) = le_tm M
            \<Longrightarrow> a_step k = le_tm M \<and> dir_step k \<in> {dir.N, dir.R}"
    proof -
      assume rd_le: "ts_pre k (n_pre k) = le_tm M"
      show "a_step k = le_tm M \<and> dir_step k \<in> {dir.N, dir.R}"
        by (rule valid_mttm_deltaLE[OF vM delta_mem, of k, OF rd_le])
    qed
    have a_not_le_k:
        "ts_pre k (n_pre k) \<noteq> le_tm M \<Longrightarrow> a_step k \<noteq> le_tm M"
      using no_le_contra by blast
    have no_le_win_k:
        "\<forall>i. 0 < i \<and> i \<le> card (UNIV :: 'c set)
                  \<longrightarrow> ts_pre k i \<noteq> le_tm M"
    proof (intro allI impI)
      fix i
      assume i_bd: "0 < i \<and> i \<le> card (UNIV :: 'c set)"
      obtain j where j_eq: "i = Suc j" using i_bd by (cases i) auto
      have j_lt: "j < card (UNIV :: 'c set)"
        using i_bd j_eq by simp
      from no_le_n' pos_0 j_lt
      have "mt_tape cM_n' k (Suc j) \<noteq> le_tm M" by blast
      thus "ts_pre k i \<noteq> le_tm M" using tp_n' j_eq by simp
    qed
    have wi_step:
        "ae_window_invariant_le0
              ((ts_pre k)(n_pre k := a_step k))
              (go_dir (dir_step k) (n_pre k))
              (end_pos_n k)
              (write_bp (buf_n' k) (end_pos_n' k) (a_step k))
              (le_tm M)"
      by (rule ae_window_invariant_le0_step
                [OF wi_k' adv_k bp_lt_k bp_pos_k
                    a_le_k a_not_le_k no_le_win_k])
    show "ae_window_invariant_le0
              (mt_tape cM_n k) (mt_pos cM_n k)
              (end_pos_n k) (buf_n k) (le_tm M)"
      using wi_step tp_n ps_n buf_n_def by simp
  qed
  \<comment> \<open>Conjunct 2 (window invariant at \<open>cM_n\<close>): assemble the
    three regime sub-lemmas \<open>win0_n\<close>, \<open>win1_n\<close>,
    \<open>win2_n\<close> into the dispatch-on-\<open>pos\<close> shape that
    matches the lemma statement
    (\<open>ae_window_invariant_general\<close>).\<close>
  have window_n:
      "\<forall>k<k_tm M. ae_window_invariant_general
              (mt_tape cM_n k) (mt_pos cM_n k)
              (end_pos_n k) (buf_n k) (pos k) (le_tm M)"
  proof (intro allI impI)
    fix k
    assume klt: "k < k_tm M"
    show "ae_window_invariant_general
            (mt_tape cM_n k) (mt_pos cM_n k)
            (end_pos_n k) (buf_n k) (pos k) (le_tm M)"
      unfolding ae_window_invariant_general_def
      using win0_n win1_n win2_n klt by blast
  qed
  \<comment> \<open>Padding shadow invariant at step \<open>Suc n'\<close>: empty
    tapes \<open>k \<ge> k_tm M\<close> keep a blank home block and a head
    parked at \<open>(AE_Home, ofs k)\<close>.  Preserved from the IH's
    \<open>pad_n'\<close> by the M-step's \<open>\<delta>\<close>-support (\<open>read = a' = bl\<close>,
    \<open>d = N\<close> past tape count): the head stays put under \<open>bp_advance\<close>
    of a \<open>dir.N\<close> step, and writing \<open>bl\<close> into the blank home
    is idempotent.\<close>
  have pad_n:
      "\<forall>k\<ge>k_tm M. fst (snd (buf_n k)) = bl_block (bl_tm M)
              \<and> end_pos_n k = (AE_Home, ofs k)"
  proof (intro allI impI)
    fix k
    assume kge: "k_tm M \<le> k"
    from pad_n'[rule_format, OF kge]
    have ph: "fst (snd (buf_n' k)) = bl_block (bl_tm M)"
      and ep: "end_pos_n' k = (AE_Home, ofs k)" by simp_all
    from valid_mttm_delta_support[OF vM delta_mem kge]
    have rd: "ts_pre k (n_pre k) = bl_tm M"
      and wr: "a_step k = bl_tm M"
      and dr: "dir_step k = dir.N" by simp_all
    have ep_n: "end_pos_n k = (AE_Home, ofs k)"
    proof -
      have adv: "bp_advance_le (le_tm M) (ts_pre k (n_pre k))
                    (end_pos_n' k) (dir_step k) = Some (end_pos_n k)"
        using end_pos_n_eq by blast
      have "bp_advance_le (le_tm M) (bl_tm M) (AE_Home, ofs k) dir.N
              = Some (AE_Home, ofs k)"
        by (simp add: bp_advance_le_def bp_advance_def)
      thus ?thesis using adv rd ep dr by simp
    qed
    have buf_n_k: "fst (snd (buf_n k)) = bl_block (bl_tm M)"
    proof -
      obtain l h r where blk: "buf_n' k = (l, h, r)"
        by (cases "buf_n' k") auto
      from ph blk have h_eq: "h = bl_block (bl_tm M)" by simp
      have "buf_n k = (l, h(ofs k := bl_tm M), r)"
        using blk ep wr by (simp add: buf_n_def write_bp_def)
      hence "fst (snd (buf_n k)) = h(ofs k := bl_tm M)" by simp
      also have "\<dots> = bl_block (bl_tm M)"
        using h_eq by (simp add: bl_block_def fun_eq_iff)
      finally show ?thesis .
    qed
    show "fst (snd (buf_n k)) = bl_block (bl_tm M)
            \<and> end_pos_n k = (AE_Home, ofs k)"
      using buf_n_k ep_n by simp
  qed
  \<comment> \<open>Final \<open>show ?case\<close> assembly: package the five
    discharged conjuncts (\<open>coupled_chain\<close>, \<open>window_n\<close>,
    \<open>no_le_n\<close>, \<open>left_n\<close>, \<open>bp_bound_n\<close>) into the
    existential output via \<open>buf_n\<close> and \<open>end_pos_n\<close>.\<close>
  show ?case
  proof (intro exI [where x = buf_n] exI [where x = end_pos_n] conjI)
    show "((qM, buf_full, \<lambda>k. (AE_Home, ofs k)),
            (mt_state cM_n, buf_n, end_pos_n))
              \<in> (m_step_buffered M) ^^ Suc n'"
      by (rule coupled_chain)
    show "\<forall>k<k_tm M. ae_window_invariant_general
                (mt_tape cM_n k) (mt_pos cM_n k)
                (end_pos_n k) (buf_n k) (pos k) (le_tm M)"
      by (rule window_n)
    show "\<forall>k. (pos k = 0
                \<longrightarrow> (\<forall>i. i < card (UNIV :: 'c set)
                          \<longrightarrow> mt_tape cM_n k (Suc i) \<noteq> le_tm M))
             \<and> (pos k = 1
                  \<longrightarrow> (\<forall>i. i < 2 * card (UNIV :: 'c set)
                            \<longrightarrow> mt_tape cM_n k (Suc i) \<noteq> le_tm M))
             \<and> (pos k \<ge> 2
                  \<longrightarrow> (\<forall>i. i < 3 * card (UNIV :: 'c set)
                            \<longrightarrow> mt_tape cM_n k
                                  ((pos k - 2) * card (UNIV :: 'c set)
                                    + 1 + i)
                                \<noteq> le_tm M))"
      by (rule no_le_n)
    show "\<forall>k<k_tm M. pos k = 0
                \<longrightarrow> fst (buf_n k) \<noteq> LE_block (le_tm M)"
      by (rule left_n)
    show "\<forall>k. card (UNIV :: 'c set) \<le> bp_linear (end_pos_n k) + Suc n'
              \<and> bp_linear (end_pos_n k)
                    < 2 * card (UNIV :: 'c set) + Suc n'"
      by (rule bp_bound_n)
    show "\<forall>k\<ge>k_tm M. fst (snd (buf_n k)) = bl_block (bl_tm M)
                \<and> end_pos_n k = (AE_Home, ofs k)"
      by (rule pad_n)
  qed
qed


text \<open>Per-tape unified companion of
  \<open>ae_m_steps_buffered_correct_trace\<close>, \<open>_le0\<close>, and
  \<open>_le1\<close>.  A wrapper over
  \<open>ae_coupled_run_aux_general\<close>: builds the
  \<open>m_steps_buffered\<close> step (= relpow plus
  \<open>kM \<le> c\<close> and end-or-halt) and re-packages the aux's
  existential into an \<open>obtains\<close>-style witness.

  The hypothesis shape matches the three siblings' wrapper
  pattern: a per-tape regime selector \<open>pos\<close>, the per-tape
  hybrid window invariant, the per-tape regime-guarded
  \<open>no_le\<close>, and the \<open>pos = 0\<close>-conditional left-slot
  guard.  Output conjuncts mirror the input, with the buffered
  config existentially bound.\<close>

lemma ae_m_steps_buffered_correct_trace_general:
  fixes M :: "('q, 'a) mttm"
    and qM :: 'q
    and tsM :: "nat \<Rightarrow> nat \<Rightarrow> 'a"
    and nM :: "nat \<Rightarrow> nat"
    and ofs :: "nat \<Rightarrow> ('c :: enum)"
    and buf_full :: "nat \<Rightarrow> (('c \<Rightarrow> 'a) \<times> ('c \<Rightarrow> 'a) \<times> ('c \<Rightarrow> 'a))"
    and pos :: "nat \<Rightarrow> nat"
    and kM :: nat
    and cM_k :: "('a, 'q) mt_config"
  assumes vM:        "valid_mttm M"
      and lu:        "le_unique M"
      and qM_in:     "qM \<in> Q_tm M"
      and window:    "\<forall>k<k_tm M. ae_window_invariant_general (tsM k) (nM k)
                            (AE_Home, ofs k) (buf_full k) (pos k) (le_tm M)"
      and pad_home:  "\<forall>k\<ge>k_tm M. fst (snd (buf_full k)) = bl_block (bl_tm M)"
      and no_le:
            "\<forall>k. (pos k = 0
                    \<longrightarrow> (\<forall>i. i < card (UNIV :: 'c set)
                              \<longrightarrow> tsM k (Suc i) \<noteq> le_tm M))
                 \<and> (pos k = 1
                      \<longrightarrow> (\<forall>i. i < 2 * card (UNIV :: 'c set)
                                \<longrightarrow> tsM k (Suc i) \<noteq> le_tm M))
                 \<and> (pos k \<ge> 2
                      \<longrightarrow> (\<forall>i. i < 3 * card (UNIV :: 'c set)
                                \<longrightarrow> tsM k
                                      ((pos k - 2) * card (UNIV :: 'c set)
                                        + 1 + i)
                                    \<noteq> le_tm M))"
      and trace:     "(Config\<^sub>M qM tsM nM, cM_k)
                        \<in> mttm_step (delta_tm M) ^^ kM"
      and kM_le:     "kM \<le> card (UNIV :: 'c set)"
      and end_or_halt:
            "kM = card (UNIV :: 'c set)
              \<or> mt_state cM_k \<in> {t_tm M, r_tm M}"
      and left_not_le_pos0:
            "\<forall>k<k_tm M. pos k = 0 \<longrightarrow> fst (buf_full k) \<noteq> LE_block (le_tm M)"
  obtains q_out buf' end_pos where
      "((qM, buf_full, \<lambda>k. (AE_Home, ofs k)),
         (q_out, buf', end_pos)) \<in> m_steps_buffered M"
    and "q_out = mt_state cM_k"
    and "\<forall>k<k_tm M. ae_window_invariant_general
              (mt_tape cM_k k) (mt_pos cM_k k)
              (end_pos k) (buf' k) (pos k) (le_tm M)"
    and "\<forall>k. (pos k = 0
                \<longrightarrow> (\<forall>i. i < card (UNIV :: 'c set)
                          \<longrightarrow> mt_tape cM_k k (Suc i) \<noteq> le_tm M))
             \<and> (pos k = 1
                  \<longrightarrow> (\<forall>i. i < 2 * card (UNIV :: 'c set)
                            \<longrightarrow> mt_tape cM_k k (Suc i) \<noteq> le_tm M))
             \<and> (pos k \<ge> 2
                  \<longrightarrow> (\<forall>i. i < 3 * card (UNIV :: 'c set)
                            \<longrightarrow> mt_tape cM_k k
                                  ((pos k - 2) * card (UNIV :: 'c set)
                                    + 1 + i)
                                \<noteq> le_tm M))"
    and "\<forall>k<k_tm M. pos k = 0
              \<longrightarrow> fst (buf' k) \<noteq> LE_block (le_tm M)"
proof -
  have ae_result_general:
      "\<exists>buf' end_pos.
          ((qM, buf_full, \<lambda>k. (AE_Home, ofs k)),
           (mt_state cM_k, buf', end_pos))
              \<in> (m_step_buffered M) ^^ kM
        \<and> (\<forall>k<k_tm M. ae_window_invariant_general
                  (mt_tape cM_k k) (mt_pos cM_k k)
                  (end_pos k) (buf' k) (pos k) (le_tm M))
        \<and> (\<forall>k. (pos k = 0
                  \<longrightarrow> (\<forall>i. i < card (UNIV :: 'c set)
                            \<longrightarrow> mt_tape cM_k k (Suc i) \<noteq> le_tm M))
               \<and> (pos k = 1
                    \<longrightarrow> (\<forall>i. i < 2 * card (UNIV :: 'c set)
                              \<longrightarrow> mt_tape cM_k k (Suc i) \<noteq> le_tm M))
               \<and> (pos k \<ge> 2
                    \<longrightarrow> (\<forall>i. i < 3 * card (UNIV :: 'c set)
                              \<longrightarrow> mt_tape cM_k k
                                    ((pos k - 2) * card (UNIV :: 'c set)
                                      + 1 + i)
                                  \<noteq> le_tm M)))
        \<and> (\<forall>k<k_tm M. pos k = 0
                  \<longrightarrow> fst (buf' k) \<noteq> LE_block (le_tm M))
        \<and> (\<forall>k. card (UNIV :: 'c set) \<le> bp_linear (end_pos k) + kM
                \<and> bp_linear (end_pos k)
                      < 2 * card (UNIV :: 'c set) + kM)
        \<and> (\<forall>k\<ge>k_tm M. fst (snd (buf' k)) = bl_block (bl_tm M)
                \<and> end_pos k = (AE_Home, ofs k))"
    by (rule ae_coupled_run_aux_general[OF vM lu qM_in window pad_home trace kM_le
                                           no_le left_not_le_pos0])
  obtain buf' end_pos where
      coupled: "((qM, buf_full, \<lambda>k. (AE_Home, ofs k)),
                 (mt_state cM_k, buf', end_pos))
                    \<in> (m_step_buffered M) ^^ kM"
    and new_window:
        "\<forall>k<k_tm M. ae_window_invariant_general
              (mt_tape cM_k k) (mt_pos cM_k k)
              (end_pos k) (buf' k) (pos k) (le_tm M)"
    and post_no_le:
        "\<forall>k. (pos k = 0
                \<longrightarrow> (\<forall>i. i < card (UNIV :: 'c set)
                          \<longrightarrow> mt_tape cM_k k (Suc i) \<noteq> le_tm M))
             \<and> (pos k = 1
                  \<longrightarrow> (\<forall>i. i < 2 * card (UNIV :: 'c set)
                            \<longrightarrow> mt_tape cM_k k (Suc i) \<noteq> le_tm M))
             \<and> (pos k \<ge> 2
                  \<longrightarrow> (\<forall>i. i < 3 * card (UNIV :: 'c set)
                            \<longrightarrow> mt_tape cM_k k
                                  ((pos k - 2) * card (UNIV :: 'c set)
                                    + 1 + i)
                                \<noteq> le_tm M))"
    and post_left_not_le_pos0:
        "\<forall>k<k_tm M. pos k = 0
              \<longrightarrow> fst (buf' k) \<noteq> LE_block (le_tm M)"
    and bp_bound:
        "\<forall>k. card (UNIV :: 'c set) \<le> bp_linear (end_pos k) + kM
              \<and> bp_linear (end_pos k)
                    < 2 * card (UNIV :: 'c set) + kM"
    using ae_result_general by blast
  have buffered_full:
      "((qM, buf_full, \<lambda>k. (AE_Home, ofs k)),
        (mt_state cM_k, buf', end_pos)) \<in> m_steps_buffered M"
    unfolding m_steps_buffered_def
    using coupled kM_le end_or_halt by auto
  show thesis
  proof (rule that[where q_out = "mt_state cM_k"
                     and buf' = buf' and end_pos = end_pos])
    show "((qM, buf_full, \<lambda>k. (AE_Home, ofs k)),
           (mt_state cM_k, buf', end_pos)) \<in> m_steps_buffered M"
      using buffered_full .
    show "mt_state cM_k = mt_state cM_k" by (rule refl)
    show "\<forall>k<k_tm M. ae_window_invariant_general
              (mt_tape cM_k k) (mt_pos cM_k k)
              (end_pos k) (buf' k) (pos k) (le_tm M)"
      using new_window .
    show "\<forall>k. (pos k = 0
                \<longrightarrow> (\<forall>i. i < card (UNIV :: 'c set)
                          \<longrightarrow> mt_tape cM_k k (Suc i) \<noteq> le_tm M))
             \<and> (pos k = 1
                  \<longrightarrow> (\<forall>i. i < 2 * card (UNIV :: 'c set)
                            \<longrightarrow> mt_tape cM_k k (Suc i) \<noteq> le_tm M))
             \<and> (pos k \<ge> 2
                  \<longrightarrow> (\<forall>i. i < 3 * card (UNIV :: 'c set)
                            \<longrightarrow> mt_tape cM_k k
                                  ((pos k - 2) * card (UNIV :: 'c set)
                                    + 1 + i)
                                \<noteq> le_tm M))"
      using post_no_le .
    show "\<forall>k<k_tm M. pos k = 0
                \<longrightarrow> fst (buf' k) \<noteq> LE_block (le_tm M)"
      using post_left_not_le_pos0 .
  qed
qed

end
