theory AlphabetEnlargement_ForwardStage
  imports AlphabetEnlargement_ForwardArms
begin

text \<open>The primary forward-stage statement, feeding
  \<open>ae_simulation_phase_step_count\<close> (theory
  \<open>AlphabetEnlargement_Acceptance\<close>).  Tip of the forward-stage
  chain \<open>ForwardCells \<rightarrow> ForwardStep \<rightarrow> ForwardArms \<rightarrow>
  ForwardStage\<close>: it composes the four arms of
  \<open>AlphabetEnlargement_ForwardArms\<close> with the SS5\<open>\<rightarrow>\<close>SS8 chain lemma
  \<open>ae_forward_stage_step_chain\<close>, decodes the head positions at
  \<open>c8\<close>, and assembles \<open>ae_simulates\<close> there.

  Each tape \<open>k\<close> picks its regime (steady / le1 / le0)
  independently from its own \<open>ktc_pos c' k\<close>; mixed
  configurations across tapes are handled natively, with no
  uniform-regime case-split at the call site.  Per-tape dispatch is
  mandatory: the regimes can differ from tape to tape.

  The \<open>no_le_per_tape\<close> hypothesis bundles a per-tape
  LE-free window whose start and width depend on the tape's
  block position: \<open>3c\<close>-cell window starting at the
  left neighbour for steady tapes, \<open>2c\<close>-cell window
  starting at position 1 for le1 tapes, \<open>c\<close>-cell window
  starting at position 1 for le0 tapes.  Discharged at the call
  site via substrate's \<open>valid_reach_LE_only_pos0_ktm\<close>
  for any reach-from-init configuration.

  The displacement disjunct's leftward branch is conditioned on
  \<open>ktc_pos c' kk > 0\<close> — le0 tapes cannot move left from
  block 0.\<close>

lemma ae_simulates_forward_stage_general:
  fixes M :: "('q, 'a) ktm"
    and cM cM_k :: "('a, 'q) ktc_config"
    and c' :: "(nat \<Rightarrow> 'a,
                'q \<times> 'a ae_stage) ktc_config"
    and k :: nat
  assumes vM:        "valid_ktm M"
      and lu:        "le_unique M"
      and sim:       "ae_simulates m M cM c'"
      and qM_in_Q:   "ktc_state cM \<in> Q_ktm M"
      and q_neq_t:   "ktc_state cM \<noteq> t_ktm M"
      and q_neq_r:   "ktc_state cM \<noteq> r_ktm M"
      and buf_gamma: "ae_buffer_in_gamma_block m M c'"
      and k_le:      "k \<le> m"
      and trace:     "(cM, cM_k) \<in> ktm_step (delta_ktm M) ^^ k"
      and end_or_halt:
            "k = m
              \<or> ktc_state cM_k \<in> {t_ktm M, r_ktm M}"
      and le_anchor:
            "\<forall>k<k_ktm M. ktc_tape c' k 0 = LE_block m (le_ktm M)"
      and le_neq_bl:
            "le_ktm M \<noteq> bl_ktm M"
      and no_le_per_tape:
            "\<forall>k. (ktc_pos c' k \<ge> 2
                    \<longrightarrow> (\<forall>i. i < 3 * m
                              \<longrightarrow> ktc_tape cM k
                                    ((ktc_pos c' k - 2) * m + 1 + i)
                                  \<noteq> le_ktm M))
                 \<and> (ktc_pos c' k = 1
                      \<longrightarrow> (\<forall>i. i < 2 * m
                                \<longrightarrow> ktc_tape cM k (Suc i) \<noteq> le_ktm M))
                 \<and> (ktc_pos c' k = 0
                      \<longrightarrow> (\<forall>i. i < m
                                \<longrightarrow> ktc_tape cM k (Suc i) \<noteq> le_ktm M))"
  obtains c'' c1 c2 c3 c4 c5 c6 c7 ofs_f buf_f dest_f where
      "(c', c'') \<in> ktm_step (alphabet_enlarge_delta m M) ^^ 8"
    and "ae_simulates m M cM_k c''"
    and "ae_buffer_in_gamma_block m M c''"
    and "\<forall>kk<k_ktm M. ktc_tape c'' kk 0 = LE_block m (le_ktm M)"
    \<comment> \<open>SS5 exposure for the det-free reverse direction
        (\<open>nae_sim_proto\<close>): the full substep chain, the SS5 state
        shape + window correspondence in \<open>(dest, ofs)\<close> bp form, and
        the buffer \<open>\<gamma>\<close>-block carrying the frozen inactive
        tails.\<close>
    and "(c', c1) \<in> ktm_step (ae_delta_ss1_ss2 m M)"
    and "(c1, c2) \<in> ktm_step (ae_delta_ss2_ss3 m M)"
    and "(c2, c3) \<in> ktm_step (ae_delta_ss3_ss4 m M)"
    and "(c3, c4) \<in> ktm_step (ae_delta_ss4_ss5 m M)"
    and "(c4, c5) \<in> ktm_step (ae_delta_ss5_ss6 m M)"
    and "(c5, c6) \<in> ktm_step (ae_delta_ss6_ss7 m M)"
    and "(c6, c7) \<in> ktm_step (ae_delta_ss7_ss8 m M)"
    and "(c7, c'') \<in> ktm_step (ae_delta_ss8_ss1 m M)"
    and "ktc_state c4 = (ktc_state cM_k, ofs_f, buf_f, dest_f, SS5)"
    and "\<forall>kk<k_ktm M. ae_window_invariant_general m
              (ktc_tape cM_k kk) (ktc_pos cM_k kk)
              (dest_f kk, ofs_f kk) (buf_f kk) (ktc_pos c' kk) (le_ktm M)"
    and "ae_buffer_in_gamma_block m M c4"
proof -
  \<comment> \<open>Substeps 1 to 4: unpack \<open>ae_simulates\<close> at the \<open>SS1\<close> entry,
      load the buffers, compute (\<open>ae_fwd_load_compute\<close>).\<close>
  obtain ofs c1 c2 c3 c4
    where tape_corr: "\<forall>k<k_ktm M. ae_tape_correspondence m (le_ktm M)
              (ktc_tape cM k) (ktc_tape c' k)"
      and pos_corr: "\<forall>k<k_ktm M. ktc_pos cM k = ae_decode_pos m (ktc_pos c' k) (ofs k)"
      and step1_sub: "(c', c1) \<in> ktm_step (ae_delta_ss1_ss2 m M)"
      and step1: "(c', c1) \<in> ktm_step (alphabet_enlarge_delta m M)"
      and step2_sub: "(c1, c2) \<in> ktm_step (ae_delta_ss2_ss3 m M)"
      and step2: "(c1, c2) \<in> ktm_step (alphabet_enlarge_delta m M)"
      and step3_sub: "(c2, c3) \<in> ktm_step (ae_delta_ss3_ss4 m M)"
      and step3: "(c2, c3) \<in> ktm_step (alphabet_enlarge_delta m M)"
      and c_ge_1: "1 \<le> m"
      and ofs_lt: "\<forall>k. ofs k < m"
      and c_eq_len: "m = length [0..<m]"
      and home_classification:
            "\<forall>k<k_ktm M. (ktc_pos c' k = 0
                \<longrightarrow> ktc_tape c' k (ktc_pos c' k) = LE_block m (le_ktm M))
              \<and> (ktc_pos c' k \<ge> 1
                \<longrightarrow> ktc_tape c' k (ktc_pos c' k) \<noteq> LE_block m (le_ktm M))"
      and c3_pos_all: "\<forall>k<k_ktm M. ktc_pos c3 k = ktc_pos c' k + 1"
      and bl_neq_le:
            "(bl_block m (bl_ktm M) :: nat \<Rightarrow> 'a) \<noteq> LE_block m (le_ktm M)"
      and step4_sub: "(c3, c4) \<in> ktm_step (ae_delta_ss4_ss5 m M)"
      and step4: "(c3, c4) \<in> ktm_step (alphabet_enlarge_delta m M)"
      and c4_q_out:
            "case ktc_state c4 of (q_out, _, _, _, _) \<Rightarrow> q_out = ktc_state cM_k"
      and c4_buf_not_le_per_tape:
            "case ktc_state c4 of (_, _, b, _, _) \<Rightarrow>
               \<forall>kk<k_ktm M. (ktc_pos c' kk = 0
                   \<longrightarrow> fst (b kk) \<noteq> LE_block m (le_ktm M)
                     \<and> snd (snd (b kk)) \<noteq> LE_block m (le_ktm M))
                 \<and> (ktc_pos c' kk = 1
                   \<longrightarrow> fst (snd (b kk)) \<noteq> LE_block m (le_ktm M)
                     \<and> snd (snd (b kk)) \<noteq> LE_block m (le_ktm M))
                 \<and> (ktc_pos c' kk \<ge> 2
                   \<longrightarrow> fst (b kk) \<noteq> LE_block m (le_ktm M)
                     \<and> fst (snd (b kk)) \<noteq> LE_block m (le_ktm M)
                     \<and> snd (snd (b kk)) \<noteq> LE_block m (le_ktm M))"
      and c4_window_general:
            "case ktc_state c4 of (_, ofs', buf', dest', _) \<Rightarrow>
               \<forall>kk<k_ktm M. ae_window_invariant_general m
                 (ktc_tape cM_k kk) (ktc_pos cM_k kk)
                 (dest' kk, ofs' kk) (buf' kk) (ktc_pos c' kk) (le_ktm M)"
      and inv_ss5: "ae_inv_ss5 M c4"
      and gamma_c4: "ae_tape_in_gamma_block m M c4"
      and buf_gamma_c4: "ae_buffer_in_gamma_block m M c4"
    by (rule ae_fwd_load_compute[OF vM lu sim qM_in_Q q_neq_t q_neq_r buf_gamma
          k_le trace end_or_halt le_anchor le_neq_bl no_le_per_tape])
  note c3_pos = c3_pos_all[rule_format]
  \<comment> \<open>The SS5\<open>\<rightarrow>\<close>SS8 chain, by
      \<open>ae_forward_stage_step_chain\<close>.  Re-binds the 12 intermediate
      witnesses and 29 named facts the per-tape reconstruction below
      consumes.\<close>
  obtain c5 q5 ofs5 buf5 dest5 c6 c7 q6 ofs6 buf6 dest6 c8
    where step5_sub: "(c4, c5) \<in> ktm_step (ae_delta_ss5_ss6 m M)"
      and step5: "(c4, c5) \<in> ktm_step (alphabet_enlarge_delta m M)"
      and c4_state: "ktc_state c4 = (q5, ofs5, buf5, dest5, SS5)"
      and c5_state: "ktc_state c5 = (q5, ofs5, buf5, dest5, SS6)"
      and tape_c4_eq_c': "ktc_tape c4 = ktc_tape c'"
      and buf5_not_le_per_tape:
      "\<forall>k<k_ktm M. (ktc_pos c' k = 0
      \<longrightarrow> fst (buf5 k) \<noteq> LE_block m (le_ktm M)
      \<and> snd (snd (buf5 k)) \<noteq> LE_block m (le_ktm M))
      \<and> (ktc_pos c' k = 1
      \<longrightarrow> fst (snd (buf5 k)) \<noteq> LE_block m (le_ktm M)
      \<and> snd (snd (buf5 k)) \<noteq> LE_block m (le_ktm M))
      \<and> (ktc_pos c' k \<ge> 2
      \<longrightarrow> fst (buf5 k) \<noteq> LE_block m (le_ktm M)
      \<and> fst (snd (buf5 k)) \<noteq> LE_block m (le_ktm M)
      \<and> snd (snd (buf5 k)) \<noteq> LE_block m (le_ktm M))"
      and right_not_le_c':
      "\<forall>k. ktc_tape c' k (ktc_pos c' k + 1) \<noteq> LE_block m (le_ktm M)"
      and c4_pos_all: "\<forall>kk. kk < k_ktm M \<longrightarrow> ktc_pos c4 kk = ktc_pos c' kk"
      and tape_c5_zero_le: "\<forall>k<k_ktm M. ktc_tape c5 k 0 = LE_block m (le_ktm M)"
      and c5_pos_for_pos1_all:
      "\<forall>kk. kk < k_ktm M \<longrightarrow> ktc_pos c' kk = 1 \<longrightarrow> dest5 kk \<noteq> AE_Left
      \<longrightarrow> ktc_pos c5 kk = 0"
      and step6_sub: "(c5, c6) \<in> ktm_step (ae_delta_ss6_ss7 m M)"
      and step6: "(c5, c6) \<in> ktm_step (alphabet_enlarge_delta m M)"
      and step7_sub: "(c6, c7) \<in> ktm_step (ae_delta_ss7_ss8 m M)"
      and step7: "(c6, c7) \<in> ktm_step (alphabet_enlarge_delta m M)"
      and gamma_c7: "ae_tape_in_gamma_block m M c7"
      and buf_gamma_c7: "ae_buffer_in_gamma_block m M c7"
      and c6_state: "ktc_state c6 = (q6, ofs6, buf6, dest6, SS7)"
      and c7_state: "ktc_state c7 = (q6, ofs6, buf6, dest6, SS8)"
      and buf6_eq_buf5: "buf6 = buf5"
      and q6_eq_q5: "q6 = q5"
      and ofs6_eq_ofs5: "ofs6 = ofs5"
      and dest6_eq_dest5: "dest6 = dest5"
      and c5_pos_for_pos1_dest_left_all:
      "\<forall>kk. kk < k_ktm M \<longrightarrow> ktc_pos c' kk = 1 \<longrightarrow> dest5 kk = AE_Left
      \<longrightarrow> ktc_pos c5 kk = 2"
      and tape_c5_at_one_pos1_all:
      "\<forall>kk. kk < k_ktm M \<longrightarrow> ktc_pos c' kk = 1
      \<longrightarrow> ktc_tape c5 kk 1 = fst (snd (buf5 kk))"
      and c6_pos_for_pos1_dest_left_all:
      "\<forall>kk. kk < k_ktm M \<longrightarrow> ktc_pos c' kk = 1 \<longrightarrow> dest5 kk = AE_Left
      \<longrightarrow> ktc_pos c6 kk = 1"
      and c7_pos_for_pos1_dest_left_all:
      "\<forall>kk. kk < k_ktm M \<longrightarrow> ktc_pos c' kk = 1 \<longrightarrow> dest5 kk = AE_Left
      \<longrightarrow> ktc_pos c7 kk = 0"
      and tape_c7_zero_le_pos1_dest_left_all:
      "\<forall>kk. kk < k_ktm M \<longrightarrow> ktc_pos c' kk = 1 \<longrightarrow> dest5 kk = AE_Left
      \<longrightarrow> ktc_tape c7 kk 0 = LE_block m (le_ktm M)"
      and step8_sub: "(c7, c8) \<in> ktm_step (ae_delta_ss8_ss1 m M)"
      and step8: "(c7, c8) \<in> ktm_step (alphabet_enlarge_delta m M)"
    by (rule ae_forward_stage_step_chain[OF vM le_anchor no_le_per_tape
          tape_corr step1_sub step2_sub step3_sub c_ge_1 c_eq_len
          home_classification c3_pos bl_neq_le step4_sub c4_buf_not_le_per_tape
          inv_ss5 gamma_c4 buf_gamma_c4])
  \<comment> \<open>Recover the \<open>\<And>kk\<close> form of the per-tape facts
      (the chain helper exposes them as \<open>\<forall>kk\<close> to survive
      elim-resolution) so the per-tape
      reconstruction below uses them unchanged.\<close>
  note c4_pos = c4_pos_all[rule_format]
  note c5_pos_for_pos1 = c5_pos_for_pos1_all[rule_format]
  note c5_pos_for_pos1_dest_left = c5_pos_for_pos1_dest_left_all[rule_format]
  note tape_c5_at_one_pos1 = tape_c5_at_one_pos1_all[rule_format]
  note c6_pos_for_pos1_dest_left = c6_pos_for_pos1_dest_left_all[rule_format]
  note c7_pos_for_pos1_dest_left = c7_pos_for_pos1_dest_left_all[rule_format]
  note tape_c7_zero_le_pos1_dest_left = tape_c7_zero_le_pos1_dest_left_all[rule_format]
  \<comment> \<open>Sub-step 6a: chain composition + c8 state shape +
      arm-uniform reconstruction facts (\<open>sim_i\<close>, \<open>sim_ii\<close>, gamma, buf-gamma).
      The chain composition uses \<open>relpow_Suc_I\<close> Suc-by-Suc; the c8
      state shape is the halt-aware \<open>?stage8\<close> let-term from
      \<open>ae_delta_ss8_ss1\<close>.\<close>
  let ?rel = "ktm_step (alphabet_enlarge_delta m M)"
  have chain1: "(c', c1) \<in> ?rel ^^ Suc 0"
    using step1 by simp
  have chain2: "(c', c2) \<in> ?rel ^^ Suc (Suc 0)"
    using chain1 step2 by (rule relpow_Suc_I)
  have chain3: "(c', c3) \<in> ?rel ^^ Suc (Suc (Suc 0))"
    using chain2 step3 by (rule relpow_Suc_I)
  have chain4: "(c', c4) \<in> ?rel ^^ Suc (Suc (Suc (Suc 0)))"
    using chain3 step4 by (rule relpow_Suc_I)
  have chain5: "(c', c5) \<in> ?rel ^^ Suc (Suc (Suc (Suc (Suc 0))))"
    using chain4 step5 by (rule relpow_Suc_I)
  have chain6: "(c', c6) \<in> ?rel ^^ Suc (Suc (Suc (Suc (Suc (Suc 0)))))"
    using chain5 step6 by (rule relpow_Suc_I)
  have chain7:
      "(c', c7) \<in> ?rel ^^ Suc (Suc (Suc (Suc (Suc (Suc (Suc 0))))))"
    using chain6 step7 by (rule relpow_Suc_I)
  have chain8_suc:
      "(c', c8) \<in> ?rel ^^ Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc 0)))))))"
    using chain7 step8 by (rule relpow_Suc_I)
  have chain8: "(c', c8) \<in> ?rel ^^ 8"
    using chain8_suc by (simp add: numeral_eq_Suc)

  let ?stage8 = "if q6 \<in> {t_ktm M, r_ktm M}
                 then init_stage m (le_ktm M)
                 else (ofs6, buf6, init_dest, SS1)"
  have c8_state: "ktc_state c8 = (q6, ?stage8)"
    using step8_sub c7_state
    by (auto simp: ae_delta_ss8_ss1_def elim: ktm_step.cases)

  \<comment> \<open>\<open>sim_i\<close>: state-tuple disjunction at \<open>c8\<close>.  The SS8\<open>\<rightarrow>\<close>SS1
      rule's \<open>?stage'\<close> case-splits on \<open>q \<in> {t_ktm M, r_ktm M}\<close>:
      halt routes to \<open>init_stage le\<close>, non-halt to \<open>(ofs, buf, init_dest, SS1)\<close>.
      The disjunction is XOR-style, with each branch matching one of the
      \<open>ae_simulates\<close>-defining disjuncts directly.\<close>
  have sim_i_c8:
      "case ktc_state c8 of (qq8, ofs8, buf8, dest8, idx8) \<Rightarrow>
           (idx8 = SS1 \<and> qq8 \<notin> {t_ktm M, r_ktm M})
         \<or> (qq8 \<in> {t_ktm M, r_ktm M}
              \<and> (ofs8, buf8, dest8, idx8) = init_stage m (le_ktm M))"
  proof (cases "q6 \<in> {t_ktm M, r_ktm M}")
    case True
    have shape: "?stage8 = init_stage m (le_ktm M)" using True by simp
    have "ktc_state c8 = (q6, init_stage m (le_ktm M))"
      using c8_state shape by simp
    thus ?thesis using True by (simp add: init_stage_def)
  next
    case False
    have shape: "?stage8 = (ofs6, buf6, init_dest, SS1)" using False by simp
    have "ktc_state c8 = (q6, ofs6, buf6, init_dest, SS1)"
      using c8_state shape by simp
    thus ?thesis using False by simp
  qed

  \<comment> \<open>\<open>sim_ii\<close>: \<open>ktc_state cM_k = q6\<close>.  q5 = q6 (no q changes through
      SS5/SS6/SS7); q5 = c4's M-state projection = \<open>ktc_state cM_k\<close>
      (via \<open>c4_q_out\<close> from the trace lemma).\<close>
  have q5_eq_q6: "q5 = q6" using q6_eq_q5 by simp
  have q5_eq_cM_k: "q5 = ktc_state cM_k"
    using c4_q_out c4_state by simp
  have q6_eq_cM_k: "q6 = ktc_state cM_k"
    using q5_eq_q6 q5_eq_cM_k by simp
  have sim_ii_c8:
      "case ktc_state c8 of (qq8, _, _, _, _) \<Rightarrow> ktc_state cM_k = qq8"
    using c8_state q6_eq_cM_k by simp

  \<comment> \<open>gamma + buf-gamma at \<open>c8\<close>: chained preservation.\<close>
  have gamma_c8: "ae_tape_in_gamma_block m M c8"
    using ae_step_alphabet_enlarge_gamma_preserve[OF gamma_c7 step8] .
  have buf_gamma_c8: "ae_buffer_in_gamma_block m M c8"
    using ae_step_alphabet_enlarge_buffer_gamma_preserve[OF step8] .

  \<comment> \<open>The \<open>M\<close> side at \<open>cM_k\<close>: window invariant, endmarker, and the
      tape outside the window (\<open>ae_fwd_m_side_window\<close>).\<close>
  note m_side = ae_fwd_m_side_window[OF tape_corr pos_corr ofs_lt
                  c4_window_general k_le trace c4_state]
  note cM_k_window_general = m_side(1)
    and cM_k_zero = m_side(2)
    and m_tape_off_window_le0 = m_side(3)
    and m_tape_off_window_le1 = m_side(4)
    and m_tape_off_window_steady = m_side(5)

  \<comment> \<open>Head positions after substeps 5 to 8, per regime
      (\<open>ae_fwd_head_positions\<close>).\<close>
  note heads = ae_fwd_head_positions[OF le_anchor no_le_per_tape tape_corr
                 c_ge_1 c_eq_len home_classification bl_neq_le gamma_c4 step5_sub step5 c4_state c5_state tape_c4_eq_c'
                 buf5_not_le_per_tape right_not_le_c' c4_pos_all tape_c5_zero_le
                 c5_pos_for_pos1_all step6_sub step6 step7_sub step7 c6_state
                 c7_state buf6_eq_buf5 dest6_eq_dest5 tape_c5_at_one_pos1_all
                 c6_pos_for_pos1_dest_left_all c7_pos_for_pos1_dest_left_all
                 tape_c7_zero_le_pos1_dest_left_all step8_sub cM_k_window_general]
  note c5_pos_for_pos0 = heads(1)
    and c5_move_for_pos_ge2 = heads(2)
    and c5_pos_for_pos_ge2 = heads(3)
    and c5_pos_for_pos_ge2_dest_left = heads(4)
    and left_not_le_c'_steady = heads(5)
    and buf5_h_le_for_pos0 = heads(6)
    and c6_pos_for_pos0 = heads(7)
    and c6_pos_for_pos_ge2 = heads(8)
    and c7_pos_for_pos0 = heads(9)
    and tape_c5_at_pos_for_pos_ge2 = heads(10)
    and c7_pos_for_pos_ge2 = heads(11)
    and c6_pos_for_pos1 = heads(12)
    and c7_pos_for_pos1 = heads(13)
    and c8_pos_for_pos0 = heads(14)
    and c8_pos_for_pos_ge2 = heads(15)
    and c8_pos_for_pos1 = heads(16)
  \<comment> \<open>Tape contents at \<open>c8\<close> (\<open>ae_fwd_cells_c8\<close>).\<close>
  \<comment> \<open>The arm's rule-shaped premises leave their hypotheses as premises
      of \<open>cells\<close>; \<open>rule\<close> discharges them by assumption.\<close>
  note cells = ae_fwd_cells_c8[OF tape_corr c_ge_1 step5 c5_state tape_c4_eq_c'
                 buf5_not_le_per_tape right_not_le_c' c4_pos_all tape_c5_zero_le
                 c5_pos_for_pos1_all step6_sub step6 step7_sub step7 c6_state
                 c7_state buf6_eq_buf5 dest6_eq_dest5
                 c5_pos_for_pos1_dest_left_all tape_c5_at_one_pos1_all
                 c7_pos_for_pos1_dest_left_all step8_sub step8
                 cM_k_window_general cM_k_zero m_tape_off_window_le0
                 m_tape_off_window_le1 m_tape_off_window_steady c5_pos_for_pos0
                 c5_move_for_pos_ge2 c5_pos_for_pos_ge2
                 c5_pos_for_pos_ge2_dest_left left_not_le_c'_steady
                 buf5_h_le_for_pos0 c6_pos_for_pos0 c6_pos_for_pos_ge2
                 c7_pos_for_pos0 tape_c5_at_pos_for_pos_ge2 c7_pos_for_pos_ge2
                 c6_pos_for_pos1 c7_pos_for_pos1]
  have tape_c8_zero_le: "\<forall>kk<k_ktm M. ktc_tape c8 kk 0 = LE_block m (le_ktm M)"
    by (rule cells(1))
  have tape_corr_c8: "\<forall>kk<k_ktm M. ae_tape_correspondence m (le_ktm M)
                         (ktc_tape cM_k kk) (ktc_tape c8 kk)"
    by (rule cells(2))
  \<comment> \<open>Sub-step 6c: position decode at \<open>c8\<close>.  Per-tape regime
      case-split on \<open>ktc_pos c' kk\<close>, then per-dest case-split.
      The \<open>idx = SS1\<close> antecedent excludes the halt branch
      (which lands at \<open>init_stage\<close> = VFwd).  Extracted to
      \<open>ae_fwd_pos_decode_c8\<close>.\<close>
  have pos_decode_c8:
      "(case ktc_state c8 of (_, _, _, _, idx) \<Rightarrow> idx = SS1)
        \<longrightarrow> (\<forall>k<k_ktm M. ktc_pos cM_k k
                  = ae_decode_pos m (ktc_pos c8 k)
                      (case ktc_state c8 of (_, off, _, _, _) \<Rightarrow> off k))"
    by (rule ae_fwd_pos_decode_c8[OF ofs6_eq_ofs5 c8_state cM_k_window_general
          c8_pos_for_pos0 c8_pos_for_pos_ge2 c8_pos_for_pos1])
  \<comment> \<open>Sub-step 6f: final assembly via \<open>rule that\<close>.  The four
      obligations of the \<open>obtains\<close>: chain composition (\<open>chain8\<close>),
      \<open>ae_simulates M cM_k c8\<close> (the four per-conjunct facts
      \<open>conj_i\<close>, \<open>conj_ii\<close>, \<open>tape_corr_c8\<close>,
      \<open>pos_decode_c8\<close>, plus gamma and buf-gamma side-bands),
      \<open>ae_buffer_in_gamma_block M c8\<close>, and \<open>c8\<close> cell 0 is
      \<open>LE_block\<close>.\<close>
  \<comment> \<open>SS5 exposure (det-free reverse direction): the SS5 state in
      \<open>(q_out, ofs, buf, dest)\<close> form (\<open>q_out = ktc_state cM_k\<close> via
      \<open>c4_q_out\<close>) and the window correspondence in \<open>(dest, ofs)\<close>
      bp form (from \<open>c4_window_general\<close> under \<open>c4_state\<close>).\<close>
  have q5_eq: "q5 = ktc_state cM_k"
    using c4_q_out c4_state by simp
  have c4f_state_exp: "ktc_state c4 = (ktc_state cM_k, ofs5, buf5, dest5, SS5)"
    using c4_state q5_eq by simp
  have fwd_window_exp:
      "\<forall>kk<k_ktm M. ae_window_invariant_general m
              (ktc_tape cM_k kk) (ktc_pos cM_k kk)
              (dest5 kk, ofs5 kk) (buf5 kk) (ktc_pos c' kk) (le_ktm M)"
    using c4_window_general c4_state by simp

  obtain qq8 ofs8 buf8 dest8 idx8 where
      c8_full: "ktc_state c8 = (qq8, ofs8, buf8, dest8, idx8)"
    by (cases "ktc_state c8") auto
  have conj_i:
      "(idx8 = SS1 \<and> qq8 \<notin> {t_ktm M, r_ktm M})
        \<or> (qq8 \<in> {t_ktm M, r_ktm M}
             \<and> (ofs8, buf8, dest8, idx8) = init_stage m (le_ktm M))"
    using sim_i_c8 c8_full by simp
  have conj_ii: "ktc_state cM_k = qq8"
    using sim_ii_c8 c8_full by simp
  have conj_iv:
      "idx8 = SS1
        \<longrightarrow> (\<forall>k<k_ktm M. ktc_pos cM_k k = ae_decode_pos m (ktc_pos c8 k) (ofs8 k))"
    using pos_decode_c8 c8_full by simp
  have sim_c8: "ae_simulates m M cM_k c8"
    unfolding ae_simulates_def
    using conj_i conj_ii conj_iv tape_corr_c8 gamma_c8 c8_full
    by simp

  show ?thesis
    by (rule that[OF chain8 sim_c8 buf_gamma_c8 tape_c8_zero_le
                     step1_sub step2_sub step3_sub step4_sub
                     step5_sub step6_sub step7_sub step8_sub
                     c4f_state_exp fwd_window_exp buf_gamma_c4])
qed

end
