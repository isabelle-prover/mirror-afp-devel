theory AlphabetEnlargement_OutputWF
  imports AlphabetEnlargement_SS4
begin

subsection \<open>Home classification and output well-formedness\<close>

subsubsection \<open>Home classification, stage unpack, load chain\<close>

text \<open>Per-tape home-cell LE-classification at SS1.  Given the
  M\<open>\<leftrightarrow>\<close>M' tape correspondence (extracted from
  \<open>ae_simulates\<close>), the LE anchor on tape 0, and the
  no-LE-window invariant on \<open>cM\<close>'s tape, the home block
  of \<open>c'\<close>'s tape \<open>k\<close> equals \<open>LE_block (le_tm M)\<close>
  iff \<open>mt_pos c' k = 0\<close>.  Direction-agnostic; consumed by
  both arms of the SS4-stage setup (the forward arm uses it to
  drive \<open>ae_ss1_to_ss4_buffer_chars_general\<close>'s
  \<open>home_class\<close> hypothesis; the reverse arm uses it for the
  symmetric extraction).\<close>

lemma ae_home_classification:
  fixes M :: "('q, 'a) mttm"
    and cM :: "('a, 'q) mt_config"
    and c' :: "('c :: enum \<Rightarrow> 'a,
                'q \<times> ('a, 'c) ae_stage) mt_config"
  assumes le_anchor:   "\<forall>k<k_tm M. mt_tape c' k 0 = LE_block (le_tm M)"
      and no_le_per_tape:
            "\<forall>k. (mt_pos c' k \<ge> 2
                    \<longrightarrow> (\<forall>i. i < 3 * card (UNIV :: 'c set)
                              \<longrightarrow> mt_tape cM k
                                    ((mt_pos c' k - 2)
                                       * card (UNIV :: 'c set) + 1 + i)
                                  \<noteq> le_tm M))
                 \<and> (mt_pos c' k = 1
                      \<longrightarrow> (\<forall>i. i < 2 * card (UNIV :: 'c set)
                                \<longrightarrow> mt_tape cM k (Suc i) \<noteq> le_tm M))
                 \<and> (mt_pos c' k = 0
                      \<longrightarrow> (\<forall>i. i < card (UNIV :: 'c set)
                                \<longrightarrow> mt_tape cM k (Suc i) \<noteq> le_tm M))"
      and tape_corr:
            "\<forall>k<k_tm M. ae_tape_correspondence (le_tm M)
                    (mt_tape cM k) (mt_tape c' k)"
    shows "\<forall>k<k_tm M. (mt_pos c' k = 0
                  \<longrightarrow> mt_tape c' k (mt_pos c' k) = LE_block (le_tm M))
              \<and> (mt_pos c' k \<ge> 1
                  \<longrightarrow> mt_tape c' k (mt_pos c' k) \<noteq> LE_block (le_tm M))"
proof (intro allI impI conjI)
  fix k :: nat
  assume klt: "k < k_tm M" and pos0: "mt_pos c' k = 0"
  have "mt_tape c' k 0 = LE_block (le_tm M)" using le_anchor klt by blast
  thus "mt_tape c' k (mt_pos c' k) = LE_block (le_tm M)"
    using pos0 by simp
next
  fix k :: nat
  assume klt: "k < k_tm M" and pos_ge1: "1 \<le> mt_pos c' k"
  have c_ge_1: "1 \<le> card (UNIV :: 'c set)"
    using c_idx_lt_card[of "SOME x :: 'c. True"] by simp
  have c_eq_len:
      "card (UNIV :: 'c set) = length (enum_class.enum :: 'c list)"
    using enum_class.UNIV_enum enum_class.enum_distinct
    by (metis distinct_card length_remdups_card_conv set_remdups)
  let ?x = "(enum_class.enum :: 'c list) ! 0"
  have zero_lt_len: "0 < length (enum_class.enum :: 'c list)"
    using c_ge_1 c_eq_len by linarith
  have x_idx0: "c_idx ?x = 0"
    using c_idx_enum_nth[OF zero_lt_len] .
  have tc_k: "ae_tape_correspondence (le_tm M)
                  (mt_tape cM k) (mt_tape c' k)"
    using tape_corr klt by blast
  have addr_lit:
      "mt_tape cM k
          ((mt_pos c' k - 1) * card (UNIV :: 'c set) + c_idx ?x + 1)
        = mt_tape c' k (mt_pos c' k) ?x"
    using tc_k[unfolded ae_tape_correspondence_def, THEN conjunct2,
               rule_format, OF pos_ge1, of ?x] .
  have addr_via_tc:
      "mt_tape cM k ((mt_pos c' k - 1) * card (UNIV :: 'c set) + 1)
        = mt_tape c' k (mt_pos c' k) ?x"
    using addr_lit x_idx0 by simp
  consider (eq1) "mt_pos c' k = 1" | (ge2) "mt_pos c' k \<ge> 2"
    using pos_ge1 by linarith
  hence "mt_tape c' k (mt_pos c' k) ?x \<noteq> le_tm M"
  proof cases
    case eq1
    have idx_lt: "(0 :: nat) < 2 * card (UNIV :: 'c set)"
      using c_ge_1 by simp
    have addr_at_1:
        "mt_tape cM k (Suc 0) = mt_tape c' k (mt_pos c' k) ?x"
      using addr_via_tc eq1 by simp
    have nle_at_1: "mt_tape cM k (Suc 0) \<noteq> le_tm M"
      using no_le_per_tape eq1 idx_lt by blast
    thus ?thesis using addr_at_1 by simp
  next
    case ge2
    let ?j = "card (UNIV :: 'c set)"
    have j_lt_3c: "?j < 3 * card (UNIV :: 'c set)"
      using c_ge_1 by simp
    have addr_eq:
        "(mt_pos c' k - 1) * card (UNIV :: 'c set) + 1
          = (mt_pos c' k - 2) * card (UNIV :: 'c set) + 1 + ?j"
      using ge2 by (simp add: algebra_simps diff_mult_distrib)
    have nle_at_addr:
        "mt_tape cM k ((mt_pos c' k - 2) * card (UNIV :: 'c set) + 1 + ?j)
          \<noteq> le_tm M"
      using no_le_per_tape ge2 j_lt_3c by blast
    hence "mt_tape cM k ((mt_pos c' k - 1) * card (UNIV :: 'c set) + 1)
            \<noteq> le_tm M"
      using addr_eq by simp
    thus ?thesis using addr_via_tc by simp
  qed
  thus "mt_tape c' k (mt_pos c' k) \<noteq> LE_block (le_tm M)"
    unfolding LE_block_def by auto
qed

text \<open>Auxiliary: unpack the \<open>ae_simulates\<close> invariant at SS1
  entry into the structural data forward-stage proofs need.
  Extracts \<open>M'\<close>'s state-tuple shape (with \<open>idx = SS1\<close> pinned
  by the M-state not-halted hypothesis), the \<open>M\<close>-state equality,
  the M\<open>\<leftrightarrow>\<close>M' tape and position correspondences, the gamma-block
  side-band, the SS1 substrate invariant, and the (vacuous-at-SS1)
  position-link.  All three forward-stage variants —
  steady-state and the two head-LE arms \<open>le0\<close>, \<open>le1\<close>
  — open with this same unpacking; factoring it out keeps
  the variants from cloning ~47 lines of preamble apiece.\<close>

lemma ae_forward_stage_unpack_sim:
  fixes M :: "('q, 'a) mttm"
    and cM :: "('a, 'q) mt_config"
    and c' :: "('c :: enum \<Rightarrow> 'a,
                'q \<times> ('a, 'c) ae_stage) mt_config"
  assumes sim:       "ae_simulates M cM c'"
      and qM_in_Q:   "mt_state cM \<in> Q_tm M"
      and q_neq_t:   "mt_state cM \<noteq> t_tm M"
      and q_neq_r:   "mt_state cM \<noteq> r_tm M"
  obtains qM' ofs buf dest where
      "mt_state c' = (qM', ofs, buf, dest, SS1)"
    and "mt_state cM = qM'"
    and "qM' \<in> Q_tm M"
    and "qM' \<noteq> t_tm M"
    and "qM' \<noteq> r_tm M"
    and "\<forall>k<k_tm M. ae_tape_correspondence (le_tm M)
              (mt_tape cM k) (mt_tape c' k)"
    and "\<forall>k<k_tm M. mt_pos cM k = ae_decode_pos (mt_pos c' k) (ofs k)"
    and "ae_tape_in_gamma_block M c'"
    and "ae_inv_ss1 M c'"
    and "ae_position_link M c'"
proof -
  obtain qM' ofs buf dest idx_init where
      state_comp: "mt_state c' = (qM', ofs, buf, dest, idx_init)"
    by (cases "mt_state c'")
  have sim_body:
      "((idx_init = SS1 \<and> qM' \<notin> {t_tm M, r_tm M})
          \<or> (qM' \<in> {t_tm M, r_tm M}
               \<and> (ofs, buf, dest, idx_init) = init_stage (le_tm M)))
       \<and> mt_state cM = qM'
       \<and> (\<forall>k<k_tm M. ae_tape_correspondence (le_tm M)
                 (mt_tape cM k) (mt_tape c' k))
       \<and> (idx_init = SS1
            \<longrightarrow> (\<forall>k<k_tm M. mt_pos cM k = ae_decode_pos (mt_pos c' k) (ofs k)))
       \<and> ae_tape_in_gamma_block M c'"
    using sim state_comp unfolding ae_simulates_def by simp
  have qM_eq: "mt_state cM = qM'" using sim_body by simp
  have qM'_neq_t: "qM' \<noteq> t_tm M" using qM_eq q_neq_t by simp
  have qM'_neq_r: "qM' \<noteq> r_tm M" using qM_eq q_neq_r by simp
  have idx_is_ss1: "idx_init = SS1"
    using sim_body qM'_neq_t qM'_neq_r by auto
  have c'_state: "mt_state c' = (qM', ofs, buf, dest, SS1)"
    using state_comp idx_is_ss1 by simp
  have tape_corr:
      "\<forall>k<k_tm M. ae_tape_correspondence (le_tm M)
              (mt_tape cM k) (mt_tape c' k)"
    using sim_body by simp
  have pos_corr:
      "\<forall>k<k_tm M. mt_pos cM k = ae_decode_pos (mt_pos c' k) (ofs k)"
    using sim_body idx_is_ss1 by simp
  have gamma_c': "ae_tape_in_gamma_block M c'"
    using sim_body by simp
  have qM'_in_Q: "qM' \<in> Q_tm M"
    using qM_in_Q qM_eq by simp
  have inv_ss1: "ae_inv_ss1 M c'"
    unfolding ae_inv_ss1_def using c'_state qM'_in_Q by simp
  have pos_link_c': "ae_position_link M c'"
    using c'_state unfolding ae_position_link_def by simp
  show ?thesis
    by (rule that[OF c'_state qM_eq qM'_in_Q qM'_neq_t qM'_neq_r
                     tape_corr pos_corr gamma_c' inv_ss1 pos_link_c'])
qed

text \<open>Auxiliary: the three buffer-load substeps SS1
  \<open>\<rightarrow>\<close> SS2 \<open>\<rightarrow>\<close> SS3 \<open>\<rightarrow>\<close> SS4 as a
  single chained existence lemma.  Threads invariant preservation,
  gamma preservation (tape + buffer), M-state propagation, and
  position-link propagation across the three substeps; produces
  the SS4-entry configuration \<open>c3\<close> with all the structural
  facts forward-stage proofs need before reaching the c-fold
  compute substep.

  The block is arm-uniform: it depends only on the SS1 invariant
  and the gamma side-band, not on the head's block position
  or the no-LE window structure.  All three forward-stage variants
  — steady-state and the head-LE arms \<open>le0\<close>,
  \<open>le1\<close> — share this load chain verbatim;
  factoring it out keeps the variants from cloning ~122 lines of
  preservation plumbing apiece.

  Position-link propagation through the load chain rests on the
  pre-state's idx being SS1, SS2, SS3 respectively at each
  substep, which keeps all three aux-void lemmas
  (\<open>ae_pos_link_aux_void_ss<N>_ss<M>\<close>) vacuously
  satisfied.\<close>

lemma ae_forward_stage_load_chain:
  fixes M :: "('q, 'a) mttm"
    and c' :: "('c :: enum \<Rightarrow> 'a,
                'q \<times> ('a, 'c) ae_stage) mt_config"
    and qM' :: 'q
    and ofs :: "nat \<Rightarrow> 'c"
    and buf :: "nat \<Rightarrow> ('c \<Rightarrow> 'a) \<times> ('c \<Rightarrow> 'a) \<times> ('c \<Rightarrow> 'a)"
    and dest :: "nat \<Rightarrow> ae_dest"
  assumes vM:          "valid_mttm M"
      and c'_state:    "mt_state c' = (qM', ofs, buf, dest, SS1)"
      and inv_ss1:     "ae_inv_ss1 M c'"
      and gamma_c':    "ae_tape_in_gamma_block M c'"
      and buf_gamma:   "ae_buffer_in_gamma_block M c'"
      and pos_link_c': "ae_position_link M c'"
      and qM'_neq_t:   "qM' \<noteq> t_tm M"
      and qM'_neq_r:   "qM' \<noteq> r_tm M"
  obtains c1 c2 c3 where
      "(c', c1) \<in> mttm_step (ae_delta_ss1_ss2 M)"
    and "(c', c1) \<in> mttm_step (alphabet_enlarge_delta M)"
    and "(c1, c2) \<in> mttm_step (ae_delta_ss2_ss3 M)"
    and "(c1, c2) \<in> mttm_step (alphabet_enlarge_delta M)"
    and "(c2, c3) \<in> mttm_step (ae_delta_ss3_ss4 M)"
    and "(c2, c3) \<in> mttm_step (alphabet_enlarge_delta M)"
    and "ae_inv_ss4 M c3"
    and "ae_tape_in_gamma_block M c3"
    and "ae_buffer_in_gamma_block M c3"
    and "fst (mt_state c3) = qM'"
    and "ae_position_link M c3"
proof -
  have c'_fst_neq_t: "fst (mt_state c') \<noteq> t_tm M"
    using c'_state qM'_neq_t by simp
  have c'_fst_neq_r: "fst (mt_state c') \<noteq> r_tm M"
    using c'_state qM'_neq_r by simp
  \<comment> \<open>Substep 1: SS1\<open>\<rightarrow>\<close>SS2.\<close>
  obtain c1 where
      step1_sub: "(c', c1) \<in> mttm_step (ae_delta_ss1_ss2 M)"
    and step1: "(c', c1) \<in> mttm_step (alphabet_enlarge_delta M)"
    using ae_step_ss1_ss2_exists[OF inv_ss1 gamma_c' buf_gamma
                                    c'_fst_neq_t c'_fst_neq_r] by blast
  have inv_ss2: "ae_inv_ss2 M c1"
    using ae_step_ss1_ss2_invariant[OF vM inv_ss1 step1_sub] .
  have gamma_c1: "ae_tape_in_gamma_block M c1"
    using ae_step_alphabet_enlarge_gamma_preserve[OF gamma_c' step1] .
  have buf_gamma_c1: "ae_buffer_in_gamma_block M c1"
    using ae_step_alphabet_enlarge_buffer_gamma_preserve[OF vM buf_gamma
                                                            gamma_c' step1] .
  have c1_fst_eq: "fst (mt_state c1) = qM'"
    using step1_sub c'_state
    by (auto simp: ae_delta_ss1_ss2_def elim: mttm_step.cases)
  have c1_fst_neq_t: "fst (mt_state c1) \<noteq> t_tm M"
    using c1_fst_eq qM'_neq_t by simp
  have c1_fst_neq_r: "fst (mt_state c1) \<noteq> r_tm M"
    using c1_fst_eq qM'_neq_r by simp
  have c'_idx_ss1: "snd (snd (snd (snd (mt_state c')))) = SS1"
    using c'_state by simp
  have aux_45_at_c': "(c', c1) \<in> mttm_step (ae_delta_ss4_ss5 M)
                        \<Longrightarrow> ae_position_link M c1"
    using ae_pos_link_aux_void_ss4_ss5[where M = M and c_pre = c' and c_post = c1]
          c'_idx_ss1 by simp
  have aux_56_at_c': "(c', c1) \<in> mttm_step (ae_delta_ss5_ss6 M)
                        \<Longrightarrow> ae_position_link M c1"
    using ae_pos_link_aux_void_ss5_ss6[where M = M and c_pre = c' and c_post = c1]
          c'_idx_ss1 by simp
  have aux_78_at_c': "(c', c1) \<in> mttm_step (ae_delta_ss7_ss8 M)
                        \<Longrightarrow> ae_position_link M c1"
    using ae_pos_link_aux_void_ss7_ss8[where M = M and c_pre = c' and c_post = c1]
          c'_idx_ss1 by simp
  have pos_link_c1: "ae_position_link M c1"
    using ae_step_alphabet_enlarge_position_link_preserve[OF pos_link_c'
            step1 aux_45_at_c' aux_56_at_c' aux_78_at_c'] .
  \<comment> \<open>Substep 2: SS2\<open>\<rightarrow>\<close>SS3.\<close>
  obtain c2 where
      step2_sub: "(c1, c2) \<in> mttm_step (ae_delta_ss2_ss3 M)"
    and step2: "(c1, c2) \<in> mttm_step (alphabet_enlarge_delta M)"
    using ae_step_ss2_ss3_exists[OF vM inv_ss2 gamma_c1 buf_gamma_c1
                                    c1_fst_neq_t c1_fst_neq_r] by blast
  have inv_ss3: "ae_inv_ss3 M c2"
    using ae_step_ss2_ss3_invariant[OF vM inv_ss2 step2_sub] .
  have gamma_c2: "ae_tape_in_gamma_block M c2"
    using ae_step_alphabet_enlarge_gamma_preserve[OF gamma_c1 step2] .
  have buf_gamma_c2: "ae_buffer_in_gamma_block M c2"
    using ae_step_alphabet_enlarge_buffer_gamma_preserve[OF vM buf_gamma_c1
                                                            gamma_c1 step2] .
  have c2_fst_eq: "fst (mt_state c2) = qM'"
    using step2_sub c1_fst_eq
    by (cases "mt_state c1")
       (auto simp: ae_delta_ss2_ss3_def elim: mttm_step.cases)
  have c2_fst_neq_t: "fst (mt_state c2) \<noteq> t_tm M"
    using c2_fst_eq qM'_neq_t by simp
  have c2_fst_neq_r: "fst (mt_state c2) \<noteq> r_tm M"
    using c2_fst_eq qM'_neq_r by simp
  have c1_idx_ss2: "snd (snd (snd (snd (mt_state c1)))) = SS2"
    using inv_ss2 unfolding ae_inv_ss2_def by (cases "mt_state c1") auto
  have aux_45_at_c1: "(c1, c2) \<in> mttm_step (ae_delta_ss4_ss5 M)
                        \<Longrightarrow> ae_position_link M c2"
    using ae_pos_link_aux_void_ss4_ss5[where M = M and c_pre = c1 and c_post = c2]
          c1_idx_ss2 by simp
  have aux_56_at_c1: "(c1, c2) \<in> mttm_step (ae_delta_ss5_ss6 M)
                        \<Longrightarrow> ae_position_link M c2"
    using ae_pos_link_aux_void_ss5_ss6[where M = M and c_pre = c1 and c_post = c2]
          c1_idx_ss2 by simp
  have aux_78_at_c1: "(c1, c2) \<in> mttm_step (ae_delta_ss7_ss8 M)
                        \<Longrightarrow> ae_position_link M c2"
    using ae_pos_link_aux_void_ss7_ss8[where M = M and c_pre = c1 and c_post = c2]
          c1_idx_ss2 by simp
  have pos_link_c2: "ae_position_link M c2"
    using ae_step_alphabet_enlarge_position_link_preserve[OF pos_link_c1
            step2 aux_45_at_c1 aux_56_at_c1 aux_78_at_c1] .
  \<comment> \<open>Substep 3: SS3\<open>\<rightarrow>\<close>SS4.\<close>
  obtain c3 where
      step3_sub: "(c2, c3) \<in> mttm_step (ae_delta_ss3_ss4 M)"
    and step3: "(c2, c3) \<in> mttm_step (alphabet_enlarge_delta M)"
    using ae_step_ss3_ss4_exists[OF inv_ss3 gamma_c2 buf_gamma_c2
                                    c2_fst_neq_t c2_fst_neq_r] by blast
  have inv_ss4: "ae_inv_ss4 M c3"
    using ae_step_ss3_ss4_invariant[OF vM inv_ss3 step3_sub] .
  have gamma_c3: "ae_tape_in_gamma_block M c3"
    using ae_step_alphabet_enlarge_gamma_preserve[OF gamma_c2 step3] .
  have buf_gamma_c3: "ae_buffer_in_gamma_block M c3"
    using ae_step_alphabet_enlarge_buffer_gamma_preserve[OF vM buf_gamma_c2
                                                            gamma_c2 step3] .
  have c3_fst_eq: "fst (mt_state c3) = qM'"
    using step3_sub c2_fst_eq
    by (cases "mt_state c2")
       (auto simp: ae_delta_ss3_ss4_def elim: mttm_step.cases)
  have c2_idx_ss3: "snd (snd (snd (snd (mt_state c2)))) = SS3"
    using inv_ss3 unfolding ae_inv_ss3_def by (cases "mt_state c2") auto
  have aux_45_at_c2: "(c2, c3) \<in> mttm_step (ae_delta_ss4_ss5 M)
                        \<Longrightarrow> ae_position_link M c3"
    using ae_pos_link_aux_void_ss4_ss5[where M = M and c_pre = c2 and c_post = c3]
          c2_idx_ss3 by simp
  have aux_56_at_c2: "(c2, c3) \<in> mttm_step (ae_delta_ss5_ss6 M)
                        \<Longrightarrow> ae_position_link M c3"
    using ae_pos_link_aux_void_ss5_ss6[where M = M and c_pre = c2 and c_post = c3]
          c2_idx_ss3 by simp
  have aux_78_at_c2: "(c2, c3) \<in> mttm_step (ae_delta_ss7_ss8 M)
                        \<Longrightarrow> ae_position_link M c3"
    using ae_pos_link_aux_void_ss7_ss8[where M = M and c_pre = c2 and c_post = c3]
          c2_idx_ss3 by simp
  have pos_link_c3: "ae_position_link M c3"
    using ae_step_alphabet_enlarge_position_link_preserve[OF pos_link_c2
            step3 aux_45_at_c2 aux_56_at_c2 aux_78_at_c2] .
  show ?thesis
    by (rule that[OF step1_sub step1 step2_sub step2 step3_sub step3
                     inv_ss4 gamma_c3 buf_gamma_c3 c3_fst_eq pos_link_c3])
qed


subsubsection \<open>Output well-formedness theorem\<close>

text \<open>Output well-formedness: \<open>alphabet_enlarge\<close> maps a valid
  substrate machine to a valid one, i.e.
  \<open>valid_mttm M \<Longrightarrow> valid_mttm (alphabet_enlarge M)\<close>.
  Every component of \<open>alphabet_enlarge M\<close> is derived from
  \<open>M\<close>'s: the state set is \<open>Q_tm M\<close> paired with the finite
  set of valid simulation stages, the tape alphabet is the block
  alphabet \<open>gamma_block (\<Gamma>_tm M)\<close>, and the input
  alphabet, endmarkers, and start/accept/reject states are the
  corresponding block-encoded images.  The proof discharges each
  \<open>valid_mttm\<close> conjunct (finiteness of the state and
  alphabet sets, \<open>\<Sigma> \<subseteq> \<Gamma>\<close>, blank- and
  endmarker-membership, and the LE-discipline on
  \<open>alphabet_enlarge_delta\<close>) from \<open>M\<close>'s.

  This is the structural precondition the headline results build
  on: \<open>alphabet_enlarge_time\<close> and the language theorems
  (\<open>alphabet_enlarge_language_forward\<close> here, the
  biconditional \<open>alphabet_enlarge_language\<close> in
  \<open>AlphabetEnlargement_Reverse.thy\<close>) all reason about runs
  of \<open>alphabet_enlarge M\<close>, which first requires it to be a
  well-formed substrate object.\<close>

text \<open>State-shape projection of \<open>alphabet_enlarge_delta\<close>: every
  transition's source and destination carry an \<open>M\<close>-state in
  \<open>Q_tm M\<close>, and the source is neither the lifted accept nor the
  lifted reject state \<open>(t_tm M, init_stage le)\<close> /
  \<open>(r_tm M, init_stage le)\<close>.  Read off the 16 substep builders by
  their explicit \<open>q \<in> Q_tm M\<close> / substep-index discipline
  (\<open>m_steps_buffered_state_preservation\<close> supplies the
  SS4\<open>\<rightarrow>\<close>SS5 destination \<open>q'\<close>).  Crucially the proof touches only
  the discrete state components, never the guarded per-tape lambdas, so
  no \<open>split: if_splits\<close> is needed — that split, applied to the
  \<open>if k < k_tm M\<close> tape count guards across all 16 unfolded builders, is
  what made the monolithic \<open>\<delta>\<close>-shape \<open>auto\<close> in
  \<open>alphabet_enlarge_wf\<close> loop.  The gamma-codomain and
  \<open>ae_valid_stage\<close> halves of that \<open>\<delta>\<close>-shape conjunct come
  straight off \<open>alphabet_enlarge_delta\<close>'s intersection guards
  instead.\<close>

lemma alphabet_enlarge_delta_state_shape:
  fixes M :: "('q, 'a) mttm"
  assumes valM: "valid_mttm M"
      and mem: "(s, a, s', a', d) \<in> alphabet_enlarge_delta M"
  shows "fst s \<in> Q_tm M \<and> fst s' \<in> Q_tm M
         \<and> s \<noteq> (t_tm M, init_stage (le_tm M))
         \<and> s \<noteq> (r_tm M, init_stage (le_tm M))"
proof -
  from mem have mem_u:
    "(s, a, s', a', d) \<in>
       ae_delta_val_fwd_advance M \<union> ae_delta_val_fwd_to_padded M
       \<union> ae_delta_val_fwd_reject M \<union> ae_delta_val_fwd_to_ret M
       \<union> ae_delta_val_pad_to_ret M \<union> ae_delta_val_pad_reject M
       \<union> ae_delta_val_ret_step M \<union> ae_delta_val_ret_to_sim M
       \<union> ae_delta_ss1_ss2 M \<union> ae_delta_ss2_ss3 M
       \<union> ae_delta_ss3_ss4 M \<union> ae_delta_ss4_ss5 M
       \<union> ae_delta_ss5_ss6 M \<union> ae_delta_ss6_ss7 M
       \<union> ae_delta_ss7_ss8 M \<union> ae_delta_ss8_ss1 M"
    unfolding alphabet_enlarge_delta_def by blast
  show ?thesis
    using mem_u
    unfolding ae_delta_val_fwd_advance_def ae_delta_val_fwd_to_padded_def
              ae_delta_val_fwd_reject_def ae_delta_val_fwd_to_ret_def
              ae_delta_val_pad_to_ret_def ae_delta_val_pad_reject_def
              ae_delta_val_ret_step_def ae_delta_val_ret_to_sim_def
              ae_delta_ss1_ss2_def ae_delta_ss2_ss3_def
              ae_delta_ss3_ss4_def ae_delta_ss4_ss5_def
              ae_delta_ss5_ss6_def ae_delta_ss6_ss7_def
              ae_delta_ss7_ss8_def ae_delta_ss8_ss1_def
              init_stage_def
    using m_steps_buffered_state_preservation[OF valM]
          valid_mttm_r_in_Q[OF valM] valid_mttm_t_in_Q[OF valM]
    by auto
qed

theorem alphabet_enlarge_wf:
  fixes M :: "('q, 'a) mttm"
  assumes valM: "valid_mttm M"
  shows "valid_mttm
           (alphabet_enlarge M
              :: ('q \<times> ('a, ('c :: enum)) ae_stage, 'c \<Rightarrow> 'a) mttm)"
proof -
  obtain Q\<^sub>M \<Sigma>\<^sub>M \<Gamma>\<^sub>M bl\<^sub>M le\<^sub>M \<delta>\<^sub>M s\<^sub>M t\<^sub>M r\<^sub>M k\<^sub>M where
    M_eq: "M = MTTM Q\<^sub>M \<Sigma>\<^sub>M \<Gamma>\<^sub>M bl\<^sub>M le\<^sub>M \<delta>\<^sub>M s\<^sub>M t\<^sub>M r\<^sub>M k\<^sub>M"
    using mttm.exhaust by metis

  have fin_Gamma: "finite \<Gamma>\<^sub>M"
    using valid_mttm_finite_Gamma[OF valM] M_eq by simp
  have le_in_Gamma: "le\<^sub>M \<in> \<Gamma>\<^sub>M"
    using valid_mttm_LE_in_Gamma[OF valM] M_eq by simp

  have ae_eq: "(alphabet_enlarge M
                  :: ('q \<times> ('a, 'c) ae_stage, 'c \<Rightarrow> 'a) mttm) =
                MTTM (Q\<^sub>M \<times> {stg. ae_valid_stage \<Gamma>\<^sub>M le\<^sub>M k\<^sub>M stg})
                     (gamma_block (\<Sigma>\<^sub>M \<union> {bl\<^sub>M})
                        - {bl_block bl\<^sub>M, LE_block le\<^sub>M})
                     (gamma_block \<Gamma>\<^sub>M)
                     (bl_block bl\<^sub>M)
                     (LE_block le\<^sub>M)
                     (alphabet_enlarge_delta M)
                     (s\<^sub>M, init_stage le\<^sub>M)
                     (t\<^sub>M, init_stage le\<^sub>M)
                     (r\<^sub>M, init_stage le\<^sub>M)
                     k\<^sub>M"
    unfolding M_eq alphabet_enlarge_def by simp

  have init_valid: "ae_valid_stage \<Gamma>\<^sub>M le\<^sub>M k\<^sub>M (init_stage le\<^sub>M)"
    by (rule ae_valid_stage_init[OF le_in_Gamma])

  show "valid_mttm
           (alphabet_enlarge M
              :: ('q \<times> ('a, ('c :: enum)) ae_stage, 'c \<Rightarrow> 'a) mttm)"
    unfolding ae_eq valid_mttm.simps
  proof (intro conjI)
    \<comment> \<open>(0) \<open>0 < k\<close>: enlargement keeps \<open>M\<close>'s tape count.\<close>
    show "0 < k\<^sub>M"
      using valid_mttm_k_pos[OF valM] M_eq by simp

    \<comment> \<open>(1) finite Q'\<close>
    show "finite (Q\<^sub>M \<times>
                    ({stg. ae_valid_stage \<Gamma>\<^sub>M le\<^sub>M k\<^sub>M stg}
                       :: ('a, 'c) ae_stage set))"
      using valid_mttm_finite_Q[OF valM] M_eq
            finite_ae_valid_stages[OF fin_Gamma]
      by (auto intro: finite_cartesian_product)

    \<comment> \<open>(2) finite \<open>\<Gamma>'\<close>\<close>
    show "finite (gamma_block \<Gamma>\<^sub>M :: ('c \<Rightarrow> 'a) set)"
      using valid_mttm_finite_Gamma[OF valM] M_eq
      by (auto intro: finite_gamma_block)

    \<comment> \<open>(3) \<open>\<Sigma>' \<subseteq> \<Gamma>'\<close>\<close>
    show "gamma_block (\<Sigma>\<^sub>M \<union> {bl\<^sub>M}) - {bl_block bl\<^sub>M, LE_block le\<^sub>M}
            \<subseteq> gamma_block \<Gamma>\<^sub>M"
    proof -
      have "\<Sigma>\<^sub>M \<union> {bl\<^sub>M} \<subseteq> \<Gamma>\<^sub>M"
        using valid_mttm_Sigma_sub_Gamma[OF valM] valid_mttm_blank_in_Gamma[OF valM] M_eq
        by auto
      hence "gamma_block (\<Sigma>\<^sub>M \<union> {bl\<^sub>M}) \<subseteq> gamma_block \<Gamma>\<^sub>M"
        by (rule gamma_block_mono)
      thus ?thesis by blast
    qed

    \<comment> \<open>(4) start state in Q'\<close>
    show "(s\<^sub>M, init_stage le\<^sub>M)
            \<in> Q\<^sub>M \<times> {stg. ae_valid_stage \<Gamma>\<^sub>M le\<^sub>M k\<^sub>M stg}"
      using valid_mttm_s_in_Q[OF valM] M_eq init_valid by simp

    \<comment> \<open>(5) accept state in Q'\<close>
    show "(t\<^sub>M, init_stage le\<^sub>M)
            \<in> Q\<^sub>M \<times> {stg. ae_valid_stage \<Gamma>\<^sub>M le\<^sub>M k\<^sub>M stg}"
      using valid_mttm_t_in_Q[OF valM] M_eq init_valid by simp

    \<comment> \<open>(6) reject state in Q'\<close>
    show "(r\<^sub>M, init_stage le\<^sub>M)
            \<in> Q\<^sub>M \<times> {stg. ae_valid_stage \<Gamma>\<^sub>M le\<^sub>M k\<^sub>M stg}"
      using valid_mttm_r_in_Q[OF valM] M_eq init_valid by simp

    \<comment> \<open>(7a) blank in \<open>\<Gamma>'\<close>\<close>
    show "bl_block bl\<^sub>M \<in> gamma_block \<Gamma>\<^sub>M"
      using bl_block_in_gamma_block[OF valid_mttm_blank_in_Gamma[OF valM]] M_eq
      by simp

    \<comment> \<open>(7b) blank not in \<open>\<Sigma>'\<close>\<close>
    show "bl_block bl\<^sub>M
            \<notin> gamma_block (\<Sigma>\<^sub>M \<union> {bl\<^sub>M}) - {bl_block bl\<^sub>M, LE_block le\<^sub>M}"
      by simp

    \<comment> \<open>(8a) LE in \<open>\<Gamma>'\<close>\<close>
    show "LE_block le\<^sub>M \<in> gamma_block \<Gamma>\<^sub>M"
      using LE_block_in_gamma_block[OF valid_mttm_LE_in_Gamma[OF valM]] M_eq
      by simp

    \<comment> \<open>(8b) LE not in \<open>\<Sigma>'\<close>\<close>
    show "LE_block le\<^sub>M
            \<notin> gamma_block (\<Sigma>\<^sub>M \<union> {bl\<^sub>M}) - {bl_block bl\<^sub>M, LE_block le\<^sub>M}"
      by simp

    \<comment> \<open>(9) accept \<open>\<noteq>\<close> reject\<close>
    show "(t\<^sub>M, init_stage le\<^sub>M) \<noteq> (r\<^sub>M, init_stage le\<^sub>M)"
      using valid_mttm_t_neq_r[OF valM] M_eq by simp

    \<comment> \<open>(10) \<open>\<delta>_set\<close> shape (range conditions on read / write
            blocks; source state in \<open>Q' - {t', r'}\<close>; dest
            state in \<open>Q'\<close>).  Decomposed by intersection structure:
            the read/write codomains and the source/dest stage
            validity come straight off \<open>alphabet_enlarge_delta\<close>'s
            three intersection guards (no builder unfold), and the
            \<open>M\<close>-state shape from \<open>alphabet_enlarge_delta_state_shape\<close>
            (discrete state components only).  Neither half needs
            \<open>split: if_splits\<close> over the 16 guarded builders — the trap
            that made the old monolithic \<open>auto\<close> loop.\<close>
    show "alphabet_enlarge_delta M
            \<subseteq> ((Q\<^sub>M \<times> {stg. ae_valid_stage \<Gamma>\<^sub>M le\<^sub>M k\<^sub>M stg})
                  - {(t\<^sub>M, init_stage le\<^sub>M), (r\<^sub>M, init_stage le\<^sub>M)})
            \<times> (UNIV \<rightarrow> gamma_block \<Gamma>\<^sub>M)
            \<times> (Q\<^sub>M \<times> {stg. ae_valid_stage \<Gamma>\<^sub>M le\<^sub>M k\<^sub>M stg})
            \<times> (UNIV \<rightarrow> gamma_block \<Gamma>\<^sub>M)
            \<times> (UNIV \<rightarrow> UNIV)"
    proof (rule subsetI)
      fix x assume xin: "x \<in> alphabet_enlarge_delta M"
      obtain s rest where x1: "x = (s, rest)" by (cases x)
      obtain a rest2 where x2: "rest = (a, rest2)" by (cases rest)
      obtain s' rest3 where x3: "rest2 = (s', rest3)" by (cases rest2)
      obtain a' d where x4: "rest3 = (a', d)" by (cases rest3)
      from x1 x2 x3 x4 have x_eq: "x = (s, a, s', a', d)" by simp
      from xin have mem_t: "(s, a, s', a', d) \<in> alphabet_enlarge_delta M"
        unfolding x_eq by simp
      \<comment> \<open>Read/write codomain + source/dest stage validity: off the
          intersection guards, no builder unfold, no \<open>if_splits\<close>.\<close>
      from mem_t have inter:
        "(\<forall>k. a k \<in> gamma_block (\<Gamma>_tm M))
           \<and> (\<forall>k. a' k \<in> gamma_block (\<Gamma>_tm M))
           \<and> ae_valid_stage (\<Gamma>_tm M) (le_tm M) (k_tm M) (snd s)
           \<and> ae_valid_stage (\<Gamma>_tm M) (le_tm M) (k_tm M) (snd s')"
        unfolding alphabet_enlarge_delta_def by simp
      \<comment> \<open>State shape from the substep builders — discrete components only.\<close>
      have shape: "fst s \<in> Q_tm M \<and> fst s' \<in> Q_tm M
                     \<and> s \<noteq> (t_tm M, init_stage (le_tm M))
                     \<and> s \<noteq> (r_tm M, init_stage (le_tm M))"
        by (rule alphabet_enlarge_delta_state_shape[OF valM mem_t])
      have s_in: "s \<in> (Q\<^sub>M \<times> {stg. ae_valid_stage \<Gamma>\<^sub>M le\<^sub>M k\<^sub>M stg})
                        - {(t\<^sub>M, init_stage le\<^sub>M), (r\<^sub>M, init_stage le\<^sub>M)}"
        using shape inter M_eq by (cases s) auto
      have s'_in: "s' \<in> Q\<^sub>M \<times> {stg. ae_valid_stage \<Gamma>\<^sub>M le\<^sub>M k\<^sub>M stg}"
        using shape inter M_eq by (cases s') auto
      have a_in: "a \<in> UNIV \<rightarrow> gamma_block \<Gamma>\<^sub>M"
        using inter M_eq by (auto simp: Pi_iff)
      have a'_in: "a' \<in> UNIV \<rightarrow> gamma_block \<Gamma>\<^sub>M"
        using inter M_eq by (auto simp: Pi_iff)
      show "x \<in> ((Q\<^sub>M \<times> {stg. ae_valid_stage \<Gamma>\<^sub>M le\<^sub>M k\<^sub>M stg})
                      - {(t\<^sub>M, init_stage le\<^sub>M), (r\<^sub>M, init_stage le\<^sub>M)})
                \<times> (UNIV \<rightarrow> gamma_block \<Gamma>\<^sub>M)
                \<times> (Q\<^sub>M \<times> {stg. ae_valid_stage \<Gamma>\<^sub>M le\<^sub>M k\<^sub>M stg})
                \<times> (UNIV \<rightarrow> gamma_block \<Gamma>\<^sub>M)
                \<times> (UNIV \<rightarrow> UNIV)"
        unfolding x_eq using s_in s'_in a_in a'_in
        by (auto simp: mem_Times_iff Pi_iff)
    qed

    \<comment> \<open>(11) \<open>\<delta>LE\<close> preservation: case-analysis across the 8
            substep relations.  Each branch's \<open>d k\<close> is
            \<open>\<delta>LE\<close>-safe by construction (LE-guard prefix on
            action helpers; conditional move on SS1\<open>\<rightarrow>\<close>SS2
            and SS4\<open>\<rightarrow>\<close>SS5).\<close>
    show "\<forall>q a q' a' d k.
            (q, a, q', a', d) \<in> alphabet_enlarge_delta M \<longrightarrow>
            a k = LE_block le\<^sub>M \<longrightarrow>
            a' k = LE_block le\<^sub>M \<and> d k \<in> {dir.N, dir.R}"
      unfolding alphabet_enlarge_delta_def
                ae_delta_val_fwd_advance_def ae_delta_val_fwd_to_padded_def
                ae_delta_val_fwd_reject_def ae_delta_val_fwd_to_ret_def
                ae_delta_val_pad_to_ret_def ae_delta_val_pad_reject_def
                ae_delta_val_ret_step_def ae_delta_val_ret_to_sim_def
                ae_delta_ss1_ss2_def ae_delta_ss2_ss3_def
                ae_delta_ss3_ss4_def ae_delta_ss4_ss5_def
                ae_delta_ss5_ss6_def ae_delta_ss6_ss7_def
                ae_delta_ss7_ss8_def ae_delta_ss8_ss1_def
                init_stage_def
      using M_eq
      by (auto split: if_splits prod.splits)
    \<comment> \<open>(12) \<open>\<delta>\<close>-support past tape count: every transition leaves
            tapes \<open>\<ge> k\<^sub>M\<close> blank for both read and write and
            stationary (\<open>dir.N\<close>).  Each builder carries the
            read-support conjunct \<open>\<forall>j\<ge>k_tm M. a j = bl_block
            (bl_tm M)\<close> (giving \<open>a j\<close>, and \<open>a' j\<close> for the
            \<open>a' = a\<close> builders); the four write-back builders
            guard \<open>a'\<close> to \<open>bl_block (bl_tm M)\<close> past tape count; and
            every \<open>d\<close>-guard's else-branch is \<open>dir.N\<close> (the
            validation builders' \<open>if k = 0\<close> direction gives
            \<open>dir.N\<close> for \<open>j \<ge> k\<^sub>M > 0\<close>, via \<open>0 < k\<^sub>M\<close>).
            Same case-analysis shape as (11); the else-branch
            selection means the action helpers are never
            evaluated, so no action unfold is needed.\<close>
    show "\<forall>q a q' a' d.
            (q, a, q', a', d) \<in> alphabet_enlarge_delta M \<longrightarrow>
            (\<forall>j\<ge>k\<^sub>M. a j = bl_block bl\<^sub>M
                       \<and> a' j = bl_block bl\<^sub>M
                       \<and> d j = dir.N)"
      unfolding alphabet_enlarge_delta_def
                ae_delta_val_fwd_advance_def ae_delta_val_fwd_to_padded_def
                ae_delta_val_fwd_reject_def ae_delta_val_fwd_to_ret_def
                ae_delta_val_pad_to_ret_def ae_delta_val_pad_reject_def
                ae_delta_val_ret_step_def ae_delta_val_ret_to_sim_def
                ae_delta_ss1_ss2_def ae_delta_ss2_ss3_def
                ae_delta_ss3_ss4_def ae_delta_ss4_ss5_def
                ae_delta_ss5_ss6_def ae_delta_ss6_ss7_def
                ae_delta_ss7_ss8_def ae_delta_ss8_ss1_def
      using M_eq valid_mttm_k_pos[OF valM]
      by (auto split: if_splits prod.splits)
  qed
qed

end
