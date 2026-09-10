theory AlphabetEnlargement_ForwardCells
  imports AlphabetEnlargement_OutputWF
begin

subsection \<open>Forward-stage per-tape reconstruction leaves\<close>

text \<open>Base of the forward-stage chain
  \<open>ForwardCells \<rightarrow> ForwardStep \<rightarrow> ForwardStage\<close>.  The unified
  forward-stage lemma \<open>ae_simulates_forward_stage_general\<close> (theory
  \<open>AlphabetEnlargement_ForwardStage\<close>) advances the simulation by one
  \<open>M\<close>-step through eight substeps (\<open>SS1\<close> through \<open>SS8\<close>);
  the \<open>SS5\<close>--\<open>SS8\<close> half is packaged as the super-step
  \<open>ae_forward_stage_step_chain\<close> (theory
  \<open>AlphabetEnlargement_ForwardStep\<close>).  From the configs
  \<open>c5\<close>--\<open>c8\<close> that super-step exposes, the lemma then
  reconstructs, tape by tape, where each simulated head sits and what its
  in-window blocks hold.  The nine lemmas in this theory are those
  per-tape reconstruction facts.

  Each branches on the tape's block position \<open>mt_pos c' kk\<close>
  into the three regimes (steady \<open>\<ge> 2\<close>, le1 \<open>= 1\<close>, le0
  \<open>= 0\<close>) and reads off the \<open>c5\<close>--\<open>c8\<close> intermediate
  configs the super-step exposes.  They group into the head-position
  trajectories (\<open>ae_fwd_c8_pos_for_*\<close>, \<open>ae_fwd_c6_pos_for_*\<close>,
  \<open>ae_fwd_pos_decode_c8\<close>), the in-window cell values
  (\<open>ae_fwd_c8_at_*\<close>), and the per-tape tape-correspondence
  (\<open>ae_fwd_tape_corr_c8\<close>).  Each was extracted from the unified
  lemma's proof, so its assumption interface is wide: the assumptions are
  exactly the data-flow the fact consumed when it was an inline block.\<close>

text \<open>Reconstruction leaf of \<open>ae_simulates_forward_stage_general\<close> (the
  pos-at-least-2 in-window \<open>c8\<close> value at block pos minus 1).\<close>

lemma ae_fwd_c8_at_pos_minus_1_ge2:
  fixes M :: "('q, 'a) mttm"
    and c' c4 c5 c6 c7 c8 :: "('c :: enum \<Rightarrow> 'a,
                'q \<times> ('a, 'c) ae_stage) mt_config"
    and q5 q6 :: 'q
    and ofs5 ofs6 :: "nat \<Rightarrow> 'c"
    and buf5 buf6 :: "nat \<Rightarrow> ('c \<Rightarrow> 'a) \<times> ('c \<Rightarrow> 'a) \<times> ('c \<Rightarrow> 'a)"
    and dest5 dest6 :: "nat \<Rightarrow> ae_dest"
  assumes step5: "(c4, c5) \<in> mttm_step (alphabet_enlarge_delta M)"
      and c5_state: "mt_state c5 = (q5, ofs5, buf5, dest5, SS6)"
      and tape_c4_eq_c': "mt_tape c4 = mt_tape c'"
      and buf5_not_le_per_tape:
            "\<forall>k<k_tm M. (mt_pos c' k = 0
                   \<longrightarrow> fst (buf5 k) \<noteq> LE_block (le_tm M)
                      \<and> snd (snd (buf5 k)) \<noteq> LE_block (le_tm M))
                 \<and> (mt_pos c' k = 1
                      \<longrightarrow> fst (snd (buf5 k)) \<noteq> LE_block (le_tm M)
                        \<and> snd (snd (buf5 k)) \<noteq> LE_block (le_tm M))
                 \<and> (mt_pos c' k \<ge> 2
                      \<longrightarrow> fst (buf5 k) \<noteq> LE_block (le_tm M)
                        \<and> fst (snd (buf5 k)) \<noteq> LE_block (le_tm M)
                        \<and> snd (snd (buf5 k)) \<noteq> LE_block (le_tm M))"
      and c4_pos: "\<And>kk. kk < k_tm M \<Longrightarrow> mt_pos c4 kk = mt_pos c' kk"
      and step6_sub: "(c5, c6) \<in> mttm_step (ae_delta_ss6_ss7 M)"
      and step6: "(c5, c6) \<in> mttm_step (alphabet_enlarge_delta M)"
      and step7: "(c6, c7) \<in> mttm_step (alphabet_enlarge_delta M)"
      and c7_state: "mt_state c7 = (q6, ofs6, buf6, dest6, SS8)"
      and buf6_eq_buf5: "buf6 = buf5"
      and dest6_eq_dest5: "dest6 = dest5"
      and step8_sub: "(c7, c8) \<in> mttm_step (ae_delta_ss8_ss1 M)"
      and step8: "(c7, c8) \<in> mttm_step (alphabet_enlarge_delta M)"
      and c5_pos_for_pos_ge2:
            "\<And>kk. kk < k_tm M \<Longrightarrow> mt_pos c' kk \<ge> 2 \<Longrightarrow> dest5 kk \<noteq> AE_Left
                  \<Longrightarrow> mt_pos c5 kk = mt_pos c' kk - 1"
      and c5_pos_for_pos_ge2_dest_left:
            "\<And>kk. kk < k_tm M \<Longrightarrow> mt_pos c' kk \<ge> 2 \<Longrightarrow> dest5 kk = AE_Left
                  \<Longrightarrow> mt_pos c5 kk = mt_pos c' kk + 1"
      and left_not_le_c'_steady:
            "\<forall>k. mt_pos c' k \<ge> 2
                  \<longrightarrow> mt_tape c' k (mt_pos c' k - 1) \<noteq> LE_block (le_tm M)"
      and c6_pos_for_pos_ge2:
            "\<And>kk. kk < k_tm M \<Longrightarrow> mt_pos c' kk \<ge> 2 \<Longrightarrow> mt_pos c6 kk = mt_pos c' kk"
      and c7_pos_for_pos_ge2:
            "\<And>kk. kk < k_tm M \<Longrightarrow> mt_pos c' kk \<ge> 2
                  \<Longrightarrow> mt_pos c7 kk = (if dest5 kk = AE_Left
                                        then mt_pos c' kk - 1
                                        else mt_pos c' kk + 1)"
  shows "\<And>kk. kk < k_tm M \<Longrightarrow> mt_pos c' kk \<ge> 2
            \<Longrightarrow> mt_tape c8 kk (mt_pos c' kk - 1) = fst (buf5 kk)"
proof -
    fix kk
    assume kklt: "kk < k_tm M"
    assume hge2: "mt_pos c' kk \<ge> 2"
    obtain ll hh rr where buf5_kk: "buf5 kk = (ll, hh, rr)"
      using prod.exhaust by metis
    have buf6_kk: "buf6 kk = (ll, hh, rr)"
      using buf5_kk buf6_eq_buf5 by simp
    have h_ne_LE: "hh \<noteq> LE_block (le_tm M)"
    proof -
      have "fst (snd (buf5 kk)) \<noteq> LE_block (le_tm M)"
        using buf5_not_le_per_tape[rule_format, OF kklt] hge2 by blast
      thus ?thesis using buf5_kk by simp
    qed
    have c4_kk_eq: "mt_pos c4 kk = mt_pos c' kk" using c4_pos kklt by simp
    have pm1_ne_c4: "(mt_pos c' kk - 1) \<noteq> mt_pos c4 kk"
      using c4_kk_eq hge2 by linarith
    have c4_at_pm1_ne_LE:
        "mt_tape c4 kk (mt_pos c' kk - 1) \<noteq> LE_block (le_tm M)"
    proof -
      have "mt_tape c4 kk (mt_pos c' kk - 1) = mt_tape c' kk (mt_pos c' kk - 1)"
        using tape_c4_eq_c' by simp
      moreover have "mt_tape c' kk (mt_pos c' kk - 1) \<noteq> LE_block (le_tm M)"
        using left_not_le_c'_steady hge2 by blast
      ultimately show ?thesis by simp
    qed
    show "mt_tape c8 kk (mt_pos c' kk - 1) = fst (buf5 kk)"
    proof (cases "dest5 kk")
      case AE_Left
      \<comment> \<open>SS5/SS6/SS7 off pos-1; SS8 writes \<open>l\<close> at
          \<open>c7_pos = pos - 1\<close>.\<close>
      have c5_pos_kk: "mt_pos c5 kk = mt_pos c' kk + 1"
        using c5_pos_for_pos_ge2_dest_left[OF kklt hge2 AE_Left] .
      have pm1_ne_c5: "(mt_pos c' kk - 1) \<noteq> mt_pos c5 kk"
        using c5_pos_kk hge2 by linarith
      have c6_pos_kk: "mt_pos c6 kk = mt_pos c' kk"
        using c6_pos_for_pos_ge2[OF kklt hge2] .
      have pm1_ne_c6: "(mt_pos c' kk - 1) \<noteq> mt_pos c6 kk"
        using c6_pos_kk hge2 by linarith
      have c7_at_pm1_eq_c4:
          "mt_tape c7 kk (mt_pos c' kk - 1) = mt_tape c4 kk (mt_pos c' kk - 1)"
      proof -
        have "mt_tape c7 kk (mt_pos c' kk - 1)
                = mt_tape c6 kk (mt_pos c' kk - 1)"
          using mttm_step_tape_off_head[OF step7 pm1_ne_c6] .
        also have "\<dots> = mt_tape c5 kk (mt_pos c' kk - 1)"
          using mttm_step_tape_off_head[OF step6 pm1_ne_c5] .
        also have "\<dots> = mt_tape c4 kk (mt_pos c' kk - 1)"
          using mttm_step_tape_off_head[OF step5 pm1_ne_c4] .
        finally show ?thesis .
      qed
      have c7_pos_kk: "mt_pos c7 kk = mt_pos c' kk - 1"
        using c7_pos_for_pos_ge2[OF kklt hge2] AE_Left by simp
      obtain qq tts nn qq' aa8 dr8 where
          c7_eq8: "c7 = Config\<^sub>M qq tts nn"
        and c8_eq: "c8 = Config\<^sub>M qq'
                            (\<lambda>k. (tts k)(nn k := aa8 k))
                            (\<lambda>k. go_dir (dr8 k) (nn k))"
        and tr_in: "(qq, \<lambda>k. tts k (nn k), qq', aa8, dr8)
                      \<in> ae_delta_ss8_ss1 M"
        using step8_sub by (auto elim: mttm_step.cases)
      obtain q ofs buf dest where
          qq_eq: "qq = (q, ofs, buf, dest, SS8)"
        and aa8_eq:
            "aa8 = (\<lambda>k. if k < k_tm M then fst (ae_ss8_action (le_tm M)
                                (tts k (nn k)) (buf k) (dest k)) else bl_block (bl_tm M))"
        using tr_in by (auto simp: ae_delta_ss8_ss1_def)
      have qq_state: "qq = (q6, ofs6, buf6, dest6, SS8)"
        using c7_state c7_eq8 by simp
      have buf_eq: "buf = buf6" using qq_eq qq_state by simp
      have dest_eq: "dest = dest6" using qq_eq qq_state by simp
      have nn_kk: "nn kk = mt_pos c7 kk" using c7_eq8 by simp
      have nn_kk_val: "nn kk = mt_pos c' kk - 1" using nn_kk c7_pos_kk by simp
      have read_ne_LE: "tts kk (nn kk) \<noteq> LE_block (le_tm M)"
      proof -
        have "tts kk (nn kk) = mt_tape c7 kk (mt_pos c7 kk)"
          using c7_eq8 nn_kk by simp
        also have "\<dots> = mt_tape c7 kk (mt_pos c' kk - 1)" using c7_pos_kk by simp
        also have "\<dots> = mt_tape c4 kk (mt_pos c' kk - 1)" using c7_at_pm1_eq_c4 .
        finally have "tts kk (nn kk) = mt_tape c4 kk (mt_pos c' kk - 1)" .
        thus ?thesis using c4_at_pm1_ne_LE by simp
      qed
      have dest6_AE_Left: "dest6 kk = AE_Left"
        using AE_Left dest6_eq_dest5 by simp
      have aa8_kk: "aa8 kk = ll"
        using aa8_eq buf_eq dest_eq dest6_AE_Left buf6_kk h_ne_LE read_ne_LE kklt
        by simp
      have "mt_tape c8 kk (mt_pos c' kk - 1) = aa8 kk"
        using c8_eq nn_kk_val by simp
      also have "\<dots> = ll" using aa8_kk .
      also have "\<dots> = fst (buf5 kk)" using buf5_kk by simp
      finally show ?thesis .
    next
      case AE_Home
      \<comment> \<open>SS6 writes \<open>l\<close> at \<open>c5_pos = pos - 1\<close>; SS7/SS8 off pos-1.\<close>
      have dest_ne_left: "dest5 kk \<noteq> AE_Left" using AE_Home by simp
      have c5_pos_kk: "mt_pos c5 kk = mt_pos c' kk - 1"
        using c5_pos_for_pos_ge2[OF kklt hge2 dest_ne_left] .
      obtain qq tts nn qq' aa6 dr6 where
          c5_eq6: "c5 = Config\<^sub>M qq tts nn"
        and c6_eq: "c6 = Config\<^sub>M qq'
                            (\<lambda>k. (tts k)(nn k := aa6 k))
                            (\<lambda>k. go_dir (dr6 k) (nn k))"
        and tr_in: "(qq, \<lambda>k. tts k (nn k), qq', aa6, dr6)
                      \<in> ae_delta_ss6_ss7 M"
        using step6_sub by (auto elim: mttm_step.cases)
      obtain q ofs buf dest where
          qq_eq: "qq = (q, ofs, buf, dest, SS6)"
        and aa6_eq:
            "aa6 = (\<lambda>k. if k < k_tm M then fst (ae_ss6_action (le_tm M)
                                (tts k (nn k)) (buf k) (dest k)) else bl_block (bl_tm M))"
        using tr_in by (auto simp: ae_delta_ss6_ss7_def)
      have qq_state: "qq = (q5, ofs5, buf5, dest5, SS6)"
        using c5_state c5_eq6 by simp
      have buf_eq: "buf = buf5" using qq_eq qq_state by simp
      have dest_eq: "dest = dest5" using qq_eq qq_state by simp
      have nn_kk: "nn kk = mt_pos c5 kk" using c5_eq6 by simp
      have nn_kk_val: "nn kk = mt_pos c' kk - 1" using nn_kk c5_pos_kk by simp
      have c5_at_pm1_eq_c4:
          "mt_tape c5 kk (mt_pos c' kk - 1) = mt_tape c4 kk (mt_pos c' kk - 1)"
        using mttm_step_tape_off_head[OF step5 pm1_ne_c4] .
      have read_ne_LE: "tts kk (nn kk) \<noteq> LE_block (le_tm M)"
      proof -
        have "tts kk (nn kk) = mt_tape c5 kk (mt_pos c5 kk)"
          using c5_eq6 nn_kk by simp
        also have "\<dots> = mt_tape c5 kk (mt_pos c' kk - 1)" using c5_pos_kk by simp
        also have "\<dots> = mt_tape c4 kk (mt_pos c' kk - 1)" using c5_at_pm1_eq_c4 .
        finally have "tts kk (nn kk) = mt_tape c4 kk (mt_pos c' kk - 1)" .
        thus ?thesis using c4_at_pm1_ne_LE by simp
      qed
      have aa6_kk: "aa6 kk = ll"
        using aa6_eq buf_eq dest_eq AE_Home buf5_kk h_ne_LE read_ne_LE kklt by simp
      have c6_at_pm1: "mt_tape c6 kk (mt_pos c' kk - 1) = ll"
      proof -
        have "mt_tape c6 kk (mt_pos c' kk - 1) = aa6 kk"
          using c6_eq nn_kk_val by simp
        thus ?thesis using aa6_kk by simp
      qed
      have c6_pos_kk: "mt_pos c6 kk = mt_pos c' kk"
        using c6_pos_for_pos_ge2[OF kklt hge2] .
      have pm1_ne_c6: "(mt_pos c' kk - 1) \<noteq> mt_pos c6 kk"
        using c6_pos_kk hge2 by linarith
      have c7_pos_kk: "mt_pos c7 kk = mt_pos c' kk + 1"
        using c7_pos_for_pos_ge2[OF kklt hge2] AE_Home by simp
      have pm1_ne_c7: "(mt_pos c' kk - 1) \<noteq> mt_pos c7 kk"
        using c7_pos_kk by linarith
      have "mt_tape c8 kk (mt_pos c' kk - 1) = mt_tape c7 kk (mt_pos c' kk - 1)"
        using mttm_step_tape_off_head[OF step8 pm1_ne_c7] .
      also have "\<dots> = mt_tape c6 kk (mt_pos c' kk - 1)"
        using mttm_step_tape_off_head[OF step7 pm1_ne_c6] .
      also have "\<dots> = ll" using c6_at_pm1 .
      also have "\<dots> = fst (buf5 kk)" using buf5_kk by simp
      finally show ?thesis .
    next
      case AE_Right
      \<comment> \<open>SS6 writes \<open>l\<close> at \<open>c5_pos = pos - 1\<close>; SS7/SS8 off pos-1.\<close>
      have dest_ne_left: "dest5 kk \<noteq> AE_Left" using AE_Right by simp
      have c5_pos_kk: "mt_pos c5 kk = mt_pos c' kk - 1"
        using c5_pos_for_pos_ge2[OF kklt hge2 dest_ne_left] .
      obtain qq tts nn qq' aa6 dr6 where
          c5_eq6: "c5 = Config\<^sub>M qq tts nn"
        and c6_eq: "c6 = Config\<^sub>M qq'
                            (\<lambda>k. (tts k)(nn k := aa6 k))
                            (\<lambda>k. go_dir (dr6 k) (nn k))"
        and tr_in: "(qq, \<lambda>k. tts k (nn k), qq', aa6, dr6)
                      \<in> ae_delta_ss6_ss7 M"
        using step6_sub by (auto elim: mttm_step.cases)
      obtain q ofs buf dest where
          qq_eq: "qq = (q, ofs, buf, dest, SS6)"
        and aa6_eq:
            "aa6 = (\<lambda>k. if k < k_tm M then fst (ae_ss6_action (le_tm M)
                                (tts k (nn k)) (buf k) (dest k)) else bl_block (bl_tm M))"
        using tr_in by (auto simp: ae_delta_ss6_ss7_def)
      have qq_state: "qq = (q5, ofs5, buf5, dest5, SS6)"
        using c5_state c5_eq6 by simp
      have buf_eq: "buf = buf5" using qq_eq qq_state by simp
      have dest_eq: "dest = dest5" using qq_eq qq_state by simp
      have nn_kk: "nn kk = mt_pos c5 kk" using c5_eq6 by simp
      have nn_kk_val: "nn kk = mt_pos c' kk - 1" using nn_kk c5_pos_kk by simp
      have c5_at_pm1_eq_c4:
          "mt_tape c5 kk (mt_pos c' kk - 1) = mt_tape c4 kk (mt_pos c' kk - 1)"
        using mttm_step_tape_off_head[OF step5 pm1_ne_c4] .
      have read_ne_LE: "tts kk (nn kk) \<noteq> LE_block (le_tm M)"
      proof -
        have "tts kk (nn kk) = mt_tape c5 kk (mt_pos c5 kk)"
          using c5_eq6 nn_kk by simp
        also have "\<dots> = mt_tape c5 kk (mt_pos c' kk - 1)" using c5_pos_kk by simp
        also have "\<dots> = mt_tape c4 kk (mt_pos c' kk - 1)" using c5_at_pm1_eq_c4 .
        finally have "tts kk (nn kk) = mt_tape c4 kk (mt_pos c' kk - 1)" .
        thus ?thesis using c4_at_pm1_ne_LE by simp
      qed
      have aa6_kk: "aa6 kk = ll"
        using aa6_eq buf_eq dest_eq AE_Right buf5_kk h_ne_LE read_ne_LE kklt by simp
      have c6_at_pm1: "mt_tape c6 kk (mt_pos c' kk - 1) = ll"
      proof -
        have "mt_tape c6 kk (mt_pos c' kk - 1) = aa6 kk"
          using c6_eq nn_kk_val by simp
        thus ?thesis using aa6_kk by simp
      qed
      have c6_pos_kk: "mt_pos c6 kk = mt_pos c' kk"
        using c6_pos_for_pos_ge2[OF kklt hge2] .
      have pm1_ne_c6: "(mt_pos c' kk - 1) \<noteq> mt_pos c6 kk"
        using c6_pos_kk hge2 by linarith
      have c7_pos_kk: "mt_pos c7 kk = mt_pos c' kk + 1"
        using c7_pos_for_pos_ge2[OF kklt hge2] AE_Right by simp
      have pm1_ne_c7: "(mt_pos c' kk - 1) \<noteq> mt_pos c7 kk"
        using c7_pos_kk by linarith
      have "mt_tape c8 kk (mt_pos c' kk - 1) = mt_tape c7 kk (mt_pos c' kk - 1)"
        using mttm_step_tape_off_head[OF step8 pm1_ne_c7] .
      also have "\<dots> = mt_tape c6 kk (mt_pos c' kk - 1)"
        using mttm_step_tape_off_head[OF step7 pm1_ne_c6] .
      also have "\<dots> = ll" using c6_at_pm1 .
      also have "\<dots> = fst (buf5 kk)" using buf5_kk by simp
      finally show ?thesis .
    qed
  qed

text \<open>Reconstruction leaf of \<open>ae_simulates_forward_stage_general\<close>: the
  per-tape regime-aware \<open>ae_tape_correspondence\<close> between the
  simulated M-config \<open>cM_k\<close> and the post-chain M'-config
  \<open>c8\<close>.  Per tape it branches on \<open>mt_pos c' kk\<close>
  (steady / le1 / le0) and within each regime on the block
  \<open>s\<close>: an in-window cell matches via the buf-lin transfer
  coinciding with the \<open>c8\<close> in-window value on the \<open>buf5\<close>
  slot, an off-window cell via \<open>cM_k = cM = c'\<close> (M-side) and
  \<open>c8 = c'\<close> (M'-side).  \<close>
lemma ae_fwd_tape_corr_c8:
  fixes M :: "('q, 'a) mttm"
    and cM cM_k :: "('a, 'q) mt_config"
    and c' c4 c5 c6 c7 c8 :: "('c :: enum \<Rightarrow> 'a,
                'q \<times> ('a, 'c) ae_stage) mt_config"
    and buf5 :: "nat \<Rightarrow> ('c \<Rightarrow> 'a) \<times> ('c \<Rightarrow> 'a) \<times> ('c \<Rightarrow> 'a)"
    and dest5 :: "nat \<Rightarrow> ae_dest"
  assumes tape_corr: "\<forall>k<k_tm M. ae_tape_correspondence (le_tm M)
            (mt_tape cM k) (mt_tape c' k)"
      and c_ge_1: "1 \<le> card (UNIV :: 'c set)"
      and c4_pos: "\<And>kk. kk < k_tm M \<Longrightarrow> mt_pos c4 kk = mt_pos c' kk"
      and c5_pos_for_pos1:
            "\<And>kk. kk < k_tm M \<Longrightarrow> mt_pos c' kk = 1 \<Longrightarrow> dest5 kk \<noteq> AE_Left
                  \<Longrightarrow> mt_pos c5 kk = 0"
      and c5_pos_for_pos1_dest_left:
            "\<And>kk. kk < k_tm M \<Longrightarrow> mt_pos c' kk = 1 \<Longrightarrow> dest5 kk = AE_Left
                  \<Longrightarrow> mt_pos c5 kk = 2"
      and c7_pos_for_pos1_dest_left:
            "\<And>kk. kk < k_tm M \<Longrightarrow> mt_pos c' kk = 1 \<Longrightarrow> dest5 kk = AE_Left
                  \<Longrightarrow> mt_pos c7 kk = 0"
      and cM_k_zero: "\<And>kk. kk < k_tm M \<Longrightarrow> mt_tape cM_k kk 0 = le_tm M"
      and m_tape_off_window_le0:
            "\<And>kk p. kk < k_tm M \<Longrightarrow> mt_pos c' kk = 0
                  \<Longrightarrow> p > card (UNIV :: 'c set)
                  \<Longrightarrow> mt_tape cM_k kk p = mt_tape cM kk p"
      and m_tape_off_window_le1:
            "\<And>kk p. kk < k_tm M \<Longrightarrow> mt_pos c' kk = 1
                  \<Longrightarrow> p > 2 * card (UNIV :: 'c set)
                  \<Longrightarrow> mt_tape cM_k kk p = mt_tape cM kk p"
      and m_tape_off_window_steady:
            "\<And>kk p. kk < k_tm M \<Longrightarrow> mt_pos c' kk \<ge> 2
                  \<Longrightarrow> p < (mt_pos c' kk - 2) * card (UNIV :: 'c set) + 1
                  \<or> p \<ge> (mt_pos c' kk - 2) * card (UNIV :: 'c set) + 1 + 3 * card (UNIV :: 'c set)
                  \<Longrightarrow> mt_tape cM_k kk p = mt_tape cM kk p"
      and c5_pos_for_pos0:
            "\<And>kk. kk < k_tm M \<Longrightarrow> mt_pos c' kk = 0 \<Longrightarrow> mt_pos c5 kk = 0"
      and c5_pos_for_pos_ge2:
            "\<And>kk. kk < k_tm M \<Longrightarrow> mt_pos c' kk \<ge> 2 \<Longrightarrow> dest5 kk \<noteq> AE_Left
                  \<Longrightarrow> mt_pos c5 kk = mt_pos c' kk - 1"
      and c5_pos_for_pos_ge2_dest_left:
            "\<And>kk. kk < k_tm M \<Longrightarrow> mt_pos c' kk \<ge> 2 \<Longrightarrow> dest5 kk = AE_Left
                  \<Longrightarrow> mt_pos c5 kk = mt_pos c' kk + 1"
      and c6_pos_for_pos0:
            "\<And>kk. kk < k_tm M \<Longrightarrow> mt_pos c' kk = 0 \<Longrightarrow> mt_pos c6 kk = 1"
      and c6_pos_for_pos_ge2:
            "\<And>kk. kk < k_tm M \<Longrightarrow> mt_pos c' kk \<ge> 2 \<Longrightarrow> mt_pos c6 kk = mt_pos c' kk"
      and c7_pos_for_pos0:
            "\<And>kk. kk < k_tm M \<Longrightarrow> mt_pos c' kk = 0
                  \<Longrightarrow> mt_pos c7 kk = (if dest5 kk = AE_Right then 1 else 0)"
      and c7_pos_for_pos_ge2:
            "\<And>kk. kk < k_tm M \<Longrightarrow> mt_pos c' kk \<ge> 2
                  \<Longrightarrow> mt_pos c7 kk = (if dest5 kk = AE_Left
                  then mt_pos c' kk - 1
                  else mt_pos c' kk + 1)"
      and c6_pos_for_pos1:
            "\<And>kk. kk < k_tm M \<Longrightarrow> mt_pos c' kk = 1 \<Longrightarrow> mt_pos c6 kk = 1"
      and c7_pos_for_pos1:
            "\<And>kk. kk < k_tm M \<Longrightarrow> mt_pos c' kk = 1
                  \<Longrightarrow> mt_pos c7 kk = (if dest5 kk = AE_Left then 0 else 2)"
      and c8_tape_off_window:
            "\<And>kk s. s \<noteq> mt_pos c4 kk \<Longrightarrow> s \<noteq> mt_pos c5 kk
                  \<Longrightarrow> s \<noteq> mt_pos c6 kk \<Longrightarrow> s \<noteq> mt_pos c7 kk
                  \<Longrightarrow> mt_tape c8 kk s = mt_tape c' kk s"
      and c8_tape_at_one_for_pos0:
            "\<And>kk. kk < k_tm M \<Longrightarrow> mt_pos c' kk = 0
                  \<Longrightarrow> mt_tape c8 kk 1 = snd (snd (buf5 kk))"
      and c8_tape_at_one_for_pos1:
            "\<And>kk. kk < k_tm M \<Longrightarrow> mt_pos c' kk = 1
                  \<Longrightarrow> mt_tape c8 kk 1 = fst (snd (buf5 kk))"
      and c8_tape_at_two_for_pos1:
            "\<And>kk. kk < k_tm M \<Longrightarrow> mt_pos c' kk = 1
                  \<Longrightarrow> mt_tape c8 kk 2 = snd (snd (buf5 kk))"
      and c8_tape_at_pos_for_pos_ge2:
            "\<And>kk. kk < k_tm M \<Longrightarrow> mt_pos c' kk \<ge> 2
                  \<Longrightarrow> mt_tape c8 kk (mt_pos c' kk) = fst (snd (buf5 kk))"
      and c8_tape_at_pos_minus_1_for_pos_ge2:
            "\<And>kk. kk < k_tm M \<Longrightarrow> mt_pos c' kk \<ge> 2
                  \<Longrightarrow> mt_tape c8 kk (mt_pos c' kk - 1) = fst (buf5 kk)"
      and c8_tape_at_pos_plus_1_for_pos_ge2:
            "\<And>kk. kk < k_tm M \<Longrightarrow> mt_pos c' kk \<ge> 2
                  \<Longrightarrow> mt_tape c8 kk (mt_pos c' kk + 1) = snd (snd (buf5 kk))"
      and tape_cM_k_at_one_for_pos0:
            "\<And>kk i. kk < k_tm M \<Longrightarrow> mt_pos c' kk = 0
                  \<Longrightarrow> mt_tape cM_k kk (Suc (c_idx (i :: 'c)))
                  = (snd (snd (buf5 kk))) i"
      and tape_cM_k_at_one_for_pos1:
            "\<And>kk i. kk < k_tm M \<Longrightarrow> mt_pos c' kk = 1
                  \<Longrightarrow> mt_tape cM_k kk (Suc (c_idx (i :: 'c)))
                  = (fst (snd (buf5 kk))) i"
      and tape_cM_k_at_two_for_pos1:
            "\<And>kk i. kk < k_tm M \<Longrightarrow> mt_pos c' kk = 1
                  \<Longrightarrow> mt_tape cM_k kk (Suc (card (UNIV :: 'c set) + c_idx (i :: 'c)))
                  = (snd (snd (buf5 kk))) i"
      and tape_cM_k_at_pos_minus_1_for_pos_ge2:
            "\<And>kk i. kk < k_tm M \<Longrightarrow> mt_pos c' kk \<ge> 2
                  \<Longrightarrow> mt_tape cM_k kk ((mt_pos c' kk - 2) * card (UNIV :: 'c set)
                  + c_idx (i :: 'c) + 1)
                  = (fst (buf5 kk)) i"
      and tape_cM_k_at_pos_for_pos_ge2:
            "\<And>kk i. kk < k_tm M \<Longrightarrow> mt_pos c' kk \<ge> 2
                  \<Longrightarrow> mt_tape cM_k kk ((mt_pos c' kk - 1) * card (UNIV :: 'c set)
                  + c_idx (i :: 'c) + 1)
                  = (fst (snd (buf5 kk))) i"
      and tape_cM_k_at_pos_plus_1_for_pos_ge2:
            "\<And>kk i. kk < k_tm M \<Longrightarrow> mt_pos c' kk \<ge> 2
                  \<Longrightarrow> mt_tape cM_k kk (mt_pos c' kk * card (UNIV :: 'c set)
                  + c_idx (i :: 'c) + 1)
                  = (snd (snd (buf5 kk))) i"
  shows "\<forall>kk<k_tm M. ae_tape_correspondence (le_tm M)
            (mt_tape cM_k kk) (mt_tape c8 kk)"
proof -
  let ?c = "card (UNIV :: 'c set)"
  show ?thesis
  proof (intro allI impI)
    fix kk
    assume kklt: "kk < k_tm M"
    show "ae_tape_correspondence (le_tm M)
            (mt_tape cM_k kk) (mt_tape c8 kk)"
      unfolding ae_tape_correspondence_def
    proof (intro conjI allI impI)
      show "mt_tape cM_k kk 0 = le_tm M" using cM_k_zero[OF kklt] by simp
    next
      fix s :: nat and i :: 'c
      assume s_ge_1: "s \<ge> 1"
      let ?p = "(s - 1) * ?c + c_idx i + 1"
      have c_idx_lt: "c_idx i < ?c" by (rule c_idx_lt_card)
      have c4_kk_eq: "mt_pos c4 kk = mt_pos c' kk" using c4_pos kklt by simp
      consider (le0) "mt_pos c' kk = 0"
             | (le1) "mt_pos c' kk = 1"
             | (steady) "mt_pos c' kk \<ge> 2"
        by linarith
      thus "mt_tape cM_k kk ?p = mt_tape c8 kk s i"
      proof cases
        case le0
        \<comment> \<open>pos=0: s=1 is in-window (buf-lin r-slot transfer
            matches c8@1 = rr); \<open>s \<ge> 2\<close> is off-window on both
            sides.\<close>
        show ?thesis
        proof (cases "s = 1")
          case True
          have p_eq: "?p = Suc (c_idx i)" using True by simp
          have lhs: "mt_tape cM_k kk ?p = (snd (snd (buf5 kk))) i"
            using p_eq tape_cM_k_at_one_for_pos0[OF kklt le0] by simp
          have c8_at_s: "mt_tape c8 kk s = mt_tape c8 kk 1" using True by simp
          have c8_at_1: "mt_tape c8 kk 1 = snd (snd (buf5 kk))"
            using c8_tape_at_one_for_pos0[OF kklt le0] .
          show ?thesis using lhs c8_at_s c8_at_1 by simp
        next
          case False
          have s_ge_2: "s \<ge> 2" using s_ge_1 False by linarith
          have p_gt_c: "?p > ?c"
          proof -
            have s_sub_ge: "s - 1 \<ge> 1" using s_ge_2 by linarith
            have mult_ge: "(s - 1) * ?c \<ge> ?c"
              using s_sub_ge c_ge_1
              by (metis mult.commute mult_le_mono2 mult_numeral_1_right
                        mult_le_cancel2 nat_mult_1_right)
            show ?thesis using mult_ge by linarith
          qed
          \<comment> \<open>M-side off-window: \<open>cM_k@p = cM@p = c'@s i\<close>.\<close>
          have cM_k_at_p: "mt_tape cM_k kk ?p = mt_tape cM kk ?p"
            using m_tape_off_window_le0[OF kklt le0 p_gt_c] .
          have tc_at: "mt_tape cM kk ?p = mt_tape c' kk s i"
            using tape_corr[rule_format, OF kklt] s_ge_1
            unfolding ae_tape_correspondence_def by simp
          \<comment> \<open>M'-side off-window: \<open>c4_pos = 0\<close>,
              \<open>c5_pos = 0\<close>, \<open>c6_pos = 1\<close>,
              \<open>c7_pos \<in> {0, 1}\<close>; for \<open>s \<ge> 2\<close> all
              four positions \<open>\<noteq> s\<close>.\<close>
          have s_ne_c4: "s \<noteq> mt_pos c4 kk"
            using c4_kk_eq le0 s_ge_2 by linarith
          have s_ne_c5: "s \<noteq> mt_pos c5 kk"
            using c5_pos_for_pos0[OF kklt le0] s_ge_2 by simp
          have s_ne_c6: "s \<noteq> mt_pos c6 kk"
            using c6_pos_for_pos0[OF kklt le0] s_ge_2 by simp
          have s_ne_c7: "s \<noteq> mt_pos c7 kk"
          proof (cases "dest5 kk = AE_Right")
            case True
            have "mt_pos c7 kk = 1"
              using c7_pos_for_pos0[OF kklt le0] True by simp
            thus ?thesis using s_ge_2 by simp
          next
            case False
            have "mt_pos c7 kk = 0"
              using c7_pos_for_pos0[OF kklt le0] False by simp
            thus ?thesis using s_ge_2 by simp
          qed
          have c8_at_s: "mt_tape c8 kk s = mt_tape c' kk s"
            using c8_tape_off_window[OF s_ne_c4 s_ne_c5 s_ne_c6 s_ne_c7] .
          show ?thesis using cM_k_at_p tc_at c8_at_s by simp
        qed
      next
        case le1
        \<comment> \<open>pos=1: \<open>s \<in> {1, 2}\<close> in-window,
            \<open>s \<ge> 3\<close> off-window.\<close>
        show ?thesis
        proof (cases "s = 1")
          case True
          have p_eq: "?p = Suc (c_idx i)" using True by simp
          have lhs: "mt_tape cM_k kk ?p = (fst (snd (buf5 kk))) i"
            using p_eq tape_cM_k_at_one_for_pos1[OF kklt le1] by simp
          have c8_at_s: "mt_tape c8 kk s = mt_tape c8 kk 1" using True by simp
          have c8_at_1: "mt_tape c8 kk 1 = fst (snd (buf5 kk))"
            using c8_tape_at_one_for_pos1[OF kklt le1] .
          show ?thesis using lhs c8_at_s c8_at_1 by simp
        next
          case False
          have s_ge_2: "s \<ge> 2" using s_ge_1 False by linarith
          show ?thesis
          proof (cases "s = 2")
            case True
            have p_eq: "?p = Suc (?c + c_idx i)" using True by simp
            have lhs: "mt_tape cM_k kk ?p = (snd (snd (buf5 kk))) i"
              using p_eq tape_cM_k_at_two_for_pos1[OF kklt le1] by simp
            have c8_at_s: "mt_tape c8 kk s = mt_tape c8 kk 2" using True by simp
            have c8_at_2: "mt_tape c8 kk 2 = snd (snd (buf5 kk))"
              using c8_tape_at_two_for_pos1[OF kklt le1] .
            show ?thesis using lhs c8_at_s c8_at_2 by simp
          next
            case False
            have s_ge_3: "s \<ge> 3" using s_ge_2 False by linarith
            have p_gt_2c: "?p > 2 * ?c"
            proof -
              have s_sub_ge: "s - 1 \<ge> 2" using s_ge_3 by linarith
              have mult_ge: "(s - 1) * ?c \<ge> 2 * ?c"
                using s_sub_ge c_ge_1
                by (metis mult.commute mult_le_mono2)
              show ?thesis using mult_ge by linarith
            qed
            have cM_k_at_p: "mt_tape cM_k kk ?p = mt_tape cM kk ?p"
              using m_tape_off_window_le1[OF kklt le1 p_gt_2c] .
            have tc_at: "mt_tape cM kk ?p = mt_tape c' kk s i"
              using tape_corr[rule_format, OF kklt] s_ge_1
              unfolding ae_tape_correspondence_def by simp
            have s_ne_c4: "s \<noteq> mt_pos c4 kk"
              using c4_kk_eq le1 s_ge_3 by linarith
            have s_ne_c5: "s \<noteq> mt_pos c5 kk"
            proof (cases "dest5 kk = AE_Left")
              case True
              have "mt_pos c5 kk = 2"
                using c5_pos_for_pos1_dest_left[OF kklt le1 True] .
              thus ?thesis using s_ge_3 by simp
            next
              case False
              have "mt_pos c5 kk = 0"
                using c5_pos_for_pos1[OF kklt le1 False] .
              thus ?thesis using s_ge_3 by simp
            qed
            have s_ne_c6: "s \<noteq> mt_pos c6 kk"
              using c6_pos_for_pos1[OF kklt le1] s_ge_3 by simp
            have s_ne_c7: "s \<noteq> mt_pos c7 kk"
            proof (cases "dest5 kk = AE_Left")
              case True
              have "mt_pos c7 kk = 0"
                using c7_pos_for_pos1_dest_left[OF kklt le1 True] .
              thus ?thesis using s_ge_3 by simp
            next
              case False
              have "mt_pos c7 kk = 2"
                using c7_pos_for_pos1[OF kklt le1] False by simp
              thus ?thesis using s_ge_3 by simp
            qed
            have c8_at_s: "mt_tape c8 kk s = mt_tape c' kk s"
              using c8_tape_off_window[OF s_ne_c4 s_ne_c5 s_ne_c6 s_ne_c7] .
            show ?thesis using cM_k_at_p tc_at c8_at_s by simp
          qed
        qed
      next
        case steady
        \<comment> \<open>pos\<open>\<ge>\<close>2: \<open>s \<in> {pos-1, pos, pos+1}\<close>
            in-window; other \<open>s\<close> off-window.\<close>
        show ?thesis
        proof (cases "s = mt_pos c' kk - 1")
          case True
          have p_eq: "?p = (mt_pos c' kk - 2) * ?c + c_idx i + 1"
          proof -
            have "s - 1 = mt_pos c' kk - 2"
              using True steady by linarith
            thus ?thesis by simp
          qed
          have lhs: "mt_tape cM_k kk ?p = (fst (buf5 kk)) i"
            using p_eq tape_cM_k_at_pos_minus_1_for_pos_ge2[OF kklt steady] by simp
          have c8_at_s: "mt_tape c8 kk s = mt_tape c8 kk (mt_pos c' kk - 1)"
            using True by simp
          have c8_at_addr: "mt_tape c8 kk (mt_pos c' kk - 1) = fst (buf5 kk)"
            using c8_tape_at_pos_minus_1_for_pos_ge2[OF kklt steady] .
          show ?thesis using lhs c8_at_s c8_at_addr by simp
        next
          case ne_pm1: False
          show ?thesis
          proof (cases "s = mt_pos c' kk")
            case True
            have p_eq: "?p = (mt_pos c' kk - 1) * ?c + c_idx i + 1"
              using True steady by simp
            have lhs: "mt_tape cM_k kk ?p = (fst (snd (buf5 kk))) i"
              using p_eq tape_cM_k_at_pos_for_pos_ge2[OF kklt steady] by simp
            have c8_at_s: "mt_tape c8 kk s = mt_tape c8 kk (mt_pos c' kk)"
              using True by simp
            have c8_at_addr: "mt_tape c8 kk (mt_pos c' kk) = fst (snd (buf5 kk))"
              using c8_tape_at_pos_for_pos_ge2[OF kklt steady] .
            show ?thesis using lhs c8_at_s c8_at_addr by simp
          next
            case ne_pos: False
            show ?thesis
            proof (cases "s = mt_pos c' kk + 1")
              case True
              have p_eq: "?p = mt_pos c' kk * ?c + c_idx i + 1"
                using True by simp
              have lhs: "mt_tape cM_k kk ?p = (snd (snd (buf5 kk))) i"
                using p_eq tape_cM_k_at_pos_plus_1_for_pos_ge2[OF kklt steady]
                by simp
              have c8_at_s: "mt_tape c8 kk s = mt_tape c8 kk (mt_pos c' kk + 1)"
                using True by simp
              have c8_at_addr:
                  "mt_tape c8 kk (mt_pos c' kk + 1) = snd (snd (buf5 kk))"
                using c8_tape_at_pos_plus_1_for_pos_ge2[OF kklt steady] .
              show ?thesis using lhs c8_at_s c8_at_addr by simp
            next
              case ne_pp1: False
              \<comment> \<open>\<open>s\<close> off-window for steady:
                  \<open>s \<notin> {pos-1, pos, pos+1}\<close>.\<close>
              have s_outside: "s + 1 < mt_pos c' kk \<or> s > mt_pos c' kk + 1"
                using ne_pm1 ne_pos ne_pp1 steady by linarith
              have p_outside:
                  "?p < (mt_pos c' kk - 2) * ?c + 1
                    \<or> ?p \<ge> (mt_pos c' kk - 2) * ?c + 1 + 3 * ?c"
              proof -
                from s_outside show ?thesis
                proof
                  assume s_lt: "s + 1 < mt_pos c' kk"
                  have pos_ge3: "mt_pos c' kk \<ge> 3" using s_lt s_ge_1 by linarith
                  have s_sub_le: "s - 1 \<le> mt_pos c' kk - 3"
                    using s_lt s_ge_1 by linarith
                  have "(s - 1) * ?c \<le> (mt_pos c' kk - 3) * ?c"
                    using s_sub_le by (simp add: mult_le_mono1)
                  hence p_le: "?p \<le> (mt_pos c' kk - 3) * ?c + c_idx i + 1"
                    by linarith
                  have c_split: "(mt_pos c' kk - 2) * ?c
                                  = (mt_pos c' kk - 3) * ?c + ?c"
                    using pos_ge3 by (simp add: algebra_simps diff_mult_distrib)
                  have "?p < (mt_pos c' kk - 2) * ?c + 1"
                    using p_le c_split c_idx_lt by linarith
                  thus ?thesis ..
                next
                  assume s_gt: "s > mt_pos c' kk + 1"
                  have s_sub_ge: "s - 1 \<ge> mt_pos c' kk + 1"
                    using s_gt by linarith
                  have "(s - 1) * ?c \<ge> (mt_pos c' kk + 1) * ?c"
                    using s_sub_ge by (rule mult_le_mono1)
                  hence p_ge: "?p \<ge> (mt_pos c' kk + 1) * ?c + 1"
                    by linarith
                  have c_split: "(mt_pos c' kk + 1) * ?c
                                  = (mt_pos c' kk - 2) * ?c + 3 * ?c"
                    using steady by (simp add: algebra_simps diff_mult_distrib)
                  have "?p \<ge> (mt_pos c' kk - 2) * ?c + 1 + 3 * ?c"
                    using p_ge c_split by linarith
                  thus ?thesis ..
                qed
              qed
              have cM_k_at_p: "mt_tape cM_k kk ?p = mt_tape cM kk ?p"
                using m_tape_off_window_steady[OF kklt steady p_outside] .
              have tc_at: "mt_tape cM kk ?p = mt_tape c' kk s i"
                using tape_corr[rule_format, OF kklt] s_ge_1
                unfolding ae_tape_correspondence_def by simp
              have s_ne_c4: "s \<noteq> mt_pos c4 kk"
                using c4_kk_eq ne_pos by simp
              have s_ne_c5: "s \<noteq> mt_pos c5 kk"
              proof (cases "dest5 kk = AE_Left")
                case True
                have "mt_pos c5 kk = mt_pos c' kk + 1"
                  using c5_pos_for_pos_ge2_dest_left[OF kklt steady True] .
                thus ?thesis using ne_pp1 by simp
              next
                case False
                have "mt_pos c5 kk = mt_pos c' kk - 1"
                  using c5_pos_for_pos_ge2[OF kklt steady False] .
                thus ?thesis using ne_pm1 by simp
              qed
              have s_ne_c6: "s \<noteq> mt_pos c6 kk"
                using c6_pos_for_pos_ge2[OF kklt steady] ne_pos by simp
              have s_ne_c7: "s \<noteq> mt_pos c7 kk"
              proof (cases "dest5 kk = AE_Left")
                case True
                have "mt_pos c7 kk = mt_pos c' kk - 1"
                  using c7_pos_for_pos_ge2[OF kklt steady] True by simp
                thus ?thesis using ne_pm1 by simp
              next
                case False
                have "mt_pos c7 kk = mt_pos c' kk + 1"
                  using c7_pos_for_pos_ge2[OF kklt steady] False by simp
                thus ?thesis using ne_pp1 by simp
              qed
              have c8_at_s: "mt_tape c8 kk s = mt_tape c' kk s"
                using c8_tape_off_window[OF s_ne_c4 s_ne_c5 s_ne_c6 s_ne_c7] .
              show ?thesis using cM_k_at_p tc_at c8_at_s by simp
            qed
          qed
        qed
      qed
    qed
  qed
qed

text \<open>Reconstruction leaf of \<open>ae_simulates_forward_stage_general\<close>:
  the in-window \<open>c8\<close> value at block 2 for an le1 tape
  (\<open>mt_pos c' kk = 1\<close>).  Uniformly \<open>c8@2 = rr\<close> (the right
  buffer slot).  Three-way \<open>dest5\<close> case-split: for \<open>AE_Left\<close>
  SS6 writes \<open>r\<close> at \<open>c5_pos = 2\<close>; for \<open>AE_Home\<close>/\<open>AE_Right\<close>
  SS8 writes \<open>r\<close> at \<open>c7_pos = 2\<close>; the other substeps are off
  cell 2.  \<close>
lemma ae_fwd_c8_at_two_for_pos1:
  fixes M :: "('q, 'a) mttm"
    and c' c4 c5 c6 c7 c8 :: "('c :: enum \<Rightarrow> 'a,
                'q \<times> ('a, 'c) ae_stage) mt_config"
    and q5 q6 :: 'q
    and ofs5 ofs6 :: "nat \<Rightarrow> 'c"
    and buf5 buf6 :: "nat \<Rightarrow> ('c \<Rightarrow> 'a) \<times> ('c \<Rightarrow> 'a) \<times> ('c \<Rightarrow> 'a)"
    and dest5 dest6 :: "nat \<Rightarrow> ae_dest"
  assumes step5: "(c4, c5) \<in> mttm_step (alphabet_enlarge_delta M)"
      and c5_state: "mt_state c5 = (q5, ofs5, buf5, dest5, SS6)"
      and tape_c4_eq_c': "mt_tape c4 = mt_tape c'"
      and buf5_not_le_per_tape:
            "\<forall>k<k_tm M. (mt_pos c' k = 0
                  \<longrightarrow> fst (buf5 k) \<noteq> LE_block (le_tm M)
                  \<and> snd (snd (buf5 k)) \<noteq> LE_block (le_tm M))
                \<and> (mt_pos c' k = 1
                  \<longrightarrow> fst (snd (buf5 k)) \<noteq> LE_block (le_tm M)
                  \<and> snd (snd (buf5 k)) \<noteq> LE_block (le_tm M))
                \<and> (mt_pos c' k \<ge> 2
                  \<longrightarrow> fst (buf5 k) \<noteq> LE_block (le_tm M)
                  \<and> fst (snd (buf5 k)) \<noteq> LE_block (le_tm M)
                  \<and> snd (snd (buf5 k)) \<noteq> LE_block (le_tm M))"
      and right_not_le_c':
            "\<forall>k. mt_tape c' k (mt_pos c' k + 1) \<noteq> LE_block (le_tm M)"
      and c4_pos: "\<And>kk. kk < k_tm M \<Longrightarrow> mt_pos c4 kk = mt_pos c' kk"
      and c5_pos_for_pos1:
            "\<And>kk. kk < k_tm M \<Longrightarrow> mt_pos c' kk = 1 \<Longrightarrow> dest5 kk \<noteq> AE_Left
                  \<Longrightarrow> mt_pos c5 kk = 0"
      and step6_sub: "(c5, c6) \<in> mttm_step (ae_delta_ss6_ss7 M)"
      and step6: "(c5, c6) \<in> mttm_step (alphabet_enlarge_delta M)"
      and step7: "(c6, c7) \<in> mttm_step (alphabet_enlarge_delta M)"
      and c7_state: "mt_state c7 = (q6, ofs6, buf6, dest6, SS8)"
      and buf6_eq_buf5: "buf6 = buf5"
      and dest6_eq_dest5: "dest6 = dest5"
      and c5_pos_for_pos1_dest_left:
            "\<And>kk. kk < k_tm M \<Longrightarrow> mt_pos c' kk = 1 \<Longrightarrow> dest5 kk = AE_Left
                  \<Longrightarrow> mt_pos c5 kk = 2"
      and c7_pos_for_pos1_dest_left:
            "\<And>kk. kk < k_tm M \<Longrightarrow> mt_pos c' kk = 1 \<Longrightarrow> dest5 kk = AE_Left
                  \<Longrightarrow> mt_pos c7 kk = 0"
      and step8_sub: "(c7, c8) \<in> mttm_step (ae_delta_ss8_ss1 M)"
      and step8: "(c7, c8) \<in> mttm_step (alphabet_enlarge_delta M)"
      and c6_pos_for_pos1:
            "\<And>kk. kk < k_tm M \<Longrightarrow> mt_pos c' kk = 1 \<Longrightarrow> mt_pos c6 kk = 1"
      and c7_pos_for_pos1:
            "\<And>kk. kk < k_tm M \<Longrightarrow> mt_pos c' kk = 1
                  \<Longrightarrow> mt_pos c7 kk = (if dest5 kk = AE_Left then 0 else 2)"
  shows "\<And>kk. kk < k_tm M \<Longrightarrow> mt_pos c' kk = 1
            \<Longrightarrow> mt_tape c8 kk 2 = snd (snd (buf5 kk))"
proof -
  fix kk
  assume kklt: "kk < k_tm M"
  assume pos_kk: "mt_pos c' kk = 1"
    obtain ll hh rr where buf5_kk: "buf5 kk = (ll, hh, rr)"
      using prod.exhaust by metis
    have buf6_kk: "buf6 kk = (ll, hh, rr)"
      using buf5_kk buf6_eq_buf5 by simp
    have h_ne_LE: "hh \<noteq> LE_block (le_tm M)"
    proof -
      have "fst (snd (buf5 kk)) \<noteq> LE_block (le_tm M)"
        using buf5_not_le_per_tape[rule_format, OF kklt] pos_kk by blast
      thus ?thesis using buf5_kk by simp
    qed
    have two_ne_c4: "(2 :: nat) \<noteq> mt_pos c4 kk"
      using c4_pos kklt pos_kk by simp
    have c4_at_2_ne_LE: "mt_tape c4 kk 2 \<noteq> LE_block (le_tm M)"
    proof -
      have "mt_tape c4 kk 2 = mt_tape c' kk 2" using tape_c4_eq_c' by simp
      moreover have "mt_tape c' kk (mt_pos c' kk + 1) \<noteq> LE_block (le_tm M)"
        using right_not_le_c' by blast
      ultimately have "mt_tape c4 kk 2 = mt_tape c' kk 2
                       \<and> mt_tape c' kk 2 \<noteq> LE_block (le_tm M)"
        using pos_kk by (simp add: numeral_2_eq_2)
      thus ?thesis by simp
    qed
    have c5_at_2: "mt_tape c5 kk 2 = mt_tape c4 kk 2"
      using mttm_step_tape_off_head[OF step5 two_ne_c4] .
    show "mt_tape c8 kk 2 = snd (snd (buf5 kk))"
    proof (cases "dest5 kk")
      case AE_Left
      \<comment> \<open>SS6 writes \<open>r\<close> at \<open>c5_pos = 2\<close>; SS7/SS8 off cell 2.\<close>
      have c5_pos_kk: "mt_pos c5 kk = 2"
        using c5_pos_for_pos1_dest_left[OF kklt pos_kk AE_Left] .
      obtain qq tts nn qq' aa6 dr6 where
          c5_eq6: "c5 = Config\<^sub>M qq tts nn"
        and c6_eq: "c6 = Config\<^sub>M qq'
                            (\<lambda>k. (tts k)(nn k := aa6 k))
                            (\<lambda>k. go_dir (dr6 k) (nn k))"
        and tr_in: "(qq, \<lambda>k. tts k (nn k), qq', aa6, dr6)
                      \<in> ae_delta_ss6_ss7 M"
        using step6_sub by (auto elim: mttm_step.cases)
      obtain q ofs buf dest where
          qq_eq: "qq = (q, ofs, buf, dest, SS6)"
        and aa6_eq:
            "aa6 = (\<lambda>k. if k < k_tm M then fst (ae_ss6_action (le_tm M)
                                (tts k (nn k)) (buf k) (dest k)) else bl_block (bl_tm M))"
        using tr_in by (auto simp: ae_delta_ss6_ss7_def)
      have qq_state: "qq = (q5, ofs5, buf5, dest5, SS6)"
        using c5_state c5_eq6 by simp
      have buf_eq: "buf = buf5" using qq_eq qq_state by simp
      have dest_eq: "dest = dest5" using qq_eq qq_state by simp
      have nn_kk: "nn kk = mt_pos c5 kk" using c5_eq6 by simp
      have nn_kk_2: "nn kk = 2" using nn_kk c5_pos_kk by simp
      have read_ne_LE: "tts kk (nn kk) \<noteq> LE_block (le_tm M)"
      proof -
        have "tts kk (nn kk) = mt_tape c5 kk (mt_pos c5 kk)"
          using c5_eq6 nn_kk by simp
        also have "\<dots> = mt_tape c5 kk 2" using c5_pos_kk by simp
        also have "\<dots> = mt_tape c4 kk 2" using c5_at_2 .
        finally have "tts kk (nn kk) = mt_tape c4 kk 2" .
        thus ?thesis using c4_at_2_ne_LE by simp
      qed
      have aa6_kk: "aa6 kk = rr"
        using aa6_eq buf_eq dest_eq AE_Left buf5_kk read_ne_LE h_ne_LE kklt by simp
      have c6_at_2: "mt_tape c6 kk 2 = rr"
      proof -
        have "mt_tape c6 kk 2 = aa6 kk" using c6_eq nn_kk_2 by simp
        thus ?thesis using aa6_kk by simp
      qed
      have two_ne_c6_pos: "(2 :: nat) \<noteq> mt_pos c6 kk"
        using c6_pos_for_pos1[OF kklt pos_kk] by simp
      have c7_at_2: "mt_tape c7 kk 2 = mt_tape c6 kk 2"
        using mttm_step_tape_off_head[OF step7 two_ne_c6_pos] .
      have c7_pos_kk: "mt_pos c7 kk = 0"
        using c7_pos_for_pos1_dest_left[OF kklt pos_kk AE_Left] .
      have two_ne_c7_pos: "(2 :: nat) \<noteq> mt_pos c7 kk"
        using c7_pos_kk by simp
      have c8_at_2: "mt_tape c8 kk 2 = mt_tape c7 kk 2"
        using mttm_step_tape_off_head[OF step8 two_ne_c7_pos] .
      have "mt_tape c8 kk 2 = mt_tape c7 kk 2" using c8_at_2 .
      also have "\<dots> = mt_tape c6 kk 2" using c7_at_2 .
      also have "\<dots> = rr" using c6_at_2 .
      also have "\<dots> = snd (snd (buf5 kk))" using buf5_kk by simp
      finally show ?thesis .
    next
      case AE_Home
      \<comment> \<open>SS6/SS7 off cell 2; SS8 writes \<open>r\<close> at \<open>c7_pos = 2\<close>.\<close>
      have dest_ne_left: "dest5 kk \<noteq> AE_Left" using AE_Home by simp
      have c5_pos_kk: "mt_pos c5 kk = 0"
        using c5_pos_for_pos1[OF kklt pos_kk dest_ne_left] .
      have two_ne_c5_pos: "(2 :: nat) \<noteq> mt_pos c5 kk"
        using c5_pos_kk by simp
      have c6_at_2_eq_c4: "mt_tape c6 kk 2 = mt_tape c4 kk 2"
      proof -
        have "mt_tape c6 kk 2 = mt_tape c5 kk 2"
          using mttm_step_tape_off_head[OF step6 two_ne_c5_pos] .
        also have "\<dots> = mt_tape c4 kk 2" using c5_at_2 .
        finally show ?thesis .
      qed
      have two_ne_c6_pos: "(2 :: nat) \<noteq> mt_pos c6 kk"
        using c6_pos_for_pos1[OF kklt pos_kk] by simp
      have c7_at_2_eq_c4: "mt_tape c7 kk 2 = mt_tape c4 kk 2"
      proof -
        have "mt_tape c7 kk 2 = mt_tape c6 kk 2"
          using mttm_step_tape_off_head[OF step7 two_ne_c6_pos] .
        also have "\<dots> = mt_tape c4 kk 2" using c6_at_2_eq_c4 .
        finally show ?thesis .
      qed
      have c7_pos_kk: "mt_pos c7 kk = 2"
        using c7_pos_for_pos1[OF kklt pos_kk] AE_Home by simp
      obtain qq tts nn qq' aa8 dr8 where
          c7_eq8: "c7 = Config\<^sub>M qq tts nn"
        and c8_eq: "c8 = Config\<^sub>M qq'
                            (\<lambda>k. (tts k)(nn k := aa8 k))
                            (\<lambda>k. go_dir (dr8 k) (nn k))"
        and tr_in: "(qq, \<lambda>k. tts k (nn k), qq', aa8, dr8)
                      \<in> ae_delta_ss8_ss1 M"
        using step8_sub by (auto elim: mttm_step.cases)
      obtain q ofs buf dest where
          qq_eq: "qq = (q, ofs, buf, dest, SS8)"
        and aa8_eq:
            "aa8 = (\<lambda>k. if k < k_tm M then fst (ae_ss8_action (le_tm M)
                                (tts k (nn k)) (buf k) (dest k)) else bl_block (bl_tm M))"
        using tr_in by (auto simp: ae_delta_ss8_ss1_def)
      have qq_state: "qq = (q6, ofs6, buf6, dest6, SS8)"
        using c7_state c7_eq8 by simp
      have buf_eq: "buf = buf6" using qq_eq qq_state by simp
      have dest_eq: "dest = dest6" using qq_eq qq_state by simp
      have nn_kk: "nn kk = mt_pos c7 kk" using c7_eq8 by simp
      have nn_kk_2: "nn kk = 2" using nn_kk c7_pos_kk by simp
      have read_ne_LE: "tts kk (nn kk) \<noteq> LE_block (le_tm M)"
      proof -
        have "tts kk (nn kk) = mt_tape c7 kk (mt_pos c7 kk)"
          using c7_eq8 nn_kk by simp
        also have "\<dots> = mt_tape c7 kk 2" using c7_pos_kk by simp
        also have "\<dots> = mt_tape c4 kk 2" using c7_at_2_eq_c4 .
        finally have "tts kk (nn kk) = mt_tape c4 kk 2" .
        thus ?thesis using c4_at_2_ne_LE by simp
      qed
      have dest6_AE_Home: "dest6 kk = AE_Home"
        using AE_Home dest6_eq_dest5 by simp
      have aa8_kk: "aa8 kk = rr"
        using aa8_eq buf_eq dest_eq dest6_AE_Home buf6_kk h_ne_LE read_ne_LE kklt
        by simp
      have "mt_tape c8 kk 2 = aa8 kk" using c8_eq nn_kk_2 by simp
      also have "\<dots> = rr" using aa8_kk .
      also have "\<dots> = snd (snd (buf5 kk))" using buf5_kk by simp
      finally show ?thesis .
    next
      case AE_Right
      \<comment> \<open>SS6/SS7 off cell 2; SS8 writes \<open>r\<close> at \<open>c7_pos = 2\<close>.\<close>
      have dest_ne_left: "dest5 kk \<noteq> AE_Left" using AE_Right by simp
      have c5_pos_kk: "mt_pos c5 kk = 0"
        using c5_pos_for_pos1[OF kklt pos_kk dest_ne_left] .
      have two_ne_c5_pos: "(2 :: nat) \<noteq> mt_pos c5 kk"
        using c5_pos_kk by simp
      have c6_at_2_eq_c4: "mt_tape c6 kk 2 = mt_tape c4 kk 2"
      proof -
        have "mt_tape c6 kk 2 = mt_tape c5 kk 2"
          using mttm_step_tape_off_head[OF step6 two_ne_c5_pos] .
        also have "\<dots> = mt_tape c4 kk 2" using c5_at_2 .
        finally show ?thesis .
      qed
      have two_ne_c6_pos: "(2 :: nat) \<noteq> mt_pos c6 kk"
        using c6_pos_for_pos1[OF kklt pos_kk] by simp
      have c7_at_2_eq_c4: "mt_tape c7 kk 2 = mt_tape c4 kk 2"
      proof -
        have "mt_tape c7 kk 2 = mt_tape c6 kk 2"
          using mttm_step_tape_off_head[OF step7 two_ne_c6_pos] .
        also have "\<dots> = mt_tape c4 kk 2" using c6_at_2_eq_c4 .
        finally show ?thesis .
      qed
      have c7_pos_kk: "mt_pos c7 kk = 2"
        using c7_pos_for_pos1[OF kklt pos_kk] AE_Right by simp
      obtain qq tts nn qq' aa8 dr8 where
          c7_eq8: "c7 = Config\<^sub>M qq tts nn"
        and c8_eq: "c8 = Config\<^sub>M qq'
                            (\<lambda>k. (tts k)(nn k := aa8 k))
                            (\<lambda>k. go_dir (dr8 k) (nn k))"
        and tr_in: "(qq, \<lambda>k. tts k (nn k), qq', aa8, dr8)
                      \<in> ae_delta_ss8_ss1 M"
        using step8_sub by (auto elim: mttm_step.cases)
      obtain q ofs buf dest where
          qq_eq: "qq = (q, ofs, buf, dest, SS8)"
        and aa8_eq:
            "aa8 = (\<lambda>k. if k < k_tm M then fst (ae_ss8_action (le_tm M)
                                (tts k (nn k)) (buf k) (dest k)) else bl_block (bl_tm M))"
        using tr_in by (auto simp: ae_delta_ss8_ss1_def)
      have qq_state: "qq = (q6, ofs6, buf6, dest6, SS8)"
        using c7_state c7_eq8 by simp
      have buf_eq: "buf = buf6" using qq_eq qq_state by simp
      have dest_eq: "dest = dest6" using qq_eq qq_state by simp
      have nn_kk: "nn kk = mt_pos c7 kk" using c7_eq8 by simp
      have nn_kk_2: "nn kk = 2" using nn_kk c7_pos_kk by simp
      have read_ne_LE: "tts kk (nn kk) \<noteq> LE_block (le_tm M)"
      proof -
        have "tts kk (nn kk) = mt_tape c7 kk (mt_pos c7 kk)"
          using c7_eq8 nn_kk by simp
        also have "\<dots> = mt_tape c7 kk 2" using c7_pos_kk by simp
        also have "\<dots> = mt_tape c4 kk 2" using c7_at_2_eq_c4 .
        finally have "tts kk (nn kk) = mt_tape c4 kk 2" .
        thus ?thesis using c4_at_2_ne_LE by simp
      qed
      have dest6_AE_Right: "dest6 kk = AE_Right"
        using AE_Right dest6_eq_dest5 by simp
      have aa8_kk: "aa8 kk = rr"
        using aa8_eq buf_eq dest_eq dest6_AE_Right buf6_kk h_ne_LE read_ne_LE kklt
        by simp
      have "mt_tape c8 kk 2 = aa8 kk" using c8_eq nn_kk_2 by simp
      also have "\<dots> = rr" using aa8_kk .
      also have "\<dots> = snd (snd (buf5 kk))" using buf5_kk by simp
      finally show ?thesis .
    qed
  qed

text \<open>Reconstruction leaf of \<open>ae_simulates_forward_stage_general\<close>:
  the in-window \<open>c8\<close> value at block \<open>pos + 1\<close> for a
  steady tape (\<open>mt_pos c' kk \<ge> 2\<close>).  Uniformly
  \<open>c8@(pos+1) = rr\<close> (the right buffer slot).  Three-way
  \<open>dest5\<close> case-split: for \<open>AE_Left\<close> SS6 writes \<open>r\<close> at
  \<open>c5_pos = pos + 1\<close>; for \<open>AE_Home\<close>/\<open>AE_Right\<close> SS8 writes
  \<open>r\<close> at \<open>c7_pos = pos + 1\<close>; the other substeps are off
  cell \<open>pos + 1\<close>.  \<close>
lemma ae_fwd_c8_at_pos_plus_1_ge2:
  fixes M :: "('q, 'a) mttm"
    and c' c4 c5 c6 c7 c8 :: "('c :: enum \<Rightarrow> 'a,
                'q \<times> ('a, 'c) ae_stage) mt_config"
    and q5 q6 :: 'q
    and ofs5 ofs6 :: "nat \<Rightarrow> 'c"
    and buf5 buf6 :: "nat \<Rightarrow> ('c \<Rightarrow> 'a) \<times> ('c \<Rightarrow> 'a) \<times> ('c \<Rightarrow> 'a)"
    and dest5 dest6 :: "nat \<Rightarrow> ae_dest"
  assumes step5: "(c4, c5) \<in> mttm_step (alphabet_enlarge_delta M)"
      and c5_state: "mt_state c5 = (q5, ofs5, buf5, dest5, SS6)"
      and tape_c4_eq_c': "mt_tape c4 = mt_tape c'"
      and buf5_not_le_per_tape:
            "\<forall>k<k_tm M. (mt_pos c' k = 0
                  \<longrightarrow> fst (buf5 k) \<noteq> LE_block (le_tm M)
                  \<and> snd (snd (buf5 k)) \<noteq> LE_block (le_tm M))
                \<and> (mt_pos c' k = 1
                  \<longrightarrow> fst (snd (buf5 k)) \<noteq> LE_block (le_tm M)
                  \<and> snd (snd (buf5 k)) \<noteq> LE_block (le_tm M))
                \<and> (mt_pos c' k \<ge> 2
                  \<longrightarrow> fst (buf5 k) \<noteq> LE_block (le_tm M)
                  \<and> fst (snd (buf5 k)) \<noteq> LE_block (le_tm M)
                  \<and> snd (snd (buf5 k)) \<noteq> LE_block (le_tm M))"
      and right_not_le_c':
            "\<forall>k. mt_tape c' k (mt_pos c' k + 1) \<noteq> LE_block (le_tm M)"
      and c4_pos: "\<And>kk. kk < k_tm M \<Longrightarrow> mt_pos c4 kk = mt_pos c' kk"
      and step6_sub: "(c5, c6) \<in> mttm_step (ae_delta_ss6_ss7 M)"
      and step6: "(c5, c6) \<in> mttm_step (alphabet_enlarge_delta M)"
      and step7: "(c6, c7) \<in> mttm_step (alphabet_enlarge_delta M)"
      and c7_state: "mt_state c7 = (q6, ofs6, buf6, dest6, SS8)"
      and buf6_eq_buf5: "buf6 = buf5"
      and dest6_eq_dest5: "dest6 = dest5"
      and step8_sub: "(c7, c8) \<in> mttm_step (ae_delta_ss8_ss1 M)"
      and step8: "(c7, c8) \<in> mttm_step (alphabet_enlarge_delta M)"
      and c5_pos_for_pos_ge2:
            "\<And>kk. kk < k_tm M \<Longrightarrow> mt_pos c' kk \<ge> 2 \<Longrightarrow> dest5 kk \<noteq> AE_Left
                  \<Longrightarrow> mt_pos c5 kk = mt_pos c' kk - 1"
      and c5_pos_for_pos_ge2_dest_left:
            "\<And>kk. kk < k_tm M \<Longrightarrow> mt_pos c' kk \<ge> 2 \<Longrightarrow> dest5 kk = AE_Left
                  \<Longrightarrow> mt_pos c5 kk = mt_pos c' kk + 1"
      and c6_pos_for_pos_ge2:
            "\<And>kk. kk < k_tm M \<Longrightarrow> mt_pos c' kk \<ge> 2 \<Longrightarrow> mt_pos c6 kk = mt_pos c' kk"
      and c7_pos_for_pos_ge2:
            "\<And>kk. kk < k_tm M \<Longrightarrow> mt_pos c' kk \<ge> 2
                  \<Longrightarrow> mt_pos c7 kk = (if dest5 kk = AE_Left
                  then mt_pos c' kk - 1
                  else mt_pos c' kk + 1)"
  shows "\<And>kk. kk < k_tm M \<Longrightarrow> mt_pos c' kk \<ge> 2
            \<Longrightarrow> mt_tape c8 kk (mt_pos c' kk + 1) = snd (snd (buf5 kk))"
proof -
  fix kk
  assume kklt: "kk < k_tm M"
  assume hge2: "mt_pos c' kk \<ge> 2"
    obtain ll hh rr where buf5_kk: "buf5 kk = (ll, hh, rr)"
      using prod.exhaust by metis
    have buf6_kk: "buf6 kk = (ll, hh, rr)"
      using buf5_kk buf6_eq_buf5 by simp
    have h_ne_LE: "hh \<noteq> LE_block (le_tm M)"
    proof -
      have "fst (snd (buf5 kk)) \<noteq> LE_block (le_tm M)"
        using buf5_not_le_per_tape[rule_format, OF kklt] hge2 by blast
      thus ?thesis using buf5_kk by simp
    qed
    have c4_kk_eq: "mt_pos c4 kk = mt_pos c' kk" using c4_pos kklt by simp
    have pp1_ne_c4: "(mt_pos c' kk + 1) \<noteq> mt_pos c4 kk"
      using c4_kk_eq by linarith
    have c4_at_pp1_ne_LE:
        "mt_tape c4 kk (mt_pos c' kk + 1) \<noteq> LE_block (le_tm M)"
    proof -
      have "mt_tape c4 kk (mt_pos c' kk + 1) = mt_tape c' kk (mt_pos c' kk + 1)"
        using tape_c4_eq_c' by simp
      moreover have "mt_tape c' kk (mt_pos c' kk + 1) \<noteq> LE_block (le_tm M)"
        using right_not_le_c' by blast
      ultimately show ?thesis by simp
    qed
    have c5_at_pp1_eq_c4:
        "mt_tape c5 kk (mt_pos c' kk + 1) = mt_tape c4 kk (mt_pos c' kk + 1)"
      using mttm_step_tape_off_head[OF step5 pp1_ne_c4] .
    show "mt_tape c8 kk (mt_pos c' kk + 1) = snd (snd (buf5 kk))"
    proof (cases "dest5 kk")
      case AE_Left
      \<comment> \<open>SS6 writes \<open>r\<close> at \<open>c5_pos = pos + 1\<close>; SS7/SS8 off pos+1.\<close>
      have c5_pos_kk: "mt_pos c5 kk = mt_pos c' kk + 1"
        using c5_pos_for_pos_ge2_dest_left[OF kklt hge2 AE_Left] .
      obtain qq tts nn qq' aa6 dr6 where
          c5_eq6: "c5 = Config\<^sub>M qq tts nn"
        and c6_eq: "c6 = Config\<^sub>M qq'
                            (\<lambda>k. (tts k)(nn k := aa6 k))
                            (\<lambda>k. go_dir (dr6 k) (nn k))"
        and tr_in: "(qq, \<lambda>k. tts k (nn k), qq', aa6, dr6)
                      \<in> ae_delta_ss6_ss7 M"
        using step6_sub by (auto elim: mttm_step.cases)
      obtain q ofs buf dest where
          qq_eq: "qq = (q, ofs, buf, dest, SS6)"
        and aa6_eq:
            "aa6 = (\<lambda>k. if k < k_tm M then fst (ae_ss6_action (le_tm M)
                                (tts k (nn k)) (buf k) (dest k)) else bl_block (bl_tm M))"
        using tr_in by (auto simp: ae_delta_ss6_ss7_def)
      have qq_state: "qq = (q5, ofs5, buf5, dest5, SS6)"
        using c5_state c5_eq6 by simp
      have buf_eq: "buf = buf5" using qq_eq qq_state by simp
      have dest_eq: "dest = dest5" using qq_eq qq_state by simp
      have nn_kk: "nn kk = mt_pos c5 kk" using c5_eq6 by simp
      have nn_kk_val: "nn kk = mt_pos c' kk + 1" using nn_kk c5_pos_kk by simp
      have read_ne_LE: "tts kk (nn kk) \<noteq> LE_block (le_tm M)"
      proof -
        have "tts kk (nn kk) = mt_tape c5 kk (mt_pos c5 kk)"
          using c5_eq6 nn_kk by simp
        also have "\<dots> = mt_tape c5 kk (mt_pos c' kk + 1)" using c5_pos_kk by simp
        also have "\<dots> = mt_tape c4 kk (mt_pos c' kk + 1)" using c5_at_pp1_eq_c4 .
        finally have "tts kk (nn kk) = mt_tape c4 kk (mt_pos c' kk + 1)" .
        thus ?thesis using c4_at_pp1_ne_LE by simp
      qed
      have aa6_kk: "aa6 kk = rr"
        using aa6_eq buf_eq dest_eq AE_Left buf5_kk read_ne_LE h_ne_LE kklt by simp
      have c6_at_pp1: "mt_tape c6 kk (mt_pos c' kk + 1) = rr"
      proof -
        have "mt_tape c6 kk (mt_pos c' kk + 1) = aa6 kk"
          using c6_eq nn_kk_val by simp
        thus ?thesis using aa6_kk by simp
      qed
      have c6_pos_kk: "mt_pos c6 kk = mt_pos c' kk"
        using c6_pos_for_pos_ge2[OF kklt hge2] .
      have pp1_ne_c6: "(mt_pos c' kk + 1) \<noteq> mt_pos c6 kk"
        using c6_pos_kk by linarith
      have c7_pos_kk: "mt_pos c7 kk = mt_pos c' kk - 1"
        using c7_pos_for_pos_ge2[OF kklt hge2] AE_Left by simp
      have pp1_ne_c7: "(mt_pos c' kk + 1) \<noteq> mt_pos c7 kk"
        using c7_pos_kk hge2 by linarith
      have "mt_tape c8 kk (mt_pos c' kk + 1) = mt_tape c7 kk (mt_pos c' kk + 1)"
        using mttm_step_tape_off_head[OF step8 pp1_ne_c7] .
      also have "\<dots> = mt_tape c6 kk (mt_pos c' kk + 1)"
        using mttm_step_tape_off_head[OF step7 pp1_ne_c6] .
      also have "\<dots> = rr" using c6_at_pp1 .
      also have "\<dots> = snd (snd (buf5 kk))" using buf5_kk by simp
      finally show ?thesis .
    next
      case AE_Home
      \<comment> \<open>SS6/SS7 off pos+1; SS8 writes \<open>r\<close> at \<open>c7_pos = pos + 1\<close>.\<close>
      have dest_ne_left: "dest5 kk \<noteq> AE_Left" using AE_Home by simp
      have c5_pos_kk: "mt_pos c5 kk = mt_pos c' kk - 1"
        using c5_pos_for_pos_ge2[OF kklt hge2 dest_ne_left] .
      have pp1_ne_c5: "(mt_pos c' kk + 1) \<noteq> mt_pos c5 kk"
        using c5_pos_kk hge2 by linarith
      have c6_pos_kk: "mt_pos c6 kk = mt_pos c' kk"
        using c6_pos_for_pos_ge2[OF kklt hge2] .
      have pp1_ne_c6: "(mt_pos c' kk + 1) \<noteq> mt_pos c6 kk"
        using c6_pos_kk by linarith
      have c7_at_pp1_eq_c4:
          "mt_tape c7 kk (mt_pos c' kk + 1) = mt_tape c4 kk (mt_pos c' kk + 1)"
      proof -
        have "mt_tape c7 kk (mt_pos c' kk + 1) = mt_tape c6 kk (mt_pos c' kk + 1)"
          using mttm_step_tape_off_head[OF step7 pp1_ne_c6] .
        also have "\<dots> = mt_tape c5 kk (mt_pos c' kk + 1)"
          using mttm_step_tape_off_head[OF step6 pp1_ne_c5] .
        also have "\<dots> = mt_tape c4 kk (mt_pos c' kk + 1)" using c5_at_pp1_eq_c4 .
        finally show ?thesis .
      qed
      have c7_pos_kk: "mt_pos c7 kk = mt_pos c' kk + 1"
        using c7_pos_for_pos_ge2[OF kklt hge2] AE_Home by simp
      obtain qq tts nn qq' aa8 dr8 where
          c7_eq8: "c7 = Config\<^sub>M qq tts nn"
        and c8_eq: "c8 = Config\<^sub>M qq'
                            (\<lambda>k. (tts k)(nn k := aa8 k))
                            (\<lambda>k. go_dir (dr8 k) (nn k))"
        and tr_in: "(qq, \<lambda>k. tts k (nn k), qq', aa8, dr8)
                      \<in> ae_delta_ss8_ss1 M"
        using step8_sub by (auto elim: mttm_step.cases)
      obtain q ofs buf dest where
          qq_eq: "qq = (q, ofs, buf, dest, SS8)"
        and aa8_eq:
            "aa8 = (\<lambda>k. if k < k_tm M then fst (ae_ss8_action (le_tm M)
                                (tts k (nn k)) (buf k) (dest k)) else bl_block (bl_tm M))"
        using tr_in by (auto simp: ae_delta_ss8_ss1_def)
      have qq_state: "qq = (q6, ofs6, buf6, dest6, SS8)"
        using c7_state c7_eq8 by simp
      have buf_eq: "buf = buf6" using qq_eq qq_state by simp
      have dest_eq: "dest = dest6" using qq_eq qq_state by simp
      have nn_kk: "nn kk = mt_pos c7 kk" using c7_eq8 by simp
      have nn_kk_val: "nn kk = mt_pos c' kk + 1" using nn_kk c7_pos_kk by simp
      have read_ne_LE: "tts kk (nn kk) \<noteq> LE_block (le_tm M)"
      proof -
        have "tts kk (nn kk) = mt_tape c7 kk (mt_pos c7 kk)"
          using c7_eq8 nn_kk by simp
        also have "\<dots> = mt_tape c7 kk (mt_pos c' kk + 1)" using c7_pos_kk by simp
        also have "\<dots> = mt_tape c4 kk (mt_pos c' kk + 1)" using c7_at_pp1_eq_c4 .
        finally have "tts kk (nn kk) = mt_tape c4 kk (mt_pos c' kk + 1)" .
        thus ?thesis using c4_at_pp1_ne_LE by simp
      qed
      have dest6_AE_Home: "dest6 kk = AE_Home"
        using AE_Home dest6_eq_dest5 by simp
      have aa8_kk: "aa8 kk = rr"
        using aa8_eq buf_eq dest_eq dest6_AE_Home buf6_kk h_ne_LE read_ne_LE kklt
        by simp
      have "mt_tape c8 kk (mt_pos c' kk + 1) = aa8 kk"
        using c8_eq nn_kk_val by simp
      also have "\<dots> = rr" using aa8_kk .
      also have "\<dots> = snd (snd (buf5 kk))" using buf5_kk by simp
      finally show ?thesis .
    next
      case AE_Right
      \<comment> \<open>SS6/SS7 off pos+1; SS8 writes \<open>r\<close> at \<open>c7_pos = pos + 1\<close>.\<close>
      have dest_ne_left: "dest5 kk \<noteq> AE_Left" using AE_Right by simp
      have c5_pos_kk: "mt_pos c5 kk = mt_pos c' kk - 1"
        using c5_pos_for_pos_ge2[OF kklt hge2 dest_ne_left] .
      have pp1_ne_c5: "(mt_pos c' kk + 1) \<noteq> mt_pos c5 kk"
        using c5_pos_kk hge2 by linarith
      have c6_pos_kk: "mt_pos c6 kk = mt_pos c' kk"
        using c6_pos_for_pos_ge2[OF kklt hge2] .
      have pp1_ne_c6: "(mt_pos c' kk + 1) \<noteq> mt_pos c6 kk"
        using c6_pos_kk by linarith
      have c7_at_pp1_eq_c4:
          "mt_tape c7 kk (mt_pos c' kk + 1) = mt_tape c4 kk (mt_pos c' kk + 1)"
      proof -
        have "mt_tape c7 kk (mt_pos c' kk + 1) = mt_tape c6 kk (mt_pos c' kk + 1)"
          using mttm_step_tape_off_head[OF step7 pp1_ne_c6] .
        also have "\<dots> = mt_tape c5 kk (mt_pos c' kk + 1)"
          using mttm_step_tape_off_head[OF step6 pp1_ne_c5] .
        also have "\<dots> = mt_tape c4 kk (mt_pos c' kk + 1)" using c5_at_pp1_eq_c4 .
        finally show ?thesis .
      qed
      have c7_pos_kk: "mt_pos c7 kk = mt_pos c' kk + 1"
        using c7_pos_for_pos_ge2[OF kklt hge2] AE_Right by simp
      obtain qq tts nn qq' aa8 dr8 where
          c7_eq8: "c7 = Config\<^sub>M qq tts nn"
        and c8_eq: "c8 = Config\<^sub>M qq'
                            (\<lambda>k. (tts k)(nn k := aa8 k))
                            (\<lambda>k. go_dir (dr8 k) (nn k))"
        and tr_in: "(qq, \<lambda>k. tts k (nn k), qq', aa8, dr8)
                      \<in> ae_delta_ss8_ss1 M"
        using step8_sub by (auto elim: mttm_step.cases)
      obtain q ofs buf dest where
          qq_eq: "qq = (q, ofs, buf, dest, SS8)"
        and aa8_eq:
            "aa8 = (\<lambda>k. if k < k_tm M then fst (ae_ss8_action (le_tm M)
                                (tts k (nn k)) (buf k) (dest k)) else bl_block (bl_tm M))"
        using tr_in by (auto simp: ae_delta_ss8_ss1_def)
      have qq_state: "qq = (q6, ofs6, buf6, dest6, SS8)"
        using c7_state c7_eq8 by simp
      have buf_eq: "buf = buf6" using qq_eq qq_state by simp
      have dest_eq: "dest = dest6" using qq_eq qq_state by simp
      have nn_kk: "nn kk = mt_pos c7 kk" using c7_eq8 by simp
      have nn_kk_val: "nn kk = mt_pos c' kk + 1" using nn_kk c7_pos_kk by simp
      have read_ne_LE: "tts kk (nn kk) \<noteq> LE_block (le_tm M)"
      proof -
        have "tts kk (nn kk) = mt_tape c7 kk (mt_pos c7 kk)"
          using c7_eq8 nn_kk by simp
        also have "\<dots> = mt_tape c7 kk (mt_pos c' kk + 1)" using c7_pos_kk by simp
        also have "\<dots> = mt_tape c4 kk (mt_pos c' kk + 1)" using c7_at_pp1_eq_c4 .
        finally have "tts kk (nn kk) = mt_tape c4 kk (mt_pos c' kk + 1)" .
        thus ?thesis using c4_at_pp1_ne_LE by simp
      qed
      have dest6_AE_Right: "dest6 kk = AE_Right"
        using AE_Right dest6_eq_dest5 by simp
      have aa8_kk: "aa8 kk = rr"
        using aa8_eq buf_eq dest_eq dest6_AE_Right buf6_kk h_ne_LE read_ne_LE kklt
        by simp
      have "mt_tape c8 kk (mt_pos c' kk + 1) = aa8 kk"
        using c8_eq nn_kk_val by simp
      also have "\<dots> = rr" using aa8_kk .
      also have "\<dots> = snd (snd (buf5 kk))" using buf5_kk by simp
      finally show ?thesis .
    qed
  qed

text \<open>Reconstruction leaf of \<open>ae_simulates_forward_stage_general\<close>:
  the \<open>c8\<close> head position for a steady tape
  (\<open>mt_pos c' kk \<ge> 2\<close>), as a \<open>dest5\<close>-case displacement of
  \<open>mt_pos c' kk\<close> (\<open>AE_Left\<close> -> \<open>pos - 1\<close>, \<open>AE_Home\<close> ->
  \<open>pos\<close>, \<open>AE_Right\<close> -> \<open>pos + 1\<close>).  SS8's action reads the
  steady-window head cell and steps per the recorded \<open>dest\<close>.
  \<close>
lemma ae_fwd_c8_pos_for_pos_ge2:
  fixes M :: "('q, 'a) mttm"
    and c' c4 c5 c6 c7 c8 :: "('c :: enum \<Rightarrow> 'a,
                'q \<times> ('a, 'c) ae_stage) mt_config"
    and q5 q6 :: 'q
    and ofs5 ofs6 :: "nat \<Rightarrow> 'c"
    and buf5 buf6 :: "nat \<Rightarrow> ('c \<Rightarrow> 'a) \<times> ('c \<Rightarrow> 'a) \<times> ('c \<Rightarrow> 'a)"
    and dest5 dest6 :: "nat \<Rightarrow> ae_dest"
  assumes step5: "(c4, c5) \<in> mttm_step (alphabet_enlarge_delta M)"
      and tape_c4_eq_c': "mt_tape c4 = mt_tape c'"
      and buf5_not_le_per_tape:
            "\<forall>k<k_tm M. (mt_pos c' k = 0
                  \<longrightarrow> fst (buf5 k) \<noteq> LE_block (le_tm M)
                  \<and> snd (snd (buf5 k)) \<noteq> LE_block (le_tm M))
                \<and> (mt_pos c' k = 1
                  \<longrightarrow> fst (snd (buf5 k)) \<noteq> LE_block (le_tm M)
                  \<and> snd (snd (buf5 k)) \<noteq> LE_block (le_tm M))
                \<and> (mt_pos c' k \<ge> 2
                  \<longrightarrow> fst (buf5 k) \<noteq> LE_block (le_tm M)
                  \<and> fst (snd (buf5 k)) \<noteq> LE_block (le_tm M)
                  \<and> snd (snd (buf5 k)) \<noteq> LE_block (le_tm M))"
      and right_not_le_c':
            "\<forall>k. mt_tape c' k (mt_pos c' k + 1) \<noteq> LE_block (le_tm M)"
      and c4_pos: "\<And>kk. kk < k_tm M \<Longrightarrow> mt_pos c4 kk = mt_pos c' kk"
      and step6: "(c5, c6) \<in> mttm_step (alphabet_enlarge_delta M)"
      and step7: "(c6, c7) \<in> mttm_step (alphabet_enlarge_delta M)"
      and c7_state: "mt_state c7 = (q6, ofs6, buf6, dest6, SS8)"
      and buf6_eq_buf5: "buf6 = buf5"
      and dest6_eq_dest5: "dest6 = dest5"
      and step8_sub: "(c7, c8) \<in> mttm_step (ae_delta_ss8_ss1 M)"
      and c5_pos_for_pos_ge2:
            "\<And>kk. kk < k_tm M \<Longrightarrow> mt_pos c' kk \<ge> 2 \<Longrightarrow> dest5 kk \<noteq> AE_Left
                  \<Longrightarrow> mt_pos c5 kk = mt_pos c' kk - 1"
      and c5_pos_for_pos_ge2_dest_left:
            "\<And>kk. kk < k_tm M \<Longrightarrow> mt_pos c' kk \<ge> 2 \<Longrightarrow> dest5 kk = AE_Left
                  \<Longrightarrow> mt_pos c5 kk = mt_pos c' kk + 1"
      and left_not_le_c'_steady:
            "\<forall>k. mt_pos c' k \<ge> 2
                  \<longrightarrow> mt_tape c' k (mt_pos c' k - 1) \<noteq> LE_block (le_tm M)"
      and c6_pos_for_pos_ge2:
            "\<And>kk. kk < k_tm M \<Longrightarrow> mt_pos c' kk \<ge> 2 \<Longrightarrow> mt_pos c6 kk = mt_pos c' kk"
      and c7_pos_for_pos_ge2:
            "\<And>kk. kk < k_tm M \<Longrightarrow> mt_pos c' kk \<ge> 2
                  \<Longrightarrow> mt_pos c7 kk = (if dest5 kk = AE_Left
                  then mt_pos c' kk - 1
                  else mt_pos c' kk + 1)"
  shows "\<And>kk. kk < k_tm M \<Longrightarrow> mt_pos c' kk \<ge> 2
            \<Longrightarrow> mt_pos c8 kk = (case dest5 kk of
                                  AE_Left  \<Rightarrow> mt_pos c' kk - 1
                                | AE_Home  \<Rightarrow> mt_pos c' kk
                                | AE_Right \<Rightarrow> mt_pos c' kk + 1)"
proof -
  fix kk
  assume kklt: "kk < k_tm M"
  assume hge2: "mt_pos c' kk \<ge> 2"
    obtain qq tts nn qq' aa8 dr8 where
        c7_eq8: "c7 = Config\<^sub>M qq tts nn"
      and c8_eq: "c8 = Config\<^sub>M qq'
                          (\<lambda>k. (tts k)(nn k := aa8 k))
                          (\<lambda>k. go_dir (dr8 k) (nn k))"
      and tr_in: "(qq, \<lambda>k. tts k (nn k), qq', aa8, dr8)
                    \<in> ae_delta_ss8_ss1 M"
      using step8_sub by (auto elim: mttm_step.cases)
    obtain q ofs buf dest where
        qq_eq: "qq = (q, ofs, buf, dest, SS8)"
      and dr8_eq:
          "dr8 = (\<lambda>k. if k < k_tm M then snd (ae_ss8_action (le_tm M)
                              (tts k (nn k)) (buf k) (dest k)) else dir.N)"
      using tr_in by (auto simp: ae_delta_ss8_ss1_def)
    have qq_state: "qq = (q6, ofs6, buf6, dest6, SS8)"
      using c7_state c7_eq8 by simp
    have buf_eq: "buf = buf6" using qq_eq qq_state by simp
    have dest_eq: "dest = dest6" using qq_eq qq_state by simp
    have nn_kk: "nn kk = mt_pos c7 kk" using c7_eq8 by simp
    obtain ll hh rr where buf5_kk: "buf5 kk = (ll, hh, rr)"
      using prod.exhaust by metis
    have buf6_kk: "buf6 kk = (ll, hh, rr)"
      using buf5_kk buf6_eq_buf5 by simp
    have h_ne_LE: "hh \<noteq> LE_block (le_tm M)"
    proof -
      have "fst (snd (buf5 kk)) \<noteq> LE_block (le_tm M)"
        using buf5_not_le_per_tape[rule_format, OF kklt] hge2 by blast
      thus ?thesis using buf5_kk by simp
    qed
    have c4_kk: "mt_pos c4 kk = mt_pos c' kk" using c4_pos kklt by simp
    show "mt_pos c8 kk = (case dest5 kk of
                            AE_Left  \<Rightarrow> mt_pos c' kk - 1
                          | AE_Home  \<Rightarrow> mt_pos c' kk
                          | AE_Right \<Rightarrow> mt_pos c' kk + 1)"
    proof (cases "dest5 kk")
      case AE_Left
      have c7_kk: "mt_pos c7 kk = mt_pos c' kk - 1"
        using c7_pos_for_pos_ge2[OF kklt hge2] AE_Left by simp
      have nn_kk_val: "nn kk = mt_pos c' kk - 1" using nn_kk c7_kk by simp
      have c5_pos_kk: "mt_pos c5 kk = mt_pos c' kk + 1"
        using c5_pos_for_pos_ge2_dest_left[OF kklt hge2 AE_Left] .
      have pm1_ne_c6: "(mt_pos c' kk - 1) \<noteq> mt_pos c6 kk"
        using c6_pos_for_pos_ge2[OF kklt hge2] hge2 by linarith
      have pm1_ne_c5: "(mt_pos c' kk - 1) \<noteq> mt_pos c5 kk"
        using c5_pos_kk hge2 by linarith
      have pm1_ne_c4: "(mt_pos c' kk - 1) \<noteq> mt_pos c4 kk"
        using c4_kk hge2 by linarith
      have c7_at_addr:
          "mt_tape c7 kk (mt_pos c' kk - 1) = mt_tape c' kk (mt_pos c' kk - 1)"
      proof -
        have "mt_tape c7 kk (mt_pos c' kk - 1) = mt_tape c6 kk (mt_pos c' kk - 1)"
          using mttm_step_tape_off_head[OF step7 pm1_ne_c6] .
        also have "\<dots> = mt_tape c5 kk (mt_pos c' kk - 1)"
          using mttm_step_tape_off_head[OF step6 pm1_ne_c5] .
        also have "\<dots> = mt_tape c4 kk (mt_pos c' kk - 1)"
          using mttm_step_tape_off_head[OF step5 pm1_ne_c4] .
        also have "\<dots> = mt_tape c' kk (mt_pos c' kk - 1)"
          using tape_c4_eq_c' by simp
        finally show ?thesis .
      qed
      have read_ne_LE: "tts kk (nn kk) \<noteq> LE_block (le_tm M)"
      proof -
        have "tts kk (nn kk) = mt_tape c7 kk (mt_pos c7 kk)"
          using c7_eq8 nn_kk by simp
        also have "\<dots> = mt_tape c7 kk (mt_pos c' kk - 1)"
          using c7_kk by simp
        also have "\<dots> = mt_tape c' kk (mt_pos c' kk - 1)" using c7_at_addr .
        finally have read_eq:
            "tts kk (nn kk) = mt_tape c' kk (mt_pos c' kk - 1)" .
        have "mt_tape c' kk (mt_pos c' kk - 1) \<noteq> LE_block (le_tm M)"
          using left_not_le_c'_steady hge2 by blast
        thus ?thesis using read_eq by simp
      qed
      have dest6_AE_Left: "dest6 kk = AE_Left"
        using AE_Left dest6_eq_dest5 by simp
      have dr8_kk: "dr8 kk = dir.N"
        using dr8_eq buf_eq dest_eq dest6_AE_Left buf6_kk h_ne_LE read_ne_LE kklt
        by simp
      have "mt_pos c8 kk = go_dir (dr8 kk) (nn kk)"
        using c8_eq by simp
      also have "\<dots> = nn kk" using dr8_kk by simp
      also have "\<dots> = mt_pos c' kk - 1" using nn_kk_val .
      finally show ?thesis using AE_Left by simp
    next
      case AE_Home
      have c7_kk: "mt_pos c7 kk = mt_pos c' kk + 1"
        using c7_pos_for_pos_ge2[OF kklt hge2] AE_Home by simp
      have nn_kk_val: "nn kk = mt_pos c' kk + 1" using nn_kk c7_kk by simp
      have dest_ne_left: "dest5 kk \<noteq> AE_Left" using AE_Home by simp
      have c5_pos_kk: "mt_pos c5 kk = mt_pos c' kk - 1"
        using c5_pos_for_pos_ge2[OF kklt hge2 dest_ne_left] .
      have pp1_ne_c6: "(mt_pos c' kk + 1) \<noteq> mt_pos c6 kk"
        using c6_pos_for_pos_ge2[OF kklt hge2] by simp
      have pp1_ne_c5: "(mt_pos c' kk + 1) \<noteq> mt_pos c5 kk"
        using c5_pos_kk hge2 by linarith
      have pp1_ne_c4: "(mt_pos c' kk + 1) \<noteq> mt_pos c4 kk"
        using c4_kk by simp
      have c7_at_addr:
          "mt_tape c7 kk (mt_pos c' kk + 1) = mt_tape c' kk (mt_pos c' kk + 1)"
      proof -
        have "mt_tape c7 kk (mt_pos c' kk + 1) = mt_tape c6 kk (mt_pos c' kk + 1)"
          using mttm_step_tape_off_head[OF step7 pp1_ne_c6] .
        also have "\<dots> = mt_tape c5 kk (mt_pos c' kk + 1)"
          using mttm_step_tape_off_head[OF step6 pp1_ne_c5] .
        also have "\<dots> = mt_tape c4 kk (mt_pos c' kk + 1)"
          using mttm_step_tape_off_head[OF step5 pp1_ne_c4] .
        also have "\<dots> = mt_tape c' kk (mt_pos c' kk + 1)"
          using tape_c4_eq_c' by simp
        finally show ?thesis .
      qed
      have read_ne_LE: "tts kk (nn kk) \<noteq> LE_block (le_tm M)"
      proof -
        have "tts kk (nn kk) = mt_tape c7 kk (mt_pos c7 kk)"
          using c7_eq8 nn_kk by simp
        also have "\<dots> = mt_tape c7 kk (mt_pos c' kk + 1)"
          using c7_kk by simp
        also have "\<dots> = mt_tape c' kk (mt_pos c' kk + 1)" using c7_at_addr .
        finally have read_eq:
            "tts kk (nn kk) = mt_tape c' kk (mt_pos c' kk + 1)" .
        have "mt_tape c' kk (mt_pos c' kk + 1) \<noteq> LE_block (le_tm M)"
          using right_not_le_c' by blast
        thus ?thesis using read_eq by simp
      qed
      have dest6_AE_Home: "dest6 kk = AE_Home"
        using AE_Home dest6_eq_dest5 by simp
      have dr8_kk: "dr8 kk = dir.L"
        using dr8_eq buf_eq dest_eq dest6_AE_Home buf6_kk h_ne_LE read_ne_LE kklt
        by simp
      have "mt_pos c8 kk = go_dir (dr8 kk) (nn kk)"
        using c8_eq by simp
      also have "\<dots> = (nn kk) - 1" using dr8_kk by simp
      also have "\<dots> = (mt_pos c' kk + 1) - 1" using nn_kk_val by simp
      also have "\<dots> = mt_pos c' kk" by simp
      finally show ?thesis using AE_Home by simp
    next
      case AE_Right
      have c7_kk: "mt_pos c7 kk = mt_pos c' kk + 1"
        using c7_pos_for_pos_ge2[OF kklt hge2] AE_Right by simp
      have nn_kk_val: "nn kk = mt_pos c' kk + 1" using nn_kk c7_kk by simp
      have dest_ne_left: "dest5 kk \<noteq> AE_Left" using AE_Right by simp
      have c5_pos_kk: "mt_pos c5 kk = mt_pos c' kk - 1"
        using c5_pos_for_pos_ge2[OF kklt hge2 dest_ne_left] .
      have pp1_ne_c6: "(mt_pos c' kk + 1) \<noteq> mt_pos c6 kk"
        using c6_pos_for_pos_ge2[OF kklt hge2] by simp
      have pp1_ne_c5: "(mt_pos c' kk + 1) \<noteq> mt_pos c5 kk"
        using c5_pos_kk hge2 by linarith
      have pp1_ne_c4: "(mt_pos c' kk + 1) \<noteq> mt_pos c4 kk"
        using c4_kk by simp
      have c7_at_addr:
          "mt_tape c7 kk (mt_pos c' kk + 1) = mt_tape c' kk (mt_pos c' kk + 1)"
      proof -
        have "mt_tape c7 kk (mt_pos c' kk + 1) = mt_tape c6 kk (mt_pos c' kk + 1)"
          using mttm_step_tape_off_head[OF step7 pp1_ne_c6] .
        also have "\<dots> = mt_tape c5 kk (mt_pos c' kk + 1)"
          using mttm_step_tape_off_head[OF step6 pp1_ne_c5] .
        also have "\<dots> = mt_tape c4 kk (mt_pos c' kk + 1)"
          using mttm_step_tape_off_head[OF step5 pp1_ne_c4] .
        also have "\<dots> = mt_tape c' kk (mt_pos c' kk + 1)"
          using tape_c4_eq_c' by simp
        finally show ?thesis .
      qed
      have read_ne_LE: "tts kk (nn kk) \<noteq> LE_block (le_tm M)"
      proof -
        have "tts kk (nn kk) = mt_tape c7 kk (mt_pos c7 kk)"
          using c7_eq8 nn_kk by simp
        also have "\<dots> = mt_tape c7 kk (mt_pos c' kk + 1)"
          using c7_kk by simp
        also have "\<dots> = mt_tape c' kk (mt_pos c' kk + 1)" using c7_at_addr .
        finally have read_eq:
            "tts kk (nn kk) = mt_tape c' kk (mt_pos c' kk + 1)" .
        have "mt_tape c' kk (mt_pos c' kk + 1) \<noteq> LE_block (le_tm M)"
          using right_not_le_c' by blast
        thus ?thesis using read_eq by simp
      qed
      have dest6_AE_Right: "dest6 kk = AE_Right"
        using AE_Right dest6_eq_dest5 by simp
      have dr8_kk: "dr8 kk = dir.N"
        using dr8_eq buf_eq dest_eq dest6_AE_Right buf6_kk h_ne_LE read_ne_LE kklt
        by simp
      have "mt_pos c8 kk = go_dir (dr8 kk) (nn kk)"
        using c8_eq by simp
      also have "\<dots> = nn kk" using dr8_kk by simp
      also have "\<dots> = mt_pos c' kk + 1" using nn_kk_val .
      finally show ?thesis using AE_Right by simp
    qed
  qed

text \<open>Reconstruction leaf of \<open>ae_simulates_forward_stage_general\<close>:
  the position-decode invariant at \<open>c8\<close>.  When \<open>c8\<close> is at
  \<open>SS1\<close> (the non-halt super-step boundary), each simulated head
  \<open>mt_pos cM_k k\<close> is recovered from the M'-side head
  \<open>mt_pos c8 k\<close> and the recorded offset \<open>off k\<close> via
  \<open>ae_decode_pos\<close>.  Per-tape regime case-split on
  \<open>mt_pos c' kk\<close> feeding the three \<open>c8_pos_for_*\<close> head
  trajectories; the \<open>idx = SS1\<close> antecedent rules out the halt
  branch (which would land at \<open>init_stage\<close> = VFwd).  \<close>
lemma ae_fwd_pos_decode_c8:
  fixes M :: "('q, 'a) mttm"
    and c' c8 :: "('c :: enum \<Rightarrow> 'a,
                'q \<times> ('a, 'c) ae_stage) mt_config"
    and cM_k :: "('a, 'q) mt_config"
    and q6 :: 'q
    and ofs5 ofs6 :: "nat \<Rightarrow> 'c"
    and buf5 buf6 :: "nat \<Rightarrow> ('c \<Rightarrow> 'a) \<times> ('c \<Rightarrow> 'a) \<times> ('c \<Rightarrow> 'a)"
    and dest5 :: "nat \<Rightarrow> ae_dest"
  assumes ofs6_eq_ofs5: "ofs6 = ofs5"
      and c8_state: "mt_state c8 = (q6, if q6 \<in> {t_tm M, r_tm M}
                 then init_stage (le_tm M)
                 else (ofs6, buf6, init_dest, SS1))"
      and cM_k_window_general:
            "\<forall>kk<k_tm M. ae_window_invariant_general
                  (mt_tape cM_k kk) (mt_pos cM_k kk)
                  (dest5 kk, ofs5 kk) (buf5 kk)
                  (mt_pos c' kk) (le_tm M)"
      and c8_pos_for_pos0:
            "\<And>kk. kk < k_tm M \<Longrightarrow> mt_pos c' kk = 0
                  \<Longrightarrow> mt_pos c8 kk = (if dest5 kk = AE_Right then 1 else 0)"
      and c8_pos_for_pos_ge2:
            "\<And>kk. kk < k_tm M \<Longrightarrow> mt_pos c' kk \<ge> 2
                  \<Longrightarrow> mt_pos c8 kk = (case dest5 kk of
                  AE_Left  \<Rightarrow> mt_pos c' kk - 1
                  | AE_Home  \<Rightarrow> mt_pos c' kk
                  | AE_Right \<Rightarrow> mt_pos c' kk + 1)"
      and c8_pos_for_pos1:
            "\<And>kk. kk < k_tm M \<Longrightarrow> mt_pos c' kk = 1
                  \<Longrightarrow> mt_pos c8 kk = (case dest5 kk of
                  AE_Left  \<Rightarrow> 0
                  | AE_Home  \<Rightarrow> 1
                  | AE_Right \<Rightarrow> 2)"
  shows "(case mt_state c8 of (_, _, _, _, idx) \<Rightarrow> idx = SS1)
        \<longrightarrow> (\<forall>k<k_tm M. mt_pos cM_k k
                  = ae_decode_pos (mt_pos c8 k)
                      (case mt_state c8 of (_, off, _, _, _) \<Rightarrow> off k))"
proof -
  let ?c = "card (UNIV :: 'c set)"
  show ?thesis
  proof
    assume idx_ss1: "case mt_state c8 of (_, _, _, _, idx) \<Rightarrow> idx = SS1"
    have q6_nhalt: "q6 \<notin> {t_tm M, r_tm M}"
    proof (rule ccontr)
      assume "\<not> q6 \<notin> {t_tm M, r_tm M}"
      hence q6_in: "q6 \<in> {t_tm M, r_tm M}" by simp
      hence c8_eq_halt: "mt_state c8 = (q6, init_stage (le_tm M))"
        using c8_state by simp
      thus False using idx_ss1 by (simp add: init_stage_def)
    qed
    have c8_nh: "mt_state c8 = (q6, ofs6, buf6, init_dest, SS1)"
      using c8_state q6_nhalt by simp
    show "\<forall>k<k_tm M. mt_pos cM_k k
              = ae_decode_pos (mt_pos c8 k)
                  (case mt_state c8 of (_, off, _, _, _) \<Rightarrow> off k)"
    proof (intro allI impI)
      fix kk assume kklt: "kk < k_tm M"
      have ofs_at_c8:
          "(case mt_state c8 of (_, off, _, _, _) \<Rightarrow> off kk) = ofs6 kk"
        using c8_nh by simp
      have ofs5_eq_kk: "ofs5 kk = ofs6 kk" using ofs6_eq_ofs5 by simp
      have wi: "ae_window_invariant_general
                  (mt_tape cM_k kk) (mt_pos cM_k kk)
                  (dest5 kk, ofs5 kk) (buf5 kk)
                  (mt_pos c' kk) (le_tm M)"
        using cM_k_window_general[rule_format, OF kklt] by simp
      consider (le0) "mt_pos c' kk = 0"
             | (le1) "mt_pos c' kk = 1"
             | (steady) "mt_pos c' kk \<ge> 2"
        by linarith
      thus "mt_pos cM_k kk
              = ae_decode_pos (mt_pos c8 kk)
                  (case mt_state c8 of (_, off, _, _, _) \<Rightarrow> off kk)"
      proof cases
        case le0
        have win_le0: "ae_window_invariant_le0
                  (mt_tape cM_k kk) (mt_pos cM_k kk)
                  (dest5 kk, ofs5 kk) (buf5 kk) (le_tm M)"
          using wi le0 unfolding ae_window_invariant_general_def by simp
        show ?thesis
        proof (cases "dest5 kk")
          case AE_Left
          have "False"
            using win_le0 AE_Left
            unfolding ae_window_invariant_le0_def by simp
          thus ?thesis ..
        next
          case AE_Home
          have c8_kk: "mt_pos c8 kk = 0"
            using c8_pos_for_pos0[OF kklt le0] AE_Home by simp
          have mp_cM_k: "mt_pos cM_k kk = 0"
            using win_le0 AE_Home
            unfolding ae_window_invariant_le0_def by simp
          have decode: "ae_decode_pos 0 (ofs6 kk) = 0"
            unfolding ae_decode_pos_def by simp
          show ?thesis using c8_kk mp_cM_k decode ofs_at_c8 by simp
        next
          case AE_Right
          have c8_kk: "mt_pos c8 kk = 1"
            using c8_pos_for_pos0[OF kklt le0] AE_Right by simp
          have mp_cM_k: "mt_pos cM_k kk = Suc (c_idx (ofs5 kk))"
            using win_le0 AE_Right
            unfolding ae_window_invariant_le0_def by simp
          have decode: "ae_decode_pos 1 (ofs6 kk) = Suc (c_idx (ofs6 kk))"
            unfolding ae_decode_pos_def by simp
          show ?thesis
            using c8_kk mp_cM_k decode ofs_at_c8 ofs5_eq_kk by simp
        qed
      next
        case le1
        have win_le1: "ae_window_invariant_le1
                  (mt_tape cM_k kk) (mt_pos cM_k kk)
                  (dest5 kk, ofs5 kk) (buf5 kk) (le_tm M)"
          using wi le1 unfolding ae_window_invariant_general_def by simp
        show ?thesis
        proof (cases "dest5 kk")
          case AE_Left
          have c8_kk: "mt_pos c8 kk = 0"
            using c8_pos_for_pos1[OF kklt le1] AE_Left by simp
          have mp_cM_k: "mt_pos cM_k kk = 0"
            using win_le1 AE_Left
            unfolding ae_window_invariant_le1_def by simp
          have decode: "ae_decode_pos 0 (ofs6 kk) = 0"
            unfolding ae_decode_pos_def by simp
          show ?thesis using c8_kk mp_cM_k decode ofs_at_c8 by simp
        next
          case AE_Home
          have c8_kk: "mt_pos c8 kk = 1"
            using c8_pos_for_pos1[OF kklt le1] AE_Home by simp
          have mp_cM_k: "mt_pos cM_k kk = Suc (c_idx (ofs5 kk))"
            using win_le1 AE_Home
            unfolding ae_window_invariant_le1_def by simp
          have decode: "ae_decode_pos 1 (ofs6 kk) = Suc (c_idx (ofs6 kk))"
            unfolding ae_decode_pos_def by simp
          show ?thesis
            using c8_kk mp_cM_k decode ofs_at_c8 ofs5_eq_kk by simp
        next
          case AE_Right
          have c8_kk: "mt_pos c8 kk = 2"
            using c8_pos_for_pos1[OF kklt le1] AE_Right by simp
          have mp_cM_k:
              "mt_pos cM_k kk = Suc (?c + c_idx (ofs5 kk))"
            using win_le1 AE_Right
            unfolding ae_window_invariant_le1_def by simp
          have decode:
              "ae_decode_pos 2 (ofs6 kk) = Suc (?c + c_idx (ofs6 kk))"
            unfolding ae_decode_pos_def by simp
          show ?thesis
            using c8_kk mp_cM_k decode ofs_at_c8 ofs5_eq_kk by simp
        qed
      next
        case steady
        have win_steady: "ae_window_invariant
                  (mt_tape cM_k kk) (mt_pos cM_k kk)
                  (dest5 kk, ofs5 kk) (buf5 kk)
                  ((mt_pos c' kk - 2) * ?c + 1)"
          using wi steady unfolding ae_window_invariant_general_def by simp
        have mp_cM_k:
            "mt_pos cM_k kk
              = (mt_pos c' kk - 2) * ?c + 1 + bp_linear (dest5 kk, ofs5 kk)"
          using win_steady unfolding ae_window_invariant_def by simp
        show ?thesis
        proof (cases "dest5 kk")
          case AE_Left
          have c8_kk: "mt_pos c8 kk = mt_pos c' kk - 1"
            using c8_pos_for_pos_ge2[OF kklt steady] AE_Left by simp
          have bp_lin: "bp_linear (dest5 kk, ofs5 kk) = c_idx (ofs5 kk)"
            using AE_Left unfolding bp_linear_def by simp
          have decode:
              "ae_decode_pos (mt_pos c' kk - 1) (ofs6 kk)
                = (mt_pos c' kk - 2) * ?c + c_idx (ofs6 kk) + 1"
          proof -
            have "ae_decode_pos (mt_pos c' kk - 1) (ofs6 kk)
                    = (mt_pos c' kk - 1 - 1) * ?c + c_idx (ofs6 kk) + 1"
              using steady unfolding ae_decode_pos_def by simp
            also have "\<dots> = (mt_pos c' kk - 2) * ?c + c_idx (ofs6 kk) + 1"
              using steady by (simp add: numeral_2_eq_2)
            finally show ?thesis .
          qed
          show ?thesis
            using c8_kk mp_cM_k bp_lin decode ofs_at_c8 ofs5_eq_kk by simp
        next
          case AE_Home
          have c8_kk: "mt_pos c8 kk = mt_pos c' kk"
            using c8_pos_for_pos_ge2[OF kklt steady] AE_Home by simp
          have bp_lin: "bp_linear (dest5 kk, ofs5 kk) = ?c + c_idx (ofs5 kk)"
            using AE_Home unfolding bp_linear_def by simp
          have decode:
              "ae_decode_pos (mt_pos c' kk) (ofs6 kk)
                = (mt_pos c' kk - 1) * ?c + c_idx (ofs6 kk) + 1"
            using steady unfolding ae_decode_pos_def by simp
          have addr_eq:
              "(mt_pos c' kk - 2) * ?c + 1 + (?c + c_idx (ofs5 kk))
                = (mt_pos c' kk - 1) * ?c + c_idx (ofs5 kk) + 1"
          proof -
            have c_split: "(mt_pos c' kk - 1) * ?c
                            = (mt_pos c' kk - 2) * ?c + ?c"
              using steady by (simp add: algebra_simps diff_mult_distrib)
            thus ?thesis by linarith
          qed
          show ?thesis
            using c8_kk mp_cM_k bp_lin decode addr_eq ofs_at_c8 ofs5_eq_kk
            by simp
        next
          case AE_Right
          have c8_kk: "mt_pos c8 kk = mt_pos c' kk + 1"
            using c8_pos_for_pos_ge2[OF kklt steady] AE_Right by simp
          have bp_lin:
              "bp_linear (dest5 kk, ofs5 kk) = 2 * ?c + c_idx (ofs5 kk)"
            using AE_Right unfolding bp_linear_def by simp
          have decode:
              "ae_decode_pos (mt_pos c' kk + 1) (ofs6 kk)
                = mt_pos c' kk * ?c + c_idx (ofs6 kk) + 1"
            unfolding ae_decode_pos_def by simp
          have addr_eq:
              "(mt_pos c' kk - 2) * ?c + 1 + (2 * ?c + c_idx (ofs5 kk))
                = mt_pos c' kk * ?c + c_idx (ofs5 kk) + 1"
          proof -
            have c_split: "mt_pos c' kk * ?c
                            = (mt_pos c' kk - 2) * ?c + 2 * ?c"
              using steady by (simp add: algebra_simps diff_mult_distrib)
            thus ?thesis by linarith
          qed
          show ?thesis
            using c8_kk mp_cM_k bp_lin decode addr_eq ofs_at_c8 ofs5_eq_kk
            by simp
        qed
      qed
    qed
  qed
qed

text \<open>Reconstruction leaf of \<open>ae_simulates_forward_stage_general\<close>:
  the \<open>c8\<close> head position for an le1 tape (\<open>mt_pos c' kk = 1\<close>),
  as a \<open>dest5\<close>-case value (\<open>AE_Left\<close> -> 0, \<open>AE_Home\<close> -> 1,
  \<open>AE_Right\<close> -> 2).  For \<open>AE_Left\<close> SS8 reads the LE-marked
  cell 0 at \<open>c7_pos = 0\<close> (via \<open>tape_c7_zero_le_pos1_dest_left\<close>)
  and stays; otherwise SS8 steps from \<open>c7_pos\<close> per the recorded
  \<open>dest\<close>.  \<close>
lemma ae_fwd_c8_pos_for_pos1:
  fixes M :: "('q, 'a) mttm"
    and c' c4 c5 c6 c7 c8 :: "('c :: enum \<Rightarrow> 'a,
                'q \<times> ('a, 'c) ae_stage) mt_config"
    and q5 q6 :: 'q
    and ofs5 ofs6 :: "nat \<Rightarrow> 'c"
    and buf5 buf6 :: "nat \<Rightarrow> ('c \<Rightarrow> 'a) \<times> ('c \<Rightarrow> 'a) \<times> ('c \<Rightarrow> 'a)"
    and dest5 dest6 :: "nat \<Rightarrow> ae_dest"
  assumes step5: "(c4, c5) \<in> mttm_step (alphabet_enlarge_delta M)"
      and tape_c4_eq_c': "mt_tape c4 = mt_tape c'"
      and buf5_not_le_per_tape:
            "\<forall>k<k_tm M. (mt_pos c' k = 0
                  \<longrightarrow> fst (buf5 k) \<noteq> LE_block (le_tm M)
                  \<and> snd (snd (buf5 k)) \<noteq> LE_block (le_tm M))
                \<and> (mt_pos c' k = 1
                  \<longrightarrow> fst (snd (buf5 k)) \<noteq> LE_block (le_tm M)
                  \<and> snd (snd (buf5 k)) \<noteq> LE_block (le_tm M))
                \<and> (mt_pos c' k \<ge> 2
                  \<longrightarrow> fst (buf5 k) \<noteq> LE_block (le_tm M)
                  \<and> fst (snd (buf5 k)) \<noteq> LE_block (le_tm M)
                  \<and> snd (snd (buf5 k)) \<noteq> LE_block (le_tm M))"
      and right_not_le_c':
            "\<forall>k. mt_tape c' k (mt_pos c' k + 1) \<noteq> LE_block (le_tm M)"
      and c4_pos: "\<And>kk. kk < k_tm M \<Longrightarrow> mt_pos c4 kk = mt_pos c' kk"
      and c5_pos_for_pos1:
            "\<And>kk. kk < k_tm M \<Longrightarrow> mt_pos c' kk = 1 \<Longrightarrow> dest5 kk \<noteq> AE_Left
                  \<Longrightarrow> mt_pos c5 kk = 0"
      and step6: "(c5, c6) \<in> mttm_step (alphabet_enlarge_delta M)"
      and step7: "(c6, c7) \<in> mttm_step (alphabet_enlarge_delta M)"
      and c7_state: "mt_state c7 = (q6, ofs6, buf6, dest6, SS8)"
      and buf6_eq_buf5: "buf6 = buf5"
      and dest6_eq_dest5: "dest6 = dest5"
      and c7_pos_for_pos1_dest_left:
            "\<And>kk. kk < k_tm M \<Longrightarrow> mt_pos c' kk = 1 \<Longrightarrow> dest5 kk = AE_Left
                  \<Longrightarrow> mt_pos c7 kk = 0"
      and tape_c7_zero_le_pos1_dest_left:
            "\<And>kk. kk < k_tm M \<Longrightarrow> mt_pos c' kk = 1 \<Longrightarrow> dest5 kk = AE_Left
                  \<Longrightarrow> mt_tape c7 kk 0 = LE_block (le_tm M)"
      and step8_sub: "(c7, c8) \<in> mttm_step (ae_delta_ss8_ss1 M)"
      and c6_pos_for_pos1:
            "\<And>kk. kk < k_tm M \<Longrightarrow> mt_pos c' kk = 1 \<Longrightarrow> mt_pos c6 kk = 1"
      and c7_pos_for_pos1:
            "\<And>kk. kk < k_tm M \<Longrightarrow> mt_pos c' kk = 1
                  \<Longrightarrow> mt_pos c7 kk = (if dest5 kk = AE_Left then 0 else 2)"
  shows "\<And>kk. kk < k_tm M \<Longrightarrow> mt_pos c' kk = 1
            \<Longrightarrow> mt_pos c8 kk = (case dest5 kk of
                                  AE_Left  \<Rightarrow> 0
                                | AE_Home  \<Rightarrow> 1
                                | AE_Right \<Rightarrow> 2)"
proof -
  fix kk
  assume kklt: "kk < k_tm M"
  assume pos_kk: "mt_pos c' kk = 1"
    obtain qq tts nn qq' aa8 dr8 where
        c7_eq8: "c7 = Config\<^sub>M qq tts nn"
      and c8_eq: "c8 = Config\<^sub>M qq'
                          (\<lambda>k. (tts k)(nn k := aa8 k))
                          (\<lambda>k. go_dir (dr8 k) (nn k))"
      and tr_in: "(qq, \<lambda>k. tts k (nn k), qq', aa8, dr8)
                    \<in> ae_delta_ss8_ss1 M"
      using step8_sub by (auto elim: mttm_step.cases)
    obtain q ofs buf dest where
        qq_eq: "qq = (q, ofs, buf, dest, SS8)"
      and dr8_eq:
          "dr8 = (\<lambda>k. if k < k_tm M then snd (ae_ss8_action (le_tm M)
                              (tts k (nn k)) (buf k) (dest k)) else dir.N)"
      using tr_in by (auto simp: ae_delta_ss8_ss1_def)
    have qq_state: "qq = (q6, ofs6, buf6, dest6, SS8)"
      using c7_state c7_eq8 by simp
    have buf_eq: "buf = buf6" using qq_eq qq_state by simp
    have dest_eq: "dest = dest6" using qq_eq qq_state by simp
    have nn_kk: "nn kk = mt_pos c7 kk" using c7_eq8 by simp
    obtain ll hh rr where buf5_kk: "buf5 kk = (ll, hh, rr)"
      using prod.exhaust by metis
    have buf6_kk: "buf6 kk = (ll, hh, rr)"
      using buf5_kk buf6_eq_buf5 by simp
    have h_ne_LE: "hh \<noteq> LE_block (le_tm M)"
    proof -
      have "fst (snd (buf5 kk)) \<noteq> LE_block (le_tm M)"
        using buf5_not_le_per_tape[rule_format, OF kklt] pos_kk by blast
      thus ?thesis using buf5_kk by simp
    qed
    show "mt_pos c8 kk = (case dest5 kk of
                            AE_Left  \<Rightarrow> 0
                          | AE_Home  \<Rightarrow> 1
                          | AE_Right \<Rightarrow> 2)"
    proof (cases "dest5 kk")
      case AE_Left
      have c7_kk: "mt_pos c7 kk = 0"
        using c7_pos_for_pos1_dest_left[OF kklt pos_kk AE_Left] .
      have nn_kk_val: "nn kk = 0" using nn_kk c7_kk by simp
      have read_LE: "tts kk (nn kk) = LE_block (le_tm M)"
      proof -
        have "tts kk (nn kk) = mt_tape c7 kk (mt_pos c7 kk)"
          using c7_eq8 nn_kk by simp
        also have "\<dots> = mt_tape c7 kk 0" using c7_kk by simp
        also have "\<dots> = LE_block (le_tm M)"
          using tape_c7_zero_le_pos1_dest_left[OF kklt pos_kk AE_Left] .
        finally show ?thesis .
      qed
      have dr8_kk: "dr8 kk = dir.N" using dr8_eq read_LE kklt by simp
      have "mt_pos c8 kk = go_dir (dr8 kk) (nn kk)"
        using c8_eq by simp
      also have "\<dots> = nn kk" using dr8_kk by simp
      also have "\<dots> = 0" using nn_kk_val .
      finally show ?thesis using AE_Left by simp
    next
      case AE_Home
      have c7_kk: "mt_pos c7 kk = 2"
        using c7_pos_for_pos1[OF kklt pos_kk] AE_Home by simp
      have nn_kk_val: "nn kk = 2" using nn_kk c7_kk by simp
      have dest_ne_left: "dest5 kk \<noteq> AE_Left" using AE_Home by simp
      have c5_pos_kk: "mt_pos c5 kk = 0"
        using c5_pos_for_pos1[OF kklt pos_kk dest_ne_left] .
      have two_ne_c6: "(2 :: nat) \<noteq> mt_pos c6 kk"
        using c6_pos_for_pos1[OF kklt pos_kk] by simp
      have two_ne_c5: "(2 :: nat) \<noteq> mt_pos c5 kk"
        using c5_pos_kk by simp
      have two_ne_c4: "(2 :: nat) \<noteq> mt_pos c4 kk"
        using c4_pos kklt pos_kk by simp
      have c7_at_2: "mt_tape c7 kk 2 = mt_tape c' kk 2"
      proof -
        have "mt_tape c7 kk 2 = mt_tape c6 kk 2"
          using mttm_step_tape_off_head[OF step7 two_ne_c6] .
        also have "\<dots> = mt_tape c5 kk 2"
          using mttm_step_tape_off_head[OF step6 two_ne_c5] .
        also have "\<dots> = mt_tape c4 kk 2"
          using mttm_step_tape_off_head[OF step5 two_ne_c4] .
        also have "\<dots> = mt_tape c' kk 2" using tape_c4_eq_c' by simp
        finally show ?thesis .
      qed
      have read_ne_LE: "tts kk (nn kk) \<noteq> LE_block (le_tm M)"
      proof -
        have "tts kk (nn kk) = mt_tape c7 kk (mt_pos c7 kk)"
          using c7_eq8 nn_kk by simp
        also have "\<dots> = mt_tape c7 kk 2" using c7_kk by simp
        also have "\<dots> = mt_tape c' kk 2" using c7_at_2 .
        finally have read_eq: "tts kk (nn kk) = mt_tape c' kk 2" .
        have "mt_tape c' kk (mt_pos c' kk + 1) \<noteq> LE_block (le_tm M)"
          using right_not_le_c' by blast
        hence "mt_tape c' kk 2 \<noteq> LE_block (le_tm M)"
          using pos_kk by (simp add: numeral_2_eq_2)
        thus ?thesis using read_eq by simp
      qed
      have dest6_AE_Home: "dest6 kk = AE_Home"
        using AE_Home dest6_eq_dest5 by simp
      have dr8_kk: "dr8 kk = dir.L"
        using dr8_eq buf_eq dest_eq dest6_AE_Home buf6_kk h_ne_LE read_ne_LE kklt
        by simp
      have "mt_pos c8 kk = go_dir (dr8 kk) (nn kk)"
        using c8_eq by simp
      also have "\<dots> = (nn kk) - 1" using dr8_kk by simp
      also have "\<dots> = 1" using nn_kk_val by simp
      finally show ?thesis using AE_Home by simp
    next
      case AE_Right
      have c7_kk: "mt_pos c7 kk = 2"
        using c7_pos_for_pos1[OF kklt pos_kk] AE_Right by simp
      have nn_kk_val: "nn kk = 2" using nn_kk c7_kk by simp
      have dest_ne_left: "dest5 kk \<noteq> AE_Left" using AE_Right by simp
      have c5_pos_kk: "mt_pos c5 kk = 0"
        using c5_pos_for_pos1[OF kklt pos_kk dest_ne_left] .
      have two_ne_c6: "(2 :: nat) \<noteq> mt_pos c6 kk"
        using c6_pos_for_pos1[OF kklt pos_kk] by simp
      have two_ne_c5: "(2 :: nat) \<noteq> mt_pos c5 kk"
        using c5_pos_kk by simp
      have two_ne_c4: "(2 :: nat) \<noteq> mt_pos c4 kk"
        using c4_pos kklt pos_kk by simp
      have c7_at_2: "mt_tape c7 kk 2 = mt_tape c' kk 2"
      proof -
        have "mt_tape c7 kk 2 = mt_tape c6 kk 2"
          using mttm_step_tape_off_head[OF step7 two_ne_c6] .
        also have "\<dots> = mt_tape c5 kk 2"
          using mttm_step_tape_off_head[OF step6 two_ne_c5] .
        also have "\<dots> = mt_tape c4 kk 2"
          using mttm_step_tape_off_head[OF step5 two_ne_c4] .
        also have "\<dots> = mt_tape c' kk 2" using tape_c4_eq_c' by simp
        finally show ?thesis .
      qed
      have read_ne_LE: "tts kk (nn kk) \<noteq> LE_block (le_tm M)"
      proof -
        have "tts kk (nn kk) = mt_tape c7 kk (mt_pos c7 kk)"
          using c7_eq8 nn_kk by simp
        also have "\<dots> = mt_tape c7 kk 2" using c7_kk by simp
        also have "\<dots> = mt_tape c' kk 2" using c7_at_2 .
        finally have read_eq: "tts kk (nn kk) = mt_tape c' kk 2" .
        have "mt_tape c' kk (mt_pos c' kk + 1) \<noteq> LE_block (le_tm M)"
          using right_not_le_c' by blast
        hence "mt_tape c' kk 2 \<noteq> LE_block (le_tm M)"
          using pos_kk by (simp add: numeral_2_eq_2)
        thus ?thesis using read_eq by simp
      qed
      have dest6_AE_Right: "dest6 kk = AE_Right"
        using AE_Right dest6_eq_dest5 by simp
      have dr8_kk: "dr8 kk = dir.N"
        using dr8_eq buf_eq dest_eq dest6_AE_Right buf6_kk h_ne_LE read_ne_LE kklt
        by simp
      have "mt_pos c8 kk = go_dir (dr8 kk) (nn kk)"
        using c8_eq by simp
      also have "\<dots> = nn kk" using dr8_kk by simp
      also have "\<dots> = 2" using nn_kk_val .
      finally show ?thesis using AE_Right by simp
    qed
  qed

text \<open>Reconstruction leaf of \<open>ae_simulates_forward_stage_general\<close>:
  the in-window \<open>c8\<close> value at block 1 for an le0 tape
  (\<open>mt_pos c' kk = 0\<close>).  Uniformly \<open>c8@1 = rr\<close> (the right
  buffer slot \<open>snd (snd (buf5 kk))\<close>); the SS6/SS7/SS8 substeps
  write at cells \<open>c5_pos = 0\<close> / \<open>c6_pos = 1\<close> / \<open>c7_pos\<close>,
  with cell 1 carrying the buffered right value.  \<close>
lemma ae_fwd_c8_at_one_for_pos0:
  fixes M :: "('q, 'a) mttm"
    and c' c4 c5 c6 c7 c8 :: "('c :: enum \<Rightarrow> 'a,
                'q \<times> ('a, 'c) ae_stage) mt_config"
    and q5 q6 :: 'q
    and ofs5 ofs6 :: "nat \<Rightarrow> 'c"
    and buf5 buf6 :: "nat \<Rightarrow> ('c \<Rightarrow> 'a) \<times> ('c \<Rightarrow> 'a) \<times> ('c \<Rightarrow> 'a)"
    and dest5 dest6 :: "nat \<Rightarrow> ae_dest"
  assumes step5: "(c4, c5) \<in> mttm_step (alphabet_enlarge_delta M)"
      and tape_c4_eq_c': "mt_tape c4 = mt_tape c'"
      and buf5_not_le_per_tape:
            "\<forall>k<k_tm M. (mt_pos c' k = 0
                  \<longrightarrow> fst (buf5 k) \<noteq> LE_block (le_tm M)
                  \<and> snd (snd (buf5 k)) \<noteq> LE_block (le_tm M))
                \<and> (mt_pos c' k = 1
                  \<longrightarrow> fst (snd (buf5 k)) \<noteq> LE_block (le_tm M)
                  \<and> snd (snd (buf5 k)) \<noteq> LE_block (le_tm M))
                \<and> (mt_pos c' k \<ge> 2
                  \<longrightarrow> fst (buf5 k) \<noteq> LE_block (le_tm M)
                  \<and> fst (snd (buf5 k)) \<noteq> LE_block (le_tm M)
                  \<and> snd (snd (buf5 k)) \<noteq> LE_block (le_tm M))"
      and right_not_le_c':
            "\<forall>k. mt_tape c' k (mt_pos c' k + 1) \<noteq> LE_block (le_tm M)"
      and c4_pos: "\<And>kk. kk < k_tm M \<Longrightarrow> mt_pos c4 kk = mt_pos c' kk"
      and step6: "(c5, c6) \<in> mttm_step (alphabet_enlarge_delta M)"
      and step7_sub: "(c6, c7) \<in> mttm_step (ae_delta_ss7_ss8 M)"
      and c6_state: "mt_state c6 = (q6, ofs6, buf6, dest6, SS7)"
      and c7_state: "mt_state c7 = (q6, ofs6, buf6, dest6, SS8)"
      and buf6_eq_buf5: "buf6 = buf5"
      and dest6_eq_dest5: "dest6 = dest5"
      and step8_sub: "(c7, c8) \<in> mttm_step (ae_delta_ss8_ss1 M)"
      and step8: "(c7, c8) \<in> mttm_step (alphabet_enlarge_delta M)"
      and c5_pos_for_pos0:
            "\<And>kk. kk < k_tm M \<Longrightarrow> mt_pos c' kk = 0 \<Longrightarrow> mt_pos c5 kk = 0"
      and buf5_h_le_for_pos0:
            "\<forall>k<k_tm M. mt_pos c' k = 0 \<longrightarrow> fst (snd (buf5 k)) = LE_block (le_tm M)"
      and c6_pos_for_pos0:
            "\<And>kk. kk < k_tm M \<Longrightarrow> mt_pos c' kk = 0 \<Longrightarrow> mt_pos c6 kk = 1"
      and c7_pos_for_pos0:
            "\<And>kk. kk < k_tm M \<Longrightarrow> mt_pos c' kk = 0
                  \<Longrightarrow> mt_pos c7 kk = (if dest5 kk = AE_Right then 1 else 0)"
  shows "\<And>kk. kk < k_tm M \<Longrightarrow> mt_pos c' kk = 0
            \<Longrightarrow> mt_tape c8 kk 1 = snd (snd (buf5 kk))"
proof -
  fix kk
  assume kklt: "kk < k_tm M"
  assume pos_kk: "mt_pos c' kk = 0"
    obtain qq tts nn qq' aa7 dr7 where
        c6_eq7: "c6 = Config\<^sub>M qq tts nn"
      and c7_eq: "c7 = Config\<^sub>M qq'
                          (\<lambda>k. (tts k)(nn k := aa7 k))
                          (\<lambda>k. go_dir (dr7 k) (nn k))"
      and tr7_in: "(qq, \<lambda>k. tts k (nn k), qq', aa7, dr7)
                    \<in> ae_delta_ss7_ss8 M"
      using step7_sub by (auto elim: mttm_step.cases)
    obtain q7 ofs7 buf7 dest7 where
        qq_eq7: "qq = (q7, ofs7, buf7, dest7, SS7)"
      and aa7_eq:
          "aa7 = (\<lambda>k. if k < k_tm M then fst (ae_ss7_action (le_tm M)
                              (tts k (nn k)) (buf7 k) (dest7 k)) else bl_block (bl_tm M))"
      using tr7_in by (auto simp: ae_delta_ss7_ss8_def)
    have qq_state: "qq = (q6, ofs6, buf6, dest6, SS7)"
      using c6_state c6_eq7 by simp
    have buf7_eq: "buf7 = buf6" using qq_eq7 qq_state by simp
    have dest7_eq: "dest7 = dest6" using qq_eq7 qq_state by simp
    have nn7_kk: "nn kk = mt_pos c6 kk" using c6_eq7 by simp
    have c6_kk: "mt_pos c6 kk = 1" using c6_pos_for_pos0[OF kklt pos_kk] .
    have nn7_kk_1: "nn kk = 1" using nn7_kk c6_kk by simp
    have one_ne_c5_pos: "(1 :: nat) \<noteq> mt_pos c5 kk"
      using c5_pos_for_pos0[OF kklt pos_kk] by simp
    have one_ne_c4_pos: "(1 :: nat) \<noteq> mt_pos c4 kk"
      using c4_pos kklt pos_kk by simp
    have c6_at_1: "mt_tape c6 kk 1 = mt_tape c' kk 1"
    proof -
      have "mt_tape c6 kk 1 = mt_tape c5 kk 1"
        using mttm_step_tape_off_head[OF step6 one_ne_c5_pos] .
      also have "\<dots> = mt_tape c4 kk 1"
        using mttm_step_tape_off_head[OF step5 one_ne_c4_pos] .
      also have "\<dots> = mt_tape c' kk 1" using tape_c4_eq_c' by simp
      finally show ?thesis .
    qed
    have read7_ne_LE: "tts kk (nn kk) \<noteq> LE_block (le_tm M)"
    proof -
      have "tts kk (nn kk) = mt_tape c6 kk (mt_pos c6 kk)"
        using c6_eq7 nn7_kk by simp
      also have "\<dots> = mt_tape c6 kk 1" using c6_kk by simp
      also have "\<dots> = mt_tape c' kk 1" using c6_at_1 .
      finally have read_eq: "tts kk (nn kk) = mt_tape c' kk 1" .
      have "mt_tape c' kk (mt_pos c' kk + 1) \<noteq> LE_block (le_tm M)"
        using right_not_le_c' by blast
      hence "mt_tape c' kk 1 \<noteq> LE_block (le_tm M)" using pos_kk by simp
      thus ?thesis using read_eq by simp
    qed
    obtain ll hh rr where buf5_kk: "buf5 kk = (ll, hh, rr)"
      using prod.exhaust by metis
    have buf6_kk: "buf6 kk = (ll, hh, rr)"
      using buf5_kk buf6_eq_buf5 by simp
    have hh_le: "hh = LE_block (le_tm M)"
    proof -
      have "fst (snd (buf5 kk)) = LE_block (le_tm M)"
        using buf5_h_le_for_pos0[rule_format, OF kklt] pos_kk by blast
      thus ?thesis using buf5_kk by simp
    qed
    have c7_at_1_eq_rr: "mt_tape c7 kk 1 = rr"
    proof -
      \<comment> \<open>SS7 writes \<open>aa7\<close> at \<open>nn = 1\<close>; with h=LE the action's
          second branch fires, returning \<open>(r, _)\<close> regardless of
          \<open>dest\<close>, so \<open>aa7 kk = r = rr\<close>.\<close>
      have aa7_kk: "aa7 kk = rr"
        using aa7_eq buf7_eq buf6_kk hh_le read7_ne_LE kklt by simp
      have "mt_tape c7 kk 1 = aa7 kk" using c7_eq nn7_kk_1 by simp
      thus ?thesis using aa7_kk by simp
    qed
    show "mt_tape c8 kk 1 = snd (snd (buf5 kk))"
    proof (cases "dest5 kk = AE_Right")
      case True
      \<comment> \<open>SS8 writes at \<open>c7_pos = 1\<close>; reads \<open>c7@1 = rr \<noteq> LE\<close>,
          \<open>h = LE\<close>, dest=Right gives \<open>(r, N)\<close>; \<open>c8@1 = rr\<close>.\<close>
      have c7_pos_kk: "mt_pos c7 kk = 1"
        using c7_pos_for_pos0[OF kklt pos_kk] True by simp
      obtain qq8 tts8 nn8 qq8' aa8 dr8 where
          c7_eq8: "c7 = Config\<^sub>M qq8 tts8 nn8"
        and c8_eq: "c8 = Config\<^sub>M qq8'
                            (\<lambda>k. (tts8 k)(nn8 k := aa8 k))
                            (\<lambda>k. go_dir (dr8 k) (nn8 k))"
        and tr8_in: "(qq8, \<lambda>k. tts8 k (nn8 k), qq8', aa8, dr8)
                      \<in> ae_delta_ss8_ss1 M"
        using step8_sub by (auto elim: mttm_step.cases)
      obtain q8 ofs8 buf8 dest8 where
          qq8_eq: "qq8 = (q8, ofs8, buf8, dest8, SS8)"
        and aa8_eq:
            "aa8 = (\<lambda>k. if k < k_tm M then fst (ae_ss8_action (le_tm M)
                                (tts8 k (nn8 k)) (buf8 k) (dest8 k)) else bl_block (bl_tm M))"
        using tr8_in by (auto simp: ae_delta_ss8_ss1_def)
      have qq8_state: "qq8 = (q6, ofs6, buf6, dest6, SS8)"
        using c7_state c7_eq8 by simp
      have buf8_eq: "buf8 = buf6" using qq8_eq qq8_state by simp
      have dest8_eq: "dest8 = dest6" using qq8_eq qq8_state by simp
      have nn8_kk: "nn8 kk = mt_pos c7 kk" using c7_eq8 by simp
      have nn8_kk_1: "nn8 kk = 1" using nn8_kk c7_pos_kk by simp
      have rr_ne_LE: "rr \<noteq> LE_block (le_tm M)"
      proof -
        have "snd (snd (buf5 kk)) \<noteq> LE_block (le_tm M)"
          using buf5_not_le_per_tape[rule_format, OF kklt] pos_kk by blast
        thus ?thesis using buf5_kk by simp
      qed
      have read8_ne_LE: "tts8 kk (nn8 kk) \<noteq> LE_block (le_tm M)"
      proof -
        have "tts8 kk (nn8 kk) = mt_tape c7 kk (mt_pos c7 kk)"
          using c7_eq8 nn8_kk by simp
        also have "\<dots> = mt_tape c7 kk 1" using c7_pos_kk by simp
        also have "\<dots> = rr" using c7_at_1_eq_rr .
        finally have "tts8 kk (nn8 kk) = rr" .
        thus ?thesis using rr_ne_LE by simp
      qed
      have dest6_eq: "dest6 kk = AE_Right" using True dest6_eq_dest5 by simp
      have aa8_kk: "aa8 kk = rr"
        using aa8_eq buf8_eq dest8_eq dest6_eq buf6_kk hh_le read8_ne_LE kklt
        by simp
      have "mt_tape c8 kk 1 = aa8 kk" using c8_eq nn8_kk_1 by simp
      also have "\<dots> = rr" using aa8_kk .
      also have "\<dots> = snd (snd (buf5 kk))" using buf5_kk by simp
      finally show ?thesis .
    next
      case False
      \<comment> \<open>SS8 writes at \<open>c7_pos = 0 \<noteq> 1\<close>, off cell 1.
          \<open>c8@1 = c7@1 = rr\<close>.\<close>
      have c7_pos_kk: "mt_pos c7 kk = 0"
        using c7_pos_for_pos0[OF kklt pos_kk] False by simp
      have one_ne_c7_pos: "(1 :: nat) \<noteq> mt_pos c7 kk"
        using c7_pos_kk by simp
      have "mt_tape c8 kk 1 = mt_tape c7 kk 1"
        using mttm_step_tape_off_head[OF step8 one_ne_c7_pos] .
      also have "\<dots> = rr" using c7_at_1_eq_rr .
      also have "\<dots> = snd (snd (buf5 kk))" using buf5_kk by simp
      finally show ?thesis .
    qed
  qed

text \<open>Reconstruction leaf of \<open>ae_simulates_forward_stage_general\<close>:
  the \<open>c6\<close> head position for a steady tape
  (\<open>mt_pos c' kk \<ge> 2\<close>) is unchanged from \<open>mt_pos c' kk\<close>.
  SS6's action writes at \<open>c5_pos\<close> (\<open>pos \<mp> 1\<close> per
  \<open>dest5\<close>) and steps back, so \<open>c6\<close> lands on the home
  block \<open>pos\<close>; the non-LE window facts rule out the
  LE-marker short-circuit.  \<close>
lemma ae_fwd_c6_pos_for_pos_ge2:
  fixes M :: "('q, 'a) mttm"
    and c' c4 c5 c6 :: "('c :: enum \<Rightarrow> 'a,
                'q \<times> ('a, 'c) ae_stage) mt_config"
    and q5 :: 'q
    and ofs5 :: "nat \<Rightarrow> 'c"
    and buf5 :: "nat \<Rightarrow> ('c \<Rightarrow> 'a) \<times> ('c \<Rightarrow> 'a) \<times> ('c \<Rightarrow> 'a)"
    and dest5 :: "nat \<Rightarrow> ae_dest"
  assumes step5: "(c4, c5) \<in> mttm_step (alphabet_enlarge_delta M)"
      and c5_state: "mt_state c5 = (q5, ofs5, buf5, dest5, SS6)"
      and tape_c4_eq_c': "mt_tape c4 = mt_tape c'"
      and buf5_not_le_per_tape:
            "\<forall>k<k_tm M. (mt_pos c' k = 0
                  \<longrightarrow> fst (buf5 k) \<noteq> LE_block (le_tm M)
                  \<and> snd (snd (buf5 k)) \<noteq> LE_block (le_tm M))
                \<and> (mt_pos c' k = 1
                  \<longrightarrow> fst (snd (buf5 k)) \<noteq> LE_block (le_tm M)
                  \<and> snd (snd (buf5 k)) \<noteq> LE_block (le_tm M))
                \<and> (mt_pos c' k \<ge> 2
                  \<longrightarrow> fst (buf5 k) \<noteq> LE_block (le_tm M)
                  \<and> fst (snd (buf5 k)) \<noteq> LE_block (le_tm M)
                  \<and> snd (snd (buf5 k)) \<noteq> LE_block (le_tm M))"
      and right_not_le_c':
            "\<forall>k. mt_tape c' k (mt_pos c' k + 1) \<noteq> LE_block (le_tm M)"
      and c4_pos: "\<And>kk. kk < k_tm M \<Longrightarrow> mt_pos c4 kk = mt_pos c' kk"
      and step6_sub: "(c5, c6) \<in> mttm_step (ae_delta_ss6_ss7 M)"
      and c5_pos_for_pos_ge2:
            "\<And>kk. kk < k_tm M \<Longrightarrow> mt_pos c' kk \<ge> 2 \<Longrightarrow> dest5 kk \<noteq> AE_Left
                  \<Longrightarrow> mt_pos c5 kk = mt_pos c' kk - 1"
      and c5_pos_for_pos_ge2_dest_left:
            "\<And>kk. kk < k_tm M \<Longrightarrow> mt_pos c' kk \<ge> 2 \<Longrightarrow> dest5 kk = AE_Left
                  \<Longrightarrow> mt_pos c5 kk = mt_pos c' kk + 1"
      and left_not_le_c'_steady:
            "\<forall>k. mt_pos c' k \<ge> 2
                  \<longrightarrow> mt_tape c' k (mt_pos c' k - 1) \<noteq> LE_block (le_tm M)"
  shows "\<And>kk. kk < k_tm M \<Longrightarrow> mt_pos c' kk \<ge> 2 \<Longrightarrow> mt_pos c6 kk = mt_pos c' kk"
proof -
  fix kk
  assume kklt: "kk < k_tm M"
  assume hge2: "mt_pos c' kk \<ge> 2"
    obtain qq tts nn qq' aa6 dr6 where
        c5_eq6: "c5 = Config\<^sub>M qq tts nn"
      and c6_eq: "c6 = Config\<^sub>M qq'
                          (\<lambda>k. (tts k)(nn k := aa6 k))
                          (\<lambda>k. go_dir (dr6 k) (nn k))"
      and tr_in: "(qq, \<lambda>k. tts k (nn k), qq', aa6, dr6)
                    \<in> ae_delta_ss6_ss7 M"
      using step6_sub by (auto elim: mttm_step.cases)
    obtain q ofs buf dest where
        qq_eq: "qq = (q, ofs, buf, dest, SS6)"
      and dr6_eq:
          "dr6 = (\<lambda>k. if k < k_tm M then snd (ae_ss6_action (le_tm M)
                              (tts k (nn k)) (buf k) (dest k)) else dir.N)"
      using tr_in by (auto simp: ae_delta_ss6_ss7_def)
    have qq_state: "qq = (q5, ofs5, buf5, dest5, SS6)"
      using c5_state c5_eq6 by simp
    have buf_eq: "buf = buf5" using qq_eq qq_state by simp
    have dest_eq: "dest = dest5" using qq_eq qq_state by simp
    have nn_kk: "nn kk = mt_pos c5 kk" using c5_eq6 by simp
    obtain ll hh rr where buf5_kk: "buf5 kk = (ll, hh, rr)"
      using prod.exhaust by metis
    have h_ne_LE: "hh \<noteq> LE_block (le_tm M)"
    proof -
      have "fst (snd (buf5 kk)) \<noteq> LE_block (le_tm M)"
        using buf5_not_le_per_tape[rule_format, OF kklt] hge2 by blast
      thus ?thesis using buf5_kk by simp
    qed
    have c4_kk: "mt_pos c4 kk = mt_pos c' kk" using c4_pos kklt by simp
    show "mt_pos c6 kk = mt_pos c' kk"
    proof (cases "dest5 kk = AE_Left")
      case True
      have c5_kk: "mt_pos c5 kk = mt_pos c' kk + 1"
        using c5_pos_for_pos_ge2_dest_left[OF kklt hge2 True] .
      have nn_kk_val: "nn kk = mt_pos c' kk + 1" using nn_kk c5_kk by simp
      have addr_ne_c4_pos: "(mt_pos c' kk + 1) \<noteq> mt_pos c4 kk"
        using c4_kk by simp
      have c5_at_addr:
          "mt_tape c5 kk (mt_pos c' kk + 1) = mt_tape c' kk (mt_pos c' kk + 1)"
      proof -
        have "mt_tape c5 kk (mt_pos c' kk + 1)
                = mt_tape c4 kk (mt_pos c' kk + 1)"
          using mttm_step_tape_off_head[OF step5 addr_ne_c4_pos] .
        also have "\<dots> = mt_tape c' kk (mt_pos c' kk + 1)"
          using tape_c4_eq_c' by simp
        finally show ?thesis .
      qed
      have read_ne_LE: "tts kk (nn kk) \<noteq> LE_block (le_tm M)"
      proof -
        have "tts kk (nn kk) = mt_tape c5 kk (mt_pos c5 kk)"
          using c5_eq6 nn_kk by simp
        also have "\<dots> = mt_tape c5 kk (mt_pos c' kk + 1)"
          using c5_kk by simp
        also have "\<dots> = mt_tape c' kk (mt_pos c' kk + 1)"
          using c5_at_addr .
        finally have read_eq:
            "tts kk (nn kk) = mt_tape c' kk (mt_pos c' kk + 1)" .
        have "mt_tape c' kk (mt_pos c' kk + 1) \<noteq> LE_block (le_tm M)"
          using right_not_le_c' by blast
        thus ?thesis using read_eq by simp
      qed
      have dr6_kk:
          "dr6 kk = (if dest5 kk = AE_Left then dir.L else dir.R)"
        using dr6_eq buf_eq dest_eq buf5_kk read_ne_LE h_ne_LE kklt by simp
      have dr6_kk_L: "dr6 kk = dir.L" using dr6_kk True by simp
      have "mt_pos c6 kk = go_dir (dr6 kk) (nn kk)"
        using c6_eq by simp
      also have "\<dots> = (nn kk) - 1" using dr6_kk_L by simp
      also have "\<dots> = (mt_pos c' kk + 1) - 1" using nn_kk_val by simp
      also have "\<dots> = mt_pos c' kk" by simp
      finally show ?thesis .
    next
      case False
      have c5_kk: "mt_pos c5 kk = mt_pos c' kk - 1"
        using c5_pos_for_pos_ge2[OF kklt hge2 False] .
      have nn_kk_val: "nn kk = mt_pos c' kk - 1" using nn_kk c5_kk by simp
      have addr_ne_c4_pos: "(mt_pos c' kk - 1) \<noteq> mt_pos c4 kk"
        using c4_kk hge2 by linarith
      have c5_at_addr:
          "mt_tape c5 kk (mt_pos c' kk - 1) = mt_tape c' kk (mt_pos c' kk - 1)"
      proof -
        have "mt_tape c5 kk (mt_pos c' kk - 1)
                = mt_tape c4 kk (mt_pos c' kk - 1)"
          using mttm_step_tape_off_head[OF step5 addr_ne_c4_pos] .
        also have "\<dots> = mt_tape c' kk (mt_pos c' kk - 1)"
          using tape_c4_eq_c' by simp
        finally show ?thesis .
      qed
      have read_ne_LE: "tts kk (nn kk) \<noteq> LE_block (le_tm M)"
      proof -
        have "tts kk (nn kk) = mt_tape c5 kk (mt_pos c5 kk)"
          using c5_eq6 nn_kk by simp
        also have "\<dots> = mt_tape c5 kk (mt_pos c' kk - 1)"
          using c5_kk by simp
        also have "\<dots> = mt_tape c' kk (mt_pos c' kk - 1)"
          using c5_at_addr .
        finally have read_eq:
            "tts kk (nn kk) = mt_tape c' kk (mt_pos c' kk - 1)" .
        have "mt_tape c' kk (mt_pos c' kk - 1) \<noteq> LE_block (le_tm M)"
          using left_not_le_c'_steady hge2 by blast
        thus ?thesis using read_eq by simp
      qed
      have dr6_kk:
          "dr6 kk = (if dest5 kk = AE_Left then dir.L else dir.R)"
        using dr6_eq buf_eq dest_eq buf5_kk read_ne_LE h_ne_LE kklt by simp
      have dr6_kk_R: "dr6 kk = dir.R" using dr6_kk False by simp
      have "mt_pos c6 kk = go_dir (dr6 kk) (nn kk)"
        using c6_eq by simp
      also have "\<dots> = Suc (nn kk)" using dr6_kk_R by simp
      also have "\<dots> = Suc (mt_pos c' kk - 1)" using nn_kk_val by simp
      also have "\<dots> = mt_pos c' kk" using hge2 by simp
      finally show ?thesis .
    qed
  qed

end
