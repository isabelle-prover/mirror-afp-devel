theory AlphabetReduction_ForwardSubsteps
  imports AlphabetReduction_Simulation
begin

subsection \<open>Per-substep simulation steps\<close>

text \<open>The compute substep: one \<open>M'\<close>-step from an
  \<open>AR_SimCompute\<close> stage whose \<open>buf\<close> field matches an
  \<open>M\<close>-\<open>\<delta>\<close>-tuple's read vector fires that tuple,
  landing at the \<open>AR_SimWrite\<close> stage with \<open>M\<close>'s
  post-step state \<open>q'\<close>, write vector \<open>m_a'\<close>, and
  direction vector \<open>m_d\<close> threaded into the stage.  No tape
  cell changes and no head moves (the substrate write is the read
  symbol back, direction \<open>N\<close>); the per-tape \<open>posk\<close>
  carries through.  The two global \<open>\<delta>LE\<close> filters are
  discharged reflexively (write equals read, move \<open>N\<close>); the
  target-stage validity rests on \<open>valid_mttm\<close>'s
  \<open>\<delta>\<close>-range typing (\<open>m_a' k \<in> \<Gamma>_tm M\<close>).
  Throughout, \<open>b\<close> abbreviates \<open>block_width \<Gamma>\<close> (the per-symbol cell width).\<close>

lemma ar_compute_step:
  fixes M :: "('q, 'a) mttm"
    and c' :: "(sym4, 'q \<times> 'a ar_stage) mt_config"
  assumes vM: "valid_mttm M"
      and stg: "mt_state c' = (q, AR_SimCompute, tk, i, buf, dvec, posk)"
      and mdelta: "(q, buf, q', m_a', m_d) \<in> delta_tm M"
      and vsrc: "ar_valid_stage (\<Gamma>_tm M) (bl_tm M)
                   (AR_SimCompute, tk, i, buf, dvec, posk)"
      and pad_blank: "\<forall>j \<ge> k_tm M. mt_tape c' j (mt_pos c' j) = BLANK4"
      and src_bounded: "ar_stage_bounded (bl_tm M) (k_tm M)
                          (AR_SimCompute, tk, i, buf, dvec, posk)"
  shows "\<exists>c''. (c', c'') \<in> mttm_step (alphabet_reduce_delta M)
              \<and> mt_state c'' = (q', AR_SimWrite, 0, 0, m_a', m_d, posk)
              \<and> mt_tape c'' = mt_tape c'
              \<and> mt_pos c'' = mt_pos c'"
proof -
  obtain ts n where c'_eq:
      "c' = Config\<^sub>M (q, AR_SimCompute, tk, i, buf, dvec, posk) ts n"
    using stg by (cases c') auto
  let ?a = "\<lambda>k. ts k (n k)"
  let ?s = "(q, AR_SimCompute, tk, i, buf, dvec, posk)"
  let ?s' = "(q', AR_SimWrite, 0, 0, m_a', m_d, posk)"
  have rel_in: "(?s, ?a, ?s', ?a, (\<lambda>_. dir.N)) \<in> ar_delta_compute M"
    unfolding ar_delta_compute_def using mdelta by auto
  have ma'_gamma: "\<forall>k. m_a' k \<in> \<Gamma>_tm M"
    using valid_mttm_delta(4)[OF vM mdelta] by simp
  have dst_valid: "ar_valid_stage (\<Gamma>_tm M) (bl_tm M) (snd ?s')"
    using ma'_gamma block_width_pos[of "\<Gamma>_tm M"]
    by (auto simp: ar_valid_stage_def)
  have pad_a: "\<forall>j \<ge> k_tm M. ?a j = BLANK4" using pad_blank c'_eq by simp
  have dsupp: "\<forall>j \<ge> k_tm M. m_a' j = bl_tm M \<and> m_d j = dir.N"
    using valid_mttm_delta_support[OF vM mdelta] by blast
  have src_posk: "\<forall>j \<ge> k_tm M. posk j = AR_AtLE"
    using src_bounded by (simp add: ar_stage_bounded_def)
  have kpos_tm: "0 < k_tm M" using vM by (cases M) auto
  have pad_read: "\<forall>j \<ge> k_tm M. ?a j = BLANK4 \<and> ?a j = BLANK4
                    \<and> (\<lambda>_. dir.N) j = dir.N"
    using pad_a by simp
  have dst_bd: "ar_stage_bounded (bl_tm M) (k_tm M) (snd ?s')"
    using dsupp src_posk kpos_tm by (simp add: ar_stage_bounded_def)
  have ard_in: "(?s, ?a, ?s', ?a, (\<lambda>_. dir.N))
                  \<in> alphabet_reduce_delta M"
    unfolding alphabet_reduce_delta_def
    using rel_in vsrc dst_valid pad_read src_bounded dst_bd by auto
  have ts_unchanged: "(\<lambda>k. (ts k)(n k := ?a k)) = ts" by (rule ext) auto
  have pos_unchanged: "(\<lambda>k. go_dir ((\<lambda>_. dir.N) k) (n k)) = n"
    by (rule ext) auto
  let ?c'' = "Config\<^sub>M ?s' ts n"
  have "(Config\<^sub>M ?s ts n,
          Config\<^sub>M ?s' (\<lambda>k. (ts k)(n k := ?a k))
            (\<lambda>k. go_dir ((\<lambda>_. dir.N) k) (n k)))
          \<in> mttm_step (alphabet_reduce_delta M)"
  proof (rule mttm_step.intros)
    show "(?s, ?a, ?s', ?a, (\<lambda>_. dir.N))
            \<in> alphabet_reduce_delta M"
      by (rule ard_in)
  qed
  hence step: "(c', ?c'') \<in> mttm_step (alphabet_reduce_delta M)"
    using c'_eq ts_unchanged pos_unchanged by simp
  show ?thesis
    using step by (intro exI[where x = ?c'']) (simp add: c'_eq)
qed

text \<open>Displacement bound: an \<open>AR_SimAdvance\<close> walk on one tape
  is at most \<open>2b\<close> cells (the \<open>L\<close>-from-\<open>AR_AtFurtherProper\<close>
  worst case).  The \<open>0 < b\<close> hypothesis is needed: the
  \<open>N\<close>-from-\<open>AR_AtLE\<close> displacement is the constant \<open>1\<close>,
  which exceeds \<open>2b = 0\<close>.  Used to discharge target-stage validity
  (\<open>Suc i < 2 * b\<close>) for the walk and boundary arms, whose
  reached bit-counter is bounded by the displacement.\<close>

lemma ar_disp_le_2k:
  assumes "0 < k"
  shows "ar_disp k d pk \<le> 2 * k"
  using assms by (cases d; cases pk) auto

text \<open>The advance walk substep: from an \<open>AR_SimAdvance\<close> stage with
  the bit-counter strictly below the per-tape displacement, one
  \<open>M'\<close>-step moves the active tape \<open>tk\<close>'s head one cell
  \<open>L\<close> (\<open>N\<close> elsewhere) and stays in \<open>AR_SimAdvance\<close> at
  \<open>Suc i\<close>; the tape contents and all other heads are unchanged.
  The \<open>a tk \<noteq> LE4\<close> hypothesis is load-bearing: it both selects
  this arm (\<open>\<delta>\<close>'s stepping arm forbids an \<open>L\<close>-walk off
  \<open>LE4\<close>) and discharges the backward-\<open>\<delta>LE\<close> filter, which
  would otherwise reject the \<open>L\<close>-move on a tape reading \<open>LE4\<close>.
  Target-stage validity rests on the displacement bound
  \<open>ar_disp_le_2k\<close>.\<close>

lemma ar_advance_walk_step:
  fixes M :: "('q, 'a) mttm"
    and c' :: "(sym4, 'q \<times> 'a ar_stage) mt_config"
  assumes vM: "valid_mttm M"
      and stg: "mt_state c' = (q, AR_SimAdvance, tk, i, buf, dvec, posk)"
      and qQ: "q \<in> Q_tm M"
      and notLE: "mt_tape c' tk (mt_pos c' tk) \<noteq> LE4"
      and step_lt: "Suc i < ar_disp (block_width (\<Gamma>_tm M)) (dvec tk) (posk tk)"
      and vsrc: "ar_valid_stage (\<Gamma>_tm M) (bl_tm M)
                   (AR_SimAdvance, tk, i, buf, dvec, posk)"
      and pad_blank: "\<forall>j \<ge> k_tm M. mt_tape c' j (mt_pos c' j) = BLANK4"
      and src_bounded: "ar_stage_bounded (bl_tm M) (k_tm M)
                          (AR_SimAdvance, tk, i, buf, dvec, posk)"
  shows "\<exists>c''. (c', c'') \<in> mttm_step (alphabet_reduce_delta M)
              \<and> mt_state c'' = (q, AR_SimAdvance, tk, Suc i, buf, dvec, posk)
              \<and> mt_tape c'' = mt_tape c'
              \<and> mt_pos c'' = (mt_pos c')(tk := mt_pos c' tk - 1)"
proof -
  obtain ts n where c'_eq:
      "c' = Config\<^sub>M (q, AR_SimAdvance, tk, i, buf, dvec, posk) ts n"
    using stg by (cases c') auto
  let ?a = "\<lambda>k. ts k (n k)"
  let ?d = "\<lambda>kk. if kk = tk then dir.L else dir.N"
  let ?s = "(q, AR_SimAdvance, tk, i, buf, dvec, posk)"
  let ?s' = "(q, AR_SimAdvance, tk, Suc i, buf, dvec, posk)"
  have aTk: "?a tk \<noteq> LE4" using notLE c'_eq by simp
  have rel_in: "(?s, ?a, ?s', ?a, ?d) \<in> ar_delta_advance M"
    unfolding ar_delta_advance_def
    using qQ aTk step_lt by (intro UnI1) blast
  have buf_valid: "\<forall>k. buf k \<in> \<Gamma>_tm M \<union> {bl_tm M}"
    using vsrc by (simp add: ar_valid_stage_def)
  have kpos: "0 < block_width (\<Gamma>_tm M)" using block_width_pos[of "\<Gamma>_tm M"] by simp
  have suc_i_lt: "Suc i < 2 * block_width (\<Gamma>_tm M)"
    using step_lt ar_disp_le_2k[OF kpos, of "dvec tk" "posk tk"] by linarith
  have dst_valid: "ar_valid_stage (\<Gamma>_tm M) (bl_tm M) (snd ?s')"
    using suc_i_lt buf_valid by (simp add: ar_valid_stage_def)
  have pad_a: "\<forall>j \<ge> k_tm M. ?a j = BLANK4" using pad_blank c'_eq by simp
  have tk_lt: "tk < k_tm M" using src_bounded by (simp add: ar_stage_bounded_def)
  have pad_read: "\<forall>j \<ge> k_tm M. ?a j = BLANK4 \<and> ?a j = BLANK4 \<and> ?d j = dir.N"
  proof (intro allI impI)
    fix j assume jge: "k_tm M \<le> j"
    have jne: "j \<noteq> tk" using tk_lt jge by linarith
    show "?a j = BLANK4 \<and> ?a j = BLANK4 \<and> ?d j = dir.N"
      using pad_a jge jne by simp
  qed
  have dst_bd: "ar_stage_bounded (bl_tm M) (k_tm M) (snd ?s')"
    using src_bounded by (simp add: ar_stage_bounded_def)
  have ard_in: "(?s, ?a, ?s', ?a, ?d) \<in> alphabet_reduce_delta M"
    unfolding alphabet_reduce_delta_def
    using rel_in vsrc dst_valid aTk pad_read src_bounded dst_bd
    by (auto split: if_splits)
  have ts_unchanged: "(\<lambda>k. (ts k)(n k := ?a k)) = ts" by (rule ext) auto
  have pos_new: "(\<lambda>k. go_dir (?d k) (n k)) = n(tk := n tk - 1)"
    by (rule ext) simp
  let ?c'' = "Config\<^sub>M ?s' ts (n(tk := n tk - 1))"
  have "(Config\<^sub>M ?s ts n,
          Config\<^sub>M ?s' (\<lambda>k. (ts k)(n k := ?a k))
            (\<lambda>k. go_dir (?d k) (n k)))
          \<in> mttm_step (alphabet_reduce_delta M)"
  proof (rule mttm_step.intros)
    show "(?s, ?a, ?s', ?a, ?d) \<in> alphabet_reduce_delta M" by (rule ard_in)
  qed
  hence step: "(c', ?c'') \<in> mttm_step (alphabet_reduce_delta M)"
    using c'_eq ts_unchanged pos_new by simp
  show ?thesis
    using step by (intro exI[where x = ?c'']) (simp add: c'_eq)
qed

text \<open>The advance boundary substep, non-last tape: the final
  \<open>M'\<close>-step of tape \<open>tk\<close>'s walk, handing off to the next
  tape \<open>k_succ tk\<close> (bit-counter reset to \<open>0\<close>, position-kind
  updated by \<open>ar_newpos\<close>, other tapes' \<open>posk\<close> preserved).
  A single hypothesis covers both firing sub-cases via the arm's own
  disjunction: the \<open>R\<close>-sub-case (\<open>dvec tk = R\<close>, zero
  displacement, no head move) and the non-\<open>R\<close> sub-case
  (\<open>dvec tk \<noteq> R\<close>, the read not \<open>LE4\<close>, counter at
  \<open>Suc i = displacement\<close>, one last \<open>L\<close>-move).  The head
  conclusion is therefore conditional on \<open>dvec tk\<close>.\<close>

lemma ar_advance_boundary_step:
  fixes M :: "('q, 'a) mttm"
    and c' :: "(sym4, 'q \<times> 'a ar_stage) mt_config"
  assumes vM: "valid_mttm M"
      and stg: "mt_state c' = (q, AR_SimAdvance, tk, i, buf, dvec, posk)"
      and qQ: "q \<in> Q_tm M"
      and notlast: "\<not> is_last_k M tk"
      and fire: "(dvec tk = dir.R \<and> i = 0)
                 \<or> (dvec tk \<noteq> dir.R
                     \<and> mt_tape c' tk (mt_pos c' tk) \<noteq> LE4
                     \<and> Suc i = ar_disp (block_width (\<Gamma>_tm M)) (dvec tk) (posk tk))"
      and vsrc: "ar_valid_stage (\<Gamma>_tm M) (bl_tm M)
                   (AR_SimAdvance, tk, i, buf, dvec, posk)"
      and pad_blank: "\<forall>j \<ge> k_tm M. mt_tape c' j (mt_pos c' j) = BLANK4"
      and src_bounded: "ar_stage_bounded (bl_tm M) (k_tm M)
                          (AR_SimAdvance, tk, i, buf, dvec, posk)"
  shows "\<exists>c''. (c', c'') \<in> mttm_step (alphabet_reduce_delta M)
              \<and> mt_state c'' = (q, AR_SimAdvance, k_succ tk, 0, buf, dvec,
                                  posk(tk := ar_newpos (dvec tk) (posk tk)))
              \<and> mt_tape c'' = mt_tape c'
              \<and> mt_pos c'' = (if dvec tk = dir.R then mt_pos c'
                              else (mt_pos c')(tk := mt_pos c' tk - 1))"
proof -
  obtain ts n where c'_eq:
      "c' = Config\<^sub>M (q, AR_SimAdvance, tk, i, buf, dvec, posk) ts n"
    using stg by (cases c') auto
  let ?a = "\<lambda>k. ts k (n k)"
  let ?d = "\<lambda>kk. if kk = tk \<and> dvec tk \<noteq> dir.R then dir.L else dir.N"
  let ?s = "(q, AR_SimAdvance, tk, i, buf, dvec, posk)"
  let ?s' = "(q, AR_SimAdvance, k_succ tk, 0, buf, dvec,
              posk(tk := ar_newpos (dvec tk) (posk tk)))"
  have fire': "(dvec tk = dir.R \<and> i = 0)
               \<or> (dvec tk \<noteq> dir.R \<and> ?a tk \<noteq> LE4
                   \<and> Suc i = ar_disp (block_width (\<Gamma>_tm M)) (dvec tk) (posk tk))"
    using fire c'_eq by simp
  have rel_in: "(?s, ?a, ?s', ?a, ?d) \<in> ar_delta_advance M"
    unfolding ar_delta_advance_def
    by (rule UnI1, rule UnI2) (use qQ notlast fire' in blast)
  have buf_valid: "\<forall>k. buf k \<in> \<Gamma>_tm M \<union> {bl_tm M}"
    using vsrc by (simp add: ar_valid_stage_def)
  have kpos: "0 < block_width (\<Gamma>_tm M)" using block_width_pos[of "\<Gamma>_tm M"] by simp
  have dst_valid: "ar_valid_stage (\<Gamma>_tm M) (bl_tm M) (snd ?s')"
    using kpos buf_valid by (simp add: ar_valid_stage_def)
  have pad_a: "\<forall>j \<ge> k_tm M. ?a j = BLANK4" using pad_blank c'_eq by simp
  have tk_lt: "tk < k_tm M" using src_bounded by (simp add: ar_stage_bounded_def)
  have ksucc_lt: "k_succ tk < k_tm M"
  proof -
    have ne: "Suc tk \<noteq> k_tm M" using notlast by (simp add: is_last_k_def)
    have le: "Suc tk \<le> k_tm M" using tk_lt by simp
    show ?thesis unfolding k_succ_def using le_neq_implies_less[OF le ne] .
  qed
  have pad_read: "\<forall>j \<ge> k_tm M. ?a j = BLANK4 \<and> ?a j = BLANK4 \<and> ?d j = dir.N"
  proof (intro allI impI)
    fix j assume jge: "k_tm M \<le> j"
    have jne: "j \<noteq> tk" using tk_lt jge by linarith
    show "?a j = BLANK4 \<and> ?a j = BLANK4 \<and> ?d j = dir.N"
      using pad_a jge jne by simp
  qed
  have dst_bd: "ar_stage_bounded (bl_tm M) (k_tm M) (snd ?s')"
  proof -
    have pk: "\<forall>j\<ge>k_tm M. (posk(tk := ar_newpos (dvec tk) (posk tk))) j = AR_AtLE"
    proof (intro allI impI)
      fix j assume jge: "k_tm M \<le> j"
      have "j \<noteq> tk" using tk_lt jge by linarith
      thus "(posk(tk := ar_newpos (dvec tk) (posk tk))) j = AR_AtLE"
        using src_bounded jge by (simp add: ar_stage_bounded_def)
    qed
    show ?thesis using src_bounded ksucc_lt pk by (simp add: ar_stage_bounded_def)
  qed
  have ard_in: "(?s, ?a, ?s', ?a, ?d) \<in> alphabet_reduce_delta M"
    unfolding alphabet_reduce_delta_def
    using rel_in vsrc dst_valid fire' pad_read src_bounded dst_bd
    by (auto split: if_splits)
  have ts_unchanged: "(\<lambda>k. (ts k)(n k := ?a k)) = ts" by (rule ext) auto
  have pos_new: "(\<lambda>k. go_dir (?d k) (n k))
                   = (if dvec tk = dir.R then n else n(tk := n tk - 1))"
    by (rule ext) (auto split: if_splits)
  let ?c'' = "Config\<^sub>M ?s' ts (if dvec tk = dir.R then n else n(tk := n tk - 1))"
  have "(Config\<^sub>M ?s ts n,
          Config\<^sub>M ?s' (\<lambda>k. (ts k)(n k := ?a k))
            (\<lambda>k. go_dir (?d k) (n k)))
          \<in> mttm_step (alphabet_reduce_delta M)"
  proof (rule mttm_step.intros)
    show "(?s, ?a, ?s', ?a, ?d) \<in> alphabet_reduce_delta M" by (rule ard_in)
  qed
  hence step: "(c', ?c'') \<in> mttm_step (alphabet_reduce_delta M)"
    using c'_eq ts_unchanged pos_new by simp
  show ?thesis
    using step by (intro exI[where x = ?c'']) (simp add: c'_eq)
qed

text \<open>The advance boundary substep, last tape: as
  \<open>ar_advance_boundary_step\<close> but \<open>tk\<close> is the last tape in
  the enumeration, so the hand-off goes to \<open>AR_SimNext\<close> (with the
  current-tape field reset to \<open>k_unidx 0\<close>) instead of advancing to
  \<open>k_succ tk\<close>.  Same two firing sub-cases and the same conditional
  head conclusion; the arm-selection move is the single \<open>rule UnI2\<close>
  (the third, rightmost arm of \<open>ar_delta_advance\<close>).\<close>

lemma ar_advance_finish_step:
  fixes M :: "('q, 'a) mttm"
    and c' :: "(sym4, 'q \<times> 'a ar_stage) mt_config"
  assumes vM: "valid_mttm M"
      and stg: "mt_state c' = (q, AR_SimAdvance, tk, i, buf, dvec, posk)"
      and qQ: "q \<in> Q_tm M"
      and last: "is_last_k M tk"
      and fire: "(dvec tk = dir.R \<and> i = 0)
                 \<or> (dvec tk \<noteq> dir.R
                     \<and> mt_tape c' tk (mt_pos c' tk) \<noteq> LE4
                     \<and> Suc i = ar_disp (block_width (\<Gamma>_tm M)) (dvec tk) (posk tk))"
      and vsrc: "ar_valid_stage (\<Gamma>_tm M) (bl_tm M)
                   (AR_SimAdvance, tk, i, buf, dvec, posk)"
      and pad_blank: "\<forall>j \<ge> k_tm M. mt_tape c' j (mt_pos c' j) = BLANK4"
      and src_bounded: "ar_stage_bounded (bl_tm M) (k_tm M)
                          (AR_SimAdvance, tk, i, buf, dvec, posk)"
  shows "\<exists>c''. (c', c'') \<in> mttm_step (alphabet_reduce_delta M)
              \<and> mt_state c'' = (q, AR_SimNext, k_unidx 0, 0, buf, dvec,
                                  posk(tk := ar_newpos (dvec tk) (posk tk)))
              \<and> mt_tape c'' = mt_tape c'
              \<and> mt_pos c'' = (if dvec tk = dir.R then mt_pos c'
                              else (mt_pos c')(tk := mt_pos c' tk - 1))"
proof -
  obtain ts n where c'_eq:
      "c' = Config\<^sub>M (q, AR_SimAdvance, tk, i, buf, dvec, posk) ts n"
    using stg by (cases c') auto
  let ?a = "\<lambda>k. ts k (n k)"
  let ?d = "\<lambda>kk. if kk = tk \<and> dvec tk \<noteq> dir.R then dir.L else dir.N"
  let ?s = "(q, AR_SimAdvance, tk, i, buf, dvec, posk)"
  let ?s' = "(q, AR_SimNext, k_unidx 0, 0, buf, dvec,
              posk(tk := ar_newpos (dvec tk) (posk tk)))"
  have fire': "(dvec tk = dir.R \<and> i = 0)
               \<or> (dvec tk \<noteq> dir.R \<and> ?a tk \<noteq> LE4
                   \<and> Suc i = ar_disp (block_width (\<Gamma>_tm M)) (dvec tk) (posk tk))"
    using fire c'_eq by simp
  have rel_in: "(?s, ?a, ?s', ?a, ?d) \<in> ar_delta_advance M"
    unfolding ar_delta_advance_def
    by (rule UnI2) (use qQ last fire' in blast)
  have buf_valid: "\<forall>k. buf k \<in> \<Gamma>_tm M \<union> {bl_tm M}"
    using vsrc by (simp add: ar_valid_stage_def)
  have kpos: "0 < block_width (\<Gamma>_tm M)" using block_width_pos[of "\<Gamma>_tm M"] by simp
  have dst_valid: "ar_valid_stage (\<Gamma>_tm M) (bl_tm M) (snd ?s')"
    using kpos buf_valid by (simp add: ar_valid_stage_def)
  have pad_a: "\<forall>j \<ge> k_tm M. ?a j = BLANK4" using pad_blank c'_eq by simp
  have tk_lt: "tk < k_tm M" using src_bounded by (simp add: ar_stage_bounded_def)
  have kpos_tm: "0 < k_tm M" using vM by (cases M) auto
  have pad_read: "\<forall>j \<ge> k_tm M. ?a j = BLANK4 \<and> ?a j = BLANK4 \<and> ?d j = dir.N"
  proof (intro allI impI)
    fix j assume jge: "k_tm M \<le> j"
    have jne: "j \<noteq> tk" using tk_lt jge by linarith
    show "?a j = BLANK4 \<and> ?a j = BLANK4 \<and> ?d j = dir.N"
      using pad_a jge jne by simp
  qed
  have dst_bd: "ar_stage_bounded (bl_tm M) (k_tm M) (snd ?s')"
  proof -
    have pk: "\<forall>j\<ge>k_tm M. (posk(tk := ar_newpos (dvec tk) (posk tk))) j = AR_AtLE"
    proof (intro allI impI)
      fix j assume jge: "k_tm M \<le> j"
      have "j \<noteq> tk" using tk_lt jge by linarith
      thus "(posk(tk := ar_newpos (dvec tk) (posk tk))) j = AR_AtLE"
        using src_bounded jge by (simp add: ar_stage_bounded_def)
    qed
    show ?thesis using src_bounded kpos_tm pk
      by (simp add: ar_stage_bounded_def k_unidx_def)
  qed
  have ard_in: "(?s, ?a, ?s', ?a, ?d) \<in> alphabet_reduce_delta M"
    unfolding alphabet_reduce_delta_def
    using rel_in vsrc dst_valid fire' pad_read src_bounded dst_bd
    by (auto split: if_splits)
  have ts_unchanged: "(\<lambda>k. (ts k)(n k := ?a k)) = ts" by (rule ext) auto
  have pos_new: "(\<lambda>k. go_dir (?d k) (n k))
                   = (if dvec tk = dir.R then n else n(tk := n tk - 1))"
    by (rule ext) (auto split: if_splits)
  let ?c'' = "Config\<^sub>M ?s' ts (if dvec tk = dir.R then n else n(tk := n tk - 1))"
  have "(Config\<^sub>M ?s ts n,
          Config\<^sub>M ?s' (\<lambda>k. (ts k)(n k := ?a k))
            (\<lambda>k. go_dir (?d k) (n k)))
          \<in> mttm_step (alphabet_reduce_delta M)"
  proof (rule mttm_step.intros)
    show "(?s, ?a, ?s', ?a, ?d) \<in> alphabet_reduce_delta M" by (rule ard_in)
  qed
  hence step: "(c', ?c'') \<in> mttm_step (alphabet_reduce_delta M)"
    using c'_eq ts_unchanged pos_new by simp
  show ?thesis
    using step by (intro exI[where x = ?c'']) (simp add: c'_eq)
qed

text \<open>The write LE-skip substep, non-last tape: when \<open>buf tk\<close>
  is the left-end marker, the cell at \<open>sim_pos 0 = 0\<close> is already
  \<open>LE4\<close> and need not be rewritten, so the per-tape write phase is
  skipped — a single all-\<open>N\<close> substep handing off to the next tape
  \<open>k_succ tk\<close> with the bit-counter still \<open>0\<close>.  Tape and
  heads unchanged (the compute-step shape).\<close>

lemma ar_write_le_step:
  fixes M :: "('q, 'a) mttm"
    and c' :: "(sym4, 'q \<times> 'a ar_stage) mt_config"
  assumes vM: "valid_mttm M"
      and stg: "mt_state c' = (q, AR_SimWrite, tk, 0, buf, dvec, posk)"
      and qQ: "q \<in> Q_tm M"
      and poskLE: "posk tk = AR_AtLE"
      and notlast: "\<not> is_last_k M tk"
      and vsrc: "ar_valid_stage (\<Gamma>_tm M) (bl_tm M)
                   (AR_SimWrite, tk, 0, buf, dvec, posk)"
      and pad_blank: "\<forall>j \<ge> k_tm M. mt_tape c' j (mt_pos c' j) = BLANK4"
      and src_bounded: "ar_stage_bounded (bl_tm M) (k_tm M)
                          (AR_SimWrite, tk, 0, buf, dvec, posk)"
  shows "\<exists>c''. (c', c'') \<in> mttm_step (alphabet_reduce_delta M)
              \<and> mt_state c'' = (q, AR_SimWrite, k_succ tk, 0, buf, dvec, posk)
              \<and> mt_tape c'' = mt_tape c'
              \<and> mt_pos c'' = mt_pos c'"
proof -
  obtain ts n where c'_eq:
      "c' = Config\<^sub>M (q, AR_SimWrite, tk, 0, buf, dvec, posk) ts n"
    using stg by (cases c') auto
  let ?a = "\<lambda>k. ts k (n k)"
  let ?d = "\<lambda>_. dir.N"
  let ?s = "(q, AR_SimWrite, tk, 0, buf, dvec, posk)"
  let ?s' = "(q, AR_SimWrite, k_succ tk, 0, buf, dvec, posk)"
  have rel_in: "(?s, ?a, ?s', ?a, ?d) \<in> ar_delta_write M"
    unfolding ar_delta_write_def
    using qQ poskLE notlast by (intro UnI1) blast
  have buf_valid: "\<forall>k. buf k \<in> \<Gamma>_tm M \<union> {bl_tm M}"
    using vsrc by (simp add: ar_valid_stage_def)
  have kpos: "0 < block_width (\<Gamma>_tm M)" using block_width_pos[of "\<Gamma>_tm M"] by simp
  have dst_valid: "ar_valid_stage (\<Gamma>_tm M) (bl_tm M) (snd ?s')"
    using kpos buf_valid by (simp add: ar_valid_stage_def)
  have pad_a: "\<forall>j \<ge> k_tm M. ?a j = BLANK4" using pad_blank c'_eq by simp
  have tk_lt: "tk < k_tm M" using src_bounded by (simp add: ar_stage_bounded_def)
  have ksucc_lt: "k_succ tk < k_tm M"
  proof -
    have ne: "Suc tk \<noteq> k_tm M" using notlast by (simp add: is_last_k_def)
    have le: "Suc tk \<le> k_tm M" using tk_lt by simp
    show ?thesis unfolding k_succ_def using le_neq_implies_less[OF le ne] .
  qed
  have pad_read: "\<forall>j \<ge> k_tm M. ?a j = BLANK4 \<and> ?a j = BLANK4 \<and> ?d j = dir.N"
    using pad_a by simp
  have dst_bd: "ar_stage_bounded (bl_tm M) (k_tm M) (snd ?s')"
    using src_bounded ksucc_lt by (simp add: ar_stage_bounded_def)
  have ard_in: "(?s, ?a, ?s', ?a, ?d) \<in> alphabet_reduce_delta M"
    unfolding alphabet_reduce_delta_def
    using rel_in vsrc dst_valid pad_read src_bounded dst_bd by auto
  have ts_unchanged: "(\<lambda>k. (ts k)(n k := ?a k)) = ts" by (rule ext) auto
  have pos_unchanged: "(\<lambda>k. go_dir (?d k) (n k)) = n" by (rule ext) auto
  let ?c'' = "Config\<^sub>M ?s' ts n"
  have "(Config\<^sub>M ?s ts n,
          Config\<^sub>M ?s' (\<lambda>k. (ts k)(n k := ?a k))
            (\<lambda>k. go_dir (?d k) (n k)))
          \<in> mttm_step (alphabet_reduce_delta M)"
  proof (rule mttm_step.intros)
    show "(?s, ?a, ?s', ?a, ?d) \<in> alphabet_reduce_delta M" by (rule ard_in)
  qed
  hence step: "(c', ?c'') \<in> mttm_step (alphabet_reduce_delta M)"
    using c'_eq ts_unchanged pos_unchanged by simp
  show ?thesis
    using step by (intro exI[where x = ?c'']) (simp add: c'_eq)
qed

text \<open>The write LE-skip substep, last tape: as \<open>ar_write_le_step\<close>
  but \<open>tk\<close> is the last tape, so the hand-off goes to
  \<open>AR_SimAdvance\<close> (current-tape field reset to \<open>k_unidx 0\<close>).
  Arm 2 of the six-arm \<open>ar_delta_write\<close> union.\<close>

lemma ar_write_le_finish_step:
  fixes M :: "('q, 'a) mttm"
    and c' :: "(sym4, 'q \<times> 'a ar_stage) mt_config"
  assumes vM: "valid_mttm M"
      and stg: "mt_state c' = (q, AR_SimWrite, tk, 0, buf, dvec, posk)"
      and qQ: "q \<in> Q_tm M"
      and poskLE: "posk tk = AR_AtLE"
      and last: "is_last_k M tk"
      and vsrc: "ar_valid_stage (\<Gamma>_tm M) (bl_tm M)
                   (AR_SimWrite, tk, 0, buf, dvec, posk)"
      and pad_blank: "\<forall>j \<ge> k_tm M. mt_tape c' j (mt_pos c' j) = BLANK4"
      and src_bounded: "ar_stage_bounded (bl_tm M) (k_tm M)
                          (AR_SimWrite, tk, 0, buf, dvec, posk)"
  shows "\<exists>c''. (c', c'') \<in> mttm_step (alphabet_reduce_delta M)
              \<and> mt_state c'' = (q, AR_SimAdvance, k_unidx 0, 0, buf, dvec, posk)
              \<and> mt_tape c'' = mt_tape c'
              \<and> mt_pos c'' = mt_pos c'"
proof -
  obtain ts n where c'_eq:
      "c' = Config\<^sub>M (q, AR_SimWrite, tk, 0, buf, dvec, posk) ts n"
    using stg by (cases c') auto
  let ?a = "\<lambda>k. ts k (n k)"
  let ?d = "\<lambda>_. dir.N"
  let ?s = "(q, AR_SimWrite, tk, 0, buf, dvec, posk)"
  let ?s' = "(q, AR_SimAdvance, k_unidx 0, 0, buf, dvec, posk)"
  have rel_in: "(?s, ?a, ?s', ?a, ?d) \<in> ar_delta_write M"
    unfolding ar_delta_write_def
    by (rule UnI1, rule UnI1, rule UnI1, rule UnI1, rule UnI2)
       (use qQ poskLE last in blast)
  have buf_valid: "\<forall>k. buf k \<in> \<Gamma>_tm M \<union> {bl_tm M}"
    using vsrc by (simp add: ar_valid_stage_def)
  have kpos: "0 < block_width (\<Gamma>_tm M)" using block_width_pos[of "\<Gamma>_tm M"] by simp
  have dst_valid: "ar_valid_stage (\<Gamma>_tm M) (bl_tm M) (snd ?s')"
    using kpos buf_valid by (simp add: ar_valid_stage_def)
  have pad_a: "\<forall>j \<ge> k_tm M. ?a j = BLANK4" using pad_blank c'_eq by simp
  have kpos_tm: "0 < k_tm M" using vM by (cases M) auto
  have pad_read: "\<forall>j \<ge> k_tm M. ?a j = BLANK4 \<and> ?a j = BLANK4 \<and> ?d j = dir.N"
    using pad_a by simp
  have dst_bd: "ar_stage_bounded (bl_tm M) (k_tm M) (snd ?s')"
    using src_bounded kpos_tm by (simp add: ar_stage_bounded_def k_unidx_def)
  have ard_in: "(?s, ?a, ?s', ?a, ?d) \<in> alphabet_reduce_delta M"
    unfolding alphabet_reduce_delta_def
    using rel_in vsrc dst_valid pad_read src_bounded dst_bd by auto
  have ts_unchanged: "(\<lambda>k. (ts k)(n k := ?a k)) = ts" by (rule ext) auto
  have pos_unchanged: "(\<lambda>k. go_dir (?d k) (n k)) = n" by (rule ext) auto
  let ?c'' = "Config\<^sub>M ?s' ts n"
  have "(Config\<^sub>M ?s ts n,
          Config\<^sub>M ?s' (\<lambda>k. (ts k)(n k := ?a k))
            (\<lambda>k. go_dir (?d k) (n k)))
          \<in> mttm_step (alphabet_reduce_delta M)"
  proof (rule mttm_step.intros)
    show "(?s, ?a, ?s', ?a, ?d) \<in> alphabet_reduce_delta M" by (rule ard_in)
  qed
  hence step: "(c', ?c'') \<in> mttm_step (alphabet_reduce_delta M)"
    using c'_eq ts_unchanged pos_unchanged by simp
  show ?thesis
    using step by (intro exI[where x = ?c'']) (simp add: c'_eq)
qed

text \<open>The write back-walk substep (proper region,
  \<open>Suc i \<le> b\<close>): with \<open>buf tk\<close> a proper symbol, the head
  first walks \<open>L\<close> back across the \<open>b\<close>-cell block before the
  forward-write phase; one \<open>L\<close>-move on \<open>tk\<close> (\<open>N\<close>
  elsewhere), no writes, staying in \<open>AR_SimWrite\<close> at \<open>Suc i\<close>.
  Structurally the \<open>ar_advance_walk_step\<close> shape; arm 3 of the
  union.  As there, \<open>a tk \<noteq> LE4\<close> selects the arm and discharges
  the backward-\<open>\<delta>LE\<close> filter.\<close>

lemma ar_write_walk_step:
  fixes M :: "('q, 'a) mttm"
    and c' :: "(sym4, 'q \<times> 'a ar_stage) mt_config"
  assumes vM: "valid_mttm M"
      and stg: "mt_state c' = (q, AR_SimWrite, tk, i, buf, dvec, posk)"
      and qQ: "q \<in> Q_tm M"
      and poskproper: "posk tk \<noteq> AR_AtLE"
      and notLE: "mt_tape c' tk (mt_pos c' tk) \<noteq> LE4"
      and step_le: "Suc i \<le> block_width (\<Gamma>_tm M)"
      and vsrc: "ar_valid_stage (\<Gamma>_tm M) (bl_tm M)
                   (AR_SimWrite, tk, i, buf, dvec, posk)"
      and pad_blank: "\<forall>j \<ge> k_tm M. mt_tape c' j (mt_pos c' j) = BLANK4"
      and src_bounded: "ar_stage_bounded (bl_tm M) (k_tm M)
                          (AR_SimWrite, tk, i, buf, dvec, posk)"
  shows "\<exists>c''. (c', c'') \<in> mttm_step (alphabet_reduce_delta M)
              \<and> mt_state c'' = (q, AR_SimWrite, tk, Suc i, buf, dvec, posk)
              \<and> mt_tape c'' = mt_tape c'
              \<and> mt_pos c'' = (mt_pos c')(tk := mt_pos c' tk - 1)"
proof -
  obtain ts n where c'_eq:
      "c' = Config\<^sub>M (q, AR_SimWrite, tk, i, buf, dvec, posk) ts n"
    using stg by (cases c') auto
  let ?a = "\<lambda>k. ts k (n k)"
  let ?d = "\<lambda>kk. if kk = tk then dir.L else dir.N"
  let ?s = "(q, AR_SimWrite, tk, i, buf, dvec, posk)"
  let ?s' = "(q, AR_SimWrite, tk, Suc i, buf, dvec, posk)"
  have aTk: "?a tk \<noteq> LE4" using notLE c'_eq by simp
  have rel_in: "(?s, ?a, ?s', ?a, ?d) \<in> ar_delta_write M"
    unfolding ar_delta_write_def
    by (rule UnI1, rule UnI1, rule UnI1, rule UnI2)
       (use qQ poskproper aTk step_le in blast)
  have buf_valid: "\<forall>k. buf k \<in> \<Gamma>_tm M \<union> {bl_tm M}"
    using vsrc by (simp add: ar_valid_stage_def)
  have kpos: "0 < block_width (\<Gamma>_tm M)" using block_width_pos[of "\<Gamma>_tm M"] by simp
  have suc_i_lt: "Suc i < 2 * block_width (\<Gamma>_tm M)"
    using step_le kpos by linarith
  have dst_valid: "ar_valid_stage (\<Gamma>_tm M) (bl_tm M) (snd ?s')"
    using suc_i_lt buf_valid by (simp add: ar_valid_stage_def)
  have pad_a: "\<forall>j \<ge> k_tm M. ?a j = BLANK4" using pad_blank c'_eq by simp
  have tk_lt: "tk < k_tm M" using src_bounded by (simp add: ar_stage_bounded_def)
  have pad_read: "\<forall>j \<ge> k_tm M. ?a j = BLANK4 \<and> ?a j = BLANK4 \<and> ?d j = dir.N"
  proof (intro allI impI)
    fix j assume jge: "k_tm M \<le> j"
    have jne: "j \<noteq> tk" using tk_lt jge by linarith
    show "?a j = BLANK4 \<and> ?a j = BLANK4 \<and> ?d j = dir.N"
      using pad_a jge jne by simp
  qed
  have dst_bd: "ar_stage_bounded (bl_tm M) (k_tm M) (snd ?s')"
    using src_bounded by (simp add: ar_stage_bounded_def)
  have ard_in: "(?s, ?a, ?s', ?a, ?d) \<in> alphabet_reduce_delta M"
    unfolding alphabet_reduce_delta_def
    using rel_in vsrc dst_valid aTk pad_read src_bounded dst_bd
    by (auto split: if_splits)
  have ts_unchanged: "(\<lambda>k. (ts k)(n k := ?a k)) = ts" by (rule ext) auto
  have pos_new: "(\<lambda>k. go_dir (?d k) (n k)) = n(tk := n tk - 1)"
    by (rule ext) simp
  let ?c'' = "Config\<^sub>M ?s' ts (n(tk := n tk - 1))"
  have "(Config\<^sub>M ?s ts n,
          Config\<^sub>M ?s' (\<lambda>k. (ts k)(n k := ?a k))
            (\<lambda>k. go_dir (?d k) (n k)))
          \<in> mttm_step (alphabet_reduce_delta M)"
  proof (rule mttm_step.intros)
    show "(?s, ?a, ?s', ?a, ?d) \<in> alphabet_reduce_delta M" by (rule ard_in)
  qed
  hence step: "(c', ?c'') \<in> mttm_step (alphabet_reduce_delta M)"
    using c'_eq ts_unchanged pos_new by simp
  show ?thesis
    using step by (intro exI[where x = ?c'']) (simp add: c'_eq)
qed

text \<open>The forward-write image is never the left-end marker: it is
  \<open>BLANK4\<close> (blank symbol) or a bit cell of \<open>encode_symbol\<close>
  (\<open>BIT0\<close>/\<open>BIT1\<close> only, by \<open>encode_symbol_cell_domain\<close>),
  in range \<open>j < b\<close>.  This is what makes the forward-write arms
  legal under both \<open>\<delta>LE\<close> filters.\<close>

lemma write_bit_not_LE4:
  assumes "j < block_width \<Gamma>"
  shows "write_bit \<Gamma> bl x j \<noteq> LE4"
proof (cases "x = bl")
  case True
  thus ?thesis by (simp add: write_bit_def)
next
  case False
  have jl: "j < length (encode_symbol \<Gamma> bl x)"
    using assms by (simp add: encode_symbol_def)
  have "encode_symbol \<Gamma> bl x ! j \<in> {BIT0, BIT1}"
    using nth_mem[OF jl] encode_symbol_cell_domain[of \<Gamma> bl x] by blast
  thus ?thesis using False by (auto simp: write_bit_def)
qed

text \<open>The \<open>j\<close>-th cell of a block's \<open>cell_repr\<close> is the
  \<open>j\<close>-th \<open>write_bit\<close> image (\<open>j < b\<close>), uniformly
  across the blank and proper branches.  This is the bridge from the
  tape-correspondence cell value (\<open>cell_repr \<dots> ! j\<close>) to the
  \<open>write_bit\<close> image that the write phase produces, and to the
  \<open>\<noteq> LE4\<close> fact the back-walk / bit-write guards need.\<close>

lemma cell_repr_nth_write_bit:
  assumes "j < block_width \<Gamma>"
  shows "cell_repr \<Gamma> bl x ! j = write_bit \<Gamma> bl x j"
  using assms by (cases "x = bl")
    (simp_all add: cell_repr_def write_bit_def length_encode_symbol)

lemma cell_repr_nth_not_LE4:
  assumes "j < block_width \<Gamma>"
  shows "cell_repr \<Gamma> bl x ! j \<noteq> LE4"
  using cell_repr_nth_write_bit[OF assms] write_bit_not_LE4[OF assms] by simp

text \<open>Under the encoding, the only \<open>LE4\<close> cell of the simulated
  tape is at position \<open>0\<close>: every position \<open>\<ge> 1\<close> lies in
  some proper block \<open>[sim_pos b p, sim_pos b p + b)\<close> (the
  \<open>div\<close>/\<open>mod\<close> decomposition of \<open>pos - 1\<close>) and so
  carries a \<open>cell_repr\<close> cell, which is never \<open>LE4\<close>.  The
  fact the advance back-walk's \<open>notLE\<close> guard rests on: a head
  walking through proper cells never reads the left-end marker.\<close>
lemma ar_tape_correspondence_not_LE4:
  assumes corr: "ar_tape_correspondence \<Gamma> le bl tM tM'"
      and pos1: "1 \<le> pos"
  shows "tM' pos \<noteq> LE4"
proof -
  let ?K = "block_width \<Gamma>"
  have K1: "1 \<le> ?K" using block_width_pos .
  have jK: "(pos - 1) mod ?K < ?K" using K1 by simp
  have p1: "1 \<le> (pos - 1) div ?K + 1" by simp
  have pe: "pos = sim_pos ?K ((pos - 1) div ?K + 1) + (pos - 1) mod ?K"
  proof -
    have "sim_pos ?K ((pos - 1) div ?K + 1) + (pos - 1) mod ?K
            = (pos - 1) div ?K * ?K + (pos - 1) mod ?K + 1"
      by (simp add: sim_pos_def)
    also have "\<dots> = (pos - 1) + 1" by (simp add: div_mult_mod_eq)
    also have "\<dots> = pos" using pos1 by simp
    finally show ?thesis by simp
  qed
  have corrprop: "tM' (sim_pos ?K p + j) = cell_repr \<Gamma> bl (tM p) ! j"
    if "1 \<le> p" and "j < ?K" for p j
    using corr that unfolding ar_tape_correspondence_def by blast
  have "tM' pos
          = cell_repr \<Gamma> bl (tM ((pos - 1) div ?K + 1)) ! ((pos - 1) mod ?K)"
    using corrprop[OF p1 jK] pe by simp
  thus ?thesis using cell_repr_nth_not_LE4[OF jK] by simp
qed

text \<open>The forward-write stepping substep (proper region,
  \<open>b \<le> i\<close>, \<open>Suc i < 2b\<close>): the \<open>(i-b)\<close>-th cell of
  \<open>cell_repr (buf tk)\<close> is written at \<open>tk\<close>, the head moves
  \<open>R\<close> on \<open>tk\<close> (\<open>N\<close> elsewhere), staying in
  \<open>AR_SimWrite\<close> at \<open>Suc i\<close>.  First per-substep lemma that
  mutates the tape: the conclusion's \<open>mt_tape\<close> is a nested
  \<open>fun_upd\<close> writing \<open>write_bit \<Gamma> bl (buf tk) (i-b)\<close> at
  \<open>tk\<close>'s head cell.  The read precondition \<open>a tk \<noteq> LE4\<close>
  (proper region is past \<open>LE4\<close>) discharges the backward-\<open>\<delta>LE\<close>
  filter; \<open>write_bit_not_LE4\<close> discharges the forward filter.\<close>

lemma ar_write_bit_step:
  fixes M :: "('q, 'a) mttm"
    and c' :: "(sym4, 'q \<times> 'a ar_stage) mt_config"
  assumes vM: "valid_mttm M"
      and stg: "mt_state c' = (q, AR_SimWrite, tk, i, buf, dvec, posk)"
      and qQ: "q \<in> Q_tm M"
      and poskproper: "posk tk \<noteq> AR_AtLE"
      and notLE: "mt_tape c' tk (mt_pos c' tk) \<noteq> LE4"
      and ilo: "block_width (\<Gamma>_tm M) \<le> i"
      and ihi: "Suc i < 2 * block_width (\<Gamma>_tm M)"
      and vsrc: "ar_valid_stage (\<Gamma>_tm M) (bl_tm M)
                   (AR_SimWrite, tk, i, buf, dvec, posk)"
      and pad_blank: "\<forall>j \<ge> k_tm M. mt_tape c' j (mt_pos c' j) = BLANK4"
      and src_bounded: "ar_stage_bounded (bl_tm M) (k_tm M)
                          (AR_SimWrite, tk, i, buf, dvec, posk)"
  shows "\<exists>c''. (c', c'') \<in> mttm_step (alphabet_reduce_delta M)
              \<and> mt_state c'' = (q, AR_SimWrite, tk, Suc i, buf, dvec, posk)
              \<and> mt_tape c'' = (mt_tape c')(tk :=
                    (mt_tape c' tk)(mt_pos c' tk :=
                       write_bit (\<Gamma>_tm M) (bl_tm M) (buf tk)
                                 (i - block_width (\<Gamma>_tm M))))
              \<and> mt_pos c'' = (mt_pos c')(tk := Suc (mt_pos c' tk))"
proof -
  obtain ts n where c'_eq:
      "c' = Config\<^sub>M (q, AR_SimWrite, tk, i, buf, dvec, posk) ts n"
    using stg by (cases c') auto
  let ?wb = "write_bit (\<Gamma>_tm M) (bl_tm M) (buf tk) (i - block_width (\<Gamma>_tm M))"
  let ?a = "\<lambda>k. ts k (n k)"
  let ?a' = "\<lambda>kk. if kk = tk then ?wb else ?a kk"
  let ?d = "\<lambda>kk. if kk = tk then dir.R else dir.N"
  let ?s = "(q, AR_SimWrite, tk, i, buf, dvec, posk)"
  let ?s' = "(q, AR_SimWrite, tk, Suc i, buf, dvec, posk)"
  have aTk: "?a tk \<noteq> LE4" using notLE c'_eq by simp
  have jlt: "i - block_width (\<Gamma>_tm M) < block_width (\<Gamma>_tm M)" using ilo ihi by linarith
  have wb_not_LE: "?wb \<noteq> LE4" using write_bit_not_LE4[OF jlt] .
  have rel_in: "(?s, ?a, ?s', ?a', ?d) \<in> ar_delta_write M"
    unfolding ar_delta_write_def
    by (rule UnI1, rule UnI1, rule UnI2)
       (use qQ poskproper ilo ihi in blast)
  have buf_valid: "\<forall>k. buf k \<in> \<Gamma>_tm M \<union> {bl_tm M}"
    using vsrc by (simp add: ar_valid_stage_def)
  have dst_valid: "ar_valid_stage (\<Gamma>_tm M) (bl_tm M) (snd ?s')"
    using ihi buf_valid by (simp add: ar_valid_stage_def)
  have pad_a: "\<forall>j \<ge> k_tm M. ?a j = BLANK4" using pad_blank c'_eq by simp
  have tk_lt: "tk < k_tm M" using src_bounded by (simp add: ar_stage_bounded_def)
  have pad_read: "\<forall>j \<ge> k_tm M. ?a j = BLANK4 \<and> ?a' j = BLANK4 \<and> ?d j = dir.N"
  proof (intro allI impI)
    fix j assume jge: "k_tm M \<le> j"
    have jne: "j \<noteq> tk" using tk_lt jge by linarith
    show "?a j = BLANK4 \<and> ?a' j = BLANK4 \<and> ?d j = dir.N"
      using pad_a jge jne by simp
  qed
  have dst_bd: "ar_stage_bounded (bl_tm M) (k_tm M) (snd ?s')"
    using src_bounded by (simp add: ar_stage_bounded_def)
  have ard_in: "(?s, ?a, ?s', ?a', ?d) \<in> alphabet_reduce_delta M"
    unfolding alphabet_reduce_delta_def
    using rel_in vsrc dst_valid aTk wb_not_LE pad_read src_bounded dst_bd
    by (auto split: if_splits)
  have tape_new: "(\<lambda>k. (ts k)(n k := ?a' k))
                    = ts(tk := (ts tk)(n tk := ?wb))"
    by (rule ext) (auto simp: fun_upd_triv)
  have pos_new: "(\<lambda>k. go_dir (?d k) (n k)) = n(tk := Suc (n tk))"
    by (rule ext) simp
  let ?c'' = "Config\<^sub>M ?s' (ts(tk := (ts tk)(n tk := ?wb))) (n(tk := Suc (n tk)))"
  have "(Config\<^sub>M ?s ts n,
          Config\<^sub>M ?s' (\<lambda>k. (ts k)(n k := ?a' k))
            (\<lambda>k. go_dir (?d k) (n k)))
          \<in> mttm_step (alphabet_reduce_delta M)"
  proof (rule mttm_step.intros)
    show "(?s, ?a, ?s', ?a', ?d) \<in> alphabet_reduce_delta M" by (rule ard_in)
  qed
  hence step: "(c', ?c'') \<in> mttm_step (alphabet_reduce_delta M)"
    using c'_eq tape_new pos_new by simp
  show ?thesis
    using step by (intro exI[where x = ?c'']) (simp add: c'_eq)
qed

text \<open>The forward-write boundary substep, non-last tape
  (\<open>Suc i = 2b\<close>): the last cell of \<open>cell_repr (buf tk)\<close> is
  written (\<open>j = i - b = b - 1\<close>), the head moves \<open>R\<close>, and the
  phase hands off to the next tape \<open>k_succ tk\<close> with the bit-counter
  reset to \<open>0\<close>.  The \<open>ar_write_bit_step\<close> tape-change shape;
  arm 5 of the union.\<close>

lemma ar_write_bit_boundary_step:
  fixes M :: "('q, 'a) mttm"
    and c' :: "(sym4, 'q \<times> 'a ar_stage) mt_config"
  assumes vM: "valid_mttm M"
      and stg: "mt_state c' = (q, AR_SimWrite, tk, i, buf, dvec, posk)"
      and qQ: "q \<in> Q_tm M"
      and poskproper: "posk tk \<noteq> AR_AtLE"
      and notLE: "mt_tape c' tk (mt_pos c' tk) \<noteq> LE4"
      and notlast: "\<not> is_last_k M tk"
      and ihi: "Suc i = 2 * block_width (\<Gamma>_tm M)"
      and vsrc: "ar_valid_stage (\<Gamma>_tm M) (bl_tm M)
                   (AR_SimWrite, tk, i, buf, dvec, posk)"
      and pad_blank: "\<forall>j \<ge> k_tm M. mt_tape c' j (mt_pos c' j) = BLANK4"
      and src_bounded: "ar_stage_bounded (bl_tm M) (k_tm M)
                          (AR_SimWrite, tk, i, buf, dvec, posk)"
  shows "\<exists>c''. (c', c'') \<in> mttm_step (alphabet_reduce_delta M)
              \<and> mt_state c'' = (q, AR_SimWrite, k_succ tk, 0, buf, dvec, posk)
              \<and> mt_tape c'' = (mt_tape c')(tk :=
                    (mt_tape c' tk)(mt_pos c' tk :=
                       write_bit (\<Gamma>_tm M) (bl_tm M) (buf tk)
                                 (i - block_width (\<Gamma>_tm M))))
              \<and> mt_pos c'' = (mt_pos c')(tk := Suc (mt_pos c' tk))"
proof -
  obtain ts n where c'_eq:
      "c' = Config\<^sub>M (q, AR_SimWrite, tk, i, buf, dvec, posk) ts n"
    using stg by (cases c') auto
  let ?wb = "write_bit (\<Gamma>_tm M) (bl_tm M) (buf tk) (i - block_width (\<Gamma>_tm M))"
  let ?a = "\<lambda>k. ts k (n k)"
  let ?a' = "\<lambda>kk. if kk = tk then ?wb else ?a kk"
  let ?d = "\<lambda>kk. if kk = tk then dir.R else dir.N"
  let ?s = "(q, AR_SimWrite, tk, i, buf, dvec, posk)"
  let ?s' = "(q, AR_SimWrite, k_succ tk, 0, buf, dvec, posk)"
  have aTk: "?a tk \<noteq> LE4" using notLE c'_eq by simp
  have kpos: "0 < block_width (\<Gamma>_tm M)" using block_width_pos[of "\<Gamma>_tm M"] by simp
  have jlt: "i - block_width (\<Gamma>_tm M) < block_width (\<Gamma>_tm M)" using ihi kpos by linarith
  have wb_not_LE: "?wb \<noteq> LE4" using write_bit_not_LE4[OF jlt] .
  have rel_in: "(?s, ?a, ?s', ?a', ?d) \<in> ar_delta_write M"
    unfolding ar_delta_write_def
    by (rule UnI1, rule UnI2) (use qQ poskproper notlast ihi in blast)
  have buf_valid: "\<forall>k. buf k \<in> \<Gamma>_tm M \<union> {bl_tm M}"
    using vsrc by (simp add: ar_valid_stage_def)
  have dst_valid: "ar_valid_stage (\<Gamma>_tm M) (bl_tm M) (snd ?s')"
    using kpos buf_valid by (simp add: ar_valid_stage_def)
  have pad_a: "\<forall>j \<ge> k_tm M. ?a j = BLANK4" using pad_blank c'_eq by simp
  have tk_lt: "tk < k_tm M" using src_bounded by (simp add: ar_stage_bounded_def)
  have ksucc_lt: "k_succ tk < k_tm M"
  proof -
    have ne: "Suc tk \<noteq> k_tm M" using notlast by (simp add: is_last_k_def)
    have le: "Suc tk \<le> k_tm M" using tk_lt by simp
    show ?thesis unfolding k_succ_def using le_neq_implies_less[OF le ne] .
  qed
  have pad_read: "\<forall>j \<ge> k_tm M. ?a j = BLANK4 \<and> ?a' j = BLANK4 \<and> ?d j = dir.N"
  proof (intro allI impI)
    fix j assume jge: "k_tm M \<le> j"
    have jne: "j \<noteq> tk" using tk_lt jge by linarith
    show "?a j = BLANK4 \<and> ?a' j = BLANK4 \<and> ?d j = dir.N"
      using pad_a jge jne by simp
  qed
  have dst_bd: "ar_stage_bounded (bl_tm M) (k_tm M) (snd ?s')"
    using src_bounded ksucc_lt by (simp add: ar_stage_bounded_def)
  have ard_in: "(?s, ?a, ?s', ?a', ?d) \<in> alphabet_reduce_delta M"
    unfolding alphabet_reduce_delta_def
    using rel_in vsrc dst_valid aTk wb_not_LE pad_read src_bounded dst_bd
    by (auto split: if_splits)
  have tape_new: "(\<lambda>k. (ts k)(n k := ?a' k))
                    = ts(tk := (ts tk)(n tk := ?wb))"
    by (rule ext) (auto simp: fun_upd_triv)
  have pos_new: "(\<lambda>k. go_dir (?d k) (n k)) = n(tk := Suc (n tk))"
    by (rule ext) simp
  let ?c'' = "Config\<^sub>M ?s' (ts(tk := (ts tk)(n tk := ?wb))) (n(tk := Suc (n tk)))"
  have "(Config\<^sub>M ?s ts n,
          Config\<^sub>M ?s' (\<lambda>k. (ts k)(n k := ?a' k))
            (\<lambda>k. go_dir (?d k) (n k)))
          \<in> mttm_step (alphabet_reduce_delta M)"
  proof (rule mttm_step.intros)
    show "(?s, ?a, ?s', ?a', ?d) \<in> alphabet_reduce_delta M" by (rule ard_in)
  qed
  hence step: "(c', ?c'') \<in> mttm_step (alphabet_reduce_delta M)"
    using c'_eq tape_new pos_new by simp
  show ?thesis
    using step by (intro exI[where x = ?c'']) (simp add: c'_eq)
qed

text \<open>The forward-write boundary substep, last tape: as
  \<open>ar_write_bit_boundary_step\<close> but \<open>tk\<close> is the last tape, so
  after the last-cell write the phase transitions to \<open>AR_SimAdvance\<close>
  (current-tape field reset to \<open>k_unidx 0\<close>).  Arm 6 (rightmost) of
  the union.\<close>

lemma ar_write_bit_finish_step:
  fixes M :: "('q, 'a) mttm"
    and c' :: "(sym4, 'q \<times> 'a ar_stage) mt_config"
  assumes vM: "valid_mttm M"
      and stg: "mt_state c' = (q, AR_SimWrite, tk, i, buf, dvec, posk)"
      and qQ: "q \<in> Q_tm M"
      and poskproper: "posk tk \<noteq> AR_AtLE"
      and notLE: "mt_tape c' tk (mt_pos c' tk) \<noteq> LE4"
      and last: "is_last_k M tk"
      and ihi: "Suc i = 2 * block_width (\<Gamma>_tm M)"
      and vsrc: "ar_valid_stage (\<Gamma>_tm M) (bl_tm M)
                   (AR_SimWrite, tk, i, buf, dvec, posk)"
      and pad_blank: "\<forall>j \<ge> k_tm M. mt_tape c' j (mt_pos c' j) = BLANK4"
      and src_bounded: "ar_stage_bounded (bl_tm M) (k_tm M)
                          (AR_SimWrite, tk, i, buf, dvec, posk)"
  shows "\<exists>c''. (c', c'') \<in> mttm_step (alphabet_reduce_delta M)
              \<and> mt_state c'' = (q, AR_SimAdvance, k_unidx 0, 0, buf, dvec, posk)
              \<and> mt_tape c'' = (mt_tape c')(tk :=
                    (mt_tape c' tk)(mt_pos c' tk :=
                       write_bit (\<Gamma>_tm M) (bl_tm M) (buf tk)
                                 (i - block_width (\<Gamma>_tm M))))
              \<and> mt_pos c'' = (mt_pos c')(tk := Suc (mt_pos c' tk))"
proof -
  obtain ts n where c'_eq:
      "c' = Config\<^sub>M (q, AR_SimWrite, tk, i, buf, dvec, posk) ts n"
    using stg by (cases c') auto
  let ?wb = "write_bit (\<Gamma>_tm M) (bl_tm M) (buf tk) (i - block_width (\<Gamma>_tm M))"
  let ?a = "\<lambda>k. ts k (n k)"
  let ?a' = "\<lambda>kk. if kk = tk then ?wb else ?a kk"
  let ?d = "\<lambda>kk. if kk = tk then dir.R else dir.N"
  let ?s = "(q, AR_SimWrite, tk, i, buf, dvec, posk)"
  let ?s' = "(q, AR_SimAdvance, k_unidx 0, 0, buf, dvec, posk)"
  have aTk: "?a tk \<noteq> LE4" using notLE c'_eq by simp
  have kpos: "0 < block_width (\<Gamma>_tm M)" using block_width_pos[of "\<Gamma>_tm M"] by simp
  have jlt: "i - block_width (\<Gamma>_tm M) < block_width (\<Gamma>_tm M)" using ihi kpos by linarith
  have wb_not_LE: "?wb \<noteq> LE4" using write_bit_not_LE4[OF jlt] .
  have rel_in: "(?s, ?a, ?s', ?a', ?d) \<in> ar_delta_write M"
    unfolding ar_delta_write_def
    by (rule UnI2) (use qQ poskproper last ihi in blast)
  have buf_valid: "\<forall>k. buf k \<in> \<Gamma>_tm M \<union> {bl_tm M}"
    using vsrc by (simp add: ar_valid_stage_def)
  have dst_valid: "ar_valid_stage (\<Gamma>_tm M) (bl_tm M) (snd ?s')"
    using kpos buf_valid by (simp add: ar_valid_stage_def)
  have pad_a: "\<forall>j \<ge> k_tm M. ?a j = BLANK4" using pad_blank c'_eq by simp
  have tk_lt: "tk < k_tm M" using src_bounded by (simp add: ar_stage_bounded_def)
  have kpos_tm: "0 < k_tm M" using vM by (cases M) auto
  have pad_read: "\<forall>j \<ge> k_tm M. ?a j = BLANK4 \<and> ?a' j = BLANK4 \<and> ?d j = dir.N"
  proof (intro allI impI)
    fix j assume jge: "k_tm M \<le> j"
    have jne: "j \<noteq> tk" using tk_lt jge by linarith
    show "?a j = BLANK4 \<and> ?a' j = BLANK4 \<and> ?d j = dir.N"
      using pad_a jge jne by simp
  qed
  have dst_bd: "ar_stage_bounded (bl_tm M) (k_tm M) (snd ?s')"
    using src_bounded kpos_tm by (simp add: ar_stage_bounded_def k_unidx_def)
  have ard_in: "(?s, ?a, ?s', ?a', ?d) \<in> alphabet_reduce_delta M"
    unfolding alphabet_reduce_delta_def
    using rel_in vsrc dst_valid aTk wb_not_LE pad_read src_bounded dst_bd
    by (auto split: if_splits)
  have tape_new: "(\<lambda>k. (ts k)(n k := ?a' k))
                    = ts(tk := (ts tk)(n tk := ?wb))"
    by (rule ext) (auto simp: fun_upd_triv)
  have pos_new: "(\<lambda>k. go_dir (?d k) (n k)) = n(tk := Suc (n tk))"
    by (rule ext) simp
  let ?c'' = "Config\<^sub>M ?s' (ts(tk := (ts tk)(n tk := ?wb))) (n(tk := Suc (n tk)))"
  have "(Config\<^sub>M ?s ts n,
          Config\<^sub>M ?s' (\<lambda>k. (ts k)(n k := ?a' k))
            (\<lambda>k. go_dir (?d k) (n k)))
          \<in> mttm_step (alphabet_reduce_delta M)"
  proof (rule mttm_step.intros)
    show "(?s, ?a, ?s', ?a', ?d) \<in> alphabet_reduce_delta M" by (rule ard_in)
  qed
  hence step: "(c', ?c'') \<in> mttm_step (alphabet_reduce_delta M)"
    using c'_eq tape_new pos_new by simp
  show ?thesis
    using step by (intro exI[where x = ?c'']) (simp add: c'_eq)
qed

text \<open>The read LE substep, non-last tape: at position \<open>0\<close> the
  head reads \<open>LE4\<close>, sets \<open>buf tk := le_tm M\<close> directly (the
  single LE-cell needs no accumulator), moves \<open>R\<close> on \<open>tk\<close>
  to position \<open>1\<close>, and hands off to the next tape's read.  Tape
  unchanged.  Target-stage validity uses \<open>valid_mttm_LE_in_Gamma\<close>
  for the \<open>buf tk := le_tm M\<close> entry.\<close>

lemma ar_read_le_step:
  fixes M :: "('q, 'a) mttm"
    and c' :: "(sym4, 'q \<times> 'a ar_stage) mt_config"
  assumes vM: "valid_mttm M"
      and stg: "mt_state c' = (q, AR_SimRead, tk, 0, buf, dvec, posk)"
      and qQ: "q \<in> Q_tm M"
      and notlast: "\<not> is_last_k M tk"
      and posk_le: "posk tk = AR_AtLE"
      and aLE: "mt_tape c' tk (mt_pos c' tk) = LE4"
      and vsrc: "ar_valid_stage (\<Gamma>_tm M) (bl_tm M)
                   (AR_SimRead, tk, 0, buf, dvec, posk)"
      and pad_blank: "\<forall>j \<ge> k_tm M. mt_tape c' j (mt_pos c' j) = BLANK4"
      and src_bounded: "ar_stage_bounded (bl_tm M) (k_tm M)
                          (AR_SimRead, tk, 0, buf, dvec, posk)"
  shows "\<exists>c''. (c', c'') \<in> mttm_step (alphabet_reduce_delta M)
              \<and> mt_state c'' = (q, AR_SimRead, k_succ tk, 0,
                                  buf(tk := le_tm M), dvec, posk)
              \<and> mt_tape c'' = mt_tape c'
              \<and> mt_pos c'' = (mt_pos c')(tk := Suc (mt_pos c' tk))"
proof -
  obtain ts n where c'_eq:
      "c' = Config\<^sub>M (q, AR_SimRead, tk, 0, buf, dvec, posk) ts n"
    using stg by (cases c') auto
  let ?a = "\<lambda>k. ts k (n k)"
  let ?d = "\<lambda>kk. if kk = tk then dir.R else dir.N"
  let ?s = "(q, AR_SimRead, tk, 0, buf, dvec, posk)"
  let ?s' = "(q, AR_SimRead, k_succ tk, 0, buf(tk := le_tm M), dvec, posk)"
  have aTk: "?a tk = LE4" using aLE c'_eq by simp
  have rel_in: "(?s, ?a, ?s', ?a, ?d) \<in> ar_delta_read M"
    unfolding ar_delta_read_def
    using qQ notlast posk_le aTk by (intro UnI1) blast
  have buf_valid: "\<forall>k. buf k \<in> \<Gamma>_tm M \<union> {bl_tm M}"
    using vsrc by (simp add: ar_valid_stage_def)
  have kpos: "0 < block_width (\<Gamma>_tm M)" using block_width_pos[of "\<Gamma>_tm M"] by simp
  have dst_valid: "ar_valid_stage (\<Gamma>_tm M) (bl_tm M) (snd ?s')"
    using buf_valid valid_mttm_LE_in_Gamma[OF vM] kpos
    by (auto simp: ar_valid_stage_def)
  have pad_a: "\<forall>j \<ge> k_tm M. ?a j = BLANK4" using pad_blank c'_eq by simp
  have tk_lt: "tk < k_tm M" using src_bounded by (simp add: ar_stage_bounded_def)
  have ksucc_lt: "k_succ tk < k_tm M"
  proof -
    have ne: "Suc tk \<noteq> k_tm M" using notlast by (simp add: is_last_k_def)
    have le: "Suc tk \<le> k_tm M" using tk_lt by simp
    show ?thesis unfolding k_succ_def using le_neq_implies_less[OF le ne] .
  qed
  have pad_read: "\<forall>j \<ge> k_tm M. ?a j = BLANK4 \<and> ?a j = BLANK4 \<and> ?d j = dir.N"
  proof (intro allI impI)
    fix j assume jge: "k_tm M \<le> j"
    have jne: "j \<noteq> tk" using tk_lt jge by linarith
    show "?a j = BLANK4 \<and> ?a j = BLANK4 \<and> ?d j = dir.N"
      using pad_a jge jne by simp
  qed
  have dst_bd: "ar_stage_bounded (bl_tm M) (k_tm M) (snd ?s')"
  proof -
    have bt: "\<forall>j\<ge>k_tm M. (buf(tk := le_tm M)) j = bl_tm M"
    proof (intro allI impI)
      fix j assume jge: "k_tm M \<le> j"
      have "j \<noteq> tk" using tk_lt jge by linarith
      thus "(buf(tk := le_tm M)) j = bl_tm M"
        using src_bounded jge by (simp add: ar_stage_bounded_def)
    qed
    show ?thesis using src_bounded ksucc_lt bt by (simp add: ar_stage_bounded_def)
  qed
  have ard_in: "(?s, ?a, ?s', ?a, ?d) \<in> alphabet_reduce_delta M"
    unfolding alphabet_reduce_delta_def
    using rel_in vsrc dst_valid pad_read src_bounded dst_bd
    by (auto split: if_splits)
  have ts_unchanged: "(\<lambda>k. (ts k)(n k := ?a k)) = ts" by (rule ext) auto
  have pos_new: "(\<lambda>k. go_dir (?d k) (n k)) = n(tk := Suc (n tk))"
    by (rule ext) simp
  let ?c'' = "Config\<^sub>M ?s' ts (n(tk := Suc (n tk)))"
  have "(Config\<^sub>M ?s ts n,
          Config\<^sub>M ?s' (\<lambda>k. (ts k)(n k := ?a k))
            (\<lambda>k. go_dir (?d k) (n k)))
          \<in> mttm_step (alphabet_reduce_delta M)"
  proof (rule mttm_step.intros)
    show "(?s, ?a, ?s', ?a, ?d) \<in> alphabet_reduce_delta M" by (rule ard_in)
  qed
  hence step: "(c', ?c'') \<in> mttm_step (alphabet_reduce_delta M)"
    using c'_eq ts_unchanged pos_new by simp
  show ?thesis
    using step by (intro exI[where x = ?c'']) (simp add: c'_eq)
qed

text \<open>The read LE substep, last tape: as \<open>ar_read_le_step\<close> but
  \<open>tk\<close> is the last tape, so the hand-off goes to
  \<open>AR_SimCompute\<close> (current-tape field reset to \<open>k_unidx 0\<close>),
  beginning the compute substep.  Arm 2 of the seven-arm
  \<open>ar_delta_read\<close> union.\<close>

lemma ar_read_le_finish_step:
  fixes M :: "('q, 'a) mttm"
    and c' :: "(sym4, 'q \<times> 'a ar_stage) mt_config"
  assumes vM: "valid_mttm M"
      and stg: "mt_state c' = (q, AR_SimRead, tk, 0, buf, dvec, posk)"
      and qQ: "q \<in> Q_tm M"
      and last: "is_last_k M tk"
      and posk_le: "posk tk = AR_AtLE"
      and aLE: "mt_tape c' tk (mt_pos c' tk) = LE4"
      and vsrc: "ar_valid_stage (\<Gamma>_tm M) (bl_tm M)
                   (AR_SimRead, tk, 0, buf, dvec, posk)"
      and pad_blank: "\<forall>j \<ge> k_tm M. mt_tape c' j (mt_pos c' j) = BLANK4"
      and src_bounded: "ar_stage_bounded (bl_tm M) (k_tm M)
                          (AR_SimRead, tk, 0, buf, dvec, posk)"
  shows "\<exists>c''. (c', c'') \<in> mttm_step (alphabet_reduce_delta M)
              \<and> mt_state c'' = (q, AR_SimCompute, k_unidx 0, 0,
                                  buf(tk := le_tm M), dvec, posk)
              \<and> mt_tape c'' = mt_tape c'
              \<and> mt_pos c'' = (mt_pos c')(tk := Suc (mt_pos c' tk))"
proof -
  obtain ts n where c'_eq:
      "c' = Config\<^sub>M (q, AR_SimRead, tk, 0, buf, dvec, posk) ts n"
    using stg by (cases c') auto
  let ?a = "\<lambda>k. ts k (n k)"
  let ?d = "\<lambda>kk. if kk = tk then dir.R else dir.N"
  let ?s = "(q, AR_SimRead, tk, 0, buf, dvec, posk)"
  let ?s' = "(q, AR_SimCompute, k_unidx 0, 0, buf(tk := le_tm M), dvec, posk)"
  have aTk: "?a tk = LE4" using aLE c'_eq by simp
  have rel_in: "(?s, ?a, ?s', ?a, ?d) \<in> ar_delta_read M"
    unfolding ar_delta_read_def
    by (rule UnI1, rule UnI1, rule UnI1, rule UnI1, rule UnI1, rule UnI2)
       (use qQ last posk_le aTk in blast)
  have buf_valid: "\<forall>k. buf k \<in> \<Gamma>_tm M \<union> {bl_tm M}"
    using vsrc by (simp add: ar_valid_stage_def)
  have kpos: "0 < block_width (\<Gamma>_tm M)" using block_width_pos[of "\<Gamma>_tm M"] by simp
  have dst_valid: "ar_valid_stage (\<Gamma>_tm M) (bl_tm M) (snd ?s')"
    using buf_valid valid_mttm_LE_in_Gamma[OF vM] kpos
    by (auto simp: ar_valid_stage_def)
  have pad_a: "\<forall>j \<ge> k_tm M. ?a j = BLANK4" using pad_blank c'_eq by simp
  have tk_lt: "tk < k_tm M" using src_bounded by (simp add: ar_stage_bounded_def)
  have kpos_tm: "0 < k_tm M" using vM by (cases M) auto
  have pad_read: "\<forall>j \<ge> k_tm M. ?a j = BLANK4 \<and> ?a j = BLANK4 \<and> ?d j = dir.N"
  proof (intro allI impI)
    fix j assume jge: "k_tm M \<le> j"
    have jne: "j \<noteq> tk" using tk_lt jge by linarith
    show "?a j = BLANK4 \<and> ?a j = BLANK4 \<and> ?d j = dir.N"
      using pad_a jge jne by simp
  qed
  have dst_bd: "ar_stage_bounded (bl_tm M) (k_tm M) (snd ?s')"
  proof -
    have bt: "\<forall>j\<ge>k_tm M. (buf(tk := le_tm M)) j = bl_tm M"
    proof (intro allI impI)
      fix j assume jge: "k_tm M \<le> j"
      have "j \<noteq> tk" using tk_lt jge by linarith
      thus "(buf(tk := le_tm M)) j = bl_tm M"
        using src_bounded jge by (simp add: ar_stage_bounded_def)
    qed
    show ?thesis using src_bounded kpos_tm bt
      by (simp add: ar_stage_bounded_def k_unidx_def)
  qed
  have ard_in: "(?s, ?a, ?s', ?a, ?d) \<in> alphabet_reduce_delta M"
    unfolding alphabet_reduce_delta_def
    using rel_in vsrc dst_valid pad_read src_bounded dst_bd
    by (auto split: if_splits)
  have ts_unchanged: "(\<lambda>k. (ts k)(n k := ?a k)) = ts" by (rule ext) auto
  have pos_new: "(\<lambda>k. go_dir (?d k) (n k)) = n(tk := Suc (n tk))"
    by (rule ext) simp
  let ?c'' = "Config\<^sub>M ?s' ts (n(tk := Suc (n tk)))"
  have "(Config\<^sub>M ?s ts n,
          Config\<^sub>M ?s' (\<lambda>k. (ts k)(n k := ?a k))
            (\<lambda>k. go_dir (?d k) (n k)))
          \<in> mttm_step (alphabet_reduce_delta M)"
  proof (rule mttm_step.intros)
    show "(?s, ?a, ?s', ?a, ?d) \<in> alphabet_reduce_delta M" by (rule ard_in)
  qed
  hence step: "(c', ?c'') \<in> mttm_step (alphabet_reduce_delta M)"
    using c'_eq ts_unchanged pos_new by simp
  show ?thesis
    using step by (intro exI[where x = ?c'']) (simp add: c'_eq)
qed

text \<open>The decoder image always lies in \<open>\<Gamma> \<union> {bl}\<close>: for
  \<open>n < card \<Gamma>\<close> it is \<open>inv_into \<Gamma> (gamma_enum \<Gamma> bl) n\<close>,
  which is in \<open>\<Gamma>\<close> since \<open>gamma_enum\<close> is onto
  \<open>{..< card \<Gamma>}\<close> (bijection); the out-of-range fallback is
  \<open>bl\<close>.  Totality here means the read arms' \<open>buf\<close>-update
  validity holds for any accumulator value without per-arm range
  reasoning.\<close>

lemma gamma_unenum_mem:
  assumes "finite \<Gamma>"
  shows "gamma_unenum \<Gamma> bl n \<in> \<Gamma> \<union> {bl}"
proof (cases "n < card \<Gamma>")
  case True
  have "n \<in> gamma_enum \<Gamma> bl ` \<Gamma>"
    using True gamma_enum_bij[OF assms] by (auto simp: bij_betw_def)
  hence "inv_into \<Gamma> (gamma_enum \<Gamma> bl) n \<in> \<Gamma>" by (rule inv_into_into)
  thus ?thesis using True by (simp add: gamma_unenum_def)
next
  case False
  thus ?thesis by (simp add: gamma_unenum_def)
qed

text \<open>The read proper-arm look-back step 1 (\<open>i = 0\<close>): with the
  position-kind already in the proper region, the head moves \<open>L\<close>
  from \<open>sim_pos(p)\<close> to \<open>sim_pos(p) - 1\<close> (the cell to
  inspect for refining the position-kind), no buf change, transitioning
  to \<open>i = 1\<close>.  Tape unchanged; \<open>a tk \<noteq> LE4\<close> selects the
  arm and discharges the backward-\<open>\<delta>LE\<close> filter.  Arm 3 of the
  seven-arm union.\<close>

lemma ar_read_lookback1_step:
  fixes M :: "('q, 'a) mttm"
    and c' :: "(sym4, 'q \<times> 'a ar_stage) mt_config"
  assumes vM: "valid_mttm M"
      and stg: "mt_state c' = (q, AR_SimRead, tk, 0, buf, dvec, posk)"
      and qQ: "q \<in> Q_tm M"
      and posk_proper: "posk tk \<in> {AR_AtFirstProper, AR_AtFurtherProper}"
      and notLE: "mt_tape c' tk (mt_pos c' tk) \<noteq> LE4"
      and vsrc: "ar_valid_stage (\<Gamma>_tm M) (bl_tm M)
                   (AR_SimRead, tk, 0, buf, dvec, posk)"
      and pad_blank: "\<forall>j \<ge> k_tm M. mt_tape c' j (mt_pos c' j) = BLANK4"
      and src_bounded: "ar_stage_bounded (bl_tm M) (k_tm M)
                          (AR_SimRead, tk, 0, buf, dvec, posk)"
  shows "\<exists>c''. (c', c'') \<in> mttm_step (alphabet_reduce_delta M)
              \<and> mt_state c'' = (q, AR_SimRead, tk, Suc 0, buf, dvec, posk)
              \<and> mt_tape c'' = mt_tape c'
              \<and> mt_pos c'' = (mt_pos c')(tk := mt_pos c' tk - 1)"
proof -
  obtain ts n where c'_eq:
      "c' = Config\<^sub>M (q, AR_SimRead, tk, 0, buf, dvec, posk) ts n"
    using stg by (cases c') auto
  let ?a = "\<lambda>k. ts k (n k)"
  let ?d = "\<lambda>kk. if kk = tk then dir.L else dir.N"
  let ?s = "(q, AR_SimRead, tk, 0, buf, dvec, posk)"
  let ?s' = "(q, AR_SimRead, tk, Suc 0, buf, dvec, posk)"
  have aTk: "?a tk \<noteq> LE4" using notLE c'_eq by simp
  have rel_in: "(?s, ?a, ?s', ?a, ?d) \<in> ar_delta_read M"
    unfolding ar_delta_read_def
    by (rule UnI1, rule UnI1, rule UnI1, rule UnI1, rule UnI2)
       (use qQ posk_proper aTk in blast)
  have buf_valid: "\<forall>k. buf k \<in> \<Gamma>_tm M \<union> {bl_tm M}"
    using vsrc by (simp add: ar_valid_stage_def)
  have kpos: "0 < block_width (\<Gamma>_tm M)" using block_width_pos[of "\<Gamma>_tm M"] by simp
  have dst_valid: "ar_valid_stage (\<Gamma>_tm M) (bl_tm M) (snd ?s')"
    using kpos buf_valid by (simp add: ar_valid_stage_def)
  have pad_a: "\<forall>j \<ge> k_tm M. ?a j = BLANK4" using pad_blank c'_eq by simp
  have tk_lt: "tk < k_tm M" using src_bounded by (simp add: ar_stage_bounded_def)
  have pad_read: "\<forall>j \<ge> k_tm M. ?a j = BLANK4 \<and> ?a j = BLANK4 \<and> ?d j = dir.N"
  proof (intro allI impI)
    fix j assume jge: "k_tm M \<le> j"
    have jne: "j \<noteq> tk" using tk_lt jge by linarith
    show "?a j = BLANK4 \<and> ?a j = BLANK4 \<and> ?d j = dir.N"
      using pad_a jge jne by simp
  qed
  have dst_bd: "ar_stage_bounded (bl_tm M) (k_tm M) (snd ?s')"
    using src_bounded by (simp add: ar_stage_bounded_def)
  have ard_in: "(?s, ?a, ?s', ?a, ?d) \<in> alphabet_reduce_delta M"
    unfolding alphabet_reduce_delta_def
    using rel_in vsrc dst_valid aTk pad_read src_bounded dst_bd
    by (auto split: if_splits)
  have ts_unchanged: "(\<lambda>k. (ts k)(n k := ?a k)) = ts" by (rule ext) auto
  have pos_new: "(\<lambda>k. go_dir (?d k) (n k)) = n(tk := n tk - 1)"
    by (rule ext) simp
  let ?c'' = "Config\<^sub>M ?s' ts (n(tk := n tk - 1))"
  have "(Config\<^sub>M ?s ts n,
          Config\<^sub>M ?s' (\<lambda>k. (ts k)(n k := ?a k))
            (\<lambda>k. go_dir (?d k) (n k)))
          \<in> mttm_step (alphabet_reduce_delta M)"
  proof (rule mttm_step.intros)
    show "(?s, ?a, ?s', ?a, ?d) \<in> alphabet_reduce_delta M" by (rule ard_in)
  qed
  hence step: "(c', ?c'') \<in> mttm_step (alphabet_reduce_delta M)"
    using c'_eq ts_unchanged pos_new by simp
  show ?thesis
    using step by (intro exI[where x = ?c'']) (simp add: c'_eq)
qed

text \<open>The read proper-arm look-back step 2 (\<open>i = 1\<close>): at
  \<open>sim_pos(p) - 1\<close> the head reads the cell, refines the
  position-kind (\<open>AR_AtFirstProper\<close> if that cell is \<open>LE4\<close>,
  i.e. the head was at \<open>sim_pos 1\<close>, else \<open>AR_AtFurtherProper\<close>),
  resets \<open>buf tk\<close> to the zero-bits partial decode, and moves
  \<open>R\<close> back to \<open>sim_pos(p)\<close>, transitioning to \<open>i = 2\<close>.
  The \<open>R\<close>-move makes \<open>\<delta>LE\<close> trivial even when reading
  \<open>LE4\<close>.  Needs \<open>2 \<le> b\<close> for target validity
  (\<open>i = 2\<close>).  Arm 4 of the union.\<close>

lemma ar_read_lookback2_step:
  fixes M :: "('q, 'a) mttm"
    and c' :: "(sym4, 'q \<times> 'a ar_stage) mt_config"
  assumes vM: "valid_mttm M"
      and stg: "mt_state c' = (q, AR_SimRead, tk, Suc 0, buf, dvec, posk)"
      and qQ: "q \<in> Q_tm M"
      and posk_proper: "posk tk \<in> {AR_AtFirstProper, AR_AtFurtherProper}"
      and kge2: "2 \<le> block_width (\<Gamma>_tm M)"
      and vsrc: "ar_valid_stage (\<Gamma>_tm M) (bl_tm M)
                   (AR_SimRead, tk, Suc 0, buf, dvec, posk)"
      and pad_blank: "\<forall>j \<ge> k_tm M. mt_tape c' j (mt_pos c' j) = BLANK4"
      and src_bounded: "ar_stage_bounded (bl_tm M) (k_tm M)
                          (AR_SimRead, tk, Suc 0, buf, dvec, posk)"
  shows "\<exists>c''. (c', c'') \<in> mttm_step (alphabet_reduce_delta M)
              \<and> mt_state c'' = (q, AR_SimRead, tk, Suc (Suc 0),
                    buf(tk := gamma_unenum (\<Gamma>_tm M) (bl_tm M) 0), dvec,
                    posk(tk := if mt_tape c' tk (mt_pos c' tk) = LE4
                               then AR_AtFirstProper else AR_AtFurtherProper))
              \<and> mt_tape c'' = mt_tape c'
              \<and> mt_pos c'' = (mt_pos c')(tk := Suc (mt_pos c' tk))"
proof -
  obtain ts n where c'_eq:
      "c' = Config\<^sub>M (q, AR_SimRead, tk, Suc 0, buf, dvec, posk) ts n"
    using stg by (cases c') auto
  let ?a = "\<lambda>k. ts k (n k)"
  let ?d = "\<lambda>kk. if kk = tk then dir.R else dir.N"
  let ?s = "(q, AR_SimRead, tk, Suc 0, buf, dvec, posk)"
  let ?s' = "(q, AR_SimRead, tk, Suc (Suc 0),
              buf(tk := gamma_unenum (\<Gamma>_tm M) (bl_tm M) 0), dvec,
              posk(tk := if ?a tk = LE4
                         then AR_AtFirstProper else AR_AtFurtherProper))"
  have rel_in: "(?s, ?a, ?s', ?a, ?d) \<in> ar_delta_read M"
    unfolding ar_delta_read_def
    by (rule UnI1, rule UnI1, rule UnI1, rule UnI2)
       (use qQ posk_proper in blast)
  have buf_valid: "\<forall>k. buf k \<in> \<Gamma>_tm M \<union> {bl_tm M}"
    using vsrc by (simp add: ar_valid_stage_def)
  have gu_mem: "gamma_unenum (\<Gamma>_tm M) (bl_tm M) 0 \<in> \<Gamma>_tm M \<union> {bl_tm M}"
    using gamma_unenum_mem[OF valid_mttm_finite_Gamma[OF vM]] .
  have dst_valid: "ar_valid_stage (\<Gamma>_tm M) (bl_tm M) (snd ?s')"
    using kge2 buf_valid gu_mem by (auto simp: ar_valid_stage_def)
  have pad_a: "\<forall>j \<ge> k_tm M. ?a j = BLANK4" using pad_blank c'_eq by simp
  have tk_lt: "tk < k_tm M" using src_bounded by (simp add: ar_stage_bounded_def)
  have pad_read: "\<forall>j \<ge> k_tm M. ?a j = BLANK4 \<and> ?a j = BLANK4 \<and> ?d j = dir.N"
  proof (intro allI impI)
    fix j assume jge: "k_tm M \<le> j"
    have jne: "j \<noteq> tk" using tk_lt jge by linarith
    show "?a j = BLANK4 \<and> ?a j = BLANK4 \<and> ?d j = dir.N"
      using pad_a jge jne by simp
  qed
  have dst_bd: "ar_stage_bounded (bl_tm M) (k_tm M) (snd ?s')"
  proof -
    have bt: "\<forall>j\<ge>k_tm M.
                (buf(tk := gamma_unenum (\<Gamma>_tm M) (bl_tm M) 0)) j = bl_tm M"
    proof (intro allI impI)
      fix j assume jge: "k_tm M \<le> j"
      have "j \<noteq> tk" using tk_lt jge by linarith
      thus "(buf(tk := gamma_unenum (\<Gamma>_tm M) (bl_tm M) 0)) j = bl_tm M"
        using src_bounded jge by (simp add: ar_stage_bounded_def)
    qed
    have pt: "\<forall>j\<ge>k_tm M. (posk(tk := if ?a tk = LE4
                  then AR_AtFirstProper else AR_AtFurtherProper)) j = AR_AtLE"
    proof (intro allI impI)
      fix j assume jge: "k_tm M \<le> j"
      have "j \<noteq> tk" using tk_lt jge by linarith
      thus "(posk(tk := if ?a tk = LE4
               then AR_AtFirstProper else AR_AtFurtherProper)) j = AR_AtLE"
        using src_bounded jge by (simp add: ar_stage_bounded_def)
    qed
    show ?thesis using src_bounded tk_lt bt pt
      by (simp add: ar_stage_bounded_def)
  qed
  have ard_in: "(?s, ?a, ?s', ?a, ?d) \<in> alphabet_reduce_delta M"
    unfolding alphabet_reduce_delta_def
    using rel_in vsrc dst_valid pad_read src_bounded dst_bd
    by (auto split: if_splits)
  have ts_unchanged: "(\<lambda>k. (ts k)(n k := ?a k)) = ts" by (rule ext) auto
  have pos_new: "(\<lambda>k. go_dir (?d k) (n k)) = n(tk := Suc (n tk))"
    by (rule ext) simp
  let ?c'' = "Config\<^sub>M ?s' ts (n(tk := Suc (n tk)))"
  have "(Config\<^sub>M ?s ts n,
          Config\<^sub>M ?s' (\<lambda>k. (ts k)(n k := ?a k))
            (\<lambda>k. go_dir (?d k) (n k)))
          \<in> mttm_step (alphabet_reduce_delta M)"
  proof (rule mttm_step.intros)
    show "(?s, ?a, ?s', ?a, ?d) \<in> alphabet_reduce_delta M" by (rule ard_in)
  qed
  hence step: "(c', ?c'') \<in> mttm_step (alphabet_reduce_delta M)"
    using c'_eq ts_unchanged pos_new by simp
  show ?thesis
    using step by (intro exI[where x = ?c'']) (simp add: c'_eq)
qed

text \<open>The read proper-arm per-bit stepping substep
  (\<open>2 \<le> i\<close>, \<open>Suc i \<le> Suc b\<close>): at
  \<open>sim_pos(p) + (i-2)\<close> the head reads a bit cell and folds it
  into the partial decode via the \<open>gamma_enum\<close>/\<open>gamma_unenum\<close>
  roundtrip \<open>partial' = 2 \<cdot> gamma_enum (buf tk) + bit_value (a tk)\<close>,
  moves \<open>R\<close>, and continues to \<open>i + 1\<close>.  Tape unchanged.  Needs
  \<open>2 \<le> b\<close> for target validity at the upper end
  (\<open>Suc i = Suc b\<close>).  Arm 5 of the union.\<close>

lemma ar_read_bit_step:
  fixes M :: "('q, 'a) mttm"
    and c' :: "(sym4, 'q \<times> 'a ar_stage) mt_config"
  assumes vM: "valid_mttm M"
      and stg: "mt_state c' = (q, AR_SimRead, tk, i, buf, dvec, posk)"
      and qQ: "q \<in> Q_tm M"
      and posk_proper: "posk tk \<in> {AR_AtFirstProper, AR_AtFurtherProper}"
      and ilo: "2 \<le> i"
      and ihi: "Suc i \<le> Suc (block_width (\<Gamma>_tm M))"
      and kge2: "2 \<le> block_width (\<Gamma>_tm M)"
      and vsrc: "ar_valid_stage (\<Gamma>_tm M) (bl_tm M)
                   (AR_SimRead, tk, i, buf, dvec, posk)"
      and pad_blank: "\<forall>j \<ge> k_tm M. mt_tape c' j (mt_pos c' j) = BLANK4"
      and src_bounded: "ar_stage_bounded (bl_tm M) (k_tm M)
                          (AR_SimRead, tk, i, buf, dvec, posk)"
  shows "\<exists>c''. (c', c'') \<in> mttm_step (alphabet_reduce_delta M)
              \<and> mt_state c'' = (q, AR_SimRead, tk, Suc i,
                    buf(tk := gamma_unenum (\<Gamma>_tm M) (bl_tm M)
                          (2 * gamma_enum (\<Gamma>_tm M) (bl_tm M) (buf tk)
                             + bit_value (mt_tape c' tk (mt_pos c' tk)))),
                    dvec, posk)
              \<and> mt_tape c'' = mt_tape c'
              \<and> mt_pos c'' = (mt_pos c')(tk := Suc (mt_pos c' tk))"
proof -
  obtain ts n where c'_eq:
      "c' = Config\<^sub>M (q, AR_SimRead, tk, i, buf, dvec, posk) ts n"
    using stg by (cases c') auto
  let ?a = "\<lambda>k. ts k (n k)"
  let ?d = "\<lambda>kk. if kk = tk then dir.R else dir.N"
  let ?s = "(q, AR_SimRead, tk, i, buf, dvec, posk)"
  let ?s' = "(q, AR_SimRead, tk, Suc i,
              buf(tk := gamma_unenum (\<Gamma>_tm M) (bl_tm M)
                    (2 * gamma_enum (\<Gamma>_tm M) (bl_tm M) (buf tk) + bit_value (?a tk))),
              dvec, posk)"
  have rel_in: "(?s, ?a, ?s', ?a, ?d) \<in> ar_delta_read M"
    unfolding ar_delta_read_def
    by (rule UnI1, rule UnI1, rule UnI2)
       (use qQ posk_proper ilo ihi in blast)
  have buf_valid: "\<forall>k. buf k \<in> \<Gamma>_tm M \<union> {bl_tm M}"
    using vsrc by (simp add: ar_valid_stage_def)
  have gu_mem: "gamma_unenum (\<Gamma>_tm M) (bl_tm M)
                  (2 * gamma_enum (\<Gamma>_tm M) (bl_tm M) (buf tk) + bit_value (?a tk))
                  \<in> \<Gamma>_tm M \<union> {bl_tm M}"
    using gamma_unenum_mem[OF valid_mttm_finite_Gamma[OF vM]] .
  have suc_i_lt: "Suc i < 2 * block_width (\<Gamma>_tm M)"
    using ihi kge2 by linarith
  have dst_valid: "ar_valid_stage (\<Gamma>_tm M) (bl_tm M) (snd ?s')"
    using suc_i_lt buf_valid gu_mem by (auto simp: ar_valid_stage_def)
  have pad_a: "\<forall>j \<ge> k_tm M. ?a j = BLANK4" using pad_blank c'_eq by simp
  have tk_lt: "tk < k_tm M" using src_bounded by (simp add: ar_stage_bounded_def)
  have pad_read: "\<forall>j \<ge> k_tm M. ?a j = BLANK4 \<and> ?a j = BLANK4 \<and> ?d j = dir.N"
  proof (intro allI impI)
    fix j assume jge: "k_tm M \<le> j"
    have jne: "j \<noteq> tk" using tk_lt jge by linarith
    show "?a j = BLANK4 \<and> ?a j = BLANK4 \<and> ?d j = dir.N"
      using pad_a jge jne by simp
  qed
  have dst_bd: "ar_stage_bounded (bl_tm M) (k_tm M) (snd ?s')"
  proof -
    have bt: "\<forall>j\<ge>k_tm M.
       (buf(tk := gamma_unenum (\<Gamma>_tm M) (bl_tm M)
              (2 * gamma_enum (\<Gamma>_tm M) (bl_tm M) (buf tk)
                 + bit_value (?a tk)))) j = bl_tm M"
    proof (intro allI impI)
      fix j assume jge: "k_tm M \<le> j"
      have "j \<noteq> tk" using tk_lt jge by linarith
      thus "(buf(tk := gamma_unenum (\<Gamma>_tm M) (bl_tm M)
                (2 * gamma_enum (\<Gamma>_tm M) (bl_tm M) (buf tk)
                   + bit_value (?a tk)))) j = bl_tm M"
        using src_bounded jge by (simp add: ar_stage_bounded_def)
    qed
    show ?thesis using src_bounded tk_lt bt by (simp add: ar_stage_bounded_def)
  qed
  have ard_in: "(?s, ?a, ?s', ?a, ?d) \<in> alphabet_reduce_delta M"
    unfolding alphabet_reduce_delta_def
    using rel_in vsrc dst_valid pad_read src_bounded dst_bd
    by (auto split: if_splits)
  have ts_unchanged: "(\<lambda>k. (ts k)(n k := ?a k)) = ts" by (rule ext) auto
  have pos_new: "(\<lambda>k. go_dir (?d k) (n k)) = n(tk := Suc (n tk))"
    by (rule ext) simp
  let ?c'' = "Config\<^sub>M ?s' ts (n(tk := Suc (n tk)))"
  have "(Config\<^sub>M ?s ts n,
          Config\<^sub>M ?s' (\<lambda>k. (ts k)(n k := ?a k))
            (\<lambda>k. go_dir (?d k) (n k)))
          \<in> mttm_step (alphabet_reduce_delta M)"
  proof (rule mttm_step.intros)
    show "(?s, ?a, ?s', ?a, ?d) \<in> alphabet_reduce_delta M" by (rule ard_in)
  qed
  hence step: "(c', ?c'') \<in> mttm_step (alphabet_reduce_delta M)"
    using c'_eq ts_unchanged pos_new by simp
  show ?thesis
    using step by (intro exI[where x = ?c'']) (simp add: c'_eq)
qed

text \<open>The read proper-arm per-bit boundary substep
  (\<open>i = Suc b\<close>), non-last tape: the last-bit accumulator step (as
  \<open>ar_read_bit_step\<close>) leaving \<open>buf tk\<close> the fully-decoded
  \<open>M\<close>-symbol, then \<open>R\<close>-move and hand-off to the next tape
  \<open>k_succ tk\<close> with the bit-counter reset.  Arm 6 of the union.\<close>

lemma ar_read_bit_boundary_step:
  fixes M :: "('q, 'a) mttm"
    and c' :: "(sym4, 'q \<times> 'a ar_stage) mt_config"
  assumes vM: "valid_mttm M"
      and stg: "mt_state c' = (q, AR_SimRead, tk, i, buf, dvec, posk)"
      and qQ: "q \<in> Q_tm M"
      and notlast: "\<not> is_last_k M tk"
      and posk_proper: "posk tk \<in> {AR_AtFirstProper, AR_AtFurtherProper}"
      and ieq: "i = Suc (block_width (\<Gamma>_tm M))"
      and vsrc: "ar_valid_stage (\<Gamma>_tm M) (bl_tm M)
                   (AR_SimRead, tk, i, buf, dvec, posk)"
      and pad_blank: "\<forall>j \<ge> k_tm M. mt_tape c' j (mt_pos c' j) = BLANK4"
      and src_bounded: "ar_stage_bounded (bl_tm M) (k_tm M)
                          (AR_SimRead, tk, i, buf, dvec, posk)"
  shows "\<exists>c''. (c', c'') \<in> mttm_step (alphabet_reduce_delta M)
              \<and> mt_state c'' = (q, AR_SimRead, k_succ tk, 0,
                    buf(tk := gamma_unenum (\<Gamma>_tm M) (bl_tm M)
                          (2 * gamma_enum (\<Gamma>_tm M) (bl_tm M) (buf tk)
                             + bit_value (mt_tape c' tk (mt_pos c' tk)))),
                    dvec, posk)
              \<and> mt_tape c'' = mt_tape c'
              \<and> mt_pos c'' = (mt_pos c')(tk := Suc (mt_pos c' tk))"
proof -
  obtain ts n where c'_eq:
      "c' = Config\<^sub>M (q, AR_SimRead, tk, i, buf, dvec, posk) ts n"
    using stg by (cases c') auto
  let ?a = "\<lambda>k. ts k (n k)"
  let ?d = "\<lambda>kk. if kk = tk then dir.R else dir.N"
  let ?s = "(q, AR_SimRead, tk, i, buf, dvec, posk)"
  let ?s' = "(q, AR_SimRead, k_succ tk, 0,
              buf(tk := gamma_unenum (\<Gamma>_tm M) (bl_tm M)
                    (2 * gamma_enum (\<Gamma>_tm M) (bl_tm M) (buf tk) + bit_value (?a tk))),
              dvec, posk)"
  have rel_in: "(?s, ?a, ?s', ?a, ?d) \<in> ar_delta_read M"
    unfolding ar_delta_read_def
    by (rule UnI1, rule UnI2) (use qQ notlast posk_proper ieq in blast)
  have buf_valid: "\<forall>k. buf k \<in> \<Gamma>_tm M \<union> {bl_tm M}"
    using vsrc by (simp add: ar_valid_stage_def)
  have gu_mem: "gamma_unenum (\<Gamma>_tm M) (bl_tm M)
                  (2 * gamma_enum (\<Gamma>_tm M) (bl_tm M) (buf tk) + bit_value (?a tk))
                  \<in> \<Gamma>_tm M \<union> {bl_tm M}"
    using gamma_unenum_mem[OF valid_mttm_finite_Gamma[OF vM]] .
  have kpos: "0 < block_width (\<Gamma>_tm M)" using block_width_pos[of "\<Gamma>_tm M"] by simp
  have dst_valid: "ar_valid_stage (\<Gamma>_tm M) (bl_tm M) (snd ?s')"
    using kpos buf_valid gu_mem by (auto simp: ar_valid_stage_def)
  have pad_a: "\<forall>j \<ge> k_tm M. ?a j = BLANK4" using pad_blank c'_eq by simp
  have tk_lt: "tk < k_tm M" using src_bounded by (simp add: ar_stage_bounded_def)
  have ksucc_lt: "k_succ tk < k_tm M"
  proof -
    have ne: "Suc tk \<noteq> k_tm M" using notlast by (simp add: is_last_k_def)
    have le: "Suc tk \<le> k_tm M" using tk_lt by simp
    show ?thesis unfolding k_succ_def using le_neq_implies_less[OF le ne] .
  qed
  have pad_read: "\<forall>j \<ge> k_tm M. ?a j = BLANK4 \<and> ?a j = BLANK4 \<and> ?d j = dir.N"
  proof (intro allI impI)
    fix j assume jge: "k_tm M \<le> j"
    have jne: "j \<noteq> tk" using tk_lt jge by linarith
    show "?a j = BLANK4 \<and> ?a j = BLANK4 \<and> ?d j = dir.N"
      using pad_a jge jne by simp
  qed
  have dst_bd: "ar_stage_bounded (bl_tm M) (k_tm M) (snd ?s')"
  proof -
    have bt: "\<forall>j\<ge>k_tm M.
       (buf(tk := gamma_unenum (\<Gamma>_tm M) (bl_tm M)
              (2 * gamma_enum (\<Gamma>_tm M) (bl_tm M) (buf tk)
                 + bit_value (?a tk)))) j = bl_tm M"
    proof (intro allI impI)
      fix j assume jge: "k_tm M \<le> j"
      have "j \<noteq> tk" using tk_lt jge by linarith
      thus "(buf(tk := gamma_unenum (\<Gamma>_tm M) (bl_tm M)
                (2 * gamma_enum (\<Gamma>_tm M) (bl_tm M) (buf tk)
                   + bit_value (?a tk)))) j = bl_tm M"
        using src_bounded jge by (simp add: ar_stage_bounded_def)
    qed
    show ?thesis using src_bounded ksucc_lt bt by (simp add: ar_stage_bounded_def)
  qed
  have ard_in: "(?s, ?a, ?s', ?a, ?d) \<in> alphabet_reduce_delta M"
    unfolding alphabet_reduce_delta_def
    using rel_in vsrc dst_valid pad_read src_bounded dst_bd
    by (auto split: if_splits)
  have ts_unchanged: "(\<lambda>k. (ts k)(n k := ?a k)) = ts" by (rule ext) auto
  have pos_new: "(\<lambda>k. go_dir (?d k) (n k)) = n(tk := Suc (n tk))"
    by (rule ext) simp
  let ?c'' = "Config\<^sub>M ?s' ts (n(tk := Suc (n tk)))"
  have "(Config\<^sub>M ?s ts n,
          Config\<^sub>M ?s' (\<lambda>k. (ts k)(n k := ?a k))
            (\<lambda>k. go_dir (?d k) (n k)))
          \<in> mttm_step (alphabet_reduce_delta M)"
  proof (rule mttm_step.intros)
    show "(?s, ?a, ?s', ?a, ?d) \<in> alphabet_reduce_delta M" by (rule ard_in)
  qed
  hence step: "(c', ?c'') \<in> mttm_step (alphabet_reduce_delta M)"
    using c'_eq ts_unchanged pos_new by simp
  show ?thesis
    using step by (intro exI[where x = ?c'']) (simp add: c'_eq)
qed

text \<open>The read proper-arm per-bit boundary substep, last tape: same
  last-bit accumulator step, transitioning to \<open>AR_SimCompute\<close> with
  the current-tape field reset to \<open>k_unidx 0\<close> (all tapes decoded,
  begin the compute substep).  Arm 7 (rightmost) of the union.\<close>

lemma ar_read_bit_finish_step:
  fixes M :: "('q, 'a) mttm"
    and c' :: "(sym4, 'q \<times> 'a ar_stage) mt_config"
  assumes vM: "valid_mttm M"
      and stg: "mt_state c' = (q, AR_SimRead, tk, i, buf, dvec, posk)"
      and qQ: "q \<in> Q_tm M"
      and last: "is_last_k M tk"
      and posk_proper: "posk tk \<in> {AR_AtFirstProper, AR_AtFurtherProper}"
      and ieq: "i = Suc (block_width (\<Gamma>_tm M))"
      and vsrc: "ar_valid_stage (\<Gamma>_tm M) (bl_tm M)
                   (AR_SimRead, tk, i, buf, dvec, posk)"
      and pad_blank: "\<forall>j \<ge> k_tm M. mt_tape c' j (mt_pos c' j) = BLANK4"
      and src_bounded: "ar_stage_bounded (bl_tm M) (k_tm M)
                          (AR_SimRead, tk, i, buf, dvec, posk)"
  shows "\<exists>c''. (c', c'') \<in> mttm_step (alphabet_reduce_delta M)
              \<and> mt_state c'' = (q, AR_SimCompute, k_unidx 0, 0,
                    buf(tk := gamma_unenum (\<Gamma>_tm M) (bl_tm M)
                          (2 * gamma_enum (\<Gamma>_tm M) (bl_tm M) (buf tk)
                             + bit_value (mt_tape c' tk (mt_pos c' tk)))),
                    dvec, posk)
              \<and> mt_tape c'' = mt_tape c'
              \<and> mt_pos c'' = (mt_pos c')(tk := Suc (mt_pos c' tk))"
proof -
  obtain ts n where c'_eq:
      "c' = Config\<^sub>M (q, AR_SimRead, tk, i, buf, dvec, posk) ts n"
    using stg by (cases c') auto
  let ?a = "\<lambda>k. ts k (n k)"
  let ?d = "\<lambda>kk. if kk = tk then dir.R else dir.N"
  let ?s = "(q, AR_SimRead, tk, i, buf, dvec, posk)"
  let ?s' = "(q, AR_SimCompute, k_unidx 0, 0,
              buf(tk := gamma_unenum (\<Gamma>_tm M) (bl_tm M)
                    (2 * gamma_enum (\<Gamma>_tm M) (bl_tm M) (buf tk) + bit_value (?a tk))),
              dvec, posk)"
  have rel_in: "(?s, ?a, ?s', ?a, ?d) \<in> ar_delta_read M"
    unfolding ar_delta_read_def
    by (rule UnI2) (use qQ last posk_proper ieq in blast)
  have buf_valid: "\<forall>k. buf k \<in> \<Gamma>_tm M \<union> {bl_tm M}"
    using vsrc by (simp add: ar_valid_stage_def)
  have gu_mem: "gamma_unenum (\<Gamma>_tm M) (bl_tm M)
                  (2 * gamma_enum (\<Gamma>_tm M) (bl_tm M) (buf tk) + bit_value (?a tk))
                  \<in> \<Gamma>_tm M \<union> {bl_tm M}"
    using gamma_unenum_mem[OF valid_mttm_finite_Gamma[OF vM]] .
  have kpos: "0 < block_width (\<Gamma>_tm M)" using block_width_pos[of "\<Gamma>_tm M"] by simp
  have dst_valid: "ar_valid_stage (\<Gamma>_tm M) (bl_tm M) (snd ?s')"
    using kpos buf_valid gu_mem by (auto simp: ar_valid_stage_def)
  have pad_a: "\<forall>j \<ge> k_tm M. ?a j = BLANK4" using pad_blank c'_eq by simp
  have tk_lt: "tk < k_tm M" using src_bounded by (simp add: ar_stage_bounded_def)
  have kpos_tm: "0 < k_tm M" using vM by (cases M) auto
  have pad_read: "\<forall>j \<ge> k_tm M. ?a j = BLANK4 \<and> ?a j = BLANK4 \<and> ?d j = dir.N"
  proof (intro allI impI)
    fix j assume jge: "k_tm M \<le> j"
    have jne: "j \<noteq> tk" using tk_lt jge by linarith
    show "?a j = BLANK4 \<and> ?a j = BLANK4 \<and> ?d j = dir.N"
      using pad_a jge jne by simp
  qed
  have dst_bd: "ar_stage_bounded (bl_tm M) (k_tm M) (snd ?s')"
  proof -
    have bt: "\<forall>j\<ge>k_tm M.
       (buf(tk := gamma_unenum (\<Gamma>_tm M) (bl_tm M)
              (2 * gamma_enum (\<Gamma>_tm M) (bl_tm M) (buf tk)
                 + bit_value (?a tk)))) j = bl_tm M"
    proof (intro allI impI)
      fix j assume jge: "k_tm M \<le> j"
      have "j \<noteq> tk" using tk_lt jge by linarith
      thus "(buf(tk := gamma_unenum (\<Gamma>_tm M) (bl_tm M)
                (2 * gamma_enum (\<Gamma>_tm M) (bl_tm M) (buf tk)
                   + bit_value (?a tk)))) j = bl_tm M"
        using src_bounded jge by (simp add: ar_stage_bounded_def)
    qed
    show ?thesis using src_bounded kpos_tm bt
      by (simp add: ar_stage_bounded_def k_unidx_def)
  qed
  have ard_in: "(?s, ?a, ?s', ?a, ?d) \<in> alphabet_reduce_delta M"
    unfolding alphabet_reduce_delta_def
    using rel_in vsrc dst_valid pad_read src_bounded dst_bd
    by (auto split: if_splits)
  have ts_unchanged: "(\<lambda>k. (ts k)(n k := ?a k)) = ts" by (rule ext) auto
  have pos_new: "(\<lambda>k. go_dir (?d k) (n k)) = n(tk := Suc (n tk))"
    by (rule ext) simp
  let ?c'' = "Config\<^sub>M ?s' ts (n(tk := Suc (n tk)))"
  have "(Config\<^sub>M ?s ts n,
          Config\<^sub>M ?s' (\<lambda>k. (ts k)(n k := ?a k))
            (\<lambda>k. go_dir (?d k) (n k)))
          \<in> mttm_step (alphabet_reduce_delta M)"
  proof (rule mttm_step.intros)
    show "(?s, ?a, ?s', ?a, ?d) \<in> alphabet_reduce_delta M" by (rule ard_in)
  qed
  hence step: "(c', ?c'') \<in> mttm_step (alphabet_reduce_delta M)"
    using c'_eq ts_unchanged pos_new by simp
  show ?thesis
    using step by (intro exI[where x = ?c'']) (simp add: c'_eq)
qed

end
