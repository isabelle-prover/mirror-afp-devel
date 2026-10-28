theory AlphabetReduction_Forward
  imports AlphabetReduction_ForwardAdvance
begin

subsection \<open>Simulating one step of \<open>M\<close>, and a whole run\<close>

text \<open>Acceptance read-out, the AR analogue of AE's
  \<open>ae_simulates_accept_iff\<close>.  Under \<open>ar_simulates\<close>, the
  source \<open>M\<close>-config is in the accept state iff the paired
  \<open>M'\<close>-config sits in the canonical accept config
  \<open>(t_ktm M, ar_accept_stage bl_M)\<close>.  Forward: \<open>q\<^sub>M = t\<close>
  forces the second \<open>ar_simulates\<close> disjunct (the first needs
  \<open>q\<^sub>M' \<notin> \<lbrace>t, r\<rbrace>\<close>; the third needs \<open>t = r\<close>, ruled
  out by \<open>valid_ktm_t_neq_r\<close>).  Reverse is immediate from the
  state-equality conjunct.
  Throughout, \<open>b\<close> abbreviates \<open>block_width \<Gamma>\<close> (the per-symbol cell width).\<close>

lemma ar_simulates_accept_iff:
  fixes M :: "('q, 'a) ktm"
    and cM :: "('a, 'q) ktc_config"
    and c' :: "(sym4, 'q \<times> 'a ar_stage) ktc_config"
  assumes vM:  "valid_ktm M"
      and sim: "ar_simulates M cM c'"
  shows "(ktc_state cM = t_ktm M)
          \<longleftrightarrow> (ktc_state c' = (t_ktm M, ar_accept_stage (bl_ktm M)))"
proof -
  obtain qM' stg where st: "ktc_state c' = (qM', stg)"
    by (cases "ktc_state c'") auto
  obtain idx tk i buf dvec posk where
      sg: "stg = (idx, tk, i, buf, dvec, posk)"
    by (cases stg) auto
  have sim_body:
      "((idx = AR_SimRead \<and> qM' \<notin> {t_ktm M, r_ktm M})
          \<or> (qM' = t_ktm M
               \<and> (idx, tk, i, buf, dvec, posk) = ar_accept_stage (bl_ktm M))
          \<or> (qM' = r_ktm M
               \<and> (idx, tk, i, buf, dvec, posk) = ar_reject_stage (bl_ktm M)))
       \<and> ktc_state cM = qM'
       \<and> (\<forall>k < k_ktm M. ar_tape_correspondence (\<Gamma>_ktm M) (le_ktm M) (bl_ktm M)
                 (ktc_tape cM k) (ktc_tape c' k))
       \<and> (idx = AR_SimRead
            \<longrightarrow> (\<forall>k. ktc_pos c' k = sim_pos (block_width (\<Gamma>_ktm M)) (ktc_pos cM k)))"
    using sim unfolding ar_simulates_def by (simp add: st sg Let_def)
  have disj:
      "(idx = AR_SimRead \<and> qM' \<notin> {t_ktm M, r_ktm M})
        \<or> (qM' = t_ktm M
             \<and> (idx, tk, i, buf, dvec, posk) = ar_accept_stage (bl_ktm M))
        \<or> (qM' = r_ktm M
             \<and> (idx, tk, i, buf, dvec, posk) = ar_reject_stage (bl_ktm M))"
    using sim_body by simp
  have qM_eq: "ktc_state cM = qM'" using sim_body by simp
  show ?thesis
  proof
    assume "ktc_state cM = t_ktm M"
    hence qt: "qM' = t_ktm M" using qM_eq by simp
    have "(idx, tk, i, buf, dvec, posk) = ar_accept_stage (bl_ktm M)"
      using disj qt valid_ktm_t_neq_r[OF vM] by auto
    thus "ktc_state c' = (t_ktm M, ar_accept_stage (bl_ktm M))"
      using st sg qt by simp
  next
    assume "ktc_state c' = (t_ktm M, ar_accept_stage (bl_ktm M))"
    hence "qM' = t_ktm M" using st by simp
    thus "ktc_state cM = t_ktm M" using qM_eq by simp
  qed
qed

text \<open>The next substep, non-terminal hand-off: a single
  \<open>M'\<close>-step from an \<open>AR_SimNext\<close> stage whose \<open>M\<close>-state
  \<open>q\<close> is neither accepting nor rejecting routes to the next
  \<open>M\<close>-step's \<open>AR_SimRead\<close> boundary, resetting both the
  current-tape and bit-counter fields to \<open>0\<close> while preserving
  \<open>buf\<close>, \<open>dvec\<close>, and the per-tape \<open>posk\<close>.  No tape
  cell changes and no head moves (all directions \<open>N\<close>,
  the write vector is the read vector).  The cleanest of the five
  phases — the \<open>ar_compute_step\<close> shape with arm 1 of the
  three-arm \<open>ar_delta_next\<close> union; the two \<open>\<delta>LE\<close>
  filters discharge reflexively (write equals read, move \<open>N\<close>)
  and target-stage validity rests only on \<open>0 < b\<close>.
  The terminal arms (\<open>q = t_ktm M\<close> / \<open>q = r_ktm M\<close>) route
  to the halt stages instead and are handled at assembly, not here.\<close>

lemma ar_next_step:
  fixes M :: "('q, 'a) ktm"
    and c' :: "(sym4, 'q \<times> 'a ar_stage) ktc_config"
  assumes vM: "valid_ktm M"
      and stg: "ktc_state c' = (q, AR_SimNext, tk, i, buf, dvec, posk)"
      and qQ: "q \<in> Q_ktm M"
      and notT: "q \<noteq> t_ktm M"
      and notR: "q \<noteq> r_ktm M"
      and vsrc: "ar_valid_stage (\<Gamma>_ktm M) (bl_ktm M)
                   (AR_SimNext, tk, i, buf, dvec, posk)"
      and pad_blank: "\<forall>j \<ge> k_ktm M. ktc_tape c' j (ktc_pos c' j) = BLANK4"
      and src_bounded: "ar_stage_bounded (bl_ktm M) (k_ktm M)
                          (AR_SimNext, tk, i, buf, dvec, posk)"
  shows "\<exists>c''. (c', c'') \<in> ktm_step (alphabet_reduce_delta M)
              \<and> ktc_state c'' = (q, AR_SimRead, 0, 0, buf, dvec, posk)
              \<and> ktc_tape c'' = ktc_tape c'
              \<and> ktc_pos c'' = ktc_pos c'"
proof -
  obtain ts n where c'_eq:
      "c' = KConfig (q, AR_SimNext, tk, i, buf, dvec, posk) ts n"
    using stg by (cases c') auto
  let ?a = "\<lambda>k. ts k (n k)"
  let ?s = "(q, AR_SimNext, tk, i, buf, dvec, posk)"
  let ?s' = "(q, AR_SimRead, 0, 0, buf, dvec, posk)"
  have rel_in: "(?s, ?a, ?s', ?a, (\<lambda>_. MoveN)) \<in> ar_delta_next M"
    unfolding ar_delta_next_def using qQ notT notR by (intro UnI1) blast
  have buf_valid: "\<forall>k. buf k \<in> \<Gamma>_ktm M \<union> {bl_ktm M}"
    using vsrc by (simp add: ar_valid_stage_def)
  have kpos: "0 < block_width (\<Gamma>_ktm M)" using block_width_pos[of "\<Gamma>_ktm M"] by simp
  have dst_valid: "ar_valid_stage (\<Gamma>_ktm M) (bl_ktm M) (snd ?s')"
    using kpos buf_valid by (simp add: ar_valid_stage_def)
  have pad_a: "\<forall>j \<ge> k_ktm M. ?a j = BLANK4" using pad_blank c'_eq by simp
  have pad_read: "\<forall>j \<ge> k_ktm M. ?a j = BLANK4 \<and> ?a j = BLANK4
                    \<and> (\<lambda>_. MoveN) j = MoveN"
    using pad_a by simp
  have kpos_ktm: "0 < k_ktm M" using vM by (cases M) auto
  have dst_bd: "ar_stage_bounded (bl_ktm M) (k_ktm M) (snd ?s')"
    using src_bounded kpos_ktm by (simp add: ar_stage_bounded_def)
  have ard_in: "(?s, ?a, ?s', ?a, (\<lambda>_. MoveN)) \<in> alphabet_reduce_delta M"
    unfolding alphabet_reduce_delta_def
    using rel_in vsrc dst_valid pad_read src_bounded dst_bd by auto
  have ts_unchanged: "(\<lambda>k. (ts k)(n k := ?a k)) = ts" by (rule ext) auto
  have pos_unchanged: "(\<lambda>k. go_move ((\<lambda>_. MoveN) k) (n k)) = n"
    by (rule ext) auto
  let ?c'' = "KConfig ?s' ts n"
  have "(KConfig ?s ts n,
          KConfig ?s' (\<lambda>k. (ts k)(n k := ?a k))
            (\<lambda>k. go_move ((\<lambda>_. MoveN) k) (n k)))
          \<in> ktm_step (alphabet_reduce_delta M)"
  proof (rule ktm_step.intros)
    show "(?s, ?a, ?s', ?a, (\<lambda>_. MoveN))
            \<in> alphabet_reduce_delta M"
      by (rule ard_in)
  qed
  hence step: "(c', ?c'') \<in> ktm_step (alphabet_reduce_delta M)"
    using c'_eq ts_unchanged pos_unchanged by simp
  show ?thesis
    using step by (intro exI[where x = ?c'']) (simp add: c'_eq)
qed

text \<open>The two terminal hand-offs, the accept and reject arms of
  \<open>ar_delta_next\<close>: a single \<open>M'\<close>-step from an
  \<open>AR_SimNext\<close> stage whose \<open>M\<close>-state \<open>q\<close> is the
  accepting (resp. rejecting) state lands on the canonical halt stage
  \<open>ar_accept_stage (bl_ktm M)\<close> (resp. \<open>ar_reject_stage\<close>),
  so the full target state equals \<open>t_ktm (alphabet_reduce M)\<close>
  (resp. \<open>r_ktm\<close>): full-state
  acceptance forces the canonicalisation.  Tape and heads are
  unchanged (the move vector is all-\<open>N\<close>, no writes).  Modelled on
  \<open>ar_next_step\<close>; the membership lets \<open>blast\<close> select the halt
  comprehension and instantiate its witnesses.\<close>
lemma ar_accept_step:
  fixes M :: "('q, 'a) ktm"
    and c' :: "(sym4, 'q \<times> 'a ar_stage) ktc_config"
  assumes vM: "valid_ktm M"
      and stg: "ktc_state c' = (q, AR_SimNext, tk, i, buf, dvec, posk)"
      and qT: "q = t_ktm M"
      and vsrc: "ar_valid_stage (\<Gamma>_ktm M) (bl_ktm M)
                   (AR_SimNext, tk, i, buf, dvec, posk)"
      and pad_blank: "\<forall>j \<ge> k_ktm M. ktc_tape c' j (ktc_pos c' j) = BLANK4"
      and src_bounded: "ar_stage_bounded (bl_ktm M) (k_ktm M)
                          (AR_SimNext, tk, i, buf, dvec, posk)"
  shows "\<exists>c''. (c', c'') \<in> ktm_step (alphabet_reduce_delta M)
              \<and> ktc_state c'' = (t_ktm M, ar_accept_stage (bl_ktm M))
              \<and> ktc_tape c'' = ktc_tape c'
              \<and> ktc_pos c'' = ktc_pos c'"
proof -
  obtain ts n where c'_eq:
      "c' = KConfig (q, AR_SimNext, tk, i, buf, dvec, posk) ts n"
    using stg by (cases c') auto
  let ?a = "\<lambda>k. ts k (n k)"
  let ?s = "(q, AR_SimNext, tk, i, buf, dvec, posk)"
  let ?s' = "(q, AR_HaltAccept, 0, 0,
              (\<lambda>_. bl_ktm M), (\<lambda>_. MoveN), (\<lambda>_. AR_AtLE))"
  have rel_in: "(?s, ?a, ?s', ?a, (\<lambda>_. MoveN)) \<in> ar_delta_next M"
    unfolding ar_delta_next_def using qT by blast
  have kpos: "0 < block_width (\<Gamma>_ktm M)" using block_width_pos[of "\<Gamma>_ktm M"] by simp
  have dst_valid: "ar_valid_stage (\<Gamma>_ktm M) (bl_ktm M) (snd ?s')"
    using kpos by (simp add: ar_valid_stage_def)
  have pad_a: "\<forall>j \<ge> k_ktm M. ?a j = BLANK4" using pad_blank c'_eq by simp
  have pad_read: "\<forall>j \<ge> k_ktm M. ?a j = BLANK4 \<and> ?a j = BLANK4
                    \<and> (\<lambda>_. MoveN) j = MoveN"
    using pad_a by simp
  have kpos_ktm: "0 < k_ktm M" using vM by (cases M) auto
  have dst_bd: "ar_stage_bounded (bl_ktm M) (k_ktm M) (snd ?s')"
    using kpos_ktm by (simp add: ar_stage_bounded_def)
  have ard_in: "(?s, ?a, ?s', ?a, (\<lambda>_. MoveN)) \<in> alphabet_reduce_delta M"
    unfolding alphabet_reduce_delta_def
    using rel_in vsrc dst_valid pad_read src_bounded dst_bd by auto
  have ts_unchanged: "(\<lambda>k. (ts k)(n k := ?a k)) = ts" by (rule ext) auto
  have pos_unchanged: "(\<lambda>k. go_move ((\<lambda>_. MoveN) k) (n k)) = n"
    by (rule ext) auto
  let ?c'' = "KConfig ?s' ts n"
  have "(KConfig ?s ts n,
          KConfig ?s' (\<lambda>k. (ts k)(n k := ?a k))
            (\<lambda>k. go_move ((\<lambda>_. MoveN) k) (n k)))
          \<in> ktm_step (alphabet_reduce_delta M)"
  proof (rule ktm_step.intros)
    show "(?s, ?a, ?s', ?a, (\<lambda>_. MoveN))
            \<in> alphabet_reduce_delta M"
      by (rule ard_in)
  qed
  hence step: "(c', ?c'') \<in> ktm_step (alphabet_reduce_delta M)"
    using c'_eq ts_unchanged pos_unchanged by simp
  show ?thesis
    using step by (intro exI[where x = ?c''])
      (simp add: c'_eq qT ar_accept_stage_def)
qed

lemma ar_reject_step:
  fixes M :: "('q, 'a) ktm"
    and c' :: "(sym4, 'q \<times> 'a ar_stage) ktc_config"
  assumes vM: "valid_ktm M"
      and stg: "ktc_state c' = (q, AR_SimNext, tk, i, buf, dvec, posk)"
      and qR: "q = r_ktm M"
      and vsrc: "ar_valid_stage (\<Gamma>_ktm M) (bl_ktm M)
                   (AR_SimNext, tk, i, buf, dvec, posk)"
      and pad_blank: "\<forall>j \<ge> k_ktm M. ktc_tape c' j (ktc_pos c' j) = BLANK4"
      and src_bounded: "ar_stage_bounded (bl_ktm M) (k_ktm M)
                          (AR_SimNext, tk, i, buf, dvec, posk)"
  shows "\<exists>c''. (c', c'') \<in> ktm_step (alphabet_reduce_delta M)
              \<and> ktc_state c'' = (r_ktm M, ar_reject_stage (bl_ktm M))
              \<and> ktc_tape c'' = ktc_tape c'
              \<and> ktc_pos c'' = ktc_pos c'"
proof -
  obtain ts n where c'_eq:
      "c' = KConfig (q, AR_SimNext, tk, i, buf, dvec, posk) ts n"
    using stg by (cases c') auto
  let ?a = "\<lambda>k. ts k (n k)"
  let ?s = "(q, AR_SimNext, tk, i, buf, dvec, posk)"
  let ?s' = "(q, AR_HaltReject, 0, 0,
              (\<lambda>_. bl_ktm M), (\<lambda>_. MoveN), (\<lambda>_. AR_AtLE))"
  have rel_in: "(?s, ?a, ?s', ?a, (\<lambda>_. MoveN)) \<in> ar_delta_next M"
    unfolding ar_delta_next_def using qR by blast
  have kpos: "0 < block_width (\<Gamma>_ktm M)" using block_width_pos[of "\<Gamma>_ktm M"] by simp
  have dst_valid: "ar_valid_stage (\<Gamma>_ktm M) (bl_ktm M) (snd ?s')"
    using kpos by (simp add: ar_valid_stage_def)
  have pad_a: "\<forall>j \<ge> k_ktm M. ?a j = BLANK4" using pad_blank c'_eq by simp
  have pad_read: "\<forall>j \<ge> k_ktm M. ?a j = BLANK4 \<and> ?a j = BLANK4
                    \<and> (\<lambda>_. MoveN) j = MoveN"
    using pad_a by simp
  have kpos_ktm: "0 < k_ktm M" using vM by (cases M) auto
  have dst_bd: "ar_stage_bounded (bl_ktm M) (k_ktm M) (snd ?s')"
    using kpos_ktm by (simp add: ar_stage_bounded_def)
  have ard_in: "(?s, ?a, ?s', ?a, (\<lambda>_. MoveN)) \<in> alphabet_reduce_delta M"
    unfolding alphabet_reduce_delta_def
    using rel_in vsrc dst_valid pad_read src_bounded dst_bd by auto
  have ts_unchanged: "(\<lambda>k. (ts k)(n k := ?a k)) = ts" by (rule ext) auto
  have pos_unchanged: "(\<lambda>k. go_move ((\<lambda>_. MoveN) k) (n k)) = n"
    by (rule ext) auto
  let ?c'' = "KConfig ?s' ts n"
  have "(KConfig ?s ts n,
          KConfig ?s' (\<lambda>k. (ts k)(n k := ?a k))
            (\<lambda>k. go_move ((\<lambda>_. MoveN) k) (n k)))
          \<in> ktm_step (alphabet_reduce_delta M)"
  proof (rule ktm_step.intros)
    show "(?s, ?a, ?s', ?a, (\<lambda>_. MoveN))
            \<in> alphabet_reduce_delta M"
      by (rule ard_in)
  qed
  hence step: "(c', ?c'') \<in> ktm_step (alphabet_reduce_delta M)"
    using c'_eq ts_unchanged pos_unchanged by simp
  show ?thesis
    using step by (intro exI[where x = ?c''])
      (simp add: c'_eq qR ar_reject_stage_def)
qed

text \<open>Two position-bookkeeping facts for the advance phase, decided
  once in a clean context (no \<open>let\<close>-bound \<open>?\<close>-vars to
  tangle the case split).  Given \<open>M\<close>'s head at position
  \<open>p\<close> moving \<open>dr\<close> (with \<open>dr \<noteq> L\<close> when
  \<open>p = 0\<close>, the \<open>\<delta>LE\<close> discipline), the read-phase
  position-kind \<open>if p=0 then AtLE else if p=1 then FirstProper else
  FurtherProper\<close> advances via \<open>ar_newpos\<close> to \<open>AtLE\<close>
  exactly when \<open>M\<close>'s new position is \<open>0\<close>, and the
  read-phase landing position less the \<open>ar_disp\<close> displacement is
  exactly \<open>sim_pos\<close> of \<open>M\<close>'s new position.  Both reduce to
  a \<open>p \<in> {0, 1, \<ge> 2}\<close> cross \<open>dr \<in> {N, R, L}\<close>
  grid.\<close>
lemma ar_newpos_atLE_iff:
  fixes p :: nat and dr :: move
  assumes nL0: "p = 0 \<Longrightarrow> dr \<noteq> MoveL"
  shows "(ar_newpos dr (if p = 0 then AR_AtLE
                        else if p = 1 then AR_AtFirstProper
                        else AR_AtFurtherProper) = AR_AtLE)
           \<longleftrightarrow> go_move dr p = 0"
proof (cases p)
  case 0
  hence "dr = MoveN \<or> dr = MoveR" using nL0 by (cases dr) auto
  thus ?thesis using 0 by auto
next
  case (Suc nat)
  show ?thesis
  proof (cases nat)
    case 0
    thus ?thesis using Suc by (cases dr) auto
  next
    case (Suc m)
    thus ?thesis using \<open>p = Suc nat\<close> by (cases dr) auto
  qed
qed

lemma ar_advance_newsimpos:
  fixes K p :: nat and dr :: move
  assumes Kge2: "2 \<le> K"
      and nL0: "p = 0 \<Longrightarrow> dr \<noteq> MoveL"
  shows "(if dr = MoveR
            then (if p = 0 then Suc 0 else sim_pos K p + K)
            else (if p = 0 then Suc 0 else sim_pos K p + K)
                   - ar_disp K dr (if p = 0 then AR_AtLE
                                   else if p = 1 then AR_AtFirstProper
                                   else AR_AtFurtherProper))
          = sim_pos K (go_move dr p)"
proof (cases p)
  case 0
  hence "dr = MoveN \<or> dr = MoveR" using nL0 by (cases dr) auto
  thus ?thesis using 0 by (auto simp: sim_pos_def)
next
  case (Suc nat)
  show ?thesis
  proof (cases nat)
    case 0
    thus ?thesis using Suc Kge2 by (cases dr) (auto simp: sim_pos_def)
  next
    case (Suc m)
    thus ?thesis using \<open>p = Suc nat\<close> Kge2
      by (cases dr) (auto simp: sim_pos_def algebra_simps)
  qed
qed

text \<open>Per-\<open>M\<close>-step forward simulation: one \<open>M\<close>-step
  \<open>cM \<rightarrow> cM\<^sub>1\<close> from an \<open>AR_SimRead\<close> boundary is matched by a
  bounded \<open>M'\<close>-phase (read \<open>\<rightarrow>\<close> compute \<open>\<rightarrow>\<close> write
  \<open>\<rightarrow>\<close> advance \<open>\<rightarrow>\<close> next) of at most \<open>k_ktm M \<cdot>
  (5b + 2) + 2\<close> \<open>M'\<close>-steps (the per-phase \<open>k_ktm M\<close>-scaled
  sum: read \<open>\<le> k_ktm M \<cdot> (b+2)\<close>, write and advance each
  \<open>\<le> k_ktm M \<cdot> 2b\<close>, compute and next one step apiece) that
  re-establishes \<open>ar_simulates\<close> at the next boundary.  This is the
  composition of the per-substep phase lemmas above into one
  \<open>M\<close>-step; the chunked engine below iterates it.  The
  reachability hypothesis \<open>reach_M\<close> with \<open>w_sub\<close> supplies
  the substrate \<open>LE\<close>-only-at-position-\<open>0\<close> fact the read
  look-back needs, and \<open>card_ge\<close> gives \<open>b \<ge> 2\<close>
  for the proper-region read arms.\<close>

text \<open>The post-write tape correspondence, factored out of
  \<open>ar_simulates_forward_step\<close> so the reverse cycle-close reuses
  it.  Given the
  read-boundary correspondence between \<open>M\<close>'s tape and the output
  tape \<open>rt\<close>, and that \<open>cM_1\<close> is \<open>M\<close> after writing
  \<open>a'\<close> under each head, the write phase's per-tape overwrite
  \<open>wt\<close> — which stamps \<open>a'\<close>'s cell block at the head's
  block and leaves the rest of \<open>rt\<close> untouched — is again a
  correspondence, now for \<open>cM_1\<close>.  Both arms supply their own
  \<open>wt\<close> and discharge \<open>wt_def\<close> from their write-phase
  output contract.\<close>

lemma ar_write_tape_correspondence:
  fixes M :: "('q, 'a) ktm"
    and cM cM_1 :: "('a, 'q) ktc_config"
    and rt wt :: "nat \<Rightarrow> nat \<Rightarrow> sym4"
    and a' :: "nat \<Rightarrow> 'a"
  assumes kge2: "2 \<le> block_width (\<Gamma>_ktm M)"
      and kN: "k < k_ktm M"
      and tcorr: "\<forall>k < k_ktm M. ar_tape_correspondence (\<Gamma>_ktm M) (le_ktm M) (bl_ktm M)
                       (ktc_tape cM k) (rt k)"
      and cM1tape: "\<And>k. ktc_tape cM_1 k = (ktc_tape cM k)(ktc_pos cM k := a' k)"
      and a'le0: "\<forall>k < k_ktm M. ktc_pos cM k = 0 \<longrightarrow> a' k = le_ktm M"
      and wt_def: "\<And>k pos. wt k pos
            = (if ktc_pos cM k = 0 then rt k pos
               else if sim_pos (block_width (\<Gamma>_ktm M)) (ktc_pos cM k) \<le> pos
                       \<and> pos < sim_pos (block_width (\<Gamma>_ktm M)) (ktc_pos cM k)
                                 + block_width (\<Gamma>_ktm M)
                    then write_bit (\<Gamma>_ktm M) (bl_ktm M) (a' k)
                           (pos - sim_pos (block_width (\<Gamma>_ktm M)) (ktc_pos cM k))
                    else rt k pos)"
  shows "ar_tape_correspondence (\<Gamma>_ktm M) (le_ktm M) (bl_ktm M)
           (ktc_tape cM_1 k) (wt k)"
proof -
  let ?k = "block_width (\<Gamma>_ktm M)"
  have k1: "1 \<le> ?k" using kge2 by simp
  have tcorr_k: "ar_tape_correspondence (\<Gamma>_ktm M) (le_ktm M) (bl_ktm M)
                   (ktc_tape cM k) (rt k)"
    using tcorr kN by blast
  have a'le0_k: "ktc_pos cM k = 0 \<longrightarrow> a' k = le_ktm M"
    using a'le0 kN by blast
  have cM0: "ktc_tape cM k 0 = le_ktm M"
    using tcorr_k unfolding ar_tape_correspondence_def by blast
  have rt0: "rt k 0 = LE4"
    using tcorr_k unfolding ar_tape_correspondence_def by blast
  have rtprop: "rt k (sim_pos ?k p + j)
                  = cell_repr (\<Gamma>_ktm M) (bl_ktm M) (ktc_tape cM k p) ! j"
    if "1 \<le> p" and "j < ?k" for p j
    using tcorr_k that unfolding ar_tape_correspondence_def by blast
  \<comment> \<open>conjunct (a): \<open>M\<close>'s updated tape still reads \<open>le\<close> at 0\<close>
  have a: "ktc_tape cM_1 k 0 = le_ktm M"
  proof (cases "ktc_pos cM k = 0")
    case True
    hence "a' k = le_ktm M" using a'le0_k by simp
    thus ?thesis using cM1tape True by simp
  next
    case False
    thus ?thesis using cM1tape cM0 by simp
  qed
  \<comment> \<open>conjunct (b): \<open>wt\<close> carries \<open>LE4\<close> at 0\<close>
  have b: "wt k 0 = LE4"
  proof (cases "ktc_pos cM k = 0")
    case True
    thus ?thesis using rt0 by (simp add: wt_def)
  next
    case False
    thus ?thesis using rt0 by (auto simp: wt_def sim_pos_def)
  qed
  \<comment> \<open>conjunct (c): every proper block of \<open>wt\<close> encodes the
     matching updated \<open>M\<close>-cell\<close>
  have c: "wt k (sim_pos ?k p + j)
             = cell_repr (\<Gamma>_ktm M) (bl_ktm M) (ktc_tape cM_1 k p) ! j"
    if p1: "1 \<le> p" and jk: "j < ?k" for p j
  proof (cases "ktc_pos cM k = 0")
    case True
    have pne: "p \<noteq> ktc_pos cM k" using True p1 by simp
    have cM1p: "ktc_tape cM_1 k p = ktc_tape cM k p" using cM1tape pne by simp
    have "wt k (sim_pos ?k p + j) = rt k (sim_pos ?k p + j)"
      using True by (simp add: wt_def)
    also have "\<dots> = cell_repr (\<Gamma>_ktm M) (bl_ktm M) (ktc_tape cM k p) ! j"
      using rtprop[OF p1 jk] by simp
    also have "\<dots> = cell_repr (\<Gamma>_ktm M) (bl_ktm M) (ktc_tape cM_1 k p) ! j"
      using cM1p by simp
    finally show ?thesis .
  next
    case False
    have pw1: "1 \<le> ktc_pos cM k" using False by simp
    show ?thesis
    proof (cases "p = ktc_pos cM k")
      case True
      have inblk: "sim_pos ?k (ktc_pos cM k) \<le> sim_pos ?k p + j
                     \<and> sim_pos ?k p + j < sim_pos ?k (ktc_pos cM k) + ?k"
        using True jk by simp
      have off: "sim_pos ?k p + j - sim_pos ?k (ktc_pos cM k) = j"
        using True by simp
      have "wt k (sim_pos ?k p + j) = write_bit (\<Gamma>_ktm M) (bl_ktm M) (a' k) j"
        using False inblk off by (simp add: wt_def)
      also have "\<dots> = cell_repr (\<Gamma>_ktm M) (bl_ktm M) (a' k) ! j"
        using cell_repr_nth_write_bit[OF jk] by simp
      also have "\<dots> = cell_repr (\<Gamma>_ktm M) (bl_ktm M) (ktc_tape cM_1 k p) ! j"
        using cM1tape True by simp
      finally show ?thesis .
    next
      case False
      have notblk: "\<not> (sim_pos ?k (ktc_pos cM k) \<le> sim_pos ?k p + j
                        \<and> sim_pos ?k p + j < sim_pos ?k (ktc_pos cM k) + ?k)"
        using sim_pos_in_block_iff[OF k1 p1 pw1 jk] False by simp
      have pne: "p \<noteq> ktc_pos cM k" using False by simp
      have cM1p: "ktc_tape cM_1 k p = ktc_tape cM k p" using cM1tape pne by simp
      have "wt k (sim_pos ?k p + j) = rt k (sim_pos ?k p + j)"
        using \<open>ktc_pos cM k \<noteq> 0\<close> by (simp add: wt_def if_not_P[OF notblk])
      also have "\<dots> = cell_repr (\<Gamma>_ktm M) (bl_ktm M) (ktc_tape cM k p) ! j"
        using rtprop[OF p1 jk] by simp
      also have "\<dots> = cell_repr (\<Gamma>_ktm M) (bl_ktm M) (ktc_tape cM_1 k p) ! j"
        using cM1p by simp
      finally show ?thesis .
    qed
  qed
  show ?thesis
    unfolding ar_tape_correspondence_def using a b c by blast
qed

lemma ar_simulates_forward_step:
  fixes M :: "('q, 'a) ktm"
    and w :: "'a list"
    and cM cM_1 :: "('a, 'q) ktc_config"
    and c' :: "(sym4, 'q \<times> 'a ar_stage) ktc_config"
  assumes vM:      "valid_ktm M"
      and w_sub:   "set w \<subseteq> Sigma_ktm M"
      and card_ge: "card (\<Gamma>_ktm M) \<ge> 4"
      and reach_M: "(init_config_ktm M w, cM) \<in> (ktm_step (delta_ktm M))\<^sup>*"
      and step:    "(cM, cM_1) \<in> ktm_step (delta_ktm M)"
      and sim:     "ar_simulates M cM c'"
      and posk_ok: "ar_posk_consistent M cM c'"
      and rbnd:    "ar_at_read_boundary M c'"
      and lebl:    "le_ktm M \<noteq> bl_ktm M"
  obtains m c'' where
      "m \<le> k_ktm M * (5 * block_width (\<Gamma>_ktm M) + 2) + 2"
    and "(c', c'') \<in> ktm_step (alphabet_reduce_delta M) ^^ m"
    and "ar_simulates M cM_1 c''"
    and "ar_posk_consistent M cM_1 c''"
    and "ar_at_read_boundary M c''"
proof -
  let ?k = "block_width (\<Gamma>_ktm M)"
  let ?N = "k_ktm M"
  \<comment> \<open>encoding length \<open>\<ge> 2\<close> from \<open>card \<Gamma>_M \<ge> 4\<close>\<close>
  have kge2: "2 \<le> ?k"
  proof -
    have "(2::nat) ^ 2 \<le> 2 ^ ?k"
      using card_ge card_le_two_pow_block_width[of "\<Gamma>_ktm M"] by simp
    thus "2 \<le> ?k" using power_le_imp_le_exp[of "2::nat" 2 ?k] by simp
  qed
  have kpos_ktm: "0 < k_ktm M" using vM by (cases M) auto
  \<comment> \<open>extract \<open>M\<close>'s firing \<open>\<delta>\<close>-tuple and the successor
     config from the one \<open>M\<close>-step\<close>
  from step obtain qC tsM nM q' a' d where
      cM_eq: "cM = KConfig qC tsM nM"
    and cM1_eq: "cM_1 = KConfig q' (\<lambda>k. (tsM k)(nM k := a' k))
                          (\<lambda>k. go_move (d k) (nM k))"
    and mdelta: "(qC, \<lambda>k. tsM k (nM k), q', a', d) \<in> delta_ktm M"
    by (auto elim: ktm_step.cases)
  have qC_eq: "qC = ktc_state cM" using cM_eq by simp
  have q'_eq: "q' = ktc_state cM_1" using cM1_eq by simp
  \<comment> \<open>the source \<open>M\<close>-state is a genuine, non-halting state\<close>
  have qQ: "ktc_state cM \<in> Q_ktm M" using ktm_step_src(1)[OF vM step] .
  have qnt: "ktc_state cM \<noteq> t_ktm M" "ktc_state cM \<noteq> r_ktm M"
    using ktm_step_src(2)[OF vM step] ktm_step_src(3)[OF vM step] by blast+
  \<comment> \<open>a reachable \<open>M\<close>-config is valid: every head reads a
     \<open>\<Gamma>\<close> symbol, and beyond the tape count it reads the blank.\<close>
  have valcM: "valid_config_ktm M cM"
    using valid_reach_ktm[OF vM w_sub reach_M] .
  have tapeG: "ktc_tape cM k (ktc_pos cM k) \<in> \<Gamma>_ktm M" for k
  proof -
    have "range (tsM k) \<subseteq> \<Gamma>_ktm M" using valcM cM_eq by (cases M) auto
    thus "ktc_tape cM k (ktc_pos cM k) \<in> \<Gamma>_ktm M" using cM_eq by auto
  qed
  have aM_tail: "\<forall>j \<ge> k_ktm M. ktc_tape cM j (ktc_pos cM j) = bl_ktm M"
    using valid_config_ktm_blank_tail[OF valcM] by blast
  \<comment> \<open>destructure the simulation invariants at the \<open>AR_SimRead\<close>
     boundary; the disjunction collapses to the \<open>AR_SimRead\<close> arm
     because the source state is non-halting.\<close>
  obtain qM' stg where st: "ktc_state c' = (qM', stg)"
    by (cases "ktc_state c'") auto
  obtain idx tk ii buf0 dvec posk0 where
      sg: "stg = (idx, tk, ii, buf0, dvec, posk0)"
    by (cases stg) auto
  have sim_body:
      "((idx = AR_SimRead \<and> qM' \<notin> {t_ktm M, r_ktm M})
          \<or> (qM' = t_ktm M
               \<and> (idx, tk, ii, buf0, dvec, posk0) = ar_accept_stage (bl_ktm M))
          \<or> (qM' = r_ktm M
               \<and> (idx, tk, ii, buf0, dvec, posk0) = ar_reject_stage (bl_ktm M)))
       \<and> ktc_state cM = qM'
       \<and> (\<forall>k < k_ktm M. ar_tape_correspondence (\<Gamma>_ktm M) (le_ktm M) (bl_ktm M)
                 (ktc_tape cM k) (ktc_tape c' k))
       \<and> (idx = AR_SimRead
            \<longrightarrow> (\<forall>k. ktc_pos c' k = sim_pos ?k (ktc_pos cM k)))"
    using sim unfolding ar_simulates_def by (simp add: st sg Let_def)
  have qM'_eq: "qM' = ktc_state cM" using sim_body by simp
  have idx_eq: "idx = AR_SimRead"
    using sim_body qnt qM'_eq
    by (auto simp: ar_accept_stage_def ar_reject_stage_def)
  have tcorr: "\<forall>k < k_ktm M. ar_tape_correspondence (\<Gamma>_ktm M) (le_ktm M) (bl_ktm M)
                 (ktc_tape cM k) (ktc_tape c' k)"
    using sim_body by simp
  have ppos0: "ktc_pos c' k = sim_pos ?k (ktc_pos cM k)" for k
    using sim_body idx_eq by simp
  \<comment> \<open>The strengthened read boundary: canonical entry shape, the
     bounded-stage fact \<open>src_c'\<close>, and the config padding-blank
     \<open>pad_c'\<close>.\<close>
  have rbnd_body:
      "idx = AR_SimRead
        \<longrightarrow> (tk = 0 \<and> ii = 0 \<and> (\<forall>k. buf0 k \<in> \<Gamma>_ktm M \<union> {bl_ktm M})
             \<and> ar_stage_bounded (bl_ktm M) (k_ktm M)
                  (idx, tk, ii, buf0, dvec, posk0))"
    using rbnd st sg unfolding ar_at_read_boundary_def
    by (auto split: prod.splits)
  have tk0: "tk = 0" using rbnd_body idx_eq by simp
  have ii0: "ii = 0" using rbnd_body idx_eq by simp
  have bufG: "buf0 k \<in> \<Gamma>_ktm M \<union> {bl_ktm M}" for k
    using rbnd_body idx_eq by simp
  have src_c': "ar_stage_bounded (bl_ktm M) (k_ktm M)
                  (AR_SimRead, 0, 0, buf0, dvec, posk0)"
    using rbnd_body idx_eq tk0 ii0 by simp
  have pad_c': "\<forall>j \<ge> k_ktm M. ktc_tape c' j (ktc_pos c' j) = BLANK4"
    using rbnd unfolding ar_at_read_boundary_def by (auto split: prod.splits)
  have posk_body:
      "idx = AR_SimRead
        \<longrightarrow> (\<forall>k. posk0 k = AR_AtLE \<longleftrightarrow> ktc_pos cM k = 0)"
    using posk_ok unfolding ar_posk_consistent_def by (simp add: st sg)
  have pkok: "posk0 k = AR_AtLE \<longleftrightarrow> ktc_pos cM k = 0" for k
    using posk_body idx_eq by simp
  have c'_state: "ktc_state c' = (ktc_state cM, AR_SimRead, 0, 0, buf0, dvec, posk0)"
    using st sg qM'_eq idx_eq tk0 ii0 by simp
  \<comment> \<open>The frozen tails beyond the tape count, read off \<open>src_c'\<close>.\<close>
  have buf0_tail: "\<forall>j \<ge> k_ktm M. buf0 j = bl_ktm M"
    using src_c' by (simp add: ar_stage_bounded_def)
  have dvec_tail: "\<forall>j \<ge> k_ktm M. dvec j = MoveN"
    using src_c' by (simp add: ar_stage_bounded_def)
  have posk0_tail: "\<forall>j \<ge> k_ktm M. posk0 j = AR_AtLE"
    using src_c' by (simp add: ar_stage_bounded_def)
  \<comment> \<open>Phase 1 — read: scan every active tape's \<open>M\<close>-cell block
     into \<open>buf\<close>, landing at \<open>AR_SimCompute\<close>.  Beyond the tape count
     \<open>buf\<close> / \<open>posk\<close> / position freeze to the entry config.\<close>
  let ?aM = "\<lambda>k. ktc_tape cM k (ktc_pos cM k)"
  let ?rbuf = "\<lambda>k. if k < k_ktm M then ?aM k else buf0 k"
  let ?rposk = "\<lambda>k. if k < k_ktm M
                     then (if ktc_pos cM k = 0 then AR_AtLE
                           else if ktc_pos cM k = 1 then AR_AtFirstProper
                           else AR_AtFurtherProper)
                     else posk0 k"
  let ?rpos = "\<lambda>k. if k < k_ktm M
                    then (if ktc_pos cM k = 0 then Suc 0
                          else sim_pos ?k (ktc_pos cM k) + ?k)
                    else ktc_pos c' k"
  obtain c_r m_r where
      r_chain: "(c', c_r) \<in> (ktm_step (alphabet_reduce_delta M)) ^^ m_r"
    and r_bound: "m_r \<le> ?N * (?k + 2)"
    and r_state: "ktc_state c_r = (ktc_state cM, AR_SimCompute, k_unidx 0, 0,
                    ?rbuf, dvec, ?rposk)"
    and r_tape: "ktc_tape c_r = ktc_tape c'"
    and r_pos: "ktc_pos c_r = ?rpos"
    using ar_read_phase[OF vM qQ kge2 c'_state tcorr ppos0 pkok tapeG bufG
                           pad_c' src_c'] ktm_run_mono [OF Int_lower1]
    by blast
  \<comment> \<open>Read-exit config padding-blank and bounded-stage facts: the
     tape and (beyond the tape count) position are unchanged, and the
     buffer / direction / posk tails freeze to the entry config.\<close>
  have pad_cr: "\<forall>j \<ge> k_ktm M. ktc_tape c_r j (ktc_pos c_r j) = BLANK4"
  proof (intro allI impI)
    fix j assume jk: "k_ktm M \<le> j"
    have "ktc_pos c_r j = ktc_pos c' j" using r_pos jk by simp
    moreover have "ktc_tape c_r j = ktc_tape c' j" using r_tape by simp
    ultimately show "ktc_tape c_r j (ktc_pos c_r j) = BLANK4"
      using pad_c' jk by simp
  qed
  have src_cr: "ar_stage_bounded (bl_ktm M) (k_ktm M)
                  (AR_SimCompute, k_unidx 0, 0, ?rbuf, dvec, ?rposk)"
    using kpos_ktm buf0_tail dvec_tail posk0_tail
    by (simp add: ar_stage_bounded_def k_unidx_zero)
  \<comment> \<open>Phase 2 — compute: \<open>M\<close>'s read vector now sits in
     \<open>buf\<close> (the guarded read buffer collapses to \<open>?aM\<close>
     because both tails are the blank), so the fired \<open>\<delta>\<close>-tuple
     steps the compute substep to \<open>AR_SimWrite\<close>.\<close>
  have aM_eq: "(\<lambda>k. tsM k (nM k)) = ?aM" by (simp add: cM_eq)
  have rbuf_eq: "?rbuf = ?aM"
  proof (rule ext)
    fix k show "?rbuf k = ?aM k"
    proof (cases "k < k_ktm M")
      case True thus ?thesis by simp
    next
      case False
      have "?rbuf k = bl_ktm M" using buf0_tail False by simp
      moreover have "?aM k = bl_ktm M" using aM_tail False by simp
      ultimately show ?thesis by simp
    qed
  qed
  have mdelta': "(ktc_state cM, ?aM, q', a', d) \<in> delta_ktm M"
    using mdelta by (simp add: qC_eq aM_eq)
  have mdelta'': "(ktc_state cM, ?rbuf, q', a', d) \<in> delta_ktm M"
    using mdelta' rbuf_eq by simp
  have vsrc_c: "ar_valid_stage (\<Gamma>_ktm M) (bl_ktm M)
                  (AR_SimCompute, k_unidx 0, 0, ?rbuf, dvec, ?rposk)"
    using kge2 tapeG bufG by (auto simp: ar_valid_stage_def)
  obtain c_c where
      c_step: "(c_r, c_c) \<in> ktm_step (alphabet_reduce_delta M)"
    and c_state: "ktc_state c_c = (q', AR_SimWrite, 0, 0, a', d, ?rposk)"
    and c_tape: "ktc_tape c_c = ktc_tape c_r"
    and c_pos: "ktc_pos c_c = ktc_pos c_r"
    using ar_compute_step[OF vM r_state mdelta'' vsrc_c pad_cr src_cr] by blast
  \<comment> \<open>Phase 3 setup — write: \<open>M\<close>'s write vector \<open>a'\<close> is the
     new \<open>buf\<close>.  Range / post-state from \<open>valid_ktm\<close>'s
     \<open>\<delta>\<close>-typing; the \<open>bufle\<close> biconditional from
     \<open>M\<close>'s \<open>\<delta>LE\<close> discipline and \<open>le\<close>-only-at-0.\<close>
  have q'Q: "q' \<in> Q_ktm M" using valid_ktm_delta(3)[OF vM mdelta] .
  have a'G: "a' k \<in> \<Gamma>_ktm M" for k using valid_ktm_delta(4)[OF vM mdelta] .
  have a'val: "\<forall>k. a' k \<in> \<Gamma>_ktm M \<union> {bl_ktm M}" using a'G by blast
  have dsupp: "\<forall>j \<ge> k_ktm M. a' j = bl_ktm M \<and> d j = MoveN"
    using valid_ktm_delta_support[OF vM mdelta] by blast
  \<comment> \<open>Cut-tolerant write dispatch.  The write phase keys the
     boundary on the position-kind flag \<open>posk\<close> (the read-phase
     \<open>?rposk\<close>, fixed by \<open>ktc_pos cM\<close>), not on \<open>a' = le\<close>
     \<^emph>\<open>which is false for a cut machine\<close> (it writes \<open>le\<close> off
     the boundary).  \<open>poskle\<close> is that dispatch fact, read off
     \<open>?rposk\<close> with no \<open>le_unique\<close>.  The correspondence rebuild
     needs only the \<open>ktc_pos cM k = 0 \<Rightarrow> a' k = le\<close>
     direction (\<open>a'le0\<close>, by clause-1 \<open>\<delta>LE\<close>, again no
     \<open>le_unique\<close>).\<close>
  have a'le0: "\<forall>k < k_ktm M. ktc_pos cM k = 0 \<longrightarrow> a' k = le_ktm M"
  proof (intro allI impI)
    fix k assume kN: "k < k_ktm M" and p0: "ktc_pos cM k = 0"
    have tsk0: "tsM k 0 = le_ktm M" using valcM cM_eq kN by (cases M) auto
    have "(\<lambda>j. tsM j (nM j)) k = le_ktm M" using tsk0 p0 cM_eq by simp
    thus "a' k = le_ktm M" using valid_ktm_deltaLE[OF vM mdelta] by simp
  qed
  have poskle: "\<forall>k < k_ktm M. ?rposk k = AR_AtLE \<longleftrightarrow> ktc_pos cM k = 0"
    by auto
  have tcorr_c: "\<forall>k < k_ktm M. ar_tape_correspondence (\<Gamma>_ktm M) (le_ktm M) (bl_ktm M)
                   (ktc_tape cM k) (ktc_tape c_c k)"
    using tcorr c_tape r_tape by simp
  have ppos_c: "\<forall>k < k_ktm M. ktc_pos c_c k = (if ktc_pos cM k = 0 then Suc 0
                   else sim_pos ?k (ktc_pos cM k) + ?k)"
    using c_pos r_pos by simp
  have pad_cc: "\<forall>j \<ge> k_ktm M. ktc_tape c_c j (ktc_pos c_c j) = BLANK4"
    using pad_cr c_tape c_pos by simp
  have src_cc: "ar_stage_bounded (bl_ktm M) (k_ktm M)
                  (AR_SimWrite, 0, 0, a', d, ?rposk)"
    using kpos_ktm dsupp posk0_tail by (simp add: ar_stage_bounded_def)
  \<comment> \<open>Phase 3 — write: stamp \<open>a'\<close>'s cell blocks onto the active
     tapes, landing at \<open>AR_SimAdvance\<close>; heads unchanged, the
     tape becomes the per-tape overwrite \<open>?wtape\<close>.\<close>
  let ?wtape = "\<lambda>k. if k < k_ktm M
     then (if ktc_pos cM k = 0 then ktc_tape c_c k
           else (\<lambda>pos. if sim_pos ?k (ktc_pos cM k) \<le> pos
                         \<and> pos < sim_pos ?k (ktc_pos cM k) + ?k
                      then write_bit (\<Gamma>_ktm M) (bl_ktm M) (a' k)
                             (pos - sim_pos ?k (ktc_pos cM k))
                      else ktc_tape c_c k pos))
     else ktc_tape c_c k"
  obtain c_w m_w where
      w_chain: "(c_c, c_w) \<in> (ktm_step (alphabet_reduce_delta M)) ^^ m_w"
    and w_bound: "m_w \<le> ?N * (2 * ?k)"
    and w_state: "ktc_state c_w = (q', AR_SimAdvance, k_unidx 0, 0, a', d, ?rposk)"
    and w_tape: "ktc_tape c_w = ?wtape"
    and w_pos: "ktc_pos c_w = ktc_pos c_c"
    using ar_write_phase[OF vM q'Q kge2 c_state tcorr_c ppos_c poskle a'val
                            pad_cc src_cc] ktm_run_mono [OF Int_lower1]
    by blast
  \<comment> \<open>Phase 4 setup — advance: move each active head to \<open>M\<close>'s
     new cell, landing at \<open>AR_SimNext\<close>.  \<open>dge1\<close> (no
     \<open>L\<close>-from-\<open>AR_AtLE\<close>): a head at \<open>M\<close>-position 0
     reads \<open>le\<close>, so \<open>\<delta>LE\<close>-forward forbids an
     \<open>L\<close>-move.  \<open>notLE\<close>: every walked cell of the
     write-output tape is \<open>\<noteq> LE4\<close>.\<close>
  have w_state': "ktc_state c_w = (q', AR_SimAdvance, 0, 0, a', d, ?rposk)"
    using w_state by (simp add: k_unidx_zero)
  have pad_cw: "\<forall>j \<ge> k_ktm M. ktc_tape c_w j (ktc_pos c_w j) = BLANK4"
  proof (intro allI impI)
    fix j assume jk: "k_ktm M \<le> j"
    have "ktc_tape c_w j = ktc_tape c_c j" using w_tape jk by simp
    moreover have "ktc_pos c_w j = ktc_pos c_c j" using w_pos by simp
    ultimately show "ktc_tape c_w j (ktc_pos c_w j) = BLANK4"
      using pad_cc jk by simp
  qed
  have src_cw: "ar_stage_bounded (bl_ktm M) (k_ktm M)
                  (AR_SimAdvance, 0, 0, a', d, ?rposk)"
    using kpos_ktm dsupp posk0_tail by (simp add: ar_stage_bounded_def)
  have dge1: "\<forall>k < k_ktm M. d k \<noteq> MoveR \<longrightarrow> 0 < ar_disp ?k (d k) (?rposk k)"
  proof (intro allI impI)
    fix k assume kN: "k < k_ktm M" and dkR: "d k \<noteq> MoveR"
    show "0 < ar_disp ?k (d k) (?rposk k)"
    proof (cases "ktc_pos cM k = 0")
      case True
      have nM0: "nM k = 0" using True cM_eq by simp
      have "tsM k 0 = le_ktm M" using valcM cM_eq kN by (cases M) auto
      hence "(\<lambda>j. tsM j (nM j)) k = le_ktm M" using nM0 by simp
      hence "d k \<in> {MoveN, MoveR}" using valid_ktm_deltaLE[OF vM mdelta] by simp
      hence "d k = MoveN" using dkR by auto
      moreover have "?rposk k = AR_AtLE" using True kN by simp
      ultimately show "0 < ar_disp ?k (d k) (?rposk k)" by simp
    next
      case False
      have dN_or_L: "d k = MoveN \<or> d k = MoveL" using dkR by (cases "d k") auto
      have rk: "?rposk k = AR_AtFirstProper \<or> ?rposk k = AR_AtFurtherProper"
        using False kN by auto
      from dN_or_L rk kge2 show "0 < ar_disp ?k (d k) (?rposk k)" by auto
    qed
  qed
  have notLE: "\<forall>k < k_ktm M. \<forall>m. m < ar_disp ?k (d k) (?rposk k)
                 \<longrightarrow> ktc_tape c_w k (ktc_pos c_w k - m) \<noteq> LE4"
  proof (intro allI impI)
    fix k m assume kN: "k < k_ktm M"
      and mlt: "m < ar_disp ?k (d k) (?rposk k)"
    have tcorr_ck: "ar_tape_correspondence (\<Gamma>_ktm M) (le_ktm M) (bl_ktm M)
                      (ktc_tape cM k) (ktc_tape c_c k)"
      using tcorr_c kN by blast
    have wcpos: "ktc_pos c_w k = (if ktc_pos cM k = 0 then Suc 0
                    else sim_pos ?k (ktc_pos cM k) + ?k)"
      using w_pos ppos_c kN by simp
    have wtape_notLE: "ktc_tape c_w k pos \<noteq> LE4" if pos1: "1 \<le> pos" for pos
    proof (cases "ktc_pos cM k = 0")
      case True
      have "ktc_tape c_w k pos = ktc_tape c_c k pos"
        using w_tape True kN by simp
      thus ?thesis
        using ar_tape_correspondence_not_LE4[OF tcorr_ck pos1] by simp
    next
      case False
      have wexp: "ktc_tape c_w k pos
            = (if sim_pos ?k (ktc_pos cM k) \<le> pos
                  \<and> pos < sim_pos ?k (ktc_pos cM k) + ?k
               then write_bit (\<Gamma>_ktm M) (bl_ktm M) (a' k)
                      (pos - sim_pos ?k (ktc_pos cM k))
               else ktc_tape c_c k pos)"
        using w_tape False kN by simp
      show ?thesis
      proof (cases "sim_pos ?k (ktc_pos cM k) \<le> pos
                      \<and> pos < sim_pos ?k (ktc_pos cM k) + ?k")
        case True
        have b: "pos - sim_pos ?k (ktc_pos cM k) < ?k" using True by linarith
        have "ktc_tape c_w k pos
                = write_bit (\<Gamma>_ktm M) (bl_ktm M) (a' k)
                    (pos - sim_pos ?k (ktc_pos cM k))"
          using wexp True by simp
        thus ?thesis using write_bit_not_LE4[OF b] by simp
      next
        case False
        have nreg: "\<not> (sim_pos ?k (ktc_pos cM k) \<le> pos
                        \<and> pos < sim_pos ?k (ktc_pos cM k) + ?k)"
          using False by simp
        have "ktc_tape c_w k pos = ktc_tape c_c k pos"
          using wexp by (simp add: if_not_P[OF nreg])
        thus ?thesis
          using ar_tape_correspondence_not_LE4[OF tcorr_ck pos1] by simp
      qed
    qed
    have rge: "ar_disp ?k (d k) (?rposk k) \<le> ktc_pos c_w k"
    proof (cases "ktc_pos cM k = 0")
      case True
      have "ar_disp ?k (d k) (?rposk k) \<le> Suc 0"
        using True kN by (cases "d k") auto
      thus ?thesis using wcpos True by simp
    next
      case nz: False
      show ?thesis
      proof (cases "ktc_pos cM k = 1")
        case True
        have "ar_disp ?k (d k) (?rposk k) \<le> Suc ?k"
          using True kN by (cases "d k") auto
        thus ?thesis using wcpos True by (simp add: sim_pos_def)
      next
        case False
        have p2: "2 \<le> ktc_pos cM k" using nz False by simp
        have d2: "ar_disp ?k (d k) (?rposk k) \<le> 2 * ?k"
          using nz False kN by (cases "d k") auto
        have cw_eq: "ktc_pos c_w k = (ktc_pos cM k - 1) * ?k + 1 + ?k"
          using wcpos nz by (simp add: sim_pos_def)
        have "(1::nat) \<le> ktc_pos cM k - 1" using p2 by simp
        hence "1 * ?k \<le> (ktc_pos cM k - 1) * ?k" by (rule mult_le_mono1)
        hence kk: "?k \<le> (ktc_pos cM k - 1) * ?k" by (simp only: mult_1_left)
        have "2 * ?k \<le> ktc_pos c_w k" using kk cw_eq by linarith
        thus ?thesis using d2 by linarith
      qed
    qed
    have "m < ktc_pos c_w k" using mlt rge by simp
    hence "1 \<le> ktc_pos c_w k - m" by simp
    thus "ktc_tape c_w k (ktc_pos c_w k - m) \<noteq> LE4" by (rule wtape_notLE)
  qed
  let ?aposk = "\<lambda>k. if k < k_ktm M then ar_newpos (d k) (?rposk k) else ?rposk k"
  let ?apos = "\<lambda>k. if k < k_ktm M
                    then (if d k = MoveR then ktc_pos c_w k
                          else ktc_pos c_w k - ar_disp ?k (d k) (?rposk k))
                    else ktc_pos c_w k"
  obtain c_adv m_a where
      a_chain: "(c_w, c_adv) \<in> (ktm_step (alphabet_reduce_delta M)) ^^ m_a"
    and a_bound: "m_a \<le> ?N * (2 * ?k)"
    and a_state: "ktc_state c_adv = (q', AR_SimNext, k_unidx 0, 0, a', d, ?aposk)"
    and a_tape: "ktc_tape c_adv = ktc_tape c_w"
    and a_pos: "ktc_pos c_adv = ?apos"
    using ar_advance_phase[OF vM q'Q kge2 w_state' a'val dge1 notLE pad_cw src_cw]
          ktm_run_mono [OF Int_lower1]
    by blast
  \<comment> \<open>Phase 5 setup — next hand-off: destination-stage validity, the
     folded read \<open>\<rightarrow>\<close> advance prefix chain with its bound, and
     the advance-exit padding-blank / bounded-stage facts.\<close>
  have st_cM1: "ktc_state cM_1 = q'" using q'_eq by simp
  have vsrc_n: "ar_valid_stage (\<Gamma>_ktm M) (bl_ktm M)
                  (AR_SimNext, k_unidx 0, 0, a', d, ?aposk)"
    using kge2 a'val by (auto simp: ar_valid_stage_def)
  have rc: "(c', c_c) \<in> (ktm_step (alphabet_reduce_delta M)) ^^ Suc m_r"
    using r_chain c_step by (rule relpow_Suc_I)
  have rcw: "(c', c_w)
               \<in> (ktm_step (alphabet_reduce_delta M)) ^^ (Suc m_r + m_w)"
    by (subst relpow_add) (rule relcompI[OF rc w_chain])
  have rcwa: "(c', c_adv)
                \<in> (ktm_step (alphabet_reduce_delta M))
                     ^^ (Suc m_r + m_w + m_a)"
    by (subst relpow_add) (rule relcompI[OF rcw a_chain])
  have dist: "?N * (5 * ?k + 2)
                = ?N * (?k + 2) + ?N * (2 * ?k) + ?N * (2 * ?k)"
    by (simp add: algebra_simps)
  have pre_bound: "Suc m_r + m_w + m_a \<le> ?N * (5 * ?k + 2) + 1"
    using r_bound w_bound a_bound dist by linarith
  \<comment> \<open>Padding heads sit at position 0: \<open>posk0\<close>'s tail is
     \<open>AR_AtLE\<close>, so \<open>pkok\<close> reads off \<open>ktc_pos cM j = 0\<close>.\<close>
  have padpos0: "\<forall>j \<ge> k_ktm M. ktc_pos cM j = 0"
    using pkok posk0_tail by blast
  have pad_cadv: "\<forall>j \<ge> k_ktm M. ktc_tape c_adv j (ktc_pos c_adv j) = BLANK4"
  proof (intro allI impI)
    fix j assume jk: "k_ktm M \<le> j"
    have "ktc_pos c_adv j = ktc_pos c_w j" using a_pos jk by simp
    moreover have "ktc_tape c_adv j = ktc_tape c_w j" using a_tape by simp
    ultimately show "ktc_tape c_adv j (ktc_pos c_adv j) = BLANK4"
      using pad_cw jk by simp
  qed
  have src_cadv: "ar_stage_bounded (bl_ktm M) (k_ktm M)
                    (AR_SimNext, k_unidx 0, 0, a', d, ?aposk)"
    using kpos_ktm dsupp posk0_tail
    by (simp add: ar_stage_bounded_def k_unidx_zero)
  have src_read: "ar_stage_bounded (bl_ktm M) (k_ktm M)
                    (AR_SimRead, 0, 0, a', d, ?aposk)"
    using kpos_ktm dsupp posk0_tail by (simp add: ar_stage_bounded_def)
  \<comment> \<open>\<open>M\<close>'s post-step head position, and the no-\<open>L\<close>-from-0
     discipline (active tapes only).\<close>
  have posM1: "ktc_pos cM_1 k = go_move (d k) (ktc_pos cM k)" for k
    using cM1_eq cM_eq by simp
  have dposL: "d k \<noteq> MoveL" if p0: "ktc_pos cM k = 0" and kN: "k < k_ktm M" for k
  proof -
    have nM0: "nM k = 0" using p0 cM_eq by simp
    have "tsM k 0 = le_ktm M" using valcM cM_eq kN by (cases M) auto
    hence "(\<lambda>j. tsM j (nM j)) k = le_ktm M" using nM0 by simp
    hence "d k \<in> {MoveN, MoveR}" using valid_ktm_deltaLE[OF vM mdelta] by simp
    thus "d k \<noteq> MoveL" by auto
  qed
  \<comment> \<open>The tape correspondence re-established at \<open>cM_1\<close> (forward
     simulation core): on active tapes via \<open>ar_write_tape_correspondence\<close>.\<close>
  have cM1tape: "ktc_tape cM_1 k = (ktc_tape cM k)(ktc_pos cM k := a' k)" for k
    using cM1_eq cM_eq by simp
  have wt_def: "ktc_tape c_adv k pos
        = (if ktc_pos cM k = 0 then ktc_tape c' k pos
           else if sim_pos ?k (ktc_pos cM k) \<le> pos
                   \<and> pos < sim_pos ?k (ktc_pos cM k) + ?k
                then write_bit (\<Gamma>_ktm M) (bl_ktm M) (a' k)
                       (pos - sim_pos ?k (ktc_pos cM k))
                else ktc_tape c' k pos)" for k pos
  proof (cases "k < k_ktm M")
    case True
    thus ?thesis using a_tape w_tape c_tape r_tape by simp
  next
    case False
    hence kge: "k_ktm M \<le> k" by simp
    have p0: "ktc_pos cM k = 0" using padpos0 kge by blast
    have "ktc_tape c_adv k = ktc_tape c' k"
      using a_tape w_tape c_tape r_tape kge by simp
    thus ?thesis using p0 by simp
  qed
  have tcorr_1: "\<forall>k < k_ktm M. ar_tape_correspondence (\<Gamma>_ktm M) (le_ktm M) (bl_ktm M)
                   (ktc_tape cM_1 k) (ktc_tape c_adv k)"
  proof (intro allI impI)
    fix k assume kN: "k < k_ktm M"
    show "ar_tape_correspondence (\<Gamma>_ktm M) (le_ktm M) (bl_ktm M)
            (ktc_tape cM_1 k) (ktc_tape c_adv k)"
      by (rule ar_write_tape_correspondence
                [OF kge2 kN tcorr cM1tape a'le0 wt_def])
  qed
  \<comment> \<open>Head position and \<open>posk\<close> consistency at \<open>cM_1\<close>: on
     active tapes via the advance helpers; on padding (\<open>d k = N\<close>,
     head at 0) both reduce to the entry config.\<close>
  have apos_1: "ktc_pos c_adv k = sim_pos ?k (ktc_pos cM_1 k)" for k
  proof (cases "k < k_ktm M")
    case kN: True
    have key: "(if d k = MoveR
                 then (if ktc_pos cM k = 0 then Suc 0
                       else sim_pos ?k (ktc_pos cM k) + ?k)
                 else (if ktc_pos cM k = 0 then Suc 0
                       else sim_pos ?k (ktc_pos cM k) + ?k)
                        - ar_disp ?k (d k)
                            (if ktc_pos cM k = 0 then AR_AtLE
                             else if ktc_pos cM k = 1 then AR_AtFirstProper
                             else AR_AtFurtherProper))
               = sim_pos ?k (go_move (d k) (ktc_pos cM k))"
    proof (rule ar_advance_newsimpos)
      show "2 \<le> ?k" by (rule kge2)
      show "ktc_pos cM k = 0 \<Longrightarrow> d k \<noteq> MoveL" using dposL kN by blast
    qed
    have c_adv_pos: "ktc_pos c_adv k = (if d k = MoveR
                 then (if ktc_pos cM k = 0 then Suc 0
                       else sim_pos ?k (ktc_pos cM k) + ?k)
                 else (if ktc_pos cM k = 0 then Suc 0
                       else sim_pos ?k (ktc_pos cM k) + ?k)
                        - ar_disp ?k (d k)
                            (if ktc_pos cM k = 0 then AR_AtLE
                             else if ktc_pos cM k = 1 then AR_AtFirstProper
                             else AR_AtFurtherProper))"
      using a_pos w_pos c_pos r_pos kN by simp
    show ?thesis by (simp add: c_adv_pos key posM1)
  next
    case False
    hence kge: "k_ktm M \<le> k" by simp
    have dN: "d k = MoveN" using dsupp kge by blast
    have "ktc_pos c_adv k = ktc_pos c' k"
      using a_pos w_pos c_pos r_pos kge by simp
    also have "\<dots> = sim_pos ?k (ktc_pos cM k)" using ppos0 by simp
    also have "\<dots> = sim_pos ?k (ktc_pos cM_1 k)" using posM1 dN by simp
    finally show ?thesis .
  qed
  have aposk_1: "?aposk k = AR_AtLE \<longleftrightarrow> ktc_pos cM_1 k = 0" for k
  proof (cases "k < k_ktm M")
    case kN: True
    have key: "(ar_newpos (d k) (if ktc_pos cM k = 0 then AR_AtLE
                  else if ktc_pos cM k = 1 then AR_AtFirstProper
                  else AR_AtFurtherProper) = AR_AtLE)
               \<longleftrightarrow> go_move (d k) (ktc_pos cM k) = 0"
    proof (rule ar_newpos_atLE_iff)
      show "ktc_pos cM k = 0 \<Longrightarrow> d k \<noteq> MoveL" using dposL kN by blast
    qed
    have aposk_k: "?aposk k = ar_newpos (d k)
                     (if ktc_pos cM k = 0 then AR_AtLE
                      else if ktc_pos cM k = 1 then AR_AtFirstProper
                      else AR_AtFurtherProper)"
      using kN by simp
    show ?thesis by (simp add: aposk_k key posM1)
  next
    case False
    hence kge: "k_ktm M \<le> k" by simp
    have dN: "d k = MoveN" using dsupp kge by blast
    have p0: "ktc_pos cM k = 0" using padpos0 kge by blast
    have "ktc_pos cM_1 k = 0" using posM1 dN p0 by simp
    moreover have pk0: "posk0 k = AR_AtLE" using posk0_tail kge by blast
    moreover have "?aposk k = posk0 k" using kge by simp
    ultimately show ?thesis by simp
  qed
  \<comment> \<open>Three-way dispatch on the post-step \<open>M\<close>-state \<open>q'\<close>:
     accept / reject (terminal hand-off) or continue (next
     \<open>AR_SimRead\<close> boundary).  Each appends one \<open>M'\<close>-step within
     bound and re-establishes the three invariants.\<close>
  consider (acc) "q' = t_ktm M" | (rej) "q' = r_ktm M"
    | (cont) "q' \<noteq> t_ktm M" "q' \<noteq> r_ktm M"
    by blast
  then show thesis
  proof cases
    case acc
    obtain c'' where
        acc_step: "(c_adv, c'') \<in> ktm_step (alphabet_reduce_delta M)"
      and acc_state: "ktc_state c'' = (t_ktm M, ar_accept_stage (bl_ktm M))"
      and acc_tape: "ktc_tape c'' = ktc_tape c_adv"
      and acc_pos: "ktc_pos c'' = ktc_pos c_adv"
      using ar_accept_step[OF vM a_state acc vsrc_n pad_cadv src_cadv] by blast
    show thesis
    proof (rule that[of "Suc (Suc m_r + m_w + m_a)" c''])
      show "Suc (Suc m_r + m_w + m_a) \<le> k_ktm M * (5 * ?k + 2) + 2"
        using pre_bound by linarith
      show "(c', c'') \<in> (ktm_step (alphabet_reduce_delta M))
              ^^ Suc (Suc m_r + m_w + m_a)"
        using rcwa acc_step by (rule relpow_Suc_I)
      show "ar_simulates M cM_1 c''"
        by (simp add: ar_simulates_def Let_def acc_state ar_accept_stage_def
                      st_cM1 acc tcorr_1 acc_tape)
      show "ar_posk_consistent M cM_1 c''"
        by (simp add: ar_posk_consistent_def acc_state ar_accept_stage_def)
      show "ar_at_read_boundary M c''"
        by (simp add: ar_at_read_boundary_def acc_state ar_accept_stage_def
                      acc_tape acc_pos pad_cadv)
    qed
  next
    case rej
    obtain c'' where
        rej_step: "(c_adv, c'') \<in> ktm_step (alphabet_reduce_delta M)"
      and rej_state: "ktc_state c'' = (r_ktm M, ar_reject_stage (bl_ktm M))"
      and rej_tape: "ktc_tape c'' = ktc_tape c_adv"
      and rej_pos: "ktc_pos c'' = ktc_pos c_adv"
      using ar_reject_step[OF vM a_state rej vsrc_n pad_cadv src_cadv] by blast
    show thesis
    proof (rule that[of "Suc (Suc m_r + m_w + m_a)" c''])
      show "Suc (Suc m_r + m_w + m_a) \<le> k_ktm M * (5 * ?k + 2) + 2"
        using pre_bound by linarith
      show "(c', c'') \<in> (ktm_step (alphabet_reduce_delta M))
              ^^ Suc (Suc m_r + m_w + m_a)"
        using rcwa rej_step by (rule relpow_Suc_I)
      show "ar_simulates M cM_1 c''"
        by (simp add: ar_simulates_def Let_def rej_state ar_reject_stage_def
                      st_cM1 rej tcorr_1 rej_tape)
      show "ar_posk_consistent M cM_1 c''"
        by (simp add: ar_posk_consistent_def rej_state ar_reject_stage_def)
      show "ar_at_read_boundary M c''"
        by (simp add: ar_at_read_boundary_def rej_state ar_reject_stage_def
                      rej_tape rej_pos pad_cadv)
    qed
  next
    case cont
    obtain c'' where
        nxt_step: "(c_adv, c'') \<in> ktm_step (alphabet_reduce_delta M)"
      and nxt_state: "ktc_state c'' = (q', AR_SimRead, 0, 0, a', d, ?aposk)"
      and nxt_tape: "ktc_tape c'' = ktc_tape c_adv"
      and nxt_pos: "ktc_pos c'' = ktc_pos c_adv"
      using ar_next_step[OF vM a_state q'Q cont(1) cont(2) vsrc_n
                            pad_cadv src_cadv] by blast
    show thesis
    proof (rule that[of "Suc (Suc m_r + m_w + m_a)" c''])
      show "Suc (Suc m_r + m_w + m_a) \<le> k_ktm M * (5 * ?k + 2) + 2"
        using pre_bound by linarith
      show "(c', c'') \<in> (ktm_step (alphabet_reduce_delta M))
              ^^ Suc (Suc m_r + m_w + m_a)"
        using rcwa nxt_step by (rule relpow_Suc_I)
      show "ar_simulates M cM_1 c''"
        by (simp add: ar_simulates_def Let_def nxt_state nxt_tape nxt_pos
                      st_cM1 cont tcorr_1 apos_1)
      show "ar_posk_consistent M cM_1 c''"
        by (simp add: ar_posk_consistent_def nxt_state nxt_pos aposk_1)
      show "ar_at_read_boundary M c''"
        by (simp add: ar_at_read_boundary_def nxt_state nxt_tape nxt_pos
                      a'G pad_cadv src_read)
    qed
  qed
qed

text \<open>Chunked-induction engine for the simulation phase, the
  AR analogue of AE's \<open>ae_simulation_phase_chunked\<close>.  Given an
  accepting \<open>M\<close>-path of length \<open>n\<close> from a reachable \<open>cM\<close>
  with a paired \<open>AR_SimRead\<close> \<open>M'\<close>-config \<open>c'\<close> satisfying
  \<open>ar_simulates\<close>, exhibit a corresponding accepting
  \<open>M'\<close>-path of length at most \<open>(5b + 2) \<cdot> n\<close> ending in the
  canonical accept config.  Unlike AE — which groups \<open>c\<close> source
  steps per stage and needs the strong \<open>less_induct\<close> with
  \<open>min n c\<close> chunk arithmetic — AR simulates one \<open>M\<close>-step per
  phase, so ordinary \<open>induction n\<close> with the fixed per-step
  bound suffices: each step contributes \<open>\<le> 5b + 2\<close>, summing to
  \<open>(5b + 2) \<cdot> n\<close> by a single \<open>linarith\<close>.  All substrate
  reasoning is delegated to \<open>ar_simulates_forward_step\<close>; the
  engine only splits the trace, recurses on the tail, and composes
  the two \<open>M'\<close>-paths via \<open>relpow_add\<close>.\<close>

lemma ar_simulation_phase_chunked:
  fixes M :: "('q, 'a) ktm"
    and w :: "'a list"
    and cM cM_final :: "('a, 'q) ktc_config"
    and c' :: "(sym4, 'q \<times> 'a ar_stage) ktc_config"
    and n :: nat
  assumes vM:      "valid_ktm M"
      and w_sub:   "set w \<subseteq> Sigma_ktm M"
      and card_ge: "card (\<Gamma>_ktm M) \<ge> 4"
      and reach_M: "(init_config_ktm M w, cM) \<in> (ktm_step (delta_ktm M))\<^sup>*"
      and trace:   "(cM, cM_final) \<in> (ktm_step (delta_ktm M))^^n"
      and accept:  "ktc_state cM_final = t_ktm M"
      and sim:     "ar_simulates M cM c'"
      and posk_ok: "ar_posk_consistent M cM c'"
      and rbnd:    "ar_at_read_boundary M c'"
      and lebl:    "le_ktm M \<noteq> bl_ktm M"
  shows "\<exists>m c''. m \<le> (k_ktm M
                          * (5 * block_width (\<Gamma>_ktm M) + 2) + 2) * n
              \<and> (c', c'') \<in> (ktm_step (alphabet_reduce_delta M))^^m
              \<and> ktc_state c'' = (t_ktm M, ar_accept_stage (bl_ktm M))"
  using reach_M trace sim posk_ok rbnd
proof (induction n arbitrary: cM c')
  case 0
  \<comment> \<open>Base case: a length-\<open>0\<close> trace forces \<open>cM = cM_final\<close>, so
      \<open>cM\<close> accepts; \<open>ar_simulates_accept_iff\<close> pins \<open>c'\<close> to the
      canonical accept config.  Witness \<open>m = 0\<close>, \<open>c'' = c'\<close>.\<close>
  have cMf: "cM = cM_final" using "0.prems"(2) by simp
  have "ktc_state cM = t_ktm M" using accept cMf by simp
  hence state_c': "ktc_state c' = (t_ktm M, ar_accept_stage (bl_ktm M))"
    using ar_simulates_accept_iff[OF vM "0.prems"(3)] by simp
  have run0: "(c', c') \<in> (ktm_step (alphabet_reduce_delta M))^^0" by simp
  have bound0: "(0::nat) \<le> (5 * block_width (\<Gamma>_ktm M) + 2) * 0" by simp
  show ?case using state_c' run0 bound0 by blast
next
  case (Suc n')
  \<comment> \<open>Inductive case: split off the first \<open>M\<close>-step
      \<open>cM \<rightarrow> cM\<^sub>1\<close>, run \<open>ar_simulates_forward_step\<close> for its
      \<open>M'\<close>-phase \<open>c' \<rightarrow>p c8\<close> (\<open>p \<le> 5b + 2\<close>), extend
      reachability to \<open>cM\<^sub>1\<close>, recurse on the length-\<open>n'\<close> tail,
      and compose.\<close>
  obtain cM_1 where
      step1: "(cM, cM_1) \<in> ktm_step (delta_ktm M)"
    and rest: "(cM_1, cM_final) \<in> ktm_step (delta_ktm M) ^^ n'"
    using relpow_Suc_D2[OF Suc.prems(2)] by blast
  obtain p c8 where
      pbound: "p \<le> k_ktm M * (5 * block_width (\<Gamma>_ktm M) + 2) + 2"
    and chainp: "(c', c8) \<in> ktm_step (alphabet_reduce_delta M) ^^ p"
    and sim8: "ar_simulates M cM_1 c8"
    and posk8: "ar_posk_consistent M cM_1 c8"
    and bnd8: "ar_at_read_boundary M c8"
    by (rule ar_simulates_forward_step
              [OF vM w_sub card_ge Suc.prems(1) step1
                  Suc.prems(3) Suc.prems(4) Suc.prems(5) lebl])
  have reach1: "(init_config_ktm M w, cM_1) \<in> (ktm_step (delta_ktm M))\<^sup>*"
    using Suc.prems(1) step1 by (rule rtrancl_into_rtrancl)
  obtain m_rec c'' where
      mbound: "m_rec \<le> (k_ktm M
                          * (5 * block_width (\<Gamma>_ktm M) + 2) + 2) * n'"
    and chainrec: "(c8, c'') \<in> (ktm_step (alphabet_reduce_delta M))^^m_rec"
    and statec'': "ktc_state c'' = (t_ktm M, ar_accept_stage (bl_ktm M))"
    using Suc.IH[OF reach1 rest sim8 posk8 bnd8] by blast
  have chain: "(c', c'') \<in> (ktm_step (alphabet_reduce_delta M))^^(p + m_rec)"
    using chainp chainrec by (auto simp: relpow_add)
  have bound: "p + m_rec \<le> (k_ktm M
                              * (5 * block_width (\<Gamma>_ktm M) + 2) + 2) * Suc n'"
  proof -
    have "p + m_rec \<le> (k_ktm M * (5 * block_width (\<Gamma>_ktm M) + 2) + 2)
                        + (k_ktm M
                            * (5 * block_width (\<Gamma>_ktm M) + 2) + 2) * n'"
      using pbound mbound by linarith
    also have "\<dots> = (k_ktm M
                       * (5 * block_width (\<Gamma>_ktm M) + 2) + 2) * Suc n'" by simp
    finally show ?thesis .
  qed
  show ?case using bound chain statec'' by blast
qed

end
