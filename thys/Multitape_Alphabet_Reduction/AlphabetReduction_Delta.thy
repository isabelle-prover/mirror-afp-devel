theory AlphabetReduction_Delta
  imports AlphabetReduction_Stage
begin

subsection \<open>Substep transition relations\<close>

text \<open>The output machine's \<open>\<delta>'\<close> is defined as a
  union of five per-substep transition relations, mirroring
  AE's \<open>alphabet_enlarge_delta\<close> shape.  Each substep
  relation is a set of substrate-shape 5-tuples
  \<open>((q, stg), a, (q', stg'), a', d)\<close> where
  \<open>q\<close> ranges over \<open>Q_tm M\<close>, \<open>stg\<close>
  over \<open>'a ar_stage\<close>, \<open>a\<close> /
  \<open>a'\<close> over \<open>nat \<Rightarrow> sym4\<close>, and
  \<open>d\<close> over \<open>nat \<Rightarrow> dir\<close>.  The five substep
  relations are defined below, one per simulation phase.

  No validation cluster: AR's language theorem is quantified
  over encoder-image inputs only, so non-canonical sym4 inputs
  are outside the theorem's scope and M''s behaviour on them is
  unconstrained.

  The union is intersected with two global restrictions:
  LE-preservation (no transition forges \<open>LE4\<close> out of
  a non-\<open>LE4\<close> cell, matching the substrate's
  \<open>\<delta>LE\<close> invariant) and
  \<open>ar_valid_stage\<close>-membership on both source and
  target stages (matching the non-product \<open>Q'\<close> shape).
  Throughout, \<open>b\<close> abbreviates \<open>block_width \<Gamma>\<close> (the per-symbol cell width).\<close>

definition ar_delta_read ::
  "('q, 'a) mttm
    \<Rightarrow> (('q \<times> 'a ar_stage)
        \<times> (nat \<Rightarrow> sym4)
        \<times> ('q \<times> 'a ar_stage)
        \<times> (nat \<Rightarrow> sym4)
        \<times> (nat \<Rightarrow> dir)) set" where
  "ar_delta_read M =
    \<comment> \<open>LE-arm, non-last tape: head at position 0
       reads \<open>LE4\<close>, sets \<open>buf tk := le_tm M\<close>
       directly (no accumulator needed for the single
       LE-cell), advances \<open>R\<close> on \<open>tk\<close> to
       position 1, and transitions to the next tape's read.
       \<open>posk tk\<close> stays \<open>AR_AtLE\<close>
       throughout this substep — \<open>SimAdvance\<close> will
       update it later when the head leaves the LE region.\<close>
    {((q, AR_SimRead, tk, 0, buf, dvec, posk), a,
       (q, AR_SimRead, k_succ tk, 0,
        buf(tk := le_tm M), dvec, posk), a, d) |
     q tk buf dvec posk a d.
       q \<in> Q_tm M
       \<and> \<not> is_last_k M tk
       \<and> posk tk = AR_AtLE
       \<and> a tk = LE4
       \<and> d = (\<lambda>kk. if kk = tk then dir.R else dir.N)}
    \<union>
    \<comment> \<open>LE-arm, last tape: same single-substep
       LE-read, transitions to \<open>AR_SimCompute\<close>
       instead of the next tape.\<close>
    {((q, AR_SimRead, tk, 0, buf, dvec, posk), a,
       (q, AR_SimCompute, k_unidx 0, 0,
        buf(tk := le_tm M), dvec, posk), a, d) |
     q tk buf dvec posk a d.
       q \<in> Q_tm M
       \<and> is_last_k M tk
       \<and> posk tk = AR_AtLE
       \<and> a tk = LE4
       \<and> d = (\<lambda>kk. if kk = tk then dir.R else dir.N)}
    \<union>
    \<comment> \<open>Proper-arm look-back step 1
       (\<open>i = 0\<close>): head at \<open>sim_pos(p)\<close>
       moves \<open>L\<close> on \<open>tk\<close> to
       \<open>sim_pos(p) - 1\<close>.  The cell at
       \<open>sim_pos(p)\<close> is some \<open>BIT0\<close> /
       \<open>BIT1\<close> / \<open>BLANK4\<close> (not
       \<open>LE4\<close>; enforced as a \<open>\<delta>LE\<close>
       precondition).  Buf, posk, dvec unchanged; substep
       transitions to \<open>i = 1\<close>.\<close>
    {((q, AR_SimRead, tk, 0, buf, dvec, posk), a,
       (q, AR_SimRead, tk, Suc 0, buf, dvec, posk), a, d) |
     q tk buf dvec posk a d.
       q \<in> Q_tm M
       \<and> posk tk \<in> {AR_AtFirstProper, AR_AtFurtherProper}
       \<and> a tk \<noteq> LE4
       \<and> d = (\<lambda>kk. if kk = tk then dir.L else dir.N)}
    \<union>
    \<comment> \<open>Proper-arm look-back step 2
       (\<open>i = 1\<close>): head at \<open>sim_pos(p) - 1\<close>
       reads the cell there; if \<open>LE4\<close>, the head was
       at \<open>sim_pos 1 = 1\<close> in the previous step so
       refine \<open>posk tk := AR_AtFirstProper\<close>;
       otherwise refine to \<open>AR_AtFurtherProper\<close>.
       Reset \<open>buf tk := gamma_unenum \<Gamma> bl 0\<close>
       (the partial-decoded ``\<open>0\<close> bits read so far''
       symbol) to prepare for the per-bit accumulator below.
       \<open>R\<close>-move back to \<open>sim_pos(p)\<close>;
       \<open>\<delta>LE\<close> with \<open>a tk = LE4\<close> is
       fine because the direction is \<open>R\<close>.
       Transitions to \<open>i = 2\<close>.\<close>
    {((q, AR_SimRead, tk, Suc 0, buf, dvec, posk), a,
       (q, AR_SimRead, tk, Suc (Suc 0),
        buf(tk := gamma_unenum (\<Gamma>_tm M) (bl_tm M) 0),
        dvec,
        posk(tk := if a tk = LE4 then AR_AtFirstProper
                                  else AR_AtFurtherProper)), a, d) |
     q tk buf dvec posk a d.
       q \<in> Q_tm M
       \<and> posk tk \<in> {AR_AtFirstProper, AR_AtFurtherProper}
       \<and> d = (\<lambda>kk. if kk = tk then dir.R else dir.N)}
    \<union>
    \<comment> \<open>Proper-arm per-bit stepping
       (\<open>2 \<le> i \<le> b\<close>): head at
       \<open>sim_pos(p) + (i - 2)\<close>, read cell, accumulate
       \<open>bit_value\<close> into the partial-decoded
       \<open>buf tk\<close> via the \<open>gamma_enum\<close>
       /\<open>gamma_unenum\<close> roundtrip
       \<open>partial' = 2 \<cdot> gamma_enum (buf tk) +
       bit_value (a tk)\<close>, \<open>buf' tk :=
       gamma_unenum partial'\<close>.  \<open>R\<close>-move on
       \<open>tk\<close>.  Transitions to \<open>i + 1\<close>
       within \<open>AR_SimRead\<close>; the next per-bit
       substep continues the accumulator chain.\<close>
    {((q, AR_SimRead, tk, i, buf, dvec, posk), a,
       (q, AR_SimRead, tk, Suc i,
        buf(tk := gamma_unenum (\<Gamma>_tm M) (bl_tm M)
                    (2 * gamma_enum (\<Gamma>_tm M) (bl_tm M) (buf tk)
                       + bit_value (a tk))),
        dvec, posk), a, d) |
     q tk i buf dvec posk a d.
       q \<in> Q_tm M
       \<and> posk tk \<in> {AR_AtFirstProper, AR_AtFurtherProper}
       \<and> 2 \<le> i
       \<and> Suc i \<le> Suc (block_width (\<Gamma>_tm M))
       \<and> d = (\<lambda>kk. if kk = tk then dir.R else dir.N)}
    \<union>
    \<comment> \<open>Proper-arm per-bit boundary
       (\<open>i = Suc (b)\<close>), non-last tape:
       same accumulator step as above on the last bit
       (\<open>j = b - 1\<close>), \<open>buf' tk\<close> holds the
       fully-decoded \<open>M\<close>-symbol (\<open>\<in>
       \<Gamma>\<close> for valid encoder images; falls back to
       \<open>bl_tm M\<close> for non-encoder inputs), then
       transitions to the same phase on \<open>k_succ tk\<close>
       with bit-counter reset to \<open>0\<close>.\<close>
    {((q, AR_SimRead, tk, i, buf, dvec, posk), a,
       (q, AR_SimRead, k_succ tk, 0,
        buf(tk := gamma_unenum (\<Gamma>_tm M) (bl_tm M)
                    (2 * gamma_enum (\<Gamma>_tm M) (bl_tm M) (buf tk)
                       + bit_value (a tk))),
        dvec, posk), a, d) |
     q tk i buf dvec posk a d.
       q \<in> Q_tm M
       \<and> \<not> is_last_k M tk
       \<and> posk tk \<in> {AR_AtFirstProper, AR_AtFurtherProper}
       \<and> i = Suc (block_width (\<Gamma>_tm M))
       \<and> d = (\<lambda>kk. if kk = tk then dir.R else dir.N)}
    \<union>
    \<comment> \<open>Proper-arm per-bit boundary, last tape: same
       last-bit accumulator step, transitions to
       \<open>AR_SimCompute\<close> with current-tape reset to
       \<open>k_unidx 0\<close>.\<close>
    {((q, AR_SimRead, tk, i, buf, dvec, posk), a,
       (q, AR_SimCompute, k_unidx 0, 0,
        buf(tk := gamma_unenum (\<Gamma>_tm M) (bl_tm M)
                    (2 * gamma_enum (\<Gamma>_tm M) (bl_tm M) (buf tk)
                       + bit_value (a tk))),
        dvec, posk), a, d) |
     q tk i buf dvec posk a d.
       q \<in> Q_tm M
       \<and> is_last_k M tk
       \<and> posk tk \<in> {AR_AtFirstProper, AR_AtFurtherProper}
       \<and> i = Suc (block_width (\<Gamma>_tm M))
       \<and> d = (\<lambda>kk. if kk = tk then dir.R else dir.N)}"

definition ar_delta_compute ::
  "('q, 'a) mttm
    \<Rightarrow> (('q \<times> 'a ar_stage)
        \<times> (nat \<Rightarrow> sym4)
        \<times> ('q \<times> 'a ar_stage)
        \<times> (nat \<Rightarrow> sym4)
        \<times> (nat \<Rightarrow> dir)) set" where
  "ar_delta_compute M =
    {((q, AR_SimCompute, tk, i, buf, dvec, posk), a,
       (q', AR_SimWrite, 0, 0, m_a', m_d, posk), a, d) |
     q buf q' m_a' m_d tk i dvec posk a d.
       (q, buf, q', m_a', m_d) \<in> delta_tm M
       \<and> d = (\<lambda>_. dir.N)}"
  \<comment> \<open>One \<open>\<delta>'\<close>-tuple per \<open>M\<close>'s
     \<open>\<delta>\<close>-tuple.  Matches the source-stage \<open>buf\<close>
     field (the decoded per-tape symbol vector, produced by
     \<open>AR_SimRead\<close>) against the M-side read symbol
     vector of the \<open>M\<close>-\<open>\<delta>\<close>-tuple
     \<open>(q, buf, q', m_a', m_d)\<close>, and threads the M-side
     output: new M-state \<open>q'\<close>, write-back vector
     \<open>m_a'\<close> (next phase's per-tape symbols to encode),
     and direction-vector \<open>m_d\<close> (consumed by
     \<open>AR_SimAdvance\<close>).  The substrate-side read \<open>a\<close>
     and write \<open>a' = a\<close> are unconstrained at this
     substep (no head moves, no writes); direction is constant
     \<open>N\<close>.  The per-tape \<open>posk\<close> carries
     through unchanged (head positions don't change during
     compute).  No halt-state shortcut: M-side halt detection
     is centralised at \<open>ar_delta_next\<close>'s three-arm
     dispatch.\<close>

definition ar_delta_write ::
  "('q, 'a) mttm
    \<Rightarrow> (('q \<times> 'a ar_stage)
        \<times> (nat \<Rightarrow> sym4)
        \<times> ('q \<times> 'a ar_stage)
        \<times> (nat \<Rightarrow> sym4)
        \<times> (nat \<Rightarrow> dir)) set" where
  "ar_delta_write M =
    \<comment> \<open>LE-arm, non-last tape: \<open>posk tk = AR_AtLE\<close>
       means tape \<open>tk\<close>'s head sits on the reduced boundary
       (\<open>sim_pos 0 = 0\<close>), whose \<open>LE4\<close> cell need not be
       rewritten (\<open>\<delta>LE\<close> requires writing \<open>le\<close>
       back, which is exactly the present cell).  Keyed on the
       position-kind flag, not on \<open>buf tk = le_tm M\<close>, so a
       source machine that writes \<open>le\<close> off the boundary (a tape
       cut) is handled by the proper arm below, as ordinary data.
       Skip the per-tape write phase entirely: single substep with
       all directions \<open>N\<close>, transitioning to the same phase on
       the next tape with bit-counter still at \<open>0\<close>.\<close>
    {((q, AR_SimWrite, tk, 0, buf, dvec, posk), a,
       (q, AR_SimWrite, k_succ tk, 0, buf, dvec, posk), a, d) |
     q tk buf dvec posk a d.
       q \<in> Q_tm M
       \<and> posk tk = AR_AtLE
       \<and> \<not> is_last_k M tk
       \<and> d = (\<lambda>_. dir.N)}
    \<union>
    \<comment> \<open>LE-arm, last tape: transitions to
       \<open>AR_SimAdvance\<close> with the current-tape index
       reset to \<open>k_unidx 0\<close>.\<close>
    {((q, AR_SimWrite, tk, 0, buf, dvec, posk), a,
       (q, AR_SimAdvance, k_unidx 0, 0, buf, dvec, posk), a, d) |
     q tk buf dvec posk a d.
       q \<in> Q_tm M
       \<and> posk tk = AR_AtLE
       \<and> is_last_k M tk
       \<and> d = (\<lambda>_. dir.N)}
    \<union>
    \<comment> \<open>Proper-arm, back-walk phase
       (\<open>0 \<le> i < b\<close>): head moves
       \<open>L\<close> on \<open>tk\<close>, \<open>N\<close>
       elsewhere; no writes.  At \<open>i = b - 1\<close> the
       substep transitions to \<open>i = b\<close>, starting the
       forward-write phase below.  Both phases share the
       \<open>AR_SimWrite\<close> substep tag; the bit-counter
       distinguishes them.  \<open>a tk \<noteq> LE4\<close>
       enforced for \<open>\<delta>LE\<close>.\<close>
    {((q, AR_SimWrite, tk, i, buf, dvec, posk), a,
       (q, AR_SimWrite, tk, Suc i, buf, dvec, posk), a, d) |
     q tk i buf dvec posk a d.
       q \<in> Q_tm M
       \<and> posk tk \<noteq> AR_AtLE
       \<and> a tk \<noteq> LE4
       \<and> Suc i \<le> block_width (\<Gamma>_tm M)
       \<and> d = (\<lambda>kk. if kk = tk then dir.L else dir.N)}
    \<union>
    \<comment> \<open>Proper-arm, forward-write stepping phase
       (\<open>b \<le> i < 2b - 1\<close>): write
       \<open>write_bit \<Gamma> bl (buf tk) (i - b)\<close> at
       \<open>tk\<close>, \<open>R\<close> on \<open>tk\<close>,
       \<open>N\<close> elsewhere.  All other tapes have their
       cells preserved.  The bit-counter advances; the next
       substep continues forward-write.\<close>
    {((q, AR_SimWrite, tk, i, buf, dvec, posk), a,
       (q, AR_SimWrite, tk, Suc i, buf, dvec, posk), a', d) |
     q tk i buf dvec posk a a' d.
       q \<in> Q_tm M
       \<and> posk tk \<noteq> AR_AtLE
       \<and> block_width (\<Gamma>_tm M) \<le> i
       \<and> Suc i < 2 * block_width (\<Gamma>_tm M)
       \<and> a' = (\<lambda>kk. if kk = tk
                       then write_bit (\<Gamma>_tm M) (bl_tm M)
                                       (buf tk)
                                       (i - block_width (\<Gamma>_tm M))
                       else a kk)
       \<and> d = (\<lambda>kk. if kk = tk then dir.R else dir.N)}
    \<union>
    \<comment> \<open>Proper-arm, forward-write boundary
       (\<open>Suc i = 2b\<close>), non-last tape: last cell of
       \<open>cell_repr (buf tk)\<close> is written, head moves
       \<open>R\<close> on \<open>tk\<close>, transitions to the
       same phase on \<open>k_succ tk\<close> with bit-counter
       reset.  Cells on other tapes preserved.\<close>
    {((q, AR_SimWrite, tk, i, buf, dvec, posk), a,
       (q, AR_SimWrite, k_succ tk, 0, buf, dvec, posk), a', d) |
     q tk i buf dvec posk a a' d.
       q \<in> Q_tm M
       \<and> posk tk \<noteq> AR_AtLE
       \<and> \<not> is_last_k M tk
       \<and> Suc i = 2 * block_width (\<Gamma>_tm M)
       \<and> a' = (\<lambda>kk. if kk = tk
                       then write_bit (\<Gamma>_tm M) (bl_tm M)
                                       (buf tk)
                                       (i - block_width (\<Gamma>_tm M))
                       else a kk)
       \<and> d = (\<lambda>kk. if kk = tk then dir.R else dir.N)}
    \<union>
    \<comment> \<open>Proper-arm, forward-write boundary, last tape:
       same last-cell write as above, transitions to
       \<open>AR_SimAdvance\<close> with the current-tape index
       reset to \<open>k_unidx 0\<close>.\<close>
    {((q, AR_SimWrite, tk, i, buf, dvec, posk), a,
       (q, AR_SimAdvance, k_unidx 0, 0, buf, dvec, posk), a', d) |
     q tk i buf dvec posk a a' d.
       q \<in> Q_tm M
       \<and> posk tk \<noteq> AR_AtLE
       \<and> is_last_k M tk
       \<and> Suc i = 2 * block_width (\<Gamma>_tm M)
       \<and> a' = (\<lambda>kk. if kk = tk
                       then write_bit (\<Gamma>_tm M) (bl_tm M)
                                       (buf tk)
                                       (i - block_width (\<Gamma>_tm M))
                       else a kk)
       \<and> d = (\<lambda>kk. if kk = tk then dir.R else dir.N)}"

definition ar_delta_advance ::
  "('q, 'a) mttm
    \<Rightarrow> (('q \<times> 'a ar_stage)
        \<times> (nat \<Rightarrow> sym4)
        \<times> ('q \<times> 'a ar_stage)
        \<times> (nat \<Rightarrow> sym4)
        \<times> (nat \<Rightarrow> dir)) set" where
  "ar_delta_advance M =
    \<comment> \<open>Stepping arm: head moves \<open>L\<close> on tape
       \<open>tk\<close>, \<open>N\<close> elsewhere; stays in
       \<open>AR_SimAdvance\<close> with the bit-counter
       advanced.  Active when \<open>Suc i\<close> is strictly
       below the per-tape displacement
       \<open>ar_disp b (dvec tk) (posk tk)\<close>; the
       \<open>R\<close>- and \<open>L\<close>-from-\<open>AR_AtLE\<close>
       cases have displacement \<open>0\<close>, so no stepping
       tuple fires; for \<open>N\<close>-from-\<open>AR_AtLE\<close>
       the displacement is \<open>1\<close>, so stepping never
       fires and the single substep goes through one of the
       boundary arms.  The read symbol on \<open>tk\<close> must
       not be \<open>LE4\<close> (\<open>\<delta>LE\<close>: an
       \<open>L\<close>-move from a tape reading \<open>LE4\<close>
       is forbidden).\<close>
    {((q, AR_SimAdvance, tk, i, buf, dvec, posk), a,
       (q, AR_SimAdvance, tk, Suc i, buf, dvec, posk), a, d) |
     q tk i buf dvec posk a d.
       q \<in> Q_tm M
       \<and> a tk \<noteq> LE4
       \<and> Suc i < ar_disp (block_width (\<Gamma>_tm M)) (dvec tk) (posk tk)
       \<and> d = (\<lambda>kk. if kk = tk then dir.L else dir.N)}
    \<union>
    \<comment> \<open>Boundary arm, non-last tape.  Two firing
       sub-cases: the \<open>R\<close>-direction case (zero
       displacement, no \<open>L\<close>-move; \<open>i = 0\<close>
       and the entire direction vector is \<open>N\<close>), and
       the non-\<open>R\<close> case at \<open>Suc i\<close> equal to
       the displacement (one last \<open>L\<close>-move on
       \<open>tk\<close>; \<open>a tk \<noteq> LE4\<close> enforced for
       \<open>\<delta>LE\<close>).  Both sub-cases transition to
       the same phase on the next tape \<open>k_succ tk\<close>
       (bit-counter reset to \<open>0\<close>) with
       \<open>posk tk\<close> updated by \<open>ar_newpos\<close>;
       all other tapes' \<open>posk\<close> entries are
       preserved.\<close>
    {((q, AR_SimAdvance, tk, i, buf, dvec, posk), a,
       (q, AR_SimAdvance, k_succ tk, 0, buf, dvec,
        posk(tk := ar_newpos (dvec tk) (posk tk))), a, d) |
     q tk i buf dvec posk a d.
       q \<in> Q_tm M
       \<and> \<not> is_last_k M tk
       \<and> ((dvec tk = dir.R \<and> i = 0)
          \<or> (dvec tk \<noteq> dir.R
              \<and> a tk \<noteq> LE4
              \<and> Suc i = ar_disp (block_width (\<Gamma>_tm M))
                                  (dvec tk) (posk tk)))
       \<and> d = (\<lambda>kk. if kk = tk \<and> dvec tk \<noteq> dir.R
                      then dir.L else dir.N)}
    \<union>
    \<comment> \<open>Boundary arm, last tape.  Same firing
       sub-cases as the non-last-tape arm; transitions to
       \<open>AR_SimNext\<close> instead of advancing
       \<open>tk\<close>.  The current-tape field is reset to
       \<open>k_unidx 0\<close> (the first tape in the
       enumeration; matches \<open>AR_SimNext\<close>'s starting
       convention and the next \<open>AR_SimRead\<close>'s
       initial tape).\<close>
    {((q, AR_SimAdvance, tk, i, buf, dvec, posk), a,
       (q, AR_SimNext, k_unidx 0, 0, buf, dvec,
        posk(tk := ar_newpos (dvec tk) (posk tk))), a, d) |
     q tk i buf dvec posk a d.
       q \<in> Q_tm M
       \<and> is_last_k M tk
       \<and> ((dvec tk = dir.R \<and> i = 0)
          \<or> (dvec tk \<noteq> dir.R
              \<and> a tk \<noteq> LE4
              \<and> Suc i = ar_disp (block_width (\<Gamma>_tm M))
                                  (dvec tk) (posk tk)))
       \<and> d = (\<lambda>kk. if kk = tk \<and> dvec tk \<noteq> dir.R
                      then dir.L else dir.N)}"

definition ar_delta_next ::
  "('q, 'a) mttm
    \<Rightarrow> (('q \<times> 'a ar_stage)
        \<times> (nat \<Rightarrow> sym4)
        \<times> ('q \<times> 'a ar_stage)
        \<times> (nat \<Rightarrow> sym4)
        \<times> (nat \<Rightarrow> dir)) set" where
  "ar_delta_next M =
    {((q, AR_SimNext, tk, i, buf, dvec, posk), a,
       (q, AR_SimRead, 0, 0, buf, dvec, posk), a, d) |
     q tk i buf dvec posk a d.
       q \<in> Q_tm M \<and> q \<noteq> t_tm M \<and> q \<noteq> r_tm M
       \<and> d = (\<lambda>_. dir.N)}
    \<union>
    {((q, AR_SimNext, tk, i, buf, dvec, posk), a,
       (q, AR_HaltAccept, 0, 0,
        (\<lambda>_. bl_tm M), (\<lambda>_. dir.N), (\<lambda>_. AR_AtLE)), a, d) |
     q tk i buf dvec posk a d.
       q = t_tm M
       \<and> d = (\<lambda>_. dir.N)}
    \<union>
    {((q, AR_SimNext, tk, i, buf, dvec, posk), a,
       (q, AR_HaltReject, 0, 0,
        (\<lambda>_. bl_tm M), (\<lambda>_. dir.N), (\<lambda>_. AR_AtLE)), a, d) |
     q tk i buf dvec posk a d.
       q = r_tm M
       \<and> d = (\<lambda>_. dir.N)}"
  \<comment> \<open>End-of-M-step handshake.  Three arms dispatch on the
     M-state \<open>q\<close>: non-terminal routes to
     \<open>AR_SimRead\<close> for the next M-step (with bit-counter
     and current-tape both reset to 0); \<open>q = t_tm M\<close>
     routes to the canonical accept stage; \<open>q = r_tm M\<close>
     routes to the canonical reject stage.  The non-terminal
     arm preserves \<open>buf\<close>, the direction-vector field
     \<open>dvec\<close> (residual from the just-completed M-step; no
     longer consulted), and the per-tape position-kind
     \<open>posk\<close> (carries the head-region across M-steps so the
     next \<open>AR_SimRead\<close>'s LE-vs-proper dispatch sees the
     correct value).  The two terminal arms instead reset
     \<open>buf\<close> / \<open>dvec\<close> / \<open>posk\<close> to the canonical
     halt values (\<open>\<lambda>_. bl_tm M\<close> / \<open>\<lambda>_.
     dir.N\<close> / \<open>\<lambda>_. AR_AtLE\<close>), so the target stage
     is exactly \<open>ar_accept_stage (bl_tm M)\<close> /
     \<open>ar_reject_stage (bl_tm M)\<close> and the handshake lands
     on \<open>M'\<close>'s halt state \<open>t_tm M'\<close> / \<open>r_tm
     M'\<close>.  \<open>Lang_mttm\<close> matches the full \<open>mt_state\<close>
     (tape and heads free), so this canonical landing is what
     makes \<open>M'\<close> acceptance / rejection detectable; the reset
     is semantically free (the residual fields are never read
     after halting).  The direction vector is all \<open>N\<close>
     (no head moves at the handshake); cell vectors
     \<open>a' = a\<close> (no writes), so LE-preservation passes
     trivially.\<close>

text \<open>The output machine's full transition relation: union of
  the five per-substep relations, intersected with three global
  restrictions — \<open>\<delta>LE\<close>-backward (no transition forges
  \<open>LE4\<close> out of a non-\<open>LE4\<close> cell),
  \<open>\<delta>LE\<close>-forward (every transition reading \<open>LE4\<close>
  on tape \<open>k\<close> rewrites \<open>LE4\<close> back on the same tape
  and moves \<open>N\<close> or \<open>R\<close>), and
  \<open>ar_valid_stage\<close>-membership on both source and target
  stages.  The two \<open>\<delta>LE\<close> filters together discharge
  the substrate's bidirectional \<open>\<delta>LE\<close> invariant
  uniformly — without per-arm \<open>a tk \<noteq> LE4\<close>
  preconditions on every arm that performs a write distinct from
  the read cell (proper-arm forward-write in particular).  The
  per-arm \<open>a tk \<noteq> LE4\<close> constraints that do appear (in
  look-back step 1, back-walk, and advance L-step) reflect the
  simulation invariant rather than the bare \<open>\<delta>LE\<close>
  requirement: those arms move \<open>L\<close> on the current tape,
  which the substrate forbids from an \<open>LE4\<close> cell
  regardless of write content.\<close>

definition alphabet_reduce_delta ::
  "('q, 'a) mttm
    \<Rightarrow> (('q \<times> 'a ar_stage)
        \<times> (nat \<Rightarrow> sym4)
        \<times> ('q \<times> 'a ar_stage)
        \<times> (nat \<Rightarrow> sym4)
        \<times> (nat \<Rightarrow> dir)) set" where
  "alphabet_reduce_delta M =
     (ar_delta_read M \<union> ar_delta_compute M
        \<union> ar_delta_write M \<union> ar_delta_advance M
        \<union> ar_delta_next M)
     \<inter> {(s, a, s', a', d).
           \<forall>k. a' k = LE4 \<longrightarrow> a k = LE4}
     \<inter> {(s, a, s', a', d).
           \<forall>k. a k = LE4 \<longrightarrow> a' k = LE4 \<and> d k \<in> {dir.N, dir.R}}
     \<inter> {(s, a, s', a', d).
           ar_valid_stage (\<Gamma>_tm M) (bl_tm M) (snd s)
           \<and> ar_valid_stage (\<Gamma>_tm M) (bl_tm M) (snd s')}
     \<inter> {(s, a, s', a', d).
           \<forall>j \<ge> k_tm M. a j = BLANK4 \<and> a' j = BLANK4 \<and> d j = dir.N}
     \<inter> {(s, a, s', a', d).
           ar_stage_bounded (bl_tm M) (k_tm M) (snd s)
           \<and> ar_stage_bounded (bl_tm M) (k_tm M) (snd s')}"


text \<open>Initial / halt stages used to populate the output
  machine's \<open>s'\<close> / \<open>t'\<close> / \<open>r'\<close>
  components.  All three share the same shape: substep-counter
  \<open>i = 0\<close>, current-tape \<open>0\<close>
  placeholder (per-tape phase fields are inactive in
  \<open>AR_SimRead\<close>'s initial entry and inactive in halt
  states), per-tape \<open>buf\<close> initialised to
  \<open>bl\<close> (any value in \<open>\<Gamma> \<union> \<lbrace>bl\<rbrace>\<close> would
  satisfy \<open>ar_valid_stage\<close>; \<open>bl\<close> is the
  canonical placeholder), per-tape direction-vector
  \<open>dir.N\<close> (irrelevant outside \<open>AR_SimAdvance\<close>),
  per-tape position-kind \<open>AR_AtLE\<close> (the initial
  head position is \<open>0\<close>; for halt states the field is
  vestigial).  The three stages differ only in their
  \<open>ar_substep_idx\<close> tag.\<close>

definition ar_init_stage ::
  "'a \<Rightarrow> 'a ar_stage" where
  "ar_init_stage bl =
     (AR_SimRead, 0, 0, (\<lambda>_. bl), (\<lambda>_. dir.N), (\<lambda>_. AR_AtLE))"

definition ar_accept_stage ::
  "'a \<Rightarrow> 'a ar_stage" where
  "ar_accept_stage bl =
     (AR_HaltAccept, 0, 0, (\<lambda>_. bl), (\<lambda>_. dir.N), (\<lambda>_. AR_AtLE))"

definition ar_reject_stage ::
  "'a \<Rightarrow> 'a ar_stage" where
  "ar_reject_stage bl =
     (AR_HaltReject, 0, 0, (\<lambda>_. bl), (\<lambda>_. dir.N), (\<lambda>_. AR_AtLE))"

text \<open>Positivity of the block width: \<open>b\<close> is bounded below
  by \<open>1\<close> via the \<open>max\<close> on the right-hand side.  Used
  below to discharge the \<open>i < 2 \<cdot> b\<close> conjunct of
  \<open>ar_valid_stage\<close> at \<open>i = 0\<close>, and downstream by
  the per-substep step-count lemmas.\<close>

lemma block_width_pos: "1 \<le> block_width \<Gamma>"
  unfolding block_width_def by simp

text \<open>The three stage constants used to populate \<open>s'\<close>,
  \<open>t'\<close>, and \<open>r'\<close> all satisfy
  \<open>ar_valid_stage \<Gamma> bl\<close> for any \<open>\<Gamma>\<close>
  and \<open>bl\<close>: the bit-counter is \<open>0 < 2 \<cdot> b\<close>
  (since \<open>b \<ge> 1\<close>) and the buf field is constantly
  \<open>bl \<in> \<Gamma> \<union> \<lbrace>bl\<rbrace>\<close>.\<close>

lemma ar_valid_stage_init: "ar_valid_stage \<Gamma> bl (ar_init_stage bl)"
proof -
  have "(0 :: nat) < 2 * block_width \<Gamma>" using block_width_pos[of \<Gamma>] by linarith
  thus ?thesis
    unfolding ar_valid_stage_def ar_init_stage_def by simp
qed

lemma ar_valid_stage_accept: "ar_valid_stage \<Gamma> bl (ar_accept_stage bl)"
proof -
  have "(0 :: nat) < 2 * block_width \<Gamma>" using block_width_pos[of \<Gamma>] by linarith
  thus ?thesis
    unfolding ar_valid_stage_def ar_accept_stage_def by simp
qed

lemma ar_valid_stage_reject: "ar_valid_stage \<Gamma> bl (ar_reject_stage bl)"
proof -
  have "(0 :: nat) < 2 * block_width \<Gamma>" using block_width_pos[of \<Gamma>] by linarith
  thus ?thesis
    unfolding ar_valid_stage_def ar_reject_stage_def by simp
qed


text \<open>The alphabet-reduction combinator.  Input: \<open>mttm\<close> over
  \<open>'a\<close>, with tape alphabet \<open>\<Gamma>_tm M\<close> a finite subset of
  \<open>'a\<close> (via \<open>valid_mttm\<close>) of cardinality \<open>\<ge> 4\<close>.
  Output: \<open>mttm\<close> over \<open>sym4\<close>, with state set
  \<open>'q \<times> 'a ar_stage\<close>.  Tape count \<open>k_tm M\<close> is preserved.

  Output components:
  \<^item> \<open>Q'\<close> = \<open>Q_M \<times> \<lbrace>stg. ar_valid_stage \<Gamma>_M bl_M stg\<rbrace>\<close>
    (the non-product Q-shape);
  \<^item> \<open>\<Sigma>'\<close> = \<open>\<lbrace>BIT0, BIT1\<rbrace>\<close>
    (the encoded input alphabet);
  \<^item> \<open>\<Gamma>'\<close> = \<open>UNIV :: sym4 set\<close>
    (all four cell shapes — BIT0, BIT1, BLANK4, LE4);
  \<^item> \<open>bl'\<close> = \<open>BLANK4\<close>, \<open>le'\<close> = \<open>LE4\<close>;
  \<^item> \<open>\<delta>'\<close> = \<open>alphabet_reduce_delta M\<close>
    (the five-substep union under the global LE-preservation
    and \<open>ar_valid_stage\<close> filters);
  \<^item> \<open>s'\<close> = \<open>(s_M, ar_init_stage bl_M)\<close>,
    \<open>t'\<close> = \<open>(t_M, ar_accept_stage bl_M)\<close>,
    \<open>r'\<close> = \<open>(r_M, ar_reject_stage bl_M)\<close>
    (M's start / accept / reject states paired with the
    matching \<open>ar_substep_idx\<close> tag).\<close>

definition alphabet_reduce ::
  "('q, 'a) mttm
    \<Rightarrow> ('q \<times> 'a ar_stage, sym4) mttm"
  where
    "alphabet_reduce M =
       (case M of MTTM Q_M _ \<Gamma>_M bl_M _ _ s_M t_M r_M k_M \<Rightarrow>
          MTTM (Q_M \<times> {stg. ar_valid_stage \<Gamma>_M bl_M stg
                              \<and> ar_stage_bounded bl_M k_M stg})
               {BIT0, BIT1}
               (UNIV :: sym4 set)
               BLANK4
               LE4
               (alphabet_reduce_delta M)
               (s_M, ar_init_stage bl_M)
               (t_M, ar_accept_stage bl_M)
               (r_M, ar_reject_stage bl_M)
               k_M)"

text \<open>Projection-simp lemmas for the reduced machine: each
  structural accessor reads straight off the \<open>MTTM\<close> the
  combinator builds.  Marked \<open>[simp]\<close> so the language and
  time proofs never re-derive them via \<open>cases M\<close>; the
  accept-state projection in particular is the bridge that makes
  the simulation engine's terminal state syntactically equal to
  \<open>t_tm (alphabet_reduce M)\<close>.\<close>

lemma alphabet_reduce_Sigma [simp]:
  "Sigma_tm (alphabet_reduce M) = {BIT0, BIT1}"
  by (cases M) (simp add: alphabet_reduce_def)

lemma alphabet_reduce_Gamma [simp]:
  "\<Gamma>_tm (alphabet_reduce M) = (UNIV :: sym4 set)"
  by (cases M) (simp add: alphabet_reduce_def)

lemma alphabet_reduce_bl [simp]:
  "bl_tm (alphabet_reduce M) = BLANK4"
  by (cases M) (simp add: alphabet_reduce_def)

lemma alphabet_reduce_le [simp]:
  "le_tm (alphabet_reduce M) = LE4"
  by (cases M) (simp add: alphabet_reduce_def)

lemma alphabet_reduce_start [simp]:
  "s_tm (alphabet_reduce M) = (s_tm M, ar_init_stage (bl_tm M))"
  by (cases M) (simp add: alphabet_reduce_def)

lemma alphabet_reduce_accept [simp]:
  "t_tm (alphabet_reduce M) = (t_tm M, ar_accept_stage (bl_tm M))"
  by (cases M) (simp add: alphabet_reduce_def)

lemma alphabet_reduce_reject [simp]:
  "r_tm (alphabet_reduce M) = (r_tm M, ar_reject_stage (bl_tm M))"
  by (cases M) (simp add: alphabet_reduce_def)

lemma alphabet_reduce_delta [simp]:
  "delta_tm (alphabet_reduce M) = alphabet_reduce_delta M"
  by (cases M) (simp add: alphabet_reduce_def)

end
