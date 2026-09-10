theory Multitape_Origin_Float
  imports Multitape_Substrate
begin

section \<open>Origin floating: an unreachable left prefix is invisible\<close>

text \<open>A machine that has planted a fresh left endmarker at some cell
  \<open>d\<close> can never read the cells to its left: the left-endmarker discipline
  (clause 1, @{thm[source] valid_mttm_deltaLE}) forbids a leftward move
  off \<open>le\<close>, so the head is penned in the semi-tape \<open>[d, \<infinity>)\<close>.  The
  content below \<open>d\<close> is therefore dead weight.  This theory makes that
  precise as a per-tape left \<^emph>\<open>shift\<close> relation and shows the substrate
  step relation translates across it in both directions.

  The intended use is origin floating on a singly-infinite tape: to
  reuse a spent input tape as a blank work tape without the linear
  rewind, a machine plants \<open>le\<close> at the current head cell \<open>d\<close> and treats
  \<open>d\<close> as the new origin.  The tape from \<open>d\<close> onward (\<open>le\<close> then blanks)
  is then indistinguishable from a fresh blank tape whose origin sits
  at cell 0 --- which is exactly a shift by \<open>d\<close>.

  \<^bold>\<open>Not a bisimulation.\<close>  The machines here may be nondeterministic, so
  the two step relations are \<^emph>\<open>not\<close> bisimilar (their successor sets do
  not correspond).  Each single-step lemma below translates \<^emph>\<open>one\<close>
  transition; chained along a path it carries a single witnessing run
  from one origin to the other, which is all that language inclusion
  needs.  The forward and reverse lemmas together give inclusion in
  both directions --- never a claim that the run trees match.\<close>

subsection \<open>The per-tape left-shift relation\<close>

text \<open>\<open>shift_rel d c1 c2\<close>: configuration \<open>c2\<close> is \<open>c1\<close> with each tape
  \<open>k\<close> shifted right by \<open>d k\<close> cells.  The state agrees, every head sits
  \<open>d k\<close> cells further right, and every cell of \<open>c1\<close> reappears \<open>d k\<close>
  cells further right in \<open>c2\<close>.  The cells of \<open>c2\<close> below \<open>d k\<close> are
  unconstrained --- that is the discarded prefix.  Setting \<open>d k = 0\<close>
  leaves tape \<open>k\<close> untouched, so a single-tape float is the instance
  \<open>d = (\<lambda>j. if j = k0 then off else 0)\<close>.\<close>

definition shift_rel ::
  "(nat \<Rightarrow> nat) \<Rightarrow> ('a, 'q) mt_config \<Rightarrow> ('a, 'q) mt_config \<Rightarrow> bool" where
  "shift_rel d c1 c2 \<longleftrightarrow>
     mt_state c2 = mt_state c1
     \<and> (\<forall>k. mt_pos c2 k = mt_pos c1 k + d k)
     \<and> (\<forall>k p. mt_tape c2 k (p + d k) = mt_tape c1 k p)"

lemma shift_rel_state:
  "shift_rel d c1 c2 \<Longrightarrow> mt_state c2 = mt_state c1"
  by (simp add: shift_rel_def)

subsection \<open>Single-step translation, both directions\<close>

text \<open>Forward: a step of \<open>M\<close> from the base config \<open>c1\<close> lifts to a step
  from the shifted config \<open>c2\<close>, landing in the shift of the base
  successor.  The one delicate point is the head position at a floated
  origin: were the head at cell 0 of a floated tape (\<open>d k > 0\<close>) to move
  left, the base clamps at 0 while the shift lands at \<open>d k - 1\<close>,
  breaking sync.  But cell 0 of the base carries \<open>le\<close> (hypothesis
  \<open>le0\<close>), so clause 1 forbids that leftward move.  \<open>le0\<close> is required only
  on the \<^emph>\<open>floated\<close> tapes (\<open>d k \<noteq> 0\<close>): where \<open>d k = 0\<close> the shift is the
  identity and a leftward move at cell 0 stays in sync, so no \<open>le\<close> is
  needed there.  This matters when the base is a lift with all-blank
  out-of-range tapes (no \<open>le\<close> at their cell 0): those tapes are never
  floated, so \<open>le0\<close> does not constrain them.  On the floated tapes \<open>le0\<close>
  holds of every configuration reachable from an initial one
  (@{thm[source] valid_reach_LE_pos0_mttm}).\<close>

lemma mttm_step_shift_forward:
  fixes M :: "('q, 'a) mttm"
  assumes vM:   "valid_mttm M"
    and le0:    "\<forall>k. d k \<noteq> 0 \<longrightarrow> mt_tape c1 k 0 = le_tm M"
    and rel:    "shift_rel d c1 c2"
    and step:   "(c1, c1') \<in> mttm_step (delta_tm M)"
  shows "\<exists>c2'. (c2, c2') \<in> mttm_step (delta_tm M) \<and> shift_rel d c1' c2'"
proof -
  from step obtain q ts1 n1 q' a dr where
      c1_eq:  "c1 = Config\<^sub>M q ts1 n1"
    and c1'_eq: "c1' = Config\<^sub>M q' (\<lambda>k. (ts1 k)(n1 k := a k))
                                    (\<lambda>k. go_dir (dr k) (n1 k))"
    and tr:   "(q, \<lambda>k. ts1 k (n1 k), q', a, dr) \<in> delta_tm M"
    by (auto elim: mttm_step.cases)
  obtain sc ts2 n2 where c2_eq: "c2 = Config\<^sub>M sc ts2 n2"
    by (cases c2) auto
  have unpacked:
    "sc = q \<and> (\<forall>k. n2 k = n1 k + d k) \<and> (\<forall>k p. ts2 k (p + d k) = ts1 k p)"
    using rel by (simp add: shift_rel_def c1_eq c2_eq)
  from unpacked have st2:  "sc = q" by simp
  from unpacked have pos2: "\<And>k. n2 k = n1 k + d k" by simp
  from unpacked have tape2: "\<And>k p. ts2 k (p + d k) = ts1 k p" by simp
  \<comment> \<open>Reads match: the shifted head reads what the base head reads.\<close>
  have read_eq: "(\<lambda>k. ts2 k (n2 k)) = (\<lambda>k. ts1 k (n1 k))"
  proof
    fix k
    have "ts2 k (n2 k) = ts2 k (n1 k + d k)" using pos2 by simp
    also have "\<dots> = ts1 k (n1 k)" using tape2 by simp
    finally show "ts2 k (n2 k) = ts1 k (n1 k)" .
  qed
  have tr2: "(q, \<lambda>k. ts2 k (n2 k), q', a, dr) \<in> delta_tm M"
    using tr read_eq by simp
  let ?c2' = "Config\<^sub>M q' (\<lambda>k. (ts2 k)(n2 k := a k))
                          (\<lambda>k. go_dir (dr k) (n2 k))"
  have step2: "(c2, ?c2') \<in> mttm_step (delta_tm M)"
    unfolding c2_eq st2 by (rule mttm_step.step, rule tr2)
  \<comment> \<open>No leftward move at a floated origin: reading \<open>le\<close> forbids \<open>L\<close>.
     Only floated tapes (\<open>d k \<noteq> 0\<close>) need this; unfloated ones stay in
     sync regardless.\<close>
  have no_L_at0: "\<And>k. d k \<noteq> 0 \<Longrightarrow> n1 k = 0 \<Longrightarrow> dr k \<noteq> dir.L"
  proof -
    fix k assume dk: "d k \<noteq> 0" and nk0: "n1 k = 0"
    have "(\<lambda>k. ts1 k (n1 k)) k = le_tm M" using le0 dk nk0 c1_eq by simp
    from valid_mttm_deltaLE[OF vM tr this] show "dr k \<noteq> dir.L" by auto
  qed
  have pos_sync: "\<And>k. go_dir (dr k) (n2 k) = go_dir (dr k) (n1 k) + d k"
  proof -
    fix k
    show "go_dir (dr k) (n2 k) = go_dir (dr k) (n1 k) + d k"
    proof (cases "dr k")
      case N thus ?thesis using pos2 by simp
    next
      case R thus ?thesis using pos2 by simp
    next
      case L
      show ?thesis
      proof (cases "d k = 0")
        case True thus ?thesis using L pos2 by simp
      next
        case False
        hence "n1 k \<noteq> 0" using no_L_at0 L by blast
        then obtain m where "n1 k = Suc m" by (cases "n1 k") auto
        thus ?thesis using L pos2 by simp
      qed
    qed
  qed
  have tape_sync:
    "\<And>k p. ((ts2 k)(n2 k := a k)) (p + d k) = ((ts1 k)(n1 k := a k)) p"
  proof -
    fix k p
    show "((ts2 k)(n2 k := a k)) (p + d k) = ((ts1 k)(n1 k := a k)) p"
    proof (cases "p = n1 k")
      case True
      hence "p + d k = n2 k" using pos2 by simp
      thus ?thesis using True by simp
    next
      case False
      hence "p + d k \<noteq> n2 k" using pos2 by simp
      thus ?thesis using False tape2 by simp
    qed
  qed
  have rel': "shift_rel d c1' ?c2'"
    unfolding shift_rel_def c1'_eq using pos_sync tape_sync by simp
  from step2 rel' show ?thesis by blast
qed

text \<open>Reverse: a step of \<open>M\<close> from the shifted config \<open>c2\<close> descends to a
  step from the base config \<open>c1\<close>.  The transition witnessing the \<open>c2\<close>
  step reads exactly what \<open>c1\<close>'s head reads (the shift relation), so the
  same transition fires from \<open>c1\<close>; the boundary argument is identical
  (\<open>le\<close> at the base origin forbids the desyncing leftward move).\<close>

lemma mttm_step_shift_reverse:
  fixes M :: "('q, 'a) mttm"
  assumes vM:   "valid_mttm M"
    and le0:    "\<forall>k. d k \<noteq> 0 \<longrightarrow> mt_tape c1 k 0 = le_tm M"
    and rel:    "shift_rel d c1 c2"
    and step:   "(c2, c2') \<in> mttm_step (delta_tm M)"
  shows "\<exists>c1'. (c1, c1') \<in> mttm_step (delta_tm M) \<and> shift_rel d c1' c2'"
proof -
  obtain q ts1 n1 where c1_eq: "c1 = Config\<^sub>M q ts1 n1"
    by (cases c1) auto
  from step obtain sc ts2 n2 q' a dr where
      c2_eq:  "c2 = Config\<^sub>M sc ts2 n2"
    and c2'_eq: "c2' = Config\<^sub>M q' (\<lambda>k. (ts2 k)(n2 k := a k))
                                    (\<lambda>k. go_dir (dr k) (n2 k))"
    and tr:   "(sc, \<lambda>k. ts2 k (n2 k), q', a, dr) \<in> delta_tm M"
    by (auto elim: mttm_step.cases)
  have unpacked:
    "sc = q \<and> (\<forall>k. n2 k = n1 k + d k) \<and> (\<forall>k p. ts2 k (p + d k) = ts1 k p)"
    using rel by (simp add: shift_rel_def c1_eq c2_eq)
  from unpacked have st2:  "sc = q" by simp
  from unpacked have pos2: "\<And>k. n2 k = n1 k + d k" by simp
  from unpacked have tape2: "\<And>k p. ts2 k (p + d k) = ts1 k p" by simp
  \<comment> \<open>The witnessing transition reads what the base head reads.\<close>
  have read_eq: "(\<lambda>k. ts2 k (n2 k)) = (\<lambda>k. ts1 k (n1 k))"
  proof
    fix k
    have "ts2 k (n2 k) = ts2 k (n1 k + d k)" using pos2 by simp
    also have "\<dots> = ts1 k (n1 k)" using tape2 by simp
    finally show "ts2 k (n2 k) = ts1 k (n1 k)" .
  qed
  have tr1: "(q, \<lambda>k. ts1 k (n1 k), q', a, dr) \<in> delta_tm M"
    using tr read_eq st2 by simp
  let ?c1' = "Config\<^sub>M q' (\<lambda>k. (ts1 k)(n1 k := a k))
                          (\<lambda>k. go_dir (dr k) (n1 k))"
  have step1: "(c1, ?c1') \<in> mttm_step (delta_tm M)"
    unfolding c1_eq by (rule mttm_step.step, rule tr1)
  have no_L_at0: "\<And>k. d k \<noteq> 0 \<Longrightarrow> n1 k = 0 \<Longrightarrow> dr k \<noteq> dir.L"
  proof -
    fix k assume dk: "d k \<noteq> 0" and nk0: "n1 k = 0"
    have "(\<lambda>k. ts1 k (n1 k)) k = le_tm M" using le0 dk nk0 c1_eq by simp
    from valid_mttm_deltaLE[OF vM tr1 this] show "dr k \<noteq> dir.L" by auto
  qed
  have pos_sync: "\<And>k. go_dir (dr k) (n2 k) = go_dir (dr k) (n1 k) + d k"
  proof -
    fix k
    show "go_dir (dr k) (n2 k) = go_dir (dr k) (n1 k) + d k"
    proof (cases "dr k")
      case N thus ?thesis using pos2 by simp
    next
      case R thus ?thesis using pos2 by simp
    next
      case L
      show ?thesis
      proof (cases "d k = 0")
        case True thus ?thesis using L pos2 by simp
      next
        case False
        hence "n1 k \<noteq> 0" using no_L_at0 L by blast
        then obtain m where "n1 k = Suc m" by (cases "n1 k") auto
        thus ?thesis using L pos2 by simp
      qed
    qed
  qed
  have tape_sync:
    "\<And>k p. ((ts2 k)(n2 k := a k)) (p + d k) = ((ts1 k)(n1 k := a k)) p"
  proof -
    fix k p
    show "((ts2 k)(n2 k := a k)) (p + d k) = ((ts1 k)(n1 k := a k)) p"
    proof (cases "p = n1 k")
      case True
      hence "p + d k = n2 k" using pos2 by simp
      thus ?thesis using True by simp
    next
      case False
      hence "p + d k \<noteq> n2 k" using pos2 by simp
      thus ?thesis using False tape2 by simp
    qed
  qed
  have rel': "shift_rel d ?c1' c2'"
    unfolding shift_rel_def c2'_eq using pos_sync tape_sync by simp
  from step1 rel' show ?thesis by blast
qed

subsection \<open>Path translation, both directions\<close>

text \<open>Chaining the single-step lemmas along a path.  The \<open>le\<close>-at-0
  invariant is re-established at each intermediate configuration by
  @{thm[source] mttm_step_LE_pos0_preserve}, so the same base config
  hypothesis \<open>le0\<close> drives the whole chain.  These translate \<^emph>\<open>one\<close>
  path of length \<open>n\<close>; there is no claim that the base and shifted
  machines have matching successor sets.\<close>

lemma mttm_relpow_shift_forward:
  fixes M :: "('q, 'a) mttm"
  assumes vM: "valid_mttm M"
  shows "\<lbrakk> \<forall>k. d k \<noteq> 0 \<longrightarrow> mt_tape c1 k 0 = le_tm M; shift_rel d c1 c2;
           (c1, c1') \<in> (mttm_step (delta_tm M)) ^^ n \<rbrakk>
         \<Longrightarrow> \<exists>c2'. (c2, c2') \<in> (mttm_step (delta_tm M)) ^^ n
                   \<and> shift_rel d c1' c2'"
proof (induction n arbitrary: c1 c2 c1')
  case 0
  then show ?case by auto
next
  case (Suc n)
  from Suc.prems(3) obtain cmid where
      first: "(c1, cmid) \<in> mttm_step (delta_tm M)"
    and rest: "(cmid, c1') \<in> (mttm_step (delta_tm M)) ^^ n"
    by (blast dest: relpow_Suc_D2)
  obtain cmid2 where
      first2:  "(c2, cmid2) \<in> mttm_step (delta_tm M)"
    and rel_mid: "shift_rel d cmid cmid2"
    using mttm_step_shift_forward[OF vM Suc.prems(1) Suc.prems(2) first] by blast
  have le0_mid: "\<forall>k. d k \<noteq> 0 \<longrightarrow> mt_tape cmid k 0 = le_tm M"
  proof (intro allI impI)
    fix k assume "d k \<noteq> 0"
    have "mt_tape c1 k 0 = le_tm M" using Suc.prems(1) \<open>d k \<noteq> 0\<close> by blast
    from mttm_step_LE_pos0_preserve[OF vM first this]
    show "mt_tape cmid k 0 = le_tm M" .
  qed
  from Suc.IH[OF le0_mid rel_mid rest] obtain c2' where
      tail2:   "(cmid2, c2') \<in> (mttm_step (delta_tm M)) ^^ n"
    and rel_end: "shift_rel d c1' c2'"
    by blast
  have "(c2, c2') \<in> (mttm_step (delta_tm M)) ^^ (Suc n)"
    using first2 tail2 by (rule relpow_Suc_I2)
  then show ?case using rel_end by blast
qed

lemma mttm_relpow_shift_reverse:
  fixes M :: "('q, 'a) mttm"
  assumes vM: "valid_mttm M"
  shows "\<lbrakk> \<forall>k. d k \<noteq> 0 \<longrightarrow> mt_tape c1 k 0 = le_tm M; shift_rel d c1 c2;
           (c2, c2') \<in> (mttm_step (delta_tm M)) ^^ n \<rbrakk>
         \<Longrightarrow> \<exists>c1'. (c1, c1') \<in> (mttm_step (delta_tm M)) ^^ n
                   \<and> shift_rel d c1' c2'"
proof (induction n arbitrary: c1 c2 c2')
  case 0
  then show ?case by auto
next
  case (Suc n)
  from Suc.prems(3) obtain cmid2 where
      first2: "(c2, cmid2) \<in> mttm_step (delta_tm M)"
    and rest2: "(cmid2, c2') \<in> (mttm_step (delta_tm M)) ^^ n"
    by (blast dest: relpow_Suc_D2)
  obtain cmid where
      first:   "(c1, cmid) \<in> mttm_step (delta_tm M)"
    and rel_mid: "shift_rel d cmid cmid2"
    using mttm_step_shift_reverse[OF vM Suc.prems(1) Suc.prems(2) first2] by blast
  have le0_mid: "\<forall>k. d k \<noteq> 0 \<longrightarrow> mt_tape cmid k 0 = le_tm M"
  proof (intro allI impI)
    fix k assume "d k \<noteq> 0"
    have "mt_tape c1 k 0 = le_tm M" using Suc.prems(1) \<open>d k \<noteq> 0\<close> by blast
    from mttm_step_LE_pos0_preserve[OF vM first this]
    show "mt_tape cmid k 0 = le_tm M" .
  qed
  from Suc.IH[OF le0_mid rel_mid rest2] obtain c1' where
      tail:    "(cmid, c1') \<in> (mttm_step (delta_tm M)) ^^ n"
    and rel_end: "shift_rel d c1' c2'"
    by blast
  have "(c1, c1') \<in> (mttm_step (delta_tm M)) ^^ (Suc n)"
    using first tail by (rule relpow_Suc_I2)
  then show ?case using rel_end by blast
qed

subsection \<open>Acceptance transfers across the shift, both directions\<close>

text \<open>The consumer-facing interface.  A run reaching a nominated state
  \<open>qa\<close> (the accept state, in use) in \<open>n\<close> steps from the base config
  yields one of the \<^emph>\<open>same length\<close> reaching the same state from the
  shifted config, and conversely.  Length preservation carries the time
  bound; state preservation (@{thm[source] shift_rel_state}) carries
  acceptance.  The two directions give language inclusion each way ---
  exactly what a nondeterministic machine admits, with no bisimulation
  claim.  These \<open>relpow\<close> (fixed-length) forms feed
  @{const accepts_in_time_mttm} directly; a caller working with
  @{const Lang_mttm} unfolds @{thm[source] rtrancl_power} to a fixed
  length first, then applies them.\<close>

lemma shift_reach_state_forward:
  fixes M :: "('q, 'a) mttm"
  assumes vM:  "valid_mttm M"
    and le0:   "\<forall>k. d k \<noteq> 0 \<longrightarrow> mt_tape c1 k 0 = le_tm M"
    and rel:   "shift_rel d c1 c2"
    and run:   "(c1, ca) \<in> (mttm_step (delta_tm M)) ^^ n"
    and acc:   "mt_state ca = qa"
  shows "\<exists>cb. (c2, cb) \<in> (mttm_step (delta_tm M)) ^^ n \<and> mt_state cb = qa"
proof -
  from mttm_relpow_shift_forward[OF vM le0 rel run] obtain cb where
      run2: "(c2, cb) \<in> (mttm_step (delta_tm M)) ^^ n"
    and rel2: "shift_rel d ca cb" by blast
  have "mt_state cb = mt_state ca" using rel2 by (rule shift_rel_state)
  thus ?thesis using run2 acc by auto
qed

lemma shift_reach_state_reverse:
  fixes M :: "('q, 'a) mttm"
  assumes vM:  "valid_mttm M"
    and le0:   "\<forall>k. d k \<noteq> 0 \<longrightarrow> mt_tape c1 k 0 = le_tm M"
    and rel:   "shift_rel d c1 c2"
    and run:   "(c2, cb) \<in> (mttm_step (delta_tm M)) ^^ n"
    and acc:   "mt_state cb = qa"
  shows "\<exists>ca. (c1, ca) \<in> (mttm_step (delta_tm M)) ^^ n \<and> mt_state ca = qa"
proof -
  from mttm_relpow_shift_reverse[OF vM le0 rel run] obtain ca where
      run1: "(c1, ca) \<in> (mttm_step (delta_tm M)) ^^ n"
    and rel2: "shift_rel d ca cb" by blast
  have "mt_state cb = mt_state ca" using rel2 by (rule shift_rel_state)
  thus ?thesis using run1 acc by auto
qed

end
