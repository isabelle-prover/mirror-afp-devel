theory Multitape_Finite_Patch
  imports Multitape_Finite_Control
begin

section \<open>Finite-control patch combinator\<close>

text \<open>The combinator @{text finite_patch} wraps an arbitrary machine
  \<open>M\<close> with a finite-control front end deciding the short inputs (length
  at most a cutoff \<open>N\<close>) by a caller-supplied table, while long inputs
  (length above \<open>N\<close>) are handed to \<open>M\<close> unchanged.  Unlike the alphabet
  combinators it performs \<^emph>\<open>no encoding\<close>: it keeps \<open>M\<close>'s input alphabet,
  tape alphabet, blank, left endmarker, and tape count, so running \<open>M\<close>
  is a pure state relabelling (@{text "FP_Run q"} mirrors \<open>M\<close>'s state
  \<open>q\<close>) on the very same tapes.

  The front end scans the input read-only as the recogniser does; once
  it has read past the cutoff it walks the head back to the origin
  (phase @{text FP_Rewind}) and enters \<open>M\<close>'s start state, so the handoff
  configuration is exactly \<open>M\<close>'s initial configuration.  Short inputs
  are decided in place: the scan ends on the end-of-input blank and
  jumps straight to \<open>M\<close>'s accept state (identify-with-run, so no extra
  halting funnel) when the table holds, or to a dedicated reject sink
  otherwise.\<close>


subsection \<open>Patch state space\<close>

text \<open>Four phases: @{text "FP_Scan u"} has read the prefix \<open>u\<close>;
  @{text FP_Rewind} is walking the head back to the origin after a
  long-input overflow; @{text "FP_Run q"} is running the wrapped
  machine in (relabelled) state \<open>q\<close>; @{text FP_Rej} is the short-input
  rejection sink.  Acceptance is identified with \<^emph>\<open>reaching \<open>M\<close>'s accept
  state under the run relabelling\<close>, @{text "FP_Run (t_tm M)"}.\<close>

datatype ('q, 'a) fp_state =
    FP_Scan "'a list" | FP_Rewind | FP_Run 'q | FP_Rej


subsection \<open>Patch transition relation\<close>

text \<open>Eight families, reusing the recogniser's read/move tuples
  @{const fr_read} / @{const fr_move} (so the front end is read-only,
  slots 2 and 4 equal).  Parameters: input alphabet \<open>Sg\<close>, blank \<open>bl\<close>,
  left endmarker \<open>le\<close>, tape count \<open>k\<close>, the wrapped machine's start
  state \<open>st\<close> and accept state \<open>tt\<close>, the short-input decision table
  \<open>table\<close>, the cutoff \<open>N\<close>, and the wrapped machine's transition relation
  \<open>deltaM\<close>.

  \<^item> advance-le --- read past the left endmarker (start step);
  \<^item> scan-extend --- extend the scanned prefix while below the cutoff;
  \<^item> overflow --- at the cutoff with input remaining, enter the rewind;
  \<^item> short-accept --- end-of-input on a table member jumps to \<open>M\<close>'s accept;
  \<^item> short-reject --- end-of-input on a non-member rejects;
  \<^item> rewind-walk --- walk the head left over the input (the only left move);
  \<^item> rewind-done --- reading the left endmarker enters \<open>M\<close>'s start state;
  \<^item> run-lift --- \<open>M\<close>'s own transitions, relabelled by @{const FP_Run}.\<close>

definition fp_delta ::
  "'a set \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> nat \<Rightarrow> 'q \<Rightarrow> 'q \<Rightarrow> ('a list \<Rightarrow> bool) \<Rightarrow> nat
     \<Rightarrow> ('q \<times> (nat \<Rightarrow> 'a) \<times> 'q \<times> (nat \<Rightarrow> 'a) \<times> (nat \<Rightarrow> dir)) set
     \<Rightarrow> (('q, 'a) fp_state \<times> (nat \<Rightarrow> 'a) \<times> ('q, 'a) fp_state
          \<times> (nat \<Rightarrow> 'a) \<times> (nat \<Rightarrow> dir)) set"
where
  "fp_delta Sg bl le k st tt table N deltaM =
     { (FP_Scan [], fr_read bl le k le, FP_Scan [],
        fr_read bl le k le, fr_move dir.R) }
     \<union> { (FP_Scan u, fr_read bl le k x, FP_Scan (u @ [x]),
          fr_read bl le k x, fr_move dir.R)
         | u x. set u \<subseteq> Sg \<and> length u < N \<and> x \<in> Sg }
     \<union> { (FP_Scan u, fr_read bl le k x, FP_Rewind,
          fr_read bl le k x, fr_move dir.N)
         | u x. set u \<subseteq> Sg \<and> length u = N \<and> x \<in> Sg }
     \<union> { (FP_Scan u, fr_read bl le k bl, FP_Run tt,
          fr_read bl le k bl, fr_move dir.N)
         | u. set u \<subseteq> Sg \<and> length u \<le> N \<and> table u }
     \<union> { (FP_Scan u, fr_read bl le k bl, FP_Rej,
          fr_read bl le k bl, fr_move dir.N)
         | u. set u \<subseteq> Sg \<and> length u \<le> N \<and> \<not> table u }
     \<union> { (FP_Rewind, fr_read bl le k x, FP_Rewind,
          fr_read bl le k x, fr_move dir.L)
         | x. x \<in> Sg }
     \<union> { (FP_Rewind, fr_read bl le k le, FP_Run st,
          fr_read bl le k le, fr_move dir.N) }
     \<union> { (FP_Run q, a, FP_Run q', a', d)
         | q a q' a' d. (q, a, q', a', d) \<in> deltaM }"


subsection \<open>The patch machine\<close>

text \<open>The finite patch of \<open>M\<close> at cutoff \<open>N\<close> with short-input table
  \<open>table\<close>.  Its state set is the scannable prefixes (words over \<open>M\<close>'s
  input alphabet up to the cutoff), the relabelled states of \<open>M\<close>, the
  rewind state, and the reject sink; alphabet, blank, endmarker, and
  tape count are inherited from \<open>M\<close>.\<close>

definition finite_patch ::
  "('q, 'a) mttm \<Rightarrow> ('a list \<Rightarrow> bool) \<Rightarrow> nat \<Rightarrow> (('q, 'a) fp_state, 'a) mttm"
where
  "finite_patch M table N =
     MTTM
       (FP_Scan ` {u. set u \<subseteq> Sigma_tm M \<and> length u \<le> N}
          \<union> FP_Run ` Q_tm M \<union> {FP_Rewind, FP_Rej})
       (Sigma_tm M)
       (\<Gamma>_tm M)
       (bl_tm M)
       (le_tm M)
       (fp_delta (Sigma_tm M) (bl_tm M) (le_tm M) (k_tm M)
          (s_tm M) (t_tm M) table N (delta_tm M))
       (FP_Scan [])
       (FP_Run (t_tm M))
       FP_Rej
       (k_tm M)"


subsection \<open>Component accessors\<close>

lemma finite_patch_k_tm:
  "k_tm (finite_patch M table N) = k_tm M"
  by (simp add: finite_patch_def)

lemma finite_patch_Sigma_tm:
  "Sigma_tm (finite_patch M table N) = Sigma_tm M"
  by (simp add: finite_patch_def)

lemma finite_patch_Gamma_tm:
  "\<Gamma>_tm (finite_patch M table N) = \<Gamma>_tm M"
  by (simp add: finite_patch_def)

lemma finite_patch_bl_tm:
  "bl_tm (finite_patch M table N) = bl_tm M"
  by (simp add: finite_patch_def)

lemma finite_patch_le_tm:
  "le_tm (finite_patch M table N) = le_tm M"
  by (simp add: finite_patch_def)

lemma finite_patch_s_tm:
  "s_tm (finite_patch M table N) = FP_Scan []"
  by (simp add: finite_patch_def)

lemma finite_patch_t_tm:
  "t_tm (finite_patch M table N) = FP_Run (t_tm M)"
  by (simp add: finite_patch_def)

lemma finite_patch_r_tm:
  "r_tm (finite_patch M table N) = FP_Rej"
  by (simp add: finite_patch_def)

lemma finite_patch_Q_tm:
  "Q_tm (finite_patch M table N)
     = FP_Scan ` {u. set u \<subseteq> Sigma_tm M \<and> length u \<le> N}
         \<union> FP_Run ` Q_tm M \<union> {FP_Rewind, FP_Rej}"
  by (simp add: finite_patch_def)

lemma finite_patch_delta_tm:
  "delta_tm (finite_patch M table N)
     = fp_delta (Sigma_tm M) (bl_tm M) (le_tm M) (k_tm M)
         (s_tm M) (t_tm M) table N (delta_tm M)"
  by (simp add: finite_patch_def)


subsection \<open>Transition-relation discipline\<close>

text \<open>The support invariant: at every inactive tape index \<open>j \<ge> k\<close>,
  each transition reads and writes the blank and stays put.  The front
  families are read-only with @{const fr_read} / @{const fr_move}, so
  \<open>j \<ge> k\<close> reads and writes \<open>bl\<close> and moves \<open>N\<close>; the run-lift family
  inherits it from the wrapped machine's own support hypothesis.\<close>

lemma fp_delta_support:
  assumes kpos: "0 < k"
    and dM: "\<forall>q a q' a' d. (q, a, q', a', d) \<in> deltaM
                \<longrightarrow> (\<forall>j\<ge>k. a j = bl \<and> a' j = bl \<and> d j = dir.N)"
    and tr: "(q, a, q', a', d) \<in> fp_delta Sg bl le k st tt table N deltaM"
    and j: "k \<le> j"
  shows "a j = bl \<and> a' j = bl \<and> d j = dir.N"
proof -
  have jn0: "j \<noteq> 0" using j kpos by simp
  have jk: "\<not> j < k" using j by simp
  from tr consider
      (front) rsym mdir where "a = fr_read bl le k rsym"
                              "a' = fr_read bl le k rsym" "d = fr_move mdir"
    | (run) q0 q0' where "(q0, a, q0', a', d) \<in> deltaM"
    unfolding fp_delta_def by blast
  then show ?thesis
  proof cases
    case front \<comment> \<open>read-only front families: \<open>bl\<close> on the support region\<close>
    show ?thesis using front jn0 jk by (simp add: fr_read_def fr_move_def)
  next
    case run \<comment> \<open>the run-lift family inherits \<open>M\<close>'s support invariant\<close>
    show ?thesis using dM run j by blast
  qed
qed

text \<open>A tape reading @{const fr_read}'s input symbol \<open>x \<in> Sg\<close> as \<open>le\<close>
  must be tape \<open>0\<close>'s neighbour, not tape \<open>0\<close> itself: tape \<open>0\<close> carries
  \<open>x\<close>, and \<open>x \<noteq> le\<close> since \<open>le \<notin> Sg\<close>.  This is what keeps the rewind
  walk's left move off any endmarker-reading tape.\<close>

lemma fr_read_le_pos:
  "le \<notin> Sg \<Longrightarrow> x \<in> Sg \<Longrightarrow> fr_read bl le k x j = le \<Longrightarrow> j \<noteq> 0"
  by (auto simp: fr_read_def split: if_splits)

text \<open>The left-endmarker read discipline: a transition reading \<open>le\<close> on
  tape \<open>j\<close> writes \<open>le\<close> back there and moves only \<open>N\<close> or \<open>R\<close>.  The front
  families are read-only, so the write half is immediate; for the move
  half the only left move is the rewind walk (@{const fr_move} \<open>L\<close>),
  and there tape \<open>0\<close> reads an input symbol (never \<open>le\<close>, as \<open>le \<notin> Sg\<close>)
  while every other tape stays put.  The run-lift family inherits it
  from the wrapped machine's own endmarker hypothesis.\<close>

lemma fp_delta_LE:
  assumes leS: "le \<notin> Sg"
    and dM: "\<forall>q a q' a' d j. (q, a, q', a', d) \<in> deltaM \<longrightarrow> a j = le
                \<longrightarrow> a' j = le \<and> d j \<in> {dir.N, dir.R}"
    and tr: "(q, a, q', a', d) \<in> fp_delta Sg bl le k st tt table N deltaM"
    and LE: "a j = le"
  shows "a' j = le \<and> d j \<in> {dir.N, dir.R}"
proof -
  \<comment> \<open>name the family up front, so each case reasons over clean
     (non-recursive) equations rather than letting the simplifier
     back-substitute \<open>le\<close> into an \<open>fr_read\<close> body\<close>
  from tr consider
      (front) "a' = a" "d = fr_move dir.R \<or> d = fr_move dir.N"
    | (rwalk) x where "x \<in> Sg" "a = fr_read bl le k x" "a' = a"
                      "d = fr_move dir.L"
    | (run) q0 q0' where "(q0, a, q0', a', d) \<in> deltaM"
    unfolding fp_delta_def by blast
  then show ?thesis
  proof cases
    case front \<comment> \<open>read-only front families with no left move\<close>
    from front(1) LE have aj: "a' j = le" by simp
    have "d j \<noteq> dir.L" using front(2) by (auto simp: fr_move_def split: if_splits)
    hence "d j \<in> {dir.N, dir.R}" by (cases "d j") auto
    with aj show ?thesis by blast
  next
    case rwalk \<comment> \<open>the rewind walk: reading \<open>le\<close> forces the head off tape \<open>0\<close>\<close>
    have aj: "fr_read bl le k x j = le" using LE rwalk(2) by simp
    have "j \<noteq> 0" using fr_read_le_pos[OF leS rwalk(1) aj] .
    moreover have "a' j = le" using LE rwalk(3) by simp
    ultimately show ?thesis using rwalk(4) by (simp add: fr_move_def)
  next
    case run \<comment> \<open>the run-lift family inherits \<open>M\<close>'s endmarker discipline\<close>
    show ?thesis using dM run LE by blast
  qed
qed


subsection \<open>Well-formedness\<close>

text \<open>The patch of a valid machine is a valid substrate machine.  The
  front families supply the finite-control side of every structural
  axiom (finiteness of the scannable prefixes, the read/write alphabet,
  the endmarker and support disciplines) and the run-lift family
  forwards \<open>M\<close>'s own structure through the substrate's projection
  lemmas.\<close>

lemma finite_patch_valid:
  assumes vM: "valid_mttm M"
  shows "valid_mttm (finite_patch M table N)"
proof -
  let ?Sg = "Sigma_tm M"
  let ?Ga = "\<Gamma>_tm M"
  let ?bl = "bl_tm M"
  let ?le = "le_tm M"
  let ?k = "k_tm M"
  let ?st = "s_tm M"
  let ?tt = "t_tm M"
  let ?QM = "Q_tm M"
  let ?Q = "FP_Scan ` {u. set u \<subseteq> ?Sg \<and> length u \<le> N}
              \<union> FP_Run ` ?QM \<union> {FP_Rewind, FP_Rej}"
  let ?dl = "fp_delta ?Sg ?bl ?le ?k ?st ?tt table N (delta_tm M)"
  \<comment> \<open>the machine's own structural facts, projected out of @{term vM}\<close>
  have SgG: "?Sg \<subseteq> ?Ga" by (rule valid_mttm_Sigma_sub_Gamma[OF vM])
  have blG: "?bl \<in> ?Ga" by (rule valid_mttm_blank_in_Gamma[OF vM])
  have blS: "?bl \<notin> ?Sg" by (rule valid_mttm_blank_not_Sigma[OF vM])
  have leG: "?le \<in> ?Ga" by (rule valid_mttm_LE_in_Gamma[OF vM])
  have leS: "?le \<notin> ?Sg" by (rule valid_mttm_LE_not_Sigma[OF vM])
  have sQ: "?st \<in> ?QM" by (rule valid_mttm_s_in_Q[OF vM])
  have tQ: "?tt \<in> ?QM" by (rule valid_mttm_t_in_Q[OF vM])
  have kpos: "0 < ?k" by (rule valid_mttm_k_pos[OF vM])
  have finGa: "finite ?Ga" by (rule valid_mttm_finite_Gamma[OF vM])
  have finQM: "finite ?QM" by (rule valid_mttm_finite_Q[OF vM])
  have dM_set: "delta_tm M
      \<subseteq> (?QM - {?tt, r_tm M}) \<times> (UNIV \<rightarrow> ?Ga) \<times> ?QM
           \<times> (UNIV \<rightarrow> ?Ga) \<times> (UNIV \<rightarrow> UNIV)"
    by (rule valid_mttm_delta_set[OF vM])
  have dM_LE: "\<forall>q a q' a' d j. (q, a, q', a', d) \<in> delta_tm M \<longrightarrow> a j = ?le
                 \<longrightarrow> a' j = ?le \<and> d j \<in> {dir.N, dir.R}"
    using valid_mttm_deltaLE[OF vM] by blast
  have dM_supp: "\<forall>q a q' a' d. (q, a, q', a', d) \<in> delta_tm M
                   \<longrightarrow> (\<forall>j\<ge>?k. a j = ?bl \<and> a' j = ?bl \<and> d j = dir.N)"
    using valid_mttm_delta_support[OF vM] by blast
  \<comment> \<open>finiteness of the scannable-prefix component, hence of \<open>Q\<close>\<close>
  have finSg: "finite ?Sg" using finite_subset[OF SgG finGa] .
  have finP: "finite {u. set u \<subseteq> ?Sg \<and> length u \<le> N}"
    using finite_lists_length_le[OF finSg] by blast
  have finQ: "finite ?Q" using finP finQM by simp
  \<comment> \<open>the transition-shape, endmarker, and support obligations\<close>
  have shape: "?dl \<subseteq> (?Q - {FP_Run ?tt, FP_Rej}) \<times> (UNIV \<rightarrow> ?Ga) \<times> ?Q
                        \<times> (UNIV \<rightarrow> ?Ga) \<times> (UNIV \<rightarrow> UNIV)"
    unfolding fp_delta_def fr_read_def
    using SgG blG leG sQ tQ dM_set by (auto simp: Pi_iff)
  have LEc: "\<forall>q a q' a' d j.
      (q, a, q', a', d) \<in> ?dl \<longrightarrow> a j = ?le \<longrightarrow> a' j = ?le \<and> d j \<in> {dir.N, dir.R}"
    using fp_delta_LE[OF leS dM_LE] by blast
  have suppc: "\<forall>q a q' a' d.
      (q, a, q', a', d) \<in> ?dl \<longrightarrow> (\<forall>j\<ge>?k. a j = ?bl \<and> a' j = ?bl \<and> d j = dir.N)"
    using fp_delta_support[OF kpos dM_supp] by blast
  show ?thesis
    unfolding finite_patch_def valid_mttm.simps
    using finQ finGa SgG blG blS leG leS kpos tQ shape LEc suppc
    by (intro conjI) auto
qed


subsection \<open>Determinism\<close>

text \<open>The patch is deterministic when the wrapped machine is.  The
  three phases are disjoint by source constructor (@{const FP_Scan} /
  @{const FP_Rewind} / @{const FP_Run}); within the scan and rewind
  phases the tape-\<open>0\<close> read (@{thm[source] fr_read_inj}) selects a unique
  family, the left endmarker, the blank, and the input alphabet being
  pairwise distinct; and the run phase is single-valued because \<open>M\<close>
  is.\<close>

lemma finite_patch_det:
  assumes vM: "valid_mttm M" and blle: "bl_tm M \<noteq> le_tm M" and dM: "det_mttm M"
  shows "det_mttm (finite_patch M table N)"
proof -
  have leS: "le_tm M \<notin> Sigma_tm M" by (rule valid_mttm_LE_not_Sigma[OF vM])
  have blS: "bl_tm M \<notin> Sigma_tm M" by (rule valid_mttm_blank_not_Sigma[OF vM])
  show ?thesis
    unfolding det_mttm_def finite_patch_delta_tm fp_delta_def
    using leS blS blle dM[unfolded det_mttm_def]
    by (auto dest: fr_read_inj)
qed


subsection \<open>Long-input simulation of the wrapped machine\<close>

text \<open>The run-lift family embeds \<open>M\<close>'s transitions verbatim, so the
  \<^emph>\<open>run relabelling\<close> --- tagging \<open>M\<close>'s state \<open>q\<close> as @{term "FP_Run q"} on
  the very same tapes --- carries every \<open>M\<close> step to a patch step.  This
  is the long-input arm's correctness, and it holds for a
  nondeterministic \<open>M\<close> (the run phase is where the patch's own
  nondeterminism lives).\<close>

fun fp_lift :: "('a, 'q) mt_config \<Rightarrow> ('a, ('q, 'a) fp_state) mt_config" where
  "fp_lift (Config\<^sub>M q ts n) = Config\<^sub>M (FP_Run q) ts n"

lemma fp_run_step:
  assumes "(c, c') \<in> mttm_step deltaM"
  shows "(fp_lift c, fp_lift c')
           \<in> mttm_step (fp_delta Sg bl le k st tt table N deltaM)"
proof -
  from assms obtain q ts n q' a d where
      c: "c = Config\<^sub>M q ts n"
    and c': "c' = Config\<^sub>M q' (\<lambda>i. (ts i)(n i := a i)) (\<lambda>i. go_dir (d i) (n i))"
    and tr: "(q, \<lambda>i. ts i (n i), q', a, d) \<in> deltaM"
    by (auto elim: mttm_step.cases)
  have tr': "(FP_Run q, \<lambda>i. ts i (n i), FP_Run q', a, d)
               \<in> fp_delta Sg bl le k st tt table N deltaM"
    unfolding fp_delta_def using tr by blast
  have "(Config\<^sub>M (FP_Run q) ts n,
         Config\<^sub>M (FP_Run q') (\<lambda>i. (ts i)(n i := a i)) (\<lambda>i. go_dir (d i) (n i)))
          \<in> mttm_step (fp_delta Sg bl le k st tt table N deltaM)"
  proof (rule mttm_step.step)
    show "(FP_Run q, \<lambda>i. ts i (n i), FP_Run q', a, d)
            \<in> fp_delta Sg bl le k st tt table N deltaM"
      by (rule tr')
  qed
  thus ?thesis using c c' by simp
qed

lemma fp_run_rtrancl:
  assumes "(c, c') \<in> (mttm_step deltaM)\<^sup>*"
  shows "(fp_lift c, fp_lift c')
           \<in> (mttm_step (fp_delta Sg bl le k st tt table N deltaM))\<^sup>*"
  using assms
proof (induction rule: rtrancl_induct)
  case base
  show ?case by simp
next
  case (step y z)
  from fp_run_step[OF step.hyps(2)] step.IH
  show ?case by (auto intro: rtrancl.rtrancl_into_rtrancl)
qed


subsection \<open>The scanning front run\<close>

text \<open>The configuration after the patch has read the left endmarker
  and the first \<open>m\<close> input symbols: state @{term "FP_Scan (take m w)"},
  the (read-only, hence unchanging) input tape, and the input head at
  position \<open>m + 1\<close>.  Identical in tape shape to the recogniser's
  @{const fr_run_config}, differing only in the scan constructor.\<close>

definition fp_scan_config ::
  "'a \<Rightarrow> 'a \<Rightarrow> nat \<Rightarrow> 'a list \<Rightarrow> nat \<Rightarrow> ('a, ('q, 'a) fp_state) mt_config"
where
  "fp_scan_config bl le k w m =
     Config\<^sub>M (FP_Scan (take m w))
       (\<lambda>i n. if i < k
              then (if n = 0 then le
                    else if i = 0 \<and> n \<le> length w then w ! (n - 1) else bl)
              else bl)
       (\<lambda>i. if i = 0 then m + 1 else 0)"

text \<open>The start step: reading the left endmarker advances the patch's
  initial configuration into the length-\<open>0\<close> scan configuration.\<close>

lemma fp_le_step:
  assumes kpos: "0 < k_tm M"
  shows "(init_config_mttm (finite_patch M table N) w,
          fp_scan_config (bl_tm M) (le_tm M) (k_tm M) w 0)
           \<in> mttm_step (fp_delta (Sigma_tm M) (bl_tm M) (le_tm M) (k_tm M)
                          (s_tm M) (t_tm M) table N (delta_tm M))"
proof -
  let ?bl = "bl_tm M" and ?le = "le_tm M" and ?k = "k_tm M"
  let ?ts = "\<lambda>i n. if i < ?k
                    then (if n = 0 then ?le
                          else if i = 0 \<and> n \<le> length w then w ! (n - 1) else ?bl)
                    else ?bl"
  let ?dl = "fp_delta (Sigma_tm M) ?bl ?le ?k (s_tm M) (t_tm M) table N (delta_tm M)"
  have read_eq: "(\<lambda>i. ?ts i ((\<lambda>_. 0) i)) = fr_read ?bl ?le ?k ?le"
  proof (rule ext)
    fix i show "?ts i ((\<lambda>_. 0) i) = fr_read ?bl ?le ?k ?le i"
      using kpos by (cases "i = 0") (auto simp: fr_read_def)
  qed
  have tr: "(FP_Scan [], fr_read ?bl ?le ?k ?le, FP_Scan [],
             fr_read ?bl ?le ?k ?le, fr_move dir.R) \<in> ?dl"
    unfolding fp_delta_def by auto
  have init_eq: "init_config_mttm (finite_patch M table N) w
                   = Config\<^sub>M (FP_Scan []) ?ts (\<lambda>_. 0)"
    by (simp add: finite_patch_def)
  have step: "(Config\<^sub>M (FP_Scan []) ?ts (\<lambda>_. 0),
               Config\<^sub>M (FP_Scan [])
                 (\<lambda>i. (?ts i)((\<lambda>_. 0) i := fr_read ?bl ?le ?k ?le i))
                 (\<lambda>i. go_dir (fr_move dir.R i) ((\<lambda>_. 0) i))) \<in> mttm_step ?dl"
  proof (rule mttm_step.step)
    show "(FP_Scan [], \<lambda>i. ?ts i ((\<lambda>_. 0) i), FP_Scan [],
           fr_read ?bl ?le ?k ?le, fr_move dir.R) \<in> ?dl"
      using tr by (simp add: read_eq)
  qed
  have tgt: "fp_scan_config ?bl ?le ?k w 0
              = Config\<^sub>M (FP_Scan [])
                  (\<lambda>i. (?ts i)((\<lambda>_. 0) i := fr_read ?bl ?le ?k ?le i))
                  (\<lambda>i. go_dir (fr_move dir.R i) ((\<lambda>_. 0) i))"
  proof -
    have tape: "(\<lambda>i. (?ts i)((\<lambda>_. 0) i := fr_read ?bl ?le ?k ?le i)) = ?ts"
    proof (rule ext)
      fix i
      have eq: "fr_read ?bl ?le ?k ?le i = ?ts i ((\<lambda>_. 0) i)"
        using kpos by (cases "i = 0") (auto simp: fr_read_def)
      show "(?ts i)((\<lambda>_. 0) i := fr_read ?bl ?le ?k ?le i) = ?ts i"
        unfolding eq by (rule fun_upd_triv)
    qed
    have head: "(\<lambda>i. go_dir (fr_move dir.R i) ((\<lambda>_. 0) i))
                  = (\<lambda>i::nat. if i = 0 then 0 + 1 else 0)"
      by (rule ext) (simp add: fr_move_def)
    show ?thesis by (simp add: fp_scan_config_def tape head)
  qed
  show ?thesis unfolding init_eq tgt by (rule step)
qed

text \<open>One scan step: reading the next input symbol extends the scanned
  prefix, provided the input still has a symbol there and the cutoff
  is not yet reached.\<close>

lemma fp_scan_step:
  assumes kpos: "0 < k" and mlt: "m < length w" and mN: "m < N"
    and wSg: "set w \<subseteq> Sg"
  shows "(fp_scan_config bl le k w m, fp_scan_config bl le k w (Suc m))
           \<in> mttm_step (fp_delta Sg bl le k st tt table N deltaM)"
proof -
  let ?x = "w ! m"
  let ?ts = "\<lambda>i n. if i < k
                    then (if n = 0 then le
                          else if i = 0 \<and> n \<le> length w then w ! (n - 1) else bl)
                    else bl"
  let ?nn = "\<lambda>i::nat. if i = 0 then m + 1 else 0"
  let ?dl = "fp_delta Sg bl le k st tt table N deltaM"
  have xSg: "?x \<in> Sg" using nth_mem[OF mlt] wSg by blast
  have lenu: "length (take m w) = m" using mlt by simp
  have takeq: "take (Suc m) w = take m w @ [?x]"
    using mlt by (simp add: take_Suc_conv_app_nth)
  have setu: "set (take m w) \<subseteq> Sg"
    using wSg by (meson set_take_subset subset_trans)
  have read_eq: "(\<lambda>i. ?ts i (?nn i)) = fr_read bl le k ?x"
  proof (rule ext)
    fix i show "?ts i (?nn i) = fr_read bl le k ?x i"
      using kpos mlt by (cases "i = 0") (auto simp: fr_read_def)
  qed
  have tr: "(FP_Scan (take m w), fr_read bl le k ?x, FP_Scan (take (Suc m) w),
             fr_read bl le k ?x, fr_move dir.R) \<in> ?dl"
    unfolding fp_delta_def takeq using setu lenu mN xSg by auto
  have src: "fp_scan_config bl le k w m = Config\<^sub>M (FP_Scan (take m w)) ?ts ?nn"
    by (simp add: fp_scan_config_def)
  have step: "(Config\<^sub>M (FP_Scan (take m w)) ?ts ?nn,
               Config\<^sub>M (FP_Scan (take (Suc m) w))
                 (\<lambda>i. (?ts i)(?nn i := fr_read bl le k ?x i))
                 (\<lambda>i. go_dir (fr_move dir.R i) (?nn i))) \<in> mttm_step ?dl"
  proof (rule mttm_step.step)
    show "(FP_Scan (take m w), \<lambda>i. ?ts i (?nn i), FP_Scan (take (Suc m) w),
           fr_read bl le k ?x, fr_move dir.R) \<in> ?dl"
      using tr by (simp add: read_eq)
  qed
  have tgt: "fp_scan_config bl le k w (Suc m)
              = Config\<^sub>M (FP_Scan (take (Suc m) w))
                  (\<lambda>i. (?ts i)(?nn i := fr_read bl le k ?x i))
                  (\<lambda>i. go_dir (fr_move dir.R i) (?nn i))"
  proof -
    have tape: "(\<lambda>i. (?ts i)(?nn i := fr_read bl le k ?x i)) = ?ts"
    proof (rule ext)
      fix i
      have eq: "fr_read bl le k ?x i = ?ts i (?nn i)"
        using kpos mlt by (cases "i = 0") (auto simp: fr_read_def)
      show "(?ts i)(?nn i := fr_read bl le k ?x i) = ?ts i"
        unfolding eq by (rule fun_upd_triv)
    qed
    have head: "(\<lambda>i. go_dir (fr_move dir.R i) (?nn i))
                  = (\<lambda>i::nat. if i = 0 then Suc m + 1 else 0)"
      by (rule ext) (simp add: fr_move_def)
    show ?thesis by (simp add: fp_scan_config_def tape head)
  qed
  show ?thesis unfolding src tgt by (rule step)
qed

text \<open>The scan phase: from the length-\<open>0\<close> scan configuration, iterating
  the scan step reaches the length-\<open>m\<close> one in \<open>m\<close> steps, for any \<open>m\<close> up
  to both the input length and the cutoff.  Assembled by the
  substrate's @{thm[source] relpow_invariant_chain}.\<close>

lemma fp_scan_chain:
  assumes kpos: "0 < k" and mle: "m \<le> length w" and mN: "m \<le> N"
    and wSg: "set w \<subseteq> Sg"
  shows "(fp_scan_config bl le k w 0, fp_scan_config bl le k w m)
           \<in> (mttm_step (fp_delta Sg bl le k st tt table N deltaM)) ^^ m"
  using mle mN
proof (induction m)
  case 0
  show ?case by simp
next
  case (Suc m)
  have mw: "m < length w" using Suc.prems(1) by simp
  have mN': "m < N" using Suc.prems(2) by simp
  have chain: "(fp_scan_config bl le k w 0, fp_scan_config bl le k w m)
                 \<in> (mttm_step (fp_delta Sg bl le k st tt table N deltaM)) ^^ m"
    using Suc.IH Suc.prems by simp
  have step: "(fp_scan_config bl le k w m, fp_scan_config bl le k w (Suc m))
                \<in> mttm_step (fp_delta Sg bl le k st tt table N deltaM)"
    by (rule fp_scan_step[OF kpos mw mN' wSg])
  from chain step show ?case by (rule relpow_Suc_I)
qed


subsection \<open>Short-input dispatch\<close>

text \<open>At the end of a short input (length at most the cutoff), reading
  the end-of-input blank on a fully-scanned prefix jumps to \<open>M\<close>'s accept
  state when the table holds --- the short arm never runs \<open>M\<close>.\<close>

lemma fp_accept_step:
  assumes wtab: "table w" and wSg: "set w \<subseteq> Sg" and lenN: "length w \<le> N"
  shows "(fp_scan_config bl le k w (length w),
          Config\<^sub>M (FP_Run tt)
            (\<lambda>i n. if i < k
                   then (if n = 0 then le
                         else if i = 0 \<and> n \<le> length w then w ! (n - 1) else bl)
                   else bl)
            (\<lambda>i::nat. if i = 0 then length w + 1 else 0))
           \<in> mttm_step (fp_delta Sg bl le k st tt table N deltaM)"
proof -
  let ?ts = "\<lambda>i n. if i < k
                    then (if n = 0 then le
                          else if i = 0 \<and> n \<le> length w then w ! (n - 1) else bl)
                    else bl"
  let ?nn = "\<lambda>i::nat. if i = 0 then length w + 1 else 0"
  let ?dl = "fp_delta Sg bl le k st tt table N deltaM"
  have read_eq: "(\<lambda>i. ?ts i (?nn i)) = fr_read bl le k bl"
  proof (rule ext)
    fix i show "?ts i (?nn i) = fr_read bl le k bl i"
      by (cases "i = 0") (auto simp: fr_read_def)
  qed
  have tr: "(FP_Scan w, fr_read bl le k bl, FP_Run tt,
             fr_read bl le k bl, fr_move dir.N) \<in> ?dl"
    unfolding fp_delta_def using wSg lenN wtab by auto
  have src: "fp_scan_config bl le k w (length w) = Config\<^sub>M (FP_Scan w) ?ts ?nn"
    by (simp add: fp_scan_config_def)
  have step: "(Config\<^sub>M (FP_Scan w) ?ts ?nn,
               Config\<^sub>M (FP_Run tt)
                 (\<lambda>i. (?ts i)(?nn i := fr_read bl le k bl i))
                 (\<lambda>i. go_dir (fr_move dir.N i) (?nn i))) \<in> mttm_step ?dl"
  proof (rule mttm_step.step)
    show "(FP_Scan w, \<lambda>i. ?ts i (?nn i), FP_Run tt,
           fr_read bl le k bl, fr_move dir.N) \<in> ?dl"
      using tr by (simp add: read_eq)
  qed
  have tape: "(\<lambda>i. (?ts i)(?nn i := fr_read bl le k bl i)) = ?ts"
  proof (rule ext)
    fix i
    have eq: "fr_read bl le k bl i = ?ts i (?nn i)"
      by (cases "i = 0") (auto simp: fr_read_def)
    show "(?ts i)(?nn i := fr_read bl le k bl i) = ?ts i"
      unfolding eq by (rule fun_upd_triv)
  qed
  have head: "(\<lambda>i. go_dir (fr_move dir.N i) (?nn i)) = ?nn"
    by (rule ext) (simp add: fr_move_def)
  show ?thesis unfolding src using step by (simp add: tape head)
qed

text \<open>The dual short-input step: on a non-member prefix the scan
  rejects into the dedicated sink @{const FP_Rej}.\<close>

lemma fp_reject_step:
  assumes wtab: "\<not> table w" and wSg: "set w \<subseteq> Sg" and lenN: "length w \<le> N"
  shows "\<exists>c'. (fp_scan_config bl le k w (length w), c')
               \<in> mttm_step (fp_delta Sg bl le k st tt table N deltaM)
             \<and> mt_state c' = FP_Rej"
proof -
  let ?ts = "\<lambda>i n. if i < k
                    then (if n = 0 then le
                          else if i = 0 \<and> n \<le> length w then w ! (n - 1) else bl)
                    else bl"
  let ?nn = "\<lambda>i::nat. if i = 0 then length w + 1 else 0"
  let ?dl = "fp_delta Sg bl le k st tt table N deltaM"
  let ?tgt = "Config\<^sub>M FP_Rej
                (\<lambda>i. (?ts i)(?nn i := fr_read bl le k bl i))
                (\<lambda>i. go_dir (fr_move dir.N i) (?nn i))"
  have read_eq: "(\<lambda>i. ?ts i (?nn i)) = fr_read bl le k bl"
  proof (rule ext)
    fix i show "?ts i (?nn i) = fr_read bl le k bl i"
      by (cases "i = 0") (auto simp: fr_read_def)
  qed
  have tr: "(FP_Scan w, fr_read bl le k bl, FP_Rej,
             fr_read bl le k bl, fr_move dir.N) \<in> ?dl"
    unfolding fp_delta_def using wSg lenN wtab by auto
  have src: "fp_scan_config bl le k w (length w) = Config\<^sub>M (FP_Scan w) ?ts ?nn"
    by (simp add: fp_scan_config_def)
  have step: "(fp_scan_config bl le k w (length w), ?tgt) \<in> mttm_step ?dl"
    unfolding src
  proof (rule mttm_step.step)
    show "(FP_Scan w, \<lambda>i. ?ts i (?nn i), FP_Rej,
           fr_read bl le k bl, fr_move dir.N) \<in> ?dl"
      using tr by (simp add: read_eq)
  qed
  have "(fp_scan_config bl le k w (length w), ?tgt) \<in> mttm_step ?dl
          \<and> mt_state ?tgt = FP_Rej"
    using step by simp
  thus ?thesis by blast
qed


subsection \<open>Long-input rewind and handoff\<close>

text \<open>The rewind configuration: state @{const FP_Rewind}, the unchanging
  input tape, and the input head at position \<open>p\<close> as it walks back to
  the origin.\<close>

definition fp_rewind_config ::
  "'a \<Rightarrow> 'a \<Rightarrow> nat \<Rightarrow> 'a list \<Rightarrow> nat \<Rightarrow> ('a, ('q, 'a) fp_state) mt_config"
where
  "fp_rewind_config bl le k w p =
     Config\<^sub>M FP_Rewind
       (\<lambda>i n. if i < k
              then (if n = 0 then le
                    else if i = 0 \<and> n \<le> length w then w ! (n - 1) else bl)
              else bl)
       (\<lambda>i. if i = 0 then p else 0)"

text \<open>Overflow: at the cutoff with input still remaining, reading the
  next symbol enters the rewind (the head does not move --- the symbol
  under it is re-read on the first rewind step).\<close>

lemma fp_overflow_step:
  assumes kpos: "0 < k" and Nlt: "N < length w" and wSg: "set w \<subseteq> Sg"
  shows "(fp_scan_config bl le k w N, fp_rewind_config bl le k w (N + 1))
           \<in> mttm_step (fp_delta Sg bl le k st tt table N deltaM)"
proof -
  let ?x = "w ! N"
  let ?ts = "\<lambda>i n. if i < k
                    then (if n = 0 then le
                          else if i = 0 \<and> n \<le> length w then w ! (n - 1) else bl)
                    else bl"
  let ?nn = "\<lambda>i::nat. if i = 0 then N + 1 else 0"
  let ?dl = "fp_delta Sg bl le k st tt table N deltaM"
  have xSg: "?x \<in> Sg" using nth_mem[OF Nlt] wSg by blast
  have lenu: "length (take N w) = N" using Nlt by simp
  have setu: "set (take N w) \<subseteq> Sg"
    using wSg by (meson set_take_subset subset_trans)
  have read_eq: "(\<lambda>i. ?ts i (?nn i)) = fr_read bl le k ?x"
  proof (rule ext)
    fix i show "?ts i (?nn i) = fr_read bl le k ?x i"
      using kpos Nlt by (cases "i = 0") (auto simp: fr_read_def)
  qed
  have tr: "(FP_Scan (take N w), fr_read bl le k ?x, FP_Rewind,
             fr_read bl le k ?x, fr_move dir.N) \<in> ?dl"
    unfolding fp_delta_def using setu lenu xSg by auto
  have src: "fp_scan_config bl le k w N = Config\<^sub>M (FP_Scan (take N w)) ?ts ?nn"
    by (simp add: fp_scan_config_def)
  have step: "(Config\<^sub>M (FP_Scan (take N w)) ?ts ?nn,
               Config\<^sub>M FP_Rewind
                 (\<lambda>i. (?ts i)(?nn i := fr_read bl le k ?x i))
                 (\<lambda>i. go_dir (fr_move dir.N i) (?nn i))) \<in> mttm_step ?dl"
  proof (rule mttm_step.step)
    show "(FP_Scan (take N w), \<lambda>i. ?ts i (?nn i), FP_Rewind,
           fr_read bl le k ?x, fr_move dir.N) \<in> ?dl"
      using tr by (simp add: read_eq)
  qed
  have tgt: "fp_rewind_config bl le k w (N + 1)
              = Config\<^sub>M FP_Rewind
                  (\<lambda>i. (?ts i)(?nn i := fr_read bl le k ?x i))
                  (\<lambda>i. go_dir (fr_move dir.N i) (?nn i))"
  proof -
    have tape: "(\<lambda>i. (?ts i)(?nn i := fr_read bl le k ?x i)) = ?ts"
    proof (rule ext)
      fix i
      have eq: "fr_read bl le k ?x i = ?ts i (?nn i)"
        using kpos Nlt by (cases "i = 0") (auto simp: fr_read_def)
      show "(?ts i)(?nn i := fr_read bl le k ?x i) = ?ts i"
        unfolding eq by (rule fun_upd_triv)
    qed
    have head: "(\<lambda>i. go_dir (fr_move dir.N i) (?nn i)) = ?nn"
      by (rule ext) (simp add: fr_move_def)
    show ?thesis by (simp add: fp_rewind_config_def tape head fun_eq_iff)
  qed
  show ?thesis unfolding src tgt by (rule step)
qed

text \<open>One rewind step: reading an input symbol walks the head one cell
  left, leaving the tape unchanged.\<close>

lemma fp_rewind_walk_step:
  assumes kpos: "0 < k" and qw: "Suc q \<le> length w" and wSg: "set w \<subseteq> Sg"
  shows "(fp_rewind_config bl le k w (Suc q), fp_rewind_config bl le k w q)
           \<in> mttm_step (fp_delta Sg bl le k st tt table N deltaM)"
proof -
  let ?x = "w ! q"
  let ?ts = "\<lambda>i n. if i < k
                    then (if n = 0 then le
                          else if i = 0 \<and> n \<le> length w then w ! (n - 1) else bl)
                    else bl"
  let ?nn = "\<lambda>i::nat. if i = 0 then Suc q else 0"
  let ?dl = "fp_delta Sg bl le k st tt table N deltaM"
  have xin: "q < length w" using qw by simp
  have xSg: "?x \<in> Sg" using nth_mem[OF xin] wSg by blast
  have read_eq: "(\<lambda>i. ?ts i (?nn i)) = fr_read bl le k ?x"
  proof (rule ext)
    fix i show "?ts i (?nn i) = fr_read bl le k ?x i"
      using kpos qw by (cases "i = 0") (auto simp: fr_read_def)
  qed
  have tr: "(FP_Rewind, fr_read bl le k ?x, FP_Rewind,
             fr_read bl le k ?x, fr_move dir.L) \<in> ?dl"
    unfolding fp_delta_def using xSg by auto
  have src: "fp_rewind_config bl le k w (Suc q) = Config\<^sub>M FP_Rewind ?ts ?nn"
    by (simp add: fp_rewind_config_def)
  have step: "(Config\<^sub>M FP_Rewind ?ts ?nn,
               Config\<^sub>M FP_Rewind
                 (\<lambda>i. (?ts i)(?nn i := fr_read bl le k ?x i))
                 (\<lambda>i. go_dir (fr_move dir.L i) (?nn i))) \<in> mttm_step ?dl"
  proof (rule mttm_step.step)
    show "(FP_Rewind, \<lambda>i. ?ts i (?nn i), FP_Rewind,
           fr_read bl le k ?x, fr_move dir.L) \<in> ?dl"
      using tr by (simp add: read_eq)
  qed
  have tgt: "fp_rewind_config bl le k w q
              = Config\<^sub>M FP_Rewind
                  (\<lambda>i. (?ts i)(?nn i := fr_read bl le k ?x i))
                  (\<lambda>i. go_dir (fr_move dir.L i) (?nn i))"
  proof -
    have tape: "(\<lambda>i. (?ts i)(?nn i := fr_read bl le k ?x i)) = ?ts"
    proof (rule ext)
      fix i
      have eq: "fr_read bl le k ?x i = ?ts i (?nn i)"
        using kpos qw by (cases "i = 0") (auto simp: fr_read_def)
      show "(?ts i)(?nn i := fr_read bl le k ?x i) = ?ts i"
        unfolding eq by (rule fun_upd_triv)
    qed
    have head: "(\<lambda>i. go_dir (fr_move dir.L i) (?nn i))
                  = (\<lambda>i::nat. if i = 0 then q else 0)"
      by (rule ext) (simp add: fr_move_def)
    show ?thesis by (simp add: fp_rewind_config_def tape head)
  qed
  show ?thesis unfolding src tgt by (rule step)
qed

text \<open>The rewind phase: from head position \<open>p\<close> (within the input) the
  walk reaches the origin in \<open>p\<close> steps.\<close>

lemma fp_rewind_chain:
  assumes kpos: "0 < k" and pw: "p \<le> length w" and wSg: "set w \<subseteq> Sg"
  shows "(fp_rewind_config bl le k w p, fp_rewind_config bl le k w 0)
           \<in> (mttm_step (fp_delta Sg bl le k st tt table N deltaM)) ^^ p"
  using pw
proof (induction p)
  case 0
  show ?case by simp
next
  case (Suc p)
  have step: "(fp_rewind_config bl le k w (Suc p), fp_rewind_config bl le k w p)
                \<in> mttm_step (fp_delta Sg bl le k st tt table N deltaM)"
    by (rule fp_rewind_walk_step[OF kpos Suc.prems wSg])
  have chain: "(fp_rewind_config bl le k w p, fp_rewind_config bl le k w 0)
                 \<in> (mttm_step (fp_delta Sg bl le k st tt table N deltaM)) ^^ p"
    using Suc.IH Suc.prems by simp
  from step chain show ?case by (rule relpow_Suc_I2)
qed

text \<open>Rewind completion: reading the left endmarker at the origin
  enters \<open>M\<close>'s start state, and the configuration is exactly the run
  relabelling of \<open>M\<close>'s initial configuration.\<close>

lemma fp_rewind_done_step:
  assumes kpos: "0 < k_tm M"
  shows "(fp_rewind_config (bl_tm M) (le_tm M) (k_tm M) w 0,
          fp_lift (init_config_mttm M w))
           \<in> mttm_step (fp_delta (Sigma_tm M) (bl_tm M) (le_tm M) (k_tm M)
                          (s_tm M) (t_tm M) table N (delta_tm M))"
proof (cases M)
  case (MTTM Q Sg Ga bl le d s t r k)
  \<comment> \<open>reduce every \<open>_tm M\<close> selector to a concrete component up front, so
     the tape reasoning is over ground terms\<close>
  have kpos': "0 < k" using kpos by (simp add: MTTM)
  let ?ts = "\<lambda>i n. if i < k
                    then (if n = 0 then le
                          else if i = 0 \<and> n \<le> length w then w ! (n - 1) else bl)
                    else bl"
  let ?dl = "fp_delta Sg bl le k s t table N d"
  have read_eq: "(\<lambda>i. ?ts i ((\<lambda>_. 0) i)) = fr_read bl le k le"
  proof (rule ext)
    fix i show "?ts i ((\<lambda>_. 0) i) = fr_read bl le k le i"
      using kpos' by (cases "i = 0") (auto simp: fr_read_def)
  qed
  have tr: "(FP_Rewind, fr_read bl le k le, FP_Run s,
             fr_read bl le k le, fr_move dir.N) \<in> ?dl"
    unfolding fp_delta_def by auto
  have src: "fp_rewind_config (bl_tm M) (le_tm M) (k_tm M) w 0
               = Config\<^sub>M FP_Rewind ?ts (\<lambda>_. 0)"
    by (simp add: fp_rewind_config_def MTTM)
  have dl_eq: "fp_delta (Sigma_tm M) (bl_tm M) (le_tm M) (k_tm M)
                 (s_tm M) (t_tm M) table N (delta_tm M) = ?dl"
    by (simp add: MTTM)
  have step: "(Config\<^sub>M FP_Rewind ?ts (\<lambda>_. 0),
               Config\<^sub>M (FP_Run s)
                 (\<lambda>i. (?ts i)((\<lambda>_. 0) i := fr_read bl le k le i))
                 (\<lambda>i. go_dir (fr_move dir.N i) ((\<lambda>_. 0) i)))
              \<in> mttm_step ?dl"
  proof (rule mttm_step.step)
    show "(FP_Rewind, \<lambda>i. ?ts i ((\<lambda>_. 0) i), FP_Run s,
           fr_read bl le k le, fr_move dir.N) \<in> ?dl"
      using tr by (simp add: read_eq)
  qed
  have tgt: "fp_lift (init_config_mttm M w)
              = Config\<^sub>M (FP_Run s)
                  (\<lambda>i. (?ts i)((\<lambda>_. 0) i := fr_read bl le k le i))
                  (\<lambda>i. go_dir (fr_move dir.N i) ((\<lambda>_. 0) i))"
  proof -
    have tape: "(\<lambda>i. (?ts i)((\<lambda>_. 0) i := fr_read bl le k le i)) = ?ts"
    proof (rule ext)
      fix i
      have eq: "fr_read bl le k le i = ?ts i ((\<lambda>_. 0) i)"
        using kpos' by (cases "i = 0") (auto simp: fr_read_def)
      show "(?ts i)((\<lambda>_. 0) i := fr_read bl le k le i) = ?ts i"
        unfolding eq by (rule fun_upd_triv)
    qed
    have head: "(\<lambda>i. go_dir (fr_move dir.N i) ((\<lambda>_. 0) i)) = (\<lambda>_::nat. 0)"
      by (rule ext) (simp add: fr_move_def)
    have init: "init_config_mttm M w = Config\<^sub>M s ?ts (\<lambda>_. 0)"
      by (simp add: MTTM)
    show ?thesis by (simp add: init tape head)
  qed
  show ?thesis unfolding dl_eq src tgt using step by simp
qed


subsection \<open>Forward language direction\<close>

text \<open>A short accepted input reaches \<open>M\<close>'s accept state without running
  \<open>M\<close>: read the endmarker, scan the whole input, and dispatch on the
  table.\<close>

lemma fp_short_run:
  assumes kpos: "0 < k_tm M" and wSg: "set w \<subseteq> Sigma_tm M"
    and lenN: "length w \<le> N" and tab: "table w"
  shows "\<exists>c. (init_config_mttm (finite_patch M table N) w, c)
               \<in> (mttm_step (delta_tm (finite_patch M table N)))\<^sup>*
             \<and> mt_state c = FP_Run (t_tm M)"
proof -
  let ?dl = "fp_delta (Sigma_tm M) (bl_tm M) (le_tm M) (k_tm M)
               (s_tm M) (t_tm M) table N (delta_tm M)"
  let ?sc = "fp_scan_config (bl_tm M) (le_tm M) (k_tm M) w"
  let ?acc = "Config\<^sub>M (FP_Run (t_tm M))
                (\<lambda>i n. if i < k_tm M
                       then (if n = 0 then le_tm M
                             else if i = 0 \<and> n \<le> length w then w ! (n - 1) else bl_tm M)
                       else bl_tm M)
                (\<lambda>i::nat. if i = 0 then length w + 1 else 0)"
  have dl: "delta_tm (finite_patch M table N) = ?dl" by (rule finite_patch_delta_tm)
  have le: "(init_config_mttm (finite_patch M table N) w, ?sc 0) \<in> (mttm_step ?dl)\<^sup>*"
    using fp_le_step[OF kpos] by (rule r_into_rtrancl)
  have sc: "(?sc 0, ?sc (length w)) \<in> (mttm_step ?dl)\<^sup>*"
    using fp_scan_chain[OF kpos order_refl lenN wSg] by (rule relpow_imp_rtrancl)
  have ac0: "(?sc (length w), ?acc) \<in> mttm_step ?dl"
    using tab wSg lenN by (rule fp_accept_step)
  have ac: "(?sc (length w), ?acc) \<in> (mttm_step ?dl)\<^sup>*"
    using ac0 by (rule r_into_rtrancl)
  have reach: "(init_config_mttm (finite_patch M table N) w, ?acc) \<in> (mttm_step ?dl)\<^sup>*"
    using le sc ac by (meson rtrancl_trans)
  have "mt_state ?acc = FP_Run (t_tm M)" by simp
  thus ?thesis using reach dl by auto
qed

text \<open>A long accepted input (in \<open>M\<close>'s language) reaches \<open>M\<close>'s accept
  state by overflowing into the rewind, walking back to \<open>M\<close>'s initial
  configuration, and then running \<open>M\<close>'s accepting computation under the
  run relabelling.\<close>

lemma fp_long_run:
  assumes kpos: "0 < k_tm M" and wSg: "set w \<subseteq> Sigma_tm M"
    and Nlt: "N < length w" and wL: "w \<in> Lang_mttm M"
  shows "\<exists>c. (init_config_mttm (finite_patch M table N) w, c)
               \<in> (mttm_step (delta_tm (finite_patch M table N)))\<^sup>*
             \<and> mt_state c = FP_Run (t_tm M)"
proof -
  let ?dl = "fp_delta (Sigma_tm M) (bl_tm M) (le_tm M) (k_tm M)
               (s_tm M) (t_tm M) table N (delta_tm M)"
  let ?init = "init_config_mttm (finite_patch M table N) w"
  let ?sc = "fp_scan_config (bl_tm M) (le_tm M) (k_tm M) w"
  let ?rw = "fp_rewind_config (bl_tm M) (le_tm M) (k_tm M) w"
  have dl: "delta_tm (finite_patch M table N) = ?dl" by (rule finite_patch_delta_tm)
  have Nle: "N \<le> length w" using Nlt by simp
  have N1le: "N + 1 \<le> length w" using Nlt by simp
  have le: "(?init, ?sc 0) \<in> (mttm_step ?dl)\<^sup>*"
    using fp_le_step[OF kpos] by (rule r_into_rtrancl)
  have sc: "(?sc 0, ?sc N) \<in> (mttm_step ?dl)\<^sup>*"
    using fp_scan_chain[OF kpos Nle order_refl wSg] by (rule relpow_imp_rtrancl)
  have ov: "(?sc N, ?rw (N + 1)) \<in> (mttm_step ?dl)\<^sup>*"
    using fp_overflow_step[OF kpos Nlt wSg] by (rule r_into_rtrancl)
  have rc: "(?rw (N + 1), ?rw 0) \<in> (mttm_step ?dl)\<^sup>*"
    using fp_rewind_chain[OF kpos N1le wSg] by (rule relpow_imp_rtrancl)
  have dn: "(?rw 0, fp_lift (init_config_mttm M w)) \<in> (mttm_step ?dl)\<^sup>*"
    using fp_rewind_done_step[OF kpos] by (rule r_into_rtrancl)
  from wL obtain w' n where mreach:
      "(init_config_mttm M w, Config\<^sub>M (t_tm M) w' n) \<in> (mttm_step (delta_tm M))\<^sup>*"
    unfolding Lang_mttm_def by auto
  have sim: "(fp_lift (init_config_mttm M w), Config\<^sub>M (FP_Run (t_tm M)) w' n)
               \<in> (mttm_step ?dl)\<^sup>*"
    using fp_run_rtrancl[OF mreach] by simp
  have r1: "(?init, ?sc N) \<in> (mttm_step ?dl)\<^sup>*" using le sc by (rule rtrancl_trans)
  have r2: "(?init, ?rw (N + 1)) \<in> (mttm_step ?dl)\<^sup>*" using r1 ov by (rule rtrancl_trans)
  have r3: "(?init, ?rw 0) \<in> (mttm_step ?dl)\<^sup>*" using r2 rc by (rule rtrancl_trans)
  have r4: "(?init, fp_lift (init_config_mttm M w)) \<in> (mttm_step ?dl)\<^sup>*"
    using r3 dn by (rule rtrancl_trans)
  have reach: "(?init, Config\<^sub>M (FP_Run (t_tm M)) w' n) \<in> (mttm_step ?dl)\<^sup>*"
    using r4 sim by (rule rtrancl_trans)
  have "mt_state (Config\<^sub>M (FP_Run (t_tm M)) w' n) = FP_Run (t_tm M)" by simp
  thus ?thesis using reach dl by auto
qed

text \<open>Forward language inclusion: every input satisfying the dispatch
  specification (short inputs decided by the table, long inputs by
  \<open>M\<close>'s language) is accepted by the patch.\<close>

theorem finite_patch_language_forward:
  assumes vM: "valid_mttm M"
  shows "{w. set w \<subseteq> Sigma_tm M
              \<and> (if length w \<le> N then table w else w \<in> Lang_mttm M)}
           \<subseteq> Lang_mttm (finite_patch M table N)"
proof
  fix w assume "w \<in> {w. set w \<subseteq> Sigma_tm M
                        \<and> (if length w \<le> N then table w else w \<in> Lang_mttm M)}"
  hence wSg: "set w \<subseteq> Sigma_tm M"
    and disp: "if length w \<le> N then table w else w \<in> Lang_mttm M" by auto
  have kpos: "0 < k_tm M" by (rule valid_mttm_k_pos[OF vM])
  have ex: "\<exists>c. (init_config_mttm (finite_patch M table N) w, c)
                  \<in> (mttm_step (delta_tm (finite_patch M table N)))\<^sup>*
                \<and> mt_state c = FP_Run (t_tm M)"
  proof (cases "length w \<le> N")
    case True
    hence tab: "table w" using disp by simp
    show ?thesis using kpos wSg True tab by (rule fp_short_run)
  next
    case False
    hence Nlt: "N < length w" by simp
    have wL: "w \<in> Lang_mttm M" using disp False by simp
    show ?thesis using kpos wSg Nlt wL by (rule fp_long_run)
  qed
  then obtain c where reach: "(init_config_mttm (finite_patch M table N) w, c)
                                \<in> (mttm_step (delta_tm (finite_patch M table N)))\<^sup>*"
    and cst: "mt_state c = FP_Run (t_tm M)" by blast
  obtain w' n where c_eq: "c = Config\<^sub>M (FP_Run (t_tm M)) w' n"
    using cst by (cases c) auto
  show "w \<in> Lang_mttm (finite_patch M table N)"
    unfolding Lang_mttm_def finite_patch_Sigma_tm finite_patch_t_tm
    using wSg reach c_eq by auto
qed


subsection \<open>Reverse language direction\<close>

text \<open>The front (scan and rewind) is deterministic irrespective of \<open>M\<close>:
  its families are the only ones with a @{const FP_Scan} or
  @{const FP_Rewind} source, and they are pairwise disjoint on the read
  (the endmarker, the blank, and the input alphabet being distinct).
  The wrapped machine's nondeterminism is confined to the @{const FP_Run}
  phase, so soundness needs no \<open>det_mttm M\<close>.\<close>

lemma fp_delta_front_functional:
  assumes leS: "le \<notin> Sg" and blS: "bl \<notin> Sg" and blle: "bl \<noteq> le"
    and src: "(\<exists>u. q = FP_Scan u) \<or> q = FP_Rewind"
    and tr1: "(q, a, p1, b1, d1) \<in> fp_delta Sg bl le k st tt table N deltaM"
    and tr2: "(q, a, p2, b2, d2) \<in> fp_delta Sg bl le k st tt table N deltaM"
  shows "(p1, b1, d1) = (p2, b2, d2)"
  using src tr1 tr2 leS blS blle
  unfolding fp_delta_def
  by (auto dest: fr_read_inj)

lemma fp_step_front_functional:
  assumes leS: "le \<notin> Sg" and blS: "bl \<notin> Sg" and blle: "bl \<noteq> le"
    and src: "(\<exists>u. mt_state c = FP_Scan u) \<or> mt_state c = FP_Rewind"
    and step1: "(c, c1) \<in> mttm_step (fp_delta Sg bl le k st tt table N deltaM)"
    and step2: "(c, c2) \<in> mttm_step (fp_delta Sg bl le k st tt table N deltaM)"
  shows "c1 = c2"
proof -
  from step1 obtain q ts n q1' a1 d1 where
      c_eq: "c = Config\<^sub>M q ts n"
    and c1_eq: "c1 = Config\<^sub>M q1' (\<lambda>i. (ts i)(n i := a1 i)) (\<lambda>i. go_dir (d1 i) (n i))"
    and tr1: "(q, \<lambda>i. ts i (n i), q1', a1, d1)
                \<in> fp_delta Sg bl le k st tt table N deltaM"
    by (auto elim: mttm_step.cases)
  from step2 obtain q2' a2 d2 where
      c2_eq: "c2 = Config\<^sub>M q2' (\<lambda>i. (ts i)(n i := a2 i)) (\<lambda>i. go_dir (d2 i) (n i))"
    and tr2: "(q, \<lambda>i. ts i (n i), q2', a2, d2)
                \<in> fp_delta Sg bl le k st tt table N deltaM"
    using c_eq by (auto elim: mttm_step.cases)
  have srcq: "(\<exists>u. q = FP_Scan u) \<or> q = FP_Rewind" using src c_eq by simp
  have "(q1', a1, d1) = (q2', a2, d2)"
    by (rule fp_delta_front_functional[OF leS blS blle srcq tr1 tr2])
  thus ?thesis using c1_eq c2_eq by simp
qed

text \<open>Reverse simulation: a step out of a run-relabelled configuration
  is a run relabelling of an \<open>M\<close> step (only the run-lift family has an
  @{const FP_Run} source).\<close>

lemma fp_run_step_rev:
  assumes step: "(fp_lift cM, c')
                   \<in> mttm_step (fp_delta Sg bl le k st tt table N deltaM)"
  shows "\<exists>cM'. c' = fp_lift cM' \<and> (cM, cM') \<in> mttm_step deltaM"
proof -
  obtain q0 ts n where cM_eq: "cM = Config\<^sub>M q0 ts n" by (cases cM)
  have lift_eq: "fp_lift cM = Config\<^sub>M (FP_Run q0) ts n" using cM_eq by simp
  from step[unfolded lift_eq] obtain q' a d where
      c'_eq: "c' = Config\<^sub>M q' (\<lambda>i. (ts i)(n i := a i)) (\<lambda>i. go_dir (d i) (n i))"
    and tr: "(FP_Run q0, \<lambda>i. ts i (n i), q', a, d)
               \<in> fp_delta Sg bl le k st tt table N deltaM"
    by (auto elim: mttm_step.cases)
  from tr obtain q0' where q'_eq: "q' = FP_Run q0'"
    and trM: "(q0, \<lambda>i. ts i (n i), q0', a, d) \<in> deltaM"
    unfolding fp_delta_def by auto
  let ?cM' = "Config\<^sub>M q0' (\<lambda>i. (ts i)(n i := a i)) (\<lambda>i. go_dir (d i) (n i))"
  have "c' = fp_lift ?cM'" using c'_eq q'_eq by simp
  moreover have "(cM, ?cM') \<in> mttm_step deltaM"
    unfolding cM_eq
  proof (rule mttm_step.step)
    show "(q0, \<lambda>i. ts i (n i), q0', a, d) \<in> deltaM" by (rule trM)
  qed
  ultimately show ?thesis by blast
qed

text \<open>The two halting states are sinks: \<open>M\<close>'s accept (relabelled) has
  no successor because \<open>M\<close>'s transitions never leave it, and the reject
  sink is the source of no family.\<close>

lemma fp_run_t_sink:
  assumes vM: "valid_mttm M"
    and step: "(c, c') \<in> mttm_step (fp_delta Sg bl le k st tt table N (delta_tm M))"
    and st: "mt_state c = FP_Run (t_tm M)"
  shows False
proof -
  from step obtain q ts n q' a d where c_eq: "c = Config\<^sub>M q ts n"
    and tr: "(q, \<lambda>i. ts i (n i), q', a, d)
               \<in> fp_delta Sg bl le k st tt table N (delta_tm M)"
    by (auto elim: mttm_step.cases)
  have q_eq: "q = FP_Run (t_tm M)" using st c_eq by simp
  from tr q_eq obtain q0' where
      trM: "(t_tm M, \<lambda>i. ts i (n i), q0', a, d) \<in> delta_tm M"
    unfolding fp_delta_def by auto
  have "t_tm M \<in> Q_tm M - {t_tm M, r_tm M}"
    using valid_mttm_delta_set[OF vM] trM by blast
  thus False by simp
qed

lemma fp_rej_sink:
  assumes step: "(c, c') \<in> mttm_step (fp_delta Sg bl le k st tt table N deltaM)"
    and st: "mt_state c = FP_Rej"
  shows False
proof -
  from step obtain q ts n q' a d where c_eq: "c = Config\<^sub>M q ts n"
    and tr: "(q, \<lambda>i. ts i (n i), q', a, d)
               \<in> fp_delta Sg bl le k st tt table N deltaM"
    by (auto elim: mttm_step.cases)
  have "q = FP_Rej" using st c_eq by simp
  thus False using tr unfolding fp_delta_def by auto
qed

text \<open>State of each canonical configuration.\<close>

lemma mt_state_fp_scan_config:
  "mt_state (fp_scan_config bl le k w m) = FP_Scan (take m w)"
  by (simp add: fp_scan_config_def)

lemma mt_state_fp_rewind_config:
  "mt_state (fp_rewind_config bl le k w p) = FP_Rewind"
  by (simp add: fp_rewind_config_def)

lemma mt_state_init_finite_patch:
  "mt_state (init_config_mttm (finite_patch M table N) w) = FP_Scan []"
  by (simp add: finite_patch_def)

lemma mt_state_fp_lift:
  "mt_state (fp_lift cM) = FP_Run (mt_state cM)"
  by (cases cM) simp

text \<open>The reachability invariant.  From the initial configuration on an
  input over \<open>M\<close>'s alphabet, every reachable configuration is: the
  initial one; a scan configuration below the cutoff; (long inputs
  only) a rewind configuration or a run relabelling of an
  \<open>M\<close>-reachable configuration; a short accept certifying the table; or a
  reject.\<close>

definition fp_inv ::
  "('q, 'a) mttm \<Rightarrow> ('a list \<Rightarrow> bool) \<Rightarrow> nat \<Rightarrow> 'a list
     \<Rightarrow> ('a, ('q, 'a) fp_state) mt_config \<Rightarrow> bool"
where
  "fp_inv M table N w c \<longleftrightarrow>
     c = init_config_mttm (finite_patch M table N) w
     \<or> (\<exists>m. m \<le> length w \<and> m \<le> N
            \<and> c = fp_scan_config (bl_tm M) (le_tm M) (k_tm M) w m)
     \<or> (N < length w \<and> (\<exists>p. p \<le> N + 1
            \<and> c = fp_rewind_config (bl_tm M) (le_tm M) (k_tm M) w p))
     \<or> (N < length w \<and> (\<exists>cM. (init_config_mttm M w, cM)
                              \<in> (mttm_step (delta_tm M))\<^sup>* \<and> c = fp_lift cM))
     \<or> (length w \<le> N \<and> table w \<and> mt_state c = FP_Run (t_tm M))
     \<or> mt_state c = FP_Rej"

text \<open>Closure of the invariant under a step.  Front configurations
  (init, scan, rewind) have a unique successor given by the matching
  step lemma (@{thm[source] fp_step_front_functional}); a run
  configuration steps to another run configuration
  (@{thm[source] fp_run_step_rev}); the two halting states are sinks.\<close>

lemma fp_inv_closed:
  assumes vM: "valid_mttm M" and blle: "bl_tm M \<noteq> le_tm M"
    and wSg: "set w \<subseteq> Sigma_tm M"
    and inv: "fp_inv M table N w c"
    and step: "(c, c') \<in> mttm_step (fp_delta (Sigma_tm M) (bl_tm M) (le_tm M)
                  (k_tm M) (s_tm M) (t_tm M) table N (delta_tm M))"
  shows "fp_inv M table N w c'"
proof -
  let ?bl = "bl_tm M"
  let ?le = "le_tm M"
  let ?k = "k_tm M"
  let ?dl = "fp_delta (Sigma_tm M) ?bl ?le ?k (s_tm M) (t_tm M) table N (delta_tm M)"
  have kpos: "0 < ?k" by (rule valid_mttm_k_pos[OF vM])
  have leS: "?le \<notin> Sigma_tm M" by (rule valid_mttm_LE_not_Sigma[OF vM])
  have blS: "?bl \<notin> Sigma_tm M" by (rule valid_mttm_blank_not_Sigma[OF vM])
  note funct = fp_step_front_functional[OF leS blS blle]
  from inv[unfolded fp_inv_def] show ?thesis
  proof (elim disjE)
    assume "c = init_config_mttm (finite_patch M table N) w"
    note cinit = this
    have src: "(\<exists>u. mt_state c = FP_Scan u) \<or> mt_state c = FP_Rewind"
      using cinit by (auto simp: mt_state_init_finite_patch)
    have cs: "(c, fp_scan_config ?bl ?le ?k w 0) \<in> mttm_step ?dl"
      using fp_le_step[OF kpos] cinit by simp
    have "c' = fp_scan_config ?bl ?le ?k w 0" by (rule funct[OF src step cs])
    thus ?thesis unfolding fp_inv_def by auto
  next
    assume "\<exists>m. m \<le> length w \<and> m \<le> N
                 \<and> c = fp_scan_config ?bl ?le ?k w m"
    then obtain m where mlw: "m \<le> length w" and mN: "m \<le> N"
      and c_eq: "c = fp_scan_config ?bl ?le ?k w m" by blast
    have src: "(\<exists>u. mt_state c = FP_Scan u) \<or> mt_state c = FP_Rewind"
      using c_eq by (auto simp: mt_state_fp_scan_config)
    show ?thesis
    proof (cases "m < length w")
      case True
      show ?thesis
      proof (cases "m < N")
        case True
        have cs: "(c, fp_scan_config ?bl ?le ?k w (Suc m)) \<in> mttm_step ?dl"
          using fp_scan_step[OF kpos \<open>m < length w\<close> True wSg] c_eq by simp
        have "c' = fp_scan_config ?bl ?le ?k w (Suc m)"
          by (rule funct[OF src step cs])
        moreover have "Suc m \<le> length w" using \<open>m < length w\<close> by simp
        moreover have "Suc m \<le> N" using True by simp
        ultimately show ?thesis unfolding fp_inv_def by blast
      next
        case False
        hence mEqN: "m = N" using mN by simp
        have Nlt: "N < length w" using \<open>m < length w\<close> mEqN by simp
        have cs: "(c, fp_rewind_config ?bl ?le ?k w (N + 1)) \<in> mttm_step ?dl"
          using fp_overflow_step[OF kpos Nlt wSg] c_eq mEqN by simp
        have "c' = fp_rewind_config ?bl ?le ?k w (N + 1)"
          by (rule funct[OF src step cs])
        moreover have "N + 1 \<le> N + 1" by simp
        ultimately show ?thesis unfolding fp_inv_def using Nlt by blast
      qed
    next
      case False
      hence mEq: "m = length w" using mlw by simp
      hence lenN: "length w \<le> N" using mN by simp
      show ?thesis
      proof (cases "table w")
        case True
        let ?acc = "Config\<^sub>M (FP_Run (t_tm M))
                      (\<lambda>i n. if i < ?k
                             then (if n = 0 then ?le
                                   else if i = 0 \<and> n \<le> length w then w ! (n - 1) else ?bl)
                             else ?bl)
                      (\<lambda>i::nat. if i = 0 then length w + 1 else 0)"
        have cs: "(c, ?acc) \<in> mttm_step ?dl"
          using True wSg lenN unfolding c_eq mEq by (rule fp_accept_step)
        have "c' = ?acc" by (rule funct[OF src step cs])
        hence "mt_state c' = FP_Run (t_tm M)" by simp
        thus ?thesis unfolding fp_inv_def using lenN True by blast
      next
        case False
        have rex: "\<exists>d. (fp_scan_config ?bl ?le ?k w (length w), d) \<in> mttm_step ?dl
                        \<and> mt_state d = FP_Rej"
          using False wSg lenN by (rule fp_reject_step)
        then obtain d where rstep: "(fp_scan_config ?bl ?le ?k w (length w), d)
                                       \<in> mttm_step ?dl" and dst: "mt_state d = FP_Rej"
          by blast
        have cs: "(c, d) \<in> mttm_step ?dl" using rstep c_eq mEq by simp
        have "c' = d" by (rule funct[OF src step cs])
        thus ?thesis unfolding fp_inv_def using dst by blast
      qed
    qed
  next
    assume "N < length w \<and> (\<exists>p. p \<le> N + 1
                                  \<and> c = fp_rewind_config ?bl ?le ?k w p)"
    then obtain p where Nlt: "N < length w" and pN1: "p \<le> N + 1"
      and c_eq: "c = fp_rewind_config ?bl ?le ?k w p" by blast
    have src: "(\<exists>u. mt_state c = FP_Scan u) \<or> mt_state c = FP_Rewind"
      using c_eq by (auto simp: mt_state_fp_rewind_config)
    have N1lw: "N + 1 \<le> length w" using Nlt by simp
    show ?thesis
    proof (cases p)
      case 0
      have cs: "(c, fp_lift (init_config_mttm M w)) \<in> mttm_step ?dl"
        using fp_rewind_done_step[OF kpos] c_eq 0 by simp
      have "c' = fp_lift (init_config_mttm M w)" by (rule funct[OF src step cs])
      moreover have "(init_config_mttm M w, init_config_mttm M w)
                       \<in> (mttm_step (delta_tm M))\<^sup>*" by simp
      ultimately show ?thesis unfolding fp_inv_def using Nlt by blast
    next
      case (Suc q)
      have Sqlw: "Suc q \<le> length w" using pN1 Suc N1lw by simp
      have cs: "(c, fp_rewind_config ?bl ?le ?k w q) \<in> mttm_step ?dl"
        using fp_rewind_walk_step[OF kpos Sqlw wSg] c_eq Suc by simp
      have "c' = fp_rewind_config ?bl ?le ?k w q" by (rule funct[OF src step cs])
      moreover have "q \<le> N + 1" using pN1 Suc by simp
      ultimately show ?thesis unfolding fp_inv_def using Nlt by blast
    qed
  next
    assume "N < length w \<and> (\<exists>cM. (init_config_mttm M w, cM)
                                  \<in> (mttm_step (delta_tm M))\<^sup>* \<and> c = fp_lift cM)"
    then obtain cM where Nlt: "N < length w"
      and reachM: "(init_config_mttm M w, cM) \<in> (mttm_step (delta_tm M))\<^sup>*"
      and c_eq: "c = fp_lift cM" by blast
    have "\<exists>cM'. c' = fp_lift cM' \<and> (cM, cM') \<in> mttm_step (delta_tm M)"
      using fp_run_step_rev[OF step[unfolded c_eq]] .
    then obtain cM' where c'_eq: "c' = fp_lift cM'"
      and mstep: "(cM, cM') \<in> mttm_step (delta_tm M)" by blast
    have "(init_config_mttm M w, cM') \<in> (mttm_step (delta_tm M))\<^sup>*"
      using reachM mstep by (rule rtrancl_into_rtrancl)
    thus ?thesis unfolding fp_inv_def using Nlt c'_eq by blast
  next
    assume "length w \<le> N \<and> table w \<and> mt_state c = FP_Run (t_tm M)"
    hence "mt_state c = FP_Run (t_tm M)" by simp
    hence False using fp_run_t_sink[OF vM step] by simp
    thus ?thesis by simp
  next
    assume "mt_state c = FP_Rej"
    hence False using fp_rej_sink[OF step] by simp
    thus ?thesis by simp
  qed
qed

text \<open>The invariant holds at every reachable configuration.\<close>

lemma fp_inv_reach:
  assumes vM: "valid_mttm M" and blle: "bl_tm M \<noteq> le_tm M"
    and wSg: "set w \<subseteq> Sigma_tm M"
    and reach: "(init_config_mttm (finite_patch M table N) w, c)
                  \<in> (mttm_step (delta_tm (finite_patch M table N)))\<^sup>*"
  shows "fp_inv M table N w c"
  using reach
proof (induction rule: rtrancl_induct)
  case base
  show ?case unfolding fp_inv_def by simp
next
  case (step y z)
  have yz: "(y, z) \<in> mttm_step (fp_delta (Sigma_tm M) (bl_tm M) (le_tm M)
              (k_tm M) (s_tm M) (t_tm M) table N (delta_tm M))"
    using step.hyps(2) by (simp add: finite_patch_delta_tm)
  show ?case by (rule fp_inv_closed[OF vM blle wSg step.IH yz])
qed

text \<open>An accepting reachable configuration certifies the dispatch
  condition: a short input satisfies the table, a long input is in
  \<open>M\<close>'s language.\<close>

lemma fp_inv_accept:
  assumes inv: "fp_inv M table N w c" and st: "mt_state c = FP_Run (t_tm M)"
    and wSg: "set w \<subseteq> Sigma_tm M"
  shows "if length w \<le> N then table w else w \<in> Lang_mttm M"
  using inv[unfolded fp_inv_def]
proof (elim disjE)
  assume "c = init_config_mttm (finite_patch M table N) w"
  hence "mt_state c = FP_Scan []" by (simp add: mt_state_init_finite_patch)
  thus ?thesis using st by simp
next
  assume "\<exists>m. m \<le> length w \<and> m \<le> N
               \<and> c = fp_scan_config (bl_tm M) (le_tm M) (k_tm M) w m"
  then obtain m where "c = fp_scan_config (bl_tm M) (le_tm M) (k_tm M) w m" by blast
  hence "mt_state c = FP_Scan (take m w)" by (simp add: mt_state_fp_scan_config)
  thus ?thesis using st by simp
next
  assume "N < length w \<and> (\<exists>p. p \<le> N + 1
                                \<and> c = fp_rewind_config (bl_tm M) (le_tm M) (k_tm M) w p)"
  then obtain p where "c = fp_rewind_config (bl_tm M) (le_tm M) (k_tm M) w p" by blast
  hence "mt_state c = FP_Rewind" by (simp add: mt_state_fp_rewind_config)
  thus ?thesis using st by simp
next
  assume "N < length w \<and> (\<exists>cM. (init_config_mttm M w, cM)
                                \<in> (mttm_step (delta_tm M))\<^sup>* \<and> c = fp_lift cM)"
  then obtain cM where Nlt: "N < length w"
    and reachM: "(init_config_mttm M w, cM) \<in> (mttm_step (delta_tm M))\<^sup>*"
    and c_eq: "c = fp_lift cM" by blast
  have "mt_state cM = t_tm M" using st c_eq by (simp add: mt_state_fp_lift)
  then obtain w' n where cM_eq: "cM = Config\<^sub>M (t_tm M) w' n" by (cases cM) auto
  have "w \<in> Lang_mttm M"
    unfolding Lang_mttm_def using wSg reachM cM_eq by auto
  thus ?thesis using Nlt by simp
next
  assume "length w \<le> N \<and> table w \<and> mt_state c = FP_Run (t_tm M)"
  thus ?thesis by simp
next
  assume "mt_state c = FP_Rej"
  thus ?thesis using st by simp
qed

text \<open>Reverse language inclusion, hence the language characterisation:
  the patch decides exactly the dispatch specification --- and this holds
  for a possibly-nondeterministic \<open>M\<close>.\<close>

theorem finite_patch_language_sound:
  assumes vM: "valid_mttm M" and blle: "bl_tm M \<noteq> le_tm M"
  shows "Lang_mttm (finite_patch M table N)
           \<subseteq> {w. set w \<subseteq> Sigma_tm M
                   \<and> (if length w \<le> N then table w else w \<in> Lang_mttm M)}"
proof
  fix w assume "w \<in> Lang_mttm (finite_patch M table N)"
  from this[unfolded Lang_mttm_def finite_patch_Sigma_tm finite_patch_t_tm]
  obtain w' n where wSg: "set w \<subseteq> Sigma_tm M"
    and r: "(init_config_mttm (finite_patch M table N) w,
             Config\<^sub>M (FP_Run (t_tm M)) w' n)
              \<in> (mttm_step (delta_tm (finite_patch M table N)))\<^sup>*"
    by auto
  have inv: "fp_inv M table N w (Config\<^sub>M (FP_Run (t_tm M)) w' n)"
    by (rule fp_inv_reach[OF vM blle wSg r])
  have "if length w \<le> N then table w else w \<in> Lang_mttm M"
    by (rule fp_inv_accept[OF inv _ wSg]) simp
  thus "w \<in> {w. set w \<subseteq> Sigma_tm M
                 \<and> (if length w \<le> N then table w else w \<in> Lang_mttm M)}"
    using wSg by simp
qed

theorem finite_patch_language:
  assumes vM: "valid_mttm M" and blle: "bl_tm M \<noteq> le_tm M"
  shows "Lang_mttm (finite_patch M table N)
           = {w. set w \<subseteq> Sigma_tm M
                   \<and> (if length w \<le> N then table w else w \<in> Lang_mttm M)}"
  using finite_patch_language_forward[OF vM] finite_patch_language_sound[OF vM blle]
  by blast


subsection \<open>Strengthened well-formedness\<close>

text \<open>The left-endmarker write discipline for the patch: the front
  families are read-only, and the run-lift family inherits it from
  \<open>M\<close>'s own @{const le_unique}.\<close>

lemma fp_delta_write_le:
  assumes dM: "\<forall>q a q' a' d j. (q, a, q', a', d) \<in> deltaM
                 \<longrightarrow> a' j = le \<longrightarrow> a j = le"
    and tr: "(q, a, q', a', d) \<in> fp_delta Sg bl le k st tt table N deltaM"
    and w: "a' j = le"
  shows "a j = le"
proof -
  from tr consider
      (front) "a' = a"
    | (run) q0 q0' where "(q0, a, q0', a', d) \<in> deltaM"
    unfolding fp_delta_def by blast
  then show ?thesis
  proof cases
    case front thus ?thesis using w by simp
  next
    case run thus ?thesis using dM w by blast
  qed
qed

text \<open>The patch of a well-formed machine is well-formed (distinct start /
  accept / reject and endmarker / blank, plus the endmarker write
  discipline).\<close>

lemma finite_patch_well_formed:
  assumes wfM: "well_formed_mttm M"
  shows "well_formed_mttm (finite_patch M table N)"
proof -
  have vM: "valid_mttm M" using wfM by simp
  have luM: "le_unique M" using wfM by simp
  have dM: "\<forall>q a q' a' d j. (q, a, q', a', d) \<in> delta_tm M
              \<longrightarrow> a' j = le_tm M \<longrightarrow> a j = le_tm M"
    using luM unfolding le_unique_def by simp
  have "valid_mttm (finite_patch M table N)" by (rule finite_patch_valid[OF vM])
  moreover have "s_tm (finite_patch M table N) \<noteq> t_tm (finite_patch M table N)"
    by (simp add: finite_patch_s_tm finite_patch_t_tm)
  moreover have "s_tm (finite_patch M table N) \<noteq> r_tm (finite_patch M table N)"
    by (simp add: finite_patch_s_tm finite_patch_r_tm)
  moreover have "le_tm (finite_patch M table N) \<noteq> bl_tm (finite_patch M table N)"
    using wfM by (simp add: finite_patch_le_tm finite_patch_bl_tm)
  moreover have "le_unique (finite_patch M table N)"
    unfolding le_unique_def finite_patch_delta_tm finite_patch_le_tm
    using fp_delta_write_le[OF dM] by blast
  ultimately show ?thesis by simp
qed


subsection \<open>Time bounds\<close>

text \<open>The step-counting analogue of @{thm[source] fp_run_rtrancl}: an
  \<open>n\<close>-step \<open>M\<close> computation lifts to an \<open>n\<close>-step patch computation.\<close>

lemma fp_run_relpow:
  assumes "(c, c') \<in> (mttm_step deltaM) ^^ n"
  shows "(fp_lift c, fp_lift c')
           \<in> (mttm_step (fp_delta Sg bl le k st tt table N deltaM)) ^^ n"
  using assms
proof (induction n arbitrary: c')
  case 0
  show ?case using 0 by simp
next
  case (Suc n)
  from Suc.prems obtain c'' where sn: "(c, c'') \<in> (mttm_step deltaM) ^^ n"
    and s1: "(c'', c') \<in> mttm_step deltaM"
    by (blast elim: relpow_Suc_E)
  have "(fp_lift c, fp_lift c'')
          \<in> (mttm_step (fp_delta Sg bl le k st tt table N deltaM)) ^^ n"
    by (rule Suc.IH[OF sn])
  moreover have "(fp_lift c'', fp_lift c')
                   \<in> mttm_step (fp_delta Sg bl le k st tt table N deltaM)"
    by (rule fp_run_step[OF s1])
  ultimately show ?case by (rule relpow_Suc_I)
qed

text \<open>A short accepted input is decided in \<open>length w + 2\<close> steps --- the
  endmarker read, the \<open>length w\<close> scan steps, and the dispatch --- without
  running \<open>M\<close> (the same \<open>+2\<close> as the recogniser).\<close>

lemma fp_short_time:
  assumes vM: "valid_mttm M" and wSg: "set w \<subseteq> Sigma_tm M"
    and lenN: "length w \<le> N" and tab: "table w"
  shows "accepts_in_time_mttm (finite_patch M table N) w (length w + 2)"
proof -
  let ?dl = "fp_delta (Sigma_tm M) (bl_tm M) (le_tm M) (k_tm M)
               (s_tm M) (t_tm M) table N (delta_tm M)"
  let ?R = "mttm_step ?dl"
  let ?sc = "fp_scan_config (bl_tm M) (le_tm M) (k_tm M) w"
  let ?init = "init_config_mttm (finite_patch M table N) w"
  let ?acc = "Config\<^sub>M (FP_Run (t_tm M))
                (\<lambda>i n. if i < k_tm M
                       then (if n = 0 then le_tm M
                             else if i = 0 \<and> n \<le> length w then w ! (n - 1) else bl_tm M)
                       else bl_tm M)
                (\<lambda>i::nat. if i = 0 then length w + 1 else 0)"
  have kpos: "0 < k_tm M" by (rule valid_mttm_k_pos[OF vM])
  have le: "(?init, ?sc 0) \<in> ?R ^^ 1" using fp_le_step[OF kpos] by simp
  have sc: "(?sc 0, ?sc (length w)) \<in> ?R ^^ (length w)"
    by (rule fp_scan_chain[OF kpos order_refl lenN wSg])
  have ac1: "(?sc (length w), ?acc) \<in> ?R" using tab wSg lenN by (rule fp_accept_step)
  have ac: "(?sc (length w), ?acc) \<in> ?R ^^ 1" using ac1 by simp
  have t1: "(?init, ?sc (length w)) \<in> ?R ^^ (1 + length w)"
    by (rule relpow_transI[OF le sc])
  have t2: "(?init, ?acc) \<in> ?R ^^ (1 + length w + 1)"
    by (rule relpow_transI[OF t1 ac])
  have run: "(?init, ?acc) \<in> ?R ^^ (length w + 2)" using t2 by (simp add: add.commute)
  have "mt_state ?acc = FP_Run (t_tm M)" by simp
  thus ?thesis
    unfolding accepts_in_time_mttm_def finite_patch_delta_tm finite_patch_t_tm
    using run by blast
qed

text \<open>A long accepted input is decided in \<open>t + c0\<close> steps, where \<open>t\<close>
  bounds \<open>M\<close>'s own acceptance time and the additive constant
  \<open>c0 = 2 * N + 4\<close> is the finite-control overhead --- the endmarker read,
  the \<open>N\<close> scan steps to the cutoff, the overflow, the \<open>N + 1\<close> rewind
  steps, and the handoff.\<close>

lemma fp_long_time:
  assumes vM: "valid_mttm M" and wSg: "set w \<subseteq> Sigma_tm M"
    and Nlt: "N < length w" and acc: "accepts_in_time_mttm M w t"
  shows "accepts_in_time_mttm (finite_patch M table N) w (t + (2 * N + 4))"
proof -
  let ?dl = "fp_delta (Sigma_tm M) (bl_tm M) (le_tm M) (k_tm M)
               (s_tm M) (t_tm M) table N (delta_tm M)"
  let ?R = "mttm_step ?dl"
  let ?sc = "fp_scan_config (bl_tm M) (le_tm M) (k_tm M) w"
  let ?rw = "fp_rewind_config (bl_tm M) (le_tm M) (k_tm M) w"
  let ?init = "init_config_mttm (finite_patch M table N) w"
  have kpos: "0 < k_tm M" by (rule valid_mttm_k_pos[OF vM])
  have Nle: "N \<le> length w" using Nlt by simp
  have N1le: "N + 1 \<le> length w" using Nlt by simp
  have le: "(?init, ?sc 0) \<in> ?R ^^ 1" using fp_le_step[OF kpos] by simp
  have sc: "(?sc 0, ?sc N) \<in> ?R ^^ N"
    by (rule fp_scan_chain[OF kpos Nle order_refl wSg])
  have ov: "(?sc N, ?rw (N + 1)) \<in> ?R ^^ 1"
    using fp_overflow_step[OF kpos Nlt wSg] by simp
  have rc: "(?rw (N + 1), ?rw 0) \<in> ?R ^^ (N + 1)"
    by (rule fp_rewind_chain[OF kpos N1le wSg])
  have dn: "(?rw 0, fp_lift (init_config_mttm M w)) \<in> ?R ^^ 1"
    using fp_rewind_done_step[OF kpos] by simp
  from acc obtain n cMn where nt: "n \<le> t"
    and mreach: "(init_config_mttm M w, cMn) \<in> (mttm_step (delta_tm M)) ^^ n"
    and mst: "mt_state cMn = t_tm M"
    unfolding accepts_in_time_mttm_def by blast
  have sim: "(fp_lift (init_config_mttm M w), fp_lift cMn) \<in> ?R ^^ n"
    by (rule fp_run_relpow[OF mreach])
  have c1: "(?init, ?sc N) \<in> ?R ^^ (1 + N)"
    by (rule relpow_transI[OF le sc])
  have c2: "(?init, ?rw (N + 1)) \<in> ?R ^^ (1 + N + 1)"
    by (rule relpow_transI[OF c1 ov])
  have c3: "(?init, ?rw 0) \<in> ?R ^^ (1 + N + 1 + (N + 1))"
    by (rule relpow_transI[OF c2 rc])
  have c4: "(?init, fp_lift (init_config_mttm M w)) \<in> ?R ^^ (1 + N + 1 + (N + 1) + 1)"
    by (rule relpow_transI[OF c3 dn])
  have c5: "(?init, fp_lift cMn) \<in> ?R ^^ (1 + N + 1 + (N + 1) + 1 + n)"
    by (rule relpow_transI[OF c4 sim])
  \<comment> \<open>keep the raw step count (\<open>2 * N + 4 + n\<close>) as the witness rather than
     rewrite the relpow exponent, which the simplifier would peel into a
     relcomp chain\<close>
  have bound: "1 + N + 1 + (N + 1) + 1 + n \<le> t + (2 * N + 4)" using nt by simp
  have "mt_state (fp_lift cMn) = FP_Run (t_tm M)" using mst by (simp add: mt_state_fp_lift)
  thus ?thesis
    unfolding accepts_in_time_mttm_def finite_patch_delta_tm finite_patch_t_tm
    using c5 bound by blast
qed

end
