theory Multitape_Finite_Control
  imports Multitape_Substrate
begin

section \<open>Finite-control small-input recogniser\<close>

text \<open>A reusable substrate construction for the ubiquitous low-level
  move: finitely many bounded-length inputs are decided directly by
  the finite control, reading the input in a fixed number of moves;
  only longer inputs need run a real machine.

  This theory provides the atom \<^emph>\<open>finite recogniser\<close>: given a finite
  input alphabet \<open>Sg\<close>, a concrete tape alphabet \<open>Gamma\<close> with a blank
  and a left endmarker, a finite set \<open>F\<close> of words over \<open>Sg\<close>, and a
  tape count \<open>k\<close>, it builds a deterministic machine that decides \<open>F\<close>
  --- accepting each member reading only its input.  The combinator
  \<^emph>\<open>finite patch\<close>, which reuses the recogniser on short inputs and
  hands off to an arbitrary machine on long inputs, is built on top.

  The construction is read-only: it never modifies the tape (the
  write component of every transition equals its read component), so
  the left-endmarker write discipline is vacuous and only the head
  movement carries the left-endmarker read discipline.\<close>


subsection \<open>Recogniser state space\<close>

text \<open>Three phases: @{text "FR_Scan u"} has read the prefix \<open>u\<close> of the
  input so far, @{text FR_Acc} has accepted, @{text FR_Rej} has
  rejected.  The scan payload ranges over words of length at most the
  recogniser's cutoff, so the state set is finite.\<close>

datatype 'a fr_state = FR_Scan "'a list" | FR_Acc | FR_Rej


subsection \<open>Recogniser transition components\<close>

text \<open>The read/write tuple for a step reading symbol \<open>x\<close> on the input
  tape \<open>0\<close>: tape \<open>0\<close> carries \<open>x\<close>, every other active tape (index
  \<open>1 \<le> j < k\<close>) reads the left endmarker \<open>le\<close> (its head never leaves
  position \<open>0\<close>), and every inactive tape (index \<open>j \<ge> k\<close>) reads the
  blank \<open>bl\<close> (the support invariant).\<close>

definition fr_read :: "'a \<Rightarrow> 'a \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> (nat \<Rightarrow> 'a)" where
  "fr_read bl le k x = (\<lambda>j. if j = 0 then x else if j < k then le else bl)"

text \<open>The head-move tuple: tape \<open>0\<close> moves by \<open>d\<close>, every other tape
  stays put.  This meets the support invariant (\<open>N\<close> beyond \<open>k\<close>) and,
  paired with @{const fr_read}, the left-endmarker read discipline.\<close>

definition fr_move :: "dir \<Rightarrow> (nat \<Rightarrow> dir)" where
  "fr_move d = (\<lambda>j. if j = 0 then d else dir.N)"


subsection \<open>Recogniser cutoff and transition relation\<close>

text \<open>The scan cutoff: an upper bound on the length of every word in
  \<open>F\<close> (the maximum length, or \<open>0\<close> when \<open>F\<close> is empty).  Inputs longer
  than the cutoff cannot be in \<open>F\<close>, so the scan rejects them on the
  overflow read.\<close>

definition fr_N :: "'a list set \<Rightarrow> nat" where
  "fr_N F = (if F = {} then 0 else Max (length ` F))"

text \<open>The recogniser transition relation.  Five families, all with
  write component equal to read component:
  \<^item> advance past the left endmarker (start step);
  \<^item> extend the scanned prefix by one symbol while below the cutoff;
  \<^item> overflow: reading a symbol at the cutoff rejects (input too long);
  \<^item> end-of-input on a member prefix accepts;
  \<^item> end-of-input on a non-member prefix rejects.\<close>

definition fr_delta ::
  "'a set \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a list set \<Rightarrow> nat \<Rightarrow> nat
     \<Rightarrow> ('a fr_state \<times> (nat \<Rightarrow> 'a) \<times> 'a fr_state
          \<times> (nat \<Rightarrow> 'a) \<times> (nat \<Rightarrow> dir)) set"
where
  "fr_delta Sg bl le F k N =
     { (FR_Scan [], fr_read bl le k le, FR_Scan [],
        fr_read bl le k le, fr_move dir.R) }
     \<union> { (FR_Scan u, fr_read bl le k x, FR_Scan (u @ [x]),
          fr_read bl le k x, fr_move dir.R)
         | u x. set u \<subseteq> Sg \<and> length u < N \<and> x \<in> Sg }
     \<union> { (FR_Scan u, fr_read bl le k x, FR_Rej,
          fr_read bl le k x, fr_move dir.N)
         | u x. set u \<subseteq> Sg \<and> length u = N \<and> x \<in> Sg }
     \<union> { (FR_Scan u, fr_read bl le k bl, FR_Acc,
          fr_read bl le k bl, fr_move dir.N)
         | u. set u \<subseteq> Sg \<and> length u \<le> N \<and> u \<in> F }
     \<union> { (FR_Scan u, fr_read bl le k bl, FR_Rej,
          fr_read bl le k bl, fr_move dir.N)
         | u. set u \<subseteq> Sg \<and> length u \<le> N \<and> u \<notin> F }"


subsection \<open>The recogniser machine\<close>

text \<open>The finite recogniser over input alphabet \<open>Sg\<close>, tape alphabet
  \<open>Gamma\<close>, blank \<open>bl\<close>, left endmarker \<open>le\<close>, word set \<open>F\<close>, and tape
  count \<open>k\<close>.  Its state set is the scannable prefixes (words over \<open>Sg\<close>
  up to the cutoff) plus the two halting states; the start state is
  the empty scan.\<close>

definition finite_recogniser ::
  "'a set \<Rightarrow> 'a set \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a list set \<Rightarrow> nat
     \<Rightarrow> ('a fr_state, 'a) mttm"
where
  "finite_recogniser Sg Gamma bl le F k =
     MTTM
       (FR_Scan ` {u. set u \<subseteq> Sg \<and> length u \<le> fr_N F} \<union> {FR_Acc, FR_Rej})
       Sg
       Gamma
       bl
       le
       (fr_delta Sg bl le F k (fr_N F))
       (FR_Scan [])
       FR_Acc
       FR_Rej
       k"


subsection \<open>Component accessors\<close>

lemma finite_recogniser_k_tm:
  "k_tm (finite_recogniser Sg Gamma bl le F k) = k"
  by (simp add: finite_recogniser_def)

lemma finite_recogniser_Sigma_tm:
  "Sigma_tm (finite_recogniser Sg Gamma bl le F k) = Sg"
  by (simp add: finite_recogniser_def)

lemma finite_recogniser_Gamma_tm:
  "\<Gamma>_tm (finite_recogniser Sg Gamma bl le F k) = Gamma"
  by (simp add: finite_recogniser_def)

lemma finite_recogniser_bl_tm:
  "bl_tm (finite_recogniser Sg Gamma bl le F k) = bl"
  by (simp add: finite_recogniser_def)

lemma finite_recogniser_le_tm:
  "le_tm (finite_recogniser Sg Gamma bl le F k) = le"
  by (simp add: finite_recogniser_def)

lemma finite_recogniser_s_tm:
  "s_tm (finite_recogniser Sg Gamma bl le F k) = FR_Scan []"
  by (simp add: finite_recogniser_def)

lemma finite_recogniser_t_tm:
  "t_tm (finite_recogniser Sg Gamma bl le F k) = FR_Acc"
  by (simp add: finite_recogniser_def)

lemma finite_recogniser_r_tm:
  "r_tm (finite_recogniser Sg Gamma bl le F k) = FR_Rej"
  by (simp add: finite_recogniser_def)

lemma finite_recogniser_Q_tm:
  "Q_tm (finite_recogniser Sg Gamma bl le F k)
     = FR_Scan ` {u. set u \<subseteq> Sg \<and> length u \<le> fr_N F} \<union> {FR_Acc, FR_Rej}"
  by (simp add: finite_recogniser_def)

lemma finite_recogniser_delta_tm:
  "delta_tm (finite_recogniser Sg Gamma bl le F k)
     = fr_delta Sg bl le F k (fr_N F)"
  by (simp add: finite_recogniser_def)


subsection \<open>Transition-relation discipline\<close>

text \<open>Every recogniser transition writes back exactly what it reads:
  the recogniser never modifies the tape.  This makes the
  left-endmarker \<^emph>\<open>write\<close> discipline (@{const le_unique}) vacuous.\<close>

lemma fr_delta_no_write:
  "(q, a, q', a', d) \<in> fr_delta Sg bl le F k N \<Longrightarrow> a' = a"
  by (auto simp: fr_delta_def)

text \<open>The read tuple is injective in the tape-\<open>0\<close> symbol (its value
  there), so a transition's read component determines the symbol
  scanned.  This is the discriminator behind determinism.\<close>

lemma fr_read_inj:
  "fr_read bl le k x = fr_read bl le k y \<Longrightarrow> x = y"
proof -
  assume "fr_read bl le k x = fr_read bl le k y"
  hence "fr_read bl le k x 0 = fr_read bl le k y 0" by simp
  thus "x = y" by (simp add: fr_read_def)
qed

text \<open>The support invariant: at every inactive tape index \<open>j \<ge> k\<close>,
  each transition reads and writes the blank and stays put.\<close>

lemma fr_delta_support:
  assumes "0 < k"
    and "(q, a, q', a', d) \<in> fr_delta Sg bl le F k N"
    and "k \<le> j"
  shows "a j = bl \<and> a' j = bl \<and> d j = dir.N"
  using assms by (auto simp: fr_delta_def fr_read_def fr_move_def)

text \<open>No recogniser transition ever moves left: the input tape moves
  \<open>R\<close> or stays, and every other tape stays put.\<close>

lemma fr_delta_move_no_L:
  "(q, a, q', a', d) \<in> fr_delta Sg bl le F k N \<Longrightarrow> d j \<in> {dir.N, dir.R}"
  by (auto simp: fr_delta_def fr_move_def split: if_splits)

text \<open>The left-endmarker read discipline: a transition reading \<open>le\<close> on
  tape \<open>j\<close> writes \<open>le\<close> back there (read-only) and moves only \<open>N\<close> or
  \<open>R\<close> (never-left).  Both halves fall out of the two facts above,
  needing no alphabet side-conditions.\<close>

lemma fr_delta_LE:
  assumes "(q, a, q', a', d) \<in> fr_delta Sg bl le F k N"
    and "a j = le"
  shows "a' j = le \<and> d j \<in> {dir.N, dir.R}"
  using fr_delta_no_write[OF assms(1)] fr_delta_move_no_L[OF assms(1)] assms(2)
  by simp


subsection \<open>Well-formedness\<close>

text \<open>The recogniser is a valid substrate machine.  The alphabet must
  be finite with the blank and left endmarker inside \<open>Gamma\<close> but
  outside \<open>Sg\<close>, and the tape count positive --- the standard machine
  hypotheses, exactly the data a concrete machine (or the combinator
  @{term finite_patch} built on this one) already carries.\<close>

lemma finite_recogniser_valid:
  assumes finG: "finite Gamma"
    and SgG:  "Sg \<subseteq> Gamma"
    and blG:  "bl \<in> Gamma"
    and blS:  "bl \<notin> Sg"
    and leG:  "le \<in> Gamma"
    and leS:  "le \<notin> Sg"
    and kpos: "0 < k"
  shows "valid_mttm (finite_recogniser Sg Gamma bl le F k)"
proof -
  have finSg: "finite Sg" using finite_subset[OF SgG finG] .
  have finP: "finite {u. set u \<subseteq> Sg \<and> length u \<le> fr_N F}"
    using finite_lists_length_le[OF finSg] by blast
  have finQ: "finite (FR_Scan ` {u. set u \<subseteq> Sg \<and> length u \<le> fr_N F}
                       \<union> {FR_Acc, FR_Rej})"
    using finP by simp
  have shape: "fr_delta Sg bl le F k (fr_N F)
      \<subseteq> (FR_Scan ` {u. set u \<subseteq> Sg \<and> length u \<le> fr_N F} \<union> {FR_Acc, FR_Rej}
           - {FR_Acc, FR_Rej})
         \<times> (UNIV \<rightarrow> Gamma)
         \<times> (FR_Scan ` {u. set u \<subseteq> Sg \<and> length u \<le> fr_N F} \<union> {FR_Acc, FR_Rej})
         \<times> (UNIV \<rightarrow> Gamma)
         \<times> (UNIV \<rightarrow> UNIV)"
    unfolding fr_delta_def fr_read_def
    using SgG blG leG by (auto simp: Pi_iff)
  have LEc: "\<forall>q a q' a' d j.
      (q, a, q', a', d) \<in> fr_delta Sg bl le F k (fr_N F)
        \<longrightarrow> a j = le \<longrightarrow> a' j = le \<and> d j \<in> {dir.N, dir.R}"
    by (auto dest: fr_delta_LE)
  have suppc: "\<forall>q a q' a' d.
      (q, a, q', a', d) \<in> fr_delta Sg bl le F k (fr_N F)
        \<longrightarrow> (\<forall>j \<ge> k. a j = bl \<and> a' j = bl \<and> d j = dir.N)"
    by (auto dest: fr_delta_support[OF kpos])
  show ?thesis
    unfolding finite_recogniser_def valid_mttm.simps
    using finQ finG SgG blG blS leG leS kpos shape LEc suppc
    by (intro conjI) auto
qed

text \<open>The recogniser is well-formed in the strengthened sense
  (@{const well_formed_mttm}): distinct start / accept / reject and
  distinct endmarker / blank, plus the left-endmarker write discipline
  --- the last free from read-only-ness.\<close>

lemma finite_recogniser_well_formed:
  assumes finG: "finite Gamma"
    and SgG:  "Sg \<subseteq> Gamma"
    and blG:  "bl \<in> Gamma"
    and blS:  "bl \<notin> Sg"
    and leG:  "le \<in> Gamma"
    and leS:  "le \<notin> Sg"
    and blle: "bl \<noteq> le"
    and kpos: "0 < k"
  shows "well_formed_mttm (finite_recogniser Sg Gamma bl le F k)"
proof -
  have lu: "le_unique (finite_recogniser Sg Gamma bl le F k)"
    unfolding le_unique_def finite_recogniser_delta_tm
    by (auto dest: fr_delta_no_write)
  have vd: "valid_mttm (finite_recogniser Sg Gamma bl le F k)"
    by (rule finite_recogniser_valid[OF finG SgG blG blS leG leS kpos])
  show ?thesis
    using vd lu blle
    by (auto simp: finite_recogniser_s_tm finite_recogniser_t_tm
                   finite_recogniser_r_tm finite_recogniser_le_tm
                   finite_recogniser_bl_tm)
qed


subsection \<open>Determinism\<close>

text \<open>The recogniser is deterministic.  The source state fixes the
  scanned prefix (constructor injectivity) and the read component
  fixes the scanned symbol (@{thm fr_read_inj}); the five transition
  families are then pairwise disjoint because the left endmarker, the
  blank, and the input alphabet are pairwise distinct.\<close>

lemma finite_recogniser_det:
  assumes leS: "le \<notin> Sg" and blS: "bl \<notin> Sg" and blle: "bl \<noteq> le"
  shows "det_mttm (finite_recogniser Sg Gamma bl le F k)"
  unfolding det_mttm_def finite_recogniser_delta_tm fr_delta_def
  using leS blS blle by (auto dest: fr_read_inj)


subsection \<open>The accepting run\<close>

text \<open>The configuration after the recogniser has read the left
  endmarker and the first \<open>m\<close> input symbols: state @{text "FR_Scan
  (take m w)"}, the (read-only, hence unchanging) input tape, and the
  input head at position \<open>m + 1\<close>.\<close>

definition fr_run_config ::
  "'a \<Rightarrow> 'a \<Rightarrow> nat \<Rightarrow> 'a list \<Rightarrow> nat \<Rightarrow> ('a, 'a fr_state) mt_config"
where
  "fr_run_config bl le k w m =
     Config\<^sub>M (FR_Scan (take m w))
       (\<lambda>i n. if i < k
              then (if n = 0 then le
                    else if i = 0 \<and> n \<le> length w then w ! (n - 1) else bl)
              else bl)
       (\<lambda>i. if i = 0 then m + 1 else 0)"

text \<open>One scan step: from the length-\<open>m\<close> scan configuration, reading
  the \<open>(m+1)\<close>-th input symbol advances to the length-\<open>(Suc m)\<close> one,
  provided the input still has a symbol there (\<open>m < length w\<close>) and the
  cutoff is not yet reached (\<open>m < fr_N F\<close>).\<close>

lemma fr_scan_step:
  assumes kpos: "0 < k" and mlt: "m < length w" and mN: "m < fr_N F"
    and wSg: "set w \<subseteq> Sg"
  shows "(fr_run_config bl le k w m, fr_run_config bl le k w (Suc m))
           \<in> mttm_step (fr_delta Sg bl le F k (fr_N F))"
proof -
  let ?x = "w ! m"
  let ?ts = "\<lambda>i n. if i < k
                    then (if n = 0 then le
                          else if i = 0 \<and> n \<le> length w then w ! (n - 1) else bl)
                    else bl"
  let ?nn = "\<lambda>i::nat. if i = 0 then m + 1 else 0"
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
  have tr: "(FR_Scan (take m w), fr_read bl le k ?x, FR_Scan (take (Suc m) w),
             fr_read bl le k ?x, fr_move dir.R) \<in> fr_delta Sg bl le F k (fr_N F)"
    unfolding fr_delta_def takeq using setu lenu mN xSg by auto
  have src: "fr_run_config bl le k w m = Config\<^sub>M (FR_Scan (take m w)) ?ts ?nn"
    by (simp add: fr_run_config_def)
  have step: "(Config\<^sub>M (FR_Scan (take m w)) ?ts ?nn,
               Config\<^sub>M (FR_Scan (take (Suc m) w))
                 (\<lambda>i. (?ts i)(?nn i := fr_read bl le k ?x i))
                 (\<lambda>i. go_dir (fr_move dir.R i) (?nn i)))
              \<in> mttm_step (fr_delta Sg bl le F k (fr_N F))"
  proof (rule mttm_step.step)
    show "(FR_Scan (take m w), \<lambda>i. ?ts i (?nn i), FR_Scan (take (Suc m) w),
           fr_read bl le k ?x, fr_move dir.R) \<in> fr_delta Sg bl le F k (fr_N F)"
      using tr by (simp add: read_eq)
  qed
  have tgt: "fr_run_config bl le k w (Suc m)
              = Config\<^sub>M (FR_Scan (take (Suc m) w))
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
    proof (rule ext)
      fix i show "go_dir (fr_move dir.R i) (?nn i) = (if i = 0 then Suc m + 1 else 0)"
        by (cases "i = 0") (simp_all add: fr_move_def)
    qed
    show ?thesis
      by (simp add: fr_run_config_def tape head)
  qed
  show ?thesis unfolding src tgt by (rule step)
qed

text \<open>Every word in \<open>F\<close> is no longer than the cutoff.\<close>

lemma fr_length_le_N:
  assumes "w \<in> F" and "finite F"
  shows "length w \<le> fr_N F"
proof -
  have "F \<noteq> {}" using assms(1) by auto
  hence "fr_N F = Max (length ` F)" by (simp add: fr_N_def)
  moreover have "length w \<in> length ` F" using assms(1) by simp
  ultimately show ?thesis using assms(2) by simp
qed

text \<open>The start step: from the initial configuration, reading the left
  endmarker advances into the length-\<open>0\<close> scan configuration.\<close>

lemma fr_le_step:
  assumes kpos: "0 < k"
  shows "(init_config_mttm (finite_recogniser Sg Gamma bl le F k) w,
          fr_run_config bl le k w 0)
           \<in> mttm_step (fr_delta Sg bl le F k (fr_N F))"
proof -
  let ?ts = "\<lambda>i n. if i < k
                    then (if n = 0 then le
                          else if i = 0 \<and> n \<le> length w then w ! (n - 1) else bl)
                    else bl"
  have read_eq: "(\<lambda>i. ?ts i ((\<lambda>_. 0) i)) = fr_read bl le k le"
  proof (rule ext)
    fix i show "?ts i ((\<lambda>_. 0) i) = fr_read bl le k le i"
      using kpos by (cases "i = 0") (auto simp: fr_read_def)
  qed
  have tr: "(FR_Scan [], fr_read bl le k le, FR_Scan [],
             fr_read bl le k le, fr_move dir.R) \<in> fr_delta Sg bl le F k (fr_N F)"
    unfolding fr_delta_def by auto
  have init_eq: "init_config_mttm (finite_recogniser Sg Gamma bl le F k) w
                   = Config\<^sub>M (FR_Scan []) ?ts (\<lambda>_. 0)"
    by (simp add: finite_recogniser_def)
  have step: "(Config\<^sub>M (FR_Scan []) ?ts (\<lambda>_. 0),
               Config\<^sub>M (FR_Scan [])
                 (\<lambda>i. (?ts i)((\<lambda>_. 0) i := fr_read bl le k le i))
                 (\<lambda>i. go_dir (fr_move dir.R i) ((\<lambda>_. 0) i)))
              \<in> mttm_step (fr_delta Sg bl le F k (fr_N F))"
  proof (rule mttm_step.step)
    show "(FR_Scan [], \<lambda>i. ?ts i ((\<lambda>_. 0) i), FR_Scan [],
           fr_read bl le k le, fr_move dir.R) \<in> fr_delta Sg bl le F k (fr_N F)"
      using tr by (simp add: read_eq)
  qed
  have tgt: "fr_run_config bl le k w 0
              = Config\<^sub>M (FR_Scan [])
                  (\<lambda>i. (?ts i)((\<lambda>_. 0) i := fr_read bl le k le i))
                  (\<lambda>i. go_dir (fr_move dir.R i) ((\<lambda>_. 0) i))"
  proof -
    have tape: "(\<lambda>i. (?ts i)((\<lambda>_. 0) i := fr_read bl le k le i)) = ?ts"
    proof (rule ext)
      fix i
      have eq: "fr_read bl le k le i = ?ts i ((\<lambda>_. 0) i)"
        using kpos by (cases "i = 0") (auto simp: fr_read_def)
      show "(?ts i)((\<lambda>_. 0) i := fr_read bl le k le i) = ?ts i"
        unfolding eq by (rule fun_upd_triv)
    qed
    have head: "(\<lambda>i. go_dir (fr_move dir.R i) ((\<lambda>_. 0) i))
                  = (\<lambda>i::nat. if i = 0 then 0 + 1 else 0)"
    proof (rule ext)
      fix i show "go_dir (fr_move dir.R i) ((\<lambda>_. 0) i) = (if i = 0 then 0 + 1 else 0)"
        by (cases "i = 0") (simp_all add: fr_move_def)
    qed
    show ?thesis by (simp add: fr_run_config_def tape head)
  qed
  show ?thesis unfolding init_eq tgt by (rule step)
qed

text \<open>The accept step: from the fully-scanned configuration (prefix
  \<open>w\<close>), reading the end-of-input blank accepts, provided \<open>w \<in> F\<close>.\<close>

lemma fr_accept_step:
  assumes wF: "w \<in> F" and wSg: "set w \<subseteq> Sg" and finF: "finite F"
  shows "(fr_run_config bl le k w (length w),
          Config\<^sub>M FR_Acc
            (\<lambda>i n. if i < k
                   then (if n = 0 then le
                         else if i = 0 \<and> n \<le> length w then w ! (n - 1) else bl)
                   else bl)
            (\<lambda>i::nat. if i = 0 then length w + 1 else 0))
           \<in> mttm_step (fr_delta Sg bl le F k (fr_N F))"
proof -
  let ?ts = "\<lambda>i n. if i < k
                    then (if n = 0 then le
                          else if i = 0 \<and> n \<le> length w then w ! (n - 1) else bl)
                    else bl"
  let ?nn = "\<lambda>i::nat. if i = 0 then length w + 1 else 0"
  have lenN: "length w \<le> fr_N F" using fr_length_le_N[OF wF finF] .
  have read_eq: "(\<lambda>i. ?ts i (?nn i)) = fr_read bl le k bl"
  proof (rule ext)
    fix i show "?ts i (?nn i) = fr_read bl le k bl i"
      by (cases "i = 0") (auto simp: fr_read_def)
  qed
  have tr: "(FR_Scan w, fr_read bl le k bl, FR_Acc,
             fr_read bl le k bl, fr_move dir.N) \<in> fr_delta Sg bl le F k (fr_N F)"
    unfolding fr_delta_def using wSg lenN wF by auto
  have src: "fr_run_config bl le k w (length w) = Config\<^sub>M (FR_Scan w) ?ts ?nn"
    by (simp add: fr_run_config_def)
  have step: "(Config\<^sub>M (FR_Scan w) ?ts ?nn,
               Config\<^sub>M FR_Acc
                 (\<lambda>i. (?ts i)(?nn i := fr_read bl le k bl i))
                 (\<lambda>i. go_dir (fr_move dir.N i) (?nn i)))
              \<in> mttm_step (fr_delta Sg bl le F k (fr_N F))"
  proof (rule mttm_step.step)
    show "(FR_Scan w, \<lambda>i. ?ts i (?nn i), FR_Acc,
           fr_read bl le k bl, fr_move dir.N) \<in> fr_delta Sg bl le F k (fr_N F)"
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
  show ?thesis
    unfolding src using step by (simp add: tape head)
qed

text \<open>The scan phase: iterating the scan step reads all of \<open>w\<close>,
  reaching the fully-scanned configuration in \<open>length w\<close> steps.
  Assembled by the substrate's bounded-iteration combinator
  @{thm[source] relpow_invariant_chain}.\<close>

lemma fr_scan_chain:
  assumes kpos: "0 < k" and wF: "w \<in> F" and wSg: "set w \<subseteq> Sg" and finF: "finite F"
  shows "(fr_run_config bl le k w 0, fr_run_config bl le k w (length w))
           \<in> (mttm_step (fr_delta Sg bl le F k (fr_N F))) ^^ (length w)"
proof -
  have lenN: "length w \<le> fr_N F" using fr_length_le_N[OF wF finF] .
  have "\<exists>c'. (fr_run_config bl le k w 0, c')
               \<in> (mttm_step (fr_delta Sg bl le F k (fr_N F))) ^^ (length w)
             \<and> c' = fr_run_config bl le k w (length w)"
  proof (rule relpow_invariant_chain[where P = "\<lambda>i c. c = fr_run_config bl le k w i"])
    fix i c assume ilt: "i < length w" and Pi: "c = fr_run_config bl le k w i"
    have iN: "i < fr_N F" using ilt lenN by linarith
    have "(fr_run_config bl le k w i, fr_run_config bl le k w (Suc i))
            \<in> mttm_step (fr_delta Sg bl le F k (fr_N F))"
      by (rule fr_scan_step[OF kpos ilt iN wSg])
    thus "\<exists>c'. (c, c') \<in> mttm_step (fr_delta Sg bl le F k (fr_N F))
                \<and> c' = fr_run_config bl le k w (Suc i)"
      using Pi by blast
  next
    show "fr_run_config bl le k w 0 = fr_run_config bl le k w 0" by (rule refl)
  qed
  thus ?thesis by blast
qed

text \<open>The full accepting run: for a member \<open>w\<close>, the recogniser reaches
  its accept state from the initial configuration in \<open>length w + 2\<close>
  steps --- the start step, the \<open>length w\<close> scan steps, and the accept
  step.\<close>

lemma fr_accepting_run:
  assumes kpos: "0 < k" and wF: "w \<in> F" and wSg: "set w \<subseteq> Sg" and finF: "finite F"
  shows "\<exists>c. (init_config_mttm (finite_recogniser Sg Gamma bl le F k) w, c)
               \<in> (mttm_step (fr_delta Sg bl le F k (fr_N F))) ^^ (length w + 2)
             \<and> mt_state c = FR_Acc"
proof -
  let ?R = "mttm_step (fr_delta Sg bl le F k (fr_N F))"
  let ?init = "init_config_mttm (finite_recogniser Sg Gamma bl le F k) w"
  let ?acc = "Config\<^sub>M FR_Acc
                (\<lambda>i n. if i < k
                       then (if n = 0 then le
                             else if i = 0 \<and> n \<le> length w then w ! (n - 1) else bl)
                       else bl)
                (\<lambda>i::nat. if i = 0 then length w + 1 else 0)"
  have le1: "(?init, fr_run_config bl le k w 0) \<in> ?R ^^ 1"
    using fr_le_step[OF kpos] by simp
  have sc: "(fr_run_config bl le k w 0, fr_run_config bl le k w (length w)) \<in> ?R ^^ (length w)"
    using fr_scan_chain[OF kpos wF wSg finF] .
  have ac: "(fr_run_config bl le k w (length w), ?acc) \<in> ?R ^^ 1"
    using fr_accept_step[OF wF wSg finF] by simp
  have t1: "(?init, fr_run_config bl le k w (length w)) \<in> ?R ^^ (1 + length w)"
    by (rule relpow_transI[OF le1 sc])
  have t2: "(?init, ?acc) \<in> ?R ^^ (1 + length w + 1)"
    by (rule relpow_transI[OF t1 ac])
  have "(?init, ?acc) \<in> ?R ^^ (length w + 2)" using t2 by (simp add: add.commute)
  moreover have "mt_state ?acc = FR_Acc" by simp
  ultimately show ?thesis by blast
qed

text \<open>Consequently a member is accepted within \<open>length w + 2\<close> steps.
  (The extra \<open>+2\<close> over the classical \<open>n+1\<close> is the substrate's left
  endmarker read, which the textbook model has no counterpart for.)\<close>

lemma finite_recogniser_accepts:
  assumes kpos: "0 < k" and wF: "w \<in> F" and wSg: "set w \<subseteq> Sg" and finF: "finite F"
  shows "accepts_in_time_mttm (finite_recogniser Sg Gamma bl le F k) w (length w + 2)"
proof -
  obtain c where c: "(init_config_mttm (finite_recogniser Sg Gamma bl le F k) w, c)
                        \<in> (mttm_step (fr_delta Sg bl le F k (fr_N F))) ^^ (length w + 2)"
             and cst: "mt_state c = FR_Acc"
    using fr_accepting_run[OF kpos wF wSg finF] by blast
  show ?thesis
    unfolding accepts_in_time_mttm_def finite_recogniser_delta_tm finite_recogniser_t_tm
    using c cst by blast
qed

text \<open>Completeness half of the language characterisation: every member
  is accepted, hence in the language.\<close>

lemma finite_recogniser_lang_complete:
  assumes kpos: "0 < k" and Fsub: "\<forall>w\<in>F. set w \<subseteq> Sg" and finF: "finite F"
  shows "F \<subseteq> Lang_mttm (finite_recogniser Sg Gamma bl le F k)"
proof
  fix w assume wF: "w \<in> F"
  have wSg: "set w \<subseteq> Sg" using Fsub wF by blast
  obtain c where c: "(init_config_mttm (finite_recogniser Sg Gamma bl le F k) w, c)
                        \<in> (mttm_step (fr_delta Sg bl le F k (fr_N F))) ^^ (length w + 2)"
             and cst: "mt_state c = FR_Acc"
    using fr_accepting_run[OF kpos wF wSg finF] by blast
  obtain w' n where c_eq: "c = Config\<^sub>M FR_Acc w' n"
    using cst by (cases c) auto
  have reach: "(init_config_mttm (finite_recogniser Sg Gamma bl le F k) w,
                Config\<^sub>M FR_Acc w' n)
                 \<in> (mttm_step (fr_delta Sg bl le F k (fr_N F)))\<^sup>*"
    using c c_eq by (metis relpow_imp_rtrancl)
  show "w \<in> Lang_mttm (finite_recogniser Sg Gamma bl le F k)"
    unfolding Lang_mttm_def finite_recogniser_Sigma_tm finite_recogniser_t_tm
              finite_recogniser_delta_tm
    using wSg reach by blast
qed


subsection \<open>Soundness of the run\<close>

text \<open>Every recogniser transition, and hence every recogniser step,
  starts from a scan state --- so the two halting states are sinks.\<close>

lemma fr_delta_src_scan:
  "(q, a, q', a', d) \<in> fr_delta Sg bl le F k N \<Longrightarrow> \<exists>u. q = FR_Scan u"
  by (auto simp: fr_delta_def)

lemma fr_step_src_scan:
  assumes "(c, c') \<in> mttm_step (fr_delta Sg bl le F k N)"
  shows "\<exists>u. mt_state c = FR_Scan u"
proof -
  from assms obtain q ts n q' a d where
      c_eq: "c = Config\<^sub>M q ts n"
    and tr: "(q, \<lambda>k. ts k (n k), q', a, d) \<in> fr_delta Sg bl le F k N"
    by (auto elim: mttm_step.cases)
  from fr_delta_src_scan[OF tr] obtain u where "q = FR_Scan u" by blast
  thus ?thesis using c_eq by auto
qed

text \<open>The overflow step: at the cutoff (\<open>m = fr_N F\<close>) with input still
  remaining (\<open>m < length w\<close>), reading the next symbol rejects.\<close>

lemma fr_overflow_step:
  assumes kpos: "0 < k" and mlt: "m < length w" and mN: "m = fr_N F"
    and wSg: "set w \<subseteq> Sg"
  shows "\<exists>c'. (fr_run_config bl le k w m, c')
               \<in> mttm_step (fr_delta Sg bl le F k (fr_N F)) \<and> mt_state c' = FR_Rej"
proof -
  let ?x = "w ! m"
  let ?ts = "\<lambda>i n. if i < k
                    then (if n = 0 then le
                          else if i = 0 \<and> n \<le> length w then w ! (n - 1) else bl)
                    else bl"
  let ?nn = "\<lambda>i::nat. if i = 0 then m + 1 else 0"
  let ?tgt = "Config\<^sub>M FR_Rej
                (\<lambda>i. (?ts i)(?nn i := fr_read bl le k ?x i))
                (\<lambda>i. go_dir (fr_move dir.N i) (?nn i))"
  have xSg: "?x \<in> Sg" using nth_mem[OF mlt] wSg by blast
  have lenu: "length (take m w) = m" using mlt by simp
  have setu: "set (take m w) \<subseteq> Sg"
    using wSg by (meson set_take_subset subset_trans)
  have read_eq: "(\<lambda>i. ?ts i (?nn i)) = fr_read bl le k ?x"
  proof (rule ext)
    fix i show "?ts i (?nn i) = fr_read bl le k ?x i"
      using kpos mlt by (cases "i = 0") (auto simp: fr_read_def)
  qed
  have tr: "(FR_Scan (take m w), fr_read bl le k ?x, FR_Rej,
             fr_read bl le k ?x, fr_move dir.N) \<in> fr_delta Sg bl le F k (fr_N F)"
    unfolding fr_delta_def using setu lenu mN xSg by auto
  have src: "fr_run_config bl le k w m = Config\<^sub>M (FR_Scan (take m w)) ?ts ?nn"
    by (simp add: fr_run_config_def)
  have step: "(fr_run_config bl le k w m, ?tgt)
                \<in> mttm_step (fr_delta Sg bl le F k (fr_N F))"
    unfolding src
  proof (rule mttm_step.step)
    show "(FR_Scan (take m w), \<lambda>i. ?ts i (?nn i), FR_Rej,
           fr_read bl le k ?x, fr_move dir.N) \<in> fr_delta Sg bl le F k (fr_N F)"
      using tr by (simp add: read_eq)
  qed
  have "(fr_run_config bl le k w m, ?tgt)
          \<in> mttm_step (fr_delta Sg bl le F k (fr_N F)) \<and> mt_state ?tgt = FR_Rej"
    using step by simp
  thus ?thesis by blast
qed

text \<open>The end-reject step: reading the end-of-input blank on a
  non-member prefix rejects.\<close>

lemma fr_reject_step:
  assumes wnF: "w \<notin> F" and wSg: "set w \<subseteq> Sg" and lenN: "length w \<le> fr_N F"
  shows "\<exists>c'. (fr_run_config bl le k w (length w), c')
               \<in> mttm_step (fr_delta Sg bl le F k (fr_N F)) \<and> mt_state c' = FR_Rej"
proof -
  let ?ts = "\<lambda>i n. if i < k
                    then (if n = 0 then le
                          else if i = 0 \<and> n \<le> length w then w ! (n - 1) else bl)
                    else bl"
  let ?nn = "\<lambda>i::nat. if i = 0 then length w + 1 else 0"
  let ?tgt = "Config\<^sub>M FR_Rej
                (\<lambda>i. (?ts i)(?nn i := fr_read bl le k bl i))
                (\<lambda>i. go_dir (fr_move dir.N i) (?nn i))"
  have read_eq: "(\<lambda>i. ?ts i (?nn i)) = fr_read bl le k bl"
  proof (rule ext)
    fix i show "?ts i (?nn i) = fr_read bl le k bl i"
      by (cases "i = 0") (auto simp: fr_read_def)
  qed
  have tr: "(FR_Scan w, fr_read bl le k bl, FR_Rej,
             fr_read bl le k bl, fr_move dir.N) \<in> fr_delta Sg bl le F k (fr_N F)"
    unfolding fr_delta_def using wSg lenN wnF by auto
  have src: "fr_run_config bl le k w (length w) = Config\<^sub>M (FR_Scan w) ?ts ?nn"
    by (simp add: fr_run_config_def)
  have step: "(fr_run_config bl le k w (length w), ?tgt)
                \<in> mttm_step (fr_delta Sg bl le F k (fr_N F))"
    unfolding src
  proof (rule mttm_step.step)
    show "(FR_Scan w, \<lambda>i. ?ts i (?nn i), FR_Rej,
           fr_read bl le k bl, fr_move dir.N) \<in> fr_delta Sg bl le F k (fr_N F)"
      using tr by (simp add: read_eq)
  qed
  have "(fr_run_config bl le k w (length w), ?tgt)
          \<in> mttm_step (fr_delta Sg bl le F k (fr_N F)) \<and> mt_state ?tgt = FR_Rej"
    using step by simp
  thus ?thesis by blast
qed

text \<open>The reachability invariant: from the initial configuration on an
  input over \<open>Sg\<close>, every reachable configuration is the initial one, a
  scan configuration below the cutoff, a reject, or an accept that
  certifies \<open>w \<in> F\<close>.\<close>

definition fr_inv ::
  "'a set \<Rightarrow> 'a set \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a list set \<Rightarrow> nat \<Rightarrow> 'a list
     \<Rightarrow> ('a, 'a fr_state) mt_config \<Rightarrow> bool"
where
  "fr_inv Sg Gamma bl le F k w c \<longleftrightarrow>
     (\<exists>m. m \<le> length w \<and> m \<le> fr_N F \<and> c = fr_run_config bl le k w m)
     \<or> c = init_config_mttm (finite_recogniser Sg Gamma bl le F k) w
     \<or> mt_state c = FR_Rej
     \<or> (mt_state c = FR_Acc \<and> w \<in> F)"

text \<open>Closure of the invariant under a step.  Each canonical
  configuration has a single successor (determinism, via
  @{thm[source] mttm_step_functional}), given by the matching step
  lemma; the two halting states are sinks
  (@{thm[source] fr_step_src_scan}).\<close>

lemma fr_inv_closed:
  assumes leS: "le \<notin> Sg" and blS: "bl \<notin> Sg" and blle: "bl \<noteq> le"
    and kpos: "0 < k" and finF: "finite F" and wSg: "set w \<subseteq> Sg"
    and inv: "fr_inv Sg Gamma bl le F k w c"
    and step: "(c, c') \<in> mttm_step (fr_delta Sg bl le F k (fr_N F))"
  shows "fr_inv Sg Gamma bl le F k w c'"
proof -
  have fdet: "\<forall>q a p\<^sub>1 b\<^sub>1 d\<^sub>1 p\<^sub>2 b\<^sub>2 d\<^sub>2.
      (q, a, p\<^sub>1, b\<^sub>1, d\<^sub>1) \<in> fr_delta Sg bl le F k (fr_N F)
        \<longrightarrow> (q, a, p\<^sub>2, b\<^sub>2, d\<^sub>2) \<in> fr_delta Sg bl le F k (fr_N F)
        \<longrightarrow> (p\<^sub>1, b\<^sub>1, d\<^sub>1) = (p\<^sub>2, b\<^sub>2, d\<^sub>2)"
    using finite_recogniser_det[OF leS blS blle]
    unfolding det_mttm_def finite_recogniser_delta_tm by blast
  from inv[unfolded fr_inv_def] show ?thesis
  proof (elim disjE)
    assume "\<exists>m. m \<le> length w \<and> m \<le> fr_N F \<and> c = fr_run_config bl le k w m"
    then obtain m where mlw: "m \<le> length w" and mN: "m \<le> fr_N F"
      and c_eq: "c = fr_run_config bl le k w m" by blast
    show ?thesis
    proof (cases "m < length w")
      case True
      show ?thesis
      proof (cases "m < fr_N F")
        case True
        have s: "(c, fr_run_config bl le k w (Suc m))
                   \<in> mttm_step (fr_delta Sg bl le F k (fr_N F))"
          using fr_scan_step[OF kpos \<open>m < length w\<close> True wSg] c_eq by simp
        have "c' = fr_run_config bl le k w (Suc m)"
          using mttm_step_functional[OF fdet step s] .
        moreover have "Suc m \<le> length w" using \<open>m < length w\<close> by simp
        moreover have "Suc m \<le> fr_N F" using True by simp
        ultimately show ?thesis unfolding fr_inv_def by blast
      next
        case False
        hence mEq: "m = fr_N F" using mN by simp
        obtain d where d: "(fr_run_config bl le k w m, d)
                             \<in> mttm_step (fr_delta Sg bl le F k (fr_N F))"
          and dst: "mt_state d = FR_Rej"
          using fr_overflow_step[OF kpos \<open>m < length w\<close> mEq wSg] by blast
        have "c' = d" using mttm_step_functional[OF fdet step] d c_eq by simp
        thus ?thesis unfolding fr_inv_def using dst by simp
      qed
    next
      case False
      hence mEq: "m = length w" using mlw by simp
      have lenN: "length w \<le> fr_N F" using mEq mN by simp
      show ?thesis
      proof (cases "w \<in> F")
        case True
        have acc: "(c, Config\<^sub>M FR_Acc
                       (\<lambda>i n. if i < k
                              then (if n = 0 then le
                                    else if i = 0 \<and> n \<le> length w
                                         then w ! (n - 1) else bl)
                              else bl)
                       (\<lambda>i::nat. if i = 0 then length w + 1 else 0))
                     \<in> mttm_step (fr_delta Sg bl le F k (fr_N F))"
          using fr_accept_step[OF True wSg finF] c_eq mEq by simp
        have "c' = Config\<^sub>M FR_Acc
                     (\<lambda>i n. if i < k
                            then (if n = 0 then le
                                  else if i = 0 \<and> n \<le> length w
                                       then w ! (n - 1) else bl)
                            else bl)
                     (\<lambda>i::nat. if i = 0 then length w + 1 else 0)"
          using mttm_step_functional[OF fdet step acc] .
        thus ?thesis unfolding fr_inv_def using True by simp
      next
        case False
        obtain d where d: "(fr_run_config bl le k w (length w), d)
                             \<in> mttm_step (fr_delta Sg bl le F k (fr_N F))"
          and dst: "mt_state d = FR_Rej"
          using fr_reject_step[OF False wSg lenN] by blast
        have "(c, d) \<in> mttm_step (fr_delta Sg bl le F k (fr_N F))"
          using d c_eq mEq by simp
        hence "c' = d" using mttm_step_functional[OF fdet step] by blast
        thus ?thesis unfolding fr_inv_def using dst by simp
      qed
    qed
  next
    assume ini: "c = init_config_mttm (finite_recogniser Sg Gamma bl le F k) w"
    have s: "(c, fr_run_config bl le k w 0)
               \<in> mttm_step (fr_delta Sg bl le F k (fr_N F))"
      using fr_le_step[OF kpos] ini by simp
    have "c' = fr_run_config bl le k w 0"
      using mttm_step_functional[OF fdet step s] .
    thus ?thesis unfolding fr_inv_def by auto
  next
    assume "mt_state c = FR_Rej"
    thus ?thesis using fr_step_src_scan[OF step] by auto
  next
    assume "mt_state c = FR_Acc \<and> w \<in> F"
    thus ?thesis using fr_step_src_scan[OF step] by auto
  qed
qed

text \<open>State of the two canonical non-halting configurations.\<close>

lemma mt_state_fr_run_config:
  "mt_state (fr_run_config bl le k w m) = FR_Scan (take m w)"
  by (simp add: fr_run_config_def)

lemma mt_state_init_finite_recogniser:
  "mt_state (init_config_mttm (finite_recogniser Sg Gamma bl le F k) w) = FR_Scan []"
  by (simp add: finite_recogniser_def)

text \<open>The invariant holds at every reachable configuration
  (@{thm[source] rtrancl_induct} from the initial configuration, using
  closure).\<close>

lemma fr_inv_reach:
  assumes leS: "le \<notin> Sg" and blS: "bl \<notin> Sg" and blle: "bl \<noteq> le"
    and kpos: "0 < k" and finF: "finite F" and wSg: "set w \<subseteq> Sg"
    and reach: "(init_config_mttm (finite_recogniser Sg Gamma bl le F k) w, c)
                  \<in> (mttm_step (fr_delta Sg bl le F k (fr_N F)))\<^sup>*"
  shows "fr_inv Sg Gamma bl le F k w c"
  using reach
proof (induction rule: rtrancl_induct)
  case base
  show ?case unfolding fr_inv_def by simp
next
  case (step y z)
  show ?case
    by (rule fr_inv_closed[OF leS blS blle kpos finF wSg step.IH step.hyps(2)])
qed

text \<open>An accepting reachable configuration certifies membership: the
  other invariant disjuncts have a non-accept state.\<close>

lemma fr_inv_acc_imp_mem:
  assumes "fr_inv Sg Gamma bl le F k w c" and "mt_state c = FR_Acc"
  shows "w \<in> F"
  using assms unfolding fr_inv_def
  by (auto simp: mt_state_fr_run_config mt_state_init_finite_recogniser)

text \<open>Soundness half of the language characterisation: only members
  are accepted.\<close>

lemma finite_recogniser_lang_sound:
  assumes leS: "le \<notin> Sg" and blS: "bl \<notin> Sg" and blle: "bl \<noteq> le"
    and kpos: "0 < k" and finF: "finite F"
  shows "Lang_mttm (finite_recogniser Sg Gamma bl le F k) \<subseteq> F"
proof
  fix w assume wL: "w \<in> Lang_mttm (finite_recogniser Sg Gamma bl le F k)"
  from wL[unfolded Lang_mttm_def finite_recogniser_Sigma_tm finite_recogniser_t_tm]
  obtain w' n where wSg: "set w \<subseteq> Sg"
    and r: "(init_config_mttm (finite_recogniser Sg Gamma bl le F k) w,
             Config\<^sub>M FR_Acc w' n)
              \<in> (mttm_step (delta_tm (finite_recogniser Sg Gamma bl le F k)))\<^sup>*"
    by auto
  have r': "(init_config_mttm (finite_recogniser Sg Gamma bl le F k) w,
             Config\<^sub>M FR_Acc w' n)
              \<in> (mttm_step (fr_delta Sg bl le F k (fr_N F)))\<^sup>*"
    using r by (simp add: finite_recogniser_delta_tm)
  have inv: "fr_inv Sg Gamma bl le F k w (Config\<^sub>M FR_Acc w' n)"
    by (rule fr_inv_reach[OF leS blS blle kpos finF wSg r'])
  show "w \<in> F" using fr_inv_acc_imp_mem[OF inv] by simp
qed

text \<open>The language characterisation: the recogniser decides exactly
  \<open>F\<close>.\<close>

theorem finite_recogniser_language:
  assumes leS: "le \<notin> Sg" and blS: "bl \<notin> Sg" and blle: "bl \<noteq> le"
    and kpos: "0 < k" and finF: "finite F" and Fsub: "\<forall>w\<in>F. set w \<subseteq> Sg"
  shows "Lang_mttm (finite_recogniser Sg Gamma bl le F k) = F"
  using finite_recogniser_lang_complete[OF kpos Fsub finF]
        finite_recogniser_lang_sound[OF leS blS blle kpos finF]
  by blast


end
