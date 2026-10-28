theory Multitape_Substrate
  imports Multitape_Substrate_Core
begin

section \<open>Basic facts about machines and runs\<close>

text \<open>The substrate metatheory --- \<^emph>\<open>our\<close> additions over the
  Dalvit--Thiemann definition surface isolated in \<open>Multitape_Substrate_Core\<close>:
  relation-power and finiteness utilities, the \<open>valid_ktm\<close>
  axiom-extraction toolkit, per-step and reachability validity
  preservation, and the displacement / left-endmarker / no-write tape
  tools.  The core (\<open>Multitape_Substrate_Core\<close>) carries the datatypes, accessors,
  step relation, and the validity / language definitions.\<close>


subsection \<open>Relation powers and finiteness\<close>

lemma finite_UNIV_move [simp, intro]: "finite (UNIV :: move set)"
proof -
  have id: "UNIV = {MoveL, MoveR, MoveN}"
    using move.exhaust by auto
  show ?thesis unfolding id by auto
qed

text \<open>Blank-tail finiteness: the set of total functions \<open>nat \<Rightarrow> 'b\<close>
  ranging in a finite codomain \<open>B\<close> and \<^emph>\<open>constant \<open>c\<close> beyond an
  index \<open>k\<close>\<close> is finite.  This replaces the function-space finiteness
  lemmas (\<open>fin_funcsetI\<close> / \<open>finite_UNIV_fun_dir\<close>) that the AFP source
  relied on: those are false at the value-level \<open>nat\<close> index, where
  the domain is infinite.  Finiteness is recovered from the support
  bound — a blank-tail function is determined by its restriction to
  \<open>{..<k}\<close>, of which there are finitely many.  Used to re-derive
  \<open>finite \<delta>\<close> for constructed machines (\<open>valid_ktm_finite_delta\<close>),
  with codomain \<open>\<Gamma>\<close> (blank tail) for read/write tuples and \<open>move\<close>
  (\<open>MoveN\<close> tail) for the move tuples.\<close>

lemma finite_tail_const_funcs:
  fixes B :: "'b set" and k :: nat and c :: 'b
  assumes finB: "finite B"
  shows "finite {f :: nat \<Rightarrow> 'b. (\<forall>j. f j \<in> B) \<and> (\<forall>j \<ge> k. f j = c)}"
proof -
  let ?S = "{f :: nat \<Rightarrow> 'b. (\<forall>j. f j \<in> B) \<and> (\<forall>j \<ge> k. f j = c)}"
  have inj: "inj_on (\<lambda>f. restrict f {..<k}) ?S"
  proof (rule inj_onI)
    fix f g
    assume f: "f \<in> ?S" and g: "g \<in> ?S"
      and eq: "restrict f {..<k} = restrict g {..<k}"
    show "f = g"
    proof
      fix j
      show "f j = g j"
      proof (cases "j < k")
        case True
        have "restrict f {..<k} j = restrict g {..<k} j" using eq by simp
        thus ?thesis using True by (simp add: restrict_def)
      next
        case False
        hence "k \<le> j" by simp
        with f g show ?thesis by simp
      qed
    qed
  qed
  have rng: "(\<lambda>f. restrict f {..<k}) ` ?S \<subseteq> ({..<k} \<rightarrow>\<^sub>E B)"
  proof
    fix h assume "h \<in> (\<lambda>f. restrict f {..<k}) ` ?S"
    then obtain f where f: "f \<in> ?S" and h: "h = restrict f {..<k}" by blast
    show "h \<in> {..<k} \<rightarrow>\<^sub>E B"
      using f unfolding h by (simp add: restrict_PiE Pi_iff)
  qed
  have finPiE: "finite ({..<k} \<rightarrow>\<^sub>E B)" using finB by (simp add: finite_PiE)
  have "finite ((\<lambda>f. restrict f {..<k}) ` ?S)"
    by (rule finite_subset[OF rng finPiE])
  thus "finite ?S" using inj by (rule finite_imageD)
qed

text \<open>Runs compose by HOL's \<open>relpow_trans\<close>.  Monotonicity in the relation is
  HOL's predicate lemma \<open>relpowp_mono\<close>, restated for relations as sets.\<close>

lemma relpow_subset_mono: fixes R :: "'a rel"
  shows "R \<subseteq> S \<Longrightarrow> R^^n \<subseteq> S^^n"
  by (induct n, auto)

text \<open>Bounded-iteration combinator: given a single-step law that,
  from any config satisfying an index-parameterised invariant
  \<open>P i\<close> with \<open>i < n\<close>, takes one \<open>R\<close>-step to a config satisfying
  \<open>P (Suc i)\<close>, iterate it: from \<open>P 0 c\<^sub>0\<close> reach a \<open>c'\<close> with
  \<open>(c\<^sub>0, c') \<in> R\<^bsup>n\<^esup>\<close> and \<open>P n c'\<close>.  A loop whose counter
  starts at some \<open>off > 0\<close> instantiates \<open>P\<close> to re-index by that
  offset.  Proved by induction generalising \<^emph>\<open>both\<close> the start
  config and the invariant, so the hypothesis applies to the shifted
  predicate \<open>\<lambda>j. P (Suc j)\<close> after peeling the first step
  (prepended via \<open>relpow_Suc_I2\<close>).\<close>

lemma relpow_invariant_chain:
  fixes R :: "('s \<times> 's) set"
    and P :: "nat \<Rightarrow> 's \<Rightarrow> bool"
  assumes step: "\<And>i c. \<lbrakk> i < n; P i c \<rbrakk>
                          \<Longrightarrow> \<exists>c'. (c, c') \<in> R \<and> P (Suc i) c'"
      and base: "P 0 c0"
  shows "\<exists>c'. (c0, c') \<in> R ^^ n \<and> P n c'"
  using assms
proof (induction n arbitrary: c0)
  case 0
  show ?case using "0.prems"(2) by auto
next
  case (Suc m)
  have step_m:
      "\<And>i c. \<lbrakk> i < m; P i c \<rbrakk>
              \<Longrightarrow> \<exists>c'. (c, c') \<in> R \<and> P (Suc i) c'"
  proof -
    fix i :: nat and c :: 's
    assume "i < m" and "P i c"
    thus "\<exists>c'. (c, c') \<in> R \<and> P (Suc i) c'"
      using Suc.prems(1)[of i c] by simp
  qed
  obtain c_m where chain_m: "(c0, c_m) \<in> R ^^ m" and Pcm: "P m c_m"
    using Suc.IH[OF step_m Suc.prems(2)] by blast
  obtain c' where last_step: "(c_m, c') \<in> R" and Pc': "P (Suc m) c'"
    using Suc.prems(1)[of m c_m] Pcm by auto
  have "(c0, c') \<in> R ^^ Suc m"
    using chain_m last_step by (rule relpow_Suc_I)
  thus ?case using Pc' by blast
qed

text \<open>\<^bold>\<open>A step simulation is a run simulation.\<close>  A construction that
  re-encodes configurations by a map \<open>h\<close> proves that each step of the
  source is a step of the target on the images, and wants the same of a run
  of any length.  The step may assume its source was reached from the run's
  start: the encodings that are steps only on reachable configurations (a
  valid one, or one with its endmarkers in place) discharge that by the
  relational-power forms of their invariants.\<close>

lemma relpow_map:
  assumes step: "\<And>m x y. (a, x) \<in> R ^^ m \<Longrightarrow> (x, y) \<in> R \<Longrightarrow> (h x, h y) \<in> S"
      and run: "(a, b) \<in> R ^^ n"
  shows "(h a, h b) \<in> S ^^ n"
  using run
proof (induction n arbitrary: b)
  case 0
  then show ?case by simp
next
  case (Suc n)
  from Suc.prems obtain x where ax: "(a, x) \<in> R ^^ n" and xb: "(x, b) \<in> R"
    by (rule relpow_Suc_E)
  from Suc.IH [OF ax] step [OF ax xb] show ?case by (rule relpow_Suc_I)
qed


subsection \<open>Uniqueness on a deterministic region\<close>

text \<open>\<^bold>\<open>\<open>det_ktm_relpow_unique\<close> (below) for a machine that is
  deterministic only somewhere.\<close>  A nondeterministic machine can still have large regions in
  which it branches nowhere, and a run that stays inside one of those is as
  pinned as a deterministic machine's.  What makes the statement usable is
  that both hypotheses are about the \<^emph>\<open>region\<close> rather than about the
  relation: \<open>R\<close> is closed under a step, and a step out of \<open>R\<close> is unique.

  The induction cannot be traded for \<^theory_text>\<open>single_valued_relpow\<close> the way
  \<open>det_ktm_relpow_unique\<close>'s was.  Restricting the relation to \<open>R\<close> does make it
  single-valued, but showing that an unrestricted run \<^emph>\<open>is\<close> a
  restricted one is the same induction again --- the closure has to be
  carried along the run, and that is precisely what the induction does.

  Stated for a bare relation because nothing here is about machines.\<close>

lemma relpow_unique_on:
  assumes closed: "\<And>x y. x \<in> R \<Longrightarrow> (x, y) \<in> S \<Longrightarrow> y \<in> R"
      and fn: "\<And>x y z. x \<in> R \<Longrightarrow> (x, y) \<in> S \<Longrightarrow> (x, z) \<in> S
                       \<Longrightarrow> y = z"
  shows "x \<in> R \<Longrightarrow> (x, y) \<in> S ^^ n \<Longrightarrow> (x, z) \<in> S ^^ n \<Longrightarrow> y = z"
proof (induct n arbitrary: x y z)
  case 0
  then show ?case by simp
next
  case (Suc n)
  from Suc.prems(2) obtain u where xu: "(x, u) \<in> S" and uy: "(u, y) \<in> S ^^ n"
    by (blast dest: relpow_Suc_D2)
  from Suc.prems(3) obtain v where xv: "(x, v) \<in> S" and vz: "(v, z) \<in> S ^^ n"
    by (blast dest: relpow_Suc_D2)
  from fn [OF Suc.prems(1) xu xv] have uv: "u = v" .
  have uR: "u \<in> R" by (rule closed [OF Suc.prems(1) xu])
  from vz uv have uz: "(u, z) \<in> S ^^ n" by simp
  show ?case by (rule Suc.hyps [OF uR uy uz])
qed

text \<open>\<^bold>\<open>What the region buys, stated the way a language argument wants
  it.\<close>  The lemma above compares runs of the \<^emph>\<open>same\<close> length, which no
  consumer ever has: one is given a path that halts and asked about another
  path that halts, and the two lengths are unrelated.  The bridge is that a
  halting configuration has no successor, so the shorter run cannot be a
  proper prefix of the longer one --- and by uniqueness it is a prefix or
  nothing.  So the two runs have the same length as well as the same end.

  So a branch-free region admits \<^emph>\<open>at most one\<close> halting configuration
  reachable from a given start, whatever the path and whatever its length.
  That is the form soundness uses: exhibit the run that halts, and every
  other halting run is that one.  The length half is what pins a phase of a
  simulation: two runs of a sub-relation that both end where it stops took
  the same number of steps.\<close>

lemma relpow_halted_le:
  assumes closed: "\<And>x y. x \<in> R \<Longrightarrow> (x, y) \<in> S \<Longrightarrow> y \<in> R"
      and fn: "\<And>x y z. x \<in> R \<Longrightarrow> (x, y) \<in> S \<Longrightarrow> (x, z) \<in> S
                       \<Longrightarrow> y = z"
      and stuck: "\<And>u v. u \<in> H \<Longrightarrow> (u, v) \<in> S \<Longrightarrow> False"
      and x: "x \<in> R"
      and r1: "(x, y) \<in> S ^^ m" and h1: "y \<in> H"
      and r2: "(x, z) \<in> S ^^ n"
      and mn: "m \<le> n"
  shows "m = n \<and> y = z"
proof -
  \<comment> \<open>the split is done to the \<^emph>\<open>exponent\<close> and then to the relation,
      never by a \<^theory_text>\<open>simp\<close> carrying \<open>n = m + (n - m)\<close>: that equation rewrites
      \<open>n\<close> into a term containing \<open>n\<close>\<close>
  have "S ^^ (m + (n - m)) = S ^^ m O S ^^ (n - m)" by (rule relpow_add)
  moreover from mn have "m + (n - m) = n" by simp
  ultimately have "S ^^ n = S ^^ m O S ^^ (n - m)" by simp
  with r2 have "(x, z) \<in> S ^^ m O S ^^ (n - m)" by simp
  then obtain u where xu: "(x, u) \<in> S ^^ m" and uz: "(u, z) \<in> S ^^ (n - m)"
    by auto
  from relpow_unique_on [OF closed fn x r1 xu] have "y = u" .
  with uz have yz: "(y, z) \<in> S ^^ (n - m)" by simp
  show ?thesis
  proof (cases "n - m")
    case 0
    with yz mn show ?thesis by simp
  next
    case (Suc k)
    from yz Suc have "(y, z) \<in> S ^^ Suc k" by simp
    then obtain v where "(y, v) \<in> S" by (blast dest: relpow_Suc_D2)
    from stuck [OF h1 this] show ?thesis ..
  qed
qed

lemma relpow_halted_same_run:
  assumes closed: "\<And>x y. x \<in> R \<Longrightarrow> (x, y) \<in> S \<Longrightarrow> y \<in> R"
      and fn: "\<And>x y z. x \<in> R \<Longrightarrow> (x, y) \<in> S \<Longrightarrow> (x, z) \<in> S
                       \<Longrightarrow> y = z"
      and stuck: "\<And>u v. u \<in> H \<Longrightarrow> (u, v) \<in> S \<Longrightarrow> False"
      and x: "x \<in> R"
      and r1: "(x, y) \<in> S ^^ m" and h1: "y \<in> H"
      and r2: "(x, z) \<in> S ^^ n" and h2: "z \<in> H"
  shows "m = n \<and> y = z"
  using nat_le_linear [of m n]
proof
  assume mn: "m \<le> n"
  from relpow_halted_le [OF closed fn stuck x r1 h1 r2 mn] show ?thesis .
next
  assume nm: "n \<le> m"
  from relpow_halted_le [OF closed fn stuck x r2 h2 r1 nm] show ?thesis by simp
qed

lemmas relpow_halted_unique_on = relpow_halted_same_run [THEN conjunct2]


subsection \<open>The conditions of validity, one at a time\<close>

text \<open>Convenience lemmas projecting the substrate's structural
  axioms out of @{const valid_ktm} at the functional layer.
  Each one is a one-shot \<open>by (cases M) auto\<close>: the case-decomposition
  rewrites @{term M} into \<open>KTM\<close>-form, exposes the @{thm[source] valid_ktm.simps}
  conjunction, and \<open>auto\<close> extracts the relevant conjunct.

  These replace what used to be locale-routed retrievals of the
  form \<open>multitape_tm.X[OF loc]\<close>.\<close>

lemma valid_ktm_finite_Q:
  assumes "valid_ktm M"
  shows "finite (Q_ktm M)"
  using assms by (cases M) auto

lemma valid_ktm_finite_Gamma:
  assumes "valid_ktm M"
  shows "finite (\<Gamma>_ktm M)"
  using assms by (cases M) auto

lemma valid_ktm_Sigma_sub_Gamma:
  assumes "valid_ktm M"
  shows "Sigma_ktm M \<subseteq> \<Gamma>_ktm M"
  using assms by (cases M) auto

lemma valid_ktm_s_in_Q:
  assumes "valid_ktm M"
  shows "s_ktm M \<in> Q_ktm M"
  using assms by (cases M) auto

lemma valid_ktm_t_in_Q:
  assumes "valid_ktm M"
  shows "t_ktm M \<in> Q_ktm M"
  using assms by (cases M) auto

lemma valid_ktm_r_in_Q:
  assumes "valid_ktm M"
  shows "r_ktm M \<in> Q_ktm M"
  using assms by (cases M) auto

lemma valid_ktm_blank_in_Gamma:
  assumes "valid_ktm M"
  shows "bl_ktm M \<in> \<Gamma>_ktm M"
  using assms by (cases M) auto

lemma valid_ktm_blank_not_Sigma:
  assumes "valid_ktm M"
  shows "bl_ktm M \<notin> Sigma_ktm M"
  using assms by (cases M) auto

lemma valid_ktm_LE_in_Gamma:
  assumes "valid_ktm M"
  shows "le_ktm M \<in> \<Gamma>_ktm M"
  using assms by (cases M) auto

lemma valid_ktm_LE_not_Sigma:
  assumes "valid_ktm M"
  shows "le_ktm M \<notin> Sigma_ktm M"
  using assms by (cases M) auto

lemma valid_ktm_t_neq_r:
  assumes "valid_ktm M"
  shows "t_ktm M \<noteq> r_ktm M"
  using assms by (cases M) auto

lemma valid_ktm_k_pos:
  assumes "valid_ktm M"
  shows "0 < k_ktm M"
  using assms by (cases M) auto

lemma valid_ktm_delta_set:
  assumes "valid_ktm M"
  shows "delta_ktm M \<subseteq>
           (Q_ktm M - {t_ktm M, r_ktm M})
             \<times> (UNIV \<rightarrow> \<Gamma>_ktm M)
             \<times> Q_ktm M
             \<times> (UNIV \<rightarrow> \<Gamma>_ktm M)
             \<times> (UNIV \<rightarrow> UNIV)"
  using assms by (cases M) auto

text \<open>Range typing for transition tuples: pulls the four
  per-component facts from a single transition membership.\<close>

lemma valid_ktm_delta:
  assumes vM: "valid_ktm M"
    and tr: "(q, a, q', b, d) \<in> delta_ktm M"
  shows "q \<in> Q_ktm M" "a k \<in> \<Gamma>_ktm M" "q' \<in> Q_ktm M" "b k \<in> \<Gamma>_ktm M"
  using valid_ktm_delta_set[OF vM] tr by auto

text \<open>Left-endmarker discipline: transitions reading \<open>le\<close> must
  rewrite \<open>le\<close> with itself and move only \<open>N\<close> or \<open>R\<close>.\<close>

lemma valid_ktm_deltaLE:
  assumes vM: "valid_ktm M"
    and tr: "(q, a, q', a', d) \<in> delta_ktm M"
    and LE: "a k = le_ktm M"
  shows "a' k = le_ktm M \<and> d k \<in> {MoveN, MoveR}"
  using vM tr LE by (cases M) auto

text \<open>Left-endmarker write discipline: a transition writes \<open>le\<close> on
  tape \<open>k\<close> only when it was reading \<open>le\<close> on the same tape.  This is
  exactly the content of @{const le_unique} specialised to one tape /
  transition; it is the sole place that fact is extracted.  Needed by
  \<open>ae_coupled_run_aux\<close> to preserve the "no LE in window" invariant
  across an M-step.  Takes @{const le_unique} (not @{const valid_ktm}):
  it is the property a machine may forgo, so consumers thread it
  explicitly rather than reading it off \<open>valid_ktm\<close>.\<close>

lemma valid_ktm_deltaLE_no_write:
  assumes lu: "le_unique M"
    and tr: "(q, a, q', a', d) \<in> delta_ktm M"
    and LE': "a' k = le_ktm M"
  shows "a k = le_ktm M"
  using lu[unfolded le_unique_def] tr LE' by blast

text \<open>Support invariant: every transition of a valid machine is
  blank on reads and writes, and stationary, at every tape index
  \<open>j \<ge> k_ktm M\<close>.  The value-level confinement of a \<open>k\<close>-tape machine's
  action to tapes \<open>0 \<dots> k - 1\<close>.\<close>

lemma valid_ktm_delta_support:
  assumes vM: "valid_ktm M"
    and tr: "(q, a, q', a', d) \<in> delta_ktm M"
    and j: "j \<ge> k_ktm M"
  shows "a j = bl_ktm M \<and> a' j = bl_ktm M \<and> d j = MoveN"
proof -
  obtain Q \<Sigma> \<Gamma> bl le \<delta> s t r K where M_eq:
      "M = KTM Q \<Sigma> \<Gamma> bl le \<delta> s t r K"
    by (cases M)
  have supp:
      "\<forall>q a q' a' d. (q, a, q', a', d) \<in> \<delta> \<longrightarrow>
                       (\<forall>j \<ge> K. a j = bl \<and> a' j = bl \<and> d j = MoveN)"
    using vM[unfolded M_eq valid_ktm.simps] by blast
  from tr M_eq have tr_delta: "(q, a, q', a', d) \<in> \<delta>" by simp
  from j M_eq have jK: "j \<ge> K" by simp
  have bleq: "bl_ktm M = bl" using M_eq by simp
  from supp tr_delta jK have "a j = bl \<and> a' j = bl \<and> d j = MoveN" by blast
  thus ?thesis using bleq by simp
qed

text \<open>Finiteness of \<open>\<delta>\<close> from bounded support: a valid machine's
  transition relation is finite.  The value-level replacement for
  the AFP source's function-space finiteness over a finite tape
  type.  Each transition's read / write tuples range in the finite
  @{term \<Gamma>} and are blank beyond \<open>k\<close>, each move tuple is \<open>N\<close>
  beyond \<open>k\<close>; by @{thm[source] finite_tail_const_funcs} there are
  finitely many of each, so \<open>\<delta>\<close> embeds in a finite product.\<close>

lemma valid_ktm_finite_delta:
  assumes vM: "valid_ktm M"
  shows "finite (delta_ktm M)"
proof -
  obtain Q \<Sigma> \<Gamma> bl le \<delta> s t r K where M_eq:
      "M = KTM Q \<Sigma> \<Gamma> bl le \<delta> s t r K"
    by (cases M)
  have finQ: "finite Q" using valid_ktm_finite_Q[OF vM] M_eq by simp
  have finG: "finite \<Gamma>" using valid_ktm_finite_Gamma[OF vM] M_eq by simp
  let ?A = "{a. (\<forall>j. a j \<in> \<Gamma>) \<and> (\<forall>j \<ge> K. a j = bl)}"
  let ?D = "{d. (\<forall>j. d j \<in> (UNIV :: move set)) \<and> (\<forall>j \<ge> K. d j = MoveN)}"
  have finA: "finite ?A" by (rule finite_tail_const_funcs[OF finG, of K bl])
  have finD: "finite ?D" by (rule finite_tail_const_funcs[OF finite_UNIV_move, of K MoveN])
  have finprod: "finite ((Q - {t, r}) \<times> ?A \<times> Q \<times> ?A \<times> ?D)"
    using finQ finA finD by (intro finite_cartesian_product) auto
  have sub: "delta_ktm M \<subseteq> (Q - {t, r}) \<times> ?A \<times> Q \<times> ?A \<times> ?D"
  proof
    fix x assume xd: "x \<in> delta_ktm M"
    obtain q a q' a' d where x: "x = (q, a, q', a', d)"
      by (cases x)
    from valid_ktm_delta_set[OF vM] xd x M_eq
    have q_mem: "q \<in> Q - {t, r}" and a_pi: "a \<in> UNIV \<rightarrow> \<Gamma>"
      and q'_mem: "q' \<in> Q" and a'_pi: "a' \<in> UNIV \<rightarrow> \<Gamma>"
      by auto
    from a_pi have aG: "\<forall>j. a j \<in> \<Gamma>" by (auto simp: Pi_iff)
    from a'_pi have a'G: "\<forall>j. a' j \<in> \<Gamma>" by (auto simp: Pi_iff)
    have trM: "(q, a, q', a', d) \<in> delta_ktm M" using xd x by simp
    have supp: "\<forall>j \<ge> K. a j = bl \<and> a' j = bl \<and> d j = MoveN"
    proof (intro allI impI)
      fix j assume "K \<le> j"
      hence "j \<ge> k_ktm M" using M_eq by simp
      thus "a j = bl \<and> a' j = bl \<and> d j = MoveN"
        using valid_ktm_delta_support[OF vM trM] M_eq by simp
    qed
    have "a \<in> ?A" using aG supp by auto
    moreover have "a' \<in> ?A" using a'G supp by auto
    moreover have "d \<in> ?D" using supp by auto
    ultimately show "x \<in> (Q - {t, r}) \<times> ?A \<times> Q \<times> ?A \<times> ?D"
      using x q_mem q'_mem by auto
  qed
  show ?thesis using sub finprod by (rule finite_subset)
qed

text \<open>State membership at the source of an \<open>ktm_step\<close>: the
  source state is in \<open>Q_ktm M\<close> and is neither the accept nor
  the reject state.  Direct consequence of the \<open>ktm_step\<close>
  introduction rule plus \<open>valid_ktm_delta_set\<close>'s range typing
  (which excludes halting states from the source projection of
  \<open>delta_ktm M\<close>).

  Used by the chunked-induction engine
  \<open>ae_simulation_phase_chunked\<close>: when the M-trace
  \<open>(cM, cM_final) \<in> ktm_step (delta_ktm M) ^^ (Suc n)\<close>
  is non-empty, the first step exists and forces \<open>cM\<close>'s state
  to be non-halt and in \<open>Q\<close>, which feeds
  \<open>ae_simulates_forward_stage_general\<close>'s \<open>qM_in_Q\<close> /
  \<open>q_neq_t\<close> / \<open>q_neq_r\<close> hypotheses.\<close>

lemma ktm_step_src:
  fixes M :: "('q, 'a) ktm"
  assumes vM:   "valid_ktm M"
    and step: "(c, c') \<in> ktm_step (delta_ktm M)"
  shows ktm_step_src_in_Q:    "ktc_state c \<in> Q_ktm M"
    and ktm_step_src_neq_t:   "ktc_state c \<noteq> t_ktm M"
    and ktm_step_src_neq_r:   "ktc_state c \<noteq> r_ktm M"
proof -
  from step obtain q ts n q' a move where
      c_eq: "c = KConfig q ts n"
    and tr: "(q, \<lambda>k. ts k (n k), q', a, move) \<in> delta_ktm M"
    by (auto elim: ktm_step.cases)
  have q_eq: "ktc_state c = q" using c_eq by simp
  have q_in_strict: "q \<in> Q_ktm M - {t_ktm M, r_ktm M}"
    using valid_ktm_delta_set[OF vM] tr by auto
  show "ktc_state c \<in> Q_ktm M"  using q_eq q_in_strict by simp
  show "ktc_state c \<noteq> t_ktm M" using q_eq q_in_strict by simp
  show "ktc_state c \<noteq> r_ktm M" using q_eq q_in_strict by simp
qed


subsection \<open>A step preserves valid configurations\<close>

text \<open>Per-step preservation of @{const valid_config_ktm}: a valid
  configuration steps only to valid configurations.  Re-derived
  directly from @{thm[source] valid_ktm_delta} (range typing),
  @{thm[source] valid_ktm_deltaLE} (left-endmarker discipline),
  and @{thm[source] valid_ktm_delta_support} (the new inactive-tape
  blank-tail case).\<close>

lemma valid_step_ktm:
  fixes M :: "('q, 'a) ktm"
  assumes vM:    "valid_ktm M"
    and step:    "(c, c') \<in> ktm_step (delta_ktm M)"
    and val_c:   "valid_config_ktm M c"
  shows "valid_config_ktm M c'"
proof -
  obtain Q \<Sigma> \<Gamma> bl le \<delta> s t r K where M_eq:
      "M = KTM Q \<Sigma> \<Gamma> bl le \<delta> s t r K"
    by (cases M)
  obtain q ts n where c_eq: "c = KConfig q ts n"
    by (cases c)
  from step M_eq c_eq have step_delta:
      "(KConfig q ts n, c') \<in> ktm_step \<delta>"
    by simp
  obtain q' a move where c'_eq:
      "c' = KConfig q' (\<lambda>k. (ts k)(n k := a k))
                       (\<lambda>k. go_move (move k) (n k))"
    and tr: "(q, (\<lambda>k. ts k (n k)), q', a, move) \<in> \<delta>"
    using step_delta by (auto elim: ktm_step.cases)
  from val_c c_eq M_eq have q_in: "q \<in> Q"
    and ts_Gamma: "\<And>k. range (ts k) \<subseteq> \<Gamma>"
    and ts_LE: "\<And>k. k < K \<Longrightarrow> ts k 0 = le"
    and ts_blank: "\<And>k p. k \<ge> K \<Longrightarrow> ts k p = bl"
    by auto
  from tr M_eq have tr_M: "(q, (\<lambda>k. ts k (n k)), q', a, move) \<in> delta_ktm M"
    by simp
  have q'_in: "q' \<in> Q_ktm M" and a_Gamma: "\<And>k. a k \<in> \<Gamma>_ktm M"
    using valid_ktm_delta[OF vM tr_M] by auto
  hence q'_in_Q: "q' \<in> Q" and a_Gamma_set: "\<And>k. a k \<in> \<Gamma>"
    using M_eq by auto
  have new_ts_Gamma: "\<And>k. range ((ts k)(n k := a k)) \<subseteq> \<Gamma>"
    using ts_Gamma a_Gamma_set by auto
  have new_LE: "\<And>k. k < K \<Longrightarrow> ((ts k)(n k := a k)) 0 = le"
  proof -
    fix k assume kK: "k < K"
    show "((ts k)(n k := a k)) 0 = le"
    proof (cases "n k = 0")
      case True
      have read_LE: "(\<lambda>j. ts j (n j)) k = le"
        using ts_LE[OF kK] True by simp
      have read_LE_le: "(\<lambda>j. ts j (n j)) k = le_ktm M"
        using read_LE M_eq by simp
      have "a k = le_ktm M"
        using valid_ktm_deltaLE[OF vM tr_M read_LE_le] by simp
      hence "a k = le" using M_eq by simp
      with True show ?thesis by simp
    next
      case False
      thus ?thesis using ts_LE[OF kK] by simp
    qed
  qed
  have new_blank: "\<And>k p. k \<ge> K \<Longrightarrow> ((ts k)(n k := a k)) p = bl"
  proof -
    fix k p assume kK: "k \<ge> K"
    have ak_bl: "a k = bl"
    proof -
      have "k \<ge> k_ktm M" using kK M_eq by simp
      hence "a k = bl_ktm M"
        using valid_ktm_delta_support[OF vM tr_M] by simp
      thus ?thesis using M_eq by simp
    qed
    show "((ts k)(n k := a k)) p = bl"
      using ts_blank[OF kK] ak_bl by (cases "p = n k") auto
  qed
  show ?thesis
    unfolding M_eq c'_eq valid_config_ktm.simps
  proof (intro conjI allI impI)
    show "q' \<in> Q" using q'_in_Q .
  next
    fix i
    show "range ((\<lambda>k. (ts k)(n k := a k)) i) \<subseteq> \<Gamma>"
      using new_ts_Gamma by simp
  next
    fix i assume "i < K"
    show "(\<lambda>k. (ts k)(n k := a k)) i 0 = le"
      using new_LE[OF \<open>i < K\<close>] by simp
  next
    fix i p assume "K \<le> i"
    show "(\<lambda>k. (ts k)(n k := a k)) i p = bl"
      using new_blank[OF \<open>K \<le> i\<close>] by simp
  qed
qed

text \<open>Initial-configuration accessors, in terms of the machine's
  structural projections.  \<^const>\<open>init_config_ktm\<close> is a \<^theory_text>\<open>fun\<close> over
  the \<open>KTM\<close> constructor, so without these a proof reads the start tape,
  state or heads only after an inline \<open>cases M\<close>.  The head positions are
  a \<^theory_text>\<open>simp\<close> rule, since every head starts at the origin.\<close>

lemma ktc_tape_init_config:
  "ktc_tape (init_config_ktm M w)
     = (\<lambda>k n. if k < k_ktm M
              then (if n = 0 then le_ktm M
                    else if k = 0 \<and> n \<le> length w then w ! (n - 1)
                    else bl_ktm M)
              else bl_ktm M)"
proof (cases M)
  case (KTM Q Sg Gm bl le dl s tt rr kk)
  then have lhs: "ktc_tape (init_config_ktm M w)
                    = (\<lambda>k n. if k < kk
                             then (if n = 0 then le
                                   else if k = 0 \<and> n \<le> length w then w ! (n - 1)
                                   else bl)
                             else bl)"
    and le': "le_ktm M = le" and bl': "bl_ktm M = bl" and kk': "k_ktm M = kk"
    by simp_all
  show ?thesis by (simp only: lhs le' bl' kk')
qed

lemma ktc_state_init_config [simp]:
  "ktc_state (init_config_ktm M w) = s_ktm M"
proof (cases M)
  case (KTM Q Sg Gm bl le dl s tt rr kk)
  then have lhs: "ktc_state (init_config_ktm M w) = s" and s': "s_ktm M = s"
    by simp_all
  show ?thesis by (simp only: lhs s')
qed

lemma ktc_pos_init_config [simp]:
  "ktc_pos (init_config_ktm M w) = (\<lambda>_. 0)"
  by (cases M) simp

text \<open>Initial-configuration validity: a valid \<open>M\<close>'s initial
  configuration on a valid input is itself valid.\<close>

lemma valid_init_config_ktm:
  fixes M :: "('q, 'a) ktm"
  assumes vM: "valid_ktm M"
    and w:    "set w \<subseteq> Sigma_ktm M"
  shows "valid_config_ktm M (init_config_ktm M w)"
proof -
  obtain Q \<Sigma> \<Gamma> bl le \<delta> s t r K where M_eq:
      "M = KTM Q \<Sigma> \<Gamma> bl le \<delta> s t r K"
    by (cases M)
  have w_Sigma: "set w \<subseteq> \<Sigma>"
    using w M_eq by simp
  have s_in: "s \<in> Q" using valid_ktm_s_in_Q[OF vM] M_eq by simp
  have Sigma_sub: "\<Sigma> \<subseteq> \<Gamma>" using valid_ktm_Sigma_sub_Gamma[OF vM] M_eq by simp
  have bl_in: "bl \<in> \<Gamma>" using valid_ktm_blank_in_Gamma[OF vM] M_eq by simp
  have le_in: "le \<in> \<Gamma>" using valid_ktm_LE_in_Gamma[OF vM] M_eq by simp
  show ?thesis
    unfolding M_eq init_config_ktm.simps valid_config_ktm.simps
  proof (intro conjI allI impI)
    show "s \<in> Q" using s_in .
  next
    fix i
    show "range (\<lambda>n. if i < K
                     then (if n = 0 then le
                           else if i = 0 \<and> n \<le> length w then w ! (n - 1)
                           else bl)
                     else bl) \<subseteq> \<Gamma>"
    proof (cases "i < K")
      case True
      show ?thesis
        using bl_in le_in Sigma_sub w_Sigma True
        by (force simp: set_conv_nth)
    next
      case False
      show ?thesis using bl_in False by simp
    qed
  next
    fix i assume "i < K"
    show "(if i < K
            then (if (0::nat) = 0 then le
                  else if i = 0 \<and> 0 \<le> length w then w ! (0 - 1)
                  else bl)
            else bl) = le"
      using \<open>i < K\<close> by simp
  next
    fix i p assume "K \<le> i"
    show "(if i < K
            then (if p = 0 then le
                  else if i = 0 \<and> p \<le> length w then w ! (p - 1)
                  else bl)
            else bl) = bl"
      using \<open>K \<le> i\<close> by simp
  qed
qed

text \<open>Reachability lift: every configuration reachable from a
  valid initial configuration is itself valid.\<close>

lemma valid_reach_ktm:
  fixes M :: "('q, 'a) ktm"
  assumes vM:    "valid_ktm M"
    and w:       "set w \<subseteq> Sigma_ktm M"
    and reach:   "(init_config_ktm M w, c) \<in> (ktm_step (delta_ktm M))\<^sup>*"
  shows "valid_config_ktm M c"
  using reach
proof induction
  case base
  show ?case using valid_init_config_ktm[OF vM w] .
next
  case (step y z)
  show ?case using valid_step_ktm[OF vM step.hyps(2) step.IH] .
qed

text \<open>Blank-tail accessor for a valid configuration: beyond the
  machine's tape count \<open>k_ktm M\<close> every cell holds the blank
  \<open>bl_ktm M\<close>.  Used on the reverse lift's padding tapes, where the
  per-tape window invariant is unavailable (it constrains the LE
  home cell, which is blank on padding) and the read-match must
  instead come from the substrate blank-tail.\<close>

lemma valid_config_ktm_blank_tail:
  assumes valc: "valid_config_ktm M c"
      and kge:  "i \<ge> k_ktm M"
  shows "ktc_tape c i p = bl_ktm M"
proof -
  obtain Q \<Sigma> \<Gamma> bl le \<delta> s t r K where
      M_eq: "M = KTM Q \<Sigma> \<Gamma> bl le \<delta> s t r K"
    by (cases M)
  obtain q ts n where c_eq: "c = KConfig q ts n" by (cases c)
  from valc kge show ?thesis
    unfolding M_eq c_eq by auto
qed

text \<open>Validity preservation along an \<open>n\<close>-step substrate trace
  from an arbitrary valid configuration (generic relpow closure of
  @{thm[source] valid_step_ktm}; @{thm[source] valid_reach_ktm}
  anchors only at \<open>init_config_ktm\<close>).  Threads the blank-tail
  validity of the reverse lift's intermediate configs \<open>cM_n'\<close>
  through the chain induction.\<close>

lemma valid_reach_relpow_ktm:
  assumes vM:    "valid_ktm M"
      and valc:  "valid_config_ktm M c"
      and reach: "(c, c') \<in> ktm_step (delta_ktm M) ^^ n"
  shows "valid_config_ktm M c'"
  using relpow_imp_rtrancl [OF reach]
  by (induction rule: rtrancl_induct) (auto intro: valc valid_step_ktm [OF vM])

text \<open>Per-tape LE-pinning corollary: along any reachable trace
  from a valid initial configuration, every \<^emph>\<open>active\<close> tape
  (index \<open>k < k_ktm M\<close>) carries \<open>le_ktm M\<close> at position 0.

  Note: \<open>valid_config_ktm\<close> only encodes the position-0 = LE
  constraint on active tapes, not the converse (positions \<open>p \<noteq> 0\<close>
  may legally hold LE in an arbitrary valid config).  The "LE only
  at position 0" property is reach-specific and proved separately
  in the companion lemma below.\<close>

lemma valid_reach_LE_pos0_ktm:
  fixes M :: "('q, 'a) ktm"
  assumes vM:  "valid_ktm M"
    and w:     "set w \<subseteq> Sigma_ktm M"
    and reach: "(init_config_ktm M w, KConfig q ts n)
                  \<in> (ktm_step (delta_ktm M))\<^sup>*"
    and kK:    "k < k_ktm M"
  shows "ts k 0 = le_ktm M"
proof -
  have val: "valid_config_ktm M (KConfig q ts n)"
    using valid_reach_ktm[OF vM w reach] .
  obtain Q \<Sigma> \<Gamma> bl le \<delta> sM t r K where M_eq:
      "M = KTM Q \<Sigma> \<Gamma> bl le \<delta> sM t r K"
    by (cases M)
  have "k < K" using kK M_eq by simp
  thus ?thesis using val M_eq by simp
qed

text \<open>Dual to @{thm[source] valid_reach_LE_pos0_ktm}: along any reachable
  trace from a valid initial configuration whose blank symbol differs
  from the left endmarker, every cell at a position \<open>p \<noteq> 0\<close> on any
  tape is not the left endmarker.  Proof: induction on the
  reachability relation.  Base: \<open>init_config_ktm\<close> places \<open>le\<close>
  only at position 0 of active tapes (input cells are in \<open>\<Sigma>\<close> hence
  \<open>\<noteq> le\<close>; other active cells and all inactive cells are \<open>bl\<close> which
  by hypothesis \<open>\<noteq> le\<close>).  Step: cells away from the head are
  preserved (substrate update is \<open>(ts k)(n k := a k)\<close>); at the head,
  the substrate's \<open>\<delta>LE\<close>-no-write rule says the write equals \<open>le\<close>
  only if the read did, which by IH is impossible since the read
  sits at the head position \<open>n k\<close> (and if \<open>n k = p \<noteq> 0\<close> the IH
  gives the read is not \<open>le\<close>; if \<open>n k = 0\<close> then \<open>p \<noteq> n k\<close> and the
  off-head case fires).\<close>

lemma valid_reach_LE_only_pos0_ktm:
  fixes M :: "('q, 'a) ktm"
    and c :: "('a, 'q) ktc_config"
    and k :: nat
    and p :: nat
  assumes vM:        "valid_ktm M"
    and lu:          "le_unique M"
    and w:           "set w \<subseteq> Sigma_ktm M"
    and reach:       "(init_config_ktm M w, c) \<in> (ktm_step (delta_ktm M))\<^sup>*"
    and p_ne_0:      "p \<noteq> 0"
    and bl_neq_le:   "bl_ktm M \<noteq> le_ktm M"
  shows "ktc_tape c k p \<noteq> le_ktm M"
proof -
  obtain Q \<Sigma> \<Gamma> bl le \<delta> sM tt rr K where M_eq:
      "M = KTM Q \<Sigma> \<Gamma> bl le \<delta> sM tt rr K"
    by (cases M)
  have le_eq:  "le_ktm M = le"  using M_eq by simp
  have bl_eq:  "bl_ktm M = bl"  using M_eq by simp
  have bl_ne_le: "bl \<noteq> le" using bl_neq_le le_eq bl_eq by simp
  have le_not_Sigma: "le \<notin> \<Sigma>"
    using valid_ktm_LE_not_Sigma[OF vM] M_eq by simp
  have w_Sigma: "set w \<subseteq> \<Sigma>" using w M_eq by simp
  have main:
    "\<forall>c'. (init_config_ktm M w, c') \<in> (ktm_step (delta_ktm M))\<^sup>*
            \<longrightarrow> ktc_tape c' k p \<noteq> le_ktm M"
  proof (intro allI impI)
    fix c'
    assume r: "(init_config_ktm M w, c') \<in> (ktm_step (delta_ktm M))\<^sup>*"
    show "ktc_tape c' k p \<noteq> le_ktm M"
      using r
    proof induction
      case base
      have tape_p_init:
          "ktc_tape (init_config_ktm M w) k p
             = (if k < K
                then (if p = 0 then le
                      else if k = 0 \<and> p \<le> length w then w ! (p - 1)
                      else bl)
                else bl)"
        unfolding M_eq init_config_ktm.simps by simp
      show ?case
      proof (cases "k = 0 \<and> p \<le> length w")
        case True
        have K_pos: "0 < K" using valid_ktm_k_pos[OF vM] M_eq by simp
        have kK: "k < K" using True K_pos by simp
        have p_ge_1: "p \<ge> 1" using p_ne_0 by simp
        have idx_lt: "p - 1 < length w" using True p_ge_1 by linarith
        have in_w: "w ! (p - 1) \<in> set w"
          using idx_lt by (auto simp: set_conv_nth)
        with w_Sigma have "w ! (p - 1) \<in> \<Sigma>" by blast
        with le_not_Sigma have "w ! (p - 1) \<noteq> le" by blast
        thus ?thesis using tape_p_init True kK p_ne_0 le_eq by simp
      next
        case False
        have "ktc_tape (init_config_ktm M w) k p = bl"
          using tape_p_init False p_ne_0 by (cases "k < K") auto
        thus ?thesis using bl_ne_le le_eq by simp
      qed
    next
      case (step y z)
      have ne_y: "ktc_tape y k p \<noteq> le_ktm M" using step.IH .
      obtain qy ts n where y_eq: "y = KConfig qy ts n"
        by (cases y)
      from step.hyps(2) y_eq obtain q' a dr where
          z_eq: "z = KConfig q'
                       (\<lambda>kk. (ts kk)(n kk := a kk))
                       (\<lambda>kk. go_move (dr kk) (n kk))"
          and tr: "(qy, (\<lambda>kk. ts kk (n kk)), q', a, dr) \<in> delta_ktm M"
        by (auto elim: ktm_step.cases)
      show ?case
      proof (cases "n k = p")
        case False
        have "ktc_tape z k p = ((ts k)(n k := a k)) p" using z_eq by simp
        also have "\<dots> = ts k p" using False by simp
        also have "\<dots> = ktc_tape y k p" using y_eq by simp
        finally have "ktc_tape z k p = ktc_tape y k p" .
        thus ?thesis using ne_y by simp
      next
        case True
        have read_at_p: "ts k (n k) = ktc_tape y k p"
          using y_eq True by simp
        have read_ne: "ts k (n k) \<noteq> le_ktm M"
          using ne_y read_at_p by simp
        have a_ne: "a k \<noteq> le_ktm M"
        proof
          assume a_le: "a k = le_ktm M"
          have "(\<lambda>kk. ts kk (n kk)) k = le_ktm M"
            using valid_ktm_deltaLE_no_write[OF lu tr a_le] by simp
          hence "ts k (n k) = le_ktm M" by simp
          thus False using read_ne by simp
        qed
        have "ktc_tape z k p = ((ts k)(n k := a k)) p" using z_eq by simp
        also have "\<dots> = a k" using True by simp
        finally have "ktc_tape z k p = a k" .
        thus ?thesis using a_ne by simp
      qed
    qed
  qed
  show ?thesis using main reach by blast
qed


subsection \<open>Step locality: non-head cells preserved, head moves by \<open>\<le>\<close> 1\<close>

text \<open>Two structural facts about \<open>ktm_step\<close> that fall directly out
  of the single rule's body \<open>(ts k)(n k := a k)\<close> and
  \<open>go_move (move k) (n k)\<close>: a single step modifies only the head
  cell on each tape, and the head displaces by at most one position
  per tape per step.  These are generic over \<open>\<delta>\<close> and used by
  alphabet-enlargement / -reduction to argue that cells outside a
  bounded window are unchanged after \<open>n\<close> steps.\<close>

lemma ktm_step_tape_off_head:
  assumes step: "(c, c') \<in> ktm_step \<delta>"
    and ne:     "p \<noteq> ktc_pos c k"
  shows "ktc_tape c' k p = ktc_tape c k p"
proof -
  from step obtain q ts n q' a dr where
      c_eq:  "c = KConfig q ts n"
    and c'_eq: "c' = KConfig q'
                       (\<lambda>k. (ts k)(n k := a k))
                       (\<lambda>k. go_move (dr k) (n k))"
    by (auto elim: ktm_step.cases)
  from ne c_eq have "p \<noteq> n k" by simp
  thus ?thesis by (simp add: c_eq c'_eq)
qed

lemma ktm_step_pos_displacement:
  assumes step: "(c, c') \<in> ktm_step \<delta>"
  shows "ktc_pos c' k \<le> ktc_pos c k + 1
         \<and> ktc_pos c k \<le> ktc_pos c' k + 1"
proof -
  from step obtain q ts n q' a dr where
      c_eq:  "c = KConfig q ts n"
    and c'_eq: "c' = KConfig q'
                       (\<lambda>k. (ts k)(n k := a k))
                       (\<lambda>k. go_move (dr k) (n k))"
    by (auto elim: ktm_step.cases)
  have pos: "ktc_pos c k = n k" by (simp add: c_eq)
  have pos': "ktc_pos c' k = go_move (dr k) (n k)" by (simp add: c'_eq)
  show ?thesis
    unfolding pos pos' by (cases "dr k") auto
qed

text \<open>\<open>n\<close>-step lift: after \<open>n\<close> steps, head displacement on each
  tape is at most \<open>n\<close>.\<close>

lemma ktm_relpow_pos_displacement:
  assumes "(c, c') \<in> ktm_step \<delta> ^^ n"
  shows "ktc_pos c' k \<le> ktc_pos c k + n
         \<and> ktc_pos c k \<le> ktc_pos c' k + n"
  using assms
proof (induction n arbitrary: c')
  case 0
  thus ?case by simp
next
  case (Suc n)
  from Suc.prems obtain c'' where
      ih: "(c, c'') \<in> ktm_step \<delta> ^^ n"
    and step: "(c'', c') \<in> ktm_step \<delta>"
    by (auto elim: relpow_Suc_E)
  have h1: "ktc_pos c'' k \<le> ktc_pos c k + n
            \<and> ktc_pos c k \<le> ktc_pos c'' k + n"
    using Suc.IH[OF ih] .
  have h2: "ktc_pos c' k \<le> ktc_pos c'' k + 1
            \<and> ktc_pos c'' k \<le> ktc_pos c' k + 1"
    using ktm_step_pos_displacement[OF step] .
  from h1 h2 show ?case by linarith
qed

text \<open>\<open>n\<close>-step lift: cells more than \<open>n\<close> away from the start head
  position are unchanged after \<open>n\<close> steps.\<close>

lemma ktm_relpow_tape_off_window:
  assumes "(c, c') \<in> ktm_step \<delta> ^^ n"
    and "p > ktc_pos c k + n \<or> p + n < ktc_pos c k"
  shows "ktc_tape c' k p = ktc_tape c k p"
  using assms
proof (induction n arbitrary: c')
  case 0
  thus ?case by simp
next
  case (Suc n)
  from Suc.prems(1) obtain c'' where
      ih: "(c, c'') \<in> ktm_step \<delta> ^^ n"
    and step: "(c'', c') \<in> ktm_step \<delta>"
    by (auto elim: relpow_Suc_E)
  have far: "p > ktc_pos c k + n \<or> p + n < ktc_pos c k"
    using Suc.prems(2) by linarith
  have eq_ih: "ktc_tape c'' k p = ktc_tape c k p"
    using Suc.IH[OF ih far] .
  have disp: "ktc_pos c'' k \<le> ktc_pos c k + n
              \<and> ktc_pos c k \<le> ktc_pos c'' k + n"
    using ktm_relpow_pos_displacement[OF ih] .
  have ne: "p \<noteq> ktc_pos c'' k"
    using Suc.prems(2) disp by linarith
  have eq_step: "ktc_tape c' k p = ktc_tape c'' k p"
    using ktm_step_tape_off_head[OF step ne] .
  show ?case using eq_step eq_ih by simp
qed


subsection \<open>The left endmarker stays at cell 0\<close>

text \<open>Local LE-pinning: any step of a valid M from a config whose
  tape \<open>k\<close> already has \<open>le_ktm M\<close> at position 0 ends with a config
  whose tape \<open>k\<close> still has \<open>le_ktm M\<close> at position 0.  Standalone
  variant of \<open>valid_step_ktm\<close>'s position-0-= LE conjunct,
  stripped of the \<open>valid_config_ktm\<close> precondition: only the
  per-tape LE-at-0 fact is needed (not Q-membership or \<open>\<Gamma>\<close>-typing).
  Case-split on whether the head is at position 0: at-head fires
  \<open>\<delta>LE\<close> (read LE forces write LE); off-head uses
  \<open>ktm_step_tape_off_head\<close> directly.\<close>

lemma ktm_step_LE_pos0_preserve:
  fixes M :: "('q, 'a) ktm"
  assumes vM:    "valid_ktm M"
    and step:    "(c, c') \<in> ktm_step (delta_ktm M)"
    and LE_at0:  "ktc_tape c k 0 = le_ktm M"
  shows "ktc_tape c' k 0 = le_ktm M"
proof (cases "ktc_pos c k = 0")
  case True
  from step obtain q ts n q' a dr where
      c_eq:  "c = KConfig q ts n"
    and c'_eq: "c' = KConfig q'
                       (\<lambda>kk. (ts kk)(n kk := a kk))
                       (\<lambda>kk. go_move (dr kk) (n kk))"
    and tr:    "(q, \<lambda>kk. ts kk (n kk), q', a, dr) \<in> delta_ktm M"
    by (auto elim: ktm_step.cases)
  have nk_0: "n k = 0" using True c_eq by simp
  have ts_k_0_le: "ts k 0 = le_ktm M" using LE_at0 c_eq by simp
  have read_LE: "(\<lambda>kk. ts kk (n kk)) k = le_ktm M"
    using ts_k_0_le nk_0 by simp
  have write_LE: "a k = le_ktm M"
    using valid_ktm_deltaLE[OF vM tr read_LE] by simp
  have "ktc_tape c' k 0 = ((ts k)(n k := a k)) 0"
    using c'_eq by simp
  also have "\<dots> = a k" using nk_0 by simp
  also have "\<dots> = le_ktm M" using write_LE .
  finally show ?thesis .
next
  case False
  have ne_0: "(0 :: nat) \<noteq> ktc_pos c k" using False by simp
  have unchanged: "ktc_tape c' k 0 = ktc_tape c k 0"
    using ktm_step_tape_off_head[OF step ne_0] .
  show ?thesis using unchanged LE_at0 by simp
qed

text \<open>\<open>n\<close>-step lift of @{thm[source] ktm_step_LE_pos0_preserve}: along
  any chain of M-steps, \<open>le_ktm M\<close> at position 0 is preserved
  on every tape.  Used in AE's LE-edge forward stage to derive
  \<open>cM_k\<close>'s position-0 = LE without recourse to reachability
  from init.\<close>

lemma ktm_relpow_LE_pos0_preserve:
  fixes M :: "('q, 'a) ktm"
  assumes vM:    "valid_ktm M"
    and chain:   "(c, c') \<in> ktm_step (delta_ktm M) ^^ n"
    and LE_at0:  "ktc_tape c k 0 = le_ktm M"
  shows "ktc_tape c' k 0 = le_ktm M"
  using relpow_imp_rtrancl [OF chain]
  by (induction rule: rtrancl_induct)
     (auto intro: LE_at0 ktm_step_LE_pos0_preserve [OF vM])


subsection \<open>Decomposing a step\<close>

text \<open>Packages \<open>ktm_step.cases\<close> with the post-state position +
  tape equations on each tape: a single \<open>obtains\<close> rule that
  yields all four useful facts (pre-state's state, post-state's
  state, the per-tape position equation \<open>go_move (dr k) (n k)\<close>,
  and the per-tape head-cell update).  Chain proofs in
  AE / AR / TR avoid re-doing the case-analysis at every
  per-substep position-trajectory step.\<close>

lemma ktm_step_obtain_action:
  assumes step: "(c, c') \<in> ktm_step \<delta>"
  obtains q q' a dr where
      "ktc_state c = q"
    and "ktc_state c' = q'"
    and "(q, \<lambda>k. ktc_tape c k (ktc_pos c k), q', a, dr) \<in> \<delta>"
    and "\<And>kk. ktc_pos c' kk = go_move (dr kk) (ktc_pos c kk)"
    and "\<And>kk p. p \<noteq> ktc_pos c kk
                  \<Longrightarrow> ktc_tape c' kk p = ktc_tape c kk p"
    and "\<And>kk. ktc_tape c' kk (ktc_pos c kk) = a kk"
proof -
  from step obtain q ts n q' a dr where
      c_eq:  "c = KConfig q ts n"
    and c'_eq: "c' = KConfig q'
                       (\<lambda>k. (ts k)(n k := a k))
                       (\<lambda>k. go_move (dr k) (n k))"
    and tr: "(q, \<lambda>k. ts k (n k), q', a, dr) \<in> \<delta>"
    by (auto elim: ktm_step.cases)
  have st_c: "ktc_state c = q" using c_eq by simp
  have st_c': "ktc_state c' = q'" using c'_eq by simp
  have pos_c: "\<And>kk. ktc_pos c kk = n kk" using c_eq by simp
  have pos_c': "\<And>kk. ktc_pos c' kk = go_move (dr kk) (n kk)"
    using c'_eq by simp
  have tape_c: "\<And>kk. ktc_tape c kk = ts kk" using c_eq by simp
  have tape_c': "\<And>kk. ktc_tape c' kk = (ts kk)(n kk := a kk)"
    using c'_eq by simp
  have tr': "(q, \<lambda>k. ktc_tape c k (ktc_pos c k), q', a, dr) \<in> \<delta>"
    using tr c_eq by simp
  show thesis
  proof (rule that[OF st_c st_c' tr'])
    fix kk show "ktc_pos c' kk = go_move (dr kk) (ktc_pos c kk)"
      using pos_c' pos_c by simp
  next
    fix kk p assume "p \<noteq> ktc_pos c kk"
    thus "ktc_tape c' kk p = ktc_tape c kk p"
      using tape_c' tape_c pos_c by simp
  next
    fix kk show "ktc_tape c' kk (ktc_pos c kk) = a kk"
      using tape_c' pos_c by simp
  qed
qed


subsection \<open>Transitions that write nothing\<close>

text \<open>For a transition relation in which every tuple's
  read-component equals its write-component, a single step
  preserves the entire tape function (the substrate update
  \<open>f(x := f x)\<close> is the identity).  Used by the alphabet-
  enlargement chain proof for the read-only buffer-loading
  substeps SS1\<open>\<rightarrow>\<close>SS2, SS2\<open>\<rightarrow>\<close>SS3, SS3\<open>\<rightarrow>\<close>SS4, SS4\<open>\<rightarrow>\<close>SS5.\<close>

lemma ktm_step_no_write_tape:
  assumes step: "(c, c') \<in> ktm_step \<delta>"
    and no_write: "\<And>q a q' a' d. (q, a, q', a', d) \<in> \<delta> \<Longrightarrow> a' = a"
  shows "ktc_tape c' = ktc_tape c"
proof -
  from step obtain q ts n q' a dr where
      c_eq:  "c = KConfig q ts n"
    and c'_eq: "c' = KConfig q'
                       (\<lambda>k. (ts k)(n k := a k))
                       (\<lambda>k. go_move (dr k) (n k))"
    and tr: "(q, \<lambda>k. ts k (n k), q', a, dr) \<in> \<delta>"
    by (auto elim: ktm_step.cases)
  from no_write[OF tr] have "a = (\<lambda>k. ts k (n k))" by simp
  hence "(\<lambda>k. (ts k)(n k := a k)) = ts" by auto
  thus ?thesis by (simp add: c_eq c'_eq)
qed


subsection \<open>Read-only steps and head walks\<close>

text \<open>The introduction direction of the same fact.  A tuple that writes back
  what it read leaves the tape function as it was, so its step is determined by
  the state change and the moves alone.  Repeated in one state with one move
  vector, it is a \<^emph>\<open>walk\<close>: the commonest subroutine of a multi-pass machine,
  which returns a head to its origin, skips a field, or seeks a marker.\<close>

lemma ktm_step_read_only:
  assumes "(q, \<lambda>i. ts i (pos i), q', \<lambda>i. ts i (pos i), mv) \<in> \<delta>"
  shows "(KConfig q ts pos, KConfig q' ts (\<lambda>i. go_move (mv i) (pos i)))
           \<in> ktm_step \<delta>"
proof -
  have "(KConfig q ts pos,
         KConfig q' (\<lambda>i. (ts i)(pos i := ts i (pos i)))
                    (\<lambda>i. go_move (mv i) (pos i))) \<in> ktm_step \<delta>"
    by (rule ktm_step.step) (rule assms)
  then show ?thesis by simp
qed

text \<open>The walk in its general form: the head positions after \<open>m\<close> steps are
  \<open>pos m\<close>, and every head moves by \<open>mv\<close> at every step.  Several heads may
  move at once, in different directions.\<close>

lemma ktm_read_only_run:
  assumes tr: "\<And>m. m < n \<Longrightarrow>
                 (q, \<lambda>i. ts i (pos m i), q, \<lambda>i. ts i (pos m i), mv) \<in> \<delta>"
      and mv: "\<And>m. m < n \<Longrightarrow> pos (Suc m) = (\<lambda>i. go_move (mv i) (pos m i))"
  shows "(KConfig q ts (pos 0), KConfig q ts (pos n)) \<in> ktm_step \<delta> ^^ n"
  using tr mv
proof (induction n)
  case 0
  show ?case by simp
next
  case (Suc n)
  have run: "(KConfig q ts (pos 0), KConfig q ts (pos n)) \<in> ktm_step \<delta> ^^ n"
    by (rule Suc.IH) (simp_all add: Suc.prems)
  have "(KConfig q ts (pos n), KConfig q ts (\<lambda>i. go_move (mv i) (pos n i)))
          \<in> ktm_step \<delta>"
    by (rule ktm_step_read_only) (simp add: Suc.prems)
  then have "(KConfig q ts (pos n), KConfig q ts (pos (Suc n))) \<in> ktm_step \<delta>"
    by (simp add: Suc.prems)
  with run show ?case by (rule relpow_Suc_I)
qed

text \<open>The usual case moves one head.\<close>

definition move_one :: "nat \<Rightarrow> move \<Rightarrow> (nat \<Rightarrow> move)" where
  "move_one tp d = (\<lambda>j. if j = tp then d else MoveN)"

lemma move_one_same [simp]: "move_one tp d tp = d"
  by (simp add: move_one_def)

lemma move_one_other [simp]: "j \<noteq> tp \<Longrightarrow> move_one tp d j = MoveN"
  by (simp add: move_one_def)

text \<open>Two heads moving, possibly in different directions.  The first tape
  wins where the two coincide.\<close>

definition move_pair :: "nat \<Rightarrow> move \<Rightarrow> nat \<Rightarrow> move \<Rightarrow> (nat \<Rightarrow> move)" where
  "move_pair tp1 d1 tp2 d2 =
     (\<lambda>j. if j = tp1 then d1 else if j = tp2 then d2 else MoveN)"

lemma move_pair_fst [simp]: "move_pair tp1 d1 tp2 d2 tp1 = d1"
  by (simp add: move_pair_def)

lemma move_pair_snd [simp]:
  "tp2 \<noteq> tp1 \<Longrightarrow> move_pair tp1 d1 tp2 d2 tp2 = d2"
  by (simp add: move_pair_def)

lemma move_pair_other [simp]:
  "j \<noteq> tp1 \<Longrightarrow> j \<noteq> tp2 \<Longrightarrow> move_pair tp1 d1 tp2 d2 j = MoveN"
  by (simp add: move_pair_def)

text \<open>On machines over \<^typ>\<open>nat\<close> symbols with blank \<open>0\<close>, the read vector of
  a one-tape arc: tape \<open>0\<close> reads \<open>x\<close>, and every other index reads the blank.\<close>

definition one_tape_read :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "one_tape_read x = (\<lambda>j. if j = 0 then x else 0)"

lemma one_tape_read_inj: "one_tape_read x = one_tape_read y \<Longrightarrow> x = y"
  by (drule fun_cong [of _ _ 0]) (simp add: one_tape_read_def)

text \<open>A one-head walk, leftwards from cell \<open>P + n\<close> to cell \<open>P\<close> and rightwards
  from \<open>P\<close> to \<open>P + n\<close>.  The hypothesis names each cell the head reads, so a
  caller states it as a property of a stretch of tape (``every cell here holds
  an input symbol'').  A walk that stops on a cell it recognises adds one exit
  step, \<open>ktm_step_read_only\<close> again but into another state.\<close>

lemma ktm_walk_left:
  assumes tr: "\<And>m. P < m \<Longrightarrow> m \<le> P + n \<Longrightarrow>
                 (q, \<lambda>i. ts i ((pos(tp := m)) i), q, \<lambda>i. ts i ((pos(tp := m)) i),
                  move_one tp MoveL) \<in> \<delta>"
  shows "(KConfig q ts (pos(tp := P + n)), KConfig q ts (pos(tp := P)))
           \<in> ktm_step \<delta> ^^ n"
proof -
  have "(KConfig q ts (pos(tp := P + n - 0)), KConfig q ts (pos(tp := P + n - n)))
          \<in> ktm_step \<delta> ^^ n"
  proof (rule ktm_read_only_run [where pos = "\<lambda>m. pos(tp := P + n - m)"
                                  and mv = "move_one tp MoveL"])
    fix m assume "m < n"
    then show "(q, \<lambda>i. ts i ((pos(tp := P + n - m)) i), q,
                \<lambda>i. ts i ((pos(tp := P + n - m)) i), move_one tp MoveL) \<in> \<delta>"
      using tr [of "P + n - m"] by simp
  next
    fix m assume "m < n"
    then show "pos(tp := P + n - Suc m)
                 = (\<lambda>i. go_move (move_one tp MoveL i) ((pos(tp := P + n - m)) i))"
      by (simp add: fun_eq_iff move_one_def)
  qed
  then show ?thesis by simp
qed

lemma ktm_walk_right:
  assumes tr: "\<And>m. P \<le> m \<Longrightarrow> m < P + n \<Longrightarrow>
                 (q, \<lambda>i. ts i ((pos(tp := m)) i), q, \<lambda>i. ts i ((pos(tp := m)) i),
                  move_one tp MoveR) \<in> \<delta>"
  shows "(KConfig q ts (pos(tp := P)), KConfig q ts (pos(tp := P + n)))
           \<in> ktm_step \<delta> ^^ n"
proof -
  have "(KConfig q ts (pos(tp := P + 0)), KConfig q ts (pos(tp := P + n)))
          \<in> ktm_step \<delta> ^^ n"
  proof (rule ktm_read_only_run [where pos = "\<lambda>m. pos(tp := P + m)"
                                  and mv = "move_one tp MoveR"])
    fix m assume "m < n"
    then show "(q, \<lambda>i. ts i ((pos(tp := P + m)) i), q,
                \<lambda>i. ts i ((pos(tp := P + m)) i), move_one tp MoveR) \<in> \<delta>"
      using tr [of "P + m"] by simp
  next
    fix m assume "m < n"
    then show "pos(tp := P + Suc m)
                 = (\<lambda>i. go_move (move_one tp MoveR i) ((pos(tp := P + m)) i))"
      by (simp add: fun_eq_iff move_one_def)
  qed
  then show ?thesis by simp
qed


subsection \<open>What a composite needs from the step relation\<close>

text \<open>Facts about \<^const>\<open>ktm_step\<close> that belong to the substrate rather
  than to any construction.

  \<^bold>\<open>The union laws are what make a turn-taking composite cheap.\<close>
  \<^const>\<open>ktm_step\<close> is defined by a single introduction rule whose only premise
  is that one tuple lies in \<open>\<delta>\<close>, and nothing in the rule quantifies over \<open>\<delta>\<close>
  --- so the step relation of a union is the union of the step relations, on
  the nose.  A composite whose transition relation is a union of arms therefore
  splits a step into "which arm took it" by rewriting, and each arm can then be
  analysed on its own.  There is no corresponding law for a \<^emph>\<open>lockstep\<close>
  product, whose transition relation is a join of the two factors' sets rather
  than a union; that asymmetry, not the running time, is why a clocked
  composite takes turns.

  \<open>ktm_step_state_rel\<close> is the state-side counterpart of the tape-side
  \<open>ktm_step_frozen_tape\<close> (\<open>Multitape_Run_Facts\<close>), and is much the weaker statement of the two:
  the state is carried through a step untouched, so any relation holding
  between the two ends of every tuple holds across the step.  It is general in
  \<open>R\<close> because the composite needs two instances of it --- one frozen component
  (the factor that is not moving keeps its state) and one that changes (the
  turn flips).  The tape lemma cannot be stated this way, because there the
  tuple's read component has to be matched against what is actually under the
  head.\<close>

lemma ktm_step_mono:
  assumes "\<delta>\<^sub>1 \<subseteq> \<delta>\<^sub>2"
  shows "ktm_step \<delta>\<^sub>1 \<subseteq> ktm_step \<delta>\<^sub>2"
  using assms by (auto elim!: ktm_step.cases intro: ktm_step.step)

lemma ktm_step_Un:
  "ktm_step (\<delta>\<^sub>1 \<union> \<delta>\<^sub>2) = ktm_step \<delta>\<^sub>1 \<union> ktm_step \<delta>\<^sub>2"
  by (auto elim!: ktm_step.cases intro: ktm_step.step)

lemma ktm_step_UN:
  "ktm_step (\<Union>i\<in>I. \<delta> i) = (\<Union>i\<in>I. ktm_step (\<delta> i))"
  by (auto elim!: ktm_step.cases intro: ktm_step.step)

text \<open>\<open>ktm_step_mono\<close> needs only the tuples the step can use, and those
  are the ones out of the configuration's state.  So a step of a union whose
  source state is known lies in the part of the union that state can fire:
  the routing fact for the tuples, \<open>sub\<close>, lifts to the step relation
  without the client taking the step apart.

  \<^bold>\<open>Apply it by \<^theory_text>\<open>rule\<close>, not \<^theory_text>\<open>OF\<close>.\<close>  Given the routing fact
  by \<^theory_text>\<open>OF\<close>, \<open>P q\<close> is matched against a condition on a \<^emph>\<open>schematic\<close>
  source state, which is not a pattern, and \<^theory_text>\<open>OF\<close> reports multiple
  unifiers.  Closing \<open>sub\<close> by \<^theory_text>\<open>erule\<close> with the routing fact binds that
  state to \<open>q\<close> first, after which \<open>P\<close> is fixed by pattern unification and
  the state hypothesis closes the last goal.\<close>

lemma ktm_step_restrict_src:
  assumes step: "(C, C') \<in> ktm_step \<delta>"
      and sub: "\<And>q a q' a' d. (q, a, q', a', d) \<in> \<delta> \<Longrightarrow> P q
                  \<Longrightarrow> (q, a, q', a', d) \<in> \<delta>'"
      and src: "P (ktc_state C)"
  shows "(C, C') \<in> ktm_step \<delta>'"
proof -
  from step obtain q ts n q' a d where
      C: "C = KConfig q ts n"
    and C': "C' = KConfig q' (\<lambda>k. (ts k)(n k := a k)) (\<lambda>k. go_move (d k) (n k))"
    and t: "(q, \<lambda>k. ts k (n k), q', a, d) \<in> \<delta>"
    by (auto elim: ktm_step.cases)
  from src C have "P q" by simp
  with t have "(q, \<lambda>k. ts k (n k), q', a, d) \<in> \<delta>'" by (rule sub)
  then show ?thesis
    unfolding C C' by (rule ktm_step.step [where ts = ts and n = n])
qed

text \<open>The run-level form of \<open>ktm_step_mono\<close>: a run of
  one arm of a composite is a run of the composite.\<close>

lemma ktm_run_mono:
  assumes sub: "\<delta>\<^sub>1 \<subseteq> \<delta>\<^sub>2"
      and run: "(c, c') \<in> (ktm_step \<delta>\<^sub>1) ^^ n"
  shows "(c, c') \<in> (ktm_step \<delta>\<^sub>2) ^^ n"
  using relpow_subset_mono [OF ktm_step_mono [OF sub]] run ..

text \<open>Both ends of a step as one tuple, and nothing else.  \<open>ktm_step.cases\<close>
  exposes the whole anatomy --- tape frame, read, write, directions --- and a
  \<^emph>\<open>routing\<close> argument wants none of it: which part of a union a step came from
  is settled by the source state alone.  This is the projection that says so.

  \<^bold>\<open>The read component stays existential.\<close>  It is determined ---
  it is \<^term>\<open>\<lambda>k. ktc_tape C k (ktc_pos C k)\<close> --- but naming it would put the
  tape frame back into every consumer, which is the thing being avoided.  A
  consumer that needs the read still has \<open>ktm_step.cases\<close>.\<close>

lemma ktm_step_states:
  assumes step: "(C, C') \<in> ktm_step \<delta>"
  obtains a a' d where "(ktc_state C, a, ktc_state C', a', d) \<in> \<delta>"
proof -
  from step obtain q ts n q' a dr where
      c_eq:  "C = KConfig q ts n"
    and c'_eq: "C' = KConfig q'
                       (\<lambda>k. (ts k)(n k := a k))
                       (\<lambda>k. go_move (dr k) (n k))"
    and tr: "(q, \<lambda>k. ts k (n k), q', a, dr) \<in> \<delta>"
    by (auto elim: ktm_step.cases)
  have "(ktc_state C, \<lambda>k. ts k (n k), ktc_state C', a, dr) \<in> \<delta>"
    using tr by (simp add: c_eq c'_eq)
  then show thesis by (rule that)
qed

lemma ktm_step_state_rel:
  assumes step: "(c, c') \<in> ktm_step \<delta>"
    and rel: "\<forall>q a q' a' d. (q, a, q', a', d) \<in> \<delta> \<longrightarrow> R q q'"
  shows "R (ktc_state c) (ktc_state c')"
proof -
  from step obtain a a' d where "(ktc_state c, a, ktc_state c', a', d) \<in> \<delta>"
    by (rule ktm_step_states)
  with rel show ?thesis by blast
qed

text \<open>\<^bold>\<open>The halting states are dead ends, so a configuration that can still
  move is not in one.\<close>  \<^const>\<open>valid_ktm\<close> restricts \<open>\<delta>\<close>'s source component to
  \<^term>\<open>Q_ktm M - {t_ktm M, r_ktm M}\<close>, which is usually read as a well-formedness
  condition and is also a \<^emph>\<open>tool\<close>: it converts "there is a next step" into
  "the state is neither halting state" (\<open>ktm_step_src\<close>), and that is the only
  way to learn anything about the \<^emph>\<open>intermediate\<close> configurations of a run
  whose endpoints are all that is stated.

  The run form below is the one a race wants.  A run of \<open>n\<close> steps that ends
  accepting says nothing directly about step \<open>k < n\<close>; but the remainder is
  non-empty, so a step leaves that configuration, so it has not halted.  This
  is what lets a caller with only "the machine halts in exactly \<open>g n\<close>
  steps" conclude that it is \<^emph>\<open>still running\<close> at any earlier time.\<close>

lemma ktm_relpow_not_halted:
  assumes vM: "valid_ktm M"
      and run: "(C, C') \<in> (ktm_step (delta_ktm M)) ^^ n" and k: "k < n"
  obtains D
    where "(C, D) \<in> (ktm_step (delta_ktm M)) ^^ k"
      and "ktc_state D \<noteq> t_ktm M" and "ktc_state D \<noteq> r_ktm M"
proof -
  \<comment> \<open>the remainder is named by arithmetic and not by \<open>less_iff_Suc_add\<close>:
      handing \<^theory_text>\<open>blast\<close> an iff whose right-hand side is an existential over the
      same variable it is solving for does not terminate\<close>
  obtain c where n: "n = k + Suc c"
  proof -
    from k have "n = k + Suc (n - Suc k)" by simp
    then show thesis by (rule that)
  qed
  from run [unfolded n relpow_add] obtain D
    where CD: "(C, D) \<in> (ktm_step (delta_ktm M)) ^^ k"
      and rest: "(D, C') \<in> (ktm_step (delta_ktm M)) ^^ Suc c" by auto
  \<comment> \<open>the \<^emph>\<open>first\<close> step of the remainder, which is why the decomposition is
      named: \<^theory_text>\<open>auto\<close>'s default peels the last one, and the last step is the one
      whose source says nothing about \<open>D\<close>\<close>
  obtain E where "(D, E) \<in> ktm_step (delta_ktm M)"
    using relpow_Suc_D2 [OF rest] by blast
  from CD ktm_step_src_neq_t [OF vM this] ktm_step_src_neq_r [OF vM this]
  show thesis by (rule that)
qed

text \<open>Single-valuedness, transported from the tuples to the configurations.
  \<^const>\<open>det_ktm\<close> is stated of a whole machine, but a composite is
  deterministic only in \<^emph>\<open>parts\<close> --- its setup phase is forced while its arms
  are not --- so the useful form is generic in \<open>\<delta>\<close> and the machine-level
  reading is the corollary.  A typical use is a converse walk: it peels a
  step, instantiates a forward lemma about the same configuration, and pins
  the two together, so the transformed tape content is never inverted.

  The read component is what carries the argument.  Two steps out of one
  configuration read the same frame \<^term>\<open>\<lambda>k. ts k (n k)\<close>, so the tuple
  hypothesis applies at a common \<open>a\<close> and the write and the direction come
  back equal --- whereupon the two successors are equal as functions of the
  \<^emph>\<open>same\<close> \<open>ts\<close> and \<open>n\<close>.

  The hypothesis is asked for \<^emph>\<open>at the state the configuration is in\<close>, not at
  every state, because a phase-wise deterministic composite is exactly the case
  this is for: the argument never leaves \<^term>\<open>ktc_state C\<close>, so demanding more
  would be demanding what the consumer cannot supply.  The uniform reading is
  \<open>ktm_step_functional\<close> below, and \<open>det_ktm_step\<close> states it for a
  deterministic machine.\<close>

lemma ktm_step_det_at:
  assumes det: "\<And>a p\<^sub>1 b\<^sub>1 d\<^sub>1 p\<^sub>2 b\<^sub>2 d\<^sub>2.
                  (ktc_state C, a, p\<^sub>1, b\<^sub>1, d\<^sub>1) \<in> \<delta>
                    \<Longrightarrow> (ktc_state C, a, p\<^sub>2, b\<^sub>2, d\<^sub>2) \<in> \<delta>
                    \<Longrightarrow> (p\<^sub>1, b\<^sub>1, d\<^sub>1) = (p\<^sub>2, b\<^sub>2, d\<^sub>2)"
      and s\<^sub>1: "(C, C\<^sub>1) \<in> ktm_step \<delta>"
      and s\<^sub>2: "(C, C\<^sub>2) \<in> ktm_step \<delta>"
  shows "C\<^sub>1 = C\<^sub>2"
proof -
  from s\<^sub>1 obtain q ts n q\<^sub>1 a\<^sub>1 d\<^sub>1 where
      C: "C = KConfig q ts n"
    and C\<^sub>1: "C\<^sub>1 = KConfig q\<^sub>1 (\<lambda>k. (ts k)(n k := a\<^sub>1 k))
                            (\<lambda>k. go_move (d\<^sub>1 k) (n k))"
    and t\<^sub>1: "(q, \<lambda>k. ts k (n k), q\<^sub>1, a\<^sub>1, d\<^sub>1) \<in> \<delta>"
    by (auto elim: ktm_step.cases)
  from s\<^sub>2 obtain q' ts' n' q\<^sub>2 a\<^sub>2 d\<^sub>2 where
      C': "C = KConfig q' ts' n'"
    and C\<^sub>2: "C\<^sub>2 = KConfig q\<^sub>2 (\<lambda>k. (ts' k)(n' k := a\<^sub>2 k))
                            (\<lambda>k. go_move (d\<^sub>2 k) (n' k))"
    and t\<^sub>2: "(q', \<lambda>k. ts' k (n' k), q\<^sub>2, a\<^sub>2, d\<^sub>2) \<in> \<delta>"
    by (auto elim: ktm_step.cases)
  have "KConfig q ts n = KConfig q' ts' n'" using C C' by simp
  then have qe: "q' = q" and te: "ts' = ts" and ne: "n' = n" by auto
  from t\<^sub>2 [unfolded qe te ne] have t\<^sub>2': "(q, \<lambda>k. ts k (n k), q\<^sub>2, a\<^sub>2, d\<^sub>2) \<in> \<delta>" .
  from t\<^sub>1 have u\<^sub>1: "(ktc_state C, \<lambda>k. ts k (n k), q\<^sub>1, a\<^sub>1, d\<^sub>1) \<in> \<delta>"
    by (simp add: C)
  from t\<^sub>2' have u\<^sub>2: "(ktc_state C, \<lambda>k. ts k (n k), q\<^sub>2, a\<^sub>2, d\<^sub>2) \<in> \<delta>"
    by (simp add: C)
  have "(q\<^sub>1, a\<^sub>1, d\<^sub>1) = (q\<^sub>2, a\<^sub>2, d\<^sub>2)" by (rule det [OF u\<^sub>1 u\<^sub>2])
  then show ?thesis by (simp add: C\<^sub>1 C\<^sub>2 te ne)
qed

lemma det_ktm_step:
  assumes det: "det_ktm M"
      and s\<^sub>1: "(C, C\<^sub>1) \<in> ktm_step (delta_ktm M)"
      and s\<^sub>2: "(C, C\<^sub>2) \<in> ktm_step (delta_ktm M)"
  shows "C\<^sub>1 = C\<^sub>2"
proof (rule ktm_step_det_at [OF _ s\<^sub>1 s\<^sub>2])
  fix a p\<^sub>1 b\<^sub>1 d\<^sub>1 p\<^sub>2 b\<^sub>2 d\<^sub>2
  assume "(ktc_state C, a, p\<^sub>1, b\<^sub>1, d\<^sub>1) \<in> delta_ktm M"
     and "(ktc_state C, a, p\<^sub>2, b\<^sub>2, d\<^sub>2) \<in> delta_ktm M"
  with det show "(p\<^sub>1, b\<^sub>1, d\<^sub>1) = (p\<^sub>2, b\<^sub>2, d\<^sub>2)" unfolding det_ktm_def by blast
qed

text \<open>The same fact once more in the library's vocabulary, which is what
  buys the run-level statement for nothing: \<^theory_text>\<open>single_valued_relpow\<close> lifts
  single-valuedness along \<open>^^ n\<close>, so a deterministic machine's runs of a
  \<^emph>\<open>given\<close> length are unique without an induction here.  The step-level and
  run-level readings are wanted in different places --- the step level pins a
  converse walk, the run level pins an alarm --- so both names earn their
  keep.\<close>

lemma det_ktm_single_valued:
  assumes det: "det_ktm M"
  shows "single_valued (ktm_step (delta_ktm M))"
  by (blast intro: single_valuedI det_ktm_step [OF det])

lemma det_ktm_relpow_unique:
  assumes det: "det_ktm M"
      and r\<^sub>1: "(C, C\<^sub>1) \<in> (ktm_step (delta_ktm M)) ^^ n"
      and r\<^sub>2: "(C, C\<^sub>2) \<in> (ktm_step (delta_ktm M)) ^^ n"
  shows "C\<^sub>1 = C\<^sub>2"
  by (rule single_valuedD
        [OF single_valued_relpow [OF det_ktm_single_valued [OF det]] r\<^sub>1 r\<^sub>2])

lemma det_ktm_dead_end_no_longer_run:
  assumes det: "det_ktm M"
      and stopped: "(initial, final) \<in> (ktm_step (delta_ktm M)) ^^ amount"
      and dead_end: "\<forall>following. (final, following) \<notin> ktm_step (delta_ktm M)"
      and longer_run: "(initial, other) \<in> (ktm_step (delta_ktm M)) ^^ longer"
      and longer: "amount < longer"
  shows False
proof -
  have "amount = longer \<and> final = other"
    by (rule relpow_halted_le [where R = UNIV and H = "{final}",
                               OF _ _ _ _ stopped _ longer_run])
       (use dead_end longer det_ktm_step [OF det] in auto)
  with longer show False by simp
qed


subsection \<open>Step determinism and acceptance monotonicity\<close>

text \<open>Two general facts promoted from the finite-control layer: a step of
  a functional transition relation is deterministic (a configuration has at
  most one successor), which is \<open>ktm_step_det_at\<close> with the hypothesis asked
  at every state, and weak time-bounded acceptance is monotone in the time
  budget.\<close>

lemma ktm_step_functional:
  assumes fdet: "\<forall>q a p\<^sub>1 b\<^sub>1 d\<^sub>1 p\<^sub>2 b\<^sub>2 d\<^sub>2.
      (q, a, p\<^sub>1, b\<^sub>1, d\<^sub>1) \<in> \<delta> \<longrightarrow> (q, a, p\<^sub>2, b\<^sub>2, d\<^sub>2) \<in> \<delta>
        \<longrightarrow> (p\<^sub>1, b\<^sub>1, d\<^sub>1) = (p\<^sub>2, b\<^sub>2, d\<^sub>2)"
    and step1: "(c, c1) \<in> ktm_step \<delta>"
    and step2: "(c, c2) \<in> ktm_step \<delta>"
  shows "c1 = c2"
  using fdet by (blast intro: ktm_step_det_at [OF _ step1 step2])

text \<open>Weak time-bounded acceptance is monotone in the time budget.\<close>

lemma accepts_in_time_ktm_mono:
  "accepts_in_time_ktm M w t \<Longrightarrow> t \<le> t' \<Longrightarrow> accepts_in_time_ktm M w t'"
  unfolding accepts_in_time_ktm_def by (meson order_trans)


subsection \<open>Reaching a given state within a time bound\<close>

text \<open>Bounded acceptance names the accept state.  A simulation argument
  usually never uses which halting state a run ends in, and a client that
  bounds rejection as well as acceptance needs the same statement for the
  reject state; so the bound is stated once for an arbitrary state, and
  acceptance is its instance at @{term "t_ktm M"}.\<close>

definition reaches_state_in_time_ktm ::
  "('q, 'a) ktm \<Rightarrow> 'a list \<Rightarrow> 'q \<Rightarrow> nat \<Rightarrow> bool" where
  "reaches_state_in_time_ktm M w q T \<longleftrightarrow>
     (\<exists>n c. n \<le> T
       \<and> (init_config_ktm M w, c) \<in> (ktm_step (delta_ktm M)) ^^ n
       \<and> ktc_state c = q)"

lemma reaches_state_in_time_ktmI:
  assumes "n \<le> T"
      and "(init_config_ktm M w, c) \<in> (ktm_step (delta_ktm M)) ^^ n"
      and "ktc_state c = q"
  shows "reaches_state_in_time_ktm M w q T"
  using assms unfolding reaches_state_in_time_ktm_def by blast

lemma reaches_state_in_time_ktmE:
  assumes "reaches_state_in_time_ktm M w q T"
  obtains n c where "n \<le> T"
    and "(init_config_ktm M w, c) \<in> (ktm_step (delta_ktm M)) ^^ n"
    and "ktc_state c = q"
  using assms unfolding reaches_state_in_time_ktm_def by blast

lemma reaches_state_in_time_ktm_mono:
  assumes "reaches_state_in_time_ktm M w q T" and "T \<le> T'"
  shows "reaches_state_in_time_ktm M w q T'"
proof -
  from assms(1) obtain n c where n: "n \<le> T"
    and run: "(init_config_ktm M w, c) \<in> (ktm_step (delta_ktm M)) ^^ n"
    and state: "ktc_state c = q"
    by (rule reaches_state_in_time_ktmE)
  from order_trans [OF n assms(2)] run state show ?thesis
    by (rule reaches_state_in_time_ktmI)
qed

lemma accepts_in_time_ktm_iff_reaches:
  "accepts_in_time_ktm M w T
     \<longleftrightarrow> reaches_state_in_time_ktm M w (t_ktm M) T"
  unfolding accepts_in_time_ktm_def reaches_state_in_time_ktm_def by blast

end
