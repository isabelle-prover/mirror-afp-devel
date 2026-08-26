theory Multitape_Substrate
  imports Multitape_Substrate_Core
begin

section \<open>Substrate metatheory\<close>

text \<open>The substrate metatheory --- \<^emph>\<open>our\<close> additions over the
  Dalvit--Thiemann definition surface isolated in \<open>Multitape_Substrate_Core\<close>:
  relation-power and finiteness utilities, the \<open>valid_mttm\<close>
  axiom-extraction toolkit, per-step and reachability validity
  preservation, and the displacement / left-endmarker / no-write tape
  tools.  The core (\<open>Multitape_Substrate_Core\<close>) carries the datatypes, accessors,
  step relation, and the validity / language definitions.\<close>


subsection \<open>Relation-power and finiteness utilities\<close>

lemma finite_UNIV_dir [simp, intro]: "finite (UNIV :: dir set)"
proof -
  have id: "UNIV = {L, R, N}"
    using dir.exhaust by auto
  show ?thesis unfolding id by auto
qed

hide_const (open) L R N

text \<open>Blank-tail finiteness: the set of total functions \<open>nat \<Rightarrow> 'b\<close>
  ranging in a finite codomain \<open>B\<close> and \<^emph>\<open>constant \<open>c\<close> beyond an
  index \<open>k\<close>\<close> is finite.  This replaces the function-space finiteness
  lemmas (\<open>fin_funcsetI\<close> / \<open>finite_UNIV_fun_dir\<close>) that the AFP source
  relied on: those are false at the value-level \<open>nat\<close> index, where
  the domain is infinite.  Finiteness is recovered from the support
  bound — a blank-tail function is determined by its restriction to
  \<open>{..<k}\<close>, of which there are finitely many.  Used to re-derive
  \<open>finite \<delta>\<close> for constructed machines (\<open>valid_mttm_finite_delta\<close>),
  with codomain \<open>\<Gamma>\<close> (blank tail) for read/write tuples and \<open>dir\<close>
  (N tail) for the move tuples.\<close>

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

lemma relpow_transI:
  "(x, y) \<in> R^^n \<Longrightarrow> (y, z) \<in> R^^m \<Longrightarrow> (x, z) \<in> R^^(n + m)"
  by (simp add: relcomp.intros relpow_add)

lemma relpow_mono: fixes R :: "'a rel"
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


subsection \<open>Functional axiom-extraction toolkit\<close>

text \<open>Convenience lemmas projecting the substrate's structural
  axioms out of @{const valid_mttm} at the functional layer.
  Each one is a one-shot \<open>by (cases M) auto\<close>: the case-decomposition
  rewrites @{term M} into MTTM-form, exposes the @{thm[source] valid_mttm.simps}
  conjunction, and \<open>auto\<close> extracts the relevant conjunct.

  These replace what used to be locale-routed retrievals of the
  form \<open>multitape_tm.X[OF loc]\<close>.\<close>

lemma valid_mttm_finite_Q:
  assumes "valid_mttm M"
  shows "finite (Q_tm M)"
  using assms by (cases M) auto

lemma valid_mttm_finite_Gamma:
  assumes "valid_mttm M"
  shows "finite (\<Gamma>_tm M)"
  using assms by (cases M) auto

lemma valid_mttm_Sigma_sub_Gamma:
  assumes "valid_mttm M"
  shows "Sigma_tm M \<subseteq> \<Gamma>_tm M"
  using assms by (cases M) auto

lemma valid_mttm_s_in_Q:
  assumes "valid_mttm M"
  shows "s_tm M \<in> Q_tm M"
  using assms by (cases M) auto

lemma valid_mttm_t_in_Q:
  assumes "valid_mttm M"
  shows "t_tm M \<in> Q_tm M"
  using assms by (cases M) auto

lemma valid_mttm_r_in_Q:
  assumes "valid_mttm M"
  shows "r_tm M \<in> Q_tm M"
  using assms by (cases M) auto

lemma valid_mttm_blank_in_Gamma:
  assumes "valid_mttm M"
  shows "bl_tm M \<in> \<Gamma>_tm M"
  using assms by (cases M) auto

lemma valid_mttm_blank_not_Sigma:
  assumes "valid_mttm M"
  shows "bl_tm M \<notin> Sigma_tm M"
  using assms by (cases M) auto

lemma valid_mttm_LE_in_Gamma:
  assumes "valid_mttm M"
  shows "le_tm M \<in> \<Gamma>_tm M"
  using assms by (cases M) auto

lemma valid_mttm_LE_not_Sigma:
  assumes "valid_mttm M"
  shows "le_tm M \<notin> Sigma_tm M"
  using assms by (cases M) auto

lemma valid_mttm_t_neq_r:
  assumes "valid_mttm M"
  shows "t_tm M \<noteq> r_tm M"
  using assms by (cases M) auto

lemma valid_mttm_k_pos:
  assumes "valid_mttm M"
  shows "0 < k_tm M"
  using assms by (cases M) auto

lemma valid_mttm_delta_set:
  assumes "valid_mttm M"
  shows "delta_tm M \<subseteq>
           (Q_tm M - {t_tm M, r_tm M})
             \<times> (UNIV \<rightarrow> \<Gamma>_tm M)
             \<times> Q_tm M
             \<times> (UNIV \<rightarrow> \<Gamma>_tm M)
             \<times> (UNIV \<rightarrow> UNIV)"
  using assms by (cases M) auto

text \<open>Range typing for transition tuples: pulls the four
  per-component facts from a single transition membership.\<close>

lemma valid_mttm_delta:
  assumes vM: "valid_mttm M"
    and tr: "(q, a, q', b, d) \<in> delta_tm M"
  shows "q \<in> Q_tm M" "a k \<in> \<Gamma>_tm M" "q' \<in> Q_tm M" "b k \<in> \<Gamma>_tm M"
  using valid_mttm_delta_set[OF vM] tr by auto

text \<open>Left-endmarker discipline: transitions reading \<open>le\<close> must
  rewrite \<open>le\<close> with itself and move only \<open>N\<close> or \<open>R\<close>.\<close>

lemma valid_mttm_deltaLE:
  assumes vM: "valid_mttm M"
    and tr: "(q, a, q', a', d) \<in> delta_tm M"
    and LE: "a k = le_tm M"
  shows "a' k = le_tm M \<and> d k \<in> {dir.N, dir.R}"
  using vM tr LE by (cases M) auto

text \<open>Left-endmarker write discipline: a transition writes \<open>le\<close> on
  tape \<open>k\<close> only when it was reading \<open>le\<close> on the same tape.  This is
  exactly the content of @{const le_unique} specialised to one tape /
  transition; it is the sole place that fact is extracted.  Needed by
  \<open>ae_coupled_run_aux\<close> to preserve the "no LE in window" invariant
  across an M-step.  Takes @{const le_unique} (not @{const valid_mttm}):
  it is the property a machine may forgo, so consumers thread it
  explicitly rather than reading it off \<open>valid_mttm\<close>.\<close>

lemma valid_mttm_deltaLE_no_write:
  assumes lu: "le_unique M"
    and tr: "(q, a, q', a', d) \<in> delta_tm M"
    and LE': "a' k = le_tm M"
  shows "a k = le_tm M"
  using lu[unfolded le_unique_def] tr LE' by blast

text \<open>Support invariant: every transition of a valid machine is
  blank on reads and writes, and stationary, at every tape index
  \<open>j \<ge> k_tm M\<close>.  The value-level confinement of a \<open>k\<close>-tape machine's
  action to tapes \<open>0 \<dots> k - 1\<close>.\<close>

lemma valid_mttm_delta_support:
  assumes vM: "valid_mttm M"
    and tr: "(q, a, q', a', d) \<in> delta_tm M"
    and j: "j \<ge> k_tm M"
  shows "a j = bl_tm M \<and> a' j = bl_tm M \<and> d j = dir.N"
proof -
  obtain Q \<Sigma> \<Gamma> bl le \<delta> s t r K where M_eq:
      "M = MTTM Q \<Sigma> \<Gamma> bl le \<delta> s t r K"
    by (cases M)
  have supp:
      "\<forall>q a q' a' d. (q, a, q', a', d) \<in> \<delta> \<longrightarrow>
                       (\<forall>j \<ge> K. a j = bl \<and> a' j = bl \<and> d j = dir.N)"
    using vM[unfolded M_eq valid_mttm.simps] by blast
  from tr M_eq have tr_delta: "(q, a, q', a', d) \<in> \<delta>" by simp
  from j M_eq have jK: "j \<ge> K" by simp
  have bleq: "bl_tm M = bl" using M_eq by simp
  from supp tr_delta jK have "a j = bl \<and> a' j = bl \<and> d j = dir.N" by blast
  thus ?thesis using bleq by simp
qed

text \<open>Finiteness of \<open>\<delta>\<close> from bounded support: a valid machine's
  transition relation is finite.  The value-level replacement for
  the AFP source's function-space finiteness over a finite tape
  type.  Each transition's read / write tuples range in the finite
  @{term \<Gamma>} and are blank beyond \<open>k\<close>, each move tuple is \<open>N\<close>
  beyond \<open>k\<close>; by @{thm[source] finite_tail_const_funcs} there are
  finitely many of each, so \<open>\<delta>\<close> embeds in a finite product.\<close>

lemma valid_mttm_finite_delta:
  assumes vM: "valid_mttm M"
  shows "finite (delta_tm M)"
proof -
  obtain Q \<Sigma> \<Gamma> bl le \<delta> s t r K where M_eq:
      "M = MTTM Q \<Sigma> \<Gamma> bl le \<delta> s t r K"
    by (cases M)
  have finQ: "finite Q" using valid_mttm_finite_Q[OF vM] M_eq by simp
  have finG: "finite \<Gamma>" using valid_mttm_finite_Gamma[OF vM] M_eq by simp
  let ?A = "{a. (\<forall>j. a j \<in> \<Gamma>) \<and> (\<forall>j \<ge> K. a j = bl)}"
  let ?D = "{d. (\<forall>j. d j \<in> (UNIV :: dir set)) \<and> (\<forall>j \<ge> K. d j = dir.N)}"
  have finA: "finite ?A" by (rule finite_tail_const_funcs[OF finG, of K bl])
  have finD: "finite ?D" by (rule finite_tail_const_funcs[OF finite_UNIV_dir, of K dir.N])
  have finprod: "finite ((Q - {t, r}) \<times> ?A \<times> Q \<times> ?A \<times> ?D)"
    using finQ finA finD by (intro finite_cartesian_product) auto
  have sub: "delta_tm M \<subseteq> (Q - {t, r}) \<times> ?A \<times> Q \<times> ?A \<times> ?D"
  proof
    fix x assume xd: "x \<in> delta_tm M"
    obtain q a q' a' d where x: "x = (q, a, q', a', d)"
      by (cases x)
    from valid_mttm_delta_set[OF vM] xd x M_eq
    have q_mem: "q \<in> Q - {t, r}" and a_pi: "a \<in> UNIV \<rightarrow> \<Gamma>"
      and q'_mem: "q' \<in> Q" and a'_pi: "a' \<in> UNIV \<rightarrow> \<Gamma>"
      by auto
    from a_pi have aG: "\<forall>j. a j \<in> \<Gamma>" by (auto simp: Pi_iff)
    from a'_pi have a'G: "\<forall>j. a' j \<in> \<Gamma>" by (auto simp: Pi_iff)
    have trM: "(q, a, q', a', d) \<in> delta_tm M" using xd x by simp
    have supp: "\<forall>j \<ge> K. a j = bl \<and> a' j = bl \<and> d j = dir.N"
    proof (intro allI impI)
      fix j assume "K \<le> j"
      hence "j \<ge> k_tm M" using M_eq by simp
      thus "a j = bl \<and> a' j = bl \<and> d j = dir.N"
        using valid_mttm_delta_support[OF vM trM] M_eq by simp
    qed
    have "a \<in> ?A" using aG supp by auto
    moreover have "a' \<in> ?A" using a'G supp by auto
    moreover have "d \<in> ?D" using supp by auto
    ultimately show "x \<in> (Q - {t, r}) \<times> ?A \<times> Q \<times> ?A \<times> ?D"
      using x q_mem q'_mem by auto
  qed
  show ?thesis using sub finprod by (rule finite_subset)
qed

text \<open>State membership at the source of an \<open>mttm_step\<close>: the
  source state is in \<open>Q_tm M\<close> and is neither the accept nor
  the reject state.  Direct consequence of the \<open>mttm_step\<close>
  introduction rule plus \<open>valid_mttm_delta_set\<close>'s range typing
  (which excludes halting states from the source projection of
  \<open>delta_tm M\<close>).

  Used by the chunked-induction engine
  \<open>ae_simulation_phase_chunked\<close>: when the M-trace
  \<open>(cM, cM_final) \<in> mttm_step (delta_tm M) ^^ (Suc n)\<close>
  is non-empty, the first step exists and forces \<open>cM\<close>'s state
  to be non-halt and in \<open>Q\<close>, which feeds
  \<open>ae_simulates_forward_stage_general\<close>'s \<open>qM_in_Q\<close> /
  \<open>q_neq_t\<close> / \<open>q_neq_r\<close> hypotheses.\<close>

lemma mttm_step_src:
  fixes M :: "('q, 'a) mttm"
  assumes vM:   "valid_mttm M"
    and step: "(c, c') \<in> mttm_step (delta_tm M)"
  shows mttm_step_src_in_Q:    "mt_state c \<in> Q_tm M"
    and mttm_step_src_neq_t:   "mt_state c \<noteq> t_tm M"
    and mttm_step_src_neq_r:   "mt_state c \<noteq> r_tm M"
proof -
  from step obtain q ts n q' a dir where
      c_eq: "c = Config\<^sub>M q ts n"
    and tr: "(q, \<lambda>k. ts k (n k), q', a, dir) \<in> delta_tm M"
    by (auto elim: mttm_step.cases)
  have q_eq: "mt_state c = q" using c_eq by simp
  have q_in_strict: "q \<in> Q_tm M - {t_tm M, r_tm M}"
    using valid_mttm_delta_set[OF vM] tr by auto
  show "mt_state c \<in> Q_tm M"  using q_eq q_in_strict by simp
  show "mt_state c \<noteq> t_tm M" using q_eq q_in_strict by simp
  show "mt_state c \<noteq> r_tm M" using q_eq q_in_strict by simp
qed


subsection \<open>Functional validity preservation\<close>

text \<open>Per-step preservation of @{const valid_config_mttm}: a valid
  configuration steps only to valid configurations.  Re-derived
  directly from @{thm[source] valid_mttm_delta} (range typing),
  @{thm[source] valid_mttm_deltaLE} (left-endmarker discipline),
  and @{thm[source] valid_mttm_delta_support} (the new inactive-tape
  blank-tail case).\<close>

lemma valid_step_mttm:
  fixes M :: "('q, 'a) mttm"
  assumes vM:    "valid_mttm M"
    and step:    "(c, c') \<in> mttm_step (delta_tm M)"
    and val_c:   "valid_config_mttm M c"
  shows "valid_config_mttm M c'"
proof -
  obtain Q \<Sigma> \<Gamma> bl le \<delta> s t r K where M_eq:
      "M = MTTM Q \<Sigma> \<Gamma> bl le \<delta> s t r K"
    by (cases M)
  obtain q ts n where c_eq: "c = Config\<^sub>M q ts n"
    by (cases c)
  from step M_eq c_eq have step_delta:
      "(Config\<^sub>M q ts n, c') \<in> mttm_step \<delta>"
    by simp
  obtain q' a dir where c'_eq:
      "c' = Config\<^sub>M q' (\<lambda>k. (ts k)(n k := a k))
                       (\<lambda>k. go_dir (dir k) (n k))"
    and tr: "(q, (\<lambda>k. ts k (n k)), q', a, dir) \<in> \<delta>"
    using step_delta by (auto elim: mttm_step.cases)
  from val_c c_eq M_eq have q_in: "q \<in> Q"
    and ts_Gamma: "\<And>k. range (ts k) \<subseteq> \<Gamma>"
    and ts_LE: "\<And>k. k < K \<Longrightarrow> ts k 0 = le"
    and ts_blank: "\<And>k p. k \<ge> K \<Longrightarrow> ts k p = bl"
    by auto
  from tr M_eq have tr_M: "(q, (\<lambda>k. ts k (n k)), q', a, dir) \<in> delta_tm M"
    by simp
  have q'_in: "q' \<in> Q_tm M" and a_Gamma: "\<And>k. a k \<in> \<Gamma>_tm M"
    using valid_mttm_delta[OF vM tr_M] by auto
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
      have read_LE_le: "(\<lambda>j. ts j (n j)) k = le_tm M"
        using read_LE M_eq by simp
      have "a k = le_tm M"
        using valid_mttm_deltaLE[OF vM tr_M read_LE_le] by simp
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
      have "k \<ge> k_tm M" using kK M_eq by simp
      hence "a k = bl_tm M"
        using valid_mttm_delta_support[OF vM tr_M] by simp
      thus ?thesis using M_eq by simp
    qed
    show "((ts k)(n k := a k)) p = bl"
      using ts_blank[OF kK] ak_bl by (cases "p = n k") auto
  qed
  show ?thesis
    unfolding M_eq c'_eq valid_config_mttm.simps
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

text \<open>Initial-configuration validity: a valid \<open>M\<close>'s initial
  configuration on a valid input is itself valid.\<close>

lemma valid_init_config_mttm:
  fixes M :: "('q, 'a) mttm"
  assumes vM: "valid_mttm M"
    and w:    "set w \<subseteq> Sigma_tm M"
  shows "valid_config_mttm M (init_config_mttm M w)"
proof -
  obtain Q \<Sigma> \<Gamma> bl le \<delta> s t r K where M_eq:
      "M = MTTM Q \<Sigma> \<Gamma> bl le \<delta> s t r K"
    by (cases M)
  have w_Sigma: "set w \<subseteq> \<Sigma>"
    using w M_eq by simp
  have s_in: "s \<in> Q" using valid_mttm_s_in_Q[OF vM] M_eq by simp
  have Sigma_sub: "\<Sigma> \<subseteq> \<Gamma>" using valid_mttm_Sigma_sub_Gamma[OF vM] M_eq by simp
  have bl_in: "bl \<in> \<Gamma>" using valid_mttm_blank_in_Gamma[OF vM] M_eq by simp
  have le_in: "le \<in> \<Gamma>" using valid_mttm_LE_in_Gamma[OF vM] M_eq by simp
  show ?thesis
    unfolding M_eq init_config_mttm.simps valid_config_mttm.simps
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

lemma valid_reach_mttm:
  fixes M :: "('q, 'a) mttm"
  assumes vM:    "valid_mttm M"
    and w:       "set w \<subseteq> Sigma_tm M"
    and reach:   "(init_config_mttm M w, c) \<in> (mttm_step (delta_tm M))\<^sup>*"
  shows "valid_config_mttm M c"
  using reach
proof induction
  case base
  show ?case using valid_init_config_mttm[OF vM w] .
next
  case (step y z)
  show ?case using valid_step_mttm[OF vM step.hyps(2) step.IH] .
qed

text \<open>Blank-tail accessor for a valid configuration: beyond the
  machine's tape count \<open>k_tm M\<close> every cell holds the blank
  \<open>bl_tm M\<close>.  Used on the reverse lift's padding tapes, where the
  per-tape window invariant is unavailable (it constrains the LE
  home cell, which is blank on padding) and the read-match must
  instead come from the substrate blank-tail.\<close>

lemma valid_config_mttm_blank_tail:
  assumes valc: "valid_config_mttm M c"
      and kge:  "i \<ge> k_tm M"
  shows "mt_tape c i p = bl_tm M"
proof -
  obtain Q \<Sigma> \<Gamma> bl le \<delta> s t r K where
      M_eq: "M = MTTM Q \<Sigma> \<Gamma> bl le \<delta> s t r K"
    by (cases M)
  obtain q ts n where c_eq: "c = Config\<^sub>M q ts n" by (cases c)
  from valc kge show ?thesis
    unfolding M_eq c_eq by auto
qed

text \<open>Validity preservation along an \<open>n\<close>-step substrate trace
  from an arbitrary valid configuration (generic relpow closure of
  @{thm[source] valid_step_mttm}; @{thm[source] valid_reach_mttm}
  anchors only at \<open>init_config_mttm\<close>).  Threads the blank-tail
  validity of the reverse lift's intermediate configs \<open>cM_n'\<close>
  through the chain induction.\<close>

lemma valid_reach_relpow_mttm:
  assumes vM:    "valid_mttm M"
      and valc:  "valid_config_mttm M c"
      and reach: "(c, c') \<in> mttm_step (delta_tm M) ^^ n"
  shows "valid_config_mttm M c'"
  using reach
proof (induction n arbitrary: c')
  case 0
  thus ?case using valc by simp
next
  case (Suc n)
  from Suc.prems obtain c'' where
      mid: "(c, c'') \<in> mttm_step (delta_tm M) ^^ n"
    and lst: "(c'', c') \<in> mttm_step (delta_tm M)"
    by (rule relpow_Suc_E)
  have "valid_config_mttm M c''" using Suc.IH[OF mid] .
  thus ?case by (rule valid_step_mttm[OF vM lst])
qed

text \<open>Per-tape LE-pinning corollary: along any reachable trace
  from a valid initial configuration, every \<^emph>\<open>active\<close> tape
  (index \<open>k < k_tm M\<close>) carries \<open>le_tm M\<close> at position 0.

  Note: \<open>valid_config_mttm\<close> only encodes the position-0 = LE
  constraint on active tapes, not the converse (positions \<open>p \<noteq> 0\<close>
  may legally hold LE in an arbitrary valid config).  The "LE only
  at position 0" property is reach-specific and proved separately
  in the companion lemma below.\<close>

lemma valid_reach_LE_pos0_mttm:
  fixes M :: "('q, 'a) mttm"
  assumes vM:  "valid_mttm M"
    and w:     "set w \<subseteq> Sigma_tm M"
    and reach: "(init_config_mttm M w, Config\<^sub>M q ts n)
                  \<in> (mttm_step (delta_tm M))\<^sup>*"
    and kK:    "k < k_tm M"
  shows "ts k 0 = le_tm M"
proof -
  have val: "valid_config_mttm M (Config\<^sub>M q ts n)"
    using valid_reach_mttm[OF vM w reach] .
  obtain Q \<Sigma> \<Gamma> bl le \<delta> sM t r K where M_eq:
      "M = MTTM Q \<Sigma> \<Gamma> bl le \<delta> sM t r K"
    by (cases M)
  have "k < K" using kK M_eq by simp
  thus ?thesis using val M_eq by simp
qed

text \<open>Dual to @{thm[source] valid_reach_LE_pos0_mttm}: along any reachable
  trace from a valid initial configuration whose blank symbol differs
  from the left endmarker, every cell at a position \<open>p \<noteq> 0\<close> on any
  tape is not the left endmarker.  Proof: induction on the
  reachability relation.  Base: \<open>init_config_mttm\<close> places \<open>le\<close>
  only at position 0 of active tapes (input cells are in \<open>\<Sigma>\<close> hence
  \<open>\<noteq> le\<close>; other active cells and all inactive cells are \<open>bl\<close> which
  by hypothesis \<open>\<noteq> le\<close>).  Step: cells away from the head are
  preserved (substrate update is \<open>(ts k)(n k := a k)\<close>); at the head,
  the substrate's \<open>\<delta>LE\<close>-no-write rule says the write equals \<open>le\<close>
  only if the read did, which by IH is impossible since the read
  sits at the head position \<open>n k\<close> (and if \<open>n k = p \<noteq> 0\<close> the IH
  gives the read is not \<open>le\<close>; if \<open>n k = 0\<close> then \<open>p \<noteq> n k\<close> and the
  off-head case fires).\<close>

lemma valid_reach_LE_only_pos0_mttm:
  fixes M :: "('q, 'a) mttm"
    and c :: "('a, 'q) mt_config"
    and k :: nat
    and p :: nat
  assumes vM:        "valid_mttm M"
    and lu:          "le_unique M"
    and w:           "set w \<subseteq> Sigma_tm M"
    and reach:       "(init_config_mttm M w, c) \<in> (mttm_step (delta_tm M))\<^sup>*"
    and p_ne_0:      "p \<noteq> 0"
    and bl_neq_le:   "bl_tm M \<noteq> le_tm M"
  shows "mt_tape c k p \<noteq> le_tm M"
proof -
  obtain Q \<Sigma> \<Gamma> bl le \<delta> sM tt rr K where M_eq:
      "M = MTTM Q \<Sigma> \<Gamma> bl le \<delta> sM tt rr K"
    by (cases M)
  have le_eq:  "le_tm M = le"  using M_eq by simp
  have bl_eq:  "bl_tm M = bl"  using M_eq by simp
  have bl_ne_le: "bl \<noteq> le" using bl_neq_le le_eq bl_eq by simp
  have le_not_Sigma: "le \<notin> \<Sigma>"
    using valid_mttm_LE_not_Sigma[OF vM] M_eq by simp
  have w_Sigma: "set w \<subseteq> \<Sigma>" using w M_eq by simp
  have main:
    "\<forall>c'. (init_config_mttm M w, c') \<in> (mttm_step (delta_tm M))\<^sup>*
            \<longrightarrow> mt_tape c' k p \<noteq> le_tm M"
  proof (intro allI impI)
    fix c'
    assume r: "(init_config_mttm M w, c') \<in> (mttm_step (delta_tm M))\<^sup>*"
    show "mt_tape c' k p \<noteq> le_tm M"
      using r
    proof induction
      case base
      have tape_p_init:
          "mt_tape (init_config_mttm M w) k p
             = (if k < K
                then (if p = 0 then le
                      else if k = 0 \<and> p \<le> length w then w ! (p - 1)
                      else bl)
                else bl)"
        unfolding M_eq init_config_mttm.simps by simp
      show ?case
      proof (cases "k = 0 \<and> p \<le> length w")
        case True
        have K_pos: "0 < K" using valid_mttm_k_pos[OF vM] M_eq by simp
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
        have "mt_tape (init_config_mttm M w) k p = bl"
          using tape_p_init False p_ne_0 by (cases "k < K") auto
        thus ?thesis using bl_ne_le le_eq by simp
      qed
    next
      case (step y z)
      have ne_y: "mt_tape y k p \<noteq> le_tm M" using step.IH .
      obtain qy ts n where y_eq: "y = Config\<^sub>M qy ts n"
        by (cases y)
      from step.hyps(2) y_eq obtain q' a dr where
          z_eq: "z = Config\<^sub>M q'
                       (\<lambda>kk. (ts kk)(n kk := a kk))
                       (\<lambda>kk. go_dir (dr kk) (n kk))"
          and tr: "(qy, (\<lambda>kk. ts kk (n kk)), q', a, dr) \<in> delta_tm M"
        by (auto elim: mttm_step.cases)
      show ?case
      proof (cases "n k = p")
        case False
        have "mt_tape z k p = ((ts k)(n k := a k)) p" using z_eq by simp
        also have "\<dots> = ts k p" using False by simp
        also have "\<dots> = mt_tape y k p" using y_eq by simp
        finally have "mt_tape z k p = mt_tape y k p" .
        thus ?thesis using ne_y by simp
      next
        case True
        have read_at_p: "ts k (n k) = mt_tape y k p"
          using y_eq True by simp
        have read_ne: "ts k (n k) \<noteq> le_tm M"
          using ne_y read_at_p by simp
        have a_ne: "a k \<noteq> le_tm M"
        proof
          assume a_le: "a k = le_tm M"
          have "(\<lambda>kk. ts kk (n kk)) k = le_tm M"
            using valid_mttm_deltaLE_no_write[OF lu tr a_le] by simp
          hence "ts k (n k) = le_tm M" by simp
          thus False using read_ne by simp
        qed
        have "mt_tape z k p = ((ts k)(n k := a k)) p" using z_eq by simp
        also have "\<dots> = a k" using True by simp
        finally have "mt_tape z k p = a k" .
        thus ?thesis using a_ne by simp
      qed
    qed
  qed
  show ?thesis using main reach by blast
qed


subsection \<open>Step locality: non-head cells preserved, head moves by \<open>\<le>\<close> 1\<close>

text \<open>Two structural facts about \<open>mttm_step\<close> that fall directly out
  of the single rule's body \<open>(ts k)(n k := a k)\<close> and
  \<open>go_dir (dir k) (n k)\<close>: a single step modifies only the head
  cell on each tape, and the head displaces by at most one position
  per tape per step.  These are generic over \<open>\<delta>\<close> and used by
  alphabet-enlargement / -reduction to argue that cells outside a
  bounded window are unchanged after \<open>n\<close> steps.\<close>

lemma mttm_step_tape_off_head:
  assumes step: "(c, c') \<in> mttm_step \<delta>"
    and ne:     "p \<noteq> mt_pos c k"
  shows "mt_tape c' k p = mt_tape c k p"
proof -
  from step obtain q ts n q' a dr where
      c_eq:  "c = Config\<^sub>M q ts n"
    and c'_eq: "c' = Config\<^sub>M q'
                       (\<lambda>k. (ts k)(n k := a k))
                       (\<lambda>k. go_dir (dr k) (n k))"
    by (auto elim: mttm_step.cases)
  from ne c_eq have "p \<noteq> n k" by simp
  thus ?thesis by (simp add: c_eq c'_eq)
qed

lemma mttm_step_pos_displacement:
  assumes step: "(c, c') \<in> mttm_step \<delta>"
  shows "mt_pos c' k \<le> mt_pos c k + 1
         \<and> mt_pos c k \<le> mt_pos c' k + 1"
proof -
  from step obtain q ts n q' a dr where
      c_eq:  "c = Config\<^sub>M q ts n"
    and c'_eq: "c' = Config\<^sub>M q'
                       (\<lambda>k. (ts k)(n k := a k))
                       (\<lambda>k. go_dir (dr k) (n k))"
    by (auto elim: mttm_step.cases)
  have pos: "mt_pos c k = n k" by (simp add: c_eq)
  have pos': "mt_pos c' k = go_dir (dr k) (n k)" by (simp add: c'_eq)
  show ?thesis
    unfolding pos pos' by (cases "dr k") auto
qed

text \<open>\<open>n\<close>-step lift: after \<open>n\<close> steps, head displacement on each
  tape is at most \<open>n\<close>.\<close>

lemma mttm_relpow_pos_displacement:
  assumes "(c, c') \<in> mttm_step \<delta> ^^ n"
  shows "mt_pos c' k \<le> mt_pos c k + n
         \<and> mt_pos c k \<le> mt_pos c' k + n"
  using assms
proof (induction n arbitrary: c')
  case 0
  thus ?case by simp
next
  case (Suc n)
  from Suc.prems obtain c'' where
      ih: "(c, c'') \<in> mttm_step \<delta> ^^ n"
    and step: "(c'', c') \<in> mttm_step \<delta>"
    by (auto elim: relpow_Suc_E)
  have h1: "mt_pos c'' k \<le> mt_pos c k + n
            \<and> mt_pos c k \<le> mt_pos c'' k + n"
    using Suc.IH[OF ih] .
  have h2: "mt_pos c' k \<le> mt_pos c'' k + 1
            \<and> mt_pos c'' k \<le> mt_pos c' k + 1"
    using mttm_step_pos_displacement[OF step] .
  from h1 h2 show ?case by linarith
qed

text \<open>\<open>n\<close>-step lift: cells more than \<open>n\<close> away from the start head
  position are unchanged after \<open>n\<close> steps.\<close>

lemma mttm_relpow_tape_off_window:
  assumes "(c, c') \<in> mttm_step \<delta> ^^ n"
    and "p > mt_pos c k + n \<or> p + n < mt_pos c k"
  shows "mt_tape c' k p = mt_tape c k p"
  using assms
proof (induction n arbitrary: c')
  case 0
  thus ?case by simp
next
  case (Suc n)
  from Suc.prems(1) obtain c'' where
      ih: "(c, c'') \<in> mttm_step \<delta> ^^ n"
    and step: "(c'', c') \<in> mttm_step \<delta>"
    by (auto elim: relpow_Suc_E)
  have far: "p > mt_pos c k + n \<or> p + n < mt_pos c k"
    using Suc.prems(2) by linarith
  have eq_ih: "mt_tape c'' k p = mt_tape c k p"
    using Suc.IH[OF ih far] .
  have disp: "mt_pos c'' k \<le> mt_pos c k + n
              \<and> mt_pos c k \<le> mt_pos c'' k + n"
    using mttm_relpow_pos_displacement[OF ih] .
  have ne: "p \<noteq> mt_pos c'' k"
    using Suc.prems(2) disp by linarith
  have eq_step: "mt_tape c' k p = mt_tape c'' k p"
    using mttm_step_tape_off_head[OF step ne] .
  show ?case using eq_step eq_ih by simp
qed


subsection \<open>Left-endmarker pinning at position 0 along execution\<close>

text \<open>Local LE-pinning: any step of a valid M from a config whose
  tape \<open>k\<close> already has \<open>le_tm M\<close> at position 0 ends with a config
  whose tape \<open>k\<close> still has \<open>le_tm M\<close> at position 0.  Standalone
  variant of \<open>valid_step_mttm\<close>'s position-0-= LE conjunct,
  stripped of the \<open>valid_config_mttm\<close> precondition: only the
  per-tape LE-at-0 fact is needed (not Q-membership or \<open>\<Gamma>\<close>-typing).
  Case-split on whether the head is at position 0: at-head fires
  \<open>\<delta>LE\<close> (read LE forces write LE); off-head uses
  \<open>mttm_step_tape_off_head\<close> directly.\<close>

lemma mttm_step_LE_pos0_preserve:
  fixes M :: "('q, 'a) mttm"
  assumes vM:    "valid_mttm M"
    and step:    "(c, c') \<in> mttm_step (delta_tm M)"
    and LE_at0:  "mt_tape c k 0 = le_tm M"
  shows "mt_tape c' k 0 = le_tm M"
proof (cases "mt_pos c k = 0")
  case True
  from step obtain q ts n q' a dr where
      c_eq:  "c = Config\<^sub>M q ts n"
    and c'_eq: "c' = Config\<^sub>M q'
                       (\<lambda>kk. (ts kk)(n kk := a kk))
                       (\<lambda>kk. go_dir (dr kk) (n kk))"
    and tr:    "(q, \<lambda>kk. ts kk (n kk), q', a, dr) \<in> delta_tm M"
    by (auto elim: mttm_step.cases)
  have nk_0: "n k = 0" using True c_eq by simp
  have ts_k_0_le: "ts k 0 = le_tm M" using LE_at0 c_eq by simp
  have read_LE: "(\<lambda>kk. ts kk (n kk)) k = le_tm M"
    using ts_k_0_le nk_0 by simp
  have write_LE: "a k = le_tm M"
    using valid_mttm_deltaLE[OF vM tr read_LE] by simp
  have "mt_tape c' k 0 = ((ts k)(n k := a k)) 0"
    using c'_eq by simp
  also have "\<dots> = a k" using nk_0 by simp
  also have "\<dots> = le_tm M" using write_LE .
  finally show ?thesis .
next
  case False
  have ne_0: "(0 :: nat) \<noteq> mt_pos c k" using False by simp
  have unchanged: "mt_tape c' k 0 = mt_tape c k 0"
    using mttm_step_tape_off_head[OF step ne_0] .
  show ?thesis using unchanged LE_at0 by simp
qed

text \<open>\<open>n\<close>-step lift of @{thm[source] mttm_step_LE_pos0_preserve}: along
  any chain of M-steps, \<open>le_tm M\<close> at position 0 is preserved
  on every tape.  Used in AE's LE-edge forward stage to derive
  \<open>cM_k\<close>'s position-0 = LE without recourse to reachability
  from init.\<close>

lemma mttm_relpow_LE_pos0_preserve:
  fixes M :: "('q, 'a) mttm"
  assumes vM:    "valid_mttm M"
    and chain:   "(c, c') \<in> mttm_step (delta_tm M) ^^ n"
    and LE_at0:  "mt_tape c k 0 = le_tm M"
  shows "mt_tape c' k 0 = le_tm M"
  using chain
proof (induction n arbitrary: c')
  case 0
  thus ?case using LE_at0 by simp
next
  case (Suc n)
  from Suc.prems obtain c'' where
      ih: "(c, c'') \<in> mttm_step (delta_tm M) ^^ n"
    and step: "(c'', c') \<in> mttm_step (delta_tm M)"
    by (auto elim: relpow_Suc_E)
  have at_c'': "mt_tape c'' k 0 = le_tm M" using Suc.IH[OF ih] .
  show ?case
    using mttm_step_LE_pos0_preserve[OF vM step at_c''] .
qed


subsection \<open>Step structural decomposition\<close>

text \<open>Packages \<open>mttm_step.cases\<close> with the post-state position +
  tape equations on each tape: a single \<open>obtains\<close> rule that
  yields all four useful facts (pre-state's state, post-state's
  state, the per-tape position equation \<open>go_dir (dr k) (n k)\<close>,
  and the per-tape head-cell update).  Chain proofs in
  AE / AR / TR avoid re-doing the case-analysis at every
  per-substep position-trajectory step.\<close>

lemma mttm_step_obtain_action:
  assumes step: "(c, c') \<in> mttm_step \<delta>"
  obtains q q' a dr where
      "mt_state c = q"
    and "mt_state c' = q'"
    and "(q, \<lambda>k. mt_tape c k (mt_pos c k), q', a, dr) \<in> \<delta>"
    and "\<And>kk. mt_pos c' kk = go_dir (dr kk) (mt_pos c kk)"
    and "\<And>kk p. p \<noteq> mt_pos c kk
                  \<Longrightarrow> mt_tape c' kk p = mt_tape c kk p"
    and "\<And>kk. mt_tape c' kk (mt_pos c kk) = a kk"
proof -
  from step obtain q ts n q' a dr where
      c_eq:  "c = Config\<^sub>M q ts n"
    and c'_eq: "c' = Config\<^sub>M q'
                       (\<lambda>k. (ts k)(n k := a k))
                       (\<lambda>k. go_dir (dr k) (n k))"
    and tr: "(q, \<lambda>k. ts k (n k), q', a, dr) \<in> \<delta>"
    by (auto elim: mttm_step.cases)
  have st_c: "mt_state c = q" using c_eq by simp
  have st_c': "mt_state c' = q'" using c'_eq by simp
  have pos_c: "\<And>kk. mt_pos c kk = n kk" using c_eq by simp
  have pos_c': "\<And>kk. mt_pos c' kk = go_dir (dr kk) (n kk)"
    using c'_eq by simp
  have tape_c: "\<And>kk. mt_tape c kk = ts kk" using c_eq by simp
  have tape_c': "\<And>kk. mt_tape c' kk = (ts kk)(n kk := a kk)"
    using c'_eq by simp
  have tr': "(q, \<lambda>k. mt_tape c k (mt_pos c k), q', a, dr) \<in> \<delta>"
    using tr c_eq by simp
  show thesis
  proof (rule that[OF st_c st_c' tr'])
    fix kk show "mt_pos c' kk = go_dir (dr kk) (mt_pos c kk)"
      using pos_c' pos_c by simp
  next
    fix kk p assume "p \<noteq> mt_pos c kk"
    thus "mt_tape c' kk p = mt_tape c kk p"
      using tape_c' tape_c pos_c by simp
  next
    fix kk show "mt_tape c' kk (mt_pos c kk) = a kk"
      using tape_c' pos_c by simp
  qed
qed


subsection \<open>No-write deltas: tape preserved across a step\<close>

text \<open>For a transition relation in which every tuple's
  read-component equals its write-component, a single step
  preserves the entire tape function (the substrate update
  \<open>f(x := f x)\<close> is the identity).  Used by the alphabet-
  enlargement chain proof for the read-only buffer-loading
  substeps SS1\<open>\<rightarrow>\<close>SS2, SS2\<open>\<rightarrow>\<close>SS3, SS3\<open>\<rightarrow>\<close>SS4, SS4\<open>\<rightarrow>\<close>SS5.\<close>

lemma mttm_step_no_write_tape:
  assumes step: "(c, c') \<in> mttm_step \<delta>"
    and no_write: "\<And>q a q' a' d. (q, a, q', a', d) \<in> \<delta> \<Longrightarrow> a' = a"
  shows "mt_tape c' = mt_tape c"
proof -
  from step obtain q ts n q' a dr where
      c_eq:  "c = Config\<^sub>M q ts n"
    and c'_eq: "c' = Config\<^sub>M q'
                       (\<lambda>k. (ts k)(n k := a k))
                       (\<lambda>k. go_dir (dr k) (n k))"
    and tr: "(q, \<lambda>k. ts k (n k), q', a, dr) \<in> \<delta>"
    by (auto elim: mttm_step.cases)
  from no_write[OF tr] have "a = (\<lambda>k. ts k (n k))" by simp
  hence "(\<lambda>k. (ts k)(n k := a k)) = ts" by auto
  thus ?thesis by (simp add: c_eq c'_eq)
qed


subsection \<open>Step determinism and acceptance monotonicity\<close>

text \<open>Two general facts promoted from the finite-control layer: a step of
  a functional transition relation is deterministic (a configuration has at
  most one successor), and weak time-bounded acceptance is monotone in the
  time budget.\<close>

lemma mttm_step_functional:
  assumes fdet: "\<forall>q a p\<^sub>1 b\<^sub>1 d\<^sub>1 p\<^sub>2 b\<^sub>2 d\<^sub>2.
      (q, a, p\<^sub>1, b\<^sub>1, d\<^sub>1) \<in> \<delta> \<longrightarrow> (q, a, p\<^sub>2, b\<^sub>2, d\<^sub>2) \<in> \<delta>
        \<longrightarrow> (p\<^sub>1, b\<^sub>1, d\<^sub>1) = (p\<^sub>2, b\<^sub>2, d\<^sub>2)"
    and step1: "(c, c1) \<in> mttm_step \<delta>"
    and step2: "(c, c2) \<in> mttm_step \<delta>"
  shows "c1 = c2"
proof -
  from step1 obtain q ts n q1' a1 d1 where
      c_eq: "c = Config\<^sub>M q ts n"
    and c1_eq: "c1 = Config\<^sub>M q1' (\<lambda>k. (ts k)(n k := a1 k)) (\<lambda>k. go_dir (d1 k) (n k))"
    and tr1: "(q, \<lambda>k. ts k (n k), q1', a1, d1) \<in> \<delta>"
    by (auto elim: mttm_step.cases)
  from step2 obtain q2' a2 d2 where
      c2_eq: "c2 = Config\<^sub>M q2' (\<lambda>k. (ts k)(n k := a2 k)) (\<lambda>k. go_dir (d2 k) (n k))"
    and tr2: "(q, \<lambda>k. ts k (n k), q2', a2, d2) \<in> \<delta>"
    using c_eq by (auto elim: mttm_step.cases)
  have "(q1', a1, d1) = (q2', a2, d2)" using fdet tr1 tr2 by blast
  thus ?thesis using c1_eq c2_eq by simp
qed

text \<open>Weak time-bounded acceptance is monotone in the time budget.\<close>

lemma accepts_in_time_mttm_mono:
  "accepts_in_time_mttm M w t \<Longrightarrow> t \<le> t' \<Longrightarrow> accepts_in_time_mttm M w t'"
  unfolding accepts_in_time_mttm_def by (meson order_trans)

end
