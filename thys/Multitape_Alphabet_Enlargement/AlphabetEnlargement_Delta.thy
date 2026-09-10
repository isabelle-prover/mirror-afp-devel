theory AlphabetEnlargement_Delta
  imports AlphabetEnlargement_Substeps
begin

subsection \<open>Transition relation (union of per-substep parts)\<close>

text \<open>The output machine's tape alphabet \<open>\<Gamma>'\<close>: the set of
  \<open>'c\<close>-blocks whose every cell is in \<open>M\<close>'s
  tape alphabet \<open>\<Gamma>\<close>.\<close>

definition gamma_block ::
  "'a set \<Rightarrow> (('c :: enum) \<Rightarrow> 'a) set" where
  "gamma_block \<Gamma> = {f. range f \<subseteq> \<Gamma>}"

lemma gamma_block_mono: "A \<subseteq> B \<Longrightarrow> gamma_block A \<subseteq> gamma_block B"
  unfolding gamma_block_def by auto

lemma finite_gamma_block:
  fixes A :: "'a set"
  assumes finA: "finite A"
  shows "finite (gamma_block A :: ('c :: enum \<Rightarrow> 'a) set)"
proof -
  have eq: "gamma_block A = Pi\<^sub>E (UNIV :: 'c set) (\<lambda>_. A)"
    by (auto simp: gamma_block_def PiE_def Pi_def extensional_def)
  show ?thesis
    unfolding eq by (intro finite_PiE) (auto simp: finA)
qed

lemma LE_block_in_gamma_block:
  "le \<in> \<Gamma> \<Longrightarrow> LE_block le \<in> gamma_block \<Gamma>"
  unfolding gamma_block_def LE_block_def by auto

lemma bl_block_in_gamma_block:
  "bl \<in> \<Gamma> \<Longrightarrow> bl_block bl \<in> gamma_block \<Gamma>"
  unfolding gamma_block_def bl_block_def by auto

text \<open>State-level buffer validity: every per-tape block triple
  stored in the stage's buffer component has all three blocks in
  \<open>gamma_block \<Gamma>\<close>.  Spec-side counterpart to the config-level
  invariant \<open>ae_buffer_in_gamma_block\<close>; used as the
  buffer-component restriction in \<open>alphabet_enlarge\<close>'s output
  state set \<open>Q'\<close>.  This makes \<open>Q'\<close> finite from the
  set-level premise \<open>finite \<Gamma>\<close> alone — without requiring
  \<open>UNIV('c \<Rightarrow> 'a)\<close> to be a finite type, which would not be
  derivable from \<open>finite \<Gamma>\<close> generically.\<close>

definition ae_valid_stage ::
  "'a set \<Rightarrow> 'a \<Rightarrow> nat \<Rightarrow> ('a, 'c :: enum) ae_stage \<Rightarrow> bool" where
  "ae_valid_stage \<Gamma> le K stg \<longleftrightarrow>
     (case stg of (off, buf, dst, _) \<Rightarrow>
        (\<forall>k. fst (buf k) \<in> gamma_block \<Gamma>
            \<and> fst (snd (buf k)) \<in> gamma_block \<Gamma>
            \<and> snd (snd (buf k)) \<in> gamma_block \<Gamma>)
      \<and> (\<forall>j\<ge>K. off j = init_offset j)
      \<and> (\<forall>j\<ge>K. buf j = init_buffer le j)
      \<and> (\<forall>j\<ge>K. dst j = init_dest j))"

lemma ae_valid_stage_init:
  assumes "le \<in> \<Gamma>"
  shows "ae_valid_stage \<Gamma> le K (init_stage le)"
  unfolding ae_valid_stage_def init_stage_def init_buffer_def
  using LE_block_in_gamma_block[OF assms] by simp

lemma init_buffer_in_gamma_block:
  fixes le :: 'a and \<Gamma> :: "'a set"
    and ib :: "nat \<Rightarrow> ('c :: enum \<Rightarrow> 'a)
                                  \<times> ('c \<Rightarrow> 'a) \<times> ('c \<Rightarrow> 'a)"
  assumes le_in: "le \<in> \<Gamma>"
      and ib_def: "ib = init_buffer le"
  shows "\<forall>k. fst (ib k) \<in> gamma_block \<Gamma>
            \<and> fst (snd (ib k)) \<in> gamma_block \<Gamma>
            \<and> snd (snd (ib k)) \<in> gamma_block \<Gamma>"
  using LE_block_in_gamma_block[OF le_in]
  by (auto simp: ib_def init_buffer_def)

text \<open>Specialized variant for direct invocation at validation-phase
  call sites where the buffer is \<open>init_buffer (le_tm M)\<close>.  The
  buf-gamma claim is in the explicit shape that
  \<open>ae_step_val_*\<close>'s new \<open>buf_gamma\<close> hypothesis expects.
  Anchors the polymorphic \<open>'c\<close> via type annotations on every
  occurrence (cf. discussion in commit a812ed0).\<close>

lemma init_buffer_in_gamma_block_at_M:
  fixes M :: "('q, 'a) mttm"
  assumes vM: "valid_mttm M"
  shows "\<forall>kk :: nat.
            fst (init_buffer (le_tm M) kk
                   :: ('c :: enum \<Rightarrow> 'a) \<times> ('c \<Rightarrow> 'a) \<times> ('c \<Rightarrow> 'a))
              \<in> gamma_block (\<Gamma>_tm M)
            \<and> fst (snd (init_buffer (le_tm M) kk
                          :: ('c \<Rightarrow> 'a) \<times> ('c \<Rightarrow> 'a) \<times> ('c \<Rightarrow> 'a)))
              \<in> gamma_block (\<Gamma>_tm M)
            \<and> snd (snd (init_buffer (le_tm M) kk
                          :: ('c \<Rightarrow> 'a) \<times> ('c \<Rightarrow> 'a) \<times> ('c \<Rightarrow> 'a)))
              \<in> gamma_block (\<Gamma>_tm M)"
proof (intro allI)
  fix kk :: nat
  have lg: "(LE_block (le_tm M) :: 'c \<Rightarrow> 'a) \<in> gamma_block (\<Gamma>_tm M)"
    by (rule LE_block_in_gamma_block[OF valid_mttm_LE_in_Gamma[OF vM]])
  show "fst (init_buffer (le_tm M) kk
              :: ('c \<Rightarrow> 'a) \<times> ('c \<Rightarrow> 'a) \<times> ('c \<Rightarrow> 'a))
            \<in> gamma_block (\<Gamma>_tm M)
          \<and> fst (snd (init_buffer (le_tm M) kk
                        :: ('c \<Rightarrow> 'a) \<times> ('c \<Rightarrow> 'a) \<times> ('c \<Rightarrow> 'a)))
              \<in> gamma_block (\<Gamma>_tm M)
          \<and> snd (snd (init_buffer (le_tm M) kk
                        :: ('c \<Rightarrow> 'a) \<times> ('c \<Rightarrow> 'a) \<times> ('c \<Rightarrow> 'a)))
              \<in> gamma_block (\<Gamma>_tm M)"
    using lg by (simp add: init_buffer_def)
qed

lemma finite_ae_valid_stages:
  fixes \<Gamma> :: "'a set" and le :: 'a and K :: nat
  assumes finG: "finite \<Gamma>"
  shows "finite {stg :: ('a, 'c :: enum) ae_stage.
                  ae_valid_stage \<Gamma> le K stg}"
proof -
  let ?G  = "gamma_block \<Gamma> :: ('c \<Rightarrow> 'a) set"
  let ?GGG = "?G \<times> ?G \<times> ?G"
  have fG: "finite ?G" by (rule finite_gamma_block[OF finG])
  have fGGG: "finite ?GGG"
    using fG by (intro finite_cartesian_product)
  \<comment> \<open>Each \<open>nat\<close>-indexed field is finite via \<open>finite_tail_const_funcs\<close>:
      constant beyond \<open>K\<close> (the frozen-at-init tail), finite codomain.\<close>
  let ?offs = "{off :: nat \<Rightarrow> 'c.
                  (\<forall>j. off j \<in> (UNIV :: 'c set))
                  \<and> (\<forall>j\<ge>K. off j = init_offset j)}"
  let ?bufs = "{buf :: nat \<Rightarrow> ('c \<Rightarrow> 'a) \<times> ('c \<Rightarrow> 'a) \<times> ('c \<Rightarrow> 'a).
                  (\<forall>j. buf j \<in> ?GGG)
                  \<and> (\<forall>j\<ge>K. buf j = init_buffer le j)}"
  let ?dsts = "{dst :: nat \<Rightarrow> ae_dest.
                  (\<forall>j. dst j \<in> (UNIV :: ae_dest set))
                  \<and> (\<forall>j\<ge>K. dst j = init_dest j)}"
  have foffs: "finite ?offs"
    using finite_tail_const_funcs[OF finite_UNIV, of K "SOME x :: 'c. True"]
    by (simp add: init_offset_def)
  have fbufs: "finite ?bufs"
    using finite_tail_const_funcs[OF fGGG, of K "init_buffer le 0"]
    by (simp add: init_buffer_def)
  have fdsts: "finite ?dsts"
    using finite_tail_const_funcs[OF finite_UNIV, of K AE_Home]
    by (simp add: init_dest_def)
  let ?ENV = "?offs \<times> ?bufs \<times> ?dsts \<times> (UNIV :: substep_idx set)"
  have "{stg :: ('a, 'c) ae_stage. ae_valid_stage \<Gamma> le K stg} \<subseteq> ?ENV"
    unfolding ae_valid_stage_def
    by (auto simp: mem_Times_iff split: prod.splits)
  moreover have "finite ?ENV"
    using foffs fbufs fdsts by (intro finite_cartesian_product) simp_all
  ultimately show ?thesis by (rule finite_subset)
qed

text \<open>LE-input simp rules for the per-tape action helpers.  When
  the read block on tape \<open>k\<close> is the all-LE block, each
  helper's LE-guard prefix returns \<open>(LE_block le, N)\<close> (or
  \<open>(LE_block le, R)\<close> for SS6) regardless of the buffer triple's
  components.  These rules unblock the \<open>\<delta>LE\<close>-preservation case
  analysis: \<open>fun\<close>-generated simp rules match only literal
  triples \<open>(l, h, r)\<close>; named LE-input lemmas simplify the
  general application form via tuple destructuring.\<close>

lemma ae_ss5_action_LE [simp]:
  "ae_ss5_action le (LE_block le) buf ds = (LE_block le, dir.N)"
proof -
  obtain l h r where "buf = (l, h, r)" using prod.exhaust by metis
  thus ?thesis by simp
qed

lemma ae_ss6_action_LE [simp]:
  "ae_ss6_action le (LE_block le) buf ds = (LE_block le, dir.R)"
proof -
  obtain l h r where "buf = (l, h, r)" using prod.exhaust by metis
  thus ?thesis by simp
qed

lemma ae_ss7_action_LE [simp]:
  "ae_ss7_action le (LE_block le) buf ds = (LE_block le, dir.N)"
proof -
  obtain l h r where "buf = (l, h, r)" using prod.exhaust by metis
  thus ?thesis by simp
qed

lemma ae_ss8_action_LE [simp]:
  "ae_ss8_action le (LE_block le) buf ds = (LE_block le, dir.N)"
proof -
  obtain l h r where "buf = (l, h, r)" using prod.exhaust by metis
  thus ?thesis by simp
qed

text \<open>State preservation for a single buffered \<open>M\<close>-step: if the
  source state is in \<open>Q\<close>, so is the destination.  Direct
  consequence of the substrate's \<open>\<delta>_set\<close> range obligation.\<close>

lemma m_step_buffered_state_preservation:
  fixes M :: "('q, 'a) mttm"
  assumes valM: "valid_mttm M"
    and step: "((q, blocks, pos), (q', blocks', pos')) \<in> m_step_buffered M"
    and qQ: "q \<in> Q_tm M"
  shows "q' \<in> Q_tm M"
proof -
  from step obtain a a' d where
    "(q, a, q', a', d) \<in> delta_tm M"
    unfolding m_step_buffered_def by blast
  thus "q' \<in> Q_tm M"
    using valid_mttm_delta_set[OF valM] by auto
qed

text \<open>State preservation for the up-to-\<open>c\<close>-step composition: if the
  source state is in \<open>Q\<close>, so is the destination.  Induction on
  the relation power.\<close>

lemma m_steps_buffered_state_preservation:
  fixes M :: "('q, 'a) mttm"
  assumes valM: "valid_mttm M"
    and steps: "((q, blocks, pos), (q', blocks', pos')) \<in> m_steps_buffered M"
    and qQ: "q \<in> Q_tm M"
  shows "q' \<in> Q_tm M"
proof -
  from steps obtain n where
    n_step: "((q, blocks, pos), (q', blocks', pos')) \<in> (m_step_buffered M) ^^ n"
    unfolding m_steps_buffered_def by blast
  from n_step qQ show ?thesis
  proof (induction n arbitrary: q' blocks' pos')
    case 0
    then show ?case by auto
  next
    case (Suc n)
    from Suc.prems(1) obtain q'' blocks'' pos'' where
      step_n: "((q, blocks, pos), (q'', blocks'', pos''))
                  \<in> (m_step_buffered M) ^^ n"
      and step_one: "((q'', blocks'', pos''), (q', blocks', pos'))
                       \<in> m_step_buffered M"
      by (auto elim: relpow_Suc_E)
    from Suc.IH[OF step_n Suc.prems(2)] have qQ'': "q'' \<in> Q_tm M" .
    from m_step_buffered_state_preservation[OF valM step_one qQ''] show ?case .
  qed
qed

text \<open>Buffer-gamma preservation under a single \<open>m_step_buffered\<close>:
  if every slot of every tape's buffer is in \<open>gamma_block (\<Gamma>_tm M)\<close>
  pre-step, the post-step buffer's slots are too.  The substantive
  fact: \<open>m_step_buffered\<close>'s write updates exactly one cell of one
  slot per tape, the written value lies in \<open>\<Gamma>_tm M\<close> (by
  \<open>valid_mttm_delta\<close>), and \<open>gamma_block\<close> is closed under such
  point-updates.\<close>

lemma m_step_buffered_gamma_preserve:
  fixes M :: "('q, 'a) mttm"
  assumes vM: "valid_mttm M"
      and step: "((q, blocks, pos), (q', blocks', pos')) \<in> m_step_buffered M"
      and pre: "\<forall>k. fst (blocks k) \<in> gamma_block (\<Gamma>_tm M)
                    \<and> fst (snd (blocks k)) \<in> gamma_block (\<Gamma>_tm M)
                    \<and> snd (snd (blocks k)) \<in> gamma_block (\<Gamma>_tm M)"
    shows "\<forall>k. fst (blocks' k) \<in> gamma_block (\<Gamma>_tm M)
              \<and> fst (snd (blocks' k)) \<in> gamma_block (\<Gamma>_tm M)
              \<and> snd (snd (blocks' k)) \<in> gamma_block (\<Gamma>_tm M)"
proof -
  from step obtain a a' d where
      tr: "(q, a, q', a', d) \<in> delta_tm M"
      and bk_update: "\<forall>k. blocks' k = write_bp (blocks k) (pos k) (a' k)"
    unfolding m_step_buffered_def by auto
  show ?thesis
  proof (intro allI)
    fix k
    obtain l h r where bk_eq: "blocks k = (l, h, r)"
      by (cases "blocks k") auto
    obtain b off where pk_eq: "pos k = (b, off)"
      by (cases "pos k") auto
    from pre[rule_format, of k] bk_eq have
        l_in: "l \<in> gamma_block (\<Gamma>_tm M)" and
        h_in: "h \<in> gamma_block (\<Gamma>_tm M)" and
        r_in: "r \<in> gamma_block (\<Gamma>_tm M)"
      by auto
    from valid_mttm_delta(4)[OF vM tr, of k] have a'_in: "a' k \<in> \<Gamma>_tm M" .
    have l_upd: "l(off := a' k) \<in> gamma_block (\<Gamma>_tm M)"
      using l_in a'_in unfolding gamma_block_def by auto
    have h_upd: "h(off := a' k) \<in> gamma_block (\<Gamma>_tm M)"
      using h_in a'_in unfolding gamma_block_def by auto
    have r_upd: "r(off := a' k) \<in> gamma_block (\<Gamma>_tm M)"
      using r_in a'_in unfolding gamma_block_def by auto
    have bk'_eq: "blocks' k = write_bp (l, h, r) (b, off) (a' k)"
      using bk_update[rule_format, of k] bk_eq pk_eq by simp
    show "fst (blocks' k) \<in> gamma_block (\<Gamma>_tm M)
          \<and> fst (snd (blocks' k)) \<in> gamma_block (\<Gamma>_tm M)
          \<and> snd (snd (blocks' k)) \<in> gamma_block (\<Gamma>_tm M)"
      using bk'_eq l_in h_in r_in l_upd h_upd r_upd
      by (cases b) (auto simp: write_bp_def)
  qed
qed

text \<open>Buffer-gamma preservation under \<open>m_steps_buffered\<close> (the
  iterated up-to-c-step relation).  Induction on the relation
  power; the step case applies \<open>m_step_buffered_gamma_preserve\<close>.\<close>

lemma m_steps_buffered_gamma_preserve:
  fixes M :: "('q, 'a) mttm"
  assumes vM: "valid_mttm M"
      and steps: "((q, blocks, pos), (q', blocks', pos')) \<in> m_steps_buffered M"
      and pre: "\<forall>k. fst (blocks k) \<in> gamma_block (\<Gamma>_tm M)
                    \<and> fst (snd (blocks k)) \<in> gamma_block (\<Gamma>_tm M)
                    \<and> snd (snd (blocks k)) \<in> gamma_block (\<Gamma>_tm M)"
    shows "\<forall>k. fst (blocks' k) \<in> gamma_block (\<Gamma>_tm M)
              \<and> fst (snd (blocks' k)) \<in> gamma_block (\<Gamma>_tm M)
              \<and> snd (snd (blocks' k)) \<in> gamma_block (\<Gamma>_tm M)"
proof -
  from steps obtain n where
      n_step: "((q, blocks, pos), (q', blocks', pos'))
                  \<in> (m_step_buffered M) ^^ n"
    unfolding m_steps_buffered_def by blast
  from n_step pre show ?thesis
  proof (induction n arbitrary: q' blocks' pos')
    case 0
    then show ?case by auto
  next
    case (Suc n)
    from Suc.prems(1) obtain q'' blocks'' pos'' where
        step_n: "((q, blocks, pos), (q'', blocks'', pos''))
                    \<in> (m_step_buffered M) ^^ n"
        and step_one: "((q'', blocks'', pos''), (q', blocks', pos'))
                          \<in> m_step_buffered M"
      by (auto elim: relpow_Suc_E)
    from Suc.IH[OF step_n Suc.prems(2)] have IH:
        "\<forall>k. fst (blocks'' k) \<in> gamma_block (\<Gamma>_tm M)
            \<and> fst (snd (blocks'' k)) \<in> gamma_block (\<Gamma>_tm M)
            \<and> snd (snd (blocks'' k)) \<in> gamma_block (\<Gamma>_tm M)" .
    from m_step_buffered_gamma_preserve[OF vM step_one IH] show ?case .
  qed
qed

text \<open>Per-substep destination-stage-validity helpers.  Given that a
  tuple is in a particular substep delta, source-stage validity, and
  any auxiliary gamma-block facts (\<open>a\<close>'s gamma, \<open>bl_M\<close>/\<open>le_M\<close>
  in \<open>\<Gamma>_M\<close> as needed for SS2\<open>\<rightarrow>\<close>SS3 and SS8\<open>\<rightarrow>\<close>SS1
  halt branch, \<open>m_steps_buffered_gamma_preserve\<close> for SS4\<open>\<rightarrow>\<close>SS5),
  the destination stage is valid.  Companion to
  \<open>ae_step_alphabet_enlarge_buffer_gamma_preserve\<close> at the
  tuple level instead of the configuration level.  These are used by
  the \<open>_exists\<close> construction lemmas to discharge the
  \<open>Q'\<close>-filter conjunct that \<open>alphabet_enlarge_delta\<close>
  carries to enforce \<open>Q' = Q \<times> {stg. ae_valid_stage \<Gamma>_M stg}\<close>
  finiteness on a set-finite-\<open>\<Gamma>\<close> premise (instead of
  type-class-finite-\<open>'a\<close>).\<close>

lemma ae_delta_ss1_ss2_dest_valid:
  assumes rel: "(s, a, s', a', d) \<in> ae_delta_ss1_ss2 M"
      and a_gamma: "\<forall>k. a k \<in> gamma_block (\<Gamma>_tm M)"
      and src_valid: "ae_valid_stage (\<Gamma>_tm M) (le_tm M) (k_tm M) (snd s)"
  shows "ae_valid_stage (\<Gamma>_tm M) (le_tm M) (k_tm M) (snd s')"
proof -
  from rel obtain q ofs buf dest buf' where
      s_eq: "s = (q, ofs, buf, dest, SS1)"
      and s'_eq: "s' = (q, ofs, buf', dest, SS2)"
      and buf'_def: "buf' = (\<lambda>k. if k < k_tm M
                                  then (fst (buf k), a k, snd (snd (buf k)))
                                  else init_buffer (le_tm M) k)"
    unfolding ae_delta_ss1_ss2_def by auto
  from src_valid s_eq have
      src_g: "\<forall>k. fst (buf k) \<in> gamma_block (\<Gamma>_tm M)
                  \<and> fst (snd (buf k)) \<in> gamma_block (\<Gamma>_tm M)
                  \<and> snd (snd (buf k)) \<in> gamma_block (\<Gamma>_tm M)"
      and src_off: "\<forall>j\<ge>k_tm M. ofs j = init_offset j"
      and src_buf: "\<forall>j\<ge>k_tm M. buf j = init_buffer (le_tm M) j"
      and src_dst: "\<forall>j\<ge>k_tm M. dest j = init_dest j"
    by (simp_all add: ae_valid_stage_def)
  have buf'_g: "\<forall>k. fst (buf' k) \<in> gamma_block (\<Gamma>_tm M)
                    \<and> fst (snd (buf' k)) \<in> gamma_block (\<Gamma>_tm M)
                    \<and> snd (snd (buf' k)) \<in> gamma_block (\<Gamma>_tm M)"
  proof (intro allI)
    fix k
    show "fst (buf' k) \<in> gamma_block (\<Gamma>_tm M)
            \<and> fst (snd (buf' k)) \<in> gamma_block (\<Gamma>_tm M)
            \<and> snd (snd (buf' k)) \<in> gamma_block (\<Gamma>_tm M)"
    proof (cases "k < k_tm M")
      case True
      thus ?thesis using buf'_def src_g a_gamma by simp
    next
      case False
      hence le_k: "k_tm M \<le> k" by simp
      have "buf' k = init_buffer (le_tm M) k" using buf'_def False by simp
      moreover have "buf k = init_buffer (le_tm M) k"
        using src_buf[rule_format, OF le_k] .
      ultimately have "buf' k = buf k" by simp
      thus ?thesis using src_g by simp
    qed
  qed
  have buf'_tail: "\<forall>j\<ge>k_tm M. buf' j = init_buffer (le_tm M) j"
    using buf'_def by simp
  show ?thesis
    unfolding s'_eq ae_valid_stage_def
    using buf'_g src_off src_dst buf'_tail by simp
qed

lemma ae_delta_ss2_ss3_dest_valid:
  assumes vM: "valid_mttm M"
      and rel: "(s, a, s', a', d) \<in> ae_delta_ss2_ss3 M"
      and a_gamma: "\<forall>k. a k \<in> gamma_block (\<Gamma>_tm M)"
      and src_valid: "ae_valid_stage (\<Gamma>_tm M) (le_tm M) (k_tm M) (snd s)"
  shows "ae_valid_stage (\<Gamma>_tm M) (le_tm M) (k_tm M) (snd s')"
proof -
  from rel obtain q ofs buf dest buf' where
      s_eq: "s = (q, ofs, buf, dest, SS2)"
      and s'_eq: "s' = (q, ofs, buf', dest, SS3)"
      and buf'_def: "buf' = (\<lambda>k. if k < k_tm M
                                  then let (l, h, r) = buf k in
                                         (if h = LE_block (le_tm M)
                                            then bl_block (bl_tm M)
                                            else a k,
                                          h, r)
                                  else init_buffer (le_tm M) k)"
    unfolding ae_delta_ss2_ss3_def by auto
  from src_valid s_eq have
      src: "\<forall>k. fst (buf k) \<in> gamma_block (\<Gamma>_tm M)
                \<and> fst (snd (buf k)) \<in> gamma_block (\<Gamma>_tm M)
                \<and> snd (snd (buf k)) \<in> gamma_block (\<Gamma>_tm M)"
      and src_off: "\<forall>j\<ge>k_tm M. ofs j = init_offset j"
      and src_buf: "\<forall>j\<ge>k_tm M. buf j = init_buffer (le_tm M) j"
      and src_dst: "\<forall>j\<ge>k_tm M. dest j = init_dest j"
    by (simp_all add: ae_valid_stage_def)
  have bl_gam: "bl_block (bl_tm M) \<in> gamma_block (\<Gamma>_tm M)"
    using bl_block_in_gamma_block[OF valid_mttm_blank_in_Gamma[OF vM]] .
  have per_k: "\<forall>k. fst (buf' k) \<in> gamma_block (\<Gamma>_tm M)
                    \<and> fst (snd (buf' k)) \<in> gamma_block (\<Gamma>_tm M)
                    \<and> snd (snd (buf' k)) \<in> gamma_block (\<Gamma>_tm M)"
  proof
    fix k
    show "fst (buf' k) \<in> gamma_block (\<Gamma>_tm M)
            \<and> fst (snd (buf' k)) \<in> gamma_block (\<Gamma>_tm M)
            \<and> snd (snd (buf' k)) \<in> gamma_block (\<Gamma>_tm M)"
    proof (cases "k < k_tm M")
      case True
      obtain l h r where buf_eq: "buf k = (l, h, r)" using prod.exhaust by metis
      have lhr: "l \<in> gamma_block (\<Gamma>_tm M)
                 \<and> h \<in> gamma_block (\<Gamma>_tm M)
                 \<and> r \<in> gamma_block (\<Gamma>_tm M)"
        using src buf_eq by (metis fst_conv snd_conv)
      have buf'_k: "buf' k = (if h = LE_block (le_tm M)
                                then bl_block (bl_tm M)
                                else a k, h, r)"
        using buf'_def buf_eq True by simp
      show ?thesis using lhr a_gamma bl_gam buf'_k by auto
    next
      case False
      hence le_k: "k_tm M \<le> k" by simp
      have "buf' k = init_buffer (le_tm M) k" using buf'_def False by simp
      moreover have "buf k = init_buffer (le_tm M) k"
        using src_buf[rule_format, OF le_k] .
      ultimately have "buf' k = buf k" by simp
      thus ?thesis using src by simp
    qed
  qed
  have buf'_tail: "\<forall>j\<ge>k_tm M. buf' j = init_buffer (le_tm M) j"
    using buf'_def by simp
  show ?thesis
    unfolding s'_eq ae_valid_stage_def
    using per_k src_off src_dst buf'_tail by simp
qed

lemma ae_delta_ss3_ss4_dest_valid:
  assumes rel: "(s, a, s', a', d) \<in> ae_delta_ss3_ss4 M"
      and src_valid: "ae_valid_stage (\<Gamma>_tm M) (le_tm M) (k_tm M) (snd s)"
  shows "ae_valid_stage (\<Gamma>_tm M) (le_tm M) (k_tm M) (snd s')"
proof -
  from rel obtain q ofs buf dest where
      s_eq: "s = (q, ofs, buf, dest, SS3)"
      and s'_eq: "s' = (q, ofs, buf, dest, SS4)"
    unfolding ae_delta_ss3_ss4_def by auto
  show ?thesis
    using src_valid unfolding s_eq s'_eq ae_valid_stage_def by simp
qed

lemma ae_delta_ss4_ss5_dest_valid:
  assumes vM: "valid_mttm M"
      and rel: "(s, a, s', a', d) \<in> ae_delta_ss4_ss5 M"
      and a_gamma: "\<forall>k. a k \<in> gamma_block (\<Gamma>_tm M)"
      and src_valid: "ae_valid_stage (\<Gamma>_tm M) (le_tm M) (k_tm M) (snd s)"
  shows "ae_valid_stage (\<Gamma>_tm M) (le_tm M) (k_tm M) (snd s')"
proof -
  from rel obtain q ofs buf dest_old q' ofs' buf' dest' buf_full end_pos bufC where
      s_eq: "s = (q, ofs, buf, dest_old, SS4)"
      and s'_eq: "s' = (q', ofs', buf', dest', SS5)"
      and buf_full_def: "buf_full = (\<lambda>k. (fst (buf k),
                            if k < k_tm M then fst (snd (buf k)) else a k,
                            a k))"
      and mst: "((q, buf_full, \<lambda>k. (AE_Home, ofs k)),
                 (q', bufC, end_pos)) \<in> m_steps_buffered M"
      and ofs'_def: "ofs' = (\<lambda>k. if k < k_tm M then snd (end_pos k) else init_offset k)"
      and buf'_def: "buf' = (\<lambda>k. if k < k_tm M then bufC k else init_buffer (le_tm M) k)"
      and dest'_def: "dest' = (\<lambda>k. if k < k_tm M then fst (end_pos k) else init_dest k)"
    unfolding ae_delta_ss4_ss5_def by auto
  from src_valid s_eq have
      src: "\<forall>k. fst (buf k) \<in> gamma_block (\<Gamma>_tm M)
                \<and> fst (snd (buf k)) \<in> gamma_block (\<Gamma>_tm M)
                \<and> snd (snd (buf k)) \<in> gamma_block (\<Gamma>_tm M)"
      and src_buf: "\<forall>j\<ge>k_tm M. buf j = init_buffer (le_tm M) j"
    by (simp_all add: ae_valid_stage_def)
  have full: "\<forall>k. fst (buf_full k) \<in> gamma_block (\<Gamma>_tm M)
                  \<and> fst (snd (buf_full k)) \<in> gamma_block (\<Gamma>_tm M)
                  \<and> snd (snd (buf_full k)) \<in> gamma_block (\<Gamma>_tm M)"
    unfolding buf_full_def using src a_gamma by (auto split: if_splits)
  have bufC_gam: "\<forall>k. fst (bufC k) \<in> gamma_block (\<Gamma>_tm M)
                      \<and> fst (snd (bufC k)) \<in> gamma_block (\<Gamma>_tm M)
                      \<and> snd (snd (bufC k)) \<in> gamma_block (\<Gamma>_tm M)"
    by (rule m_steps_buffered_gamma_preserve[OF vM mst full])
  have buf'_gam: "\<forall>k. fst (buf' k) \<in> gamma_block (\<Gamma>_tm M)
                      \<and> fst (snd (buf' k)) \<in> gamma_block (\<Gamma>_tm M)
                      \<and> snd (snd (buf' k)) \<in> gamma_block (\<Gamma>_tm M)"
  proof (intro allI)
    fix k
    show "fst (buf' k) \<in> gamma_block (\<Gamma>_tm M)
            \<and> fst (snd (buf' k)) \<in> gamma_block (\<Gamma>_tm M)
            \<and> snd (snd (buf' k)) \<in> gamma_block (\<Gamma>_tm M)"
    proof (cases "k < k_tm M")
      case True
      thus ?thesis using bufC_gam by (simp add: buf'_def)
    next
      case False
      hence le_k: "k_tm M \<le> k" by simp
      have "buf' k = init_buffer (le_tm M) k" by (simp add: buf'_def False)
      also have "\<dots> = buf k" using src_buf[rule_format, OF le_k] by simp
      finally have "buf' k = buf k" .
      thus ?thesis using src by simp
    qed
  qed
  have ofs'_tail: "\<forall>j\<ge>k_tm M. ofs' j = init_offset j" by (simp add: ofs'_def)
  have buf'_tail: "\<forall>j\<ge>k_tm M. buf' j = init_buffer (le_tm M) j" by (simp add: buf'_def)
  have dest'_tail: "\<forall>j\<ge>k_tm M. dest' j = init_dest j" by (simp add: dest'_def)
  show ?thesis unfolding s'_eq ae_valid_stage_def
    using buf'_gam ofs'_tail buf'_tail dest'_tail by simp
qed

lemma ae_delta_ss5_ss6_dest_valid:
  assumes rel: "(s, a, s', a', d) \<in> ae_delta_ss5_ss6 M"
      and src_valid: "ae_valid_stage (\<Gamma>_tm M) (le_tm M) (k_tm M) (snd s)"
  shows "ae_valid_stage (\<Gamma>_tm M) (le_tm M) (k_tm M) (snd s')"
proof -
  from rel obtain q ofs buf dest where
      s_eq: "s = (q, ofs, buf, dest, SS5)"
      and s'_eq: "s' = (q, ofs, buf, dest, SS6)"
    unfolding ae_delta_ss5_ss6_def by auto
  show ?thesis
    using src_valid unfolding s_eq s'_eq ae_valid_stage_def by simp
qed

lemma ae_delta_ss6_ss7_dest_valid:
  assumes rel: "(s, a, s', a', d) \<in> ae_delta_ss6_ss7 M"
      and src_valid: "ae_valid_stage (\<Gamma>_tm M) (le_tm M) (k_tm M) (snd s)"
  shows "ae_valid_stage (\<Gamma>_tm M) (le_tm M) (k_tm M) (snd s')"
proof -
  from rel obtain q ofs buf dest where
      s_eq: "s = (q, ofs, buf, dest, SS6)"
      and s'_eq: "s' = (q, ofs, buf, dest, SS7)"
    unfolding ae_delta_ss6_ss7_def by auto
  show ?thesis
    using src_valid unfolding s_eq s'_eq ae_valid_stage_def by simp
qed

lemma ae_delta_ss7_ss8_dest_valid:
  assumes rel: "(s, a, s', a', d) \<in> ae_delta_ss7_ss8 M"
      and src_valid: "ae_valid_stage (\<Gamma>_tm M) (le_tm M) (k_tm M) (snd s)"
  shows "ae_valid_stage (\<Gamma>_tm M) (le_tm M) (k_tm M) (snd s')"
proof -
  from rel obtain q ofs buf dest where
      s_eq: "s = (q, ofs, buf, dest, SS7)"
      and s'_eq: "s' = (q, ofs, buf, dest, SS8)"
    unfolding ae_delta_ss7_ss8_def by auto
  show ?thesis
    using src_valid unfolding s_eq s'_eq ae_valid_stage_def by simp
qed

lemma ae_delta_ss8_ss1_dest_valid:
  assumes vM: "valid_mttm M"
      and rel: "(s, a, s', a', d) \<in> ae_delta_ss8_ss1 M"
      and src_valid: "ae_valid_stage (\<Gamma>_tm M) (le_tm M) (k_tm M) (snd s)"
  shows "ae_valid_stage (\<Gamma>_tm M) (le_tm M) (k_tm M) (snd s')"
proof -
  from rel obtain q ofs buf dest stage' where
      s_eq: "s = (q, ofs, buf, dest, SS8)"
      and s'_eq: "s' = (q, stage')"
      and stage'_def: "stage' = (if q \<in> {t_tm M, r_tm M}
                                   then init_stage (le_tm M)
                                   else (ofs, buf, init_dest, SS1))"
    unfolding ae_delta_ss8_ss1_def by auto
  from src_valid s_eq have
      buf_src: "\<forall>k. fst (buf k) \<in> gamma_block (\<Gamma>_tm M)
                    \<and> fst (snd (buf k)) \<in> gamma_block (\<Gamma>_tm M)
                    \<and> snd (snd (buf k)) \<in> gamma_block (\<Gamma>_tm M)"
      and src_off: "\<forall>j\<ge>k_tm M. ofs j = init_offset j"
      and src_buf: "\<forall>j\<ge>k_tm M. buf j = init_buffer (le_tm M) j"
    by (simp_all add: ae_valid_stage_def)
  show ?thesis
  proof (cases "q \<in> {t_tm M, r_tm M}")
    case True
    hence "stage' = init_stage (le_tm M)" using stage'_def by simp
    moreover have "ae_valid_stage (\<Gamma>_tm M) (le_tm M) (k_tm M) (init_stage (le_tm M))"
      using ae_valid_stage_init[OF valid_mttm_LE_in_Gamma[OF vM]] .
    ultimately show ?thesis unfolding s'_eq by simp
  next
    case False
    hence "stage' = (ofs, buf, init_dest, SS1)" using stage'_def by simp
    thus ?thesis unfolding s'_eq ae_valid_stage_def
      using buf_src src_off src_buf by simp
  qed
qed

text \<open>Validation-phase destination-stage-validity helpers.  All 8
  validation substeps preserve the buffer component, so the proofs
  are mechanical: extract the stage destructuring from the relation
  and propagate \<open>src_valid\<close>.\<close>

lemma ae_delta_val_fwd_advance_dest_valid:
  assumes rel: "(s, a, s', a', d) \<in> ae_delta_val_fwd_advance M"
      and src_valid: "ae_valid_stage (\<Gamma>_tm M) (le_tm M) (k_tm M) (snd s)"
  shows "ae_valid_stage (\<Gamma>_tm M) (le_tm M) (k_tm M) (snd s')"
proof -
  from rel obtain q ofs buf dest where
      s_eq: "s = (q, ofs, buf, dest, VFwd)"
      and s'_eq: "s' = (q, ofs, buf, dest, VFwd)"
    unfolding ae_delta_val_fwd_advance_def by auto
  show ?thesis using src_valid unfolding s_eq s'_eq by simp
qed

lemma ae_delta_val_fwd_to_padded_dest_valid:
  assumes rel: "(s, a, s', a', d) \<in> ae_delta_val_fwd_to_padded M"
      and src_valid: "ae_valid_stage (\<Gamma>_tm M) (le_tm M) (k_tm M) (snd s)"
  shows "ae_valid_stage (\<Gamma>_tm M) (le_tm M) (k_tm M) (snd s')"
proof -
  from rel obtain q ofs buf dest where
      s_eq: "s = (q, ofs, buf, dest, VFwd)"
      and s'_eq: "s' = (q, ofs, buf, dest, VFwdPad)"
    unfolding ae_delta_val_fwd_to_padded_def by auto
  show ?thesis
    using src_valid unfolding s_eq s'_eq ae_valid_stage_def by simp
qed

lemma ae_delta_val_fwd_reject_dest_valid:
  assumes vM: "valid_mttm M"
      and rel: "(s, a, s', a', d) \<in> ae_delta_val_fwd_reject M"
      and src_valid: "ae_valid_stage (\<Gamma>_tm M) (le_tm M) (k_tm M) (snd s)"
  shows "ae_valid_stage (\<Gamma>_tm M) (le_tm M) (k_tm M) (snd s')"
proof -
  from rel have s'_eq: "s' = (r_tm M, init_stage (le_tm M))"
    unfolding ae_delta_val_fwd_reject_def by auto
  have "ae_valid_stage (\<Gamma>_tm M) (le_tm M) (k_tm M) (init_stage (le_tm M))"
    using ae_valid_stage_init[OF valid_mttm_LE_in_Gamma[OF vM]] .
  thus ?thesis unfolding s'_eq by simp
qed

lemma ae_delta_val_fwd_to_ret_dest_valid:
  assumes rel: "(s, a, s', a', d) \<in> ae_delta_val_fwd_to_ret M"
      and src_valid: "ae_valid_stage (\<Gamma>_tm M) (le_tm M) (k_tm M) (snd s)"
  shows "ae_valid_stage (\<Gamma>_tm M) (le_tm M) (k_tm M) (snd s')"
proof -
  from rel obtain q ofs buf dest where
      s_eq: "s = (q, ofs, buf, dest, VFwd)"
      and s'_eq: "s' = (q, ofs, buf, dest, VRet)"
    unfolding ae_delta_val_fwd_to_ret_def by auto
  show ?thesis
    using src_valid unfolding s_eq s'_eq ae_valid_stage_def by simp
qed

lemma ae_delta_val_pad_to_ret_dest_valid:
  assumes rel: "(s, a, s', a', d) \<in> ae_delta_val_pad_to_ret M"
      and src_valid: "ae_valid_stage (\<Gamma>_tm M) (le_tm M) (k_tm M) (snd s)"
  shows "ae_valid_stage (\<Gamma>_tm M) (le_tm M) (k_tm M) (snd s')"
proof -
  from rel obtain q ofs buf dest where
      s_eq: "s = (q, ofs, buf, dest, VFwdPad)"
      and s'_eq: "s' = (q, ofs, buf, dest, VRet)"
    unfolding ae_delta_val_pad_to_ret_def by auto
  show ?thesis
    using src_valid unfolding s_eq s'_eq ae_valid_stage_def by simp
qed

lemma ae_delta_val_pad_reject_dest_valid:
  assumes vM: "valid_mttm M"
      and rel: "(s, a, s', a', d) \<in> ae_delta_val_pad_reject M"
      and src_valid: "ae_valid_stage (\<Gamma>_tm M) (le_tm M) (k_tm M) (snd s)"
  shows "ae_valid_stage (\<Gamma>_tm M) (le_tm M) (k_tm M) (snd s')"
proof -
  from rel have s'_eq: "s' = (r_tm M, init_stage (le_tm M))"
    unfolding ae_delta_val_pad_reject_def by auto
  have "ae_valid_stage (\<Gamma>_tm M) (le_tm M) (k_tm M) (init_stage (le_tm M))"
    using ae_valid_stage_init[OF valid_mttm_LE_in_Gamma[OF vM]] .
  thus ?thesis unfolding s'_eq by simp
qed

lemma ae_delta_val_ret_step_dest_valid:
  assumes rel: "(s, a, s', a', d) \<in> ae_delta_val_ret_step M"
      and src_valid: "ae_valid_stage (\<Gamma>_tm M) (le_tm M) (k_tm M) (snd s)"
  shows "ae_valid_stage (\<Gamma>_tm M) (le_tm M) (k_tm M) (snd s')"
proof -
  from rel obtain q ofs buf dest where
      s_eq: "s = (q, ofs, buf, dest, VRet)"
      and s'_eq: "s' = (q, ofs, buf, dest, VRet)"
    unfolding ae_delta_val_ret_step_def by auto
  show ?thesis using src_valid unfolding s_eq s'_eq by simp
qed

lemma ae_delta_val_ret_to_sim_dest_valid:
  assumes rel: "(s, a, s', a', d) \<in> ae_delta_val_ret_to_sim M"
      and src_valid: "ae_valid_stage (\<Gamma>_tm M) (le_tm M) (k_tm M) (snd s)"
  shows "ae_valid_stage (\<Gamma>_tm M) (le_tm M) (k_tm M) (snd s')"
proof -
  from rel obtain q ofs buf dest where
      s_eq: "s = (q, ofs, buf, dest, VRet)"
      and s'_eq: "s' = (q, ofs, buf, dest, SS1)"
    unfolding ae_delta_val_ret_to_sim_def by auto
  show ?thesis
    using src_valid unfolding s_eq s'_eq ae_valid_stage_def by simp
qed

text \<open>\<open>\<delta>'\<close> for the alphabet-enlargement combinator: the union of
  the 16 per-substep relations, intersected with two restrictions.

  First restriction: read / write blocks lie in
  \<open>\<Gamma>' = gamma_block (\<Gamma>_tm M)\<close>.  This makes \<open>\<delta>'\<close> satisfy
  the substrate's \<open>\<delta>_set\<close>-shape obligation.

  Second restriction (added 2026-05-09 alongside the substrate's
  \<open>\<delta>LE\<close>-no-write strengthening): a transition writes
  \<open>LE_block (le_tm M)\<close> on tape \<open>k\<close> only when reading the same.
  The substep relations for SS5\<open>\<rightarrow>\<close>SS8 produce write-back tuples
  whose \<open>a' k\<close> can in unreachable buffer states (left or right
  block holding \<open>LE_block (le_tm M)\<close>) equal \<open>LE_block (le_tm M)\<close>
  without the read \<open>a k\<close> matching; the intersection drops those
  tuples.  Since reachable buffer states do not put \<open>LE_block\<close>
  in left or right blocks (the LE block stays at M-position
  0, below the simulation phase's \<open>p_start \<ge> 1\<close> window), this is
  semantically inert in reachable executions and exists only to
  syntactically satisfy the substrate's universal
  \<open>\<delta>LE\<close>-no-write obligation.\<close>

definition alphabet_enlarge_delta ::
  "('q, 'a) mttm
    \<Rightarrow> (('q \<times> ('a, 'c :: enum) ae_stage)
        \<times> (nat \<Rightarrow> ('c \<Rightarrow> 'a))
        \<times> ('q \<times> ('a, 'c) ae_stage)
        \<times> (nat \<Rightarrow> ('c \<Rightarrow> 'a))
        \<times> (nat \<Rightarrow> dir)) set" where
  "alphabet_enlarge_delta M =
     (ae_delta_val_fwd_advance M
        \<union> ae_delta_val_fwd_to_padded M
        \<union> ae_delta_val_fwd_reject M
        \<union> ae_delta_val_fwd_to_ret M
        \<union> ae_delta_val_pad_to_ret M
        \<union> ae_delta_val_pad_reject M
        \<union> ae_delta_val_ret_step M
        \<union> ae_delta_val_ret_to_sim M
        \<union> ae_delta_ss1_ss2 M
        \<union> ae_delta_ss2_ss3 M
        \<union> ae_delta_ss3_ss4 M
        \<union> ae_delta_ss4_ss5 M
        \<union> ae_delta_ss5_ss6 M
        \<union> ae_delta_ss6_ss7 M
        \<union> ae_delta_ss7_ss8 M
        \<union> ae_delta_ss8_ss1 M)
     \<inter> {(s, a, s', a', d).
           (\<forall>k. a k \<in> gamma_block (\<Gamma>_tm M))
           \<and> (\<forall>k. a' k \<in> gamma_block (\<Gamma>_tm M))}
     \<inter> {(s, a, s', a', d).
           \<forall>k. a' k = LE_block (le_tm M) \<longrightarrow> a k = LE_block (le_tm M)}
     \<inter> {(s, a, s', a', d).
           ae_valid_stage (\<Gamma>_tm M) (le_tm M) (k_tm M) (snd s)
           \<and> ae_valid_stage (\<Gamma>_tm M) (le_tm M) (k_tm M) (snd s')}"

subsection \<open>Per-substep functionality (source determines target,
  except SS4\<open>\<rightarrow>\<close>SS5)\<close>

text \<open>For each of the 15 non-compute substep relations, the source
  configuration uniquely determines the target.  These functionality
  lemmas underpin the reverse-arm trace decoder: given an
  \<open>M'\<close>-step from a config with a known substep index, the
  target components are mechanically read off.\<close>

lemma ae_delta_val_fwd_advance_functional:
  assumes "(s, a, s1, a1, d1) \<in> ae_delta_val_fwd_advance M"
      and "(s, a, s2, a2, d2) \<in> ae_delta_val_fwd_advance M"
  shows "s1 = s2 \<and> a1 = a2 \<and> d1 = d2"
  using assms unfolding ae_delta_val_fwd_advance_def by auto

lemma ae_delta_val_fwd_to_padded_functional:
  assumes "(s, a, s1, a1, d1) \<in> ae_delta_val_fwd_to_padded M"
      and "(s, a, s2, a2, d2) \<in> ae_delta_val_fwd_to_padded M"
  shows "s1 = s2 \<and> a1 = a2 \<and> d1 = d2"
  using assms unfolding ae_delta_val_fwd_to_padded_def by auto

lemma ae_delta_val_fwd_reject_functional:
  assumes "(s, a, s1, a1, d1) \<in> ae_delta_val_fwd_reject M"
      and "(s, a, s2, a2, d2) \<in> ae_delta_val_fwd_reject M"
  shows "s1 = s2 \<and> a1 = a2 \<and> d1 = d2"
  using assms unfolding ae_delta_val_fwd_reject_def by auto

lemma ae_delta_val_fwd_to_ret_functional:
  assumes "(s, a, s1, a1, d1) \<in> ae_delta_val_fwd_to_ret M"
      and "(s, a, s2, a2, d2) \<in> ae_delta_val_fwd_to_ret M"
  shows "s1 = s2 \<and> a1 = a2 \<and> d1 = d2"
  using assms unfolding ae_delta_val_fwd_to_ret_def by auto

lemma ae_delta_val_pad_to_ret_functional:
  assumes "(s, a, s1, a1, d1) \<in> ae_delta_val_pad_to_ret M"
      and "(s, a, s2, a2, d2) \<in> ae_delta_val_pad_to_ret M"
  shows "s1 = s2 \<and> a1 = a2 \<and> d1 = d2"
  using assms unfolding ae_delta_val_pad_to_ret_def by auto

lemma ae_delta_val_pad_reject_functional:
  assumes "(s, a, s1, a1, d1) \<in> ae_delta_val_pad_reject M"
      and "(s, a, s2, a2, d2) \<in> ae_delta_val_pad_reject M"
  shows "s1 = s2 \<and> a1 = a2 \<and> d1 = d2"
  using assms unfolding ae_delta_val_pad_reject_def by auto

lemma ae_delta_val_ret_step_functional:
  assumes "(s, a, s1, a1, d1) \<in> ae_delta_val_ret_step M"
      and "(s, a, s2, a2, d2) \<in> ae_delta_val_ret_step M"
  shows "s1 = s2 \<and> a1 = a2 \<and> d1 = d2"
  using assms unfolding ae_delta_val_ret_step_def by auto

lemma ae_delta_val_ret_to_sim_functional:
  assumes "(s, a, s1, a1, d1) \<in> ae_delta_val_ret_to_sim M"
      and "(s, a, s2, a2, d2) \<in> ae_delta_val_ret_to_sim M"
  shows "s1 = s2 \<and> a1 = a2 \<and> d1 = d2"
  using assms unfolding ae_delta_val_ret_to_sim_def by auto

lemma ae_delta_ss1_ss2_functional:
  assumes "(s, a, s1, a1, d1) \<in> ae_delta_ss1_ss2 M"
      and "(s, a, s2, a2, d2) \<in> ae_delta_ss1_ss2 M"
  shows "s1 = s2 \<and> a1 = a2 \<and> d1 = d2"
  using assms unfolding ae_delta_ss1_ss2_def by auto

lemma ae_delta_ss2_ss3_functional:
  assumes "(s, a, s1, a1, d1) \<in> ae_delta_ss2_ss3 M"
      and "(s, a, s2, a2, d2) \<in> ae_delta_ss2_ss3 M"
  shows "s1 = s2 \<and> a1 = a2 \<and> d1 = d2"
  using assms unfolding ae_delta_ss2_ss3_def by auto

lemma ae_delta_ss3_ss4_functional:
  assumes "(s, a, s1, a1, d1) \<in> ae_delta_ss3_ss4 M"
      and "(s, a, s2, a2, d2) \<in> ae_delta_ss3_ss4 M"
  shows "s1 = s2 \<and> a1 = a2 \<and> d1 = d2"
  using assms unfolding ae_delta_ss3_ss4_def by auto

text \<open>SS4\<open>\<rightarrow>\<close>SS5 (compute substep) functionality under
  \<open>det_mttm M\<close>: the source determines the target uniquely.
  Unlike the other 15 substep functionality lemmas which follow
  from pure definitional unfolding, this one consumes M's
  determinism via \<open>m_steps_buffered_functional\<close> because
  SS4\<open>\<rightarrow>\<close>SS5 is precisely where M's \<open>\<delta>\<close> enters AE's
  \<open>\<delta>'\<close>.  Completes the 16th functionality entry; together
  with the 15 simpler entries, this discharges the per-substep
  functionality obligations of the reverse-arm chain-uniqueness
  argument.\<close>

lemma ae_delta_ss4_ss5_functional:
  fixes M :: "('q, 'a) mttm"
  assumes vM:  "valid_mttm M"
      and det: "det_mttm M"
      and h1: "(s, a, s1, a1, d1) \<in> ae_delta_ss4_ss5 M"
      and h2: "(s, a, s2, a2, d2) \<in> ae_delta_ss4_ss5 M"
  shows "s1 = s2 \<and> a1 = a2 \<and> d1 = d2"
proof -
  from h1 obtain q ofs buf dest_old q1' ofs1' buf1' dest1' buf_full1 end_pos1 bufC1
    where sd1: "s = (q, ofs, buf, dest_old, SS4)"
      and rs1: "s1 = (q1', ofs1', buf1', dest1', SS5)"
      and ad1: "a1 = a"
      and dd1: "d1 = (\<lambda>k. if k < k_tm M
                            then (if a k = LE_block (le_tm M) then dir.N else dir.L)
                            else dir.N)"
      and bf1: "buf_full1 = (\<lambda>k. (fst (buf k),
                                  if k < k_tm M then fst (snd (buf k)) else a k,
                                  a k))"
      and ms1: "((q, buf_full1, \<lambda>k. (AE_Home, ofs k)),
                 (q1', bufC1, end_pos1)) \<in> m_steps_buffered M"
      and of1: "ofs1' = (\<lambda>k. if k < k_tm M then snd (end_pos1 k) else init_offset k)"
      and bd1: "buf1' = (\<lambda>k. if k < k_tm M then bufC1 k else init_buffer (le_tm M) k)"
      and de1: "dest1' = (\<lambda>k. if k < k_tm M then fst (end_pos1 k) else init_dest k)"
    unfolding ae_delta_ss4_ss5_def by auto
  from h2 obtain q2 ofs2v buf2v dest_old2 q2' ofs2' buf2' dest2' buf_full2 end_pos2 bufC2
    where sd2: "s = (q2, ofs2v, buf2v, dest_old2, SS4)"
      and rs2: "s2 = (q2', ofs2', buf2', dest2', SS5)"
      and ad2: "a2 = a"
      and dd2: "d2 = (\<lambda>k. if k < k_tm M
                            then (if a k = LE_block (le_tm M) then dir.N else dir.L)
                            else dir.N)"
      and bf2: "buf_full2 = (\<lambda>k. (fst (buf2v k),
                                  if k < k_tm M then fst (snd (buf2v k)) else a k,
                                  a k))"
      and ms2: "((q2, buf_full2, \<lambda>k. (AE_Home, ofs2v k)),
                 (q2', bufC2, end_pos2)) \<in> m_steps_buffered M"
      and of2: "ofs2' = (\<lambda>k. if k < k_tm M then snd (end_pos2 k) else init_offset k)"
      and bd2: "buf2' = (\<lambda>k. if k < k_tm M then bufC2 k else init_buffer (le_tm M) k)"
      and de2: "dest2' = (\<lambda>k. if k < k_tm M then fst (end_pos2 k) else init_dest k)"
    unfolding ae_delta_ss4_ss5_def by auto

  \<comment> \<open>Source matches force the buffer / offset components to
      agree, and hence \<open>buf_full\<close> agrees.\<close>
  from sd1 sd2 have q2_eq: "q2 = q" and ofs2_eq: "ofs2v = ofs"
    and buf2_eq: "buf2v = buf" by simp_all
  have bf_eq: "buf_full2 = buf_full1"
    unfolding bf1 bf2 buf2_eq by (rule refl)

  \<comment> \<open>Apply \<open>m_steps_buffered_functional\<close>: with the
      compute-substep input identified across the two witnesses,
      determinism yields a unique \<open>(q', buf', end_pos)\<close>.\<close>
  have ms2': "((q, buf_full1, \<lambda>k. (AE_Home, ofs k)),
               (q2', bufC2, end_pos2)) \<in> m_steps_buffered M"
    using ms2 q2_eq ofs2_eq bf_eq by simp
  from m_steps_buffered_functional[OF vM det ms1 ms2']
  have target_eq: "(q1', bufC1, end_pos1) = (q2', bufC2, end_pos2)" .
  hence q'_eq: "q1' = q2'" and bufC_eq: "bufC1 = bufC2"
    and ep_eq: "end_pos1 = end_pos2" by auto

  show ?thesis
  proof (intro conjI)
    show "s1 = s2"
      using rs1 rs2 of1 of2 bd1 bd2 de1 de2 q'_eq bufC_eq ep_eq
      by (simp add: fun_eq_iff)
    show "a1 = a2" using ad1 ad2 by simp
    show "d1 = d2" using dd1 dd2 by simp
  qed
qed

lemma ae_delta_ss5_ss6_functional:
  assumes "(s, a, s1, a1, d1) \<in> ae_delta_ss5_ss6 M"
      and "(s, a, s2, a2, d2) \<in> ae_delta_ss5_ss6 M"
  shows "s1 = s2 \<and> a1 = a2 \<and> d1 = d2"
  using assms unfolding ae_delta_ss5_ss6_def by auto

lemma ae_delta_ss6_ss7_functional:
  assumes "(s, a, s1, a1, d1) \<in> ae_delta_ss6_ss7 M"
      and "(s, a, s2, a2, d2) \<in> ae_delta_ss6_ss7 M"
  shows "s1 = s2 \<and> a1 = a2 \<and> d1 = d2"
  using assms unfolding ae_delta_ss6_ss7_def by auto

lemma ae_delta_ss7_ss8_functional:
  assumes "(s, a, s1, a1, d1) \<in> ae_delta_ss7_ss8 M"
      and "(s, a, s2, a2, d2) \<in> ae_delta_ss7_ss8 M"
  shows "s1 = s2 \<and> a1 = a2 \<and> d1 = d2"
  using assms unfolding ae_delta_ss7_ss8_def by auto

lemma ae_delta_ss8_ss1_functional:
  assumes "(s, a, s1, a1, d1) \<in> ae_delta_ss8_ss1 M"
      and "(s, a, s2, a2, d2) \<in> ae_delta_ss8_ss1 M"
  shows "s1 = s2 \<and> a1 = a2 \<and> d1 = d2"
  using assms unfolding ae_delta_ss8_ss1_def by (auto split: if_split_asm)

text \<open>Within-phase exclusion: for each source substep index with
  multiple relations (VFwd: 4, VFwdPad: 2, VRet: 2), the relations
  do not overlap.  These lemmas commit the reverse-arm trace
  decoder to a specific branch.\<close>

lemma ae_delta_val_pad_to_ret_pad_reject_disjoint:
  assumes "(s, a, s1, a1, d1) \<in> ae_delta_val_pad_to_ret M"
      and "(s, a, s2, a2, d2) \<in> ae_delta_val_pad_reject M"
  shows "False"
  using assms unfolding ae_delta_val_pad_to_ret_def ae_delta_val_pad_reject_def
  by auto

lemma ae_delta_val_ret_step_ret_to_sim_disjoint:
  assumes "(s, a, s1, a1, d1) \<in> ae_delta_val_ret_step M"
      and "(s, a, s2, a2, d2) \<in> ae_delta_val_ret_to_sim M"
  shows "False"
  using assms unfolding ae_delta_val_ret_step_def ae_delta_val_ret_to_sim_def
  by auto

text \<open>Cross-phase exclusion: a tuple in \<open>alphabet_enlarge_delta M\<close>
  whose source state has substep index \<open>SSn\<close> lies in the
  matching \<open>ae_delta_ssn_ssm M\<close> (and not in any other relation
  of the union).  Each of the 16 union components pins its source
  substep index to a specific value; the 15 other relations have
  source substep indices in
  \<open>{VFwd, VFwdPad, VRet, SS1, \<dots>, SS8} \<setminus> {SSn}\<close>, hence
  cannot match.  The alphabet intersection clauses are preserved
  through the conclusion (membership in
  \<open>ae_delta_ssn_ssm M\<close> does not require them, so we discard
  them).  Used by the reverse-arm trace decoder to commit each
  peeled \<open>\<delta>'\<close>-step to its canonical substep.\<close>

lemma ae_delta_ss1_only:
  fixes M :: "('q, 'a) mttm"
  assumes "(s, a, s', a', d) \<in> alphabet_enlarge_delta M"
      and "snd (snd (snd (snd s))) = SS1"
    shows "(s, a, s', a', d) \<in> ae_delta_ss1_ss2 M"
  using assms
  unfolding alphabet_enlarge_delta_def
            ae_delta_val_fwd_advance_def
            ae_delta_val_fwd_to_padded_def
            ae_delta_val_fwd_reject_def
            ae_delta_val_fwd_to_ret_def
            ae_delta_val_pad_to_ret_def
            ae_delta_val_pad_reject_def
            ae_delta_val_ret_step_def
            ae_delta_val_ret_to_sim_def
            ae_delta_ss2_ss3_def
            ae_delta_ss3_ss4_def
            ae_delta_ss4_ss5_def
            ae_delta_ss5_ss6_def
            ae_delta_ss6_ss7_def
            ae_delta_ss7_ss8_def
            ae_delta_ss8_ss1_def
  by auto

lemma ae_delta_ss2_only:
  fixes M :: "('q, 'a) mttm"
  assumes "(s, a, s', a', d) \<in> alphabet_enlarge_delta M"
      and "snd (snd (snd (snd s))) = SS2"
    shows "(s, a, s', a', d) \<in> ae_delta_ss2_ss3 M"
  using assms
  unfolding alphabet_enlarge_delta_def
            ae_delta_val_fwd_advance_def
            ae_delta_val_fwd_to_padded_def
            ae_delta_val_fwd_reject_def
            ae_delta_val_fwd_to_ret_def
            ae_delta_val_pad_to_ret_def
            ae_delta_val_pad_reject_def
            ae_delta_val_ret_step_def
            ae_delta_val_ret_to_sim_def
            ae_delta_ss1_ss2_def
            ae_delta_ss3_ss4_def
            ae_delta_ss4_ss5_def
            ae_delta_ss5_ss6_def
            ae_delta_ss6_ss7_def
            ae_delta_ss7_ss8_def
            ae_delta_ss8_ss1_def
  by auto

lemma ae_delta_ss3_only:
  fixes M :: "('q, 'a) mttm"
  assumes "(s, a, s', a', d) \<in> alphabet_enlarge_delta M"
      and "snd (snd (snd (snd s))) = SS3"
    shows "(s, a, s', a', d) \<in> ae_delta_ss3_ss4 M"
  using assms
  unfolding alphabet_enlarge_delta_def
            ae_delta_val_fwd_advance_def
            ae_delta_val_fwd_to_padded_def
            ae_delta_val_fwd_reject_def
            ae_delta_val_fwd_to_ret_def
            ae_delta_val_pad_to_ret_def
            ae_delta_val_pad_reject_def
            ae_delta_val_ret_step_def
            ae_delta_val_ret_to_sim_def
            ae_delta_ss1_ss2_def
            ae_delta_ss2_ss3_def
            ae_delta_ss4_ss5_def
            ae_delta_ss5_ss6_def
            ae_delta_ss6_ss7_def
            ae_delta_ss7_ss8_def
            ae_delta_ss8_ss1_def
  by auto

lemma ae_delta_ss4_only:
  fixes M :: "('q, 'a) mttm"
  assumes "(s, a, s', a', d) \<in> alphabet_enlarge_delta M"
      and "snd (snd (snd (snd s))) = SS4"
    shows "(s, a, s', a', d) \<in> ae_delta_ss4_ss5 M"
  using assms
  unfolding alphabet_enlarge_delta_def
            ae_delta_val_fwd_advance_def
            ae_delta_val_fwd_to_padded_def
            ae_delta_val_fwd_reject_def
            ae_delta_val_fwd_to_ret_def
            ae_delta_val_pad_to_ret_def
            ae_delta_val_pad_reject_def
            ae_delta_val_ret_step_def
            ae_delta_val_ret_to_sim_def
            ae_delta_ss1_ss2_def
            ae_delta_ss2_ss3_def
            ae_delta_ss3_ss4_def
            ae_delta_ss5_ss6_def
            ae_delta_ss6_ss7_def
            ae_delta_ss7_ss8_def
            ae_delta_ss8_ss1_def
  by auto

lemma ae_delta_ss5_only:
  fixes M :: "('q, 'a) mttm"
  assumes "(s, a, s', a', d) \<in> alphabet_enlarge_delta M"
      and "snd (snd (snd (snd s))) = SS5"
    shows "(s, a, s', a', d) \<in> ae_delta_ss5_ss6 M"
  using assms
  unfolding alphabet_enlarge_delta_def
            ae_delta_val_fwd_advance_def
            ae_delta_val_fwd_to_padded_def
            ae_delta_val_fwd_reject_def
            ae_delta_val_fwd_to_ret_def
            ae_delta_val_pad_to_ret_def
            ae_delta_val_pad_reject_def
            ae_delta_val_ret_step_def
            ae_delta_val_ret_to_sim_def
            ae_delta_ss1_ss2_def
            ae_delta_ss2_ss3_def
            ae_delta_ss3_ss4_def
            ae_delta_ss4_ss5_def
            ae_delta_ss6_ss7_def
            ae_delta_ss7_ss8_def
            ae_delta_ss8_ss1_def
  by auto

lemma ae_delta_ss6_only:
  fixes M :: "('q, 'a) mttm"
  assumes "(s, a, s', a', d) \<in> alphabet_enlarge_delta M"
      and "snd (snd (snd (snd s))) = SS6"
    shows "(s, a, s', a', d) \<in> ae_delta_ss6_ss7 M"
  using assms
  unfolding alphabet_enlarge_delta_def
            ae_delta_val_fwd_advance_def
            ae_delta_val_fwd_to_padded_def
            ae_delta_val_fwd_reject_def
            ae_delta_val_fwd_to_ret_def
            ae_delta_val_pad_to_ret_def
            ae_delta_val_pad_reject_def
            ae_delta_val_ret_step_def
            ae_delta_val_ret_to_sim_def
            ae_delta_ss1_ss2_def
            ae_delta_ss2_ss3_def
            ae_delta_ss3_ss4_def
            ae_delta_ss4_ss5_def
            ae_delta_ss5_ss6_def
            ae_delta_ss7_ss8_def
            ae_delta_ss8_ss1_def
  by auto

lemma ae_delta_ss7_only:
  fixes M :: "('q, 'a) mttm"
  assumes "(s, a, s', a', d) \<in> alphabet_enlarge_delta M"
      and "snd (snd (snd (snd s))) = SS7"
    shows "(s, a, s', a', d) \<in> ae_delta_ss7_ss8 M"
  using assms
  unfolding alphabet_enlarge_delta_def
            ae_delta_val_fwd_advance_def
            ae_delta_val_fwd_to_padded_def
            ae_delta_val_fwd_reject_def
            ae_delta_val_fwd_to_ret_def
            ae_delta_val_pad_to_ret_def
            ae_delta_val_pad_reject_def
            ae_delta_val_ret_step_def
            ae_delta_val_ret_to_sim_def
            ae_delta_ss1_ss2_def
            ae_delta_ss2_ss3_def
            ae_delta_ss3_ss4_def
            ae_delta_ss4_ss5_def
            ae_delta_ss5_ss6_def
            ae_delta_ss6_ss7_def
            ae_delta_ss8_ss1_def
  by auto

lemma ae_delta_ss8_only:
  fixes M :: "('q, 'a) mttm"
  assumes "(s, a, s', a', d) \<in> alphabet_enlarge_delta M"
      and "snd (snd (snd (snd s))) = SS8"
    shows "(s, a, s', a', d) \<in> ae_delta_ss8_ss1 M"
  using assms
  unfolding alphabet_enlarge_delta_def
            ae_delta_val_fwd_advance_def
            ae_delta_val_fwd_to_padded_def
            ae_delta_val_fwd_reject_def
            ae_delta_val_fwd_to_ret_def
            ae_delta_val_pad_to_ret_def
            ae_delta_val_pad_reject_def
            ae_delta_val_ret_step_def
            ae_delta_val_ret_to_sim_def
            ae_delta_ss1_ss2_def
            ae_delta_ss2_ss3_def
            ae_delta_ss3_ss4_def
            ae_delta_ss4_ss5_def
            ae_delta_ss5_ss6_def
            ae_delta_ss6_ss7_def
            ae_delta_ss7_ss8_def
  by auto

end
