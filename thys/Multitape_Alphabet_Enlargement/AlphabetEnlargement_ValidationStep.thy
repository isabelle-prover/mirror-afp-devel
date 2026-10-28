theory AlphabetEnlargement_ValidationStep
  imports AlphabetEnlargement_Codec
begin

subsection \<open>Validation step machinery and initial config\<close>

subsubsection \<open>Validation canonicity equivalence with encoder image\<close>

text \<open>If a block is in \<open>gamma_block (Sigma_M \<union> {bl_M})\<close>,
  then the decoder's per-block output stays in \<open>Sigma_M\<close>: the
  takeWhile-prefix strips off any \<open>bl_M\<close>-symbols, leaving only
  \<open>Sigma_M\<close> elements.  Per-block contribution to the
  set-containment side of the iff lemma's forward direction.\<close>

lemma ae_decode_block_subset:
  fixes c :: "'c :: enum \<Rightarrow> 'a"
    and Sigma :: "'a set"
    and bl :: 'a
  assumes "c \<in> gamma_block (Sigma \<union> {bl})"
  shows "set (ae_decode_block bl c) \<subseteq> Sigma"
proof
  fix a assume a_in: "a \<in> set (ae_decode_block bl c)"
  let ?xs = "map c (enum_class.enum :: 'c list)"
  have a_in_tW: "a \<in> set (takeWhile (\<lambda>a. a \<noteq> bl) ?xs)"
    using a_in by (simp add: ae_decode_block_def)
  have neq_bl: "\<And>ys :: 'a list. \<forall>x \<in> set (takeWhile (\<lambda>a. a \<noteq> bl) ys).
                                    x \<noteq> bl"
  proof -
    fix ys :: "'a list"
    show "\<forall>x \<in> set (takeWhile (\<lambda>a. a \<noteq> bl) ys). x \<noteq> bl"
      by (induct ys) (auto split: if_split_asm)
  qed
  have a_neq_bl: "a \<noteq> bl" using a_in_tW neq_bl by blast
  have a_in_xs: "a \<in> set ?xs" using a_in_tW set_takeWhileD by metis
  obtain x where a_eq: "a = c x" using a_in_xs by auto
  have c_x_in: "c x \<in> Sigma \<union> {bl}"
    using assms unfolding gamma_block_def by auto
  show "a \<in> Sigma" using a_eq a_neq_bl c_x_in by blast
qed

text \<open>Validation lemmas — structural induction over the input.
  These do not require simulation infrastructure.\<close>

text \<open>The following biconditional characterises the AE machine's
  set of well-formed inputs: a string is
  \<open>ae_input_well_formed\<close> if and only if it is the encoder
  image of some base-alphabet input.  The headline language
  theorems \<open>alphabet_enlarge_language\<close> and
  \<open>alphabet_enlarge_language_forward\<close> are quantified only
  over explicit encoder-image inputs (\<open>set w \<subseteq> Sigma_ktm M\<close>,
  with the AE-side string given as
  \<open>encode_input (bl_ktm M) w\<close>), so they need only the
  forward direction, \<open>encode_input_well_formed\<close> of theory
  \<open>AlphabetEnlargement_Codec\<close>; they never appeal to this
  biconditional's reverse direction (every well-formed AE-input
  has a preimage under the encoder).  The biconditional is
  retained as a structural completeness result identifying
  exactly what the AE machine accepts as a legitimate input, and
  is potentially useful for the nondeterministic-reverse
  research thread, where extracting an encoder preimage from an
  AE-validation hypothesis is one of the load-bearing steps.\<close>

lemma ae_validation_canonical_iff_encoder_image:
  fixes M :: "('q, 'a) ktm"
    and w :: "('c :: enum \<Rightarrow> 'a) list"
  assumes vM: "valid_ktm M"
      and w_sub: "set w \<subseteq> gamma_block (Sigma_ktm M \<union> {bl_ktm M})"
  shows "ae_input_well_formed (bl_ktm M) w
         \<longleftrightarrow> (\<exists>u. set u \<subseteq> Sigma_ktm M
                  \<and> w = encode_input (bl_ktm M) u)"
proof
  assume wf: "ae_input_well_formed (bl_ktm M) w"
  let ?u = "ae_decode_input (bl_ktm M) w"
  have round_trip: "encode_input (bl_ktm M) ?u = w"
    using encode_decode_round_trip[OF wf] .
  have u_sub: "set ?u \<subseteq> Sigma_ktm M"
  proof
    fix a assume "a \<in> set ?u"
    hence "a \<in> set (concat (map (ae_decode_block (bl_ktm M)) w))"
      by (simp add: ae_decode_input_def)
    then obtain c where c_in: "c \<in> set w"
                    and a_in_blk: "a \<in> set (ae_decode_block (bl_ktm M) c)"
      by auto
    have c_in_gamma: "c \<in> gamma_block (Sigma_ktm M \<union> {bl_ktm M})"
      using c_in w_sub by blast
    have "set (ae_decode_block (bl_ktm M) c) \<subseteq> Sigma_ktm M"
      by (rule ae_decode_block_subset[OF c_in_gamma])
    thus "a \<in> Sigma_ktm M" using a_in_blk by blast
  qed
  show "\<exists>u. set u \<subseteq> Sigma_ktm M
              \<and> w = encode_input (bl_ktm M) u"
    using u_sub round_trip[symmetric] by blast
next
  assume "\<exists>u. set u \<subseteq> Sigma_ktm M
              \<and> w = encode_input (bl_ktm M) u"
  then obtain u where
    u_sub: "set u \<subseteq> Sigma_ktm M" and
    w_eq: "w = encode_input (bl_ktm M) u" by blast
  have "ae_input_well_formed (bl_ktm M)
            (encode_input (bl_ktm M) u :: ('c \<Rightarrow> 'a) list)"
    using encode_input_well_formed[OF vM u_sub] .
  thus "ae_input_well_formed (bl_ktm M) w" using w_eq by simp
qed

subsubsection \<open>Validation step helpers\<close>

text \<open>Step-helper library for the validation phase.  Each
  helper packages one validation substep relation as an
  \<open>ktm_step\<close>-constructor: given source-state and
  read-tape constraints satisfying the relation's source pattern,
  produce a single \<open>ktm_step (alphabet_enlarge_delta M)\<close>.
  Used by the three remaining commit-B lemmas
  (\<open>ae_validation_steps_bound\<close>,
  \<open>ae_validation_post_state_canonical\<close>,
  \<open>ae_validation_post_state_noncanonical\<close>) to assemble
  validation-phase chains by composition rather than re-deriving
  each step.\<close>

lemma ae_step_make:
  fixes M :: "('q, 'a) ktm"
    and ts :: "nat \<Rightarrow> nat \<Rightarrow> ('c :: enum \<Rightarrow> 'a)"
    and n :: "nat \<Rightarrow> nat"
    and s s' :: "'q \<times> ('a, 'c) ae_stage"
    and a' :: "nat \<Rightarrow> ('c \<Rightarrow> 'a)"
    and d :: "nat \<Rightarrow> move"
  assumes rel: "(s, (\<lambda>k. ts k (n k)), s', a', d)
                  \<in> alphabet_enlarge_delta M"
  shows "(KConfig s ts n,
            KConfig s' (\<lambda>k. (ts k)(n k := a' k))
              (\<lambda>k. go_move (d k) (n k)))
           \<in> ktm_step (alphabet_enlarge_delta M)"
proof (rule ktm_step.intros)
  show "(s, (\<lambda>k. ts k (n k)), s', a', d)
          \<in> alphabet_enlarge_delta M" by (rule rel)
qed

text \<open>Reflexive frozen-tail for the initial stage.  The stage
  fields \<open>init_offset\<close> / \<open>init_buffer le\<close> / \<open>init_dest\<close> agree with
  themselves beyond any tape count \<open>K\<close>, so this discharges the
  \<open>stage_tail\<close> premise of every validation step-helper at the call
  sites, where the stage is literally \<open>init_stage (le_ktm M)\<close> (the
  validation phases never touch the buffer).\<close>

lemma init_stage_tail:
  "(\<forall>j\<ge>K. init_offset j = init_offset j)
   \<and> (\<forall>j\<ge>K. init_buffer le j = init_buffer le j)
   \<and> (\<forall>j\<ge>K. init_dest j = init_dest j)"
  by simp

text \<open>VFwd advance: read \<open>LE_block\<close> or a pure block on
  tape 0; head moves R on tape 0, N elsewhere; phase stays VFwd;
  no write change.\<close>

lemma ae_step_val_fwd_advance:
  fixes M :: "('q, 'a) ktm"
    and ts :: "nat \<Rightarrow> nat \<Rightarrow> ('c :: enum \<Rightarrow> 'a)"
    and n :: "nat \<Rightarrow> nat"
    and q :: 'q
    and ofs :: "nat \<Rightarrow> 'c"
    and buf :: "nat \<Rightarrow> ('c \<Rightarrow> 'a) \<times> ('c \<Rightarrow> 'a) \<times> ('c \<Rightarrow> 'a)"
    and dest :: "nat \<Rightarrow> ae_dest"
  assumes q_in: "q \<in> Q_ktm M"
      and q_neq_t: "q \<noteq> t_ktm M"
      and q_neq_r: "q \<noteq> r_ktm M"
      and read: "ts (0 :: nat) (n 0) = LE_block (le_ktm M)
                  \<or> is_pure_block (bl_ktm M) (ts 0 (n 0))"
      and bt: "\<forall>j\<ge>k_ktm M. \<forall>i. ts j i = bl_block (bl_ktm M)"
      and stage_tail: "(\<forall>j\<ge>k_ktm M. ofs j = init_offset j)
                        \<and> (\<forall>j\<ge>k_ktm M. buf j = init_buffer (le_ktm M) j)
                        \<and> (\<forall>j\<ge>k_ktm M. dest j = init_dest j)"
      and gamma: "\<forall>k. ts k (n k) \<in> gamma_block (\<Gamma>_ktm M)"
      and buf_gamma: "\<forall>k. fst (buf k) \<in> gamma_block (\<Gamma>_ktm M)
                            \<and> fst (snd (buf k)) \<in> gamma_block (\<Gamma>_ktm M)
                            \<and> snd (snd (buf k)) \<in> gamma_block (\<Gamma>_ktm M)"
  shows "(KConfig (q, ofs, buf, dest, VFwd) ts n,
            KConfig (q, ofs, buf, dest, VFwd) ts
              (\<lambda>k. go_move (if k = 0 then MoveR else MoveN) (n k)))
           \<in> ktm_step (alphabet_enlarge_delta M)"
proof -
  let ?d = "\<lambda>k :: nat. if k = 0 then MoveR else MoveN"
  let ?a = "\<lambda>k. ts k (n k)"
  have rel_in: "((q, ofs, buf, dest, VFwd), ?a,
                  (q, ofs, buf, dest, VFwd), ?a, ?d)
                  \<in> ae_delta_val_fwd_advance M"
    unfolding ae_delta_val_fwd_advance_def
    using q_in q_neq_t q_neq_r read bt by auto
  have src_valid: "ae_valid_stage (\<Gamma>_ktm M) (le_ktm M) (k_ktm M)
                      (snd ((q, ofs, buf, dest, VFwd)
                              :: 'q \<times> ('a, 'c) ae_stage))"
    using buf_gamma stage_tail unfolding ae_valid_stage_def by simp
  have aed_in: "((q, ofs, buf, dest, VFwd), ?a,
                  (q, ofs, buf, dest, VFwd), ?a, ?d)
                  \<in> alphabet_enlarge_delta M"
    unfolding alphabet_enlarge_delta_def
    using rel_in gamma src_valid by auto
  have ts_unchanged: "(\<lambda>k. (ts k)(n k := ?a k)) = ts"
    by (rule ext) auto
  have step: "(KConfig (q, ofs, buf, dest, VFwd) ts n,
                KConfig (q, ofs, buf, dest, VFwd)
                  (\<lambda>k. (ts k)(n k := ?a k))
                  (\<lambda>k. go_move (?d k) (n k)))
                \<in> ktm_step (alphabet_enlarge_delta M)"
  proof (rule ae_step_make)
    show "((q, ofs, buf, dest, VFwd), ?a,
            (q, ofs, buf, dest, VFwd), ?a, ?d)
              \<in> alphabet_enlarge_delta M" by (rule aed_in)
  qed
  show ?thesis using step ts_unchanged by simp
qed

text \<open>VFwd \<open>\<rightarrow>\<close> VFwdPad: read a padded block on
  tape 0; head moves R on tape 0, N elsewhere; phase becomes
  VFwdPad; no write change.\<close>

lemma ae_step_val_fwd_to_padded:
  fixes M :: "('q, 'a) ktm"
    and ts :: "nat \<Rightarrow> nat \<Rightarrow> ('c :: enum \<Rightarrow> 'a)"
    and n :: "nat \<Rightarrow> nat"
    and q :: 'q
    and ofs :: "nat \<Rightarrow> 'c"
    and buf :: "nat \<Rightarrow> ('c \<Rightarrow> 'a) \<times> ('c \<Rightarrow> 'a) \<times> ('c \<Rightarrow> 'a)"
    and dest :: "nat \<Rightarrow> ae_dest"
  assumes q_in: "q \<in> Q_ktm M"
      and q_neq_t: "q \<noteq> t_ktm M"
      and q_neq_r: "q \<noteq> r_ktm M"
      and read: "is_padded_block (bl_ktm M) (ts (0 :: nat) (n 0))"
      and bt: "\<forall>j\<ge>k_ktm M. \<forall>i. ts j i = bl_block (bl_ktm M)"
      and stage_tail: "(\<forall>j\<ge>k_ktm M. ofs j = init_offset j)
                        \<and> (\<forall>j\<ge>k_ktm M. buf j = init_buffer (le_ktm M) j)
                        \<and> (\<forall>j\<ge>k_ktm M. dest j = init_dest j)"
      and gamma: "\<forall>k. ts k (n k) \<in> gamma_block (\<Gamma>_ktm M)"
      and buf_gamma: "\<forall>k. fst (buf k) \<in> gamma_block (\<Gamma>_ktm M)
                            \<and> fst (snd (buf k)) \<in> gamma_block (\<Gamma>_ktm M)
                            \<and> snd (snd (buf k)) \<in> gamma_block (\<Gamma>_ktm M)"
  shows "(KConfig (q, ofs, buf, dest, VFwd) ts n,
            KConfig (q, ofs, buf, dest, VFwdPad) ts
              (\<lambda>k. go_move (if k = 0 then MoveR else MoveN) (n k)))
           \<in> ktm_step (alphabet_enlarge_delta M)"
proof -
  let ?d = "\<lambda>k :: nat. if k = 0 then MoveR else MoveN"
  let ?a = "\<lambda>k. ts k (n k)"
  have rel_in: "((q, ofs, buf, dest, VFwd), ?a,
                  (q, ofs, buf, dest, VFwdPad), ?a, ?d)
                  \<in> ae_delta_val_fwd_to_padded M"
    unfolding ae_delta_val_fwd_to_padded_def
    using q_in q_neq_t q_neq_r read bt by auto
  have src_valid: "ae_valid_stage (\<Gamma>_ktm M) (le_ktm M) (k_ktm M)
                      (snd ((q, ofs, buf, dest, VFwd)
                              :: 'q \<times> ('a, 'c) ae_stage))"
    using buf_gamma stage_tail unfolding ae_valid_stage_def by simp
  have dst_valid: "ae_valid_stage (\<Gamma>_ktm M) (le_ktm M) (k_ktm M)
                      (snd ((q, ofs, buf, dest, VFwdPad)
                              :: 'q \<times> ('a, 'c) ae_stage))"
    using buf_gamma stage_tail unfolding ae_valid_stage_def by simp
  have aed_in: "((q, ofs, buf, dest, VFwd), ?a,
                  (q, ofs, buf, dest, VFwdPad), ?a, ?d)
                  \<in> alphabet_enlarge_delta M"
    unfolding alphabet_enlarge_delta_def
    using rel_in gamma src_valid dst_valid by auto
  have ts_unchanged: "(\<lambda>k. (ts k)(n k := ?a k)) = ts"
    by (rule ext) auto
  have step: "(KConfig (q, ofs, buf, dest, VFwd) ts n,
                KConfig (q, ofs, buf, dest, VFwdPad)
                  (\<lambda>k. (ts k)(n k := ?a k))
                  (\<lambda>k. go_move (?d k) (n k)))
                \<in> ktm_step (alphabet_enlarge_delta M)"
  proof (rule ae_step_make)
    show "((q, ofs, buf, dest, VFwd), ?a,
            (q, ofs, buf, dest, VFwdPad), ?a, ?d)
              \<in> alphabet_enlarge_delta M" by (rule aed_in)
  qed
  show ?thesis using step ts_unchanged by simp
qed

text \<open>VFwd \<open>\<rightarrow>\<close> VRet: read \<open>bl_block bl_M\<close> on tape 0
  (past the encoded input); N moves uniformly (head stays); phase
  becomes VRet.\<close>

lemma ae_step_val_fwd_to_ret:
  fixes M :: "('q, 'a) ktm"
    and ts :: "nat \<Rightarrow> nat \<Rightarrow> ('c :: enum \<Rightarrow> 'a)"
    and n :: "nat \<Rightarrow> nat"
    and q :: 'q
    and ofs :: "nat \<Rightarrow> 'c"
    and buf :: "nat \<Rightarrow> ('c \<Rightarrow> 'a) \<times> ('c \<Rightarrow> 'a) \<times> ('c \<Rightarrow> 'a)"
    and dest :: "nat \<Rightarrow> ae_dest"
  assumes q_in: "q \<in> Q_ktm M"
      and q_neq_t: "q \<noteq> t_ktm M"
      and q_neq_r: "q \<noteq> r_ktm M"
      and read: "ts (0 :: nat) (n 0) = bl_block (bl_ktm M)"
      and bt: "\<forall>j\<ge>k_ktm M. \<forall>i. ts j i = bl_block (bl_ktm M)"
      and stage_tail: "(\<forall>j\<ge>k_ktm M. ofs j = init_offset j)
                        \<and> (\<forall>j\<ge>k_ktm M. buf j = init_buffer (le_ktm M) j)
                        \<and> (\<forall>j\<ge>k_ktm M. dest j = init_dest j)"
      and gamma: "\<forall>k. ts k (n k) \<in> gamma_block (\<Gamma>_ktm M)"
      and buf_gamma: "\<forall>k. fst (buf k) \<in> gamma_block (\<Gamma>_ktm M)
                            \<and> fst (snd (buf k)) \<in> gamma_block (\<Gamma>_ktm M)
                            \<and> snd (snd (buf k)) \<in> gamma_block (\<Gamma>_ktm M)"
  shows "(KConfig (q, ofs, buf, dest, VFwd) ts n,
            KConfig (q, ofs, buf, dest, VRet) ts n)
           \<in> ktm_step (alphabet_enlarge_delta M)"
proof -
  let ?d = "\<lambda>_ :: nat. MoveN"
  let ?a = "\<lambda>k. ts k (n k)"
  have rel_in: "((q, ofs, buf, dest, VFwd), ?a,
                  (q, ofs, buf, dest, VRet), ?a, ?d)
                  \<in> ae_delta_val_fwd_to_ret M"
    unfolding ae_delta_val_fwd_to_ret_def
    using q_in q_neq_t q_neq_r read bt by auto
  have src_valid: "ae_valid_stage (\<Gamma>_ktm M) (le_ktm M) (k_ktm M)
                      (snd ((q, ofs, buf, dest, VFwd)
                              :: 'q \<times> ('a, 'c) ae_stage))"
    using buf_gamma stage_tail unfolding ae_valid_stage_def by simp
  have dst_valid: "ae_valid_stage (\<Gamma>_ktm M) (le_ktm M) (k_ktm M)
                      (snd ((q, ofs, buf, dest, VRet)
                              :: 'q \<times> ('a, 'c) ae_stage))"
    using buf_gamma stage_tail unfolding ae_valid_stage_def by simp
  have aed_in: "((q, ofs, buf, dest, VFwd), ?a,
                  (q, ofs, buf, dest, VRet), ?a, ?d)
                  \<in> alphabet_enlarge_delta M"
    unfolding alphabet_enlarge_delta_def
    using rel_in gamma src_valid dst_valid by auto
  have ts_unchanged: "(\<lambda>k. (ts k)(n k := ?a k)) = ts"
    by (rule ext) auto
  have n_unchanged: "(\<lambda>k :: nat. go_move (?d k) (n k)) = n"
    by (rule ext) simp
  have step: "(KConfig (q, ofs, buf, dest, VFwd) ts n,
                KConfig (q, ofs, buf, dest, VRet)
                  (\<lambda>k. (ts k)(n k := ?a k))
                  (\<lambda>k. go_move (?d k) (n k)))
                \<in> ktm_step (alphabet_enlarge_delta M)"
  proof (rule ae_step_make)
    show "((q, ofs, buf, dest, VFwd), ?a,
            (q, ofs, buf, dest, VRet), ?a, ?d)
              \<in> alphabet_enlarge_delta M" by (rule aed_in)
  qed
  show ?thesis using step ts_unchanged n_unchanged by simp
qed

text \<open>VFwdPad \<open>\<rightarrow>\<close> VRet: read \<open>bl_block bl_M\<close> on tape 0
  (past the trailing-padded block into the blanks); N moves;
  phase becomes VRet.\<close>

lemma ae_step_val_pad_to_ret:
  fixes M :: "('q, 'a) ktm"
    and ts :: "nat \<Rightarrow> nat \<Rightarrow> ('c :: enum \<Rightarrow> 'a)"
    and n :: "nat \<Rightarrow> nat"
    and q :: 'q
    and ofs :: "nat \<Rightarrow> 'c"
    and buf :: "nat \<Rightarrow> ('c \<Rightarrow> 'a) \<times> ('c \<Rightarrow> 'a) \<times> ('c \<Rightarrow> 'a)"
    and dest :: "nat \<Rightarrow> ae_dest"
  assumes q_in: "q \<in> Q_ktm M"
      and read: "ts (0 :: nat) (n 0) = bl_block (bl_ktm M)"
      and bt: "\<forall>j\<ge>k_ktm M. \<forall>i. ts j i = bl_block (bl_ktm M)"
      and stage_tail: "(\<forall>j\<ge>k_ktm M. ofs j = init_offset j)
                        \<and> (\<forall>j\<ge>k_ktm M. buf j = init_buffer (le_ktm M) j)
                        \<and> (\<forall>j\<ge>k_ktm M. dest j = init_dest j)"
      and gamma: "\<forall>k. ts k (n k) \<in> gamma_block (\<Gamma>_ktm M)"
      and buf_gamma: "\<forall>k. fst (buf k) \<in> gamma_block (\<Gamma>_ktm M)
                            \<and> fst (snd (buf k)) \<in> gamma_block (\<Gamma>_ktm M)
                            \<and> snd (snd (buf k)) \<in> gamma_block (\<Gamma>_ktm M)"
  shows "(KConfig (q, ofs, buf, dest, VFwdPad) ts n,
            KConfig (q, ofs, buf, dest, VRet) ts n)
           \<in> ktm_step (alphabet_enlarge_delta M)"
proof -
  let ?d = "\<lambda>_ :: nat. MoveN"
  let ?a = "\<lambda>k. ts k (n k)"
  have rel_in: "((q, ofs, buf, dest, VFwdPad), ?a,
                  (q, ofs, buf, dest, VRet), ?a, ?d)
                  \<in> ae_delta_val_pad_to_ret M"
    unfolding ae_delta_val_pad_to_ret_def
    using q_in read bt by auto
  have src_valid: "ae_valid_stage (\<Gamma>_ktm M) (le_ktm M) (k_ktm M)
                      (snd ((q, ofs, buf, dest, VFwdPad)
                              :: 'q \<times> ('a, 'c) ae_stage))"
    using buf_gamma stage_tail unfolding ae_valid_stage_def by simp
  have dst_valid: "ae_valid_stage (\<Gamma>_ktm M) (le_ktm M) (k_ktm M)
                      (snd ((q, ofs, buf, dest, VRet)
                              :: 'q \<times> ('a, 'c) ae_stage))"
    using buf_gamma stage_tail unfolding ae_valid_stage_def by simp
  have aed_in: "((q, ofs, buf, dest, VFwdPad), ?a,
                  (q, ofs, buf, dest, VRet), ?a, ?d)
                  \<in> alphabet_enlarge_delta M"
    unfolding alphabet_enlarge_delta_def
    using rel_in gamma src_valid dst_valid by auto
  have ts_unchanged: "(\<lambda>k. (ts k)(n k := ?a k)) = ts"
    by (rule ext) auto
  have n_unchanged: "(\<lambda>k :: nat. go_move (?d k) (n k)) = n"
    by (rule ext) simp
  have step: "(KConfig (q, ofs, buf, dest, VFwdPad) ts n,
                KConfig (q, ofs, buf, dest, VRet)
                  (\<lambda>k. (ts k)(n k := ?a k))
                  (\<lambda>k. go_move (?d k) (n k)))
                \<in> ktm_step (alphabet_enlarge_delta M)"
  proof (rule ae_step_make)
    show "((q, ofs, buf, dest, VFwdPad), ?a,
            (q, ofs, buf, dest, VRet), ?a, ?d)
              \<in> alphabet_enlarge_delta M" by (rule aed_in)
  qed
  show ?thesis using step ts_unchanged n_unchanged by simp
qed

text \<open>VRet step: read a non-LE block on tape 0 (during the
  return scan); head moves L on tape 0, N elsewhere; phase stays
  VRet.\<close>

lemma ae_step_val_ret_step:
  fixes M :: "('q, 'a) ktm"
    and ts :: "nat \<Rightarrow> nat \<Rightarrow> ('c :: enum \<Rightarrow> 'a)"
    and n :: "nat \<Rightarrow> nat"
    and q :: 'q
    and ofs :: "nat \<Rightarrow> 'c"
    and buf :: "nat \<Rightarrow> ('c \<Rightarrow> 'a) \<times> ('c \<Rightarrow> 'a) \<times> ('c \<Rightarrow> 'a)"
    and dest :: "nat \<Rightarrow> ae_dest"
  assumes q_in: "q \<in> Q_ktm M"
      and read: "ts (0 :: nat) (n 0) \<noteq> LE_block (le_ktm M)"
      and bt: "\<forall>j\<ge>k_ktm M. \<forall>i. ts j i = bl_block (bl_ktm M)"
      and stage_tail: "(\<forall>j\<ge>k_ktm M. ofs j = init_offset j)
                        \<and> (\<forall>j\<ge>k_ktm M. buf j = init_buffer (le_ktm M) j)
                        \<and> (\<forall>j\<ge>k_ktm M. dest j = init_dest j)"
      and gamma: "\<forall>k. ts k (n k) \<in> gamma_block (\<Gamma>_ktm M)"
      and buf_gamma: "\<forall>k. fst (buf k) \<in> gamma_block (\<Gamma>_ktm M)
                            \<and> fst (snd (buf k)) \<in> gamma_block (\<Gamma>_ktm M)
                            \<and> snd (snd (buf k)) \<in> gamma_block (\<Gamma>_ktm M)"
  shows "(KConfig (q, ofs, buf, dest, VRet) ts n,
            KConfig (q, ofs, buf, dest, VRet) ts
              (\<lambda>k. go_move (if k = 0 then MoveL else MoveN) (n k)))
           \<in> ktm_step (alphabet_enlarge_delta M)"
proof -
  let ?d = "\<lambda>k :: nat. if k = 0 then MoveL else MoveN"
  let ?a = "\<lambda>k. ts k (n k)"
  have rel_in: "((q, ofs, buf, dest, VRet), ?a,
                  (q, ofs, buf, dest, VRet), ?a, ?d)
                  \<in> ae_delta_val_ret_step M"
    unfolding ae_delta_val_ret_step_def
    using q_in read bt by auto
  have src_valid: "ae_valid_stage (\<Gamma>_ktm M) (le_ktm M) (k_ktm M)
                      (snd ((q, ofs, buf, dest, VRet)
                              :: 'q \<times> ('a, 'c) ae_stage))"
    using buf_gamma stage_tail unfolding ae_valid_stage_def by simp
  have aed_in: "((q, ofs, buf, dest, VRet), ?a,
                  (q, ofs, buf, dest, VRet), ?a, ?d)
                  \<in> alphabet_enlarge_delta M"
    unfolding alphabet_enlarge_delta_def
    using rel_in gamma src_valid by auto
  have ts_unchanged: "(\<lambda>k. (ts k)(n k := ?a k)) = ts"
    by (rule ext) auto
  have step: "(KConfig (q, ofs, buf, dest, VRet) ts n,
                KConfig (q, ofs, buf, dest, VRet)
                  (\<lambda>k. (ts k)(n k := ?a k))
                  (\<lambda>k. go_move (?d k) (n k)))
                \<in> ktm_step (alphabet_enlarge_delta M)"
  proof (rule ae_step_make)
    show "((q, ofs, buf, dest, VRet), ?a,
            (q, ofs, buf, dest, VRet), ?a, ?d)
              \<in> alphabet_enlarge_delta M" by (rule aed_in)
  qed
  show ?thesis using step ts_unchanged by simp
qed

text \<open>VRet \<open>\<rightarrow>\<close> Sim: read \<open>LE_block le_M\<close> on tape 0
  (return scan reached position 0); N moves uniformly (head
  stays); phase becomes Sim with \<open>substep_idx\<close> = SS1.\<close>

lemma ae_step_val_ret_to_sim:
  fixes M :: "('q, 'a) ktm"
    and ts :: "nat \<Rightarrow> nat \<Rightarrow> ('c :: enum \<Rightarrow> 'a)"
    and n :: "nat \<Rightarrow> nat"
    and q :: 'q
    and ofs :: "nat \<Rightarrow> 'c"
    and buf :: "nat \<Rightarrow> ('c \<Rightarrow> 'a) \<times> ('c \<Rightarrow> 'a) \<times> ('c \<Rightarrow> 'a)"
    and dest :: "nat \<Rightarrow> ae_dest"
  assumes q_in: "q \<in> Q_ktm M"
      and read: "ts (0 :: nat) (n 0) = LE_block (le_ktm M)"
      and bt: "\<forall>j\<ge>k_ktm M. \<forall>i. ts j i = bl_block (bl_ktm M)"
      and stage_tail: "(\<forall>j\<ge>k_ktm M. ofs j = init_offset j)
                        \<and> (\<forall>j\<ge>k_ktm M. buf j = init_buffer (le_ktm M) j)
                        \<and> (\<forall>j\<ge>k_ktm M. dest j = init_dest j)"
      and gamma: "\<forall>k. ts k (n k) \<in> gamma_block (\<Gamma>_ktm M)"
      and buf_gamma: "\<forall>k. fst (buf k) \<in> gamma_block (\<Gamma>_ktm M)
                            \<and> fst (snd (buf k)) \<in> gamma_block (\<Gamma>_ktm M)
                            \<and> snd (snd (buf k)) \<in> gamma_block (\<Gamma>_ktm M)"
  shows "(KConfig (q, ofs, buf, dest, VRet) ts n,
            KConfig (q, ofs, buf, dest, SS1) ts n)
           \<in> ktm_step (alphabet_enlarge_delta M)"
proof -
  let ?d = "\<lambda>_ :: nat. MoveN"
  let ?a = "\<lambda>k. ts k (n k)"
  have rel_in: "((q, ofs, buf, dest, VRet), ?a,
                  (q, ofs, buf, dest, SS1), ?a, ?d)
                  \<in> ae_delta_val_ret_to_sim M"
    unfolding ae_delta_val_ret_to_sim_def
    using q_in read bt by auto
  have src_valid: "ae_valid_stage (\<Gamma>_ktm M) (le_ktm M) (k_ktm M)
                      (snd ((q, ofs, buf, dest, VRet)
                              :: 'q \<times> ('a, 'c) ae_stage))"
    using buf_gamma stage_tail unfolding ae_valid_stage_def by simp
  have dst_valid: "ae_valid_stage (\<Gamma>_ktm M) (le_ktm M) (k_ktm M)
                      (snd ((q, ofs, buf, dest, SS1)
                              :: 'q \<times> ('a, 'c) ae_stage))"
    using buf_gamma stage_tail unfolding ae_valid_stage_def by simp
  have aed_in: "((q, ofs, buf, dest, VRet), ?a,
                  (q, ofs, buf, dest, SS1), ?a, ?d)
                  \<in> alphabet_enlarge_delta M"
    unfolding alphabet_enlarge_delta_def
    using rel_in gamma src_valid dst_valid by auto
  have ts_unchanged: "(\<lambda>k. (ts k)(n k := ?a k)) = ts"
    by (rule ext) auto
  have n_unchanged: "(\<lambda>k :: nat. go_move (?d k) (n k)) = n"
    by (rule ext) simp
  have step: "(KConfig (q, ofs, buf, dest, VRet) ts n,
                KConfig (q, ofs, buf, dest, SS1)
                  (\<lambda>k. (ts k)(n k := ?a k))
                  (\<lambda>k. go_move (?d k) (n k)))
                \<in> ktm_step (alphabet_enlarge_delta M)"
  proof (rule ae_step_make)
    show "((q, ofs, buf, dest, VRet), ?a,
            (q, ofs, buf, dest, SS1), ?a, ?d)
              \<in> alphabet_enlarge_delta M" by (rule aed_in)
  qed
  show ?thesis using step ts_unchanged n_unchanged by simp
qed

text \<open>VFwd reject: read a non-canonical block on tape 0
  (in \<open>\<Sigma>'\<close> but neither pure nor padded — blanks in
  non-trailing positions); N moves uniformly; transition to
  \<open>(r_M, init_stage le_M)\<close>.\<close>

lemma ae_step_val_fwd_reject:
  fixes M :: "('q, 'a) ktm"
    and ts :: "nat \<Rightarrow> nat \<Rightarrow> ('c :: enum \<Rightarrow> 'a)"
    and n :: "nat \<Rightarrow> nat"
    and q :: 'q
    and ofs :: "nat \<Rightarrow> 'c"
    and buf :: "nat \<Rightarrow> ('c \<Rightarrow> 'a) \<times> ('c \<Rightarrow> 'a) \<times> ('c \<Rightarrow> 'a)"
    and dest :: "nat \<Rightarrow> ae_dest"
  assumes vM: "valid_ktm M"
      and q_in: "q \<in> Q_ktm M"
      and q_neq_t: "q \<noteq> t_ktm M"
      and q_neq_r: "q \<noteq> r_ktm M"
      and read_nle: "ts (0 :: nat) (n 0) \<noteq> LE_block (le_ktm M)"
      and read_nbl: "ts (0 :: nat) (n 0) \<noteq> bl_block (bl_ktm M)"
      and read_ncan: "\<not> is_canonical_block (bl_ktm M) (ts (0 :: nat) (n 0))"
      and bt: "\<forall>j\<ge>k_ktm M. \<forall>i. ts j i = bl_block (bl_ktm M)"
      and stage_tail: "(\<forall>j\<ge>k_ktm M. ofs j = init_offset j)
                        \<and> (\<forall>j\<ge>k_ktm M. buf j = init_buffer (le_ktm M) j)
                        \<and> (\<forall>j\<ge>k_ktm M. dest j = init_dest j)"
      and gamma: "\<forall>k. ts k (n k) \<in> gamma_block (\<Gamma>_ktm M)"
      and buf_gamma: "\<forall>k. fst (buf k) \<in> gamma_block (\<Gamma>_ktm M)
                            \<and> fst (snd (buf k)) \<in> gamma_block (\<Gamma>_ktm M)
                            \<and> snd (snd (buf k)) \<in> gamma_block (\<Gamma>_ktm M)"
  shows "(KConfig (q, ofs, buf, dest, VFwd) ts n,
            KConfig (r_ktm M, init_stage (le_ktm M)) ts n)
           \<in> ktm_step (alphabet_enlarge_delta M)"
proof -
  let ?d = "\<lambda>_ :: nat. MoveN"
  let ?a = "\<lambda>k. ts k (n k)"
  have rel_in: "((q, ofs, buf, dest, VFwd), ?a,
                  (r_ktm M, init_stage (le_ktm M)), ?a, ?d)
                  \<in> ae_delta_val_fwd_reject M"
    unfolding ae_delta_val_fwd_reject_def
    using q_in q_neq_t q_neq_r read_nle read_nbl read_ncan bt by auto
  have src_valid: "ae_valid_stage (\<Gamma>_ktm M) (le_ktm M) (k_ktm M)
                      (snd ((q, ofs, buf, dest, VFwd)
                              :: 'q \<times> ('a, 'c) ae_stage))"
    using buf_gamma stage_tail unfolding ae_valid_stage_def by simp
  have dst_valid: "ae_valid_stage (\<Gamma>_ktm M) (le_ktm M) (k_ktm M)
                      (snd ((r_ktm M, init_stage (le_ktm M))
                              :: 'q \<times> ('a, 'c) ae_stage))"
    using ae_valid_stage_init[OF valid_ktm_LE_in_Gamma[OF vM]] by simp
  have aed_in: "((q, ofs, buf, dest, VFwd), ?a,
                  (r_ktm M, init_stage (le_ktm M)), ?a, ?d)
                  \<in> alphabet_enlarge_delta M"
    unfolding alphabet_enlarge_delta_def
    using rel_in gamma src_valid dst_valid by auto
  have ts_unchanged: "(\<lambda>k. (ts k)(n k := ?a k)) = ts"
    by (rule ext) auto
  have n_unchanged: "(\<lambda>k :: nat. go_move (?d k) (n k)) = n"
    by (rule ext) simp
  have step: "(KConfig (q, ofs, buf, dest, VFwd) ts n,
                KConfig (r_ktm M, init_stage (le_ktm M))
                  (\<lambda>k. (ts k)(n k := ?a k))
                  (\<lambda>k. go_move (?d k) (n k)))
                \<in> ktm_step (alphabet_enlarge_delta M)"
  proof (rule ae_step_make)
    show "((q, ofs, buf, dest, VFwd), ?a,
            (r_ktm M, init_stage (le_ktm M)), ?a, ?d)
              \<in> alphabet_enlarge_delta M" by (rule aed_in)
  qed
  show ?thesis using step ts_unchanged n_unchanged by simp
qed

text \<open>VFwdPad reject: read anything on tape 0 other than
  \<open>bl_block bl_M\<close> (a non-blank block after the
  trailing-padded one); N moves; transition to
  \<open>(r_M, init_stage le_M)\<close>.\<close>

lemma ae_step_val_pad_reject:
  fixes M :: "('q, 'a) ktm"
    and ts :: "nat \<Rightarrow> nat \<Rightarrow> ('c :: enum \<Rightarrow> 'a)"
    and n :: "nat \<Rightarrow> nat"
    and q :: 'q
    and ofs :: "nat \<Rightarrow> 'c"
    and buf :: "nat \<Rightarrow> ('c \<Rightarrow> 'a) \<times> ('c \<Rightarrow> 'a) \<times> ('c \<Rightarrow> 'a)"
    and dest :: "nat \<Rightarrow> ae_dest"
  assumes vM: "valid_ktm M"
      and q_in: "q \<in> Q_ktm M"
      and read: "ts (0 :: nat) (n 0) \<noteq> bl_block (bl_ktm M)"
      and bt: "\<forall>j\<ge>k_ktm M. \<forall>i. ts j i = bl_block (bl_ktm M)"
      and stage_tail: "(\<forall>j\<ge>k_ktm M. ofs j = init_offset j)
                        \<and> (\<forall>j\<ge>k_ktm M. buf j = init_buffer (le_ktm M) j)
                        \<and> (\<forall>j\<ge>k_ktm M. dest j = init_dest j)"
      and gamma: "\<forall>k. ts k (n k) \<in> gamma_block (\<Gamma>_ktm M)"
      and buf_gamma: "\<forall>k. fst (buf k) \<in> gamma_block (\<Gamma>_ktm M)
                            \<and> fst (snd (buf k)) \<in> gamma_block (\<Gamma>_ktm M)
                            \<and> snd (snd (buf k)) \<in> gamma_block (\<Gamma>_ktm M)"
  shows "(KConfig (q, ofs, buf, dest, VFwdPad) ts n,
            KConfig (r_ktm M, init_stage (le_ktm M)) ts n)
           \<in> ktm_step (alphabet_enlarge_delta M)"
proof -
  let ?d = "\<lambda>_ :: nat. MoveN"
  let ?a = "\<lambda>k. ts k (n k)"
  have rel_in: "((q, ofs, buf, dest, VFwdPad), ?a,
                  (r_ktm M, init_stage (le_ktm M)), ?a, ?d)
                  \<in> ae_delta_val_pad_reject M"
    unfolding ae_delta_val_pad_reject_def
    using q_in read bt by auto
  have src_valid: "ae_valid_stage (\<Gamma>_ktm M) (le_ktm M) (k_ktm M)
                      (snd ((q, ofs, buf, dest, VFwdPad)
                              :: 'q \<times> ('a, 'c) ae_stage))"
    using buf_gamma stage_tail unfolding ae_valid_stage_def by simp
  have dst_valid: "ae_valid_stage (\<Gamma>_ktm M) (le_ktm M) (k_ktm M)
                      (snd ((r_ktm M, init_stage (le_ktm M))
                              :: 'q \<times> ('a, 'c) ae_stage))"
    using ae_valid_stage_init[OF valid_ktm_LE_in_Gamma[OF vM]] by simp
  have aed_in: "((q, ofs, buf, dest, VFwdPad), ?a,
                  (r_ktm M, init_stage (le_ktm M)), ?a, ?d)
                  \<in> alphabet_enlarge_delta M"
    unfolding alphabet_enlarge_delta_def
    using rel_in gamma src_valid dst_valid by auto
  have ts_unchanged: "(\<lambda>k. (ts k)(n k := ?a k)) = ts"
    by (rule ext) auto
  have n_unchanged: "(\<lambda>k :: nat. go_move (?d k) (n k)) = n"
    by (rule ext) simp
  have step: "(KConfig (q, ofs, buf, dest, VFwdPad) ts n,
                KConfig (r_ktm M, init_stage (le_ktm M))
                  (\<lambda>k. (ts k)(n k := ?a k))
                  (\<lambda>k. go_move (?d k) (n k)))
                \<in> ktm_step (alphabet_enlarge_delta M)"
  proof (rule ae_step_make)
    show "((q, ofs, buf, dest, VFwdPad), ?a,
            (r_ktm M, init_stage (le_ktm M)), ?a, ?d)
              \<in> alphabet_enlarge_delta M" by (rule aed_in)
  qed
  show ?thesis using step ts_unchanged n_unchanged by simp
qed

subsubsection \<open>The initial configuration\<close>

text \<open>Shape lookups for \<open>ae_init_config\<close>.  These give the tape
  contents at named positions — LE at position 0, input blocks
  at positions \<open>1\<dots>length w\<close>, blank-block elsewhere — and the
  uniform state / head shape.  Used pervasively by the validation
  chain proofs; trivial unfoldings of \<open>ae_init_config_def\<close>.\<close>

lemma ae_init_config_state:
  "ktc_state (ae_init_config M w) = (s_ktm M, init_stage (le_ktm M))"
  unfolding ae_init_config_def by simp

lemma ae_init_config_pos:
  "ktc_pos (ae_init_config M w) k = 0"
  unfolding ae_init_config_def by simp

lemma ae_init_config_tape_le:
  assumes "k < k_ktm M"
  shows "ktc_tape (ae_init_config M w) k 0 = LE_block (le_ktm M)"
  using assms unfolding ae_init_config_def by simp

lemma ae_init_config_tape_input:
  assumes "1 \<le> p" and "p \<le> length w" and "0 < k_ktm M"
  shows "ktc_tape (ae_init_config M w) 0 p = w ! (p - 1)"
  using assms unfolding ae_init_config_def by simp

lemma ae_init_config_tape_blank_after_input:
  assumes "p > length w"
  shows "ktc_tape (ae_init_config M w) 0 p = bl_block (bl_ktm M)"
  using assms unfolding ae_init_config_def by simp

lemma ae_init_config_tape_other:
  assumes "k \<noteq> 0" and "p > 0"
  shows "ktc_tape (ae_init_config M w) k p = bl_block (bl_ktm M)"
  using assms unfolding ae_init_config_def by simp

text \<open>Blank-tail of the initial configuration: every cell of every
  inactive tape (index \<open>\<ge> k_ktm M\<close>) holds the blank block.
  This is the value-level support condition the substrate's
  \<open>init_config_ktm\<close> imposes on \<open>alphabet_enlarge M\<close>; it discharges
  the \<open>\<forall>j\<ge>k_ktm M. ts j (n j) = bl_block (bl_ktm M)\<close> premise of every
  validation step-helper (the tape is never written during
  validation, so \<open>ts = ktc_tape (ae_init_config M w)\<close> throughout).\<close>

lemma ae_init_config_tape_blank_tail:
  assumes "k_ktm M \<le> k"
  shows "ktc_tape (ae_init_config M w) k p = bl_block (bl_ktm M)"
  using assms unfolding ae_init_config_def by simp

text \<open>Gamma-block membership of every tape cell of the initial
  configuration.  Uniformly discharges the
  \<open>\<forall>k. ts k (n k) \<in> gamma_block (\<Gamma>_ktm M)\<close> premise of every
  validation step-helper, regardless of the head position \<open>n\<close>
  reached during the chain.\<close>

lemma ae_init_config_in_gamma_block:
  fixes M :: "('q, 'a) ktm"
    and w :: "(('c :: enum) \<Rightarrow> 'a) list"
  assumes vM: "valid_ktm M"
      and w_sub: "set w \<subseteq> gamma_block (Sigma_ktm M \<union> {bl_ktm M})"
  shows "ktc_tape (ae_init_config M w) k p \<in> gamma_block (\<Gamma>_ktm M)"
proof -
  have bl_in: "bl_ktm M \<in> \<Gamma>_ktm M"
    by (rule valid_ktm_blank_in_Gamma[OF vM])
  have le_in: "le_ktm M \<in> \<Gamma>_ktm M"
    by (rule valid_ktm_LE_in_Gamma[OF vM])
  have Sigma_sub: "Sigma_ktm M \<subseteq> \<Gamma>_ktm M"
    by (rule valid_ktm_Sigma_sub_Gamma[OF vM])
  have sub: "Sigma_ktm M \<union> {bl_ktm M} \<subseteq> \<Gamma>_ktm M"
    using Sigma_sub bl_in by auto
  have w_sub_G: "set w \<subseteq> gamma_block (\<Gamma>_ktm M)"
    using w_sub gamma_block_mono[OF sub] by blast
  have kpos: "0 < k_ktm M" by (rule valid_ktm_k_pos[OF vM])
  consider
      (zero_act) "p = 0" and "k < k_ktm M"
    | (zero_inact) "p = 0" and "\<not> k < k_ktm M"
    | (input) "p \<noteq> 0" and "k = 0" and "p \<le> length w"
    | (blank) "p \<noteq> 0" and "\<not> (k = 0 \<and> p \<le> length w)"
    by blast
  thus ?thesis
  proof cases
    case zero_act
    have "ktc_tape (ae_init_config M w) k p = LE_block (le_ktm M)"
      using zero_act ae_init_config_tape_le by simp
    thus ?thesis using LE_block_in_gamma_block[OF le_in] by simp
  next
    case zero_inact
    have "ktc_tape (ae_init_config M w) k p = bl_block (bl_ktm M)"
      using zero_inact unfolding ae_init_config_def by simp
    thus ?thesis using bl_block_in_gamma_block[OF bl_in] by simp
  next
    case input
    have "ktc_tape (ae_init_config M w) k p = w ! (p - 1)"
      using input kpos ae_init_config_tape_input[of p w M] by simp
    moreover have "w ! (p - 1) \<in> set w"
      using input by auto
    ultimately show ?thesis using w_sub_G by auto
  next
    case blank
    have "ktc_tape (ae_init_config M w) k p = bl_block (bl_ktm M)"
      using blank unfolding ae_init_config_def by auto
    thus ?thesis using bl_block_in_gamma_block[OF bl_in] by simp
  qed
qed

end
