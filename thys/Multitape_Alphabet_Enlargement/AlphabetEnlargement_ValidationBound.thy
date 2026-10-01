theory AlphabetEnlargement_ValidationBound
  imports AlphabetEnlargement_ValidationStep
begin

subsection \<open>Validation sweeps, post-state, and step bound\<close>

subsubsection \<open>Validation sweeps and tape correspondence\<close>

text \<open>Forward-sweep iteration helper.  Starting from
  \<open>ae_init_config M w\<close>, after \<open>Suc k\<close> validation steps along a
  \<open>k\<close>-pure prefix of \<open>w\<close>, the head on tape 0 is at position
  \<open>Suc k\<close> and the phase is still \<open>VFwd\<close>.  The chain is built
  by induction on \<open>k\<close>, applying \<open>ae_step_val_fwd_advance\<close> once
  per step (the LE block at position 0 takes the first step, then
  each pure block along positions \<open>1\<dots>k\<close> takes one more).\<close>

lemma ae_validation_fwd_sweep_pure:
  fixes M :: "('q, 'a) mttm"
    and w :: "(('c :: enum) \<Rightarrow> 'a) list"
  assumes vM: "valid_mttm M"
      and w_sub: "set w \<subseteq> gamma_block (Sigma_tm M \<union> {bl_tm M})"
      and s_in_Q: "s_tm M \<in> Q_tm M"
      and s_neq_t: "s_tm M \<noteq> t_tm M"
      and s_neq_r: "s_tm M \<noteq> r_tm M"
      and k_bound: "k \<le> length w"
      and pure: "\<forall>i < k. is_pure_block (bl_tm M) (w ! i)"
  shows "(ae_init_config M w,
            Config\<^sub>M (s_tm M, init_stage (le_tm M))
                     (mt_tape (ae_init_config M w))
                     (\<lambda>i :: nat. if i = 0 then Suc k else 0))
           \<in> mttm_step (alphabet_enlarge_delta M) ^^ Suc k"
  using k_bound pure
proof (induction k)
  case 0
  let ?ts = "mt_tape (ae_init_config M w)"
  let ?n0 = "\<lambda>_ :: nat. 0 :: nat"
  let ?n1 = "\<lambda>i :: nat. if i = 0 then Suc 0 else 0"
  have init_eq: "ae_init_config M w
                  = Config\<^sub>M (s_tm M, init_stage (le_tm M)) ?ts ?n0"
    by (simp add: ae_init_config_def)
  have kpos: "0 < k_tm M" by (rule valid_mttm_k_pos[OF vM])
  have read: "?ts 0 (?n0 0) = LE_block (le_tm M)
              \<or> is_pure_block (bl_tm M) (?ts 0 (?n0 0))"
    using ae_init_config_tape_le[OF kpos] by auto
  have bt_all: "\<forall>j\<ge>k_tm M. \<forall>i. ?ts j i = bl_block (bl_tm M)"
    using ae_init_config_tape_blank_tail by blast
  have gamma: "\<forall>kk :: nat. ?ts kk (?n0 kk) \<in> gamma_block (\<Gamma>_tm M)"
    using ae_init_config_in_gamma_block[OF vM w_sub] by simp
  have buf_gamma_init:
      "\<forall>kk :: nat.
          fst (init_buffer (le_tm M) kk
                  :: ('c \<Rightarrow> 'a) \<times> ('c \<Rightarrow> 'a) \<times> ('c \<Rightarrow> 'a))
              \<in> gamma_block (\<Gamma>_tm M)
          \<and> fst (snd (init_buffer (le_tm M) kk
                        :: ('c \<Rightarrow> 'a) \<times> ('c \<Rightarrow> 'a) \<times> ('c \<Rightarrow> 'a)))
              \<in> gamma_block (\<Gamma>_tm M)
          \<and> snd (snd (init_buffer (le_tm M) kk
                        :: ('c \<Rightarrow> 'a) \<times> ('c \<Rightarrow> 'a) \<times> ('c \<Rightarrow> 'a)))
              \<in> gamma_block (\<Gamma>_tm M)"
    by (rule init_buffer_in_gamma_block_at_M[OF vM])
  have step1: "(Config\<^sub>M (s_tm M, init_offset, init_buffer (le_tm M),
                            init_dest, VFwd) ?ts ?n0,
                Config\<^sub>M (s_tm M, init_offset, init_buffer (le_tm M),
                            init_dest, VFwd) ?ts
                  (\<lambda>kk. go_dir (if kk = (0 :: nat) then dir.R else dir.N)
                                 (?n0 kk)))
                \<in> mttm_step (alphabet_enlarge_delta M)"
    by (rule ae_step_val_fwd_advance[where ts = ?ts and n = ?n0,
                                     OF s_in_Q s_neq_t s_neq_r read bt_all
                                        init_stage_tail gamma buf_gamma_init])
  have post_eq:
    "(\<lambda>kk :: nat. go_dir (if kk = 0 then dir.R else dir.N) (?n0 kk)) = ?n1"
    by (rule ext) simp
  have step1_n1: "(Config\<^sub>M (s_tm M, init_offset, init_buffer (le_tm M),
                              init_dest, VFwd) ?ts ?n0,
                   Config\<^sub>M (s_tm M, init_offset, init_buffer (le_tm M),
                              init_dest, VFwd) ?ts ?n1)
                  \<in> mttm_step (alphabet_enlarge_delta M)"
    using step1 post_eq by simp
  have stage_eq: "init_stage (le_tm M)
                  = (init_offset, init_buffer (le_tm M), init_dest, VFwd)"
    unfolding init_stage_def ..
  have step1_init: "(Config\<^sub>M (s_tm M, init_stage (le_tm M)) ?ts ?n0,
                     Config\<^sub>M (s_tm M, init_stage (le_tm M)) ?ts ?n1)
                    \<in> mttm_step (alphabet_enlarge_delta M)"
    using step1_n1 unfolding stage_eq by simp
  have chain1: "(ae_init_config M w,
                  Config\<^sub>M (s_tm M, init_stage (le_tm M)) ?ts ?n1)
                 \<in> mttm_step (alphabet_enlarge_delta M)"
    using step1_init init_eq by simp
  show ?case using chain1 by (simp add: relpow_1)
next
  case (Suc k)
  let ?ts = "mt_tape (ae_init_config M w)"
  let ?n_k = "\<lambda>i :: nat. if i = 0 then Suc k else 0"
  let ?n_Sk = "\<lambda>i :: nat. if i = 0 then Suc (Suc k) else 0"
  have k_le: "k \<le> length w" using Suc.prems(1) by simp
  have pure_k: "\<forall>i < k. is_pure_block (bl_tm M) (w ! i)"
    using Suc.prems(2) by simp
  from Suc.IH[OF k_le pure_k]
  have IH: "(ae_init_config M w,
              Config\<^sub>M (s_tm M, init_stage (le_tm M)) ?ts ?n_k)
              \<in> mttm_step (alphabet_enlarge_delta M) ^^ Suc k" .
  have read_pure: "is_pure_block (bl_tm M) (w ! k)"
    using Suc.prems(2) by auto
  have Sk_pos: "1 \<le> Suc k" by simp
  have Sk_le: "Suc k \<le> length w" using Suc.prems(1) .
  have kpos: "0 < k_tm M" by (rule valid_mttm_k_pos[OF vM])
  have read_eq: "?ts 0 (Suc k) = w ! k"
    using ae_init_config_tape_input[OF Sk_pos Sk_le kpos] by simp
  have read: "?ts 0 (?n_k 0) = LE_block (le_tm M)
              \<or> is_pure_block (bl_tm M) (?ts 0 (?n_k 0))"
    using read_pure read_eq by simp
  have bt_all: "\<forall>j\<ge>k_tm M. \<forall>i. ?ts j i = bl_block (bl_tm M)"
    using ae_init_config_tape_blank_tail by blast
  have gamma: "\<forall>kk :: nat. ?ts kk (?n_k kk) \<in> gamma_block (\<Gamma>_tm M)"
    using ae_init_config_in_gamma_block[OF vM w_sub] by simp
  have buf_gamma_init:
      "\<forall>kk :: nat.
          fst (init_buffer (le_tm M) kk
                  :: ('c \<Rightarrow> 'a) \<times> ('c \<Rightarrow> 'a) \<times> ('c \<Rightarrow> 'a))
              \<in> gamma_block (\<Gamma>_tm M)
          \<and> fst (snd (init_buffer (le_tm M) kk
                        :: ('c \<Rightarrow> 'a) \<times> ('c \<Rightarrow> 'a) \<times> ('c \<Rightarrow> 'a)))
              \<in> gamma_block (\<Gamma>_tm M)
          \<and> snd (snd (init_buffer (le_tm M) kk
                        :: ('c \<Rightarrow> 'a) \<times> ('c \<Rightarrow> 'a) \<times> ('c \<Rightarrow> 'a)))
              \<in> gamma_block (\<Gamma>_tm M)"
    by (rule init_buffer_in_gamma_block_at_M[OF vM])
  have step: "(Config\<^sub>M (s_tm M, init_offset, init_buffer (le_tm M),
                            init_dest, VFwd) ?ts ?n_k,
                Config\<^sub>M (s_tm M, init_offset, init_buffer (le_tm M),
                            init_dest, VFwd) ?ts
                  (\<lambda>kk. go_dir (if kk = (0 :: nat) then dir.R else dir.N)
                                 (?n_k kk)))
                \<in> mttm_step (alphabet_enlarge_delta M)"
    by (rule ae_step_val_fwd_advance[where ts = ?ts and n = ?n_k,
                                     OF s_in_Q s_neq_t s_neq_r read bt_all
                                        init_stage_tail gamma buf_gamma_init])
  have post_eq:
    "(\<lambda>kk :: nat. go_dir (if kk = 0 then dir.R else dir.N) (?n_k kk)) = ?n_Sk"
    by (rule ext) simp
  have step_n_Sk: "(Config\<^sub>M (s_tm M, init_offset, init_buffer (le_tm M),
                                init_dest, VFwd) ?ts ?n_k,
                    Config\<^sub>M (s_tm M, init_offset, init_buffer (le_tm M),
                                init_dest, VFwd) ?ts ?n_Sk)
                   \<in> mttm_step (alphabet_enlarge_delta M)"
    using step post_eq by simp
  have stage_eq: "init_stage (le_tm M)
                  = (init_offset, init_buffer (le_tm M), init_dest, VFwd)"
    unfolding init_stage_def ..
  have step_init: "(Config\<^sub>M (s_tm M, init_stage (le_tm M)) ?ts ?n_k,
                    Config\<^sub>M (s_tm M, init_stage (le_tm M)) ?ts ?n_Sk)
                   \<in> mttm_step (alphabet_enlarge_delta M)"
    using step_n_Sk unfolding stage_eq by simp
  show ?case by (rule relpow_Suc_I[OF IH step_init])
qed

text \<open>Return-sweep iteration helper.  Symmetric counterpart to
  the forward sweep: starting at \<open>VRet\<close> with the head on tape 0
  at position \<open>p\<close>, retreat to position 0 in \<open>p\<close> applications of
  \<open>ae_step_val_ret_step\<close>, then take one more step via
  \<open>ae_step_val_ret_to_sim\<close> to reach \<open>SS1\<close>.  Total: \<open>Suc p\<close>
  steps.  The non-LE constraint on positions \<open>1\<dots>p\<close> is hoisted
  into the goal as a \<open>\<longrightarrow>\<close>-form so the standard induction on
  \<open>p\<close> exposes the correct restriction at the IH.\<close>

lemma ae_validation_ret_sweep:
  fixes M :: "('q, 'a) mttm"
    and ts :: "nat \<Rightarrow> nat \<Rightarrow> ('c :: enum \<Rightarrow> 'a)"
    and q :: 'q
    and ofs :: "nat \<Rightarrow> 'c"
    and buf :: "nat \<Rightarrow> ('c \<Rightarrow> 'a) \<times> ('c \<Rightarrow> 'a) \<times> ('c \<Rightarrow> 'a)"
    and dest :: "nat \<Rightarrow> ae_dest"
    and p :: nat
  assumes q_in: "q \<in> Q_tm M"
      and tape_le: "ts (0 :: nat) 0 = LE_block (le_tm M)"
      and gamma: "\<forall>k i. ts k i \<in> gamma_block (\<Gamma>_tm M)"
      and buf_gamma: "\<forall>k. fst (buf k) \<in> gamma_block (\<Gamma>_tm M)
                            \<and> fst (snd (buf k)) \<in> gamma_block (\<Gamma>_tm M)
                            \<and> snd (snd (buf k)) \<in> gamma_block (\<Gamma>_tm M)"
      and bt: "\<forall>k\<ge>k_tm M. \<forall>i. ts k i = bl_block (bl_tm M)"
      and stage_tail: "(\<forall>j\<ge>k_tm M. ofs j = init_offset j)
                        \<and> (\<forall>j\<ge>k_tm M. buf j = init_buffer (le_tm M) j)
                        \<and> (\<forall>j\<ge>k_tm M. dest j = init_dest j)"
  shows "(\<forall>i. 1 \<le> i \<and> i \<le> p \<longrightarrow> ts 0 i \<noteq> LE_block (le_tm M))
         \<longrightarrow> (Config\<^sub>M (q, ofs, buf, dest, VRet) ts
                       (\<lambda>i :: nat. if i = 0 then p else 0),
              Config\<^sub>M (q, ofs, buf, dest, SS1) ts (\<lambda>_. 0))
              \<in> mttm_step (alphabet_enlarge_delta M) ^^ Suc p"
proof (induction p)
  case 0
  let ?n0 = "\<lambda>_ :: nat. 0 :: nat"
  have read: "ts (0 :: nat) (?n0 0) = LE_block (le_tm M)"
    using tape_le by simp
  have gamma_at: "\<forall>k :: nat. ts k (?n0 k) \<in> gamma_block (\<Gamma>_tm M)"
    using gamma by simp
  have step1: "(Config\<^sub>M (q, ofs, buf, dest, VRet) ts ?n0,
                 Config\<^sub>M (q, ofs, buf, dest, SS1) ts ?n0)
                \<in> mttm_step (alphabet_enlarge_delta M)"
    by (rule ae_step_val_ret_to_sim[where ts = ts and n = ?n0,
                                    OF q_in read bt stage_tail gamma_at
                                       buf_gamma])
  have shape_eq: "(\<lambda>i :: nat. if i = 0 then (0 :: nat) else 0) = ?n0"
    by (rule ext) simp
  show ?case
  proof
    assume "(\<forall>i. 1 \<le> i \<and> i \<le> 0 \<longrightarrow> ts 0 i \<noteq> LE_block (le_tm M))"
    have one_step: "(Config\<^sub>M (q, ofs, buf, dest, VRet) ts
                       (\<lambda>i :: nat. if i = 0 then 0 else 0),
                     Config\<^sub>M (q, ofs, buf, dest, SS1) ts (\<lambda>_. 0))
                    \<in> mttm_step (alphabet_enlarge_delta M)"
      using step1 shape_eq by simp
    thus "(Config\<^sub>M (q, ofs, buf, dest, VRet) ts
              (\<lambda>i :: nat. if i = 0 then 0 else 0),
            Config\<^sub>M (q, ofs, buf, dest, SS1) ts (\<lambda>_. 0))
            \<in> mttm_step (alphabet_enlarge_delta M) ^^ Suc 0"
      by (simp add: relpow_1)
  qed
next
  case (Suc p)
  let ?n_Sp = "\<lambda>i :: nat. if i = 0 then Suc p else 0"
  let ?n_p = "\<lambda>i :: nat. if i = 0 then p else 0"
  show ?case
  proof
    assume tape_non_le_Sp:
      "(\<forall>i. 1 \<le> i \<and> i \<le> Suc p \<longrightarrow> ts 0 i \<noteq> LE_block (le_tm M))"
    have read_non_le: "ts (0 :: nat) (?n_Sp 0) \<noteq> LE_block (le_tm M)"
      using tape_non_le_Sp[rule_format, of "Suc p"] by simp
    have gamma_Sp: "\<forall>k :: nat. ts k (?n_Sp k) \<in> gamma_block (\<Gamma>_tm M)"
      using gamma by simp
    have step1: "(Config\<^sub>M (q, ofs, buf, dest, VRet) ts ?n_Sp,
                   Config\<^sub>M (q, ofs, buf, dest, VRet) ts
                     (\<lambda>kk. go_dir (if kk = (0 :: nat) then dir.L else dir.N)
                                   (?n_Sp kk)))
                  \<in> mttm_step (alphabet_enlarge_delta M)"
      by (rule ae_step_val_ret_step[where ts = ts and n = ?n_Sp,
                                    OF q_in read_non_le bt stage_tail
                                       gamma_Sp buf_gamma])
    have post_eq:
      "(\<lambda>kk :: nat. go_dir (if kk = 0 then dir.L else dir.N) (?n_Sp kk))
       = ?n_p"
      by (rule ext) simp
    have step1_p: "(Config\<^sub>M (q, ofs, buf, dest, VRet) ts ?n_Sp,
                    Config\<^sub>M (q, ofs, buf, dest, VRet) ts ?n_p)
                   \<in> mttm_step (alphabet_enlarge_delta M)"
      using step1 post_eq by simp
    have tape_non_le_p:
      "\<forall>i. 1 \<le> i \<and> i \<le> p \<longrightarrow> ts 0 i \<noteq> LE_block (le_tm M)"
      using tape_non_le_Sp by auto
    have IH_chain: "(Config\<^sub>M (q, ofs, buf, dest, VRet) ts ?n_p,
                     Config\<^sub>M (q, ofs, buf, dest, SS1) ts (\<lambda>_. 0))
                    \<in> mttm_step (alphabet_enlarge_delta M) ^^ Suc p"
      using Suc.IH tape_non_le_p by blast
    show "(Config\<^sub>M (q, ofs, buf, dest, VRet) ts ?n_Sp,
            Config\<^sub>M (q, ofs, buf, dest, SS1) ts (\<lambda>_. 0))
            \<in> mttm_step (alphabet_enlarge_delta M) ^^ Suc (Suc p)"
      by (rule relpow_Suc_I2[OF step1_p IH_chain])
  qed
qed

text \<open>Partial return sweep: \<open>m\<close> leftward \<open>VRet\<close> steps from head
  \<open>p\<close> reach head \<open>p - m\<close>, staying in \<open>VRet\<close>, provided every visited
  cell \<open>1 \<dots> p\<close> is non-\<open>LE\<close> (so the return never short-circuits to
  \<open>SS1\<close>).  This exposes each intermediate validation config as a
  reachable witness, which the full \<open>ae_validation_ret_sweep\<close> hides
  behind its composed endpoint.  Used by \<open>ae_validation_prefix_markers\<close>
  to supply return-phase witnesses for the prefix-uniqueness induction.\<close>

lemma ae_validation_ret_partial:
  fixes M :: "('q, 'a) mttm"
    and ts :: "nat \<Rightarrow> nat \<Rightarrow> ('c :: enum \<Rightarrow> 'a)"
    and q :: 'q
    and ofs :: "nat \<Rightarrow> 'c"
    and buf :: "nat \<Rightarrow> ('c \<Rightarrow> 'a) \<times> ('c \<Rightarrow> 'a) \<times> ('c \<Rightarrow> 'a)"
    and dest :: "nat \<Rightarrow> ae_dest"
    and p :: nat
  assumes q_in: "q \<in> Q_tm M"
      and gamma: "\<forall>k i. ts k i \<in> gamma_block (\<Gamma>_tm M)"
      and buf_gamma: "\<forall>k. fst (buf k) \<in> gamma_block (\<Gamma>_tm M)
                            \<and> fst (snd (buf k)) \<in> gamma_block (\<Gamma>_tm M)
                            \<and> snd (snd (buf k)) \<in> gamma_block (\<Gamma>_tm M)"
      and bt: "\<forall>k\<ge>k_tm M. \<forall>i. ts k i = bl_block (bl_tm M)"
      and stage_tail: "(\<forall>j\<ge>k_tm M. ofs j = init_offset j)
                        \<and> (\<forall>j\<ge>k_tm M. buf j = init_buffer (le_tm M) j)
                        \<and> (\<forall>j\<ge>k_tm M. dest j = init_dest j)"
      and non_le: "\<forall>i. 1 \<le> i \<and> i \<le> p \<longrightarrow> ts 0 i \<noteq> LE_block (le_tm M)"
  shows "m \<le> p
         \<longrightarrow> (Config\<^sub>M (q, ofs, buf, dest, VRet) ts
                       (\<lambda>i :: nat. if i = 0 then p else 0),
              Config\<^sub>M (q, ofs, buf, dest, VRet) ts
                       (\<lambda>i :: nat. if i = 0 then p - m else 0))
              \<in> mttm_step (alphabet_enlarge_delta M) ^^ m"
proof (induction m)
  case 0
  have eq: "p - 0 = p" by simp
  show ?case unfolding eq by simp
next
  case (Suc m)
  let ?n_pm = "\<lambda>i :: nat. if i = 0 then p - m else 0"
  let ?n_pSm = "\<lambda>i :: nat. if i = 0 then p - Suc m else 0"
  show ?case
  proof
    assume Sm_le: "Suc m \<le> p"
    have m_le: "m \<le> p" using Sm_le by simp
    have pm_pos: "1 \<le> p - m" using Sm_le by simp
    have pm_le: "p - m \<le> p" by simp
    have read_non_le: "ts (0 :: nat) (?n_pm 0) \<noteq> LE_block (le_tm M)"
      using non_le[rule_format, of "p - m"] pm_pos pm_le by simp
    have gamma_pm: "\<forall>k :: nat. ts k (?n_pm k) \<in> gamma_block (\<Gamma>_tm M)"
      using gamma by simp
    have step1: "(Config\<^sub>M (q, ofs, buf, dest, VRet) ts ?n_pm,
                   Config\<^sub>M (q, ofs, buf, dest, VRet) ts
                     (\<lambda>kk. go_dir (if kk = (0 :: nat) then dir.L else dir.N)
                                   (?n_pm kk)))
                  \<in> mttm_step (alphabet_enlarge_delta M)"
      by (rule ae_step_val_ret_step[where ts = ts and n = ?n_pm,
                                    OF q_in read_non_le bt stage_tail
                                       gamma_pm buf_gamma])
    have post_eq:
      "(\<lambda>kk :: nat. go_dir (if kk = 0 then dir.L else dir.N) (?n_pm kk))
       = ?n_pSm"
      using pm_pos by (rule_tac ext) simp
    have step1_pSm:
      "(Config\<^sub>M (q, ofs, buf, dest, VRet) ts ?n_pm,
         Config\<^sub>M (q, ofs, buf, dest, VRet) ts ?n_pSm)
        \<in> mttm_step (alphabet_enlarge_delta M)"
      using step1 post_eq by simp
    have IH_chain:
      "(Config\<^sub>M (q, ofs, buf, dest, VRet) ts
                 (\<lambda>i :: nat. if i = 0 then p else 0),
        Config\<^sub>M (q, ofs, buf, dest, VRet) ts ?n_pm)
        \<in> mttm_step (alphabet_enlarge_delta M) ^^ m"
      using Suc.IH m_le by blast
    show "(Config\<^sub>M (q, ofs, buf, dest, VRet) ts
                    (\<lambda>i :: nat. if i = 0 then p else 0),
           Config\<^sub>M (q, ofs, buf, dest, VRet) ts ?n_pSm)
            \<in> mttm_step (alphabet_enlarge_delta M) ^^ Suc m"
      by (rule relpow_Suc_I[OF IH_chain step1_pSm])
  qed
qed

text \<open>Tape correspondence at the initial configuration: the
  substrate's \<open>init_config\<close> tape (raw input \<open>u\<close>) corresponds to
  the AE-side \<open>ae_init_config\<close> tape (encoded block list
  \<open>encode_input bl_M u\<close>) under \<open>ae_tape_correspondence\<close>.  The
  three position regions match one-to-one:
  \<^item> position \<open>0\<close>: substrate has \<open>LE = le_M\<close>; ae has \<open>LE_block\<close>
    (the correspondence's \<open>tM 0 = le\<close> conjunct);
  \<^item> tape \<open>0\<close>, position \<open>p = (s-1)\<cdot>c + c_idx i + 1 \<le> length u\<close>:
    substrate has \<open>u ! (p-1)\<close>; ae has \<open>encode_input ! (s-1)\<close> at
    offset \<open>i\<close>, which by \<open>encode_input_nth\<close> is \<open>u ! (p-1)\<close>;
  \<^item> any position past the input or any tape \<open>k \<noteq> 0\<close>: both sides
    deliver \<open>bl_M = blank_M\<close>.\<close>
lemma ae_tape_correspondence_init:
  fixes M :: "('q, 'a) mttm"
    and u :: "'a list"
  assumes vM: "valid_mttm M"
      and u_sub: "set u \<subseteq> Sigma_tm M"
  shows "\<forall>k<k_tm M. ae_tape_correspondence (le_tm M)
              (mt_tape (init_config_mttm M u) k)
              (mt_tape (ae_init_config M
                         (encode_input (bl_tm M) u
                              :: ('c :: enum \<Rightarrow> 'a) list)) k)"
proof (intro allI impI)
  fix k :: nat
  assume k_lt: "k < k_tm M"
  have kpos: "0 < k_tm M" using k_lt by linarith
  obtain Q \<Sigma> \<Gamma> bl le \<delta> sM tM r kM where MTTM:
    "M = MTTM Q \<Sigma> \<Gamma> bl le \<delta> sM tM r kM"
    using mttm.exhaust by metis
  let ?w = "encode_input (bl_tm M) u :: ('c :: enum \<Rightarrow> 'a) list"
  let ?c = "card (UNIV :: 'c set)"
  show "ae_tape_correspondence (le_tm M)
          (mt_tape (init_config_mttm M u) k)
          (mt_tape (ae_init_config M ?w) k)"
    unfolding ae_tape_correspondence_def
  proof (intro conjI allI impI)
    show "mt_tape (init_config_mttm M u) k 0 = le_tm M"
      using MTTM k_lt by simp
  next
    fix s :: nat and i :: 'c
    assume s_ge: "1 \<le> s"
    let ?p = "(s - 1) * ?c + c_idx i + 1"
    have p_pos: "?p \<ge> 1" by simp
    show "mt_tape (init_config_mttm M u) k ?p
          = mt_tape (ae_init_config M ?w) k s i"
    proof (cases "k = 0")
      case False
      have subst:
        "mt_tape (init_config_mttm M u) k ?p = bl_tm M"
        using MTTM False p_pos by simp
      have ae:
        "mt_tape (ae_init_config M ?w) k s i = bl_tm M"
        unfolding ae_init_config_def using s_ge False
        by (simp add: bl_block_def)
      show ?thesis using subst ae by simp
    next
      case True
      have k_eq: "k = 0" using True .
      show ?thesis
      proof (cases "?p \<le> length u")
        case False
        have p_gt: "length u < ?p" using False by simp
        have subst_bl:
          "mt_tape (init_config_mttm M u) k ?p = bl_tm M"
          using MTTM k_eq p_pos p_gt by simp
        have ae_bl:
          "mt_tape (ae_init_config M ?w) k s i = bl_tm M"
        proof (cases "s \<le> length ?w")
          case False
          thus ?thesis
            unfolding ae_init_config_def using s_ge k_eq
            by (simp add: bl_block_def)
        next
          case True
          have s_minus_1_lt: "s - 1 < length ?w"
            using True s_ge by simp
          have nth_eq:
            "(?w ! (s - 1)) i =
                (let j = (s - 1) * ?c + c_idx i in
                    if j < length u then u ! j else bl_tm M)"
            by (rule encode_input_nth[OF s_minus_1_lt])
          have j_ge: "(s - 1) * ?c + c_idx i \<ge> length u"
            using p_gt by simp
          have ae_val: "(?w ! (s - 1)) i = bl_tm M"
            using nth_eq j_ge by (simp add: Let_def)
          have ae_lhs:
            "mt_tape (ae_init_config M ?w) k s i = (?w ! (s - 1)) i"
            unfolding ae_init_config_def using s_ge k_eq True kpos by simp
          show ?thesis using ae_lhs ae_val by simp
        qed
        show ?thesis using subst_bl ae_bl by simp
      next
        case True
        have p_le: "?p \<le> length u" using True .
        have subst_val:
          "mt_tape (init_config_mttm M u) k ?p
             = u ! ((s - 1) * ?c + c_idx i)"
          using MTTM k_eq p_pos p_le kpos by simp
        have c_pos: "?c > 0" using c_idx_lt_card[where x = i] by linarith
        have len_w: "length ?w = (length u + ?c - 1) div ?c"
          by (rule length_encode_input)
        have prod_lt: "(s - 1) * ?c < length u"
          using p_le by linarith
        have s_le_len_w: "s \<le> length ?w"
        proof -
          have s_times_c_eq: "s * ?c = (s - 1) * ?c + ?c"
            using s_ge by (auto simp: algebra_simps)
          have step: "s * ?c \<le> length u + ?c - 1"
            using prod_lt c_pos s_times_c_eq by linarith
          have s_div: "s * ?c div ?c = s" using c_pos by simp
          have "s = s * ?c div ?c" using s_div by simp
          also have "\<dots> \<le> (length u + ?c - 1) div ?c"
            using step by (rule div_le_mono)
          finally show ?thesis using len_w by simp
        qed
        have s_minus_1_lt: "s - 1 < length ?w"
          using s_le_len_w s_ge by simp
        have nth_eq:
          "(?w ! (s - 1)) i =
              (let j = (s - 1) * ?c + c_idx i in
                  if j < length u then u ! j else bl_tm M)"
          by (rule encode_input_nth[OF s_minus_1_lt])
        have j_lt: "(s - 1) * ?c + c_idx i < length u"
          using p_le by simp
        have ae_val: "(?w ! (s - 1)) i = u ! ((s - 1) * ?c + c_idx i)"
          using nth_eq j_lt by (simp add: Let_def)
        have ae_lhs:
          "mt_tape (ae_init_config M ?w) k s i = (?w ! (s - 1)) i"
          unfolding ae_init_config_def using s_ge k_eq s_le_len_w kpos
          by simp
        show ?thesis using subst_val ae_lhs ae_val by simp
      qed
    qed
  qed
qed

subsubsection \<open>Validation post-state and step count\<close>

text \<open>Well-formed inputs (without \<open>bl_block\<close>) drive the validation
  chain to the explicit SS1 boundary configuration.  Extracted from
  the well-formed branch of \<open>ae_validation_steps_bound\<close> so that
  \<open>ae_validation_post_state_canonical\<close> can use the same chain to
  prove the simulation against the substrate's \<open>init_config\<close>
  (the steps-bound lemma's \<open>obtains\<close> form discards the explicit
  final config).

  This is the narrower companion of the general step-count form
  \<open>ae_validation_phase_step_count\<close> in theory
  \<open>AlphabetEnlargement\<close>: it gives the exact length
  \<open>2 \<cdot> |w| + 4\<close> with SS1 as the only outcome under the
  stronger precondition \<open>ae_input_well_formed (bl_tm M) w\<close>,
  whereas the general form gives an existential bound
  \<open>n \<le> 2 \<cdot> |w| + f\<^sub>v\<close> with SS1-or-reject outcomes
  for any input (well-formed or not).  The linear-speedup proof
  uses this canonical form, applied via
  \<open>encode_input_well_formed\<close> to explicit encoder-image
  inputs.\<close>
lemma ae_validation_well_formed_to_SS1:
  fixes M :: "('q, 'a) mttm"
    and w :: "('c :: enum \<Rightarrow> 'a) list"
  assumes vM: "valid_mttm M"
      and w_sub: "set w \<subseteq> gamma_block (Sigma_tm M \<union> {bl_tm M})"
      and wf: "ae_input_well_formed (bl_tm M) w"
      and s_in_Q: "s_tm M \<in> Q_tm M"
      and s_neq_t: "s_tm M \<noteq> t_tm M"
      and s_neq_r: "s_tm M \<noteq> r_tm M"
      and le_neq_bl: "le_tm M \<noteq> bl_tm M"
  shows "(ae_init_config M w,
          Config\<^sub>M (s_tm M, init_offset, init_buffer (le_tm M),
                     init_dest, SS1)
                   (mt_tape (ae_init_config M w)) (\<lambda>_. 0))
            \<in> mttm_step (alphabet_enlarge_delta M) ^^ (2 * length w + 4)"
proof -
  let ?init = "ae_init_config M w"
  let ?ts = "mt_tape ?init"
  have kpos: "0 < k_tm M" by (rule valid_mttm_k_pos[OF vM])
  have bt_all: "\<forall>j\<ge>k_tm M. \<forall>i. ?ts j i = bl_block (bl_tm M)"
    using ae_init_config_tape_blank_tail by blast
  have buf_gamma_init:
      "\<forall>kk :: nat.
          fst (init_buffer (le_tm M) kk
                  :: ('c \<Rightarrow> 'a) \<times> ('c \<Rightarrow> 'a) \<times> ('c \<Rightarrow> 'a))
              \<in> gamma_block (\<Gamma>_tm M)
          \<and> fst (snd (init_buffer (le_tm M) kk
                        :: ('c \<Rightarrow> 'a) \<times> ('c \<Rightarrow> 'a) \<times> ('c \<Rightarrow> 'a)))
              \<in> gamma_block (\<Gamma>_tm M)
          \<and> snd (snd (init_buffer (le_tm M) kk
                        :: ('c \<Rightarrow> 'a) \<times> ('c \<Rightarrow> 'a) \<times> ('c \<Rightarrow> 'a)))
              \<in> gamma_block (\<Gamma>_tm M)"
    by (rule init_buffer_in_gamma_block_at_M[OF vM])
  have LE_neq_bl_block: "LE_block (le_tm M) \<noteq> bl_block (bl_tm M)"
    using le_neq_bl unfolding LE_block_def bl_block_def
    by (metis fun_eq_iff)
  have LE_notin: "LE_block (le_tm M) \<notin> set w"
  proof -
    have le_notin: "le_tm M \<notin> Sigma_tm M \<union> {bl_tm M}"
      using valid_mttm_LE_not_Sigma[OF vM] le_neq_bl by auto
    have "LE_block (le_tm M) \<notin> gamma_block (Sigma_tm M \<union> {bl_tm M})"
      using le_notin
      unfolding LE_block_def gamma_block_def by auto
    thus ?thesis using w_sub by auto
  qed
  \<comment> \<open>Determine whether all w-cells are pure or the last is padded.\<close>
  have all_pure_or_last_padded:
    "(\<forall>i < length w. is_pure_block (bl_tm M) (w ! i))
     \<or> (0 < length w
          \<and> (\<forall>i < length w - 1. is_pure_block (bl_tm M) (w ! i))
          \<and> is_padded_block (bl_tm M) (w ! (length w - 1)))"
  proof (cases "length w = 0")
    case True
    thus ?thesis by simp
  next
    case False
    hence wpos: "0 < length w" by simp
    show ?thesis
    proof (cases "is_pure_block (bl_tm M) (w ! (length w - 1))")
      case True
      have "\<forall>i < length w. is_pure_block (bl_tm M) (w ! i)"
      proof (intro allI impI)
        fix i assume i_lt: "i < length w"
        have "is_pure_block (bl_tm M) (w ! i)
              \<or> (i = length w - 1
                 \<and> is_padded_block (bl_tm M) (w ! i))"
          using wf i_lt unfolding ae_input_well_formed_def by auto
        thus "is_pure_block (bl_tm M) (w ! i)"
          using True by auto
      qed
      thus ?thesis by simp
    next
      case False
      have last_padded: "is_padded_block (bl_tm M) (w ! (length w - 1))"
      proof -
        have idx_lt: "length w - 1 < length w" using wpos by linarith
        have or_form: "is_pure_block (bl_tm M) (w ! (length w - 1))
              \<or> (length w - 1 = length w - 1
                 \<and> is_padded_block (bl_tm M) (w ! (length w - 1)))"
          using wf idx_lt unfolding ae_input_well_formed_def by blast
        thus ?thesis using False by auto
      qed
      have prefix_pure: "\<forall>i < length w - 1. is_pure_block (bl_tm M) (w ! i)"
      proof (intro allI impI)
        fix i assume i_lt: "i < length w - 1"
        hence i_lt2: "i < length w" using wpos by linarith
        have "is_pure_block (bl_tm M) (w ! i)
              \<or> (i = length w - 1
                 \<and> is_padded_block (bl_tm M) (w ! i))"
          using wf i_lt2 unfolding ae_input_well_formed_def by auto
        thus "is_pure_block (bl_tm M) (w ! i)" using i_lt by auto
      qed
      show ?thesis using wpos prefix_pure last_padded by blast
    qed
  qed
  have tape_le: "?ts (0 :: nat) 0 = LE_block (le_tm M)"
    by (rule ae_init_config_tape_le[OF kpos])
  have gamma_all: "\<forall>k i. ?ts k i \<in> gamma_block (\<Gamma>_tm M)"
    using ae_init_config_in_gamma_block[OF vM w_sub] by simp
  have stage_eq: "init_stage (le_tm M)
                  = (init_offset, init_buffer (le_tm M), init_dest, VFwd)"
    unfolding init_stage_def ..
  \<comment> \<open>Verify positions \<open>1\<dots>Suc (length w)\<close> on tape 0 are non-LE
      (from \<open>LE_notin\<close> for input positions; from
      \<open>LE_neq_bl_block\<close> for the blank tail).\<close>
  have non_le: "\<forall>i. 1 \<le> i \<and> i \<le> Suc (length w)
                     \<longrightarrow> ?ts 0 i \<noteq> LE_block (le_tm M)"
  proof (intro allI impI)
    fix i assume i_range: "1 \<le> i \<and> i \<le> Suc (length w)"
    have i_pos: "1 \<le> i" using i_range by simp
    consider (in_input) "i \<le> length w" | (past) "i = Suc (length w)"
      using i_range by linarith
    thus "?ts 0 i \<noteq> LE_block (le_tm M)"
    proof cases
      case in_input
      have eq: "?ts 0 i = w ! (i - 1)"
        using ae_init_config_tape_input[OF i_pos in_input kpos] by simp
      have "w ! (i - 1) \<in> set w" using i_pos in_input by auto
      thus ?thesis using LE_notin eq by auto
    next
      case past
      have ineq: "length w < i" using past by simp
      have eq: "?ts 0 i = bl_block (bl_tm M)"
        by (rule ae_init_config_tape_blank_after_input[OF ineq])
      have "LE_block (le_tm M) \<noteq> bl_block (bl_tm M)"
        by (rule LE_neq_bl_block)
      thus ?thesis using eq by force
    qed
  qed
  from all_pure_or_last_padded consider
      (all_pure) "\<forall>i < length w. is_pure_block (bl_tm M) (w ! i)"
    | (last_padded) "0 < length w"
                     "\<forall>i < length w - 1. is_pure_block (bl_tm M) (w ! i)"
                     "is_padded_block (bl_tm M) (w ! (length w - 1))"
    by blast
  thus ?thesis
  proof cases
    case all_pure
    let ?n_lwSS = "\<lambda>i :: nat. if i = 0 then Suc (length w) else 0"
    have lw_le: "length w \<le> length w" by simp
    have sweep:
      "(?init,
          Config\<^sub>M (s_tm M, init_stage (le_tm M)) ?ts ?n_lwSS)
          \<in> mttm_step (alphabet_enlarge_delta M) ^^ Suc (length w)"
      by (rule ae_validation_fwd_sweep_pure[OF vM w_sub s_in_Q s_neq_t
                                              s_neq_r lw_le all_pure])
    have lw_gt: "Suc (length w) > length w" by simp
    have read_bl: "?ts 0 (?n_lwSS 0) = bl_block (bl_tm M)"
      using ae_init_config_tape_blank_after_input[OF lw_gt] by simp
    have gamma_lwSS:
      "\<forall>kk :: nat. ?ts kk (?n_lwSS kk) \<in> gamma_block (\<Gamma>_tm M)"
      using gamma_all by simp
    have step_to_ret:
      "(Config\<^sub>M (s_tm M, init_offset, init_buffer (le_tm M),
                    init_dest, VFwd) ?ts ?n_lwSS,
         Config\<^sub>M (s_tm M, init_offset, init_buffer (le_tm M),
                    init_dest, VRet) ?ts ?n_lwSS)
          \<in> mttm_step (alphabet_enlarge_delta M)"
      by (rule ae_step_val_fwd_to_ret[where ts = ?ts and n = ?n_lwSS,
            OF s_in_Q s_neq_t s_neq_r read_bl bt_all init_stage_tail
               gamma_lwSS buf_gamma_init])
    have step_to_ret_init:
      "(Config\<^sub>M (s_tm M, init_stage (le_tm M)) ?ts ?n_lwSS,
         Config\<^sub>M (s_tm M, init_offset, init_buffer (le_tm M),
                    init_dest, VRet) ?ts ?n_lwSS)
          \<in> mttm_step (alphabet_enlarge_delta M)"
      using step_to_ret unfolding stage_eq by simp
    have post_sweep:
      "(?init,
         Config\<^sub>M (s_tm M, init_offset, init_buffer (le_tm M),
                    init_dest, VRet) ?ts ?n_lwSS)
          \<in> mttm_step (alphabet_enlarge_delta M) ^^ Suc (Suc (length w))"
      by (rule relpow_Suc_I[OF sweep step_to_ret_init])
    have ret_arrow:
      "(\<forall>i. 1 \<le> i \<and> i \<le> Suc (length w)
            \<longrightarrow> ?ts 0 i \<noteq> LE_block (le_tm M))
       \<longrightarrow> (Config\<^sub>M (s_tm M, init_offset, init_buffer (le_tm M),
                        init_dest, VRet) ?ts ?n_lwSS,
            Config\<^sub>M (s_tm M, init_offset, init_buffer (le_tm M),
                        init_dest, SS1) ?ts (\<lambda>_. 0))
            \<in> mttm_step (alphabet_enlarge_delta M)
                ^^ Suc (Suc (length w))"
      by (rule ae_validation_ret_sweep[OF s_in_Q tape_le gamma_all
                                          buf_gamma_init bt_all init_stage_tail])
    have ret_chain:
      "(Config\<^sub>M (s_tm M, init_offset, init_buffer (le_tm M),
                    init_dest, VRet) ?ts ?n_lwSS,
         Config\<^sub>M (s_tm M, init_offset, init_buffer (le_tm M),
                    init_dest, SS1) ?ts (\<lambda>_. 0))
          \<in> mttm_step (alphabet_enlarge_delta M)
              ^^ Suc (Suc (length w))"
      using ret_arrow non_le by (rule mp)
    have full_chain_pre:
      "(?init,
         Config\<^sub>M (s_tm M, init_offset, init_buffer (le_tm M),
                    init_dest, SS1) ?ts (\<lambda>_. 0))
          \<in> mttm_step (alphabet_enlarge_delta M)
              ^^ (Suc (Suc (length w)) + Suc (Suc (length w)))"
    proof -
      have comp:
        "(?init,
           Config\<^sub>M (s_tm M, init_offset, init_buffer (le_tm M),
                      init_dest, SS1) ?ts (\<lambda>_. 0))
            \<in> mttm_step (alphabet_enlarge_delta M)
                ^^ Suc (Suc (length w))
              O mttm_step (alphabet_enlarge_delta M)
                ^^ Suc (Suc (length w))"
        using post_sweep ret_chain by (rule relcompI)
      thus ?thesis by (simp only: relpow_add)
    qed
    have total_eq:
      "Suc (Suc (length w)) + Suc (Suc (length w)) = 2 * length w + 4"
      by simp
    have full_chain:
      "(?init,
         Config\<^sub>M (s_tm M, init_offset, init_buffer (le_tm M),
                    init_dest, SS1) ?ts (\<lambda>_. 0))
          \<in> mttm_step (alphabet_enlarge_delta M)
              ^^ (2 * length w + 4)"
      using full_chain_pre unfolding total_eq .
    show ?thesis using full_chain .
  next
    case last_padded
    let ?lw = "length w"
    let ?lwm1 = "length w - 1"
    let ?n_lw = "\<lambda>i :: nat. if i = 0 then ?lw else 0"
    let ?n_lwSS = "\<lambda>i :: nat. if i = 0 then Suc ?lw else 0"
    have wpos: "0 < ?lw" using last_padded(1) .
    have m1_le: "?lwm1 \<le> ?lw" by simp
    have prefix_pure: "\<forall>i < ?lwm1. is_pure_block (bl_tm M) (w ! i)"
      using last_padded(2) .
    have sweep:
      "(?init,
          Config\<^sub>M (s_tm M, init_stage (le_tm M)) ?ts
                   (\<lambda>i :: nat. if i = 0 then Suc ?lwm1 else 0))
          \<in> mttm_step (alphabet_enlarge_delta M) ^^ Suc ?lwm1"
      by (rule ae_validation_fwd_sweep_pure[OF vM w_sub s_in_Q s_neq_t
                                              s_neq_r m1_le prefix_pure])
    have suc_m1_eq: "Suc ?lwm1 = ?lw" using wpos by simp
    have sweep_lw:
      "(?init,
          Config\<^sub>M (s_tm M, init_stage (le_tm M)) ?ts ?n_lw)
          \<in> mttm_step (alphabet_enlarge_delta M) ^^ ?lw"
      using sweep unfolding suc_m1_eq .
    have lw_pos: "1 \<le> ?lw" using wpos by linarith
    have lw_le: "?lw \<le> ?lw" by simp
    have read_at_lw_eq: "?ts 0 ?lw = w ! ?lwm1"
      using ae_init_config_tape_input[OF lw_pos lw_le kpos] by simp
    have read_padded:
      "is_padded_block (bl_tm M) (?ts 0 (?n_lw 0))"
      using read_at_lw_eq last_padded(3) by simp
    have gamma_lw:
      "\<forall>kk :: nat. ?ts kk (?n_lw kk) \<in> gamma_block (\<Gamma>_tm M)"
      using gamma_all by simp
    have step_to_pad:
      "(Config\<^sub>M (s_tm M, init_offset, init_buffer (le_tm M),
                    init_dest, VFwd) ?ts ?n_lw,
         Config\<^sub>M (s_tm M, init_offset, init_buffer (le_tm M),
                    init_dest, VFwdPad) ?ts
                (\<lambda>kk. go_dir (if kk = (0 :: nat) then dir.R else dir.N)
                               (?n_lw kk)))
          \<in> mttm_step (alphabet_enlarge_delta M)"
      by (rule ae_step_val_fwd_to_padded[where ts = ?ts and n = ?n_lw,
            OF s_in_Q s_neq_t s_neq_r read_padded bt_all init_stage_tail
               gamma_lw buf_gamma_init])
    have post_eq_pad:
      "(\<lambda>kk :: nat. go_dir (if kk = 0 then dir.R else dir.N) (?n_lw kk))
       = ?n_lwSS"
      by (rule ext) simp
    have step_to_pad_norm:
      "(Config\<^sub>M (s_tm M, init_offset, init_buffer (le_tm M),
                    init_dest, VFwd) ?ts ?n_lw,
         Config\<^sub>M (s_tm M, init_offset, init_buffer (le_tm M),
                    init_dest, VFwdPad) ?ts ?n_lwSS)
          \<in> mttm_step (alphabet_enlarge_delta M)"
      using step_to_pad post_eq_pad by simp
    have step_to_pad_init:
      "(Config\<^sub>M (s_tm M, init_stage (le_tm M)) ?ts ?n_lw,
         Config\<^sub>M (s_tm M, init_offset, init_buffer (le_tm M),
                    init_dest, VFwdPad) ?ts ?n_lwSS)
          \<in> mttm_step (alphabet_enlarge_delta M)"
      using step_to_pad_norm unfolding stage_eq by simp
    have lw_gt: "Suc ?lw > ?lw" by simp
    have read_bl_lwSS: "?ts 0 (?n_lwSS 0) = bl_block (bl_tm M)"
      using ae_init_config_tape_blank_after_input[OF lw_gt] by simp
    have gamma_lwSS:
      "\<forall>kk :: nat. ?ts kk (?n_lwSS kk) \<in> gamma_block (\<Gamma>_tm M)"
      using gamma_all by simp
    have step_pad_to_ret:
      "(Config\<^sub>M (s_tm M, init_offset, init_buffer (le_tm M),
                    init_dest, VFwdPad) ?ts ?n_lwSS,
         Config\<^sub>M (s_tm M, init_offset, init_buffer (le_tm M),
                    init_dest, VRet) ?ts ?n_lwSS)
          \<in> mttm_step (alphabet_enlarge_delta M)"
      by (rule ae_step_val_pad_to_ret[where ts = ?ts and n = ?n_lwSS,
            OF s_in_Q read_bl_lwSS bt_all init_stage_tail
               gamma_lwSS buf_gamma_init])
    have chain_lw_to_VFwdPad:
      "(?init,
         Config\<^sub>M (s_tm M, init_offset, init_buffer (le_tm M),
                    init_dest, VFwdPad) ?ts ?n_lwSS)
          \<in> mttm_step (alphabet_enlarge_delta M) ^^ Suc ?lw"
      by (rule relpow_Suc_I[OF sweep_lw step_to_pad_init])
    have chain_to_VRet:
      "(?init,
         Config\<^sub>M (s_tm M, init_offset, init_buffer (le_tm M),
                    init_dest, VRet) ?ts ?n_lwSS)
          \<in> mttm_step (alphabet_enlarge_delta M) ^^ Suc (Suc ?lw)"
      by (rule relpow_Suc_I[OF chain_lw_to_VFwdPad step_pad_to_ret])
    have ret_arrow:
      "(\<forall>i. 1 \<le> i \<and> i \<le> Suc ?lw
            \<longrightarrow> ?ts 0 i \<noteq> LE_block (le_tm M))
       \<longrightarrow> (Config\<^sub>M (s_tm M, init_offset, init_buffer (le_tm M),
                        init_dest, VRet) ?ts ?n_lwSS,
            Config\<^sub>M (s_tm M, init_offset, init_buffer (le_tm M),
                        init_dest, SS1) ?ts (\<lambda>_. 0))
            \<in> mttm_step (alphabet_enlarge_delta M)
                ^^ Suc (Suc ?lw)"
      by (rule ae_validation_ret_sweep[OF s_in_Q tape_le gamma_all
                                          buf_gamma_init bt_all init_stage_tail])
    have ret_chain:
      "(Config\<^sub>M (s_tm M, init_offset, init_buffer (le_tm M),
                    init_dest, VRet) ?ts ?n_lwSS,
         Config\<^sub>M (s_tm M, init_offset, init_buffer (le_tm M),
                    init_dest, SS1) ?ts (\<lambda>_. 0))
          \<in> mttm_step (alphabet_enlarge_delta M)
              ^^ Suc (Suc ?lw)"
      using ret_arrow non_le by (rule mp)
    have full_chain_pre:
      "(?init,
         Config\<^sub>M (s_tm M, init_offset, init_buffer (le_tm M),
                    init_dest, SS1) ?ts (\<lambda>_. 0))
          \<in> mttm_step (alphabet_enlarge_delta M)
              ^^ (Suc (Suc ?lw) + Suc (Suc ?lw))"
    proof -
      have comp:
        "(?init,
           Config\<^sub>M (s_tm M, init_offset, init_buffer (le_tm M),
                      init_dest, SS1) ?ts (\<lambda>_. 0))
            \<in> mttm_step (alphabet_enlarge_delta M)
                ^^ Suc (Suc ?lw)
              O mttm_step (alphabet_enlarge_delta M)
                ^^ Suc (Suc ?lw)"
        using chain_to_VRet ret_chain by (rule relcompI)
      thus ?thesis by (simp only: relpow_add)
    qed
    have total_eq:
      "Suc (Suc ?lw) + Suc (Suc ?lw) = 2 * ?lw + 4"
      by simp
    have full_chain:
      "(?init,
         Config\<^sub>M (s_tm M, init_offset, init_buffer (le_tm M),
                    init_dest, SS1) ?ts (\<lambda>_. 0))
          \<in> mttm_step (alphabet_enlarge_delta M)
              ^^ (2 * ?lw + 4)"
      using full_chain_pre unfolding total_eq .
    show ?thesis using full_chain .
  qed
qed

text \<open>Every prefix of the validation run carries a \<^emph>\<open>marker\<close>
  witness: a config reachable in exactly \<open>i\<close> steps whose stage index
  is one of \<open>VFwd\<close> / \<open>VFwdPad\<close> / \<open>VRet\<close> (i.e.\ still inside the
  validation sweep, not yet at \<open>SS1\<close> nor rejected), for every
  \<open>i < 2 * length w + 4\<close>.  Forward witnesses for \<open>i \<le> length w\<close>
  come from \<open>ae_validation_fwd_sweep_pure\<close> at parameter \<open>i - 1\<close>;
  the boundary slot \<open>i = Suc (length w)\<close> is \<open>VFwd\<close> (all-pure) or
  \<open>VFwdPad\<close> (last-padded); return witnesses come from the partial
  return sweep.  This is the witness half of the prefix-uniqueness
  argument in \<open>ae_validation_prefix_markers\<close>.\<close>

lemma ae_validation_prefix_witnesses:
  fixes M :: "('q, 'a) mttm"
    and w :: "('c :: enum \<Rightarrow> 'a) list"
  assumes vM: "valid_mttm M"
      and w_sub: "set w \<subseteq> gamma_block (Sigma_tm M \<union> {bl_tm M})"
      and wf: "ae_input_well_formed (bl_tm M) w"
      and s_in_Q: "s_tm M \<in> Q_tm M"
      and s_neq_t: "s_tm M \<noteq> t_tm M"
      and s_neq_r: "s_tm M \<noteq> r_tm M"
      and le_neq_bl: "le_tm M \<noteq> bl_tm M"
  shows "\<forall>i<2 * length w + 4. \<exists>d.
            (ae_init_config M w, d)
                \<in> mttm_step (alphabet_enlarge_delta M) ^^ i
              \<and> snd (snd (snd (snd (mt_state d))))
                    \<in> {VFwd, VFwdPad, VRet}"
proof -
  let ?init = "ae_init_config M w"
  let ?ts = "mt_tape ?init"
  let ?R = "mttm_step (alphabet_enlarge_delta M)"
  let ?lw = "length w"
  let ?vfwd = "\<lambda>h :: nat. Config\<^sub>M (s_tm M, init_offset,
                  init_buffer (le_tm M), init_dest, VFwd) ?ts
                  (\<lambda>i :: nat. if i = 0 then h else 0)"
  let ?vret = "\<lambda>h :: nat. Config\<^sub>M (s_tm M, init_offset,
                  init_buffer (le_tm M), init_dest, VRet) ?ts
                  (\<lambda>i :: nat. if i = 0 then h else 0)"
  let ?vpad = "\<lambda>h :: nat. Config\<^sub>M (s_tm M, init_offset,
                  init_buffer (le_tm M), init_dest, VFwdPad) ?ts
                  (\<lambda>i :: nat. if i = 0 then h else 0)"
  have kpos: "0 < k_tm M" by (rule valid_mttm_k_pos[OF vM])
  have bt_all: "\<forall>j\<ge>k_tm M. \<forall>i. ?ts j i = bl_block (bl_tm M)"
    using ae_init_config_tape_blank_tail by blast
  have buf_gamma_init:
      "\<forall>kk :: nat.
          fst (init_buffer (le_tm M) kk
                  :: ('c \<Rightarrow> 'a) \<times> ('c \<Rightarrow> 'a) \<times> ('c \<Rightarrow> 'a))
              \<in> gamma_block (\<Gamma>_tm M)
          \<and> fst (snd (init_buffer (le_tm M) kk
                        :: ('c \<Rightarrow> 'a) \<times> ('c \<Rightarrow> 'a) \<times> ('c \<Rightarrow> 'a)))
              \<in> gamma_block (\<Gamma>_tm M)
          \<and> snd (snd (init_buffer (le_tm M) kk
                        :: ('c \<Rightarrow> 'a) \<times> ('c \<Rightarrow> 'a) \<times> ('c \<Rightarrow> 'a)))
              \<in> gamma_block (\<Gamma>_tm M)"
    by (rule init_buffer_in_gamma_block_at_M[OF vM])
  have LE_neq_bl_block: "LE_block (le_tm M) \<noteq> bl_block (bl_tm M)"
    using le_neq_bl unfolding LE_block_def bl_block_def
    by (metis fun_eq_iff)
  have LE_notin: "LE_block (le_tm M) \<notin> set w"
  proof -
    have le_notin: "le_tm M \<notin> Sigma_tm M \<union> {bl_tm M}"
      using valid_mttm_LE_not_Sigma[OF vM] le_neq_bl by auto
    have "LE_block (le_tm M) \<notin> gamma_block (Sigma_tm M \<union> {bl_tm M})"
      using le_notin unfolding LE_block_def gamma_block_def by auto
    thus ?thesis using w_sub by auto
  qed
  have tape_le: "?ts (0 :: nat) 0 = LE_block (le_tm M)"
    by (rule ae_init_config_tape_le[OF kpos])
  have gamma_all: "\<forall>k i. ?ts k i \<in> gamma_block (\<Gamma>_tm M)"
    using ae_init_config_in_gamma_block[OF vM w_sub] by simp
  have stage_eq: "init_stage (le_tm M)
                  = (init_offset, init_buffer (le_tm M), init_dest, VFwd)"
    unfolding init_stage_def ..
  have non_le_Slw: "\<forall>i. 1 \<le> i \<and> i \<le> Suc ?lw
                       \<longrightarrow> ?ts 0 i \<noteq> LE_block (le_tm M)"
  proof (intro allI impI)
    fix i assume i_range: "1 \<le> i \<and> i \<le> Suc ?lw"
    have i_pos: "1 \<le> i" using i_range by simp
    consider (in_input) "i \<le> ?lw" | (past) "i = Suc ?lw"
      using i_range by linarith
    thus "?ts 0 i \<noteq> LE_block (le_tm M)"
    proof cases
      case in_input
      have eq: "?ts 0 i = w ! (i - 1)"
        using ae_init_config_tape_input[OF i_pos in_input kpos] by simp
      have "w ! (i - 1) \<in> set w" using i_pos in_input by auto
      thus ?thesis using LE_notin eq by auto
    next
      case past
      have ineq: "?lw < i" using past by simp
      have eq: "?ts 0 i = bl_block (bl_tm M)"
        by (rule ae_init_config_tape_blank_after_input[OF ineq])
      thus ?thesis using LE_neq_bl_block by force
    qed
  qed
  \<comment> \<open>Forward witnesses for \<open>i \<le> length w\<close>, uniformly (the
      pure-prefix \<open>\<forall>j < i-1\<close> holds for any well-formed input).\<close>
  have vfwd_wit: "\<And>i. i \<le> ?lw \<Longrightarrow> (?init, ?vfwd i) \<in> ?R ^^ i"
  proof -
    fix i assume i_le: "i \<le> ?lw"
    show "(?init, ?vfwd i) \<in> ?R ^^ i"
    proof (cases "i = 0")
      case True
      have head0: "(\<lambda>i :: nat. if i = 0 then 0 else (0 :: nat)) = (\<lambda>_. 0)"
        by simp
      have eq0: "?vfwd 0 = ?init"
        unfolding ae_init_config_def init_stage_def head0 by simp
      have "(?init, ?vfwd 0) \<in> ?R ^^ 0" using eq0 relpow_0_I by metis
      thus ?thesis unfolding True .
    next
      case False
      hence i_pos: "1 \<le> i" by simp
      have k_le: "i - 1 \<le> ?lw" using i_le by simp
      have pure_short: "\<forall>j < i - 1. is_pure_block (bl_tm M) (w ! j)"
      proof (intro allI impI)
        fix j assume j_lt: "j < i - 1"
        have j_lt_lw: "j < ?lw" using j_lt i_le by linarith
        have j_neq: "j \<noteq> ?lw - 1" using j_lt i_le by linarith
        have "is_pure_block (bl_tm M) (w ! j)
              \<or> (j = ?lw - 1 \<and> is_padded_block (bl_tm M) (w ! j))"
          using wf j_lt_lw unfolding ae_input_well_formed_def by auto
        thus "is_pure_block (bl_tm M) (w ! j)" using j_neq by auto
      qed
      have sweep:
        "(?init, Config\<^sub>M (s_tm M, init_stage (le_tm M)) ?ts
                          (\<lambda>j :: nat. if j = 0 then Suc (i - 1) else 0))
            \<in> ?R ^^ Suc (i - 1)"
        by (rule ae_validation_fwd_sweep_pure[OF vM w_sub s_in_Q s_neq_t
                                                s_neq_r k_le pure_short])
      have suci: "Suc (i - 1) = i" using i_pos by simp
      show ?thesis using sweep unfolding suci stage_eq by simp
    qed
  qed
  \<comment> \<open>Classify the input: all blocks pure, or the last padded.\<close>
  have all_pure_or_last_padded:
    "(\<forall>i < ?lw. is_pure_block (bl_tm M) (w ! i))
     \<or> (0 < ?lw
          \<and> (\<forall>i < ?lw - 1. is_pure_block (bl_tm M) (w ! i))
          \<and> is_padded_block (bl_tm M) (w ! (?lw - 1)))"
  proof (cases "?lw = 0")
    case True thus ?thesis by simp
  next
    case False
    hence wpos: "0 < ?lw" by simp
    show ?thesis
    proof (cases "is_pure_block (bl_tm M) (w ! (?lw - 1))")
      case True
      have "\<forall>i < ?lw. is_pure_block (bl_tm M) (w ! i)"
      proof (intro allI impI)
        fix i assume i_lt: "i < ?lw"
        have "is_pure_block (bl_tm M) (w ! i)
              \<or> (i = ?lw - 1 \<and> is_padded_block (bl_tm M) (w ! i))"
          using wf i_lt unfolding ae_input_well_formed_def by auto
        thus "is_pure_block (bl_tm M) (w ! i)" using True by auto
      qed
      thus ?thesis by simp
    next
      case False
      have last_padded: "is_padded_block (bl_tm M) (w ! (?lw - 1))"
      proof -
        have idx_lt: "?lw - 1 < ?lw" using wpos by linarith
        have "is_pure_block (bl_tm M) (w ! (?lw - 1))
              \<or> (?lw - 1 = ?lw - 1
                 \<and> is_padded_block (bl_tm M) (w ! (?lw - 1)))"
          using wf idx_lt unfolding ae_input_well_formed_def by blast
        thus ?thesis using False by auto
      qed
      have prefix_pure: "\<forall>i < ?lw - 1. is_pure_block (bl_tm M) (w ! i)"
      proof (intro allI impI)
        fix i assume i_lt: "i < ?lw - 1"
        hence i_lt2: "i < ?lw" using wpos by linarith
        have "is_pure_block (bl_tm M) (w ! i)
              \<or> (i = ?lw - 1 \<and> is_padded_block (bl_tm M) (w ! i))"
          using wf i_lt2 unfolding ae_input_well_formed_def by auto
        thus "is_pure_block (bl_tm M) (w ! i)" using i_lt by auto
      qed
      show ?thesis using wpos prefix_pure last_padded by blast
    qed
  qed
  \<comment> \<open>Boundary witness at step \<open>Suc (length w)\<close>: \<open>VFwd\<close> head
      \<open>Suc lw\<close> (all-pure) or \<open>VFwdPad\<close> head \<open>Suc lw\<close> (last-padded).\<close>
  have boundary_wit: "\<exists>d. (?init, d) \<in> ?R ^^ Suc ?lw
            \<and> snd (snd (snd (snd (mt_state d)))) \<in> {VFwd, VFwdPad, VRet}"
  proof -
    from all_pure_or_last_padded consider
        (all_pure) "\<forall>i < ?lw. is_pure_block (bl_tm M) (w ! i)"
      | (last_padded) "0 < ?lw"
                       "\<forall>i < ?lw - 1. is_pure_block (bl_tm M) (w ! i)"
                       "is_padded_block (bl_tm M) (w ! (?lw - 1))"
      by blast
    thus ?thesis
    proof cases
      case all_pure
      have lw_le: "?lw \<le> ?lw" by simp
      have sweep:
        "(?init, Config\<^sub>M (s_tm M, init_stage (le_tm M)) ?ts
                          (\<lambda>i :: nat. if i = 0 then Suc ?lw else 0))
            \<in> ?R ^^ Suc ?lw"
        by (rule ae_validation_fwd_sweep_pure[OF vM w_sub s_in_Q s_neq_t
                                                s_neq_r lw_le all_pure])
      have reach: "(?init, ?vfwd (Suc ?lw)) \<in> ?R ^^ Suc ?lw"
        using sweep unfolding stage_eq by simp
      have "snd (snd (snd (snd (mt_state (?vfwd (Suc ?lw))))))
              \<in> {VFwd, VFwdPad, VRet}" by simp
      thus ?thesis using reach by blast
    next
      case last_padded
      let ?n_lw = "\<lambda>i :: nat. if i = 0 then ?lw else 0"
      have wpos: "0 < ?lw" using last_padded(1) .
      have m1_le: "?lw - 1 \<le> ?lw" by simp
      have sweep:
        "(?init, Config\<^sub>M (s_tm M, init_stage (le_tm M)) ?ts
                   (\<lambda>i :: nat. if i = 0 then Suc (?lw - 1) else 0))
            \<in> ?R ^^ Suc (?lw - 1)"
        by (rule ae_validation_fwd_sweep_pure[OF vM w_sub s_in_Q s_neq_t
                                                s_neq_r m1_le last_padded(2)])
      have suc_m1_eq: "Suc (?lw - 1) = ?lw" using wpos by simp
      have sweep_lw: "(?init, ?vfwd ?lw) \<in> ?R ^^ ?lw"
        using sweep unfolding suc_m1_eq stage_eq by simp
      have lw_pos: "1 \<le> ?lw" using wpos by linarith
      have lw_le: "?lw \<le> ?lw" by simp
      have read_at_lw_eq: "?ts 0 ?lw = w ! (?lw - 1)"
        using ae_init_config_tape_input[OF lw_pos lw_le kpos] by simp
      have read_padded: "is_padded_block (bl_tm M) (?ts 0 (?n_lw 0))"
        using read_at_lw_eq last_padded(3) by simp
      have gamma_lw: "\<forall>kk :: nat. ?ts kk (?n_lw kk) \<in> gamma_block (\<Gamma>_tm M)"
        using gamma_all by simp
      have step_to_pad:
        "(Config\<^sub>M (s_tm M, init_offset, init_buffer (le_tm M),
                      init_dest, VFwd) ?ts ?n_lw,
           Config\<^sub>M (s_tm M, init_offset, init_buffer (le_tm M),
                      init_dest, VFwdPad) ?ts
                  (\<lambda>kk. go_dir (if kk = (0 :: nat) then dir.R else dir.N)
                                 (?n_lw kk)))
            \<in> ?R"
        by (rule ae_step_val_fwd_to_padded[where ts = ?ts and n = ?n_lw,
              OF s_in_Q s_neq_t s_neq_r read_padded bt_all init_stage_tail
                 gamma_lw buf_gamma_init])
      have post_eq_pad:
        "(\<lambda>kk :: nat. go_dir (if kk = 0 then dir.R else dir.N) (?n_lw kk))
         = (\<lambda>i :: nat. if i = 0 then Suc ?lw else 0)"
        by (rule ext) simp
      have step_to_pad_norm: "(?vfwd ?lw, ?vpad (Suc ?lw)) \<in> ?R"
        using step_to_pad post_eq_pad by simp
      have reach: "(?init, ?vpad (Suc ?lw)) \<in> ?R ^^ Suc ?lw"
        by (rule relpow_Suc_I[OF sweep_lw step_to_pad_norm])
      have "snd (snd (snd (snd (mt_state (?vpad (Suc ?lw))))))
              \<in> {VFwd, VFwdPad, VRet}" by simp
      thus ?thesis using reach by blast
    qed
  qed
  \<comment> \<open>Pivot witness into \<open>VRet\<close> at head \<open>Suc lw\<close>, reached in
      \<open>Suc (Suc lw)\<close> steps (both classification cases).\<close>
  have to_VRet: "(?init, ?vret (Suc ?lw)) \<in> ?R ^^ Suc (Suc ?lw)"
  proof -
    from all_pure_or_last_padded consider
        (all_pure) "\<forall>i < ?lw. is_pure_block (bl_tm M) (w ! i)"
      | (last_padded) "0 < ?lw"
                       "\<forall>i < ?lw - 1. is_pure_block (bl_tm M) (w ! i)"
                       "is_padded_block (bl_tm M) (w ! (?lw - 1))"
      by blast
    thus ?thesis
    proof cases
      case all_pure
      let ?n_Slw = "\<lambda>i :: nat. if i = 0 then Suc ?lw else 0"
      have lw_le: "?lw \<le> ?lw" by simp
      have sweep: "(?init, ?vfwd (Suc ?lw)) \<in> ?R ^^ Suc ?lw"
        using ae_validation_fwd_sweep_pure[OF vM w_sub s_in_Q s_neq_t
                  s_neq_r lw_le all_pure] unfolding stage_eq by simp
      have lw_gt: "Suc ?lw > ?lw" by simp
      have read_bl: "?ts 0 (?n_Slw 0) = bl_block (bl_tm M)"
        using ae_init_config_tape_blank_after_input[OF lw_gt] by simp
      have gamma_Slw: "\<forall>kk :: nat. ?ts kk (?n_Slw kk) \<in> gamma_block (\<Gamma>_tm M)"
        using gamma_all by simp
      have step_to_ret: "(?vfwd (Suc ?lw), ?vret (Suc ?lw)) \<in> ?R"
        by (rule ae_step_val_fwd_to_ret[where ts = ?ts and n = ?n_Slw,
              OF s_in_Q s_neq_t s_neq_r read_bl bt_all init_stage_tail
                 gamma_Slw buf_gamma_init])
      show ?thesis by (rule relpow_Suc_I[OF sweep step_to_ret])
    next
      case last_padded
      let ?n_lw = "\<lambda>i :: nat. if i = 0 then ?lw else 0"
      let ?n_Slw = "\<lambda>i :: nat. if i = 0 then Suc ?lw else 0"
      have wpos: "0 < ?lw" using last_padded(1) .
      have m1_le: "?lw - 1 \<le> ?lw" by simp
      have sweep:
        "(?init, Config\<^sub>M (s_tm M, init_stage (le_tm M)) ?ts
                   (\<lambda>i :: nat. if i = 0 then Suc (?lw - 1) else 0))
            \<in> ?R ^^ Suc (?lw - 1)"
        by (rule ae_validation_fwd_sweep_pure[OF vM w_sub s_in_Q s_neq_t
                                                s_neq_r m1_le last_padded(2)])
      have suc_m1_eq: "Suc (?lw - 1) = ?lw" using wpos by simp
      have sweep_lw: "(?init, ?vfwd ?lw) \<in> ?R ^^ ?lw"
        using sweep unfolding suc_m1_eq stage_eq by simp
      have lw_pos: "1 \<le> ?lw" using wpos by linarith
      have lw_le: "?lw \<le> ?lw" by simp
      have read_at_lw_eq: "?ts 0 ?lw = w ! (?lw - 1)"
        using ae_init_config_tape_input[OF lw_pos lw_le kpos] by simp
      have read_padded: "is_padded_block (bl_tm M) (?ts 0 (?n_lw 0))"
        using read_at_lw_eq last_padded(3) by simp
      have gamma_lw: "\<forall>kk :: nat. ?ts kk (?n_lw kk) \<in> gamma_block (\<Gamma>_tm M)"
        using gamma_all by simp
      have step_to_pad:
        "(Config\<^sub>M (s_tm M, init_offset, init_buffer (le_tm M),
                      init_dest, VFwd) ?ts ?n_lw,
           Config\<^sub>M (s_tm M, init_offset, init_buffer (le_tm M),
                      init_dest, VFwdPad) ?ts
                  (\<lambda>kk. go_dir (if kk = (0 :: nat) then dir.R else dir.N)
                                 (?n_lw kk)))
            \<in> ?R"
        by (rule ae_step_val_fwd_to_padded[where ts = ?ts and n = ?n_lw,
              OF s_in_Q s_neq_t s_neq_r read_padded bt_all init_stage_tail
                 gamma_lw buf_gamma_init])
      have post_eq_pad:
        "(\<lambda>kk :: nat. go_dir (if kk = 0 then dir.R else dir.N) (?n_lw kk))
         = ?n_Slw"
        by (rule ext) simp
      have step_to_pad_norm: "(?vfwd ?lw, ?vpad (Suc ?lw)) \<in> ?R"
        using step_to_pad post_eq_pad by simp
      have chain_lw_to_VFwdPad: "(?init, ?vpad (Suc ?lw)) \<in> ?R ^^ Suc ?lw"
        by (rule relpow_Suc_I[OF sweep_lw step_to_pad_norm])
      have read_bl_Slw: "?ts 0 (?n_Slw 0) = bl_block (bl_tm M)"
        using ae_init_config_tape_blank_after_input[OF lessI] by simp
      have gamma_Slw: "\<forall>kk :: nat. ?ts kk (?n_Slw kk) \<in> gamma_block (\<Gamma>_tm M)"
        using gamma_all by simp
      have step_pad_to_ret: "(?vpad (Suc ?lw), ?vret (Suc ?lw)) \<in> ?R"
        by (rule ae_step_val_pad_to_ret[where ts = ?ts and n = ?n_Slw,
              OF s_in_Q read_bl_Slw bt_all init_stage_tail
                 gamma_Slw buf_gamma_init])
      show ?thesis
        by (rule relpow_Suc_I[OF chain_lw_to_VFwdPad step_pad_to_ret])
    qed
  qed
  \<comment> \<open>Return witnesses: \<open>m\<close> leftward steps from the pivot reach
      \<open>VRet\<close> head \<open>Suc lw - m\<close> in \<open>Suc (Suc lw) + m\<close> steps.\<close>
  have ret_reach: "\<And>m. m \<le> Suc ?lw
            \<Longrightarrow> (?init, ?vret (Suc ?lw - m)) \<in> ?R ^^ (Suc (Suc ?lw) + m)"
  proof -
    fix m assume mle: "m \<le> Suc ?lw"
    have rp: "(?vret (Suc ?lw), ?vret (Suc ?lw - m)) \<in> ?R ^^ m"
      by (rule mp[OF ae_validation_ret_partial[OF s_in_Q gamma_all
            buf_gamma_init bt_all init_stage_tail non_le_Slw] mle])
    have "(?init, ?vret (Suc ?lw - m)) \<in> ?R ^^ Suc (Suc ?lw) O ?R ^^ m"
      using to_VRet rp by (rule relcompI)
    thus "(?init, ?vret (Suc ?lw - m)) \<in> ?R ^^ (Suc (Suc ?lw) + m)"
      by (simp only: relpow_add)
  qed
  \<comment> \<open>Assemble: each step \<open>i < 2 lw + 4\<close> falls in the forward,
      boundary, or return region.\<close>
  show ?thesis
  proof (intro allI impI)
    fix i :: nat assume i_lt: "i < 2 * ?lw + 4"
    consider (fwd) "i \<le> ?lw" | (bd) "i = Suc ?lw" | (ret) "Suc ?lw < i"
      by linarith
    thus "\<exists>d. (?init, d) \<in> ?R ^^ i
              \<and> snd (snd (snd (snd (mt_state d)))) \<in> {VFwd, VFwdPad, VRet}"
    proof cases
      case fwd
      have "(?init, ?vfwd i) \<in> ?R ^^ i" by (rule vfwd_wit[OF fwd])
      moreover have "snd (snd (snd (snd (mt_state (?vfwd i)))))
                       \<in> {VFwd, VFwdPad, VRet}" by simp
      ultimately show ?thesis by blast
    next
      case bd
      show ?thesis using boundary_wit unfolding bd by blast
    next
      case ret
      define m where "m = i - Suc (Suc ?lw)"
      have i_ge: "Suc (Suc ?lw) \<le> i" using ret by simp
      have m_le: "m \<le> Suc ?lw" using i_lt m_def by simp
      have i_eq: "Suc (Suc ?lw) + m = i" using i_ge m_def by simp
      have "(?init, ?vret (Suc ?lw - m)) \<in> ?R ^^ i"
        using ret_reach[OF m_le] unfolding i_eq .
      moreover have "snd (snd (snd (snd (mt_state (?vret (Suc ?lw - m))))))
                       \<in> {VFwd, VFwdPad, VRet}" by simp
      ultimately show ?thesis by blast
    qed
  qed
qed

text \<open>Prefix uniqueness: every config reachable from \<open>ae_init_config\<close>
  in \<open>i < 2 * length w + 4\<close> steps is a validation marker (stage index
  \<open>VFwd\<close> / \<open>VFwdPad\<close> / \<open>VRet\<close>).  This is the invariant the relpow
  validation-functional needs, and is \<^emph>\<open>det-free\<close>: the validation
  sweep is functional regardless of \<open>M\<close>'s (non)determinism, since the
  only nondeterministic substep of \<open>alphabet_enlarge_delta\<close> (the
  \<open>SS4\<close>-to-\<open>SS5\<close> transition) is never reached before \<open>SS1\<close>.  Proof:
  strong induction on \<open>i\<close>;
  the induction hypothesis supplies the relpow-functional's invariant
  premise, so the arbitrary reachable \<open>d\<close> is forced equal to the
  marker witness exhibited by \<open>ae_validation_prefix_witnesses\<close>.\<close>

lemma ae_validation_prefix_markers:
  fixes M :: "('q, 'a) mttm"
    and w :: "('c :: enum \<Rightarrow> 'a) list"
  assumes vM: "valid_mttm M"
      and w_sub: "set w \<subseteq> gamma_block (Sigma_tm M \<union> {bl_tm M})"
      and wf: "ae_input_well_formed (bl_tm M) w"
      and s_in_Q: "s_tm M \<in> Q_tm M"
      and s_neq_t: "s_tm M \<noteq> t_tm M"
      and s_neq_r: "s_tm M \<noteq> r_tm M"
      and le_neq_bl: "le_tm M \<noteq> bl_tm M"
  shows "\<forall>i<2 * length w + 4. \<forall>d.
            (ae_init_config M w, d)
                \<in> mttm_step (alphabet_enlarge_delta M) ^^ i
              \<longrightarrow> snd (snd (snd (snd (mt_state d))))
                    \<in> {VFwd, VFwdPad, VRet}"
proof -
  let ?init = "ae_init_config M w"
  let ?R = "mttm_step (alphabet_enlarge_delta M)"
  let ?n_val = "2 * length w + 4"
  have wit: "\<forall>i<?n_val. \<exists>d. (?init, d) \<in> ?R ^^ i
              \<and> snd (snd (snd (snd (mt_state d)))) \<in> {VFwd, VFwdPad, VRet}"
    by (rule ae_validation_prefix_witnesses[OF vM w_sub wf s_in_Q
                                              s_neq_t s_neq_r le_neq_bl])
  have main: "\<forall>i0. i0 < ?n_val
                \<longrightarrow> (\<forall>d. (?init, d) \<in> ?R ^^ i0
                          \<longrightarrow> snd (snd (snd (snd (mt_state d))))
                                \<in> {VFwd, VFwdPad, VRet})"
  proof (rule allI)
    fix i1 :: nat
    show "i1 < ?n_val
            \<longrightarrow> (\<forall>d. (?init, d) \<in> ?R ^^ i1
                  \<longrightarrow> snd (snd (snd (snd (mt_state d))))
                        \<in> {VFwd, VFwdPad, VRet})"
    proof (induction i1 rule: less_induct)
      case (less i)
      show ?case
      proof (rule impI)
        assume i_lt: "i < ?n_val"
        show "\<forall>d. (?init, d) \<in> ?R ^^ i
                    \<longrightarrow> snd (snd (snd (snd (mt_state d))))
                          \<in> {VFwd, VFwdPad, VRet}"
        proof (intro allI impI)
          fix d assume reach: "(?init, d) \<in> ?R ^^ i"
          have inv: "\<forall>j<i. \<forall>d'. (?init, d') \<in> ?R ^^ j
                      \<longrightarrow> snd (snd (snd (snd (mt_state d'))))
                            \<in> {VFwd, VFwdPad, VRet}"
          proof (intro allI impI)
            fix j d' assume j_lt: "j < i" and reach': "(?init, d') \<in> ?R ^^ j"
            have "j < ?n_val" using j_lt i_lt by simp
            thus "snd (snd (snd (snd (mt_state d')))) \<in> {VFwd, VFwdPad, VRet}"
              using less.IH[OF j_lt] reach' by blast
          qed
          obtain wd where wreach: "(?init, wd) \<in> ?R ^^ i"
            and wmark: "snd (snd (snd (snd (mt_state wd)))) \<in> {VFwd, VFwdPad, VRet}"
            using wit i_lt by blast
          have "d = wd"
            by (rule mttm_step_alphabet_enlarge_val_relpow_functional
                       [OF le_neq_bl reach wreach inv])
          thus "snd (snd (snd (snd (mt_state d)))) \<in> {VFwd, VFwdPad, VRet}"
            using wmark by simp
        qed
      qed
    qed
  qed
  show ?thesis using main by blast
qed

lemma ae_validation_post_state_canonical:
  fixes M :: "('q, 'a) mttm"
    and u :: "'a list"
  assumes vM: "valid_mttm M"
      and u_sub: "set u \<subseteq> Sigma_tm M"
      and le_neq_bl: "le_tm M \<noteq> bl_tm M"
  obtains n :: nat and c' where
      "(ae_init_config M (encode_input (bl_tm M) u), c')
            \<in> mttm_step (alphabet_enlarge_delta M) ^^ n"
    and "ae_simulates M
            (init_config_mttm M u)
            (c' :: ('c :: enum \<Rightarrow> 'a,
                    'q \<times> ('a, 'c) ae_stage) mt_config)"
    and "ae_buffer_in_gamma_block M c'"
    and "\<forall>kk<k_tm M. mt_tape c' kk 0 = LE_block (le_tm M)"
    and "\<forall>i<n. \<forall>d :: ('c :: enum \<Rightarrow> 'a,
                          'q \<times> ('a, 'c) ae_stage) mt_config.
            (ae_init_config M (encode_input (bl_tm M) u), d)
                \<in> mttm_step (alphabet_enlarge_delta M) ^^ i
              \<longrightarrow> snd (snd (snd (snd (mt_state d))))
                    \<in> {VFwd, VFwdPad, VRet}"
proof -
  let ?w = "encode_input (bl_tm M) u :: ('c :: enum \<Rightarrow> 'a) list"
  let ?init = "ae_init_config M ?w"
  let ?subst_init = "init_config_mttm M u :: ('a, 'q) mt_config"
  have w_sub: "set ?w \<subseteq> gamma_block (Sigma_tm M \<union> {bl_tm M})"
    by (rule encode_input_in_gamma_block[OF u_sub])
  have wf: "ae_input_well_formed (bl_tm M) ?w"
    by (rule encode_input_well_formed[OF vM u_sub])
  have s_in_Q: "s_tm M \<in> Q_tm M" by (rule s_tm_in_Q_tm[OF vM])
  \<comment> \<open>Tape correspondence is shared across the s-degenerate and
      s-nondegenerate cases (the chain doesn't modify the tape).\<close>
  have tape_corr:
    "\<forall>k<k_tm M. ae_tape_correspondence (le_tm M)
            (mt_tape ?subst_init k) (mt_tape ?init k)"
    by (rule ae_tape_correspondence_init[OF vM u_sub])
  \<comment> \<open>Gamma-block invariant on the M'-tape: also shared across
      both cases since the validation chain in the nondegen case
      reuses \<open>mt_tape ?init\<close> verbatim (no writes).\<close>
  have gamma_block_init: "ae_tape_in_gamma_block M ?init"
    unfolding ae_tape_in_gamma_block_def
  proof (intro conjI)
    show "\<forall>k p. mt_tape ?init k p \<in> gamma_block (\<Gamma>_tm M)"
      using ae_init_config_in_gamma_block[OF vM w_sub] by simp
  next
    show "\<forall>j\<ge>k_tm M. \<forall>p. mt_tape ?init j p = bl_block (bl_tm M)"
      using ae_init_config_tape_blank_tail by blast
  qed
  \<comment> \<open>Position correspondence: substrate's \<open>n_M k = 0\<close>; ae's
      \<open>n_M' k = 0\<close>; \<open>ae_decode_pos 0 _ = 0\<close>.\<close>
  have ae_pos_zero: "\<forall>k. mt_pos ?init k = 0"
    unfolding ae_init_config_def by simp
  have subst_pos_zero: "\<forall>k. mt_pos ?subst_init k = 0"
    by (cases M) simp
  have pos_corr_init:
    "\<forall>k. mt_pos ?subst_init k
            = ae_decode_pos (mt_pos ?init k) ((init_offset :: nat \<Rightarrow> 'c) k)"
    using ae_pos_zero subst_pos_zero
    unfolding ae_decode_pos_def by simp
  consider (degen) "s_tm M = t_tm M \<or> s_tm M = r_tm M"
         | (nondegen) "s_tm M \<noteq> t_tm M \<and> s_tm M \<noteq> r_tm M"
    by blast
  thus ?thesis
  proof cases
    case degen
    \<comment> \<open>\<open>n = 0\<close>: chain is reflexive; simulation's halt-branch fires.\<close>
    have chain_0:
      "(?init, ?init) \<in> mttm_step (alphabet_enlarge_delta M) ^^ 0"
      by simp
    have qM_subst: "mt_state ?subst_init = s_tm M"
      by (cases M) simp
    have init_state:
      "mt_state ?init = (s_tm M, init_offset,
                          init_buffer (le_tm M), init_dest, VFwd)"
      unfolding ae_init_config_def init_stage_def by simp
    have simulation: "ae_simulates M ?subst_init ?init"
      unfolding ae_simulates_def Let_def init_state init_stage_def
      using qM_subst tape_corr pos_corr_init degen gamma_block_init by simp
    \<comment> \<open>\<open>buf_gamma\<close>: \<open>?init\<close>'s state buffer is \<open>init_buffer (le_tm M)\<close>,
        which is constant \<open>LE_block (le_tm M)\<close> in every slot;
        \<open>init_buffer_in_gamma_block_at_M\<close> discharges.\<close>
    have buf_gamma_init: "ae_buffer_in_gamma_block M ?init"
      unfolding ae_buffer_in_gamma_block_def init_state init_stage_def
      using init_buffer_in_gamma_block_at_M[OF vM] by simp
    \<comment> \<open>\<open>le_anchor\<close>: position 0 of every M'-tape is \<open>LE_block (le_tm M)\<close>
        by \<open>ae_init_config_def\<close>.\<close>
    have le_anchor_init:
        "\<forall>kk<k_tm M. mt_tape ?init kk 0 = LE_block (le_tm M)"
      by (auto intro: ae_init_config_tape_le)
    \<comment> \<open>\<open>n = 0\<close>, so the prefix-marker clause is vacuous.\<close>
    have markers_0:
      "\<forall>i<(0 :: nat). \<forall>d.
          (?init, d) \<in> mttm_step (alphabet_enlarge_delta M) ^^ i
            \<longrightarrow> snd (snd (snd (snd (mt_state d)))) \<in> {VFwd, VFwdPad, VRet}"
      by simp
    show ?thesis
      using chain_0 simulation buf_gamma_init le_anchor_init markers_0
      by (rule that)
  next
    case nondegen
    \<comment> \<open>Build SS1-landing chain via helper; simulation's SS1-branch
        fires.\<close>
    have s_neq_t: "s_tm M \<noteq> t_tm M" using nondegen by simp
    have s_neq_r: "s_tm M \<noteq> r_tm M" using nondegen by simp
    let ?c' = "Config\<^sub>M (s_tm M, init_offset, init_buffer (le_tm M),
                          init_dest, SS1)
                       (mt_tape ?init) (\<lambda>_ :: nat. (0 :: nat))
                  :: ('c \<Rightarrow> 'a, 'q \<times> ('a, 'c) ae_stage) mt_config"
    have chain:
      "(?init, ?c') \<in> mttm_step (alphabet_enlarge_delta M)
                        ^^ (2 * length ?w + 4)"
      by (rule ae_validation_well_formed_to_SS1[OF vM w_sub wf
            s_in_Q s_neq_t s_neq_r le_neq_bl])
    have qM_subst: "mt_state ?subst_init = s_tm M"
      by (cases M) simp
    have c'_state:
      "mt_state ?c' = (s_tm M, init_offset,
                          init_buffer (le_tm M), init_dest, SS1)"
      by simp
    have pos_corr_c':
      "\<forall>k. mt_pos ?subst_init k
              = ae_decode_pos (mt_pos ?c' k)
                              ((init_offset :: nat \<Rightarrow> 'c) k)"
      using subst_pos_zero by (simp add: ae_decode_pos_def)
    have gamma_block_c': "ae_tape_in_gamma_block M ?c'"
      unfolding ae_tape_in_gamma_block_def
      using gamma_block_init unfolding ae_tape_in_gamma_block_def
      by simp
    have simulation: "ae_simulates M ?subst_init ?c'"
      unfolding ae_simulates_def Let_def c'_state
      using qM_subst tape_corr pos_corr_c' gamma_block_c'
            s_neq_t s_neq_r by simp
    \<comment> \<open>\<open>buf_gamma\<close>: SS1-landing config still carries the canonical
        \<open>init_buffer (le_tm M)\<close>; \<open>init_buffer_in_gamma_block_at_M\<close>
        discharges as in the degen case.\<close>
    have buf_gamma_c': "ae_buffer_in_gamma_block M ?c'"
      unfolding ae_buffer_in_gamma_block_def
      using init_buffer_in_gamma_block_at_M[OF vM] by simp
    \<comment> \<open>\<open>le_anchor\<close>: the SS1-landing config's tape equals
        \<open>mt_tape ?init\<close> verbatim (validation does not write the
        M'-tape); position 0 inherits \<open>LE_block (le_tm M)\<close> from
        \<open>ae_init_config_tape_le\<close>.\<close>
    have le_anchor_c':
        "\<forall>kk<k_tm M. mt_tape ?c' kk 0 = LE_block (le_tm M)"
      by (auto intro: ae_init_config_tape_le)
    \<comment> \<open>The validation prefix is uniquely a marker run (det-free).\<close>
    have markers:
      "\<forall>i<2 * length ?w + 4. \<forall>d.
          (?init, d) \<in> mttm_step (alphabet_enlarge_delta M) ^^ i
            \<longrightarrow> snd (snd (snd (snd (mt_state d)))) \<in> {VFwd, VFwdPad, VRet}"
      by (rule ae_validation_prefix_markers[OF vM w_sub wf s_in_Q
            s_neq_t s_neq_r le_neq_bl])
    show ?thesis
      using chain simulation buf_gamma_c' le_anchor_c' markers
      by (rule that)
  qed
qed

text \<open>Noncanonical inputs reject.  The \<open>bl_block bl_M \<notin> set w\<close>
  hypothesis matches \<open>M'\<close>'s input alphabet \<open>\<Sigma>'\<close>
  (\<open>\<Sigma>' = gamma_block (\<Sigma>_M \<union> {bl_M}) - {bl_block, LE_block}\<close>).
  Without it, e.g.\ \<open>w = [bl_block bl_M]\<close>
  triggers \<open>ae_delta_val_fwd_to_ret\<close> at the first input
  block, mistaking it for end-of-input — validation passes
  rather than rejecting, falsifying the lemma as previously
  stated.  \<open>LE_block le_M \<notin> set w\<close> follows already from
  \<open>set w \<subseteq> gamma_block (\<Sigma>_M \<union> {bl_M})\<close> plus
  \<open>le_M \<notin> \<Sigma>_M \<union> {bl_M}\<close>, so it need not be assumed
  separately.\<close>

lemma ae_validation_post_state_noncanonical:
  fixes M :: "('q, 'a) mttm"
    and w :: "(('c :: enum) \<Rightarrow> 'a) list"
  assumes vM: "valid_mttm M"
      and w_sub: "set w \<subseteq> gamma_block (Sigma_tm M \<union> {bl_tm M})"
      and bl_notin: "bl_block (bl_tm M) \<notin> set w"
      and w_bad: "\<not> ae_input_well_formed (bl_tm M) w"
      and s_neq_t: "s_tm M \<noteq> t_tm M"
      and s_neq_r: "s_tm M \<noteq> r_tm M"
  obtains n :: nat and c' where
      "n \<le> length w + 2"
    and "(ae_init_config M w, c')
            \<in> mttm_step (alphabet_enlarge_delta M) ^^ n"
    and "case mt_state c' of (qM', _, _, _, _) \<Rightarrow> qM' = r_tm M"
proof -
  let ?init = "ae_init_config M w"
  let ?ts = "mt_tape ?init"
  have kpos: "0 < k_tm M" by (rule valid_mttm_k_pos[OF vM])
  have bt_all: "\<forall>j\<ge>k_tm M. \<forall>i. ?ts j i = bl_block (bl_tm M)"
    using ae_init_config_tape_blank_tail by blast
  have buf_gamma_init:
      "\<forall>kk :: nat.
          fst (init_buffer (le_tm M) kk
                  :: ('c \<Rightarrow> 'a) \<times> ('c \<Rightarrow> 'a) \<times> ('c \<Rightarrow> 'a))
              \<in> gamma_block (\<Gamma>_tm M)
          \<and> fst (snd (init_buffer (le_tm M) kk
                        :: ('c \<Rightarrow> 'a) \<times> ('c \<Rightarrow> 'a) \<times> ('c \<Rightarrow> 'a)))
              \<in> gamma_block (\<Gamma>_tm M)
          \<and> snd (snd (init_buffer (le_tm M) kk
                        :: ('c \<Rightarrow> 'a) \<times> ('c \<Rightarrow> 'a) \<times> ('c \<Rightarrow> 'a)))
              \<in> gamma_block (\<Gamma>_tm M)"
    by (rule init_buffer_in_gamma_block_at_M[OF vM])
  have s_in_Q: "s_tm M \<in> Q_tm M" by (rule s_tm_in_Q_tm[OF vM])
  from w_bad have failure_exists:
    "\<exists>s'. s' < length w
          \<and> \<not> is_pure_block (bl_tm M) (w ! s')
          \<and> \<not> (s' = length w - 1
               \<and> is_padded_block (bl_tm M) (w ! s'))"
    unfolding ae_input_well_formed_def by auto
  define P where
    "P = (\<lambda>s'. s' < length w
               \<and> \<not> is_pure_block (bl_tm M) (w ! s')
               \<and> \<not> (s' = length w - 1
                    \<and> is_padded_block (bl_tm M) (w ! s')))"
  define s where "s = (LEAST s'. P s')"
  have failure_exists_P: "\<exists>s'. P s'"
    using failure_exists unfolding P_def by simp
  from failure_exists_P have P_s: "P s"
    unfolding s_def by (rule LeastI_ex)
  have s_lt: "s < length w" using P_s unfolding P_def by simp
  have w_pos: "0 < length w" using s_lt by linarith
  have s_not_pure: "\<not> is_pure_block (bl_tm M) (w ! s)"
    using P_s unfolding P_def by simp
  have s_not_last_padded:
    "\<not> (s = length w - 1 \<and> is_padded_block (bl_tm M) (w ! s))"
    using P_s unfolding P_def by simp
  have s_min: "\<forall>s'. P s' \<longrightarrow> s \<le> s'"
    unfolding s_def using Least_le by metis
  have pure_prefix: "\<forall>i < s. is_pure_block (bl_tm M) (w ! i)"
  proof (intro allI impI)
    fix i assume i_lt_s: "i < s"
    have i_lt_lw: "i < length w" using i_lt_s s_lt by simp
    have i_neq_last: "i \<noteq> length w - 1"
      using i_lt_s s_lt w_pos by linarith
    have not_P_i: "\<not> P i" using s_min i_lt_s by force
    hence "is_pure_block (bl_tm M) (w ! i)
           \<or> (i = length w - 1
              \<and> is_padded_block (bl_tm M) (w ! i))"
      using i_lt_lw unfolding P_def by auto
    thus "is_pure_block (bl_tm M) (w ! i)"
      using i_neq_last by auto
  qed
  have s_le_lw: "s \<le> length w" using s_lt by simp
  have sweep:
    "(?init,
       Config\<^sub>M (s_tm M, init_stage (le_tm M)) ?ts
                (\<lambda>i :: nat. if i = 0 then Suc s else 0))
      \<in> mttm_step (alphabet_enlarge_delta M) ^^ Suc s"
    by (rule ae_validation_fwd_sweep_pure[OF vM w_sub s_in_Q s_neq_t s_neq_r
                                            s_le_lw pure_prefix])
  have Sk_pos: "1 \<le> Suc s" by simp
  have Sk_le: "Suc s \<le> length w" using s_lt by simp
  have read_at_Ss: "?ts 0 (Suc s) = w ! s"
    using ae_init_config_tape_input[OF Sk_pos Sk_le kpos] by simp
  have w_s_in_set: "w ! s \<in> set w" using s_lt by auto
  have w_s_neq_bl: "w ! s \<noteq> bl_block (bl_tm M)"
    using w_s_in_set bl_notin by auto
  have w_s_neq_le: "w ! s \<noteq> LE_block (le_tm M)"
  proof (cases "le_tm M = bl_tm M")
    case True
    have eq: "LE_block (le_tm M) = bl_block (bl_tm M)"
      using True unfolding LE_block_def bl_block_def by simp
    have "w ! s \<noteq> bl_block (bl_tm M)" using w_s_in_set bl_notin by auto
    thus ?thesis using eq by metis
  next
    case False
    have le_notin: "le_tm M \<notin> Sigma_tm M \<union> {bl_tm M}"
      using valid_mttm_LE_not_Sigma[OF vM] False by auto
    have "LE_block (le_tm M) \<notin> gamma_block (Sigma_tm M \<union> {bl_tm M})"
      using le_notin
      unfolding LE_block_def gamma_block_def by auto
    moreover have "w ! s \<in> gamma_block (Sigma_tm M \<union> {bl_tm M})"
      using w_s_in_set w_sub by auto
    ultimately show ?thesis by auto
  qed
  have case_split: "(\<not> is_canonical_block (bl_tm M) (w ! s))
                     \<or> (is_padded_block (bl_tm M) (w ! s)
                        \<and> Suc s < length w)"
  proof (cases "is_padded_block (bl_tm M) (w ! s)")
    case True
    have "s \<noteq> length w - 1" using s_not_last_padded True by simp
    hence "Suc s < length w" using s_lt by linarith
    thus ?thesis using True by simp
  next
    case False
    hence "\<not> is_canonical_block (bl_tm M) (w ! s)"
      using s_not_pure unfolding is_canonical_block_def by simp
    thus ?thesis by simp
  qed
  consider
      (noncan) "\<not> is_canonical_block (bl_tm M) (w ! s)"
    | (pad_misplaced) "is_padded_block (bl_tm M) (w ! s)"
                       "Suc s < length w"
    using case_split by blast
  thus ?thesis
  proof cases
    case noncan
    let ?n_Ss = "\<lambda>i :: nat. if i = 0 then Suc s else 0"
    have read_nle: "?ts 0 (?n_Ss 0) \<noteq> LE_block (le_tm M)"
      using read_at_Ss w_s_neq_le by simp
    have read_nbl: "?ts 0 (?n_Ss 0) \<noteq> bl_block (bl_tm M)"
      using read_at_Ss w_s_neq_bl by simp
    have read_ncan: "\<not> is_canonical_block (bl_tm M) (?ts 0 (?n_Ss 0))"
      using read_at_Ss noncan by simp
    have gamma: "\<forall>kk :: nat. ?ts kk (?n_Ss kk) \<in> gamma_block (\<Gamma>_tm M)"
      using ae_init_config_in_gamma_block[OF vM w_sub] by simp
    have step_rej:
      "(Config\<^sub>M (s_tm M, init_offset, init_buffer (le_tm M),
                    init_dest, VFwd) ?ts ?n_Ss,
         Config\<^sub>M (r_tm M, init_stage (le_tm M)) ?ts ?n_Ss)
        \<in> mttm_step (alphabet_enlarge_delta M)"
      by (rule ae_step_val_fwd_reject[where ts = ?ts and n = ?n_Ss,
            OF vM s_in_Q s_neq_t s_neq_r read_nle read_nbl read_ncan
            bt_all init_stage_tail gamma buf_gamma_init])
    have stage_eq: "init_stage (le_tm M)
                    = (init_offset, init_buffer (le_tm M), init_dest, VFwd)"
      unfolding init_stage_def ..
    have step_rej_init:
      "(Config\<^sub>M (s_tm M, init_stage (le_tm M)) ?ts ?n_Ss,
         Config\<^sub>M (r_tm M, init_stage (le_tm M)) ?ts ?n_Ss)
        \<in> mttm_step (alphabet_enlarge_delta M)"
      using step_rej unfolding stage_eq by simp
    have full_chain:
      "(?init, Config\<^sub>M (r_tm M, init_stage (le_tm M)) ?ts ?n_Ss)
        \<in> mttm_step (alphabet_enlarge_delta M) ^^ Suc (Suc s)"
      by (rule relpow_Suc_I[OF sweep step_rej_init])
    have bound: "Suc (Suc s) \<le> length w + 2" using s_lt by linarith
    have q_eq:
      "case mt_state (Config\<^sub>M (r_tm M, init_stage (le_tm M)) ?ts ?n_Ss)
         of (qM', _, _, _, _) \<Rightarrow> qM' = r_tm M"
      by (simp add: init_stage_def)
    show ?thesis
      by (rule that[OF bound full_chain q_eq])
  next
    case pad_misplaced
    let ?n_Ss = "\<lambda>i :: nat. if i = 0 then Suc s else 0"
    let ?n_SSs = "\<lambda>i :: nat. if i = 0 then Suc (Suc s) else 0"
    have read_pad: "is_padded_block (bl_tm M) (?ts 0 (?n_Ss 0))"
      using read_at_Ss pad_misplaced(1) by simp
    have gamma_Ss: "\<forall>kk :: nat. ?ts kk (?n_Ss kk) \<in> gamma_block (\<Gamma>_tm M)"
      using ae_init_config_in_gamma_block[OF vM w_sub] by simp
    have step_to_pad:
      "(Config\<^sub>M (s_tm M, init_offset, init_buffer (le_tm M),
                    init_dest, VFwd) ?ts ?n_Ss,
         Config\<^sub>M (s_tm M, init_offset, init_buffer (le_tm M),
                    init_dest, VFwdPad) ?ts
                  (\<lambda>kk. go_dir (if kk = (0 :: nat) then dir.R else dir.N)
                                 (?n_Ss kk)))
        \<in> mttm_step (alphabet_enlarge_delta M)"
      by (rule ae_step_val_fwd_to_padded[where ts = ?ts and n = ?n_Ss,
            OF s_in_Q s_neq_t s_neq_r read_pad bt_all init_stage_tail
               gamma_Ss buf_gamma_init])
    have post_eq:
      "(\<lambda>kk :: nat. go_dir (if kk = 0 then dir.R else dir.N) (?n_Ss kk))
       = ?n_SSs"
      by (rule ext) simp
    have step_to_pad_SS:
      "(Config\<^sub>M (s_tm M, init_offset, init_buffer (le_tm M),
                    init_dest, VFwd) ?ts ?n_Ss,
         Config\<^sub>M (s_tm M, init_offset, init_buffer (le_tm M),
                    init_dest, VFwdPad) ?ts ?n_SSs)
        \<in> mttm_step (alphabet_enlarge_delta M)"
      using step_to_pad post_eq by simp
    have stage_eq: "init_stage (le_tm M)
                    = (init_offset, init_buffer (le_tm M), init_dest, VFwd)"
      unfolding init_stage_def ..
    have step_to_pad_init:
      "(Config\<^sub>M (s_tm M, init_stage (le_tm M)) ?ts ?n_Ss,
         Config\<^sub>M (s_tm M, init_offset, init_buffer (le_tm M),
                    init_dest, VFwdPad) ?ts ?n_SSs)
        \<in> mttm_step (alphabet_enlarge_delta M)"
      using step_to_pad_SS unfolding stage_eq by simp
    have SSs_pos: "1 \<le> Suc (Suc s)" by simp
    have SSs_le: "Suc (Suc s) \<le> length w"
      using pad_misplaced(2) by linarith
    have read_at_SSs: "?ts 0 (Suc (Suc s)) = w ! Suc s"
      using ae_init_config_tape_input[OF SSs_pos SSs_le kpos] by simp
    have wSs_in_set: "w ! Suc s \<in> set w"
      using SSs_le by auto
    have wSs_neq_bl: "w ! Suc s \<noteq> bl_block (bl_tm M)"
      using wSs_in_set bl_notin by auto
    have read_nbl_SS: "?ts 0 (?n_SSs 0) \<noteq> bl_block (bl_tm M)"
      using read_at_SSs wSs_neq_bl by simp
    have gamma_SS: "\<forall>kk :: nat. ?ts kk (?n_SSs kk) \<in> gamma_block (\<Gamma>_tm M)"
      using ae_init_config_in_gamma_block[OF vM w_sub] by simp
    have step_pad_rej:
      "(Config\<^sub>M (s_tm M, init_offset, init_buffer (le_tm M),
                    init_dest, VFwdPad) ?ts ?n_SSs,
         Config\<^sub>M (r_tm M, init_stage (le_tm M)) ?ts ?n_SSs)
        \<in> mttm_step (alphabet_enlarge_delta M)"
      by (rule ae_step_val_pad_reject[where ts = ?ts and n = ?n_SSs,
            OF vM s_in_Q read_nbl_SS bt_all init_stage_tail
               gamma_SS buf_gamma_init])
    have post_sweep:
      "(?init,
         Config\<^sub>M (s_tm M, init_offset, init_buffer (le_tm M),
                    init_dest, VFwdPad) ?ts ?n_SSs)
        \<in> mttm_step (alphabet_enlarge_delta M) ^^ Suc (Suc s)"
      by (rule relpow_Suc_I[OF sweep step_to_pad_init])
    have full_chain:
      "(?init, Config\<^sub>M (r_tm M, init_stage (le_tm M)) ?ts ?n_SSs)
        \<in> mttm_step (alphabet_enlarge_delta M) ^^ Suc (Suc (Suc s))"
      by (rule relpow_Suc_I[OF post_sweep step_pad_rej])
    have bound: "Suc (Suc (Suc s)) \<le> length w + 2"
      using pad_misplaced(2) by linarith
    have q_eq:
      "case mt_state (Config\<^sub>M (r_tm M, init_stage (le_tm M)) ?ts ?n_SSs)
         of (qM', _, _, _, _) \<Rightarrow> qM' = r_tm M"
      by (simp add: init_stage_def)
    show ?thesis
      by (rule that[OF bound full_chain q_eq])
  qed
qed

lemma ae_validation_steps_bound:
  fixes M :: "('q, 'a) mttm"
    and w :: "('c :: enum \<Rightarrow> 'a) list"
  assumes vM: "valid_mttm M"
      and w_sub: "set w \<subseteq> gamma_block (Sigma_tm M \<union> {bl_tm M})"
      and s_neq_t: "s_tm M \<noteq> t_tm M"
      and s_neq_r: "s_tm M \<noteq> r_tm M"
      and le_neq_bl: "le_tm M \<noteq> bl_tm M"
  obtains f\<^sub>v :: nat and n :: nat and c' where
      "n \<le> 2 * length w + f\<^sub>v"
    and "(ae_init_config M w, c')
            \<in> mttm_step (alphabet_enlarge_delta M) ^^ n"
    and "case mt_state c' of (qM', _, _, _, idx) \<Rightarrow>
            idx = SS1 \<or> qM' = r_tm M"
proof -
  let ?init = "ae_init_config M w"
  let ?ts = "mt_tape ?init"
  have kpos: "0 < k_tm M" by (rule valid_mttm_k_pos[OF vM])
  have bt_all: "\<forall>j\<ge>k_tm M. \<forall>i. ?ts j i = bl_block (bl_tm M)"
    using ae_init_config_tape_blank_tail by blast
  have buf_gamma_init:
      "\<forall>kk :: nat.
          fst (init_buffer (le_tm M) kk
                  :: ('c \<Rightarrow> 'a) \<times> ('c \<Rightarrow> 'a) \<times> ('c \<Rightarrow> 'a))
              \<in> gamma_block (\<Gamma>_tm M)
          \<and> fst (snd (init_buffer (le_tm M) kk
                        :: ('c \<Rightarrow> 'a) \<times> ('c \<Rightarrow> 'a) \<times> ('c \<Rightarrow> 'a)))
              \<in> gamma_block (\<Gamma>_tm M)
          \<and> snd (snd (init_buffer (le_tm M) kk
                        :: ('c \<Rightarrow> 'a) \<times> ('c \<Rightarrow> 'a) \<times> ('c \<Rightarrow> 'a)))
              \<in> gamma_block (\<Gamma>_tm M)"
    by (rule init_buffer_in_gamma_block_at_M[OF vM])
  have s_in_Q: "s_tm M \<in> Q_tm M" by (rule s_tm_in_Q_tm[OF vM])
  consider
      (no_bl_wf)
        "bl_block (bl_tm M) \<notin> set w" "ae_input_well_formed (bl_tm M) w"
    | (no_bl_nwf)
        "bl_block (bl_tm M) \<notin> set w" "\<not> ae_input_well_formed (bl_tm M) w"
    | (has_bl)
        "bl_block (bl_tm M) \<in> set w"
    by blast
  thus ?thesis
  proof cases
    case no_bl_nwf
    obtain n c' where
        bound: "n \<le> length w + 2"
      and chain: "(ae_init_config M w, c')
                    \<in> mttm_step (alphabet_enlarge_delta M) ^^ n"
      and state_eq: "case mt_state c' of (qM', _, _, _, _) \<Rightarrow> qM' = r_tm M"
      using ae_validation_post_state_noncanonical[OF vM w_sub
              no_bl_nwf(1) no_bl_nwf(2) s_neq_t s_neq_r] by metis
    have bound2: "n \<le> 2 * length w + 4" using bound by linarith
    have state_eq_disj: "case mt_state c'
            of (qM', _, _, _, idx) \<Rightarrow> idx = SS1 \<or> qM' = r_tm M"
      using state_eq by (cases "mt_state c'") auto
    show ?thesis using bound2 chain state_eq_disj by (rule that)
  next
    case no_bl_wf
    have wf: "ae_input_well_formed (bl_tm M) w" using no_bl_wf(2) .
    have full_chain:
      "(?init,
         Config\<^sub>M (s_tm M, init_offset, init_buffer (le_tm M),
                    init_dest, SS1) ?ts (\<lambda>_. 0))
          \<in> mttm_step (alphabet_enlarge_delta M)
              ^^ (2 * length w + 4)"
      by (rule ae_validation_well_formed_to_SS1[OF vM w_sub wf s_in_Q
            s_neq_t s_neq_r le_neq_bl])
    have bound: "(2 * length w + 4 :: nat) \<le> 2 * length w + 4" by simp
    have state_eq:
      "case mt_state (Config\<^sub>M (s_tm M, init_offset,
                                     init_buffer (le_tm M),
                                     init_dest, SS1) ?ts (\<lambda>_. 0))
          of (qM', _, _, _, idx) \<Rightarrow> idx = SS1 \<or> qM' = r_tm M"
      by simp
    show ?thesis by (rule that[OF bound full_chain state_eq])
  next
    case has_bl
    have LE_neq_bl_block: "LE_block (le_tm M) \<noteq> bl_block (bl_tm M)"
      using le_neq_bl unfolding LE_block_def bl_block_def
      by (metis fun_eq_iff)
    have tape_le: "?ts (0 :: nat) 0 = LE_block (le_tm M)"
      by (rule ae_init_config_tape_le[OF kpos])
    have gamma_all: "\<forall>k i. ?ts k i \<in> gamma_block (\<Gamma>_tm M)"
      using ae_init_config_in_gamma_block[OF vM w_sub] by simp
    have stage_eq: "init_stage (le_tm M)
                    = (init_offset, init_buffer (le_tm M), init_dest, VFwd)"
      unfolding init_stage_def ..
    \<comment> \<open>Show \<open>LE_block le_M \<notin> set w\<close>: in the \<open>le \<noteq> bl\<close>
        regime, \<open>le \<notin> \<Sigma> \<union> {bl}\<close> forces \<open>LE_block\<close> out of
        \<open>gamma_block\<close>.\<close>
    have LE_notin: "LE_block (le_tm M) \<notin> set w"
    proof -
      have le_notin: "le_tm M \<notin> Sigma_tm M \<union> {bl_tm M}"
        using valid_mttm_LE_not_Sigma[OF vM] le_neq_bl by auto
      have "LE_block (le_tm M) \<notin> gamma_block (Sigma_tm M \<union> {bl_tm M})"
        using le_notin
        unfolding LE_block_def gamma_block_def by auto
      thus ?thesis using w_sub by auto
    qed
    \<comment> \<open>Find the first non-pure index — well-defined because
        \<open>bl_block\<close> is non-pure and present somewhere in \<open>w\<close>.\<close>
    define P where
      "P = (\<lambda>i. i < length w \<and> \<not> is_pure_block (bl_tm M) (w ! i))"
    have ex_P: "\<exists>i. P i"
    proof -
      from has_bl obtain j where j_lt: "j < length w" and j_eq: "w ! j = bl_block (bl_tm M)"
        by (auto simp: in_set_conv_nth)
      have "\<not> is_pure_block (bl_tm M) (bl_block (bl_tm M))"
        unfolding is_pure_block_def bl_block_def by auto
      hence "\<not> is_pure_block (bl_tm M) (w ! j)" using j_eq by simp
      thus ?thesis unfolding P_def using j_lt by auto
    qed
    define k where "k = (LEAST i. P i)"
    from ex_P have P_k: "P k" unfolding k_def by (rule LeastI_ex)
    have k_lt: "k < length w" using P_k unfolding P_def by simp
    have k_not_pure: "\<not> is_pure_block (bl_tm M) (w ! k)"
      using P_k unfolding P_def by simp
    have k_min: "\<forall>j. P j \<longrightarrow> k \<le> j"
      unfolding k_def using Least_le by metis
    have pure_prefix: "\<forall>i < k. is_pure_block (bl_tm M) (w ! i)"
    proof (intro allI impI)
      fix i assume i_lt_k: "i < k"
      have i_lt_w: "i < length w" using i_lt_k k_lt by simp
      have "\<not> P i" using k_min i_lt_k by force
      thus "is_pure_block (bl_tm M) (w ! i)" unfolding P_def using i_lt_w by auto
    qed
    have k_le_lw: "k \<le> length w" using k_lt by simp
    have sweep:
      "(?init,
          Config\<^sub>M (s_tm M, init_stage (le_tm M)) ?ts
                   (\<lambda>i :: nat. if i = 0 then Suc k else 0))
          \<in> mttm_step (alphabet_enlarge_delta M) ^^ Suc k"
      by (rule ae_validation_fwd_sweep_pure[OF vM w_sub s_in_Q s_neq_t
                                              s_neq_r k_le_lw pure_prefix])
    let ?n_Sk = "\<lambda>i :: nat. if i = 0 then Suc k else 0"
    have Sk_pos: "1 \<le> Suc k" by simp
    have Sk_le: "Suc k \<le> length w" using k_lt by simp
    have read_at_Sk: "?ts 0 (Suc k) = w ! k"
      using ae_init_config_tape_input[OF Sk_pos Sk_le kpos] by simp
    have w_k_in_set: "w ! k \<in> set w" using k_lt by auto
    have w_k_neq_le: "w ! k \<noteq> LE_block (le_tm M)"
      using w_k_in_set LE_notin by auto
    \<comment> \<open>Case-split on \<open>w!k\<close>: \<open>bl_block\<close> (passes), padded
        (sub-case on next), or non-canonical (rejects).\<close>
    consider
        (case_bl) "w ! k = bl_block (bl_tm M)"
      | (case_pad) "is_padded_block (bl_tm M) (w ! k)"
      | (case_noncan) "\<not> is_canonical_block (bl_tm M) (w ! k)"
                       "w ! k \<noteq> bl_block (bl_tm M)"
      using k_not_pure unfolding is_canonical_block_def by blast
    thus ?thesis
    proof cases
      case case_bl
      \<comment> \<open>Forward sweep + \<open>fwd_to_ret\<close> + return sweep, ending at SS1.\<close>
      have read_bl: "?ts 0 (?n_Sk 0) = bl_block (bl_tm M)"
        using read_at_Sk case_bl by simp
      have gamma_Sk:
        "\<forall>kk :: nat. ?ts kk (?n_Sk kk) \<in> gamma_block (\<Gamma>_tm M)"
        using gamma_all by simp
      have step_to_ret:
        "(Config\<^sub>M (s_tm M, init_offset, init_buffer (le_tm M),
                      init_dest, VFwd) ?ts ?n_Sk,
           Config\<^sub>M (s_tm M, init_offset, init_buffer (le_tm M),
                      init_dest, VRet) ?ts ?n_Sk)
            \<in> mttm_step (alphabet_enlarge_delta M)"
        by (rule ae_step_val_fwd_to_ret[where ts = ?ts and n = ?n_Sk,
              OF s_in_Q s_neq_t s_neq_r read_bl bt_all init_stage_tail
                 gamma_Sk buf_gamma_init])
      have step_to_ret_init:
        "(Config\<^sub>M (s_tm M, init_stage (le_tm M)) ?ts ?n_Sk,
           Config\<^sub>M (s_tm M, init_offset, init_buffer (le_tm M),
                      init_dest, VRet) ?ts ?n_Sk)
            \<in> mttm_step (alphabet_enlarge_delta M)"
        using step_to_ret unfolding stage_eq by simp
      have post_sweep:
        "(?init,
           Config\<^sub>M (s_tm M, init_offset, init_buffer (le_tm M),
                      init_dest, VRet) ?ts ?n_Sk)
            \<in> mttm_step (alphabet_enlarge_delta M) ^^ Suc (Suc k)"
        by (rule relpow_Suc_I[OF sweep step_to_ret_init])
      have non_le_Sk: "\<forall>i. 1 \<le> i \<and> i \<le> Suc k
                          \<longrightarrow> ?ts 0 i \<noteq> LE_block (le_tm M)"
      proof (intro allI impI)
        fix i assume i_range: "1 \<le> i \<and> i \<le> Suc k"
        have i_pos: "1 \<le> i" using i_range by simp
        have i_le_lw: "i \<le> length w" using i_range Sk_le by linarith
        have eq: "?ts 0 i = w ! (i - 1)"
          using ae_init_config_tape_input[OF i_pos i_le_lw kpos] by simp
        have "w ! (i - 1) \<in> set w" using i_pos i_le_lw by auto
        thus "?ts 0 i \<noteq> LE_block (le_tm M)" using LE_notin eq by auto
      qed
      have ret_arrow:
        "(\<forall>i. 1 \<le> i \<and> i \<le> Suc k
              \<longrightarrow> ?ts 0 i \<noteq> LE_block (le_tm M))
         \<longrightarrow> (Config\<^sub>M (s_tm M, init_offset, init_buffer (le_tm M),
                          init_dest, VRet) ?ts ?n_Sk,
              Config\<^sub>M (s_tm M, init_offset, init_buffer (le_tm M),
                          init_dest, SS1) ?ts (\<lambda>_. 0))
              \<in> mttm_step (alphabet_enlarge_delta M)
                  ^^ Suc (Suc k)"
        by (rule ae_validation_ret_sweep[OF s_in_Q tape_le gamma_all
                                          buf_gamma_init bt_all init_stage_tail])
      have ret_chain:
        "(Config\<^sub>M (s_tm M, init_offset, init_buffer (le_tm M),
                      init_dest, VRet) ?ts ?n_Sk,
           Config\<^sub>M (s_tm M, init_offset, init_buffer (le_tm M),
                      init_dest, SS1) ?ts (\<lambda>_. 0))
            \<in> mttm_step (alphabet_enlarge_delta M)
                ^^ Suc (Suc k)"
        using ret_arrow non_le_Sk by (rule mp)
      have full_chain_pre:
        "(?init,
           Config\<^sub>M (s_tm M, init_offset, init_buffer (le_tm M),
                      init_dest, SS1) ?ts (\<lambda>_. 0))
            \<in> mttm_step (alphabet_enlarge_delta M)
                ^^ (Suc (Suc k) + Suc (Suc k))"
      proof -
        have comp:
          "(?init,
             Config\<^sub>M (s_tm M, init_offset, init_buffer (le_tm M),
                        init_dest, SS1) ?ts (\<lambda>_. 0))
              \<in> mttm_step (alphabet_enlarge_delta M)
                  ^^ Suc (Suc k)
                O mttm_step (alphabet_enlarge_delta M)
                  ^^ Suc (Suc k)"
          using post_sweep ret_chain by (rule relcompI)
        thus ?thesis by (simp only: relpow_add)
      qed
      have bound: "Suc (Suc k) + Suc (Suc k) \<le> 2 * length w + 4"
        using k_lt by linarith
      have state_eq:
        "case mt_state (Config\<^sub>M (s_tm M, init_offset,
                                       init_buffer (le_tm M),
                                       init_dest, SS1) ?ts (\<lambda>_. 0))
            of (qM', _, _, _, idx) \<Rightarrow> idx = SS1 \<or> qM' = r_tm M"
        by simp
      show ?thesis by (rule that[OF bound full_chain_pre state_eq])
    next
      case case_pad
      \<comment> \<open>In \<open>has_bl\<close> + first-non-pure-padded, the \<open>bl_block\<close> must
          appear at some position \<open>j > k\<close>, hence \<open>Suc k < length
          w\<close>.\<close>
      have Sk_lt: "Suc k < length w"
      proof -
        from has_bl obtain j where j_lt: "j < length w"
              and j_eq: "w ! j = bl_block (bl_tm M)" by (auto simp: in_set_conv_nth)
        have "j \<ge> k"
        proof (rule ccontr)
          assume "\<not> j \<ge> k"
          hence "j < k" by simp
          hence "is_pure_block (bl_tm M) (w ! j)" using pure_prefix by simp
          moreover have "\<not> is_pure_block (bl_tm M) (bl_block (bl_tm M))"
            unfolding is_pure_block_def bl_block_def by auto
          ultimately show False using j_eq by auto
        qed
        moreover have "j \<noteq> k"
        proof
          assume "j = k"
          hence wk_bl: "w ! k = bl_block (bl_tm M)" using j_eq by simp
          have not_padded:
            "\<not> is_padded_block (bl_tm M) ((bl_block (bl_tm M)) :: 'c \<Rightarrow> 'a)"
          proof
            assume "is_padded_block (bl_tm M)
                    ((bl_block (bl_tm M)) :: 'c \<Rightarrow> 'a)"
            then obtain k_pad where
                k_pad_pos: "k_pad \<ge> 1"
              and k_pad_lt: "k_pad < length (enum_class.enum :: 'c list)"
              and prefix_cond:
                "\<forall>x. c_idx x < k_pad
                      \<longrightarrow> ((bl_block (bl_tm M)) :: 'c \<Rightarrow> 'a) x \<noteq> bl_tm M"
              unfolding is_padded_block_def by blast
            have len_pos: "0 < length (enum_class.enum :: 'c list)"
              using k_pad_lt k_pad_pos by linarith
            have "c_idx ((enum_class.enum :: 'c list) ! 0) = 0"
              by (rule c_idx_enum_nth[OF len_pos])
            hence c_first_idx: "c_idx (c_first :: 'c) = 0"
              unfolding c_first_def .
            hence "c_idx (c_first :: 'c) < k_pad"
              using k_pad_pos by simp
            hence "(bl_block (bl_tm M) :: 'c \<Rightarrow> 'a) c_first \<noteq> bl_tm M"
              using prefix_cond by blast
            thus False unfolding bl_block_def by simp
          qed
          show False using case_pad wk_bl not_padded by simp
        qed
        ultimately have "j > k" by simp
        thus ?thesis using j_lt by linarith
      qed
      let ?n_SSk = "\<lambda>i :: nat. if i = 0 then Suc (Suc k) else 0"
      have read_pad: "is_padded_block (bl_tm M) (?ts 0 (?n_Sk 0))"
        using read_at_Sk case_pad by simp
      have gamma_Sk:
        "\<forall>kk :: nat. ?ts kk (?n_Sk kk) \<in> gamma_block (\<Gamma>_tm M)"
        using gamma_all by simp
      have step_to_pad:
        "(Config\<^sub>M (s_tm M, init_offset, init_buffer (le_tm M),
                      init_dest, VFwd) ?ts ?n_Sk,
           Config\<^sub>M (s_tm M, init_offset, init_buffer (le_tm M),
                      init_dest, VFwdPad) ?ts
                  (\<lambda>kk. go_dir (if kk = (0 :: nat) then dir.R else dir.N)
                                 (?n_Sk kk)))
            \<in> mttm_step (alphabet_enlarge_delta M)"
        by (rule ae_step_val_fwd_to_padded[where ts = ?ts and n = ?n_Sk,
              OF s_in_Q s_neq_t s_neq_r read_pad bt_all init_stage_tail
                 gamma_Sk buf_gamma_init])
      have post_eq_pad:
        "(\<lambda>kk :: nat. go_dir (if kk = 0 then dir.R else dir.N) (?n_Sk kk))
         = ?n_SSk"
        by (rule ext) simp
      have step_to_pad_norm:
        "(Config\<^sub>M (s_tm M, init_offset, init_buffer (le_tm M),
                      init_dest, VFwd) ?ts ?n_Sk,
           Config\<^sub>M (s_tm M, init_offset, init_buffer (le_tm M),
                      init_dest, VFwdPad) ?ts ?n_SSk)
            \<in> mttm_step (alphabet_enlarge_delta M)"
        using step_to_pad post_eq_pad by simp
      have step_to_pad_init:
        "(Config\<^sub>M (s_tm M, init_stage (le_tm M)) ?ts ?n_Sk,
           Config\<^sub>M (s_tm M, init_offset, init_buffer (le_tm M),
                      init_dest, VFwdPad) ?ts ?n_SSk)
            \<in> mttm_step (alphabet_enlarge_delta M)"
        using step_to_pad_norm unfolding stage_eq by simp
      have post_sweep_VFwdPad:
        "(?init,
           Config\<^sub>M (s_tm M, init_offset, init_buffer (le_tm M),
                      init_dest, VFwdPad) ?ts ?n_SSk)
            \<in> mttm_step (alphabet_enlarge_delta M) ^^ Suc (Suc k)"
        by (rule relpow_Suc_I[OF sweep step_to_pad_init])
      have SSk_pos: "1 \<le> Suc (Suc k)" by simp
      have SSk_le: "Suc (Suc k) \<le> length w" using Sk_lt by linarith
      have read_at_SSk: "?ts 0 (Suc (Suc k)) = w ! Suc k"
        using ae_init_config_tape_input[OF SSk_pos SSk_le kpos] by simp
      have wSk_in_set: "w ! Suc k \<in> set w" using SSk_le by auto
      have gamma_SSk:
        "\<forall>kk :: nat. ?ts kk (?n_SSk kk) \<in> gamma_block (\<Gamma>_tm M)"
        using gamma_all by simp
      \<comment> \<open>Sub-case on \<open>w ! Suc k\<close>: \<open>bl_block\<close> (passes via
          \<open>pad_to_ret\<close>) or non-\<open>bl_block\<close> (rejects via \<open>pad_reject\<close>).\<close>
      consider
          (pad_pass) "w ! Suc k = bl_block (bl_tm M)"
        | (pad_reject) "w ! Suc k \<noteq> bl_block (bl_tm M)"
        by blast
      thus ?thesis
      proof cases
        case pad_pass
        have read_bl_SSk: "?ts 0 (?n_SSk 0) = bl_block (bl_tm M)"
          using read_at_SSk pad_pass by simp
        have step_pad_to_ret:
          "(Config\<^sub>M (s_tm M, init_offset, init_buffer (le_tm M),
                        init_dest, VFwdPad) ?ts ?n_SSk,
             Config\<^sub>M (s_tm M, init_offset, init_buffer (le_tm M),
                        init_dest, VRet) ?ts ?n_SSk)
              \<in> mttm_step (alphabet_enlarge_delta M)"
          by (rule ae_step_val_pad_to_ret[where ts = ?ts and n = ?n_SSk,
                OF s_in_Q read_bl_SSk bt_all init_stage_tail
                   gamma_SSk buf_gamma_init])
        have post_sweep_VRet:
          "(?init,
             Config\<^sub>M (s_tm M, init_offset, init_buffer (le_tm M),
                        init_dest, VRet) ?ts ?n_SSk)
              \<in> mttm_step (alphabet_enlarge_delta M) ^^ Suc (Suc (Suc k))"
          by (rule relpow_Suc_I[OF post_sweep_VFwdPad step_pad_to_ret])
        have non_le_SSk: "\<forall>i. 1 \<le> i \<and> i \<le> Suc (Suc k)
                              \<longrightarrow> ?ts 0 i \<noteq> LE_block (le_tm M)"
        proof (intro allI impI)
          fix i assume i_range: "1 \<le> i \<and> i \<le> Suc (Suc k)"
          have i_pos: "1 \<le> i" using i_range by simp
          have i_le_lw: "i \<le> length w" using i_range SSk_le by linarith
          have eq: "?ts 0 i = w ! (i - 1)"
            using ae_init_config_tape_input[OF i_pos i_le_lw kpos] by simp
          have "w ! (i - 1) \<in> set w" using i_pos i_le_lw by auto
          thus "?ts 0 i \<noteq> LE_block (le_tm M)" using LE_notin eq by auto
        qed
        have ret_arrow:
          "(\<forall>i. 1 \<le> i \<and> i \<le> Suc (Suc k)
                \<longrightarrow> ?ts 0 i \<noteq> LE_block (le_tm M))
           \<longrightarrow> (Config\<^sub>M (s_tm M, init_offset, init_buffer (le_tm M),
                            init_dest, VRet) ?ts ?n_SSk,
                Config\<^sub>M (s_tm M, init_offset, init_buffer (le_tm M),
                            init_dest, SS1) ?ts (\<lambda>_. 0))
                \<in> mttm_step (alphabet_enlarge_delta M)
                    ^^ Suc (Suc (Suc k))"
          by (rule ae_validation_ret_sweep[OF s_in_Q tape_le gamma_all
                                          buf_gamma_init bt_all init_stage_tail])
        have ret_chain:
          "(Config\<^sub>M (s_tm M, init_offset, init_buffer (le_tm M),
                        init_dest, VRet) ?ts ?n_SSk,
             Config\<^sub>M (s_tm M, init_offset, init_buffer (le_tm M),
                        init_dest, SS1) ?ts (\<lambda>_. 0))
              \<in> mttm_step (alphabet_enlarge_delta M)
                  ^^ Suc (Suc (Suc k))"
          using ret_arrow non_le_SSk by (rule mp)
        have full_chain:
          "(?init,
             Config\<^sub>M (s_tm M, init_offset, init_buffer (le_tm M),
                        init_dest, SS1) ?ts (\<lambda>_. 0))
              \<in> mttm_step (alphabet_enlarge_delta M)
                  ^^ (Suc (Suc (Suc k)) + Suc (Suc (Suc k)))"
        proof -
          have comp:
            "(?init,
               Config\<^sub>M (s_tm M, init_offset, init_buffer (le_tm M),
                          init_dest, SS1) ?ts (\<lambda>_. 0))
                \<in> mttm_step (alphabet_enlarge_delta M)
                    ^^ Suc (Suc (Suc k))
                  O mttm_step (alphabet_enlarge_delta M)
                    ^^ Suc (Suc (Suc k))"
            using post_sweep_VRet ret_chain by (rule relcompI)
          thus ?thesis by (simp only: relpow_add)
        qed
        have bound:
          "Suc (Suc (Suc k)) + Suc (Suc (Suc k)) \<le> 2 * length w + 4"
          using Sk_lt by linarith
        have state_eq:
          "case mt_state (Config\<^sub>M (s_tm M, init_offset,
                                         init_buffer (le_tm M),
                                         init_dest, SS1) ?ts (\<lambda>_. 0))
              of (qM', _, _, _, idx) \<Rightarrow> idx = SS1 \<or> qM' = r_tm M"
          by simp
        show ?thesis by (rule that[OF bound full_chain state_eq])
      next
        case pad_reject
        have read_nbl_SSk: "?ts 0 (?n_SSk 0) \<noteq> bl_block (bl_tm M)"
          using read_at_SSk pad_reject by simp
        have step_pad_rej:
          "(Config\<^sub>M (s_tm M, init_offset, init_buffer (le_tm M),
                        init_dest, VFwdPad) ?ts ?n_SSk,
             Config\<^sub>M (r_tm M, init_stage (le_tm M)) ?ts ?n_SSk)
              \<in> mttm_step (alphabet_enlarge_delta M)"
          by (rule ae_step_val_pad_reject[where ts = ?ts and n = ?n_SSk,
                OF vM s_in_Q read_nbl_SSk bt_all init_stage_tail
                   gamma_SSk buf_gamma_init])
        have full_chain:
          "(?init, Config\<^sub>M (r_tm M, init_stage (le_tm M)) ?ts ?n_SSk)
              \<in> mttm_step (alphabet_enlarge_delta M)
                  ^^ Suc (Suc (Suc k))"
          by (rule relpow_Suc_I[OF post_sweep_VFwdPad step_pad_rej])
        have bound: "Suc (Suc (Suc k)) \<le> 2 * length w + 4"
          using Sk_lt by linarith
        have state_eq:
          "case mt_state (Config\<^sub>M (r_tm M, init_stage (le_tm M))
                                       ?ts ?n_SSk)
              of (qM', _, _, _, idx) \<Rightarrow> idx = SS1 \<or> qM' = r_tm M"
          by (simp add: init_stage_def)
        show ?thesis by (rule that[OF bound full_chain state_eq])
      qed
    next
      case case_noncan
      have read_nle: "?ts 0 (?n_Sk 0) \<noteq> LE_block (le_tm M)"
        using read_at_Sk w_k_neq_le by simp
      have read_nbl: "?ts 0 (?n_Sk 0) \<noteq> bl_block (bl_tm M)"
        using read_at_Sk case_noncan(2) by simp
      have read_ncan: "\<not> is_canonical_block (bl_tm M) (?ts 0 (?n_Sk 0))"
        using read_at_Sk case_noncan(1) by simp
      have gamma_Sk:
        "\<forall>kk :: nat. ?ts kk (?n_Sk kk) \<in> gamma_block (\<Gamma>_tm M)"
        using gamma_all by simp
      have step_rej:
        "(Config\<^sub>M (s_tm M, init_offset, init_buffer (le_tm M),
                      init_dest, VFwd) ?ts ?n_Sk,
           Config\<^sub>M (r_tm M, init_stage (le_tm M)) ?ts ?n_Sk)
            \<in> mttm_step (alphabet_enlarge_delta M)"
        by (rule ae_step_val_fwd_reject[where ts = ?ts and n = ?n_Sk,
              OF vM s_in_Q s_neq_t s_neq_r read_nle read_nbl read_ncan
              bt_all init_stage_tail gamma_Sk buf_gamma_init])
      have step_rej_init:
        "(Config\<^sub>M (s_tm M, init_stage (le_tm M)) ?ts ?n_Sk,
           Config\<^sub>M (r_tm M, init_stage (le_tm M)) ?ts ?n_Sk)
            \<in> mttm_step (alphabet_enlarge_delta M)"
        using step_rej unfolding stage_eq by simp
      have full_chain:
        "(?init, Config\<^sub>M (r_tm M, init_stage (le_tm M)) ?ts ?n_Sk)
            \<in> mttm_step (alphabet_enlarge_delta M) ^^ Suc (Suc k)"
        by (rule relpow_Suc_I[OF sweep step_rej_init])
      have bound: "Suc (Suc k) \<le> 2 * length w + 4" using k_lt by linarith
      have state_eq:
        "case mt_state (Config\<^sub>M (r_tm M, init_stage (le_tm M)) ?ts ?n_Sk)
            of (qM', _, _, _, idx) \<Rightarrow> idx = SS1 \<or> qM' = r_tm M"
        by (simp add: init_stage_def)
      show ?thesis by (rule that[OF bound full_chain state_eq])
    qed
  qed
qed

end
