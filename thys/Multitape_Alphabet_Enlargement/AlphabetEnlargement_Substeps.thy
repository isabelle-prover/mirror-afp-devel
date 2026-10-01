theory AlphabetEnlargement_Substeps
  imports AlphabetEnlargement_Defs
begin

subsection \<open>Per-substep transition relations\<close>

text \<open>\<open>\<delta>'\<close> is decomposed into named per-substep relations for the
  validation and simulation phases.  Validation: 8 relations
  (forward LE-skip / pure / padded / non-canonical-reject /
  end-of-input; padded end-of-input / padded-reject; return
  step / return-LE-to-Sim).  Simulation: 8 relations
  (SS1\<open>\<rightarrow>\<close>SS2, \<open>\<dots>\<close>, SS7\<open>\<rightarrow>\<close>SS8, SS8\<open>\<rightarrow>\<close>SS1).
  Total: 16 relations.

  The substrate transition shape is
  \<open>(q, a, q', a', d)\<close> with state \<open>'q \<times> ae_stage\<close>, tape
  symbol \<open>'c \<Rightarrow> 'a\<close>.  Source-state constraint
  \<open>q \<in> Q \<and> q \<noteq> t \<and> q \<noteq> r\<close> matches substrate \<open>\<delta>_set\<close>
  for VFwd-source relations (whose \<open>substep_idx\<close> coincides with
  \<open>t', r'\<close>'s); for the other phases the \<open>substep_idx\<close> mismatch
  itself rules out source = \<open>t'\<close> / \<open>r'\<close>.\<close>

text \<open>Validation, VFwd, advance: read either \<open>LE_block le_M\<close>
  (initial step from position 0) or a pure block
  (no blanks); R move on tape 0; N moves on other tapes;
  phase stays \<open>VFwd\<close>.  No write change.\<close>

definition ae_delta_val_fwd_advance ::
  "('q, 'a) mttm
    \<Rightarrow> (('q \<times> ('a, 'c :: enum) ae_stage)
        \<times> (nat \<Rightarrow> ('c \<Rightarrow> 'a))
        \<times> ('q \<times> ('a, 'c) ae_stage)
        \<times> (nat \<Rightarrow> ('c \<Rightarrow> 'a))
        \<times> (nat \<Rightarrow> dir)) set" where
  "ae_delta_val_fwd_advance M =
    {((q, ofs, buf, dest, VFwd), a,
       (q, ofs, buf, dest, VFwd), a, d) |
     q ofs buf dest a d.
       q \<in> Q_tm M \<and> q \<noteq> t_tm M \<and> q \<noteq> r_tm M
       \<and> (a 0 = LE_block (le_tm M)
           \<or> is_pure_block (bl_tm M) (a 0))
       \<and> (\<forall>j\<ge>k_tm M. a j = bl_block (bl_tm M))
       \<and> d = (\<lambda>k. if k = 0 then dir.R else dir.N)}"

text \<open>Validation, VFwd \<open>\<rightarrow>\<close> VFwdPad: read a trailing-padded
  block on tape 0; R move on tape 0; N moves on other
  tapes; phase becomes VFwdPad.  No write change.\<close>

definition ae_delta_val_fwd_to_padded ::
  "('q, 'a) mttm
    \<Rightarrow> (('q \<times> ('a, 'c :: enum) ae_stage)
        \<times> (nat \<Rightarrow> ('c \<Rightarrow> 'a))
        \<times> ('q \<times> ('a, 'c) ae_stage)
        \<times> (nat \<Rightarrow> ('c \<Rightarrow> 'a))
        \<times> (nat \<Rightarrow> dir)) set" where
  "ae_delta_val_fwd_to_padded M =
    {((q, ofs, buf, dest, VFwd), a,
       (q, ofs, buf, dest, VFwdPad), a, d) |
     q ofs buf dest a d.
       q \<in> Q_tm M \<and> q \<noteq> t_tm M \<and> q \<noteq> r_tm M
       \<and> is_padded_block (bl_tm M) (a 0)
       \<and> (\<forall>j\<ge>k_tm M. a j = bl_block (bl_tm M))
       \<and> d = (\<lambda>k. if k = 0 then dir.R else dir.N)}"

text \<open>Validation, VFwd reject: read a non-canonical block
  on tape 0 (in \<open>\<Sigma>'\<close> but neither pure nor padded — blanks in
  non-trailing positions); N moves uniformly; transition to
  \<open>r_M'\<close> (= the canonical reject state of \<open>M'\<close>).\<close>

definition ae_delta_val_fwd_reject ::
  "('q, 'a) mttm
    \<Rightarrow> (('q \<times> ('a, 'c :: enum) ae_stage)
        \<times> (nat \<Rightarrow> ('c \<Rightarrow> 'a))
        \<times> ('q \<times> ('a, 'c) ae_stage)
        \<times> (nat \<Rightarrow> ('c \<Rightarrow> 'a))
        \<times> (nat \<Rightarrow> dir)) set" where
  "ae_delta_val_fwd_reject M =
    {((q, ofs, buf, dest, VFwd), a,
       (r_tm M, init_stage (le_tm M)), a, d) |
     q ofs buf dest a d.
       q \<in> Q_tm M \<and> q \<noteq> t_tm M \<and> q \<noteq> r_tm M
       \<and> a 0 \<noteq> LE_block (le_tm M)
       \<and> a 0 \<noteq> bl_block (bl_tm M)
       \<and> \<not> is_canonical_block (bl_tm M) (a 0)
       \<and> (\<forall>j\<ge>k_tm M. a j = bl_block (bl_tm M))
       \<and> d = (\<lambda>_. dir.N)}"

text \<open>Validation, VFwd end-of-input: read \<open>bl_block bl_M\<close>
  (past the encoded input); N moves; transition to VRet to
  begin the return scan.\<close>

definition ae_delta_val_fwd_to_ret ::
  "('q, 'a) mttm
    \<Rightarrow> (('q \<times> ('a, 'c :: enum) ae_stage)
        \<times> (nat \<Rightarrow> ('c \<Rightarrow> 'a))
        \<times> ('q \<times> ('a, 'c) ae_stage)
        \<times> (nat \<Rightarrow> ('c \<Rightarrow> 'a))
        \<times> (nat \<Rightarrow> dir)) set" where
  "ae_delta_val_fwd_to_ret M =
    {((q, ofs, buf, dest, VFwd), a,
       (q, ofs, buf, dest, VRet), a, d) |
     q ofs buf dest a d.
       q \<in> Q_tm M \<and> q \<noteq> t_tm M \<and> q \<noteq> r_tm M
       \<and> a 0 = bl_block (bl_tm M)
       \<and> (\<forall>j\<ge>k_tm M. a j = bl_block (bl_tm M))
       \<and> d = (\<lambda>_. dir.N)}"

text \<open>Validation, VFwdPad end-of-input: read \<open>bl_block bl_M\<close>;
  N moves; transition to VRet.  Same as the VFwd version
  except the source phase.\<close>

definition ae_delta_val_pad_to_ret ::
  "('q, 'a) mttm
    \<Rightarrow> (('q \<times> ('a, 'c :: enum) ae_stage)
        \<times> (nat \<Rightarrow> ('c \<Rightarrow> 'a))
        \<times> ('q \<times> ('a, 'c) ae_stage)
        \<times> (nat \<Rightarrow> ('c \<Rightarrow> 'a))
        \<times> (nat \<Rightarrow> dir)) set" where
  "ae_delta_val_pad_to_ret M =
    {((q, ofs, buf, dest, VFwdPad), a,
       (q, ofs, buf, dest, VRet), a, d) |
     q ofs buf dest a d.
       q \<in> Q_tm M
       \<and> a 0 = bl_block (bl_tm M)
       \<and> (\<forall>j\<ge>k_tm M. a j = bl_block (bl_tm M))
       \<and> d = (\<lambda>_. dir.N)}"

text \<open>Validation, VFwdPad reject: read anything on tape 0 other
  than \<open>bl_block bl_M\<close>.  This signals a non-blank block
  appearing after the trailing-padded block.  N moves;
  transition to \<open>r_M'\<close>.\<close>

definition ae_delta_val_pad_reject ::
  "('q, 'a) mttm
    \<Rightarrow> (('q \<times> ('a, 'c :: enum) ae_stage)
        \<times> (nat \<Rightarrow> ('c \<Rightarrow> 'a))
        \<times> ('q \<times> ('a, 'c) ae_stage)
        \<times> (nat \<Rightarrow> ('c \<Rightarrow> 'a))
        \<times> (nat \<Rightarrow> dir)) set" where
  "ae_delta_val_pad_reject M =
    {((q, ofs, buf, dest, VFwdPad), a,
       (r_tm M, init_stage (le_tm M)), a, d) |
     q ofs buf dest a d.
       q \<in> Q_tm M
       \<and> a 0 \<noteq> bl_block (bl_tm M)
       \<and> (\<forall>j\<ge>k_tm M. a j = bl_block (bl_tm M))
       \<and> d = (\<lambda>_. dir.N)}"

text \<open>Validation, VRet step: read a non-LE block on tape 0
  (during the return scan); L move on tape 0; N moves on other
  tapes; phase stays VRet.\<close>

definition ae_delta_val_ret_step ::
  "('q, 'a) mttm
    \<Rightarrow> (('q \<times> ('a, 'c :: enum) ae_stage)
        \<times> (nat \<Rightarrow> ('c \<Rightarrow> 'a))
        \<times> ('q \<times> ('a, 'c) ae_stage)
        \<times> (nat \<Rightarrow> ('c \<Rightarrow> 'a))
        \<times> (nat \<Rightarrow> dir)) set" where
  "ae_delta_val_ret_step M =
    {((q, ofs, buf, dest, VRet), a,
       (q, ofs, buf, dest, VRet), a, d) |
     q ofs buf dest a d.
       q \<in> Q_tm M
       \<and> a 0 \<noteq> LE_block (le_tm M)
       \<and> (\<forall>j\<ge>k_tm M. a j = bl_block (bl_tm M))
       \<and> d = (\<lambda>k. if k = 0 then dir.L else dir.N)}"

text \<open>Validation, VRet \<open>\<rightarrow>\<close> Sim: read \<open>LE_block le_M\<close> on tape 0
  (return scan reached position 0); N moves uniformly (head
  stays at position 0, the LE-block); phase becomes Sim with
  \<open>substep_idx\<close> = SS1.

  The N move on tape 0 — rather than R — leaves \<open>M'\<close>'s head at
  block 0 (\<open>LE_M'\<close>) post-validation, so the simulation
  phase's first stage runs in LE-stage mode
  (\<open>home = LE_M'\<close>) and the c-fold compute correctly simulates
  \<open>M\<close>'s first step from \<open>(s_M, LE)\<close>.  See \<open>bp_advance_le\<close>
  below for how the c-fold compute handles M's first R-move out
  of LE.\<close>

definition ae_delta_val_ret_to_sim ::
  "('q, 'a) mttm
    \<Rightarrow> (('q \<times> ('a, 'c :: enum) ae_stage)
        \<times> (nat \<Rightarrow> ('c \<Rightarrow> 'a))
        \<times> ('q \<times> ('a, 'c) ae_stage)
        \<times> (nat \<Rightarrow> ('c \<Rightarrow> 'a))
        \<times> (nat \<Rightarrow> dir)) set" where
  "ae_delta_val_ret_to_sim M =
    {((q, ofs, buf, dest, VRet), a,
       (q, ofs, buf, dest, SS1), a, d) |
     q ofs buf dest a d.
       q \<in> Q_tm M
       \<and> a 0 = LE_block (le_tm M)
       \<and> (\<forall>j\<ge>k_tm M. a j = bl_block (bl_tm M))
       \<and> d = (\<lambda>_. dir.N)}"

text \<open>SS1 \<open>\<rightarrow>\<close> SS2: read home into buffer; per-tape move L
  (steady-state) or N (LE-stage).  No write change
  (\<open>a' = a\<close>); no \<open>M\<close>-state advance.  Buffer-phase substep 1.\<close>

definition ae_delta_ss1_ss2 ::
  "('q, 'a) mttm
    \<Rightarrow> (('q \<times> ('a, 'c :: enum) ae_stage)
        \<times> (nat \<Rightarrow> ('c \<Rightarrow> 'a))
        \<times> ('q \<times> ('a, 'c) ae_stage)
        \<times> (nat \<Rightarrow> ('c \<Rightarrow> 'a))
        \<times> (nat \<Rightarrow> dir)) set" where
  "ae_delta_ss1_ss2 M =
    {((q, ofs, buf, dest, SS1), a,
       (q, ofs, buf', dest, SS2), a, d) |
     q ofs buf dest a buf' d.
       q \<in> Q_tm M \<and> q \<noteq> t_tm M \<and> q \<noteq> r_tm M
       \<and> (\<forall>j\<ge>k_tm M. a j = bl_block (bl_tm M))
       \<and> buf' = (\<lambda>k. if k < k_tm M
                     then (fst (buf k), a k, snd (snd (buf k)))
                     else init_buffer (le_tm M) k)
       \<and> d = (\<lambda>k. if k < k_tm M
                  then (if a k = LE_block (le_tm M) then dir.N else dir.L)
                  else dir.N)}"

text \<open>SS2 \<open>\<rightarrow>\<close> SS3: read left into buffer (or placeholder for
  LE-stage); per-tape move R (steady-state, returning to home)
  or N (LE-stage, staying at home).  Buffer-phase substep 2.

  In LE-stage (\<open>buf k.home = LE_M'\<close>), the read is again
  \<open>LE_M'\<close> (head didn't move at SS1) and \<open>buf' k.left\<close> is set to
  \<open>bl_block bl_M\<close> as a semantic placeholder.\<close>

definition ae_delta_ss2_ss3 ::
  "('q, 'a) mttm
    \<Rightarrow> (('q \<times> ('a, 'c :: enum) ae_stage)
        \<times> (nat \<Rightarrow> ('c \<Rightarrow> 'a))
        \<times> ('q \<times> ('a, 'c) ae_stage)
        \<times> (nat \<Rightarrow> ('c \<Rightarrow> 'a))
        \<times> (nat \<Rightarrow> dir)) set" where
  "ae_delta_ss2_ss3 M =
    {((q, ofs, buf, dest, SS2), a,
       (q, ofs, buf', dest, SS3), a, d) |
     q ofs buf dest a buf' d.
       q \<in> Q_tm M \<and> q \<noteq> t_tm M \<and> q \<noteq> r_tm M
       \<and> (\<forall>j\<ge>k_tm M. a j = bl_block (bl_tm M))
       \<and> buf' = (\<lambda>k. if k < k_tm M
                     then (let (l, h, r) = buf k in
                            (if h = LE_block (le_tm M)
                               then bl_block (bl_tm M)
                               else a k,
                             h, r))
                     else init_buffer (le_tm M) k)
       \<and> d = (\<lambda>k. if k < k_tm M
                  then (if (fst (snd (buf k))) = LE_block (le_tm M)
                         then dir.N else dir.R)
                  else dir.N)}"

text \<open>SS3 \<open>\<rightarrow>\<close> SS4: uniform R move per tape (no buffer update,
  no \<open>M\<close>-state advance).  Both steady-state and LE-stage move
  R (steady-state from home to right; LE-stage from home (= LE)
  to right neighbour, satisfying \<open>\<delta>LE\<close> since R is allowed
  from LE).  Buffer-phase substep 3.\<close>

definition ae_delta_ss3_ss4 ::
  "('q, 'a) mttm
    \<Rightarrow> (('q \<times> ('a, 'c :: enum) ae_stage)
        \<times> (nat \<Rightarrow> ('c \<Rightarrow> 'a))
        \<times> ('q \<times> ('a, 'c) ae_stage)
        \<times> (nat \<Rightarrow> ('c \<Rightarrow> 'a))
        \<times> (nat \<Rightarrow> dir)) set" where
  "ae_delta_ss3_ss4 M =
    {((q, ofs, buf, dest, SS3), a,
       (q, ofs, buf, dest, SS4), a, d) |
     q ofs buf dest a d.
       q \<in> Q_tm M \<and> q \<noteq> t_tm M \<and> q \<noteq> r_tm M
       \<and> (\<forall>j\<ge>k_tm M. a j = bl_block (bl_tm M))
       \<and> d = (\<lambda>k. if k < k_tm M then dir.R else dir.N)}"

text \<open>Buffered head position: which buffer slot
  (\<open>AE_Left\<close> / \<open>AE_Home\<close> / \<open>AE_Right\<close>) and which offset
  within that slot.  Internal to the compute substep; the
  output of \<open>m_steps_buffered\<close> projects this onto
  \<open>(nat \<Rightarrow> 'c) \<times> (nat \<Rightarrow> ae_dest)\<close>.\<close>

type_synonym 'c bp = "ae_dest \<times> 'c"

text \<open>Read the symbol at a buffered head position.\<close>

definition read_bp ::
  "(('c :: enum \<Rightarrow> 'a) \<times> ('c \<Rightarrow> 'a) \<times> ('c \<Rightarrow> 'a))
    \<Rightarrow> 'c bp \<Rightarrow> 'a" where
  "read_bp blocks p =
     (let (b, off) = p; (l, h, r) = blocks in
        case b of AE_Left \<Rightarrow> l off
                | AE_Home \<Rightarrow> h off
                | AE_Right \<Rightarrow> r off)"

text \<open>Write a symbol at a buffered head position.\<close>

definition write_bp ::
  "(('c :: enum \<Rightarrow> 'a) \<times> ('c \<Rightarrow> 'a) \<times> ('c \<Rightarrow> 'a))
    \<Rightarrow> 'c bp \<Rightarrow> 'a
    \<Rightarrow> (('c \<Rightarrow> 'a) \<times> ('c \<Rightarrow> 'a) \<times> ('c \<Rightarrow> 'a))" where
  "write_bp blocks p x =
     (let (b, off) = p; (l, h, r) = blocks in
        case b of AE_Left  \<Rightarrow> (l(off := x), h, r)
                | AE_Home  \<Rightarrow> (l, h(off := x), r)
                | AE_Right \<Rightarrow> (l, h, r(off := x)))"

text \<open>Advance a buffered head position by a direction.  Returns
  \<open>None\<close> if the head would exit the 3-block buffer (which by the
  per-\<open>c\<close>-step head-displacement bound of Hopcroft--Ullman
  \<^cite>\<open>\<open>Theorem 12.3\<close> in "Hopcroft1979:introduction"\<close> cannot
  happen during a single \<open>c\<close>-step compute starting from
  \<open>(AE_Home, ofs)\<close>; relations using \<open>bp_advance\<close> filter the
  \<open>None\<close> case as a vacuous side condition).\<close>

definition bp_advance ::
  "('c :: enum) bp \<Rightarrow> dir \<Rightarrow> 'c bp option" where
  "bp_advance p d =
     (let (b, off) = p in
        case d of
          dir.N \<Rightarrow> Some (b, off)
        | dir.R \<Rightarrow>
            (case c_succ off of
               Some off' \<Rightarrow> Some (b, off')
             | None \<Rightarrow>
                 (case b of
                    AE_Left  \<Rightarrow> Some (AE_Home,  c_first)
                  | AE_Home  \<Rightarrow> Some (AE_Right, c_first)
                  | AE_Right \<Rightarrow> None))
        | dir.L \<Rightarrow>
            (case c_pred off of
               Some off' \<Rightarrow> Some (b, off')
             | None \<Rightarrow>
                 (case b of
                    AE_Right \<Rightarrow> Some (AE_Home, c_last)
                  | AE_Home  \<Rightarrow> Some (AE_Left, c_last)
                  | AE_Left  \<Rightarrow> None)))"

text \<open>LE-aware buffered head advance.  Wraps \<open>bp_advance\<close>
  with the substrate-induced LE-skip rule: when the read symbol
  is \<open>le\<close> (i.e., the head is positioned within an \<open>LE_M'\<close>
  block) and the move is R, jump to \<open>(AE_Right, c_first)\<close>
  rather than advancing within the home block.  This corresponds
  to \<open>M\<close>'s actual head crossing from position 0 (LE) to
  position 1 (the first input cell), which the simulation
  correspondence requires as a single bp-step rather than a
  sequence of c within-block bp-steps.

  Rationale: the
  \<open>LE_M'\<close> block is a c-tuple but only its slot 0 represents
  a real \<open>M\<close>-cell; slots 1..c-1 are structural padding.
  \<open>bp_advance\<close>'s standard offset arithmetic would walk through
  these padding slots, which doesn't correspond to any
  \<open>M\<close>-step.  N stays in place (consistent with \<open>M\<close>
  staying at LE on N), L is forbidden by \<open>\<delta>LE\<close> at LE so
  the case is unreachable.\<close>

definition bp_advance_le ::
  "'a \<Rightarrow> 'a \<Rightarrow> ('c :: enum) bp \<Rightarrow> dir \<Rightarrow> 'c bp option" where
  "bp_advance_le le a p d =
     (if a = le \<and> fst p = AE_Home \<and> d = dir.R
        then Some (AE_Right, c_first)
        else bp_advance p d)"

text \<open>Single buffered \<open>M\<close>-step: applies \<open>M\<close>'s \<open>\<delta>\<close> to the
  current per-tape buffered reads, writes the post-symbols
  back into the buffer, and advances each per-tape head
  position via \<open>bp_advance_le\<close> (the LE-aware wrapper around
  \<open>bp_advance\<close>).  The relation is empty
  for configurations whose source \<open>M\<close>-state is halting
  (\<open>M\<close>'s \<open>\<delta>\<close> excludes those) or whose head movement would
  exit the 3-block buffer on any tape.\<close>

definition m_step_buffered ::
  "('q, 'a) mttm
    \<Rightarrow> (('q
         \<times> (nat \<Rightarrow> ('c :: enum \<Rightarrow> 'a) \<times> ('c \<Rightarrow> 'a) \<times> ('c \<Rightarrow> 'a))
         \<times> (nat \<Rightarrow> 'c bp))
        \<times> ('q
           \<times> (nat \<Rightarrow> ('c \<Rightarrow> 'a) \<times> ('c \<Rightarrow> 'a) \<times> ('c \<Rightarrow> 'a))
           \<times> (nat \<Rightarrow> 'c bp))) set" where
  "m_step_buffered M =
     {((q, blocks, pos), (q', blocks', pos')) |
        q blocks pos q' blocks' pos' a a' d.
          (q, a, q', a', d) \<in> delta_tm M
          \<and> (\<forall>k. a k = read_bp (blocks k) (pos k))
          \<and> (\<forall>k. blocks' k = write_bp (blocks k) (pos k) (a' k))
          \<and> (\<forall>k. bp_advance_le (le_tm M) (a k) (pos k) (d k)
                  = Some (pos' k))}"

text \<open>Introduction rule for \<open>m_step_buffered\<close>: package the
  four ingredients (\<open>\<delta>\<close>-tuple, read-from-buffer match,
  write-back, head-advance) into the relational membership
  claim.  Used by the inductive step of
  \<open>ae_m_steps_buffered_correct\<close> (\<open>AlphabetEnlargement.thy\<close>)
  to extend a coupled run by one step.\<close>

lemma m_step_bufferedI:
  fixes M :: "('q, 'a) mttm"
    and a a' :: "nat \<Rightarrow> 'a"
    and d :: "nat \<Rightarrow> dir"
    and blocks blocks' ::
          "nat \<Rightarrow> (('c :: enum \<Rightarrow> 'a) \<times> ('c \<Rightarrow> 'a) \<times> ('c \<Rightarrow> 'a))"
    and pos pos' :: "nat \<Rightarrow> 'c bp"
  assumes "(q, a, q', a', d) \<in> delta_tm M"
      and "\<forall>k. a k = read_bp (blocks k) (pos k)"
      and "\<forall>k. blocks' k = write_bp (blocks k) (pos k) (a' k)"
      and "\<forall>k. bp_advance_le (le_tm M) (a k) (pos k) (d k)
              = Some (pos' k)"
  shows "((q, blocks, pos), (q', blocks', pos')) \<in> m_step_buffered M"
  using assms unfolding m_step_buffered_def by blast

text \<open>Auxiliary: up-to-\<open>c\<close>-step composition of \<open>M\<close>'s \<open>\<delta>\<close> on
  the buffered representation.  Captures the cumulative effect
  of either \<open>c\<close> consecutive \<open>M\<close>-steps, or fewer if \<open>M\<close>
  reaches a halting state (\<open>t_M\<close> / \<open>r_M\<close>) earlier.

  Defined as the union of \<open>n\<close>-fold relational compositions of
  \<open>m_step_buffered M\<close> for \<open>n \<le> c = card (UNIV :: 'c set)\<close>,
  filtered to enforce the early-stop discipline (the run runs
  the full \<open>c\<close> steps unless \<open>M\<close> halts).  This is the
  semantic core of the compute substep (SS4\<open>\<rightarrow>\<close>SS5).\<close>

definition m_steps_buffered ::
  "('q, 'a) mttm
    \<Rightarrow> (('q
         \<times> (nat \<Rightarrow> ('c :: enum \<Rightarrow> 'a) \<times> ('c \<Rightarrow> 'a) \<times> ('c \<Rightarrow> 'a))
         \<times> (nat \<Rightarrow> 'c bp))
        \<times> ('q
           \<times> (nat \<Rightarrow> ('c \<Rightarrow> 'a) \<times> ('c \<Rightarrow> 'a) \<times> ('c \<Rightarrow> 'a))
           \<times> (nat \<Rightarrow> 'c bp))) set" where
  "m_steps_buffered M =
     {(s, s') | s s' n.
        n \<le> card (UNIV :: 'c set)
        \<and> (s, s') \<in> (m_step_buffered M) ^^ n
        \<and> (n = card (UNIV :: 'c set)
            \<or> fst s' \<in> {t_tm M, r_tm M})}"

text \<open>Functionality of \<open>m_step_buffered\<close> under
  \<open>det_mttm M\<close>: a single buffered M-step from a fixed source
  determines the target uniquely.  Threaded through
  \<open>m_step_buffered_relpow_functional\<close> and
  \<open>m_steps_buffered_functional\<close> below into the
  SS4\<open>\<rightarrow>\<close>SS5 compute substep's functionality lemma — the
  16th entry in the per-substep functionality cluster, completing
  it under \<open>det_mttm M\<close>.\<close>

lemma m_step_buffered_functional:
  fixes M :: "('q, 'a) mttm"
  assumes det: "det_mttm M"
    and h1: "((q, blocks, pos), (q1, blocks1, pos1)) \<in> m_step_buffered M"
    and h2: "((q, blocks, pos), (q2, blocks2, pos2)) \<in> m_step_buffered M"
  shows "(q1, blocks1, pos1) = (q2, blocks2, pos2)"
proof -
  from h1 obtain a1 a1' d1 where
      t1: "(q, a1, q1, a1', d1) \<in> delta_tm M"
    and r1: "\<forall>k. a1 k = read_bp (blocks k) (pos k)"
    and w1: "\<forall>k. blocks1 k = write_bp (blocks k) (pos k) (a1' k)"
    and p1: "\<forall>k. bp_advance_le (le_tm M) (a1 k) (pos k) (d1 k)
                    = Some (pos1 k)"
    unfolding m_step_buffered_def by blast
  from h2 obtain a2 a2' d2 where
      t2: "(q, a2, q2, a2', d2) \<in> delta_tm M"
    and r2: "\<forall>k. a2 k = read_bp (blocks k) (pos k)"
    and w2: "\<forall>k. blocks2 k = write_bp (blocks k) (pos k) (a2' k)"
    and p2: "\<forall>k. bp_advance_le (le_tm M) (a2 k) (pos k) (d2 k)
                    = Some (pos2 k)"
    unfolding m_step_buffered_def by blast
  have a_eq: "a1 = a2"
    using r1 r2 by (intro ext) auto
  have t2': "(q, a1, q2, a2', d2) \<in> delta_tm M"
    using t2 a_eq by simp
  from det t1 t2'
  have qad: "(q1, a1', d1) = (q2, a2', d2)"
    unfolding det_mttm_def by blast
  hence q_eq: "q1 = q2" and a'_eq: "a1' = a2'" and d_eq: "d1 = d2"
    by auto
  have b_eq: "blocks1 = blocks2"
    using w1 w2 a'_eq by (intro ext) auto
  have p_eq: "pos1 = pos2"
  proof (intro ext)
    fix k
    have "Some (pos1 k) = Some (pos2 k)"
      using p1 p2 a_eq d_eq by metis
    thus "pos1 k = pos2 k" by simp
  qed
  show ?thesis using q_eq b_eq p_eq by simp
qed

text \<open>Relational-power lift of \<open>m_step_buffered_functional\<close>:
  under \<open>det_mttm M\<close>, n-fold composition is functional too.
  Standard induction-on-n proof using the single-step lemma.\<close>

lemma m_step_buffered_relpow_functional:
  fixes M :: "('q, 'a) mttm"
  assumes det: "det_mttm M"
      and h1: "(s, s1) \<in> (m_step_buffered M) ^^ n"
      and h2: "(s, s2) \<in> (m_step_buffered M) ^^ n"
  shows "s1 = s2"
  using h1 h2
proof (induction n arbitrary: s s1 s2)
  case 0
  thus ?case by simp
next
  case (Suc n)
  from Suc.prems(1) obtain s1' where
      step1: "(s, s1') \<in> m_step_buffered M"
    and rest1: "(s1', s1) \<in> (m_step_buffered M) ^^ n"
    by (meson relpow_Suc_D2)
  from Suc.prems(2) obtain s2' where
      step2: "(s, s2') \<in> m_step_buffered M"
    and rest2: "(s2', s2) \<in> (m_step_buffered M) ^^ n"
    by (meson relpow_Suc_D2)
  obtain q b p where s_eq: "s = (q, b, p)" by (cases s)
  obtain q1' b1' p1' where s1'_eq: "s1' = (q1', b1', p1')" by (cases s1')
  obtain q2' b2' p2' where s2'_eq: "s2' = (q2', b2', p2')" by (cases s2')
  from step1 s_eq s1'_eq
  have st1: "((q, b, p), (q1', b1', p1')) \<in> m_step_buffered M"
    by simp
  from step2 s_eq s2'_eq
  have st2: "((q, b, p), (q2', b2', p2')) \<in> m_step_buffered M"
    by simp
  from m_step_buffered_functional[OF det st1 st2]
  have "(q1', b1', p1') = (q2', b2', p2')" .
  hence s'_eq: "s1' = s2'" using s1'_eq s2'_eq by simp
  show ?case using Suc.IH[OF rest1] rest2 s'_eq by simp
qed

text \<open>From a halt state, no buffered M-step is possible.  Follows
  from \<open>valid_mttm M\<close>'s structural constraint that
  \<open>delta_tm M\<close> has no transitions originating in
  \<open>{t_tm M, r_tm M}\<close>.  Used below to rule out the case
  where the two witnesses of \<open>m_steps_buffered\<close>'s
  functionality argument use different step counts.\<close>

lemma m_step_buffered_no_halt:
  fixes M :: "('q, 'a) mttm"
  assumes vM: "valid_mttm M"
      and halt: "q \<in> {t_tm M, r_tm M}"
  shows "((q, blocks, pos), s') \<notin> m_step_buffered M"
proof
  assume "((q, blocks, pos), s') \<in> m_step_buffered M"
  then obtain a q' a' d where
      st: "(q, a, q', a', d) \<in> delta_tm M"
    unfolding m_step_buffered_def by blast
  from valid_mttm_delta_set[OF vM] st
  have "q \<in> Q_tm M - {t_tm M, r_tm M}" by auto
  with halt show False by auto
qed

text \<open>Functionality of \<open>m_steps_buffered\<close> under
  \<open>det_mttm M\<close>: the bounded-and-halt-truncated buffered
  M-run is functional in its source.

  Argument: from membership we obtain step counts \<open>n1, n2\<close>
  with \<open>n_i \<le> c\<close> and \<open>n_i = c \<or> fst s_i \<in> {t, r}\<close>.
  First show \<open>n1 = n2\<close>: if \<open>n1 < n2\<close> the prefix run
  determines the n1-step state to be \<open>s1\<close> (by
  \<open>m_step_buffered_relpow_functional\<close>), and the
  remaining \<open>n2 - n1 \<ge> 1\<close> steps require a transition
  from \<open>s1\<close>.  The disjunction on \<open>s1\<close> forces either
  \<open>n1 = c\<close> (contradicting \<open>n1 < n2 \<le> c\<close>) or
  \<open>fst s1 \<in> {t, r}\<close>, the latter ruled out by
  \<open>m_step_buffered_no_halt\<close>.  Symmetric for \<open>n2 < n1\<close>.
  With \<open>n1 = n2\<close>, the relpow functional lemma finishes.\<close>

lemma m_steps_buffered_functional:
  fixes M :: "('q, 'a) mttm"
    and s s1 s2 :: "'q
                      \<times> (nat \<Rightarrow> ('c :: enum \<Rightarrow> 'a)
                              \<times> ('c \<Rightarrow> 'a) \<times> ('c \<Rightarrow> 'a))
                      \<times> (nat \<Rightarrow> 'c bp)"
  assumes vM:  "valid_mttm M"
      and det: "det_mttm M"
      and h1:  "(s, s1) \<in> m_steps_buffered M"
      and h2:  "(s, s2) \<in> m_steps_buffered M"
  shows "s1 = s2"
proof -
  let ?c = "card (UNIV :: 'c set)"
  let ?R = "m_step_buffered M"
  from h1 obtain n1 where
      n1_bnd:  "n1 \<le> ?c"
    and n1_run: "(s, s1) \<in> ?R ^^ n1"
    and n1_halt: "n1 = ?c \<or> fst s1 \<in> {t_tm M, r_tm M}"
    unfolding m_steps_buffered_def by blast
  from h2 obtain n2 where
      n2_bnd:  "n2 \<le> ?c"
    and n2_run: "(s, s2) \<in> ?R ^^ n2"
    and n2_halt: "n2 = ?c \<or> fst s2 \<in> {t_tm M, r_tm M}"
    unfolding m_steps_buffered_def by blast

  \<comment> \<open>Sub-lemma: under \<open>m < n\<close>, the run from the m-step
      state cannot extend, contradicting the halt-or-full
      disjunction at the m-step state.\<close>
  have no_extend:
    "\<And>m n s_m s_n.
        (s, s_m) \<in> ?R ^^ m
        \<Longrightarrow> (s, s_n) \<in> ?R ^^ n
        \<Longrightarrow> m < n
        \<Longrightarrow> n \<le> ?c
        \<Longrightarrow> m = ?c \<or> fst s_m \<in> {t_tm M, r_tm M}
        \<Longrightarrow> False"
  proof -
    fix m n :: nat and s_m s_n
    assume rm: "(s, s_m) \<in> ?R ^^ m"
       and rn: "(s, s_n) \<in> ?R ^^ n"
       and mn: "m < n"
       and nc: "n \<le> ?c"
       and hl: "m = ?c \<or> fst s_m \<in> {t_tm M, r_tm M}"
    define k where "k = n - m - 1"
    have k_eq: "n = m + Suc k"
      unfolding k_def using mn by simp
    from rn k_eq have rn': "(s, s_n) \<in> ?R ^^ (m + Suc k)" by simp
    from rn'[unfolded relpow_add]
    obtain s' where
        rpre: "(s, s') \<in> ?R ^^ m"
      and rpost: "(s', s_n) \<in> ?R ^^ Suc k"
      by blast
    from m_step_buffered_relpow_functional[OF det rm rpre]
    have s_eq: "s_m = s'" .
    from rpost obtain s'' where step: "(s', s'') \<in> ?R"
      by (meson relpow_Suc_D2)
    with s_eq have step_sm: "(s_m, s'') \<in> ?R" by simp
    from hl show False
    proof
      assume "m = ?c"
      with k_eq nc show False by linarith
    next
      assume halt: "fst s_m \<in> {t_tm M, r_tm M}"
      obtain q b p where sm_eq: "s_m = (q, b, p)" by (cases s_m)
      from halt sm_eq have q_halt: "q \<in> {t_tm M, r_tm M}" by simp
      from step_sm sm_eq have "((q, b, p), s'') \<in> ?R" by simp
      with m_step_buffered_no_halt[OF vM q_halt] show False by blast
    qed
  qed

  \<comment> \<open>The step counts must be equal.\<close>
  have n_eq: "n1 = n2"
  proof (rule ccontr)
    assume "n1 \<noteq> n2"
    then consider (lt) "n1 < n2" | (gt) "n2 < n1" by linarith
    thus False
    proof cases
      case lt
      from no_extend[OF n1_run n2_run lt n2_bnd n1_halt] show False .
    next
      case gt
      from no_extend[OF n2_run n1_run gt n1_bnd n2_halt] show False .
    qed
  qed
  from n1_run n2_run n_eq
  show ?thesis
    using m_step_buffered_relpow_functional[OF det] by metis
qed

text \<open>Linearisation helpers for the 3-block buffer.  These map
  \<open>(block, offset)\<close>-pairs to indices in \<open>[0, 3c)\<close> and read
  the symbol at a linearised buffer index.  Used to express the
  buffered compute's correctness as a contiguous-tape-window
  match.\<close>

definition bp_linear :: "('c :: enum) bp \<Rightarrow> nat" where
  "bp_linear p =
     (case fst p of
        AE_Left  \<Rightarrow> 0
      | AE_Home  \<Rightarrow> card (UNIV :: 'c set)
      | AE_Right \<Rightarrow> 2 * card (UNIV :: 'c set))
     + c_idx (snd p)"

definition buf_lin_at ::
  "(('c :: enum \<Rightarrow> 'a) \<times> ('c \<Rightarrow> 'a) \<times> ('c \<Rightarrow> 'a))
    \<Rightarrow> nat \<Rightarrow> 'a" where
  "buf_lin_at blocks i =
     (let c = card (UNIV :: 'c set);
          enum_c = (enum_class.enum :: 'c list);
          (l, h, r) = blocks in
        if i < c then l (enum_c ! i)
        else if i < 2 * c then h (enum_c ! (i - c))
        else r (enum_c ! (i - 2 * c)))"

text \<open>Window invariant on a 3-block buffer plus buffered head:
  (1) the buffer's linearisation matches an M-tape window of
  3c contiguous positions starting at \<open>p_start\<close>; (2) the
  buffered head decodes to the actual M-head position via
  \<open>bp_linear\<close>; (3) the entire window lies in the non-LE
  region of the M-tape (\<open>p_start \<ge> 1\<close>).  The non-LE
  precondition keeps the predicate steady-state; the LE-edge
  case (window intersects M-position 0) is handled by a
  separate lemma at the simulation level.\<close>

definition ae_window_invariant ::
  "(nat \<Rightarrow> 'a) \<Rightarrow> nat
    \<Rightarrow> ('c :: enum) bp
    \<Rightarrow> (('c \<Rightarrow> 'a) \<times> ('c \<Rightarrow> 'a) \<times> ('c \<Rightarrow> 'a))
    \<Rightarrow> nat \<Rightarrow> bool" where
  "ae_window_invariant tM nM bp blocks p_start \<longleftrightarrow>
     p_start \<ge> 1
     \<and> nM = p_start + bp_linear bp
     \<and> (\<forall>i. i < 3 * card (UNIV :: 'c set)
              \<longrightarrow> tM (p_start + i) = buf_lin_at blocks i)"

text \<open>LE-edge analogue of \<open>ae_window_invariant\<close> for the
  \<open>le1\<close> sub-case: \<open>M'\<close>'s head is at block 1 (the first
  content block), so the buffer's left slot is
  \<open>LE_block le\<close> (block 0's content under
  \<open>ae_init_config\<close>) and M's tape position lies in
  \<open>{0, \<dots>, 2c}\<close>.  The home and right buffer slots linearise
  to an M-tape window starting at position 1; the left buffer
  slot is \<open>LE_block\<close> by construction, with no claim about
  M-tape positions \<open>0, \<dots>, c-1\<close> beyond \<open>tM 0 = le\<close>.  Under
  \<open>\<delta>LE\<close> on \<open>delta_tm M\<close>, M's buffered trajectory in this
  setting visits only \<open>(AE_Left, c_last)\<close> within the left
  block (when reading LE), never the other left slots, so
  the buffer\<open>\<leftrightarrow>\<close>tape mismatch there is harmless.

  The buffered head \<open>bp\<close> decodes to the actual M-tape position
  by a three-way case-split (\<open>AE_Left c_last \<mapsto> 0\<close>,
  \<open>AE_Home \<mapsto> 1 + c_idx ofs\<close>,
  \<open>AE_Right \<mapsto> 1 + c + c_idx ofs\<close>) so the predicate serves
  as both SS4 entry condition (\<open>bp = (AE_Home, ofs)\<close>) and
  post-compute condition (\<open>bp\<close> anywhere in the three-block
  buffer except \<open>AE_Left\<close> at non-\<open>c_last\<close> offsets, which the
  \<open>\<delta>LE\<close>-respecting buffered trajectory cannot reach).\<close>

definition ae_window_invariant_le1 ::
  "(nat \<Rightarrow> 'a) \<Rightarrow> nat
    \<Rightarrow> ('c :: enum) bp
    \<Rightarrow> (('c \<Rightarrow> 'a) \<times> ('c \<Rightarrow> 'a) \<times> ('c \<Rightarrow> 'a))
    \<Rightarrow> 'a \<Rightarrow> bool" where
  "ae_window_invariant_le1 tM nM bp blocks le \<longleftrightarrow>
     fst blocks = LE_block le
     \<and> tM 0 = le
     \<and> (case fst bp of
          AE_Left  \<Rightarrow> snd bp = c_last \<and> nM = 0
        | AE_Home  \<Rightarrow> nM = Suc (c_idx (snd bp))
        | AE_Right \<Rightarrow> nM = Suc (card (UNIV :: 'c set) + c_idx (snd bp)))
     \<and> (\<forall>i. i < 2 * card (UNIV :: 'c set)
              \<longrightarrow> tM (Suc i)
                    = buf_lin_at blocks (card (UNIV :: 'c set) + i))"

text \<open>LE-edge analogue of \<open>ae_window_invariant\<close> for the
  \<open>le0\<close> sub-case: \<open>M'\<close>'s head is at block 0 (the LE
  block itself).  Buffer shape: the home slot is
  \<open>LE_block le\<close> (block 0's content), the right slot is
  block 1's content (real input/blank), and the left slot
  holds an arbitrary sentinel (SS2 \<open>\<rightarrow>\<close> SS3 installs
  \<open>bl_block (bl_tm M)\<close>; the predicate doesn't constrain it
  because M's buffered trajectory cannot reach the left
  block under \<open>\<delta>LE\<close> — M starts at home reading LE,
  can only move N or R, and any R-move from home reading LE
  jumps via \<open>bp_advance_le\<close>'s special case to
  \<open>(AE_Right, c_first)\<close>, bypassing the rest of home and
  never visiting left).

  The buffered head \<open>bp\<close> decodes:
  \<open>AE_Home \<mapsto> 0\<close> (M sits at LE regardless of
  \<open>snd bp\<close>, since home is all-LE) and
  \<open>AE_Right \<mapsto> 1 + c_idx ofs\<close> (M is in block 1's
  range).  \<open>AE_Left\<close> is excluded.

  Only the right slot's linearisation is asserted: the home
  slot is fully LE (so linearisation matches \<open>tM\<close> only at
  position 0, which \<open>tM 0 = le\<close> covers; the rest of home's
  linearisation is fake but unread).\<close>

definition ae_window_invariant_le0 ::
  "(nat \<Rightarrow> 'a) \<Rightarrow> nat
    \<Rightarrow> ('c :: enum) bp
    \<Rightarrow> (('c \<Rightarrow> 'a) \<times> ('c \<Rightarrow> 'a) \<times> ('c \<Rightarrow> 'a))
    \<Rightarrow> 'a \<Rightarrow> bool" where
  "ae_window_invariant_le0 tM nM bp blocks le \<longleftrightarrow>
     fst (snd blocks) = LE_block le
     \<and> tM 0 = le
     \<and> (case fst bp of
          AE_Home  \<Rightarrow> nM = 0
        | AE_Right \<Rightarrow> nM = Suc (c_idx (snd bp))
        | AE_Left  \<Rightarrow> False)
     \<and> (\<forall>i. i < card (UNIV :: 'c set)
              \<longrightarrow> tM (Suc i)
                    = buf_lin_at blocks (2 * card (UNIV :: 'c set) + i))"

text \<open>Per-tape unified window invariant for the SS4\<open>\<rightarrow>\<close>SS5
  trace toolkit.  Hybrid encapsulation of the three regime-specific
  sibling predicates: one extra parameter \<open>pos\<close> (the per-tape
  \<open>mt_pos c' k\<close> at SS4 entry, a frozen value during the
  buffered \<open>M\<close>-side run) selects which sibling fires.  Each
  regime is expressed as an implication, so the dispatch is by
  partition of \<open>pos :: nat\<close> into \<open>0\<close> / \<open>1\<close> /
  \<open>\<ge> 2\<close> — exactly one implication is non-vacuous on any
  fixed \<open>pos\<close>.

  Design choice rationale: the conjunction-of-implications form
  avoids forcing consumers to disjunction-eliminate before getting
  at the relevant conjunct, while the indexing by \<open>pos\<close>
  (rather than a uniform regime tag) lets the predicate be
  instantiated directly from the consumer's per-tape
  \<open>mt_pos c' k\<close> without an extra dispatch parameter.  The
  fixed-regime-per-tape property — \<open>pos\<close> doesn't change
  during the buffered run because \<open>m_step_buffered\<close> is
  parameterised by \<open>(q, blocks, pos\<^sub>b\<^sub>p)\<close> with no
  \<open>c'\<close> in scope — makes per-tape regime selection commute
  with the induction in \<open>ae_coupled_run_aux_general\<close>.\<close>

definition ae_window_invariant_general ::
  "(nat \<Rightarrow> 'a) \<Rightarrow> nat
    \<Rightarrow> ('c :: enum) bp
    \<Rightarrow> (('c \<Rightarrow> 'a) \<times> ('c \<Rightarrow> 'a) \<times> ('c \<Rightarrow> 'a))
    \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> bool" where
  "ae_window_invariant_general tM nM bp blocks pos le \<longleftrightarrow>
     (pos = 0 \<longrightarrow> ae_window_invariant_le0 tM nM bp blocks le)
     \<and> (pos = 1 \<longrightarrow> ae_window_invariant_le1 tM nM bp blocks le)
     \<and> (pos \<ge> 2
          \<longrightarrow> ae_window_invariant tM nM bp blocks
                ((pos - 2) * card (UNIV :: 'c set) + 1))"

text \<open>SS4 \<open>\<rightarrow>\<close> SS5: read right into buffer; apply the compute
  (c-fold composition of \<open>M\<close>'s \<open>\<delta>\<close>) to determine the
  post-stage \<open>M\<close>-state, the per-tape destination indicator,
  the modified buffer slots, and the new per-tape offset; per-tape
  move L back to home.  Buffer-phase substep 4 (compute folded in).

  The substrate write \<open>a' = a\<close> is a no-op (SS4 reads the right
  block but does not modify the on-tape contents; modifications
  are materialised during the write-back phase SS5\<open>\<rightarrow>\<close>SS8).
  The compute happens in the state component: \<open>m_steps_buffered\<close>
  consumes the (fully buffered) blocks plus \<open>(AE_Home, ofs)\<close>
  starting position and produces the post-compute
  \<open>(q', buf', end_pos)\<close>; the new offset and destination are
  projected from \<open>end_pos\<close>.\<close>

definition ae_delta_ss4_ss5 ::
  "('q, 'a) mttm
    \<Rightarrow> (('q \<times> ('a, 'c :: enum) ae_stage)
        \<times> (nat \<Rightarrow> ('c \<Rightarrow> 'a))
        \<times> ('q \<times> ('a, 'c) ae_stage)
        \<times> (nat \<Rightarrow> ('c \<Rightarrow> 'a))
        \<times> (nat \<Rightarrow> dir)) set" where
  "ae_delta_ss4_ss5 M =
     {((q, ofs, buf, dest_old, SS4), a,
        (q', ofs', buf', dest', SS5), a, d) |
        q ofs buf dest_old a q' ofs' buf' dest' d
        buf_full end_pos bufC.
          q \<in> Q_tm M \<and> q \<noteq> t_tm M \<and> q \<noteq> r_tm M
          \<and> (\<forall>j\<ge>k_tm M. a j = bl_block (bl_tm M))
          \<and> buf_full = (\<lambda>k. (fst (buf k),
                              if k < k_tm M then fst (snd (buf k)) else a k,
                              a k))
          \<and> ((q, buf_full, \<lambda>k. (AE_Home, ofs k)),
             (q', bufC, end_pos)) \<in> m_steps_buffered M
          \<and> ofs' = (\<lambda>k. if k < k_tm M then snd (end_pos k) else init_offset k)
          \<and> buf' = (\<lambda>k. if k < k_tm M then bufC k else init_buffer (le_tm M) k)
          \<and> dest' = (\<lambda>k. if k < k_tm M then fst (end_pos k) else init_dest k)
          \<and> d = (\<lambda>k. if k < k_tm M
                       then (if a k = LE_block (le_tm M)
                               then dir.N else dir.L)
                       else dir.N)}"

text \<open>Per-tape (write, move) action helpers for the four
  write-back substeps (SS5\<open>\<rightarrow>\<close>SS6, SS6\<open>\<rightarrow>\<close>SS7,
  SS7\<open>\<rightarrow>\<close>SS8, SS8\<open>\<rightarrow>\<close>SS1).  Each takes
  \<open>(le, a, buf, dest)\<close> and returns \<open>(a', d)\<close>: the per-tape
  written block and direction.

  Convention: \<open>buf k = (l, h, r)\<close> is the post-compute buffer.
  LE-stage \<open>\<longleftrightarrow>\<close> \<open>h = LE_block le\<close>.  In steady-state, \<open>dest\<close>
  ranges over \<open>{AE_Left, AE_Home, AE_Right}\<close>; in LE-stage, the
  compute restricts \<open>dest\<close> to \<open>{AE_Home, AE_Right}\<close> but the
  helpers handle the \<open>AE_Left\<close> branch as a vacuous fall-through
  (will never fire under the compute's invariants).\<close>

text \<open>**Head trajectory through the writeback chain.**  The
  direction rules in the action helpers below thread \<open>M'\<close>'s
  head through a specific sequence of block positions
  across SS5 \<open>\<rightarrow>\<close> SS8.  Starting from the SS4
  \<open>\<rightarrow>\<close> SS5 transition (which moves L when reading
  non-LE, so SS5 entry is at block \<open>s\<close>, the original
  home), the chain walks:

  \<^item> SS5: at block \<open>s\<close>; writes \<open>h\<close>; moves L
    (\<open>dest \<noteq> AE_Left\<close>) or R (\<open>dest = AE_Left\<close>).
  \<^item> SS6: at block \<open>s-1\<close> or \<open>s+1\<close>; writes
    \<open>l\<close>/\<open>r\<close> depending on \<open>dest\<close>; moves back toward home.
  \<^item> SS7: at block \<open>s\<close>; writes \<open>a\<close> (idempotent);
    moves L (\<open>dest = AE_Left\<close>) or R (otherwise).
  \<^item> SS8: at block \<open>s+1\<close> (\<open>dest \<in> {AE_Home,
    AE_Right}\<close>) or \<open>s-1\<close> (\<open>dest = AE_Left\<close>); writes
    \<open>r\<close>/\<open>l\<close>; lands at block \<open>s + dest_offset\<close>
    for the next stage.

  **Why this matters for the LE-edge cases.**  For
  steady-state (\<open>s \<ge> 2\<close>), the walk stays in data
  territory and the LE-guard never fires.  For le1
  (\<open>s = 1\<close>), the walk reaches **block 0 — the LE
  position** at SS6 entry (when \<open>dest \<noteq> AE_Left\<close>) or
  at SS8 entry (when \<open>dest = AE_Left\<close>).  At those moments
  the LE-guard branch fires (head reads \<open>LE_block\<close>),
  writing \<open>LE_block\<close> back idempotently.  The
  side-band invariant \<open>ae_position_link\<close> records that
  these LE-guard firings happen at exactly the substeps where
  the default branch would otherwise write the buffer's
  \<open>l\<close>-slot (which is \<open>LE_block\<close> in le1, having been
  loaded from block 0) to a non-LE position — the
  pre-emption that keeps the encoding consistent.\<close>

text \<open>**LE-guard prefix and \<open>\<delta>LE\<close> compatibility.**
  Each action helper prepends an LE-guard
  \<open>if a = LE_block le then (a, N) else \<dots>\<close> for syntactic
  \<open>\<delta>LE\<close>-compatibility: the per-substep relations are over
  all \<open>(state, a, \<dots>)\<close> tuples, not just reachable ones, and
  the substrate's \<open>\<delta>LE\<close> well-formedness conjunct (a
  \<open>valid_mttm\<close> clause) is universal.
  In reachable executions \<open>a = h\<close> at SS5\<open>\<rightarrow>\<close>SS8 (head at
  the home position), so the guard agrees with the
  \<open>h = LE_block le\<close> branch; in unreachable tuples
  (\<open>a = LE_block le\<close> but \<open>h \<noteq> LE_block le\<close>), the guard forces
  a \<open>\<delta>LE\<close>-safe \<open>(a, N)\<close> output rather than the
  buffer-driven \<open>(\<dots>, L)\<close> that would violate \<open>\<delta>LE\<close>.

  This guard serves a double purpose: substrate compatibility
  (the immediate concern above) AND the LE-pre-emption used
  by le1/le0.  In those regimes the head genuinely reaches
  block 0, the LE-guard's \<open>a = LE_block\<close>
  antecedent is true, and the guard fires the LE-block-write
  branch in preference to the default — protecting block
  0 from being clobbered by a non-LE buffer slot.\<close>

fun ae_ss5_action ::
  "'a \<Rightarrow> ('c :: enum \<Rightarrow> 'a)
    \<Rightarrow> (('c \<Rightarrow> 'a) \<times> ('c \<Rightarrow> 'a) \<times> ('c \<Rightarrow> 'a))
    \<Rightarrow> ae_dest \<Rightarrow> (('c \<Rightarrow> 'a) \<times> dir)" where
  "ae_ss5_action le a (l, h, r) ds =
     (if a = LE_block le then (a, dir.N)
      else if h = LE_block le then (a, dir.N)
      else (h, if ds = AE_Left then dir.R else dir.L))"

fun ae_ss6_action ::
  "'a \<Rightarrow> ('c :: enum \<Rightarrow> 'a)
    \<Rightarrow> (('c \<Rightarrow> 'a) \<times> ('c \<Rightarrow> 'a) \<times> ('c \<Rightarrow> 'a))
    \<Rightarrow> ae_dest \<Rightarrow> (('c \<Rightarrow> 'a) \<times> dir)" where
  "ae_ss6_action le a (l, h, r) ds =
     (if a = LE_block le then (a, dir.R)
      else if h = LE_block le then (a, dir.R)
      else if ds = AE_Left then (r, dir.L) else (l, dir.R))"

fun ae_ss7_action ::
  "'a \<Rightarrow> ('c :: enum \<Rightarrow> 'a)
    \<Rightarrow> (('c \<Rightarrow> 'a) \<times> ('c \<Rightarrow> 'a) \<times> ('c \<Rightarrow> 'a))
    \<Rightarrow> ae_dest \<Rightarrow> (('c \<Rightarrow> 'a) \<times> dir)" where
  "ae_ss7_action le a (l, h, r) ds =
     (if a = LE_block le then (a, dir.N)
      else if h = LE_block le
        then (r, if ds = AE_Right then dir.N else dir.L)
      else (a, if ds = AE_Left then dir.L else dir.R))"

fun ae_ss8_action ::
  "'a \<Rightarrow> ('c :: enum \<Rightarrow> 'a)
    \<Rightarrow> (('c \<Rightarrow> 'a) \<times> ('c \<Rightarrow> 'a) \<times> ('c \<Rightarrow> 'a))
    \<Rightarrow> ae_dest \<Rightarrow> (('c \<Rightarrow> 'a) \<times> dir)" where
  "ae_ss8_action le a (l, h, r) ds =
     (if a = LE_block le then (a, dir.N)
      else if h = LE_block le
        then (if ds = AE_Right then (r, dir.N) else (a, dir.N))
      else (case ds of
              AE_Left  \<Rightarrow> (l, dir.N)
            | AE_Home  \<Rightarrow> (r, dir.L)
            | AE_Right \<Rightarrow> (r, dir.N)))"

text \<open>SS5 \<open>\<rightarrow>\<close> SS6: write home block; per-tape move depends on
  \<open>(stage_kind k, dest k)\<close>.  Write-back substep 5.\<close>

definition ae_delta_ss5_ss6 ::
  "('q, 'a) mttm
    \<Rightarrow> (('q \<times> ('a, 'c :: enum) ae_stage)
        \<times> (nat \<Rightarrow> ('c \<Rightarrow> 'a))
        \<times> ('q \<times> ('a, 'c) ae_stage)
        \<times> (nat \<Rightarrow> ('c \<Rightarrow> 'a))
        \<times> (nat \<Rightarrow> dir)) set" where
  "ae_delta_ss5_ss6 M =
    {((q, ofs, buf, dest, SS5), a,
       (q, ofs, buf, dest, SS6), a', d) |
     q ofs buf dest a a' d.
       q \<in> Q_tm M
       \<and> (\<forall>j\<ge>k_tm M. a j = bl_block (bl_tm M))
       \<and> a' = (\<lambda>k. if k < k_tm M
                     then fst (ae_ss5_action (le_tm M) (a k) (buf k) (dest k))
                     else bl_block (bl_tm M))
       \<and> d  = (\<lambda>k. if k < k_tm M
                     then snd (ae_ss5_action (le_tm M) (a k) (buf k) (dest k))
                     else dir.N)}"

text \<open>SS6 \<open>\<rightarrow>\<close> SS7: write left (steady-state, \<open>dest \<in> {AE_Home,
  AE_Right}\<close>) or right (steady-state, \<open>dest = AE_Left\<close>) or
  home (LE-stage); per-tape move per dest.  Write-back substep 6.\<close>

definition ae_delta_ss6_ss7 ::
  "('q, 'a) mttm
    \<Rightarrow> (('q \<times> ('a, 'c :: enum) ae_stage)
        \<times> (nat \<Rightarrow> ('c \<Rightarrow> 'a))
        \<times> ('q \<times> ('a, 'c) ae_stage)
        \<times> (nat \<Rightarrow> ('c \<Rightarrow> 'a))
        \<times> (nat \<Rightarrow> dir)) set" where
  "ae_delta_ss6_ss7 M =
    {((q, ofs, buf, dest, SS6), a,
       (q, ofs, buf, dest, SS7), a', d) |
     q ofs buf dest a a' d.
       q \<in> Q_tm M
       \<and> (\<forall>j\<ge>k_tm M. a j = bl_block (bl_tm M))
       \<and> a' = (\<lambda>k. if k < k_tm M
                     then fst (ae_ss6_action (le_tm M) (a k) (buf k) (dest k))
                     else bl_block (bl_tm M))
       \<and> d  = (\<lambda>k. if k < k_tm M
                     then snd (ae_ss6_action (le_tm M) (a k) (buf k) (dest k))
                     else dir.N)}"

text \<open>SS7 \<open>\<rightarrow>\<close> SS8: idempotent home re-write (steady-state) or
  right write (LE-stage); per-tape move per dest.  Write-back
  substep 7.\<close>

definition ae_delta_ss7_ss8 ::
  "('q, 'a) mttm
    \<Rightarrow> (('q \<times> ('a, 'c :: enum) ae_stage)
        \<times> (nat \<Rightarrow> ('c \<Rightarrow> 'a))
        \<times> ('q \<times> ('a, 'c) ae_stage)
        \<times> (nat \<Rightarrow> ('c \<Rightarrow> 'a))
        \<times> (nat \<Rightarrow> dir)) set" where
  "ae_delta_ss7_ss8 M =
    {((q, ofs, buf, dest, SS7), a,
       (q, ofs, buf, dest, SS8), a', d) |
     q ofs buf dest a a' d.
       q \<in> Q_tm M
       \<and> (\<forall>j\<ge>k_tm M. a j = bl_block (bl_tm M))
       \<and> a' = (\<lambda>k. if k < k_tm M
                     then fst (ae_ss7_action (le_tm M) (a k) (buf k) (dest k))
                     else bl_block (bl_tm M))
       \<and> d  = (\<lambda>k. if k < k_tm M
                     then snd (ae_ss7_action (le_tm M) (a k) (buf k) (dest k))
                     else dir.N)}"

text \<open>SS8 \<open>\<rightarrow>\<close> SS1: write final block at destination; head ends
  at \<open>dest\<close> position; substep counter resets to SS1.  End of
  write-back phase.

  Halt-aware destination: if \<open>q\<close> reached a halting state
  (\<open>t_tm M\<close> / \<open>r_tm M\<close>) during the compute substep, the
  end-of-stage state is forced to \<open>(q, init_stage le_M)\<close>,
  which equals \<open>t_M'\<close> / \<open>r_M'\<close> by construction.  This makes
  M' actually reach its canonical accept / reject state when M
  halts mid-stage, rather than stalling at SS5.  For non-halting
  \<open>q\<close>, the (offset, buffer) pair is preserved for the next
  stage; \<open>dest\<close> resets to \<open>AE_Home\<close>.\<close>

definition ae_delta_ss8_ss1 ::
  "('q, 'a) mttm
    \<Rightarrow> (('q \<times> ('a, 'c :: enum) ae_stage)
        \<times> (nat \<Rightarrow> ('c \<Rightarrow> 'a))
        \<times> ('q \<times> ('a, 'c) ae_stage)
        \<times> (nat \<Rightarrow> ('c \<Rightarrow> 'a))
        \<times> (nat \<Rightarrow> dir)) set" where
  "ae_delta_ss8_ss1 M =
    {((q, ofs, buf, dest, SS8), a,
       (q, stage'), a', d) |
     q ofs buf dest a stage' a' d.
       q \<in> Q_tm M
       \<and> (\<forall>j\<ge>k_tm M. a j = bl_block (bl_tm M))
       \<and> stage' = (if q \<in> {t_tm M, r_tm M}
                    then init_stage (le_tm M)
                    else (ofs, buf, init_dest, SS1))
       \<and> a' = (\<lambda>k. if k < k_tm M
                     then fst (ae_ss8_action (le_tm M) (a k) (buf k) (dest k))
                     else bl_block (bl_tm M))
       \<and> d  = (\<lambda>k. if k < k_tm M
                     then snd (ae_ss8_action (le_tm M) (a k) (buf k) (dest k))
                     else dir.N)}"

end
