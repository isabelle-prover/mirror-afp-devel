theory AlphabetEnlargement_Defs
  imports "Multitape_TM_Substrate.Multitape_Substrate"
begin

section \<open>Alphabet enlargement\<close>

text \<open>Setup for the \<open>alphabet_enlarge\<close> combinator:
  substrate selectors, stage-bookkeeping types, offset and
  block helpers, encoder / decoder, encoder-canonicity
  predicates, per-substep transition relations, the
  \<open>alphabet_enlarge\<close> combinator itself, the
  \<open>ae_simulates\<close> relation, and the eight mid-stage
  invariants \<open>ae_inv_ss1\<close> through \<open>ae_inv_ss8\<close>,
  plus the upstream structural lemmas, the encoder-roundtrip
  chain, and the validation-phase chain culminating in
  \<open>ae_validation_steps_bound\<close>.

  The forward-simulation chain that consumes the validation
  result, and the top-level theorems
  \<open>alphabet_enlarge_wf\<close>,
  \<open>alphabet_enlarge_language\<close>, and
  \<open>alphabet_enlarge_time\<close>, follow further on in this
  chapter.\<close>

text \<open>Substrate selectors (\<open>bl_tm\<close>, \<open>le_tm\<close>, \<open>delta_tm\<close>,
  \<open>s_tm\<close>, \<open>t_tm\<close>, \<open>r_tm\<close>, \<open>Sigma_tm\<close>, \<open>mt_tape\<close>) live in
  the \<open>Multitape_Substrate\<close> theory alongside the functional substrate
  layer; they're imported transitively.\<close>

subsection \<open>Stage bookkeeping types\<close>

text \<open>Substep counter / phase indicator for \<open>M'\<close>'s state machine.

  Constructors \<open>VFwd\<close> / \<open>VFwdPad\<close> / \<open>VRet\<close> mark the
  validation phase: forward scan (no padded block seen yet),
  forward scan after a trailing-padded block has been
  observed, and return scan back to the first input block.

  Constructors \<open>SS1\<close> … \<open>SS8\<close> mark the 8-substep simulation
  stage of Hopcroft--Ullman
  \<^cite>\<open>\<open>Theorem 12.3\<close> in "Hopcroft1979:introduction"\<close>; \<open>SSn\<close>
  corresponds to the spec's "substep \<open>n\<close>".\<close>

datatype substep_idx =
    VFwd | VFwdPad | VRet
  | SS1 | SS2 | SS3 | SS4 | SS5 | SS6 | SS7 | SS8

instance substep_idx :: finite
proof (intro_classes)
  have "(UNIV :: substep_idx set) \<subseteq>
          {VFwd, VFwdPad, VRet,
           SS1, SS2, SS3, SS4, SS5, SS6, SS7, SS8}"
    using substep_idx.exhaust by blast
  thus "finite (UNIV :: substep_idx set)"
    using finite_subset by auto
qed

text \<open>Per-tape destination indicator: which buffer slot now holds
  the home block of \<open>M\<close>'s simulated head, after the compute
  substep (the 4th component of \<open>stage\<close>).
  The compute substep sets this; the write-back phase consumes it
  to choose between move-sequence variants
  (`L,R,R,N` / `L,R,R,L` / `R,L,L,N` for steady-state stages).\<close>

datatype ae_dest = AE_Left | AE_Home | AE_Right

instance ae_dest :: finite
proof (intro_classes)
  have "(UNIV :: ae_dest set) \<subseteq> {AE_Left, AE_Home, AE_Right}"
    using ae_dest.exhaust by blast
  thus "finite (UNIV :: ae_dest set)"
    using finite_subset by auto
qed

text \<open>Stage bookkeeping carried in the output machine's state set:
  per-tape within-block offset (\<open>nat \<Rightarrow> 'c\<close>), per-tape three-block
  buffer (left, home, right), per-tape destination indicator
  (\<open>AE_Left\<close> / \<open>AE_Home\<close> / \<open>AE_Right\<close>), and the substep counter
  within the current 8-substep stage.\<close>

type_synonym ('a, 'c) ae_stage =
  "(nat \<Rightarrow> 'c)
   \<times> (nat \<Rightarrow> ('c \<Rightarrow> 'a) \<times> ('c \<Rightarrow> 'a) \<times> ('c \<Rightarrow> 'a))
   \<times> (nat \<Rightarrow> ae_dest)
   \<times> substep_idx"

subsection \<open>Offset arithmetic on \<open>'c\<close>\<close>

text \<open>The compute substep tracks a simulated head position by an
  offset within a 3-block buffer; advancing by \<open>L\<close> / \<open>R\<close>
  requires partial successor / predecessor on \<open>'c\<close>.  We use the
  canonical enumeration provided by the \<open>enum\<close> class.\<close>

definition c_idx :: "'c :: enum \<Rightarrow> nat" where
  "c_idx x = (THE i. i < length (enum_class.enum :: 'c list)
                     \<and> (enum_class.enum :: 'c list) ! i = x)"

definition c_first :: "'c :: enum" where
  "c_first = (enum_class.enum :: 'c list) ! 0"

definition c_last :: "'c :: enum" where
  "c_last = (enum_class.enum :: 'c list)
              ! (length (enum_class.enum :: 'c list) - 1)"

definition c_succ :: "'c :: enum \<Rightarrow> 'c option" where
  "c_succ x =
     (let xs = enum_class.enum :: 'c list; i = c_idx x in
        if Suc i < length xs then Some (xs ! Suc i) else None)"

definition c_pred :: "'c :: enum \<Rightarrow> 'c option" where
  "c_pred x =
     (let xs = enum_class.enum :: 'c list; i = c_idx x in
        if i = 0 then None else Some (xs ! (i - 1)))"

subsection \<open>Block-encoding helpers\<close>

text \<open>The constant LE-block: a block whose every cell holds
  \<open>M\<close>'s left-endmarker symbol.  Used as \<open>M'\<close>'s left endmarker.
  Compatible with the substrate's \<open>\<delta>LE\<close> invariant: any read of
  this block tests \<open>le\<close> at every cell, so the
  \<open>a k = LE \<Longrightarrow> a' k = LE \<and> d k \<in> {N, R}\<close> obligation lifts
  pointwise from \<open>M\<close>'s.\<close>

definition LE_block :: "'a \<Rightarrow> ('c :: enum \<Rightarrow> 'a)" where
  "LE_block le = (\<lambda>_. le)"

text \<open>The constant blank-block: a block whose every cell holds
  \<open>M\<close>'s blank symbol.  Used as \<open>M'\<close>'s blank, and also as the
  semantic placeholder for \<open>buf.left\<close> in LE-stages.\<close>

definition bl_block :: "'a \<Rightarrow> ('c :: enum \<Rightarrow> 'a)" where
  "bl_block bl = (\<lambda>_. bl)"

subsection \<open>Encoder\<close>

text \<open>Encoding an input word as a list of \<open>c\<close>-blocks,
  padding the final block with the substrate's blank symbol if the
  input length is not a multiple of \<open>c\<close>.

  The grouping factor \<open>c = card (UNIV :: 'c set)\<close> is determined at
  the type level.  Block \<open>i\<close> (for \<open>i < \<lceil>length w / c\<rceil>\<close>) is
  the function \<open>\<lambda>x. if i \<cdot> c + c_idx x < length w then w ! (i \<cdot> c
  + c_idx x) else bl\<close>; the output list has length
  \<open>\<lceil>length w / c\<rceil>\<close>, computed in nat arithmetic as
  \<open>(length w + c - 1) div c\<close>.\<close>

definition encode_input ::
  "'a \<Rightarrow> 'a list \<Rightarrow> (('c :: enum) \<Rightarrow> 'a) list" where
  "encode_input bl w =
     (let c = card (UNIV :: 'c set) in
        map (\<lambda>i. (\<lambda>x. let j = i * c + c_idx x in
                          if j < length w then w ! j else bl))
            [0 ..< (length w + c - 1) div c])"

subsection \<open>Decoder\<close>

text \<open>Decoder: extract \<open>M\<close>-symbols from a list of blocks by
  taking each block's \<open>bl\<close>-free prefix under the canonical
  \<open>'c\<close>-enumeration.  For pure blocks this yields all \<open>c\<close>
  cells; for trailing-padded blocks it yields the non-blank
  prefix; for non-canonical blocks (blank-then-non-blank
  pattern) it yields the leading non-blank prefix only — but
  the validation phase rejects these before decoding is invoked.
  Inverse to \<open>encode_input\<close> on the encoder image; cited by the
  forward direction of
  \<open>ae_validation_canonical_iff_encoder_image\<close>.\<close>

definition ae_decode_block :: "'a \<Rightarrow> ('c :: enum \<Rightarrow> 'a) \<Rightarrow> 'a list" where
  "ae_decode_block bl f =
     takeWhile (\<lambda>a. a \<noteq> bl) (map f (enum_class.enum :: 'c list))"

definition ae_decode_input :: "'a \<Rightarrow> (('c :: enum) \<Rightarrow> 'a) list \<Rightarrow> 'a list" where
  "ae_decode_input bl w = concat (map (ae_decode_block bl) w)"

subsection \<open>Initial stage\<close>

text \<open>Initial within-block offset.  Every tape's offset starts at a
  canonical element of \<open>'c\<close> (treated as the within-block position
  of \<open>M\<close>'s left endmarker on each tape).  The specific element is
  underspecified at this level; the simulation argument (§30.4)
  fixes a canonical \<open>0\<close>-offset matching \<open>M\<close>'s initial head
  position.\<close>

definition init_offset :: "nat \<Rightarrow> ('c :: enum)" where
  "init_offset = (\<lambda>_. SOME x. True)"

text \<open>Initial buffer.  Every tape starts with three constant
  \<open>LE\<close>-blocks: at \<open>M'\<close>'s position 0 the home block is the
  left-endmarker block, and the buffer phase has not yet executed
  on the surrounding cells; the SS1\<open>\<rightarrow>\<close>SS4 buffer phase
  refills the slots from actual tape contents at the start of
  every stage.\<close>

definition init_buffer ::
  "'a \<Rightarrow> (nat \<Rightarrow> (('c :: enum \<Rightarrow> 'a)
                  \<times> ('c \<Rightarrow> 'a)
                  \<times> ('c \<Rightarrow> 'a)))" where
  "init_buffer le = (\<lambda>_. (LE_block le, LE_block le, LE_block le))"

text \<open>Initial destination indicator: every tape starts with
  \<open>AE_Home\<close> (the indicator is meaningful only after the compute
  substep sets it; the initial value is canonical).\<close>

definition init_dest :: "nat \<Rightarrow> ae_dest" where
  "init_dest = (\<lambda>_. AE_Home)"

text \<open>Initial stage: zero offset, all-\<open>LE\<close> buffers, dest = home,
  substep counter \<open>SS1\<close>.\<close>

definition init_stage ::
  "'a \<Rightarrow> ('a, 'c :: enum) ae_stage" where
  "init_stage le = (init_offset, init_buffer le, init_dest, VFwd)"

subsection \<open>Encoder-canonicity predicates\<close>

text \<open>A block is \<open>pure\<close> if every cell is non-blank.  In the
  encoder image, every block except possibly the last has
  this form (every cell is from the original input).\<close>

definition is_pure_block ::
  "'a \<Rightarrow> ('c :: enum \<Rightarrow> 'a) \<Rightarrow> bool" where
  "is_pure_block bl f = (\<forall>x. f x \<noteq> bl)"

text \<open>A block is \<open>trailing-padded\<close> if there is a non-empty,
  proper prefix (under the canonical \<open>'c\<close>-enumeration) of
  non-blank cells, and the remaining cells are all blank.  In the
  encoder image, the last block has this form when the
  input length is not a multiple of \<open>c\<close>.\<close>

definition is_padded_block ::
  "'a \<Rightarrow> ('c :: enum \<Rightarrow> 'a) \<Rightarrow> bool" where
  "is_padded_block bl f =
     (\<exists>k. k \<ge> 1 \<and> k < length (enum_class.enum :: 'c list)
       \<and> (\<forall>x. c_idx x < k \<longrightarrow> f x \<noteq> bl)
       \<and> (\<forall>x. c_idx x \<ge> k \<longrightarrow> f x = bl))"

text \<open>Encoder-canonical block: pure or trailing-padded.  The
  validation phase accepts only blocks satisfying this
  predicate; non-canonical blocks (blanks scattered in
  non-trailing positions) route the input to \<open>r_M'\<close>.\<close>

definition is_canonical_block ::
  "'a \<Rightarrow> ('c :: enum \<Rightarrow> 'a) \<Rightarrow> bool" where
  "is_canonical_block bl f = (is_pure_block bl f \<or> is_padded_block bl f)"

text \<open>Sequence-level encoder-canonicity: the input \<open>w\<close> is
  well-formed (= in the encoder image) iff every block is
  pure, *except possibly the last* which may also be padded.
  Per block encoder-canonicity (\<open>is_canonical_block\<close>) is
  necessary but not sufficient — a sequence with a padded
  block followed by anything else is per-cell canonical but
  not in the encoder image.

  The validation phase enforces exactly this distinction: VFwd
  reject fires on non-canonical cells; VFwdPad reject fires on
  any non-\<open>bl_block\<close> cell after a padded block.\<close>

definition ae_input_well_formed ::
  "'a \<Rightarrow> ('c :: enum \<Rightarrow> 'a) list \<Rightarrow> bool" where
  "ae_input_well_formed bl w \<longleftrightarrow>
     (\<forall>s. s < length w \<longrightarrow>
        (is_pure_block bl (w ! s)
         \<or> (s = length w - 1 \<and> is_padded_block bl (w ! s))))"

end
