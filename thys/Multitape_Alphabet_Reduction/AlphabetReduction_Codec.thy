theory AlphabetReduction_Codec
  imports "Multitape_TM_Substrate.Multitape_Substrate"
    "Multitape_TM_Substrate.Multitape_Binary_Codec"
begin

section \<open>Alphabet reduction\<close>

text \<open>This theory opens the alphabet-reduction development.  The
  \<open>alphabet_reduce\<close> combinator takes a well-formed substrate
  machine over an arbitrary finite alphabet \<open>'a\<close> (with
  tape-alphabet cardinality \<open>\<ge>\<close> 4) and produces a
  well-formed substrate machine over the fixed four-element alphabet
  \<open>sym4\<close>, preserving the accepted language, determinism, and
  tape count.

  This is the elementary determinism-preserving per-symbol multi-cell
  encoding.

  The development is layered: this first theory fixes the output
  alphabet \<open>sym4\<close> and the per-symbol binary codec; the
  simulator, its delta, and the headline theorems
  (\<open>alphabet_reduce_wf\<close>, \<open>alphabet_reduce_language\<close>,
  \<open>alphabet_reduce_time\<close>, \<open>alphabet_reduce_det\<close>) are
  built across the theories that follow.
  Throughout, \<open>b\<close> abbreviates \<open>block_width \<Gamma>\<close> (the per-symbol cell width).\<close>

text \<open>The fixed four-element output alphabet:
  \<open>BLANK4\<close> (blank), \<open>LE4\<close> (left endmarker),
  \<open>BIT0\<close> (binary 0), \<open>BIT1\<close> (binary 1).\<close>

datatype sym4 = BLANK4 | LE4 | BIT0 | BIT1

lemma sym4_UNIV: "(UNIV :: sym4 set) = {BLANK4, LE4, BIT0, BIT1}"
  using sym4.exhaust by blast

lemma sym4_card: "card (UNIV :: sym4 set) = 4"
proof -
  have "(UNIV :: sym4 set) = {BLANK4, LE4, BIT0, BIT1}"
    by (rule sym4_UNIV)
  moreover have "card {BLANK4, LE4, BIT0, BIT1} = 4"
    by simp
  ultimately show ?thesis by simp
qed

subsection \<open>Per-symbol encoder helpers\<close>

text \<open>The binary codec is the substrate's
  (\<open>Multitape_Binary_Codec\<close>), at the digits \<open>BIT0\<close> and \<open>BIT1\<close>.  The
  per-source-symbol block length is its \<^const>\<open>block_width\<close> of \<open>\<Gamma>\<close>: the
  number of \<open>sym4\<close> cells that encode one \<open>\<Gamma>\<close>-symbol, and so the slowdown
  factor of the reduction, \<open>\<lceil>log\<^sub>2 (card \<Gamma>)\<rceil>\<close> and at least \<open>1\<close>.  It rises
  in unit steps as \<open>card \<Gamma>\<close> passes a power of two, not smoothly with the
  alphabet's size.

  \<^bold>\<open>What is counted.\<close>  The index space \<open>{..< card \<Gamma>}\<close>
  covers \<^emph>\<open>every\<close> symbol of \<open>\<Gamma>\<close>: the blank at index
  \<open>0\<close> (the anchor \<open>gamma_enum\<close> relies on --- see below), and
  the left endmarker \<open>le\<close> as an ordinary coded symbol, since
  \<open>valid_ktm\<close> permits a machine to write \<open>le\<close> at any tape
  position (its only special handling is the single \<open>LE4\<close> cell at
  position \<open>0\<close>).  So \<open>block_width\<close> is genuinely the width of
  this uniform code, not a loose bound on a smaller one --- but it is not
  the \<^emph>\<open>coding\<close> minimum.  Reserving index \<open>0\<close> for the
  blank (so an all-\<open>BLANK4\<close> block reads back through the same
  accumulator) puts it one digit above
  \<open>\<lceil>log\<^sub>2 (card \<Gamma> - 1)\<rceil>\<close>, the width for the
  \<open>card \<Gamma> - 1\<close> non-blank symbols; the two agree except just
  past a power of two.  Detecting the all-\<open>BLANK4\<close> block directly
  would recover that digit, and additionally giving \<open>le\<close> its own
  marker block would reach \<open>\<lceil>log\<^sub>2 (card \<Gamma> - 2)\<rceil>\<close>
  --- but each costs a marker-detection branch in the read and write
  phases, so that constant-factor gain is deliberately not taken.\<close>

text \<open>A \<^emph>\<open>blank-anchored\<close> enumeration of \<open>\<Gamma>\<close> as a
  bijection to \<open>{..< card \<Gamma>}\<close> that additionally sends the
  blank \<open>bl\<close> to \<open>0\<close>.  The anchor is load-bearing for the
  read phase: a blank source cell is encoded as a \<open>b\<close>-cell
  all-\<open>BLANK4\<close> block (\<open>bit_value = 0\<close>), so the read fold
  is a fixpoint at \<open>gamma_unenum \<Gamma> bl 0\<close>, which must equal
  \<open>bl\<close> — and the decode round-trips force that to
  \<open>gamma_enum \<Gamma> bl bl = 0\<close>.  Existence of such a bijection
  is unconditional on \<open>finite \<Gamma>\<close> for \<^emph>\<open>any\<close>
  \<open>bl\<close> (\<open>ex_bij_betw_anchor\<close> below: swap \<open>0\<close> with
  \<open>g bl\<close> when \<open>bl \<in> \<Gamma>\<close>, otherwise free off-domain),
  so the carried \<open>bl\<close> needs no \<open>bl \<in> \<Gamma>\<close> side
  condition.  Downstream proofs reason about \<open>bij_betw\<close>- and
  anchor-derived facts only; the Hilbert choice picks one specific
  anchored bijection.\<close>

definition gamma_enum :: "'a set \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> nat" where
  "gamma_enum \<Gamma> bl =
     (SOME f. bij_betw f \<Gamma> {..< card \<Gamma>} \<and> f bl = 0)"

text \<open>Render a natural number as a fixed-length \<open>sym4\<close>
  bit list (\<open>BIT0\<close> / \<open>BIT1\<close> only).  The list has
  shape \<open>[bit\<^sub>b\<^sub>-\<^sub>1, \<dots>, bit\<^sub>1, bit\<^sub>0]\<close>:
  most-significant bit at the head, least-significant bit at
  the tail.  For \<open>n \<ge> 2 ^ b\<close> the high bits are dropped
  (only the low \<open>b\<close> bits are rendered).\<close>

abbreviation nat_to_bits :: "nat \<Rightarrow> nat \<Rightarrow> sym4 list" where
  "nat_to_bits \<equiv> nat_to_syms BIT0 BIT1"

subsection \<open>Per-symbol encoder\<close>

text \<open>Encoding a single \<open>'a\<close>-symbol as a fixed-length list of
  \<open>sym4\<close>-symbols, parameterised over the source alphabet
  \<open>\<Gamma>\<close> (a finite set, passed explicitly as a value rather
  than through a type-class constraint, so the construction is uniform
  over all source alphabets).  The
  length \<open>b\<close> is the slowdown factor; the encoding is
  injective on \<open>\<Gamma>\<close>.  The two bit symbols \<open>BIT0\<close>,
  \<open>BIT1\<close> carry the payload; \<open>LE4\<close> and \<open>BLANK4\<close>
  do not appear in any encoder image.  For \<open>x \<notin> \<Gamma>\<close> the
  encoder produces a value that's structurally well-shaped (a
  \<open>b\<close>-cell bit list) but semantically arbitrary —
  downstream proofs always operate on \<open>x \<in> \<Gamma>\<close>.\<close>

definition encode_symbol ::
  "'a set \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> sym4 list" where
  "encode_symbol \<Gamma> bl x = nat_to_bits (block_width \<Gamma>) (gamma_enum \<Gamma> bl x)"

text \<open>Encoding an input word as a flat list of \<open>sym4\<close>-symbols
  (concatenation of per-symbol encodings under the given \<open>\<Gamma>\<close>).\<close>

definition encode_input_ar ::
  "'a set \<Rightarrow> 'a \<Rightarrow> 'a list \<Rightarrow> sym4 list" where
  "encode_input_ar \<Gamma> bl w = concat (map (encode_symbol \<Gamma> bl) w)"

subsection \<open>Per-symbol encoder lemmas\<close>

lemma length_encode_symbol [simp]:
  "length (encode_symbol \<Gamma> bl x) = block_width \<Gamma>"
  unfolding encode_symbol_def by simp

lemma encode_symbol_cell_domain:
  "set (encode_symbol \<Gamma> bl x) \<subseteq> {BIT0, BIT1}"
  unfolding encode_symbol_def
  by (rule set_nat_to_syms)

text \<open>The enumeration \<open>gamma_enum \<Gamma> bl\<close> is a genuine bijection
  from \<open>\<Gamma>\<close> to \<open>{..< card \<Gamma>}\<close> whenever \<open>\<Gamma>\<close> is
  finite.  Existence is library
  (\<open>ex_bij_betw_finite_nat\<close>); the Hilbert-choice operator
  picks one such bijection.\<close>

text \<open>Existence of a blank-anchored bijection
  \<open>\<Gamma> \<rightarrow> {..< card \<Gamma>}\<close> sending \<open>bl\<close> to \<open>0\<close>,
  unconditional on \<open>finite \<Gamma>\<close> for any \<open>bl\<close>.  Take any
  bijection \<open>g\<close> (library \<open>ex_bij_betw_finite_nat\<close>); if
  \<open>bl \<in> \<Gamma>\<close>, post-compose with the nat-level transposition of
  \<open>0\<close> and \<open>g bl\<close> (both \<open>< card \<Gamma>\<close>), which is a
  \<open>bij_betw\<close> of \<open>{..< card \<Gamma>}\<close> onto itself by
  \<open>endo_inj_surj\<close>; if \<open>bl \<notin> \<Gamma>\<close>, just override
  \<open>g\<close> at \<open>bl\<close> (off-domain, so \<open>bij_betw\<close> is
  unchanged by \<open>bij_betw_cong\<close>).\<close>

lemma ex_bij_betw_anchor:
  fixes \<Gamma> :: "'a set" and bl :: 'a
  assumes finG: "finite \<Gamma>"
  shows "\<exists>f. bij_betw f \<Gamma> {..< card \<Gamma>} \<and> f bl = 0"
proof -
  obtain g where g: "bij_betw g \<Gamma> {..< card \<Gamma>}"
    using ex_bij_betw_finite_nat[OF finG] by (auto simp: atLeast0LessThan)
  show ?thesis
  proof (cases "bl \<in> \<Gamma>")
    case False
    have agree: "\<And>x. x \<in> \<Gamma> \<Longrightarrow> (g(bl := 0)) x = g x"
      using False by auto
    have "bij_betw (g(bl := 0)) \<Gamma> {..< card \<Gamma>}"
      using g agree by (metis bij_betw_cong)
    moreover have "(g(bl := 0)) bl = 0" by simp
    ultimately show ?thesis by blast
  next
    case True
    have npos: "0 < card \<Gamma>" using True finG by (auto simp: card_gt_0_iff)
    have gbl: "g bl < card \<Gamma>" using g True by (auto simp: bij_betw_def)
    let ?s = "\<lambda>i. if i = 0 then g bl else if i = g bl then 0 else i"
    have into: "?s ` {..< card \<Gamma>} \<subseteq> {..< card \<Gamma>}"
      using gbl npos by auto
    have inj: "inj_on ?s {..< card \<Gamma>}"
      by (auto simp: inj_on_def split: if_splits)
    have "bij_betw ?s {..< card \<Gamma>} {..< card \<Gamma>}"
      unfolding bij_betw_def
      using inj endo_inj_surj[OF finite_lessThan into inj] by blast
    from bij_betw_trans[OF g this]
    have "bij_betw (?s \<circ> g) \<Gamma> {..< card \<Gamma>}" .
    moreover have "(?s \<circ> g) bl = 0" using gbl by (auto simp: comp_def)
    ultimately show ?thesis by blast
  qed
qed

lemma gamma_enum_anchor:
  assumes "finite \<Gamma>"
  shows "bij_betw (gamma_enum \<Gamma> bl) \<Gamma> {..< card \<Gamma>}
           \<and> gamma_enum \<Gamma> bl bl = 0"
  unfolding gamma_enum_def
  using ex_bij_betw_anchor[OF assms] by (rule someI_ex)

lemma gamma_enum_bij:
  assumes "finite \<Gamma>"
  shows "bij_betw (gamma_enum \<Gamma> bl) \<Gamma> {..< card \<Gamma>}"
  using gamma_enum_anchor[OF assms] by simp

text \<open>The anchor: the blank-anchored enumeration sends the blank to
  \<open>0\<close>.  This is what makes an all-\<open>BLANK4\<close> block decode to
  \<open>bl\<close> (\<open>decode_blank\<close>).\<close>

lemma gamma_enum_blank:
  assumes "finite \<Gamma>"
  shows "gamma_enum \<Gamma> bl bl = 0"
  using gamma_enum_anchor[OF assms] by simp

lemma gamma_enum_lt_card:
  assumes "finite \<Gamma>" and "x \<in> \<Gamma>"
  shows "gamma_enum \<Gamma> bl x < card \<Gamma>"
proof -
  from gamma_enum_bij[OF \<open>finite \<Gamma>\<close>] \<open>x \<in> \<Gamma>\<close>
  have "gamma_enum \<Gamma> bl x \<in> {..< card \<Gamma>}"
    by (auto simp: bij_betw_def)
  thus ?thesis by simp
qed

text \<open>Injectivity-on-\<open>\<Gamma>\<close>: distinct source symbols in \<open>\<Gamma>\<close>
  produce distinct encoder images.  This is the load-bearing
  property for language preservation: no two source symbols
  collide under the encoder.\<close>

lemma encode_symbol_inj_on_Gamma:
  assumes "finite \<Gamma>"
      and "x \<in> \<Gamma>" and "y \<in> \<Gamma>"
      and "encode_symbol \<Gamma> bl x = encode_symbol \<Gamma> bl y"
  shows "x = y"
proof -
  from \<open>encode_symbol \<Gamma> bl x = encode_symbol \<Gamma> bl y\<close>
  have bits_eq:
    "nat_to_bits (block_width \<Gamma>) (gamma_enum \<Gamma> bl x)
       = nat_to_bits (block_width \<Gamma>) (gamma_enum \<Gamma> bl y)"
    by (simp add: encode_symbol_def)
  have lt_x: "gamma_enum \<Gamma> bl x < 2 ^ block_width \<Gamma>"
    using gamma_enum_lt_card[OF \<open>finite \<Gamma>\<close> \<open>x \<in> \<Gamma>\<close>, of bl]
          card_le_two_pow_block_width[of \<Gamma>]
    by linarith
  have lt_y: "gamma_enum \<Gamma> bl y < 2 ^ block_width \<Gamma>"
    using gamma_enum_lt_card[OF \<open>finite \<Gamma>\<close> \<open>y \<in> \<Gamma>\<close>, of bl]
          card_le_two_pow_block_width[of \<Gamma>]
    by linarith
  have enum_eq: "gamma_enum \<Gamma> bl x = gamma_enum \<Gamma> bl y"
    using nat_to_syms_inj[OF _ lt_x lt_y bits_eq] by simp
  have "inj_on (gamma_enum \<Gamma> bl) \<Gamma>"
    using gamma_enum_bij[OF \<open>finite \<Gamma>\<close>]
    by (simp add: bij_betw_def)
  from this enum_eq \<open>x \<in> \<Gamma>\<close> \<open>y \<in> \<Gamma>\<close> show ?thesis
    by (rule inj_onD)
qed

text \<open>Structural properties of the input-word encoder.  These
  follow directly from the \<open>concat (map (encode_symbol \<Gamma> bl)
  \<dots>)\<close> definition and are useful for the validation-phase
  reach lemmas in later slices.\<close>

lemma encode_input_ar_Nil [simp]:
  "encode_input_ar \<Gamma> bl [] = []"
  unfolding encode_input_ar_def by simp

lemma encode_input_ar_append:
  "encode_input_ar \<Gamma> bl (w1 @ w2)
     = encode_input_ar \<Gamma> bl w1 @ encode_input_ar \<Gamma> bl w2"
  unfolding encode_input_ar_def by simp

lemma length_encode_input_ar:
  "length (encode_input_ar \<Gamma> bl w) = block_width \<Gamma> * length w"
  unfolding encode_input_ar_def
  by (induct w) auto

text \<open>Uniform-width block indexing: when every block \<open>f x\<close>
  has the same length \<open>K\<close>, the \<open>(i \<cdot> K + j)\<close>-th cell
  of \<open>concat (map f xs)\<close> is the \<open>j\<close>-th cell of the
  \<open>i\<close>-th block.  The list-level fact underlying the
  initial-tape correspondence: \<open>encode_input_ar\<close> is exactly
  such a uniform concatenation, every block \<open>b\<close>
  wide by \<open>length_encode_symbol\<close>.\<close>
lemma nth_concat_map_uniform:
  assumes K: "\<And>x. length (f x) = K"
      and i: "i < length xs"
      and j: "j < K"
  shows "concat (map f xs) ! (i * K + j) = f (xs ! i) ! j"
  using i
proof (induct xs arbitrary: i)
  case Nil
  then show ?case by simp
next
  case (Cons x xs)
  show ?case
  proof (cases i)
    case 0
    have "concat (map f (x # xs)) ! (i * K + j)
            = (f x @ concat (map f xs)) ! j"
      using 0 by simp
    also have "\<dots> = f x ! j"
      using j K[of x] by (simp add: nth_append)
    finally show ?thesis using 0 by simp
  next
    case (Suc i')
    have i'len: "i' < length xs" using Cons.prems Suc by simp
    have idx: "i * K + j = length (f x) + (i' * K + j)"
      using Suc K[of x] by simp
    have "concat (map f (x # xs)) ! (i * K + j)
            = concat (map f xs) ! (i' * K + j)"
      using idx by (simp add: nth_append)
    also have "\<dots> = f (xs ! i') ! j"
      using Cons.hyps[OF i'len] .
    finally show ?thesis using Suc by simp
  qed
qed

lemma nth_encode_input_ar:
  assumes "i < length w" and "j < block_width \<Gamma>"
  shows "encode_input_ar \<Gamma> bl w ! (i * block_width \<Gamma> + j)
           = encode_symbol \<Gamma> bl (w ! i) ! j"
  unfolding encode_input_ar_def
  by (rule nth_concat_map_uniform[OF length_encode_symbol assms])

subsection \<open>Per-symbol decoder helpers\<close>

text \<open>Bit value of a \<open>sym4\<close> cell.  \<open>BIT1\<close> contributes
  1, every other symbol contributes 0; the non-bit symbols
  (\<open>BIT0\<close>, \<open>LE4\<close>, \<open>BLANK4\<close>) are conflated to
  zero — junk-in, junk-out — so the decoder produces a
  well-defined nat even on malformed input.  Validity checking
  is performed separately by \<open>decode_symbol\<close>'s cell-domain
  test.\<close>

abbreviation bit_value :: "sym4 \<Rightarrow> nat" where
  "bit_value \<equiv> bit_of BIT1"

text \<open>Read a \<open>sym4\<close> list as a binary number, MSB at the
  head (matches \<open>nat_to_bits\<close>'s output shape).  Each
  position contributes \<open>bit_value\<close> times the appropriate
  power of two.\<close>

abbreviation bits_to_nat :: "sym4 list \<Rightarrow> nat" where
  "bits_to_nat \<equiv> syms_to_nat BIT1"

subsection \<open>Per-symbol decoder\<close>

text \<open>Partial inverse of \<open>encode_symbol\<close>.  Returns
  \<open>Some x\<close> when the input list:
  \<^enum> has length \<open>b\<close> (correct cell count);
  \<^enum> contains only \<open>BIT0\<close> / \<open>BIT1\<close> cells (no
    substrate-reserved markers); and
  \<^enum> has binary interpretation strictly below
    \<open>card \<Gamma>\<close> (in the enumeration range).

  Otherwise returns \<open>None\<close>.  The validation phase in
  later slices implements this check as a sequence of substep
  transitions; the abstract \<open>decode_symbol\<close> partial
  function is the specification target.\<close>

definition decode_symbol ::
  "'a set \<Rightarrow> 'a \<Rightarrow> sym4 list \<Rightarrow> 'a option" where
  "decode_symbol \<Gamma> bl ys =
     (if length ys = block_width \<Gamma>
              \<and> set ys \<subseteq> {BIT0, BIT1}
              \<and> bits_to_nat ys < card \<Gamma>
      then Some (inv_into \<Gamma> (gamma_enum \<Gamma> bl) (bits_to_nat ys))
      else None)"

text \<open>Round-trip: decoding an encoded symbol from
  \<open>\<Gamma>\<close> recovers the source value.  All three validity
  preconditions of \<open>decode_symbol\<close> are satisfied by the
  encoder image; \<open>inv_into\<close> resolves to \<open>x\<close> via
  \<open>gamma_enum\<close>'s injectivity-on-\<open>\<Gamma>\<close>.\<close>

lemma decode_symbol_encode_symbol:
  assumes "finite \<Gamma>" and "x \<in> \<Gamma>"
  shows "decode_symbol \<Gamma> bl (encode_symbol \<Gamma> bl x) = Some x"
proof -
  let ?ys = "encode_symbol \<Gamma> bl x"
  have len: "length ?ys = block_width \<Gamma>" by simp
  have cd: "set ?ys \<subseteq> {BIT0, BIT1}"
    by (rule encode_symbol_cell_domain)
  have lt_x: "gamma_enum \<Gamma> bl x < 2 ^ block_width \<Gamma>"
    using gamma_enum_lt_card[OF \<open>finite \<Gamma>\<close> \<open>x \<in> \<Gamma>\<close>, of bl]
          card_le_two_pow_block_width[of \<Gamma>]
    by linarith
  have bn: "bits_to_nat ?ys = gamma_enum \<Gamma> bl x"
    unfolding encode_symbol_def
    by (rule syms_to_nat_nat_to_syms[OF _ lt_x]) simp
  have lt_card: "bits_to_nat ?ys < card \<Gamma>"
    using bn gamma_enum_lt_card[OF \<open>finite \<Gamma>\<close> \<open>x \<in> \<Gamma>\<close>] by simp
  have inj: "inj_on (gamma_enum \<Gamma> bl) \<Gamma>"
    using gamma_enum_bij[OF \<open>finite \<Gamma>\<close>]
    by (simp add: bij_betw_def)
  have inv_eq: "inv_into \<Gamma> (gamma_enum \<Gamma> bl) (bits_to_nat ?ys) = x"
    using bn inv_into_f_f[OF inj \<open>x \<in> \<Gamma>\<close>] by simp
  show ?thesis
    unfolding decode_symbol_def
    using len cd lt_card inv_eq by simp
qed

text \<open>A total form of the symbol decoder, indexed by a
  natural number rather than a bit list.  For \<open>n < card
  \<Gamma>\<close>, returns the unique \<open>x \<in> \<Gamma>\<close> with
  \<open>gamma_enum \<Gamma> bl x = n\<close> (via \<open>inv_into\<close>);
  for \<open>n \<ge> card \<Gamma>\<close>, returns the blank
  \<open>bl\<close> as a defensive fallback.  Used by
  \<open>ar_delta_read\<close>'s per-bit accumulator to maintain
  \<open>buf\<close> as a partial-decoded \<open>'a\<close> value: at
  every per-bit substep before the boundary, the partial nat is
  strictly less than \<open>2 ^ (b - 1) < card \<Gamma>\<close>
  (since \<open>b\<close> is the \<^emph>\<open>least\<close> \<open>n\<close>
  with \<open>card \<Gamma> \<le> 2 ^ n\<close>), so the fallback is
  never substantively reached for valid inputs; only the
  boundary substep can land out of range under
  non-encoder-image inputs, where the language theorem doesn't
  care.\<close>

definition gamma_unenum :: "'a set \<Rightarrow> 'a \<Rightarrow> nat \<Rightarrow> 'a" where
  "gamma_unenum \<Gamma> bl n =
     (if n < card \<Gamma>
      then inv_into \<Gamma> (gamma_enum \<Gamma> bl) n
      else bl)"

text \<open>Enumeration round-trips between \<open>gamma_enum\<close> and its
  total inverse \<open>gamma_unenum\<close>, the arithmetic core the read
  phase's incremental decode rests on.  \<open>gamma_enum \<circ>
  gamma_unenum\<close> is the identity on the in-range index set
  \<open>\<lbrace>0..<card \<Gamma>\<rbrace>\<close> (where \<open>gamma_unenum\<close> resolves
  to \<open>inv_into\<close> and \<open>gamma_enum\<close> is surjective onto that
  set), and \<open>gamma_unenum \<circ> gamma_enum\<close> is the identity on
  \<open>\<Gamma>\<close> (where \<open>gamma_enum\<close> is injective and lands
  below \<open>card \<Gamma>\<close>).\<close>

lemma gamma_enum_gamma_unenum:
  assumes "finite \<Gamma>" and "n < card \<Gamma>"
  shows "gamma_enum \<Gamma> bl (gamma_unenum \<Gamma> bl n) = n"
proof -
  have img: "gamma_enum \<Gamma> bl ` \<Gamma> = {..<card \<Gamma>}"
    using gamma_enum_bij[OF assms(1)] by (simp add: bij_betw_def)
  have "n \<in> gamma_enum \<Gamma> bl ` \<Gamma>" using assms(2) img by simp
  hence "gamma_enum \<Gamma> bl (inv_into \<Gamma> (gamma_enum \<Gamma> bl) n) = n"
    by (rule f_inv_into_f)
  thus ?thesis using assms(2) by (simp add: gamma_unenum_def)
qed

lemma gamma_unenum_gamma_enum:
  assumes "finite \<Gamma>" and "x \<in> \<Gamma>"
  shows "gamma_unenum \<Gamma> bl (gamma_enum \<Gamma> bl x) = x"
proof -
  have lt: "gamma_enum \<Gamma> bl x < card \<Gamma>"
    by (rule gamma_enum_lt_card[OF assms])
  have inj: "inj_on (gamma_enum \<Gamma> bl) \<Gamma>"
    using gamma_enum_bij[OF assms(1)] by (simp add: bij_betw_def)
  have "inv_into \<Gamma> (gamma_enum \<Gamma> bl) (gamma_enum \<Gamma> bl x) = x"
    by (rule inv_into_f_f[OF inj assms(2)])
  thus ?thesis using lt by (simp add: gamma_unenum_def)
qed

text \<open>Reading an encoded symbol back via \<open>bits_to_nat\<close>
  recovers its enumeration index, the named form of the local
  \<open>bn\<close> fact inside \<open>decode_symbol_encode_symbol\<close>.  Needed
  by the read-phase accumulator below.\<close>

lemma bits_to_nat_encode_symbol:
  assumes "finite \<Gamma>" and "x \<in> \<Gamma>"
  shows "bits_to_nat (encode_symbol \<Gamma> bl x) = gamma_enum \<Gamma> bl x"
proof -
  have lt_x: "gamma_enum \<Gamma> bl x < 2 ^ block_width \<Gamma>"
    using gamma_enum_lt_card[OF assms, of bl] card_le_two_pow_block_width[of \<Gamma>]
    by linarith
  show ?thesis
    unfolding encode_symbol_def by (rule syms_to_nat_nat_to_syms[OF _ lt_x]) simp
qed

text \<open>The read-phase accumulator: one bit-cell folded into the
  running symbol.  Mirrors the per-bit update the read substeps
  perform — \<open>buf := gamma_unenum (2 \<cdot> gamma_enum buf +
  bit_value c)\<close> — reading the \<open>b\<close>-cell block most-significant
  bit first.\<close>

definition ar_acc :: "'a set \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> sym4 \<Rightarrow> 'a" where
  "ar_acc \<Gamma> bl b c = gamma_unenum \<Gamma> bl (2 * gamma_enum \<Gamma> bl b + bit_value c)"

text \<open>Folding the accumulator from the seed \<open>gamma_unenum 0\<close>
  over a bit list whose value is in enumeration range yields exactly
  \<open>gamma_unenum (bits_to_nat ys)\<close>.  Proof by \<open>rev_induct\<close>:
  appending a low bit shifts the running value left and adds it
  (\<open>syms_to_nat_snoc\<close>), the prefix value stays in range
  (\<open>bits_to_nat zs \<le> bits_to_nat (zs @ [b])\<close>, no separate
  \<open>take\<close>-bound lemma needed), and the \<open>gamma_enum \<circ>
  gamma_unenum\<close> round-trip cancels at each step.\<close>

lemma foldl_ar_acc_eq:
  assumes "finite \<Gamma>"
  shows "set ys \<subseteq> {BIT0, BIT1} \<Longrightarrow> bits_to_nat ys < card \<Gamma>
          \<Longrightarrow> foldl (ar_acc \<Gamma> bl) (gamma_unenum \<Gamma> bl 0) ys
                = gamma_unenum \<Gamma> bl (bits_to_nat ys)"
proof (induct ys rule: rev_induct)
  case Nil
  show ?case by simp
next
  case (snoc b zs)
  have set_zs: "set zs \<subseteq> {BIT0, BIT1}" using snoc.prems(1) by simp
  have snoc_eq: "bits_to_nat (zs @ [b]) = 2 * bits_to_nat zs + bit_value b"
    by (rule syms_to_nat_snoc)
  have bound_zs: "bits_to_nat zs < card \<Gamma>"
    using snoc.prems(2) snoc_eq by linarith
  have IH: "foldl (ar_acc \<Gamma> bl) (gamma_unenum \<Gamma> bl 0) zs
              = gamma_unenum \<Gamma> bl (bits_to_nat zs)"
    using snoc.hyps set_zs bound_zs by blast
  have ge_zs: "gamma_enum \<Gamma> bl
                 (foldl (ar_acc \<Gamma> bl) (gamma_unenum \<Gamma> bl 0) zs)
               = bits_to_nat zs"
    using IH gamma_enum_gamma_unenum[OF assms bound_zs] by simp
  have "foldl (ar_acc \<Gamma> bl) (gamma_unenum \<Gamma> bl 0) (zs @ [b])
          = ar_acc \<Gamma> bl
              (foldl (ar_acc \<Gamma> bl) (gamma_unenum \<Gamma> bl 0) zs) b"
    by simp
  also have "\<dots> = gamma_unenum \<Gamma> bl (2 * bits_to_nat zs + bit_value b)"
    by (simp add: ar_acc_def ge_zs)
  also have "\<dots> = gamma_unenum \<Gamma> bl (bits_to_nat (zs @ [b]))"
    using snoc_eq by simp
  finally show ?case .
qed

text \<open>Read-phase decode correctness: folding the accumulator over
  a symbol's encoding recovers the symbol.  This is the arithmetic
  content the read phase delivers — every tape's \<open>buf\<close> field,
  after walking its \<open>b\<close>-cell block, holds the source cell's
  value.\<close>

lemma foldl_ar_acc_encode_symbol:
  assumes "finite \<Gamma>" and "x \<in> \<Gamma>"
  shows "foldl (ar_acc \<Gamma> bl) (gamma_unenum \<Gamma> bl 0) (encode_symbol \<Gamma> bl x) = x"
proof -
  have cd: "set (encode_symbol \<Gamma> bl x) \<subseteq> {BIT0, BIT1}"
    by (rule encode_symbol_cell_domain)
  have bn: "bits_to_nat (encode_symbol \<Gamma> bl x) = gamma_enum \<Gamma> bl x"
    by (rule bits_to_nat_encode_symbol[OF assms])
  have lt: "bits_to_nat (encode_symbol \<Gamma> bl x) < card \<Gamma>"
    using bn gamma_enum_lt_card[OF assms] by simp
  have "foldl (ar_acc \<Gamma> bl) (gamma_unenum \<Gamma> bl 0) (encode_symbol \<Gamma> bl x)
          = gamma_unenum \<Gamma> bl (bits_to_nat (encode_symbol \<Gamma> bl x))"
    by (rule foldl_ar_acc_eq[OF assms(1) cd lt])
  also have "\<dots> = gamma_unenum \<Gamma> bl (gamma_enum \<Gamma> bl x)" using bn by simp
  also have "\<dots> = x" by (rule gamma_unenum_gamma_enum[OF assms])
  finally show ?thesis .
qed

text \<open>The decoder's neutral element is the blank: \<open>gamma_unenum
  \<Gamma> bl 0 = bl\<close>, since the anchor puts \<open>bl\<close> at index
  \<open>0\<close> and the enumeration is injective.\<close>

lemma gamma_unenum_zero:
  assumes "finite \<Gamma>" and "bl \<in> \<Gamma>"
  shows "gamma_unenum \<Gamma> bl 0 = bl"
proof -
  have npos: "0 < card \<Gamma>" using assms by (auto simp: card_gt_0_iff)
  have inj: "inj_on (gamma_enum \<Gamma> bl) \<Gamma>"
    using gamma_enum_bij[OF assms(1)] by (simp add: bij_betw_def)
  have "gamma_unenum \<Gamma> bl 0 = inv_into \<Gamma> (gamma_enum \<Gamma> bl) 0"
    using npos by (simp add: gamma_unenum_def)
  also have "\<dots>
        = inv_into \<Gamma> (gamma_enum \<Gamma> bl) (gamma_enum \<Gamma> bl bl)"
    using gamma_enum_blank[OF assms(1)] by simp
  also have "\<dots> = bl" by (rule inv_into_f_f[OF inj assms(2)])
  finally show ?thesis .
qed

text \<open>An all-\<open>BLANK4\<close> block decodes to the blank: \<open>bl\<close> is a
  fixpoint of the accumulator on a \<open>BLANK4\<close> cell (\<open>2 \<cdot>
  gamma_enum bl + 0 = 0\<close>, decoding back to \<open>bl\<close>), so folding
  any number of \<open>BLANK4\<close> cells from \<open>bl\<close> stays \<open>bl\<close>.
  This is the read-phase decode correctness for the blank cell, the
  \<open>BLANK4\<close> counterpart of \<open>foldl_ar_acc_encode_symbol\<close>.\<close>

lemma foldl_ar_acc_blank:
  assumes "finite \<Gamma>" and "bl \<in> \<Gamma>"
  shows "foldl (ar_acc \<Gamma> bl) bl (replicate k BLANK4) = bl"
proof (induct k)
  case 0
  show ?case by simp
next
  case (Suc k)
  have step: "ar_acc \<Gamma> bl bl BLANK4 = bl"
    unfolding ar_acc_def
    using gamma_enum_blank[OF assms(1)] gamma_unenum_zero[OF assms] by simp
  have "foldl (ar_acc \<Gamma> bl) bl (replicate (Suc k) BLANK4)
          = foldl (ar_acc \<Gamma> bl) (ar_acc \<Gamma> bl bl BLANK4)
                  (replicate k BLANK4)"
    by (simp add: replicate_Suc)
  also have "\<dots> = foldl (ar_acc \<Gamma> bl) bl (replicate k BLANK4)"
    using step by simp
  also have "\<dots> = bl" by (rule Suc.hyps)
  finally show ?case .
qed

end
