theory Wrap_Base
  imports "Multitape_TM_Substrate.Multitape_Substrate"
begin

section \<open>Encoding-wrap combinator\<close>

text \<open>The encoding-wrap combinator.  Given a substrate machine
  \<open>M\<close> over an encoded alphabet \<open>'b\<close> and a per-block packer
  \<open>pack :: 'a list \<Rightarrow> 'b\<close> together with a block size \<open>c\<close>, the
  combinator produces a substrate machine over the union
  alphabet \<open>('a, 'b) wrap_alphabet = Raw 'a | Enc 'b\<close> at the
  textbook tape count \<open>k_tm M\<close> (no extra tape): the user's raw
  input starts on tape \<open>0\<close>, which the wrap reuses as a work tape
  rather than adding one (faithful \<open>k\<close>-tape section below).

  The wrap operates in five reachable phases:
  \<^enum> @{text W_Init} — advance both \<open>W_User\<close> and \<open>W_M 0\<close> past their
    LE markers in a single super-step.
  \<^enum> @{text "W_Buf ws"} — accumulate up to \<open>c\<close> raw symbols from
    \<open>W_User\<close>; on filling the buffer, pack and write one block
    to \<open>W_M 0\<close>; on seeing an \<open>Enc _\<close> symbol (blank past the input
    region), flush any partial buffer and proceed to reset.
  \<^enum> @{text W_Reset} — move \<open>W_M 0\<close>'s head left until LE, restoring
    the canonical "head at position 0 reading LE" position M
    expects at the start of its own computation.
  \<^enum> @{text W_Disp} — single transition handing over to M.
  \<^enum> @{text "W_Run q"} — simulate M directly: every M-\<open>\<delta>\<close> entry
    lifts to a wrap-\<open>\<delta>\<close> entry that reads M's tapes through the
    \<open>Enc\<close> embedding and leaves \<open>W_User\<close> untouched.

  Halt propagation rides directly on the @{text W_Run}
  constructor: the wrap's accept state is @{text "W_Run (t_tm M)"},
  inheriting M's acceptance.  The wrap's reject state
  @{text W_Rej} is declared for substrate compliance (the
  @{text "t \<noteq> r"} requirement) but is unreachable from the start
  state.\<close>

text \<open>Architecture note: the wrap is monolithic at the substrate
  level.  The substrate has no generic machine-composition
  combinator, so the wrap's per-cell read, head-positioning, and
  per-cell write actions are written directly into the wrap's
  \<open>\<delta>\<close>-table rather than as composed sub-machines.\<close>


subsection \<open>Wrap alphabet\<close>

text \<open>Disjoint union of user-facing and encoded alphabets.
  Constructors are injective and disjoint;
  the wrap's substrate-level blank and LE symbols are chosen
  from the \<open>Enc\<close>-image to keep lifted M-transitions transparent.\<close>

datatype ('a, 'b) wrap_alphabet = Raw 'a | Enc 'b


subsection \<open>Wrap tape index\<close>

text \<open>Value-level tape indices (@{typ nat}).  The wrap keeps the
  textbook tape count @{term "k_tm M"} --- \<^emph>\<open>no\<close> extra tape.  Tape
  \<open>0\<close> initially holds the user's raw input (matching the substrate
  convention); once the encoder has consumed it, that spent tape is
  reused as one of M's work tapes rather than a fresh tape being
  prepended (faithful \<open>k\<close>-tape section below).\<close>


subsection \<open>Wrap state space\<close>

text \<open>Five reachable phases plus a formal reject.  The
  @{text W_Buf} payload is a partial encoder buffer of length
  strictly less than \<open>c\<close>; the @{text W_Run} payload is the
  current M-state lifted through @{text W_Run}.\<close>

datatype ('q, 'a, 'b) wrap_state =
    W_Init
  | W_Buf "'a list"
  | W_Reset
  | W_Disp
  | W_Run 'q
  | W_Rej

text \<open>The wrap's state set: @{text W_Init}, @{text W_Reset},
  @{text W_Disp}, @{text W_Rej} as singletons; @{text W_Buf}
  variants ranging over partial buffers of length \<open><c\<close> with
  symbols drawn from the user-facing alphabet; and @{text W_Run}
  variants ranging over M's state set.  Polynomial in
  \<open>|\<Sigma>u| ^ c + |Q_tm M|\<close>; finite when both factors are.\<close>

definition wrap_state_set ::
  "('q, 'b) mttm \<Rightarrow> nat \<Rightarrow> 'a set
   \<Rightarrow> ('q, 'a, 'b) wrap_state set"
where
  "wrap_state_set M c \<Sigma>u =
     {W_Init, W_Reset, W_Disp, W_Rej}
     \<union> {W_Buf ws | ws. length ws < c \<and> set ws \<subseteq> \<Sigma>u}
     \<union> W_Run ` Q_tm M"


subsection \<open>Generic single-tape rewind\<close>

text \<open>The one piece of the wrap \<open>\<delta>\<close>-relation kept in the base: a generic
  family for rewinding a single tape's head back to its \<open>le\<close> marker.  The
  full wrap transition relations — the phase-local encoder, reset, dispatch,
  and lifted-M families — are assembled downstream, on the \<open>_gen\<close> builders
  shared with the plant wrap \<open>wrap_delta\<close>; only this rewind family, reused
  verbatim there, lives at the base.\<close>

text \<open>\<open>wrap_rewind_loop_delta_gen qf j K M\<close> walks tape @{text j}'s head one
  cell left per step while it reads a non-\<open>le\<close> symbol, looping in state
  @{text qf} and leaving every other tape idle.  Parameterised over the tape
  index @{text j} and the blank-tail boundary @{text K}, so it rewinds
  \<^emph>\<open>any\<close> tape at either wrap tape count (@{term "Suc (k_tm M)"} or the
  faithful @{term "k_tm M"}); the loop state @{text qf} lets it splice into any
  phase.  The plant wrap instantiates it at @{term "j = Suc 0"} to rewind the
  storage tape (\<open>wrap_delta\<close>'s \<open>rloop\<close> family).\<close>

definition wrap_rewind_loop_delta_gen ::
  "('q, 'a, 'b) wrap_state \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> ('q, 'b) mttm \<Rightarrow> 'a set
   \<Rightarrow> (('q, 'a, 'b) wrap_state
       \<times> (nat \<Rightarrow> ('a, 'b) wrap_alphabet)
       \<times> ('q, 'a, 'b) wrap_state
       \<times> (nat \<Rightarrow> ('a, 'b) wrap_alphabet)
       \<times> (nat \<Rightarrow> dir)) set"
where
  "wrap_rewind_loop_delta_gen qf j K M \<Sigma>u =
     { (qf, sym, qf, sym, \<lambda>t. if t = j then dir.L else dir.N)
       | sym.
           sym j \<noteq> Enc (le_tm M)
           \<and> (\<forall>i\<ge>K. sym i = Enc (bl_tm M))
           \<and> sym \<in> UNIV \<rightarrow> Raw ` \<Sigma>u \<union> Enc ` \<Gamma>_tm M }"


subsection \<open>User-facing language and time-bounded acceptance\<close>

text \<open>The user-facing language of a
  wrap-shaped machine is the @{const Lang_mttm} preimage under
  the @{text Raw} embedding: a user input @{text w} is in the
  user-facing language iff its @{text Raw}-embedded form is in
  the wrap's substrate-level language.  Same routing for
  time-bounded acceptance.  These predicates are stated over
  arbitrary @{type mttm} values whose alphabet is a
  @{type wrap_alphabet}; their primary use is on the encoding-wrap
  machines built downstream (the plant wrap \<open>encoding_wrap\<close>), but the
  definitions are alphabet-shape-agnostic.\<close>

definition Lang_user_wrap ::
  "('q, ('a, 'b) wrap_alphabet) mttm \<Rightarrow> 'a list set"
where
  "Lang_user_wrap M'' = {w. map Raw w \<in> Lang_mttm M''}"

definition accepts_in_time_user_wrap ::
  "('q, ('a, 'b) wrap_alphabet) mttm
   \<Rightarrow> 'a list \<Rightarrow> nat \<Rightarrow> bool"
where
  "accepts_in_time_user_wrap M'' w t =
     accepts_in_time_mttm M'' (map Raw w) t"

subsection \<open>Encoder image and state-set finiteness\<close>

text \<open>Two shared base helpers of the encoding wrap: the encoder image
  function @{text wrap_enc} (the packed form of a user input, which
  @{const Lang_user_wrap} and @{const accepts_in_time_user_wrap} refer to)
  and the finiteness of the wrap state set.  Both feed the downstream wrap
  well-formedness, determinism, and language proofs; neither depends on the
  wrap's transition relation.\<close>

text \<open>The encoder image of a user input: chunk @{term w} into blocks of
  size @{term c}, apply @{term pack} to each block.  This is the
  full encoder @{text "enc :: 'a list \<Rightarrow> 'b list"}, derived from
  @{term pack} and @{term c} because the wrap constructions take the
  per-chunk packer plus chunk size rather than an opaque encoder argument.
  Recursion is over @{text "drop c w"}, not a direct subterm, hence
  @{command function}+@{command termination} rather than @{command fun}.\<close>

function wrap_enc ::
  "('a list \<Rightarrow> 'b) \<Rightarrow> nat \<Rightarrow> 'a list \<Rightarrow> 'b list"
where
  "wrap_enc pack 0 w = []"
| "wrap_enc pack (Suc k) [] = []"
| "wrap_enc pack (Suc k) (x # xs) =
     pack (take (Suc k) (x # xs))
     # wrap_enc pack (Suc k) (drop (Suc k) (x # xs))"
  by pat_completeness auto
termination
  by (relation "measure (\<lambda>(_, _, w). length w)") auto

text \<open>Helper: the wrap state set is finite when M is valid and the
  user alphabet is finite.  @{text W_Buf}'s payload range is finite
  because length is bounded by @{term c} and entries are drawn from
  the finite @{term \<Sigma>u}; @{text W_Run}'s payload range is finite
  because @{term "Q_tm M"} is finite by @{thm valid_mttm_finite_Q}.\<close>

lemma finite_wrap_state_set:
  assumes "valid_mttm M"
      and "finite \<Sigma>u"
  shows "finite (wrap_state_set M c \<Sigma>u)"
proof -
  have fin_Q: "finite (Q_tm M)"
    by (rule valid_mttm_finite_Q[OF assms(1)])
  have fin_buf: "finite {W_Buf ws | ws. length ws < c \<and> set ws \<subseteq> \<Sigma>u}"
  proof -
    have "{ws. length ws < c \<and> set ws \<subseteq> \<Sigma>u} \<subseteq> {ws. set ws \<subseteq> \<Sigma>u \<and> length ws \<le> c}"
      by auto
    moreover have "finite {ws. set ws \<subseteq> \<Sigma>u \<and> length ws \<le> c}"
      using finite_lists_length_le[OF \<open>finite \<Sigma>u\<close>] by simp
    ultimately have "finite {ws. length ws < c \<and> set ws \<subseteq> \<Sigma>u}"
      by (rule finite_subset)
    hence "finite (W_Buf ` {ws. length ws < c \<and> set ws \<subseteq> \<Sigma>u})"
      by (rule finite_imageI)
    moreover have "{W_Buf ws | ws. length ws < c \<and> set ws \<subseteq> \<Sigma>u}
                     = W_Buf ` {ws. length ws < c \<and> set ws \<subseteq> \<Sigma>u}"
      by blast
    ultimately show ?thesis by metis
  qed
  have fin_run: "finite (W_Run ` Q_tm M)"
    using fin_Q by (rule finite_imageI)
  have "finite ({W_Init, W_Reset, W_Disp, W_Rej}
                  \<union> {W_Buf ws | ws. length ws < c \<and> set ws \<subseteq> \<Sigma>u}
                  \<union> W_Run ` Q_tm M)"
    using fin_buf fin_run by simp
  thus ?thesis
    unfolding wrap_state_set_def by simp
qed

subsection \<open>Encoder-image support lemmas\<close>

text \<open>Structural facts about the encoder image @{const wrap_enc}, which chunks
  the user input into blocks of size @{term c} and applies @{term pack} to each.
  These lemmas pin down that image cell-by-cell: the per-block content of a full
  block (@{text wrap_enc_nth}) and of the final short block
  (@{text wrap_enc_nth_partial}), the length of the packed sequence
  (@{text length_wrap_enc}), and the tape-alphabet membership of every packed
  symbol --- each lies in the @{text Enc}-image of @{term "\<Gamma>_tm M"}
  (@{text wrap_enc_in_Gamma}), is distinct from the @{text le} marker
  (@{text wrap_enc_ne_le}), and lies in @{term "Sigma_tm M"} whenever the
  packer contracts into it (@{text wrap_enc_in_Sigma}, with that packing
  side-condition isolated in @{text pack_take_in_set_wrap_enc}).

  This is shared base machinery.  The faithful \<open>k\<close>-tape encoder simulation ---
  the \<open>_gen\<close> / \<open>_B\<close> transition chains that write @{const wrap_enc} onto the
  storage tape --- reads these invariants back to certify the encoded input; and
  the AE-wrap glue @{text wrap_enc_eq_encode_input} builds on them to match
  @{const wrap_enc} against the alphabet-enlargement @{text encode_input}.\<close>

text \<open>Support lemma about @{const wrap_enc}: when a full block at offset
  @{term "i * c"} fits within @{term w}, the @{term i}-th encoded entry is the
  pack of that block.  Proof is by induction on @{term i}, peeling one block
  off the front per step via @{const wrap_enc}'s recursive equation.\<close>

lemma wrap_enc_nth:
  assumes "0 < c"
      and "(Suc i) * c \<le> length w"
  shows "wrap_enc pack c w ! i = pack (take c (drop (i * c) w))"
  using assms
proof (induction i arbitrary: w)
  case 0
  from \<open>0 < c\<close> obtain k where c_eq: "c = Suc k"
    by (cases c) auto
  from \<open>Suc 0 * c \<le> length w\<close> have c_le: "c \<le> length w"
    by simp
  with c_eq have "w \<noteq> []"
    by (cases w) auto
  then obtain x xs where w_eq: "w = x # xs"
    by (cases w) auto
  have "wrap_enc pack c w
          = pack (take c (x # xs)) # wrap_enc pack c (drop c (x # xs))"
    using c_eq w_eq by simp
  hence "wrap_enc pack c w ! 0 = pack (take c (x # xs))"
    by simp
  also have "\<dots> = pack (take c (drop (0 * c) w))"
    using w_eq by simp
  finally show ?case .
next
  case (Suc i)
  from \<open>0 < c\<close> obtain k where c_eq: "c = Suc k"
    by (cases c) auto
  from \<open>Suc (Suc i) * c \<le> length w\<close> have c_le: "c \<le> length w"
    by simp
  with c_eq have "w \<noteq> []"
    by (cases w) auto
  then obtain x xs where w_eq: "w = x # xs"
    by (cases w) auto
  have unfold:
    "wrap_enc pack c w
       = pack (take c (x # xs)) # wrap_enc pack c (drop c (x # xs))"
    using c_eq w_eq by simp
  have nth_step:
    "wrap_enc pack c w ! Suc i = wrap_enc pack c (drop c w) ! i"
    using unfold w_eq by simp
  have len_drop: "Suc i * c \<le> length (drop c w)"
    using \<open>Suc (Suc i) * c \<le> length w\<close> by simp
  have ih:
    "wrap_enc pack c (drop c w) ! i = pack (take c (drop (i * c) (drop c w)))"
    using Suc.IH[OF \<open>0 < c\<close> len_drop] .
  have drop_drop: "drop (i * c) (drop c w) = drop (Suc i * c) w"
    by (simp add: add.commute)
  from nth_step ih drop_drop
  show ?case by simp
qed

text \<open>Length of @{const wrap_enc}: @{term "length w div c"} full blocks plus
  one partial block if @{term "length w mod c \<noteq> 0"}.  Proof is by strong
  induction on @{term "length w"}: case-split on whether \<open>c \<le> length w\<close>;
  if not, the encoding is empty (\<open>w = []\<close>) or a single partial block; if so,
  peel one full block off the front and recurse on @{term "drop c w"}.\<close>

lemma length_wrap_enc:
  assumes "0 < c"
  shows "length (wrap_enc pack c w) =
         length w div c + (if length w mod c = 0 then 0 else 1)"
  using assms
proof (induction "length w" arbitrary: w rule: less_induct)
  case less
  from \<open>0 < c\<close> obtain k where c_eq: "c = Suc k" by (cases c) auto
  show ?case
  proof (cases "c \<le> length w")
    case False
    hence w_short: "length w < c" by simp
    show ?thesis
    proof (cases w)
      case Nil
      with c_eq show ?thesis by simp
    next
      case (Cons x xs)
      have unfold:
        "wrap_enc pack c w = pack (take c w) # wrap_enc pack c (drop c w)"
        using c_eq Cons by simp
      have drop_eq: "drop c w = []"
        using w_short by simp
      have wrap_eq: "wrap_enc pack c w = [pack (take c w)]"
        using unfold drop_eq c_eq by simp
      from w_short \<open>0 < c\<close> have div_eq: "length w div c = 0" by simp
      from w_short Cons \<open>0 < c\<close> have mod_pos: "length w mod c \<noteq> 0"
        by (auto simp: mod_less)
      from wrap_eq have "length (wrap_enc pack c w) = 1" by simp
      with div_eq mod_pos show ?thesis by simp
    qed
  next
    case True
    hence c_le: "c \<le> length w" by simp
    have w_nonempty: "w \<noteq> []" using c_le \<open>0 < c\<close> by auto
    then obtain x xs where w_cons: "w = x # xs" by (cases w) auto
    have unfold:
      "wrap_enc pack c w = pack (take c w) # wrap_enc pack c (drop c w)"
      using c_eq w_cons by simp
    have tail_len: "length (drop c w) = length w - c" by simp
    have tail_less: "length (drop c w) < length w"
      using c_le \<open>0 < c\<close> tail_len by simp
    from less.hyps[OF tail_less \<open>0 < c\<close>]
    have ih: "length (wrap_enc pack c (drop c w)) =
              length (drop c w) div c +
              (if length (drop c w) mod c = 0 then 0 else 1)" .
    have div_step: "length w div c = (length w - c) div c + 1"
      using c_le \<open>0 < c\<close> by (simp add: le_div_geq)
    have mod_step: "length w mod c = (length w - c) mod c"
      using c_le \<open>0 < c\<close> by (simp add: le_mod_geq)
    from unfold have "length (wrap_enc pack c w) =
                      1 + length (wrap_enc pack c (drop c w))" by simp
    also have "\<dots> = 1 + length (drop c w) div c +
                    (if length (drop c w) mod c = 0 then 0 else 1)"
      using ih by simp
    also have "\<dots> = length w div c +
                    (if length w mod c = 0 then 0 else 1)"
      using div_step mod_step tail_len by simp
    finally show ?thesis .
  qed
qed

text \<open>The last entry of @{const wrap_enc} when the input has a non-trivial
  trailing partial block: it is the @{term pack} of that trailing block
  @{term "drop (length w div c * c) w"} (of length @{term "length w mod c"}).
  Proof by the same strong-induction shape as @{thm[source] length_wrap_enc}, with
  the partial-block case yielding the singleton directly and the full-block
  case recursing on @{term "drop c w"}.\<close>

lemma wrap_enc_nth_partial:
  assumes "0 < c"
      and "length w mod c \<noteq> 0"
  shows "wrap_enc pack c w ! (length w div c) =
         pack (drop ((length w div c) * c) w)"
  using assms
proof (induction "length w" arbitrary: w rule: less_induct)
  case less
  from \<open>0 < c\<close> obtain k where c_eq: "c = Suc k" by (cases c) auto
  show ?case
  proof (cases "c \<le> length w")
    case False
    hence w_short: "length w < c" by simp
    from \<open>length w mod c \<noteq> 0\<close> w_short \<open>0 < c\<close>
    have w_nonempty: "w \<noteq> []" by auto
    then obtain x xs where w_cons: "w = x # xs" by (cases w) auto
    have unfold:
      "wrap_enc pack c w = pack (take c w) # wrap_enc pack c (drop c w)"
      using c_eq w_cons by simp
    have drop_eq: "drop c w = []" using w_short by simp
    have take_all: "take c w = w" using w_short by simp
    have wrap_eq: "wrap_enc pack c w = [pack w]"
      using unfold drop_eq take_all c_eq by simp
    from w_short \<open>0 < c\<close> have div_eq: "length w div c = 0" by simp
    have lhs: "wrap_enc pack c w ! (length w div c) = pack w"
      using wrap_eq div_eq by simp
    have rhs: "drop ((length w div c) * c) w = w"
      using div_eq by simp
    from lhs rhs show ?thesis by simp
  next
    case True
    hence c_le: "c \<le> length w" by simp
    have w_nonempty: "w \<noteq> []" using c_le \<open>0 < c\<close> by auto
    then obtain x xs where w_cons: "w = x # xs" by (cases w) auto
    have unfold:
      "wrap_enc pack c w = pack (take c w) # wrap_enc pack c (drop c w)"
      using c_eq w_cons by simp
    have tail_less: "length (drop c w) < length w"
      using c_le \<open>0 < c\<close> by simp
    have tail_mod: "length (drop c w) mod c = length w mod c"
      using c_le \<open>0 < c\<close> by (simp add: le_mod_geq)
    have tail_div: "length (drop c w) div c = length w div c - 1"
      using c_le \<open>0 < c\<close> by (simp add: le_div_geq)
    have div_pos: "length w div c > 0"
      using c_le \<open>0 < c\<close> by (simp add: le_div_geq)
    have mod_pos_tail: "length (drop c w) mod c \<noteq> 0"
      using \<open>length w mod c \<noteq> 0\<close> tail_mod by simp
    note ih = less.hyps[OF tail_less \<open>0 < c\<close> mod_pos_tail]
    have idx_step:
      "wrap_enc pack c w ! (length w div c) =
       wrap_enc pack c (drop c w) ! (length w div c - 1)"
      using unfold div_pos by (simp add: nth_Cons')
    also have "\<dots> = wrap_enc pack c (drop c w) ! (length (drop c w) div c)"
      using tail_div by simp
    also have "\<dots> = pack (drop ((length (drop c w) div c) * c) (drop c w))"
      using ih .
    also have "drop ((length (drop c w) div c) * c) (drop c w)
               = drop ((length w div c) * c) w"
      using tail_div c_le div_pos
      by (simp add: drop_drop algebra_simps)
    finally show ?thesis .
  qed
qed

text \<open>Derived safety lemmas for entries of @{const wrap_enc}: under the pack
  contracts (@{term "pack (take c (drop (i * c) w)) \<in> \<Gamma>_tm M"} and the
  \<open>\<noteq> le_tm M\<close> companion, universally quantified over indices @{term i} with
  @{term "i * c < length w"}), every entry of @{term "wrap_enc pack c w"} lies in
  @{term "\<Gamma>_tm M"} and differs from @{term "le_tm M"}.  Proof case-splits on
  whether the entry is a full block (@{term "j < length w div c"}, served by
  @{thm[source] wrap_enc_nth}) or the trailing partial block
  (@{term "j = length w div c"} forced by length, served by
  @{thm[source] wrap_enc_nth_partial}).  For the partial case
  @{term "take c (drop (j * c) w) = drop (j * c) w"} because the drop has length
  @{term "length w mod c"} < @{term c}, so the universal pack contract still
  fires.  These lemmas are the bridge from the pack contracts to the per-cell
  symbol safety conditions used by @{text wrap_reset_loop_delta} and
  @{text wrap_reset_done_delta}.\<close>

text \<open>Bridge for the reverse direction (consumed by @{text wrap_language_reverse}):
  every pack output of the form @{term "pack (take c (drop (i * c) w))"} for
  @{term "i * c < length w"} appears as some entry of @{term "wrap_enc pack c w"}.
  Case-splits on whether the @{term i}-th block is full
  (@{term "(Suc i) * c \<le> length w"}, served by @{thm[source] wrap_enc_nth}) or the
  trailing partial block (forced when @{term "(Suc i) * c > length w"} and
  @{term "i * c < length w"}, served by @{thm[source] wrap_enc_nth_partial}).  Composing
  with @{prop "set (wrap_enc pack c w) \<subseteq> Sigma_tm M"} (from
  @{text "wrap_enc pack c w \<in> Lang_mttm M"}) yields the pack contracts that
  @{text encoder_phase_terminates} / @{text reset_phase_terminates} need.\<close>

lemma pack_take_in_set_wrap_enc:
  assumes c_pos: "0 < c"
      and i_c_lt: "i * c < length w"
    shows "pack (take c (drop (i * c) w)) \<in> set (wrap_enc pack c w)"
proof -
  let ?L = "length (wrap_enc pack c w)"
  let ?q = "length w div c"
  let ?r = "length w mod c"
  have len_eq: "?L = ?q + (if ?r = 0 then 0 else 1)"
    by (rule length_wrap_enc[OF c_pos])
  have q_c_le: "?q * c \<le> length w"
    by (rule div_times_less_eq_dividend)
  have div_mod_eq: "?q * c + ?r = length w"
    by (rule div_mult_mod_eq)
  show ?thesis
  proof (cases "(Suc i) * c \<le> length w")
    case True
    \<comment> \<open>Full block at index @{term i}.\<close>
    have div_le_mono_step: "(Suc i) * c div c \<le> length w div c"
      using True div_le_mono by blast
    have Suc_i_le_q: "Suc i \<le> ?q"
      using div_le_mono_step c_pos by simp
    have i_lt_q: "i < ?q" using Suc_i_le_q by simp
    have i_lt_L: "i < ?L" using i_lt_q len_eq by simp
    have nth_eq: "wrap_enc pack c w ! i = pack (take c (drop (i * c) w))"
      by (rule wrap_enc_nth[OF c_pos True])
    show ?thesis using nth_eq i_lt_L by (metis nth_mem)
  next
    case False
    \<comment> \<open>Partial trailing block: @{term i} forced to equal @{term ?q}.\<close>
    hence Sci_gt: "length w < (Suc i) * c" by simp
    \<comment> \<open>From @{prop "i * c < length w"}: @{term "i \<le> ?q"}.\<close>
    have div_le_mono_step: "i * c div c \<le> length w div c"
      using i_c_lt by (intro div_le_mono) simp
    have i_le_q: "i \<le> ?q" using div_le_mono_step c_pos by simp
    \<comment> \<open>From \<open>Sci_gt\<close>: @{term "?q \<le> i"} (else \<open>(Suc i) * c \<le> ?q * c \<le> length w\<close>).\<close>
    have q_le_i: "?q \<le> i"
    proof (rule ccontr)
      assume "\<not> ?q \<le> i"
      hence "i < ?q" by simp
      hence "Suc i \<le> ?q" by simp
      hence "(Suc i) * c \<le> ?q * c" by (rule mult_le_mono1)
      with q_c_le have "(Suc i) * c \<le> length w" by linarith
      with Sci_gt show False by simp
    qed
    have i_eq: "i = ?q" using i_le_q q_le_i by simp
    have ic_eq_qc: "i * c = ?q * c" using i_eq by simp
    have mod_pos: "0 < ?r"
      using i_c_lt ic_eq_qc div_mod_eq by linarith
    have mod_ne: "?r \<noteq> 0" using mod_pos by simp
    have len_drop_basic: "length (drop (i * c) w) = length w - i * c"
      by simp
    have len_drop: "length (drop (i * c) w) = ?r"
      using len_drop_basic ic_eq_qc div_mod_eq by linarith
    have mod_lt_c: "?r < c" using c_pos by (rule mod_less_divisor)
    have take_eq: "take c (drop (i * c) w) = drop (i * c) w"
      using len_drop mod_lt_c by simp
    have partial_nth:
      "wrap_enc pack c w ! ?q = pack (drop (?q * c) w)"
      by (rule wrap_enc_nth_partial[OF c_pos mod_ne])
    have nth_eq:
      "wrap_enc pack c w ! i = pack (take c (drop (i * c) w))"
      using partial_nth i_eq take_eq ic_eq_qc by simp
    have i_lt_L: "i < ?L" using i_eq mod_ne len_eq by simp
    show ?thesis using nth_eq i_lt_L by (metis nth_mem)
  qed
qed

lemma wrap_enc_in_Gamma:
  assumes c_pos: "0 < c"
      and pack_contract_in:
        "\<And>i. i * c < length w \<Longrightarrow> pack (take c (drop (i * c) w)) \<in> \<Gamma>_tm M"
      and j_lt: "j < length (wrap_enc pack c w)"
    shows "wrap_enc pack c w ! j \<in> \<Gamma>_tm M"
proof -
  have len_eq:
    "length (wrap_enc pack c w)
       = length w div c + (if length w mod c = 0 then 0 else 1)"
    by (rule length_wrap_enc[OF c_pos])
  have q_c_le: "(length w div c) * c \<le> length w"
    by (rule div_times_less_eq_dividend)
  show ?thesis
  proof (cases "j < length w div c")
    case True
    hence Suc_j_le_q: "Suc j \<le> length w div c" by simp
    have Sjc_le_qc: "(Suc j) * c \<le> (length w div c) * c"
      by (rule mult_le_mono1[OF Suc_j_le_q])
    hence Sjc_le: "(Suc j) * c \<le> length w" using q_c_le by linarith
    have jc_lt_Sjc: "j * c < Suc j * c" using c_pos by simp
    have jc_lt: "j * c < length w"
      using jc_lt_Sjc Sjc_le by linarith
    have nth_eq:
      "wrap_enc pack c w ! j = pack (take c (drop (j * c) w))"
      by (rule wrap_enc_nth[OF c_pos Sjc_le])
    show ?thesis using nth_eq pack_contract_in[OF jc_lt] by simp
  next
    case False
    with j_lt len_eq have j_eq: "j = length w div c"
                          and mod_ne: "length w mod c \<noteq> 0"
      by (auto split: if_splits)
    have nth_eq:
      "wrap_enc pack c w ! j = pack (drop ((length w div c) * c) w)"
      using j_eq wrap_enc_nth_partial[OF c_pos mod_ne] by simp
    have div_mod_eq: "(length w div c) * c + length w mod c = length w"
      by (rule div_mult_mod_eq)
    have mod_pos: "0 < length w mod c" using mod_ne by simp
    have jc_eq: "j * c = (length w div c) * c" using j_eq by simp
    have jc_lt: "j * c < length w"
      using jc_eq div_mod_eq mod_pos by linarith
    have len_drop_basic: "length (drop (j * c) w) = length w - j * c"
      by simp
    have len_drop: "length (drop (j * c) w) = length w mod c"
      using len_drop_basic jc_eq div_mod_eq by linarith
    have mod_lt_c: "length w mod c < c"
      using c_pos by (rule mod_less_divisor)
    have take_eq: "take c (drop (j * c) w) = drop (j * c) w"
      using len_drop mod_lt_c by simp
    have nth_eq': "wrap_enc pack c w ! j = pack (take c (drop (j * c) w))"
      using nth_eq take_eq j_eq by simp
    show ?thesis using nth_eq' pack_contract_in[OF jc_lt] by simp
  qed
qed

lemma wrap_enc_ne_le:
  assumes c_pos: "0 < c"
      and pack_contract_ne_le:
        "\<And>i. i * c < length w \<Longrightarrow> pack (take c (drop (i * c) w)) \<noteq> le_tm M"
      and j_lt: "j < length (wrap_enc pack c w)"
    shows "wrap_enc pack c w ! j \<noteq> le_tm M"
proof -
  have len_eq:
    "length (wrap_enc pack c w)
       = length w div c + (if length w mod c = 0 then 0 else 1)"
    by (rule length_wrap_enc[OF c_pos])
  have q_c_le: "(length w div c) * c \<le> length w"
    by (rule div_times_less_eq_dividend)
  show ?thesis
  proof (cases "j < length w div c")
    case True
    hence Suc_j_le_q: "Suc j \<le> length w div c" by simp
    have Sjc_le_qc: "(Suc j) * c \<le> (length w div c) * c"
      by (rule mult_le_mono1[OF Suc_j_le_q])
    hence Sjc_le: "(Suc j) * c \<le> length w" using q_c_le by linarith
    have jc_lt_Sjc: "j * c < Suc j * c" using c_pos by simp
    have jc_lt: "j * c < length w"
      using jc_lt_Sjc Sjc_le by linarith
    have nth_eq:
      "wrap_enc pack c w ! j = pack (take c (drop (j * c) w))"
      by (rule wrap_enc_nth[OF c_pos Sjc_le])
    show ?thesis using nth_eq pack_contract_ne_le[OF jc_lt] by simp
  next
    case False
    with j_lt len_eq have j_eq: "j = length w div c"
                          and mod_ne: "length w mod c \<noteq> 0"
      by (auto split: if_splits)
    have nth_eq:
      "wrap_enc pack c w ! j = pack (drop ((length w div c) * c) w)"
      using j_eq wrap_enc_nth_partial[OF c_pos mod_ne] by simp
    have div_mod_eq: "(length w div c) * c + length w mod c = length w"
      by (rule div_mult_mod_eq)
    have mod_pos: "0 < length w mod c" using mod_ne by simp
    have jc_eq: "j * c = (length w div c) * c" using j_eq by simp
    have jc_lt: "j * c < length w"
      using jc_eq div_mod_eq mod_pos by linarith
    have len_drop_basic: "length (drop (j * c) w) = length w - j * c"
      by simp
    have len_drop: "length (drop (j * c) w) = length w mod c"
      using len_drop_basic jc_eq div_mod_eq by linarith
    have mod_lt_c: "length w mod c < c"
      using c_pos by (rule mod_less_divisor)
    have take_eq: "take c (drop (j * c) w) = drop (j * c) w"
      using len_drop mod_lt_c by simp
    have nth_eq': "wrap_enc pack c w ! j = pack (take c (drop (j * c) w))"
      using nth_eq take_eq j_eq by simp
    show ?thesis using nth_eq' pack_contract_ne_le[OF jc_lt] by simp
  qed
qed

text \<open>Companion to @{thm[source] wrap_enc_in_Gamma} for the Sigma alphabet (the
  tightened pack-image discipline from the 2026-05-20 Sigma-tightening of the
  buffer-close delta-families).  Used in the forward direction of
  @{text wrap_language} to conclude @{prop "set (wrap_enc pack c w) \<subseteq>
  Sigma_tm M"} from the pack-contracts-in-Sigma derived from a wrap-accepting
  trace.\<close>

lemma wrap_enc_in_Sigma:
  assumes c_pos: "0 < c"
      and pack_contract_in_Sigma:
        "\<And>i. i * c < length w \<Longrightarrow> pack (take c (drop (i * c) w)) \<in> Sigma_tm M"
      and j_lt: "j < length (wrap_enc pack c w)"
    shows "wrap_enc pack c w ! j \<in> Sigma_tm M"
proof -
  have len_eq:
    "length (wrap_enc pack c w)
       = length w div c + (if length w mod c = 0 then 0 else 1)"
    by (rule length_wrap_enc[OF c_pos])
  have q_c_le: "(length w div c) * c \<le> length w"
    by (rule div_times_less_eq_dividend)
  show ?thesis
  proof (cases "j < length w div c")
    case True
    hence Suc_j_le_q: "Suc j \<le> length w div c" by simp
    have Sjc_le_qc: "(Suc j) * c \<le> (length w div c) * c"
      by (rule mult_le_mono1[OF Suc_j_le_q])
    hence Sjc_le: "(Suc j) * c \<le> length w" using q_c_le by linarith
    have jc_lt_Sjc: "j * c < Suc j * c" using c_pos by simp
    have jc_lt: "j * c < length w"
      using jc_lt_Sjc Sjc_le by linarith
    have nth_eq:
      "wrap_enc pack c w ! j = pack (take c (drop (j * c) w))"
      by (rule wrap_enc_nth[OF c_pos Sjc_le])
    show ?thesis using nth_eq pack_contract_in_Sigma[OF jc_lt] by simp
  next
    case False
    with j_lt len_eq have j_eq: "j = length w div c"
                          and mod_ne: "length w mod c \<noteq> 0"
      by (auto split: if_splits)
    have nth_eq:
      "wrap_enc pack c w ! j = pack (drop ((length w div c) * c) w)"
      using j_eq wrap_enc_nth_partial[OF c_pos mod_ne] by simp
    have div_mod_eq: "(length w div c) * c + length w mod c = length w"
      by (rule div_mult_mod_eq)
    have mod_pos: "0 < length w mod c" using mod_ne by simp
    have jc_eq: "j * c = (length w div c) * c" using j_eq by simp
    have jc_lt: "j * c < length w"
      using jc_eq div_mod_eq mod_pos by linarith
    have len_drop_basic: "length (drop (j * c) w) = length w - j * c"
      by simp
    have len_drop: "length (drop (j * c) w) = length w mod c"
      using len_drop_basic jc_eq div_mod_eq by linarith
    have mod_lt_c: "length w mod c < c"
      using c_pos by (rule mod_less_divisor)
    have take_eq: "take c (drop (j * c) w) = drop (j * c) w"
      using len_drop mod_lt_c by simp
    have nth_eq': "wrap_enc pack c w ! j = pack (take c (drop (j * c) w))"
      using nth_eq take_eq j_eq by simp
    show ?thesis using nth_eq' pack_contract_in_Sigma[OF jc_lt] by simp
  qed
qed

section \<open>Faithful (k-tape) encoding wrap: transpose primitives\<close>

text \<open>The faithful @{text k}-tape encoding wrap runs an alphabet-enlarged
  machine M on exactly @{term "k_tm M"} physical tapes — the textbook tape
  count, matching the textbook @{text "k > 1"}.  The obvious encoding wrap would
  prepend a dedicated raw-input tape and run M on physical tapes
  @{text "1 \<dots> k"}, costing @{term "Suc (k_tm M)"} tapes; the faithful
  variant instead reuses the spent input tape.  After the encoder has written
  the encoded input onto physical tape @{text 1} (= M's tape @{text 0}),
  physical tape @{text 0} is blanked and serves as M's tape @{text 1}, and the
  run phase \<^emph>\<open>transposes\<close> physical tapes @{text 0} and @{text 1}
  (M's tape @{text i} lives on physical tape @{term "wrap_tau i"}).  This is
  Hopcroft and Ullman's ``use the storage tape as the input tape and the old
  input tape as a storage tape''
  \<^cite>\<open>\<open>p.~290\<close> in "Hopcroft1979:introduction"\<close>, and needs
  @{term "k_tm M \<ge> 2"} (the textbook @{text "k > 1"}).
  No substrate change: the leftward blanking walk stops at the existing
  @{text le} (LE discipline clause 1) and writes no fresh @{text le}.

  This section introduces the tape transposition, the boundary-parameterised
  encoder families, and the transposed run relation — purely additive
  definitions over the base wrap types above; they are assembled into the
  plant-\<open>le\<close> combinator \<open>wrap_delta\<close> downstream.\<close>


subsection \<open>The tape transposition\<close>

text \<open>@{text wrap_tau} swaps tape indices @{text 0} and @{text 1} and fixes
  every other index.  It is the involution that places M's tape @{text 0}
  (the encoded input) on physical tape @{text 1} and M's tape @{text 1} (the
  reused input tape) on physical tape @{text 0}.\<close>

definition wrap_tau :: "nat \<Rightarrow> nat" where
  "wrap_tau p =
     (case p of 0 \<Rightarrow> Suc 0 | Suc 0 \<Rightarrow> 0 | Suc (Suc k) \<Rightarrow> Suc (Suc k))"

lemma wrap_tau_0 [simp]: "wrap_tau 0 = Suc 0"
  by (simp add: wrap_tau_def)

lemma wrap_tau_1 [simp]: "wrap_tau (Suc 0) = 0"
  by (simp add: wrap_tau_def)

lemma wrap_tau_ge2 [simp]: "wrap_tau (Suc (Suc k)) = Suc (Suc k)"
  by (simp add: wrap_tau_def)

lemma wrap_tau_invol [simp]: "wrap_tau (wrap_tau p) = p"
  by (cases p; simp; rename_tac n, case_tac n; simp)

lemma wrap_tau_ge2_id: "2 \<le> p \<Longrightarrow> wrap_tau p = p"
  by (cases p; simp; rename_tac n, case_tac n; simp)

lemma wrap_tau_lt2: "wrap_tau p < 2 \<longleftrightarrow> p < 2"
  by (cases p; simp; rename_tac n, case_tac n; simp)


subsection \<open>Boundary-parameterised encoder families\<close>

text \<open>The six encoder phase families, generalised over the in-range tape
  boundary @{term K} and instantiated below at the faithful tape count
  @{term "K = k_tm M"}.  Each read / write / head action addresses only
  physical tapes @{text 0} and @{text 1}; @{term K} marks the boundary above
  which tapes are out of range and blank.  Stating the families over the
  boundary @{term K} keeps the encoder-correctness lemmas independent of the
  exact tape count.\<close>

definition wrap_init_delta_gen ::
  "nat \<Rightarrow> ('q, 'b) mttm
   \<Rightarrow> (('q, 'a, 'b) wrap_state
       \<times> (nat \<Rightarrow> ('a, 'b) wrap_alphabet)
       \<times> ('q, 'a, 'b) wrap_state
       \<times> (nat \<Rightarrow> ('a, 'b) wrap_alphabet)
       \<times> (nat \<Rightarrow> dir)) set"
where
  "wrap_init_delta_gen K M =
     { (W_Init,
        \<lambda>t. if t < K then Enc (le_tm M) else Enc (bl_tm M),
        W_Buf [],
        \<lambda>t. if t < K then Enc (le_tm M) else Enc (bl_tm M),
        \<lambda>t. case t of 0 \<Rightarrow> dir.R
                    | Suc k \<Rightarrow> (if k = 0 then dir.R else dir.N)) }"

definition wrap_buf_extend_delta_gen ::
  "nat \<Rightarrow> ('q, 'b) mttm \<Rightarrow> nat \<Rightarrow> 'a set
   \<Rightarrow> (('q, 'a, 'b) wrap_state
       \<times> (nat \<Rightarrow> ('a, 'b) wrap_alphabet)
       \<times> ('q, 'a, 'b) wrap_state
       \<times> (nat \<Rightarrow> ('a, 'b) wrap_alphabet)
       \<times> (nat \<Rightarrow> dir)) set"
where
  "wrap_buf_extend_delta_gen K M c \<Sigma>u =
     { (W_Buf ws, sym, W_Buf (ws @ [a]), sym,
        \<lambda>t. case t of 0 \<Rightarrow> dir.R | _ \<Rightarrow> dir.N)
       | ws a sym.
           length ws + 1 < c \<and> a \<in> \<Sigma>u \<and> set ws \<subseteq> \<Sigma>u
           \<and> sym 0 = Raw a
           \<and> (\<forall>j\<ge>K. sym j = Enc (bl_tm M))
           \<and> sym \<in> UNIV \<rightarrow> Raw ` \<Sigma>u \<union> Enc ` \<Gamma>_tm M }"

definition wrap_buf_close_delta_gen ::
  "nat \<Rightarrow> ('q, 'b) mttm \<Rightarrow> ('a list \<Rightarrow> 'b) \<Rightarrow> nat \<Rightarrow> 'a set
   \<Rightarrow> (('q, 'a, 'b) wrap_state
       \<times> (nat \<Rightarrow> ('a, 'b) wrap_alphabet)
       \<times> ('q, 'a, 'b) wrap_state
       \<times> (nat \<Rightarrow> ('a, 'b) wrap_alphabet)
       \<times> (nat \<Rightarrow> dir)) set"
where
  "wrap_buf_close_delta_gen K M pack c \<Sigma>u =
     { (W_Buf ws, sym, W_Buf [],
        (\<lambda>t. case t of Suc k \<Rightarrow> (if k = 0 then Enc (pack (ws @ [a]))
                                else sym (Suc k))
                     | 0 \<Rightarrow> sym 0),
        \<lambda>t. case t of 0 \<Rightarrow> dir.R
                    | Suc k \<Rightarrow> (if k = 0 then dir.R else dir.N))
       | ws a sym.
           length ws + 1 = c \<and> a \<in> \<Sigma>u \<and> set ws \<subseteq> \<Sigma>u
           \<and> sym 0 = Raw a
           \<and> sym (Suc 0) \<noteq> Enc (le_tm M)
           \<and> pack (ws @ [a]) \<in> Sigma_tm M
           \<and> (\<forall>j\<ge>K. sym j = Enc (bl_tm M))
           \<and> sym \<in> UNIV \<rightarrow> Raw ` \<Sigma>u \<union> Enc ` \<Gamma>_tm M }"

definition wrap_buf_empty_end_delta_gen ::
  "nat \<Rightarrow> ('q, 'b) mttm \<Rightarrow> 'a set
   \<Rightarrow> (('q, 'a, 'b) wrap_state
       \<times> (nat \<Rightarrow> ('a, 'b) wrap_alphabet)
       \<times> ('q, 'a, 'b) wrap_state
       \<times> (nat \<Rightarrow> ('a, 'b) wrap_alphabet)
       \<times> (nat \<Rightarrow> dir)) set"
where
  "wrap_buf_empty_end_delta_gen K M \<Sigma>u =
     { (W_Buf [], sym, W_Reset, sym, \<lambda>_. dir.N)
       | sym.
           sym 0 = Enc (bl_tm M)
           \<and> (\<forall>j\<ge>K. sym j = Enc (bl_tm M))
           \<and> sym \<in> UNIV \<rightarrow> Raw ` \<Sigma>u \<union> Enc ` \<Gamma>_tm M }"

definition wrap_buf_nonempty_end_delta_gen ::
  "nat \<Rightarrow> ('q, 'b) mttm \<Rightarrow> ('a list \<Rightarrow> 'b) \<Rightarrow> nat \<Rightarrow> 'a set
   \<Rightarrow> (('q, 'a, 'b) wrap_state
       \<times> (nat \<Rightarrow> ('a, 'b) wrap_alphabet)
       \<times> ('q, 'a, 'b) wrap_state
       \<times> (nat \<Rightarrow> ('a, 'b) wrap_alphabet)
       \<times> (nat \<Rightarrow> dir)) set"
where
  "wrap_buf_nonempty_end_delta_gen K M pack c \<Sigma>u =
     { (W_Buf ws, sym, W_Reset,
        (\<lambda>t. case t of Suc k \<Rightarrow> (if k = 0 then Enc (pack ws)
                                else sym (Suc k))
                     | 0 \<Rightarrow> sym 0),
        \<lambda>t. case t of Suc k \<Rightarrow> (if k = 0 then dir.R else dir.N)
                    | 0 \<Rightarrow> dir.N)
       | ws sym.
           ws \<noteq> [] \<and> length ws < c \<and> set ws \<subseteq> \<Sigma>u
           \<and> sym 0 = Enc (bl_tm M)
           \<and> sym (Suc 0) \<noteq> Enc (le_tm M)
           \<and> pack ws \<in> Sigma_tm M
           \<and> (\<forall>j\<ge>K. sym j = Enc (bl_tm M))
           \<and> sym \<in> UNIV \<rightarrow> Raw ` \<Sigma>u \<union> Enc ` \<Gamma>_tm M }"

definition wrap_disp_delta_gen ::
  "nat \<Rightarrow> ('q, 'b) mttm \<Rightarrow> 'a set
   \<Rightarrow> (('q, 'a, 'b) wrap_state
       \<times> (nat \<Rightarrow> ('a, 'b) wrap_alphabet)
       \<times> ('q, 'a, 'b) wrap_state
       \<times> (nat \<Rightarrow> ('a, 'b) wrap_alphabet)
       \<times> (nat \<Rightarrow> dir)) set"
where
  "wrap_disp_delta_gen K M \<Sigma>u =
     { (W_Disp, sym, W_Run (s_tm M), sym, \<lambda>_. dir.N)
       | sym.
           (\<forall>j\<ge>K. sym j = Enc (bl_tm M))
           \<and> sym \<in> UNIV \<rightarrow> Raw ` \<Sigma>u \<union> Enc ` \<Gamma>_tm M }"


subsection \<open>Transposed run relation\<close>

text \<open>Phase 5, faithful form.  Each M-@{text \<delta>} entry
  @{text "(q, \<sigma>, q', \<sigma>', d)"} lifts so that physical tape @{text p} carries
  M's tape @{term "wrap_tau p"}: it is read as @{term "Enc (\<sigma> (wrap_tau p))"},
  written as @{term "Enc (\<sigma>' (wrap_tau p))"}, and moved by
  @{term "d (wrap_tau p)"}.  No physical tape is frozen as a leftover input
  tape: physical tape @{text 0} is M's tape @{text 1}, an ordinary work
  tape.\<close>

definition wrap_run_delta ::
  "('q, 'b) mttm \<Rightarrow> 'a set
   \<Rightarrow> (('q, 'a, 'b) wrap_state
       \<times> (nat \<Rightarrow> ('a, 'b) wrap_alphabet)
       \<times> ('q, 'a, 'b) wrap_state
       \<times> (nat \<Rightarrow> ('a, 'b) wrap_alphabet)
       \<times> (nat \<Rightarrow> dir)) set"
where
  "wrap_run_delta M \<Sigma>u =
     { (W_Run q, sym, W_Run q',
        (\<lambda>p. Enc (\<sigma>' (wrap_tau p))),
        (\<lambda>p. d (wrap_tau p)))
       | q \<sigma> q' \<sigma>' d sym.
           (q, \<sigma>, q', \<sigma>', d) \<in> delta_tm M
           \<and> (\<forall>p. sym p = Enc (\<sigma> (wrap_tau p)))
           \<and> sym \<in> UNIV \<rightarrow> Raw ` \<Sigma>u \<union> Enc ` \<Gamma>_tm M }"

section \<open>Faithful (k-tape) encoding wrap: encoder-phase threading\<close>

text \<open>The boundary-parameterised encoder configurations that the six encoder
  families thread through.  The families address only
  physical tape @{text 0} (reading the raw input) and physical tape @{text 1}
  (receiving the encoded input); the in-range boundary @{term "k_tm M"} fixes
  the content of every tape from index @{term "k_tm M"} up (out of range,
  blank).  The encoder never touches those tapes, so the config-threading
  lemmas are stated generically over the boundary @{term K} and specialised
  at @{term "K = k_tm M"}.

  The threading reuses the boundary-\<^emph>\<open>independent\<close> @{const wrap_enc}
  lemmas (@{thm[source] length_wrap_enc}, @{thm[source] wrap_enc_nth},
  @{thm[source] wrap_enc_in_Gamma}, \<open>\<dots>\<close>); the three encoder
  configurations defined below are parameterised by the in-range boundary
  @{term K}.\<close>


subsection \<open>Boundary-parameterised encoder configurations\<close>

text \<open>The post-encoder waypoint: the encoder has finished, state @{text W_Reset},
  physical tape @{text 0} still holding the raw input, physical tape @{text 1}
  holding the full @{const wrap_enc} encoding, both heads at the right end.
  Generalised over the in-range boundary @{term K}, specialised below at the
  faithful instance @{term "K = k_tm M"}.\<close>

definition post_encoder_config_gen ::
  "nat \<Rightarrow> ('q, 'b) mttm \<Rightarrow> ('a list \<Rightarrow> 'b) \<Rightarrow> nat \<Rightarrow> 'a list
   \<Rightarrow> (('a, 'b) wrap_alphabet, ('q, 'a, 'b) wrap_state) mt_config"
where
  "post_encoder_config_gen K M pack c w =
     Config\<^sub>M W_Reset
       (\<lambda>t n. if t < K
              then (case t of
                0 \<Rightarrow> (if n = 0 then Enc (le_tm M)
                          else if n \<le> length w then Raw (w ! (n - 1))
                          else Enc (bl_tm M))
              | Suc k \<Rightarrow> (if n = 0 then Enc (le_tm M)
                          else if k = 0 \<and> n \<le> length (wrap_enc pack c w)
                            then Enc (wrap_enc pack c w ! (n - 1))
                          else Enc (bl_tm M)))
              else Enc (bl_tm M))
       (\<lambda>t. case t of
              0 \<Rightarrow> length w + 1
            | Suc k \<Rightarrow> (if k = 0 then 1 + length (wrap_enc pack c w) else 0))"

text \<open>Intermediate encoder configuration after @{term i} complete block
  cycles: state @{text "W_Buf []"}, physical tape @{text 1} holding the first
  @{term i} encoded blocks at positions @{text "1..i"} with head at
  @{text "1 + i"}, physical tape @{text 0} head at @{text "1 + i * c"}.\<close>

definition mid_encoder_config_gen ::
  "nat \<Rightarrow> ('q, 'b) mttm \<Rightarrow> ('a list \<Rightarrow> 'b) \<Rightarrow> nat \<Rightarrow> 'a list \<Rightarrow> nat
   \<Rightarrow> (('a, 'b) wrap_alphabet, ('q, 'a, 'b) wrap_state) mt_config"
where
  "mid_encoder_config_gen K M pack c w i =
     Config\<^sub>M (W_Buf [])
       (\<lambda>t n. if t < K
              then (case t of
                0 \<Rightarrow> (if n = 0 then Enc (le_tm M)
                          else if n \<le> length w then Raw (w ! (n - 1))
                          else Enc (bl_tm M))
              | Suc k \<Rightarrow> (if n = 0 then Enc (le_tm M)
                          else if k = 0 \<and> n \<le> i
                            then Enc (wrap_enc pack c w ! (n - 1))
                          else Enc (bl_tm M)))
              else Enc (bl_tm M))
       (\<lambda>t. case t of
              0 \<Rightarrow> 1 + i * c
            | Suc k \<Rightarrow> (if k = 0 then 1 + i else 0))"

text \<open>Finer-grained intermediate inside the @{term i}-th cycle, with @{term j}
  input symbols already accumulated in the buffer (@{text "0 \<le> j \<le> c - 1"}).\<close>

definition mid_buf_extending_config_gen ::
  "nat \<Rightarrow> ('q, 'b) mttm \<Rightarrow> ('a list \<Rightarrow> 'b) \<Rightarrow> nat \<Rightarrow> 'a list
   \<Rightarrow> nat \<Rightarrow> nat
   \<Rightarrow> (('a, 'b) wrap_alphabet, ('q, 'a, 'b) wrap_state) mt_config"
where
  "mid_buf_extending_config_gen K M pack c w i j =
     Config\<^sub>M (W_Buf (take j (drop (i * c) w)))
       (\<lambda>t n. if t < K
              then (case t of
                0 \<Rightarrow> (if n = 0 then Enc (le_tm M)
                          else if n \<le> length w then Raw (w ! (n - 1))
                          else Enc (bl_tm M))
              | Suc k \<Rightarrow> (if n = 0 then Enc (le_tm M)
                          else if k = 0 \<and> n \<le> i
                            then Enc (wrap_enc pack c w ! (n - 1))
                          else Enc (bl_tm M)))
              else Enc (bl_tm M))
       (\<lambda>t. case t of
              0 \<Rightarrow> 1 + i * c + j
            | Suc k \<Rightarrow> (if k = 0 then 1 + i else 0))"

section \<open>Faithful (k-tape) encoding wrap: combined reset and dispatch\<close>

text \<open>After the encoder phase the faithful wrap is at
  @{const post_encoder_config_gen}: physical tape @{text 0} still holds the raw
  input (the spent input tape), physical tape @{text 1} holds the encoded input,
  both heads parked at the right end.  The \<^emph>\<open>combined reset\<close> walks both heads
  left at once — blanking physical tape @{text 0} (which becomes M's blank work
  tape @{text 1}) while \<^emph>\<open>preserving\<close> physical tape @{text 1}'s encoded content
  — each head halting at its own @{text le}; when both read @{text le} the
  dispatch fires (@{text "W_Reset \<rightarrow> W_Disp \<rightarrow> W_Run (s_tm M)"}).  The
  resulting configuration is the @{text \<tau>}-lift of M's initial configuration on
  the encoded input.

  Physical tape @{text 0}'s content evolves with its head as it is blanked,
  and the two heads walk at different speeds: the encoded tape is no longer
  than the input tape, so its head reaches @{text le} first and then sits
  there while the input tape finishes blanking.\<close>


subsection \<open>The \<open>\<tau>\<close>-lift of an M-configuration\<close>

text \<open>Physical tape @{text p} carries M's tape @{term "wrap_tau p"}, encoded.
  No frozen input tape: every physical tape is an @{const Enc}-image of an
  M-tape, so the lift needs no @{text "pack / c / w"} parameters.\<close>

definition lift_M_config ::
  "('q, 'b) mttm \<Rightarrow> ('b, 'q) mt_config
   \<Rightarrow> (('a, 'b) wrap_alphabet, ('q, 'a, 'b) wrap_state) mt_config"
where
  "lift_M_config M cM =
     Config\<^sub>M (W_Run (mt_state cM))
       (\<lambda>p n. if p < k_tm M then Enc (mt_tape cM (wrap_tau p) n)
              else Enc (bl_tm M))
       (\<lambda>p. mt_pos cM (wrap_tau p))"


subsection \<open>The combined reset configuration\<close>

text \<open>State @{text W_Reset}; physical tape @{text 0} head at @{term m0} with the
  raw input blanked above it (cells @{text "> m0"} are @{text bl}); physical
  tape @{text 1} head at @{term m1} with the encoded input preserved; tapes
  @{text "2 \<dots> K-1"} untouched.  Parameterised by the in-range boundary
  @{term K} and the two head positions.\<close>

definition mid_reset_combined_config_gen ::
  "nat \<Rightarrow> ('q, 'b) mttm \<Rightarrow> ('a list \<Rightarrow> 'b) \<Rightarrow> nat \<Rightarrow> 'a list \<Rightarrow> nat \<Rightarrow> nat
   \<Rightarrow> (('a, 'b) wrap_alphabet, ('q, 'a, 'b) wrap_state) mt_config"
where
  "mid_reset_combined_config_gen K M pack c w m0 m1 =
     Config\<^sub>M W_Reset
       (\<lambda>t n. if t < K
              then (case t of
                0 \<Rightarrow> (if n = 0 then Enc (le_tm M)
                          else if n \<le> m0 \<and> n \<le> length w then Raw (w ! (n - 1))
                          else Enc (bl_tm M))
              | Suc k \<Rightarrow> (if n = 0 then Enc (le_tm M)
                          else if k = 0 \<and> n \<le> length (wrap_enc pack c w)
                            then Enc (wrap_enc pack c w ! (n - 1))
                          else Enc (bl_tm M)))
              else Enc (bl_tm M))
       (\<lambda>t. case t of
              0 \<Rightarrow> m0
            | Suc k \<Rightarrow> (if k = 0 then m1 else 0))"

text \<open>Boundary identity: @{const post_encoder_config_gen} is the top of the
  combined reset — physical tape @{text 0} head at @{term "length w + 1"} (no
  cell blanked yet, since @{term "n \<le> length w + 1 \<and> n \<le> length w"} collapses
  to @{term "n \<le> length w"}), physical tape @{text 1} head at
  @{term "1 + length (wrap_enc pack c w)"}.\<close>

lemma post_encoder_eq_mid_reset_combined_top:
  "post_encoder_config_gen K M pack c w
     = mid_reset_combined_config_gen K M pack c w
         (length w + 1) (Suc (length (wrap_enc pack c w)))"
  unfolding post_encoder_config_gen_def mid_reset_combined_config_gen_def
  by (simp add: fun_eq_iff split: nat.split)

end
