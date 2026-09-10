theory AlphabetRoundtrip
  imports
    "Multitape_Alphabet_Enlargement.AlphabetEnlargement_Reverse"
    "Multitape_Alphabet_Reduction.AlphabetReduction_Reverse"
begin

section \<open>Round-trip composition of the alphabet transformations\<close>

text \<open>The two alphabet transformations compose \<^emph>\<open>as machines\<close> in both
  orders on the shared substrate.  This theory states, for each order,
  language preservation and a composed linear-time slowdown bound.  Nothing
  is re-proved: each headline chains the language / time theorems of
  \<^const>\<open>alphabet_enlarge\<close> and \<^const>\<open>alphabet_reduce\<close> already established
  in the two sibling sessions.

  Two directions:
  \<^item> \<^bold>\<open>reduce after enlarge\<close>: \<^term>\<open>alphabet_reduce (alphabet_enlarge M)\<close>.
    The enlarged machine feeds \<^const>\<open>alphabet_reduce\<close>; the four-symbol lower
    bound its hypotheses require follows from the constant-cell embedding of
    the source alphabet into the block alphabet (\<open>card_gamma_block_ge_card\<close>).
  \<^item> \<^bold>\<open>enlarge after reduce\<close>: \<^term>\<open>alphabet_enlarge (alphabet_reduce M)\<close>.
    The reduced machine is well-formed for \<^emph>\<open>any\<close> valid source with a
    four-symbol alphabet (\<open>alphabet_reduce_well_formed\<close>), which discharges the
    \<^const>\<open>well_formed_mttm\<close> hypothesis \<^const>\<open>alphabet_enlarge\<close> requires of its
    input -- the cut-tolerance payoff.\<close>

subsection \<open>The enlarged alphabet has at least as many symbols as the source\<close>

text \<open>The block alphabet \<^term>\<open>gamma_block \<Gamma>\<close> contains the constant
  blocks \<^term>\<open>\<lambda>_. a\<close> for every \<^term>\<open>a \<in> \<Gamma>\<close>, and the embedding sending
  \<open>a\<close> to that constant cell is injective (the index type is inhabited).  Hence
  the enlarged alphabet is at least as large as the source, so a source with
  \<^term>\<open>4 \<le> card \<Gamma>\<close> enlarges to a machine whose alphabet still meets the
  reduction combinator's minimal-alphabet bound.\<close>

lemma card_gamma_block_ge_card:
  fixes \<Gamma> :: "'a set"
  assumes finG: "finite \<Gamma>"
  shows "card \<Gamma> \<le> card (gamma_block \<Gamma> :: (('c :: enum) \<Rightarrow> 'a) set)"
proof -
  have inj: "inj_on (\<lambda>a. (\<lambda>_::'c. a)) \<Gamma>"
    by (rule inj_onI) (metis fun_cong)
  have img: "(\<lambda>a. (\<lambda>_::'c. a)) ` \<Gamma> \<subseteq> gamma_block \<Gamma>"
    by (auto simp: gamma_block_def)
  have "card \<Gamma> = card ((\<lambda>a. (\<lambda>_::'c. a)) ` \<Gamma>)"
    by (simp add: card_image[OF inj])
  also have "\<dots> \<le> card (gamma_block \<Gamma> :: ('c \<Rightarrow> 'a) set)"
    by (rule card_mono[OF finite_gamma_block[OF finG] img])
  finally show ?thesis .
qed

subsection \<open>Time-composition preliminaries\<close>

text \<open>A small fact used when composing the running-time bounds: the block
  count \<open>(n + c - 1) div c\<close> (rounding \<open>n / c\<close> up) that the enlargement
  bound divides by never exceeds \<open>n\<close> for a nonempty index (\<open>0 < c\<close>).  (Weak
  acceptance monotonicity, formerly local here, is now the substrate's
  \<open>accepts_in_time_mttm_mono\<close>.)\<close>

lemma ceil_div_le:
  fixes n c :: nat
  assumes cpos: "0 < c"
  shows "(n + c - 1) div c \<le> n"
proof (cases "n = 0")
  case True
  from cpos obtain m where cm: "c = Suc m" using gr0_implies_Suc by blast
  have "c - 1 < c" using cm by simp
  hence "(c - 1) div c = 0" by (rule div_less)
  thus ?thesis using True by simp
next
  case False
  then have n1: "1 \<le> n" by simp
  have cnz: "c \<noteq> 0" using cpos by simp
  have eq: "n + c - 1 = (n - 1) + c" using n1 by simp
  have "(n + c - 1) div c = (n - 1) div c + 1"
    unfolding eq by (rule div_add_self2[OF cnz])
  also have "\<dots> \<le> (n - 1) + 1"
    using div_le_dividend[of "n - 1" c] by simp
  also have "\<dots> = n" using n1 by simp
  finally show ?thesis .
qed

subsection \<open>Enlarge after reduce\<close>

text \<open>Reduce \<open>M\<close> to the four-symbol machine \<^term>\<open>alphabet_reduce M\<close>, then
  enlarge that.  Language preservation chains the two headline biconditionals:
  \<open>alphabet_reduce_language\<close> (from \<open>M\<close> to the reduced machine, under the
  per-symbol encoding \<^const>\<open>encode_input_ar\<close>) and \<open>alphabet_enlarge_language\<close>
  (from the reduced machine to its enlargement, under the block encoding
  \<^const>\<open>encode_input\<close>).  Two seams are discharged locally: the reduced machine
  is well-formed for any valid four-symbol source
  (\<open>alphabet_reduce_well_formed\<close>, the input hypothesis
  \<^const>\<open>alphabet_enlarge\<close> requires), and the encoded intermediate word lies in
  the reduced machine's input alphabet \<^term>\<open>{BIT0, BIT1}\<close>
  (\<open>set_encode_input_ar\<close>).\<close>

theorem alphabet_reduce_enlarge_language:
  fixes M :: "('q, 'a) mttm"
  assumes vM: "valid_mttm M"
      and s_neq_t: "s_tm M \<noteq> t_tm M"
      and s_neq_r: "s_tm M \<noteq> r_tm M"
      and le_neq_bl: "le_tm M \<noteq> bl_tm M"
      and card_ge: "card (\<Gamma>_tm M) \<ge> 4"
  shows "\<forall>w. set w \<subseteq> Sigma_tm M \<longrightarrow>
           (encode_input (bl_tm (alphabet_reduce M))
                (encode_input_ar (\<Gamma>_tm M) (bl_tm M) w)
              \<in> Lang_mttm (alphabet_enlarge (alphabet_reduce M)
                   :: ((('q \<times> 'a ar_stage) \<times> (sym4, 'c :: enum) ae_stage),
                       'c \<Rightarrow> sym4) mttm))
           = (w \<in> Lang_mttm M)"
proof (intro allI impI)
  fix w assume w: "set w \<subseteq> Sigma_tm M"
  let ?Mr = "alphabet_reduce M :: ('q \<times> 'a ar_stage, sym4) mttm"
  let ?enc = "encode_input_ar (\<Gamma>_tm M) (bl_tm M) w"
  have wfr: "well_formed_mttm ?Mr"
    by (rule alphabet_reduce_well_formed[OF vM card_ge])
  have red: "(?enc \<in> Lang_mttm ?Mr) = (w \<in> Lang_mttm M)"
    using alphabet_reduce_language[OF vM s_neq_t s_neq_r le_neq_bl card_ge] w
    by blast
  have guard: "set ?enc \<subseteq> Sigma_tm ?Mr"
    using set_encode_input_ar[of "\<Gamma>_tm M" "bl_tm M" w]
    by (simp add: alphabet_reduce_Sigma)
  have enl: "(encode_input (bl_tm ?Mr) ?enc
                \<in> Lang_mttm (alphabet_enlarge ?Mr
                     :: ((('q \<times> 'a ar_stage) \<times> (sym4, 'c) ae_stage),
                         'c \<Rightarrow> sym4) mttm))
             = (?enc \<in> Lang_mttm ?Mr)"
    using alphabet_enlarge_language[OF wfr] guard by blast
  show "(encode_input (bl_tm ?Mr) ?enc
            \<in> Lang_mttm (alphabet_enlarge ?Mr
                 :: ((('q \<times> 'a ar_stage) \<times> (sym4, 'c) ae_stage),
                     'c \<Rightarrow> sym4) mttm))
        = (w \<in> Lang_mttm M)"
    using enl red by simp
qed

text \<open>The composed slowdown, with explicit constants.  Reducing then
  enlarging is linear-time, with the affine bound
  \<open>8 \<cdot> (6 \<cdot> k_tm M + 1) \<cdot> b \<cdot> T(|w|) + 2 \<cdot> b \<cdot> |w| + 4\<close>, where
  \<open>b = block_width (\<Gamma>_tm M)\<close> is the per-symbol binary width and \<open>k_tm M\<close> the tape
  count.  It routes the explicit reduction bound
  (\<open>(6 \<cdot> k_tm M + 1) \<cdot> b \<cdot> T\<close>, \<open>alphabet_reduce_time_explicit\<close>) in as the
  enlargement's per-input running-time function \<open>Tr\<close>; on the encoded
  intermediate word (length \<open>b \<cdot> |w|\<close>) the enlargement hypothesis holds
  \<^emph>\<open>exactly\<close> (\<open>Tr (b \<cdot> |w|) = (6 \<cdot> k_tm M + 1) \<cdot> b \<cdot> T(|w|)\<close>), and the
  enlargement's ceiling divisions are relaxed by \<open>ceil_div_le\<close> and
  \<open>accepts_in_time_mttm_mono\<close>.  The enlargement's block-speedup divisor
  \<open>c = card (UNIV :: 'c set)\<close> \<^emph>\<open>cancels\<close>: it divides the intermediate length
  and running time, but \<open>ceil_div_le\<close> discards it in the relaxation, so it
  does not appear in the bound --- the block speedup buys nothing once the
  reduction has fixed the alphabet.  The classical existential form is
  \<open>alphabet_reduce_enlarge_time\<close> below.\<close>

theorem alphabet_reduce_enlarge_time_explicit:
  fixes M :: "('q, 'a) mttm" and T :: "nat \<Rightarrow> nat"
  assumes vM: "valid_mttm M"
      and s_neq_t: "s_tm M \<noteq> t_tm M"
      and s_neq_r: "s_tm M \<noteq> r_tm M"
      and le_neq_bl: "le_tm M \<noteq> bl_tm M"
      and card_ge: "card (\<Gamma>_tm M) \<ge> 4"
  shows "\<forall>w. set w \<subseteq> Sigma_tm M \<longrightarrow>
           accepts_in_time_mttm M w (T (length w)) \<longrightarrow>
           accepts_in_time_mttm
             (alphabet_enlarge (alphabet_reduce M)
                :: ((('q \<times> 'a ar_stage) \<times> (sym4, 'c :: enum) ae_stage),
                    'c \<Rightarrow> sym4) mttm)
             (encode_input (bl_tm (alphabet_reduce M))
                (encode_input_ar (\<Gamma>_tm M) (bl_tm M) w))
             (8 * (6 * k_tm M + 1) * block_width (\<Gamma>_tm M) * T (length w)
               + 2 * block_width (\<Gamma>_tm M) * length w + 4)"
proof -
  let ?Mr = "alphabet_reduce M :: ('q \<times> 'a ar_stage, sym4) mttm"
  let ?Me = "alphabet_enlarge ?Mr
               :: ((('q \<times> 'a ar_stage) \<times> (sym4, 'c :: enum) ae_stage),
                   'c \<Rightarrow> sym4) mttm"
  let ?kf = "block_width (\<Gamma>_tm M)"
  let ?c = "card (UNIV :: 'c set)"
  let ?d = "6 * k_tm M + 1"
  have wfr: "well_formed_mttm ?Mr" by (rule alphabet_reduce_well_formed[OF vM card_ge])
  have kfpos: "0 < ?kf" using block_width_pos[of "\<Gamma>_tm M"] by simp
  have cpos: "0 < ?c" by (simp add: card_gt_0_iff)
  have ar: "\<forall>w. set w \<subseteq> Sigma_tm M \<longrightarrow>
               accepts_in_time_mttm M w (T (length w)) \<longrightarrow>
               accepts_in_time_mttm ?Mr (encode_input_ar (\<Gamma>_tm M) (bl_tm M) w)
                 (?d * ?kf * T (length w))"
    by (rule alphabet_reduce_time_explicit[OF vM s_neq_t s_neq_r le_neq_bl card_ge])
  \<comment> \<open>route the reduction bound in as the enlargement's per-input time function\<close>
  define Tr :: "nat \<Rightarrow> nat" where "Tr = (\<lambda>n. ?d * ?kf * T (n div ?kf))"
  have ae: "\<forall>v. set v \<subseteq> Sigma_tm ?Mr \<longrightarrow>
        accepts_in_time_mttm ?Mr v (Tr (length v)) \<longrightarrow>
        accepts_in_time_mttm ?Me (encode_input (bl_tm ?Mr) v)
          (2 * ((length v + ?c - 1) div ?c)
            + 8 * ((Tr (length v) + ?c - 1) div ?c) + 4)"
    by (rule alphabet_enlarge_time_explicit[OF wfr, where T = Tr])
  show "\<forall>w. set w \<subseteq> Sigma_tm M \<longrightarrow>
        accepts_in_time_mttm M w (T (length w)) \<longrightarrow>
        accepts_in_time_mttm ?Me
          (encode_input (bl_tm ?Mr) (encode_input_ar (\<Gamma>_tm M) (bl_tm M) w))
          (8 * (6 * k_tm M + 1) * block_width (\<Gamma>_tm M) * T (length w)
            + 2 * block_width (\<Gamma>_tm M) * length w + 4)"
  proof (intro allI impI)
    fix w assume w: "set w \<subseteq> Sigma_tm M"
      and accM: "accepts_in_time_mttm M w (T (length w))"
    let ?v = "encode_input_ar (\<Gamma>_tm M) (bl_tm M) w"
    have lenv: "length ?v = ?kf * length w"
      by (simp add: length_encode_input_ar)
    have div_w: "length ?v div ?kf = length w"
      using lenv kfpos by simp
    have Tr_v: "Tr (length ?v) = ?d * ?kf * T (length w)"
      using div_w by (simp add: Tr_def)
    have accr: "accepts_in_time_mttm ?Mr ?v (Tr (length ?v))"
      using ar w accM Tr_v by simp
    have guard: "set ?v \<subseteq> Sigma_tm ?Mr"
      using set_encode_input_ar[of "\<Gamma>_tm M" "bl_tm M" w]
      by (simp add: alphabet_reduce_Sigma)
    have ae_acc: "accepts_in_time_mttm ?Me (encode_input (bl_tm ?Mr) ?v)
                    (2 * ((length ?v + ?c - 1) div ?c)
                      + 8 * ((Tr (length ?v) + ?c - 1) div ?c) + 4)"
      using ae guard accr by blast
    have bound_le:
      "2 * ((length ?v + ?c - 1) div ?c)
         + 8 * ((Tr (length ?v) + ?c - 1) div ?c) + 4
       \<le> 8 * ?d * ?kf * T (length w) + 2 * ?kf * length w + 4"
    proof -
      have h1: "(length ?v + ?c - 1) div ?c \<le> length ?v" by (rule ceil_div_le[OF cpos])
      have h2: "(Tr (length ?v) + ?c - 1) div ?c \<le> Tr (length ?v)" by (rule ceil_div_le[OF cpos])
      have "2 * ((length ?v + ?c - 1) div ?c)
              + 8 * ((Tr (length ?v) + ?c - 1) div ?c) + 4
            \<le> 2 * length ?v + 8 * Tr (length ?v) + 4"
        using h1 h2 by (simp add: add_mono mult_le_mono2)
      also have "\<dots> = 2 * (?kf * length w) + 8 * (?d * ?kf * T (length w)) + 4"
        using lenv Tr_v by simp
      also have "\<dots> = 8 * ?d * ?kf * T (length w) + 2 * ?kf * length w + 4"
        by (simp add: algebra_simps)
      finally show ?thesis .
    qed
    show "accepts_in_time_mttm ?Me
            (encode_input (bl_tm ?Mr) ?v)
            (8 * (6 * k_tm M + 1) * block_width (\<Gamma>_tm M) * T (length w)
              + 2 * block_width (\<Gamma>_tm M) * length w + 4)"
      by (rule accepts_in_time_mttm_mono[OF ae_acc bound_le])
  qed
qed

text \<open>The classical existential form \<open>A \<cdot> T(|w|) + B \<cdot> |w| + C\<close>, with
  \<open>A = 8 \<cdot> (6 \<cdot> k_tm M + 1) \<cdot> b\<close>,
  \<open>B = 2 \<cdot> b\<close>, and \<open>C = 4\<close> from
  \<open>alphabet_reduce_enlarge_time_explicit\<close>.\<close>

theorem alphabet_reduce_enlarge_time:
  fixes M :: "('q, 'a) mttm" and T :: "nat \<Rightarrow> nat"
  assumes vM: "valid_mttm M"
      and s_neq_t: "s_tm M \<noteq> t_tm M"
      and s_neq_r: "s_tm M \<noteq> r_tm M"
      and le_neq_bl: "le_tm M \<noteq> bl_tm M"
      and card_ge: "card (\<Gamma>_tm M) \<ge> 4"
  obtains A B C :: nat
  where "\<forall>w. set w \<subseteq> Sigma_tm M \<longrightarrow>
           accepts_in_time_mttm M w (T (length w)) \<longrightarrow>
           accepts_in_time_mttm
             (alphabet_enlarge (alphabet_reduce M)
                :: ((('q \<times> 'a ar_stage) \<times> (sym4, 'c :: enum) ae_stage),
                    'c \<Rightarrow> sym4) mttm)
             (encode_input (bl_tm (alphabet_reduce M))
                (encode_input_ar (\<Gamma>_tm M) (bl_tm M) w))
             (A * T (length w) + B * length w + C)"
proof (rule that[of "8 * (6 * k_tm M + 1) * block_width (\<Gamma>_tm M)"
                    "2 * block_width (\<Gamma>_tm M)" 4])
  show "\<forall>w. set w \<subseteq> Sigma_tm M \<longrightarrow>
           accepts_in_time_mttm M w (T (length w)) \<longrightarrow>
           accepts_in_time_mttm
             (alphabet_enlarge (alphabet_reduce M)
                :: ((('q \<times> 'a ar_stage) \<times> (sym4, 'c :: enum) ae_stage),
                    'c \<Rightarrow> sym4) mttm)
             (encode_input (bl_tm (alphabet_reduce M))
                (encode_input_ar (\<Gamma>_tm M) (bl_tm M) w))
             (8 * (6 * k_tm M + 1) * block_width (\<Gamma>_tm M) * T (length w)
               + 2 * block_width (\<Gamma>_tm M) * length w + 4)"
    by (rule alphabet_reduce_enlarge_time_explicit[OF vM s_neq_t s_neq_r le_neq_bl card_ge])
qed

subsection \<open>Reduce after enlarge\<close>

text \<open>Enlarge \<open>M\<close> to the block machine \<^term>\<open>alphabet_enlarge M\<close>, then reduce
  that back to four symbols.  This is the direction whose seams need the
  enlarged machine's own well-formedness data: its start / accept / reject
  states, blank and endmarker are the source ones tagged / block-encoded (the
  field accessors \<open>s_tm_alphabet_enlarge\<close> etc.), and its tape alphabet is the
  block alphabet \<^term>\<open>gamma_block (\<Gamma>_tm M)\<close>, whose cardinality is at least
  the source's (\<open>card_gamma_block_ge_card\<close>) --- so a four-symbol source stays
  above the reduction's minimal-alphabet bound.\<close>

lemma Gamma_tm_alphabet_enlarge:
  fixes M :: "('q, 'a) mttm"
  shows "\<Gamma>_tm (alphabet_enlarge M
                  :: ('q \<times> ('a, ('c :: enum)) ae_stage, 'c \<Rightarrow> 'a) mttm)
          = gamma_block (\<Gamma>_tm M)"
  by (cases M) (simp add: alphabet_enlarge_def)

text \<open>Enlargement preserves the tape count (the last \<open>mttm\<close> field is
  copied unchanged): the block transformation is purely alphabet-level, so the
  reduction's tape-count factor \<open>6 \<cdot> k_tm M + 1\<close> is the \<^emph>\<open>source\<close> tape count
  even when the reduction is applied to the enlarged machine.  Mirrors
  \<open>alphabet_reduce_preserves_tape_count\<close>.\<close>

lemma k_tm_alphabet_enlarge:
  fixes M :: "('q, 'a) mttm"
  shows "k_tm (alphabet_enlarge M
                  :: ('q \<times> ('a, ('c :: enum)) ae_stage, 'c \<Rightarrow> 'a) mttm)
          = k_tm M"
  by (cases M) (simp add: alphabet_enlarge_def)

text \<open>Discharge of the reduction's input hypotheses on the enlarged machine
  (validity, the three non-degeneracy conditions, and the four-symbol lower
  bound), packaged for reuse by both the language and the time theorem.\<close>

lemma alphabet_enlarge_reduce_hyps:
  fixes M :: "('q, 'a) mttm"
  assumes vM: "valid_mttm M"
      and s_neq_t: "s_tm M \<noteq> t_tm M"
      and s_neq_r: "s_tm M \<noteq> r_tm M"
      and le_neq_bl: "le_tm M \<noteq> bl_tm M"
      and card_ge: "card (\<Gamma>_tm M) \<ge> 4"
  shows "valid_mttm (alphabet_enlarge M
            :: ('q \<times> ('a, 'c :: enum) ae_stage, 'c \<Rightarrow> 'a) mttm)"
    and "s_tm (alphabet_enlarge M
            :: ('q \<times> ('a, 'c) ae_stage, 'c \<Rightarrow> 'a) mttm)
          \<noteq> t_tm (alphabet_enlarge M)"
    and "s_tm (alphabet_enlarge M
            :: ('q \<times> ('a, 'c) ae_stage, 'c \<Rightarrow> 'a) mttm)
          \<noteq> r_tm (alphabet_enlarge M)"
    and "le_tm (alphabet_enlarge M
            :: ('q \<times> ('a, 'c) ae_stage, 'c \<Rightarrow> 'a) mttm)
          \<noteq> bl_tm (alphabet_enlarge M)"
    and "card (\<Gamma>_tm (alphabet_enlarge M
            :: ('q \<times> ('a, 'c) ae_stage, 'c \<Rightarrow> 'a) mttm)) \<ge> 4"
proof -
  let ?M' = "alphabet_enlarge M :: ('q \<times> ('a, 'c) ae_stage, 'c \<Rightarrow> 'a) mttm"
  have finG: "finite (\<Gamma>_tm M)" by (rule valid_mttm_finite_Gamma[OF vM])
  show "valid_mttm ?M'" by (rule alphabet_enlarge_wf[OF vM])
  show "s_tm ?M' \<noteq> t_tm ?M'"
    using s_neq_t by (simp add: s_tm_alphabet_enlarge t_tm_alphabet_enlarge)
  show "s_tm ?M' \<noteq> r_tm ?M'"
    using s_neq_r by (simp add: s_tm_alphabet_enlarge r_tm_alphabet_enlarge)
  show "le_tm ?M' \<noteq> bl_tm ?M'"
  proof
    assume "le_tm ?M' = bl_tm ?M'"
    hence "(LE_block (le_tm M) :: 'c \<Rightarrow> 'a) = bl_block (bl_tm M)"
      by (simp add: le_tm_alphabet_enlarge bl_tm_alphabet_enlarge)
    hence "le_tm M = bl_tm M" by (rule LE_block_eq_bl_block_imp_eq)
    with le_neq_bl show False by simp
  qed
  have "card (\<Gamma>_tm M) \<le> card (gamma_block (\<Gamma>_tm M) :: ('c \<Rightarrow> 'a) set)"
    by (rule card_gamma_block_ge_card[OF finG])
  hence "4 \<le> card (gamma_block (\<Gamma>_tm M) :: ('c \<Rightarrow> 'a) set)"
    using card_ge by linarith
  thus "card (\<Gamma>_tm ?M') \<ge> 4" by (simp add: Gamma_tm_alphabet_enlarge)
qed

text \<open>The intermediate-word guard: the block encoding of a genuine input
  word lands in the enlarged machine's input alphabet (it is a block
  over the source, and avoids the two reserved blocks).  Shared by the
  language and time theorems of this direction.\<close>

lemma encode_input_in_Sigma_alphabet_enlarge:
  fixes M :: "('q, 'a) mttm"
  assumes vM: "valid_mttm M" and w: "set w \<subseteq> Sigma_tm M"
  shows "set (encode_input (bl_tm M) w :: ('c :: enum \<Rightarrow> 'a) list)
           \<subseteq> Sigma_tm (alphabet_enlarge M
                :: ('q \<times> ('a, 'c) ae_stage, 'c \<Rightarrow> 'a) mttm)"
proof -
  have "set (encode_input (bl_tm M) w :: ('c \<Rightarrow> 'a) list)
          \<subseteq> gamma_block (Sigma_tm M \<union> {bl_tm M})"
    by (rule encode_input_in_gamma_block[OF w])
  moreover have "bl_block (bl_tm M)
          \<notin> set (encode_input (bl_tm M) w :: ('c \<Rightarrow> 'a) list)"
    by (rule encode_input_no_bl_block[OF vM w])
  moreover have "LE_block (le_tm M)
          \<notin> set (encode_input (bl_tm M) w :: ('c \<Rightarrow> 'a) list)"
    by (rule encode_input_no_LE_block[OF vM w])
  ultimately show ?thesis by (auto simp: Sigma_tm_alphabet_enlarge)
qed

theorem alphabet_enlarge_reduce_language:
  fixes M :: "('q, 'a) mttm"
  assumes wfM: "well_formed_mttm M"
      and card_ge: "card (\<Gamma>_tm M) \<ge> 4"
  shows "\<forall>w. set w \<subseteq> Sigma_tm M \<longrightarrow>
           (encode_input_ar
               (\<Gamma>_tm (alphabet_enlarge M
                        :: ('q \<times> ('a, 'c :: enum) ae_stage, 'c \<Rightarrow> 'a) mttm))
               (bl_tm (alphabet_enlarge M))
               (encode_input (bl_tm M) w)
             \<in> Lang_mttm (alphabet_reduce (alphabet_enlarge M)
                  :: ((('q \<times> ('a, 'c) ae_stage) \<times> ('c \<Rightarrow> 'a) ar_stage), sym4) mttm))
           = (w \<in> Lang_mttm M)"
proof (intro allI impI)
  fix w assume w: "set w \<subseteq> Sigma_tm M"
  let ?M' = "alphabet_enlarge M :: ('q \<times> ('a, 'c) ae_stage, 'c \<Rightarrow> 'a) mttm"
  have vM: "valid_mttm M"
    and s_neq_t: "s_tm M \<noteq> t_tm M"
    and s_neq_r: "s_tm M \<noteq> r_tm M"
    and le_neq_bl: "le_tm M \<noteq> bl_tm M"
    using wfM by auto
  note hyps = alphabet_enlarge_reduce_hyps[OF vM s_neq_t s_neq_r le_neq_bl card_ge]
  have enl: "(encode_input (bl_tm M) w \<in> Lang_mttm ?M') = (w \<in> Lang_mttm M)"
    using alphabet_enlarge_language[OF wfM] w by blast
  have guard: "set (encode_input (bl_tm M) w :: ('c \<Rightarrow> 'a) list) \<subseteq> Sigma_tm ?M'"
    by (rule encode_input_in_Sigma_alphabet_enlarge[OF vM w])
  have red: "(encode_input_ar (\<Gamma>_tm ?M') (bl_tm ?M') (encode_input (bl_tm M) w)
                \<in> Lang_mttm (alphabet_reduce ?M'
                     :: ((('q \<times> ('a, 'c) ae_stage) \<times> ('c \<Rightarrow> 'a) ar_stage), sym4) mttm))
             = (encode_input (bl_tm M) w \<in> Lang_mttm ?M')"
    using alphabet_reduce_language[OF hyps(1) hyps(2) hyps(3) hyps(4) hyps(5)] guard
    by blast
  show "(encode_input_ar (\<Gamma>_tm ?M') (bl_tm ?M') (encode_input (bl_tm M) w)
            \<in> Lang_mttm (alphabet_reduce ?M'
                 :: ((('q \<times> ('a, 'c) ae_stage) \<times> ('c \<Rightarrow> 'a) ar_stage), sym4) mttm))
        = (w \<in> Lang_mttm M)"
    using red enl by simp
qed

text \<open>The composed slowdown for reduce-after-enlarge, with explicit
  constants.  Unlike the other order, the inner transformation (enlargement)
  \<^emph>\<open>speeds up\<close> by the block factor \<open>c = card (UNIV :: 'c set)\<close>, so the
  intermediate word has length \<open>\<lceil>|w| / c\<rceil>\<close> --- a lossy function of \<open>|w|\<close>,
  not an exact multiple --- and the enlarged machine's running time cannot be
  routed into the reduction's time function exactly.  Two mild ingredients
  close the gap: \<open>T\<close> is assumed non-decreasing (\<open>mono T\<close>), and the outer
  bound is stated at \<open>T(|w| + c - 1)\<close> --- \<open>T\<close> at the input length rounded up
  to the next block boundary.  The bound is
  \<open>8 \<cdot> D \<cdot> b' \<cdot> T(|w| + c - 1) + 2 \<cdot> D \<cdot> b' \<cdot> |w| + 4 \<cdot> D \<cdot> b'\<close>, where
  \<open>D = 6 \<cdot> k_tm M + 1\<close> (the tape count is preserved by enlargement,
  \<open>k_tm_alphabet_enlarge\<close>) and
  \<open>b' = block_width (\<Gamma>_tm (alphabet_enlarge M)) = block_width (gamma_block (\<Gamma>_tm M))\<close> is
  the per-symbol width of the \<^emph>\<open>block\<close> alphabet, i.e.
  \<open>\<lceil>c \<cdot> log\<^sub>2 (card \<Gamma>\<^sub>M)\<rceil>\<close>.  Because \<open>b'\<close> grows with \<open>c\<close>, the block-speedup
  factor \<^emph>\<open>does not\<close> cancel here: \<open>c\<close> survives both in the time argument
  \<open>T(|w| + c - 1)\<close> and, through \<open>b'\<close>, in every coefficient.  The classical
  existential form is \<open>alphabet_enlarge_reduce_time\<close> below.\<close>

theorem alphabet_enlarge_reduce_time_explicit:
  fixes M :: "('q, 'a) mttm" and T :: "nat \<Rightarrow> nat"
  assumes wfM: "well_formed_mttm M"
      and card_ge: "card (\<Gamma>_tm M) \<ge> 4"
      and Tmono: "mono T"
  shows "\<forall>w. set w \<subseteq> Sigma_tm M \<longrightarrow>
           accepts_in_time_mttm M w (T (length w)) \<longrightarrow>
           accepts_in_time_mttm
             (alphabet_reduce (alphabet_enlarge M)
                :: ((('q \<times> ('a, 'c :: enum) ae_stage) \<times> ('c \<Rightarrow> 'a) ar_stage), sym4) mttm)
             (encode_input_ar
                 (\<Gamma>_tm (alphabet_enlarge M :: ('q \<times> ('a, 'c) ae_stage, 'c \<Rightarrow> 'a) mttm))
                 (bl_tm (alphabet_enlarge M))
                 (encode_input (bl_tm M) w))
             (8 * (6 * k_tm M + 1)
                   * block_width (\<Gamma>_tm (alphabet_enlarge M
                        :: ('q \<times> ('a, 'c) ae_stage, 'c \<Rightarrow> 'a) mttm))
                   * T (length w + card (UNIV :: 'c set) - 1)
               + 2 * (6 * k_tm M + 1)
                   * block_width (\<Gamma>_tm (alphabet_enlarge M
                        :: ('q \<times> ('a, 'c) ae_stage, 'c \<Rightarrow> 'a) mttm))
                   * length w
               + 4 * (6 * k_tm M + 1)
                   * block_width (\<Gamma>_tm (alphabet_enlarge M
                        :: ('q \<times> ('a, 'c) ae_stage, 'c \<Rightarrow> 'a) mttm)))"
proof -
  let ?M' = "alphabet_enlarge M :: ('q \<times> ('a, 'c) ae_stage, 'c \<Rightarrow> 'a) mttm"
  let ?c = "card (UNIV :: 'c set)"
  let ?ke = "block_width (\<Gamma>_tm ?M')"
  let ?d = "6 * k_tm M + 1"
  have vM: "valid_mttm M"
    and s_neq_t: "s_tm M \<noteq> t_tm M"
    and s_neq_r: "s_tm M \<noteq> r_tm M"
    and le_neq_bl: "le_tm M \<noteq> bl_tm M"
    using wfM by auto
  have cpos: "0 < ?c" by (simp add: card_gt_0_iff)
  have ktm: "k_tm ?M' = k_tm M" by (rule k_tm_alphabet_enlarge)
  note hyps = alphabet_enlarge_reduce_hyps[OF vM s_neq_t s_neq_r le_neq_bl card_ge]
  \<comment> \<open>enlargement time constants (explicit: \<open>al = 2\<close>, \<open>fe = 4\<close>)\<close>
  have ae: "\<forall>w. set w \<subseteq> Sigma_tm M \<longrightarrow>
        accepts_in_time_mttm M w (T (length w)) \<longrightarrow>
        accepts_in_time_mttm ?M' (encode_input (bl_tm M) w)
          (2 * ((length w + ?c - 1) div ?c)
            + 8 * ((T (length w) + ?c - 1) div ?c) + 4)"
    by (rule alphabet_enlarge_time_explicit[OF wfM])
  \<comment> \<open>route the enlarged machine's running time in as the reduction's time function\<close>
  define Te :: "nat \<Rightarrow> nat" where "Te = (\<lambda>n. 8 * T (?c * n) + 2 * n + 4)"
  \<comment> \<open>reduction on the enlarged machine (explicit: \<open>e = fr = 0\<close>,
      \<open>d = 6 \<cdot> k_tm M + 1\<close> by tape preservation, \<open>b\<close> the block-alphabet width)\<close>
  have ar0: "\<forall>v. set v \<subseteq> Sigma_tm ?M' \<longrightarrow>
        accepts_in_time_mttm ?M' v (Te (length v)) \<longrightarrow>
        accepts_in_time_mttm (alphabet_reduce ?M'
            :: ((('q \<times> ('a, 'c) ae_stage) \<times> ('c \<Rightarrow> 'a) ar_stage), sym4) mttm)
          (encode_input_ar (\<Gamma>_tm ?M') (bl_tm ?M') v)
          ((6 * k_tm ?M' + 1) * ?ke * Te (length v))"
    by (rule alphabet_reduce_time_explicit[OF hyps(1) hyps(2) hyps(3) hyps(4) hyps(5)])
  have ar: "\<forall>v. set v \<subseteq> Sigma_tm ?M' \<longrightarrow>
        accepts_in_time_mttm ?M' v (Te (length v)) \<longrightarrow>
        accepts_in_time_mttm (alphabet_reduce ?M'
            :: ((('q \<times> ('a, 'c) ae_stage) \<times> ('c \<Rightarrow> 'a) ar_stage), sym4) mttm)
          (encode_input_ar (\<Gamma>_tm ?M') (bl_tm ?M') v)
          (?d * ?ke * Te (length v))"
    using ar0 by (simp add: ktm)
  show "\<forall>w. set w \<subseteq> Sigma_tm M \<longrightarrow>
        accepts_in_time_mttm M w (T (length w)) \<longrightarrow>
        accepts_in_time_mttm (alphabet_reduce ?M'
            :: ((('q \<times> ('a, 'c) ae_stage) \<times> ('c \<Rightarrow> 'a) ar_stage), sym4) mttm)
          (encode_input_ar (\<Gamma>_tm ?M') (bl_tm ?M') (encode_input (bl_tm M) w))
          (8 * ?d * ?ke * T (length w + ?c - 1)
            + 2 * ?d * ?ke * length w + 4 * ?d * ?ke)"
  proof (intro allI impI)
    fix w assume w: "set w \<subseteq> Sigma_tm M"
      and accM: "accepts_in_time_mttm M w (T (length w))"
    let ?v = "encode_input (bl_tm M) w :: ('c \<Rightarrow> 'a) list"
    have lenv: "length ?v = (length w + ?c - 1) div ?c"
      by (rule length_encode_input)
    have lv_le: "length ?v \<le> length w"
      using lenv ceil_div_le[OF cpos] by simp
    have cge: "length w \<le> ?c * length ?v"
    proof -
      have eq: "?c * ((length w + ?c - 1) div ?c) + (length w + ?c - 1) mod ?c
              = length w + ?c - 1"
        by (rule mult_div_mod_eq)
      have ml: "(length w + ?c - 1) mod ?c < ?c"
        using cpos by (rule mod_less_divisor)
      have "length w \<le> ?c * ((length w + ?c - 1) div ?c)"
        using eq ml cpos by linarith
      thus ?thesis by (simp add: lenv)
    qed
    have mcle: "?c * length ?v \<le> length w + ?c - 1"
    proof -
      have "?c * ((length w + ?c - 1) div ?c) \<le> length w + ?c - 1"
        by (metis mult_div_mod_eq le_add1)
      thus ?thesis using lenv by simp
    qed
    \<comment> \<open>enlargement: the enlarged machine accepts the block encoding\<close>
    have accAE: "accepts_in_time_mttm ?M' ?v
                   (2 * ((length w + ?c - 1) div ?c)
                     + 8 * ((T (length w) + ?c - 1) div ?c) + 4)"
      using ae w accM by blast
    \<comment> \<open>its bound is dominated by \<open>Te\<close> at the intermediate length\<close>
    have le1: "2 * ((length w + ?c - 1) div ?c)
                 + 8 * ((T (length w) + ?c - 1) div ?c) + 4
               \<le> Te (length ?v)"
    proof -
      have alv: "2 * ((length w + ?c - 1) div ?c) = 2 * length ?v"
        by (simp add: lenv)
      have tb: "8 * ((T (length w) + ?c - 1) div ?c) \<le> 8 * T (?c * length ?v)"
      proof -
        have "(T (length w) + ?c - 1) div ?c \<le> T (length w)"
          by (rule ceil_div_le[OF cpos])
        also have "\<dots> \<le> T (?c * length ?v)" using Tmono cge by (rule monoD)
        finally show ?thesis by (rule mult_le_mono2)
      qed
      have "2 * ((length w + ?c - 1) div ?c)
              + 8 * ((T (length w) + ?c - 1) div ?c) + 4
            = 2 * length ?v + 8 * ((T (length w) + ?c - 1) div ?c) + 4"
        by (simp only: alv)
      also have "\<dots> \<le> 2 * length ?v + 8 * T (?c * length ?v) + 4"
        using tb by simp
      also have "\<dots> = Te (length ?v)" by (simp add: Te_def)
      finally show ?thesis .
    qed
    have accr_hyp: "accepts_in_time_mttm ?M' ?v (Te (length ?v))"
      by (rule accepts_in_time_mttm_mono[OF accAE le1])
    have guard: "set ?v \<subseteq> Sigma_tm ?M'"
      by (rule encode_input_in_Sigma_alphabet_enlarge[OF vM w])
    have accAR: "accepts_in_time_mttm (alphabet_reduce ?M'
                    :: ((('q \<times> ('a, 'c) ae_stage) \<times> ('c \<Rightarrow> 'a) ar_stage), sym4) mttm)
                    (encode_input_ar (\<Gamma>_tm ?M') (bl_tm ?M') ?v)
                    (?d * ?ke * Te (length ?v))"
      using ar guard accr_hyp by blast
    have le2: "?d * ?ke * Te (length ?v)
                 \<le> 8 * ?d * ?ke * T (length w + ?c - 1)
                     + 2 * ?d * ?ke * length w + 4 * ?d * ?ke"
    proof -
      have T_le: "T (?c * length ?v) \<le> T (length w + ?c - 1)"
        using Tmono mcle by (simp add: monoD)
      have TeB: "Te (length ?v) \<le> 8 * T (length w + ?c - 1) + 2 * length w + 4"
        unfolding Te_def using T_le lv_le
        by (auto intro: add_mono mult_le_mono2)
      have "?d * ?ke * Te (length ?v)
              \<le> ?d * ?ke * (8 * T (length w + ?c - 1) + 2 * length w + 4)"
        using TeB by (rule mult_le_mono2)
      also have "\<dots> = 8 * ?d * ?ke * T (length w + ?c - 1)
                        + 2 * ?d * ?ke * length w + 4 * ?d * ?ke"
        by (simp add: algebra_simps)
      finally show ?thesis .
    qed
    show "accepts_in_time_mttm (alphabet_reduce ?M'
              :: ((('q \<times> ('a, 'c) ae_stage) \<times> ('c \<Rightarrow> 'a) ar_stage), sym4) mttm)
            (encode_input_ar (\<Gamma>_tm ?M') (bl_tm ?M') ?v)
            (8 * ?d * ?ke * T (length w + ?c - 1)
              + 2 * ?d * ?ke * length w + 4 * ?d * ?ke)"
      by (rule accepts_in_time_mttm_mono[OF accAR le2])
  qed
qed

text \<open>The classical existential form \<open>A \<cdot> T(|w| + c - 1) + B \<cdot> |w| + C\<close>,
  with \<open>A = 8 \<cdot> D \<cdot> b'\<close>, \<open>B = 2 \<cdot> D \<cdot> b'\<close>, \<open>C = 4 \<cdot> D \<cdot> b'\<close> for
  \<open>D = 6 \<cdot> k_tm M + 1\<close> and \<open>b' = block_width (\<Gamma>_tm (alphabet_enlarge M))\<close>, from
  \<open>alphabet_enlarge_reduce_time_explicit\<close>.\<close>

theorem alphabet_enlarge_reduce_time:
  fixes M :: "('q, 'a) mttm" and T :: "nat \<Rightarrow> nat"
  assumes wfM: "well_formed_mttm M"
      and card_ge: "card (\<Gamma>_tm M) \<ge> 4"
      and Tmono: "mono T"
  obtains A B C :: nat
  where "\<forall>w. set w \<subseteq> Sigma_tm M \<longrightarrow>
           accepts_in_time_mttm M w (T (length w)) \<longrightarrow>
           accepts_in_time_mttm
             (alphabet_reduce (alphabet_enlarge M)
                :: ((('q \<times> ('a, 'c :: enum) ae_stage) \<times> ('c \<Rightarrow> 'a) ar_stage), sym4) mttm)
             (encode_input_ar
                 (\<Gamma>_tm (alphabet_enlarge M :: ('q \<times> ('a, 'c) ae_stage, 'c \<Rightarrow> 'a) mttm))
                 (bl_tm (alphabet_enlarge M))
                 (encode_input (bl_tm M) w))
             (A * T (length w + card (UNIV :: 'c set) - 1) + B * length w + C)"
proof (rule that[of "8 * (6 * k_tm M + 1)
                       * block_width (\<Gamma>_tm (alphabet_enlarge M
                            :: ('q \<times> ('a, 'c) ae_stage, 'c \<Rightarrow> 'a) mttm))"
                    "2 * (6 * k_tm M + 1)
                       * block_width (\<Gamma>_tm (alphabet_enlarge M
                            :: ('q \<times> ('a, 'c) ae_stage, 'c \<Rightarrow> 'a) mttm))"
                    "4 * (6 * k_tm M + 1)
                       * block_width (\<Gamma>_tm (alphabet_enlarge M
                            :: ('q \<times> ('a, 'c) ae_stage, 'c \<Rightarrow> 'a) mttm))"])
  show "\<forall>w. set w \<subseteq> Sigma_tm M \<longrightarrow>
           accepts_in_time_mttm M w (T (length w)) \<longrightarrow>
           accepts_in_time_mttm
             (alphabet_reduce (alphabet_enlarge M)
                :: ((('q \<times> ('a, 'c) ae_stage) \<times> ('c \<Rightarrow> 'a) ar_stage), sym4) mttm)
             (encode_input_ar
                 (\<Gamma>_tm (alphabet_enlarge M :: ('q \<times> ('a, 'c) ae_stage, 'c \<Rightarrow> 'a) mttm))
                 (bl_tm (alphabet_enlarge M))
                 (encode_input (bl_tm M) w))
             (8 * (6 * k_tm M + 1)
                   * block_width (\<Gamma>_tm (alphabet_enlarge M
                        :: ('q \<times> ('a, 'c) ae_stage, 'c \<Rightarrow> 'a) mttm))
                   * T (length w + card (UNIV :: 'c set) - 1)
               + 2 * (6 * k_tm M + 1)
                   * block_width (\<Gamma>_tm (alphabet_enlarge M
                        :: ('q \<times> ('a, 'c) ae_stage, 'c \<Rightarrow> 'a) mttm))
                   * length w
               + 4 * (6 * k_tm M + 1)
                   * block_width (\<Gamma>_tm (alphabet_enlarge M
                        :: ('q \<times> ('a, 'c) ae_stage, 'c \<Rightarrow> 'a) mttm)))"
    by (rule alphabet_enlarge_reduce_time_explicit[OF wfM card_ge Tmono])
qed

end
