theory Wrap_Speedup
  imports AlphabetEnlargement_Pack Wrap_Time
begin

section \<open>Faithful (k-tape) classical linear-speedup headlines --- plant-\<open>le\<close> wrap\<close>

text \<open>The faithful @{text k}-tape statements of the classical linear-speedup
  theorems, over the plant-\<open>le\<close> wrap @{const encoding_wrap} at tape count
  @{term "k_tm M"}.  These are the textbook statements of Hopcroft--Ullman
  \<^cite>\<open>\<open>Theorem 12.4\<close> in "Hopcroft1979:introduction"\<close> and its
  nondeterministic corollary, genuinely
  @{text k}-tape-to-@{text k}-tape (matching the textbook @{text "k > 1"}).

  The development has two layers: a Form-1 raw composition
  (@{text linear_speedup_form_1_raw_nae} / @{text "_dae_B"}) that glues
  the alphabet-enlargement engine to the plant-\<open>le\<close> wrap's correctness lemmas
  (@{thm[source] wrap_wf}, @{thm[source] wrap_language},
  @{thm[source] wrap_time}, @{thm[source] wrap_det}), then the textbook
  corollaries (@{text linear_speedup_HU_12_4_nae} = the nondeterministic
  corollary \<^cite>\<open>\<open>p.~291\<close> in "Hopcroft1979:introduction"\<close>,
  @{text "_dae_B"} = Theorem 12.4 proper) as arithmetic
  specialisations.

  The wrap correctness lemmas carry the side-condition @{term "2 \<le> k_tm M"},
  which holds on the source via @{term "k_tm (alphabet_enlarge M) = k_tm M"}.
  The Form-1 time bound has a coefficient-@{text 1} linear term
  @{term "length w"} (the encoder pass): the plant-\<open>le\<close> reset rewinds only the
  storage tape (at most
  @{term "(length w + card (UNIV :: 'c set) - 1) div card (UNIV :: 'c set)"}
  cells) and never the raw input, so unlike the transpose's coefficient-@{text 2}
  bound this meets the @{text "(1+\<epsilon>)n"} form HU 12.4 requires.\<close>


subsection \<open>Linear speedup theorem (Form 1, raw composition) --- faithful\<close>

text \<open>The faithful Form-1 corollary: the plant-\<open>le\<close>-wrap-over-AE machine
  @{text "M''"} satisfies the three det-free conjuncts of Form 1 --- wf,
  language-equality, and an explicit time bound whose linear-in-@{text "|w|"}
  coefficient is @{text 1} (the @{text "(1+\<epsilon>)n"} payoff --- no input
  rewind).\<close>

lemma linear_speedup_form_1_raw_nae:
  fixes M :: "('q, 'a) mttm"
    and T :: "nat \<Rightarrow> nat"
  assumes wf:        "well_formed_mttm M"
      and c_pos:     "0 < (card (UNIV :: ('c :: enum) set))"
      and k2:        "2 \<le> k_tm M"
  shows "valid_mttm
          (encoding_wrap
             (alphabet_enlarge M
                :: ('q \<times> ('a, 'c) ae_stage, 'c \<Rightarrow> 'a) mttm)
             (ae_pack (bl_tm M) :: 'a list \<Rightarrow> ('c \<Rightarrow> 'a))
             (card (UNIV :: 'c set))
             (Sigma_tm M))"
    and "Lang_user_wrap
          (encoding_wrap
             (alphabet_enlarge M
                :: ('q \<times> ('a, 'c) ae_stage, 'c \<Rightarrow> 'a) mttm)
             (ae_pack (bl_tm M) :: 'a list \<Rightarrow> ('c \<Rightarrow> 'a))
             (card (UNIV :: 'c set))
             (Sigma_tm M))
         = Lang_mttm M"
    and "\<forall>w. set w \<subseteq> Sigma_tm M
              \<longrightarrow> accepts_in_time_mttm M w (T (length w))
              \<longrightarrow> accepts_in_time_user_wrap
                    (encoding_wrap
                       (alphabet_enlarge M
                          :: ('q \<times> ('a, 'c) ae_stage, 'c \<Rightarrow> 'a) mttm)
                       (ae_pack (bl_tm M) :: 'a list \<Rightarrow> ('c \<Rightarrow> 'a))
                       (card (UNIV :: 'c set))
                       (Sigma_tm M))
                    w
                    (length w
                     + (length w + card (UNIV :: 'c set) - 1)
                              div card (UNIV :: 'c set)
                     + 5
                     + 2 * ((length w + card (UNIV :: 'c set) - 1)
                              div card (UNIV :: 'c set))
                     + 8 * ((T (length w) + card (UNIV :: 'c set) - 1)
                              div card (UNIV :: 'c set))
                     + 4)"
proof -
  from wf have vM:        "valid_mttm M"
           and le_neq_bl: "le_tm M \<noteq> bl_tm M"
    by auto

  let ?M' = "alphabet_enlarge M
              :: ('q \<times> ('a, 'c) ae_stage, 'c \<Rightarrow> 'a) mttm"
  let ?c = "card (UNIV :: 'c set)"
  let ?pack = "ae_pack (bl_tm M) :: 'a list \<Rightarrow> ('c \<Rightarrow> 'a)"
  let ?M'' = "encoding_wrap ?M' ?pack ?c (Sigma_tm M)"

  \<comment> \<open>AE preserves validity.\<close>
  have vM': "valid_mttm ?M'"
    by (rule alphabet_enlarge_wf[OF vM])

  \<comment> \<open>\<open>Sigma_tm\<close> M is finite (\<open>Sigma\<close> \<open>\<subseteq>\<close> \<open>Gamma\<close>, \<open>Gamma\<close> finite).\<close>
  have finSigma: "finite (Sigma_tm M)"
    using valid_mttm_Sigma_sub_Gamma[OF vM]
          valid_mttm_finite_Gamma[OF vM]
          rev_finite_subset by blast

  \<comment> \<open>\<open>bl\<close> ?M' \<open>\<noteq>\<close> \<open>le\<close> ?M' (from the AE substrate projections).\<close>
  have bl_ne_le': "bl_tm ?M' \<noteq> le_tm ?M'"
    unfolding bl_tm_alphabet_enlarge le_tm_alphabet_enlarge
    using le_neq_bl by (simp add: bl_block_def LE_block_def fun_eq_iff)

  \<comment> \<open>AE preserves the tape count, so \<open>2 \<le> k_tm\<close> ?M'.\<close>
  have k_eq: "k_tm ?M' = k_tm M"
    by (cases M) (simp add: alphabet_enlarge_def)
  have k2': "2 \<le> k_tm ?M'" using k2 k_eq by simp

  \<comment> \<open>The faithful wrap preserves validity.  Since the clause-2
     relaxation \<open>wrap_wf\<close> needs only \<open>valid_mttm\<close> and \<open>le \<noteq> bl\<close> of its
     input (not LE-uniqueness), both of which AE preserves.\<close>
  have le_neq_bl': "le_tm ?M' \<noteq> bl_tm ?M'" using bl_ne_le' by simp
  have wf_wrap: "valid_mttm ?M''"
    by (rule wrap_wf[OF vM' le_neq_bl' finSigma c_pos k2'])

  \<comment> \<open>Glue: \<open>wrap_enc\<close> = \<open>encode_input\<close> (under the \<open>ae_pack\<close> instantiation).\<close>
  have glue: "\<And>w. wrap_enc ?pack ?c w = encode_input (bl_tm M) w"
  proof -
    fix w
    show "wrap_enc ?pack ?c w = encode_input (bl_tm M) w"
      by (rule wrap_enc_eq_encode_input[OF c_pos])
  qed

  \<comment> \<open>For any input word w with set w \<open>\<subseteq>\<close> \<open>Sigma_tm\<close> M, the encoded form lives
     in \<open>Sigma_tm\<close> ?M'.\<close>
  have enc_in_Sigma_M':
    "\<And>w. set w \<subseteq> Sigma_tm M
            \<Longrightarrow> set (wrap_enc ?pack ?c w) \<subseteq> Sigma_tm ?M'"
  proof -
    fix w :: "'a list" assume w_sub: "set w \<subseteq> Sigma_tm M"
    have in_gamma:
      "set (encode_input (bl_tm M) w :: ('c \<Rightarrow> 'a) list)
        \<subseteq> gamma_block (Sigma_tm M \<union> {bl_tm M})"
      by (rule encode_input_in_gamma_block[OF w_sub])
    have no_bl:
      "bl_block (bl_tm M) \<notin> set (encode_input (bl_tm M) w :: ('c \<Rightarrow> 'a) list)"
      by (rule encode_input_no_bl_block[OF vM w_sub])
    have no_LE:
      "LE_block (le_tm M) \<notin> set (encode_input (bl_tm M) w :: ('c \<Rightarrow> 'a) list)"
      by (rule encode_input_no_LE_block[OF vM w_sub])
    from in_gamma no_bl no_LE
    have "set (encode_input (bl_tm M) w :: ('c \<Rightarrow> 'a) list)
            \<subseteq> gamma_block (Sigma_tm M \<union> {bl_tm M})
              - {bl_block (bl_tm M), LE_block (le_tm M)}"
      by auto
    hence "set (encode_input (bl_tm M) w :: ('c \<Rightarrow> 'a) list)
            \<subseteq> Sigma_tm ?M'"
      unfolding Sigma_tm_alphabet_enlarge by simp
    thus "set (wrap_enc ?pack ?c w) \<subseteq> Sigma_tm ?M'"
      using glue by simp
  qed

  \<comment> \<open>Language equivalence (faithful wrap).\<close>
  have lang_eq: "Lang_user_wrap ?M'' = Lang_mttm M"
  proof -
    have wrap_lang:
      "Lang_user_wrap ?M''
        = {w. set w \<subseteq> Sigma_tm M
              \<and> wrap_enc ?pack ?c w \<in> Lang_mttm ?M'}"
      using wrap_language[OF vM' finSigma c_pos bl_ne_le' k2'] .
    have ae_lang:
      "\<forall>w. set w \<subseteq> Sigma_tm M
              \<longrightarrow> (encode_input (bl_tm M) w \<in> Lang_mttm ?M')
                  = (w \<in> Lang_mttm M)"
      using alphabet_enlarge_language[OF wf]
      by simp
    have lang_subset: "Lang_mttm M \<subseteq> {w. set w \<subseteq> Sigma_tm M}"
      unfolding Lang_mttm_def by auto
    show ?thesis
    proof
      show "Lang_user_wrap ?M'' \<subseteq> Lang_mttm M"
        using wrap_lang glue ae_lang by auto
    next
      show "Lang_mttm M \<subseteq> Lang_user_wrap ?M''"
      proof
        fix w assume wL: "w \<in> Lang_mttm M"
        with lang_subset have w_sub: "set w \<subseteq> Sigma_tm M" by auto
        from wL ae_lang w_sub
        have "encode_input (bl_tm M) w \<in> Lang_mttm ?M'" by simp
        hence "wrap_enc ?pack ?c w \<in> Lang_mttm ?M'" using glue by simp
        with w_sub wrap_lang show "w \<in> Lang_user_wrap ?M''" by auto
      qed
    qed
  qed

  \<comment> \<open>Time bound: compose \<open>wrap_time\<close> + \<open>alphabet_enlarge_time\<close> + glue.
     The faithful wrap charges the encoder pass plus the storage rewind
     (length of \<open>wrap_enc\<close>, i.e. \<open>\<lceil>|w|/c\<rceil>\<close>) --- no input rewind, so the
     linear term is @{term "length w"} with coefficient @{text 1}.\<close>
  \<comment> \<open>The AE structural constants are literal: \<open>\<alpha> = 2\<close>, \<open>f = 4\<close> (from the
     explicit AE time bound @{thm[source] alphabet_enlarge_time_explicit}).
     They are pinned to named locals so the arithmetic body below reads
     unchanged; the headline states them as literals.\<close>
  obtain \<alpha> f :: nat where alpha2: "\<alpha> = (2::nat)" and f4: "f = (4::nat)"
    by blast
  have ae_time:
    "\<forall>w. set w \<subseteq> Sigma_tm M
            \<longrightarrow> accepts_in_time_mttm M w (T (length w))
            \<longrightarrow> accepts_in_time_mttm ?M'
                  (encode_input (bl_tm M) w)
                  (\<alpha> * ((length w + ?c - 1) div ?c)
                   + 8 * ((T (length w) + ?c - 1) div ?c)
                   + f)"
    unfolding alpha2 f4 using alphabet_enlarge_time_explicit[OF wf, of T] by blast

  have time_bound:
    "\<forall>w. set w \<subseteq> Sigma_tm M
            \<longrightarrow> accepts_in_time_mttm M w (T (length w))
            \<longrightarrow> accepts_in_time_user_wrap ?M'' w
                  (length w
                   + (length w + ?c - 1) div ?c
                   + 5
                   + \<alpha> * ((length w + ?c - 1) div ?c)
                   + 8 * ((T (length w) + ?c - 1) div ?c)
                   + f)"
  proof (intro allI impI)
    fix w :: "'a list"
    assume w_sub: "set w \<subseteq> Sigma_tm M"
       and accept_M: "accepts_in_time_mttm M w (T (length w))"
    let ?t_ae = "\<alpha> * ((length w + ?c - 1) div ?c)
                  + 8 * ((T (length w) + ?c - 1) div ?c) + f"
    from ae_time w_sub accept_M
    have ae_step:
      "accepts_in_time_mttm ?M' (encode_input (bl_tm M) w) ?t_ae"
      by blast
    have wrap_input: "accepts_in_time_mttm ?M' (wrap_enc ?pack ?c w) ?t_ae"
      using ae_step glue by simp
    have enc_in: "set (wrap_enc ?pack ?c w) \<subseteq> Sigma_tm ?M'"
      using enc_in_Sigma_M'[OF w_sub] .

    \<comment> \<open>The plant wrap's storage-rewind term is exactly the encoded-tape
       length, which is the ceiling \<open>\<lceil>|w|/c\<rceil>\<close> (via the \<open>encode_input\<close>
       length lemma and the \<open>wrap_enc\<close> = \<open>encode_input\<close> glue).\<close>
    have len_enc: "length (wrap_enc ?pack ?c w) = (length w + ?c - 1) div ?c"
    proof -
      have "length (wrap_enc ?pack ?c w)
              = length (encode_input (bl_tm M) w :: ('c \<Rightarrow> 'a) list)"
        using glue by simp
      also have "\<dots> = (length w + ?c - 1) div ?c"
        by (rule length_encode_input)
      finally show ?thesis .
    qed

    have wrap_step:
      "accepts_in_time_user_wrap ?M'' w
          (length w + length (wrap_enc ?pack ?c w) + 5 + ?t_ae)"
      using wrap_time[OF vM' finSigma c_pos bl_ne_le' k2'
                           w_sub enc_in wrap_input] .
    \<comment> \<open>Rewrite the storage-rewind term to the ceiling form and re-bracket;
       \<open>argo\<close> substitutes through the uninterpreted predicate.\<close>
    have teq:
      "length w + length (wrap_enc ?pack ?c w) + 5 + ?t_ae
         = length w + (length w + ?c - 1) div ?c + 5
           + \<alpha> * ((length w + ?c - 1) div ?c)
           + 8 * ((T (length w) + ?c - 1) div ?c) + f"
      using len_enc by simp
    show "accepts_in_time_user_wrap ?M'' w
            (length w
             + (length w + ?c - 1) div ?c
             + 5
             + \<alpha> * ((length w + ?c - 1) div ?c)
             + 8 * ((T (length w) + ?c - 1) div ?c)
             + f)"
      using wrap_step teq by argo
  qed

  show "valid_mttm ?M''" by (rule wf_wrap)
  show "Lang_user_wrap ?M'' = Lang_mttm M" by (rule lang_eq)
  show "\<forall>w. set w \<subseteq> Sigma_tm M
              \<longrightarrow> accepts_in_time_mttm M w (T (length w))
              \<longrightarrow> accepts_in_time_user_wrap ?M'' w
                    (length w
                     + (length w + ?c - 1) div ?c
                     + 5
                     + 2 * ((length w + ?c - 1) div ?c)
                     + 8 * ((T (length w) + ?c - 1) div ?c)
                     + 4)"
    by (rule time_bound[unfolded alpha2 f4])
qed


text \<open>Determinism-preserving faithful Form-1 raw composition (DAE).  The
  det-free base @{thm[source] linear_speedup_form_1_raw_nae} supplies the
  validity, language, and time conjuncts; the extra @{const det_mttm} output
  conjunct is the one piece that consumes @{term "det_mttm M"} (via
  @{thm[source] wrap_det}).\<close>

lemma linear_speedup_form_1_raw_dae:
  fixes M :: "('q, 'a) mttm"
    and T :: "nat \<Rightarrow> nat"
  assumes wf:        "well_formed_mttm M"
      and det:       "det_mttm M"
      and c_pos:     "0 < (card (UNIV :: ('c :: enum) set))"
      and k2:        "2 \<le> k_tm M"
  shows "valid_mttm
          (encoding_wrap
             (alphabet_enlarge M
                :: ('q \<times> ('a, 'c) ae_stage, 'c \<Rightarrow> 'a) mttm)
             (ae_pack (bl_tm M) :: 'a list \<Rightarrow> ('c \<Rightarrow> 'a))
             (card (UNIV :: 'c set))
             (Sigma_tm M))"
    and "det_mttm
          (encoding_wrap
             (alphabet_enlarge M
                :: ('q \<times> ('a, 'c) ae_stage, 'c \<Rightarrow> 'a) mttm)
             (ae_pack (bl_tm M) :: 'a list \<Rightarrow> ('c \<Rightarrow> 'a))
             (card (UNIV :: 'c set))
             (Sigma_tm M))"
    and "Lang_user_wrap
          (encoding_wrap
             (alphabet_enlarge M
                :: ('q \<times> ('a, 'c) ae_stage, 'c \<Rightarrow> 'a) mttm)
             (ae_pack (bl_tm M) :: 'a list \<Rightarrow> ('c \<Rightarrow> 'a))
             (card (UNIV :: 'c set))
             (Sigma_tm M))
         = Lang_mttm M"
    and "\<forall>w. set w \<subseteq> Sigma_tm M
              \<longrightarrow> accepts_in_time_mttm M w (T (length w))
              \<longrightarrow> accepts_in_time_user_wrap
                    (encoding_wrap
                       (alphabet_enlarge M
                          :: ('q \<times> ('a, 'c) ae_stage, 'c \<Rightarrow> 'a) mttm)
                       (ae_pack (bl_tm M) :: 'a list \<Rightarrow> ('c \<Rightarrow> 'a))
                       (card (UNIV :: 'c set))
                       (Sigma_tm M))
                    w
                    (length w
                     + (length w + card (UNIV :: 'c set) - 1)
                              div card (UNIV :: 'c set)
                     + 5
                     + 2 * ((length w + card (UNIV :: 'c set) - 1)
                              div card (UNIV :: 'c set))
                     + 8 * ((T (length w) + card (UNIV :: 'c set) - 1)
                              div card (UNIV :: 'c set))
                     + 4)"
proof -
  from wf have vM: "valid_mttm M"
           and le_neq_bl: "le_tm M \<noteq> bl_tm M"
    by auto
  let ?M' = "alphabet_enlarge M
              :: ('q \<times> ('a, 'c) ae_stage, 'c \<Rightarrow> 'a) mttm"
  let ?c = "card (UNIV :: 'c set)"
  let ?pack = "ae_pack (bl_tm M) :: 'a list \<Rightarrow> ('c \<Rightarrow> 'a)"
  let ?M'' = "encoding_wrap ?M' ?pack ?c (Sigma_tm M)"

  \<comment> \<open>Validity, language, and time come from the det-free base (now with
     literal AE constants \<open>2\<close>, \<open>8\<close>, \<open>4\<close>).\<close>
  have v: "valid_mttm ?M''"
    and l: "Lang_user_wrap ?M'' = Lang_mttm M"
    and t: "\<forall>w. set w \<subseteq> Sigma_tm M
                \<longrightarrow> accepts_in_time_mttm M w (T (length w))
                \<longrightarrow> accepts_in_time_user_wrap ?M'' w
                      (length w
                       + (length w + ?c - 1) div ?c
                       + 5
                       + 2 * ((length w + ?c - 1) div ?c)
                       + 8 * ((T (length w) + ?c - 1) div ?c)
                       + 4)"
    by (rule linear_speedup_form_1_raw_nae[OF wf c_pos k2])+

  \<comment> \<open>Determinism is the one extra conjunct; it needs \<open>det_mttm M\<close>.\<close>
  have vM': "valid_mttm ?M'" by (rule alphabet_enlarge_wf[OF vM])
  have detM': "det_mttm ?M'"
    unfolding det_mttm_def delta_tm_alphabet_enlarge
    using alphabet_enlarge_delta_functional[OF vM det le_neq_bl] by blast
  have finSigma: "finite (Sigma_tm M)"
    using valid_mttm_Sigma_sub_Gamma[OF vM]
          valid_mttm_finite_Gamma[OF vM]
          rev_finite_subset by blast
  have det_wrap: "det_mttm ?M''"
    by (rule wrap_det[OF vM' detM' finSigma c_pos])

  show "valid_mttm ?M''" by (rule v)
  show "det_mttm ?M''" by (rule det_wrap)
  show "Lang_user_wrap ?M'' = Lang_mttm M" by (rule l)
  show "\<forall>w. set w \<subseteq> Sigma_tm M
              \<longrightarrow> accepts_in_time_mttm M w (T (length w))
              \<longrightarrow> accepts_in_time_user_wrap ?M'' w
                    (length w
                     + (length w + ?c - 1) div ?c
                     + 5
                     + 2 * ((length w + ?c - 1) div ?c)
                     + 8 * ((T (length w) + ?c - 1) div ?c)
                     + 4)"
    by (rule t)
qed


subsection \<open>Textbook linear-speedup theorem (HU 12.4) --- faithful k-tape\<close>
text \<open>The textbook linear-speedup theorem, Form 1
  \<^cite>\<open>\<open>Theorem 12.4\<close> in "Hopcroft1979:introduction"\<close>: the
  linear-time-bound case @{text "T(n) \<le> d_0 \<cdot> n + b"}.

  HU 12.4 is the linear-@{text T} corollary of the raw composition
  @{thm[source] linear_speedup_form_1_raw_dae}: where the raw form carries the
  full ceiling-divisional bound
  @{text "|w| + \<lceil>|w|/c\<rceil> + 5 + 2\<lceil>|w|/c\<rceil> + 8\<lceil>T(|w|)/c\<rceil> + 4"} (the AE
  structural constants are now the literals @{text "\<alpha> = 2"},
  @{text "f = 4"}), HU 12.4 absorbs the @{text "T_linear"} hypothesis
  @{text "T(n) \<le> d_0 \<cdot> n + b"} and the ceiling-division slack into the
  \<^emph>\<open>explicit\<close> textbook constant @{text "K = 28 + 8 d_0 + 8 b"} under
  a positive-nat @{text q} (the textbook real-valued @{text \<epsilon>} taken as
  @{text "1/q"}).  The conclusion shape collapses to
  @{text "|w| + |w| div q + (28 + 8 d_0 + 8 b)"}, gated by a single
  @{text c_large} side condition @{text "q * (3 + 8 * d_0) \<le> c"} on the
  cardinality of the grouping-factor type @{typ 'c}.

  Statement is parametric in @{typ 'c} (the AE grouping-factor type) and
  in @{text q}.  Consumers instantiate @{typ 'c} at use sites via a
  @{text "HOL.Library.Numeral_Type"} of cardinality large enough to
  satisfy the @{text c_large} side condition on the time-bound conjunct.
  With @{text \<alpha>} now literal the constant @{text K} is a closed
  expression in @{text "d_0, b"} (no @{text "obtains"}), and the wf, det,
  and language-equality conjuncts hold unconditionally (they do not
  depend on @{text q}); only the time-bound conjunct is gated by
  @{text c_large}.

  Note on packaging: the @{text c_large} side condition for HU 12.4 takes
  the form @{text "q * (3 + 8 * d_0) \<le> c"}.  It is @{text \<alpha>}-free (the
  simulation constant is the literal @{text 2}), but @{text "d_0"}-dependent,
  and is retained INSIDE the statement as an implication on the time-bound
  conjunct rather than externalised as an outer @{text "assumes"}, so the
  four convention / eventual corollaries thread it uniformly.  HU 12.3
  below packages its corresponding side condition as an outer
  @{text "assumes c_large: 16 * q \<le> c"}, its constant @{text "16 * q"}
  being @{text "d_0"}-free.\<close>

theorem linear_speedup_HU_12_4_nae:
  fixes M :: "('q, 'a) mttm"
    and T :: "nat \<Rightarrow> nat"
    and d_0 b q :: nat
  assumes wf:        "well_formed_mttm M"
      and T_linear:  "\<forall>n. T n \<le> d_0 * n + b"
      and q_pos:     "0 < q"
      and c_pos:     "0 < (card (UNIV :: ('c :: enum) set))"
      and k2:        "2 \<le> k_tm M"
  shows "valid_mttm
          (encoding_wrap
             (alphabet_enlarge M
                :: ('q \<times> ('a, 'c) ae_stage, 'c \<Rightarrow> 'a) mttm)
             (ae_pack (bl_tm M) :: 'a list \<Rightarrow> ('c \<Rightarrow> 'a))
             (card (UNIV :: 'c set))
             (Sigma_tm M))"
    and "Lang_user_wrap
          (encoding_wrap
             (alphabet_enlarge M
                :: ('q \<times> ('a, 'c) ae_stage, 'c \<Rightarrow> 'a) mttm)
             (ae_pack (bl_tm M) :: 'a list \<Rightarrow> ('c \<Rightarrow> 'a))
             (card (UNIV :: 'c set))
             (Sigma_tm M))
         = Lang_mttm M"
    and "q * (3 + 8 * d_0) \<le> card (UNIV :: 'c set)
         \<longrightarrow> (\<forall>w. set w \<subseteq> Sigma_tm M
                   \<longrightarrow> accepts_in_time_mttm M w (T (length w))
                   \<longrightarrow> accepts_in_time_user_wrap
                         (encoding_wrap
                            (alphabet_enlarge M
                               :: ('q \<times> ('a, 'c) ae_stage, 'c \<Rightarrow> 'a) mttm)
                            (ae_pack (bl_tm M) :: 'a list \<Rightarrow> ('c \<Rightarrow> 'a))
                            (card (UNIV :: 'c set))
                            (Sigma_tm M))
                         w
                         (length w + length w div q + (28 + 8 * d_0 + 8 * b)))"
proof -
  let ?M' = "alphabet_enlarge M
              :: ('q \<times> ('a, 'c) ae_stage, 'c \<Rightarrow> 'a) mttm"
  let ?c = "card (UNIV :: 'c set)"
  let ?pack = "ae_pack (bl_tm M) :: 'a list \<Rightarrow> ('c \<Rightarrow> 'a)"
  let ?M'' = "encoding_wrap ?M' ?pack ?c (Sigma_tm M)"

  \<comment> \<open>Materialise form-1's structural conjuncts.  The AE constants are
     literal (\<open>\<alpha> = 2\<close>, \<open>f = 4\<close>); pinned to named locals so the
     specialisation arithmetic below reads unchanged.\<close>
  obtain \<alpha> f :: nat where alpha2: "\<alpha> = (2::nat)" and f4: "f = (4::nat)"
    by blast
  have wf_M'':   "valid_mttm ?M''"
    and lang_M'': "Lang_user_wrap ?M'' = Lang_mttm M"
    and time_F1:  "\<forall>w. set w \<subseteq> Sigma_tm M
                        \<longrightarrow> accepts_in_time_mttm M w (T (length w))
                        \<longrightarrow> accepts_in_time_user_wrap ?M'' w
                              (length w
                               + (length w + ?c - 1) div ?c
                               + 5
                               + \<alpha> * ((length w + ?c - 1) div ?c)
                               + 8 * ((T (length w) + ?c - 1) div ?c)
                               + f)"
    unfolding alpha2 f4
    by (rule linear_speedup_form_1_raw_nae[OF wf c_pos k2])+

  \<comment> \<open>HU 12.4 specialisation constant: pick @{text K} big enough to absorb
     the ceiling-division slack plus the @{text T_linear} additive @{text b}
     plus form-1's structural constants.  Under
     @{text "c \<ge> q * (1 + \<alpha> + 8 * d_0)"} the form-1 bound simplifies
     to @{text "|w| + |w| div q + K"}.\<close>
  define K :: nat where
    "K = 22 + \<alpha> + 8 * d_0 + 8 * b + f"

  \<comment> \<open>Monotonicity of @{const accepts_in_time_user_wrap} in its time argument
     (immediate from the @{text "n \<le> t"} bound inside @{const accepts_in_time_mttm}).\<close>
  have user_mono:
    "\<And>w t\<^sub>1 t\<^sub>2. accepts_in_time_user_wrap ?M'' w t\<^sub>1 \<Longrightarrow> t\<^sub>1 \<le> t\<^sub>2
                  \<Longrightarrow> accepts_in_time_user_wrap ?M'' w t\<^sub>2"
    unfolding accepts_in_time_user_wrap_def accepts_in_time_mttm_def
    by (meson le_trans)

  have time_HU_12_4:
    "q * (1 + \<alpha> + 8 * d_0) \<le> ?c
       \<longrightarrow> (\<forall>w. set w \<subseteq> Sigma_tm M
                  \<longrightarrow> accepts_in_time_mttm M w (T (length w))
                  \<longrightarrow> accepts_in_time_user_wrap ?M'' w
                        (length w + length w div q + K))"
  proof
    assume c_large: "q * (1 + \<alpha> + 8 * d_0) \<le> ?c"
    show "\<forall>w. set w \<subseteq> Sigma_tm M
                \<longrightarrow> accepts_in_time_mttm M w (T (length w))
                \<longrightarrow> accepts_in_time_user_wrap ?M'' w
                      (length w + length w div q + K)"
    proof
      fix w :: "'a list"
      show "set w \<subseteq> Sigma_tm M
              \<longrightarrow> accepts_in_time_mttm M w (T (length w))
              \<longrightarrow> accepts_in_time_user_wrap ?M'' w
                    (length w + length w div q + K)"
      proof
        assume w_sub: "set w \<subseteq> Sigma_tm M"
        show "accepts_in_time_mttm M w (T (length w))
                \<longrightarrow> accepts_in_time_user_wrap ?M'' w
                      (length w + length w div q + K)"
        proof
          assume accepts_M: "accepts_in_time_mttm M w (T (length w))"

          let ?n = "length w"
          let ?B1 = "?n + (?n + ?c - 1) div ?c + 5
                      + \<alpha> * ((?n + ?c - 1) div ?c)
                      + 8 * ((T ?n + ?c - 1) div ?c) + f"

          \<comment> \<open>Form-1's bound applies to @{term w}.\<close>
          have form_1_accepts: "accepts_in_time_user_wrap ?M'' w ?B1"
            using time_F1 w_sub accepts_M by blast

          \<comment> \<open>Ceiling-via-floor:  \<open>(x + c - 1) div c \<le> x div c + 1\<close>.\<close>
          have ceil_le: "(x + ?c - 1) div ?c \<le> x div ?c + 1" for x :: nat
          proof -
            have a: "x + ?c - 1 \<le> x + ?c" by simp
            have b: "(x + ?c) div ?c = x div ?c + 1"
              using c_pos by (simp add: div_add_self2)
            from a have "(x + ?c - 1) div ?c \<le> (x + ?c) div ?c"
              by (rule div_le_mono)
            with b show ?thesis by simp
          qed

          \<comment> \<open>Two consequences of @{thm[source] ceil_le}.\<close>
          have base_ceil_le: "(?n + ?c - 1) div ?c \<le> ?n div ?c + 1"
            by (rule ceil_le)
          have alpha_ceil_le:
            "\<alpha> * ((?n + ?c - 1) div ?c) \<le> \<alpha> * (?n div ?c) + \<alpha>"
          proof -
            have "\<alpha> * ((?n + ?c - 1) div ?c) \<le> \<alpha> * (?n div ?c + 1)"
              using base_ceil_le by (rule mult_le_mono2)
            also have "\<dots> = \<alpha> * (?n div ?c) + \<alpha>" by simp
            finally show ?thesis .
          qed

          \<comment> \<open>@{text T_linear} hypothesis specialised at @{term "length w"}.\<close>
          have T_n_bound: "T ?n \<le> d_0 * ?n + b"
            using T_linear by blast

          \<comment> \<open>Strict overshoot: @{text "n < c * (n div c + 1)"}.  From Euclidean
             @{text "n = c * (n div c) + n mod c"} plus @{text "n mod c < c"}.\<close>
          have n_lt_c_succ: "?n < ?c * (?n div ?c + 1)"
          proof -
            have e: "?c * (?n div ?c) + ?n mod ?c = ?n"
              by (rule mult_div_mod_eq)
            have m: "?n mod ?c < ?c" using c_pos by simp
            have d: "?c * (?n div ?c + 1) = ?c * (?n div ?c) + ?c"
              by (simp add: distrib_left)
            from e m d show ?thesis by linarith
          qed

          \<comment> \<open>Scalar overshoot: @{text "d_0 * n \<le> c * (d_0 * (n div c + 1))"}.
             Avoids reasoning about @{text "(d_0 * n) div c"} directly.\<close>
          have d0n_le_dc: "d_0 * ?n \<le> ?c * (d_0 * (?n div ?c + 1))"
          proof -
            have a: "?n \<le> ?c * (?n div ?c + 1)"
              using n_lt_c_succ by simp
            have b: "d_0 * ?n \<le> d_0 * (?c * (?n div ?c + 1))"
              using a by (rule mult_le_mono2)
            have c: "d_0 * (?c * (?n div ?c + 1)) = ?c * (d_0 * (?n div ?c + 1))"
              by (metis mult.commute mult.assoc)
            show ?thesis using b unfolding c .
          qed

          \<comment> \<open>The clean T-ceiling bound:
             @{text "(T n + c - 1) div c \<le> d_0 * (n div c + 1) + (b + c - 1) div c"}.
             Derived from @{text T_n_bound} + @{text d0n_le_dc} + @{thm[source] div_le_mono}
             + @{thm[source] div_mult_self4}.\<close>
          have T_to_c_div:
            "(T ?n + ?c - 1) div ?c
              \<le> d_0 * (?n div ?c + 1) + (b + ?c - 1) div ?c"
          proof -
            have h1: "T ?n + ?c - 1 \<le> d_0 * ?n + b + ?c - 1"
              using T_n_bound by simp
            have h2: "d_0 * ?n + b + ?c - 1
                        \<le> ?c * (d_0 * (?n div ?c + 1)) + (b + ?c - 1)"
              using d0n_le_dc by simp
            have h3: "T ?n + ?c - 1
                        \<le> ?c * (d_0 * (?n div ?c + 1)) + (b + ?c - 1)"
              using h1 h2 by linarith
            have h4: "(T ?n + ?c - 1) div ?c
                        \<le> (?c * (d_0 * (?n div ?c + 1)) + (b + ?c - 1)) div ?c"
              using h3 by (rule div_le_mono)
            have c_nz: "?c \<noteq> 0" using c_pos by simp
            have h5: "(?c * (d_0 * (?n div ?c + 1)) + (b + ?c - 1)) div ?c
                        = d_0 * (?n div ?c + 1) + (b + ?c - 1) div ?c"
              using c_nz by (rule div_mult_self4)
            from h4 h5 show ?thesis by simp
          qed

          \<comment> \<open>Collapse the @{text "(b + c - 1) div c"} residue into @{text "b + 1"}.\<close>
          have b_div_le_b: "b div ?c \<le> b"
            by (rule div_le_dividend)
          have ceil_b_simple: "(b + ?c - 1) div ?c \<le> b + 1"
          proof -
            have a: "(b + ?c - 1) div ?c \<le> b div ?c + 1" by (rule ceil_le)
            from a b_div_le_b show ?thesis by linarith
          qed

          \<comment> \<open>Full T-ceiling bound via @{text T_to_c_div} + @{text ceil_b_simple},
             multiplied by 8.  Needs an explicit @{text "d_0 * (k+1) = d_0 * k + d_0"}
             expansion since @{text linarith} doesn't multiply by variables.\<close>
          have eight_T_full:
            "8 * ((T ?n + ?c - 1) div ?c)
              \<le> 8 * d_0 * (?n div ?c) + 8 * d_0 + 8 * b + 8"
          proof -
            have d0_succ: "d_0 * (?n div ?c + 1) = d_0 * (?n div ?c) + d_0"
              by simp
            have step: "(T ?n + ?c - 1) div ?c
                          \<le> d_0 * (?n div ?c) + d_0 + b + 1"
              using T_to_c_div d0_succ ceil_b_simple by linarith
            have eight_d0: "8 * (d_0 * (?n div ?c)) = 8 * d_0 * (?n div ?c)"
              by (simp add: mult.assoc)
            from step eight_d0 show ?thesis by linarith
          qed

          \<comment> \<open>Compact form: factor the @{text "(1 + \<alpha> + 8 d_0)"} coefficient
             via @{thm[source] distrib_right}.\<close>
          have B1_compact:
            "?B1 \<le> ?n + (1 + \<alpha> + 8 * d_0) * (?n div ?c)
                       + (14 + \<alpha> + 8 * d_0 + 8 * b + f)"
          proof -
            have combine:
              "(1 + \<alpha> + 8 * d_0) * (?n div ?c)
                 = ?n div ?c + \<alpha> * (?n div ?c) + 8 * d_0 * (?n div ?c)"
              by (simp add: algebra_simps)
            show ?thesis
              using base_ceil_le alpha_ceil_le eight_T_full combine
              by linarith
          qed

          \<comment> \<open>@{text c_large} absorption: from @{text "q * (1 + \<alpha> + 8 d_0) \<le> c"}
             derive @{text "(1 + \<alpha> + 8 d_0) * (n div c) \<le> n div q"}.
             Uses @{thm[source] mult_div_mod_eq} for @{text "c * (n div c) \<le> n"}
             and @{thm[source] less_eq_div_iff_mult_less_eq} for the final step.\<close>
          have c_absorb: "(1 + \<alpha> + 8 * d_0) * (?n div ?c) \<le> ?n div q"
          proof -
            let ?X = "(1 + \<alpha> + 8 * d_0) * (?n div ?c)"
            have eu: "?c * (?n div ?c) + ?n mod ?c = ?n"
              by (rule mult_div_mod_eq)
            have c_n: "?c * (?n div ?c) \<le> ?n" using eu by simp
            have h2: "q * (1 + \<alpha> + 8 * d_0) * (?n div ?c) \<le> ?c * (?n div ?c)"
              using c_large by (rule mult_le_mono1)
            have assoc: "q * (1 + \<alpha> + 8 * d_0) * (?n div ?c) = q * ?X"
              by (simp only: mult.assoc)
            have q_X_le_n: "q * ?X \<le> ?n"
              using h2 assoc c_n by linarith
            have comm: "q * ?X = ?X * q" by (metis mult.commute)
            have X_q_le_n: "?X * q \<le> ?n"
              using q_X_le_n comm by linarith
            show "?X \<le> ?n div q"
              using X_q_le_n q_pos
              by (simp add: less_eq_div_iff_mult_less_eq)
          qed

          \<comment> \<open>Final composition: @{text B1_compact} + @{text c_absorb} + @{text K_def}
             via @{text linarith} (everything linear in the atomic
             @{text "(1 + \<alpha> + 8 d_0) * (n div c)"} term and its absorption).\<close>
          have B1_le_target: "?B1 \<le> ?n + ?n div q + K"
            using B1_compact c_absorb K_def by linarith

          \<comment> \<open>Conclude via monotonicity of @{const accepts_in_time_user_wrap} in time.\<close>
          show "accepts_in_time_user_wrap ?M'' w (?n + ?n div q + K)"
            using user_mono[OF form_1_accepts B1_le_target] .
        qed
      qed
    qed
  qed

  \<comment> \<open>Discharge the three literal conjuncts.  The side condition and the
     additive constant are stated as literals; the pinning equations
     \<open>\<alpha> = 2\<close>, \<open>f = 4\<close> reconcile them with the \<open>\<alpha>\<close>-parametric
     @{text time_HU_12_4} (\<open>q(1 + \<alpha> + 8 d_0) = q(3 + 8 d_0)\<close> and
     \<open>K = 22 + \<alpha> + 8 d_0 + 8 b + f = 28 + 8 d_0 + 8 b\<close>).\<close>
  show "valid_mttm ?M''" by (rule wf_M'')
  show "Lang_user_wrap ?M'' = Lang_mttm M" by (rule lang_M'')
  show "q * (3 + 8 * d_0) \<le> ?c
          \<longrightarrow> (\<forall>w. set w \<subseteq> Sigma_tm M
                     \<longrightarrow> accepts_in_time_mttm M w (T (length w))
                     \<longrightarrow> accepts_in_time_user_wrap ?M'' w
                           (length w + length w div q + (28 + 8 * d_0 + 8 * b)))"
  proof -
    have s0: "(3::nat) + 8 * d_0 = 1 + \<alpha> + 8 * d_0" using alpha2 by simp
    have kk: "(28::nat) + 8 * d_0 + 8 * b = K" using K_def alpha2 f4 by simp
    show ?thesis unfolding s0 kk by (rule time_HU_12_4)
  qed
qed


text \<open>Deterministic specialisation of \<open>linear_speedup_HU_12_4_nae\<close>
  (Theorem 12.4 proper): adds determinism preservation (via
  \<open>wrap_det\<close>) on top of the nondeterministic linear-time-case
  corollary.\<close>

theorem linear_speedup_HU_12_4_dae:
  fixes M :: "('q, 'a) mttm"
    and T :: "nat \<Rightarrow> nat"
    and d_0 b q :: nat
  assumes wf:        "well_formed_mttm M"
      and det:       "det_mttm M"
      and T_linear:  "\<forall>n. T n \<le> d_0 * n + b"
      and q_pos:     "0 < q"
      and c_pos:     "0 < (card (UNIV :: ('c :: enum) set))"
      and k2:        "2 \<le> k_tm M"
  shows "valid_mttm
          (encoding_wrap
             (alphabet_enlarge M
                :: ('q \<times> ('a, 'c) ae_stage, 'c \<Rightarrow> 'a) mttm)
             (ae_pack (bl_tm M) :: 'a list \<Rightarrow> ('c \<Rightarrow> 'a))
             (card (UNIV :: 'c set))
             (Sigma_tm M))"
    and "det_mttm
          (encoding_wrap
             (alphabet_enlarge M
                :: ('q \<times> ('a, 'c) ae_stage, 'c \<Rightarrow> 'a) mttm)
             (ae_pack (bl_tm M) :: 'a list \<Rightarrow> ('c \<Rightarrow> 'a))
             (card (UNIV :: 'c set))
             (Sigma_tm M))"
    and "Lang_user_wrap
          (encoding_wrap
             (alphabet_enlarge M
                :: ('q \<times> ('a, 'c) ae_stage, 'c \<Rightarrow> 'a) mttm)
             (ae_pack (bl_tm M) :: 'a list \<Rightarrow> ('c \<Rightarrow> 'a))
             (card (UNIV :: 'c set))
             (Sigma_tm M))
         = Lang_mttm M"
    and "q * (3 + 8 * d_0) \<le> card (UNIV :: 'c set)
         \<longrightarrow> (\<forall>w. set w \<subseteq> Sigma_tm M
                   \<longrightarrow> accepts_in_time_mttm M w (T (length w))
                   \<longrightarrow> accepts_in_time_user_wrap
                         (encoding_wrap
                            (alphabet_enlarge M
                               :: ('q \<times> ('a, 'c) ae_stage, 'c \<Rightarrow> 'a) mttm)
                            (ae_pack (bl_tm M) :: 'a list \<Rightarrow> ('c \<Rightarrow> 'a))
                            (card (UNIV :: 'c set))
                            (Sigma_tm M))
                         w
                         (length w + length w div q + (28 + 8 * d_0 + 8 * b)))"
proof -
  from wf have vM: "valid_mttm M"
           and le_neq_bl: "le_tm M \<noteq> bl_tm M"
    by auto
  let ?M' = "alphabet_enlarge M
              :: ('q \<times> ('a, 'c) ae_stage, 'c \<Rightarrow> 'a) mttm"
  let ?c = "card (UNIV :: 'c set)"
  let ?pack = "ae_pack (bl_tm M) :: 'a list \<Rightarrow> ('c \<Rightarrow> 'a)"
  let ?M'' = "encoding_wrap ?M' ?pack ?c (Sigma_tm M)"

  have v: "valid_mttm ?M''"
    and l: "Lang_user_wrap ?M'' = Lang_mttm M"
    and tm: "q * (3 + 8 * d_0) \<le> ?c
              \<longrightarrow> (\<forall>w. set w \<subseteq> Sigma_tm M
                        \<longrightarrow> accepts_in_time_mttm M w (T (length w))
                        \<longrightarrow> accepts_in_time_user_wrap ?M'' w
                              (length w + length w div q + (28 + 8 * d_0 + 8 * b)))"
    by (rule linear_speedup_HU_12_4_nae[OF wf T_linear q_pos c_pos k2])+

  have vM': "valid_mttm ?M'" by (rule alphabet_enlarge_wf[OF vM])
  have detM': "det_mttm ?M'"
    unfolding det_mttm_def delta_tm_alphabet_enlarge
    using alphabet_enlarge_delta_functional[OF vM det le_neq_bl] by blast
  have finSigma: "finite (Sigma_tm M)"
    using valid_mttm_Sigma_sub_Gamma[OF vM]
          valid_mttm_finite_Gamma[OF vM]
          rev_finite_subset by blast
  have det_wrap: "det_mttm ?M''"
    by (rule wrap_det[OF vM' detM' finSigma c_pos])

  show "valid_mttm ?M''" by (rule v)
  show "det_mttm ?M''" by (rule det_wrap)
  show "Lang_user_wrap ?M'' = Lang_mttm M" by (rule l)
  show "q * (3 + 8 * d_0) \<le> ?c
          \<longrightarrow> (\<forall>w. set w \<subseteq> Sigma_tm M
                     \<longrightarrow> accepts_in_time_mttm M w (T (length w))
                     \<longrightarrow> accepts_in_time_user_wrap ?M'' w
                           (length w + length w div q + (28 + 8 * d_0 + 8 * b)))"
    by (rule tm)
qed


subsection \<open>Textbook linear-speedup theorem (HU 12.3) — faithful k-tape\<close>

text \<open>The textbook linear-speedup theorem, Form 1
  \<^cite>\<open>\<open>Theorem 12.3\<close> in "Hopcroft1979:introduction"\<close>, faithful at
  @{term "k_tm M"} tapes (matching HU's @{text "k > 1"} via
  @{term "2 \<le> k_tm M"}): the super-linear-@{text T} case
  (@{text "lim T(n)/n = \<infinity>"} as the growth hypothesis
  @{text "\<forall>d. \<exists>N. \<forall>n \<ge> N. d * n \<le> T n"}).  This is HU's
  nondeterministic corollary (a) — no @{term "det_mttm M"} hypothesis, no
  determinism asserted of the result.  The growth hypothesis absorbs the
  linear-in-@{text "|w|"} overhead into @{text "T(|w|)/(2q)"}, so the Form-1
  bound's coefficient-@{text 1} linear term (the encoder pass @{term "length w"}
  plus the storage-tape rewind, and --- unlike the transpose's coefficient-@{text 2}
  @{term "2 * length w"} --- no input rewind) drops out and the textbook bound
  @{term "T (length w) div q + K"} follows.  Reuses the faithful Form-1 raw base
  @{thm[source] linear_speedup_form_1_raw_nae}, so the plant wrap carries both
  HU 12.3 (this, general super-linear @{text T}) and HU 12.4 (the tight
  @{text "(1+\<epsilon>)n"} linear-@{text T} case above).\<close>

theorem linear_speedup_HU_12_3_nae:
  fixes M :: "('q, 'a) mttm"
    and T :: "nat \<Rightarrow> nat"
    and q :: nat
  assumes wf:        "well_formed_mttm M"
      and growth:    "\<forall>d. \<exists>N. \<forall>n. N \<le> n \<longrightarrow> d * n \<le> T n"
      and q_pos:     "0 < q"
      and c_large:   "16 * q \<le> card (UNIV :: ('c :: enum) set)"
      and k2:        "2 \<le> k_tm M"
  obtains K N0 :: nat
  where "valid_mttm
          (encoding_wrap
             (alphabet_enlarge M
                :: ('q \<times> ('a, 'c) ae_stage, 'c \<Rightarrow> 'a) mttm)
             (ae_pack (bl_tm M) :: 'a list \<Rightarrow> ('c \<Rightarrow> 'a))
             (card (UNIV :: 'c set))
             (Sigma_tm M))"
    and "Lang_user_wrap
          (encoding_wrap
             (alphabet_enlarge M
                :: ('q \<times> ('a, 'c) ae_stage, 'c \<Rightarrow> 'a) mttm)
             (ae_pack (bl_tm M) :: 'a list \<Rightarrow> ('c \<Rightarrow> 'a))
             (card (UNIV :: 'c set))
             (Sigma_tm M))
         = Lang_mttm M"
    and "\<forall>w. set w \<subseteq> Sigma_tm M
              \<longrightarrow> N0 \<le> length w
              \<longrightarrow> accepts_in_time_mttm M w (T (length w))
              \<longrightarrow> accepts_in_time_user_wrap
                    (encoding_wrap
                       (alphabet_enlarge M
                          :: ('q \<times> ('a, 'c) ae_stage, 'c \<Rightarrow> 'a) mttm)
                       (ae_pack (bl_tm M) :: 'a list \<Rightarrow> ('c \<Rightarrow> 'a))
                       (card (UNIV :: 'c set))
                       (Sigma_tm M))
                    w
                    (T (length w) div q + K)"
proof -
  let ?M' = "alphabet_enlarge M
              :: ('q \<times> ('a, 'c) ae_stage, 'c \<Rightarrow> 'a) mttm"
  let ?c = "card (UNIV :: 'c set)"
  let ?pack = "ae_pack (bl_tm M) :: 'a list \<Rightarrow> ('c \<Rightarrow> 'a)"
  let ?M'' = "encoding_wrap ?M' ?pack ?c (Sigma_tm M)"

  have c_pos: "0 < ?c"
    using c_large q_pos by linarith

  \<comment> \<open>The AE constants are literal (\<open>\<alpha> = 2\<close>, \<open>f = 4\<close>); pinned to named
     locals so the superlinear absorption below reads unchanged.\<close>
  obtain \<alpha> f :: nat where alpha2: "\<alpha> = (2::nat)" and f4: "f = (4::nat)"
    by blast
  have wf_M'':   "valid_mttm ?M''"
    and lang_M'': "Lang_user_wrap ?M'' = Lang_mttm M"
    and time_F1:  "\<forall>w. set w \<subseteq> Sigma_tm M
                        \<longrightarrow> accepts_in_time_mttm M w (T (length w))
                        \<longrightarrow> accepts_in_time_user_wrap ?M'' w
                              (length w
                               + (length w + ?c - 1) div ?c
                               + 5
                               + \<alpha> * ((length w + ?c - 1) div ?c)
                               + 8 * ((T (length w) + ?c - 1) div ?c)
                               + f)"
    unfolding alpha2 f4
    by (rule linear_speedup_form_1_raw_nae[OF wf c_pos k2])+

  have user_mono:
    "\<And>w t\<^sub>1 t\<^sub>2. accepts_in_time_user_wrap ?M'' w t\<^sub>1 \<Longrightarrow> t\<^sub>1 \<le> t\<^sub>2
                  \<Longrightarrow> accepts_in_time_user_wrap ?M'' w t\<^sub>2"
    unfolding accepts_in_time_user_wrap_def accepts_in_time_mttm_def
    by (meson le_trans)

  define d :: nat where "d = 2 * q * (2 + \<alpha>)"
  obtain N :: nat where N_growth: "\<forall>n. N \<le> n \<longrightarrow> d * n \<le> T n"
    using growth by blast

  define K :: nat where "K = 14 + \<alpha> + f"
  define N0 :: nat where "N0 = N"

  have time_HU_12_3:
    "\<forall>w. set w \<subseteq> Sigma_tm M
            \<longrightarrow> N0 \<le> length w
            \<longrightarrow> accepts_in_time_mttm M w (T (length w))
            \<longrightarrow> accepts_in_time_user_wrap ?M'' w
                  (T (length w) div q + K)"
  proof (intro allI impI)
    fix w :: "'a list"
    assume w_sub: "set w \<subseteq> Sigma_tm M"
       and n_ge_N0: "N0 \<le> length w"
       and accepts_M: "accepts_in_time_mttm M w (T (length w))"

    let ?n = "length w"
    let ?B1 = "?n + (?n + ?c - 1) div ?c + 5
                + \<alpha> * ((?n + ?c - 1) div ?c)
                + 8 * ((T ?n + ?c - 1) div ?c) + f"

    \<comment> \<open>Form-1's bound applies to @{term w}.\<close>
    have form_1_accepts: "accepts_in_time_user_wrap ?M'' w ?B1"
      using time_F1 w_sub accepts_M by blast

    \<comment> \<open>Ceiling-via-floor:  \<open>(x + c - 1) div c \<le> x div c + 1\<close>.\<close>
    have ceil_le: "(x + ?c - 1) div ?c \<le> x div ?c + 1" for x :: nat
    proof -
      have a: "x + ?c - 1 \<le> x + ?c" by simp
      have b: "(x + ?c) div ?c = x div ?c + 1"
        using c_pos by (simp add: div_add_self2)
      from a have "(x + ?c - 1) div ?c \<le> (x + ?c) div ?c"
        by (rule div_le_mono)
      with b show ?thesis by simp
    qed

    \<comment> \<open>Consequences of @{thm[source] ceil_le}, mirroring HU 12.4.\<close>
    have base_ceil_le: "(?n + ?c - 1) div ?c \<le> ?n div ?c + 1"
      by (rule ceil_le)
    have alpha_ceil_le:
      "\<alpha> * ((?n + ?c - 1) div ?c) \<le> \<alpha> * (?n div ?c) + \<alpha>"
    proof -
      have "\<alpha> * ((?n + ?c - 1) div ?c) \<le> \<alpha> * (?n div ?c + 1)"
        using base_ceil_le by (rule mult_le_mono2)
      also have "\<dots> = \<alpha> * (?n div ?c) + \<alpha>" by simp
      finally show ?thesis .
    qed
    have eight_T_ceil_le:
      "8 * ((T ?n + ?c - 1) div ?c) \<le> 8 * (T ?n div ?c) + 8"
    proof -
      have "8 * ((T ?n + ?c - 1) div ?c) \<le> 8 * (T ?n div ?c + 1)"
        using ceil_le[of "T ?n"] by (rule mult_le_mono2)
      also have "\<dots> = 8 * (T ?n div ?c) + 8" by simp
      finally show ?thesis .
    qed

    \<comment> \<open>@{text c_large} absorption: from @{text "16 * q \<le> c"} derive
       @{text "8 * (T n div c) \<le> T n div (2 * q)"}.\<close>
    have eight_T_to_2q: "8 * (T ?n div ?c) \<le> T ?n div (2 * q)"
    proof -
      let ?Y = "T ?n div ?c"
      let ?Z = "8 * ?Y"
      have c_n: "?c * ?Y \<le> T ?n"
        using mult_div_mod_eq[of ?c "T ?n"] by linarith
      have c16: "16 * q * ?Y \<le> ?c * ?Y"
        using c_large by (rule mult_le_mono1)
      have step1: "16 * q * ?Y \<le> T ?n" using c16 c_n by linarith
      have assoc: "16 * q * ?Y = ?Z * (2 * q)" by simp
      have step2: "?Z * (2 * q) \<le> T ?n" using step1 assoc by linarith
      have q2_pos: "0 < 2 * q" using q_pos by linarith
      show ?thesis using step2 q2_pos
        by (simp add: less_eq_div_iff_mult_less_eq)
    qed

    \<comment> \<open>Growth at @{term "?n"}: from @{text "N0 \<le> ?n"} and @{text "N0 = N"}.\<close>
    have growth_at_n: "d * ?n \<le> T ?n"
    proof -
      have "N \<le> ?n" using n_ge_N0 unfolding N0_def by simp
      then show ?thesis using N_growth by blast
    qed

    \<comment> \<open>Convert to the @{text "T n div (2 * q)"} form.\<close>
    have linear_to_2q: "(2 + \<alpha>) * ?n \<le> T ?n div (2 * q)"
    proof -
      have d_assoc: "d * ?n = ((2 + \<alpha>) * ?n) * (2 * q)"
        unfolding d_def by (simp add: algebra_simps)
      have step1: "((2 + \<alpha>) * ?n) * (2 * q) \<le> T ?n"
        using growth_at_n d_assoc by linarith
      have q2_pos: "0 < 2 * q" using q_pos by linarith
      show ?thesis using step1 q2_pos
        by (simp add: less_eq_div_iff_mult_less_eq)
    qed

    \<comment> \<open>Universal nat-fact: @{text "2 * (T n div (2 * q)) \<le> T n div q"}.\<close>
    have double_div: "2 * (T ?n div (2 * q)) \<le> T ?n div q"
    proof -
      let ?D = "T ?n div (2 * q)"
      have q2_n: "(2 * q) * ?D \<le> T ?n"
        using mult_div_mod_eq[of "2 * q" "T ?n"] by linarith
      have rebracket: "(2 * q) * ?D = (2 * ?D) * q"
        by (simp add: ac_simps)
      have step: "(2 * ?D) * q \<le> T ?n"
        using q2_n rebracket by linarith
      show ?thesis using step q_pos
        by (simp add: less_eq_div_iff_mult_less_eq)
    qed

    \<comment> \<open>Arithmetic discharge: @{text "?B1 \<le> T ?n div q + K"}.  The plant
       wrap's leading linear term is @{text "n"} plus the storage-rewind ceiling
       @{text "(n + c - 1) div c"} (coefficient @{text 1}, no input rewind);
       the ceiling is bounded by @{text "n + 1"} via @{thm[source] ceil_le}, so
       the same growth absorption as the transpose's @{text "2 \<cdot> n"} applies.\<close>
    have B1_le_target: "?B1 \<le> T ?n div q + K"
    proof -
      have n_div_n: "?n div ?c \<le> ?n" by (rule div_le_dividend)
      have ceil_n_bound: "(?n + ?c - 1) div ?c \<le> ?n + 1"
        using base_ceil_le n_div_n by linarith
      have alpha_n_div: "\<alpha> * (?n div ?c) \<le> \<alpha> * ?n"
        using n_div_n by (rule mult_le_mono2)
      have b_n: "\<alpha> * ((?n + ?c - 1) div ?c) \<le> \<alpha> * ?n + \<alpha>"
        using alpha_ceil_le alpha_n_div by linarith
      have eight_T_full:
        "8 * ((T ?n + ?c - 1) div ?c) \<le> T ?n div (2 * q) + 8"
        using eight_T_ceil_le eight_T_to_2q by linarith
      have lin_split: "?n + ?n + \<alpha> * ?n \<le> T ?n div (2 * q)"
      proof -
        have eq: "?n + ?n + \<alpha> * ?n = (2 + \<alpha>) * ?n"
          by (simp add: algebra_simps)
        show ?thesis unfolding eq by (rule linear_to_2q)
      qed
      show ?thesis
        using b_n eight_T_full lin_split double_div K_def ceil_n_bound
        by linarith
    qed

    show "accepts_in_time_user_wrap ?M'' w (T ?n div q + K)"
      using user_mono[OF form_1_accepts B1_le_target] .
  qed

  show ?thesis
  proof (rule that)
    show "valid_mttm ?M''" by (rule wf_M'')
    show "Lang_user_wrap ?M'' = Lang_mttm M" by (rule lang_M'')
    show "\<forall>w. set w \<subseteq> Sigma_tm M
                \<longrightarrow> N0 \<le> length w
                \<longrightarrow> accepts_in_time_mttm M w (T (length w))
                \<longrightarrow> accepts_in_time_user_wrap ?M'' w
                      (T (length w) div q + K)"
      by (rule time_HU_12_3)
  qed
qed


text \<open>Deterministic specialisation of @{thm[source] linear_speedup_HU_12_3_nae}
  (Theorem 12.3 proper, faithful @{text k}-tape): adds determinism
  preservation on top of the nondeterministic super-linear-case corollary.\<close>

theorem linear_speedup_HU_12_3_dae:
  fixes M :: "('q, 'a) mttm"
    and T :: "nat \<Rightarrow> nat"
    and q :: nat
  assumes wf:        "well_formed_mttm M"
      and det:       "det_mttm M"
      and growth:    "\<forall>d. \<exists>N. \<forall>n. N \<le> n \<longrightarrow> d * n \<le> T n"
      and q_pos:     "0 < q"
      and c_large:   "16 * q \<le> card (UNIV :: ('c :: enum) set)"
      and k2:        "2 \<le> k_tm M"
  obtains K N0 :: nat
  where "valid_mttm
          (encoding_wrap
             (alphabet_enlarge M
                :: ('q \<times> ('a, 'c) ae_stage, 'c \<Rightarrow> 'a) mttm)
             (ae_pack (bl_tm M) :: 'a list \<Rightarrow> ('c \<Rightarrow> 'a))
             (card (UNIV :: 'c set))
             (Sigma_tm M))"
    and "det_mttm
          (encoding_wrap
             (alphabet_enlarge M
                :: ('q \<times> ('a, 'c) ae_stage, 'c \<Rightarrow> 'a) mttm)
             (ae_pack (bl_tm M) :: 'a list \<Rightarrow> ('c \<Rightarrow> 'a))
             (card (UNIV :: 'c set))
             (Sigma_tm M))"
    and "Lang_user_wrap
          (encoding_wrap
             (alphabet_enlarge M
                :: ('q \<times> ('a, 'c) ae_stage, 'c \<Rightarrow> 'a) mttm)
             (ae_pack (bl_tm M) :: 'a list \<Rightarrow> ('c \<Rightarrow> 'a))
             (card (UNIV :: 'c set))
             (Sigma_tm M))
         = Lang_mttm M"
    and "\<forall>w. set w \<subseteq> Sigma_tm M
              \<longrightarrow> N0 \<le> length w
              \<longrightarrow> accepts_in_time_mttm M w (T (length w))
              \<longrightarrow> accepts_in_time_user_wrap
                    (encoding_wrap
                       (alphabet_enlarge M
                          :: ('q \<times> ('a, 'c) ae_stage, 'c \<Rightarrow> 'a) mttm)
                       (ae_pack (bl_tm M) :: 'a list \<Rightarrow> ('c \<Rightarrow> 'a))
                       (card (UNIV :: 'c set))
                       (Sigma_tm M))
                    w
                    (T (length w) div q + K)"
proof -
  from wf have vM: "valid_mttm M"
           and le_neq_bl: "le_tm M \<noteq> bl_tm M"
    by auto
  let ?M' = "alphabet_enlarge M
              :: ('q \<times> ('a, 'c) ae_stage, 'c \<Rightarrow> 'a) mttm"
  let ?c = "card (UNIV :: 'c set)"
  let ?pack = "ae_pack (bl_tm M) :: 'a list \<Rightarrow> ('c \<Rightarrow> 'a)"
  let ?M'' = "encoding_wrap ?M' ?pack ?c (Sigma_tm M)"

  have c_pos: "0 < ?c"
  proof -
    have "0 < 16 * q" using q_pos by simp
    thus ?thesis using c_large by linarith
  qed

  obtain K N0 :: nat where
      v: "valid_mttm ?M''"
    and l: "Lang_user_wrap ?M'' = Lang_mttm M"
    and tm: "\<forall>w. set w \<subseteq> Sigma_tm M
                \<longrightarrow> N0 \<le> length w
                \<longrightarrow> accepts_in_time_mttm M w (T (length w))
                \<longrightarrow> accepts_in_time_user_wrap ?M'' w
                      (T (length w) div q + K)"
    by (rule linear_speedup_HU_12_3_nae[OF wf growth q_pos c_large k2])

  have vM': "valid_mttm ?M'" by (rule alphabet_enlarge_wf[OF vM])
  have detM': "det_mttm ?M'"
    unfolding det_mttm_def delta_tm_alphabet_enlarge
    using alphabet_enlarge_delta_functional[OF vM det le_neq_bl] by blast
  have finSigma: "finite (Sigma_tm M)"
    using valid_mttm_Sigma_sub_Gamma[OF vM]
          valid_mttm_finite_Gamma[OF vM]
          rev_finite_subset by blast
  have det_wrap: "det_mttm ?M''"
    by (rule wrap_det[OF vM' detM' finSigma c_pos])

  show ?thesis
  proof (rule that)
    show "valid_mttm ?M''" by (rule v)
    show "det_mttm ?M''" by (rule det_wrap)
    show "Lang_user_wrap ?M'' = Lang_mttm M" by (rule l)
    show "\<forall>w. set w \<subseteq> Sigma_tm M
                \<longrightarrow> N0 \<le> length w
                \<longrightarrow> accepts_in_time_mttm M w (T (length w))
                \<longrightarrow> accepts_in_time_user_wrap ?M'' w
                      (T (length w) div q + K)"
      by (rule tm)
  qed
qed

end
