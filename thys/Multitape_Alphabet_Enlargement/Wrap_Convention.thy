theory Wrap_Convention
  imports Wrap_Speedup "Multitape_TM_Substrate.Multitape_Time_Convention"
begin

section \<open>The linear-speedup headlines in Hopcroft--Ullman's
  time-complexity convention\<close>

text \<open>The @{theory Multitape_Alphabet_Enlargement.Wrap_Speedup} headlines
  \<open>linear_speedup_HU_12_3\<close> / \<open>linear_speedup_HU_12_4\<close> prove a \<^emph>\<open>raw\<close>
  bound: a per-run additive constant \<open>K\<close> (and for 12.3 a bare length
  threshold \<open>N0\<close>), gated on the input run itself completing within
  \<open>T\<close>.  Hopcroft and Ullman state 12.3 / 12.4 in a \<^emph>\<open>time-complexity
  convention\<close> \<^cite>\<open>\<open>p.~291\<close> in "Hopcroft1979:introduction"\<close>: a machine
  ``runs in time \<open>cT(n)\<close>'' means it accepts every
  word of its language within @{text \<open>max(n + 1, ceil(cT(n)))\<close>} steps, the
  @{text \<open>n + 1\<close>} floor being the cost of reading the input.  On our
  substrate the floor is @{text \<open>n + 2\<close>} (the left endmarker is read
  before the first input symbol); this is exactly the
  @{const time_bounded_conv} predicate of
  @{theory Multitape_TM_Substrate.Multitape_Time_Convention}.

  This theory restates the two headlines in that convention.  The
  wrapped machine is a genuine @{type mttm}, and its user-facing
  language / timing (@{const Lang_user_wrap} / @{const
  accepts_in_time_user_wrap}) are the @{const Lang_mttm} / @{const
  accepts_in_time_mttm} of the wrap read through @{const Raw}, so
  @{const time_bounded_conv} applied to the wrap \<^emph>\<open>is\<close> the user-level
  convention statement (\<open>Lang_mttm_encoding_wrap_ex_Raw\<close> below is the
  bridge).  The two cases diverge:

  \<^item> \<^bold>\<open>12.4 (linear \<open>T\<close>).\<close>  The raw bound @{text \<open>|w| + |w| div q + K\<close>}
    already holds for \<^emph>\<open>all\<close> lengths, so the convention statement is the
    max-floored restatement, provided \<open>M\<close> runs in time \<open>T\<close> on its
    language.  The additive \<open>K\<close> cannot be folded into a smaller
    @{text \<open>eps = 1 / q\<close>} on all inputs: the clean form
    @{term \<open>time_bounded_conv M (\<lambda>n. n + n div q)\<close>} is provably
    \<^emph>\<open>unattainable\<close> in general (the counterexample
    \<open>clean_convention_unattainable\<close> in
    @{theory Multitape_TM_Substrate.Multitape_Time_Convention} --- a valid machine can
    accept its language yet exceed the floor \<open>n + 2\<close> on its shortest input,
    as the wrap's own setup phases do at \<open>n = 0\<close>).  The obstruction is the
    finite-prefix \<^emph>\<open>band\<close>: an outer @{const finite_patch} cleanup scans
    proportionally to its cutoff, so its overhead never drops below
    \<open>eps\<close>, and shaving the rewind only narrows the band.  It is
    \<^emph>\<open>not\<close> the origin rewind of
    the faithful \<open>k\<close>-tape construction (a distinct obstruction).  So
    \<open>K\<close> is kept explicit.

  \<^item> \<^bold>\<open>12.3 (superlinear \<open>T\<close>).\<close>  Here superlinear growth dominates any
    linear-in-cutoff cost, so the @{const finite_patch} small-input
    cleanup (\<open>time_cleanup\<close> on the table @{term \<open>\<lambda>w. w \<in> Lang_mttm M\<close>})
    and the additive constant both wash out into a slightly larger
    multiplicative constant --- a clean @{text \<open>ceil(c T(n))\<close>} convention
    bound with no residual constant.

  The raw @{text \<open>+ K\<close>} theorems remain the explicit-constant corollaries
  (nothing is lost).\<close>

subsection \<open>Bridge: an accepted word of the wrap is @{const Raw}-encoded\<close>

text \<open>Every word of @{const Lang_mttm} of an @{const encoding_wrap} is
  @{term \<open>map Raw w\<close>} for a user word \<open>w\<close>, because the wrap's input
  alphabet is @{term \<open>Raw ` \<Sigma>u\<close>}.  This lets a @{const time_bounded_conv}
  goal over the wrap's @{const Lang_mttm} be discharged through the
  user-level @{const accepts_in_time_user_wrap} bound the raw headlines
  supply, and conversely.\<close>

lemma Lang_mttm_encoding_wrap_ex_Raw:
  assumes "v \<in> Lang_mttm (encoding_wrap M pack c \<Sigma>u)"
  shows "\<exists>w. v = map Raw w \<and> w \<in> Lang_user_wrap (encoding_wrap M pack c \<Sigma>u)"
proof -
  let ?W = "encoding_wrap M pack c \<Sigma>u"
  have sv: "set v \<subseteq> Raw ` \<Sigma>u"
    using assms unfolding Lang_mttm_def by simp
  have "\<forall>x\<in>set v. \<exists>y. x = Raw y" using sv by auto
  then obtain w where vw: "v = map Raw w" by (metis ex_map_conv)
  have "map Raw w \<in> Lang_mttm ?W" using assms vw by simp
  hence "w \<in> Lang_user_wrap ?W" unfolding Lang_user_wrap_def by simp
  thus ?thesis using vw by blast
qed

subsection \<open>Arithmetic core of the superlinear absorption\<close>

text \<open>The one inequality that makes 12.3 clean where 12.4 is not: a
  constant \<open>C\<close> is absorbed by dropping the speedup denominator from
  \<open>q + 1\<close> to \<open>q\<close>, provided the numerator \<open>a\<close> is at least
  \<open>q (q + 1) C\<close>.  In use \<open>a = T n\<close>, and the superlinear growth of \<open>T\<close>
  makes the premise hold for all large \<open>n\<close> --- including \<open>C = K + 2 N1
  + 4\<close> where \<open>N1\<close> is the finite-control cutoff, because the numerator
  grows superlinearly in \<open>n\<close> while \<open>C\<close> grows only linearly in \<open>N1\<close>.\<close>

lemma div_absorb_step:
  fixes a q C :: nat
  assumes q_pos: "0 < q" and big: "q * (q + 1) * C \<le> a"
  shows "a div (q + 1) + C \<le> a div q"
proof -
  have qne: "q \<noteq> 0" using q_pos by simp
  have q1ne: "q + 1 \<noteq> 0" by simp
  have qC: "q * C \<le> a div (q + 1)"
  proof -
    have "(q + 1) * (q * C) \<le> a" using big by (simp add: algebra_simps)
    hence "((q + 1) * (q * C)) div (q + 1) \<le> a div (q + 1)" by (rule div_le_mono)
    moreover have "((q + 1) * (q * C)) div (q + 1) = q * C"
      by (metis nonzero_mult_div_cancel_left q1ne)
    ultimately show ?thesis by simp
  qed
  have "q * (a div (q + 1) + C) = q * (a div (q + 1)) + q * C"
    by (simp add: algebra_simps)
  also have "\<dots> \<le> q * (a div (q + 1)) + a div (q + 1)" using qC by simp
  also have "\<dots> = (q + 1) * (a div (q + 1))" by (simp add: algebra_simps)
  also have "\<dots> \<le> a" by (metis mult.commute div_times_less_eq_dividend)
  finally have le_a: "q * (a div (q + 1) + C) \<le> a" .
  hence "(q * (a div (q + 1) + C)) div q \<le> a div q" by (rule div_le_mono)
  moreover have "(q * (a div (q + 1) + C)) div q = a div (q + 1) + C"
    by (metis nonzero_mult_div_cancel_left qne)
  ultimately show ?thesis by simp
qed

subsection \<open>HU 12.4 in the convention (linear \<open>T\<close>)\<close>

text \<open>The nondeterministic linear-\<open>T\<close> headline, restated as a
  @{const time_bounded_conv} bound.  The extra hypothesis over the raw
  @{thm[source] linear_speedup_HU_12_4_nae} is \<open>Mtime\<close>: \<open>M\<close> accepts every
  word of its language within \<open>T\<close> --- i.e. \<open>L(M)\<close> \<^emph>\<open>is\<close> a \<open>T\<close>-time
  language, the textbook premise.  The bound @{term \<open>\<lambda>n. n + n div q + K\<close>}
  is the raw @{text \<open>+ K\<close>} constant read in the @{text \<open>max(n + 2, ...)\<close>}
  convention.\<close>

theorem linear_speedup_HU_12_4_nae_conv:
  fixes M :: "('q, 'a) mttm"
    and T :: "nat \<Rightarrow> nat"
    and d_0 b q :: nat
  assumes wf:        "well_formed_mttm M"
      and Mtime:     "\<And>w. w \<in> Lang_mttm M \<Longrightarrow> accepts_in_time_mttm M w (T (length w))"
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
         \<longrightarrow> time_bounded_conv
               (encoding_wrap
                  (alphabet_enlarge M
                     :: ('q \<times> ('a, 'c) ae_stage, 'c \<Rightarrow> 'a) mttm)
                  (ae_pack (bl_tm M) :: 'a list \<Rightarrow> ('c \<Rightarrow> 'a))
                  (card (UNIV :: 'c set))
                  (Sigma_tm M))
               (\<lambda>n. n + n div q + (28 + 8 * d_0 + 8 * b))"
proof -
  let ?W = "encoding_wrap
              (alphabet_enlarge M
                 :: ('q \<times> ('a, 'c) ae_stage, 'c \<Rightarrow> 'a) mttm)
              (ae_pack (bl_tm M) :: 'a list \<Rightarrow> ('c \<Rightarrow> 'a))
              (card (UNIV :: 'c set))
              (Sigma_tm M)"
  obtain \<alpha> K :: nat where alpha2: "\<alpha> = (2::nat)"
    and Kdef: "K = 28 + 8 * d_0 + 8 * b" by blast
  have V: "valid_mttm ?W"
    and L: "Lang_user_wrap ?W = Lang_mttm M"
    and Tb': "q * (3 + 8 * d_0) \<le> card (UNIV :: 'c set)
          \<longrightarrow> (\<forall>w. set w \<subseteq> Sigma_tm M
                    \<longrightarrow> accepts_in_time_mttm M w (T (length w))
                    \<longrightarrow> accepts_in_time_user_wrap ?W w
                          (length w + length w div q + (28 + 8 * d_0 + 8 * b)))"
    by (rule linear_speedup_HU_12_4_nae[OF wf T_linear q_pos c_pos k2])+
  have e: "(1::nat) + \<alpha> + 8 * d_0 = 3 + 8 * d_0" using alpha2 by simp
  have Tb: "q * (1 + \<alpha> + 8 * d_0) \<le> card (UNIV :: 'c set)
          \<longrightarrow> (\<forall>w. set w \<subseteq> Sigma_tm M
                    \<longrightarrow> accepts_in_time_mttm M w (T (length w))
                    \<longrightarrow> accepts_in_time_user_wrap ?W w
                          (length w + length w div q + K))"
    unfolding e Kdef by (rule Tb')
  have conv: "q * (1 + \<alpha> + 8 * d_0) \<le> card (UNIV :: 'c set)
               \<longrightarrow> time_bounded_conv ?W (\<lambda>n. n + n div q + K)"
  proof
    assume cL: "q * (1 + \<alpha> + 8 * d_0) \<le> card (UNIV :: 'c set)"
    show "time_bounded_conv ?W (\<lambda>n. n + n div q + K)"
      unfolding time_bounded_conv_def
    proof
      fix v assume vW: "v \<in> Lang_mttm ?W"
      then obtain w where vmap: "v = map Raw w" and wU: "w \<in> Lang_user_wrap ?W"
        using Lang_mttm_encoding_wrap_ex_Raw by blast
      from wU L have wM: "w \<in> Lang_mttm M" by simp
      hence wSg: "set w \<subseteq> Sigma_tm M" unfolding Lang_mttm_def by simp
      from wM have accM: "accepts_in_time_mttm M w (T (length w))" by (rule Mtime)
      have "accepts_in_time_user_wrap ?W w (length w + length w div q + K)"
        using Tb cL wSg accM by blast
      hence "accepts_in_time_mttm ?W v (length w + length w div q + K)"
        using vmap unfolding accepts_in_time_user_wrap_def by simp
      hence "accepts_in_time_mttm ?W v (length v + length v div q + K)"
        using vmap by simp
      thus "accepts_in_time_mttm ?W v
              (max (length v + 2) ((\<lambda>n. n + n div q + K) (length v)))"
        by (auto elim: accepts_in_time_mttm_mono)
    qed
  qed
  show "valid_mttm ?W" by (rule V)
  show "Lang_user_wrap ?W = Lang_mttm M" by (rule L)
  show "q * (3 + 8 * d_0) \<le> card (UNIV :: 'c set)
         \<longrightarrow> time_bounded_conv ?W (\<lambda>n. n + n div q + (28 + 8 * d_0 + 8 * b))"
  proof -
    have s0: "(3::nat) + 8 * d_0 = 1 + \<alpha> + 8 * d_0" using alpha2 by simp
    show ?thesis unfolding s0 Kdef[symmetric] by (rule conv)
  qed
qed

text \<open>The nondeterministic linear-\<open>T\<close> headline in the \<^emph>\<open>eventual\<close>,
  constant-free form: past an explicit input-length threshold the wrap runs
  in \<open>n + n div q\<close> exactly --- the additive \<open>K\<close> of
  @{thm[source] linear_speedup_HU_12_4_nae_conv} is gone, at the cost of a
  hypothesis \<open>q\<cdot>(q+1)\<cdot>K \<le> length v\<close> instead of the convention
  floor.  This is the honest \<open>(1+\<epsilon>)\<cdot>n\<close> shape (with
  \<open>\<epsilon> = 1/q\<close>): clean coefficient, no residual constant, but only
  for long enough inputs --- the small-input band is not covered (it cannot
  be, without the non-effective finite-exceptions table; see the counterexample
  \<open>clean_convention_unattainable\<close>).
  Proof: run @{thm[source] linear_speedup_HU_12_4_nae} one denominator tighter
  (at \<open>q+1\<close>), then absorb \<open>K\<close> into the extra \<open>div\<close>-slack via
  @{thm[source] div_absorb_step} once \<open>q\<cdot>(q+1)\<cdot>K \<le> length v\<close> ---
  the same inequality that makes the superlinear 12.3 constant-free, here read
  in the linear regime as an explicit threshold rather than an absorbed
  constant.  With \<open>K\<close> now the literal \<open>28 + 8 d_0 + 8 b\<close>, the crossover
  threshold is the closed formula \<open>q\<cdot>(q+1)\<cdot>(28 + 8 d_0 + 8 b)\<close> ---
  quadratic in \<open>q\<close> (i.e. \<open>O(1/\<epsilon>\<^sup>2)\<close>), and linear in the input
  machine's time-bound constants \<open>d_0, b\<close>.\<close>

theorem linear_speedup_HU_12_4_nae_eventual:
  fixes M :: "('q, 'a) mttm"
    and T :: "nat \<Rightarrow> nat"
    and d_0 b q :: nat
  assumes wf:        "well_formed_mttm M"
      and Mtime:     "\<And>w. w \<in> Lang_mttm M \<Longrightarrow> accepts_in_time_mttm M w (T (length w))"
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
    and "(q + 1) * (3 + 8 * d_0) \<le> card (UNIV :: 'c set)
         \<longrightarrow> (\<forall>v \<in> Lang_mttm
                     (encoding_wrap
                        (alphabet_enlarge M
                           :: ('q \<times> ('a, 'c) ae_stage, 'c \<Rightarrow> 'a) mttm)
                        (ae_pack (bl_tm M) :: 'a list \<Rightarrow> ('c \<Rightarrow> 'a))
                        (card (UNIV :: 'c set))
                        (Sigma_tm M)).
                q * (q + 1) * (28 + 8 * d_0 + 8 * b) \<le> length v
                \<longrightarrow> accepts_in_time_mttm
                      (encoding_wrap
                         (alphabet_enlarge M
                            :: ('q \<times> ('a, 'c) ae_stage, 'c \<Rightarrow> 'a) mttm)
                         (ae_pack (bl_tm M) :: 'a list \<Rightarrow> ('c \<Rightarrow> 'a))
                         (card (UNIV :: 'c set))
                         (Sigma_tm M))
                      v
                      (length v + length v div q))"
proof -
  let ?W = "encoding_wrap
              (alphabet_enlarge M
                 :: ('q \<times> ('a, 'c) ae_stage, 'c \<Rightarrow> 'a) mttm)
              (ae_pack (bl_tm M) :: 'a list \<Rightarrow> ('c \<Rightarrow> 'a))
              (card (UNIV :: 'c set))
              (Sigma_tm M)"
  have q1_pos: "0 < q + 1" by simp
  obtain \<alpha> K :: nat where alpha2: "\<alpha> = (2::nat)"
    and Kdef: "K = 28 + 8 * d_0 + 8 * b" by blast
  have V: "valid_mttm ?W"
    and L: "Lang_user_wrap ?W = Lang_mttm M"
    and Tb': "(q + 1) * (3 + 8 * d_0) \<le> card (UNIV :: 'c set)
          \<longrightarrow> (\<forall>w. set w \<subseteq> Sigma_tm M
                    \<longrightarrow> accepts_in_time_mttm M w (T (length w))
                    \<longrightarrow> accepts_in_time_user_wrap ?W w
                          (length w + length w div (q + 1) + (28 + 8 * d_0 + 8 * b)))"
    by (rule linear_speedup_HU_12_4_nae[where q = "q + 1", OF wf T_linear q1_pos c_pos k2])+
  have e: "(1::nat) + \<alpha> + 8 * d_0 = 3 + 8 * d_0" using alpha2 by simp
  have Tb: "(q + 1) * (1 + \<alpha> + 8 * d_0) \<le> card (UNIV :: 'c set)
          \<longrightarrow> (\<forall>w. set w \<subseteq> Sigma_tm M
                    \<longrightarrow> accepts_in_time_mttm M w (T (length w))
                    \<longrightarrow> accepts_in_time_user_wrap ?W w
                          (length w + length w div (q + 1) + K))"
    unfolding e Kdef by (rule Tb')
  have ev: "(q + 1) * (1 + \<alpha> + 8 * d_0) \<le> card (UNIV :: 'c set)
             \<longrightarrow> (\<forall>v \<in> Lang_mttm ?W. q * (q + 1) * K \<le> length v
                    \<longrightarrow> accepts_in_time_mttm ?W v (length v + length v div q))"
  proof
    assume cL: "(q + 1) * (1 + \<alpha> + 8 * d_0) \<le> card (UNIV :: 'c set)"
    show "\<forall>v \<in> Lang_mttm ?W. q * (q + 1) * K \<le> length v
            \<longrightarrow> accepts_in_time_mttm ?W v (length v + length v div q)"
    proof
      fix v assume vW: "v \<in> Lang_mttm ?W"
      show "q * (q + 1) * K \<le> length v
              \<longrightarrow> accepts_in_time_mttm ?W v (length v + length v div q)"
      proof
        assume lv: "q * (q + 1) * K \<le> length v"
        from vW obtain w where vmap: "v = map Raw w"
          and wU: "w \<in> Lang_user_wrap ?W"
          using Lang_mttm_encoding_wrap_ex_Raw by blast
        from wU L have wM: "w \<in> Lang_mttm M" by simp
        hence wSg: "set w \<subseteq> Sigma_tm M" unfolding Lang_mttm_def by simp
        from wM have accM: "accepts_in_time_mttm M w (T (length w))" by (rule Mtime)
        have lenwv: "length w = length v" using vmap by simp
        have raw: "accepts_in_time_user_wrap ?W w
                     (length w + length w div (q + 1) + K)"
          using Tb cL wSg accM by blast
        have absorb: "length w div (q + 1) + K \<le> length w div q"
          by (rule div_absorb_step[OF q_pos]) (use lv lenwv in simp)
        hence le: "length w + length w div (q + 1) + K
                     \<le> length w + length w div q" by simp
        have "accepts_in_time_mttm ?W (map Raw w)
                (length w + length w div (q + 1) + K)"
          using raw unfolding accepts_in_time_user_wrap_def by simp
        hence "accepts_in_time_mttm ?W (map Raw w) (length w + length w div q)"
          using le by (auto elim: accepts_in_time_mttm_mono)
        thus "accepts_in_time_mttm ?W v (length v + length v div q)"
          by (simp only: vmap length_map)
      qed
    qed
  qed
  show "valid_mttm ?W" by (rule V)
  show "Lang_user_wrap ?W = Lang_mttm M" by (rule L)
  show "(q + 1) * (3 + 8 * d_0) \<le> card (UNIV :: 'c set)
         \<longrightarrow> (\<forall>v \<in> Lang_mttm ?W. q * (q + 1) * (28 + 8 * d_0 + 8 * b) \<le> length v
                \<longrightarrow> accepts_in_time_mttm ?W v (length v + length v div q))"
  proof -
    have s0: "(3::nat) + 8 * d_0 = 1 + \<alpha> + 8 * d_0" using alpha2 by simp
    show ?thesis unfolding s0 Kdef[symmetric] by (rule ev)
  qed
qed

text \<open>The deterministic specialisation: adds the \<open>det\<close> hypothesis on
  \<open>M\<close> and the determinism-preservation conjunct on the wrap, on top of
  @{thm[source] linear_speedup_HU_12_4_nae_conv}.\<close>

theorem linear_speedup_HU_12_4_dae_conv:
  fixes M :: "('q, 'a) mttm"
    and T :: "nat \<Rightarrow> nat"
    and d_0 b q :: nat
  assumes wf:        "well_formed_mttm M"
      and det:       "det_mttm M"
      and Mtime:     "\<And>w. w \<in> Lang_mttm M \<Longrightarrow> accepts_in_time_mttm M w (T (length w))"
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
         \<longrightarrow> time_bounded_conv
               (encoding_wrap
                  (alphabet_enlarge M
                     :: ('q \<times> ('a, 'c) ae_stage, 'c \<Rightarrow> 'a) mttm)
                  (ae_pack (bl_tm M) :: 'a list \<Rightarrow> ('c \<Rightarrow> 'a))
                  (card (UNIV :: 'c set))
                  (Sigma_tm M))
               (\<lambda>n. n + n div q + (28 + 8 * d_0 + 8 * b))"
proof -
  let ?W = "encoding_wrap
              (alphabet_enlarge M
                 :: ('q \<times> ('a, 'c) ae_stage, 'c \<Rightarrow> 'a) mttm)
              (ae_pack (bl_tm M) :: 'a list \<Rightarrow> ('c \<Rightarrow> 'a))
              (card (UNIV :: 'c set))
              (Sigma_tm M)"
  obtain \<alpha> K :: nat where alpha2: "\<alpha> = (2::nat)"
    and Kdef: "K = 28 + 8 * d_0 + 8 * b" by blast
  have V: "valid_mttm ?W"
    and D: "det_mttm ?W"
    and L: "Lang_user_wrap ?W = Lang_mttm M"
    and Tb': "q * (3 + 8 * d_0) \<le> card (UNIV :: 'c set)
          \<longrightarrow> (\<forall>w. set w \<subseteq> Sigma_tm M
                    \<longrightarrow> accepts_in_time_mttm M w (T (length w))
                    \<longrightarrow> accepts_in_time_user_wrap ?W w
                          (length w + length w div q + (28 + 8 * d_0 + 8 * b)))"
    by (rule linear_speedup_HU_12_4_dae[OF wf det T_linear q_pos c_pos k2])+
  have e: "(1::nat) + \<alpha> + 8 * d_0 = 3 + 8 * d_0" using alpha2 by simp
  have Tb: "q * (1 + \<alpha> + 8 * d_0) \<le> card (UNIV :: 'c set)
          \<longrightarrow> (\<forall>w. set w \<subseteq> Sigma_tm M
                    \<longrightarrow> accepts_in_time_mttm M w (T (length w))
                    \<longrightarrow> accepts_in_time_user_wrap ?W w
                          (length w + length w div q + K))"
    unfolding e Kdef by (rule Tb')
  have conv: "q * (1 + \<alpha> + 8 * d_0) \<le> card (UNIV :: 'c set)
               \<longrightarrow> time_bounded_conv ?W (\<lambda>n. n + n div q + K)"
  proof
    assume cL: "q * (1 + \<alpha> + 8 * d_0) \<le> card (UNIV :: 'c set)"
    show "time_bounded_conv ?W (\<lambda>n. n + n div q + K)"
      unfolding time_bounded_conv_def
    proof
      fix v assume vW: "v \<in> Lang_mttm ?W"
      then obtain w where vmap: "v = map Raw w" and wU: "w \<in> Lang_user_wrap ?W"
        using Lang_mttm_encoding_wrap_ex_Raw by blast
      from wU L have wM: "w \<in> Lang_mttm M" by simp
      hence wSg: "set w \<subseteq> Sigma_tm M" unfolding Lang_mttm_def by simp
      from wM have accM: "accepts_in_time_mttm M w (T (length w))" by (rule Mtime)
      have "accepts_in_time_user_wrap ?W w (length w + length w div q + K)"
        using Tb cL wSg accM by blast
      hence "accepts_in_time_mttm ?W v (length w + length w div q + K)"
        using vmap unfolding accepts_in_time_user_wrap_def by simp
      hence "accepts_in_time_mttm ?W v (length v + length v div q + K)"
        using vmap by simp
      thus "accepts_in_time_mttm ?W v
              (max (length v + 2) ((\<lambda>n. n + n div q + K) (length v)))"
        by (auto elim: accepts_in_time_mttm_mono)
    qed
  qed
  show "valid_mttm ?W" by (rule V)
  show "det_mttm ?W" by (rule D)
  show "Lang_user_wrap ?W = Lang_mttm M" by (rule L)
  show "q * (3 + 8 * d_0) \<le> card (UNIV :: 'c set)
         \<longrightarrow> time_bounded_conv ?W (\<lambda>n. n + n div q + (28 + 8 * d_0 + 8 * b))"
  proof -
    have s0: "(3::nat) + 8 * d_0 = 1 + \<alpha> + 8 * d_0" using alpha2 by simp
    show ?thesis unfolding s0 Kdef[symmetric] by (rule conv)
  qed
qed

text \<open>The determinism-preserving eventual form: @{thm[source]
  linear_speedup_HU_12_4_nae_eventual} with the \<open>det\<close> hypothesis and the
  determinism-preservation conjunct, over @{thm[source]
  linear_speedup_HU_12_4_dae}.\<close>

theorem linear_speedup_HU_12_4_dae_eventual:
  fixes M :: "('q, 'a) mttm"
    and T :: "nat \<Rightarrow> nat"
    and d_0 b q :: nat
  assumes wf:        "well_formed_mttm M"
      and det:       "det_mttm M"
      and Mtime:     "\<And>w. w \<in> Lang_mttm M \<Longrightarrow> accepts_in_time_mttm M w (T (length w))"
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
    and "(q + 1) * (3 + 8 * d_0) \<le> card (UNIV :: 'c set)
         \<longrightarrow> (\<forall>v \<in> Lang_mttm
                     (encoding_wrap
                        (alphabet_enlarge M
                           :: ('q \<times> ('a, 'c) ae_stage, 'c \<Rightarrow> 'a) mttm)
                        (ae_pack (bl_tm M) :: 'a list \<Rightarrow> ('c \<Rightarrow> 'a))
                        (card (UNIV :: 'c set))
                        (Sigma_tm M)).
                q * (q + 1) * (28 + 8 * d_0 + 8 * b) \<le> length v
                \<longrightarrow> accepts_in_time_mttm
                      (encoding_wrap
                         (alphabet_enlarge M
                            :: ('q \<times> ('a, 'c) ae_stage, 'c \<Rightarrow> 'a) mttm)
                         (ae_pack (bl_tm M) :: 'a list \<Rightarrow> ('c \<Rightarrow> 'a))
                         (card (UNIV :: 'c set))
                         (Sigma_tm M))
                      v
                      (length v + length v div q))"
proof -
  let ?W = "encoding_wrap
              (alphabet_enlarge M
                 :: ('q \<times> ('a, 'c) ae_stage, 'c \<Rightarrow> 'a) mttm)
              (ae_pack (bl_tm M) :: 'a list \<Rightarrow> ('c \<Rightarrow> 'a))
              (card (UNIV :: 'c set))
              (Sigma_tm M)"
  have q1_pos: "0 < q + 1" by simp
  obtain \<alpha> K :: nat where alpha2: "\<alpha> = (2::nat)"
    and Kdef: "K = 28 + 8 * d_0 + 8 * b" by blast
  have V: "valid_mttm ?W"
    and D: "det_mttm ?W"
    and L: "Lang_user_wrap ?W = Lang_mttm M"
    and Tb': "(q + 1) * (3 + 8 * d_0) \<le> card (UNIV :: 'c set)
          \<longrightarrow> (\<forall>w. set w \<subseteq> Sigma_tm M
                    \<longrightarrow> accepts_in_time_mttm M w (T (length w))
                    \<longrightarrow> accepts_in_time_user_wrap ?W w
                          (length w + length w div (q + 1) + (28 + 8 * d_0 + 8 * b)))"
    by (rule linear_speedup_HU_12_4_dae[where q = "q + 1", OF wf det T_linear q1_pos c_pos k2])+
  have e: "(1::nat) + \<alpha> + 8 * d_0 = 3 + 8 * d_0" using alpha2 by simp
  have Tb: "(q + 1) * (1 + \<alpha> + 8 * d_0) \<le> card (UNIV :: 'c set)
          \<longrightarrow> (\<forall>w. set w \<subseteq> Sigma_tm M
                    \<longrightarrow> accepts_in_time_mttm M w (T (length w))
                    \<longrightarrow> accepts_in_time_user_wrap ?W w
                          (length w + length w div (q + 1) + K))"
    unfolding e Kdef by (rule Tb')
  have ev: "(q + 1) * (1 + \<alpha> + 8 * d_0) \<le> card (UNIV :: 'c set)
             \<longrightarrow> (\<forall>v \<in> Lang_mttm ?W. q * (q + 1) * K \<le> length v
                    \<longrightarrow> accepts_in_time_mttm ?W v (length v + length v div q))"
  proof
    assume cL: "(q + 1) * (1 + \<alpha> + 8 * d_0) \<le> card (UNIV :: 'c set)"
    show "\<forall>v \<in> Lang_mttm ?W. q * (q + 1) * K \<le> length v
            \<longrightarrow> accepts_in_time_mttm ?W v (length v + length v div q)"
    proof
      fix v assume vW: "v \<in> Lang_mttm ?W"
      show "q * (q + 1) * K \<le> length v
              \<longrightarrow> accepts_in_time_mttm ?W v (length v + length v div q)"
      proof
        assume lv: "q * (q + 1) * K \<le> length v"
        from vW obtain w where vmap: "v = map Raw w"
          and wU: "w \<in> Lang_user_wrap ?W"
          using Lang_mttm_encoding_wrap_ex_Raw by blast
        from wU L have wM: "w \<in> Lang_mttm M" by simp
        hence wSg: "set w \<subseteq> Sigma_tm M" unfolding Lang_mttm_def by simp
        from wM have accM: "accepts_in_time_mttm M w (T (length w))" by (rule Mtime)
        have lenwv: "length w = length v" using vmap by simp
        have raw: "accepts_in_time_user_wrap ?W w
                     (length w + length w div (q + 1) + K)"
          using Tb cL wSg accM by blast
        have absorb: "length w div (q + 1) + K \<le> length w div q"
          by (rule div_absorb_step[OF q_pos]) (use lv lenwv in simp)
        hence le: "length w + length w div (q + 1) + K
                     \<le> length w + length w div q" by simp
        have "accepts_in_time_mttm ?W (map Raw w)
                (length w + length w div (q + 1) + K)"
          using raw unfolding accepts_in_time_user_wrap_def by simp
        hence "accepts_in_time_mttm ?W (map Raw w) (length w + length w div q)"
          using le by (auto elim: accepts_in_time_mttm_mono)
        thus "accepts_in_time_mttm ?W v (length v + length v div q)"
          by (simp only: vmap length_map)
      qed
    qed
  qed
  show "valid_mttm ?W" by (rule V)
  show "det_mttm ?W" by (rule D)
  show "Lang_user_wrap ?W = Lang_mttm M" by (rule L)
  show "(q + 1) * (3 + 8 * d_0) \<le> card (UNIV :: 'c set)
         \<longrightarrow> (\<forall>v \<in> Lang_mttm ?W. q * (q + 1) * (28 + 8 * d_0 + 8 * b) \<le> length v
                \<longrightarrow> accepts_in_time_mttm ?W v (length v + length v div q))"
  proof -
    have s0: "(3::nat) + 8 * d_0 = 1 + \<alpha> + 8 * d_0" using alpha2 by simp
    show ?thesis unfolding s0 Kdef[symmetric] by (rule ev)
  qed
qed

subsection \<open>HU 12.3 in the convention (superlinear \<open>T\<close>): the clean bound\<close>

text \<open>The nondeterministic superlinear-\<open>T\<close> headline, restated as a
  \<^emph>\<open>constant-free\<close> @{const time_bounded_conv} bound @{term \<open>\<lambda>n. T n div q\<close>}.
  Unlike 12.4, no additive constant survives: the raw simulation
  constant \<open>K\<close> \<^emph>\<open>and\<close> the finite-control overhead \<open>2 N1 + 4\<close> are both
  absorbed into a slightly smaller speedup denominator (the raw
  construction is run at \<open>q + 1\<close>, the headline states \<open>q\<close>), because
  superlinear \<open>T\<close> makes @{thm[source] div_absorb_step}'s premise
  \<open>q (q + 1) C \<le> T n\<close> hold for all long \<open>n\<close> with \<open>C = K + 2 N1 + 4\<close>.

  The machine is @{const finite_patch} of the wrap under the table
  \<open>u \<in> Lang_mttm\<close> of the wrap --- the wrap with the finite-control
  small-input cleanup planted on top (short inputs decided by table
  lookup in \<open>n + 2\<close>, long inputs run the wrap after the O(1) rewind).
  The extra hypothesis over the raw
  @{thm[source] linear_speedup_HU_12_3_nae} is again \<open>Mtime\<close>, and the
  cardinality side condition tightens from \<open>16 q\<close> to \<open>16 (q + 1)\<close> (the
  faster inner run).\<close>

theorem linear_speedup_HU_12_3_nae_conv:
  fixes M :: "('q, 'a) mttm"
    and T :: "nat \<Rightarrow> nat"
    and q :: nat
  assumes wf:      "well_formed_mttm M"
      and Mtime:   "\<And>w. w \<in> Lang_mttm M \<Longrightarrow> accepts_in_time_mttm M w (T (length w))"
      and growth:  "\<forall>d. \<exists>N. \<forall>n. N \<le> n \<longrightarrow> d * n \<le> T n"
      and q_pos:   "0 < q"
      and c_large: "16 * (q + 1) \<le> card (UNIV :: ('c :: enum) set)"
      and k2:      "2 \<le> k_tm M"
  obtains W' :: "((('q \<times> ('a, 'c::enum) ae_stage, 'a, 'c \<Rightarrow> 'a) wrap_state,
                   ('a, 'c \<Rightarrow> 'a) wrap_alphabet) fp_state,
                  ('a, 'c \<Rightarrow> 'a) wrap_alphabet) mttm"
  where "valid_mttm W'"
    and "Lang_user_wrap W' = Lang_mttm M"
    and "time_bounded_conv W' (\<lambda>n. T n div q)"
proof -
  let ?W = "encoding_wrap
              (alphabet_enlarge M
                 :: ('q \<times> ('a, 'c) ae_stage, 'c \<Rightarrow> 'a) mttm)
              (ae_pack (bl_tm M) :: 'a list \<Rightarrow> ('c \<Rightarrow> 'a))
              (card (UNIV :: 'c set))
              (Sigma_tm M)"
  have q1pos: "0 < q + 1" by simp
  obtain K N0 where
    Vraw: "valid_mttm ?W" and
    Lraw: "Lang_user_wrap ?W = Lang_mttm M" and
    Traw: "\<forall>w. set w \<subseteq> Sigma_tm M
                \<longrightarrow> N0 \<le> length w
                \<longrightarrow> accepts_in_time_mttm M w (T (length w))
                \<longrightarrow> accepts_in_time_user_wrap ?W w (T (length w) div (q + 1) + K)"
    by (rule linear_speedup_HU_12_3_nae[OF wf growth q1pos c_large k2])
  have blle: "bl_tm ?W \<noteq> le_tm ?W"
  proof -
    have le_neq_bl: "le_tm M \<noteq> bl_tm M" using wf by auto
    have "bl_tm (alphabet_enlarge M :: ('q \<times> ('a, 'c) ae_stage, 'c \<Rightarrow> 'a) mttm)
            \<noteq> le_tm (alphabet_enlarge M :: ('q \<times> ('a, 'c) ae_stage, 'c \<Rightarrow> 'a) mttm)"
      unfolding bl_tm_alphabet_enlarge le_tm_alphabet_enlarge
      using le_neq_bl by (simp add: bl_block_def LE_block_def fun_eq_iff)
    thus ?thesis by simp
  qed
  from growth obtain Nd where
    growthN: "\<forall>n. Nd \<le> n \<longrightarrow> 3 * q * (q + 1) * n \<le> T n" by blast
  define N1 where "N1 = max N0 (max Nd (K + 4))"
  have N1_N0: "N0 \<le> N1" and N1_Nd: "Nd \<le> N1" and N1_K: "K + 4 \<le> N1"
    unfolding N1_def by auto
  let ?W' = "finite_patch ?W (\<lambda>u. u \<in> Lang_mttm ?W) N1"
  have lang': "Lang_mttm ?W' = Lang_mttm ?W"
  proof -
    have "Lang_mttm ?W' = {u. set u \<subseteq> Sigma_tm ?W \<and> u \<in> Lang_mttm ?W}"
      using finite_patch_language[OF Vraw blle] by simp
    also have "\<dots> = Lang_mttm ?W" unfolding Lang_mttm_def by auto
    finally show ?thesis .
  qed
  have valid': "valid_mttm ?W'" by (rule finite_patch_valid[OF Vraw])
  have Luser': "Lang_user_wrap ?W' = Lang_mttm M"
    using lang' Lraw unfolding Lang_user_wrap_def by simp
  have conv': "time_bounded_conv ?W' (\<lambda>n. T n div q)"
    unfolding time_bounded_conv_def
  proof
    fix v assume vW': "v \<in> Lang_mttm ?W'"
    hence vW: "v \<in> Lang_mttm ?W" using lang' by simp
    hence vSg: "set v \<subseteq> Sigma_tm ?W" unfolding Lang_mttm_def by simp
    show "accepts_in_time_mttm ?W' v (max (length v + 2) ((\<lambda>n. T n div q) (length v)))"
    proof (cases "length v \<le> N1")
      case True
      have "accepts_in_time_mttm ?W' v (length v + 2)"
        using Vraw vSg True vW by (rule fp_short_time)
      thus ?thesis by (auto elim: accepts_in_time_mttm_mono)
    next
      case False
      hence N1lt: "N1 < length v" by simp
      obtain w where vmap: "v = map Raw w" and wU: "w \<in> Lang_user_wrap ?W"
        using vW Lang_mttm_encoding_wrap_ex_Raw by blast
      from wU Lraw have wM: "w \<in> Lang_mttm M" by simp
      hence wSgM: "set w \<subseteq> Sigma_tm M" unfolding Lang_mttm_def by simp
      from wM have accM: "accepts_in_time_mttm M w (T (length w))" by (rule Mtime)
      have lenwv: "length w = length v" using vmap by simp
      have N0w: "N0 \<le> length w" using N1lt lenwv N1_N0 by simp
      have "accepts_in_time_user_wrap ?W w (T (length w) div (q + 1) + K)"
        using Traw wSgM N0w accM by blast
      hence accW: "accepts_in_time_mttm ?W v (T (length v) div (q + 1) + K)"
        by (simp only: accepts_in_time_user_wrap_def vmap[symmetric] lenwv)
      have "accepts_in_time_mttm ?W' v ((T (length v) div (q + 1) + K) + (2 * N1 + 4))"
        using Vraw vSg N1lt accW by (rule fp_long_time)
      moreover have "(T (length v) div (q + 1) + K) + (2 * N1 + 4) \<le> T (length v) div q"
      proof -
        have Ndlv: "Nd \<le> length v" using N1_Nd N1lt by simp
        have TN: "3 * q * (q + 1) * length v \<le> T (length v)"
          using growthN Ndlv by blast
        have "K + 2 * N1 + 4 \<le> 3 * length v"
        proof -
          have "K + 2 * N1 + 4 \<le> 3 * N1" using N1_K by linarith
          also have "\<dots> \<le> 3 * length v" using N1lt by linarith
          finally show ?thesis .
        qed
        hence "q * (q + 1) * (K + 2 * N1 + 4) \<le> q * (q + 1) * (3 * length v)"
          by (rule mult_le_mono2)
        also have "q * (q + 1) * (3 * length v) = 3 * q * (q + 1) * length v"
          by (simp add: algebra_simps)
        also note TN
        finally have big: "q * (q + 1) * (K + 2 * N1 + 4) \<le> T (length v)" .
        have "T (length v) div (q + 1) + (K + 2 * N1 + 4) \<le> T (length v) div q"
          using q_pos big by (rule div_absorb_step)
        thus ?thesis by simp
      qed
      ultimately have "accepts_in_time_mttm ?W' v (T (length v) div q)"
        by (auto elim: accepts_in_time_mttm_mono)
      thus ?thesis by (auto elim: accepts_in_time_mttm_mono)
    qed
  qed
  show thesis
  proof (rule that[of ?W'])
    show "valid_mttm ?W'" by (rule valid')
    show "Lang_user_wrap ?W' = Lang_mttm M" by (rule Luser')
    show "time_bounded_conv ?W' (\<lambda>n. T n div q)" by (rule conv')
  qed
qed

text \<open>The deterministic specialisation of
  @{thm[source] linear_speedup_HU_12_3_nae_conv}: adds the \<open>det\<close>
  hypothesis on \<open>M\<close> and the determinism-preservation conjunct on the
  cleaned machine (via @{thm[source] finite_patch_det}).\<close>

theorem linear_speedup_HU_12_3_dae_conv:
  fixes M :: "('q, 'a) mttm"
    and T :: "nat \<Rightarrow> nat"
    and q :: nat
  assumes wf:      "well_formed_mttm M"
      and det:     "det_mttm M"
      and Mtime:   "\<And>w. w \<in> Lang_mttm M \<Longrightarrow> accepts_in_time_mttm M w (T (length w))"
      and growth:  "\<forall>d. \<exists>N. \<forall>n. N \<le> n \<longrightarrow> d * n \<le> T n"
      and q_pos:   "0 < q"
      and c_large: "16 * (q + 1) \<le> card (UNIV :: ('c :: enum) set)"
      and k2:      "2 \<le> k_tm M"
  obtains W' :: "((('q \<times> ('a, 'c::enum) ae_stage, 'a, 'c \<Rightarrow> 'a) wrap_state,
                   ('a, 'c \<Rightarrow> 'a) wrap_alphabet) fp_state,
                  ('a, 'c \<Rightarrow> 'a) wrap_alphabet) mttm"
  where "valid_mttm W'"
    and "det_mttm W'"
    and "Lang_user_wrap W' = Lang_mttm M"
    and "time_bounded_conv W' (\<lambda>n. T n div q)"
proof -
  let ?W = "encoding_wrap
              (alphabet_enlarge M
                 :: ('q \<times> ('a, 'c) ae_stage, 'c \<Rightarrow> 'a) mttm)
              (ae_pack (bl_tm M) :: 'a list \<Rightarrow> ('c \<Rightarrow> 'a))
              (card (UNIV :: 'c set))
              (Sigma_tm M)"
  have q1pos: "0 < q + 1" by simp
  obtain K N0 where
    Vraw: "valid_mttm ?W" and
    Draw: "det_mttm ?W" and
    Lraw: "Lang_user_wrap ?W = Lang_mttm M" and
    Traw: "\<forall>w. set w \<subseteq> Sigma_tm M
                \<longrightarrow> N0 \<le> length w
                \<longrightarrow> accepts_in_time_mttm M w (T (length w))
                \<longrightarrow> accepts_in_time_user_wrap ?W w (T (length w) div (q + 1) + K)"
    by (rule linear_speedup_HU_12_3_dae[OF wf det growth q1pos c_large k2])
  have blle: "bl_tm ?W \<noteq> le_tm ?W"
  proof -
    have le_neq_bl: "le_tm M \<noteq> bl_tm M" using wf by auto
    have "bl_tm (alphabet_enlarge M :: ('q \<times> ('a, 'c) ae_stage, 'c \<Rightarrow> 'a) mttm)
            \<noteq> le_tm (alphabet_enlarge M :: ('q \<times> ('a, 'c) ae_stage, 'c \<Rightarrow> 'a) mttm)"
      unfolding bl_tm_alphabet_enlarge le_tm_alphabet_enlarge
      using le_neq_bl by (simp add: bl_block_def LE_block_def fun_eq_iff)
    thus ?thesis by simp
  qed
  from growth obtain Nd where
    growthN: "\<forall>n. Nd \<le> n \<longrightarrow> 3 * q * (q + 1) * n \<le> T n" by blast
  define N1 where "N1 = max N0 (max Nd (K + 4))"
  have N1_N0: "N0 \<le> N1" and N1_Nd: "Nd \<le> N1" and N1_K: "K + 4 \<le> N1"
    unfolding N1_def by auto
  let ?W' = "finite_patch ?W (\<lambda>u. u \<in> Lang_mttm ?W) N1"
  have lang': "Lang_mttm ?W' = Lang_mttm ?W"
  proof -
    have "Lang_mttm ?W' = {u. set u \<subseteq> Sigma_tm ?W \<and> u \<in> Lang_mttm ?W}"
      using finite_patch_language[OF Vraw blle] by simp
    also have "\<dots> = Lang_mttm ?W" unfolding Lang_mttm_def by auto
    finally show ?thesis .
  qed
  have valid': "valid_mttm ?W'" by (rule finite_patch_valid[OF Vraw])
  have det': "det_mttm ?W'" by (rule finite_patch_det[OF Vraw blle Draw])
  have Luser': "Lang_user_wrap ?W' = Lang_mttm M"
    using lang' Lraw unfolding Lang_user_wrap_def by simp
  have conv': "time_bounded_conv ?W' (\<lambda>n. T n div q)"
    unfolding time_bounded_conv_def
  proof
    fix v assume vW': "v \<in> Lang_mttm ?W'"
    hence vW: "v \<in> Lang_mttm ?W" using lang' by simp
    hence vSg: "set v \<subseteq> Sigma_tm ?W" unfolding Lang_mttm_def by simp
    show "accepts_in_time_mttm ?W' v (max (length v + 2) ((\<lambda>n. T n div q) (length v)))"
    proof (cases "length v \<le> N1")
      case True
      have "accepts_in_time_mttm ?W' v (length v + 2)"
        using Vraw vSg True vW by (rule fp_short_time)
      thus ?thesis by (auto elim: accepts_in_time_mttm_mono)
    next
      case False
      hence N1lt: "N1 < length v" by simp
      obtain w where vmap: "v = map Raw w" and wU: "w \<in> Lang_user_wrap ?W"
        using vW Lang_mttm_encoding_wrap_ex_Raw by blast
      from wU Lraw have wM: "w \<in> Lang_mttm M" by simp
      hence wSgM: "set w \<subseteq> Sigma_tm M" unfolding Lang_mttm_def by simp
      from wM have accM: "accepts_in_time_mttm M w (T (length w))" by (rule Mtime)
      have lenwv: "length w = length v" using vmap by simp
      have N0w: "N0 \<le> length w" using N1lt lenwv N1_N0 by simp
      have "accepts_in_time_user_wrap ?W w (T (length w) div (q + 1) + K)"
        using Traw wSgM N0w accM by blast
      hence accW: "accepts_in_time_mttm ?W v (T (length v) div (q + 1) + K)"
        by (simp only: accepts_in_time_user_wrap_def vmap[symmetric] lenwv)
      have "accepts_in_time_mttm ?W' v ((T (length v) div (q + 1) + K) + (2 * N1 + 4))"
        using Vraw vSg N1lt accW by (rule fp_long_time)
      moreover have "(T (length v) div (q + 1) + K) + (2 * N1 + 4) \<le> T (length v) div q"
      proof -
        have Ndlv: "Nd \<le> length v" using N1_Nd N1lt by simp
        have TN: "3 * q * (q + 1) * length v \<le> T (length v)"
          using growthN Ndlv by blast
        have "K + 2 * N1 + 4 \<le> 3 * length v"
        proof -
          have "K + 2 * N1 + 4 \<le> 3 * N1" using N1_K by linarith
          also have "\<dots> \<le> 3 * length v" using N1lt by linarith
          finally show ?thesis .
        qed
        hence "q * (q + 1) * (K + 2 * N1 + 4) \<le> q * (q + 1) * (3 * length v)"
          by (rule mult_le_mono2)
        also have "q * (q + 1) * (3 * length v) = 3 * q * (q + 1) * length v"
          by (simp add: algebra_simps)
        also note TN
        finally have big: "q * (q + 1) * (K + 2 * N1 + 4) \<le> T (length v)" .
        have "T (length v) div (q + 1) + (K + 2 * N1 + 4) \<le> T (length v) div q"
          using q_pos big by (rule div_absorb_step)
        thus ?thesis by simp
      qed
      ultimately have "accepts_in_time_mttm ?W' v (T (length v) div q)"
        by (auto elim: accepts_in_time_mttm_mono)
      thus ?thesis by (auto elim: accepts_in_time_mttm_mono)
    qed
  qed
  show thesis
  proof (rule that[of ?W'])
    show "valid_mttm ?W'" by (rule valid')
    show "det_mttm ?W'" by (rule det')
    show "Lang_user_wrap ?W' = Lang_mttm M" by (rule Luser')
    show "time_bounded_conv ?W' (\<lambda>n. T n div q)" by (rule conv')
  qed
qed

end
