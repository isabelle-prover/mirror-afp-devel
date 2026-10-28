theory Wrap_Band_Speedup
  imports Wrap_Convention Wrap_Speedup_Arithmetic
begin

section \<open>First-block speedup above a linear band\<close>

text \<open>The machine here is the wrap with its first-block language table.  The
  table decides short inputs within the convention's floor; long inputs follow
  the raw wrap at the same cost.  The table is a finite restriction of the
  source language, so the machine is shown to exist rather than computed from
  the source.

  The timing conclusion gives a bounded accepting run for each word in the
  language, and says nothing about rejecting runs.  On a short word the machine
  stops with the table's verdict, so a nondeterministic source that both
  accepts and rejects that word along different runs keeps only its accepting
  verdict.  On long inputs every simulated run is carried over, so a statement
  about the time to reject needs its own argument about how the source's runs
  end.\<close>

abbreviation wrap_speedup ::
  "('q, 'a) ktm \<Rightarrow>
    (('q \<times> ('a, 'c::enum) ae_stage, 'a, 'c \<Rightarrow> 'a) wrap_state,
      ('a, 'c \<Rightarrow> 'a) wrap_alphabet) ktm" where
  "wrap_speedup M \<equiv> encoding_wrap
    (alphabet_enlarge M) (ae_pack (bl_ktm M)) (card (UNIV :: 'c set)) (Sigma_ktm M)"

definition wrap_speedup_bound :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "wrap_speedup_bound m n T = n + 3 * ((n + m - 1) div m) +
    8 * ((T + m - 1) div m) + 9"

abbreviation wrap_prefix_speedup ::
  "('q,'a) ktm \<Rightarrow> nat \<Rightarrow>
    (bool \<times> (('q \<times> ('a,'c::enum) ae_stage,'a,'c \<Rightarrow> 'a) wrap_state),
      ('a,'c \<Rightarrow> 'a) wrap_alphabet) ktm" where
  "wrap_prefix_speedup M N \<equiv>
    wrap_prefix_patch (wrap_speedup M) (\<lambda>w. w \<in> Lang_ktm M) N"

definition wrap_prefix_speedup_bound where
  "wrap_prefix_speedup_bound N m n T = (if n \<le> N then n+2 else wrap_speedup_bound m n T)"

lemma wrap_prefix_speedup_contract:
  fixes M :: "('s,'a) ktm"
    and P :: "(bool \<times> (('s \<times> ('a,'b::enum) ae_stage,'a,'b \<Rightarrow> 'a) wrap_state),
      ('a,'b \<Rightarrow> 'a) wrap_alphabet) ktm"
  assumes wf: "well_formed_ktm M" and k2: "2 \<le> k_ktm M"
      and width: "N < card (UNIV :: 'b set)"
  defines "P \<equiv> wrap_prefix_speedup M N"
  shows "valid_ktm P"
    and "Lang_ktm P = map Raw ` Lang_ktm M"
    and "det_ktm M \<Longrightarrow> det_ktm P"
proof -
  let ?m = "card (UNIV :: 'b set)"
  let ?A = "alphabet_enlarge M :: ('s \<times> ('a,'b) ae_stage,'b \<Rightarrow> 'a) ktm"
  let ?pack = "ae_pack (bl_ktm M) :: 'a list \<Rightarrow> ('b \<Rightarrow> 'a)"
  let ?W = "encoding_wrap ?A ?pack ?m (Sigma_ktm M)"
  have validM: "valid_ktm M" and blle: "le_ktm M \<noteq> bl_ktm M" using wf by auto
  have validA: "valid_ktm ?A" by (rule alphabet_enlarge_wf[OF validM])
  have positive: "0 < ?m" by (simp add: card_gt_0_iff)
  have blleA: "bl_ktm ?A \<noteq> le_ktm ?A"
    using blle by (simp add: bl_ktm_alphabet_enlarge le_ktm_alphabet_enlarge
      bl_block_def LE_block_def fun_eq_iff)
  have k2A: "2 \<le> k_ktm ?A" using k2 by (cases M) (simp add: alphabet_enlarge_def)
  note F = linear_speedup_form_1_raw_nae[where 'c='b, OF wf k2]
  show "valid_ktm P" unfolding P_def by (rule wrap_prefix_patch_valid[OF F(1)])
  have enc: "set (wrap_enc ?pack ?m w) \<subseteq> Sigma_ktm ?A"
    if "set w \<subseteq> Sigma_ktm M" for w
    by (rule ae_wrap_enc_in_Sigma[OF validM that])
  have table: "(\<lambda>u. u \<in> Lang_ktm M) = (\<lambda>u. u \<in> Lang_user_wrap ?W)"
    using F(2) by simp
  have lang: "Lang_user_wrap P = Lang_ktm M"
  proof -
    have "Lang_user_wrap P = Lang_user_wrap ?W"
      unfolding P_def table
      by (rule wrap_prefix_language[OF validA positive blleA k2A width enc])
    then show ?thesis using F(2) by simp
  qed
  show "Lang_ktm P = map Raw ` Lang_ktm M"
  proof
    show "Lang_ktm P \<subseteq> map Raw ` Lang_ktm M"
    proof
      fix v assume member: "v \<in> Lang_ktm P"
      then have "set v \<subseteq> Raw ` Sigma_ktm M"
        by (simp add: P_def Lang_ktm_iff)
      then have "v \<in> lists (Raw ` Sigma_ktm M)" by (auto simp: in_lists_conv_set)
      then obtain w where v: "v = map Raw w" by (auto simp: lists_image)
      have "w \<in> Lang_user_wrap P"
        unfolding Lang_user_wrap_def mem_Collect_eq using member unfolding v .
      then show "v \<in> map Raw ` Lang_ktm M" using lang v by blast
    qed
    show "map Raw ` Lang_ktm M \<subseteq> Lang_ktm P"
      using lang unfolding Lang_user_wrap_def by blast
  qed
  assume det: "det_ktm M"
  have "det_ktm ?W"
    by (rule linear_speedup_form_1_raw_dae(2)[where 'c='b, OF wf det k2])
  then show "det_ktm P" unfolding P_def by (rule wrap_prefix_patch_det)
qed

lemma wrap_prefix_speedup_short:
  fixes M :: "('s,'a) ktm"
    and P :: "(bool \<times> (('s \<times> ('a,'b::enum) ae_stage,'a,'b \<Rightarrow> 'a) wrap_state),
      ('a,'b \<Rightarrow> 'a) wrap_alphabet) ktm"
  assumes wf: "well_formed_ktm M" and k2: "2 \<le> k_ktm M"
      and width: "N < card (UNIV :: 'b set)"
      and word: "set w \<subseteq> Sigma_ktm M" and short: "length w \<le> N"
  defines "P \<equiv> wrap_prefix_speedup M N"
  shows "reaches_state_in_time_ktm P (map Raw w)
    (if w \<in> Lang_ktm M then t_ktm P else r_ktm P) (length w + 2)"
proof -
  let ?m = "card (UNIV :: 'b set)"
  let ?A = "alphabet_enlarge M :: ('s \<times> ('a,'b) ae_stage,'b \<Rightarrow> 'a) ktm"
  let ?pack = "ae_pack (bl_ktm M) :: 'a list \<Rightarrow> ('b \<Rightarrow> 'a)"
  let ?W = "encoding_wrap ?A ?pack ?m (Sigma_ktm M)"
  have validM: "valid_ktm M" and blle: "le_ktm M \<noteq> bl_ktm M" using wf by auto
  have validA: "valid_ktm ?A" by (rule alphabet_enlarge_wf[OF validM])
  have positive: "0 < ?m" by (simp add: card_gt_0_iff)
  have blleA: "bl_ktm ?A \<noteq> le_ktm ?A"
    using blle by (simp add: bl_ktm_alphabet_enlarge le_ktm_alphabet_enlarge
      bl_block_def LE_block_def fun_eq_iff)
  have k2A: "2 \<le> k_ktm ?A" using k2 by (cases M) (simp add: alphabet_enlarge_def)
  have pack: "?pack (take ?m (drop (i*?m) w)) \<in> Sigma_ktm ?A"
    if "i*?m < length w" for i
    using ae_wrap_enc_in_Sigma[OF validM word, where 'c='b]
      pack_take_in_set_wrap_enc[OF positive that, where pack="?pack"] by blast
  have shortm: "length w < ?m" using short width by arith
  have run: "reaches_state_in_time_ktm P (map Raw w)
    (False, if w \<in> Lang_ktm M then t_ktm ?W else r_ktm ?W) (length w + 2)"
    unfolding P_def
    by (rule wrap_prefix_short_reaches[where A="?A" and pack="?pack" and m="?m"
      and S="Sigma_ktm M" and w=w and table="\<lambda>u. u \<in> Lang_ktm M" and N=N,
      OF validA positive word blleA k2A pack shortm short])
  show ?thesis using run by (cases "w \<in> Lang_ktm M") (simp_all add: P_def)
qed

lemma wrap_prefix_speedup_long:
  fixes M :: "('s,'a) ktm"
    and P :: "(bool \<times> (('s \<times> ('a,'b::enum) ae_stage,'a,'b \<Rightarrow> 'a) wrap_state),
      ('a,'b \<Rightarrow> 'a) wrap_alphabet) ktm"
  assumes wf: "well_formed_ktm M" and k2: "2 \<le> k_ktm M"
      and word: "set w \<subseteq> Sigma_ktm M" and long: "N < length w"
      and run: "reaches_state_in_time_ktm (wrap_speedup M) (map Raw w) (W_Run q) T"
  defines "P \<equiv> wrap_prefix_speedup M N"
  shows "reaches_state_in_time_ktm P (map Raw w) (False, W_Run q) T"
proof -
  let ?m = "card (UNIV :: 'b set)"
  let ?A = "alphabet_enlarge M :: ('s \<times> ('a,'b) ae_stage,'b \<Rightarrow> 'a) ktm"
  let ?pack = "ae_pack (bl_ktm M) :: 'a list \<Rightarrow> ('b \<Rightarrow> 'a)"
  have validM: "valid_ktm M" and blle: "le_ktm M \<noteq> bl_ktm M" using wf by auto
  have validA: "valid_ktm ?A" by (rule alphabet_enlarge_wf[OF validM])
  have positive: "0 < ?m" by (simp add: card_gt_0_iff)
  have blleA: "bl_ktm ?A \<noteq> le_ktm ?A"
    using blle by (simp add: bl_ktm_alphabet_enlarge le_ktm_alphabet_enlarge
      bl_block_def LE_block_def fun_eq_iff)
  have k2A: "2 \<le> k_ktm ?A" using k2 by (cases M) (simp add: alphabet_enlarge_def)
  have pack: "?pack (take ?m (drop (i*?m) w)) \<in> Sigma_ktm ?A"
    if "i*?m < length w" for i
    using ae_wrap_enc_in_Sigma[OF validM word, where 'c='b]
      pack_take_in_set_wrap_enc[OF positive that, where pack="?pack"] by blast
  show ?thesis unfolding P_def
    by (rule wrap_prefix_transport[where A="?A" and pack="?pack" and m="?m"
      and S="Sigma_ktm M" and w=w and table="\<lambda>u. u \<in> Lang_ktm M" and N=N,
      OF validA positive word blleA k2A pack long run])
qed

lemma wrap_prefix_speedup_accepts:
  fixes M :: "('s,'a) ktm"
    and P :: "(bool \<times> (('s \<times> ('a,'b::enum) ae_stage,'a,'b \<Rightarrow> 'a) wrap_state),
      ('a,'b \<Rightarrow> 'a) wrap_alphabet) ktm"
  assumes wf: "well_formed_ktm M" and k2: "2 \<le> k_ktm M"
      and width: "N < card (UNIV :: 'b set)"
      and word: "set w \<subseteq> Sigma_ktm M"
      and source: "accepts_in_time_ktm M w T"
  defines "P \<equiv> wrap_prefix_speedup M N"
  shows "accepts_in_time_ktm P (map Raw w)
    (wrap_prefix_speedup_bound N (card (UNIV :: 'b set)) (length w) T)"
proof (cases "length w \<le> N")
  case True
  have member: "w \<in> Lang_ktm M" using word source by (auto simp: Lang_ktm_iff)
  have run: "reaches_state_in_time_ktm P (map Raw w)
    (if w \<in> Lang_ktm M then t_ktm P else r_ktm P) (length w + 2)"
    unfolding P_def by (rule wrap_prefix_speedup_short[OF wf k2 width word True])
  show ?thesis using run member True
    by (simp add: accepts_in_time_ktm_iff_reaches wrap_prefix_speedup_bound_def)
next
  case False
  let ?m = "card (UNIV :: 'b set)"
  let ?W = "wrap_speedup M :: (('s \<times> ('a,'b) ae_stage,'a,'b \<Rightarrow> 'a) wrap_state,
      ('a,'b \<Rightarrow> 'a) wrap_alphabet) ktm"
  have long: "N < length w" using False by simp
  have raw: "accepts_in_time_user_wrap ?W w
    (length w + (length w + ?m - 1) div ?m + 5
      + 2 * ((length w + ?m - 1) div ?m) + 8 * ((T + ?m - 1) div ?m) + 4)"
    using linear_speedup_form_1_raw_nae(3)[where 'c='b and T="\<lambda>_. T",
      OF wf k2] word source by blast
  have run: "reaches_state_in_time_ktm ?W (map Raw w)
    (W_Run (t_ktm M, init_stage (le_ktm M))) (wrap_speedup_bound ?m (length w) T)"
    using raw by (simp add: accepts_in_time_user_wrap_def accepts_in_time_ktm_iff_reaches
      t_ktm_alphabet_enlarge wrap_speedup_bound_def algebra_simps)
  have "reaches_state_in_time_ktm P (map Raw w)
    (False, W_Run (t_ktm M, init_stage (le_ktm M))) (wrap_speedup_bound ?m (length w) T)"
    unfolding P_def by (rule wrap_prefix_speedup_long[OF wf k2 word long run])
  then show ?thesis using False
    by (simp add: P_def accepts_in_time_ktm_iff_reaches
      t_ktm_alphabet_enlarge wrap_prefix_speedup_bound_def)
qed

lemma wrap_prefix_speedup_bound_band:
  assumes q: "0 < q"
      and width: "16 * (3 + 8*c) * (q+1) + 16*c + 1 \<le> m"
      and band: "\<And>n. N0 \<le> n \<Longrightarrow> n + n div q \<le> t n"
  shows "wrap_prefix_speedup_bound (max N0 (q * (81 + 128*e))) m n (c*t n+e)
    \<le> max (n+2) (t n)"
proof (cases "n \<le> max N0 (q * (81 + 128*e))")
  case True then show ?thesis by (simp add: wrap_prefix_speedup_bound_def)
next
  case False
  have far: "N0 \<le> n" and big: "q * (81 + 128*e) \<le> n" using False by auto
  have "n + (n+m-1) div m + 5 + 2*((n+m-1) div m)
    + 8*((c*t n+e+m-1) div m) + 4 \<le> t n"
    by (rule speedup_band_arith[OF q width big band[OF far]])
  then show ?thesis using False
    by (simp add: wrap_prefix_speedup_bound_def wrap_speedup_bound_def algebra_simps)
qed

theorem wrap_prefix_speedup_band:
  fixes M :: "('s,'a) ktm"
    and P :: "(bool \<times> (('s \<times> ('a,'b::enum) ae_stage,'a,'b \<Rightarrow> 'a) wrap_state),
      ('a,'b \<Rightarrow> 'a) wrap_alphabet) ktm"
  assumes wf: "well_formed_ktm M" and k2: "2 \<le> k_ktm M"
      and timed: "\<And>w. w \<in> Lang_ktm M \<Longrightarrow>
        accepts_in_time_ktm M w (c * t (length w) + e)"
      and q: "0 < q"
      and band: "\<And>n. N0 \<le> n \<Longrightarrow> n + n div q \<le> t n"
      and large: "16 * (3 + 8*c) * (q+1) + 16*c + 1 \<le> card (UNIV :: 'b set)"
      and width: "max N0 (q * (81 + 128*e)) < card (UNIV :: 'b set)"
  defines "P \<equiv> wrap_prefix_speedup M (max N0 (q * (81 + 128*e)))"
  shows "time_bounded_conv P t"
proof -
  have lang: "Lang_ktm P = map Raw ` Lang_ktm M"
    unfolding P_def by (rule wrap_prefix_speedup_contract(2)[OF wf k2 width])
  show ?thesis unfolding time_bounded_conv_def
  proof
    fix v assume "v \<in> Lang_ktm P"
    then obtain w where v: "v = map Raw w" and member: "w \<in> Lang_ktm M"
      using lang by blast
    have word: "set w \<subseteq> Sigma_ktm M" using member by (simp add: Lang_ktm_iff)
    have run: "accepts_in_time_ktm P (map Raw w)
      (wrap_prefix_speedup_bound (max N0 (q * (81 + 128*e)))
        (card (UNIV :: 'b set)) (length w) (c*t (length w)+e))"
      unfolding P_def by (rule wrap_prefix_speedup_accepts[OF wf k2 width word timed[OF member]])
    have "accepts_in_time_ktm P (map Raw w) (max (length w+2) (t (length w)))"
      by (rule accepts_in_time_ktm_mono[OF run wrap_prefix_speedup_bound_band[OF q large band]])
    then show "accepts_in_time_ktm P v (max (length v+2) (t (length v)))"
      by (simp add: v)
  qed
qed

end
