theory Multitape_Time_Convention
  imports Multitape_Finite_Patch
begin

section \<open>Time-bound class predicates and cleanup\<close>

text \<open>Shared vocabulary for the linear-speedup consumers.  An
  \<^emph>\<open>eventual\<close> bound holds for all long enough inputs in the language; a
  \<^emph>\<open>convention\<close> bound is the Hopcroft--Ullman
  \<^cite>\<open>\<open>p.~291\<close> in "Hopcroft1979:introduction"\<close> \<open>max(n+1, ...)\<close> form on
  the substrate, where the floor is \<open>n + 2\<close> (the substrate reads the
  left endmarker before the first input symbol).\<close>

definition time_bounded_ev :: "('q, 'a) mttm \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> bool" where
  "time_bounded_ev M g \<longleftrightarrow>
     (\<exists>N. \<forall>w\<in>Lang_mttm M. N \<le> length w
             \<longrightarrow> accepts_in_time_mttm M w (g (length w)))"

definition time_bounded_conv :: "('q, 'a) mttm \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> bool" where
  "time_bounded_conv M g \<longleftrightarrow>
     (\<forall>w\<in>Lang_mttm M.
        accepts_in_time_mttm M w (max (length w + 2) (g (length w))))"

text \<open>The cleanup corollary: an eventual bound is upgraded to a
  convention bound on \<^emph>\<open>all\<close> inputs, at the cost of the finite-control
  overhead \<open>c0 = 2 * N + 4\<close>, with language, tape count, and determinism
  preserved.  Instantiates @{const finite_patch} with the (finite, hence
  unconditionally available) table \<open>w \<in> Lang_mttm M\<close>.

  Hypotheses are the weakest the proof uses --- @{const valid_mttm} and
  \<open>bl_tm M \<noteq> le_tm M\<close>, matching the @{const finite_patch} contract
  lemmas it composes (\<open>finite_patch_language\<close> / \<open>_det\<close> /
  \<open>fp_short_time\<close> / \<open>fp_long_time\<close>).  In particular it does \<^emph>\<open>not\<close>
  require @{const le_unique} or the state distinctness of
  @{const well_formed_mttm}, so it applies to machines (e.g. the
  encoding wrap) whose \<open>le\<close>-uniqueness is not separately established.\<close>

theorem time_cleanup:
  assumes vM: "valid_mttm M" and blle: "bl_tm M \<noteq> le_tm M"
    and ev: "time_bounded_ev M g"
  obtains N where
    "Lang_mttm (finite_patch M (\<lambda>w. w \<in> Lang_mttm M) N) = Lang_mttm M"
    and "k_tm (finite_patch M (\<lambda>w. w \<in> Lang_mttm M) N) = k_tm M"
    and "det_mttm M \<longrightarrow> det_mttm (finite_patch M (\<lambda>w. w \<in> Lang_mttm M) N)"
    and "time_bounded_conv (finite_patch M (\<lambda>w. w \<in> Lang_mttm M) N)
           (\<lambda>n. g n + (2 * N + 4))"
proof -
  from ev obtain N where evN: "\<forall>w\<in>Lang_mttm M. N \<le> length w
                                 \<longrightarrow> accepts_in_time_mttm M w (g (length w))"
    unfolding time_bounded_ev_def by blast
  let ?M' = "finite_patch M (\<lambda>w. w \<in> Lang_mttm M) N"
  have lang: "Lang_mttm ?M' = Lang_mttm M"
  proof -
    have "Lang_mttm ?M' = {w. set w \<subseteq> Sigma_tm M
             \<and> (if length w \<le> N then w \<in> Lang_mttm M else w \<in> Lang_mttm M)}"
      by (rule finite_patch_language[OF vM blle])
    also have "\<dots> = {w. set w \<subseteq> Sigma_tm M \<and> w \<in> Lang_mttm M}" by simp
    also have "\<dots> = Lang_mttm M" unfolding Lang_mttm_def by auto
    finally show ?thesis .
  qed
  have kpres: "k_tm ?M' = k_tm M" by (rule finite_patch_k_tm)
  have detpres: "det_mttm M \<longrightarrow> det_mttm ?M'"
    using finite_patch_det[OF vM blle] by blast
  have conv: "time_bounded_conv ?M' (\<lambda>n. g n + (2 * N + 4))"
    unfolding time_bounded_conv_def
  proof
    fix w assume "w \<in> Lang_mttm ?M'"
    hence wL: "w \<in> Lang_mttm M" using lang by simp
    have wSg: "set w \<subseteq> Sigma_tm M" using wL unfolding Lang_mttm_def by simp
    show "accepts_in_time_mttm ?M' w
            (max (length w + 2) ((\<lambda>n. g n + (2 * N + 4)) (length w)))"
    proof (cases "length w \<le> N")
      case True
      have "accepts_in_time_mttm ?M' w (length w + 2)"
        using vM wSg True wL by (rule fp_short_time)
      moreover have "length w + 2 \<le> max (length w + 2) (g (length w) + (2 * N + 4))"
        by simp
      ultimately show ?thesis by (auto elim: accepts_in_time_mttm_mono)
    next
      case False
      hence Nlt: "N < length w" by simp
      have "accepts_in_time_mttm M w (g (length w))" using evN wL Nlt by simp
      hence "accepts_in_time_mttm ?M' w (g (length w) + (2 * N + 4))"
        by (rule fp_long_time[OF vM wSg Nlt])
      moreover have "g (length w) + (2 * N + 4)
                       \<le> max (length w + 2) (g (length w) + (2 * N + 4))" by simp
      ultimately show ?thesis by (auto elim: accepts_in_time_mttm_mono)
    qed
  qed
  show thesis
  proof (rule that[of N])
    show "Lang_mttm ?M' = Lang_mttm M" by (rule lang)
    show "k_tm ?M' = k_tm M" by (rule kpres)
    show "det_mttm M \<longrightarrow> det_mttm ?M'" by (rule detpres)
    show "time_bounded_conv ?M' (\<lambda>n. g n + (2 * N + 4))" by (rule conv)
  qed
qed


subsection \<open>The clean convention form is unattainable in general\<close>

text \<open>Why the linear-\<open>T\<close> speedup theorems are stated with a residual
  \<open>+K\<close> (all inputs) or an explicit threshold (eventual), never as the clean
  \<open>time_bounded_conv M (\<lambda>n. n + n div q)\<close> on \<^emph>\<open>all\<close> inputs: that clean form
  is not attainable for a machine whose small-input computation exceeds the
  convention floor \<open>n + 2\<close>.  The minimal witness \<open>CE\<close> below is a deterministic,
  valid machine over the empty input alphabet that accepts the empty input in
  exactly \<^emph>\<open>three\<close> steps (state chain \<open>0 \<rightarrow> 1 \<rightarrow> 2 \<rightarrow> 3\<close>, reading and
  rewriting the left endmarker in place), one more than the floor
  \<open>length [] + 2 = 2\<close>.  So \<open>[] \<in> Lang_mttm CE\<close> yet
  \<open>\<not> accepts_in_time_mttm CE [] 2\<close>, hence \<open>time_bounded_conv CE (\<lambda>n. n + n div q)\<close>
  fails at \<open>[]\<close> for every \<open>q\<close>.  \<open>CE\<close> stands in for the encoding wrap, whose
  own setup phases (\<open>W_Init \<rightarrow> W_Buf \<rightarrow> W_Reset \<rightarrow> W_Disp\<close>) likewise exceed the
  floor on tiny inputs; closing the small-input band needs the non-effective
  finite-exceptions table (an existence-only object; see \<open>time_cleanup\<close>),
  which is exactly what the clean form would
  demand and what the speedup construction does not build.\<close>

definition ce_read :: "nat \<Rightarrow> nat" where
  "ce_read = (\<lambda>j. if j = 0 then 1 else 0)"

definition ce_delta ::
  "(nat \<times> (nat \<Rightarrow> nat) \<times> nat \<times> (nat \<Rightarrow> nat) \<times> (nat \<Rightarrow> dir)) set" where
  "ce_delta = {(0, ce_read, 1, ce_read, \<lambda>_. dir.N),
               (1, ce_read, 2, ce_read, \<lambda>_. dir.N),
               (2, ce_read, 3, ce_read, \<lambda>_. dir.N)}"

definition CE :: "(nat, nat) mttm" where
  "CE = MTTM {0,1,2,3,4} {} {0,1} 0 1 ce_delta 0 3 4 1"

definition ce_tape :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "ce_tape = (\<lambda>i n. if i = 0 \<and> n = 0 then 1 else 0)"

abbreviation ce_cfg :: "nat \<Rightarrow> (nat, nat) mt_config" where
  "ce_cfg q \<equiv> Config\<^sub>M q ce_tape (\<lambda>_. 0)"

lemma ce_delta_tm: "delta_tm CE = ce_delta" by (simp add: CE_def)
lemma ce_t_tm: "t_tm CE = 3" by (simp add: CE_def)

lemma ce_read_eq: "(\<lambda>k. ce_tape k ((\<lambda>_. 0::nat) k)) = ce_read"
  by (simp add: ce_tape_def ce_read_def fun_eq_iff)

lemma ce_valid: "valid_mttm CE"
  by (auto simp: CE_def ce_delta_def ce_read_def Pi_iff)

lemma ce_det: "det_mttm CE"
  by (auto simp: det_mttm_def ce_delta_tm ce_delta_def)

lemma ce_init: "init_config_mttm CE [] = ce_cfg 0"
  by (auto simp: CE_def ce_tape_def fun_eq_iff)

text \<open>Forward: each state \<open>m \<le> 2\<close> steps deterministically to \<open>m + 1\<close>, the
  tape and heads unchanged (the endmarker is re-read and re-written in place).\<close>

lemma ce_step_fwd:
  assumes "m \<le> 2"
  shows "(ce_cfg m, ce_cfg (Suc m)) \<in> mttm_step ce_delta"
proof -
  have mem: "(m, ce_read, Suc m, ce_read, \<lambda>_. dir.N) \<in> ce_delta"
    using assms unfolding ce_delta_def by (cases m; simp; presburger)
  have upd: "(\<lambda>k. (ce_tape k)((\<lambda>_. 0::nat) k := ce_read k)) = ce_tape"
    by (simp add: ce_tape_def ce_read_def fun_eq_iff)
  have mov: "(\<lambda>k. go_dir ((\<lambda>_. dir.N) k) ((\<lambda>_. 0::nat) k)) = (\<lambda>_. 0)"
    by simp
  have "(Config\<^sub>M m ce_tape (\<lambda>_. 0),
         Config\<^sub>M (Suc m) (\<lambda>k. (ce_tape k)((\<lambda>_. 0) k := ce_read k))
                          (\<lambda>k. go_dir ((\<lambda>_. dir.N) k) ((\<lambda>_. 0) k)))
          \<in> mttm_step ce_delta"
    by (rule mttm_step.step) (use mem ce_read_eq in simp)
  thus ?thesis by (simp add: upd mov)
qed

text \<open>Backward: from state \<open>m\<close> the \<^emph>\<open>only\<close> successor is state \<open>m + 1\<close> ---
  the single \<open>ce_delta\<close> entry with source \<open>m\<close>, tape and heads fixed.\<close>

lemma ce_delta_inv:
  "(m, ce_read, q', a, dir) \<in> ce_delta \<Longrightarrow> q' = Suc m \<and> a = ce_read \<and> dir = (\<lambda>_. dir.N)"
  by (auto simp: ce_delta_def)

lemma ce_step_unique:
  "(ce_cfg m, cM) \<in> mttm_step ce_delta \<Longrightarrow> cM = ce_cfg (Suc m)"
  by (auto elim!: mttm_step.cases
           simp: ce_delta_def ce_tape_def ce_read_def fun_eq_iff)

text \<open>Reachability: in \<open>n \<le> 2\<close> steps from the start the machine is in state
  \<open>n \<le> 2 \<noteq> 3\<close> --- so it cannot have accepted.\<close>

lemma ce_reach:
  "(ce_cfg 0, cM) \<in> (mttm_step ce_delta) ^^ n \<Longrightarrow> n \<le> 2 \<Longrightarrow> cM = ce_cfg n"
proof (induction n arbitrary: cM)
  case 0
  then show ?case by simp
next
  case (Suc m)
  from Suc.prems(1) obtain c where
    rm: "(ce_cfg 0, c) \<in> (mttm_step ce_delta) ^^ m" and
    st: "(c, cM) \<in> mttm_step ce_delta"
    by (auto elim: relpow_Suc_E)
  have "m \<le> 2" using Suc.prems(2) by simp
  from Suc.IH[OF rm this] have "c = ce_cfg m" .
  with st have "(ce_cfg m, cM) \<in> mttm_step ce_delta" by simp
  from ce_step_unique[OF this] show ?case .
qed

lemma ce_lang: "[] \<in> Lang_mttm CE"
proof -
  have s0: "(ce_cfg 0, ce_cfg (Suc 0)) \<in> mttm_step ce_delta"
    by (rule ce_step_fwd) simp
  have s1: "(ce_cfg (Suc 0), ce_cfg (Suc (Suc 0))) \<in> mttm_step ce_delta"
    by (rule ce_step_fwd) simp
  have s2: "(ce_cfg (Suc (Suc 0)), ce_cfg (Suc (Suc (Suc 0)))) \<in> mttm_step ce_delta"
    by (rule ce_step_fwd) simp
  have "(ce_cfg 0, ce_cfg (Suc (Suc (Suc 0)))) \<in> (mttm_step ce_delta) ^^ (Suc (Suc (Suc 0)))"
    by (rule relpow_Suc_I2[OF s0 relpow_Suc_I2[OF s1 relpow_Suc_I2[OF s2 relpow_0_I]]])
  hence "(ce_cfg 0, ce_cfg (Suc (Suc (Suc 0)))) \<in> (mttm_step ce_delta)\<^sup>*"
    by (rule relpow_imp_rtrancl)
  hence "(init_config_mttm CE [], Config\<^sub>M (t_tm CE) ce_tape (\<lambda>_. 0))
           \<in> (mttm_step (delta_tm CE))\<^sup>*"
    by (simp add: ce_init ce_delta_tm ce_t_tm numeral_3_eq_3)
  thus ?thesis
    unfolding Lang_mttm_def by (auto simp: CE_def)
qed

lemma ce_not_accepts: "\<not> accepts_in_time_mttm CE [] 2"
proof
  assume "accepts_in_time_mttm CE [] 2"
  then obtain n cM where nle: "n \<le> 2"
    and reach: "(init_config_mttm CE [], cM) \<in> (mttm_step (delta_tm CE)) ^^ n"
    and acc: "mt_state cM = t_tm CE"
    unfolding accepts_in_time_mttm_def by blast
  from reach have "(ce_cfg 0, cM) \<in> (mttm_step ce_delta) ^^ n"
    by (simp add: ce_init ce_delta_tm)
  from ce_reach[OF this nle] have "mt_state cM = n" by simp
  with acc nle show False by (simp add: ce_t_tm)
qed

theorem clean_convention_unattainable:
  "\<not> time_bounded_conv CE (\<lambda>n. n + n div q)"
proof
  assume "time_bounded_conv CE (\<lambda>n. n + n div q)"
  hence "\<forall>w\<in>Lang_mttm CE.
           accepts_in_time_mttm CE w (max (length w + 2) (length w + length w div q))"
    by (simp add: time_bounded_conv_def)
  from bspec[OF this ce_lang] have "accepts_in_time_mttm CE [] 2"
    by (simp add: numeral_2_eq_2)
  with ce_not_accepts show False by simp
qed

end
