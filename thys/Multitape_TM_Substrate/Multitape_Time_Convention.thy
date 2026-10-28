theory Multitape_Time_Convention
  imports Multitape_Finite_Patch
begin

section \<open>Time bounds in the textbook convention, and the cleanup\<close>

text \<open>Shared vocabulary for the linear-speedup consumers.  An
  \<^emph>\<open>eventual\<close> bound holds for all long enough inputs in the language; a
  \<^emph>\<open>convention\<close> bound is the Hopcroft--Ullman
  \<^cite>\<open>\<open>p.~291\<close> in "Hopcroft1979:introduction"\<close> \<open>max(n+1, ...)\<close> form on
  the substrate, where the floor is \<open>n + 2\<close> (the substrate reads the
  left endmarker before the first input symbol).\<close>

definition time_bounded_ev :: "('q, 'a) ktm \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> bool" where
  "time_bounded_ev M g \<longleftrightarrow>
     (\<exists>N. \<forall>w\<in>Lang_ktm M. N \<le> length w
             \<longrightarrow> accepts_in_time_ktm M w (g (length w)))"

definition time_bounded_conv :: "('q, 'a) ktm \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> bool" where
  "time_bounded_conv M g \<longleftrightarrow>
     (\<forall>w\<in>Lang_ktm M.
        accepts_in_time_ktm M w (max (length w + 2) (g (length w))))"

text \<open>The cleanup corollary: an eventual bound is upgraded to a
  convention bound on \<^emph>\<open>all\<close> inputs, at the cost of the finite-control
  overhead \<open>c0 = 2 * N + 4\<close>, with language, tape count, and determinism
  preserved.  Instantiates @{const finite_patch} with the (finite, hence
  unconditionally available) table \<open>w \<in> Lang_ktm M\<close>.

  Hypotheses are the weakest the proof uses --- @{const valid_ktm} and
  \<open>bl_ktm M \<noteq> le_ktm M\<close>, matching the @{const finite_patch} contract
  lemmas it composes (\<open>finite_patch_language\<close> / \<open>_det\<close> /
  \<open>fp_short_time\<close> / \<open>fp_long_time\<close>).  In particular it does \<^emph>\<open>not\<close>
  require @{const le_unique} or the state distinctness of
  @{const well_formed_ktm}, so it applies to machines (e.g. the
  encoding wrap) whose \<open>le\<close>-uniqueness is not separately established.\<close>

theorem time_cleanup:
  assumes vM: "valid_ktm M" and blle: "bl_ktm M \<noteq> le_ktm M"
    and ev: "time_bounded_ev M g"
  obtains N where
    "Lang_ktm (finite_patch M (\<lambda>w. w \<in> Lang_ktm M) N) = Lang_ktm M"
    and "k_ktm (finite_patch M (\<lambda>w. w \<in> Lang_ktm M) N) = k_ktm M"
    and "det_ktm M \<longrightarrow> det_ktm (finite_patch M (\<lambda>w. w \<in> Lang_ktm M) N)"
    and "time_bounded_conv (finite_patch M (\<lambda>w. w \<in> Lang_ktm M) N)
           (\<lambda>n. g n + (2 * N + 4))"
proof -
  from ev obtain N where evN: "\<forall>w\<in>Lang_ktm M. N \<le> length w
                                 \<longrightarrow> accepts_in_time_ktm M w (g (length w))"
    unfolding time_bounded_ev_def by blast
  let ?M' = "finite_patch M (\<lambda>w. w \<in> Lang_ktm M) N"
  have lang: "Lang_ktm ?M' = Lang_ktm M"
  proof -
    have "Lang_ktm ?M' = {w. set w \<subseteq> Sigma_ktm M
             \<and> (if length w \<le> N then w \<in> Lang_ktm M else w \<in> Lang_ktm M)}"
      by (rule finite_patch_language[OF vM blle])
    also have "\<dots> = {w. set w \<subseteq> Sigma_ktm M \<and> w \<in> Lang_ktm M}" by simp
    also have "\<dots> = Lang_ktm M" unfolding Lang_ktm_def by auto
    finally show ?thesis .
  qed
  have kpres: "k_ktm ?M' = k_ktm M" by (rule finite_patch_k_ktm)
  have detpres: "det_ktm M \<longrightarrow> det_ktm ?M'"
    using finite_patch_det[OF vM blle] by blast
  have conv: "time_bounded_conv ?M' (\<lambda>n. g n + (2 * N + 4))"
    unfolding time_bounded_conv_def
  proof
    fix w assume "w \<in> Lang_ktm ?M'"
    hence wL: "w \<in> Lang_ktm M" using lang by simp
    have wSg: "set w \<subseteq> Sigma_ktm M" using wL unfolding Lang_ktm_def by simp
    show "accepts_in_time_ktm ?M' w
            (max (length w + 2) ((\<lambda>n. g n + (2 * N + 4)) (length w)))"
    proof (cases "length w \<le> N")
      case True
      have "accepts_in_time_ktm ?M' w (length w + 2)"
        using vM wSg True wL by (rule fp_short_time)
      moreover have "length w + 2 \<le> max (length w + 2) (g (length w) + (2 * N + 4))"
        by simp
      ultimately show ?thesis by (auto elim: accepts_in_time_ktm_mono)
    next
      case False
      hence Nlt: "N < length w" by simp
      have "accepts_in_time_ktm M w (g (length w))" using evN wL Nlt by simp
      hence "accepts_in_time_ktm ?M' w (g (length w) + (2 * N + 4))"
        by (rule fp_long_time[OF vM wSg Nlt])
      moreover have "g (length w) + (2 * N + 4)
                       \<le> max (length w + 2) (g (length w) + (2 * N + 4))" by simp
      ultimately show ?thesis by (auto elim: accepts_in_time_ktm_mono)
    qed
  qed
  show thesis
  proof (rule that[of N])
    show "Lang_ktm ?M' = Lang_ktm M" by (rule lang)
    show "k_ktm ?M' = k_ktm M" by (rule kpres)
    show "det_ktm M \<longrightarrow> det_ktm ?M'" by (rule detpres)
    show "time_bounded_conv ?M' (\<lambda>n. g n + (2 * N + 4))" by (rule conv)
  qed
qed


subsection \<open>The clean convention form is unattainable in general\<close>

text \<open>Why the linear-\<open>T\<close> speedup theorems are stated with a residual
  \<open>+K\<close> (all inputs) or an explicit threshold (eventual), never as the clean
  \<open>time_bounded_conv M (\<lambda>n. n + n div q)\<close> on \<^emph>\<open>all\<close> inputs: that clean form
  is not attainable for a machine whose small-input computation exceeds the
  convention floor \<open>n + 2\<close>.  The minimal witness \<open>conv_cex_ktm\<close> below
  (the convention's counterexample) is a deterministic, valid machine over the
  empty input alphabet that accepts the empty input in exactly
  \<^emph>\<open>three\<close> steps (state chain \<open>0 \<rightarrow> 1 \<rightarrow> 2 \<rightarrow> 3\<close>, reading and
  rewriting the left endmarker in place), one more than the floor
  \<open>length [] + 2 = 2\<close>.  So \<open>[] \<in> Lang_ktm conv_cex_ktm\<close> yet
  \<open>\<not> accepts_in_time_ktm conv_cex_ktm [] 2\<close>, hence
  \<open>time_bounded_conv conv_cex_ktm (\<lambda>n. n + n div q)\<close> fails at \<open>[]\<close> for
  every \<open>q\<close>.  \<open>conv_cex_ktm\<close> stands in for the encoding wrap, whose
  own setup phases (\<open>W_Init \<rightarrow> W_Buf \<rightarrow> W_Reset \<rightarrow> W_Disp\<close>) likewise exceed the
  floor on tiny inputs; closing the small-input band needs the non-effective
  finite-exceptions table (an existence-only object; see \<open>time_cleanup\<close>),
  which is exactly what the clean form would
  demand and what the speedup construction does not build.\<close>

definition conv_cex_delta ::
  "(nat \<times> (nat \<Rightarrow> nat) \<times> nat \<times> (nat \<Rightarrow> nat) \<times> (nat \<Rightarrow> move)) set" where
  "conv_cex_delta = {(0, one_tape_read 1, 1, one_tape_read 1, \<lambda>_. MoveN),
                     (1, one_tape_read 1, 2, one_tape_read 1, \<lambda>_. MoveN),
                     (2, one_tape_read 1, 3, one_tape_read 1, \<lambda>_. MoveN)}"

definition conv_cex_ktm :: "(nat, nat) ktm" where
  "conv_cex_ktm = KTM {0,1,2,3,4} {} {0,1} 0 1 conv_cex_delta 0 3 4 1"

definition conv_cex_tape :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "conv_cex_tape = (\<lambda>i n. if i = 0 \<and> n = 0 then 1 else 0)"

abbreviation conv_cex_cfg :: "nat \<Rightarrow> (nat, nat) ktc_config" where
  "conv_cex_cfg q \<equiv> KConfig q conv_cex_tape (\<lambda>_. 0)"

lemma conv_cex_delta_ktm: "delta_ktm conv_cex_ktm = conv_cex_delta"
  by (simp add: conv_cex_ktm_def)
lemma conv_cex_t_ktm: "t_ktm conv_cex_ktm = 3" by (simp add: conv_cex_ktm_def)

lemma conv_cex_read_eq: "(\<lambda>k. conv_cex_tape k ((\<lambda>_. 0::nat) k)) = one_tape_read 1"
  by (simp add: conv_cex_tape_def one_tape_read_def fun_eq_iff)

lemma conv_cex_valid: "valid_ktm conv_cex_ktm"
  by (auto simp: conv_cex_ktm_def conv_cex_delta_def one_tape_read_def Pi_iff)

lemma conv_cex_det: "det_ktm conv_cex_ktm"
  by (auto simp: det_ktm_def conv_cex_delta_ktm conv_cex_delta_def)

lemma conv_cex_init: "init_config_ktm conv_cex_ktm [] = conv_cex_cfg 0"
  by (auto simp: conv_cex_ktm_def conv_cex_tape_def fun_eq_iff)

text \<open>Forward: each state \<open>m \<le> 2\<close> steps deterministically to \<open>m + 1\<close>, the
  tape and heads unchanged (the endmarker is re-read and re-written in place).\<close>

lemma conv_cex_step_fwd:
  assumes "m \<le> 2"
  shows "(conv_cex_cfg m, conv_cex_cfg (Suc m)) \<in> ktm_step conv_cex_delta"
proof -
  have mem: "(m, one_tape_read 1, Suc m, one_tape_read 1, \<lambda>_. MoveN) \<in> conv_cex_delta"
    using assms unfolding conv_cex_delta_def by (cases m; simp; presburger)
  have upd: "(\<lambda>k. (conv_cex_tape k)((\<lambda>_. 0::nat) k := one_tape_read 1 k)) = conv_cex_tape"
    by (simp add: conv_cex_tape_def one_tape_read_def fun_eq_iff)
  have mov: "(\<lambda>k. go_move ((\<lambda>_. MoveN) k) ((\<lambda>_. 0::nat) k)) = (\<lambda>_. 0)"
    by simp
  have "(KConfig m conv_cex_tape (\<lambda>_. 0),
         KConfig (Suc m) (\<lambda>k. (conv_cex_tape k)((\<lambda>_. 0) k := one_tape_read 1 k))
                          (\<lambda>k. go_move ((\<lambda>_. MoveN) k) ((\<lambda>_. 0) k)))
          \<in> ktm_step conv_cex_delta"
    by (rule ktm_step.step) (use mem conv_cex_read_eq in simp)
  thus ?thesis using upd mov by simp
qed

text \<open>Backward: from state \<open>m\<close> the \<^emph>\<open>only\<close> successor is state \<open>m + 1\<close> ---
  the single \<open>conv_cex_delta\<close> entry with source \<open>m\<close>, tape and heads fixed.\<close>

lemma conv_cex_delta_inv:
  "(m, one_tape_read 1, q', a, move) \<in> conv_cex_delta \<Longrightarrow> q' = Suc m \<and> a = one_tape_read 1 \<and> move = (\<lambda>_. MoveN)"
  by (auto simp: conv_cex_delta_def)

lemma conv_cex_step_unique:
  "(conv_cex_cfg m, cM) \<in> ktm_step conv_cex_delta \<Longrightarrow> cM = conv_cex_cfg (Suc m)"
  by (auto elim!: ktm_step.cases
           simp: conv_cex_delta_def conv_cex_tape_def one_tape_read_def fun_eq_iff)

text \<open>Reachability: in \<open>n \<le> 2\<close> steps from the start the machine is in state
  \<open>n \<le> 2 \<noteq> 3\<close> --- so it cannot have accepted.\<close>

lemma conv_cex_reach:
  "(conv_cex_cfg 0, cM) \<in> (ktm_step conv_cex_delta) ^^ n \<Longrightarrow> n \<le> 2 \<Longrightarrow> cM = conv_cex_cfg n"
proof (induction n arbitrary: cM)
  case 0
  then show ?case by simp
next
  case (Suc m)
  from Suc.prems(1) obtain c where
    rm: "(conv_cex_cfg 0, c) \<in> (ktm_step conv_cex_delta) ^^ m" and
    st: "(c, cM) \<in> ktm_step conv_cex_delta"
    by (auto elim: relpow_Suc_E)
  have "m \<le> 2" using Suc.prems(2) by simp
  from Suc.IH[OF rm this] have "c = conv_cex_cfg m" .
  with st have "(conv_cex_cfg m, cM) \<in> ktm_step conv_cex_delta" by simp
  from conv_cex_step_unique[OF this] show ?case .
qed

lemma conv_cex_lang: "[] \<in> Lang_ktm conv_cex_ktm"
proof -
  have s0: "(conv_cex_cfg 0, conv_cex_cfg (Suc 0)) \<in> ktm_step conv_cex_delta"
    by (rule conv_cex_step_fwd) simp
  have s1: "(conv_cex_cfg (Suc 0), conv_cex_cfg (Suc (Suc 0))) \<in> ktm_step conv_cex_delta"
    by (rule conv_cex_step_fwd) simp
  have s2: "(conv_cex_cfg (Suc (Suc 0)), conv_cex_cfg (Suc (Suc (Suc 0)))) \<in> ktm_step conv_cex_delta"
    by (rule conv_cex_step_fwd) simp
  have "(conv_cex_cfg 0, conv_cex_cfg (Suc (Suc (Suc 0)))) \<in> (ktm_step conv_cex_delta) ^^ (Suc (Suc (Suc 0)))"
    by (rule relpow_Suc_I2[OF s0 relpow_Suc_I2[OF s1 relpow_Suc_I2[OF s2 relpow_0_I]]])
  hence "(conv_cex_cfg 0, conv_cex_cfg (Suc (Suc (Suc 0)))) \<in> (ktm_step conv_cex_delta)\<^sup>*"
    by (rule relpow_imp_rtrancl)
  hence "(init_config_ktm conv_cex_ktm [], KConfig (t_ktm conv_cex_ktm) conv_cex_tape (\<lambda>_. 0))
           \<in> (ktm_step (delta_ktm conv_cex_ktm))\<^sup>*"
    by (simp add: conv_cex_init conv_cex_delta_ktm conv_cex_t_ktm numeral_3_eq_3)
  thus ?thesis
    unfolding Lang_ktm_def by (auto simp: conv_cex_ktm_def)
qed

lemma conv_cex_not_accepts: "\<not> accepts_in_time_ktm conv_cex_ktm [] 2"
proof
  assume "accepts_in_time_ktm conv_cex_ktm [] 2"
  then obtain n cM where nle: "n \<le> 2"
    and reach: "(init_config_ktm conv_cex_ktm [], cM) \<in> (ktm_step (delta_ktm conv_cex_ktm)) ^^ n"
    and acc: "ktc_state cM = t_ktm conv_cex_ktm"
    unfolding accepts_in_time_ktm_def by blast
  from reach have "(conv_cex_cfg 0, cM) \<in> (ktm_step conv_cex_delta) ^^ n"
    by (simp add: conv_cex_init conv_cex_delta_ktm)
  from conv_cex_reach[OF this nle] have "ktc_state cM = n" by simp
  with acc nle show False by (simp add: conv_cex_t_ktm)
qed

theorem clean_convention_unattainable:
  "\<not> time_bounded_conv conv_cex_ktm (\<lambda>n. n + n div q)"
proof
  assume "time_bounded_conv conv_cex_ktm (\<lambda>n. n + n div q)"
  hence "\<forall>w\<in>Lang_ktm conv_cex_ktm.
           accepts_in_time_ktm conv_cex_ktm w (max (length w + 2) (length w + length w div q))"
    by (simp add: time_bounded_conv_def)
  from bspec[OF this conv_cex_lang] have "accepts_in_time_ktm conv_cex_ktm [] 2"
    by (simp add: numeral_2_eq_2)
  with conv_cex_not_accepts show False by simp
qed

end
