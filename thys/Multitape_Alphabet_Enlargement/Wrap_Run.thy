theory Wrap_Run
  imports Wrap_Reset
begin

section \<open>Faithful (k-tape) plant-\<open>le\<close> wrap: the transposed run\<close>

text \<open>The run phase of the plant wrap dispatches to @{const wrap_run_delta},
  the shared transposed-run family, on @{text W_Run} states.  The correspondence
  lemmas below --- an M-step lifts to a wrap-step and back --- rest on two facts
  about @{const wrap_delta}: it \<^emph>\<open>contains\<close> @{const wrap_run_delta},
  and its only @{text W_Run}-sourced transitions are in @{const wrap_run_delta}
  (the other eight families source from @{text W_Init} / @{text "W_Buf"} /
  @{text W_Reset} / @{text W_Disp}).  This is the run correspondence for the
  faithful \<open>k\<close>-tape wrap.\<close>


subsection \<open>Forward simulation: an M-step lifts to a wrap-step\<close>

lemma run_step_forward:
  assumes vM: "valid_mttm M"
      and k2: "2 \<le> k_tm M"
      and val_cM: "valid_config_mttm M cM"
      and step_M: "(cM, cM') \<in> mttm_step (delta_tm M)"
    shows "(lift_M_config M cM, lift_M_config M cM')
           \<in> mttm_step (wrap_delta M pack c \<Sigma>u)"
proof -
  obtain Q \<Sigma>i \<Gamma> bl le \<delta>M sM tM rM kM where M_eq:
    "M = MTTM Q \<Sigma>i \<Gamma> bl le \<delta>M sM tM rM kM"
    by (cases M)
  obtain q ts n where cM_eq: "cM = Config\<^sub>M q ts n"
    by (cases cM)
  obtain q' a d where cM'_eq:
    "cM' = Config\<^sub>M q' (\<lambda>k. (ts k)(n k := a k))
                     (\<lambda>k. go_dir (d k) (n k))"
    and tr: "(q, (\<lambda>k. ts k (n k)), q', a, d) \<in> delta_tm M"
    using step_M cM_eq by (auto elim: mttm_step.cases)

  have bl_in: "bl_tm M \<in> \<Gamma>_tm M" by (rule valid_mttm_blank_in_Gamma[OF vM])
  have le_in: "le_tm M \<in> \<Gamma>_tm M" by (rule valid_mttm_LE_in_Gamma[OF vM])

  from val_cM cM_eq M_eq have ts_Gamma: "\<And>k m. ts k m \<in> \<Gamma>_tm M"
    by (auto simp: M_eq)
  have ts_tail: "\<forall>i\<ge>k_tm M. \<forall>p. ts i p = bl_tm M"
    using val_cM unfolding cM_eq by (cases M) auto
  have a_tail: "\<forall>j\<ge>k_tm M. a j = bl_tm M"
  proof (intro allI impI)
    fix j assume "k_tm M \<le> j"
    thus "a j = bl_tm M" using valid_mttm_delta_support[OF vM tr] by blast
  qed

  let ?src = "lift_M_config M cM"
  let ?dst = "lift_M_config M cM'"
  let ?lift_ts =
    "\<lambda>p m. if p < k_tm M then Enc (ts (wrap_tau p) m) else Enc (bl_tm M)"
  let ?lift_n = "\<lambda>p. n (wrap_tau p)"
  let ?sym = "\<lambda>p. ?lift_ts p (?lift_n p)"
  let ?\<sigma> = "\<lambda>k. ts k (n k)"
  let ?wrap_a = "\<lambda>p. Enc (a (wrap_tau p))"
  let ?wrap_dir = "\<lambda>p. d (wrap_tau p)"

  have src_unfold: "?src = Config\<^sub>M (W_Run q) ?lift_ts ?lift_n"
    unfolding lift_M_config_def cM_eq by (simp add: fun_eq_iff)

  have sym_eq: "\<forall>p. ?sym p = Enc (?\<sigma> (wrap_tau p))"
  proof
    fix p
    show "?sym p = Enc (?\<sigma> (wrap_tau p))"
    proof (cases "p < k_tm M")
      case True
      thus ?thesis by simp
    next
      case False
      hence jge: "k_tm M \<le> p" by simp
      with k2 have "2 \<le> p" by simp
      hence wtp: "wrap_tau p = p" by (rule wrap_tau_ge2_id)
      have "?sym p = Enc (bl_tm M)" using False by simp
      moreover have "?\<sigma> (wrap_tau p) = bl_tm M"
        using wtp jge ts_tail by simp
      ultimately show ?thesis by simp
    qed
  qed

  have sym_range: "?sym \<in> UNIV \<rightarrow> Raw ` \<Sigma>u \<union> Enc ` \<Gamma>_tm M"
    using bl_in ts_Gamma by auto

  have tuple_in_run:
    "(W_Run q, ?sym, W_Run q', ?wrap_a, ?wrap_dir) \<in> wrap_run_delta M \<Sigma>u"
    unfolding wrap_run_delta_def
    using tr sym_eq sym_range by blast
  hence tuple_in:
    "(W_Run q, ?sym, W_Run q', ?wrap_a, ?wrap_dir) \<in> wrap_delta M pack c \<Sigma>u"
    by (simp add: wrap_delta_def)

  have step_holds:
    "(Config\<^sub>M (W_Run q) ?lift_ts ?lift_n,
      Config\<^sub>M (W_Run q')
        (\<lambda>p. (?lift_ts p)(?lift_n p := ?wrap_a p))
        (\<lambda>p. go_dir (?wrap_dir p) (?lift_n p)))
     \<in> mttm_step (wrap_delta M pack c \<Sigma>u)"
    by (rule mttm_step.step
          [where ts = ?lift_ts and n = ?lift_n
                 and a = ?wrap_a and dir = ?wrap_dir, OF tuple_in])

  have dst_unfold:
    "?dst = Config\<^sub>M (W_Run q')
              (\<lambda>p. (?lift_ts p)(?lift_n p := ?wrap_a p))
              (\<lambda>p. go_dir (?wrap_dir p) (?lift_n p))"
    unfolding lift_M_config_def cM'_eq
    using ts_tail a_tail k2
    by (auto simp: fun_eq_iff wrap_tau_ge2_id)

  show ?thesis
    unfolding src_unfold dst_unfold by (rule step_holds)
qed


subsection \<open>State-routing exclusion\<close>

text \<open>Only @{const wrap_run_delta} contains a tuple whose source state is
  @{term "W_Run q"}; the other eight families of @{const wrap_delta} source
  from @{text W_Init}, @{text "W_Buf ws"}, @{text W_Reset}, or @{text W_Disp}
  (the storage rewind loop and the plant-done step both from @{text W_Reset}).\<close>

lemma wrap_delta_W_Run_source_only_run:
  fixes M :: "('q, 'b) mttm"
    and sym :: "nat \<Rightarrow> ('a, 'b) wrap_alphabet"
    and qs' :: "('q, 'a, 'b) wrap_state"
    and a' :: "nat \<Rightarrow> ('a, 'b) wrap_alphabet"
    and dir :: "nat \<Rightarrow> dir"
  assumes "(W_Run q, sym, qs', a', dir) \<in> wrap_delta M pack c \<Sigma>u"
  shows "(W_Run q, sym, qs', a', dir) \<in> wrap_run_delta M \<Sigma>u"
  using assms
  unfolding wrap_delta_def wrap_init_delta_gen_def wrap_buf_extend_delta_gen_def
            wrap_buf_close_delta_gen_def wrap_buf_empty_end_delta_gen_def
            wrap_buf_nonempty_end_delta_gen_def wrap_rewind_loop_delta_gen_def
            wrap_plant_done_delta_def wrap_disp_delta_gen_def
  by auto


subsection \<open>Reverse simulation: a wrap-step projects to an M-step\<close>

lemma run_step_reverse:
  assumes vM: "valid_mttm M"
      and k2: "2 \<le> k_tm M"
      and val_cM: "valid_config_mttm M cM"
      and step_wrap:
        "(lift_M_config M cM, C') \<in> mttm_step (wrap_delta M pack c \<Sigma>u)"
    shows "\<exists>cM'. C' = lift_M_config M cM'
              \<and> (cM, cM') \<in> mttm_step (delta_tm M)"
proof -
  obtain q ts n where cM_eq: "cM = Config\<^sub>M q ts n"
    by (cases cM)

  let ?lift_ts =
    "\<lambda>p m. if p < k_tm M then Enc (ts (wrap_tau p) m) else Enc (bl_tm M)"
  let ?lift_n = "\<lambda>p. n (wrap_tau p)"

  have ts_tail: "\<forall>i\<ge>k_tm M. \<forall>p. ts i p = bl_tm M"
    using val_cM unfolding cM_eq by (cases M) auto

  have src_eq:
    "lift_M_config M cM = Config\<^sub>M (W_Run q) ?lift_ts ?lift_n"
    unfolding lift_M_config_def cM_eq by (simp add: fun_eq_iff)

  note step_wrap' = step_wrap[unfolded src_eq]
  from step_wrap' obtain qs' a' dir' where
    C'_eq:
      "C' = Config\<^sub>M qs'
              (\<lambda>x. (?lift_ts x)(?lift_n x := a' x))
              (\<lambda>x. go_dir (dir' x) (?lift_n x))"
    and tuple_in:
      "(W_Run q, \<lambda>x. ?lift_ts x (?lift_n x), qs', a', dir')
         \<in> wrap_delta M pack c \<Sigma>u"
    by (auto elim: mttm_step.cases)

  have tuple_run:
    "(W_Run q, \<lambda>x. ?lift_ts x (?lift_n x), qs', a', dir')
       \<in> wrap_run_delta M \<Sigma>u"
    by (rule wrap_delta_W_Run_source_only_run[OF tuple_in])

  from tuple_run[unfolded wrap_run_delta_def mem_Collect_eq]
  obtain qa \<sigma> q'_in \<sigma>'_M d sym_pat where
    raw: "(W_Run q, \<lambda>x. ?lift_ts x (?lift_n x), qs', a', dir')
            = (W_Run qa, sym_pat, W_Run q'_in,
               (\<lambda>p. Enc (\<sigma>'_M (wrap_tau p))), (\<lambda>p. d (wrap_tau p)))"
    and tr_M_pre: "(qa, \<sigma>, q'_in, \<sigma>'_M, d) \<in> delta_tm M"
    and sym_pat_eq: "\<forall>p. sym_pat p = Enc (\<sigma> (wrap_tau p))"
    and sym_range: "sym_pat \<in> UNIV \<rightarrow> Raw ` \<Sigma>u \<union> Enc ` \<Gamma>_tm M"
    by blast

  from raw have q_eq: "qa = q" by simp
  from raw have read_eq: "(\<lambda>x. ?lift_ts x (?lift_n x)) = sym_pat" by simp
  from raw have qs'_eq: "qs' = W_Run q'_in" by simp
  from raw have a'_eq: "a' = (\<lambda>p. Enc (\<sigma>'_M (wrap_tau p)))" by simp
  from raw have dir'_eq: "dir' = (\<lambda>p. d (wrap_tau p))" by simp

  have sigma_eq: "\<sigma> = (\<lambda>k. ts k (n k))"
  proof (rule ext)
    fix k
    have rk: "?lift_ts (wrap_tau k) (?lift_n (wrap_tau k)) = sym_pat (wrap_tau k)"
      using fun_cong[OF read_eq, of "wrap_tau k"] by simp
    have sk: "sym_pat (wrap_tau k) = Enc (\<sigma> k)"
      using sym_pat_eq by simp
    show "\<sigma> k = ts k (n k)"
    proof (cases "k < k_tm M")
      case True
      have wk_lt: "wrap_tau k < k_tm M"
      proof (cases "k < 2")
        case True
        hence "wrap_tau k < 2" using wrap_tau_lt2 by simp
        thus ?thesis using k2 by simp
      next
        case False
        hence "2 \<le> k" by simp
        hence "wrap_tau k = k" by (rule wrap_tau_ge2_id)
        thus ?thesis using \<open>k < k_tm M\<close> by simp
      qed
      have "Enc (\<sigma> k) = sym_pat (wrap_tau k)" using sk by (rule sym)
      also have "\<dots> = ?lift_ts (wrap_tau k) (?lift_n (wrap_tau k))"
        using rk by (rule sym)
      also have "\<dots> = Enc (ts k (n k))" using wk_lt by simp
      finally show ?thesis by simp
    next
      case False
      hence kge: "k_tm M \<le> k" by simp
      with k2 have "2 \<le> k" by simp
      hence wk: "wrap_tau k = k" by (rule wrap_tau_ge2_id)
      have "Enc (\<sigma> k) = sym_pat (wrap_tau k)" using sk by (rule sym)
      also have "\<dots> = ?lift_ts (wrap_tau k) (?lift_n (wrap_tau k))"
        using rk by (rule sym)
      also have "\<dots> = Enc (bl_tm M)" using wk kge by simp
      finally have "\<sigma> k = bl_tm M" by simp
      moreover have "ts k (n k) = bl_tm M" using ts_tail kge by simp
      ultimately show ?thesis by simp
    qed
  qed

  have tr_M: "(q, \<lambda>k. ts k (n k), q'_in, \<sigma>'_M, d) \<in> delta_tm M"
    using tr_M_pre q_eq sigma_eq by simp

  have sigma'_tail: "\<forall>j\<ge>k_tm M. \<sigma>'_M j = bl_tm M"
  proof (intro allI impI)
    fix j assume "k_tm M \<le> j"
    thus "\<sigma>'_M j = bl_tm M" using valid_mttm_delta_support[OF vM tr_M] by blast
  qed

  let ?cM' = "Config\<^sub>M q'_in (\<lambda>k. (ts k)(n k := \<sigma>'_M k))
                            (\<lambda>k. go_dir (d k) (n k))"
  have M_step: "(cM, ?cM') \<in> mttm_step (delta_tm M)"
    unfolding cM_eq
    by (rule mttm_step.step
          [where ts = ts and n = n and a = \<sigma>'_M and dir = d, OF tr_M])

  have C'_lift: "C' = lift_M_config M ?cM'"
    unfolding C'_eq qs'_eq a'_eq dir'_eq lift_M_config_def
    using ts_tail sigma'_tail k2
    by (auto simp: fun_eq_iff wrap_tau_ge2_id)

  show ?thesis using C'_lift M_step by blast
qed


subsection \<open>Iterated simulation\<close>

text \<open>An entire M-trace lifts to a wrap-trace of the same length, and vice
  versa --- iterating the single-step correspondence, threading
  @{const valid_config_mttm} through @{thm[source] valid_step_mttm}.\<close>

lemma run_steps_forward:
  assumes vM: "valid_mttm M"
      and k2: "2 \<le> k_tm M"
      and val_cM: "valid_config_mttm M cM"
      and steps_M: "(cM, cM') \<in> (mttm_step (delta_tm M))\<^sup>*"
    shows "(lift_M_config M cM, lift_M_config M cM')
           \<in> (mttm_step (wrap_delta M pack c \<Sigma>u))\<^sup>*"
proof -
  let ?R_W = "mttm_step (wrap_delta M pack c \<Sigma>u)"
  have helper:
    "valid_config_mttm M cM' \<and>
     (lift_M_config M cM, lift_M_config M cM') \<in> ?R_W\<^sup>*"
    using steps_M
  proof induction
    case base
    show ?case using val_cM by simp
  next
    case (step y z)
    from step.IH have val_y: "valid_config_mttm M y"
                  and ih_lift: "(lift_M_config M cM, lift_M_config M y) \<in> ?R_W\<^sup>*"
      by auto
    have val_z: "valid_config_mttm M z"
      by (rule valid_step_mttm[OF vM step.hyps(2) val_y])
    have step_lift: "(lift_M_config M y, lift_M_config M z) \<in> ?R_W"
      by (rule run_step_forward[OF vM k2 val_y step.hyps(2)])
    from ih_lift step_lift
    have lift_z: "(lift_M_config M cM, lift_M_config M z) \<in> ?R_W\<^sup>*"
      by (rule rtrancl_into_rtrancl)
    from val_z lift_z show ?case by simp
  qed
  thus ?thesis by simp
qed

lemma run_steps_forward_relpow:
  assumes vM: "valid_mttm M"
      and k2: "2 \<le> k_tm M"
      and val_cM: "valid_config_mttm M cM"
      and steps_M: "(cM, cM') \<in> (mttm_step (delta_tm M)) ^^ n"
    shows "(lift_M_config M cM, lift_M_config M cM')
           \<in> (mttm_step (wrap_delta M pack c \<Sigma>u)) ^^ n"
proof -
  let ?R_M = "mttm_step (delta_tm M)"
  let ?R_W = "mttm_step (wrap_delta M pack c \<Sigma>u)"
  have helper:
    "\<And>cM'. (cM, cM') \<in> ?R_M ^^ n \<Longrightarrow>
            valid_config_mttm M cM' \<and>
            (lift_M_config M cM, lift_M_config M cM') \<in> ?R_W ^^ n"
  proof (induction n)
    case 0
    fix cM'
    assume "(cM, cM') \<in> ?R_M ^^ 0"
    hence "cM' = cM" by simp
    thus "valid_config_mttm M cM' \<and>
          (lift_M_config M cM, lift_M_config M cM') \<in> ?R_W ^^ 0"
      using val_cM by simp
  next
    case (Suc n)
    fix cM'
    assume chain: "(cM, cM') \<in> ?R_M ^^ Suc n"
    from chain obtain y where
        prefix: "(cM, y) \<in> ?R_M ^^ n" and last: "(y, cM') \<in> ?R_M"
      by (auto elim: relpow_Suc_E)
    from Suc.IH[OF prefix] have
        val_y: "valid_config_mttm M y"
        and ih_lift: "(lift_M_config M cM, lift_M_config M y) \<in> ?R_W ^^ n"
      by auto
    have val_cM': "valid_config_mttm M cM'"
      by (rule valid_step_mttm[OF vM last val_y])
    have step_lift: "(lift_M_config M y, lift_M_config M cM') \<in> ?R_W"
      by (rule run_step_forward[OF vM k2 val_y last])
    from ih_lift step_lift
    have suc_chain:
      "(lift_M_config M cM, lift_M_config M cM') \<in> ?R_W ^^ Suc n"
      by (rule relpow_Suc_I)
    from val_cM' suc_chain show
      "valid_config_mttm M cM' \<and>
       (lift_M_config M cM, lift_M_config M cM') \<in> ?R_W ^^ Suc n"
      by simp
  qed
  show ?thesis using helper[OF steps_M] by simp
qed

lemma run_steps_reverse:
  assumes vM: "valid_mttm M"
      and k2: "2 \<le> k_tm M"
      and val_cM: "valid_config_mttm M cM"
      and steps_wrap:
        "(lift_M_config M cM, C') \<in> (mttm_step (wrap_delta M pack c \<Sigma>u))\<^sup>*"
    shows "\<exists>cM'. C' = lift_M_config M cM'
              \<and> (cM, cM') \<in> (mttm_step (delta_tm M))\<^sup>*
              \<and> valid_config_mttm M cM'"
  using steps_wrap
proof induction
  case base
  show ?case using val_cM by blast
next
  case (step y z)
  from step.IH obtain cM_y where
      y_lift: "y = lift_M_config M cM_y"
    and y_M: "(cM, cM_y) \<in> (mttm_step (delta_tm M))\<^sup>*"
    and val_y: "valid_config_mttm M cM_y"
    by blast
  from step.hyps(2) y_lift have
    "(lift_M_config M cM_y, z) \<in> mttm_step (wrap_delta M pack c \<Sigma>u)"
    by simp
  from run_step_reverse[OF vM k2 val_y this]
  obtain cM_z where
      z_lift: "z = lift_M_config M cM_z"
    and step_M: "(cM_y, cM_z) \<in> mttm_step (delta_tm M)"
    by blast
  have val_z: "valid_config_mttm M cM_z"
    by (rule valid_step_mttm[OF vM step_M val_y])
  from y_M step_M
  have steps_z: "(cM, cM_z) \<in> (mttm_step (delta_tm M))\<^sup>*"
    by (rule rtrancl_into_rtrancl)
  from z_lift steps_z val_z show ?case by blast
qed

end
