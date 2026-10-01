theory Wrap_Language
  imports Wrap_Canonical
begin

section \<open>Faithful (k-tape) plant-\<open>le\<close> wrap: language preservation\<close>

text \<open>The user-facing language of the faithful plant-\<open>le\<close> wrap equals the
  encoded-input language of M: @{term "Lang_user_wrap (encoding_wrap M pack c
  \<Sigma>u) = {w. set w \<subseteq> \<Sigma>u \<and> wrap_enc pack c w \<in> Lang_mttm M}"}.  As with the
  transpose wrap this is mutual inclusion of accepting languages (two one-way
  trace arguments; not a bisimulation, since @{term M} is nondeterministic).

  The \<^emph>\<open>reverse\<close> inclusion (M-acceptance of the encoded input gives
  wrap-acceptance) differs from the transpose at the reset\<open>\<rightarrow>\<close>run seam.  Where
  the transpose rewinds all the way to the true origin and hands the run the
  genuine @{const lift_M_config}, the plant wrap stops at the \<^emph>\<open>floated\<close>
  configuration @{const post_plant_dispatch_config} --- no input rewind, a fresh
  @{text le} planted at the reused input head.  The origin-float bridge
  reconciles the two: the M-run lifts (via @{thm[source] run_steps_forward_relpow})
  to a run from the @{text \<tau>}-lift, and @{thm[source] shift_reach_state_forward}
  --- instantiated at the wrap machine itself --- re-bases that run onto the
  floated config the plant reset actually reaches, preserving the accept state.\<close>


subsection \<open>Reverse inclusion: chaining the phases through the floated origin\<close>

lemma wrap_language_reverse:
  assumes vM: "valid_mttm M"
      and fin_Sigmau: "finite \<Sigma>u"
      and c_pos: "0 < c"
      and bl_ne_le: "bl_tm M \<noteq> le_tm M"
      and k2: "2 \<le> k_tm M"
    shows "{w. set w \<subseteq> \<Sigma>u \<and> wrap_enc pack c w \<in> Lang_mttm M}
           \<subseteq> Lang_user_wrap (encoding_wrap M pack c \<Sigma>u)"
proof
  fix w
  assume "w \<in> {w. set w \<subseteq> \<Sigma>u \<and> wrap_enc pack c w \<in> Lang_mttm M}"
  hence w_alpha: "set w \<subseteq> \<Sigma>u"
    and enc_lang: "wrap_enc pack c w \<in> Lang_mttm M"
    by auto

  from enc_lang have enc_in_Sigma: "set (wrap_enc pack c w) \<subseteq> Sigma_tm M"
    by (simp add: Lang_mttm_def)
  from enc_lang obtain w_ts cf_pos where M_trace:
    "(init_config_mttm M (wrap_enc pack c w),
      Config\<^sub>M (t_tm M) w_ts cf_pos)
     \<in> (mttm_step (delta_tm M))\<^sup>*"
    by (auto simp: Lang_mttm_def)

  let ?W = "encoding_wrap M pack c \<Sigma>u"
  let ?init_M = "init_config_mttm M (wrap_enc pack c w)"
  let ?cf_M = "Config\<^sub>M (t_tm M) w_ts cf_pos"
  let ?R_W = "mttm_step (wrap_delta M pack c \<Sigma>u)"
  let ?d = "\<lambda>p::nat. if p = 0 then length w + 1 else 0"

  obtain Q \<Sigma>i \<Gamma>set bl le \<delta>M sM tM rM kM where M_eq:
    "M = MTTM Q \<Sigma>i \<Gamma>set bl le \<delta>M sM tM rM kM"
    by (cases M)
  have Sigma_sub_\<Gamma>: "Sigma_tm M \<subseteq> \<Gamma>_tm M" using vM M_eq by auto
  have le_not_in_Sigma: "le_tm M \<notin> Sigma_tm M" using vM M_eq by auto

  \<comment> \<open>Pack contracts from the Sigma containment (as in the transpose reverse).\<close>
  have pack_in_Sigma:
    "\<And>i. i * c < length w \<Longrightarrow> pack (take c (drop (i * c) w)) \<in> Sigma_tm M"
  proof -
    fix i :: nat
    assume i_c_lt: "i * c < length w"
    have "pack (take c (drop (i * c) w)) \<in> set (wrap_enc pack c w)"
      by (rule pack_take_in_set_wrap_enc[OF c_pos i_c_lt])
    thus "pack (take c (drop (i * c) w)) \<in> Sigma_tm M"
      using enc_in_Sigma by auto
  qed
  have pack_in:
    "\<And>i. i * c < length w \<Longrightarrow> pack (take c (drop (i * c) w)) \<in> \<Gamma>_tm M"
  proof -
    fix i :: nat
    assume i_c_lt: "i * c < length w"
    from pack_in_Sigma[OF i_c_lt] Sigma_sub_\<Gamma>
    show "pack (take c (drop (i * c) w)) \<in> \<Gamma>_tm M" by auto
  qed
  have pack_ne_le:
    "\<And>i. i * c < length w \<Longrightarrow> pack (take c (drop (i * c) w)) \<noteq> le_tm M"
  proof -
    fix i :: nat
    assume i_c_lt: "i * c < length w"
    from pack_in_Sigma[OF i_c_lt] le_not_in_Sigma
    show "pack (take c (drop (i * c) w)) \<noteq> le_tm M" by auto
  qed

  \<comment> \<open>Phase 1: encoder.\<close>
  have enc_step:
    "(init_config_mttm ?W (map Raw w),
      post_encoder_config_gen (k_tm M) M pack c w) \<in> ?R_W\<^sup>*"
    by (rule encoder_phase_terminates
          [where pack = pack, OF vM c_pos w_alpha bl_ne_le k2 pack_in_Sigma])
  \<comment> \<open>Phase 2+3: storage rewind, plant-\<open>le\<close>, dispatch --- reaching the floated
     engine config.  The input tape is never walked.\<close>
  have pr_step:
    "(post_encoder_config_gen (k_tm M) M pack c w,
      post_plant_dispatch_config M pack c w) \<in> ?R_W\<^sup>*"
    by (rule plant_reset_dispatch_rtrancl
          [where pack = pack, OF vM c_pos w_alpha bl_ne_le k2 pack_in pack_ne_le])

  \<comment> \<open>Phase 4: the run, spliced through the origin float.\<close>
  have val_init_M: "valid_config_mttm M ?init_M"
    by (rule valid_init_config_mttm[OF vM enc_in_Sigma])
  from M_trace obtain n where M_trace_n:
    "(?init_M, ?cf_M) \<in> (mttm_step (delta_tm M)) ^^ n"
    by (auto simp: rtrancl_power)
  have run_relpow:
    "(lift_M_config M ?init_M, lift_M_config M ?cf_M) \<in> ?R_W ^^ n"
    by (rule run_steps_forward_relpow[OF vM k2 val_init_M M_trace_n])

  have wf_wrap: "valid_mttm ?W"
    by (rule wrap_wf[OF vM bl_ne_le[THEN not_sym] fin_Sigmau c_pos k2])
  have shift:
    "shift_rel ?d (lift_M_config M ?init_M)
        (post_plant_dispatch_config M pack c w)"
    by (rule post_plant_dispatch_shift_lift[OF k2])
  have wrap_delta_eq: "delta_tm ?W = wrap_delta M pack c \<Sigma>u"
    by simp

  \<comment> \<open>@{text le0}: only physical @{text 0} floats, and the @{text \<tau>}-lift holds
     @{text le} there --- the M-init left endmarker at cell @{text 0} of the
     active storage tape @{term "Suc 0"} (in range since @{term "2 \<le> k_tm M"}).\<close>
  have suc0_lt: "Suc 0 < k_tm M" using k2 by simp
  have le0:
    "\<forall>k. ?d k \<noteq> 0 \<longrightarrow> mt_tape (lift_M_config M ?init_M) k 0 = le_tm ?W"
  proof (intro allI impI)
    fix k :: nat
    assume "?d k \<noteq> 0"
    hence k0: "k = 0" by (auto split: if_splits)
    have "mt_tape (lift_M_config M ?init_M) 0 0
            = Enc (mt_tape ?init_M (wrap_tau 0) 0)"
      using k2 by (simp add: lift_M_config_def)
    also have "\<dots> = Enc (mt_tape ?init_M (Suc 0) 0)"
      by (simp add: wrap_tau_def)
    also have "mt_tape ?init_M (Suc 0) 0 = le_tm M"
      using suc0_lt by (simp add: M_eq)
    finally show "mt_tape (lift_M_config M ?init_M) k 0 = le_tm ?W"
      using k0 by simp
  qed

  have acc_lift: "mt_state (lift_M_config M ?cf_M) = W_Run (t_tm M)"
    by (simp add: lift_M_config_def)
  have run_relpow':
    "(lift_M_config M ?init_M, lift_M_config M ?cf_M)
       \<in> (mttm_step (delta_tm ?W)) ^^ n"
    using run_relpow wrap_delta_eq by simp
  from shift_reach_state_forward[OF wf_wrap le0 shift run_relpow' acc_lift]
  obtain cb where cb_run:
      "(post_plant_dispatch_config M pack c w, cb)
         \<in> (mttm_step (delta_tm ?W)) ^^ n"
    and cb_state: "mt_state cb = W_Run (t_tm M)"
    by blast
  have cb_run_R: "(post_plant_dispatch_config M pack c w, cb) \<in> ?R_W ^^ n"
    using cb_run wrap_delta_eq by simp
  have cb_run_rtrancl: "(post_plant_dispatch_config M pack c w, cb) \<in> ?R_W\<^sup>*"
    by (rule relpow_imp_rtrancl[OF cb_run_R])

  \<comment> \<open>Compose the four phases into one accepting wrap-trace.\<close>
  from enc_step pr_step have er_step:
    "(init_config_mttm ?W (map Raw w),
      post_plant_dispatch_config M pack c w) \<in> ?R_W\<^sup>*"
    by (rule rtrancl_trans)
  from er_step cb_run_rtrancl have full_trace:
    "(init_config_mttm ?W (map Raw w), cb) \<in> ?R_W\<^sup>*"
    by (rule rtrancl_trans)

  \<comment> \<open>@{term cb} is in the wrap accept state @{term "t_tm ?W = W_Run (t_tm M)"}.\<close>
  obtain cb_ts cb_n where cb_eq:
    "cb = Config\<^sub>M (t_tm ?W) cb_ts cb_n"
  proof -
    have "t_tm ?W = W_Run (t_tm M)" by simp
    hence "cb = Config\<^sub>M (t_tm ?W) (mt_tape cb) (mt_pos cb)"
      using cb_state by (cases cb) simp
    thus thesis by (rule that)
  qed
  from full_trace cb_eq have accept_trace:
    "(init_config_mttm ?W (map Raw w),
      Config\<^sub>M (t_tm ?W) cb_ts cb_n) \<in> ?R_W\<^sup>*"
    by simp

  have set_Raw_w: "set (map Raw w) \<subseteq> Sigma_tm ?W"
    using w_alpha by auto

  show "w \<in> Lang_user_wrap ?W"
    unfolding Lang_user_wrap_def Lang_mttm_def
    using set_Raw_w accept_trace wrap_delta_eq by auto
qed


subsection \<open>Forward inclusion: factoring through the floated origin\<close>

text \<open>The forward inclusion: wrap-B acceptance of @{term "map Raw w"} gives
  M-acceptance of @{term "wrap_enc pack c w"}.  The accepting wrap-trace factors
  via @{thm[source] wrap_accept_canonical_factor} (reaching the \<^emph>\<open>floated\<close>
  @{const post_plant_dispatch_config}), then the origin float runs in reverse:
  @{thm[source] shift_reach_state_reverse} re-bases the run-phase tail from the
  floated config to the @{text \<tau>}-lift, and @{thm[source] run_steps_reverse}
  projects it to an accepting M-trace on @{term "wrap_enc pack c w"}.\<close>

lemma wrap_language_forward:
  fixes M :: "('q, 'b) mttm"
  assumes vM: "valid_mttm M"
      and fin_Sigmau: "finite \<Sigma>u"
      and c_pos: "0 < c"
      and bl_ne_le: "bl_tm M \<noteq> le_tm M"
      and k2: "2 \<le> k_tm M"
  shows "Lang_user_wrap (encoding_wrap M pack c \<Sigma>u)
         \<subseteq> {w. set w \<subseteq> \<Sigma>u \<and> wrap_enc pack c w \<in> Lang_mttm M}"
proof
  fix w
  assume mem: "w \<in> Lang_user_wrap (encoding_wrap M pack c \<Sigma>u)"
  hence raw_w_lang:
    "map Raw w \<in> Lang_mttm (encoding_wrap M pack c \<Sigma>u)"
    unfolding Lang_user_wrap_def by simp

  have w_alpha: "set w \<subseteq> \<Sigma>u"
  proof
    fix x assume x_in: "x \<in> set w"
    hence raw_x_in: "Raw x \<in> set (map Raw w)" by simp
    from raw_w_lang have map_raw_in:
      "set (map Raw w) \<subseteq> Raw ` \<Sigma>u"
      unfolding Lang_mttm_def by auto
    from raw_x_in map_raw_in have "Raw x \<in> Raw ` \<Sigma>u" by blast
    thus "x \<in> \<Sigma>u" by auto
  qed

  let ?W = "encoding_wrap M pack c \<Sigma>u"
  let ?R_W = "mttm_step (wrap_delta M pack c \<Sigma>u)"
  let ?init_M = "init_config_mttm M (wrap_enc pack c w)"
  let ?d = "\<lambda>p::nat. if p = 0 then length w + 1 else 0"

  from raw_w_lang obtain w_ts cf_pos where wrap_trace_raw:
    "(init_config_mttm ?W (map Raw w),
      Config\<^sub>M (t_tm ?W) w_ts cf_pos)
     \<in> (mttm_step (delta_tm ?W))\<^sup>*"
    unfolding Lang_mttm_def by auto

  let ?C_acc = "Config\<^sub>M (W_Run (t_tm M)) w_ts cf_pos"

  have wrap_trace:
    "(init_config_mttm ?W (map Raw w), ?C_acc) \<in> ?R_W\<^sup>*"
    using wrap_trace_raw by simp
  have accept_state: "\<exists>q. mt_state ?C_acc = W_Run q" by simp

  from wrap_accept_canonical_factor
         [OF vM c_pos bl_ne_le w_alpha k2 wrap_trace accept_state]
  have suffix:
       "(post_plant_dispatch_config M pack c w, ?C_acc) \<in> ?R_W\<^sup>*"
   and pack_in_Sigma:
       "\<And>i. i * c < length w \<Longrightarrow> pack (take c (drop (i * c) w)) \<in> Sigma_tm M"
    by auto

  have enc_in_Sigma: "set (wrap_enc pack c w) \<subseteq> Sigma_tm M"
  proof
    fix x
    assume "x \<in> set (wrap_enc pack c w)"
    then obtain j where j_lt: "j < length (wrap_enc pack c w)"
                   and x_eq: "x = wrap_enc pack c w ! j"
      by (auto simp: in_set_conv_nth)
    from wrap_enc_in_Sigma[OF c_pos pack_in_Sigma j_lt]
    show "x \<in> Sigma_tm M" using x_eq by simp
  qed
  have val_init_M: "valid_config_mttm M ?init_M"
    by (rule valid_init_config_mttm[OF vM enc_in_Sigma])

  \<comment> \<open>Reverse origin float: the accepting run from the floated config lifts to a
     run from the @{text \<tau>}-lift, reaching the same accept state.\<close>
  have wf_wrap: "valid_mttm ?W"
    by (rule wrap_wf[OF vM bl_ne_le[THEN not_sym] fin_Sigmau c_pos k2])
  have shift:
    "shift_rel ?d (lift_M_config M ?init_M)
        (post_plant_dispatch_config M pack c w)"
    by (rule post_plant_dispatch_shift_lift[OF k2])
  have wrap_delta_eq: "delta_tm ?W = wrap_delta M pack c \<Sigma>u"
    by simp

  obtain Q \<Sigma>i \<Gamma>set bl le \<delta>M sM tM rM kM where M_eq:
    "M = MTTM Q \<Sigma>i \<Gamma>set bl le \<delta>M sM tM rM kM"
    by (cases M)
  have suc0_lt: "Suc 0 < k_tm M" using k2 by simp
  have le0:
    "\<forall>k. ?d k \<noteq> 0 \<longrightarrow> mt_tape (lift_M_config M ?init_M) k 0 = le_tm ?W"
  proof (intro allI impI)
    fix k :: nat
    assume "?d k \<noteq> 0"
    hence k0: "k = 0" by (auto split: if_splits)
    have "mt_tape (lift_M_config M ?init_M) 0 0
            = Enc (mt_tape ?init_M (wrap_tau 0) 0)"
      using k2 by (simp add: lift_M_config_def)
    also have "\<dots> = Enc (mt_tape ?init_M (Suc 0) 0)"
      by (simp add: wrap_tau_def)
    also have "mt_tape ?init_M (Suc 0) 0 = le_tm M"
      using suc0_lt by (simp add: M_eq)
    finally show "mt_tape (lift_M_config M ?init_M) k 0 = le_tm ?W"
      using k0 by simp
  qed

  from suffix obtain n where suffix_n:
    "(post_plant_dispatch_config M pack c w, ?C_acc) \<in> ?R_W ^^ n"
    by (auto simp: rtrancl_power)
  have suffix_n':
    "(post_plant_dispatch_config M pack c w, ?C_acc)
       \<in> (mttm_step (delta_tm ?W)) ^^ n"
    using suffix_n wrap_delta_eq by simp
  have acc_state: "mt_state ?C_acc = W_Run (t_tm M)" by simp
  from shift_reach_state_reverse[OF wf_wrap le0 shift suffix_n' acc_state]
  obtain ca where ca_run:
      "(lift_M_config M ?init_M, ca) \<in> (mttm_step (delta_tm ?W)) ^^ n"
    and ca_state: "mt_state ca = W_Run (t_tm M)"
    by blast
  have ca_run_rt: "(lift_M_config M ?init_M, ca) \<in> ?R_W\<^sup>*"
  proof -
    have "(lift_M_config M ?init_M, ca) \<in> ?R_W ^^ n"
      using ca_run wrap_delta_eq by simp
    thus ?thesis by (rule relpow_imp_rtrancl)
  qed

  from run_steps_reverse[OF vM k2 val_init_M ca_run_rt]
  obtain cM_acc where
      ca_lift: "ca = lift_M_config M cM_acc"
    and M_trace_acc: "(?init_M, cM_acc) \<in> (mttm_step (delta_tm M))\<^sup>*"
    by blast

  obtain cM_q cM_ts cM_n where cM_decomp:
    "cM_acc = Config\<^sub>M cM_q cM_ts cM_n"
    by (cases cM_acc)
  with ca_lift have lift_state_eq:
    "mt_state ca = W_Run cM_q"
    by (simp add: lift_M_config_def)
  with ca_state have cM_q_eq: "cM_q = t_tm M" by simp

  have enc_lang: "wrap_enc pack c w \<in> Lang_mttm M"
    unfolding Lang_mttm_def
    using enc_in_Sigma M_trace_acc cM_decomp cM_q_eq
    by auto

  show "w \<in> {w. set w \<subseteq> \<Sigma>u \<and> wrap_enc pack c w \<in> Lang_mttm M}"
    using w_alpha enc_lang by simp
qed


subsection \<open>Language equality headline\<close>

text \<open>The user-facing language of the faithful @{text k}-tape plant-\<open>le\<close> wrap
  equals the encoded-input language of M --- both inclusions, spliced through the
  origin float in opposite directions.\<close>

lemma wrap_language:
  assumes "valid_mttm M"
      and "finite \<Sigma>u"
      and "0 < c"
      and "bl_tm M \<noteq> le_tm M"
      and "2 \<le> k_tm M"
  shows "Lang_user_wrap (encoding_wrap M pack c \<Sigma>u)
         = {w. set w \<subseteq> \<Sigma>u \<and> wrap_enc pack c w \<in> Lang_mttm M}"
  using wrap_language_forward[OF assms] wrap_language_reverse[OF assms]
  by blast

end
