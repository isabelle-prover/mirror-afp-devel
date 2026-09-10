theory Wrap_Time
  imports Wrap_Language
begin

section \<open>Faithful (k-tape) plant-\<open>le\<close> wrap: time bound\<close>

text \<open>The wrap's user-facing time on @{term w} decomposes into the encoder
  phase (@{term "length w + 2"} steps, @{thm[source] init_to_post_encoder_relpow}),
  the storage rewind + plant-\<open>le\<close> + dispatch
  (@{term "Suc (length (wrap_enc pack c w)) + 2"} steps,
  @{thm[source] plant_reset_dispatch_relpow}, reaching the floated engine
  configuration \<open>post_plant_dispatch_config\<close>), and the run phase, which the
  origin float carries onto the floated configuration one-for-one
  (@{thm[source] shift_reach_state_forward}, step count preserved).  The total
  is @{term "length w + length (wrap_enc pack c w) + 5 + t"}.

  The linear-in-@{term "length w"} part has coefficient @{text 1}: unlike the
  transpose wrap's combined reset (cost @{term "2 * length w"}), wrapper B
  \<^emph>\<open>never walks back over the raw input\<close> --- the plant-\<open>le\<close> reset rewinds only
  the storage tape (@{term "length (wrap_enc pack c w)"} packed cells, at most
  @{term "length w"}), then plants a fresh @{text le} at the input origin.
  This is the @{text "(1 + \<epsilon>)\<cdot>n"} setup the linear-time speed-up
  \<^cite>\<open>\<open>Theorem 12.4\<close> in "Hopcroft1979:introduction"\<close> needs; the
  transpose's @{text "~2\<cdot>n"} rewind is what the super-linear
  \<^cite>\<open>\<open>Theorem 12.3\<close> in "Hopcroft1979:introduction"\<close> tolerates but
  12.4 does not.

  The per-input precondition @{term "set (wrap_enc pack c w) \<subseteq> Sigma_tm M"}
  feeds the encoder pack-contracts and
  @{thm[source] valid_init_config_mttm}.\<close>

lemma wrap_time:
  assumes vM: "valid_mttm M"
      and fin_Sigmau: "finite \<Sigma>u"
      and c_pos: "0 < c"
      and bl_ne_le: "bl_tm M \<noteq> le_tm M"
      and k2: "2 \<le> k_tm M"
      and w_alpha: "set w \<subseteq> \<Sigma>u"
      and enc_in_Sigma: "set (wrap_enc pack c w) \<subseteq> Sigma_tm M"
      and accept_M: "accepts_in_time_mttm M (wrap_enc pack c w) t"
  shows "accepts_in_time_user_wrap (encoding_wrap M pack c \<Sigma>u) w
           (length w + length (wrap_enc pack c w) + 5 + t)"
proof -
  let ?R_W = "mttm_step (wrap_delta M pack c \<Sigma>u)"
  let ?W = "encoding_wrap M pack c \<Sigma>u"
  let ?init_M = "init_config_mttm M (wrap_enc pack c w)"
  let ?d = "\<lambda>p::nat. if p = 0 then length w + 1 else 0"

  \<comment> \<open>Unpack M's accepting trace at exact length @{term n}.\<close>
  from accept_M obtain n cM_n where
      n_le: "n \<le> t"
      and M_trace: "(?init_M, cM_n) \<in> (mttm_step (delta_tm M)) ^^ n"
      and cM_n_accept: "mt_state cM_n = t_tm M"
    unfolding accepts_in_time_mttm_def by auto

  \<comment> \<open>Substrate facts and pack contracts (as in the reverse inclusion).\<close>
  obtain Q \<Sigma>i \<Gamma>set bl le \<delta>M sM tM rM kM where M_eq:
    "M = MTTM Q \<Sigma>i \<Gamma>set bl le \<delta>M sM tM rM kM"
    by (cases M)
  have Sigma_sub_Gamma: "Sigma_tm M \<subseteq> \<Gamma>_tm M" using vM M_eq by auto
  have le_not_in_Sigma: "le_tm M \<notin> Sigma_tm M" using vM M_eq by auto

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
    from pack_in_Sigma[OF i_c_lt] Sigma_sub_Gamma
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

  \<comment> \<open>Phase 1: encoder --- kept at exact relpow length @{term "length w + 2"}.\<close>
  have enc_chain:
    "(init_config_mttm ?W (map Raw w),
      post_encoder_config_gen (k_tm M) M pack c w) \<in> ?R_W ^^ (length w + 2)"
    by (rule init_to_post_encoder_relpow
          [where pack = pack, OF vM c_pos w_alpha bl_ne_le k2 pack_in_Sigma])

  \<comment> \<open>Phase 2+3: storage rewind, plant-\<open>le\<close>, dispatch --- reaching the floated
     engine config in @{term "Suc (length (wrap_enc pack c w)) + 2"} steps.  The
     input tape is never walked (contrast the transpose's @{term "length w + 3"}).\<close>
  have rd_chain:
    "(post_encoder_config_gen (k_tm M) M pack c w,
      post_plant_dispatch_config M pack c w)
       \<in> ?R_W ^^ (Suc (length (wrap_enc pack c w)) + 2)"
    by (rule plant_reset_dispatch_relpow
          [where pack = pack, OF vM c_pos w_alpha bl_ne_le k2 pack_in pack_ne_le])

  \<comment> \<open>Phase 4: the run, spliced through the origin float --- step count preserved.\<close>
  have val_init_M: "valid_config_mttm M ?init_M"
    by (rule valid_init_config_mttm[OF vM enc_in_Sigma])
  have run_relpow:
    "(lift_M_config M ?init_M, lift_M_config M cM_n) \<in> ?R_W ^^ n"
    by (rule run_steps_forward_relpow[OF vM k2 val_init_M M_trace])
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

  have acc_lift: "mt_state (lift_M_config M cM_n) = W_Run (t_tm M)"
    using cM_n_accept by (cases cM_n) (simp add: lift_M_config_def)
  have run_relpow':
    "(lift_M_config M ?init_M, lift_M_config M cM_n)
       \<in> (mttm_step (delta_tm ?W)) ^^ n"
    using run_relpow wrap_delta_eq by simp
  from shift_reach_state_forward[OF wf_wrap le0 shift run_relpow' acc_lift]
  obtain cb where cb_run:
      "(post_plant_dispatch_config M pack c w, cb)
         \<in> (mttm_step (delta_tm ?W)) ^^ n"
    and cb_state: "mt_state cb = W_Run (t_tm M)"
    by blast
  have run_chain: "(post_plant_dispatch_config M pack c w, cb) \<in> ?R_W ^^ n"
    using cb_run wrap_delta_eq by simp

  let ?N_total = "(length w + 2) + (Suc (length (wrap_enc pack c w)) + 2) + n"

  \<comment> \<open>Compose phases via @{thm relpow_add}.\<close>
  from enc_chain rd_chain
  have er_chain:
    "(init_config_mttm ?W (map Raw w),
      post_plant_dispatch_config M pack c w)
       \<in> ?R_W ^^ ((length w + 2) + (Suc (length (wrap_enc pack c w)) + 2))"
    unfolding relpow_add by blast
  from er_chain run_chain
  have full_chain:
    "(init_config_mttm ?W (map Raw w), cb) \<in> ?R_W ^^ ?N_total"
    unfolding relpow_add by blast

  have total_bound:
    "?N_total \<le> length w + length (wrap_enc pack c w) + 5 + t"
    using n_le by linarith

  \<comment> \<open>The reached config @{term cb} is in the wrap accept state.\<close>
  have wrap_accept: "t_tm ?W = W_Run (t_tm M)" by simp
  have cb_accept: "mt_state cb = t_tm ?W"
    using cb_state wrap_accept by simp

  have delta_eq: "delta_tm ?W = wrap_delta M pack c \<Sigma>u" by simp
  have fact_b:
    "(init_config_mttm ?W (map Raw w), cb)
        \<in> mttm_step (delta_tm ?W) ^^ ?N_total"
    using full_chain delta_eq by simp

  have ex_witness:
    "\<exists>m cw. m \<le> length w + length (wrap_enc pack c w) + 5 + t
          \<and> (init_config_mttm ?W (map Raw w), cw)
              \<in> mttm_step (delta_tm ?W) ^^ m
          \<and> mt_state cw = t_tm ?W"
    using total_bound fact_b cb_accept by blast

  show "accepts_in_time_user_wrap ?W w
          (length w + length (wrap_enc pack c w) + 5 + t)"
    unfolding accepts_in_time_user_wrap_def accepts_in_time_mttm_def
    using ex_witness by simp
qed

end
