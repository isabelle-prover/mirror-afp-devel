theory Wrap_Time
  imports Wrap_Language
begin

section \<open>The wrap: time bound\<close>

text \<open>The wrap's user-facing time on @{term w} decomposes into the encoder
  phase (@{term "length w + 2"} steps, @{thm[source] init_to_post_encoder_relpow}),
  the storage rewind, the plant-done step and the dispatch
  (@{term "Suc (length (wrap_enc pack c w)) + 2"} steps,
  @{thm[source] plant_reset_dispatch_relpow}, reaching the floated engine
  configuration \<open>post_plant_dispatch_config\<close>), and the run phase, which the
  origin float carries onto the floated configuration one-for-one
  (@{thm[source] shift_reach_state_forward}, step count preserved).  The total
  is @{term "length w + length (wrap_enc pack c w) + 5 + t"}.

  The linear-in-@{term "length w"} part has coefficient @{text 1}, because
  the wrap \<^emph>\<open>never walks back over the raw input\<close>: the reset rewinds only
  the storage tape (@{term "length (wrap_enc pack c w)"} packed cells, at most
  @{term "length w"}), then plants a fresh @{text le} at the input head.
  This is the @{text "(1 + \<epsilon>)\<cdot>n"} setup the linear-time speed-up
  \<^cite>\<open>\<open>Theorem 12.4\<close> in "Hopcroft1979:introduction"\<close> needs.  Rewinding
  the input tape as well would cost about @{text "2\<cdot>n"}, which the
  super-linear case
  \<^cite>\<open>\<open>Theorem 12.3\<close> in "Hopcroft1979:introduction"\<close> tolerates but
  12.4 does not.

  The per-input precondition @{term "set (wrap_enc pack c w) \<subseteq> Sigma_ktm M"}
  feeds the encoder pack-contracts and
  @{thm[source] valid_init_config_ktm}.\<close>

lemma wrap_reaches_state:
  assumes vM: "valid_ktm M"
      and fin_Sigmau: "finite \<Sigma>u"
      and c_pos: "0 < c"
      and bl_ne_le: "bl_ktm M \<noteq> le_ktm M"
      and k2: "2 \<le> k_ktm M"
      and w_alpha: "set w \<subseteq> \<Sigma>u"
      and enc_in_Sigma: "set (wrap_enc pack c w) \<subseteq> Sigma_ktm M"
      and accept_M: "reaches_state_in_time_ktm M (wrap_enc pack c w) q_stop t"
  shows "reaches_state_in_time_ktm (encoding_wrap M pack c \<Sigma>u) (map Raw w) (W_Run q_stop)
           (length w + length (wrap_enc pack c w) + 5 + t)"
proof -
  let ?R_W = "ktm_step (wrap_delta M pack c \<Sigma>u)"
  let ?W = "encoding_wrap M pack c \<Sigma>u"
  let ?init_M = "init_config_ktm M (wrap_enc pack c w)"
  let ?d = "\<lambda>p::nat. if p = 0 then length w + 1 else 0"

  \<comment> \<open>Unpack M's accepting trace at exact length @{term n}.\<close>
  from accept_M obtain n cM_n where
      n_le: "n \<le> t"
      and M_trace: "(?init_M, cM_n) \<in> (ktm_step (delta_ktm M)) ^^ n"
      and cM_n_accept: "ktc_state cM_n = q_stop"
    unfolding reaches_state_in_time_ktm_def by auto

  \<comment> \<open>Substrate facts and pack contracts (as in the reverse inclusion).\<close>
  obtain Q \<Sigma>i \<Gamma>set bl le \<delta>M sM tM rM kM where M_eq:
    "M = KTM Q \<Sigma>i \<Gamma>set bl le \<delta>M sM tM rM kM"
    by (cases M)
  have Sigma_sub_Gamma: "Sigma_ktm M \<subseteq> \<Gamma>_ktm M" using vM M_eq by auto
  have le_not_in_Sigma: "le_ktm M \<notin> Sigma_ktm M" using vM M_eq by auto

  have pack_in_Sigma:
    "\<And>i. i * c < length w \<Longrightarrow> pack (take c (drop (i * c) w)) \<in> Sigma_ktm M"
  proof -
    fix i :: nat
    assume i_c_lt: "i * c < length w"
    have "pack (take c (drop (i * c) w)) \<in> set (wrap_enc pack c w)"
      by (rule pack_take_in_set_wrap_enc[OF c_pos i_c_lt])
    thus "pack (take c (drop (i * c) w)) \<in> Sigma_ktm M"
      using enc_in_Sigma by auto
  qed
  have pack_in:
    "\<And>i. i * c < length w \<Longrightarrow> pack (take c (drop (i * c) w)) \<in> \<Gamma>_ktm M"
  proof -
    fix i :: nat
    assume i_c_lt: "i * c < length w"
    from pack_in_Sigma[OF i_c_lt] Sigma_sub_Gamma
    show "pack (take c (drop (i * c) w)) \<in> \<Gamma>_ktm M" by auto
  qed
  have pack_ne_le:
    "\<And>i. i * c < length w \<Longrightarrow> pack (take c (drop (i * c) w)) \<noteq> le_ktm M"
  proof -
    fix i :: nat
    assume i_c_lt: "i * c < length w"
    from pack_in_Sigma[OF i_c_lt] le_not_in_Sigma
    show "pack (take c (drop (i * c) w)) \<noteq> le_ktm M" by auto
  qed

  \<comment> \<open>Phase 1: encoder --- kept at exact relpow length @{term "length w + 2"}.\<close>
  have enc_chain:
    "(init_config_ktm ?W (map Raw w),
      post_encoder_config_gen (k_ktm M) M pack c w) \<in> ?R_W ^^ (length w + 2)"
    by (rule init_to_post_encoder_relpow
          [where pack = pack, OF vM c_pos w_alpha bl_ne_le k2 pack_in_Sigma])

  \<comment> \<open>Phase 2+3: storage rewind, plant-done, dispatch --- reaching the floated
     engine config in @{term "Suc (length (wrap_enc pack c w)) + 2"} steps.  The
     input tape is never walked.\<close>
  have rd_chain:
    "(post_encoder_config_gen (k_ktm M) M pack c w,
      post_plant_dispatch_config M pack c w)
       \<in> ?R_W ^^ (Suc (length (wrap_enc pack c w)) + 2)"
    by (rule plant_reset_dispatch_relpow
          [where pack = pack, OF vM c_pos w_alpha bl_ne_le k2 pack_in pack_ne_le])

  \<comment> \<open>Phase 4: the run, spliced through the origin float --- step count preserved.\<close>
  have val_init_M: "valid_config_ktm M ?init_M"
    by (rule valid_init_config_ktm[OF vM enc_in_Sigma])
  have run_relpow:
    "(lift_M_config M ?init_M, lift_M_config M cM_n) \<in> ?R_W ^^ n"
    by (rule run_steps_forward_relpow[OF vM k2 val_init_M M_trace])
  have wf_wrap: "valid_ktm ?W"
    by (rule wrap_wf[OF vM bl_ne_le[THEN not_sym] fin_Sigmau c_pos k2])
  have shift:
    "shift_rel ?d (lift_M_config M ?init_M)
        (post_plant_dispatch_config M pack c w)"
    by (rule post_plant_dispatch_shift_lift[OF k2])
  have wrap_delta_eq: "delta_ktm ?W = wrap_delta M pack c \<Sigma>u"
    by simp

  \<comment> \<open>@{text le0}: only physical @{text 0} floats, and the @{text \<tau>}-lift holds
     @{text le} there --- the M-init left endmarker at cell @{text 0} of the
     active storage tape @{term "Suc 0"} (in range since @{term "2 \<le> k_ktm M"}).\<close>
  have suc0_lt: "Suc 0 < k_ktm M" using k2 by simp
  have le0:
    "\<forall>k. ?d k \<noteq> 0 \<longrightarrow> ktc_tape (lift_M_config M ?init_M) k 0 = le_ktm ?W"
  proof (intro allI impI)
    fix k :: nat
    assume "?d k \<noteq> 0"
    hence k0: "k = 0" by (auto split: if_splits)
    have "ktc_tape (lift_M_config M ?init_M) 0 0
            = Enc (ktc_tape ?init_M (wrap_tau 0) 0)"
      using k2 by (simp add: lift_M_config_def)
    also have "\<dots> = Enc (ktc_tape ?init_M (Suc 0) 0)"
      by (simp add: wrap_tau_def)
    also have "ktc_tape ?init_M (Suc 0) 0 = le_ktm M"
      using suc0_lt by (simp add: M_eq)
    finally show "ktc_tape (lift_M_config M ?init_M) k 0 = le_ktm ?W"
      using k0 by simp
  qed

  have acc_lift: "ktc_state (lift_M_config M cM_n) = W_Run q_stop"
    using cM_n_accept by (cases cM_n) (simp add: lift_M_config_def)
  have run_relpow':
    "(lift_M_config M ?init_M, lift_M_config M cM_n)
       \<in> (ktm_step (delta_ktm ?W)) ^^ n"
    using run_relpow wrap_delta_eq by simp
  from shift_reach_state_forward[OF wf_wrap le0 shift run_relpow' acc_lift]
  obtain cb where cb_run:
      "(post_plant_dispatch_config M pack c w, cb)
         \<in> (ktm_step (delta_ktm ?W)) ^^ n"
    and cb_state: "ktc_state cb = W_Run q_stop"
    by blast
  have run_chain: "(post_plant_dispatch_config M pack c w, cb) \<in> ?R_W ^^ n"
    using cb_run wrap_delta_eq by simp

  let ?N_total = "(length w + 2) + (Suc (length (wrap_enc pack c w)) + 2) + n"

  \<comment> \<open>Compose phases via @{thm relpow_add}.\<close>
  from enc_chain rd_chain
  have er_chain:
    "(init_config_ktm ?W (map Raw w),
      post_plant_dispatch_config M pack c w)
       \<in> ?R_W ^^ ((length w + 2) + (Suc (length (wrap_enc pack c w)) + 2))"
    unfolding relpow_add by blast
  from er_chain run_chain
  have full_chain:
    "(init_config_ktm ?W (map Raw w), cb) \<in> ?R_W ^^ ?N_total"
    unfolding relpow_add by blast

  have total_bound:
    "?N_total \<le> length w + length (wrap_enc pack c w) + 5 + t"
    using n_le by linarith

  \<comment> \<open>The reached config @{term cb} is in the wrap accept state.\<close>
  have cb_accept: "ktc_state cb = W_Run q_stop"
    by (rule cb_state)

  have delta_eq: "delta_ktm ?W = wrap_delta M pack c \<Sigma>u" by simp
  have fact_b:
    "(init_config_ktm ?W (map Raw w), cb)
        \<in> ktm_step (delta_ktm ?W) ^^ ?N_total"
    using full_chain delta_eq by simp

  have ex_witness:
    "\<exists>m cw. m \<le> length w + length (wrap_enc pack c w) + 5 + t
          \<and> (init_config_ktm ?W (map Raw w), cw)
              \<in> ktm_step (delta_ktm ?W) ^^ m
          \<and> ktc_state cw = W_Run q_stop"
    using total_bound fact_b cb_accept by blast

  show "reaches_state_in_time_ktm ?W (map Raw w) (W_Run q_stop)
          (length w + length (wrap_enc pack c w) + 5 + t)"
    unfolding reaches_state_in_time_ktm_def
    using ex_witness by simp
qed

text \<open>The accepting instance, in the wrap's user-facing vocabulary.\<close>

lemma wrap_time:
  assumes vM: "valid_ktm M"
      and fin_Sigmau: "finite \<Sigma>u"
      and c_pos: "0 < c"
      and bl_ne_le: "bl_ktm M \<noteq> le_ktm M"
      and k2: "2 \<le> k_ktm M"
      and w_alpha: "set w \<subseteq> \<Sigma>u"
      and enc_in_Sigma: "set (wrap_enc pack c w) \<subseteq> Sigma_ktm M"
      and accept_M: "accepts_in_time_ktm M (wrap_enc pack c w) t"
  shows "accepts_in_time_user_wrap (encoding_wrap M pack c \<Sigma>u) w
           (length w + length (wrap_enc pack c w) + 5 + t)"
  using wrap_reaches_state [OF vM fin_Sigmau c_pos bl_ne_le k2 w_alpha enc_in_Sigma
      accept_M [unfolded accepts_in_time_ktm_iff_reaches]]
  unfolding accepts_in_time_user_wrap_def accepts_in_time_ktm_iff_reaches
  by simp

end
