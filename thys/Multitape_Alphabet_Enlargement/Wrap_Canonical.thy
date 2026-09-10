theory Wrap_Canonical
  imports Wrap_Forcing
begin

section \<open>Faithful (k-tape) encoding wrap: canonical factor\<close>

text \<open>The pack contracts and the canonical-factor lemma for the faithful wrap:
  any \<^emph>\<open>accepting\<close> wrap-trace reaches @{const post_plant_dispatch_config} and
  the per-block pack contracts hold in @{text "Sigma_tm M"}-form.  These are
  the forward-direction obligations for @{const wrap_delta}, built over the
  forcing layer @{theory Multitape_Alphabet_Enlargement.Wrap_Forcing}.\<close>


subsection \<open>Canonical chain construction\<close>

text \<open>Canonical sub-chain to
  @{term "mid_buf_extending_config_gen (k_tm M) M pack c w i (c - 1)"}: given
  pack contracts for blocks @{term "j < i"}, the wrap-trace extends through the
  encoder phase up to (but not including) block @{term i}'s close-step.  Carries
  @{term "2 \<le> k_tm M"}.\<close>

lemma init_to_mid_buf_extending:
  fixes M :: "('q, 'b) mttm"
  assumes vM: "valid_mttm M"
      and c_pos: "0 < c"
      and w_alpha: "set w \<subseteq> \<Sigma>u"
      and bl_ne_le: "bl_tm M \<noteq> le_tm M"
      and k2: "2 \<le> k_tm M"
      and i_full: "(Suc i) * c \<le> length w"
      and pack_ih: "\<And>j. j < i \<Longrightarrow> pack (take c (drop (j * c) w)) \<in> Sigma_tm M"
    shows "(init_config_mttm (encoding_wrap M pack c \<Sigma>u) (map Raw w),
            mid_buf_extending_config_gen (k_tm M) M pack c w i (c - 1))
              \<in> (mttm_step (wrap_delta M pack c \<Sigma>u))\<^sup>*"
proof -
  let ?R = "mttm_step (wrap_delta M pack c \<Sigma>u)"

  have init_step:
    "(init_config_mttm (encoding_wrap M pack c \<Sigma>u) (map Raw w),
      mid_encoder_config_gen (k_tm M) M pack c w 0) \<in> ?R"
    by (rule init_to_mid_zero[OF vM c_pos])

  have iter:
    "j \<le> i \<Longrightarrow>
     (mid_encoder_config_gen (k_tm M) M pack c w 0,
      mid_encoder_config_gen (k_tm M) M pack c w j) \<in> ?R\<^sup>*" for j
  proof (induction j)
    case 0 show ?case by simp
  next
    case (Suc j)
    from Suc.prems have j_le_i: "j \<le> i" by simp
    from Suc.prems have Suc_j_le_i: "Suc j \<le> i" by simp
    from Suc.IH[OF j_le_i]
    have ih: "(mid_encoder_config_gen (k_tm M) M pack c w 0,
               mid_encoder_config_gen (k_tm M) M pack c w j) \<in> ?R\<^sup>*" .
    have block_full: "(Suc j) * c \<le> length w"
    proof -
      from Suc_j_le_i have "(Suc j) * c \<le> i * c"
        by (rule mult_le_mono1)
      also have "\<dots> \<le> (Suc i) * c" by simp
      also have "\<dots> \<le> length w" using i_full .
      finally show ?thesis .
    qed
    from Suc_j_le_i have j_lt_i: "j < i" by simp
    from pack_ih[OF j_lt_i]
    have pack_block_j: "pack (take c (drop (j * c) w)) \<in> Sigma_tm M" .
    have step:
      "(mid_encoder_config_gen (k_tm M) M pack c w j,
        mid_encoder_config_gen (k_tm M) M pack c w (Suc j)) \<in> ?R\<^sup>*"
      by (rule mid_encoder_step[where pack = pack,
                OF vM c_pos w_alpha block_full pack_block_j bl_ne_le k2])
    from ih step show ?case by (rule rtrancl_trans)
  qed

  have to_mid_i: "(mid_encoder_config_gen (k_tm M) M pack c w 0,
                    mid_encoder_config_gen (k_tm M) M pack c w i) \<in> ?R\<^sup>*"
    using iter[of i] by simp

  have boundary:
    "mid_encoder_config_gen (k_tm M) M pack c w i
       = mid_buf_extending_config_gen (k_tm M) M pack c w i 0"
    by (simp add: mid_encoder_config_gen_def mid_buf_extending_config_gen_def
                  fun_eq_iff split: nat.split)

  have extend_iter:
    "k < c \<Longrightarrow>
     (mid_buf_extending_config_gen (k_tm M) M pack c w i 0,
      mid_buf_extending_config_gen (k_tm M) M pack c w i k) \<in> ?R\<^sup>*" for k
  proof (induction k)
    case 0 show ?case by simp
  next
    case (Suc k)
    from Suc.prems have Suc_k_lt_c: "Suc k < c" by simp
    from Suc_k_lt_c have k_lt_c: "k < c" by simp
    from Suc.IH[OF k_lt_c]
    have ih_k: "(mid_buf_extending_config_gen (k_tm M) M pack c w i 0,
                  mid_buf_extending_config_gen (k_tm M) M pack c w i k) \<in> ?R\<^sup>*" .
    have ic_k_lt: "i * c + k < length w"
    proof -
      have "i * c + k < i * c + c" using k_lt_c by simp
      also have "\<dots> = (Suc i) * c" by simp
      also have "\<dots> \<le> length w" using i_full .
      finally show ?thesis .
    qed
    have step:
      "(mid_buf_extending_config_gen (k_tm M) M pack c w i k,
        mid_buf_extending_config_gen (k_tm M) M pack c w i (Suc k)) \<in> ?R"
      by (rule mid_buf_extend_step[OF vM c_pos w_alpha Suc_k_lt_c ic_k_lt])
    from ih_k step show ?case
      by (rule rtrancl_into_rtrancl)
  qed

  have to_extending:
    "(mid_buf_extending_config_gen (k_tm M) M pack c w i 0,
      mid_buf_extending_config_gen (k_tm M) M pack c w i (c - 1)) \<in> ?R\<^sup>*"
    using extend_iter[of "c - 1"] c_pos by simp

  from init_step have init_rt:
    "(init_config_mttm (encoding_wrap M pack c \<Sigma>u) (map Raw w),
      mid_encoder_config_gen (k_tm M) M pack c w 0) \<in> ?R\<^sup>*"
    by (rule r_into_rtrancl)
  from init_rt to_mid_i
  have init_to_mid_i:
    "(init_config_mttm (encoding_wrap M pack c \<Sigma>u) (map Raw w),
      mid_encoder_config_gen (k_tm M) M pack c w i) \<in> ?R\<^sup>*"
    by (rule rtrancl_trans)
  from to_extending boundary
  have mid_to_ext:
    "(mid_encoder_config_gen (k_tm M) M pack c w i,
      mid_buf_extending_config_gen (k_tm M) M pack c w i (c - 1)) \<in> ?R\<^sup>*"
    by simp
  from init_to_mid_i mid_to_ext
  show ?thesis by (rule rtrancl_trans)
qed

text \<open>Canonical sub-chain to the partial-block end-of-input config.  Given pack
  contracts for every full block @{term "j < i"}, the trace extends through the
  encoder up to the partial block's last extend, stopping right before the
  partial close.\<close>

lemma init_to_mid_buf_partial:
  fixes M :: "('q, 'b) mttm"
  assumes vM: "valid_mttm M"
      and c_pos: "0 < c"
      and w_alpha: "set w \<subseteq> \<Sigma>u"
      and bl_ne_le: "bl_tm M \<noteq> le_tm M"
      and k2: "2 \<le> k_tm M"
      and i_lt: "i * c < length w"
      and i_partial: "length w < (Suc i) * c"
      and pack_ih: "\<And>j. j < i \<Longrightarrow> pack (take c (drop (j * c) w)) \<in> Sigma_tm M"
    shows "(init_config_mttm (encoding_wrap M pack c \<Sigma>u) (map Raw w),
            mid_buf_extending_config_gen (k_tm M) M pack c w i (length w - i * c))
              \<in> (mttm_step (wrap_delta M pack c \<Sigma>u))\<^sup>*"
proof -
  let ?R = "mttm_step (wrap_delta M pack c \<Sigma>u)"
  define kp where "kp = length w - i * c"

  from i_lt have kp_pos: "0 < kp" unfolding kp_def by simp
  from i_partial have len_lt: "length w < c + i * c" by simp
  from i_lt len_lt have kp_lt_c: "kp < c"
    unfolding kp_def by linarith
  have ic_plus_kp: "i * c + kp = length w"
    using i_lt unfolding kp_def by simp

  have init_step:
    "(init_config_mttm (encoding_wrap M pack c \<Sigma>u) (map Raw w),
      mid_encoder_config_gen (k_tm M) M pack c w 0) \<in> ?R"
    by (rule init_to_mid_zero[OF vM c_pos])

  have iter:
    "j \<le> i \<Longrightarrow>
     (mid_encoder_config_gen (k_tm M) M pack c w 0,
      mid_encoder_config_gen (k_tm M) M pack c w j) \<in> ?R\<^sup>*" for j
  proof (induction j)
    case 0 show ?case by simp
  next
    case (Suc j)
    from Suc.prems have j_le_i: "j \<le> i" by simp
    from Suc.prems have Suc_j_le_i: "Suc j \<le> i" by simp
    from Suc.IH[OF j_le_i]
    have ih: "(mid_encoder_config_gen (k_tm M) M pack c w 0,
               mid_encoder_config_gen (k_tm M) M pack c w j) \<in> ?R\<^sup>*" .
    have block_full: "(Suc j) * c \<le> length w"
    proof -
      from Suc_j_le_i have "(Suc j) * c \<le> i * c"
        by (rule mult_le_mono1)
      also have "\<dots> \<le> length w" using i_lt by simp
      finally show ?thesis .
    qed
    from Suc_j_le_i have j_lt_i: "j < i" by simp
    from pack_ih[OF j_lt_i]
    have pack_block_j: "pack (take c (drop (j * c) w)) \<in> Sigma_tm M" .
    have step:
      "(mid_encoder_config_gen (k_tm M) M pack c w j,
        mid_encoder_config_gen (k_tm M) M pack c w (Suc j)) \<in> ?R\<^sup>*"
      by (rule mid_encoder_step[where pack = pack,
                OF vM c_pos w_alpha block_full pack_block_j bl_ne_le k2])
    from ih step show ?case by (rule rtrancl_trans)
  qed

  have to_mid_i: "(mid_encoder_config_gen (k_tm M) M pack c w 0,
                    mid_encoder_config_gen (k_tm M) M pack c w i) \<in> ?R\<^sup>*"
    using iter[of i] by simp

  have boundary:
    "mid_encoder_config_gen (k_tm M) M pack c w i
       = mid_buf_extending_config_gen (k_tm M) M pack c w i 0"
    by (simp add: mid_encoder_config_gen_def mid_buf_extending_config_gen_def
                  fun_eq_iff split: nat.split)

  have extend_iter:
    "k \<le> kp \<Longrightarrow>
     (mid_buf_extending_config_gen (k_tm M) M pack c w i 0,
      mid_buf_extending_config_gen (k_tm M) M pack c w i k) \<in> ?R\<^sup>*" for k
  proof (induction k)
    case 0 show ?case by simp
  next
    case (Suc k)
    from Suc.prems have Suc_k_le_kp: "Suc k \<le> kp" by simp
    from Suc_k_le_kp have k_le_kp: "k \<le> kp" by simp
    from Suc.IH[OF k_le_kp]
    have ih_k: "(mid_buf_extending_config_gen (k_tm M) M pack c w i 0,
                  mid_buf_extending_config_gen (k_tm M) M pack c w i k) \<in> ?R\<^sup>*" .
    from Suc_k_le_kp kp_lt_c have Suc_k_lt_c: "Suc k < c" by simp
    from Suc_k_le_kp ic_plus_kp have ic_k_lt: "i * c + k < length w"
      by linarith
    have step:
      "(mid_buf_extending_config_gen (k_tm M) M pack c w i k,
        mid_buf_extending_config_gen (k_tm M) M pack c w i (Suc k)) \<in> ?R"
      by (rule mid_buf_extend_step[OF vM c_pos w_alpha Suc_k_lt_c ic_k_lt])
    from ih_k step show ?case
      by (rule rtrancl_into_rtrancl)
  qed

  have to_extending:
    "(mid_buf_extending_config_gen (k_tm M) M pack c w i 0,
      mid_buf_extending_config_gen (k_tm M) M pack c w i kp) \<in> ?R\<^sup>*"
    using extend_iter[of kp] by simp

  from init_step have init_rt:
    "(init_config_mttm (encoding_wrap M pack c \<Sigma>u) (map Raw w),
      mid_encoder_config_gen (k_tm M) M pack c w 0) \<in> ?R\<^sup>*"
    by (rule r_into_rtrancl)
  from init_rt to_mid_i
  have init_to_mid_i:
    "(init_config_mttm (encoding_wrap M pack c \<Sigma>u) (map Raw w),
      mid_encoder_config_gen (k_tm M) M pack c w i) \<in> ?R\<^sup>*"
    by (rule rtrancl_trans)
  from to_extending boundary
  have mid_to_ext:
    "(mid_encoder_config_gen (k_tm M) M pack c w i,
      mid_buf_extending_config_gen (k_tm M) M pack c w i kp) \<in> ?R\<^sup>*"
    by simp
  from init_to_mid_i mid_to_ext
  have "(init_config_mttm (encoding_wrap M pack c \<Sigma>u) (map Raw w),
         mid_buf_extending_config_gen (k_tm M) M pack c w i kp) \<in> ?R\<^sup>*"
    by (rule rtrancl_trans)
  thus ?thesis unfolding kp_def .
qed


subsection \<open>Pack contracts by strong induction\<close>

text \<open>Pack contracts for full blocks via strong induction: given an accepting
  wrap-trace, every full block @{term i} satisfies
  @{prop "pack (take c (drop (i * c) w)) \<in> Sigma_tm M"}.\<close>

lemma wrap_full_block_pack_contract:
  fixes M :: "('q, 'b) mttm"
    and i :: nat
  assumes vM: "valid_mttm M"
      and c_pos: "0 < c"
      and bl_ne_le: "bl_tm M \<noteq> le_tm M"
      and w_alpha: "set w \<subseteq> \<Sigma>u"
      and k2: "2 \<le> k_tm M"
      and trace: "(init_config_mttm (encoding_wrap M pack c \<Sigma>u) (map Raw w), C_acc)
                    \<in> (mttm_step (wrap_delta M pack c \<Sigma>u))\<^sup>*"
      and accept: "\<exists>q. mt_state C_acc = W_Run q"
      and i_full: "(Suc i) * c \<le> length w"
    shows "pack (take c (drop (i * c) w)) \<in> Sigma_tm M"
proof -
  let ?R = "mttm_step (wrap_delta M pack c \<Sigma>u)"
  let ?init = "init_config_mttm (encoding_wrap M pack c \<Sigma>u) (map Raw w)"

  from wrap_first_W_Run_decomp[OF trace accept]
  obtain C_pre C_post where
      pre_chain: "(?init, C_pre) \<in> ?R\<^sup>*"
    and pre_state: "mt_state C_pre = W_Disp"
    and pre_step: "(C_pre, C_post) \<in> ?R"
    and post_state: "mt_state C_post = W_Run (s_tm M)"
    and post_chain: "(C_post, C_acc) \<in> ?R\<^sup>*"
    by blast

  have C_pre_non_run: "\<forall>q. mt_state C_pre \<noteq> W_Run q"
    by (simp add: pre_state)

  from pre_chain obtain T_pre where pre_pow:
    "(?init, C_pre) \<in> ?R ^^ T_pre"
    by (auto dest: rtrancl_imp_relpow)

  from i_full
  show ?thesis
  proof (induction i rule: less_induct)
    case (less i)
    note i_full_curr = less.prems

    have pack_ih: "\<And>j. j < i \<Longrightarrow> pack (take c (drop (j * c) w)) \<in> Sigma_tm M"
    proof -
      fix j assume j_lt: "j < i"
      have j_full: "(Suc j) * c \<le> length w"
      proof -
        from j_lt have "Suc j \<le> i" by simp
        hence "(Suc j) * c \<le> i * c" by (rule mult_le_mono1)
        also have "\<dots> \<le> (Suc i) * c" by simp
        also have "\<dots> \<le> length w" using i_full_curr .
        finally show ?thesis .
      qed
      from less.IH[OF j_lt j_full]
      show "pack (take c (drop (j * c) w)) \<in> Sigma_tm M" .
    qed

    have chain_i:
      "(?init, mid_buf_extending_config_gen (k_tm M) M pack c w i (c - 1)) \<in> ?R\<^sup>*"
      by (rule init_to_mid_buf_extending
            [where pack = pack,
             OF vM c_pos w_alpha bl_ne_le k2 i_full_curr pack_ih])
    from chain_i obtain N_i where chain_pow:
      "(?init, mid_buf_extending_config_gen (k_tm M) M pack c w i (c - 1)) \<in> ?R ^^ N_i"
      by (auto dest: rtrancl_imp_relpow)

    have end_state:
      "mt_state (mid_buf_extending_config_gen (k_tm M) M pack c w i (c - 1))
         = W_Buf (take (c - 1) (drop (i * c) w))"
      by (simp add: mid_buf_extending_config_gen_def)
    have end_non_run:
      "\<forall>q. mt_state (mid_buf_extending_config_gen (k_tm M) M pack c w i (c - 1)) \<noteq> W_Run q"
      using end_state by auto

    have T_pre_ge: "N_i \<le> T_pre"
    proof (rule ccontr)
      assume "\<not> N_i \<le> T_pre"
      hence T_lt: "T_pre < N_i" by simp
      have add_eq: "T_pre + (N_i - T_pre) = N_i"
        using T_lt by simp
      have rel_add:
        "(?R ^^ T_pre) O (?R ^^ (N_i - T_pre)) = ?R ^^ N_i"
        using add_eq by (metis relpow_add)
      from chain_pow rel_add
      have "(?init, mid_buf_extending_config_gen (k_tm M) M pack c w i (c - 1))
              \<in> (?R ^^ T_pre) O (?R ^^ (N_i - T_pre))"
        by simp
      then obtain Z where
          Z_path: "(?init, Z) \<in> ?R ^^ T_pre"
        and Z_to_end: "(Z, mid_buf_extending_config_gen (k_tm M) M pack c w i (c - 1))
                         \<in> ?R ^^ (N_i - T_pre)"
        by auto

      have Z_to_end_rt:
        "(Z, mid_buf_extending_config_gen (k_tm M) M pack c w i (c - 1)) \<in> ?R\<^sup>*"
        using Z_to_end by (rule relpow_imp_rtrancl)
      have Z_non_run: "\<forall>q. mt_state Z \<noteq> W_Run q"
      proof (intro allI notI)
        fix q assume Z_run: "mt_state Z = W_Run q"
        from wrap_W_Run_persistent[OF Z_to_end_rt Z_run]
        obtain q' where
          "mt_state (mid_buf_extending_config_gen (k_tm M) M pack c w i (c - 1)) = W_Run q'"
          by blast
        with end_non_run show False by blast
      qed

      from wrap_path_det_non_run[OF Z_path pre_pow Z_non_run C_pre_non_run]
      have Z_eq: "Z = C_pre" .
      have Z_state: "mt_state Z = W_Disp" using Z_eq pre_state by simp
      have N_i_gt: "0 < N_i - T_pre" using T_lt by simp
      from wrap_W_Disp_then_W_Run[OF Z_to_end Z_state N_i_gt]
      obtain q' where
        "mt_state (mid_buf_extending_config_gen (k_tm M) M pack c w i (c - 1)) = W_Run q'"
        by blast
      with end_non_run show False by blast
    qed

    from T_pre_ge obtain T_suffix where T_split: "T_pre = N_i + T_suffix"
      by (metis le_iff_add)
    have rel_add_pre:
      "(?R ^^ N_i) O (?R ^^ T_suffix) = ?R ^^ T_pre"
      using T_split by (metis relpow_add)
    from pre_pow rel_add_pre
    have "(?init, C_pre) \<in> (?R ^^ N_i) O (?R ^^ T_suffix)"
      by simp
    then obtain Y_N where
        init_to_Y: "(?init, Y_N) \<in> ?R ^^ N_i"
      and Y_to_pre: "(Y_N, C_pre) \<in> ?R ^^ T_suffix"
      by auto

    have Y_to_pre_rt: "(Y_N, C_pre) \<in> ?R\<^sup>*"
      using Y_to_pre by (rule relpow_imp_rtrancl)
    have Y_N_non_run: "\<forall>q. mt_state Y_N \<noteq> W_Run q"
    proof (intro allI notI)
      fix q assume Y_N_run: "mt_state Y_N = W_Run q"
      from wrap_W_Run_persistent[OF Y_to_pre_rt Y_N_run]
      obtain q' where "mt_state C_pre = W_Run q'" by blast
      with C_pre_non_run show False by blast
    qed
    from wrap_path_det_non_run[OF init_to_Y chain_pow Y_N_non_run end_non_run]
    have Y_N_eq: "Y_N = mid_buf_extending_config_gen (k_tm M) M pack c w i (c - 1)" .

    have T_suffix_pos: "0 < T_suffix"
    proof (rule ccontr)
      assume "\<not> 0 < T_suffix"
      hence T_suff_0: "T_suffix = 0" by simp
      from Y_to_pre T_suff_0 have Y_eq_pre: "Y_N = C_pre" by simp
      from Y_eq_pre Y_N_eq pre_state
      have "mt_state (mid_buf_extending_config_gen (k_tm M) M pack c w i (c - 1)) = W_Disp"
        by simp
      with end_state show False by simp
    qed

    from T_suffix_pos obtain T' where T_suff_eq: "T_suffix = Suc T'"
      by (cases T_suffix) auto
    from Y_to_pre T_suff_eq
    have Y_to_pre_Suc: "(Y_N, C_pre) \<in> ?R ^^ Suc T'" by simp
    from Y_to_pre_Suc obtain Z_next where
        Y_to_Z: "(Y_N, Z_next) \<in> ?R"
      and Z_to_pre: "(Z_next, C_pre) \<in> ?R ^^ T'"
      by (rule relpow_Suc_E2)

    have step_close:
      "(mid_buf_extending_config_gen (k_tm M) M pack c w i (c - 1), Z_next) \<in> ?R"
      using Y_to_Z Y_N_eq by simp
    from wrap_close_step_forces_pack
          [OF vM c_pos w_alpha i_full_curr bl_ne_le k2 step_close]
    have "pack (take c (drop (i * c) w)) \<in> Sigma_tm M
          \<and> Z_next = mid_encoder_config_gen (k_tm M) M pack c w (Suc i)" .
    thus ?case by simp
  qed
qed

text \<open>Pack contract for the partial block, by single-shot argument.\<close>

lemma wrap_partial_block_pack_contract:
  fixes M :: "('q, 'b) mttm"
    and i :: nat
  assumes vM: "valid_mttm M"
      and c_pos: "0 < c"
      and bl_ne_le: "bl_tm M \<noteq> le_tm M"
      and w_alpha: "set w \<subseteq> \<Sigma>u"
      and k2: "2 \<le> k_tm M"
      and trace: "(init_config_mttm (encoding_wrap M pack c \<Sigma>u) (map Raw w), C_acc)
                    \<in> (mttm_step (wrap_delta M pack c \<Sigma>u))\<^sup>*"
      and accept: "\<exists>q. mt_state C_acc = W_Run q"
      and i_lt: "i * c < length w"
      and i_partial: "length w < (Suc i) * c"
      and i_div: "i = length w div c"
      and pack_ih: "\<And>j. j < i \<Longrightarrow> pack (take c (drop (j * c) w)) \<in> Sigma_tm M"
    shows "pack (take c (drop (i * c) w)) \<in> Sigma_tm M"
proof -
  let ?R = "mttm_step (wrap_delta M pack c \<Sigma>u)"
  let ?init = "init_config_mttm (encoding_wrap M pack c \<Sigma>u) (map Raw w)"
  define kp where "kp = length w - i * c"

  from wrap_first_W_Run_decomp[OF trace accept]
  obtain C_pre C_post where
      pre_chain: "(?init, C_pre) \<in> ?R\<^sup>*"
    and pre_state: "mt_state C_pre = W_Disp"
    and pre_step: "(C_pre, C_post) \<in> ?R"
    and post_state: "mt_state C_post = W_Run (s_tm M)"
    and post_chain: "(C_post, C_acc) \<in> ?R\<^sup>*"
    by blast

  have C_pre_non_run: "\<forall>q. mt_state C_pre \<noteq> W_Run q"
    by (simp add: pre_state)

  from pre_chain obtain T_pre where pre_pow:
    "(?init, C_pre) \<in> ?R ^^ T_pre"
    by (auto dest: rtrancl_imp_relpow)

  have chain_i:
    "(?init, mid_buf_extending_config_gen (k_tm M) M pack c w i kp) \<in> ?R\<^sup>*"
    using init_to_mid_buf_partial
            [where pack = pack,
             OF vM c_pos w_alpha bl_ne_le k2 i_lt i_partial pack_ih]
    unfolding kp_def .
  from chain_i obtain N_i where chain_pow:
    "(?init, mid_buf_extending_config_gen (k_tm M) M pack c w i kp) \<in> ?R ^^ N_i"
    by (auto dest: rtrancl_imp_relpow)

  have end_state:
    "mt_state (mid_buf_extending_config_gen (k_tm M) M pack c w i kp)
       = W_Buf (take kp (drop (i * c) w))"
    by (simp add: mid_buf_extending_config_gen_def)
  have end_non_run:
    "\<forall>q. mt_state (mid_buf_extending_config_gen (k_tm M) M pack c w i kp) \<noteq> W_Run q"
    using end_state by auto

  have T_pre_ge: "N_i \<le> T_pre"
  proof (rule ccontr)
    assume "\<not> N_i \<le> T_pre"
    hence T_lt: "T_pre < N_i" by simp
    have add_eq: "T_pre + (N_i - T_pre) = N_i"
      using T_lt by simp
    have rel_add:
      "(?R ^^ T_pre) O (?R ^^ (N_i - T_pre)) = ?R ^^ N_i"
      using add_eq by (metis relpow_add)
    from chain_pow rel_add
    have "(?init, mid_buf_extending_config_gen (k_tm M) M pack c w i kp)
            \<in> (?R ^^ T_pre) O (?R ^^ (N_i - T_pre))"
      by simp
    then obtain Z where
        Z_path: "(?init, Z) \<in> ?R ^^ T_pre"
      and Z_to_end: "(Z, mid_buf_extending_config_gen (k_tm M) M pack c w i kp)
                       \<in> ?R ^^ (N_i - T_pre)"
      by auto

    have Z_to_end_rt:
      "(Z, mid_buf_extending_config_gen (k_tm M) M pack c w i kp) \<in> ?R\<^sup>*"
      using Z_to_end by (rule relpow_imp_rtrancl)
    have Z_non_run: "\<forall>q. mt_state Z \<noteq> W_Run q"
    proof (intro allI notI)
      fix q assume Z_run: "mt_state Z = W_Run q"
      from wrap_W_Run_persistent[OF Z_to_end_rt Z_run]
      obtain q' where
        "mt_state (mid_buf_extending_config_gen (k_tm M) M pack c w i kp) = W_Run q'"
        by blast
      with end_non_run show False by blast
    qed

    from wrap_path_det_non_run[OF Z_path pre_pow Z_non_run C_pre_non_run]
    have Z_eq: "Z = C_pre" .
    have Z_state: "mt_state Z = W_Disp" using Z_eq pre_state by simp
    have N_i_gt: "0 < N_i - T_pre" using T_lt by simp
    from wrap_W_Disp_then_W_Run[OF Z_to_end Z_state N_i_gt]
    obtain q' where
      "mt_state (mid_buf_extending_config_gen (k_tm M) M pack c w i kp) = W_Run q'"
      by blast
    with end_non_run show False by blast
  qed

  from T_pre_ge obtain T_suffix where T_split: "T_pre = N_i + T_suffix"
    by (metis le_iff_add)
  have rel_add_pre:
    "(?R ^^ N_i) O (?R ^^ T_suffix) = ?R ^^ T_pre"
    using T_split by (metis relpow_add)
  from pre_pow rel_add_pre
  have "(?init, C_pre) \<in> (?R ^^ N_i) O (?R ^^ T_suffix)"
    by simp
  then obtain Y_N where
      init_to_Y: "(?init, Y_N) \<in> ?R ^^ N_i"
    and Y_to_pre: "(Y_N, C_pre) \<in> ?R ^^ T_suffix"
    by auto

  have Y_to_pre_rt: "(Y_N, C_pre) \<in> ?R\<^sup>*"
    using Y_to_pre by (rule relpow_imp_rtrancl)
  have Y_N_non_run: "\<forall>q. mt_state Y_N \<noteq> W_Run q"
  proof (intro allI notI)
    fix q assume Y_N_run: "mt_state Y_N = W_Run q"
    from wrap_W_Run_persistent[OF Y_to_pre_rt Y_N_run]
    obtain q' where "mt_state C_pre = W_Run q'" by blast
    with C_pre_non_run show False by blast
  qed
  from wrap_path_det_non_run[OF init_to_Y chain_pow Y_N_non_run end_non_run]
  have Y_N_eq: "Y_N = mid_buf_extending_config_gen (k_tm M) M pack c w i kp" .

  have T_suffix_pos: "0 < T_suffix"
  proof (rule ccontr)
    assume "\<not> 0 < T_suffix"
    hence T_suff_0: "T_suffix = 0" by simp
    from Y_to_pre T_suff_0 have Y_eq_pre: "Y_N = C_pre" by simp
    from Y_eq_pre Y_N_eq pre_state
    have "mt_state (mid_buf_extending_config_gen (k_tm M) M pack c w i kp) = W_Disp"
      by simp
    with end_state show False by simp
  qed

  from T_suffix_pos obtain T' where T_suff_eq: "T_suffix = Suc T'"
    by (cases T_suffix) auto
  from Y_to_pre T_suff_eq
  have Y_to_pre_Suc: "(Y_N, C_pre) \<in> ?R ^^ Suc T'" by simp
  from Y_to_pre_Suc obtain Z_next where
      Y_to_Z: "(Y_N, Z_next) \<in> ?R"
    and Z_to_pre: "(Z_next, C_pre) \<in> ?R ^^ T'"
    by (rule relpow_Suc_E2)

  have step_close:
    "(mid_buf_extending_config_gen (k_tm M) M pack c w i kp, Z_next) \<in> ?R"
    using Y_to_Z Y_N_eq by simp
  have step_close_kp:
    "(mid_buf_extending_config_gen (k_tm M) M pack c w i (length w - i * c), Z_next) \<in> ?R"
    using step_close unfolding kp_def .
  from wrap_partial_close_step_forces_pack
        [OF vM c_pos w_alpha bl_ne_le k2 i_lt i_partial i_div step_close_kp]
  have "pack (take c (drop (i * c) w)) \<in> Sigma_tm M
        \<and> Z_next = post_encoder_config_gen (k_tm M) M pack c w" .
  thus ?thesis by simp
qed

subsection \<open>The canonical-factor lemma\<close>

text \<open>Any accepting wrap-trace reaches the floated @{const post_plant_dispatch_config}
  and the per-block pack contracts hold.
  The canonical chain to the @{term W_Disp} config @{const mid_plant_disp_config}
  goes through the plant reset (@{thm[source] plant_rewind_loop_relpow} +
  @{thm[source] plant_done_step}), and the dispatch step is
  @{thm[source] plant_disp_step}.\<close>

lemma wrap_accept_canonical_factor:
  fixes M :: "('q, 'b) mttm"
  assumes vM: "valid_mttm M"
      and c_pos: "0 < c"
      and bl_ne_le: "bl_tm M \<noteq> le_tm M"
      and w_alpha: "set w \<subseteq> \<Sigma>u"
      and k2: "2 \<le> k_tm M"
      and trace: "(init_config_mttm (encoding_wrap M pack c \<Sigma>u) (map Raw w),
                   C_acc)
                    \<in> (mttm_step (wrap_delta M pack c \<Sigma>u))\<^sup>*"
      and accept_state: "\<exists>q. mt_state C_acc = W_Run q"
    shows "(post_plant_dispatch_config M pack c w, C_acc)
              \<in> (mttm_step (wrap_delta M pack c \<Sigma>u))\<^sup>*
        \<and> (\<forall>i. i * c < length w
              \<longrightarrow> pack (take c (drop (i * c) w)) \<in> Sigma_tm M)"
proof -
  let ?R = "mttm_step (wrap_delta M pack c \<Sigma>u)"
  let ?init = "init_config_mttm (encoding_wrap M pack c \<Sigma>u) (map Raw w)"

  obtain Q \<Sigma>i \<Gamma>set bl le \<delta>M sM tM rM kM where M_eq:
    "M = MTTM Q \<Sigma>i \<Gamma>set bl le \<delta>M sM tM rM kM"
    by (cases M)
  have Sigma_sub_Gamma: "Sigma_tm M \<subseteq> \<Gamma>_tm M" using vM M_eq by auto
  have le_not_in_Sigma: "le_tm M \<notin> Sigma_tm M" using vM M_eq by auto

  \<comment> \<open>Pack contracts: full blocks via @{thm[source] wrap_full_block_pack_contract},
    the partial block via @{thm[source] wrap_partial_block_pack_contract}.\<close>
  have pack_in_Sigma:
    "\<And>i. i * c < length w \<Longrightarrow> pack (take c (drop (i * c) w)) \<in> Sigma_tm M"
  proof -
    fix i :: nat
    assume i_lt: "i * c < length w"
    show "pack (take c (drop (i * c) w)) \<in> Sigma_tm M"
    proof (cases "(Suc i) * c \<le> length w")
      case True
      show ?thesis
        by (rule wrap_full_block_pack_contract
              [where pack = pack,
               OF vM c_pos bl_ne_le w_alpha k2 trace accept_state True])
    next
      case False
      hence i_partial: "length w < (Suc i) * c" by simp
      have i_div: "i = length w div c"
      proof -
        have lo: "i \<le> length w div c"
        proof -
          from i_lt have "i * c \<le> length w" by simp
          hence "(i * c) div c \<le> length w div c" by (rule div_le_mono)
          with c_pos show "i \<le> length w div c" by simp
        qed
        have hi: "length w div c \<le> i"
        proof -
          from i_partial c_pos have "length w div c < Suc i"
            by (simp add: div_less_iff_less_mult mult.commute)
          thus "length w div c \<le> i" by simp
        qed
        from lo hi show ?thesis by simp
      qed
      have pack_ih:
        "\<And>j. j < i \<Longrightarrow> pack (take c (drop (j * c) w)) \<in> Sigma_tm M"
      proof -
        fix j assume j_lt: "j < i"
        have j_full: "(Suc j) * c \<le> length w"
        proof -
          from j_lt have "Suc j \<le> i" by simp
          hence "(Suc j) * c \<le> i * c" by (rule mult_le_mono1)
          also have "\<dots> \<le> length w" using i_lt by simp
          finally show ?thesis .
        qed
        show "pack (take c (drop (j * c) w)) \<in> Sigma_tm M"
          by (rule wrap_full_block_pack_contract
                [where pack = pack,
                 OF vM c_pos bl_ne_le w_alpha k2 trace accept_state j_full])
      qed
      show ?thesis
        by (rule wrap_partial_block_pack_contract
              [where pack = pack,
               OF vM c_pos bl_ne_le w_alpha k2 trace accept_state
                  i_lt i_partial i_div pack_ih])
    qed
  qed

  have pack_in_Gamma:
    "\<And>i. i * c < length w \<Longrightarrow> pack (take c (drop (i * c) w)) \<in> \<Gamma>_tm M"
  proof -
    fix i :: nat assume i_lt: "i * c < length w"
    from pack_in_Sigma[OF i_lt] Sigma_sub_Gamma
    show "pack (take c (drop (i * c) w)) \<in> \<Gamma>_tm M" by auto
  qed
  have pack_ne_le:
    "\<And>i. i * c < length w \<Longrightarrow> pack (take c (drop (i * c) w)) \<noteq> le_tm M"
  proof -
    fix i :: nat assume i_lt: "i * c < length w"
    from pack_in_Sigma[OF i_lt] le_not_in_Sigma
    show "pack (take c (drop (i * c) w)) \<noteq> le_tm M" by auto
  qed

  \<comment> \<open>Canonical chain to @{const mid_plant_disp_config}: encoder, plant
    storage rewind (input head frozen), plant-done.\<close>
  have enc_step:
    "(?init, post_encoder_config_gen (k_tm M) M pack c w) \<in> ?R\<^sup>*"
    by (rule encoder_phase_terminates
          [where pack = pack,
           OF vM c_pos w_alpha bl_ne_le k2 pack_in_Sigma])
  have loop_relpow:
    "(post_encoder_config_gen (k_tm M) M pack c w,
      mid_reset_combined_config_gen (k_tm M) M pack c w (length w + 1) 0)
       \<in> ?R ^^ (Suc (length (wrap_enc pack c w)))"
    apply (rule plant_rewind_loop_relpow[OF vM c_pos w_alpha bl_ne_le k2])
     apply (fact pack_in_Gamma)
    apply (fact pack_ne_le)
    done
  have loop_step:
    "(post_encoder_config_gen (k_tm M) M pack c w,
      mid_reset_combined_config_gen (k_tm M) M pack c w (length w + 1) 0) \<in> ?R\<^sup>*"
    using loop_relpow by (rule relpow_imp_rtrancl)
  have done_step:
    "(mid_reset_combined_config_gen (k_tm M) M pack c w (length w + 1) 0,
      mid_plant_disp_config M pack c w) \<in> ?R"
    by (rule plant_done_step[OF vM k2])
  have done_step_rt:
    "(mid_reset_combined_config_gen (k_tm M) M pack c w (length w + 1) 0,
      mid_plant_disp_config M pack c w) \<in> ?R\<^sup>*"
    using done_step by (rule r_into_rtrancl)
  from enc_step loop_step have init_to_loop:
    "(?init, mid_reset_combined_config_gen (k_tm M) M pack c w (length w + 1) 0) \<in> ?R\<^sup>*"
    by (rule rtrancl_trans)
  from init_to_loop done_step_rt have canon_to_disp:
    "(?init, mid_plant_disp_config M pack c w) \<in> ?R\<^sup>*"
    by (rule rtrancl_trans)

  have canon_disp_step:
    "(mid_plant_disp_config M pack c w, post_plant_dispatch_config M pack c w) \<in> ?R"
    by (rule plant_disp_step[OF vM k2])

  from wrap_first_W_Run_decomp[OF trace accept_state]
  obtain C_pre C_post where
      pre_chain: "(?init, C_pre) \<in> ?R\<^sup>*"
    and pre_state: "mt_state C_pre = W_Disp"
    and pre_step: "(C_pre, C_post) \<in> ?R"
    and post_state: "mt_state C_post = W_Run (s_tm M)"
    and post_chain: "(C_post, C_acc) \<in> ?R\<^sup>*"
    by blast

  have C_pre_non_run: "\<forall>q. mt_state C_pre \<noteq> W_Run q"
    by (simp add: pre_state)
  have disp_state:
    "mt_state (mid_plant_disp_config M pack c w) = W_Disp"
    by (simp add: mid_plant_disp_config_def)
  have disp_non_run:
    "\<forall>q. mt_state (mid_plant_disp_config M pack c w) \<noteq> W_Run q"
    by (simp add: disp_state)

  from pre_chain obtain T_pre where pre_pow:
    "(?init, C_pre) \<in> ?R ^^ T_pre"
    by (auto dest: rtrancl_imp_relpow)
  from canon_to_disp obtain N where canon_pow:
    "(?init, mid_plant_disp_config M pack c w) \<in> ?R ^^ N"
    by (auto dest: rtrancl_imp_relpow)

  have T_pre_ge: "N \<le> T_pre"
  proof (rule ccontr)
    assume "\<not> N \<le> T_pre"
    hence T_lt: "T_pre < N" by simp
    have add_eq: "T_pre + (N - T_pre) = N" using T_lt by simp
    have rel_add:
      "(?R ^^ T_pre) O (?R ^^ (N - T_pre)) = ?R ^^ N"
      using add_eq by (metis relpow_add)
    from canon_pow rel_add
    have "(?init, mid_plant_disp_config M pack c w)
            \<in> (?R ^^ T_pre) O (?R ^^ (N - T_pre))"
      by simp
    then obtain Z where
        Z_path: "(?init, Z) \<in> ?R ^^ T_pre"
      and Z_to_disp: "(Z, mid_plant_disp_config M pack c w) \<in> ?R ^^ (N - T_pre)"
      by auto
    have Z_to_disp_rt: "(Z, mid_plant_disp_config M pack c w) \<in> ?R\<^sup>*"
      using Z_to_disp by (rule relpow_imp_rtrancl)
    have Z_non_run: "\<forall>q. mt_state Z \<noteq> W_Run q"
    proof (intro allI notI)
      fix q assume Z_run: "mt_state Z = W_Run q"
      from wrap_W_Run_persistent[OF Z_to_disp_rt Z_run]
      obtain q' where
        "mt_state (mid_plant_disp_config M pack c w) = W_Run q'" by blast
      with disp_non_run show False by blast
    qed
    from wrap_path_det_non_run[OF Z_path pre_pow Z_non_run C_pre_non_run]
    have Z_eq: "Z = C_pre" .
    have Z_state: "mt_state Z = W_Disp" using Z_eq pre_state by simp
    have N_gt: "0 < N - T_pre" using T_lt by simp
    from wrap_W_Disp_then_W_Run[OF Z_to_disp Z_state N_gt]
    obtain q' where
      "mt_state (mid_plant_disp_config M pack c w) = W_Run q'" by blast
    with disp_non_run show False by blast
  qed

  have T_pre_le: "T_pre \<le> N"
  proof (rule ccontr)
    assume "\<not> T_pre \<le> N"
    hence N_lt: "N < T_pre" by simp
    have add_eq: "N + (T_pre - N) = T_pre" using N_lt by simp
    have rel_add:
      "(?R ^^ N) O (?R ^^ (T_pre - N)) = ?R ^^ T_pre"
      using add_eq by (metis relpow_add)
    from pre_pow rel_add
    have "(?init, C_pre) \<in> (?R ^^ N) O (?R ^^ (T_pre - N))"
      by simp
    then obtain Y where
        Y_path: "(?init, Y) \<in> ?R ^^ N"
      and Y_to_pre: "(Y, C_pre) \<in> ?R ^^ (T_pre - N)"
      by auto
    have Y_to_pre_rt: "(Y, C_pre) \<in> ?R\<^sup>*"
      using Y_to_pre by (rule relpow_imp_rtrancl)
    have Y_non_run: "\<forall>q. mt_state Y \<noteq> W_Run q"
    proof (intro allI notI)
      fix q assume Y_run: "mt_state Y = W_Run q"
      from wrap_W_Run_persistent[OF Y_to_pre_rt Y_run]
      obtain q' where "mt_state C_pre = W_Run q'" by blast
      with C_pre_non_run show False by blast
    qed
    from wrap_path_det_non_run[OF Y_path canon_pow Y_non_run disp_non_run]
    have Y_eq: "Y = mid_plant_disp_config M pack c w" .
    have Y_state: "mt_state Y = W_Disp" using Y_eq disp_state by simp
    have T_gt: "0 < T_pre - N" using N_lt by simp
    from wrap_W_Disp_then_W_Run[OF Y_to_pre Y_state T_gt]
    obtain q' where "mt_state C_pre = W_Run q'" by blast
    with C_pre_non_run show False by blast
  qed

  from T_pre_ge T_pre_le have T_eq_N: "T_pre = N" by simp

  from pre_pow T_eq_N have pre_pow_N: "(?init, C_pre) \<in> ?R ^^ N" by simp
  from wrap_path_det_non_run[OF pre_pow_N canon_pow C_pre_non_run disp_non_run]
  have C_pre_eq: "C_pre = mid_plant_disp_config M pack c w" .

  have actual_disp_step:
    "(mid_plant_disp_config M pack c w, C_post) \<in> ?R"
    using pre_step C_pre_eq by simp
  have C_post_eq:
    "C_post = post_plant_dispatch_config M pack c w"
    by (rule wrap_step_unique_non_run
          [OF actual_disp_step canon_disp_step disp_non_run])

  from post_chain C_post_eq have suffix:
    "(post_plant_dispatch_config M pack c w, C_acc) \<in> ?R\<^sup>*"
    by simp

  from suffix pack_in_Sigma show ?thesis by blast
qed
end
