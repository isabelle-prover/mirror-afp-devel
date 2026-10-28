theory Wrap_Encoder
  imports Wrap_Run
begin

section \<open>The wrap: the encoder phase\<close>

text \<open>The encoder phase of @{const encoding_wrap} threads the six encoder
  families through the boundary-parameterised configurations
  (@{const post_encoder_config_gen}, @{const mid_encoder_config_gen},
  @{const mid_buf_extending_config_gen}), reaching @{const post_encoder_config_gen}
  in state @{text W_Reset}.  The encoder stops \<^emph>\<open>before\<close> the reset's first
  step.  These step-membership lemmas compose with
  @{thm[source] plant_reset_dispatch_rtrancl} at @{const post_encoder_config_gen}.\<close>

subsection \<open>The initial encoder step\<close>

text \<open>One wrap-step from the initial configuration reaches
  @{term "mid_encoder_config_gen (k_ktm M) M pack c w 0"}, via the unique
  @{const wrap_init_delta_gen} transition.\<close>

lemma init_to_mid_zero:
  assumes "valid_ktm M"
      and "0 < c"
  shows "(init_config_ktm (encoding_wrap M pack c \<Sigma>u) (map Raw w),
          mid_encoder_config_gen (k_ktm M) M pack c w 0)
         \<in> ktm_step (wrap_delta M pack c \<Sigma>u)"
proof -
  let ?init = "init_config_ktm (encoding_wrap M pack c \<Sigma>u) (map Raw w)"

  have init_state: "ktc_state ?init = W_Init"
    by simp
  have init_pos: "ktc_pos ?init = (\<lambda>_. 0)"
    by simp
  have init_tape:
    "ktc_tape ?init
       = (\<lambda>k n. if k < k_ktm M
                then (if n = 0 then Enc (le_ktm M)
                      else if k = 0 \<and> n \<le> length (map Raw w)
                           then (map Raw w) ! (n - 1)
                           else Enc (bl_ktm M))
                else Enc (bl_ktm M))"
    by (simp add: fun_eq_iff)

  have init_eq: "?init = KConfig W_Init (ktc_tape ?init) (ktc_pos ?init)"
    using init_state init_pos init_tape
    by (cases ?init) simp

  have read_at_init:
    "(\<lambda>k. ktc_tape ?init k (ktc_pos ?init k))
       = (\<lambda>t. if t < k_ktm M then Enc (le_ktm M) else Enc (bl_ktm M))"
    by (simp add: init_pos init_tape fun_eq_iff)

  have tuple_in:
    "(W_Init, \<lambda>k. ktc_tape ?init k (ktc_pos ?init k), W_Buf [],
      \<lambda>t. if t < k_ktm M then Enc (le_ktm M) else Enc (bl_ktm M),
      \<lambda>t. case t of 0 \<Rightarrow> MoveR | Suc k \<Rightarrow> if k = 0 then MoveR else MoveN)
     \<in> wrap_delta M pack c \<Sigma>u"
    using read_at_init
    by (simp add: wrap_delta_def wrap_init_delta_gen_def)

  have step_holds:
    "(KConfig W_Init (ktc_tape ?init) (ktc_pos ?init),
      KConfig (W_Buf [])
        (\<lambda>k. (ktc_tape ?init k)((ktc_pos ?init k) :=
                (if k < k_ktm M then Enc (le_ktm M) else Enc (bl_ktm M))))
        (\<lambda>k. go_move
              ((\<lambda>t. case t of 0 \<Rightarrow> MoveR
                            | Suc k' \<Rightarrow> if k' = 0 then MoveR else MoveN) k)
              (ktc_pos ?init k)))
     \<in> ktm_step (wrap_delta M pack c \<Sigma>u)"
    by (rule ktm_step.step
          [where ts = "ktc_tape ?init" and n = "ktc_pos ?init"
                 and a = "\<lambda>t. if t < k_ktm M then Enc (le_ktm M) else Enc (bl_ktm M)"
                 and move = "\<lambda>t. case t of 0 \<Rightarrow> MoveR
                                       | Suc k' \<Rightarrow> if k' = 0 then MoveR else MoveN",
           OF tuple_in])

  have target_eq:
    "KConfig (W_Buf [])
       (\<lambda>k. (ktc_tape ?init k)((ktc_pos ?init k) :=
               (if k < k_ktm M then Enc (le_ktm M) else Enc (bl_ktm M))))
       (\<lambda>k. go_move
             ((\<lambda>t. case t of 0 \<Rightarrow> MoveR
                           | Suc k' \<Rightarrow> if k' = 0 then MoveR else MoveN) k)
             (ktc_pos ?init k))
     = mid_encoder_config_gen (k_ktm M) M pack c w 0"
    unfolding mid_encoder_config_gen_def
    by (auto simp: init_pos init_tape fun_eq_iff
             split: nat.split if_splits)

  from step_holds target_eq init_eq
  show ?thesis by simp
qed


subsection \<open>One step extending a block\<close>

text \<open>A single @{const wrap_buf_extend_delta_gen} step within cycle @{term i},
  advancing the buffer fill level from @{term j} to @{term "Suc j"}.  The
  buffer-extend step
  only grows the buffer and advances @{text W_User} (physical tape @{text 0}),
  touching no other tape, so it is boundary-insensitive.\<close>

lemma mid_buf_extend_step:
  assumes "valid_ktm M"
      and "0 < c"
      and "set w \<subseteq> \<Sigma>u"
      and "Suc j < c"
      and "i * c + j < length w"
  shows "(mid_buf_extending_config_gen (k_ktm M) M pack c w i j,
          mid_buf_extending_config_gen (k_ktm M) M pack c w i (Suc j))
         \<in> ktm_step (wrap_delta M pack c \<Sigma>u)"
proof -
  let ?src = "mid_buf_extending_config_gen (k_ktm M) M pack c w i j"
  let ?ws = "take j (drop (i * c) w)"
  let ?a = "w ! (i * c + j)"

  \<comment> \<open>List-arithmetic facts about the buffer prefix.\<close>
  have j_lt_drop: "j < length (drop (i * c) w)"
    using \<open>i * c + j < length w\<close> by simp
  have len_ws: "length ?ws = j"
    using j_lt_drop by simp
  have set_ws: "set ?ws \<subseteq> \<Sigma>u"
    using \<open>set w \<subseteq> \<Sigma>u\<close>
    by (meson dual_order.trans set_drop_subset set_take_subset)
  have take_app: "?ws @ [?a] = take (Suc j) (drop (i * c) w)"
    using j_lt_drop by (simp add: take_Suc_conv_app_nth)
  have a_in_Sigmau: "?a \<in> \<Sigma>u"
    using \<open>set w \<subseteq> \<Sigma>u\<close> \<open>i * c + j < length w\<close>
    by (meson nth_mem subsetD)

  \<comment> \<open>Substrate facts about M's distinguished symbols.\<close>
  have bl_in: "bl_ktm M \<in> \<Gamma>_ktm M"
    by (rule valid_ktm_blank_in_Gamma[OF \<open>valid_ktm M\<close>])
  have le_in: "le_ktm M \<in> \<Gamma>_ktm M"
    by (rule valid_ktm_LE_in_Gamma[OF \<open>valid_ktm M\<close>])

  \<comment> \<open>Selector facts for the source config.\<close>
  have src_state: "ktc_state ?src = W_Buf ?ws"
    by (simp add: mid_buf_extending_config_gen_def)
  have src_pos:
    "ktc_pos ?src
       = (\<lambda>t. case t of 0 \<Rightarrow> 1 + i * c + j
                       | Suc k \<Rightarrow> (if k = 0 then 1 + i else 0))"
    by (simp add: mid_buf_extending_config_gen_def fun_eq_iff)
  have src_tape:
    "ktc_tape ?src
       = (\<lambda>t n. if t < k_ktm M
                then (case t of
                  0 \<Rightarrow> (if n = 0 then Enc (le_ktm M)
                            else if n \<le> length w then Raw (w ! (n - 1))
                            else Enc (bl_ktm M))
                | Suc k \<Rightarrow> (if n = 0 then Enc (le_ktm M)
                            else if k = 0 \<and> n \<le> i
                              then Enc (wrap_enc pack c w ! (n - 1))
                            else Enc (bl_ktm M)))
                else Enc (bl_ktm M))"
    by (simp add: mid_buf_extending_config_gen_def fun_eq_iff)

  have src_eq: "?src = KConfig (W_Buf ?ws) (ktc_tape ?src) (ktc_pos ?src)"
    using src_state src_pos src_tape
    by (cases ?src) simp

  \<comment> \<open>The load-bearing read: @{text W_User} sees @{text "Raw ?a"}.\<close>
  have read_W_User:
    "ktc_tape ?src 0 (ktc_pos ?src 0) = Raw ?a"
    using \<open>i * c + j < length w\<close> valid_ktm_k_pos[OF \<open>valid_ktm M\<close>]
    by (simp add: src_tape src_pos)

  \<comment> \<open>Range typing of the read function.\<close>
  have rd_range:
    "(\<lambda>k. ktc_tape (mid_buf_extending_config_gen (k_ktm M) M pack c w i j) k
           (ktc_pos (mid_buf_extending_config_gen (k_ktm M) M pack c w i j) k))
       \<in> UNIV \<rightarrow> Raw ` \<Sigma>u \<union> Enc ` \<Gamma>_ktm M"
    using a_in_Sigmau bl_in le_in \<open>i * c + j < length w\<close>
    by (auto simp: mid_buf_extending_config_gen_def split: nat.split)

  \<comment> \<open>The \<open>wrap_buf_extend_delta_gen\<close> tuple.\<close>
  have tuple_in:
    "(W_Buf ?ws,
      \<lambda>k. ktc_tape ?src k (ktc_pos ?src k),
      W_Buf (?ws @ [?a]),
      \<lambda>k. ktc_tape ?src k (ktc_pos ?src k),
      \<lambda>t. case t of 0 \<Rightarrow> MoveR | _ \<Rightarrow> MoveN)
     \<in> wrap_delta M pack c \<Sigma>u"
  proof -
    have "(W_Buf ?ws,
           \<lambda>k. ktc_tape ?src k (ktc_pos ?src k),
           W_Buf (?ws @ [?a]),
           \<lambda>k. ktc_tape ?src k (ktc_pos ?src k),
           \<lambda>t. case t of 0 \<Rightarrow> MoveR | _ \<Rightarrow> MoveN)
          \<in> wrap_buf_extend_delta_gen (k_ktm M) M c \<Sigma>u"
      unfolding wrap_buf_extend_delta_gen_def
      using len_ws \<open>Suc j < c\<close> a_in_Sigmau set_ws read_W_User rd_range
      by (auto simp: src_tape)
    thus ?thesis
      by (simp add: wrap_delta_def)
  qed

  \<comment> \<open>Apply \<open>ktm_step.step\<close>.\<close>
  have step_holds:
    "(KConfig (W_Buf ?ws) (ktc_tape ?src) (ktc_pos ?src),
      KConfig (W_Buf (?ws @ [?a]))
        (\<lambda>k. (ktc_tape ?src k)((ktc_pos ?src k) :=
                              ktc_tape ?src k (ktc_pos ?src k)))
        (\<lambda>k. go_move
              ((\<lambda>t. case t of 0 \<Rightarrow> MoveR | _ \<Rightarrow> MoveN) k)
              (ktc_pos ?src k)))
     \<in> ktm_step (wrap_delta M pack c \<Sigma>u)"
    by (rule ktm_step.step
          [where ts = "ktc_tape ?src" and n = "ktc_pos ?src"
                 and a = "\<lambda>k. ktc_tape ?src k (ktc_pos ?src k)"
                 and move = "\<lambda>t. case t of 0 \<Rightarrow> MoveR | _ \<Rightarrow> MoveN",
           OF tuple_in])

  \<comment> \<open>Target equality.\<close>
  have target_eq:
    "KConfig (W_Buf (?ws @ [?a]))
       (\<lambda>k. (ktc_tape ?src k)((ktc_pos ?src k) :=
                             ktc_tape ?src k (ktc_pos ?src k)))
       (\<lambda>k. go_move
             ((\<lambda>t. case t of 0 \<Rightarrow> MoveR | _ \<Rightarrow> MoveN) k)
             (ktc_pos ?src k))
     = mid_buf_extending_config_gen (k_ktm M) M pack c w i (Suc j)"
    unfolding mid_buf_extending_config_gen_def
    using take_app
    by (auto simp: src_pos src_tape fun_eq_iff
             split: nat.split)

  from step_holds target_eq src_eq
  show ?thesis by simp
qed


subsection \<open>One step closing a block\<close>

text \<open>A single @{const wrap_buf_close_delta_gen} step closing cycle @{term i}:
  packs the completed block, writes the encoded block to physical tape
  @{text 1}, and advances both heads.  Needs @{term "2 \<le> k_ktm M"}: the encoded
  block is written to physical tape @{text 1}, which must be in range for
  the target configuration to record the write.\<close>

lemma mid_buf_close_step:
  assumes "valid_ktm M"
      and "0 < c"
      and "set w \<subseteq> \<Sigma>u"
      and "(Suc i) * c \<le> length w"
      and "pack (take c (drop (i * c) w)) \<in> Sigma_ktm M"
      and "bl_ktm M \<noteq> le_ktm M"
      and k2: "2 \<le> k_ktm M"
  shows "(mid_buf_extending_config_gen (k_ktm M) M pack c w i (c - 1),
          mid_encoder_config_gen (k_ktm M) M pack c w (Suc i))
         \<in> ktm_step (wrap_delta M pack c \<Sigma>u)"
proof -
  \<comment> \<open>Local opaque abbreviation \<open>cm = c - 1\<close>.\<close>
  define cm where "cm = c - 1"
  let ?src = "mid_buf_extending_config_gen (k_ktm M) M pack c w i cm"
  let ?ws = "take cm (drop (i * c) w)"
  let ?a = "w ! (i * c + cm)"
  let ?packed = "pack (take c (drop (i * c) w))"

  \<comment> \<open>Arithmetic facts about \<open>c\<close>.\<close>
  from \<open>0 < c\<close> have c_succ: "Suc cm = c" unfolding cm_def by simp
  from \<open>(Suc i) * c \<le> length w\<close> have full_block:
    "i * c + c \<le> length w" by simp
  with \<open>0 < c\<close> have a_idx: "i * c + cm < length w"
    unfolding cm_def by linarith
  from c_succ have a_idx_succ: "i * c + cm + 1 = i * c + c"
    by simp

  \<comment> \<open>List-arithmetic facts about the completed block.\<close>
  have c1_lt_drop: "cm < length (drop (i * c) w)"
    using a_idx by simp
  have len_ws: "length ?ws = cm"
    using c1_lt_drop by simp
  have len_ws_plus_one: "length ?ws + 1 = c"
    using len_ws c_succ by simp
  have set_ws: "set ?ws \<subseteq> \<Sigma>u"
    using \<open>set w \<subseteq> \<Sigma>u\<close>
    by (meson dual_order.trans set_drop_subset set_take_subset)
  have take_app: "?ws @ [?a] = take c (drop (i * c) w)"
  proof -
    have "take c (drop (i * c) w) = take (Suc cm) (drop (i * c) w)"
      using c_succ by simp
    also have "\<dots> = take cm (drop (i * c) w) @ [drop (i * c) w ! cm]"
      using c1_lt_drop by (simp add: take_Suc_conv_app_nth)
    also have "drop (i * c) w ! cm = w ! (i * c + cm)"
      using a_idx by simp
    finally show ?thesis by simp
  qed
  have a_in_Sigmau: "?a \<in> \<Sigma>u"
    using \<open>set w \<subseteq> \<Sigma>u\<close> a_idx
    by (meson nth_mem subsetD)
  have pack_app_eq: "pack (?ws @ [?a]) = ?packed"
    using take_app by simp

  \<comment> \<open>Substrate facts about M's distinguished symbols.\<close>
  have bl_in: "bl_ktm M \<in> \<Gamma>_ktm M"
    by (rule valid_ktm_blank_in_Gamma[OF \<open>valid_ktm M\<close>])
  have le_in: "le_ktm M \<in> \<Gamma>_ktm M"
    by (rule valid_ktm_LE_in_Gamma[OF \<open>valid_ktm M\<close>])

  \<comment> \<open>Pack-value / @{const wrap_enc}-entry identity.\<close>
  have wenc_eq: "?packed = wrap_enc pack c w ! i"
    by (rule wrap_enc_nth[OF \<open>0 < c\<close> \<open>(Suc i) * c \<le> length w\<close>, symmetric])

  \<comment> \<open>Selector facts for the source config.\<close>
  have src_state: "ktc_state ?src = W_Buf ?ws"
    by (simp add: mid_buf_extending_config_gen_def)
  have src_pos:
    "ktc_pos ?src
       = (\<lambda>t. case t of 0 \<Rightarrow> 1 + i * c + cm
                       | Suc k \<Rightarrow> (if k = 0 then 1 + i else 0))"
    by (simp add: mid_buf_extending_config_gen_def fun_eq_iff)
  have src_tape:
    "ktc_tape ?src
       = (\<lambda>t n. if t < k_ktm M
                then (case t of
                  0 \<Rightarrow> (if n = 0 then Enc (le_ktm M)
                            else if n \<le> length w then Raw (w ! (n - 1))
                            else Enc (bl_ktm M))
                | Suc k \<Rightarrow> (if n = 0 then Enc (le_ktm M)
                            else if k = 0 \<and> n \<le> i
                              then Enc (wrap_enc pack c w ! (n - 1))
                            else Enc (bl_ktm M)))
                else Enc (bl_ktm M))"
    by (simp add: mid_buf_extending_config_gen_def fun_eq_iff)

  have src_eq: "?src = KConfig (W_Buf ?ws) (ktc_tape ?src) (ktc_pos ?src)"
    using src_state src_pos src_tape
    by (cases ?src) simp

  \<comment> \<open>Per-tape reads.  @{text W_M} \<open>0\<close> (physical tape @{text 1}) reads blank in
    both boundary branches (head at \<open>1 + i\<close>, beyond the \<open>1..i\<close> encoded
    prefix), so this read is boundary-insensitive.\<close>
  have read_W_User:
    "ktc_tape ?src 0 (ktc_pos ?src 0) = Raw ?a"
    using a_idx valid_ktm_k_pos[OF \<open>valid_ktm M\<close>]
    by (simp add: src_tape src_pos)
  have read_W_M_0:
    "ktc_tape ?src (Suc 0) (ktc_pos ?src (Suc 0)) = Enc (bl_ktm M)"
    by (simp add: src_tape src_pos)

  \<comment> \<open>Range typing of the read function.\<close>
  have rd_range:
    "(\<lambda>k. ktc_tape (mid_buf_extending_config_gen (k_ktm M) M pack c w i cm) k
           (ktc_pos (mid_buf_extending_config_gen (k_ktm M) M pack c w i cm) k))
       \<in> UNIV \<rightarrow> Raw ` \<Sigma>u \<union> Enc ` \<Gamma>_ktm M"
    using a_in_Sigmau bl_in le_in a_idx
    by (auto simp: mid_buf_extending_config_gen_def split: nat.split)

  \<comment> \<open>Static guard \<open>sym (Suc 0) \<noteq> Enc (le_ktm M)\<close>.\<close>
  have sym_W_M_0_ne_LE:
    "ktc_tape ?src (Suc 0) (ktc_pos ?src (Suc 0)) \<noteq> Enc (le_ktm M)"
    using read_W_M_0 \<open>bl_ktm M \<noteq> le_ktm M\<close> by simp

  \<comment> \<open>Padded-tail blank fact for the boundary \<open>\<forall>j \<ge> k_ktm M\<close>.\<close>
  have tail_bl:
    "\<forall>j\<ge>k_ktm M. ktc_tape ?src j (ktc_pos ?src j) = Enc (bl_ktm M)"
    by (simp add: src_tape)

  \<comment> \<open>The \<open>wrap_buf_close_delta_gen\<close> tuple.\<close>
  have tuple_in:
    "(W_Buf ?ws,
      \<lambda>k. ktc_tape ?src k (ktc_pos ?src k),
      W_Buf [],
      (\<lambda>t. case t of
             Suc k \<Rightarrow> if k = 0 then Enc (pack (?ws @ [?a]))
                       else ktc_tape ?src (Suc k) (ktc_pos ?src (Suc k))
           | 0 \<Rightarrow> ktc_tape ?src 0 (ktc_pos ?src 0)),
      \<lambda>t. case t of 0 \<Rightarrow> MoveR
                  | Suc k \<Rightarrow> if k = 0 then MoveR else MoveN)
     \<in> wrap_delta M pack c \<Sigma>u"
  proof -
    have "(W_Buf ?ws,
           \<lambda>k. ktc_tape ?src k (ktc_pos ?src k),
           W_Buf [],
           (\<lambda>t. case t of
                  Suc k \<Rightarrow> if k = 0 then Enc (pack (?ws @ [?a]))
                            else ktc_tape ?src (Suc k) (ktc_pos ?src (Suc k))
                | 0 \<Rightarrow> ktc_tape ?src 0 (ktc_pos ?src 0)),
           \<lambda>t. case t of 0 \<Rightarrow> MoveR
                       | Suc k \<Rightarrow> if k = 0 then MoveR else MoveN)
          \<in> wrap_buf_close_delta_gen (k_ktm M) M pack c \<Sigma>u"
      unfolding wrap_buf_close_delta_gen_def
      using len_ws_plus_one a_in_Sigmau set_ws read_W_User sym_W_M_0_ne_LE
            \<open>pack (take c (drop (i * c) w)) \<in> Sigma_ktm M\<close>
            pack_app_eq rd_range tail_bl
      by auto
    thus ?thesis
      by (simp add: wrap_delta_def)
  qed

  \<comment> \<open>Apply \<open>ktm_step.step\<close>.\<close>
  have step_holds:
    "(KConfig (W_Buf ?ws) (ktc_tape ?src) (ktc_pos ?src),
      KConfig (W_Buf [])
        (\<lambda>k. (ktc_tape ?src k)
              ((ktc_pos ?src k) :=
                 (case k of
                    Suc k' \<Rightarrow> if k' = 0 then Enc (pack (?ws @ [?a]))
                              else ktc_tape ?src (Suc k') (ktc_pos ?src (Suc k'))
                  | 0 \<Rightarrow> ktc_tape ?src 0 (ktc_pos ?src 0))))
        (\<lambda>k. go_move
              ((\<lambda>t. case t of 0 \<Rightarrow> MoveR
                            | Suc k' \<Rightarrow> if k' = 0 then MoveR else MoveN) k)
              (ktc_pos ?src k)))
     \<in> ktm_step (wrap_delta M pack c \<Sigma>u)"
    by (rule ktm_step.step
          [where ts = "ktc_tape ?src" and n = "ktc_pos ?src"
                 and a = "\<lambda>t. case t of
                                Suc k \<Rightarrow> if k = 0 then Enc (pack (?ws @ [?a]))
                                          else ktc_tape ?src (Suc k) (ktc_pos ?src (Suc k))
                              | 0 \<Rightarrow> ktc_tape ?src 0 (ktc_pos ?src 0)"
                 and move = "\<lambda>t. case t of 0 \<Rightarrow> MoveR
                                       | Suc k' \<Rightarrow> if k' = 0 then MoveR else MoveN",
           OF tuple_in])

  \<comment> \<open>Target equality.  The block write to physical tape @{text 1} lands in
    range (needs @{term "2 \<le> k_ktm M"}); the written \<open>Enc (pack (?ws @ [?a]))\<close>
    matches the target's \<open>Enc (wrap_enc pack c w ! i)\<close> via @{thm wenc_eq}.\<close>
  have target_eq:
    "KConfig (W_Buf [])
       (\<lambda>k. (ktc_tape ?src k)
             ((ktc_pos ?src k) :=
                (case k of
                   Suc k' \<Rightarrow> if k' = 0 then Enc (pack (?ws @ [?a]))
                             else ktc_tape ?src (Suc k') (ktc_pos ?src (Suc k'))
                 | 0 \<Rightarrow> ktc_tape ?src 0 (ktc_pos ?src 0))))
       (\<lambda>k. go_move
             ((\<lambda>t. case t of 0 \<Rightarrow> MoveR
                           | Suc k' \<Rightarrow> if k' = 0 then MoveR else MoveN) k)
             (ktc_pos ?src k))
     = mid_encoder_config_gen (k_ktm M) M pack c w (Suc i)"
    unfolding mid_encoder_config_gen_def
    using a_idx pack_app_eq wenc_eq c_succ a_idx_succ
          valid_ktm_k_pos[OF \<open>valid_ktm M\<close>] k2
    by (auto simp: src_pos src_tape fun_eq_iff
             split: nat.split if_splits)

  from step_holds target_eq src_eq
  show ?thesis unfolding cm_def by simp
qed


subsection \<open>One block\<close>

text \<open>One cycle composes @{text "c - 1"} @{thm[source] mid_buf_extend_step}s
  with one @{thm[source] mid_buf_close_step}; carries @{term "2 \<le> k_ktm M"}
  for the closing step.\<close>

lemma mid_encoder_step:
  assumes vM: "valid_ktm M"
      and c_pos: "0 < c"
      and w_alpha: "set w \<subseteq> \<Sigma>u"
      and block_fits: "(Suc i) * c \<le> length w"
      and pack_in_Sigma: "pack (take c (drop (i * c) w)) \<in> Sigma_ktm M"
      and bl_ne_le: "bl_ktm M \<noteq> le_ktm M"
      and k2: "2 \<le> k_ktm M"
  shows "(mid_encoder_config_gen (k_ktm M) M pack c w i,
          mid_encoder_config_gen (k_ktm M) M pack c w (Suc i))
         \<in> (ktm_step (wrap_delta M pack c \<Sigma>u))\<^sup>*"
proof -
  let ?R = "ktm_step (wrap_delta M pack c \<Sigma>u)"

  have base_eq:
    "mid_buf_extending_config_gen (k_ktm M) M pack c w i 0
       = mid_encoder_config_gen (k_ktm M) M pack c w i"
    by (simp add: mid_encoder_config_gen_def mid_buf_extending_config_gen_def
              fun_eq_iff split: nat.split)

  have block_pos: "\<And>j. j < c \<Longrightarrow> i * c + j < length w"
    using block_fits by simp

  have iter:
    "j \<le> c - 1 \<Longrightarrow>
     (mid_buf_extending_config_gen (k_ktm M) M pack c w i 0,
      mid_buf_extending_config_gen (k_ktm M) M pack c w i j) \<in> ?R\<^sup>*"
    for j
  proof (induction j)
    case 0
    show ?case by simp
  next
    case (Suc j)
    from Suc.prems c_pos have j_le: "j \<le> c - 1" by linarith
    note ih = Suc.IH[OF j_le]
    from Suc.prems c_pos have Suc_j_lt: "Suc j < c" by linarith
    from Suc.prems c_pos have j_lt: "j < c" by linarith
    have block_in: "i * c + j < length w"
      using block_pos[OF j_lt] .
    have step:
      "(mid_buf_extending_config_gen (k_ktm M) M pack c w i j,
        mid_buf_extending_config_gen (k_ktm M) M pack c w i (Suc j)) \<in> ?R"
      by (rule mid_buf_extend_step
            [OF vM c_pos w_alpha Suc_j_lt block_in])
    show ?case using ih step by (rule rtrancl_into_rtrancl)
  qed

  have extends_done:
    "(mid_buf_extending_config_gen (k_ktm M) M pack c w i 0,
      mid_buf_extending_config_gen (k_ktm M) M pack c w i (c - 1)) \<in> ?R\<^sup>*"
    using iter[of "c - 1"] by simp

  have close_step:
    "(mid_buf_extending_config_gen (k_ktm M) M pack c w i (c - 1),
      mid_encoder_config_gen (k_ktm M) M pack c w (Suc i)) \<in> ?R"
    by (rule mid_buf_close_step
          [where pack = pack,
           OF vM c_pos w_alpha block_fits pack_in_Sigma bl_ne_le k2])

  from extends_done close_step
  have "(mid_buf_extending_config_gen (k_ktm M) M pack c w i 0,
         mid_encoder_config_gen (k_ktm M) M pack c w (Suc i)) \<in> ?R\<^sup>*"
    by (rule rtrancl_into_rtrancl)
  with base_eq show ?thesis by simp
qed

text \<open>L1+L2: relpow variant — one cycle is exactly @{term c} wrap-steps.\<close>

lemma mid_encoder_step_relpow:
  assumes vM: "valid_ktm M"
      and c_pos: "0 < c"
      and w_alpha: "set w \<subseteq> \<Sigma>u"
      and block_fits: "(Suc i) * c \<le> length w"
      and pack_in_Sigma: "pack (take c (drop (i * c) w)) \<in> Sigma_ktm M"
      and bl_ne_le: "bl_ktm M \<noteq> le_ktm M"
      and k2: "2 \<le> k_ktm M"
  shows "(mid_encoder_config_gen (k_ktm M) M pack c w i,
          mid_encoder_config_gen (k_ktm M) M pack c w (Suc i))
         \<in> (ktm_step (wrap_delta M pack c \<Sigma>u)) ^^ c"
proof -
  let ?R = "ktm_step (wrap_delta M pack c \<Sigma>u)"

  have base_eq:
    "mid_buf_extending_config_gen (k_ktm M) M pack c w i 0
       = mid_encoder_config_gen (k_ktm M) M pack c w i"
    by (simp add: mid_encoder_config_gen_def mid_buf_extending_config_gen_def
              fun_eq_iff split: nat.split)

  have block_pos: "\<And>j. j < c \<Longrightarrow> i * c + j < length w"
    using block_fits by simp

  have iter:
    "j \<le> c - 1 \<Longrightarrow>
     (mid_buf_extending_config_gen (k_ktm M) M pack c w i 0,
      mid_buf_extending_config_gen (k_ktm M) M pack c w i j) \<in> ?R ^^ j"
    for j
  proof (induction j)
    case 0
    show ?case by simp
  next
    case (Suc j)
    from Suc.prems c_pos have j_le: "j \<le> c - 1" by linarith
    note ih = Suc.IH[OF j_le]
    from Suc.prems c_pos have Suc_j_lt: "Suc j < c" by linarith
    from Suc.prems c_pos have j_lt: "j < c" by linarith
    have block_in: "i * c + j < length w"
      using block_pos[OF j_lt] .
    have step:
      "(mid_buf_extending_config_gen (k_ktm M) M pack c w i j,
        mid_buf_extending_config_gen (k_ktm M) M pack c w i (Suc j)) \<in> ?R"
      by (rule mid_buf_extend_step
            [OF vM c_pos w_alpha Suc_j_lt block_in])
    from ih step show ?case by (rule relpow_Suc_I)
  qed

  have extends_done:
    "(mid_buf_extending_config_gen (k_ktm M) M pack c w i 0,
      mid_buf_extending_config_gen (k_ktm M) M pack c w i (c - 1)) \<in> ?R ^^ (c - 1)"
    using iter[of "c - 1"] by simp

  have close_step:
    "(mid_buf_extending_config_gen (k_ktm M) M pack c w i (c - 1),
      mid_encoder_config_gen (k_ktm M) M pack c w (Suc i)) \<in> ?R"
    by (rule mid_buf_close_step
          [where pack = pack,
           OF vM c_pos w_alpha block_fits pack_in_Sigma bl_ne_le k2])

  from extends_done close_step
  have combined:
    "(mid_buf_extending_config_gen (k_ktm M) M pack c w i 0,
      mid_encoder_config_gen (k_ktm M) M pack c w (Suc i)) \<in> ?R ^^ Suc (c - 1)"
    by (rule relpow_Suc_I)

  have c_eq: "Suc (c - 1) = c" using c_pos by simp

  from combined base_eq c_eq show ?thesis by simp
qed

text \<open>L3: encoder iter to @{term "mid_encoder_config_gen (k_ktm M) M pack c w i"}
  for any @{term "i \<le> length w div c"} takes exactly @{term "c * i"} wrap-steps.\<close>

lemma mid_encoder_iter_relpow:
  assumes vM: "valid_ktm M"
      and c_pos: "0 < c"
      and w_alpha: "set w \<subseteq> \<Sigma>u"
      and bl_ne_le: "bl_ktm M \<noteq> le_ktm M"
      and k2: "2 \<le> k_ktm M"
      and pack_contract_in_Sigma:
        "\<And>i. i * c < length w \<Longrightarrow>
              pack (take c (drop (i * c) w)) \<in> Sigma_ktm M"
      and i_le: "i \<le> length w div c"
    shows "(mid_encoder_config_gen (k_ktm M) M pack c w 0,
            mid_encoder_config_gen (k_ktm M) M pack c w i)
           \<in> (ktm_step (wrap_delta M pack c \<Sigma>u)) ^^ (c * i)"
proof -
  let ?R = "ktm_step (wrap_delta M pack c \<Sigma>u)"
  let ?q = "length w div c"
  let ?r = "length w mod c"

  have div_mod_eq: "?q * c + ?r = length w"
    by (rule div_mult_mod_eq)

  show ?thesis using i_le
  proof (induction i)
    case 0
    show ?case by simp
  next
    case (Suc i)
    from Suc.prems have i_le_q: "i \<le> ?q" by simp
    from Suc.prems have Suc_i_le_q: "Suc i \<le> ?q" by simp
    note ih = Suc.IH[OF i_le_q]

    have suc_ic_le_qc: "(Suc i) * c \<le> ?q * c"
      by (rule mult_le_mono1[OF Suc_i_le_q])
    have block_fits: "(Suc i) * c \<le> length w"
      using suc_ic_le_qc div_mod_eq by linarith
    have i_lt_q: "i < ?q" using Suc_i_le_q by simp
    have ic_lt_qc: "i * c < ?q * c"
      using i_lt_q c_pos by simp
    have ic_lt: "i * c < length w"
      using ic_lt_qc div_mod_eq by linarith

    have pack_in_Sigma: "pack (take c (drop (i * c) w)) \<in> Sigma_ktm M"
      by (rule pack_contract_in_Sigma[OF ic_lt])

    have step:
      "(mid_encoder_config_gen (k_ktm M) M pack c w i,
        mid_encoder_config_gen (k_ktm M) M pack c w (Suc i)) \<in> ?R ^^ c"
      by (rule mid_encoder_step_relpow
            [where pack = pack,
             OF vM c_pos w_alpha block_fits pack_in_Sigma bl_ne_le k2])

    from ih step
    have "(mid_encoder_config_gen (k_ktm M) M pack c w 0,
           mid_encoder_config_gen (k_ktm M) M pack c w (Suc i)) \<in> ?R ^^ (c * i + c)"
      by (auto simp: relpow_add)
    moreover have "c * i + c = c * Suc i" by simp
    ultimately show ?case by simp
  qed
qed


subsection \<open>The end of the input after a full block\<close>

text \<open>When @{term "length w mod c = 0"}, a single @{const wrap_buf_empty_end_delta_gen}
  step takes the post-final-cycle waypoint to @{const post_encoder_config_gen};
  boundary-insensitive (the empty-end step writes nothing).\<close>

lemma mid_to_post_empty:
  assumes vM: "valid_ktm M"
      and c_pos: "0 < c"
      and r_zero: "length w mod c = 0"
  shows "(mid_encoder_config_gen (k_ktm M) M pack c w (length w div c),
          post_encoder_config_gen (k_ktm M) M pack c w)
         \<in> ktm_step (wrap_delta M pack c \<Sigma>u)"
proof -
  let ?q = "length w div c"
  let ?src = "mid_encoder_config_gen (k_ktm M) M pack c w ?q"

  have qc_eq: "?q * c = length w"
    using div_mult_mod_eq[of "length w" c] r_zero by simp
  have len_wenc: "length (wrap_enc pack c w) = ?q"
    using length_wrap_enc[OF c_pos, of pack w] r_zero by simp

  have bl_in: "bl_ktm M \<in> \<Gamma>_ktm M"
    by (rule valid_ktm_blank_in_Gamma[OF vM])
  have le_in: "le_ktm M \<in> \<Gamma>_ktm M"
    by (rule valid_ktm_LE_in_Gamma[OF vM])

  have src_state: "ktc_state ?src = W_Buf []"
    by (simp add: mid_encoder_config_gen_def)
  have src_pos:
    "ktc_pos ?src
       = (\<lambda>t. case t of 0 \<Rightarrow> 1 + ?q * c
                       | Suc k \<Rightarrow> (if k = 0 then 1 + ?q else 0))"
    by (simp add: mid_encoder_config_gen_def fun_eq_iff)
  have src_tape:
    "ktc_tape ?src
       = (\<lambda>t n. if t < k_ktm M
                then (case t of
                  0 \<Rightarrow> (if n = 0 then Enc (le_ktm M)
                            else if n \<le> length w then Raw (w ! (n - 1))
                            else Enc (bl_ktm M))
                | Suc k \<Rightarrow> (if n = 0 then Enc (le_ktm M)
                            else if k = 0 \<and> n \<le> ?q
                              then Enc (wrap_enc pack c w ! (n - 1))
                            else Enc (bl_ktm M)))
                else Enc (bl_ktm M))"
    by (simp add: mid_encoder_config_gen_def fun_eq_iff)

  have src_eq: "?src = KConfig (W_Buf []) (ktc_tape ?src) (ktc_pos ?src)"
    using src_state src_pos src_tape
    by (cases ?src) simp

  have read_W_User:
    "ktc_tape ?src 0 (ktc_pos ?src 0) = Enc (bl_ktm M)"
    by (simp add: src_tape src_pos qc_eq)

  have rd_range:
    "(\<lambda>k. ktc_tape (mid_encoder_config_gen (k_ktm M) M pack c w ?q) k
           (ktc_pos (mid_encoder_config_gen (k_ktm M) M pack c w ?q) k))
       \<in> UNIV \<rightarrow> Raw ` \<Sigma>u \<union> Enc ` \<Gamma>_ktm M"
    using bl_in le_in qc_eq
    by (auto simp: mid_encoder_config_gen_def split: nat.split)

  have tuple_in:
    "(W_Buf [],
      \<lambda>k. ktc_tape ?src k (ktc_pos ?src k),
      W_Reset,
      \<lambda>k. ktc_tape ?src k (ktc_pos ?src k),
      \<lambda>_. MoveN)
     \<in> wrap_delta M pack c \<Sigma>u"
  proof -
    have "(W_Buf [],
           \<lambda>k. ktc_tape ?src k (ktc_pos ?src k),
           W_Reset,
           \<lambda>k. ktc_tape ?src k (ktc_pos ?src k),
           \<lambda>_. MoveN)
          \<in> wrap_buf_empty_end_delta_gen (k_ktm M) M \<Sigma>u"
      unfolding wrap_buf_empty_end_delta_gen_def
      using read_W_User rd_range
      by (auto simp: src_tape)
    thus ?thesis by (simp add: wrap_delta_def)
  qed

  have step_holds:
    "(KConfig (W_Buf []) (ktc_tape ?src) (ktc_pos ?src),
      KConfig W_Reset
        (\<lambda>k. (ktc_tape ?src k)((ktc_pos ?src k) :=
                              ktc_tape ?src k (ktc_pos ?src k)))
        (\<lambda>k. go_move MoveN (ktc_pos ?src k)))
     \<in> ktm_step (wrap_delta M pack c \<Sigma>u)"
    by (rule ktm_step.step
          [where ts = "ktc_tape ?src" and n = "ktc_pos ?src"
                 and a = "\<lambda>k. ktc_tape ?src k (ktc_pos ?src k)"
                 and move = "\<lambda>_. MoveN",
           OF tuple_in])

  have target_eq:
    "KConfig W_Reset
       (\<lambda>k. (ktc_tape ?src k)((ktc_pos ?src k) :=
                             ktc_tape ?src k (ktc_pos ?src k)))
       (\<lambda>k. go_move MoveN (ktc_pos ?src k))
     = post_encoder_config_gen (k_ktm M) M pack c w"
    unfolding post_encoder_config_gen_def
    using qc_eq len_wenc
    by (auto simp: src_pos src_tape fun_eq_iff
             split: nat.split)

  from step_holds target_eq src_eq
  show ?thesis by simp
qed


subsection \<open>The end of the input inside a block\<close>

text \<open>When @{term "length w mod c \<noteq> 0"}, @{term "length w mod c"} extends plus
  one @{const wrap_buf_nonempty_end_delta_gen} close pack the partial block onto
  physical tape @{text 1} and reach @{const post_encoder_config_gen}.  Needs
  @{term "2 \<le> k_ktm M"}
  for the partial-block write to physical tape @{text 1}.\<close>

lemma mid_to_post_partial:
  assumes vM: "valid_ktm M"
      and c_pos: "0 < c"
      and w_alpha: "set w \<subseteq> \<Sigma>u"
      and r_pos: "length w mod c \<noteq> 0"
      and pack_tail_in_Sigma:
        "pack (drop ((length w div c) * c) w) \<in> Sigma_ktm M"
      and bl_ne_le: "bl_ktm M \<noteq> le_ktm M"
      and k2: "2 \<le> k_ktm M"
  shows "(mid_encoder_config_gen (k_ktm M) M pack c w (length w div c),
          post_encoder_config_gen (k_ktm M) M pack c w)
         \<in> (ktm_step (wrap_delta M pack c \<Sigma>u))\<^sup>*"
proof -
  let ?q = "length w div c"
  let ?r = "length w mod c"
  let ?R = "ktm_step (wrap_delta M pack c \<Sigma>u)"
  let ?tail = "drop (?q * c) w"
  let ?src = "mid_buf_extending_config_gen (k_ktm M) M pack c w ?q ?r"

  have div_mod_eq: "?q * c + ?r = length w"
    by (rule div_mult_mod_eq)
  have r_lt: "?r < c" using c_pos by simp
  have tail_len: "length ?tail = ?r"
  proof -
    have "length ?tail = length w - ?q * c" by simp
    also have "\<dots> = ?r" using div_mod_eq by linarith
    finally show ?thesis .
  qed
  have take_tail_eq: "take ?r ?tail = ?tail"
    using tail_len by simp
  have buf_take_eq: "take ?r (drop (?q * c) w) = ?tail"
    using take_tail_eq by simp
  have set_tail: "set ?tail \<subseteq> \<Sigma>u"
    using w_alpha by (meson set_drop_subset subset_trans)

  have len_wenc: "length (wrap_enc pack c w) = ?q + 1"
    using length_wrap_enc[OF c_pos, of pack w] r_pos by simp
  have wenc_q_eq: "wrap_enc pack c w ! ?q = pack ?tail"
    using wrap_enc_nth_partial[OF c_pos r_pos] .

  have bl_in: "bl_ktm M \<in> \<Gamma>_ktm M"
    by (rule valid_ktm_blank_in_Gamma[OF vM])
  have le_in: "le_ktm M \<in> \<Gamma>_ktm M"
    by (rule valid_ktm_LE_in_Gamma[OF vM])

  have base_eq:
    "mid_buf_extending_config_gen (k_ktm M) M pack c w ?q 0
       = mid_encoder_config_gen (k_ktm M) M pack c w ?q"
    by (simp add: mid_encoder_config_gen_def mid_buf_extending_config_gen_def
              fun_eq_iff split: nat.split)

  have iter:
    "j \<le> ?r \<Longrightarrow>
     (mid_buf_extending_config_gen (k_ktm M) M pack c w ?q 0,
      mid_buf_extending_config_gen (k_ktm M) M pack c w ?q j) \<in> ?R\<^sup>*"
    for j
  proof (induction j)
    case 0
    show ?case by simp
  next
    case (Suc j)
    from Suc.prems have j_le: "j \<le> ?r" by simp
    note ih = Suc.IH[OF j_le]
    from Suc.prems r_lt have Suc_j_lt: "Suc j < c" by linarith
    from Suc.prems r_lt have j_lt: "j < ?r" by linarith
    have block_in: "?q * c + j < length w"
      using j_lt div_mod_eq by linarith
    have step:
      "(mid_buf_extending_config_gen (k_ktm M) M pack c w ?q j,
        mid_buf_extending_config_gen (k_ktm M) M pack c w ?q (Suc j)) \<in> ?R"
      by (rule mid_buf_extend_step
            [OF vM c_pos w_alpha Suc_j_lt block_in])
    show ?case using ih step by (rule rtrancl_into_rtrancl)
  qed

  have extends_done:
    "(mid_buf_extending_config_gen (k_ktm M) M pack c w ?q 0,
      mid_buf_extending_config_gen (k_ktm M) M pack c w ?q ?r) \<in> ?R\<^sup>*"
    using iter[of ?r] by simp

  have src_state: "ktc_state ?src = W_Buf ?tail"
    using buf_take_eq by (simp add: mid_buf_extending_config_gen_def)
  have src_pos:
    "ktc_pos ?src
       = (\<lambda>t. case t of 0 \<Rightarrow> 1 + ?q * c + ?r
                       | Suc k \<Rightarrow> (if k = 0 then 1 + ?q else 0))"
    by (simp add: mid_buf_extending_config_gen_def fun_eq_iff)
  have src_tape:
    "ktc_tape ?src
       = (\<lambda>t n. if t < k_ktm M
                then (case t of
                  0 \<Rightarrow> (if n = 0 then Enc (le_ktm M)
                            else if n \<le> length w then Raw (w ! (n - 1))
                            else Enc (bl_ktm M))
                | Suc k \<Rightarrow> (if n = 0 then Enc (le_ktm M)
                            else if k = 0 \<and> n \<le> ?q
                              then Enc (wrap_enc pack c w ! (n - 1))
                            else Enc (bl_ktm M)))
                else Enc (bl_ktm M))"
    by (simp add: mid_buf_extending_config_gen_def fun_eq_iff)

  have src_eq: "?src = KConfig (W_Buf ?tail) (ktc_tape ?src) (ktc_pos ?src)"
    using src_state src_pos src_tape
    by (cases ?src) simp

  have read_W_User:
    "ktc_tape ?src 0 (ktc_pos ?src 0) = Enc (bl_ktm M)"
    using div_mod_eq by (simp add: src_tape src_pos)
  have read_W_M_0:
    "ktc_tape ?src (Suc 0) (ktc_pos ?src (Suc 0)) = Enc (bl_ktm M)"
    by (simp add: src_tape src_pos)

  have rd_range:
    "(\<lambda>k. ktc_tape (mid_buf_extending_config_gen (k_ktm M) M pack c w ?q ?r) k
           (ktc_pos (mid_buf_extending_config_gen (k_ktm M) M pack c w ?q ?r) k))
       \<in> UNIV \<rightarrow> Raw ` \<Sigma>u \<union> Enc ` \<Gamma>_ktm M"
    using bl_in le_in div_mod_eq
    by (auto simp: mid_buf_extending_config_gen_def split: nat.split)

  have sym_W_M_0_ne_LE:
    "ktc_tape ?src (Suc 0) (ktc_pos ?src (Suc 0)) \<noteq> Enc (le_ktm M)"
    using read_W_M_0 bl_ne_le by simp

  have tail_bl:
    "\<forall>j\<ge>k_ktm M. ktc_tape ?src j (ktc_pos ?src j) = Enc (bl_ktm M)"
    by (simp add: src_tape)

  have tuple_in:
    "(W_Buf ?tail,
      \<lambda>k. ktc_tape ?src k (ktc_pos ?src k),
      W_Reset,
      (\<lambda>t. case t of
             Suc k \<Rightarrow> if k = 0 then Enc (pack ?tail)
                       else ktc_tape ?src (Suc k) (ktc_pos ?src (Suc k))
           | 0 \<Rightarrow> ktc_tape ?src 0 (ktc_pos ?src 0)),
      \<lambda>t. case t of Suc k \<Rightarrow> if k = 0 then MoveR else MoveN
                  | 0 \<Rightarrow> MoveN)
     \<in> wrap_delta M pack c \<Sigma>u"
  proof -
    have tail_nonempty: "?tail \<noteq> []"
      using tail_len r_pos by (cases ?tail) auto
    have "(W_Buf ?tail,
           \<lambda>k. ktc_tape ?src k (ktc_pos ?src k),
           W_Reset,
           (\<lambda>t. case t of
                  Suc k \<Rightarrow> if k = 0 then Enc (pack ?tail)
                            else ktc_tape ?src (Suc k) (ktc_pos ?src (Suc k))
                | 0 \<Rightarrow> ktc_tape ?src 0 (ktc_pos ?src 0)),
           \<lambda>t. case t of Suc k \<Rightarrow> if k = 0 then MoveR else MoveN
                       | 0 \<Rightarrow> MoveN)
          \<in> wrap_buf_nonempty_end_delta_gen (k_ktm M) M pack c \<Sigma>u"
      unfolding wrap_buf_nonempty_end_delta_gen_def
      using tail_nonempty tail_len r_lt set_tail read_W_User
            sym_W_M_0_ne_LE pack_tail_in_Sigma rd_range tail_bl
      by auto
    thus ?thesis by (simp add: wrap_delta_def)
  qed

  have step_holds:
    "(KConfig (W_Buf ?tail) (ktc_tape ?src) (ktc_pos ?src),
      KConfig W_Reset
        (\<lambda>k. (ktc_tape ?src k)
              ((ktc_pos ?src k) :=
                 (case k of
                    Suc k' \<Rightarrow> if k' = 0 then Enc (pack ?tail)
                              else ktc_tape ?src (Suc k') (ktc_pos ?src (Suc k'))
                  | 0 \<Rightarrow> ktc_tape ?src 0 (ktc_pos ?src 0))))
        (\<lambda>k. go_move
              ((\<lambda>t. case t of Suc k' \<Rightarrow> if k' = 0 then MoveR else MoveN
                            | 0 \<Rightarrow> MoveN) k)
              (ktc_pos ?src k)))
     \<in> ktm_step (wrap_delta M pack c \<Sigma>u)"
    by (rule ktm_step.step
          [where ts = "ktc_tape ?src" and n = "ktc_pos ?src"
                 and a = "\<lambda>t. case t of
                                Suc k \<Rightarrow> if k = 0 then Enc (pack ?tail)
                                          else ktc_tape ?src (Suc k) (ktc_pos ?src (Suc k))
                              | 0 \<Rightarrow> ktc_tape ?src 0 (ktc_pos ?src 0)"
                 and move = "\<lambda>t. case t of Suc k' \<Rightarrow> if k' = 0 then MoveR else MoveN
                                       | 0 \<Rightarrow> MoveN",
           OF tuple_in])

  have target_eq:
    "KConfig W_Reset
       (\<lambda>k. (ktc_tape ?src k)
             ((ktc_pos ?src k) :=
                (case k of
                   Suc k' \<Rightarrow> if k' = 0 then Enc (pack ?tail)
                             else ktc_tape ?src (Suc k') (ktc_pos ?src (Suc k'))
                 | 0 \<Rightarrow> ktc_tape ?src 0 (ktc_pos ?src 0))))
       (\<lambda>k. go_move
             ((\<lambda>t. case t of Suc k' \<Rightarrow> if k' = 0 then MoveR else MoveN
                           | 0 \<Rightarrow> MoveN) k)
             (ktc_pos ?src k))
     = post_encoder_config_gen (k_ktm M) M pack c w"
    unfolding post_encoder_config_gen_def
    using div_mod_eq len_wenc wenc_q_eq r_pos valid_ktm_k_pos[OF vM] k2
    by (auto simp: src_pos src_tape fun_eq_iff
             split: nat.split if_splits)

  have final_step:
    "(?src, post_encoder_config_gen (k_ktm M) M pack c w) \<in> ?R"
    using step_holds target_eq src_eq by simp

  from extends_done final_step
  have "(mid_buf_extending_config_gen (k_ktm M) M pack c w ?q 0,
         post_encoder_config_gen (k_ktm M) M pack c w) \<in> ?R\<^sup>*"
    by (rule rtrancl_into_rtrancl)
  with base_eq show ?thesis by simp
qed

text \<open>L4: relpow form of @{thm[source] mid_to_post_partial} — the partial tail
  takes exactly @{term "Suc (length w mod c)"} wrap-steps.\<close>

lemma mid_to_post_partial_relpow:
  assumes vM: "valid_ktm M"
      and c_pos: "0 < c"
      and w_alpha: "set w \<subseteq> \<Sigma>u"
      and r_pos: "length w mod c \<noteq> 0"
      and pack_tail_in_Sigma:
        "pack (drop ((length w div c) * c) w) \<in> Sigma_ktm M"
      and bl_ne_le: "bl_ktm M \<noteq> le_ktm M"
      and k2: "2 \<le> k_ktm M"
  shows "(mid_encoder_config_gen (k_ktm M) M pack c w (length w div c),
          post_encoder_config_gen (k_ktm M) M pack c w)
         \<in> (ktm_step (wrap_delta M pack c \<Sigma>u)) ^^ Suc (length w mod c)"
proof -
  let ?q = "length w div c"
  let ?r = "length w mod c"
  let ?R = "ktm_step (wrap_delta M pack c \<Sigma>u)"
  let ?tail = "drop (?q * c) w"
  let ?src = "mid_buf_extending_config_gen (k_ktm M) M pack c w ?q ?r"

  have div_mod_eq: "?q * c + ?r = length w"
    by (rule div_mult_mod_eq)
  have r_lt: "?r < c" using c_pos by simp
  have tail_len: "length ?tail = ?r"
  proof -
    have "length ?tail = length w - ?q * c" by simp
    also have "\<dots> = ?r" using div_mod_eq by linarith
    finally show ?thesis .
  qed
  have take_tail_eq: "take ?r ?tail = ?tail"
    using tail_len by simp
  have buf_take_eq: "take ?r (drop (?q * c) w) = ?tail"
    using take_tail_eq by simp
  have set_tail: "set ?tail \<subseteq> \<Sigma>u"
    using w_alpha by (meson set_drop_subset subset_trans)

  have len_wenc: "length (wrap_enc pack c w) = ?q + 1"
    using length_wrap_enc[OF c_pos, of pack w] r_pos by simp
  have wenc_q_eq: "wrap_enc pack c w ! ?q = pack ?tail"
    using wrap_enc_nth_partial[OF c_pos r_pos] .

  have bl_in: "bl_ktm M \<in> \<Gamma>_ktm M"
    by (rule valid_ktm_blank_in_Gamma[OF vM])
  have le_in: "le_ktm M \<in> \<Gamma>_ktm M"
    by (rule valid_ktm_LE_in_Gamma[OF vM])

  have base_eq:
    "mid_buf_extending_config_gen (k_ktm M) M pack c w ?q 0
       = mid_encoder_config_gen (k_ktm M) M pack c w ?q"
    by (simp add: mid_encoder_config_gen_def mid_buf_extending_config_gen_def
              fun_eq_iff split: nat.split)

  have iter:
    "j \<le> ?r \<Longrightarrow>
     (mid_buf_extending_config_gen (k_ktm M) M pack c w ?q 0,
      mid_buf_extending_config_gen (k_ktm M) M pack c w ?q j) \<in> ?R ^^ j"
    for j
  proof (induction j)
    case 0
    show ?case by simp
  next
    case (Suc j)
    from Suc.prems have j_le: "j \<le> ?r" by simp
    note ih = Suc.IH[OF j_le]
    from Suc.prems r_lt have Suc_j_lt: "Suc j < c" by linarith
    from Suc.prems r_lt have j_lt: "j < ?r" by linarith
    have block_in: "?q * c + j < length w"
      using j_lt div_mod_eq by linarith
    have step:
      "(mid_buf_extending_config_gen (k_ktm M) M pack c w ?q j,
        mid_buf_extending_config_gen (k_ktm M) M pack c w ?q (Suc j)) \<in> ?R"
      by (rule mid_buf_extend_step
            [OF vM c_pos w_alpha Suc_j_lt block_in])
    from ih step show ?case by (rule relpow_Suc_I)
  qed

  have extends_done:
    "(mid_buf_extending_config_gen (k_ktm M) M pack c w ?q 0,
      mid_buf_extending_config_gen (k_ktm M) M pack c w ?q ?r) \<in> ?R ^^ ?r"
    using iter[of ?r] by simp

  have src_state: "ktc_state ?src = W_Buf ?tail"
    using buf_take_eq by (simp add: mid_buf_extending_config_gen_def)
  have src_pos:
    "ktc_pos ?src
       = (\<lambda>t. case t of 0 \<Rightarrow> 1 + ?q * c + ?r
                       | Suc k \<Rightarrow> (if k = 0 then 1 + ?q else 0))"
    by (simp add: mid_buf_extending_config_gen_def fun_eq_iff)
  have src_tape:
    "ktc_tape ?src
       = (\<lambda>t n. if t < k_ktm M
                then (case t of
                  0 \<Rightarrow> (if n = 0 then Enc (le_ktm M)
                            else if n \<le> length w then Raw (w ! (n - 1))
                            else Enc (bl_ktm M))
                | Suc k \<Rightarrow> (if n = 0 then Enc (le_ktm M)
                            else if k = 0 \<and> n \<le> ?q
                              then Enc (wrap_enc pack c w ! (n - 1))
                            else Enc (bl_ktm M)))
                else Enc (bl_ktm M))"
    by (simp add: mid_buf_extending_config_gen_def fun_eq_iff)

  have src_eq: "?src = KConfig (W_Buf ?tail) (ktc_tape ?src) (ktc_pos ?src)"
    using src_state src_pos src_tape
    by (cases ?src) simp

  have read_W_User:
    "ktc_tape ?src 0 (ktc_pos ?src 0) = Enc (bl_ktm M)"
    using div_mod_eq by (simp add: src_tape src_pos)
  have read_W_M_0:
    "ktc_tape ?src (Suc 0) (ktc_pos ?src (Suc 0)) = Enc (bl_ktm M)"
    by (simp add: src_tape src_pos)

  have rd_range:
    "(\<lambda>k. ktc_tape (mid_buf_extending_config_gen (k_ktm M) M pack c w ?q ?r) k
           (ktc_pos (mid_buf_extending_config_gen (k_ktm M) M pack c w ?q ?r) k))
       \<in> UNIV \<rightarrow> Raw ` \<Sigma>u \<union> Enc ` \<Gamma>_ktm M"
    using bl_in le_in div_mod_eq
    by (auto simp: mid_buf_extending_config_gen_def split: nat.split)

  have sym_W_M_0_ne_LE:
    "ktc_tape ?src (Suc 0) (ktc_pos ?src (Suc 0)) \<noteq> Enc (le_ktm M)"
    using read_W_M_0 bl_ne_le by simp

  have tail_bl:
    "\<forall>j\<ge>k_ktm M. ktc_tape ?src j (ktc_pos ?src j) = Enc (bl_ktm M)"
    by (simp add: src_tape)

  have tuple_in:
    "(W_Buf ?tail,
      \<lambda>k. ktc_tape ?src k (ktc_pos ?src k),
      W_Reset,
      (\<lambda>t. case t of
             Suc k \<Rightarrow> if k = 0 then Enc (pack ?tail)
                       else ktc_tape ?src (Suc k) (ktc_pos ?src (Suc k))
           | 0 \<Rightarrow> ktc_tape ?src 0 (ktc_pos ?src 0)),
      \<lambda>t. case t of Suc k \<Rightarrow> if k = 0 then MoveR else MoveN
                  | 0 \<Rightarrow> MoveN)
     \<in> wrap_delta M pack c \<Sigma>u"
  proof -
    have tail_nonempty: "?tail \<noteq> []"
      using tail_len r_pos by (cases ?tail) auto
    have "(W_Buf ?tail,
           \<lambda>k. ktc_tape ?src k (ktc_pos ?src k),
           W_Reset,
           (\<lambda>t. case t of
                  Suc k \<Rightarrow> if k = 0 then Enc (pack ?tail)
                            else ktc_tape ?src (Suc k) (ktc_pos ?src (Suc k))
                | 0 \<Rightarrow> ktc_tape ?src 0 (ktc_pos ?src 0)),
           \<lambda>t. case t of Suc k \<Rightarrow> if k = 0 then MoveR else MoveN
                       | 0 \<Rightarrow> MoveN)
          \<in> wrap_buf_nonempty_end_delta_gen (k_ktm M) M pack c \<Sigma>u"
      unfolding wrap_buf_nonempty_end_delta_gen_def
      using tail_nonempty tail_len r_lt set_tail read_W_User
            sym_W_M_0_ne_LE pack_tail_in_Sigma rd_range tail_bl
      by auto
    thus ?thesis by (simp add: wrap_delta_def)
  qed

  have step_holds:
    "(KConfig (W_Buf ?tail) (ktc_tape ?src) (ktc_pos ?src),
      KConfig W_Reset
        (\<lambda>k. (ktc_tape ?src k)
              ((ktc_pos ?src k) :=
                 (case k of
                    Suc k' \<Rightarrow> if k' = 0 then Enc (pack ?tail)
                              else ktc_tape ?src (Suc k') (ktc_pos ?src (Suc k'))
                  | 0 \<Rightarrow> ktc_tape ?src 0 (ktc_pos ?src 0))))
        (\<lambda>k. go_move
              ((\<lambda>t. case t of Suc k' \<Rightarrow> if k' = 0 then MoveR else MoveN
                            | 0 \<Rightarrow> MoveN) k)
              (ktc_pos ?src k)))
     \<in> ktm_step (wrap_delta M pack c \<Sigma>u)"
    by (rule ktm_step.step
          [where ts = "ktc_tape ?src" and n = "ktc_pos ?src"
                 and a = "\<lambda>t. case t of
                                Suc k \<Rightarrow> if k = 0 then Enc (pack ?tail)
                                          else ktc_tape ?src (Suc k) (ktc_pos ?src (Suc k))
                              | 0 \<Rightarrow> ktc_tape ?src 0 (ktc_pos ?src 0)"
                 and move = "\<lambda>t. case t of Suc k' \<Rightarrow> if k' = 0 then MoveR else MoveN
                                       | 0 \<Rightarrow> MoveN",
           OF tuple_in])

  have target_eq:
    "KConfig W_Reset
       (\<lambda>k. (ktc_tape ?src k)
             ((ktc_pos ?src k) :=
                (case k of
                   Suc k' \<Rightarrow> if k' = 0 then Enc (pack ?tail)
                             else ktc_tape ?src (Suc k') (ktc_pos ?src (Suc k'))
                 | 0 \<Rightarrow> ktc_tape ?src 0 (ktc_pos ?src 0))))
       (\<lambda>k. go_move
             ((\<lambda>t. case t of Suc k' \<Rightarrow> if k' = 0 then MoveR else MoveN
                           | 0 \<Rightarrow> MoveN) k)
             (ktc_pos ?src k))
     = post_encoder_config_gen (k_ktm M) M pack c w"
    unfolding post_encoder_config_gen_def
    using div_mod_eq len_wenc wenc_q_eq r_pos valid_ktm_k_pos[OF vM] k2
    by (auto simp: src_pos src_tape fun_eq_iff
             split: nat.split if_splits)

  have final_step:
    "(?src, post_encoder_config_gen (k_ktm M) M pack c w) \<in> ?R"
    using step_holds target_eq src_eq by simp

  from extends_done final_step
  have "(mid_buf_extending_config_gen (k_ktm M) M pack c w ?q 0,
         post_encoder_config_gen (k_ktm M) M pack c w) \<in> ?R ^^ Suc ?r"
    by (rule relpow_Suc_I)
  with base_eq show ?thesis by simp
qed


subsection \<open>The end of the input\<close>

text \<open>Tail step from the post-final-full-cycle waypoint to
  @{const post_encoder_config_gen}, dispatching on @{term "length w mod c"}.\<close>

lemma mid_to_post:
  assumes vM: "valid_ktm M"
      and c_pos: "0 < c"
      and w_alpha: "set w \<subseteq> \<Sigma>u"
      and bl_ne_le: "bl_ktm M \<noteq> le_ktm M"
      and k2: "2 \<le> k_ktm M"
      and pack_tail_in_Sigma:
        "length w mod c \<noteq> 0 \<Longrightarrow>
         pack (drop ((length w div c) * c) w) \<in> Sigma_ktm M"
  shows "(mid_encoder_config_gen (k_ktm M) M pack c w (length w div c),
          post_encoder_config_gen (k_ktm M) M pack c w)
         \<in> (ktm_step (wrap_delta M pack c \<Sigma>u))\<^sup>*"
proof (cases "length w mod c = 0")
  case True
  from mid_to_post_empty[OF vM c_pos True, of pack \<Sigma>u]
  show ?thesis by (rule r_into_rtrancl)
next
  case False
  show ?thesis
    by (rule mid_to_post_partial
          [where pack = pack,
           OF vM c_pos w_alpha False
              pack_tail_in_Sigma[OF False] bl_ne_le k2])
qed


subsection \<open>Encoder-phase reachability and step count\<close>

text \<open>The full encoder phase reaches @{const post_encoder_config_gen}.\<close>

lemma encoder_phase_terminates:
  assumes vM: "valid_ktm M"
      and c_pos: "0 < c"
      and w_alpha: "set w \<subseteq> \<Sigma>u"
      and bl_ne_le: "bl_ktm M \<noteq> le_ktm M"
      and k2: "2 \<le> k_ktm M"
      and pack_contract_in_Sigma:
        "\<And>i. i * c < length w \<Longrightarrow>
              pack (take c (drop (i * c) w)) \<in> Sigma_ktm M"
  shows "(init_config_ktm (encoding_wrap M pack c \<Sigma>u) (map Raw w),
          post_encoder_config_gen (k_ktm M) M pack c w)
         \<in> (ktm_step (wrap_delta M pack c \<Sigma>u))\<^sup>*"
proof -
  let ?q = "length w div c"
  let ?r = "length w mod c"
  let ?R = "ktm_step (wrap_delta M pack c \<Sigma>u)"

  have div_mod_eq: "?q * c + ?r = length w"
    by (rule div_mult_mod_eq)
  have r_lt: "?r < c" using c_pos by simp

  have init_step:
    "(init_config_ktm (encoding_wrap M pack c \<Sigma>u) (map Raw w),
      mid_encoder_config_gen (k_ktm M) M pack c w 0) \<in> ?R"
    by (rule init_to_mid_zero[OF vM c_pos])

  have iter:
    "i \<le> ?q \<Longrightarrow>
     (mid_encoder_config_gen (k_ktm M) M pack c w 0,
      mid_encoder_config_gen (k_ktm M) M pack c w i) \<in> ?R\<^sup>*"
    for i
  proof (induction i)
    case 0
    show ?case by simp
  next
    case (Suc i)
    from Suc.prems have i_le_q: "i \<le> ?q" by simp
    from Suc.prems have Suc_i_le_q: "Suc i \<le> ?q" by simp
    note ih = Suc.IH[OF i_le_q]

    have suc_ic_le_qc: "(Suc i) * c \<le> ?q * c"
      by (rule mult_le_mono1[OF Suc_i_le_q])
    have block_full: "(Suc i) * c \<le> length w"
      using suc_ic_le_qc div_mod_eq by linarith
    have i_lt_q: "i < ?q" using Suc_i_le_q by simp
    have ic_lt_qc: "i * c < ?q * c"
      using i_lt_q c_pos by simp
    have ic_lt: "i * c < length w"
      using ic_lt_qc div_mod_eq by linarith

    have pack_in_Sigma: "pack (take c (drop (i * c) w)) \<in> Sigma_ktm M"
      by (rule pack_contract_in_Sigma[OF ic_lt])

    have step:
      "(mid_encoder_config_gen (k_ktm M) M pack c w i,
        mid_encoder_config_gen (k_ktm M) M pack c w (Suc i)) \<in> ?R\<^sup>*"
      by (rule mid_encoder_step
            [where pack = pack,
             OF vM c_pos w_alpha block_full pack_in_Sigma bl_ne_le k2])
    show ?case using ih step by (rule rtrancl_trans)
  qed

  have outer_done:
    "(mid_encoder_config_gen (k_ktm M) M pack c w 0,
      mid_encoder_config_gen (k_ktm M) M pack c w ?q) \<in> ?R\<^sup>*"
    using iter[of ?q] by simp

  have qc_lt: "?r \<noteq> 0 \<Longrightarrow> ?q * c < length w"
    using div_mod_eq by linarith
  have take_drop_eq:
    "?r \<noteq> 0 \<Longrightarrow> take c (drop (?q * c) w) = drop (?q * c) w"
  proof -
    assume "?r \<noteq> 0"
    have "length (drop (?q * c) w) = length w - ?q * c"
      by simp
    also have "\<dots> = ?r" using div_mod_eq by linarith
    finally have "length (drop (?q * c) w) = ?r" .
    moreover have "?r < c" using r_lt .
    ultimately show "take c (drop (?q * c) w) = drop (?q * c) w"
      by simp
  qed
  have pack_tail_in_Sigma:
    "?r \<noteq> 0 \<Longrightarrow> pack (drop (?q * c) w) \<in> Sigma_ktm M"
  proof -
    assume r_pos: "?r \<noteq> 0"
    from pack_contract_in_Sigma[OF qc_lt[OF r_pos]]
    have "pack (take c (drop (?q * c) w)) \<in> Sigma_ktm M" .
    with take_drop_eq[OF r_pos] show ?thesis by simp
  qed

  have tail_step:
    "(mid_encoder_config_gen (k_ktm M) M pack c w ?q,
      post_encoder_config_gen (k_ktm M) M pack c w) \<in> ?R\<^sup>*"
    by (rule mid_to_post
          [where pack = pack,
           OF vM c_pos w_alpha bl_ne_le k2 pack_tail_in_Sigma])

  from outer_done tail_step
  have "(mid_encoder_config_gen (k_ktm M) M pack c w 0,
         post_encoder_config_gen (k_ktm M) M pack c w) \<in> ?R\<^sup>*"
    by (rule rtrancl_trans)
  with init_step
  show ?thesis
    by (rule converse_rtrancl_into_rtrancl)
qed

text \<open>L5: relpow form — the encoder phase takes exactly @{term "length w + 2"}
  wrap-steps.\<close>

lemma init_to_post_encoder_relpow:
  assumes vM: "valid_ktm M"
      and c_pos: "0 < c"
      and w_alpha: "set w \<subseteq> \<Sigma>u"
      and bl_ne_le: "bl_ktm M \<noteq> le_ktm M"
      and k2: "2 \<le> k_ktm M"
      and pack_contract_in_Sigma:
        "\<And>i. i * c < length w \<Longrightarrow>
              pack (take c (drop (i * c) w)) \<in> Sigma_ktm M"
  shows "(init_config_ktm (encoding_wrap M pack c \<Sigma>u) (map Raw w),
          post_encoder_config_gen (k_ktm M) M pack c w)
         \<in> (ktm_step (wrap_delta M pack c \<Sigma>u)) ^^ (length w + 2)"
proof -
  let ?q = "length w div c"
  let ?r = "length w mod c"
  let ?R = "ktm_step (wrap_delta M pack c \<Sigma>u)"

  have div_mod_eq: "?q * c + ?r = length w"
    by (rule div_mult_mod_eq)
  have r_lt: "?r < c" using c_pos by simp

  have init_step:
    "(init_config_ktm (encoding_wrap M pack c \<Sigma>u) (map Raw w),
      mid_encoder_config_gen (k_ktm M) M pack c w 0) \<in> ?R"
    by (rule init_to_mid_zero[OF vM c_pos])

  have iter_step:
    "(mid_encoder_config_gen (k_ktm M) M pack c w 0,
      mid_encoder_config_gen (k_ktm M) M pack c w ?q)
       \<in> ?R ^^ (c * ?q)"
    by (rule mid_encoder_iter_relpow
          [where pack = pack,
           OF vM c_pos w_alpha bl_ne_le k2 pack_contract_in_Sigma order_refl])

  from relpow_Suc_I2[OF init_step iter_step]
  have init_to_q:
    "(init_config_ktm (encoding_wrap M pack c \<Sigma>u) (map Raw w),
      mid_encoder_config_gen (k_ktm M) M pack c w ?q) \<in> ?R ^^ Suc (c * ?q)" .

  show ?thesis
  proof (cases "?r = 0")
    case True
    have tail_step:
      "(mid_encoder_config_gen (k_ktm M) M pack c w ?q,
        post_encoder_config_gen (k_ktm M) M pack c w) \<in> ?R"
      by (rule mid_to_post_empty[OF vM c_pos True])
    from relpow_Suc_I[OF init_to_q tail_step]
    have chain:
      "(init_config_ktm (encoding_wrap M pack c \<Sigma>u) (map Raw w),
        post_encoder_config_gen (k_ktm M) M pack c w) \<in> ?R ^^ Suc (Suc (c * ?q))" .
    have len_eq: "Suc (Suc (c * ?q)) = length w + 2"
      using True div_mod_eq by (simp add: mult.commute)
    from chain len_eq show ?thesis by simp
  next
    case False
    have pack_tail_in_Sigma:
      "pack (drop (?q * c) w) \<in> Sigma_ktm M"
    proof -
      have qc_lt: "?q * c < length w"
        using False div_mod_eq by linarith
      have "pack (take c (drop (?q * c) w))
              = pack (drop (?q * c) w)"
      proof -
        have len_drop_eq: "length (drop (?q * c) w) = ?r"
        proof -
          have "length (drop (?q * c) w) = length w - ?q * c" by simp
          also have "\<dots> = ?r" using div_mod_eq by linarith
          finally show ?thesis .
        qed
        from r_lt len_drop_eq have "take c (drop (?q * c) w) = drop (?q * c) w"
          by simp
        thus ?thesis by simp
      qed
      with pack_contract_in_Sigma[OF qc_lt]
      show ?thesis by simp
    qed
    have tail_step:
      "(mid_encoder_config_gen (k_ktm M) M pack c w ?q,
        post_encoder_config_gen (k_ktm M) M pack c w) \<in> ?R ^^ Suc ?r"
      by (rule mid_to_post_partial_relpow
            [where pack = pack,
             OF vM c_pos w_alpha False pack_tail_in_Sigma bl_ne_le k2])
    from init_to_q tail_step
    have chain:
      "(init_config_ktm (encoding_wrap M pack c \<Sigma>u) (map Raw w),
        post_encoder_config_gen (k_ktm M) M pack c w)
         \<in> ?R ^^ (Suc (c * ?q) + Suc ?r)"
      unfolding relpow_add by blast
    have len_eq: "Suc (c * ?q) + Suc ?r = length w + 2"
      using div_mod_eq by (simp add: mult.commute)
    from chain len_eq show ?thesis by simp
  qed
qed

end
