theory Wrap_Reset
  imports Wrap_Defs
begin

section \<open>Faithful (k-tape) plant-\<open>le\<close> wrap: reset threading and the origin float\<close>

text \<open>The plant wrap's reset differs from a combined blank-and-rewind reset
  in that it
  \<^emph>\<open>does not\<close> walk the input tape (physical @{text 0}) back to its @{text le}.
  It rewinds only the storage tape (physical @{text 1}, carrying M's tape
  @{text 0} = the encoded input) --- the @{text "\<lceil>n/c\<rceil>"} cells that make
  up the @{text "\<epsilon>\<cdot>n"} term --- freezing the input head at
  @{term "length w + 1"} throughout.  When the storage head reaches its
  @{text le} at cell @{text 0}, the plant-done step writes a fresh @{text le}
  on the input tape at the frozen head and hands to @{text W_Disp}.

  The resulting engine configuration is the input tape \<^emph>\<open>floated\<close>: physical
  tape @{text 0} carries a planted @{text le} at cell @{term "length w + 1"}
  with the spent raw input as an unreachable prefix below it, and blanks
  above --- indistinguishable, from the engine's position-agnostic view,
  from a fresh blank work tape whose origin sits at @{term "length w + 1"}.
  This is exactly a @{const shift_rel} by @{term "length w + 1"} of the
  @{text \<tau>}-lift of M's initial configuration, so the origin-float lemmas
  of @{theory Multitape_TM_Substrate.Multitape_Origin_Float} bridge the floated run back
  to the proper @{const init_config_mttm} the transpose run machinery
  consumes.\<close>


subsection \<open>The storage-tape rewind, input head frozen\<close>

text \<open>One generic-rewind step retracts the storage head (physical
  @{text "Suc 0"}) from @{term "Suc m1"} to @{term m1}, the input head frozen
  at @{term "length w + 1"} and every tape's content preserved.  This reuses
  @{const mid_reset_combined_config_gen} with the input head @{term m0} pinned
  at @{term "length w + 1"}: since that config only blanks cells @{text "> m0"}
  and @{term "length w + 1 > length w"}, the raw input stays intact and the
  configuration depends on the storage head @{term m1} only through its
  position.\<close>

lemma mid_plant_rewind_step:
  assumes vM: "valid_mttm M"
      and c_pos: "0 < c"
      and w_alpha: "set w \<subseteq> \<Sigma>u"
      and bl_ne_le: "bl_tm M \<noteq> le_tm M"
      and k2: "2 \<le> k_tm M"
      and pack_in:
        "\<And>i. i * c < length w \<Longrightarrow> pack (take c (drop (i * c) w)) \<in> \<Gamma>_tm M"
      and pack_ne_le:
        "\<And>i. i * c < length w \<Longrightarrow> pack (take c (drop (i * c) w)) \<noteq> le_tm M"
    shows "(mid_reset_combined_config_gen (k_tm M) M pack c w (length w + 1) (Suc m1),
            mid_reset_combined_config_gen (k_tm M) M pack c w (length w + 1) m1)
           \<in> mttm_step (wrap_delta M pack c \<Sigma>u)"
proof -
  let ?src = "mid_reset_combined_config_gen (k_tm M) M pack c w (length w + 1) (Suc m1)"
  let ?L = "length (wrap_enc pack c w)"
  let ?sym = "\<lambda>k. mt_tape ?src k (mt_pos ?src k)"

  have bl_in: "bl_tm M \<in> \<Gamma>_tm M" by (rule valid_mttm_blank_in_Gamma[OF vM])
  have le_in: "le_tm M \<in> \<Gamma>_tm M" by (rule valid_mttm_LE_in_Gamma[OF vM])
  have kpos: "0 < k_tm M" using k2 by simp

  have src_state: "mt_state ?src = W_Reset"
    by (simp add: mid_reset_combined_config_gen_def)

  have src_eq: "?src = Config\<^sub>M W_Reset (mt_tape ?src) (mt_pos ?src)"
    using src_state by (cases ?src) simp

  \<comment> \<open>Storage head reads a non-@{text le} at @{term "Suc m1"} (never cell 0).\<close>
  have sym1_ne_le: "?sym (Suc 0) \<noteq> Enc (le_tm M)"
  proof (cases "Suc m1 \<le> ?L")
    case True
    hence m1_lt_L: "m1 < ?L" by simp
    have ne: "wrap_enc pack c w ! m1 \<noteq> le_tm M"
      by (rule wrap_enc_ne_le[OF c_pos pack_ne_le m1_lt_L])
    have read: "?sym (Suc 0) = Enc (wrap_enc pack c w ! m1)"
      using True k2 by (simp add: mid_reset_combined_config_gen_def split: nat.split)
    show ?thesis using read ne by simp
  next
    case False
    have read: "?sym (Suc 0) = Enc (bl_tm M)"
      using False k2 by (simp add: mid_reset_combined_config_gen_def split: nat.split)
    show ?thesis using read bl_ne_le by simp
  qed

  \<comment> \<open>Range typing and blank tail of the read function.\<close>
  have enc_in_Gamma:
    "\<And>i. i < length (wrap_enc pack c w) \<Longrightarrow> wrap_enc pack c w ! i \<in> \<Gamma>_tm M"
    by (rule wrap_enc_in_Gamma[where pack = pack, OF c_pos pack_in])
  have wi0: "\<And>i. Suc i \<le> length w \<Longrightarrow> w ! i \<in> \<Sigma>u"
    using w_alpha by (meson Suc_le_eq nth_mem subsetD)
  have rd_range: "?sym \<in> UNIV \<rightarrow> Raw ` \<Sigma>u \<union> Enc ` \<Gamma>_tm M"
    using bl_in le_in enc_in_Gamma wi0
    by (auto simp: mid_reset_combined_config_gen_def split: nat.split)

  have tail_bl: "\<forall>j\<ge>k_tm M. ?sym j = Enc (bl_tm M)"
    by (auto simp: mid_reset_combined_config_gen_def)

  \<comment> \<open>The generic-rewind tuple: read = write, storage head left, all else N.\<close>
  let ?dir = "\<lambda>t. if t = Suc 0 then dir.L else dir.N"
  have tuple_in: "(W_Reset, ?sym, W_Reset, ?sym, ?dir) \<in> wrap_delta M pack c \<Sigma>u"
  proof -
    have "(W_Reset, ?sym, W_Reset, ?sym, ?dir)
            \<in> wrap_rewind_loop_delta_gen W_Reset (Suc 0) (k_tm M) M \<Sigma>u"
      unfolding wrap_rewind_loop_delta_gen_def
      using sym1_ne_le tail_bl rd_range by blast
    thus ?thesis by (simp add: wrap_delta_def)
  qed

  have step_holds:
    "(Config\<^sub>M W_Reset (mt_tape ?src) (mt_pos ?src),
      Config\<^sub>M W_Reset
        (\<lambda>k. (mt_tape ?src k)((mt_pos ?src k) := ?sym k))
        (\<lambda>k. go_dir (?dir k) (mt_pos ?src k)))
     \<in> mttm_step (wrap_delta M pack c \<Sigma>u)"
    by (rule mttm_step.step
          [where ts = "mt_tape ?src" and n = "mt_pos ?src" and a = ?sym and dir = ?dir,
           OF tuple_in])

  \<comment> \<open>Target equality.  Write = read, so tapes are preserved; only the storage
    head moves left (@{term "Suc m1"} to @{term m1}); the input head stays.\<close>
  have target_eq:
    "Config\<^sub>M W_Reset
       (\<lambda>k. (mt_tape ?src k)((mt_pos ?src k) := ?sym k))
       (\<lambda>k. go_dir (?dir k) (mt_pos ?src k))
     = mid_reset_combined_config_gen (k_tm M) M pack c w (length w + 1) m1"
    by (auto simp: mid_reset_combined_config_gen_def fun_upd_triv fun_eq_iff
             split: nat.split)

  from step_holds target_eq src_eq show ?thesis by simp
qed

text \<open>Iterated: @{term s} storage-rewind steps retract the storage head from
  @{term "m1 + s"} to @{term m1}, the input head frozen throughout.\<close>

lemma mid_plant_rewind_iter:
  assumes vM: "valid_mttm M"
      and c_pos: "0 < c"
      and w_alpha: "set w \<subseteq> \<Sigma>u"
      and bl_ne_le: "bl_tm M \<noteq> le_tm M"
      and k2: "2 \<le> k_tm M"
      and pack_in:
        "\<And>i. i * c < length w \<Longrightarrow> pack (take c (drop (i * c) w)) \<in> \<Gamma>_tm M"
      and pack_ne_le:
        "\<And>i. i * c < length w \<Longrightarrow> pack (take c (drop (i * c) w)) \<noteq> le_tm M"
    shows "(mid_reset_combined_config_gen (k_tm M) M pack c w (length w + 1) (m1 + s),
            mid_reset_combined_config_gen (k_tm M) M pack c w (length w + 1) m1)
           \<in> (mttm_step (wrap_delta M pack c \<Sigma>u)) ^^ s"
proof (induction s)
  case 0
  show ?case by simp
next
  case (Suc s)
  have step:
    "(mid_reset_combined_config_gen (k_tm M) M pack c w (length w + 1) (Suc (m1 + s)),
      mid_reset_combined_config_gen (k_tm M) M pack c w (length w + 1) (m1 + s))
       \<in> mttm_step (wrap_delta M pack c \<Sigma>u)"
    apply (rule mid_plant_rewind_step[OF vM c_pos w_alpha bl_ne_le k2])
     apply (fact pack_in)
    apply (fact pack_ne_le)
    done
  from relpow_Suc_I2[OF step Suc.IH]
  show ?case by simp
qed

text \<open>The storage rewind reaches the bottom @{term "mid_reset_combined_config_gen
  (k_tm M) M pack c w (length w + 1) 0"} (storage head at @{text le}, input head
  still frozen at @{term "length w + 1"}) from @{const post_encoder_config_gen}
  in exactly @{term "Suc (length (wrap_enc pack c w))"} rewind steps --- the
  @{text "\<lceil>n/c\<rceil>"} storage cells, the @{text "\<epsilon>\<cdot>n"} term.  The input tape
  is \<^emph>\<open>never\<close> walked.\<close>

lemma plant_rewind_loop_relpow:
  assumes vM: "valid_mttm M"
      and c_pos: "0 < c"
      and w_alpha: "set w \<subseteq> \<Sigma>u"
      and bl_ne_le: "bl_tm M \<noteq> le_tm M"
      and k2: "2 \<le> k_tm M"
      and pack_in:
        "\<And>i. i * c < length w \<Longrightarrow> pack (take c (drop (i * c) w)) \<in> \<Gamma>_tm M"
      and pack_ne_le:
        "\<And>i. i * c < length w \<Longrightarrow> pack (take c (drop (i * c) w)) \<noteq> le_tm M"
    shows "(post_encoder_config_gen (k_tm M) M pack c w,
            mid_reset_combined_config_gen (k_tm M) M pack c w (length w + 1) 0)
           \<in> (mttm_step (wrap_delta M pack c \<Sigma>u))
               ^^ (Suc (length (wrap_enc pack c w)))"
proof -
  let ?L = "length (wrap_enc pack c w)"
  have iter:
    "(mid_reset_combined_config_gen (k_tm M) M pack c w (length w + 1) (0 + Suc ?L),
      mid_reset_combined_config_gen (k_tm M) M pack c w (length w + 1) 0)
       \<in> (mttm_step (wrap_delta M pack c \<Sigma>u)) ^^ (Suc ?L)"
    apply (rule mid_plant_rewind_iter[OF vM c_pos w_alpha bl_ne_le k2])
     apply (fact pack_in)
    apply (fact pack_ne_le)
    done
  show ?thesis
    using iter by (simp add: post_encoder_eq_mid_reset_combined_top)
qed


subsection \<open>The floated engine configuration and the plant-done / dispatch steps\<close>

text \<open>After the rewind bottoms out, the plant-done step writes a fresh
  @{text le} on the input tape (physical @{text 0}) at its frozen head
  @{term "length w + 1"} and hands to @{text W_Disp}; the dispatch then
  lifts @{text "W_Disp \<rightarrow> W_Run (s_tm M)"}.  Both leave heads fixed.  The
  common tape function \<open>plant_reset_tape\<close> is the rewind bottom with
  the planted @{text le}: physical tape @{text 0} carries @{text le} at cell
  @{text 0}, the spent raw input at cells @{text "1 \<dots> length w"}, the
  \<^emph>\<open>planted\<close> @{text le} at cell @{term "length w + 1"}, and blanks above.\<close>

definition plant_reset_tape ::
  "('q, 'b) mttm \<Rightarrow> ('a list \<Rightarrow> 'b) \<Rightarrow> nat \<Rightarrow> 'a list \<Rightarrow> nat \<Rightarrow> nat
   \<Rightarrow> ('a, 'b) wrap_alphabet"
where
  "plant_reset_tape M pack c w t n =
     (if t < k_tm M
      then (case t of
        0 \<Rightarrow> (if n = 0 then Enc (le_tm M)
              else if n \<le> length w then Raw (w ! (n - 1))
              else if n = length w + 1 then Enc (le_tm M)
              else Enc (bl_tm M))
      | Suc k \<Rightarrow> (if n = 0 then Enc (le_tm M)
                 else if k = 0 \<and> n \<le> length (wrap_enc pack c w)
                   then Enc (wrap_enc pack c w ! (n - 1))
                 else Enc (bl_tm M)))
      else Enc (bl_tm M))"

definition plant_reset_pos :: "'a list \<Rightarrow> nat \<Rightarrow> nat" where
  "plant_reset_pos w t = (case t of 0 \<Rightarrow> length w + 1 | Suc _ \<Rightarrow> 0)"

definition mid_plant_disp_config ::
  "('q, 'b) mttm \<Rightarrow> ('a list \<Rightarrow> 'b) \<Rightarrow> nat \<Rightarrow> 'a list
   \<Rightarrow> (('a, 'b) wrap_alphabet, ('q, 'a, 'b) wrap_state) mt_config"
where
  "mid_plant_disp_config M pack c w =
     Config\<^sub>M W_Disp (plant_reset_tape M pack c w) (plant_reset_pos w)"

definition post_plant_dispatch_config ::
  "('q, 'b) mttm \<Rightarrow> ('a list \<Rightarrow> 'b) \<Rightarrow> nat \<Rightarrow> 'a list
   \<Rightarrow> (('a, 'b) wrap_alphabet, ('q, 'a, 'b) wrap_state) mt_config"
where
  "post_plant_dispatch_config M pack c w =
     Config\<^sub>M (W_Run (s_tm M)) (plant_reset_tape M pack c w) (plant_reset_pos w)"

text \<open>The plant-done step: from the rewind bottom (storage head at @{text le})
  one @{const wrap_plant_done_delta} transition plants @{text le} on the
  input tape at its frozen head and lifts @{text "W_Reset \<rightarrow> W_Disp"}.\<close>

lemma plant_done_step:
  assumes vM: "valid_mttm M"
      and k2: "2 \<le> k_tm M"
    shows "(mid_reset_combined_config_gen (k_tm M) M pack c w (length w + 1) 0,
            mid_plant_disp_config M pack c w)
           \<in> mttm_step (wrap_delta M pack c \<Sigma>u)"
proof -
  let ?src = "mid_reset_combined_config_gen (k_tm M) M pack c w (length w + 1) 0"
  let ?sym = "\<lambda>k. mt_tape ?src k (mt_pos ?src k)"
  let ?a = "\<lambda>t. if t = 0 then Enc (le_tm M) else ?sym t"
  have bl_in: "bl_tm M \<in> \<Gamma>_tm M" by (rule valid_mttm_blank_in_Gamma[OF vM])
  have le_in: "le_tm M \<in> \<Gamma>_tm M" by (rule valid_mttm_LE_in_Gamma[OF vM])

  have src_state: "mt_state ?src = W_Reset"
    by (simp add: mid_reset_combined_config_gen_def)
  have src_eq: "?src = Config\<^sub>M W_Reset (mt_tape ?src) (mt_pos ?src)"
    using src_state by (cases ?src) simp

  have sym1_le: "?sym (Suc 0) = Enc (le_tm M)"
    using k2 by (simp add: mid_reset_combined_config_gen_def split: nat.split)
  have tail_bl: "\<forall>j\<ge>k_tm M. ?sym j = Enc (bl_tm M)"
    by (auto simp: mid_reset_combined_config_gen_def)
  have rd_range: "?sym \<in> UNIV \<rightarrow> Raw ` \<Sigma>u \<union> Enc ` \<Gamma>_tm M"
    using bl_in le_in
    by (auto simp: mid_reset_combined_config_gen_def split: nat.split)

  have tuple_in: "(W_Reset, ?sym, W_Disp, ?a, \<lambda>_. dir.N)
                    \<in> wrap_delta M pack c \<Sigma>u"
  proof -
    have "(W_Reset, ?sym, W_Disp, ?a, \<lambda>_. dir.N)
            \<in> wrap_plant_done_delta M \<Sigma>u"
      unfolding wrap_plant_done_delta_def
      using sym1_le tail_bl rd_range by blast
    thus ?thesis by (simp add: wrap_delta_def)
  qed

  have step_holds:
    "(Config\<^sub>M W_Reset (mt_tape ?src) (mt_pos ?src),
      Config\<^sub>M W_Disp
        (\<lambda>k. (mt_tape ?src k)((mt_pos ?src k) := ?a k))
        (\<lambda>k. go_dir dir.N (mt_pos ?src k)))
     \<in> mttm_step (wrap_delta M pack c \<Sigma>u)"
    by (rule mttm_step.step
          [where ts = "mt_tape ?src" and n = "mt_pos ?src" and a = ?a
                 and dir = "\<lambda>_. dir.N", OF tuple_in])

  have target_eq:
    "Config\<^sub>M W_Disp
       (\<lambda>k. (mt_tape ?src k)((mt_pos ?src k) := ?a k))
       (\<lambda>k. go_dir dir.N (mt_pos ?src k))
     = mid_plant_disp_config M pack c w"
    using k2
    by (auto simp: mid_plant_disp_config_def plant_reset_tape_def plant_reset_pos_def
                   mid_reset_combined_config_gen_def fun_eq_iff
             split: nat.split)

  from step_holds target_eq src_eq show ?thesis by simp
qed

text \<open>The dispatch step: one @{const wrap_disp_delta_gen} transition lifts
  @{text "W_Disp \<rightarrow> W_Run (s_tm M)"}, tapes and heads untouched --- reaching
  the floated engine configuration @{const post_plant_dispatch_config}.\<close>

lemma plant_disp_step:
  assumes vM: "valid_mttm M"
      and k2: "2 \<le> k_tm M"
    shows "(mid_plant_disp_config M pack c w, post_plant_dispatch_config M pack c w)
           \<in> mttm_step (wrap_delta M pack c \<Sigma>u)"
proof -
  let ?src = "mid_plant_disp_config M pack c w"
  let ?sym = "\<lambda>k. mt_tape ?src k (mt_pos ?src k)"
  have bl_in: "bl_tm M \<in> \<Gamma>_tm M" by (rule valid_mttm_blank_in_Gamma[OF vM])
  have le_in: "le_tm M \<in> \<Gamma>_tm M" by (rule valid_mttm_LE_in_Gamma[OF vM])

  have src_state: "mt_state ?src = W_Disp"
    by (simp add: mid_plant_disp_config_def)
  have src_eq: "?src = Config\<^sub>M W_Disp (mt_tape ?src) (mt_pos ?src)"
    using src_state by (cases ?src) simp

  have tail_bl: "\<forall>j\<ge>k_tm M. ?sym j = Enc (bl_tm M)"
    by (auto simp: mid_plant_disp_config_def plant_reset_tape_def)
  have rd_range: "?sym \<in> UNIV \<rightarrow> Raw ` \<Sigma>u \<union> Enc ` \<Gamma>_tm M"
    using bl_in le_in
    by (auto simp: mid_plant_disp_config_def plant_reset_tape_def plant_reset_pos_def
             split: nat.split)

  have tuple_in:
    "(W_Disp, ?sym, W_Run (s_tm M), ?sym, \<lambda>_. dir.N) \<in> wrap_delta M pack c \<Sigma>u"
  proof -
    have "(W_Disp, ?sym, W_Run (s_tm M), ?sym, \<lambda>_. dir.N)
            \<in> wrap_disp_delta_gen (k_tm M) M \<Sigma>u"
      unfolding wrap_disp_delta_gen_def
      using tail_bl rd_range by blast
    thus ?thesis by (simp add: wrap_delta_def)
  qed

  have step_holds:
    "(Config\<^sub>M W_Disp (mt_tape ?src) (mt_pos ?src),
      Config\<^sub>M (W_Run (s_tm M))
        (\<lambda>k. (mt_tape ?src k)((mt_pos ?src k) := ?sym k))
        (\<lambda>k. go_dir dir.N (mt_pos ?src k)))
     \<in> mttm_step (wrap_delta M pack c \<Sigma>u)"
    by (rule mttm_step.step
          [where ts = "mt_tape ?src" and n = "mt_pos ?src"
                 and a = ?sym and dir = "\<lambda>_. dir.N", OF tuple_in])

  have target_eq:
    "Config\<^sub>M (W_Run (s_tm M))
       (\<lambda>k. (mt_tape ?src k)((mt_pos ?src k) := ?sym k))
       (\<lambda>k. go_dir dir.N (mt_pos ?src k))
     = post_plant_dispatch_config M pack c w"
    by (simp add: post_plant_dispatch_config_def mid_plant_disp_config_def fun_eq_iff)

  from step_holds target_eq src_eq show ?thesis by simp
qed


subsection \<open>The reset reaches the floated engine configuration\<close>

text \<open>From @{const post_encoder_config_gen} the storage rewind, plant-done, and
  dispatch together reach the floated engine configuration
  @{const post_plant_dispatch_config} in @{term "Suc (length (wrap_enc pack c
  w)) + 2"} wrap-steps: @{term "Suc (length (wrap_enc pack c w))"} storage-rewind
  steps, the plant-done step, and the dispatch step.  Only the storage tape is
  walked; the input tape is left in place with a planted @{text le}.\<close>

lemma plant_reset_dispatch_relpow:
  assumes vM: "valid_mttm M"
      and c_pos: "0 < c"
      and w_alpha: "set w \<subseteq> \<Sigma>u"
      and bl_ne_le: "bl_tm M \<noteq> le_tm M"
      and k2: "2 \<le> k_tm M"
      and pack_in:
        "\<And>i. i * c < length w \<Longrightarrow> pack (take c (drop (i * c) w)) \<in> \<Gamma>_tm M"
      and pack_ne_le:
        "\<And>i. i * c < length w \<Longrightarrow> pack (take c (drop (i * c) w)) \<noteq> le_tm M"
    shows "(post_encoder_config_gen (k_tm M) M pack c w,
            post_plant_dispatch_config M pack c w)
           \<in> (mttm_step (wrap_delta M pack c \<Sigma>u))
               ^^ (Suc (length (wrap_enc pack c w)) + 2)"
proof -
  let ?R = "mttm_step (wrap_delta M pack c \<Sigma>u)"
  let ?L = "length (wrap_enc pack c w)"
  have loop: "(post_encoder_config_gen (k_tm M) M pack c w,
               mid_reset_combined_config_gen (k_tm M) M pack c w (length w + 1) 0)
                \<in> ?R ^^ (Suc ?L)"
    apply (rule plant_rewind_loop_relpow[OF vM c_pos w_alpha bl_ne_le k2])
     apply (fact pack_in)
    apply (fact pack_ne_le)
    done
  have done_step: "(mid_reset_combined_config_gen (k_tm M) M pack c w (length w + 1) 0,
                    mid_plant_disp_config M pack c w) \<in> ?R"
    by (rule plant_done_step[OF vM k2])
  have disp: "(mid_plant_disp_config M pack c w, post_plant_dispatch_config M pack c w)
                \<in> ?R"
    by (rule plant_disp_step[OF vM k2])

  from relpow_Suc_I[OF loop done_step]
  have "(post_encoder_config_gen (k_tm M) M pack c w, mid_plant_disp_config M pack c w)
          \<in> ?R ^^ Suc (Suc ?L)" .
  from relpow_Suc_I[OF this disp]
  have "(post_encoder_config_gen (k_tm M) M pack c w,
         post_plant_dispatch_config M pack c w) \<in> ?R ^^ Suc (Suc (Suc ?L))" .
  thus ?thesis by (simp add: numeral_2_eq_2)
qed

lemma plant_reset_dispatch_rtrancl:
  assumes vM: "valid_mttm M"
      and c_pos: "0 < c"
      and w_alpha: "set w \<subseteq> \<Sigma>u"
      and bl_ne_le: "bl_tm M \<noteq> le_tm M"
      and k2: "2 \<le> k_tm M"
      and pack_in:
        "\<And>i. i * c < length w \<Longrightarrow> pack (take c (drop (i * c) w)) \<in> \<Gamma>_tm M"
      and pack_ne_le:
        "\<And>i. i * c < length w \<Longrightarrow> pack (take c (drop (i * c) w)) \<noteq> le_tm M"
    shows "(post_encoder_config_gen (k_tm M) M pack c w,
            post_plant_dispatch_config M pack c w)
           \<in> (mttm_step (wrap_delta M pack c \<Sigma>u))\<^sup>*"
proof -
  have "(post_encoder_config_gen (k_tm M) M pack c w,
         post_plant_dispatch_config M pack c w)
          \<in> (mttm_step (wrap_delta M pack c \<Sigma>u))
              ^^ (Suc (length (wrap_enc pack c w)) + 2)"
    apply (rule plant_reset_dispatch_relpow[OF vM c_pos w_alpha bl_ne_le k2])
     apply (fact pack_in)
    apply (fact pack_ne_le)
    done
  thus ?thesis by (rule relpow_imp_rtrancl)
qed


subsection \<open>The floated config is a shift of the proper \<open>\<tau>\<close>-lift\<close>

text \<open>The floated engine configuration @{const post_plant_dispatch_config} is
  exactly a @{const shift_rel} of the @{text \<tau>}-lift of M's initial
  configuration on the encoded input, shifting \<^emph>\<open>only\<close> physical tape @{text 0}
  (M's tape @{text 1}) right by @{term "length w + 1"}: the planted @{text le}
  sits at the shifted origin, the spent raw input is the discarded prefix
  below it, and blanks lie above.  Every other physical tape (the storage tape
  @{text 1} = M's tape @{text 0}, carrying the encoded input, and the fresh
  work tapes @{text "2 \<dots> k-1"}) is unshifted (@{term "d p = 0"}), so it
  matches the lift verbatim.  This is the hinge: the origin-float lemmas of
  @{theory Multitape_TM_Substrate.Multitape_Origin_Float} translate runs between the two
  configs, and only physical tape @{text 0} needs @{text le} at its base
  origin --- which the lift supplies (M's blank tape @{text 1} has @{text le}
  at cell @{text 0}).\<close>

lemma post_plant_dispatch_shift_lift:
  assumes k2: "2 \<le> k_tm M"
  shows "shift_rel (\<lambda>p. if p = 0 then length w + 1 else 0)
           (lift_M_config M (init_config_mttm M (wrap_enc pack c w)))
           (post_plant_dispatch_config M pack c w)"
proof (cases M)
  case (MTTM Q \<Sigma>i \<Gamma> bl le \<delta> s t r kM)
  show ?thesis
    using k2
    unfolding shift_rel_def MTTM
              post_plant_dispatch_config_def plant_reset_tape_def plant_reset_pos_def
              lift_M_config_def
    by (auto simp: wrap_tau_def fun_eq_iff split: nat.split if_splits)
qed

end
