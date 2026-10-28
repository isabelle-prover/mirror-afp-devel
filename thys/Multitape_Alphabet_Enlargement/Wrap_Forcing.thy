theory Wrap_Forcing
  imports Wrap_Encoder
begin

section \<open>The wrap: forced steps\<close>

text \<open>The forward language inclusion needs that any \<^emph>\<open>accepting\<close> wrap-trace
  factors canonically through the encoder: the encoder / reset /
  dispatch transitions are \<^emph>\<open>forced\<close> (functional in
  \<open>(state, read-vector)\<close> regardless of M's nondeterminism), and only the
  @{const wrap_run_delta} portion follows M's @{text \<delta>}.

  The state-routing graph of @{const wrap_delta} is
  @{text "W_Init \<rightarrow> W_Buf \<rightarrow> W_Reset \<rightarrow> W_Disp \<rightarrow> W_Run"}; the families are the
  boundary-parameterised encoder families (@{term "k_ktm M"} via the
  @{text "_gen"} families), the reset, and the transposed run.  The
  reset's @{text le}-guards make a few routing / determinism closes
  need @{text "(auto split: if_splits)"}.\<close>


subsection \<open>State-routing exclusions and forward determinism\<close>

text \<open>Target-side exclusion for \<open>W_Run\<close> entry: if a wrap-tuple's target state
  is @{term "W_Run q'"} and its source is non-\<open>W_Run\<close>, only
  @{const wrap_disp_delta_gen} fires, forcing source @{text W_Disp} and target
  @{term "W_Run (s_ktm M)"}.  Every other non-\<open>W_Run\<close>-source family has a
  non-\<open>W_Run\<close> target.\<close>

lemma wrap_delta_W_Run_target_from_W_Disp:
  fixes M :: "('q, 'b) ktm"
    and sym :: "nat \<Rightarrow> ('a, 'b) wrap_alphabet"
    and a' :: "nat \<Rightarrow> ('a, 'b) wrap_alphabet"
    and move :: "nat \<Rightarrow> move"
  assumes tuple_in: "(q, sym, W_Run q', a', move) \<in> wrap_delta M pack c \<Sigma>u"
      and non_run_src: "\<forall>q\<^sub>M. q \<noteq> W_Run q\<^sub>M"
    shows "q = W_Disp \<and> q' = s_ktm M
           \<and> (q, sym, W_Run q', a', move) \<in> wrap_disp_delta_gen (k_ktm M) M \<Sigma>u"
  using tuple_in non_run_src
  unfolding wrap_delta_def
            wrap_init_delta_gen_def wrap_buf_extend_delta_gen_def
            wrap_buf_close_delta_gen_def wrap_buf_empty_end_delta_gen_def
            wrap_buf_nonempty_end_delta_gen_def
            wrap_rewind_loop_delta_gen_def
            wrap_plant_done_delta_def
            wrap_disp_delta_gen_def wrap_run_delta_def
  by auto

text \<open>Unconditional forward determinism in the non-\<open>W_Run\<close> portion of
  @{const wrap_delta}.  The
  @{text W_Reset} branch needs @{text "split: if_splits"} for the
  reset's @{text le}-guards (cf. @{thm[source] wrap_det}).\<close>

lemma wrap_delta_non_W_Run_det:
  assumes t1: "(q, a, p\<^sub>1, b\<^sub>1, d\<^sub>1) \<in> wrap_delta M pack c \<Sigma>u"
      and t2: "(q, a, p\<^sub>2, b\<^sub>2, d\<^sub>2) \<in> wrap_delta M pack c \<Sigma>u"
      and non_run: "\<forall>q\<^sub>M. q \<noteq> W_Run q\<^sub>M"
    shows "(p\<^sub>1, b\<^sub>1, d\<^sub>1) = (p\<^sub>2, b\<^sub>2, d\<^sub>2)"
proof (cases q)
  case W_Init
  with t1 t2 show ?thesis
    unfolding wrap_delta_def
              wrap_init_delta_gen_def wrap_buf_extend_delta_gen_def
              wrap_buf_close_delta_gen_def wrap_buf_empty_end_delta_gen_def
              wrap_buf_nonempty_end_delta_gen_def
              wrap_rewind_loop_delta_gen_def
              wrap_plant_done_delta_def
              wrap_disp_delta_gen_def wrap_run_delta_def
    by auto
next
  case (W_Buf ws)
  with t1 t2 show ?thesis
    unfolding wrap_delta_def
              wrap_init_delta_gen_def wrap_buf_extend_delta_gen_def
              wrap_buf_close_delta_gen_def wrap_buf_empty_end_delta_gen_def
              wrap_buf_nonempty_end_delta_gen_def
              wrap_rewind_loop_delta_gen_def
              wrap_plant_done_delta_def
              wrap_disp_delta_gen_def wrap_run_delta_def
    by auto
next
  case W_Reset
  with t1 t2 show ?thesis
    unfolding wrap_delta_def
              wrap_init_delta_gen_def wrap_buf_extend_delta_gen_def
              wrap_buf_close_delta_gen_def wrap_buf_empty_end_delta_gen_def
              wrap_buf_nonempty_end_delta_gen_def
              wrap_rewind_loop_delta_gen_def
              wrap_plant_done_delta_def
              wrap_disp_delta_gen_def wrap_run_delta_def
    by (auto split: if_splits)
next
  case W_Disp
  with t1 t2 show ?thesis
    unfolding wrap_delta_def
              wrap_init_delta_gen_def wrap_buf_extend_delta_gen_def
              wrap_buf_close_delta_gen_def wrap_buf_empty_end_delta_gen_def
              wrap_buf_nonempty_end_delta_gen_def
              wrap_rewind_loop_delta_gen_def
              wrap_plant_done_delta_def
              wrap_disp_delta_gen_def wrap_run_delta_def
    by auto
next
  case (W_Run q\<^sub>M)
  with non_run show ?thesis by blast
qed

text \<open>Once the wrap-state has the form @{term "W_Run q"}, every successor along
  the wrap rtrancl also has that form.  By
  @{thm[source] wrap_delta_W_Run_source_only_run}, any step out of
  @{text "W_Run q"} comes from @{const wrap_run_delta}, whose target is
  structurally @{text "W_Run q'"}.\<close>

lemma wrap_W_Run_persistent:
  assumes steps: "(C, C') \<in> (ktm_step (wrap_delta M pack c \<Sigma>u))\<^sup>*"
      and src:   "ktc_state C = W_Run q"
    shows "\<exists>q'. ktc_state C' = W_Run q'"
  using steps
proof induction
  case base
  show ?case using src by blast
next
  case (step y z)
  from step.IH obtain qy where qy: "ktc_state y = W_Run qy" by blast
  obtain y_q ts n where y_decomp: "y = KConfig y_q ts n"
    by (cases y)
  with qy have y_eq: "y = KConfig (W_Run qy) ts n" by simp
  from step.hyps(2) y_eq
  obtain qs' a' dir' where
      tuple_in: "(W_Run qy, \<lambda>k. ts k (n k), qs', a', dir')
                   \<in> wrap_delta M pack c \<Sigma>u"
    and z_eq: "z = KConfig qs' (\<lambda>k. (ts k)(n k := a' k))
                                 (\<lambda>k. go_move (dir' k) (n k))"
    by (auto elim: ktm_step.cases)
  from wrap_delta_W_Run_source_only_run[OF tuple_in]
  have "(W_Run qy, \<lambda>k. ts k (n k), qs', a', dir')
          \<in> wrap_run_delta M \<Sigma>u" .
  hence "\<exists>q'. qs' = W_Run q'"
    unfolding wrap_run_delta_def by auto
  thus ?case using z_eq by auto
qed

text \<open>Symmetric routing exclusion at the @{term W_Disp} source: only
  @{const wrap_disp_delta_gen} sources from @{term W_Disp}.\<close>

lemma wrap_delta_W_Disp_source_only_disp:
  fixes M :: "('q, 'b) ktm"
    and inp :: "nat \<Rightarrow> ('a, 'b) wrap_alphabet"
    and qs' :: "('q, 'a, 'b) wrap_state"
    and a' :: "nat \<Rightarrow> ('a, 'b) wrap_alphabet"
    and move :: "nat \<Rightarrow> move"
  assumes "(W_Disp, inp, qs', a', move) \<in> wrap_delta M pack c \<Sigma>u"
  shows "(W_Disp, inp, qs', a', move) \<in> wrap_disp_delta_gen (k_ktm M) M \<Sigma>u"
  using assms
  unfolding wrap_delta_def
            wrap_init_delta_gen_def wrap_buf_extend_delta_gen_def
            wrap_buf_close_delta_gen_def wrap_buf_empty_end_delta_gen_def
            wrap_buf_nonempty_end_delta_gen_def
            wrap_rewind_loop_delta_gen_def
            wrap_plant_done_delta_def
            wrap_run_delta_def
  by auto

text \<open>Any wrap-step from a @{term W_Disp} config lands in
  @{term "W_Run (s_ktm M)"}.\<close>

lemma wrap_step_W_Disp_to_W_Run:
  fixes M :: "('q, 'b) ktm"
  assumes step: "(C, C') \<in> ktm_step (wrap_delta M pack c \<Sigma>u)"
      and src:  "ktc_state C = W_Disp"
    shows "ktc_state C' = W_Run (s_ktm M)"
proof -
  obtain c_q ts n where c_decomp: "C = KConfig c_q ts n"
    by (cases C)
  with src have c_eq: "C = KConfig W_Disp ts n" by simp
  from step c_eq obtain qs' a' dir' where
      tuple_in: "(W_Disp, \<lambda>k. ts k (n k), qs', a', dir')
                   \<in> wrap_delta M pack c \<Sigma>u"
    and dst_eq: "C' = KConfig qs' (\<lambda>k. (ts k)(n k := a' k))
                                   (\<lambda>k. go_move (dir' k) (n k))"
    by (auto elim: ktm_step.cases)
  from wrap_delta_W_Disp_source_only_disp[OF tuple_in]
  have "(W_Disp, \<lambda>k. ts k (n k), qs', a', dir')
          \<in> wrap_disp_delta_gen (k_ktm M) M \<Sigma>u" .
  hence "qs' = W_Run (s_ktm M)"
    unfolding wrap_disp_delta_gen_def by auto
  with dst_eq show ?thesis by simp
qed

text \<open>Any non-empty wrap-trace from a @{term W_Disp} config ends in
  @{term W_Run}: one step into @{term W_Run} then
  @{thm[source] wrap_W_Run_persistent}.\<close>

lemma wrap_W_Disp_then_W_Run:
  fixes M :: "('q, 'b) ktm"
  assumes path: "(C, C') \<in> (ktm_step (wrap_delta M pack c \<Sigma>u)) ^^ n"
      and src:  "ktc_state C = W_Disp"
      and n_pos: "0 < n"
    shows "\<exists>q. ktc_state C' = W_Run q"
proof -
  from n_pos obtain m where n_eq: "n = Suc m"
    by (cases n) auto
  from path n_eq have path_Suc:
    "(C, C') \<in> (ktm_step (wrap_delta M pack c \<Sigma>u)) ^^ Suc m"
    by simp
  from path_Suc obtain Y where
      first_step: "(C, Y) \<in> ktm_step (wrap_delta M pack c \<Sigma>u)"
    and rest: "(Y, C') \<in> (ktm_step (wrap_delta M pack c \<Sigma>u)) ^^ m"
    by (rule relpow_Suc_E2)
  from wrap_step_W_Disp_to_W_Run[OF first_step src]
  have Y_run: "ktc_state Y = W_Run (s_ktm M)" .
  from rest have rest_rt: "(Y, C') \<in> (ktm_step (wrap_delta M pack c \<Sigma>u))\<^sup>*"
    by (rule relpow_imp_rtrancl)
  from wrap_W_Run_persistent[OF rest_rt Y_run]
  show ?thesis .
qed

text \<open>Structural decomposition of an accepting wrap-trace at the first entry
  into the @{term W_Run} phase.  Purely structural — no forward determinism or
  pack contracts.\<close>

lemma wrap_first_W_Run_decomp:
  fixes M :: "('q, 'b) ktm"
  assumes trace: "(init_config_ktm (encoding_wrap M pack c \<Sigma>u) (map Raw w), C_acc)
                    \<in> (ktm_step (wrap_delta M pack c \<Sigma>u))\<^sup>*"
      and accept: "\<exists>q. ktc_state C_acc = W_Run q"
  shows "\<exists>C_pre C_post.
            (init_config_ktm (encoding_wrap M pack c \<Sigma>u) (map Raw w), C_pre)
              \<in> (ktm_step (wrap_delta M pack c \<Sigma>u))\<^sup>*
          \<and> ktc_state C_pre = W_Disp
          \<and> (C_pre, C_post) \<in> ktm_step (wrap_delta M pack c \<Sigma>u)
          \<and> ktc_state C_post = W_Run (s_ktm M)
          \<and> (C_post, C_acc) \<in> (ktm_step (wrap_delta M pack c \<Sigma>u))\<^sup>*"
proof -
  let ?init_W = "init_config_ktm (encoding_wrap M pack c \<Sigma>u) (map Raw w)"
  let ?R = "ktm_step (wrap_delta M pack c \<Sigma>u)"
  have init_state: "ktc_state ?init_W = W_Init" by simp
  from trace obtain n where pow: "(?init_W, C_acc) \<in> ?R ^^ n"
    using rtrancl_imp_relpow by metis
  from pow accept
  show ?thesis
  proof (induction n arbitrary: C_acc)
    case 0
    from "0.prems"(1) have C_eq: "C_acc = ?init_W" by simp
    from "0.prems"(2) C_eq init_state show ?case by auto
  next
    case (Suc m)
    from Suc.prems(1) obtain y where
        prefix: "(?init_W, y) \<in> ?R ^^ m"
      and last_step: "(y, C_acc) \<in> ?R"
      by (auto elim: relpow_Suc_E)
    show ?case
    proof (cases "\<exists>q. ktc_state y = W_Run q")
      case True
      from Suc.IH[OF prefix True] obtain C_pre C_post where
          dec: "(?init_W, C_pre) \<in> ?R\<^sup>*"
               "ktc_state C_pre = W_Disp"
               "(C_pre, C_post) \<in> ?R"
               "ktc_state C_post = W_Run (s_ktm M)"
               "(C_post, y) \<in> ?R\<^sup>*"
        by blast
      from dec(5) last_step have "(C_post, C_acc) \<in> ?R\<^sup>*"
        by (rule rtrancl_into_rtrancl)
      with dec(1-4) show ?thesis by blast
    next
      case False
      obtain y_q y_ts y_n where y_eq: "y = KConfig y_q y_ts y_n"
        by (cases y)
      from Suc.prems(2) obtain q_acc where
          acc_state: "ktc_state C_acc = W_Run q_acc" by blast
      obtain Cq Cts Cn where C_eq: "C_acc = KConfig Cq Cts Cn"
        by (cases C_acc)
      with acc_state have C_q_eq: "Cq = W_Run q_acc" by simp
      from last_step y_eq C_eq obtain a' dir' where
          tuple_in: "(y_q, \<lambda>k. y_ts k (y_n k), Cq, a', dir')
                       \<in> wrap_delta M pack c \<Sigma>u"
        by (auto elim: ktm_step.cases)
      with C_q_eq have tuple_W_Run:
          "(y_q, \<lambda>k. y_ts k (y_n k), W_Run q_acc, a', dir')
             \<in> wrap_delta M pack c \<Sigma>u"
        by simp
      have non_run_y: "\<forall>q\<^sub>M. y_q \<noteq> W_Run q\<^sub>M"
      proof (intro allI notI)
        fix q\<^sub>M assume "y_q = W_Run q\<^sub>M"
        hence "ktc_state y = W_Run q\<^sub>M" using y_eq by simp
        with False show False by blast
      qed
      from wrap_delta_W_Run_target_from_W_Disp[OF tuple_W_Run non_run_y]
      have y_W_Disp: "y_q = W_Disp"
       and q_acc_s: "q_acc = s_ktm M"
        by auto
      have y_state: "ktc_state y = W_Disp" using y_eq y_W_Disp by simp
      have C_state: "ktc_state C_acc = W_Run (s_ktm M)"
        using acc_state q_acc_s by simp
      from prefix have prefix_rt: "(?init_W, y) \<in> ?R\<^sup>*"
        by (rule relpow_imp_rtrancl)
      have refl_C: "(C_acc, C_acc) \<in> ?R\<^sup>*" by simp
      from prefix_rt y_state last_step C_state refl_C show ?thesis by blast
    qed
  qed
qed

text \<open>Single-step forward determinism from a non-@{term W_Run} source: lifts
  @{thm[source] wrap_delta_non_W_Run_det} to @{term ktm_step} target-config
  uniqueness.\<close>

lemma wrap_step_unique_non_run:
  assumes step1: "(C, C1) \<in> ktm_step (wrap_delta M pack c \<Sigma>u)"
      and step2: "(C, C2) \<in> ktm_step (wrap_delta M pack c \<Sigma>u)"
      and non_run: "\<forall>q\<^sub>M. ktc_state C \<noteq> W_Run q\<^sub>M"
    shows "C1 = C2"
proof -
  obtain Cq Cts Cn where C_eq: "C = KConfig Cq Cts Cn" by (cases C)
  from C_eq non_run have non_run_q: "\<forall>q\<^sub>M. Cq \<noteq> W_Run q\<^sub>M" by simp
  from step1 C_eq obtain qs1' a1' dir1' where
      tuple1: "(Cq, \<lambda>k. Cts k (Cn k), qs1', a1', dir1') \<in> wrap_delta M pack c \<Sigma>u"
    and C1_eq: "C1 = KConfig qs1'
                  (\<lambda>k. (Cts k)(Cn k := a1' k))
                  (\<lambda>k. go_move (dir1' k) (Cn k))"
    by (auto elim: ktm_step.cases)
  from step2 C_eq obtain qs2' a2' dir2' where
      tuple2: "(Cq, \<lambda>k. Cts k (Cn k), qs2', a2', dir2') \<in> wrap_delta M pack c \<Sigma>u"
    and C2_eq: "C2 = KConfig qs2'
                  (\<lambda>k. (Cts k)(Cn k := a2' k))
                  (\<lambda>k. go_move (dir2' k) (Cn k))"
    by (auto elim: ktm_step.cases)
  from wrap_delta_non_W_Run_det[OF tuple1 tuple2 non_run_q]
  have tuple_eq: "(qs1', a1', dir1') = (qs2', a2', dir2')" .
  show ?thesis using C1_eq C2_eq tuple_eq by simp
qed

text \<open>Two runs of the same length from the same configuration agree when
  the relation is single-valued at every configuration satisfying \<open>G\<close>,
  \<open>G\<close> propagates backwards along a step, and the first run ends in a
  configuration satisfying \<open>G\<close>.  For the wrap and its patch, \<open>G\<close> says that
  the run has not yet entered the simulation phase.\<close>

lemma relpow_forced:
  assumes unique: "\<And>x y z. (x, y) \<in> R \<Longrightarrow> (x, z) \<in> R \<Longrightarrow> G x \<Longrightarrow> y = z"
      and backward: "\<And>x y. (x, y) \<in> R \<Longrightarrow> G y \<Longrightarrow> G x"
      and one: "(a, b) \<in> R ^^ n" and two: "(a, c) \<in> R ^^ n"
      and good: "G b"
  shows "b = c"
  using one two good
proof (induction n arbitrary: b c)
  case 0
  then show ?case by simp
next
  case (Suc n)
  obtain b' where b1: "(a, b') \<in> R ^^ n" and b2: "(b', b) \<in> R"
    using Suc.prems(1) by (rule relpow_Suc_E)
  obtain c' where c1: "(a, c') \<in> R ^^ n" and c2: "(c', c) \<in> R"
    using Suc.prems(2) by (rule relpow_Suc_E)
  have gb': "G b'" by (rule backward[OF b2 Suc.prems(3)])
  have "b' = c'" by (rule Suc.IH[OF b1 c1 gb'])
  then show ?case using unique[OF b2 _ gb'] c2 by simp
qed

lemma wrap_step_back_non_run:
  assumes step: "(x, y) \<in> ktm_step (wrap_delta M pack c \<Sigma>u)"
      and later: "\<forall>q. ktc_state y \<noteq> W_Run q"
  shows "\<forall>q. ktc_state x \<noteq> W_Run q"
proof (intro allI notI)
  fix q assume "ktc_state x = W_Run q"
  then obtain q' where "ktc_state y = W_Run q'"
    using wrap_W_Run_persistent[OF r_into_rtrancl[OF step]] by blast
  with later show False by simp
qed

text \<open>Iterated forward determinism: two same-length wrap-traces from a
  common source coincide when the first ends outside the
  @{term W_Run} phase.  Its intermediates are then outside that phase as
  well, by @{thm[source] wrap_W_Run_persistent}, so the second trace is
  forced step by step.\<close>

lemma wrap_path_det_non_run:
  fixes M :: "('q, 'b) ktm"
  assumes path1: "(C0, C1) \<in> (ktm_step (wrap_delta M pack c \<Sigma>u)) ^^ n"
      and path2: "(C0, C2) \<in> (ktm_step (wrap_delta M pack c \<Sigma>u)) ^^ n"
      and non_run_C1: "\<forall>q\<^sub>M. ktc_state C1 \<noteq> W_Run q\<^sub>M"
    shows "C1 = C2"
  by (rule relpow_forced[where G = "\<lambda>C. \<forall>q. ktc_state C \<noteq> W_Run q",
        OF wrap_step_unique_non_run wrap_step_back_non_run path1 path2 non_run_C1])


subsection \<open>Pack-contract forcing\<close>

text \<open>Wrap-tuple family identification at full-buffer close: a @{const W_Buf}
  source with @{prop "length ws + 1 = c"} reading @{term "Raw a"} on the
  user-tape fires only @{const wrap_buf_close_delta_gen}.\<close>

lemma wrap_delta_full_buf_in_close:
  fixes M :: "('q, 'b) ktm"
    and inp :: "nat \<Rightarrow> ('a, 'b) wrap_alphabet"
    and a' :: "nat \<Rightarrow> ('a, 'b) wrap_alphabet"
    and dir' :: "nat \<Rightarrow> move"
  assumes tuple_in: "(W_Buf ws, inp, qs', a', dir') \<in> wrap_delta M pack c \<Sigma>u"
      and ws_full: "length ws + 1 = c"
      and inp_W_User_Raw: "inp 0 = Raw a"
    shows "(W_Buf ws, inp, qs', a', dir') \<in> wrap_buf_close_delta_gen (k_ktm M) M pack c \<Sigma>u"
  using tuple_in ws_full inp_W_User_Raw
  unfolding wrap_delta_def
            wrap_init_delta_gen_def wrap_buf_extend_delta_gen_def
            wrap_buf_empty_end_delta_gen_def wrap_buf_nonempty_end_delta_gen_def
            wrap_rewind_loop_delta_gen_def
            wrap_plant_done_delta_def
            wrap_disp_delta_gen_def wrap_run_delta_def
  by auto

text \<open>Family identification at the partial-block end-of-input point: a
  @{const W_Buf} source with non-empty partial buffer reading
  @{term "Enc (bl_ktm M)"} fires only @{const wrap_buf_nonempty_end_delta_gen}.\<close>

lemma wrap_delta_partial_buf_in_nonempty_end:
  fixes M :: "('q, 'b) ktm"
    and inp :: "nat \<Rightarrow> ('a, 'b) wrap_alphabet"
    and a' :: "nat \<Rightarrow> ('a, 'b) wrap_alphabet"
    and dir' :: "nat \<Rightarrow> move"
  assumes tuple_in: "(W_Buf ws, inp, qs', a', dir') \<in> wrap_delta M pack c \<Sigma>u"
      and ws_partial: "length ws < c"
      and ws_nonempty: "ws \<noteq> []"
      and inp_W_User_bl: "inp 0 = Enc (bl_ktm M)"
    shows "(W_Buf ws, inp, qs', a', dir') \<in> wrap_buf_nonempty_end_delta_gen (k_ktm M) M pack c \<Sigma>u"
  using tuple_in ws_partial ws_nonempty inp_W_User_bl
  unfolding wrap_delta_def
            wrap_init_delta_gen_def wrap_buf_extend_delta_gen_def
            wrap_buf_close_delta_gen_def wrap_buf_empty_end_delta_gen_def
            wrap_rewind_loop_delta_gen_def
            wrap_plant_done_delta_def
            wrap_disp_delta_gen_def wrap_run_delta_def
  by auto

text \<open>Forward forcing of the close-step at a full block boundary.  At
  @{term "mid_buf_extending_config_gen (k_ktm M) M pack c w i (c - 1)"} with
  @{prop "(Suc i) * c \<le> length w"}, any firing wrap-step forces both the pack
  contract @{prop "pack (take c (drop (i * c) w)) \<in> Sigma_ktm M"} and the
  successor identity @{term "mid_encoder_config_gen (k_ktm M) M pack c w (Suc i)"}.
  The canonical step is @{thm[source] mid_buf_close_step} (needs
  @{term "2 \<le> k_ktm M"}).\<close>

lemma wrap_close_step_forces_pack:
  fixes M :: "('q, 'b) ktm"
  assumes vM: "valid_ktm M"
      and c_pos: "0 < c"
      and w_alpha: "set w \<subseteq> \<Sigma>u"
      and block_full: "(Suc i) * c \<le> length w"
      and bl_ne_le: "bl_ktm M \<noteq> le_ktm M"
      and k2: "2 \<le> k_ktm M"
      and step: "(mid_buf_extending_config_gen (k_ktm M) M pack c w i (c - 1), C')
                    \<in> ktm_step (wrap_delta M pack c \<Sigma>u)"
    shows "pack (take c (drop (i * c) w)) \<in> Sigma_ktm M
        \<and> C' = mid_encoder_config_gen (k_ktm M) M pack c w (Suc i)"
proof -
  define cm where "cm = c - 1"
  let ?src = "mid_buf_extending_config_gen (k_ktm M) M pack c w i cm"
  let ?ws = "take cm (drop (i * c) w)"
  let ?aa = "w ! (i * c + cm)"
  let ?packed = "pack (take c (drop (i * c) w))"
  let ?inp = "\<lambda>k. ktc_tape ?src k (ktc_pos ?src k)"

  from c_pos have c_succ: "Suc cm = c" unfolding cm_def by simp
  from block_full have full_block_form: "i * c + c \<le> length w" by simp
  from full_block_form c_pos have a_idx: "i * c + cm < length w"
    unfolding cm_def by linarith
  have ws_lt_drop: "cm < length (drop (i * c) w)" using a_idx by simp
  have len_ws: "length ?ws = cm" using ws_lt_drop by simp
  have len_ws_plus_one: "length ?ws + 1 = c"
    using len_ws c_succ by simp
  have take_app: "?ws @ [?aa] = take c (drop (i * c) w)"
  proof -
    have "take c (drop (i * c) w) = take (Suc cm) (drop (i * c) w)"
      using c_succ by simp
    also have "\<dots> = take cm (drop (i * c) w) @ [drop (i * c) w ! cm]"
      using ws_lt_drop by (simp add: take_Suc_conv_app_nth)
    also have "drop (i * c) w ! cm = w ! (i * c + cm)"
      using a_idx by simp
    finally show ?thesis by simp
  qed

  have k_pos: "0 < k_ktm M" using k2 by simp
  have src_state: "ktc_state ?src = W_Buf ?ws"
    by (simp add: mid_buf_extending_config_gen_def)
  have src_pos: "ktc_pos ?src
       = (\<lambda>t. case t of 0 \<Rightarrow> 1 + i * c + cm
                       | Suc k \<Rightarrow> (if k = 0 then 1 + i else 0))"
    by (simp add: mid_buf_extending_config_gen_def fun_eq_iff)
  have src_tape: "ktc_tape ?src
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
  have read_W_User: "?inp 0 = Raw ?aa"
    using a_idx k_pos by (simp add: src_tape src_pos)

  have src_decomp: "?src = KConfig (W_Buf ?ws) (ktc_tape ?src) (ktc_pos ?src)"
    using src_state src_pos src_tape by (cases ?src) simp

  have step_src: "(?src, C') \<in> ktm_step (wrap_delta M pack c \<Sigma>u)"
    using step unfolding cm_def by simp
  from step_src src_decomp obtain qs' a' dir' where
      C'_step: "C' = KConfig qs'
                    (\<lambda>k. (ktc_tape ?src k)(ktc_pos ?src k := a' k))
                    (\<lambda>k. go_move (dir' k) (ktc_pos ?src k))"
    and tuple_in: "(W_Buf ?ws, ?inp, qs', a', dir') \<in> wrap_delta M pack c \<Sigma>u"
    by (auto elim: ktm_step.cases)

  from wrap_delta_full_buf_in_close[OF tuple_in len_ws_plus_one read_W_User]
  have tuple_close:
    "(W_Buf ?ws, ?inp, qs', a', dir') \<in> wrap_buf_close_delta_gen (k_ktm M) M pack c \<Sigma>u" .

  from tuple_close obtain ws_x a_x inp_x where
      close_eq: "(W_Buf ?ws, ?inp, qs', a', dir')
                  = (W_Buf ws_x, inp_x, W_Buf [],
                     (\<lambda>t. case t of Suc k \<Rightarrow> if k = 0 then Enc (pack (ws_x @ [a_x]))
                                              else inp_x (Suc k)
                                  | 0 \<Rightarrow> inp_x 0),
                     \<lambda>t. case t of 0 \<Rightarrow> MoveR
                                  | Suc k \<Rightarrow> if k = 0 then MoveR else MoveN)"
    and close_inp_W_User: "inp_x 0 = Raw a_x"
    and close_pack: "pack (ws_x @ [a_x]) \<in> Sigma_ktm M"
    unfolding wrap_buf_close_delta_gen_def by blast

  have ws_eq: "?ws = ws_x" using close_eq by simp
  have inp_eq: "?inp = inp_x" using close_eq by simp
  have a_eq: "?aa = a_x"
  proof -
    from inp_eq have inp_at_User: "?inp 0 = inp_x 0"
      by (rule fun_cong)
    from read_W_User inp_at_User close_inp_W_User
    have "Raw ?aa = Raw a_x" by simp
    thus ?thesis by simp
  qed
  have pack_in: "?packed \<in> Sigma_ktm M"
    using close_pack ws_eq a_eq take_app by simp

  have canonical:
    "(mid_buf_extending_config_gen (k_ktm M) M pack c w i (c - 1),
      mid_encoder_config_gen (k_ktm M) M pack c w (Suc i))
       \<in> ktm_step (wrap_delta M pack c \<Sigma>u)"
    by (rule mid_buf_close_step[where pack = pack,
              OF vM c_pos w_alpha block_full pack_in bl_ne_le k2])
  have non_run_src:
    "\<forall>q\<^sub>M. ktc_state (mid_buf_extending_config_gen (k_ktm M) M pack c w i (c - 1)) \<noteq> W_Run q\<^sub>M"
    by (simp add: mid_buf_extending_config_gen_def)
  from wrap_step_unique_non_run[OF step canonical non_run_src]
  have C'_eq_final: "C' = mid_encoder_config_gen (k_ktm M) M pack c w (Suc i)" .

  from pack_in C'_eq_final show ?thesis by simp
qed

text \<open>Forward forcing of the partial close-step at end-of-input.  At
  @{term "mid_buf_extending_config_gen (k_ktm M) M pack c w i (length w - i * c)"}
  with @{term i} the partial block index, any firing wrap-step forces the pack
  contract and the successor identity @{term "post_encoder_config_gen (k_ktm M) M pack c w"}.
  The successor is computed explicitly (no single-step canonical lemma to the
  partial close) and needs @{term "2 \<le> k_ktm M"} for the tape-@{text 1} write
  to land in range.\<close>

lemma wrap_partial_close_step_forces_pack:
  fixes M :: "('q, 'b) ktm"
    and i :: nat
  assumes vM: "valid_ktm M"
      and c_pos: "0 < c"
      and w_alpha: "set w \<subseteq> \<Sigma>u"
      and bl_ne_le: "bl_ktm M \<noteq> le_ktm M"
      and k2: "2 \<le> k_ktm M"
      and i_lt: "i * c < length w"
      and i_partial: "length w < (Suc i) * c"
      and i_div: "i = length w div c"
      and step: "(mid_buf_extending_config_gen (k_ktm M) M pack c w i (length w - i * c), C')
                    \<in> ktm_step (wrap_delta M pack c \<Sigma>u)"
    shows "pack (take c (drop (i * c) w)) \<in> Sigma_ktm M
        \<and> C' = post_encoder_config_gen (k_ktm M) M pack c w"
proof -
  define kp where "kp = length w - i * c"
  let ?src = "mid_buf_extending_config_gen (k_ktm M) M pack c w i kp"
  let ?tail = "drop (i * c) w"
  let ?inp = "\<lambda>k. ktc_tape ?src k (ktc_pos ?src k)"

  from i_lt have kp_pos: "0 < kp" unfolding kp_def by simp
  from i_partial have len_lt: "length w < c + i * c" by simp
  from i_lt len_lt have kp_lt_c: "kp < c"
    unfolding kp_def by linarith
  have ic_plus_kp: "i * c + kp = length w"
    using i_lt unfolding kp_def by simp
  have r_eq: "length w mod c = kp"
  proof -
    have "length w = (length w div c) * c + length w mod c"
      by (simp add: div_mult_mod_eq)
    with i_div have "length w = i * c + length w mod c" by simp
    thus "length w mod c = kp" unfolding kp_def by linarith
  qed
  have r_pos: "length w mod c \<noteq> 0"
    using r_eq kp_pos by simp
  have tail_len: "length ?tail = kp"
    using ic_plus_kp by simp
  have take_kp: "take kp ?tail = ?tail"
    using tail_len by simp
  have take_c_eq: "take c ?tail = ?tail"
    using tail_len kp_lt_c by simp
  have pack_eq: "pack (take c ?tail) = pack ?tail"
    using take_c_eq by simp

  have len_wenc: "length (wrap_enc pack c w) = i + 1"
    using length_wrap_enc[OF c_pos, of pack w] r_pos i_div by simp
  have wenc_q_eq: "wrap_enc pack c w ! i = pack ?tail"
    using wrap_enc_nth_partial[OF c_pos r_pos] i_div by simp
  have k_pos: "0 < k_ktm M" using k2 by simp

  have buf_take_kp: "take kp (drop (i * c) w) = ?tail"
    using take_kp by simp
  have src_state: "ktc_state ?src = W_Buf ?tail"
    using buf_take_kp by (simp add: mid_buf_extending_config_gen_def)
  have src_pos: "ktc_pos ?src
       = (\<lambda>t. case t of 0 \<Rightarrow> 1 + i * c + kp
                       | Suc k \<Rightarrow> (if k = 0 then 1 + i else 0))"
    by (simp add: mid_buf_extending_config_gen_def fun_eq_iff)
  have src_tape: "ktc_tape ?src
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
  have read_W_User: "?inp 0 = Enc (bl_ktm M)"
    using ic_plus_kp k_pos by (simp add: src_tape src_pos)

  have src_decomp: "?src = KConfig (W_Buf ?tail) (ktc_tape ?src) (ktc_pos ?src)"
    using src_state src_pos src_tape by (cases ?src) simp

  have step_src: "(?src, C') \<in> ktm_step (wrap_delta M pack c \<Sigma>u)"
    using step unfolding kp_def by simp
  from step_src src_decomp obtain qs' a' dir' where
      C'_step: "C' = KConfig qs'
                    (\<lambda>k. (ktc_tape ?src k)(ktc_pos ?src k := a' k))
                    (\<lambda>k. go_move (dir' k) (ktc_pos ?src k))"
    and tuple_in: "(W_Buf ?tail, ?inp, qs', a', dir') \<in> wrap_delta M pack c \<Sigma>u"
    by (auto elim: ktm_step.cases)

  have tail_nonempty: "?tail \<noteq> []"
    using tail_len kp_pos by (cases ?tail) auto
  have tail_lt_c: "length ?tail < c"
    using tail_len kp_lt_c by simp
  from wrap_delta_partial_buf_in_nonempty_end
        [OF tuple_in tail_lt_c tail_nonempty read_W_User]
  have tuple_neEnd:
    "(W_Buf ?tail, ?inp, qs', a', dir') \<in> wrap_buf_nonempty_end_delta_gen (k_ktm M) M pack c \<Sigma>u" .

  from tuple_neEnd obtain ws_x inp_x where
      neEnd_eq: "(W_Buf ?tail, ?inp, qs', a', dir')
                  = (W_Buf ws_x, inp_x, W_Reset,
                     (\<lambda>t. case t of Suc k \<Rightarrow> if k = 0 then Enc (pack ws_x)
                                              else inp_x (Suc k)
                                  | 0 \<Rightarrow> inp_x 0),
                     \<lambda>t. case t of Suc k \<Rightarrow> if k = 0 then MoveR else MoveN
                                  | 0 \<Rightarrow> MoveN)"
    and neEnd_pack: "pack ws_x \<in> Sigma_ktm M"
    unfolding wrap_buf_nonempty_end_delta_gen_def by blast
  have ws_eq: "?tail = ws_x" using neEnd_eq by simp
  have inp_eq: "?inp = inp_x" using neEnd_eq by simp
  have qs'_eq: "qs' = W_Reset" using neEnd_eq by simp
  have a'_eq:
    "a' = (\<lambda>t. case t of Suc k \<Rightarrow> if k = 0 then Enc (pack ws_x)
                                  else inp_x (Suc k)
                      | 0 \<Rightarrow> inp_x 0)"
    using neEnd_eq by simp
  have dir'_eq:
    "dir' = (\<lambda>t. case t of Suc k \<Rightarrow> if k = 0 then MoveR else MoveN
                         | 0 \<Rightarrow> MoveN)"
    using neEnd_eq by simp
  have pack_tail_in: "pack ?tail \<in> Sigma_ktm M"
    using neEnd_pack ws_eq by simp
  have pack_in: "pack (take c (drop (i * c) w)) \<in> Sigma_ktm M"
    using pack_tail_in pack_eq by simp

  have a'_concrete:
    "a' = (\<lambda>t. case t of 0 \<Rightarrow> ?inp 0
                       | Suc k \<Rightarrow> if k = 0 then Enc (pack ?tail)
                                  else ?inp (Suc k))"
    using a'_eq ws_eq inp_eq by (auto simp: fun_eq_iff split: nat.split)
  have C'_concrete:
    "C' = KConfig W_Reset
            (\<lambda>k. (ktc_tape ?src k)
                  ((ktc_pos ?src k) :=
                     (case k of
                        0 \<Rightarrow> ?inp 0
                      | Suc k' \<Rightarrow> if k' = 0 then Enc (pack ?tail)
                                  else ?inp (Suc k'))))
            (\<lambda>k. go_move
                  ((\<lambda>t. case t of 0 \<Rightarrow> MoveN
                                | Suc k' \<Rightarrow> if k' = 0 then MoveR else MoveN) k)
                  (ktc_pos ?src k))"
    using C'_step qs'_eq a'_concrete dir'_eq
    by (auto simp: fun_eq_iff split: nat.split)

  have target_eq:
    "KConfig W_Reset
       (\<lambda>k. (ktc_tape ?src k)
             ((ktc_pos ?src k) :=
                (case k of
                   0 \<Rightarrow> ?inp 0
                 | Suc k' \<Rightarrow> if k' = 0 then Enc (pack ?tail)
                             else ?inp (Suc k'))))
       (\<lambda>k. go_move
             ((\<lambda>t. case t of 0 \<Rightarrow> MoveN
                           | Suc k' \<Rightarrow> if k' = 0 then MoveR else MoveN) k)
             (ktc_pos ?src k))
     = post_encoder_config_gen (k_ktm M) M pack c w"
    unfolding post_encoder_config_gen_def
    using ic_plus_kp len_wenc wenc_q_eq r_pos k2 valid_ktm_k_pos[OF vM]
    by (auto simp: src_pos src_tape fun_eq_iff
             split: nat.split if_splits)

  from C'_concrete target_eq pack_in
  show ?thesis by simp
qed
end
