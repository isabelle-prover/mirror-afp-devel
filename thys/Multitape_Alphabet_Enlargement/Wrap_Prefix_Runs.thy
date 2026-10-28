theory Wrap_Prefix_Runs
  imports Wrap_Prefix_Patch
begin

section \<open>Runs of the patched wrap\<close>

text \<open>The patched wrap's first steps are its encoder's, forced because the
  encoder is deterministic; the runs below are the canonical ones, and
  \<open>relpow_forced_split\<close> below says every other run of the wrap or of
  its patch agrees with them.  None of the arguments assumes the
  simulated machine deterministic.\<close>

subsection \<open>Forced splitting\<close>

lemma relpow_backward:
  assumes backward: "\<And>x y. (x, y) \<in> R \<Longrightarrow> G y \<Longrightarrow> G x"
      and run: "(a, b) \<in> R ^^ n" and good: "G b"
  shows "G a"
  using run good
proof (induction n arbitrary: b)
  case 0
  then show ?case by simp
next
  case (Suc n)
  obtain b' where "(a, b') \<in> R ^^ n" and "(b', b) \<in> R"
    using Suc.prems(1) by (rule relpow_Suc_E)
  then show ?case using Suc.IH backward Suc.prems(2) by blast
qed

text \<open>Against a run that is good at step \<open>p\<close>, a run of length \<open>n\<close> from
  the same configuration either passes through that point, or stops
  short of it while still good.\<close>

lemma relpow_forced_split:
  assumes unique: "\<And>x y z. (x, y) \<in> R \<Longrightarrow> (x, z) \<in> R \<Longrightarrow> G x \<Longrightarrow> y = z"
      and backward: "\<And>x y. (x, y) \<in> R \<Longrightarrow> G y \<Longrightarrow> G x"
      and one: "(a, b) \<in> R ^^ p" and good: "G b"
      and two: "(a, c) \<in> R ^^ n"
  shows "p \<le> n \<and> (b, c) \<in> R ^^ (n - p) \<or> n < p \<and> G c"
proof (cases "p \<le> n")
  case True
  have "(a, c) \<in> R ^^ (p + (n - p))" using two True by simp
  then obtain x where ax: "(a, x) \<in> R ^^ p" and xc: "(x, c) \<in> R ^^ (n - p)"
    unfolding relpow_add by blast
  have "b = x" by (rule relpow_forced[where R=R and G=G, OF unique backward one ax good])
  then show ?thesis using True xc by simp
next
  case False
  have "(a, b) \<in> R ^^ (n + (p - n))" using one False by simp
  then obtain y where ay: "(a, y) \<in> R ^^ n" and yb: "(y, b) \<in> R ^^ (p - n)"
    unfolding relpow_add by blast
  have gy: "G y" by (rule relpow_backward[where R=R and G=G, OF backward yb good])
  have "y = c" by (rule relpow_forced[where R=R and G=G, OF unique backward ay two gy])
  then show ?thesis using False gy by simp
qed

lemma wrap_forced_split:
  fixes A :: "('q, 'b) ktm"
  assumes one: "(a, b) \<in> (ktm_step (delta_ktm (encoding_wrap A pack m S))) ^^ p"
      and good: "\<forall>q. ktc_state b \<noteq> W_Run q"
      and two: "(a, c) \<in> (ktm_step (delta_ktm (encoding_wrap A pack m S))) ^^ n"
  shows "p \<le> n \<and> (b, c) \<in> (ktm_step (delta_ktm (encoding_wrap A pack m S))) ^^ (n - p)
    \<or> n < p \<and> (\<forall>q. ktc_state c \<noteq> W_Run q)"
proof -
  have d: "delta_ktm (encoding_wrap A pack m S) = wrap_delta A pack m S" by simp
  show ?thesis unfolding d
    by (rule relpow_forced_split[where R = "ktm_step (wrap_delta A pack m S)"
        and G = "\<lambda>C. \<forall>q. ktc_state C \<noteq> W_Run q",
        OF wrap_step_unique_non_run wrap_step_back_non_run
        one[unfolded d] good two[unfolded d]])
qed

lemma wrap_prefix_forced_split:
  fixes A :: "('q, 'b) ktm" and pack :: "'a list \<Rightarrow> 'b"
    and table :: "'a list \<Rightarrow> bool"
  assumes one: "(a, b) \<in> (ktm_step (delta_ktm
        (wrap_prefix_patch (encoding_wrap A pack m S) table N))) ^^ p"
      and good: "\<forall>q. snd (ktc_state b) \<noteq> W_Run q"
      and two: "(a, c) \<in> (ktm_step (delta_ktm
        (wrap_prefix_patch (encoding_wrap A pack m S) table N))) ^^ n"
  shows "p \<le> n \<and> (b, c) \<in> (ktm_step (delta_ktm
        (wrap_prefix_patch (encoding_wrap A pack m S) table N))) ^^ (n - p)
    \<or> n < p \<and> (\<forall>q. snd (ktc_state c) \<noteq> W_Run q)"
  by (rule relpow_forced_split[where R = "ktm_step (delta_ktm
        (wrap_prefix_patch (encoding_wrap A pack m S) table N))"
      and G = "\<lambda>C. \<forall>q. snd (ktc_state C) \<noteq> W_Run q",
      OF wrap_prefix_step_unique wrap_prefix_step_back_non_run one good two])


subsection \<open>The flagged first compression block\<close>

lemma wrap_prefix_first_block:
  fixes A :: "('q,'b) ktm" and pack :: "'a list \<Rightarrow> 'b"
    and table :: "'a list \<Rightarrow> bool" and N :: nat
    and W :: "(('q,'a,'b) wrap_state,('a,'b) wrap_alphabet) ktm"
  assumes valid: "valid_ktm A" and positive: "0 < m"
      and word: "set w \<subseteq> S" and j: "j < m" "j \<le> length w"
  defines "W \<equiv> encoding_wrap A pack m S"
      and "P \<equiv> wrap_prefix_patch W table N"
      and "C \<equiv> \<lambda>j. mid_buf_extending_config_gen (k_ktm A) A pack m w 0 j"
  shows "(init_config_ktm P (map Raw w),wrap_flag_config True (C j))
      \<in> (ktm_step (delta_ktm P)) ^^ Suc j"
    and "(init_config_ktm W (map Raw w),C j)
      \<in> (ktm_step (delta_ktm W)) ^^ Suc j"
proof -
  have zero: "C 0 = mid_encoder_config_gen (k_ktm A) A pack m w 0"
    by (simp add: C_def mid_buf_extending_config_gen_def mid_encoder_config_gen_def fun_eq_iff split: nat.split)
  have old_init: "(init_config_ktm W (map Raw w),C 0)
    \<in> ktm_step (delta_ktm W)"
    using init_to_mid_zero[OF valid positive, where pack=pack and w=w and \<Sigma>u=S]
    by (simp add: W_def zero)
  have new_init: "(init_config_ktm P (map Raw w),wrap_flag_config True (C 0))
    \<in> ktm_step (delta_ktm P)"
  proof -
    have target: "wrap_prefix_target W table N True
        (ktc_state (init_config_ktm W (map Raw w)))
        (\<lambda>k. ktc_tape (init_config_ktm W (map Raw w)) k
          (ktc_pos (init_config_ktm W (map Raw w)) k)) (ktc_state (C 0))
        = (True,ktc_state (C 0))"
      by (auto simp: W_def C_def
        mid_buf_extending_config_gen_def wrap_prefix_target_def wrap_first_flag_def)
    show ?thesis using wrap_prefix_step[OF old_init target]
      by (simp add: P_def)
  qed
  have prefixes:
    "(init_config_ktm P (map Raw w),wrap_flag_config True (C i))
        \<in> (ktm_step (delta_ktm P)) ^^ Suc i \<and>
      (init_config_ktm W (map Raw w),C i)
        \<in> (ktm_step (delta_ktm W)) ^^ Suc i"
    if "i < m" "i \<le> length w" for i
    using that
  proof (induction i)
    case 0
    show ?case using old_init new_init by simp
  next
    case (Suc i)
    have i: "i < m" "i < length w" using Suc.prems by auto
    have old_step: "(C i,C (Suc i)) \<in> ktm_step (delta_ktm W)"
      using mid_buf_extend_step[where i=0 and j=i, OF valid positive word Suc.prems(1)]
        i by (simp add: C_def W_def)
    have k: "0 < k_ktm A" by (rule valid_ktm_k_pos[OF valid])
    have nonempty: "w \<noteq> []" using i(2) by (cases w) auto
    have target: "wrap_prefix_target W table N True (ktc_state (C i))
      (\<lambda>k. ktc_tape (C i) k (ktc_pos (C i) k)) (ktc_state (C (Suc i)))
        = (True,ktc_state (C (Suc i)))"
      using i Suc.prems k nonempty
      by (simp add: W_def C_def
        mid_buf_extending_config_gen_def wrap_prefix_target_def wrap_first_flag_def)
    have new_step: "(wrap_flag_config True (C i),wrap_flag_config True (C (Suc i)))
      \<in> ktm_step (delta_ktm P)"
      using wrap_prefix_step[OF old_step target] by (simp add: P_def)
    have ih: "(init_config_ktm P (map Raw w),wrap_flag_config True (C i))
        \<in> (ktm_step (delta_ktm P)) ^^ Suc i"
      "(init_config_ktm W (map Raw w),C i)
        \<in> (ktm_step (delta_ktm W)) ^^ Suc i"
      using Suc.IH[OF i(1)] Suc.prems by auto
    show ?case using relpow_Suc_I[OF ih(1) new_step]
      relpow_Suc_I[OF ih(2) old_step] by blast
  qed
  show "(init_config_ktm P (map Raw w),wrap_flag_config True (C j))
      \<in> (ktm_step (delta_ktm P)) ^^ Suc j"
    and "(init_config_ktm W (map Raw w),C j)
      \<in> (ktm_step (delta_ktm W)) ^^ Suc j"
    using prefixes[OF j] by auto
qed

lemma wrap_prefix_short_run:
  fixes A :: "('q,'b) ktm" and pack :: "'a list \<Rightarrow> 'b"
    and table :: "'a list \<Rightarrow> bool" and N :: nat
    and W :: "(('q,'a,'b) wrap_state,('a,'b) wrap_alphabet) ktm"
  assumes valid: "valid_ktm A" and positive: "0 < m"
      and word: "set w \<subseteq> S" and blle: "bl_ktm A \<noteq> le_ktm A"
      and k2: "2 \<le> k_ktm A"
      and pack: "\<And>i. i*m < length w \<Longrightarrow>
        pack (take m (drop (i*m) w)) \<in> Sigma_ktm A"
  defines "W \<equiv> encoding_wrap A pack m S"
      and "P \<equiv> wrap_prefix_patch W table N"
  assumes short: "length w < m" "length w \<le> N"
  shows "(init_config_ktm P (map Raw w),
      wrap_flag_config True (mid_buf_extending_config_gen (k_ktm A) A pack m w 0 (length w)))
      \<in> (ktm_step (delta_ktm P)) ^^ Suc (length w)"
    and "(wrap_flag_config True (mid_buf_extending_config_gen (k_ktm A) A pack m w 0 (length w)),
      KConfig (False,if table w then t_ktm W else r_ktm W)
        (ktc_tape (post_encoder_config_gen (k_ktm A) A pack m w))
        (ktc_pos (post_encoder_config_gen (k_ktm A) A pack m w)))
      \<in> ktm_step (delta_ktm P)"
proof -
  let ?C = "mid_buf_extending_config_gen (k_ktm A) A pack m w 0 (length w)"
  let ?D = "post_encoder_config_gen (k_ktm A) A pack m w"
  let ?q = "if table w then t_ktm W else r_ktm W"
  have first: "(init_config_ktm P (map Raw w),wrap_flag_config True ?C)
      \<in> (ktm_step (delta_ktm P)) ^^ Suc (length w)"
    using wrap_prefix_first_block(1)[where A=A and pack=pack and table=table and N=N
      and m=m and w=w and S=S and j="length w"]
      valid positive word short
    by (simp add: W_def P_def)
  have old_first: "(init_config_ktm W (map Raw w),?C)
      \<in> (ktm_step (delta_ktm W)) ^^ Suc (length w)"
    using wrap_prefix_first_block(2)[where A=A and pack=pack
      and m=m and w=w and S=S and j="length w"]
      valid positive word short
    by (simp add: W_def)
  have old_whole: "(init_config_ktm W (map Raw w),?D)
    \<in> (ktm_step (delta_ktm W)) ^^ (length w+2)"
    using init_to_post_encoder_relpow[where M=A and pack=pack and c=m and w=w and \<Sigma>u=S, OF valid positive word blle k2 pack]
    by (simp add: W_def)
  have goodC: "\<forall>q. ktc_state ?C \<noteq> W_Run q"
    by (simp add: mid_buf_extending_config_gen_def)
  have last: "(?C,?D) \<in> ktm_step (delta_ktm W)"
    using wrap_forced_split[OF old_first[unfolded W_def] goodC old_whole[unfolded W_def]]
    by (simp add: W_def)
  have k: "0 < k_ktm A" by (rule valid_ktm_k_pos[OF valid])
  have target: "wrap_prefix_target W table N True (ktc_state ?C)
    (\<lambda>j. ktc_tape ?C j (ktc_pos ?C j)) (ktc_state ?D) = (False,?q)"
    using short k
    by (simp add: W_def wrap_prefix_target_def
      mid_buf_extending_config_gen_def post_encoder_config_gen_def)
  let ?final = "KConfig (False,?q) (ktc_tape ?D) (ktc_pos ?D)"
  have new_last: "(wrap_flag_config True ?C,?final) \<in> ktm_step (delta_ktm P)"
    using wrap_prefix_redirect_step[OF last target] by (simp add: P_def)
  show "(init_config_ktm P (map Raw w),wrap_flag_config True ?C)
      \<in> (ktm_step (delta_ktm P)) ^^ Suc (length w)" by (rule first)
  show "(wrap_flag_config True ?C,?final) \<in> ktm_step (delta_ktm P)" by (rule new_last)
qed

lemma wrap_prefix_long_prefix:
  fixes A :: "('q,'b) ktm" and pack :: "'a list \<Rightarrow> 'b"
    and table :: "'a list \<Rightarrow> bool" and N :: nat
    and W :: "(('q,'a,'b) wrap_state,('a,'b) wrap_alphabet) ktm"
  assumes valid: "valid_ktm A" and positive: "0 < m"
      and word: "set w \<subseteq> S" and blle: "bl_ktm A \<noteq> le_ktm A"
      and k2: "2 \<le> k_ktm A"
      and pack: "\<And>i. i*m < length w \<Longrightarrow>
        pack (take m (drop (i*m) w)) \<in> Sigma_ktm A"
  defines "W \<equiv> encoding_wrap A pack m S"
      and "P \<equiv> wrap_prefix_patch W table N"
  assumes long: "N < length w"
  shows "(init_config_ktm P (map Raw w),
      wrap_flag_config False (post_encoder_config_gen (k_ktm A) A pack m w))
      \<in> (ktm_step (delta_ktm P)) ^^ (length w+2)"
proof -
  let ?C = "\<lambda>j. mid_buf_extending_config_gen (k_ktm A) A pack m w 0 j"
  let ?D = "post_encoder_config_gen (k_ktm A) A pack m w"
  have old_whole: "(init_config_ktm W (map Raw w),?D)
    \<in> (ktm_step (delta_ktm W)) ^^ (length w+2)"
    using init_to_post_encoder_relpow[where M=A and pack=pack and c=m and w=w
      and \<Sigma>u=S, OF valid positive word blle k2 pack]
    by (simp add: W_def)
  have k: "0 < k_ktm A" by (rule valid_ktm_k_pos[OF valid])
  show ?thesis
  proof (cases "length w < m")
    case True
    have first: "(init_config_ktm P (map Raw w),wrap_flag_config True (?C (length w)))
      \<in> (ktm_step (delta_ktm P)) ^^ Suc (length w)"
      using wrap_prefix_first_block(1)[where A=A and pack=pack and table=table and N=N
        and m=m and w=w and S=S and j="length w"] valid positive word True
      by (simp add: W_def P_def)
    have old_first: "(init_config_ktm W (map Raw w),?C (length w))
      \<in> (ktm_step (delta_ktm W)) ^^ Suc (length w)"
      using wrap_prefix_first_block(2)[where A=A and pack=pack
        and m=m and w=w and S=S and j="length w"] valid positive word True
      by (simp add: W_def)
    have goodC: "\<forall>q. ktc_state (?C (length w)) \<noteq> W_Run q"
      by (simp add: mid_buf_extending_config_gen_def)
    have last: "(?C (length w),?D) \<in> ktm_step (delta_ktm W)"
      using wrap_forced_split[OF old_first[unfolded W_def] goodC old_whole[unfolded W_def]]
      by (simp add: W_def)
    have target: "wrap_prefix_target W table N True (ktc_state (?C (length w)))
      (\<lambda>j. ktc_tape (?C (length w)) j (ktc_pos (?C (length w)) j))
      (ktc_state ?D) = (False,ktc_state ?D)"
      using long k
      by (simp add: W_def wrap_prefix_target_def wrap_first_flag_def
        mid_buf_extending_config_gen_def post_encoder_config_gen_def)
    have new_last: "(wrap_flag_config True (?C (length w)),wrap_flag_config False ?D)
      \<in> ktm_step (delta_ktm P)"
      using wrap_prefix_step[OF last target] by (simp add: P_def)
    show ?thesis using relpow_Suc_I[OF first new_last] by simp
  next
    case False
    have m_le: "m \<le> length w" using False by simp
    have index: "m-1 < m" "m-1 \<le> length w" using positive m_le by arith+
    let ?B = "mid_encoder_config_gen (k_ktm A) A pack m w 1"
    have first: "(init_config_ktm P (map Raw w),wrap_flag_config True (?C (m-1)))
      \<in> (ktm_step (delta_ktm P)) ^^ m"
      using wrap_prefix_first_block(1)[where A=A and pack=pack and table=table and N=N
        and m=m and w=w and S=S and j="m-1"] valid positive word index
      by (simp add: W_def P_def)
    have old_first: "(init_config_ktm W (map Raw w),?C (m-1))
      \<in> (ktm_step (delta_ktm W)) ^^ m"
      using wrap_prefix_first_block(2)[where A=A and pack=pack
        and m=m and w=w and S=S and j="m-1"] valid positive word index
      by (simp add: W_def)
    have nonempty: "w \<noteq> []" using positive m_le by (cases w) auto
    have block: "pack (take m w) \<in> Sigma_ktm A"
      using pack[of 0] nonempty by simp
    have close: "(?C (m-1),?B) \<in> ktm_step (delta_ktm W)"
      using mid_buf_close_step[where M=A and pack=pack and c=m and w=w
        and \<Sigma>u=S and i=0, OF valid positive word _ _ blle k2] m_le block
      by (simp add: W_def)
    have target: "wrap_prefix_target W table N True (ktc_state (?C (m-1)))
      (\<lambda>j. ktc_tape (?C (m-1)) j (ktc_pos (?C (m-1)) j))
      (ktc_state ?B) = (False,ktc_state ?B)"
      using positive m_le k
      by (simp add: W_def wrap_prefix_target_def wrap_first_flag_def
        mid_buf_extending_config_gen_def mid_encoder_config_gen_def)
    have new_close: "(wrap_flag_config True (?C (m-1)),wrap_flag_config False ?B)
      \<in> ktm_step (delta_ktm P)"
      using wrap_prefix_step[OF close target] by (simp add: P_def)
    have new_block: "(init_config_ktm P (map Raw w),wrap_flag_config False ?B)
      \<in> (ktm_step (delta_ktm P)) ^^ Suc m"
      by (rule relpow_Suc_I[OF first new_close])
    have old_block: "(init_config_ktm W (map Raw w),?B)
      \<in> (ktm_step (delta_ktm W)) ^^ Suc m"
      by (rule relpow_Suc_I[OF old_first close])
    have order: "Suc m \<le> length w+2" using m_le by arith
    have goodB: "\<forall>q. ktc_state ?B \<noteq> W_Run q"
      by (simp add: mid_encoder_config_gen_def)
    have suffix: "(?B,?D) \<in> (ktm_step (delta_ktm W)) ^^ (length w+2-Suc m)"
      using wrap_forced_split[OF old_block[unfolded W_def] goodB old_whole[unfolded W_def]]
        order by (simp add: W_def)
    have lifted: "(wrap_flag_config False ?B,wrap_flag_config False ?D)
      \<in> (ktm_step (delta_ktm P)) ^^ (length w+2-Suc m)"
      using wrap_prefix_false_run[OF suffix] by (simp add: P_def)
    have total: "(init_config_ktm P (map Raw w),wrap_flag_config False ?D)
      \<in> (ktm_step (delta_ktm P)) ^^ (Suc m+(length w+2-Suc m))"
      using new_block lifted unfolding relpow_add by blast
    show ?thesis using total order by simp
  qed
qed

lemma wrap_prefix_short_reaches:
  fixes A :: "('q,'b) ktm" and pack :: "'a list \<Rightarrow> 'b"
    and table :: "'a list \<Rightarrow> bool" and N :: nat
  assumes valid: "valid_ktm A" and positive: "0 < m"
      and word: "set w \<subseteq> S" and blle: "bl_ktm A \<noteq> le_ktm A"
      and k2: "2 \<le> k_ktm A"
      and pack: "\<And>i. i*m < length w \<Longrightarrow>
        pack (take m (drop (i*m) w)) \<in> Sigma_ktm A"
      and short: "length w < m" "length w \<le> N"
  shows "reaches_state_in_time_ktm
    (wrap_prefix_patch (encoding_wrap A pack m S) table N) (map Raw w)
    (False,if table w then t_ktm (encoding_wrap A pack m S)
      else r_ktm (encoding_wrap A pack m S)) (length w+2)"
proof -
  note run = wrap_prefix_short_run[where A=A and pack=pack and m=m and S=S and w=w
    and table=table and N=N, OF valid positive word blle k2 pack short]
  show ?thesis
    by (rule reaches_state_in_time_ktmI[OF _ relpow_Suc_I[OF run]]) simp_all
qed


subsection \<open>Terminal states, transport and language\<close>

text \<open>The simulated machine's halting states are sinks of the wrap, and so
  of its patch.\<close>

lemma wrap_run_terminal_sink:
  assumes valid: "valid_ktm A" and q: "q \<in> {t_ktm A, r_ktm A}"
  shows "(W_Run q, a, p, b, d) \<notin> wrap_delta A pack m S"
proof
  assume member: "(W_Run q, a, p, b, d) \<in> wrap_delta A pack m S"
  have run: "(W_Run q, a, p, b, d) \<in> wrap_run_delta A S"
    by (rule wrap_delta_W_Run_source_only_run[OF member])
  obtain a0 p0 b0 d0 where source: "(q, a0, p0, b0, d0) \<in> delta_ktm A"
    using run unfolding wrap_run_delta_def by auto
  have "delta_ktm A \<subseteq>
    (Q_ktm A - {t_ktm A, r_ktm A}) \<times> (UNIV \<rightarrow> \<Gamma>_ktm A) \<times>
    Q_ktm A \<times> (UNIV \<rightarrow> \<Gamma>_ktm A) \<times> (UNIV \<rightarrow> UNIV)"
    by (rule valid_ktm_delta_set[OF valid])
  with source q show False by auto
qed

lemma wrap_prefix_terminal_sink:
  fixes A :: "('q,'b) ktm"
  assumes valid: "valid_ktm A" and q: "q \<in> {t_ktm A, r_ktm A}"
      and state: "snd (ktc_state c) = W_Run q"
  shows "(c, y) \<notin> ktm_step (delta_ktm (wrap_prefix_patch (encoding_wrap A pack m S) table N))"
proof
  assume "(c, y) \<in> ktm_step (delta_ktm (wrap_prefix_patch (encoding_wrap A pack m S) table N))"
  then obtain s ts n p' b d where src: "c = KConfig s ts n"
    and tuple: "(s, \<lambda>j. ts j (n j), p', b, d) \<in> wrap_prefix_delta (encoding_wrap A pack m S) table N"
    by (cases rule: ktm_step.cases) auto
  obtain first q0 p where s: "s = (first, q0)"
    and old: "(q0, \<lambda>j. ts j (n j), p, b, d) \<in> delta_ktm (encoding_wrap A pack m S)"
    using tuple unfolding wrap_prefix_delta_def by blast
  have "q0 = W_Run q" using state src s by simp
  then have "(W_Run q, \<lambda>j. ts j (n j), p, b, d) \<in> wrap_delta A pack m S"
    using old by simp
  with wrap_run_terminal_sink[OF valid q] show False by blast
qed

text \<open>On a long input the patch runs as the wrap does, so every
  simulation-phase state the wrap reaches the patch reaches in the same
  time, with the flag clear.\<close>

lemma wrap_prefix_transport:
  fixes A :: "('q,'b) ktm" and pack :: "'a list \<Rightarrow> 'b"
    and table :: "'a list \<Rightarrow> bool" and N :: nat
  assumes valid: "valid_ktm A" and positive: "0 < m"
      and word: "set w \<subseteq> S" and blle: "bl_ktm A \<noteq> le_ktm A"
      and k2: "2 \<le> k_ktm A"
      and pack: "\<And>i. i*m < length w \<Longrightarrow>
        pack (take m (drop (i*m) w)) \<in> Sigma_ktm A"
      and long: "N < length w"
      and reach: "reaches_state_in_time_ktm (encoding_wrap A pack m S) (map Raw w) (W_Run q) T"
  shows "reaches_state_in_time_ktm (wrap_prefix_patch (encoding_wrap A pack m S) table N) (map Raw w) (False, W_Run q) T"
proof -
  obtain k fin where k: "k \<le> T"
    and run: "(init_config_ktm (encoding_wrap A pack m S) (map Raw w), fin) \<in> (ktm_step (delta_ktm (encoding_wrap A pack m S))) ^^ k"
    and st: "ktc_state fin = W_Run q"
    using reach unfolding reaches_state_in_time_ktm_def by blast
  let ?D = "post_encoder_config_gen (k_ktm A) A pack m w"
  have old_whole: "(init_config_ktm (encoding_wrap A pack m S) (map Raw w), ?D)
      \<in> (ktm_step (delta_ktm (encoding_wrap A pack m S))) ^^ (length w + 2)"
    using init_to_post_encoder_relpow[where M=A and pack=pack and c=m and w=w
      and \<Sigma>u=S, OF valid positive word blle k2 pack] by simp
  have goodD: "\<forall>q. ktc_state ?D \<noteq> W_Run q" by (simp add: post_encoder_config_gen_def)
  have split: "length w + 2 \<le> k \<and>
      (?D, fin) \<in> (ktm_step (delta_ktm (encoding_wrap A pack m S))) ^^ (k - (length w + 2))"
    using wrap_forced_split[OF old_whole goodD run] st by auto
  have new_prefix: "(init_config_ktm (wrap_prefix_patch (encoding_wrap A pack m S) table N) (map Raw w), wrap_flag_config False ?D)
      \<in> (ktm_step (delta_ktm (wrap_prefix_patch (encoding_wrap A pack m S) table N))) ^^ (length w + 2)"
    by (rule wrap_prefix_long_prefix[where A=A and pack=pack and m=m and S=S and w=w and table=table and N=N, OF valid positive word blle k2 pack long])
  have lifted: "(wrap_flag_config False ?D, wrap_flag_config False fin)
      \<in> (ktm_step (delta_ktm (wrap_prefix_patch (encoding_wrap A pack m S) table N))) ^^ (k - (length w + 2))"
    using wrap_prefix_false_run split by blast
  have "(init_config_ktm (wrap_prefix_patch (encoding_wrap A pack m S) table N) (map Raw w), wrap_flag_config False fin)
      \<in> (ktm_step (delta_ktm (wrap_prefix_patch (encoding_wrap A pack m S) table N))) ^^ (length w + 2 + (k - (length w + 2)))"
    using new_prefix lifted unfolding relpow_add by blast
  moreover have eqk: "length w + 2 + (k - (length w + 2)) = k"
    using split[THEN conjunct1] by simp
  ultimately have whole: "(init_config_ktm (wrap_prefix_patch (encoding_wrap A pack m S) table N) (map Raw w), wrap_flag_config False fin)
      \<in> (ktm_step (delta_ktm (wrap_prefix_patch (encoding_wrap A pack m S) table N))) ^^ k"
    by (simp only: eqk)
  show ?thesis by (rule reaches_state_in_time_ktmI[OF k whole]) (simp add: st)
qed

text \<open>On a short input every accepting run is the table's: the forced
  prefix ends in the redirected transition, whose target is a sink.\<close>

lemma wrap_prefix_short_accepts:
  fixes A :: "('q,'b) ktm" and pack :: "'a list \<Rightarrow> 'b"
    and table :: "'a list \<Rightarrow> bool" and N :: nat
  assumes valid: "valid_ktm A" and positive: "0 < m"
      and word: "set w \<subseteq> S" and blle: "bl_ktm A \<noteq> le_ktm A"
      and k2: "2 \<le> k_ktm A"
      and pack: "\<And>i. i*m < length w \<Longrightarrow>
        pack (take m (drop (i*m) w)) \<in> Sigma_ktm A"
      and short: "length w < m" "length w \<le> N"
      and acc: "accepts_in_time_ktm (wrap_prefix_patch (encoding_wrap A pack m S) table N) (map Raw w) T"
  shows "table w"
proof -
  let ?C = "wrap_flag_config True (mid_buf_extending_config_gen (k_ktm A) A pack m w 0 (length w))"
  let ?D = "post_encoder_config_gen (k_ktm A) A pack m w"
  let ?q = "if table w then t_ktm (encoding_wrap A pack m S) else r_ktm (encoding_wrap A pack m S)"
  let ?fin = "KConfig (False, ?q) (ktc_tape ?D) (ktc_pos ?D)"
  note run = wrap_prefix_short_run[where A=A and pack=pack and m=m and S=S and w=w and table=table and N=N, OF valid positive word blle k2 pack short]
  obtain k E where accrun: "(init_config_ktm (wrap_prefix_patch (encoding_wrap A pack m S) table N) (map Raw w), E)
      \<in> (ktm_step (delta_ktm (wrap_prefix_patch (encoding_wrap A pack m S) table N))) ^^ k"
    and stE: "ktc_state E = t_ktm (wrap_prefix_patch (encoding_wrap A pack m S) table N)"
    using acc unfolding accepts_in_time_ktm_iff_reaches reaches_state_in_time_ktm_def by blast
  have stE': "ktc_state E = (False, W_Run (t_ktm A))" using stE by simp
  have goodC: "\<forall>q. snd (ktc_state ?C) \<noteq> W_Run q"
    by (simp add: mid_buf_extending_config_gen_def)
  have after: "(?C, E) \<in> (ktm_step (delta_ktm (wrap_prefix_patch (encoding_wrap A pack m S) table N))) ^^ (k - Suc (length w))"
    using wrap_prefix_forced_split[OF run(1) goodC accrun] stE' by auto
  obtain j where j: "k - Suc (length w) = Suc j"
  proof (cases "k - Suc (length w)")
    case 0
    then have "E = ?C" using after by simp
    then show ?thesis using stE' by simp
  next
    case (Suc j)
    then show ?thesis by (rule that)
  qed
  obtain Y where CY: "(?C, Y) \<in> ktm_step (delta_ktm (wrap_prefix_patch (encoding_wrap A pack m S) table N))"
    and YE: "(Y, E) \<in> (ktm_step (delta_ktm (wrap_prefix_patch (encoding_wrap A pack m S) table N))) ^^ j"
    using relpow_Suc_D2[OF after[unfolded j]] by blast
  have Y: "Y = ?fin" by (rule wrap_prefix_step_unique[OF CY run(2) goodC])
  have sink: "(?fin, Z) \<notin> ktm_step (delta_ktm (wrap_prefix_patch (encoding_wrap A pack m S) table N))" for Z
  proof (cases "table w")
    case True
    show ?thesis by (rule wrap_prefix_terminal_sink[OF valid, of "t_ktm A"]) (simp_all add: True)
  next
    case False
    show ?thesis by (rule wrap_prefix_terminal_sink[OF valid, of "r_ktm A"]) (simp_all add: False)
  qed
  have "E = ?fin"
  proof (cases j)
    case 0
    then show ?thesis using YE Y by simp
  next
    case (Suc i)
    then obtain Z where "(?fin, Z) \<in> ktm_step (delta_ktm (wrap_prefix_patch (encoding_wrap A pack m S) table N))"
      using relpow_Suc_D2[OF YE[unfolded Y Suc]] by blast
    with sink show ?thesis by blast
  qed
  then have "?q = W_Run (t_ktm A)" using stE' by simp
  moreover have "r_ktm A \<noteq> t_ktm A" using valid by (cases A) auto
  ultimately show "table w" by (cases "table w") simp_all
qed

text \<open>On a long input every accepting run of the patch passes through the
  wrap's post-encoder configuration with the flag clear, and from there it
  is a run of the wrap.\<close>

lemma wrap_prefix_long_accepts:
  fixes A :: "('q,'b) ktm" and pack :: "'a list \<Rightarrow> 'b"
    and table :: "'a list \<Rightarrow> bool" and N :: nat
  assumes valid: "valid_ktm A" and positive: "0 < m"
      and word: "set w \<subseteq> S" and blle: "bl_ktm A \<noteq> le_ktm A"
      and k2: "2 \<le> k_ktm A"
      and pack: "\<And>i. i*m < length w \<Longrightarrow>
        pack (take m (drop (i*m) w)) \<in> Sigma_ktm A"
      and long: "N < length w"
      and acc: "accepts_in_time_ktm (wrap_prefix_patch (encoding_wrap A pack m S) table N) (map Raw w) T"
  shows "accepts_in_time_ktm (encoding_wrap A pack m S) (map Raw w) T"
proof -
  let ?D = "post_encoder_config_gen (k_ktm A) A pack m w"
  have new_prefix: "(init_config_ktm (wrap_prefix_patch (encoding_wrap A pack m S) table N) (map Raw w), wrap_flag_config False ?D)
      \<in> (ktm_step (delta_ktm (wrap_prefix_patch (encoding_wrap A pack m S) table N))) ^^ (length w + 2)"
    by (rule wrap_prefix_long_prefix[where A=A and pack=pack and m=m and S=S and w=w and table=table and N=N, OF valid positive word blle k2 pack long])
  have old_whole: "(init_config_ktm (encoding_wrap A pack m S) (map Raw w), ?D)
      \<in> (ktm_step (delta_ktm (encoding_wrap A pack m S))) ^^ (length w + 2)"
    using init_to_post_encoder_relpow[where M=A and pack=pack and c=m and w=w
      and \<Sigma>u=S, OF valid positive word blle k2 pack] by simp
  obtain k E where k: "k \<le> T"
    and accrun: "(init_config_ktm (wrap_prefix_patch (encoding_wrap A pack m S) table N) (map Raw w), E) \<in> (ktm_step (delta_ktm (wrap_prefix_patch (encoding_wrap A pack m S) table N))) ^^ k"
    and stE: "ktc_state E = t_ktm (wrap_prefix_patch (encoding_wrap A pack m S) table N)"
    using acc unfolding accepts_in_time_ktm_iff_reaches reaches_state_in_time_ktm_def by blast
  have stE': "ktc_state E = (False, W_Run (t_ktm A))" using stE by simp
  have goodD: "\<forall>q. snd (ktc_state (wrap_flag_config False ?D)) \<noteq> W_Run q"
    by (simp add: post_encoder_config_gen_def)
  have split: "length w + 2 \<le> k \<and> (wrap_flag_config False ?D, E)
      \<in> (ktm_step (delta_ktm (wrap_prefix_patch (encoding_wrap A pack m S) table N))) ^^ (k - (length w + 2))"
    using wrap_prefix_forced_split[OF new_prefix goodD accrun] stE' by auto
  obtain E' where E: "E = wrap_flag_config False E'"
    and tail: "(?D, E') \<in> (ktm_step (delta_ktm (encoding_wrap A pack m S))) ^^ (k - (length w + 2))"
    using wrap_prefix_false_run_proj split by blast
  have "(init_config_ktm (encoding_wrap A pack m S) (map Raw w), E')
      \<in> (ktm_step (delta_ktm (encoding_wrap A pack m S))) ^^ (length w + 2 + (k - (length w + 2)))"
    using old_whole tail unfolding relpow_add by blast
  moreover have eqk: "length w + 2 + (k - (length w + 2)) = k"
    using split[THEN conjunct1] by simp
  ultimately have whole: "(init_config_ktm (encoding_wrap A pack m S) (map Raw w), E')
      \<in> (ktm_step (delta_ktm (encoding_wrap A pack m S))) ^^ k"
    by (simp only: eqk)
  have "ktc_state E' = t_ktm (encoding_wrap A pack m S)" using stE' E by simp
  then show ?thesis unfolding accepts_in_time_ktm_iff_reaches
    by (rule reaches_state_in_time_ktmI[OF k whole])
qed

text \<open>With the wrap's own language as the table, the patch accepts the
  same user-facing language as the wrap.  No determinism is assumed.\<close>

theorem wrap_prefix_language:
  fixes A :: "('q,'b) ktm" and pack :: "'a list \<Rightarrow> 'b" and N :: nat
  assumes valid: "valid_ktm A" and positive: "0 < m"
      and blle: "bl_ktm A \<noteq> le_ktm A" and k2: "2 \<le> k_ktm A"
      and width: "N < m"
      and enc: "\<And>w. set w \<subseteq> S \<Longrightarrow> set (wrap_enc pack m w) \<subseteq> Sigma_ktm A"
  shows "Lang_user_wrap (wrap_prefix_patch (encoding_wrap A pack m S) (\<lambda>u. u \<in> Lang_user_wrap (encoding_wrap A pack m S)) N) = Lang_user_wrap (encoding_wrap A pack m S)"
proof (rule set_eqI)
  fix w
  have legal: "set (map Raw w) \<subseteq> Raw ` S \<longleftrightarrow> set w \<subseteq> S" by auto
  have tP: "t_ktm (wrap_prefix_patch (encoding_wrap A pack m S) (\<lambda>u. u \<in> Lang_user_wrap (encoding_wrap A pack m S)) N) = (False, W_Run (t_ktm A))" by simp
  show "w \<in> Lang_user_wrap (wrap_prefix_patch (encoding_wrap A pack m S) (\<lambda>u. u \<in> Lang_user_wrap (encoding_wrap A pack m S)) N) \<longleftrightarrow> w \<in> Lang_user_wrap (encoding_wrap A pack m S)"
  proof (cases "set w \<subseteq> S")
    case False
    then have badW: "\<not> set (map Raw w) \<subseteq> Sigma_ktm (encoding_wrap A pack m S)"
      and badP: "\<not> set (map Raw w) \<subseteq> Sigma_ktm (wrap_prefix_patch (encoding_wrap A pack m S) (\<lambda>u. u \<in> Lang_user_wrap (encoding_wrap A pack m S)) N)" by auto
    have "map Raw w \<notin> Lang_ktm (wrap_prefix_patch (encoding_wrap A pack m S) (\<lambda>u. u \<in> Lang_user_wrap (encoding_wrap A pack m S)) N)" and "map Raw w \<notin> Lang_ktm (encoding_wrap A pack m S)"
      using badW badP unfolding Lang_ktm_iff by blast+
    then show ?thesis by (simp add: Lang_user_wrap_def)
  next
    case word: True
    have packw: "pack (take m (drop (i*m) w)) \<in> Sigma_ktm A" if "i*m < length w" for i
      using enc[OF word] pack_take_in_set_wrap_enc[OF positive that, where pack=pack] by blast
    show ?thesis
    proof (cases "length w \<le> N")
      case short: True
      have shortm: "length w < m" using short width by simp
      show ?thesis
      proof
        assume "w \<in> Lang_user_wrap (wrap_prefix_patch (encoding_wrap A pack m S) (\<lambda>u. u \<in> Lang_user_wrap (encoding_wrap A pack m S)) N)"
        then obtain T where acc: "accepts_in_time_ktm (wrap_prefix_patch (encoding_wrap A pack m S) (\<lambda>u. u \<in> Lang_user_wrap (encoding_wrap A pack m S)) N) (map Raw w) T"
          by (auto simp: Lang_user_wrap_def Lang_ktm_iff)
        show "w \<in> Lang_user_wrap (encoding_wrap A pack m S)"
          by (rule wrap_prefix_short_accepts[where A=A and pack=pack and m=m and S=S and w=w and table="\<lambda>u. u \<in> Lang_user_wrap (encoding_wrap A pack m S)" and N=N,
              OF valid positive word blle k2 packw shortm short acc])
      next
        assume member: "w \<in> Lang_user_wrap (encoding_wrap A pack m S)"
        have "reaches_state_in_time_ktm (wrap_prefix_patch (encoding_wrap A pack m S) (\<lambda>u. u \<in> Lang_user_wrap (encoding_wrap A pack m S)) N) (map Raw w)
            (False, W_Run (t_ktm A)) (length w + 2)"
          using wrap_prefix_short_reaches[where A=A and pack=pack and m=m and S=S and w=w and table="\<lambda>u. u \<in> Lang_user_wrap (encoding_wrap A pack m S)" and N=N,
              OF valid positive word blle k2 packw shortm short] member by simp
        then have "accepts_in_time_ktm (wrap_prefix_patch (encoding_wrap A pack m S) (\<lambda>u. u \<in> Lang_user_wrap (encoding_wrap A pack m S)) N) (map Raw w) (length w + 2)"
          unfolding accepts_in_time_ktm_iff_reaches tP .
        then show "w \<in> Lang_user_wrap (wrap_prefix_patch (encoding_wrap A pack m S) (\<lambda>u. u \<in> Lang_user_wrap (encoding_wrap A pack m S)) N)"
          using word legal by (auto simp: Lang_user_wrap_def Lang_ktm_iff)
      qed
    next
      case long: False
      have longN: "N < length w" using long by simp
      show ?thesis
      proof
        assume "w \<in> Lang_user_wrap (wrap_prefix_patch (encoding_wrap A pack m S) (\<lambda>u. u \<in> Lang_user_wrap (encoding_wrap A pack m S)) N)"
        then obtain T where acc: "accepts_in_time_ktm (wrap_prefix_patch (encoding_wrap A pack m S) (\<lambda>u. u \<in> Lang_user_wrap (encoding_wrap A pack m S)) N) (map Raw w) T"
          by (auto simp: Lang_user_wrap_def Lang_ktm_iff)
        have "accepts_in_time_ktm (encoding_wrap A pack m S) (map Raw w) T"
          by (rule wrap_prefix_long_accepts[where A=A and pack=pack and m=m and S=S and w=w and table="\<lambda>u. u \<in> Lang_user_wrap (encoding_wrap A pack m S)" and N=N,
              OF valid positive word blle k2 packw longN acc])
        then show "w \<in> Lang_user_wrap (encoding_wrap A pack m S)"
          using word legal by (auto simp: Lang_user_wrap_def Lang_ktm_iff)
      next
        assume "w \<in> Lang_user_wrap (encoding_wrap A pack m S)"
        then obtain T where acc: "accepts_in_time_ktm (encoding_wrap A pack m S) (map Raw w) T"
          by (auto simp: Lang_user_wrap_def Lang_ktm_iff)
        have reach: "reaches_state_in_time_ktm (encoding_wrap A pack m S) (map Raw w) (W_Run (t_ktm A)) T"
          using acc unfolding accepts_in_time_ktm_iff_reaches by simp
        have "reaches_state_in_time_ktm (wrap_prefix_patch (encoding_wrap A pack m S) (\<lambda>u. u \<in> Lang_user_wrap (encoding_wrap A pack m S)) N) (map Raw w) (False, W_Run (t_ktm A)) T"
          by (rule wrap_prefix_transport[where A=A and pack=pack and m=m and S=S and w=w and table="\<lambda>u. u \<in> Lang_user_wrap (encoding_wrap A pack m S)" and N=N,
              OF valid positive word blle k2 packw longN reach])
        then have "accepts_in_time_ktm (wrap_prefix_patch (encoding_wrap A pack m S) (\<lambda>u. u \<in> Lang_user_wrap (encoding_wrap A pack m S)) N) (map Raw w) T"
          unfolding accepts_in_time_ktm_iff_reaches tP .
        then show "w \<in> Lang_user_wrap (wrap_prefix_patch (encoding_wrap A pack m S) (\<lambda>u. u \<in> Lang_user_wrap (encoding_wrap A pack m S)) N)"
          using word legal by (auto simp: Lang_user_wrap_def Lang_ktm_iff)
      qed
    qed
  qed
qed

end
