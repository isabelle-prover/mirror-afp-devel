theory Wrap_Prefix_Patch
  imports Wrap_Forcing "Multitape_TM_Substrate.Multitape_Run_Facts"
begin

section \<open>A finite decision inside the first encoder block\<close>

text \<open>Hopcroft and Ullman finish the proof of Theorem~12.3 by recognising the
  finitely many short words ``using [the] finite control only, taking
  \<open>n + 1\<close> moves'', and prove Theorem~12.4 with the same construction
  \<^cite>\<open>\<open>p.~291\<close> in "Hopcroft1979:introduction"\<close>.  This theory builds that
  step into the encoding wrap.  The wrap already reads
  the whole of a short input into its first buffer and then takes one
  end-of-input transition; the patch redirects exactly that transition, for
  inputs of length at most a cutoff \<open>N\<close>, to the accept or reject state
  chosen by a finite table.  A Boolean flag, set at the start and cleared
  when the first block closes, confines the redirection to the first block,
  so no rescan is added and longer inputs run as before.

  The patch needs no determinism of the simulated machine: the wrap is deterministic outside its simulation
  phase (@{thm[source] wrap_delta_non_W_Run_det}), so its encoder prefix is
  forced, and that forcing is all the arguments below need.\<close>

definition wrap_first_flag where
  "wrap_first_flag first q p = (first \<and>
    (case p of W_Buf v \<Rightarrow> v \<noteq> [] \<or> q = W_Init | _ \<Rightarrow> False))"

definition wrap_prefix_target where
  "wrap_prefix_target W table N first q a p =
    (case q of W_Buf u \<Rightarrow>
      if first \<and> length u \<le> N \<and> a 0 = bl_ktm W
      then (False, if table u then t_ktm W else r_ktm W)
      else (wrap_first_flag first q p, p)
    | _ \<Rightarrow> (wrap_first_flag first q p, p))"

definition wrap_prefix_delta where
  "wrap_prefix_delta W table N =
    {((first, q), a, wrap_prefix_target W table N first q a p, b, d)
      | first q a p b d. (q, a, p, b, d) \<in> delta_ktm W}"

lemma wrap_prefix_deltaI:
  "(q, a, p, b, d) \<in> delta_ktm W \<Longrightarrow>
    ((first, q), a, wrap_prefix_target W table N first q a p, b, d)
      \<in> wrap_prefix_delta W table N"
  unfolding wrap_prefix_delta_def by blast

definition wrap_prefix_patch where
  "wrap_prefix_patch W table N =
    KTM (UNIV \<times> Q_ktm W) (Sigma_ktm W) (\<Gamma>_ktm W)
      (bl_ktm W) (le_ktm W) (wrap_prefix_delta W table N)
      (True, s_ktm W) (False, t_ktm W) (False, r_ktm W) (k_ktm W)"

lemma wrap_prefix_fields [simp]:
  "Q_ktm (wrap_prefix_patch W table N) = UNIV \<times> Q_ktm W"
  "Sigma_ktm (wrap_prefix_patch W table N) = Sigma_ktm W"
  "\<Gamma>_ktm (wrap_prefix_patch W table N) = \<Gamma>_ktm W"
  "bl_ktm (wrap_prefix_patch W table N) = bl_ktm W"
  "le_ktm (wrap_prefix_patch W table N) = le_ktm W"
  "delta_ktm (wrap_prefix_patch W table N) = wrap_prefix_delta W table N"
  "s_ktm (wrap_prefix_patch W table N) = (True, s_ktm W)"
  "t_ktm (wrap_prefix_patch W table N) = (False, t_ktm W)"
  "r_ktm (wrap_prefix_patch W table N) = (False, r_ktm W)"
  "k_ktm (wrap_prefix_patch W table N) = k_ktm W"
  by (simp_all add: wrap_prefix_patch_def)

lemma wrap_prefix_target_false [simp]:
  "wrap_prefix_target W table N False q a p = (False, p)"
  by (simp add: wrap_prefix_target_def wrap_first_flag_def split: wrap_state.split)

lemma wrap_prefix_target_state:
  assumes "valid_ktm W" "p \<in> Q_ktm W"
  shows "wrap_prefix_target W table N first q a p \<in> UNIV \<times> Q_ktm W"
  using assms by (cases W)
    (auto simp: wrap_prefix_target_def split: wrap_state.split if_splits)

text \<open>Outside a buffer state the target keeps the wrap's own successor,
  so a step from a simulation state stays in the simulation phase.\<close>

lemma wrap_prefix_target_non_buf:
  assumes "\<forall>u. q \<noteq> W_Buf u"
  shows "snd (wrap_prefix_target W table N first q a p) = p"
  using assms by (cases q) (simp_all add: wrap_prefix_target_def)

lemma wrap_prefix_patch_valid:
  assumes valid: "valid_ktm W"
  shows "valid_ktm (wrap_prefix_patch W table N)"
proof -
  have typed: "delta_ktm W \<subseteq>
    (Q_ktm W - {t_ktm W, r_ktm W}) \<times> (UNIV \<rightarrow> \<Gamma>_ktm W) \<times>
    Q_ktm W \<times> (UNIV \<rightarrow> \<Gamma>_ktm W) \<times> (UNIV \<rightarrow> UNIV)"
    by (rule valid_ktm_delta_set[OF valid])
  have delta: "wrap_prefix_delta W table N \<subseteq>
    ((UNIV \<times> Q_ktm W) - {(False, t_ktm W), (False, r_ktm W)}) \<times>
    (UNIV \<rightarrow> \<Gamma>_ktm W) \<times> (UNIV \<times> Q_ktm W) \<times>
    (UNIV \<rightarrow> \<Gamma>_ktm W) \<times> (UNIV \<rightarrow> UNIV)"
  proof
    fix z assume member: "z \<in> wrap_prefix_delta W table N"
    obtain first q a p b d where z:
      "z = ((first, q), a, wrap_prefix_target W table N first q a p, b, d)"
      and source: "(q, a, p, b, d) \<in> delta_ktm W"
      using member unfolding wrap_prefix_delta_def by blast
    have old: "(q, a, p, b, d) \<in>
      (Q_ktm W - {t_ktm W, r_ktm W}) \<times> (UNIV \<rightarrow> \<Gamma>_ktm W) \<times>
      Q_ktm W \<times> (UNIV \<rightarrow> \<Gamma>_ktm W) \<times> (UNIV \<rightarrow> UNIV)"
      using typed source by blast
    have p: "p \<in> Q_ktm W" using old by simp
    have target: "wrap_prefix_target W table N first q a p \<in> UNIV \<times> Q_ktm W"
      by (rule wrap_prefix_target_state[OF valid p])
    show "z \<in>
      ((UNIV \<times> Q_ktm W) - {(False, t_ktm W), (False, r_ktm W)}) \<times>
      (UNIV \<rightarrow> \<Gamma>_ktm W) \<times> (UNIV \<times> Q_ktm W) \<times>
      (UNIV \<rightarrow> \<Gamma>_ktm W) \<times> (UNIV \<rightarrow> UNIV)"
      using old target by (auto simp: z)
  qed
  have le: "\<forall>q a p b d j. (q, a, p, b, d) \<in> wrap_prefix_delta W table N \<longrightarrow>
    a j = le_ktm W \<longrightarrow> b j = le_ktm W \<and> d j \<in> {MoveN, MoveR}"
    using valid by (cases W)
      (auto simp: wrap_prefix_delta_def; metis valid_ktm_deltaLE[OF valid])
  have inactive: "\<forall>q a p b d. (q, a, p, b, d) \<in> wrap_prefix_delta W table N \<longrightarrow>
    (\<forall>j \<ge> k_ktm W. a j = bl_ktm W \<and> b j = bl_ktm W \<and> d j = MoveN)"
    by (auto simp: wrap_prefix_delta_def; metis valid_ktm_delta_support[OF valid])
  show ?thesis using valid delta le inactive
    by (cases W) (simp only: wrap_prefix_patch_def valid_ktm.simps
      ktm.sel Sigma_ktm.simps bl_ktm.simps le_ktm.simps delta_ktm.simps
      s_ktm.simps t_ktm.simps r_ktm.simps k_ktm.simps; auto)
qed

lemma wrap_prefix_patch_det:
  assumes det: "det_ktm W"
  shows "det_ktm (wrap_prefix_patch W table N)"
proof (unfold det_ktm_def, intro allI impI)
  fix q a p1 b1 d1 p2 b2 d2
  assume one: "(q, a, p1, b1, d1) \<in> delta_ktm (wrap_prefix_patch W table N)"
    and two: "(q, a, p2, b2, d2) \<in> delta_ktm (wrap_prefix_patch W table N)"
  obtain first s where q: "q = (first, s)" by (cases q) auto
  obtain r1 where old1: "(s, a, r1, b1, d1) \<in> delta_ktm W"
    and p1: "p1 = wrap_prefix_target W table N first s a r1"
    using one by (auto simp: q wrap_prefix_delta_def)
  obtain r2 where old2: "(s, a, r2, b2, d2) \<in> delta_ktm W"
    and p2: "p2 = wrap_prefix_target W table N first s a r2"
    using two by (auto simp: q wrap_prefix_delta_def)
  have equal: "r1 = r2 \<and> b1 = b2 \<and> d1 = d2"
    using det old1 old2 unfolding det_ktm_def by blast
  show "(p1, b1, d1) = (p2, b2, d2)" using equal by (simp add: p1 p2)
qed


subsection \<open>Lifting and projecting runs\<close>

definition wrap_flag_config where
  "wrap_flag_config first c = KConfig (first, ktc_state c) (ktc_tape c) (ktc_pos c)"

lemma wrap_flag_config_fields [simp]:
  "ktc_state (wrap_flag_config first c) = (first, ktc_state c)"
  "ktc_tape (wrap_flag_config first c) = ktc_tape c"
  "ktc_pos (wrap_flag_config first c) = ktc_pos c"
  by (simp_all add: wrap_flag_config_def)

lemma wrap_prefix_init [simp]:
  "init_config_ktm (wrap_prefix_patch W table N) w =
    wrap_flag_config True (init_config_ktm W w)"
  by (cases W) (simp add: wrap_prefix_patch_def wrap_flag_config_def)

text \<open>A wrap step lifts to a patch step whose target is the one the patch
  assigns; when that target keeps the wrap's successor state, the result
  is again a flagged configuration.\<close>

lemma wrap_prefix_redirect_step:
  assumes step: "(c, c') \<in> ktm_step (delta_ktm W)"
      and target: "wrap_prefix_target W table N first (ktc_state c)
        (\<lambda>j. ktc_tape c j (ktc_pos c j)) (ktc_state c') = (next, p')"
  shows "(wrap_flag_config first c,
    KConfig (next, p') (ktc_tape c') (ktc_pos c')) \<in>
    ktm_step (delta_ktm (wrap_prefix_patch W table N))"
proof -
  from step obtain q ts n p b d where c: "c = KConfig q ts n"
    and c': "c' = KConfig p (\<lambda>j. (ts j)(n j := b j))
      (\<lambda>j. go_move (d j) (n j))"
    and tuple: "(q, \<lambda>j. ts j (n j), p, b, d) \<in> delta_ktm W"
    by (cases rule: ktm_step.cases) auto
  have transformed: "((first, q), \<lambda>j. ts j (n j), (next, p'), b, d)
    \<in> wrap_prefix_delta W table N"
    using wrap_prefix_deltaI[OF tuple, where first=first and table=table and N=N]
      target by (simp add: c c')
  have lifted: "(KConfig (first, q) ts n,
    KConfig (next, p') (\<lambda>j. (ts j)(n j := b j))
      (\<lambda>j. go_move (d j) (n j))) \<in> ktm_step (wrap_prefix_delta W table N)"
    by (rule ktm_step.step[where ts=ts and n=n and a=b and move=d, OF transformed])
  show ?thesis using lifted by (simp add: c c' wrap_flag_config_def)
qed

lemma wrap_prefix_step:
  assumes step: "(c, c') \<in> ktm_step (delta_ktm W)"
      and target: "wrap_prefix_target W table N first (ktc_state c)
        (\<lambda>j. ktc_tape c j (ktc_pos c j)) (ktc_state c') = (next, ktc_state c')"
  shows "(wrap_flag_config first c, wrap_flag_config next c') \<in>
    ktm_step (delta_ktm (wrap_prefix_patch W table N))"
  using wrap_prefix_redirect_step[OF step target]
  by (simp add: wrap_flag_config_def)

lemma wrap_prefix_false_run:
  assumes "(c, c') \<in> (ktm_step (delta_ktm W)) ^^ n"
  shows "(wrap_flag_config False c, wrap_flag_config False c') \<in>
    (ktm_step (delta_ktm (wrap_prefix_patch W table N))) ^^ n"
  by (rule relpow_map [where h = "wrap_flag_config False", OF _ assms])
     (erule wrap_prefix_step, simp)

text \<open>Conversely, once the flag is clear the patch is the wrap: every
  step from a cleared configuration is a flagged wrap step.\<close>

lemma wrap_prefix_false_step_proj:
  assumes step: "(wrap_flag_config False c, y) \<in>
    ktm_step (delta_ktm (wrap_prefix_patch W table N))"
  shows "\<exists>c'. y = wrap_flag_config False c' \<and> (c, c') \<in> ktm_step (delta_ktm W)"
proof -
  from step obtain s ts n p' b d where src: "wrap_flag_config False c = KConfig s ts n"
    and y: "y = KConfig p' (\<lambda>j. (ts j)(n j := b j)) (\<lambda>j. go_move (d j) (n j))"
    and tuple: "(s, \<lambda>j. ts j (n j), p', b, d) \<in> wrap_prefix_delta W table N"
    by (cases rule: ktm_step.cases) auto
  have s: "s = (False, ktc_state c)" and ts: "ts = ktc_tape c" and n: "n = ktc_pos c"
    using src by (simp_all add: wrap_flag_config_def)
  obtain p where p': "p' = (False, p)"
    and old: "(ktc_state c, \<lambda>j. ts j (n j), p, b, d) \<in> delta_ktm W"
    using tuple unfolding wrap_prefix_delta_def s by auto
  let ?c' = "KConfig p (\<lambda>j. (ts j)(n j := b j)) (\<lambda>j. go_move (d j) (n j))"
  have "(KConfig (ktc_state c) ts n, ?c') \<in> ktm_step (delta_ktm W)"
    by (rule ktm_step.step[where ts=ts and n=n and a=b and move=d, OF old])
  moreover have "KConfig (ktc_state c) ts n = c" by (cases c) (simp add: ts n)
  moreover have "y = wrap_flag_config False ?c'" by (simp add: y p' wrap_flag_config_def)
  ultimately show ?thesis by auto
qed

lemma wrap_prefix_false_run_proj:
  assumes "(wrap_flag_config False c, y) \<in>
    (ktm_step (delta_ktm (wrap_prefix_patch W table N))) ^^ n"
  shows "\<exists>c'. y = wrap_flag_config False c' \<and> (c, c') \<in> (ktm_step (delta_ktm W)) ^^ n"
  using assms
proof (induction n arbitrary: y)
  case 0
  then show ?case by auto
next
  case (Suc n)
  from Suc.prems obtain mid where prefix:
      "(wrap_flag_config False c, mid) \<in>
        (ktm_step (delta_ktm (wrap_prefix_patch W table N))) ^^ n"
    and step: "(mid, y) \<in> ktm_step (delta_ktm (wrap_prefix_patch W table N))"
    by (rule relpow_Suc_E)
  obtain m where mid: "mid = wrap_flag_config False m"
    and run: "(c, m) \<in> (ktm_step (delta_ktm W)) ^^ n"
    using Suc.IH[OF prefix] by blast
  obtain c' where y: "y = wrap_flag_config False c'"
    and last: "(m, c') \<in> ktm_step (delta_ktm W)"
    using wrap_prefix_false_step_proj[OF step[unfolded mid]] by blast
  show ?case using relpow_Suc_I[OF run last] y by blast
qed


subsection \<open>Forced prefixes\<close>

text \<open>The patch inherits the wrap's determinism outside the simulation
  phase, and its own simulation phase is closed under steps, so
  @{thm[source] relpow_forced} applies to it as it does to the wrap
  (@{thm[source] wrap_path_det_non_run}).\<close>

lemma wrap_prefix_step_unique:
  fixes A :: "('q, 'b) ktm"
  assumes one: "(x, y1) \<in> ktm_step (delta_ktm (wrap_prefix_patch
        (encoding_wrap A pack m S) table N))"
      and two: "(x, y2) \<in> ktm_step (delta_ktm (wrap_prefix_patch
        (encoding_wrap A pack m S) table N))"
      and pre: "\<forall>q. snd (ktc_state x) \<noteq> W_Run q"
  shows "y1 = y2"
proof (rule ktm_step_det_at[OF _ one two])
  fix a p1 b1 d1 p2 b2 d2
  assume t1: "(ktc_state x, a, p1, b1, d1) \<in> delta_ktm (wrap_prefix_patch
        (encoding_wrap A pack m S) table N)"
    and t2: "(ktc_state x, a, p2, b2, d2) \<in> delta_ktm (wrap_prefix_patch
        (encoding_wrap A pack m S) table N)"
  obtain first s where x: "ktc_state x = (first, s)" by (cases "ktc_state x") auto
  obtain r1 where old1: "(s, a, r1, b1, d1) \<in> wrap_delta A pack m S"
    and p1: "p1 = wrap_prefix_target (encoding_wrap A pack m S) table N first s a r1"
    using t1 by (auto simp: x wrap_prefix_delta_def)
  obtain r2 where old2: "(s, a, r2, b2, d2) \<in> wrap_delta A pack m S"
    and p2: "p2 = wrap_prefix_target (encoding_wrap A pack m S) table N first s a r2"
    using t2 by (auto simp: x wrap_prefix_delta_def)
  have "\<forall>q. s \<noteq> W_Run q" using pre by (simp add: x)
  then have "(r1, b1, d1) = (r2, b2, d2)"
    by (rule wrap_delta_non_W_Run_det[OF old1 old2])
  then show "(p1, b1, d1) = (p2, b2, d2)" by (simp add: p1 p2)
qed

lemma wrap_prefix_step_back_non_run:
  fixes A :: "('q, 'b) ktm"
  assumes step: "(x, y) \<in> ktm_step (delta_ktm (wrap_prefix_patch
        (encoding_wrap A pack m S) table N))"
      and later: "\<forall>q. snd (ktc_state y) \<noteq> W_Run q"
  shows "\<forall>q. snd (ktc_state x) \<noteq> W_Run q"
proof (intro allI notI)
  fix q assume run: "snd (ktc_state x) = W_Run q"
  from step obtain s ts n p' b d where src: "x = KConfig s ts n"
    and y: "y = KConfig p' (\<lambda>j. (ts j)(n j := b j)) (\<lambda>j. go_move (d j) (n j))"
    and tuple: "(s, \<lambda>j. ts j (n j), p', b, d) \<in>
      wrap_prefix_delta (encoding_wrap A pack m S) table N"
    by (cases rule: ktm_step.cases) auto
  obtain first q0 p where s: "s = (first, q0)"
    and p': "p' = wrap_prefix_target (encoding_wrap A pack m S) table N first
      q0 (\<lambda>j. ts j (n j)) p"
    and old0: "(q0, \<lambda>j. ts j (n j), p, b, d) \<in> delta_ktm (encoding_wrap A pack m S)"
    using tuple unfolding wrap_prefix_delta_def by blast
  have q0: "q0 = W_Run q" using run src s by simp
  have old: "(W_Run q, \<lambda>j. ts j (n j), p, b, d) \<in> wrap_delta A pack m S"
    using old0 q0 by simp
  obtain q' where "p = W_Run q'"
    using wrap_delta_W_Run_source_only_run[OF old] unfolding wrap_run_delta_def by auto
  moreover have "snd p' = p" unfolding p' by (rule wrap_prefix_target_non_buf) (simp add: q0)
  ultimately show False using later by (simp add: y)
qed

end
