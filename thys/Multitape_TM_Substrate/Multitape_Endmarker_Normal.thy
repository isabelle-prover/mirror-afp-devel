theory Multitape_Endmarker_Normal
  imports Multitape_Run_Facts
begin

section \<open>Restoring the endmarker discipline\<close>

text \<open>@{const le_unique} asks that a transition write the left endmarker on a
  tape only where it reads one.  It is a hypothesis of the tape reduction
  and hence of everything built on it, but it is not part of what a machine
  \<^emph>\<open>is\<close>: a valid machine may write the endmarker anywhere, and validity
  only pins what happens when one is read --- it is rewritten, and the head
  does not move left.  So an endmarker written away from cell 0 is inert
  except as a symbol that sends the head right.

  \<open>endmarker_normal M\<close> separates the two roles.  Its alphabet is \<open>'a option\<close>, with
  \<^term>\<open>None\<close> a second endmarker: every endmarker \<open>M\<close> writes where it does
  not read the real one becomes \<^term>\<open>None\<close>, and each transition of \<open>M\<close>
  is replicated for every way of reading its endmarkers as the real one or
  as \<^term>\<open>None\<close>.  The copy is valid, satisfies @{const le_unique}, and runs
  step for step with \<open>M\<close> on the words \<open>map Some w\<close>: decoding \<^term>\<open>None\<close>
  to the endmarker maps its runs to \<open>M\<close>'s, and encoding \<open>M\<close>'s tapes maps
  \<open>M\<close>'s runs to its own, because cell 0 of every tape holds the real
  endmarker throughout (\<open>ktm_relpow_LE_pos0_preserve\<close>).

  The same renaming separates a blank that \<^emph>\<open>is\<close> the endmarker.  Validity
  allows it, and such a machine treats every blank cell as an endmarker; the
  copy's blank is then \<^term>\<open>None\<close>, which is what those cells are anyway.  So
  the copy also satisfies the substrate's other endmarker condition,
  blank and endmarker distinct, for every valid machine.\<close>

subsection \<open>The combinator\<close>

definition endmarker_reads :: "'a \<Rightarrow> (nat \<Rightarrow> 'a) \<Rightarrow> (nat \<Rightarrow> 'a option) set" where
  "endmarker_reads le a = {b. \<forall>j. b j = Some (a j) \<or> (a j = le \<and> b j = None)}"

definition endmarker_write :: "'a \<Rightarrow> (nat \<Rightarrow> 'a option) \<Rightarrow> (nat \<Rightarrow> 'a) \<Rightarrow> nat \<Rightarrow> 'a option"
  where
  "endmarker_write le b a' j = (if a' j = le \<and> b j \<noteq> Some le then None else Some (a' j))"

text \<open>The copy's blank: the original one, unless it is the endmarker.\<close>

definition endmarker_blank :: "'a \<Rightarrow> 'a \<Rightarrow> 'a option" where
  "endmarker_blank le bl = (if bl = le then None else Some bl)"

text \<open>Above the tape count validity pins every read to the blank, so there the
  copy reads its own blank and nothing else.\<close>

definition endmarker_normal_delta ::
  "'a \<Rightarrow> 'a option \<Rightarrow> nat
     \<Rightarrow> ('q \<times> (nat \<Rightarrow> 'a) \<times> 'q \<times> (nat \<Rightarrow> 'a) \<times> (nat \<Rightarrow> move)) set
     \<Rightarrow> ('q \<times> (nat \<Rightarrow> 'a option) \<times> 'q \<times> (nat \<Rightarrow> 'a option) \<times> (nat \<Rightarrow> move)) set"
  where
  "endmarker_normal_delta le nb k D =
     {(q, b, q', endmarker_write le b a', d) | q a q' a' d b.
        (q, a, q', a', d) \<in> D \<and> b \<in> endmarker_reads le a \<and> (\<forall>j\<ge>k. b j = nb)}"

definition endmarker_normal :: "('q, 'a) ktm \<Rightarrow> ('q, 'a option) ktm" where
  "endmarker_normal M =
     KTM
       (Q_ktm M)
       (Some ` Sigma_ktm M)
       (insert None (Some ` \<Gamma>_ktm M))
       (endmarker_blank (le_ktm M) (bl_ktm M))
       (Some (le_ktm M))
       (endmarker_normal_delta (le_ktm M) (endmarker_blank (le_ktm M) (bl_ktm M)) (k_ktm M) (delta_ktm M))
       (s_ktm M)
       (t_ktm M)
       (r_ktm M)
       (k_ktm M)"

lemma endmarker_normal_fields [simp]:
  "Q_ktm (endmarker_normal M) = Q_ktm M"
  "Sigma_ktm (endmarker_normal M) = Some ` Sigma_ktm M"
  "\<Gamma>_ktm (endmarker_normal M) = insert None (Some ` \<Gamma>_ktm M)"
  "bl_ktm (endmarker_normal M) = endmarker_blank (le_ktm M) (bl_ktm M)"
  "le_ktm (endmarker_normal M) = Some (le_ktm M)"
  "delta_ktm (endmarker_normal M) = endmarker_normal_delta (le_ktm M) (endmarker_blank (le_ktm M) (bl_ktm M)) (k_ktm M) (delta_ktm M)"
  "s_ktm (endmarker_normal M) = s_ktm M"
  "t_ktm (endmarker_normal M) = t_ktm M"
  "r_ktm (endmarker_normal M) = r_ktm M"
  "k_ktm (endmarker_normal M) = k_ktm M"
  by (simp_all add: endmarker_normal_def)

lemma endmarker_normal_delta_I:
  "(q, a, q', a', d) \<in> D \<Longrightarrow> b \<in> endmarker_reads le a \<Longrightarrow> (\<And>j. k \<le> j \<Longrightarrow> b j = nb)
     \<Longrightarrow> (q, b, q', endmarker_write le b a', d) \<in> endmarker_normal_delta le nb k D"
  unfolding endmarker_normal_delta_def by blast

lemma endmarker_normal_delta_E:
  assumes "(q, b, q', b', d) \<in> endmarker_normal_delta le nb k D"
  obtains a a' where "(q, a, q', a', d) \<in> D" and "b \<in> endmarker_reads le a"
    and "\<And>j. k \<le> j \<Longrightarrow> b j = nb" and "b' = endmarker_write le b a'"
  using assms unfolding endmarker_normal_delta_def by blast

lemma endmarker_blank_simps [simp]:
  "bl = le \<Longrightarrow> endmarker_blank le bl = None"
  "bl \<noteq> le \<Longrightarrow> endmarker_blank le bl = Some bl"
  "endmarker_blank le bl \<noteq> Some le"
  by (simp_all add: endmarker_blank_def)


subsection \<open>Validity and the discipline\<close>

lemma endmarker_normal_valid:
  assumes vM: "valid_ktm M"
  shows "valid_ktm (endmarker_normal M)"
proof (cases M)
  case M_eq: (KTM Q Sg Gm bl le D s t r k)
  have V0: "valid_ktm (KTM Q Sg Gm bl le D s t r k)" using vM by (simp only: M_eq)
  note V = V0 [unfolded valid_ktm.simps]
  have v: "finite Q" "finite Gm" "Sg \<subseteq> Gm" "s \<in> Q" "t \<in> Q" "r \<in> Q"
    "bl \<in> Gm" "bl \<notin> Sg" "le \<in> Gm" "le \<notin> Sg" "t \<noteq> r" "0 < k"
    using V by simp_all
  have Dsub: "D \<subseteq> (Q - {t, r}) \<times> (UNIV \<rightarrow> Gm) \<times> Q \<times> (UNIV \<rightarrow> Gm) \<times> (UNIV \<rightarrow> UNIV)"
    using V by (simp only:)
  have Dle: "a' j = le \<and> d j \<in> {MoveN, MoveR}"
    if "(q, a, q', a', d) \<in> D" and "a j = le" for q a q' a' d j
    using V that by blast
  have Dk: "a j = bl \<and> a' j = bl \<and> d j = MoveN"
    if "(q, a, q', a', d) \<in> D" and "k \<le> j" for q a q' a' d j
    using V that by blast
  define nb where "nb = endmarker_blank le bl"
  have F: "endmarker_normal M = KTM Q (Some ` Sg) (insert None (Some ` Gm)) nb (Some le)
             (endmarker_normal_delta le nb k D) s t r k"
    using M_eq by (simp add: endmarker_normal_def nb_def)
  have nbG: "nb \<in> insert None (Some ` Gm)" using v(7) by (simp add: nb_def endmarker_blank_def)
  have nbS: "nb \<notin> Some ` Sg" using v(8) by (auto simp: nb_def endmarker_blank_def)
  have sub: "endmarker_normal_delta le nb k D
               \<subseteq> (Q - {t, r}) \<times> (UNIV \<rightarrow> insert None (Some ` Gm)) \<times> Q
                   \<times> (UNIV \<rightarrow> insert None (Some ` Gm)) \<times> (UNIV \<rightarrow> UNIV)"
  proof
    fix x assume "x \<in> endmarker_normal_delta le nb k D"
    then obtain q b q' a a' d where x: "x = (q, b, q', endmarker_write le b a', d)"
      and tr: "(q, a, q', a', d) \<in> D" and b: "b \<in> endmarker_reads le a"
      unfolding endmarker_normal_delta_def by blast
    from tr Dsub have "q \<in> Q - {t, r}" "q' \<in> Q" "\<And>j. a j \<in> Gm" "\<And>j. a' j \<in> Gm"
      by (auto simp: Pi_def)
    moreover have "b j \<in> insert None (Some ` Gm)" for j
    proof -
      have "b j = Some (a j) \<or> (a j = le \<and> b j = None)"
        using b unfolding endmarker_reads_def by blast
      then show ?thesis using \<open>\<And>j. a j \<in> Gm\<close> by auto
    qed
    moreover have "endmarker_write le b a' j \<in> insert None (Some ` Gm)" for j
      using \<open>\<And>j. a' j \<in> Gm\<close> unfolding endmarker_write_def by auto
    ultimately show "x \<in> (Q - {t, r}) \<times> (UNIV \<rightarrow> insert None (Some ` Gm)) \<times> Q
                       \<times> (UNIV \<rightarrow> insert None (Some ` Gm)) \<times> (UNIV \<rightarrow> UNIV)"
      unfolding x by auto
  qed
  have lecond: "b' j = Some le \<and> d j \<in> {MoveN, MoveR}"
    if "(q, b, q', b', d) \<in> endmarker_normal_delta le nb k D" and "b j = Some le" for q b q' b' d j
  proof -
    from that(1) obtain a a' where tr: "(q, a, q', a', d) \<in> D"
      and b: "b \<in> endmarker_reads le a" and "\<And>j. k \<le> j \<Longrightarrow> b j = nb"
      and b': "b' = endmarker_write le b a'"
      by (rule endmarker_normal_delta_E) blast
    have "b j = Some (a j) \<or> (a j = le \<and> b j = None)"
      using b unfolding endmarker_reads_def by blast
    then have "a j = le" using that(2) by auto
    then have "a' j = le \<and> d j \<in> {MoveN, MoveR}" using Dle [OF tr] by blast
    then show ?thesis using b' that(2) unfolding endmarker_write_def by simp
  qed
  have kcond: "b j = nb \<and> b' j = nb \<and> d j = MoveN"
    if "(q, b, q', b', d) \<in> endmarker_normal_delta le nb k D" and "k \<le> j" for q b q' b' d j
  proof -
    from that(1) obtain a a' where tr: "(q, a, q', a', d) \<in> D"
      and "b \<in> endmarker_reads le a" and kb: "\<And>j. k \<le> j \<Longrightarrow> b j = nb"
      and b': "b' = endmarker_write le b a'"
      by (rule endmarker_normal_delta_E) blast
    have a: "a' j = bl \<and> d j = MoveN" using Dk [OF tr that(2)] by blast
    have bj: "b j = nb" by (rule kb [OF that(2)])
    have "b' j = nb"
      unfolding b' endmarker_write_def using a bj by (simp add: nb_def endmarker_blank_def)
    then show ?thesis using a bj by blast
  qed
  show ?thesis
    unfolding F valid_ktm.simps
    apply (intro conjI allI impI)
    using v nbG nbS sub lecond kcond by (blast | auto)+
qed

lemma endmarker_normal_le_unique: "le_unique (endmarker_normal M)"
  unfolding le_unique_def
proof (intro allI impI)
  fix q b q' b' d j
  assume tr: "(q, b, q', b', d) \<in> delta_ktm (endmarker_normal M)"
    and w: "b' j = le_ktm (endmarker_normal M)"
  from tr obtain a a' where "b' = endmarker_write (le_ktm M) b a'"
    by (auto elim: endmarker_normal_delta_E)
  with w show "b j = le_ktm (endmarker_normal M)"
    unfolding endmarker_write_def by (auto split: if_splits)
qed

lemma endmarker_normal_bl_le: "bl_ktm (endmarker_normal M) \<noteq> le_ktm (endmarker_normal M)"
  by simp

subsection \<open>Decoding: every run of the copy is a run of the machine\<close>

definition endmarker_dec :: "'a \<Rightarrow> 'a option \<Rightarrow> 'a" where
  "endmarker_dec le x = (case x of None \<Rightarrow> le | Some a \<Rightarrow> a)"

lemma endmarker_dec_simps [simp]:
  "endmarker_dec le (Some a) = a"
  "endmarker_dec le None = le"
  by (simp_all add: endmarker_dec_def)

definition endmarker_dec_config :: "'a \<Rightarrow> ('a option, 'q) ktc_config \<Rightarrow> ('a, 'q) ktc_config"
  where
  "endmarker_dec_config le c = KConfig (ktc_state c) (\<lambda>j p. endmarker_dec le (ktc_tape c j p)) (ktc_pos c)"

lemma endmarker_dec_config_simps [simp]:
  "ktc_state (endmarker_dec_config le c) = ktc_state c"
  "ktc_pos (endmarker_dec_config le c) = ktc_pos c"
  by (simp_all add: endmarker_dec_config_def)

lemma endmarker_dec_blank [simp]: "endmarker_dec le (endmarker_blank le bl) = bl"
  by (simp add: endmarker_blank_def)

lemma endmarker_dec_reads:
  assumes "b \<in> endmarker_reads le a"
  shows "(\<lambda>j. endmarker_dec le (b j)) = a"
proof
  fix j
  have "b j = Some (a j) \<or> (a j = le \<and> b j = None)"
    using assms unfolding endmarker_reads_def by blast
  then show "endmarker_dec le (b j) = a j" by auto
qed

lemma endmarker_dec_write: "endmarker_dec le (endmarker_write le b a' j) = a' j"
  unfolding endmarker_write_def by simp

lemma endmarker_normal_step_rev:
  assumes "(c, c') \<in> ktm_step (delta_ktm (endmarker_normal M))"
  shows "(endmarker_dec_config (le_ktm M) c, endmarker_dec_config (le_ktm M) c') \<in> ktm_step (delta_ktm M)"
  using assms
proof (cases rule: ktm_step.cases)
  case (step q ts n q' b' move)
  from step(3) obtain a a' where tr: "(q, a, q', a', move) \<in> delta_ktm M"
    and rd: "(\<lambda>j. ts j (n j)) \<in> endmarker_reads (le_ktm M) a"
    and wr: "b' = endmarker_write (le_ktm M) (\<lambda>j. ts j (n j)) a'"
    by (auto elim!: endmarker_normal_delta_E)
  have a_eq: "(\<lambda>j. endmarker_dec (le_ktm M) (ts j (n j))) = a" by (rule endmarker_dec_reads [OF rd])
  have "(KConfig q (\<lambda>j p. endmarker_dec (le_ktm M) (ts j p)) n,
         KConfig q' (\<lambda>j. (\<lambda>p. endmarker_dec (le_ktm M) (ts j p))(n j := a' j))
                    (\<lambda>j. go_move (move j) (n j)))
          \<in> ktm_step (delta_ktm M)"
  proof (rule ktm_step.step)
    show "(q, \<lambda>j. (\<lambda>p. endmarker_dec (le_ktm M) (ts j p)) (n j), q', a', move) \<in> delta_ktm M"
      using tr a_eq by simp
  qed
  moreover have "(\<lambda>j p. endmarker_dec (le_ktm M) (((ts j)(n j := b' j)) p))
                   = (\<lambda>j. (\<lambda>p. endmarker_dec (le_ktm M) (ts j p))(n j := a' j))"
    unfolding wr by (simp add: fun_eq_iff endmarker_dec_write)
  ultimately show ?thesis
    using step(1,2) by (simp add: endmarker_dec_config_def)
qed

lemma endmarker_normal_run_rev:
  assumes "(c, c') \<in> (ktm_step (delta_ktm (endmarker_normal M))) ^^ n"
  shows "(endmarker_dec_config (le_ktm M) c, endmarker_dec_config (le_ktm M) c') \<in> (ktm_step (delta_ktm M)) ^^ n"
  using assms
proof (induct n arbitrary: c')
  case 0 then show ?case by simp
next
  case (Suc n)
  from Suc.prems obtain e where ce: "(c, e) \<in> (ktm_step (delta_ktm (endmarker_normal M))) ^^ n"
    and ec': "(e, c') \<in> ktm_step (delta_ktm (endmarker_normal M))" by auto
  from Suc.hyps [OF ce] endmarker_normal_step_rev [OF ec'] show ?case by auto
qed

lemma endmarker_dec_init_config:
  "endmarker_dec_config (le_ktm M) (init_config_ktm (endmarker_normal M) (map Some w)) = init_config_ktm M w"
proof (cases M)
  case (KTM Q Sg Gm bl le D s t r k)
  then show ?thesis
    by (auto simp: endmarker_normal_def endmarker_dec_config_def fun_eq_iff)
qed

lemma endmarker_normal_accepts_in_time_rev:
  assumes "accepts_in_time_ktm (endmarker_normal M) (map Some w) n"
  shows "accepts_in_time_ktm M w n"
proof -
  from assms obtain m c
    where m: "m \<le> n"
      and run: "(init_config_ktm (endmarker_normal M) (map Some w), c)
                  \<in> (ktm_step (delta_ktm (endmarker_normal M))) ^^ m"
      and acc: "ktc_state c = t_ktm (endmarker_normal M)"
    by (auto simp: accepts_in_time_ktm_def)
  from endmarker_normal_run_rev [OF run]
  have "(init_config_ktm M w, endmarker_dec_config (le_ktm M) c) \<in> (ktm_step (delta_ktm M)) ^^ m"
    by (simp add: endmarker_dec_init_config)
  moreover have "ktc_state (endmarker_dec_config (le_ktm M) c) = t_ktm M" using acc by simp
  ultimately show ?thesis
    unfolding accepts_in_time_ktm_def using m by blast
qed

subsection \<open>Encoding: every run of the machine is a run of the copy\<close>

text \<open>An endmarker away from cell 0 is encoded as \<^term>\<open>None\<close>, and so is
  one on a tape at or above the tape count, where it can only be a blank that
  is the endmarker.  The step goes through because cell 0 of every tape below
  the tape count holds the real endmarker, so a transition that writes the
  endmarker at cell 0 is reading the real one there; above the tape count
  every read and write is a blank.\<close>

definition endmarker_enc :: "'a \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> 'a option" where
  "endmarker_enc le k j p x = (if (p \<noteq> 0 \<or> k \<le> j) \<and> x = le then None else Some x)"

definition endmarker_enc_config :: "'a \<Rightarrow> nat \<Rightarrow> ('a, 'q) ktc_config \<Rightarrow> ('a option, 'q) ktc_config"
  where
  "endmarker_enc_config le k c =
     KConfig (ktc_state c) (\<lambda>j p. endmarker_enc le k j p (ktc_tape c j p)) (ktc_pos c)"

lemma endmarker_enc_config_state [simp]: "ktc_state (endmarker_enc_config le k c) = ktc_state c"
  by (simp add: endmarker_enc_config_def)

lemma endmarker_normal_step:
  assumes vM: "valid_ktm M"
      and st: "(c, c') \<in> ktm_step (delta_ktm M)"
      and at0: "\<And>j. j < k_ktm M \<Longrightarrow> ktc_tape c j 0 = le_ktm M"
  shows "(endmarker_enc_config (le_ktm M) (k_ktm M) c, endmarker_enc_config (le_ktm M) (k_ktm M) c')
           \<in> ktm_step (delta_ktm (endmarker_normal M))"
  using st
proof (cases rule: ktm_step.cases)
  case (step q ts n q' a' move)
  let ?le = "le_ktm M" and ?k = "k_ktm M" and ?nb = "endmarker_blank (le_ktm M) (bl_ktm M)"
  define b where "b j = endmarker_enc ?le ?k j (n j) (ts j (n j))" for j
  have rd: "b \<in> endmarker_reads ?le (\<lambda>j. ts j (n j))"
    unfolding endmarker_reads_def b_def endmarker_enc_def by auto
  have sup: "ts j (n j) = bl_ktm M \<and> a' j = bl_ktm M" if "?k \<le> j" for j
    using valid_ktm_delta_support [OF vM step(3) that] by simp
  have kb: "b j = ?nb" if "?k \<le> j" for j
    using sup [OF that] that by (simp add: b_def endmarker_enc_def endmarker_blank_def)
  have tr': "(q, b, q', endmarker_write ?le b a', move) \<in> delta_ktm (endmarker_normal M)"
    using endmarker_normal_delta_I [OF step(3) rd kb] by simp
  have wr: "endmarker_write ?le b a' j = endmarker_enc ?le ?k j (n j) (a' j)" for j
  proof (cases "?k \<le> j")
    case True
    then show ?thesis
      using sup [OF True] kb [OF True] by (simp add: endmarker_write_def endmarker_enc_def endmarker_blank_def)
  next
    case False
    then have jk: "j < ?k" by simp
    show ?thesis
    proof (cases "n j = 0")
      case n0: True
      have "ts j 0 = ?le" using at0 [OF jk] step(1) by simp
      then have "b j = Some ?le" unfolding b_def endmarker_enc_def using n0 jk by simp
      then show ?thesis unfolding endmarker_write_def endmarker_enc_def using n0 jk by simp
    next
      case False
      have "b j \<noteq> Some ?le" unfolding b_def endmarker_enc_def using False by simp
      then show ?thesis unfolding endmarker_write_def endmarker_enc_def using False by simp
    qed
  qed
  have "(KConfig q (\<lambda>j p. endmarker_enc ?le ?k j p (ts j p)) n,
         KConfig q' (\<lambda>j. (\<lambda>p. endmarker_enc ?le ?k j p (ts j p))(n j := endmarker_write ?le b a' j))
                    (\<lambda>j. go_move (move j) (n j)))
          \<in> ktm_step (delta_ktm (endmarker_normal M))"
  proof (rule ktm_step.step)
    show "(q, \<lambda>j. (\<lambda>p. endmarker_enc ?le ?k j p (ts j p)) (n j), q',
             \<lambda>j. endmarker_write ?le b a' j, move) \<in> delta_ktm (endmarker_normal M)"
      using tr' unfolding b_def by simp
  qed
  moreover have "(\<lambda>j p. endmarker_enc ?le ?k j p (((ts j)(n j := a' j)) p))
                   = (\<lambda>j. (\<lambda>p. endmarker_enc ?le ?k j p (ts j p))(n j := endmarker_write ?le b a' j))"
    by (simp add: fun_eq_iff wr)
  ultimately show ?thesis
    using step(1,2) by (simp add: endmarker_enc_config_def)
qed

lemma endmarker_normal_run:
  assumes vM: "valid_ktm M"
      and run: "(c, c') \<in> (ktm_step (delta_ktm M)) ^^ n"
      and at0: "\<And>j. j < k_ktm M \<Longrightarrow> ktc_tape c j 0 = le_ktm M"
  shows "(endmarker_enc_config (le_ktm M) (k_ktm M) c, endmarker_enc_config (le_ktm M) (k_ktm M) c')
           \<in> (ktm_step (delta_ktm (endmarker_normal M))) ^^ n"
proof (rule relpow_map [where h = "endmarker_enc_config (le_ktm M) (k_ktm M)", OF _ run])
  fix m e e'
  assume ce: "(c, e) \<in> (ktm_step (delta_ktm M)) ^^ m"
     and ee': "(e, e') \<in> ktm_step (delta_ktm M)"
  have at0e: "ktc_tape e j 0 = le_ktm M" if "j < k_ktm M" for j
    by (rule ktm_relpow_LE_pos0_preserve [OF vM ce at0 [OF that]])
  show "(endmarker_enc_config (le_ktm M) (k_ktm M) e,
         endmarker_enc_config (le_ktm M) (k_ktm M) e')
          \<in> ktm_step (delta_ktm (endmarker_normal M))"
    by (rule endmarker_normal_step [OF vM ee' at0e])
qed

lemma endmarker_enc_init_config:
  assumes vM: "valid_ktm M" and w: "set w \<subseteq> Sigma_ktm M"
  shows "endmarker_enc_config (le_ktm M) (k_ktm M) (init_config_ktm M w)
           = init_config_ktm (endmarker_normal M) (map Some w)"
proof (cases M)
  case M_eq: (KTM Q Sg Gm bl le D s t r k)
  have wle: "w ! i \<noteq> le" if "i < length w" for i
    using valid_ktm_LE_not_Sigma [OF vM] w nth_mem [OF that] M_eq by auto
  have wle': "(w ! (p - Suc 0) = le) = False" if "0 < p" and "p \<le> length w" for p
    using wle [of "p - Suc 0"] that by simp
  have mapS: "map Some w ! (p - Suc 0) = Some (w ! (p - Suc 0))"
    if "0 < p" and "p \<le> length w" for p
    using that by simp
  show ?thesis
  proof (cases "bl = le")
    case True
    then show ?thesis
      using M_eq by (simp add: endmarker_normal_def endmarker_enc_config_def endmarker_enc_def fun_eq_iff wle' mapS)
  next
    case False
    then have bl: "(bl = le) = False" by simp
    show ?thesis
      using M_eq by (simp add: endmarker_normal_def endmarker_enc_config_def endmarker_enc_def fun_eq_iff wle' mapS bl)
  qed
qed

lemma init_config_at0:
  "j < k_ktm M \<Longrightarrow> ktc_tape (init_config_ktm M w) j 0 = le_ktm M"
  by (cases M) simp

lemma endmarker_normal_accepts_in_time:
  assumes vM: "valid_ktm M"
      and w: "set w \<subseteq> Sigma_ktm M"
      and acc: "accepts_in_time_ktm M w n"
  shows "accepts_in_time_ktm (endmarker_normal M) (map Some w) n"
proof -
  from acc obtain m c
    where m: "m \<le> n"
      and run: "(init_config_ktm M w, c) \<in> (ktm_step (delta_ktm M)) ^^ m"
      and tc: "ktc_state c = t_ktm M"
    by (auto simp: accepts_in_time_ktm_def)
  from endmarker_normal_run [OF vM run init_config_at0]
  have "(init_config_ktm (endmarker_normal M) (map Some w), endmarker_enc_config (le_ktm M) (k_ktm M) c)
          \<in> (ktm_step (delta_ktm (endmarker_normal M))) ^^ m"
    by (simp add: endmarker_enc_init_config [OF vM w])
  moreover have "ktc_state (endmarker_enc_config (le_ktm M) (k_ktm M) c) = t_ktm (endmarker_normal M)"
    using tc by simp
  ultimately show ?thesis
    unfolding accepts_in_time_ktm_def using m by blast
qed

subsection \<open>The headline\<close>

theorem endmarker_normal_lang:
  assumes vM: "valid_ktm M"
  shows "Lang_ktm (endmarker_normal M) = map Some ` Lang_ktm M"
proof (rule set_eqI, rule iffI)
  fix v assume v: "v \<in> Lang_ktm (endmarker_normal M)"
  then have "v \<in> lists (Some ` Sigma_ktm M)" by (auto simp: Lang_ktm_def)
  then obtain w where wv: "v = map Some w" and w: "set w \<subseteq> Sigma_ktm M"
    by (auto simp: lists_image)
  from v wv obtain e j
    where "(init_config_ktm (endmarker_normal M) (map Some w), e)
             \<in> (ktm_step (delta_ktm (endmarker_normal M))) ^^ j"
      and te: "ktc_state e = t_ktm (endmarker_normal M)"
    by (auto simp: Lang_ktm_def rtrancl_power)
  then have "accepts_in_time_ktm (endmarker_normal M) (map Some w) j"
    unfolding accepts_in_time_ktm_def by blast
  from endmarker_normal_accepts_in_time_rev [OF this]
  obtain i c where "i \<le> j"
    and "(init_config_ktm M w, c) \<in> (ktm_step (delta_ktm M)) ^^ i"
    and "ktc_state c = t_ktm M"
    by (auto simp: accepts_in_time_ktm_def)
  then have "w \<in> Lang_ktm M"
    using w by (cases c) (auto simp: Lang_ktm_def rtrancl_power)
  with wv show "v \<in> map Some ` Lang_ktm M" by blast
next
  fix v assume "v \<in> map Some ` Lang_ktm M"
  then obtain w where wv: "v = map Some w" and w: "w \<in> Lang_ktm M" by blast
  from w have wS: "set w \<subseteq> Sigma_ktm M" by (simp add: Lang_ktm_def)
  from w obtain c j where run: "(init_config_ktm M w, c) \<in> (ktm_step (delta_ktm M)) ^^ j"
    and tc: "ktc_state c = t_ktm M"
    by (cases M) (auto simp: Lang_ktm_def rtrancl_power)
  then have "accepts_in_time_ktm M w j"
    unfolding accepts_in_time_ktm_def by blast
  from endmarker_normal_accepts_in_time [OF vM wS this]
  obtain i e where "i \<le> j"
    and "(init_config_ktm (endmarker_normal M) (map Some w), e)
           \<in> (ktm_step (delta_ktm (endmarker_normal M))) ^^ i"
    and "ktc_state e = t_ktm (endmarker_normal M)"
    by (auto simp: accepts_in_time_ktm_def)
  moreover have "set (map Some w) \<subseteq> Sigma_ktm (endmarker_normal M)" using wS by auto
  ultimately show "v \<in> Lang_ktm (endmarker_normal M)"
    unfolding wv by (cases e) (auto simp: Lang_ktm_def rtrancl_power)
qed

end
