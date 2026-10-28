theory Multitape_Run_Facts
  imports Multitape_Time_Convention
begin

section \<open>Facts about runs\<close>

text \<open>Everything here is about \<^const>\<open>ktm_step\<close>, \<^const>\<open>Lang_ktm\<close> or
  \<^const>\<open>valid_ktm\<close> and mentions no machine construction at all.  These
  are the facts that constructions over the substrate kept re-proving: the
  theories after this one (relabelling, embedding, endmarker normalisation
  and clocks) all build on them.  Nothing here depends on any of those
  theories, which is the property to preserve --- if a lemma added here starts
  needing a combinator, it belongs in the theory that defines the combinator
  instead.

  The groups are unrelated to each other and are together only because
  they share that entry condition: acceptance and parked heads, the
  frozen-tape fact, and where the heads start and how far they get.  The
  step-relation algebra and the determinism facts are not here but in
  \<open>Multitape_Substrate\<close>, because the alphabet transformations and the tape
  reductions need them and import only that.\<close>

subsection \<open>Acceptance and parked heads\<close>

text \<open>\<^const>\<open>Lang_ktm\<close> is defined by a reflexive-transitive closure reaching
  a configuration whose \<^emph>\<open>shape\<close> names the accepting state, while
  \<^const>\<open>accepts_in_time_ktm\<close> is defined by a bounded power reaching a
  configuration whose \<^emph>\<open>state\<close> is accepting.  They say the same thing once
  the bound is existentially closed, and saying so once is what lets a
  language theorem be read off a timing theorem instead of repeating its
  induction.\<close>

lemma Lang_ktm_iff:
  "w \<in> Lang_ktm M
     \<longleftrightarrow> set w \<subseteq> Sigma_ktm M \<and> (\<exists>n. accepts_in_time_ktm M w n)"
proof
  assume "w \<in> Lang_ktm M"
  then obtain w' p where wS: "set w \<subseteq> Sigma_ktm M"
    and r: "(init_config_ktm M w, KConfig (t_ktm M) w' p)
              \<in> (ktm_step (delta_ktm M))\<^sup>*"
    by (auto simp: Lang_ktm_def)
  from r obtain n where "(init_config_ktm M w, KConfig (t_ktm M) w' p)
                           \<in> (ktm_step (delta_ktm M)) ^^ n"
    by (auto simp: rtrancl_power)
  then have "accepts_in_time_ktm M w n"
    unfolding accepts_in_time_ktm_def by force
  with wS show "set w \<subseteq> Sigma_ktm M \<and> (\<exists>n. accepts_in_time_ktm M w n)"
    by blast
next
  assume "set w \<subseteq> Sigma_ktm M \<and> (\<exists>n. accepts_in_time_ktm M w n)"
  then obtain n where wS: "set w \<subseteq> Sigma_ktm M"
    and acc: "accepts_in_time_ktm M w n" by blast
  from acc obtain m c
    where r: "(init_config_ktm M w, c) \<in> (ktm_step (delta_ktm M)) ^^ m"
      and tc: "ktc_state c = t_ktm M"
    by (auto simp: accepts_in_time_ktm_def)
  from r have "(init_config_ktm M w, c) \<in> (ktm_step (delta_ktm M))\<^sup>*"
    by (auto simp: rtrancl_power)
  with tc wS show "w \<in> Lang_ktm M"
    by (cases c) (auto simp: Lang_ktm_def)
qed

text \<open>The introduction and elimination rules for both predicates, phrased
  with a run of a given length ending in the accepting state.  A proof that
  holds such a run concludes either predicate without unfolding a definition,
  and one that holds either predicate gets the run back.\<close>

lemma Lang_ktm_run:
  assumes "w \<in> Lang_ktm M"
  obtains n c where "(init_config_ktm M w, c) \<in> (ktm_step (delta_ktm M)) ^^ n"
    and "ktc_state c = t_ktm M"
proof -
  from assms obtain w' p
    where "(init_config_ktm M w, KConfig (t_ktm M) w' p)
             \<in> (ktm_step (delta_ktm M))\<^sup>*"
    by (auto simp: Lang_ktm_def)
  then obtain n
    where run: "(init_config_ktm M w, KConfig (t_ktm M) w' p)
                  \<in> (ktm_step (delta_ktm M)) ^^ n"
    by (auto simp: rtrancl_power)
  have st: "ktc_state (KConfig (t_ktm M) w' p) = t_ktm M" by simp
  from run st show ?thesis by (rule that)
qed

lemma accepts_in_timeI:
  assumes "(init_config_ktm M w, c) \<in> (ktm_step (delta_ktm M)) ^^ n"
      and "ktc_state c = t_ktm M" and "n \<le> T"
  shows "accepts_in_time_ktm M w T"
  using assms by (auto simp: accepts_in_time_ktm_def)

lemma accepts_in_timeE:
  assumes "accepts_in_time_ktm M w T"
  obtains n c where "n \<le> T"
    and "(init_config_ktm M w, c) \<in> (ktm_step (delta_ktm M)) ^^ n"
    and "ktc_state c = t_ktm M"
  using assms by (auto simp: accepts_in_time_ktm_def)

lemma Lang_ktmI:
  assumes w: "set w \<subseteq> Sigma_ktm M"
      and run: "(init_config_ktm M w, c) \<in> (ktm_step (delta_ktm M)) ^^ n"
      and st: "ktc_state c = t_ktm M"
  shows "w \<in> Lang_ktm M"
proof -
  from run have r: "(init_config_ktm M w, c) \<in> (ktm_step (delta_ktm M))\<^sup>*"
    by (auto simp: rtrancl_power)
  obtain p ts n' where cc: "c = KConfig p ts n'" by (cases c) auto
  with st have "c = KConfig (t_ktm M) ts n'" by simp
  with r w show ?thesis by (auto simp: Lang_ktm_def)
qed

text \<open>\<^bold>\<open>The heads beyond the tape count stay at the origin.\<close>
  \<^const>\<open>valid_config_ktm\<close> records that those tapes are blank but says
  nothing about where their heads are, and the widening needs to know ---
  its new tapes carry an endmarker in cell 0, so the machine reads that
  endmarker only if the head is there.  It is true for the same reason the
  tapes stay blank: \<^const>\<open>valid_ktm\<close>'s support invariant makes every
  transition stationary beyond the count, and the initial configuration parks
  every head at 0.  Kept as a separate predicate rather than folded into
  \<^const>\<open>valid_config_ktm\<close>, which is the substrate's and not ours.\<close>

definition heads_parked :: "nat \<Rightarrow> ('a, 'q) ktc_config \<Rightarrow> bool" where
  "heads_parked k c \<longleftrightarrow> (\<forall>j. k \<le> j \<longrightarrow> ktc_pos c j = 0)"

lemma heads_parked_init: "heads_parked k (init_config_ktm M w)"
  by (cases M) (simp add: heads_parked_def)

lemma heads_parked_step:
  assumes vM: "valid_ktm M"
      and hp: "heads_parked (k_ktm M) c"
      and step: "(c, c') \<in> ktm_step (delta_ktm M)"
  shows "heads_parked (k_ktm M) c'"
proof -
  from step obtain q ts n q' a d
    where c: "c = KConfig q ts n"
      and c': "c' = KConfig q' (\<lambda>j. (ts j)(n j := a j))
                              (\<lambda>j. go_move (d j) (n j))"
      and tr: "(q, \<lambda>j. ts j (n j), q', a, d) \<in> delta_ktm M"
    by (auto elim!: ktm_step.cases)
  show ?thesis
    unfolding heads_parked_def
  proof (intro allI impI)
    fix j assume j: "k_ktm M \<le> j"
    from valid_ktm_delta_support [OF vM tr j] have "d j = MoveN" by simp
    moreover from hp j c have "n j = 0" by (simp add: heads_parked_def)
    ultimately show "ktc_pos c' j = 0" using c' by simp
  qed
qed

lemma heads_parked_run:
  assumes vM: "valid_ktm M"
      and hp: "heads_parked (k_ktm M) c"
      and run: "(c, c') \<in> (ktm_step (delta_ktm M)) ^^ n"
  shows "heads_parked (k_ktm M) c'"
  using relpow_imp_rtrancl [OF run]
  by (induction rule: rtrancl_induct) (auto intro: hp heads_parked_step [OF vM])


subsection \<open>Freezing a tape\<close>

text \<open>The half of a two-machine composite that is \<^emph>\<open>not\<close> moving.  When two
  machines run side by side on disjoint tapes --- in lockstep or by turns ---
  every transition of the composite is an action of one factor extended over
  the other factor's tapes, and the extension has to be inert: read what is
  there, write it back, stay put.  The lemma says that such a tuple does
  exactly nothing to that tape.

  \<open>ktm_step_no_write_tape\<close> is the all-tapes version and is not usable here,
  because the moving factor does write.  The relativisation is stated
  \<^emph>\<open>per index\<close> rather than per set, which is the weaker hypothesis and the one
  a composite actually supplies: its arms are inert on a range of indices, and
  a range is just a conjunction of indices.

  \<^bold>\<open>The head is part of the claim, and is the half that does not come for
  free.\<close>  \<open>ktm_step_tape_off_head\<close> already gives cell preservation away from
  the head, so the tape contents would follow from the write component alone.
  The head position would not --- and a frozen tape must keep its head where it
  was, or the factor's next turn resumes in the wrong place.  It is the
  direction component that carries that, which is why the hypothesis names
  both.\<close>

lemma ktm_step_frozen_tape:
  assumes step: "(c, c') \<in> ktm_step \<delta>"
    and frozen: "\<forall>q a q' a' d. (q, a, q', a', d) \<in> \<delta>
                    \<longrightarrow> a' j = a j \<and> d j = MoveN"
  shows "ktc_tape c' j = ktc_tape c j \<and> ktc_pos c' j = ktc_pos c j"
proof -
  from step obtain q ts n q' a dr where
      c_eq:  "c = KConfig q ts n"
    and c'_eq: "c' = KConfig q'
                       (\<lambda>k. (ts k)(n k := a k))
                       (\<lambda>k. go_move (dr k) (n k))"
    and tr: "(q, \<lambda>k. ts k (n k), q', a, dr) \<in> \<delta>"
    by (auto elim: ktm_step.cases)
  from frozen [rule_format, OF tr] have aj: "a j = ts j (n j)"
    and dj: "dr j = MoveN"
    by simp_all
  from aj have "(ts j)(n j := a j) = ts j" by auto
  moreover from dj have "go_move (dr j) (n j) = n j" by simp
  ultimately show ?thesis by (simp add: c_eq c'_eq)
qed


subsection \<open>Every head starts at the origin\<close>

text \<open>\<^bold>\<open>\<open>ktc_pos_init_config\<close> paired with
  \<open>ktm_relpow_pos_displacement\<close>, because the caller should not have to
  write the step count twice.\<close>  The pairing is what turns a step count into a
  head bound --- the reason a run lemma need not report a head it never
  promised.  A head that starts at the origin and moves at most
  one cell a step is bounded by \<^emph>\<open>any\<close> bound on the step count, so a phase
  that already reports its cost reports every head it never mentioned.  Stated
  over an abstract \<^term>\<open>n\<close> and \<^term>\<open>B\<close> rather than inline at the call site:
  the counts this composes with are twenty-line terms, and quoting one to
  instantiate \<open>ktm_relpow_pos_displacement\<close> and again to bound it invites
  the two copies to be spelled differently.\<close>

lemma ktm_relpow_pos_bound:
  assumes run: "(init_config_ktm M w, Z) \<in> (ktm_step (delta_ktm M)) ^^ n"
      and nB: "n \<le> B"
  shows "ktc_pos Z k \<le> B"
proof -
  have "ktc_pos Z k \<le> ktc_pos (init_config_ktm M w) k + n"
    using ktm_relpow_pos_displacement [OF run, of k] by blast
  then have "ktc_pos Z k \<le> n" by simp
  with nB show ?thesis by simp
qed


end
