theory Multitape_Relabelling
  imports Multitape_Run_Facts
begin

section \<open>Transporting a machine along injections\<close>

text \<open>Many constructions on machines change the machine's \<^emph>\<open>type\<close> as well
  as its behaviour: \<open>alphabet_enlarge\<close> in \<open>Multitape_Alphabet_Enlargement\<close>,
  for instance, takes a \<open>('q, 'a) ktm\<close> to a machine over a block alphabet
  \<open>'c \<Rightarrow> 'a\<close>.  That is the right design for results whose statements
  quantify over the source machine's type.  It is the wrong shape for anything
  that must collect machines in one concrete type, such as an enumeration
  \<open>nat \<Rightarrow> (nat, nat) ktm\<close>.  HOL has no quantification over types, so a
  class of machines "with any alphabet" has to be represented by a fixed
  universe of machines that is shown to be complete.

  This theory is the bridge.  A machine is transported along an injection on
  states and an injection on the tape alphabet, which changes only the names of
  things, and so preserves the language up to the alphabet map and the running
  time \<^emph>\<open>exactly\<close>.  Two field-level combinators on the tapes follow:
  \<open>widen_tapes\<close> raises the tape count, and \<open>swap_tapes\<close> exchanges two
  tapes.  Last comes the injection arithmetic that supplies the relabelling's
  hypotheses.

  \<open>Multitape_Run_Facts\<close> holds the facts about runs that mention no
  combinator, and this theory sits over it.  \<open>Multitape_Embedding\<close> holds the
  composite machinery, which builds no machine at all and is a
  \<^emph>\<open>sibling\<close> rather than a layer: neither theory cites the other.\<close>


subsection \<open>The combinator\<close>

text \<open>\<open>relabel_ktm f g M\<close> renames states along \<open>f\<close> and tape symbols along
  \<open>g\<close>.  Transition tuples are rewritten componentwise; the direction
  component is untouched, and the tape count is carried across, so the
  transported machine has the same tape count and the same branching
  structure.\<close>

definition relabel_delta ::
  "('q \<Rightarrow> 'p) \<Rightarrow> ('a \<Rightarrow> 'b)
     \<Rightarrow> ('q \<times> (nat \<Rightarrow> 'a) \<times> 'q \<times> (nat \<Rightarrow> 'a) \<times> (nat \<Rightarrow> move)) set
     \<Rightarrow> ('p \<times> (nat \<Rightarrow> 'b) \<times> 'p \<times> (nat \<Rightarrow> 'b) \<times> (nat \<Rightarrow> move)) set" where
  "relabel_delta f g D =
     (\<lambda>(q, a, q', a', d). (f q, g \<circ> a, f q', g \<circ> a', d)) ` D"

definition relabel_ktm ::
  "('q \<Rightarrow> 'p) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> ('q, 'a) ktm \<Rightarrow> ('p, 'b) ktm" where
  "relabel_ktm f g M =
     KTM
       (f ` Q_ktm M)
       (g ` Sigma_ktm M)
       (g ` \<Gamma>_ktm M)
       (g (bl_ktm M))
       (g (le_ktm M))
       (relabel_delta f g (delta_ktm M))
       (f (s_ktm M))
       (f (t_ktm M))
       (f (r_ktm M))
       (k_ktm M)"


subsection \<open>Structural preservation\<close>

text \<open>The selectors go through by construction; these are the lemmas every
  downstream hypothesis discharge needs, and they should all be one-liners
  off \<^const>\<open>relabel_ktm\<close>'s definition.\<close>

lemma relabel_Q_ktm [simp]: "Q_ktm (relabel_ktm f g M) = f ` Q_ktm M"
  by (simp add: relabel_ktm_def)

lemma relabel_k_ktm [simp]: "k_ktm (relabel_ktm f g M) = k_ktm M"
  by (simp add: relabel_ktm_def)

lemma relabel_Sigma_ktm [simp]:
  "Sigma_ktm (relabel_ktm f g M) = g ` Sigma_ktm M"
  by (simp add: relabel_ktm_def)

lemma relabel_Gamma_ktm [simp]:
  "\<Gamma>_ktm (relabel_ktm f g M) = g ` \<Gamma>_ktm M"
  by (simp add: relabel_ktm_def)

lemma relabel_bl_ktm [simp]: "bl_ktm (relabel_ktm f g M) = g (bl_ktm M)"
  by (simp add: relabel_ktm_def)

lemma relabel_le_ktm [simp]: "le_ktm (relabel_ktm f g M) = g (le_ktm M)"
  by (simp add: relabel_ktm_def)

lemma relabel_s_ktm [simp]: "s_ktm (relabel_ktm f g M) = f (s_ktm M)"
  by (simp add: relabel_ktm_def)

lemma relabel_t_ktm [simp]: "t_ktm (relabel_ktm f g M) = f (t_ktm M)"
  by (simp add: relabel_ktm_def)

lemma relabel_r_ktm [simp]: "r_ktm (relabel_ktm f g M) = f (r_ktm M)"
  by (simp add: relabel_ktm_def)


subsection \<open>Validity\<close>

text \<open>Validity transports under injectivity on the two carriers.  Both
  injectivity hypotheses are needed and neither is decorative: \<open>f\<close> injective
  keeps \<open>t \<noteq> r\<close> apart, and \<open>g\<close> injective keeps \<open>bl \<notin> \<Sigma>\<close>, \<open>le \<notin> \<Sigma>\<close> and the
  left-endmarker discipline intact.  Injectivity is asked for only \<^emph>\<open>on the
  machine's own carriers\<close> rather than globally, which is what lets the
  enumeration's encoding be a partial numbering.\<close>

lemma relabel_source:
  assumes "(q, a, q', a', d) \<in> relabel_delta f g D"
  obtains p b p' b'
  where "(p, b, p', b', d) \<in> D"
    and "q = f p" and "q' = f p'" and "a = g \<circ> b" and "a' = g \<circ> b'"
  using assms by (auto simp: relabel_delta_def)

lemma relabel_valid:
  assumes vM: "valid_ktm M"
      and injf: "inj_on f (Q_ktm M)"
      and injg: "inj_on g (\<Gamma>_ktm M)"
  shows "valid_ktm (relabel_ktm f g M)"
proof (cases M)
  case M_eq: (KTM Q Sg Gm bl le D s t r k)
  have R: "relabel_ktm f g M
             = KTM (f ` Q) (g ` Sg) (g ` Gm) (g bl) (g le)
                    (relabel_delta f g D) (f s) (f t) (f r) k"
    using M_eq by (simp add: relabel_ktm_def)
  have Qf: "inj_on f Q" and Gg: "inj_on g Gm"
    using injf injg M_eq by simp_all
  have base: "finite Q" "finite Gm" "Sg \<subseteq> Gm" "s \<in> Q" "t \<in> Q" "r \<in> Q"
             "bl \<in> Gm" "bl \<notin> Sg" "le \<in> Gm" "le \<notin> Sg" "t \<noteq> r" "0 < k"
    using vM M_eq by auto

  \<comment> \<open>the endmarker and blank stay outside the input alphabet only because
      \<open>g\<close> is injective on the whole tape alphabet, not merely on \<open>Sg\<close>\<close>
  have notin: "g x \<notin> g ` Sg" if x: "x \<in> Gm" and xS: "x \<notin> Sg" for x
  proof
    assume "g x \<in> g ` Sg"
    then obtain y where y: "y \<in> Sg" and gy: "g x = g y" by blast
    from y base(3) have "y \<in> Gm" by blast
    with x gy Gg have "x = y" by (auto dest: inj_onD)
    with y xS show False by simp
  qed

  have tuple: "q \<in> f ` Q - {f t, f r} \<and> q' \<in> f ` Q
               \<and> (\<forall>j. a j \<in> g ` Gm) \<and> (\<forall>j. a' j \<in> g ` Gm)"
    if tr: "(q, a, q', a', d) \<in> relabel_delta f g D" for q a q' a' d
  proof -
    from tr obtain p b p' b'
      where trD: "(p, b, p', b', d) \<in> D"
        and qp: "q = f p" and qp': "q' = f p'"
        and ab: "a = g \<circ> b" and ab': "a' = g \<circ> b'"
      by (rule relabel_source)
    from trD M_eq have trM: "(p, b, p', b', d) \<in> delta_ktm M" by simp
    from valid_ktm_delta_set [OF vM] trM M_eq
    have p: "p \<in> Q - {t, r}" and p': "p' \<in> Q"
      and bG: "\<forall>j. b j \<in> Gm" and bG': "\<forall>j. b' j \<in> Gm"
      by (auto simp: Pi_iff)
    have "f p \<noteq> f t" "f p \<noteq> f r"
      using p base(5,6) Qf by (auto dest: inj_onD)
    with p p' bG bG' qp qp' ab ab' show ?thesis by auto
  qed

  have LEdisc: "a' j = g le \<and> d j \<in> {MoveN, MoveR}"
    if tr: "(q, a, q', a', d) \<in> relabel_delta f g D" and aj: "a j = g le"
    for q a q' a' d j
  proof -
    from tr obtain p b p' b'
      where trD: "(p, b, p', b', d) \<in> D"
        and ab: "a = g \<circ> b" and ab': "a' = g \<circ> b'"
      by (rule relabel_source)
    from trD M_eq have trM: "(p, b, p', b', d) \<in> delta_ktm M" by simp
    from valid_ktm_delta_set [OF vM] trM M_eq have "b j \<in> Gm"
      by (auto simp: Pi_iff)
    with aj ab base(9) Gg have "b j = le_ktm M"
      using M_eq by (auto dest: inj_onD)
    from valid_ktm_deltaLE [OF vM trM this] ab' M_eq show ?thesis by simp
  qed

  have supp: "a j = g bl \<and> a' j = g bl \<and> d j = MoveN"
    if tr: "(q, a, q', a', d) \<in> relabel_delta f g D" and j: "k \<le> j"
    for q a q' a' d j
  proof -
    from tr obtain p b p' b'
      where trD: "(p, b, p', b', d) \<in> D"
        and ab: "a = g \<circ> b" and ab': "a' = g \<circ> b'"
      by (rule relabel_source)
    from trD M_eq have trM: "(p, b, p', b', d) \<in> delta_ktm M" by simp
    from j M_eq have "k_ktm M \<le> j" by simp
    from valid_ktm_delta_support [OF vM trM this] ab ab' M_eq
    show ?thesis by simp
  qed

  have sub: "relabel_delta f g D
               \<subseteq> (f ` Q - {f t, f r}) \<times> (UNIV \<rightarrow> g ` Gm) \<times> f ` Q
                   \<times> (UNIV \<rightarrow> g ` Gm) \<times> (UNIV \<rightarrow> UNIV)"
  proof (rule subsetI)
    fix x assume x: "x \<in> relabel_delta f g D"
    obtain q a q' a' d where xe: "x = (q, a, q', a', d)" by (cases x) auto
    from tuple [OF x [unfolded xe]] xe
    show "x \<in> (f ` Q - {f t, f r}) \<times> (UNIV \<rightarrow> g ` Gm) \<times> f ` Q
                \<times> (UNIV \<rightarrow> g ` Gm) \<times> (UNIV \<rightarrow> UNIV)"
      by (simp add: Pi_iff)
  qed

  have tr_neq: "f t \<noteq> f r" using base(5,6,11) Qf by (auto dest: inj_onD)

  show ?thesis
    unfolding R valid_ktm.simps
  proof (intro conjI)
    show "finite (f ` Q)" using base(1) by simp
    show "finite (g ` Gm)" using base(2) by simp
    show "g ` Sg \<subseteq> g ` Gm" using base(3) by blast
    show "f s \<in> f ` Q" using base(4) by simp
    show "f t \<in> f ` Q" using base(5) by simp
    show "f r \<in> f ` Q" using base(6) by simp
    show "g bl \<in> g ` Gm" using base(7) by simp
    show "g bl \<notin> g ` Sg" by (rule notin [OF base(7) base(8)])
    show "g le \<in> g ` Gm" using base(9) by simp
    show "g le \<notin> g ` Sg" by (rule notin [OF base(9) base(10)])
    show "f t \<noteq> f r" by (rule tr_neq)
    show "0 < k" by (rule base(12))
    show "relabel_delta f g D
            \<subseteq> (f ` Q - {f t, f r}) \<times> (UNIV \<rightarrow> g ` Gm) \<times> f ` Q
                \<times> (UNIV \<rightarrow> g ` Gm) \<times> (UNIV \<rightarrow> UNIV)"
      by (rule sub)
    show "\<forall>q a q' a' d j. (q, a, q', a', d) \<in> relabel_delta f g D \<longrightarrow>
            a j = g le \<longrightarrow> a' j = g le \<and> d j \<in> {MoveN, MoveR}"
      using LEdisc by blast
    show "\<forall>q a q' a' d. (q, a, q', a', d) \<in> relabel_delta f g D \<longrightarrow>
            (\<forall>j \<ge> k. a j = g bl \<and> a' j = g bl \<and> d j = MoveN)"
      using supp by blast
  qed
qed

text \<open>Determinism is a property of the transition relation's shape, so it
  transports for the same reason.  Both injectivity hypotheses are used here
  and used differently: \<open>f\<close> injective is what identifies the two source
  states, and \<open>g\<close> injective is what identifies the two read vectors
  pointwise --- without either, two distinct transitions of \<open>M\<close> could be
  merged into one branch point.\<close>

lemma relabel_det:
  assumes vM: "valid_ktm M"
      and injf: "inj_on f (Q_ktm M)"
      and injg: "inj_on g (\<Gamma>_ktm M)"
      and dM: "det_ktm M"
  shows "det_ktm (relabel_ktm f g M)"
  unfolding det_ktm_def
proof (intro allI impI)
  fix q a p\<^sub>1 b\<^sub>1 d\<^sub>1 p\<^sub>2 b\<^sub>2 d\<^sub>2
  assume "(q, a, p\<^sub>1, b\<^sub>1, d\<^sub>1) \<in> delta_ktm (relabel_ktm f g M)"
     and "(q, a, p\<^sub>2, b\<^sub>2, d\<^sub>2) \<in> delta_ktm (relabel_ktm f g M)"
  then have t\<^sub>1: "(q, a, p\<^sub>1, b\<^sub>1, d\<^sub>1) \<in> relabel_delta f g (delta_ktm M)"
    and t\<^sub>2: "(q, a, p\<^sub>2, b\<^sub>2, d\<^sub>2) \<in> relabel_delta f g (delta_ktm M)"
    by (simp_all add: relabel_ktm_def)
  from t\<^sub>1 obtain u c u' c'
    where s\<^sub>1: "(u, c, u', c', d\<^sub>1) \<in> delta_ktm M"
      and q\<^sub>1: "q = f u" and p\<^sub>1: "p\<^sub>1 = f u'"
      and a\<^sub>1: "a = g \<circ> c" and b\<^sub>1: "b\<^sub>1 = g \<circ> c'"
    by (rule relabel_source)
  from t\<^sub>2 obtain v e v' e'
    where s\<^sub>2: "(v, e, v', e', d\<^sub>2) \<in> delta_ktm M"
      and q\<^sub>2: "q = f v" and p\<^sub>2: "p\<^sub>2 = f v'"
      and a\<^sub>2: "a = g \<circ> e" and b\<^sub>2: "b\<^sub>2 = g \<circ> e'"
    by (rule relabel_source)
  from valid_ktm_delta_set [OF vM] s\<^sub>1 s\<^sub>2
  have uQ: "u \<in> Q_ktm M" and vQ: "v \<in> Q_ktm M"
    and cG: "\<forall>j. c j \<in> \<Gamma>_ktm M" and eG: "\<forall>j. e j \<in> \<Gamma>_ktm M"
    by (auto simp: Pi_iff)
  from q\<^sub>1 q\<^sub>2 uQ vQ injf have uv: "u = v" by (auto dest: inj_onD)
  have ce: "c = e"
  proof
    fix j
    from a\<^sub>1 a\<^sub>2 have "g (c j) = g (e j)" by (simp add: fun_eq_iff)
    with cG eG injg show "c j = e j" by (auto dest: inj_onD)
  qed
  from dM s\<^sub>1 s\<^sub>2 [unfolded uv [symmetric] ce [symmetric]]
  have "(u', c', d\<^sub>1) = (v', e', d\<^sub>2)" by (simp add: det_ktm_def)
  with p\<^sub>1 p\<^sub>2 b\<^sub>1 b\<^sub>2 show "(p\<^sub>1, b\<^sub>1, d\<^sub>1) = (p\<^sub>2, b\<^sub>2, d\<^sub>2)" by simp
qed

text \<open>The endmarker write discipline transports too, and unlike the two above
  it spends only \<^emph>\<open>one\<close> of the injectivities: \<^const>\<open>le_unique\<close> says nothing
  about states, so \<open>f\<close> may collapse them freely.  What \<open>g\<close> injective buys is
  the one inference the proof turns on --- from \<^term>\<open>g (b j) = g (le_ktm M)\<close>
  back to \<^term>\<open>b j = le_ktm M\<close> --- and validity is what places both sides
  inside \<open>\<Gamma>\<close>, where injectivity is assumed.  Without it a relabelling could
  identify the endmarker with an ordinary symbol and manufacture a write that
  the original never made.\<close>

lemma relabel_le_unique:
  assumes vM: "valid_ktm M"
      and injg: "inj_on g (\<Gamma>_ktm M)"
      and lu: "le_unique M"
  shows "le_unique (relabel_ktm f g M)"
  unfolding le_unique_def
proof (intro allI impI)
  fix q a q' a' d and j :: nat
  assume "(q, a, q', a', d) \<in> delta_ktm (relabel_ktm f g M)"
  then have t: "(q, a, q', a', d) \<in> relabel_delta f g (delta_ktm M)"
    by (simp add: relabel_ktm_def)
  then obtain p b p' b'
    where s: "(p, b, p', b', d) \<in> delta_ktm M"
      and "q = f p" and "q' = f p'"
      and ab: "a = g \<circ> b" and ab': "a' = g \<circ> b'"
    by (rule relabel_source)
  assume "a' j = le_ktm (relabel_ktm f g M)"
  then have geq: "g (b' j) = g (le_ktm M)" using ab' by simp
  have b'G: "b' j \<in> \<Gamma>_ktm M" by (rule valid_ktm_delta (4) [OF vM s])
  have leG: "le_ktm M \<in> \<Gamma>_ktm M" by (rule valid_ktm_LE_in_Gamma [OF vM])
  from geq b'G leG injg have "b' j = le_ktm M" by (auto dest: inj_onD)
  with lu s have "b j = le_ktm M" unfolding le_unique_def by blast
  then show "a j = le_ktm (relabel_ktm f g M)" using ab by simp
qed


subsection \<open>Semantic preservation\<close>

text \<open>The point of the combinator.  A relabelling is a bijection on
  configurations, so runs correspond step for step: no step is added and none
  is lost, and the time bound is preserved \<^emph>\<open>with no constant at all\<close>.  This
  is what distinguishes relabelling from the sibling combinators, every one
  of which pays a multiplicative or additive price.\<close>

definition relabel_config ::
  "('q \<Rightarrow> 'p) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> ('a, 'q) ktc_config \<Rightarrow> ('b, 'p) ktc_config" where
  "relabel_config f g c =
     KConfig (f (ktc_state c)) (\<lambda>j p. g (ktc_tape c j p)) (ktc_pos c)"

lemma relabel_config_simps [simp]:
  "ktc_state (relabel_config f g c) = f (ktc_state c)"
  "ktc_tape (relabel_config f g c) = (\<lambda>j p. g (ktc_tape c j p))"
  "ktc_pos (relabel_config f g c) = ktc_pos c"
  by (simp_all add: relabel_config_def)

lemma relabel_delta_ktm [simp]:
  "delta_ktm (relabel_ktm f g M) = relabel_delta f g (delta_ktm M)"
  by (simp add: relabel_ktm_def)

lemma relabel_delta_I:
  "(q, a, q', a', d) \<in> D \<Longrightarrow>
     (f q, \<lambda>j. g (a j), f q', \<lambda>j. g (a' j), d) \<in> relabel_delta f g D"
  by (force simp: relabel_delta_def comp_def)

text \<open>The initial configuration is the relabelling of the initial
  configuration, which is what makes the input word \<^term>\<open>map g w\<close> and not
  something needing a separate encoding argument.\<close>

lemma relabel_init_config:
  "relabel_config f g (init_config_ktm M w)
     = init_config_ktm (relabel_ktm f g M) (map g w)"
proof (cases M)
  case (KTM Q Sg Gm bl le D s t r k)
  then show ?thesis
    by (auto simp: relabel_config_def relabel_ktm_def fun_eq_iff)
qed

text \<open>One step of \<open>M\<close> is one step of the relabelling, with no hypotheses at
  all: the forward direction needs neither validity nor injectivity, because
  a transition of \<open>M\<close> maps to a transition of the image by construction.
  Injectivity is what the \<^emph>\<open>reverse\<close> direction costs, and it is charged
  there.\<close>

lemma relabel_step:
  assumes "(c, c') \<in> ktm_step (delta_ktm M)"
  shows "(relabel_config f g c, relabel_config f g c')
           \<in> ktm_step (delta_ktm (relabel_ktm f g M))"
  using assms
proof (cases rule: ktm_step.cases)
  case (step q ts n q' a move)
  have "(KConfig (f q) (\<lambda>j p. g (ts j p)) n,
         KConfig (f q') (\<lambda>j. (\<lambda>p. g (ts j p))(n j := g (a j)))
                        (\<lambda>j. go_move (move j) (n j)))
          \<in> ktm_step (delta_ktm (relabel_ktm f g M))"
  proof (rule ktm_step.step)
    show "(f q, \<lambda>j. (\<lambda>p. g (ts j p)) (n j), f q', \<lambda>j. g (a j), move)
            \<in> delta_ktm (relabel_ktm f g M)"
      using relabel_delta_I [OF step(3)] by simp
  qed
  moreover have "(\<lambda>j p. g (((ts j)(n j := a j)) p))
                   = (\<lambda>j. (\<lambda>p. g (ts j p))(n j := g (a j)))"
    by (simp add: fun_eq_iff)
  ultimately show ?thesis
    using step(1,2) by (simp add: relabel_config_def)
qed

lemma relabel_run:
  assumes "(c, c') \<in> (ktm_step (delta_ktm M)) ^^ n"
  shows "(relabel_config f g c, relabel_config f g c')
           \<in> (ktm_step (delta_ktm (relabel_ktm f g M))) ^^ n"
  by (rule relpow_map [where h = "relabel_config f g", OF _ assms])
     (erule relabel_step)

lemma relabel_accepts_in_time:
  assumes "valid_ktm M" and "inj_on f (Q_ktm M)" and "inj_on g (\<Gamma>_ktm M)"
      and "set w \<subseteq> Sigma_ktm M"
      and "accepts_in_time_ktm M w n"
  shows "accepts_in_time_ktm (relabel_ktm f g M) (map g w) n"
proof -
  from assms(5) obtain m c
    where m: "m \<le> n"
      and run: "(init_config_ktm M w, c) \<in> (ktm_step (delta_ktm M)) ^^ m"
      and acc: "ktc_state c = t_ktm M"
    by (auto simp: accepts_in_time_ktm_def)
  from relabel_run [OF run]
  have "(init_config_ktm (relabel_ktm f g M) (map g w), relabel_config f g c)
          \<in> (ktm_step (delta_ktm (relabel_ktm f g M))) ^^ m"
    by (simp add: relabel_init_config)
  moreover have "ktc_state (relabel_config f g c) = t_ktm (relabel_ktm f g M)"
    using acc by simp
  ultimately show ?thesis
    unfolding accepts_in_time_ktm_def using m by blast
qed

text \<open>\<^bold>\<open>Where the injectivity hypotheses are spent.\<close>  Inverting a step of the
  relabelling needs to know that the transition it came from is \<^emph>\<open>the\<close>
  transition of \<open>M\<close> and not merely one with the same image, and that is two
  separate identifications: \<open>f\<close> injective recovers the source state and \<open>g\<close>
  injective recovers the read vector cell by cell.  Both need their arguments
  to lie in the machine's carriers, which is why the configuration must be
  valid --- \<^const>\<open>valid_config_ktm\<close> supplies exactly the two facts, the
  state in \<^term>\<open>Q_ktm M\<close> and every tape cell in \<^term>\<open>\<Gamma>_ktm M\<close>.\<close>

lemma relabel_step_rev:
  assumes vM: "valid_ktm M"
      and injf: "inj_on f (Q_ktm M)"
      and injg: "inj_on g (\<Gamma>_ktm M)"
      and valc: "valid_config_ktm M c"
      and step: "(relabel_config f g c, e)
                   \<in> ktm_step (delta_ktm (relabel_ktm f g M))"
  obtains c' where "(c, c') \<in> ktm_step (delta_ktm M)"
    and "e = relabel_config f g c'"
proof -
  obtain q ts n where c: "c = KConfig q ts n" by (cases c) auto
  from valc c have qQ: "q \<in> Q_ktm M" and tsG: "\<And>j p. ts j p \<in> \<Gamma>_ktm M"
    by (cases M; simp; blast)+
  from step c obtain Q' A D
    where tr: "(f q, \<lambda>j. g (ts j (n j)), Q', A, D)
                 \<in> relabel_delta f g (delta_ktm M)"
      and e: "e = KConfig Q' (\<lambda>j. (\<lambda>p. g (ts j p))(n j := A j))
                            (\<lambda>j. go_move (D j) (n j))"
    by (auto simp: relabel_config_def elim!: ktm_step.cases)
  from tr obtain p b p' b'
    where trM: "(p, b, p', b', D) \<in> delta_ktm M"
      and fp: "f q = f p" and Q'e: "Q' = f p'"
      and bg: "(\<lambda>j. g (ts j (n j))) = g \<circ> b" and Ae: "A = g \<circ> b'"
    by (rule relabel_source)
  from valid_ktm_delta_set [OF vM] trM
  have pQ: "p \<in> Q_ktm M" and bG: "\<And>j. b j \<in> \<Gamma>_ktm M" by (auto simp: Pi_iff)
  from fp qQ pQ injf have pq: "p = q" by (auto dest: inj_onD)
  have "b = (\<lambda>j. ts j (n j))"
  proof
    fix j
    from bg have "g (ts j (n j)) = g (b j)" by (simp add: fun_eq_iff)
    with tsG bG injg show "b j = ts j (n j)" by (auto dest: inj_onD)
  qed
  with trM pq have trq: "(q, \<lambda>j. ts j (n j), p', b', D) \<in> delta_ktm M" by simp
  let ?c' = "KConfig p' (\<lambda>j. (ts j)(n j := b' j)) (\<lambda>j. go_move (D j) (n j))"
  have "(KConfig q ts n, ?c') \<in> ktm_step (delta_ktm M)"
    by (rule ktm_step.step) (rule trq)
  then have "(c, ?c') \<in> ktm_step (delta_ktm M)" unfolding c .
  moreover have "e = relabel_config f g ?c'"
    using e Q'e Ae by (simp add: relabel_config_def fun_eq_iff)
  ultimately show thesis by (rule that)
qed

lemma relabel_run_rev:
  assumes vM: "valid_ktm M"
      and injf: "inj_on f (Q_ktm M)"
      and injg: "inj_on g (\<Gamma>_ktm M)"
      and valc: "valid_config_ktm M c"
      and run: "(relabel_config f g c, e)
                  \<in> (ktm_step (delta_ktm (relabel_ktm f g M))) ^^ n"
  obtains c' where "(c, c') \<in> (ktm_step (delta_ktm M)) ^^ n"
    and "e = relabel_config f g c'"
  using run
proof (induct n arbitrary: e thesis)
  case 0 then show ?case by simp
next
  case (Suc n)
  from Suc.prems(2) obtain d
    where cd: "(relabel_config f g c, d)
                 \<in> (ktm_step (delta_ktm (relabel_ktm f g M))) ^^ n"
      and de: "(d, e) \<in> ktm_step (delta_ktm (relabel_ktm f g M))" by auto
  from Suc.hyps [OF _ cd] obtain c''
    where cc'': "(c, c'') \<in> (ktm_step (delta_ktm M)) ^^ n"
      and dc'': "d = relabel_config f g c''" by blast
  from valid_reach_relpow_ktm [OF vM valc cc'']
  have valc'': "valid_config_ktm M c''" .
  from de [unfolded dc''] obtain c'
    where c''c': "(c'', c') \<in> ktm_step (delta_ktm M)"
      and ec': "e = relabel_config f g c'"
    by (rule relabel_step_rev [OF vM injf injg valc''])
  from cc'' c''c' have "(c, c') \<in> (ktm_step (delta_ktm M)) ^^ Suc n" by auto
  from Suc.prems(1) [OF this ec'] show ?case .
qed

lemma relabel_accepts_in_time_rev:
  assumes vM: "valid_ktm M" and injf: "inj_on f (Q_ktm M)"
      and injg: "inj_on g (\<Gamma>_ktm M)"
      and w: "set w \<subseteq> Sigma_ktm M"
      and acc: "accepts_in_time_ktm (relabel_ktm f g M) (map g w) n"
  shows "accepts_in_time_ktm M w n"
proof -
  from acc obtain m e
    where m: "m \<le> n"
      and run: "(init_config_ktm (relabel_ktm f g M) (map g w), e)
                  \<in> (ktm_step (delta_ktm (relabel_ktm f g M))) ^^ m"
      and te: "ktc_state e = t_ktm (relabel_ktm f g M)"
    by (auto simp: accepts_in_time_ktm_def)
  have valinit: "valid_config_ktm M (init_config_ktm M w)"
    by (rule valid_init_config_ktm [OF vM w])
  from run [folded relabel_init_config] obtain c'
    where run': "(init_config_ktm M w, c') \<in> (ktm_step (delta_ktm M)) ^^ m"
      and ec': "e = relabel_config f g c'"
    by (rule relabel_run_rev [OF vM injf injg valinit])
  from valid_reach_relpow_ktm [OF vM valinit run']
  have "ktc_state c' \<in> Q_ktm M" by (cases M; cases c') simp
  moreover have "t_ktm M \<in> Q_ktm M" by (rule valid_ktm_t_in_Q [OF vM])
  moreover from te ec' have "f (ktc_state c') = f (t_ktm M)" by simp
  ultimately have "ktc_state c' = t_ktm M" using injf by (auto dest: inj_onD)
  with run' m show ?thesis unfolding accepts_in_time_ktm_def by blast
qed

theorem relabel_lang:
  assumes vM: "valid_ktm M" and injf: "inj_on f (Q_ktm M)"
      and injg: "inj_on g (\<Gamma>_ktm M)"
  shows "Lang_ktm (relabel_ktm f g M) = map g ` Lang_ktm M"
proof (rule set_eqI, rule iffI)
  fix v assume v: "v \<in> Lang_ktm (relabel_ktm f g M)"
  then have "v \<in> lists (g ` Sigma_ktm M)" by (auto simp: Lang_ktm_def)
  then obtain w where wv: "v = map g w" and w: "set w \<subseteq> Sigma_ktm M"
    by (auto simp: lists_image)
  from v wv obtain e j
    where "(init_config_ktm (relabel_ktm f g M) (map g w), e)
             \<in> (ktm_step (delta_ktm (relabel_ktm f g M))) ^^ j"
      and te: "ktc_state e = t_ktm (relabel_ktm f g M)"
    by (auto simp: Lang_ktm_def rtrancl_power)
  then have "accepts_in_time_ktm (relabel_ktm f g M) (map g w) j"
    unfolding accepts_in_time_ktm_def by blast
  from relabel_accepts_in_time_rev [OF vM injf injg w this]
  obtain i c where "i \<le> j"
    and "(init_config_ktm M w, c) \<in> (ktm_step (delta_ktm M)) ^^ i"
    and "ktc_state c = t_ktm M"
    by (auto simp: accepts_in_time_ktm_def)
  then have "w \<in> Lang_ktm M"
    using w by (cases c) (auto simp: Lang_ktm_def rtrancl_power)
  with wv show "v \<in> map g ` Lang_ktm M" by blast
next
  fix v assume "v \<in> map g ` Lang_ktm M"
  then obtain w where wv: "v = map g w" and w: "w \<in> Lang_ktm M" by blast
  from w have wS: "set w \<subseteq> Sigma_ktm M" by (simp add: Lang_ktm_def)
  from w obtain c j where run: "(init_config_ktm M w, c)
                                  \<in> (ktm_step (delta_ktm M)) ^^ j"
    and tc: "ktc_state c = t_ktm M"
    by (cases M) (auto simp: Lang_ktm_def rtrancl_power)
  from relabel_run [OF run]
  have "(init_config_ktm (relabel_ktm f g M) (map g w), relabel_config f g c)
          \<in> (ktm_step (delta_ktm (relabel_ktm f g M))) ^^ j"
    by (simp add: relabel_init_config)
  moreover have "ktc_state (relabel_config f g c)
                   = t_ktm (relabel_ktm f g M)" using tc by simp
  moreover have "set (map g w) \<subseteq> Sigma_ktm (relabel_ktm f g M)"
    using wS by auto
  ultimately show "v \<in> Lang_ktm (relabel_ktm f g M)"
    unfolding wv
    by (cases "relabel_config f g c")
       (auto simp: Lang_ktm_def rtrancl_power)
qed


subsection \<open>Widening the tape count\<close>

text \<open>Textbook arguments that move a machine into a class with more tapes
  say "a \<open>k\<close>-tape machine is a \<open>k'\<close>-tape machine with unused extra tapes"
  and move on.  On the value-level substrate that sentence is not just true but
  \<^emph>\<open>free\<close>, and it is worth seeing why.

  \<^bold>\<open>It is not a field update, and the reason is worth stating because the
  plausible argument for "free" is nearly right.\<close>  Validity does constrain
  transitions only \<^emph>\<open>beyond\<close> the tape count --- for \<open>j \<ge> k\<close> a transition
  must read blank, write blank and stay --- so raising \<open>k\<close> weakens that
  obligation and a machine's own transition relation stays legal at the larger
  count.  \<open>widen_valid\<close> really is free.

  But \<open>k\<close> has a second consumer.  \<^const>\<open>init_config_ktm\<close> reads it to decide
  which tapes \<^emph>\<open>exist\<close>, and every tape below \<open>k\<close> starts with the left
  endmarker in cell 0 while every tape at or above \<open>k\<close> is uniformly blank.
  Raising the count therefore \<^emph>\<open>adds\<close> endmarkers, on exactly the tapes whose
  transitions are required to read blank --- so a bare field update leaves a
  machine that cannot take its first step at all, for any input.  The two
  consumers of \<open>k\<close> move in opposite directions.

  So the widening also patches the transition relation, replacing the blank
  that \<^const>\<open>valid_ktm\<close> forces on tapes \<open>[k, k')\<close> with the endmarker those
  tapes now carry.  The heads there never move (the direction component is
  already stationary beyond \<open>k\<close>), so each new tape holds its endmarker in
  cell 0 for the whole run and reads it every step.  The correspondence with
  \<open>M\<close>'s own run is still step for step and the time bound is still exact ---
  what is lost is only the claim that no proof obligation arises.

  This remains a place where the value-level tape count pays for itself.  With
  the count trapped in a type parameter, as in the AFP source this substrate
  was forked from, the same step would be a transport across two different
  types and would need the machinery above on top of this patch.\<close>

definition widen_delta ::
  "nat \<Rightarrow> nat \<Rightarrow> 'a
     \<Rightarrow> ('q \<times> (nat \<Rightarrow> 'a) \<times> 'q \<times> (nat \<Rightarrow> 'a) \<times> (nat \<Rightarrow> move)) set
     \<Rightarrow> ('q \<times> (nat \<Rightarrow> 'a) \<times> 'q \<times> (nat \<Rightarrow> 'a) \<times> (nat \<Rightarrow> move)) set" where
  "widen_delta k k' le D =
     (\<lambda>(q, a, q', a', d).
        (q, \<lambda>j. if k \<le> j \<and> j < k' then le else a j,
         q', \<lambda>j. if k \<le> j \<and> j < k' then le else a' j, d)) ` D"

definition widen_tapes :: "nat \<Rightarrow> ('q, 'a) ktm \<Rightarrow> ('q, 'a) ktm" where
  "widen_tapes k' M =
     KTM (Q_ktm M) (Sigma_ktm M) (\<Gamma>_ktm M) (bl_ktm M) (le_ktm M)
          (widen_delta (k_ktm M) k' (le_ktm M) (delta_ktm M))
          (s_ktm M) (t_ktm M) (r_ktm M) k'"

lemma widen_k_ktm [simp]: "k_ktm (widen_tapes k' M) = k'"
  by (simp add: widen_tapes_def)

lemma widen_delta_ktm [simp]:
  "delta_ktm (widen_tapes k' M)
     = widen_delta (k_ktm M) k' (le_ktm M) (delta_ktm M)"
  by (simp add: widen_tapes_def)

lemma widen_Sigma_ktm [simp]: "Sigma_ktm (widen_tapes k' M) = Sigma_ktm M"
  by (simp add: widen_tapes_def)

lemma widen_Gamma_ktm [simp]: "\<Gamma>_ktm (widen_tapes k' M) = \<Gamma>_ktm M"
  by (simp add: widen_tapes_def)

lemma widen_bl_ktm [simp]: "bl_ktm (widen_tapes k' M) = bl_ktm M"
  by (simp add: widen_tapes_def)

lemma widen_le_ktm [simp]: "le_ktm (widen_tapes k' M) = le_ktm M"
  by (simp add: widen_tapes_def)

lemma widen_t_ktm [simp]: "t_ktm (widen_tapes k' M) = t_ktm M"
  by (simp add: widen_tapes_def)

text \<open>The patched tuple's four obligations, each read off \<open>M\<close>'s own.  The
  endmarker case is the one the bare field update could not meet: on
  \<open>[k, k')\<close> the read is now \<open>le\<close>, and what licenses it is that \<open>M\<close>'s support
  invariant already makes the direction stationary there, so the endmarker
  discipline's \<open>d j \<in> {N, R}\<close> is satisfied without choosing anything.\<close>

lemma widen_valid:
  assumes vM: "valid_ktm M" and kk: "k_ktm M \<le> k'" and pos: "0 < k'"
  shows "valid_ktm (widen_tapes k' M)"
proof (cases M)
  case M_eq: (KTM Q Sg Gm bl le D s t r k)
  have kD: "k_ktm M = k" "le_ktm M = le" "bl_ktm M = bl" "delta_ktm M = D"
    using M_eq by simp_all
  have W: "widen_tapes k' M
             = KTM Q Sg Gm bl le (widen_delta k k' le D) s t r k'"
    using M_eq by (simp add: widen_tapes_def)
  have kle: "k \<le> k'" using kk kD by simp
  have leG: "le \<in> Gm" using valid_ktm_LE_in_Gamma [OF vM] M_eq by simp

  have split: "\<exists>b b'. (q, b, q', b', d) \<in> delta_ktm M
                      \<and> a = (\<lambda>j. if k \<le> j \<and> j < k' then le else b j)
                      \<and> a' = (\<lambda>j. if k \<le> j \<and> j < k' then le else b' j)"
    if "(q, a, q', a', d) \<in> widen_delta k k' le D" for q a q' a' d
    using that kD by (auto simp: widen_delta_def)

  have tuple: "q \<in> Q - {t, r} \<and> q' \<in> Q
               \<and> (\<forall>j. a j \<in> Gm) \<and> (\<forall>j. a' j \<in> Gm)"
    if tr: "(q, a, q', a', d) \<in> widen_delta k k' le D" for q a q' a' d
  proof -
    from split [OF tr] obtain b b'
      where trM: "(q, b, q', b', d) \<in> delta_ktm M"
        and ae: "a = (\<lambda>j. if k \<le> j \<and> j < k' then le else b j)"
        and ae': "a' = (\<lambda>j. if k \<le> j \<and> j < k' then le else b' j)" by blast
    from valid_ktm_delta_set [OF vM] trM M_eq
    have "q \<in> Q - {t, r}" "q' \<in> Q" "\<forall>j. b j \<in> Gm" "\<forall>j. b' j \<in> Gm"
      by (auto simp: Pi_iff)
    with leG ae ae' show ?thesis by simp
  qed

  have LEdisc: "a' j = le \<and> d j \<in> {MoveN, MoveR}"
    if tr: "(q, a, q', a', d) \<in> widen_delta k k' le D" and aj: "a j = le"
    for q a q' a' d j
  proof -
    from split [OF tr] obtain b b'
      where trM: "(q, b, q', b', d) \<in> delta_ktm M"
        and ae: "a = (\<lambda>j. if k \<le> j \<and> j < k' then le else b j)"
        and ae': "a' = (\<lambda>j. if k \<le> j \<and> j < k' then le else b' j)" by blast
    show ?thesis
    proof (cases "k \<le> j \<and> j < k'")
      case True
      then have "d j = MoveN"
        using valid_ktm_delta_support [OF vM trM] kD by simp
      with True ae' show ?thesis by simp
    next
      case False
      with aj ae have "b j = le_ktm M" using kD by simp
      from valid_ktm_deltaLE [OF vM trM this] False ae' kD
      show ?thesis by simp
    qed
  qed

  have supp: "a j = bl \<and> a' j = bl \<and> d j = MoveN"
    if tr: "(q, a, q', a', d) \<in> widen_delta k k' le D" and j: "k' \<le> j"
    for q a q' a' d j
  proof -
    from split [OF tr] obtain b b'
      where trM: "(q, b, q', b', d) \<in> delta_ktm M"
        and ae: "a = (\<lambda>j. if k \<le> j \<and> j < k' then le else b j)"
        and ae': "a' = (\<lambda>j. if k \<le> j \<and> j < k' then le else b' j)" by blast
    from j kle have "k_ktm M \<le> j" using kD by simp
    from valid_ktm_delta_support [OF vM trM this] j ae ae' kD
    show ?thesis by simp
  qed

  have sub: "widen_delta k k' le D
               \<subseteq> (Q - {t, r}) \<times> (UNIV \<rightarrow> Gm) \<times> Q \<times> (UNIV \<rightarrow> Gm)
                   \<times> (UNIV \<rightarrow> UNIV)"
  proof (rule subsetI)
    fix x assume x: "x \<in> widen_delta k k' le D"
    obtain q a q' a' d where xe: "x = (q, a, q', a', d)"
      by (cases x) auto
    from tuple [OF x [unfolded xe]] xe
    show "x \<in> (Q - {t, r}) \<times> (UNIV \<rightarrow> Gm) \<times> Q \<times> (UNIV \<rightarrow> Gm)
                \<times> (UNIV \<rightarrow> UNIV)"
      by (simp add: Pi_iff)
  qed

  have base: "finite Q" "finite Gm" "Sg \<subseteq> Gm" "s \<in> Q" "t \<in> Q" "r \<in> Q"
             "bl \<in> Gm" "bl \<notin> Sg" "le \<in> Gm" "le \<notin> Sg" "t \<noteq> r"
    using vM M_eq by auto

  show ?thesis
    unfolding W valid_ktm.simps
    using base pos sub LEdisc supp by blast
qed

text \<open>\<^bold>\<open>And \<^const>\<open>le_unique\<close>, which the widening preserves for the reason
  it is stated the way it is.\<close>  On the tapes it invents the read and the write
  are the \<^emph>\<open>same\<close> endmarker, so the implication holds there with nothing to
  prove; elsewhere the vectors are \<open>M\<close>'s own.  A pipeline of
  constructions that has to deliver a machine with the property needs every
  stage to preserve it.\<close>

lemma widen_le_unique:
  assumes lu: "le_unique M"
  shows "le_unique (widen_tapes k' M)"
  using lu by (fastforce simp: le_unique_def widen_tapes_def widen_delta_def)

text \<open>The configuration correspondence.  On \<open>[k, k')\<close> the widened machine
  shows the endmarker in cell 0 and blanks beyond it, and its head there never
  moves; everywhere else it is \<open>M\<close>'s own configuration.  What makes this an
  \<^emph>\<open>equality\<close> of runs rather than a simulation is that \<^const>\<open>valid_config_ktm\<close>
  already forces \<open>M\<close>'s tapes beyond \<open>k\<close> to be uniformly blank with the head at
  the origin, so nothing on those tapes is being thrown away.\<close>

definition widen_config ::
  "nat \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> ('a, 'q) ktc_config \<Rightarrow> ('a, 'q) ktc_config" where
  "widen_config k k' le bl c =
     KConfig (ktc_state c)
       (\<lambda>j p. if k \<le> j \<and> j < k'
              then (if p = 0 then le else bl) else ktc_tape c j p)
       (ktc_pos c)"

lemma widen_config_simps [simp]:
  "ktc_state (widen_config k k' le bl c) = ktc_state c"
  "ktc_pos (widen_config k k' le bl c) = ktc_pos c"
  by (simp_all add: widen_config_def)

lemma widen_init_config:
  assumes vM: "valid_ktm M" and kk: "k_ktm M \<le> k'"
  shows "widen_config (k_ktm M) k' (le_ktm M) (bl_ktm M) (init_config_ktm M w)
           = init_config_ktm (widen_tapes k' M) w"
  using kk valid_ktm_k_pos [OF vM]
  by (cases M) (auto simp: widen_config_def widen_tapes_def fun_eq_iff)

lemma widen_delta_I:
  "(q, a, q', a', d) \<in> D \<Longrightarrow>
     (q, \<lambda>j. if k \<le> j \<and> j < k' then le else a j, q',
      \<lambda>j. if k \<le> j \<and> j < k' then le else a' j, d) \<in> widen_delta k k' le D"
  by (force simp: widen_delta_def)

lemma widen_step:
  assumes vM: "valid_ktm M" and kk: "k_ktm M \<le> k'"
      and valc: "valid_config_ktm M c"
      and hp: "heads_parked (k_ktm M) c"
      and step: "(c, c') \<in> ktm_step (delta_ktm M)"
  shows "(widen_config (k_ktm M) k' (le_ktm M) (bl_ktm M) c,
          widen_config (k_ktm M) k' (le_ktm M) (bl_ktm M) c')
           \<in> ktm_step (delta_ktm (widen_tapes k' M))"
proof -
  let ?k = "k_ktm M" and ?le = "le_ktm M" and ?bl = "bl_ktm M"
  from step obtain q ts n q' a d
    where c: "c = KConfig q ts n"
      and c': "c' = KConfig q' (\<lambda>j. (ts j)(n j := a j))
                              (\<lambda>j. go_move (d j) (n j))"
      and tr: "(q, \<lambda>j. ts j (n j), q', a, d) \<in> delta_ktm M"
    by (auto elim!: ktm_step.cases)
  \<comment> \<open>beyond \<open>k\<close> the head is at the origin and stays there\<close>
  have pos0: "n j = 0" if "?k \<le> j" for j
    using hp c that by (simp add: heads_parked_def)
  let ?tw = "\<lambda>j p. if ?k \<le> j \<and> j < k' then (if p = 0 then ?le else ?bl)
                   else ts j p"
  let ?aw = "\<lambda>j. if ?k \<le> j \<and> j < k' then ?le else a j"
  have wc: "widen_config ?k k' ?le ?bl c = KConfig q ?tw n"
    unfolding c widen_config_def by (auto simp: fun_eq_iff)
  have wc': "widen_config ?k k' ?le ?bl c'
               = KConfig q' (\<lambda>j. (?tw j)(n j := ?aw j))
                            (\<lambda>j. go_move (d j) (n j))"
    unfolding c' widen_config_def using pos0 by (auto simp: fun_eq_iff)
  have read: "(\<lambda>j. ?tw j (n j)) = (\<lambda>j. if ?k \<le> j \<and> j < k' then ?le
                                        else ts j (n j))"
    using pos0 by (auto simp: fun_eq_iff)
  show ?thesis
    unfolding wc wc'
  proof (rule ktm_step.step)
    show "(q, \<lambda>j. ?tw j (n j), q', ?aw, d) \<in> delta_ktm (widen_tapes k' M)"
      using widen_delta_I [OF tr] read by simp
  qed
qed

lemma widen_run:
  assumes vM: "valid_ktm M" and kk: "k_ktm M \<le> k'"
      and valc: "valid_config_ktm M c"
      and hp: "heads_parked (k_ktm M) c"
      and run: "(c, c') \<in> (ktm_step (delta_ktm M)) ^^ n"
  shows "(widen_config (k_ktm M) k' (le_ktm M) (bl_ktm M) c,
          widen_config (k_ktm M) k' (le_ktm M) (bl_ktm M) c')
           \<in> (ktm_step (delta_ktm (widen_tapes k' M))) ^^ n"
  by (rule relpow_map [where h = "widen_config (k_ktm M) k' (le_ktm M) (bl_ktm M)", OF _ run])
     (rule widen_step [OF vM kk valid_reach_relpow_ktm [OF vM valc]
                       heads_parked_run [OF vM hp]])

text \<open>The reverse direction reuses the forward one rather than repeating the
  correspondence: \<open>widen_tapes\<close> does not change the state set, so an accepting
  run of the widened machine is a run of \<open>M\<close> read back through the same
  bijection on configurations.  Stating it as \<open>relabel_ktm\<close>'s reverse would
  need a second inversion argument; instead the widened step relation is
  inverted directly, which is cheap because \<open>widen_delta\<close> is injective on the
  part of the read vector that matters.\<close>

lemma widen_step_rev:
  assumes vM: "valid_ktm M" and kk: "k_ktm M \<le> k'"
      and valc: "valid_config_ktm M c"
      and hp: "heads_parked (k_ktm M) c"
      and step: "(widen_config (k_ktm M) k' (le_ktm M) (bl_ktm M) c, e)
                   \<in> ktm_step (delta_ktm (widen_tapes k' M))"
  obtains c' where "(c, c') \<in> ktm_step (delta_ktm M)"
    and "e = widen_config (k_ktm M) k' (le_ktm M) (bl_ktm M) c'"
proof -
  let ?k = "k_ktm M" and ?le = "le_ktm M" and ?bl = "bl_ktm M"
  obtain q ts n where c: "c = KConfig q ts n" by (cases c) auto
  have pos0: "n j = 0" if "?k \<le> j" for j
    using hp c that by (simp add: heads_parked_def)
  let ?tw = "\<lambda>j p. if ?k \<le> j \<and> j < k' then (if p = 0 then ?le else ?bl)
                   else ts j p"
  have wc: "widen_config ?k k' ?le ?bl c = KConfig q ?tw n"
    unfolding c widen_config_def by (auto simp: fun_eq_iff)
  from step [unfolded wc] obtain Q' A D
    where tr: "(q, \<lambda>j. ?tw j (n j), Q', A, D)
                 \<in> widen_delta ?k k' ?le (delta_ktm M)"
      and e: "e = KConfig Q' (\<lambda>j. (?tw j)(n j := A j))
                            (\<lambda>j. go_move (D j) (n j))"
    by (auto elim!: ktm_step.cases)
  from tr obtain b b'
    where trM: "(q, b, Q', b', D) \<in> delta_ktm M"
      and bw: "(\<lambda>j. ?tw j (n j))
                 = (\<lambda>j. if ?k \<le> j \<and> j < k' then ?le else b j)"
      and Aw: "A = (\<lambda>j. if ?k \<le> j \<and> j < k' then ?le else b' j)"
    by (auto simp: widen_delta_def)
  have "b = (\<lambda>j. ts j (n j))"
  proof
    fix j
    show "b j = ts j (n j)"
    proof (cases "?k \<le> j \<and> j < k'")
      case True
      from valid_ktm_delta_support [OF vM trM] True have "b j = ?bl" by simp
      moreover from valc c True have "ts j (n j) = ?bl"
        by (cases M) (auto simp: valid_config_ktm.simps)
      ultimately show ?thesis by simp
    next
      case False
      from bw have "?tw j (n j) = (if ?k \<le> j \<and> j < k' then ?le else b j)"
        by (simp add: fun_eq_iff)
      with False show ?thesis by (auto split: if_splits)
    qed
  qed
  with trM have trq: "(q, \<lambda>j. ts j (n j), Q', b', D) \<in> delta_ktm M" by simp
  let ?c' = "KConfig Q' (\<lambda>j. (ts j)(n j := b' j)) (\<lambda>j. go_move (D j) (n j))"
  have "(KConfig q ts n, ?c') \<in> ktm_step (delta_ktm M)"
    by (rule ktm_step.step) (rule trq)
  then have "(c, ?c') \<in> ktm_step (delta_ktm M)" unfolding c .
  moreover have "e = widen_config ?k k' ?le ?bl ?c'"
    using e Aw pos0 by (auto simp: widen_config_def fun_eq_iff)
  ultimately show thesis by (rule that)
qed

lemma widen_run_rev:
  assumes vM: "valid_ktm M" and kk: "k_ktm M \<le> k'"
      and valc: "valid_config_ktm M c"
      and hp: "heads_parked (k_ktm M) c"
      and run: "(widen_config (k_ktm M) k' (le_ktm M) (bl_ktm M) c, e)
                  \<in> (ktm_step (delta_ktm (widen_tapes k' M))) ^^ n"
  obtains c' where "(c, c') \<in> (ktm_step (delta_ktm M)) ^^ n"
    and "e = widen_config (k_ktm M) k' (le_ktm M) (bl_ktm M) c'"
  using run
proof (induct n arbitrary: e thesis)
  case 0 then show ?case by simp
next
  case (Suc n)
  from Suc.prems(2) obtain d
    where cd: "(widen_config (k_ktm M) k' (le_ktm M) (bl_ktm M) c, d)
                 \<in> (ktm_step (delta_ktm (widen_tapes k' M))) ^^ n"
      and de: "(d, e) \<in> ktm_step (delta_ktm (widen_tapes k' M))" by auto
  from Suc.hyps [OF _ cd] obtain c''
    where cc'': "(c, c'') \<in> (ktm_step (delta_ktm M)) ^^ n"
      and dc'': "d = widen_config (k_ktm M) k' (le_ktm M) (bl_ktm M) c''" by blast
  from valid_reach_relpow_ktm [OF vM valc cc'']
  have valc'': "valid_config_ktm M c''" .
  from heads_parked_run [OF vM hp cc''] have hpc'': "heads_parked (k_ktm M) c''" .
  from de [unfolded dc''] obtain c'
    where c''c': "(c'', c') \<in> ktm_step (delta_ktm M)"
      and ec': "e = widen_config (k_ktm M) k' (le_ktm M) (bl_ktm M) c'"
    by (rule widen_step_rev [OF vM kk valc'' hpc''])
  from cc'' c''c' have "(c, c') \<in> (ktm_step (delta_ktm M)) ^^ Suc n" by auto
  from Suc.prems(1) [OF this ec'] show ?case .
qed

lemma widen_accepts_in_time:
  assumes vM: "valid_ktm M" and kk: "k_ktm M \<le> k'"
      and w: "set w \<subseteq> Sigma_ktm M"
  shows "accepts_in_time_ktm (widen_tapes k' M) w n
           \<longleftrightarrow> accepts_in_time_ktm M w n"
proof
  have valinit: "valid_config_ktm M (init_config_ktm M w)"
    by (rule valid_init_config_ktm [OF vM w])
  have hpinit: "heads_parked (k_ktm M) (init_config_ktm M w)"
    by (rule heads_parked_init)
  assume "accepts_in_time_ktm (widen_tapes k' M) w n"
  then obtain m e
    where m: "m \<le> n"
      and run: "(init_config_ktm (widen_tapes k' M) w, e)
                  \<in> (ktm_step (delta_ktm (widen_tapes k' M))) ^^ m"
      and te: "ktc_state e = t_ktm (widen_tapes k' M)"
    by (auto simp: accepts_in_time_ktm_def)
  from run [folded widen_init_config [OF vM kk]] obtain c'
    where run': "(init_config_ktm M w, c') \<in> (ktm_step (delta_ktm M)) ^^ m"
      and ec': "e = widen_config (k_ktm M) k' (le_ktm M) (bl_ktm M) c'"
    by (rule widen_run_rev [OF vM kk valinit hpinit])
  from te ec' have "ktc_state c' = t_ktm M" by (simp add: widen_tapes_def)
  with run' m show "accepts_in_time_ktm M w n"
    unfolding accepts_in_time_ktm_def by blast
next
  have valinit: "valid_config_ktm M (init_config_ktm M w)"
    by (rule valid_init_config_ktm [OF vM w])
  have hpinit: "heads_parked (k_ktm M) (init_config_ktm M w)"
    by (rule heads_parked_init)
  assume "accepts_in_time_ktm M w n"
  then obtain m c
    where m: "m \<le> n"
      and run: "(init_config_ktm M w, c) \<in> (ktm_step (delta_ktm M)) ^^ m"
      and tc: "ktc_state c = t_ktm M"
    by (auto simp: accepts_in_time_ktm_def)
  from widen_run [OF vM kk valinit hpinit run]
  have run': "(init_config_ktm (widen_tapes k' M) w,
               widen_config (k_ktm M) k' (le_ktm M) (bl_ktm M) c)
                \<in> (ktm_step (delta_ktm (widen_tapes k' M))) ^^ m"
    by (simp add: widen_init_config [OF vM kk])
  have "ktc_state (widen_config (k_ktm M) k' (le_ktm M) (bl_ktm M) c)
          = t_ktm (widen_tapes k' M)"
    using tc by (simp add: widen_tapes_def)
  with run' m show "accepts_in_time_ktm (widen_tapes k' M) w n"
    unfolding accepts_in_time_ktm_def by blast
qed

theorem widen_lang:
  assumes vM: "valid_ktm M" and kk: "k_ktm M \<le> k'"
  shows "Lang_ktm (widen_tapes k' M) = Lang_ktm M"
proof (rule set_eqI)
  fix w
  have "set w \<subseteq> Sigma_ktm (widen_tapes k' M) \<longleftrightarrow> set w \<subseteq> Sigma_ktm M"
    by (simp add: widen_tapes_def)
  then show "w \<in> Lang_ktm (widen_tapes k' M) \<longleftrightarrow> w \<in> Lang_ktm M"
    unfolding Lang_ktm_iff
    using widen_accepts_in_time [OF vM kk] by blast
qed


subsection \<open>Exchanging two tapes\<close>

text \<open>The cheapest of the three combinators.  Renaming tape indices in the
  transition relation renames them in the configuration; the machine cannot
  tell the difference, and no step is spent.

  \<^bold>\<open>Why a transposition rather than a permutation.\<close>  Every permutation of a
  finite index set is a product of transpositions, so the single exchange is
  enough, and it is what a construction that hands one tape's role to another
  needs.  \<open>tswap\<close> is \<open>transpose\<close> of \<open>HOL-Combinatorics.Transposition\<close> at
  type \<^typ>\<open>nat\<close>; it is defined here so that this entry does not depend on
  that session.  Restricting to two indices also keeps the side condition to
  \<open>i < k\<close> and \<open>j < k\<close>, which is what the support invariant needs: a
  transposition of two indices \<^emph>\<open>below\<close> the tape count fixes every index at
  or above it, so the requirement that transitions read blank, write blank and
  stay put beyond \<open>k\<close> transports unchanged.

  \<^bold>\<open>What it costs, compared with the widening above.\<close>  Nothing --- and the
  contrast is the point.  \<open>widen_step\<close> carries \<^const>\<open>valid_config_ktm\<close> and
  \<^const>\<open>heads_parked\<close> as hypotheses, because widening \<^emph>\<open>invents\<close> tape
  content (endmarkers on tapes that had none) and has to know the discarded
  content was blank and its heads at the origin.  A transposition invents
  nothing: it is a bijection on configurations, so the step correspondence is
  an iff with no hypotheses at all, and the reverse direction is the forward
  one applied to the exchanged machine rather than a second argument.

  \<^bold>\<open>Why a widening often wants one.\<close>  The tape \<^const>\<open>widen_tapes\<close>
  adds is not a free tape: widening pins it to the endmarker in cell 0 with
  the head stationary.  So a tape a construction walks along has to be one the
  machine already had, and exchanging tapes moves the pinned role onto a tape
  that is no longer needed.\<close>

definition tswap :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "tswap i j m = (if m = i then j else if m = j then i else m)"

lemma tswap_tswap [simp]: "tswap i j (tswap i j m) = m"
  by (simp add: tswap_def)

lemma tswap_same [simp]: "tswap i i = id"
  by (auto simp: tswap_def)

lemma tswap_out:
  assumes "i < k" and "j < k" and "k \<le> m"
  shows "tswap i j m = m"
  using assms by (simp add: tswap_def)

definition swap_delta ::
  "nat \<Rightarrow> nat
     \<Rightarrow> ('q \<times> (nat \<Rightarrow> 'a) \<times> 'q \<times> (nat \<Rightarrow> 'a) \<times> (nat \<Rightarrow> move)) set
     \<Rightarrow> ('q \<times> (nat \<Rightarrow> 'a) \<times> 'q \<times> (nat \<Rightarrow> 'a) \<times> (nat \<Rightarrow> move)) set" where
  "swap_delta i j D =
     (\<lambda>(q, a, q', a', d).
        (q, a \<circ> tswap i j, q', a' \<circ> tswap i j, d \<circ> tswap i j)) ` D"

lemma swap_delta_I:
  "(q, a, q', a', d) \<in> D \<Longrightarrow>
     (q, a \<circ> tswap i j, q', a' \<circ> tswap i j, d \<circ> tswap i j)
       \<in> swap_delta i j D"
  by (force simp: swap_delta_def)

lemma swap_delta_E:
  assumes "(q, a, q', a', d) \<in> swap_delta i j D"
  obtains b b' e where "(q, b, q', b', e) \<in> D"
    and "a = b \<circ> tswap i j" and "a' = b' \<circ> tswap i j" and "d = e \<circ> tswap i j"
  using assms by (auto simp: swap_delta_def)

lemma swap_delta_swap_delta [simp]:
  fixes D :: "('q \<times> (nat \<Rightarrow> 'a) \<times> 'q \<times> (nat \<Rightarrow> 'a) \<times> (nat \<Rightarrow> move)) set"
  shows "swap_delta i j (swap_delta i j D) = D"
proof (rule set_eqI)
  fix x :: "'q \<times> (nat \<Rightarrow> 'a) \<times> 'q \<times> (nat \<Rightarrow> 'a) \<times> (nat \<Rightarrow> move)"
  obtain q a q' a' d where xe: "x = (q, a, q', a', d)" by (cases x) auto
  show "(x \<in> swap_delta i j (swap_delta i j D)) = (x \<in> D)"
  proof
    assume "x \<in> swap_delta i j (swap_delta i j D)"
    from this [unfolded xe] obtain b b' e
      where m: "(q, b, q', b', e) \<in> swap_delta i j D"
        and ab: "a = b \<circ> tswap i j" and ab': "a' = b' \<circ> tswap i j"
        and de: "d = e \<circ> tswap i j"
      by (rule swap_delta_E)
    from m obtain c c' f
      where mD: "(q, c, q', c', f) \<in> D"
        and bc: "b = c \<circ> tswap i j" and bc': "b' = c' \<circ> tswap i j"
        and ef: "e = f \<circ> tswap i j"
      by (rule swap_delta_E)
    have "a = c" "a' = c'" "d = f"
      using ab ab' de bc bc' ef by (simp_all add: comp_def)
    with mD xe show "x \<in> D" by simp
  next
    assume "x \<in> D"
    from swap_delta_I [OF this [unfolded xe], of i j]
    have "(q, a \<circ> tswap i j, q', a' \<circ> tswap i j, d \<circ> tswap i j)
            \<in> swap_delta i j D" .
    from swap_delta_I [OF this, of i j]
    show "x \<in> swap_delta i j (swap_delta i j D)"
      using xe by (simp add: comp_def)
  qed
qed

lemma swap_delta_finite [simp]: "finite (swap_delta i j D) = finite D"
proof
  assume "finite (swap_delta i j D)"
  then have "finite (swap_delta i j (swap_delta i j D))"
    by (simp add: swap_delta_def)
  then show "finite D" by simp
qed (simp add: swap_delta_def)

definition swap_tapes :: "nat \<Rightarrow> nat \<Rightarrow> ('q, 'a) ktm \<Rightarrow> ('q, 'a) ktm" where
  "swap_tapes i j M =
     KTM (Q_ktm M) (Sigma_ktm M) (\<Gamma>_ktm M) (bl_ktm M) (le_ktm M)
          (swap_delta i j (delta_ktm M))
          (s_ktm M) (t_ktm M) (r_ktm M) (k_ktm M)"

lemma swap_fields [simp]:
  "Q_ktm (swap_tapes i j M) = Q_ktm M"
  "Sigma_ktm (swap_tapes i j M) = Sigma_ktm M"
  "\<Gamma>_ktm (swap_tapes i j M) = \<Gamma>_ktm M"
  "bl_ktm (swap_tapes i j M) = bl_ktm M"
  "le_ktm (swap_tapes i j M) = le_ktm M"
  "s_ktm (swap_tapes i j M) = s_ktm M"
  "t_ktm (swap_tapes i j M) = t_ktm M"
  "r_ktm (swap_tapes i j M) = r_ktm M"
  "k_ktm (swap_tapes i j M) = k_ktm M"
  "delta_ktm (swap_tapes i j M) = swap_delta i j (delta_ktm M)"
  by (simp_all add: swap_tapes_def)

lemma swap_tapes_swap_tapes [simp]: "swap_tapes i j (swap_tapes i j M) = M"
  by (cases M) (simp add: swap_tapes_def)

text \<open>Validity, and the only place the side condition is used: the support
  invariant speaks about indices at or above \<open>k\<close>, and a transposition of two
  indices below \<open>k\<close> fixes each of them.  The endmarker discipline needs no
  side condition, because it is a statement about \<^emph>\<open>every\<close> index and the
  exchange only permutes which one is being spoken about.\<close>

lemma swap_valid:
  assumes vM: "valid_ktm M" and i: "i < k_ktm M" and j: "j < k_ktm M"
  shows "valid_ktm (swap_tapes i j M)"
proof (cases M)
  case M_eq: (KTM Q Sg Gm bl le D s t r k)
  have kD: "k_ktm M = k" "bl_ktm M = bl" "le_ktm M = le" "delta_ktm M = D"
    using M_eq by simp_all
  have W: "swap_tapes i j M = KTM Q Sg Gm bl le (swap_delta i j D) s t r k"
    using M_eq by (simp add: swap_tapes_def)

  have tuple: "q \<in> Q - {t, r} \<and> q' \<in> Q
               \<and> (\<forall>m. a m \<in> Gm) \<and> (\<forall>m. a' m \<in> Gm)"
    if tr: "(q, a, q', a', d) \<in> swap_delta i j D" for q a q' a' d
  proof -
    from tr [folded kD] obtain b b' e
      where trM: "(q, b, q', b', e) \<in> delta_ktm M"
        and ab: "a = b \<circ> tswap i j" and ab': "a' = b' \<circ> tswap i j"
      by (rule swap_delta_E)
    from valid_ktm_delta_set [OF vM] trM M_eq
    have "q \<in> Q - {t, r}" "q' \<in> Q" "\<forall>m. b m \<in> Gm" "\<forall>m. b' m \<in> Gm"
      by (auto simp: Pi_iff)
    with ab ab' show ?thesis by (simp add: comp_def)
  qed

  have LEdisc: "a' m = le \<and> d m \<in> {MoveN, MoveR}"
    if tr: "(q, a, q', a', d) \<in> swap_delta i j D" and am: "a m = le"
    for q a q' a' d m
  proof -
    from tr [folded kD] obtain b b' e
      where trM: "(q, b, q', b', e) \<in> delta_ktm M"
        and ab: "a = b \<circ> tswap i j" and ab': "a' = b' \<circ> tswap i j"
        and de: "d = e \<circ> tswap i j"
      by (rule swap_delta_E)
    from am ab kD have "b (tswap i j m) = le_ktm M" by (simp add: comp_def)
    from valid_ktm_deltaLE [OF vM trM this] ab' de kD
    show ?thesis by (simp add: comp_def)
  qed

  have supp: "a m = bl \<and> a' m = bl \<and> d m = MoveN"
    if tr: "(q, a, q', a', d) \<in> swap_delta i j D" and m: "k \<le> m"
    for q a q' a' d m
  proof -
    from tr [folded kD] obtain b b' e
      where trM: "(q, b, q', b', e) \<in> delta_ktm M"
        and ab: "a = b \<circ> tswap i j" and ab': "a' = b' \<circ> tswap i j"
        and de: "d = e \<circ> tswap i j"
      by (rule swap_delta_E)
    from i j kD have ik: "i < k" "j < k" by simp_all
    have fix_m: "tswap i j m = m" by (rule tswap_out [OF ik m])
    from m kD have "k_ktm M \<le> m" by simp
    from valid_ktm_delta_support [OF vM trM this] ab ab' de kD fix_m
    show ?thesis by (simp add: comp_def)
  qed

  have sub: "swap_delta i j D
               \<subseteq> (Q - {t, r}) \<times> (UNIV \<rightarrow> Gm) \<times> Q \<times> (UNIV \<rightarrow> Gm)
                   \<times> (UNIV \<rightarrow> UNIV)"
  proof (rule subsetI)
    fix x assume x: "x \<in> swap_delta i j D"
    obtain q a q' a' d where xe: "x = (q, a, q', a', d)" by (cases x) auto
    from tuple [OF x [unfolded xe]] xe
    show "x \<in> (Q - {t, r}) \<times> (UNIV \<rightarrow> Gm) \<times> Q \<times> (UNIV \<rightarrow> Gm)
                \<times> (UNIV \<rightarrow> UNIV)"
      by (simp add: Pi_iff)
  qed

  have base: "finite Q" "finite Gm" "Sg \<subseteq> Gm" "s \<in> Q" "t \<in> Q" "r \<in> Q"
             "bl \<in> Gm" "bl \<notin> Sg" "le \<in> Gm" "le \<notin> Sg" "t \<noteq> r" "0 < k"
    using vM M_eq by auto

  show ?thesis
    unfolding W valid_ktm.simps
    using base sub LEdisc supp by blast
qed

text \<open>Determinism too: two transitions of the exchanged machine on one
  state and read vector come from two transitions of \<open>M\<close> on one read vector,
  because composing with the exchange is injective.\<close>

lemma swap_det:
  assumes dM: "det_ktm M"
  shows "det_ktm (swap_tapes i j M)"
  unfolding det_ktm_def swap_fields
proof (intro allI impI)
  fix q A p1 b1 e1 p2 b2 e2
  assume t1: "(q, A, p1, b1, e1) \<in> swap_delta i j (delta_ktm M)"
    and t2: "(q, A, p2, b2, e2) \<in> swap_delta i j (delta_ktm M)"
  from swap_delta_E [OF t1] obtain c1 c1' f1
    where r1: "(q, c1, p1, c1', f1) \<in> delta_ktm M" and A1: "A = c1 \<circ> tswap i j"
      and B1: "b1 = c1' \<circ> tswap i j" and E1: "e1 = f1 \<circ> tswap i j" .
  from swap_delta_E [OF t2] obtain c2 c2' f2
    where r2: "(q, c2, p2, c2', f2) \<in> delta_ktm M" and A2: "A = c2 \<circ> tswap i j"
      and B2: "b2 = c2' \<circ> tswap i j" and E2: "e2 = f2 \<circ> tswap i j" .
  have c: "c1 = c2"
  proof
    fix x
    have "c1 x = (c1 \<circ> tswap i j) (tswap i j x)" by simp
    also have "\<dots> = (c2 \<circ> tswap i j) (tswap i j x)" using A1 A2 by simp
    also have "\<dots> = c2 x" by simp
    finally show "c1 x = c2 x" .
  qed
  from dM r1 r2 [folded c] have "(p1, c1', f1) = (p2, c2', f2)"
    unfolding det_ktm_def by blast
  then show "(p1, b1, e1) = (p2, b2, e2)" using B1 B2 E1 E2 by simp
qed

text \<open>And \<^const>\<open>le_unique\<close> again, which an exchange of two tape indices
  preserves because the property is a conjunction over indices and the exchange
  permutes them.\<close>

lemma swap_le_unique:
  assumes lu: "le_unique M"
  shows "le_unique (swap_tapes i j M)"
  using lu by (fastforce simp: le_unique_def swap_tapes_def swap_delta_def)

text \<open>The configuration correspondence, and it is a bijection rather than an
  embedding --- which is what removes every hypothesis from the two run
  lemmas below.  Nothing is invented and nothing is discarded, so the reverse
  direction is the forward one applied to the exchanged machine and needs no
  argument of its own.\<close>

definition swap_config ::
  "nat \<Rightarrow> nat \<Rightarrow> ('a, 'q) ktc_config \<Rightarrow> ('a, 'q) ktc_config" where
  "swap_config i j c =
     KConfig (ktc_state c) (ktc_tape c \<circ> tswap i j) (ktc_pos c \<circ> tswap i j)"

lemma swap_config_Config [simp]:
  "swap_config i j (KConfig q ts n)
     = KConfig q (ts \<circ> tswap i j) (n \<circ> tswap i j)"
  by (simp add: swap_config_def)

lemma swap_config_simps [simp]:
  "ktc_state (swap_config i j c) = ktc_state c"
  "ktc_tape (swap_config i j c) = ktc_tape c \<circ> tswap i j"
  "ktc_pos (swap_config i j c) = ktc_pos c \<circ> tswap i j"
  by (simp_all add: swap_config_def)

lemma swap_config_swap_config [simp]:
  "swap_config i j (swap_config i j c) = c"
  by (cases c) (simp add: comp_def)

lemma swap_step:
  assumes step: "(c, c') \<in> ktm_step (delta_ktm M)"
  shows "(swap_config i j c, swap_config i j c')
           \<in> ktm_step (delta_ktm (swap_tapes i j M))"
proof -
  from step obtain q ts n q' a d
    where c: "c = KConfig q ts n"
      and c': "c' = KConfig q' (\<lambda>m. (ts m)(n m := a m))
                              (\<lambda>m. go_move (d m) (n m))"
      and tr: "(q, \<lambda>m. ts m (n m), q', a, d) \<in> delta_ktm M"
    by (auto elim!: ktm_step.cases)
  let ?s = "tswap i j"
  have "(KConfig q (ts \<circ> ?s) (n \<circ> ?s),
         KConfig q' (\<lambda>m. ((ts \<circ> ?s) m)((n \<circ> ?s) m := (a \<circ> ?s) m))
                    (\<lambda>m. go_move ((d \<circ> ?s) m) ((n \<circ> ?s) m)))
          \<in> ktm_step (delta_ktm (swap_tapes i j M))"
  proof (rule ktm_step.step)
    show "(q, \<lambda>m. (ts \<circ> ?s) m ((n \<circ> ?s) m), q', a \<circ> ?s, d \<circ> ?s)
            \<in> delta_ktm (swap_tapes i j M)"
      using swap_delta_I [OF tr, of i j] by (simp add: comp_def)
  qed
  moreover have "swap_config i j c = KConfig q (ts \<circ> ?s) (n \<circ> ?s)"
    unfolding c by simp
  moreover have "swap_config i j c'
                   = KConfig q' (\<lambda>m. ((ts \<circ> ?s) m)((n \<circ> ?s) m := (a \<circ> ?s) m))
                                (\<lambda>m. go_move ((d \<circ> ?s) m) ((n \<circ> ?s) m))"
    unfolding c' by (simp add: comp_def)
  ultimately show ?thesis by simp
qed

lemma swap_run:
  assumes run: "(c, c') \<in> (ktm_step (delta_ktm M)) ^^ n"
  shows "(swap_config i j c, swap_config i j c')
           \<in> (ktm_step (delta_ktm (swap_tapes i j M))) ^^ n"
  by (rule relpow_map [where h = "swap_config i j", OF _ run]) (erule swap_step)

text \<open>The reverse direction, and the whole of its proof: exchange the same two
  tapes again.  \<open>widen_run_rev\<close> next door needs its own inversion argument
  because widening is not onto; this one does not.\<close>

lemma swap_run_rev:
  assumes run: "(swap_config i j c, e)
                  \<in> (ktm_step (delta_ktm (swap_tapes i j M))) ^^ n"
  shows "(c, swap_config i j e) \<in> (ktm_step (delta_ktm M)) ^^ n"
proof -
  from swap_run [OF run, of i j]
  have "(swap_config i j (swap_config i j c), swap_config i j e)
          \<in> (ktm_step (delta_ktm (swap_tapes i j (swap_tapes i j M)))) ^^ n" .
  then show ?thesis by simp
qed


subsection \<open>Pinning two points of an injection\<close>

text \<open>Pin two elements at chosen values, and push everything else clear of
  both and of a given finite set.  \<^emph>\<open>Which\<close>
  injection carries the rest is immaterial --- any injection of a finite set
  into \<^typ>\<open>nat\<close> serves, and \<open>finite\<close> supplies one --- so all of the content
  is in the offset.

  Numbering a machine's states and symbols into an initial segment uses it at
  the values \<open>0\<close> and \<open>1\<close> with nothing to avoid.  A composite of two machines
  uses the general form: one factor's blank and endmarker have to land on
  \<^emph>\<open>the other's\<close>, since a machine has only one of each, while its remaining
  symbols must stay clear of the other's alphabet, or a step of one factor
  would read a symbol meant for the other.

  Injectivity needs only \<open>x \<noteq> y\<close> and \<open>u \<noteq> v\<close>, and in particular \<^emph>\<open>not\<close>
  that either point lies in \<open>A\<close>.  The offset puts the shifted remainder
  strictly above \<open>u\<close>, \<open>v\<close> and all of \<open>B\<close> at once, so no collision is possible
  whether or not the pinned points are themselves being numbered.  That is
  what lets one lemma serve every call without a side condition placing the
  blank in the alphabet or the start state in \<open>Q\<close>.\<close>

lemma inj_on_pin_two_avoiding:
  assumes finA: "finite A" and finB: "finite B"
    and xy: "x \<noteq> y" and uv: "u \<noteq> v"
  obtains h :: "'b \<Rightarrow> nat"
  where "inj_on h A" and "h x = u" and "h y = v"
    and "h ` (A - {x, y}) \<inter> B = {}"
proof -
  from finite_imp_inj_to_nat_seg [OF finA]
  obtain e :: "'b \<Rightarrow> nat" where inje: "inj_on e A" by blast
  define m where "m = Suc (Max (insert u (insert v B)))"
  have fin': "finite (insert u (insert v B))" using finB by simp
  have lt: "z < m" if "z \<in> insert u (insert v B)" for z
    using Max_ge [OF fin' that] by (simp add: m_def)
  have um: "u < m" by (rule lt) simp
  have vm: "v < m" by (rule lt) simp
  have ltB: "z < m" if "z \<in> B" for z using that by (intro lt) simp
  let ?h = "\<lambda>z. if z = x then u else if z = y then v else m + e z"
  have inj: "inj_on ?h A"
  proof (rule inj_onI)
    fix a b
    assume a: "a \<in> A" and b: "b \<in> A" and eq: "?h a = ?h b"
    show "a = b"
    proof (cases "a = x \<or> a = y")
      case True
      with eq xy uv um vm show ?thesis by (auto split: if_splits)
    next
      case False
      with eq um vm have "b \<noteq> x" "b \<noteq> y" by (auto split: if_splits)
      with False eq have "e a = e b" by simp
      with inje a b show ?thesis by (auto dest: inj_onD)
    qed
  qed
  have notB: "?h z \<notin> B" if z: "z \<in> A - {x, y}" for z
  proof
    assume mem: "?h z \<in> B"
    from z have "?h z = m + e z" by simp
    with mem have "m + e z \<in> B" by simp
    from ltB [OF this] show False by simp
  qed
  show thesis
  proof (rule that)
    show "inj_on ?h A" by (rule inj)
    show "?h x = u" by simp
    show "?h y = v" using xy by simp
    show "?h ` (A - {x, y}) \<inter> B = {}" using notB by blast
  qed
qed

end
