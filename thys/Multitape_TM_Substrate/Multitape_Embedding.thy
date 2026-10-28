theory Multitape_Embedding
  imports Multitape_Run_Facts
begin

section \<open>Placing a machine inside a composite\<close>

text \<open>A composite machine runs several factors on one frame: each gets a
  window of the tapes and a region of the state space, and outside its own
  window and region it must be inert.  This theory is the machinery for
  saying that once --- \<open>embed_delta\<close> on the tape side,
  \<open>tag_delta\<close> on the state side, and the correspondences that let a
  factor's run be read as the composite's.  A factor's transition relation,
  placed in this way, is called an \<^emph>\<open>arm\<close> of the composite.

  \<^bold>\<open>It is not a combinator, which is why it is not in
  \<open>Multitape_Relabelling\<close>.\<close>  Those take a machine to a machine.  Nothing here
  builds a machine at all: \<open>embed_delta\<close> and \<open>tag_delta\<close> place a
  \<^emph>\<open>transition relation\<close> into a larger frame, and what assembles the
  results into a machine is the consumer, which knows how many factors there
  are and what else the composite does.  The two theories are siblings over
  \<open>Multitape_Run_Facts\<close> and neither imports the other; the citation graph has no
  edge between them in either direction.

  The order to read it in is the order it is written: place the tapes, place
  the states, then what a run leaves behind --- which is the invariant the
  forward direction needs and the one place a factor's \<^const>\<open>valid_ktm\<close>
  is spent.\<close>

subsection \<open>Placing a machine among other tapes\<close>

text \<open>\<open>widen_tapes\<close> (\<open>Multitape_Relabelling\<close>, a sibling this theory does
  not import) puts a machine into a wider tape frame at offset
  zero, with the added tapes inert because their heads are parked.  A composite
  of two machines needs the same move at a \<^emph>\<open>nonzero\<close> offset, and with the
  other tapes live --- they are the other factor's, so their heads are wherever
  that factor left them and their cells hold whatever it wrote.

  That difference is why this is a separate construction rather than a
  parameter of the widening.  \<open>widen_delta\<close> can pad the reads on the
  added tapes with a single symbol, the endmarker, because a parked head reads
  cell 0 forever.  Here there is no such symbol: a transition of one factor has
  to be paired with \<^emph>\<open>every\<close> admissible reading of the other factor's tapes,
  which is what \<open>free_context\<close> ranges over.  The pairing is what makes the arm
  inert --- each such reading is written straight back and the head does not
  move --- so \<open>embed_delta_frozen\<close> below is precisely the hypothesis
  \<open>ktm_step_frozen_tape\<close> asks for.

  \<^bold>\<open>The context has to be a finite set, and that is the one real obligation.\<close>
  \<^const>\<open>valid_ktm\<close> requires a finite transition relation, and an arm is a
  product of the factor's tuples with the contexts.  The substrate's
  \<open>finite_tail_const_funcs\<close> is the tool: its shape is reads ranging in a finite
  set and constant beyond an index, which is what a context is.  Stating
  \<open>free_context\<close> in that shape --- rather than the more natural "in \<open>\<Gamma>\<close> below
  \<open>k'\<close>, unconstrained above" --- is what makes the finiteness proof one rule
  application instead of a subset argument.\<close>

definition free_context :: "'a set \<Rightarrow> 'a \<Rightarrow> nat \<Rightarrow> (nat \<Rightarrow> 'a) set" where
  "free_context \<Gamma> bl k' =
     {b. (\<forall>j. b j \<in> \<Gamma>) \<and> (\<forall>j \<ge> k'. b j = bl)}"

definition embed_delta ::
  "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a set \<Rightarrow> 'a
     \<Rightarrow> ('q \<times> (nat \<Rightarrow> 'a) \<times> 'q \<times> (nat \<Rightarrow> 'a) \<times> (nat \<Rightarrow> move)) set
     \<Rightarrow> ('q \<times> (nat \<Rightarrow> 'a) \<times> 'q \<times> (nat \<Rightarrow> 'a) \<times> (nat \<Rightarrow> move)) set" where
  "embed_delta off k k' \<Gamma> bl D =
     (\<lambda>((q, a, q', a', d), b).
        (q, \<lambda>j. if off \<le> j \<and> j < off + k then a (j - off) else b j,
         q', \<lambda>j. if off \<le> j \<and> j < off + k then a' (j - off) else b j,
         \<lambda>j. if off \<le> j \<and> j < off + k then d (j - off) else MoveN))
       ` (D \<times> free_context \<Gamma> bl k')"

lemma free_context_finite:
  assumes fG: "finite \<Gamma>"
  shows "finite (free_context \<Gamma> bl k')"
  unfolding free_context_def
  by (rule finite_tail_const_funcs [OF fG])

text \<open>The connector to the previous subsection: outside its own window an arm
  reads what is there, writes it back, and stays.  Stated in the \<open>\<forall>\<close>-form
  \<open>ktm_step_frozen_tape\<close> consumes, so the two compose by \<open>OF\<close>.\<close>

lemma embed_delta_frozen:
  assumes j: "j < off \<or> off + k \<le> j"
  shows "\<forall>q a q' a' d. (q, a, q', a', d) \<in> embed_delta off k k' \<Gamma> bl D
            \<longrightarrow> a' j = a j \<and> d j = MoveN"
  using j by (auto simp: embed_delta_def)

lemma embed_delta_support:
  assumes fit: "off + k \<le> k'" and j: "k' \<le> j"
  shows "\<forall>q a q' a' d. (q, a, q', a', d) \<in> embed_delta off k k' \<Gamma> bl D
            \<longrightarrow> a j = bl \<and> a' j = bl \<and> d j = MoveN"
  using fit j by (auto simp: embed_delta_def free_context_def)

text \<open>The third connector, and the one an arm needs to inherit its factor's
  endmarker discipline.  It is the frozen/window split again: inside the window
  the write is the factor's own and the hypothesis applies after shifting the
  index, and outside it the arm writes back what it read, so there is nothing
  to check.  Stated on the raw relation rather than on \<^const>\<open>le_unique\<close>,
  because an arm is a set of tuples and not yet a machine --- and in the
  \<open>\<forall>\<close>-form of the two connectors above rather than as a rule with the
  membership as a premise.  That is not cosmetic: in the premise form both this
  lemma and \<open>tag_delta_le_unique\<close> leave the window parameters schematic, and
  chaining them with \<^theory_text>\<open>OF\<close> reports multiple unifiers.  As closed
  propositions they compose first-order.\<close>

lemma embed_delta_le_unique:
  assumes lu: "\<forall>q a q' a' d j. (q, a, q', a', d) \<in> D
                  \<longrightarrow> a' j = le \<longrightarrow> a j = le"
  shows "\<forall>q a q' a' d j. (q, a, q', a', d) \<in> embed_delta off k k' \<Gamma> bl D
            \<longrightarrow> a' j = le \<longrightarrow> a j = le"
proof (intro allI impI)
  fix q a q' a' d and j :: nat
  assume mem: "(q, a, q', a', d) \<in> embed_delta off k k' \<Gamma> bl D"
     and w: "a' j = le"
  from mem obtain p b p' b' e c
    where tup: "(p, b, p', b', e) \<in> D"
      and a: "a = (\<lambda>i. if off \<le> i \<and> i < off + k then b (i - off) else c i)"
      and a': "a' = (\<lambda>i. if off \<le> i \<and> i < off + k then b' (i - off) else c i)"
    by (auto simp: embed_delta_def)
  show "a j = le"
  proof (cases "off \<le> j \<and> j < off + k")
    case True
    with w a' have "b' (j - off) = le" by simp
    with lu tup have "b (j - off) = le" by blast
    with True a show ?thesis by simp
  next
    \<comment> \<open>the negated window condition is a \<^emph>\<open>conjunction\<close>, whose normal form is
        an implication and so not a rewrite \<^theory_text>\<open>simp\<close> can fire on the
        \<^theory_text>\<open>if\<close>; \<open>if_not_P\<close> turns it into one\<close>
    case False
    then have out: "\<not> (off \<le> j \<and> j < off + k)" by blast
    from w a' have "c j = le" by (simp add: if_not_P [OF out])
    with a show ?thesis by (simp add: if_not_P [OF out])
  qed
qed

lemma embed_delta_finite:
  assumes fD: "finite D" and fG: "finite \<Gamma>"
  shows "finite (embed_delta off k k' \<Gamma> bl D)"
  unfolding embed_delta_def
  using fD free_context_finite [OF fG] by blast

text \<open>What a step of an arm does, in the two halves the composite argument
  needs.  Outside the window it does nothing, which is the previous subsection
  applied through \<open>embed_delta_frozen\<close> --- a rule application, not a proof.
  Inside it, the arm is the factor, which is \<open>embed_step_rev\<close> below.\<close>

lemma embed_step_outside:
  assumes step: "(C, C') \<in> ktm_step (embed_delta off k k' \<Gamma> bl D)"
    and j: "j < off \<or> off + k \<le> j"
  shows "ktc_tape C' j = ktc_tape C j \<and> ktc_pos C' j = ktc_pos C j"
  by (rule ktm_step_frozen_tape [OF step embed_delta_frozen [OF j]])

text \<open>The window, read back as a configuration of the factor.  Beyond the
  factor's own tape count the projection is uniformly blank with the head at
  the origin --- not an arbitrary choice, but what \<^const>\<open>valid_config_ktm\<close>
  demands of the factor, so the projection of a composite configuration is a
  configuration the factor could actually be in.\<close>

definition proj_config ::
  "nat \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> ('a, 'q) ktc_config \<Rightarrow> ('a, 'q) ktc_config" where
  "proj_config off k bl C =
     KConfig (ktc_state C)
       (\<lambda>j. if j < k then ktc_tape C (j + off) else (\<lambda>_. bl))
       (\<lambda>j. if j < k then ktc_pos C (j + off) else 0)"

lemma proj_config_state [simp]:
  "ktc_state (proj_config off k bl C) = ktc_state C"
  by (simp add: proj_config_def)

text \<open>\<^const>\<open>ktc_tape\<close> returns a function rather than a value, so its
  selector equation rewrites only once the goal is pointwise; \<open>fun_eq_iff\<close>
  is what makes it fire, as in \<open>widen_step\<close>.  Doing that once here keeps it out
  of every consumer.\<close>

lemma proj_config_Config [simp]:
  "proj_config off k bl (KConfig q ts n)
     = KConfig q (\<lambda>j. if j < k then ts (j + off) else (\<lambda>_. bl))
                  (\<lambda>j. if j < k then n (j + off) else 0)"
  by (simp add: proj_config_def fun_eq_iff)

text \<open>The same content through the selectors, for the case the rule above
  does not reach: an argument that is not literally a \<^const>\<open>KConfig\<close>.  With
  the datatype's own \<open>ktc_config.expand\<close> (followed by \<open>intro conjI\<close>) these
  turn an equation between configurations into three equations between
  components, which is the form in which the \<^const>\<open>ktc_tape\<close> eta-problem above
  stops mattering --- each component \<^emph>\<open>is\<close> a function equation, so
  \<open>fun_eq_iff\<close> has something to bite on.\<close>

lemma proj_config_tape [simp]:
  "ktc_tape (proj_config off k bl C)
     = (\<lambda>j. if j < k then ktc_tape C (j + off) else (\<lambda>_. bl))"
  by (simp add: proj_config_def)

lemma proj_config_pos [simp]:
  "ktc_pos (proj_config off k bl C)
     = (\<lambda>j. if j < k then ktc_pos C (j + off) else 0)"
  by (simp add: proj_config_def)

text \<open>\<^bold>\<open>The projection sees the window and nothing else\<close>, which is obvious
  from the definition and worth having as a rule because the consumer that
  needs it has a composite it cannot rewrite.  Two configurations of the whole
  machine agreeing on one factor's tapes and heads project to the same
  configuration of that factor, whatever they do elsewhere --- so a phase that
  writes outside the window leaves every later projection of it alone.\<close>

lemma proj_config_cong:
  assumes st: "ktc_state X = ktc_state Y"
      and tp: "\<And>j. j < k \<Longrightarrow> ktc_tape X (j + off) = ktc_tape Y (j + off)"
      and ps: "\<And>j. j < k \<Longrightarrow> ktc_pos X (j + off) = ktc_pos Y (j + off)"
  shows "proj_config off k bl X = proj_config off k bl Y"
  using assms by (simp add: proj_config_def fun_eq_iff)

text \<open>\<^bold>\<open>The support hypothesis is doing real work and is not decoration.\<close>
  Beyond the factor's tape count the projection is blank with a parked head,
  and a step has to leave it that way; that holds exactly because a valid
  factor's transitions are blank and stationary there.  Callers discharge it
  from \<open>valid_ktm_delta_support\<close>.  It is stated in the \<open>\<forall>\<close>-form because a
  meta-quantified premise passed with \<open>OF\<close> is a higher-order pattern that
  the unifier cannot solve uniquely, while an object-level one matches
  directly.\<close>

lemma embed_step_rev:
  assumes step: "(C, C') \<in> ktm_step (embed_delta off k k' \<Gamma> bl D)"
    and supp: "\<forall>q a q' a' d. (q, a, q', a', d) \<in> D
                  \<longrightarrow> (\<forall>j \<ge> k. a j = bl \<and> a' j = bl \<and> d j = MoveN)"
  shows "(proj_config off k bl C, proj_config off k bl C') \<in> ktm_step D"
proof -
  from step obtain q ts n q' A Dd where
      C: "C = KConfig q ts n"
    and C': "C' = KConfig q' (\<lambda>j. (ts j)(n j := A j))
                             (\<lambda>j. go_move (Dd j) (n j))"
    and tr: "(q, \<lambda>j. ts j (n j), q', A, Dd)
               \<in> embed_delta off k k' \<Gamma> bl D"
    by (auto elim!: ktm_step.cases)
  from tr obtain a a' d b where
      inD: "(q, a, q', a', d) \<in> D"
    and rd: "(\<lambda>j. ts j (n j))
               = (\<lambda>j. if off \<le> j \<and> j < off + k then a (j - off) else b j)"
    and wr: "A = (\<lambda>j. if off \<le> j \<and> j < off + k then a' (j - off) else b j)"
    and dd: "Dd = (\<lambda>j. if off \<le> j \<and> j < off + k
                        then d (j - off) else MoveN)"
    by (auto simp: embed_delta_def)
  from supp inD have sa: "\<And>j. k \<le> j \<Longrightarrow> a j = bl"
    and sa': "\<And>j. k \<le> j \<Longrightarrow> a' j = bl"
    and sd: "\<And>j. k \<le> j \<Longrightarrow> d j = MoveN"
    by blast+
  let ?tp = "\<lambda>j. if j < k then ts (j + off) else (\<lambda>_. bl)"
  let ?np = "\<lambda>j. if j < k then n (j + off) else 0"
  have pc: "proj_config off k bl C = KConfig q ?tp ?np"
    unfolding C by simp
  have read: "(\<lambda>j. ?tp j (?np j)) = a"
  proof (rule ext)
    fix j
    show "?tp j (?np j) = a j"
    proof (cases "j < k")
      case True
      from fun_cong [OF rd, of "j + off"] True
      have "ts (j + off) (n (j + off)) = a j" by simp
      with True show ?thesis by simp
    next
      case False
      with sa show ?thesis by simp
    qed
  qed
  have tape': "(\<lambda>j. if j < k then (ts (j + off))(n (j + off) := A (j + off))
                    else (\<lambda>_. bl))
                 = (\<lambda>j. (?tp j)(?np j := a' j))"
  proof (rule ext)
    fix j
    show "(if j < k then (ts (j + off))(n (j + off) := A (j + off))
           else (\<lambda>_. bl)) = (?tp j)(?np j := a' j)"
    proof (cases "j < k")
      case True
      from fun_cong [OF wr, of "j + off"] True
      have "A (j + off) = a' j" by simp
      with True show ?thesis by simp
    next
      case False
      with sa' show ?thesis by (simp add: fun_eq_iff)
    qed
  qed
  have pos': "(\<lambda>j. if j < k then go_move (Dd (j + off)) (n (j + off)) else 0)
                = (\<lambda>j. go_move (d j) (?np j))"
  proof (rule ext)
    fix j
    show "(if j < k then go_move (Dd (j + off)) (n (j + off)) else 0)
            = go_move (d j) (?np j)"
    proof (cases "j < k")
      case True
      from fun_cong [OF dd, of "j + off"] True
      have "Dd (j + off) = d j" by simp
      with True show ?thesis by simp
    next
      case False
      with sd show ?thesis by simp
    qed
  qed
  have pc': "proj_config off k bl C'
               = KConfig q' (\<lambda>j. (?tp j)(?np j := a' j))
                            (\<lambda>j. go_move (d j) (?np j))"
    unfolding C' using tape' pos' by simp
  show ?thesis
    unfolding pc pc'
  proof (rule ktm_step.step)
    show "(q, \<lambda>j. ?tp j (?np j), q', a', d) \<in> D"
      using read inD by simp
  qed
qed

lemma embed_run_rev:
  assumes supp: "\<forall>q a q' a' d. (q, a, q', a', d) \<in> D
                    \<longrightarrow> (\<forall>j \<ge> k. a j = bl \<and> a' j = bl \<and> d j = MoveN)"
    and run: "(C, C') \<in> ktm_step (embed_delta off k k' \<Gamma> bl D) ^^ N"
  shows "(proj_config off k bl C, proj_config off k bl C') \<in> ktm_step D ^^ N"
  using run
proof (induction N arbitrary: C')
  case 0
  then show ?case by simp
next
  case (Suc N)
  from Suc.prems obtain E
    where CE: "(C, E) \<in> ktm_step (embed_delta off k k' \<Gamma> bl D) ^^ N"
      and EC': "(E, C') \<in> ktm_step (embed_delta off k k' \<Gamma> bl D)"
    by auto
  from Suc.IH [OF CE] embed_step_rev [OF EC' supp] show ?case by auto
qed

text \<open>The forward direction.  Where the reverse lemma projects, this one
  \<^emph>\<open>updates\<close>: the factor moves inside the window and everything else stays as
  the composite configuration had it.

  \<^bold>\<open>The agreement hypothesis is \<open>proj_config off k bl C = c\<close> rather than a
  predicate of its own\<close>, which is what makes the two directions compose without
  a translation step --- the reverse lemma \<^emph>\<open>produces\<close> exactly this equation.
  It also says more than "the window matches": it pins the factor's tapes
  beyond its own count to blank with the head at the origin, which is what
  \<^const>\<open>valid_config_ktm\<close> asks of the factor anyway.

  \<^bold>\<open>No support hypothesis here, unlike the reverse direction.\<close>  Going this way
  nothing outside the window is claimed about the factor's transitions: the
  frozen tapes are carried by the context \<open>b\<close>, which is chosen to be the
  composite's own reads, so each is written straight back whatever the factor's
  tuple says beyond \<open>k\<close>.  The obligation that replaces it is \<open>ctx\<close>, and that
  one is about the \<^emph>\<open>composite\<close> configuration rather than the factor.\<close>

definition embed_update ::
  "nat \<Rightarrow> nat \<Rightarrow> ('a, 'q) ktc_config \<Rightarrow> ('a, 'q) ktc_config
     \<Rightarrow> ('a, 'q) ktc_config" where
  "embed_update off k C c' =
     KConfig (ktc_state c')
       (\<lambda>j. if off \<le> j \<and> j < off + k then ktc_tape c' (j - off)
            else ktc_tape C j)
       (\<lambda>j. if off \<le> j \<and> j < off + k then ktc_pos c' (j - off)
            else ktc_pos C j)"

lemma embed_update_Config [simp]:
  "embed_update off k (KConfig Q TS N) (KConfig q' T P)
     = KConfig q' (\<lambda>j. if off \<le> j \<and> j < off + k then T (j - off) else TS j)
                  (\<lambda>j. if off \<le> j \<and> j < off + k then P (j - off) else N j)"
  by (simp add: embed_update_def fun_eq_iff)

text \<open>The state selector separately, because the rule above needs both
  arguments to be literal \<^const>\<open>KConfig\<close> terms and the one an iteration
  produces is not.  The composite takes the factor's state whole: the window
  is where the two frames differ, and the state is not in the window.\<close>

lemma embed_update_state [simp]:
  "ktc_state (embed_update off k X c') = ktc_state c'"
  by (simp add: embed_update_def)

text \<open>The tape selectors, one per side of the window boundary, and they are
  what a \<^emph>\<open>value\<close> read off a composite tape needs.  \<^const>\<open>proj_config\<close> answers
  the same question for the whole window at once, but a consumer that wants one
  tape --- a counter, a numeral, an output --- would have to project, discard
  \<open>k - 1\<close> tapes and index the survivor.  Addressing the cell directly is the
  same fact with no packaging, and the second form is the one that says a
  neighbouring window read the update as if it had not happened.

  Stated at \<^term>\<open>off + l\<close> rather than at an arbitrary \<open>j\<close> in range, because
  that is the shape a layout produces: an address is built by adding a
  factor-local index to the window's base, so the subtraction the definition
  performs cancels syntactically instead of by an arithmetic side goal.\<close>

lemma embed_update_tape_in:
  assumes "l < k"
  shows "ktc_tape (embed_update off k X c') (off + l) = ktc_tape c' l"
  using assms by (simp add: embed_update_def)

lemma embed_update_pos_in:
  assumes "l < k"
  shows "ktc_pos (embed_update off k X c') (off + l) = ktc_pos c' l"
  using assms by (simp add: embed_update_def)

lemma embed_update_tape_out:
  assumes "j < off \<or> off + k \<le> j"
  shows "ktc_tape (embed_update off k X c') j = ktc_tape X j"
  using assms by (auto simp: embed_update_def)

text \<open>The head half of the clause above.  A caller outside the window
  usually wants both: that the cells did not change \<^emph>\<open>and\<close> that the head
  did not move, so that what another factor reads on a tape outside the
  window survives a step taken inside it.\<close>

lemma embed_update_pos_out:
  assumes "j < off \<or> off + k \<le> j"
  shows "ktc_pos (embed_update off k X c') j = ktc_pos X j"
  using assms by (auto simp: embed_update_def)

lemma embed_step:
  assumes step: "(proj_config off k bl C, c') \<in> ktm_step D"
    and ctx: "(\<lambda>j. ktc_tape C j (ktc_pos C j)) \<in> free_context \<Gamma> bl k'"
  shows "(C, embed_update off k C c')
           \<in> ktm_step (embed_delta off k k' \<Gamma> bl D)"
proof -
  obtain Q TS N where C: "C = KConfig Q TS N" by (cases C)
  let ?ts = "\<lambda>i. if i < k then TS (i + off) else (\<lambda>_. bl)"
  let ?n = "\<lambda>i. if i < k then N (i + off) else 0"
  have pc: "proj_config off k bl C = KConfig Q ?ts ?n"
    unfolding C by simp
  from step obtain q ts n q' a' d where
      pceq: "proj_config off k bl C = KConfig q ts n"
    and c': "c' = KConfig q' (\<lambda>i. (ts i)(n i := a' i))
                             (\<lambda>i. go_move (d i) (n i))"
    and tr: "(q, \<lambda>i. ts i (n i), q', a', d) \<in> D"
    by (auto elim!: ktm_step.cases)
  from pc pceq have q: "q = Q" and ts: "ts = ?ts" and n: "n = ?n" by auto
  \<comment> \<open>inside the window the factor's tapes are the composite's, shifted\<close>
  have win_ts: "ts (j - off) = TS j" if "off \<le> j" and "j < off + k" for j
  proof -
    from that have "j - off < k" and "j - off + off = j" by auto
    then show ?thesis by (simp add: ts)
  qed
  have win_n: "n (j - off) = N j" if "off \<le> j" and "j < off + k" for j
  proof -
    from that have "j - off < k" and "j - off + off = j" by auto
    then show ?thesis by (simp add: n)
  qed
  let ?b = "\<lambda>j. TS j (N j)"
  let ?A = "\<lambda>j. if off \<le> j \<and> j < off + k then a' (j - off) else ?b j"
  let ?Dd = "\<lambda>j. if off \<le> j \<and> j < off + k then d (j - off) else MoveN"
  have ctxb: "?b \<in> free_context \<Gamma> bl k'" using ctx unfolding C by simp
  have read: "(\<lambda>j. if off \<le> j \<and> j < off + k
                    then (\<lambda>i. ts i (n i)) (j - off) else ?b j) = ?b"
  proof (rule ext)
    fix j
    show "(if off \<le> j \<and> j < off + k
           then (\<lambda>i. ts i (n i)) (j - off) else ?b j) = ?b j"
      using win_ts win_n by simp
  qed
  have inarm: "(Q, ?b, q', ?A, ?Dd) \<in> embed_delta off k k' \<Gamma> bl D"
    unfolding embed_delta_def
  proof (rule image_eqI [where x = "((q, \<lambda>i. ts i (n i), q', a', d), ?b)"])
    show "((q, \<lambda>i. ts i (n i), q', a', d), ?b)
            \<in> D \<times> free_context \<Gamma> bl k'"
      using tr ctxb by simp
  qed (use q read in simp)
  have tp: "(\<lambda>j. if off \<le> j \<and> j < off + k
                  then (ts (j - off))(n (j - off) := a' (j - off)) else TS j)
              = (\<lambda>j. (TS j)(N j := ?A j))"
  proof (rule ext)
    fix j
    show "(if off \<le> j \<and> j < off + k
           then (ts (j - off))(n (j - off) := a' (j - off)) else TS j)
            = (TS j)(N j := ?A j)"
    proof (cases "off \<le> j \<and> j < off + k")
      case True
      then have "ts (j - off) = TS j" and "n (j - off) = N j"
        using win_ts win_n by auto
      with True show ?thesis by simp
    next
      case False
      then show ?thesis by (simp add: if_not_P [OF False])
    qed
  qed
  have pp: "(\<lambda>j. if off \<le> j \<and> j < off + k
                  then go_move (d (j - off)) (n (j - off)) else N j)
              = (\<lambda>j. go_move (?Dd j) (N j))"
  proof (rule ext)
    fix j
    show "(if off \<le> j \<and> j < off + k
           then go_move (d (j - off)) (n (j - off)) else N j)
            = go_move (?Dd j) (N j)"
    proof (cases "off \<le> j \<and> j < off + k")
      case True
      then have "n (j - off) = N j" using win_n by auto
      with True show ?thesis by simp
    next
      case False
      then show ?thesis by (simp add: if_not_P [OF False])
    qed
  qed
  \<comment> \<open>stated in \<open>C\<close>-normal form: \<^theory_text>\<open>unfolding\<close> normalises with all its
      equations at once, so an \<open>eu\<close> mentioning \<open>C\<close> could never match\<close>
  have eu: "embed_update off k (KConfig Q TS N) c'
              = KConfig q' (\<lambda>j. (TS j)(N j := ?A j))
                           (\<lambda>j. go_move (?Dd j) (N j))"
    unfolding c' using tp pp by simp
  show ?thesis
    unfolding C eu
  proof (rule ktm_step.step)
    show "(Q, \<lambda>j. TS j (N j), q', ?A, ?Dd)
            \<in> embed_delta off k k' \<Gamma> bl D"
      by (rule inarm)
  qed
qed

text \<open>The two directions are inverse on the window, which is what lets
  \<open>embed_step\<close> be iterated: the composite configuration it produces projects
  back to the factor configuration it was given.  The hypothesis is the
  factor's blank-and-parked tail, exactly what \<^const>\<open>valid_config_ktm\<close>
  supplies --- the projection cannot invent it, because beyond \<open>k\<close> the window
  carries no information.

  \<^bold>\<open>Iterating needs \<open>ctx\<close> at every intermediate composite configuration,
  and that is an invariant of the \<^emph>\<open>window\<close> rather than of the composite.\<close>
  Which is what makes the forward run lemma statable at all, and it is worth
  saying why the opposite looked true.  The intermediate configurations of the
  iteration are not arbitrary composites: every one of them is
  \<^term>\<open>embed_update off k X d\<close>, equal to the starting \<open>X\<close> everywhere outside
  the window.  So the two clauses of \<open>ctx\<close> are re-established from different
  places --- outside the window from \<open>X\<close>'s own \<open>ctx\<close>, unchanged; inside it
  from the \<^emph>\<open>factor's\<close> alphabet clause, and the factor is a machine already.
  The composite never has to be valid, and never has to exist.  \<open>embed_run\<close>
  below is the iteration; the three lemmas here are the window algebra it
  spends, and they hold with no machine in sight.\<close>

lemma proj_embed_update:
  assumes tail: "\<forall>i \<ge> k. ktc_tape c' i = (\<lambda>_. bl) \<and> ktc_pos c' i = 0"
  shows "proj_config off k bl (embed_update off k C c') = c'"
proof -
  obtain Q TS N where C: "C = KConfig Q TS N" by (cases C)
  obtain q' T P where c': "c' = KConfig q' T P" by (cases c')
  from tail c' have tT: "\<And>i. k \<le> i \<Longrightarrow> T i = (\<lambda>_. bl)"
    and tP: "\<And>i. k \<le> i \<Longrightarrow> P i = 0" by auto
  show ?thesis
    unfolding C c' by (auto simp: fun_eq_iff tT tP)
qed

text \<open>The other inverse, and unlike the one above it needs no hypothesis:
  updating a window with what that window already holds is the identity.  This
  is the iteration's base case, where zero steps of the factor have to leave
  the composite configuration syntactically unchanged rather than merely
  equivalent on the window.\<close>

lemma embed_update_proj_config:
  "embed_update off k X (proj_config off k bl X) = X"
proof -
  obtain Q TS N where X: "X = KConfig Q TS N" by (cases X)
  show ?thesis unfolding X
    by (auto simp: embed_update_def proj_config_def fun_eq_iff)
qed

text \<open>And the composition: a second update overwrites the first, because the
  window is written wholesale and the outside is carried from the same \<open>X\<close>
  both times.  Without this the induction produces a tower of updates one deep
  per step instead of the single one the statement claims.\<close>

lemma embed_update_embed_update:
  "embed_update off k (embed_update off k X d) c' = embed_update off k X c'"
  by (simp add: embed_update_def fun_eq_iff)

text \<open>The invariant itself.  \<open>ctx\<close> asks two things of the composite's read
  vector and they come from opposite sides: every cell is in \<open>\<Gamma>\<close>, which
  inside the window is the factor's alphabet clause and outside is \<open>X\<close>'s; and
  everything from \<open>k'\<close> on is blank, which is \<open>X\<close>'s alone --- the window sits
  below \<open>k'\<close>, so the factor is never asked about it.  Hence \<open>fit\<close>, and hence
  no hypothesis about the factor's own blank.\<close>

lemma embed_update_context:
  assumes ctx: "(\<lambda>j. ktc_tape X j (ktc_pos X j)) \<in> free_context \<Gamma> bl k'"
      and sym: "\<And>j p. ktc_tape c j p \<in> \<Gamma>"
      and fit: "off + k \<le> k'"
  shows "(\<lambda>j. ktc_tape (embed_update off k X c) j
                 (ktc_pos (embed_update off k X c) j))
           \<in> free_context \<Gamma> bl k'"
proof -
  have out: "\<not> (off \<le> j \<and> j < off + k)" if "k' \<le> j" for j
    using that fit by simp
  show ?thesis
    using ctx sym out
    by (auto simp: free_context_def embed_update_def)
qed


subsection \<open>Placing a machine inside a larger state space\<close>

text \<open>The state-side counterpart of the previous subsection, and the second
  half of an arm.  Placing a factor among other tapes says where it acts; this
  says who it is while it acts.  A composite of two machines taking turns has
  states \<open>'q\<^sub>N \<times> 'q\<^sub>D \<times> bool\<close>, and an arm is the moving factor's transitions with
  the other factor's state carried along untouched and the turn flipped.

  \<^bold>\<open>This is not \<open>relabel_delta\<close>, and the difference is the whole
  point.\<close>  A relabelling applies \<^emph>\<open>one\<close> map to both ends of a tuple, which is
  what makes it a bijection on configurations and lets its language theorem go
  through.  Here the two ends need \<^emph>\<open>different\<close> maps, because the turn
  component differs between them: an \<open>N\<close>-turn tuple starts in a state whose turn
  says \<open>N\<close> and ends in one whose turn says \<open>D\<close>.  So this is a genuinely weaker
  construction --- no bijection, no language theorem --- and correspondingly it
  gets only the two step lemmas a union of arms actually consumes.

  \<open>tag_delta\<close> leaves the tape components of every tuple alone.  That is what
  lets the previous subsection's facts be reused through it: the frozen and
  support properties are conditions on those components, so they survive
  tagging verbatim, and \<open>tag_delta_frozen\<close> and \<open>tag_delta_support\<close> below are
  the connectors that say so.\<close>

definition ktc_set_state :: "'r \<Rightarrow> ('a, 'q) ktc_config \<Rightarrow> ('a, 'r) ktc_config" where
  "ktc_set_state p C = KConfig p (ktc_tape C) (ktc_pos C)"

text \<open>
  The embedding relation carries an arbitrary context on the tapes outside
  the factor window.  Determinism therefore needs the factor's support
  invariant: beyond its own tape count every source read is the fixed blank.
  With that invariant, equal composite reads determine equal factor reads in
  the window and the support determines the tail; the context is then fixed
  outside the window as well.
\<close>

lemma embed_delta_det:
  assumes det:
    "\<And>q a p\<^sub>1 b\<^sub>1 d\<^sub>1 p\<^sub>2 b\<^sub>2 d\<^sub>2.
       (q, a, p\<^sub>1, b\<^sub>1, d\<^sub>1) \<in> D \<Longrightarrow>
       (q, a, p\<^sub>2, b\<^sub>2, d\<^sub>2) \<in> D \<Longrightarrow>
       (p\<^sub>1, b\<^sub>1, d\<^sub>1) = (p\<^sub>2, b\<^sub>2, d\<^sub>2)"
      and supp:
    "\<And>q a p b d. (q, a, p, b, d) \<in> D \<Longrightarrow>
      (\<And>j. k \<le> j \<Longrightarrow> a j = bl)"
      and tr\<^sub>1: "(Q, A, Q\<^sub>1, A\<^sub>1, E\<^sub>1)
                    \<in> embed_delta off k k' \<Gamma> bl D"
      and tr\<^sub>2: "(Q, A, Q\<^sub>2, A\<^sub>2, E\<^sub>2)
                    \<in> embed_delta off k k' \<Gamma> bl D"
  shows "(Q\<^sub>1, A\<^sub>1, E\<^sub>1) = (Q\<^sub>2, A\<^sub>2, E\<^sub>2)"
proof -
  from tr\<^sub>1 obtain q\<^sub>1 a\<^sub>1 p\<^sub>1 b\<^sub>1 d\<^sub>1 c\<^sub>1
    where in\<^sub>1: "(q\<^sub>1, a\<^sub>1, p\<^sub>1, b\<^sub>1, d\<^sub>1) \<in> D"
      and c\<^sub>1: "c\<^sub>1 \<in> free_context \<Gamma> bl k'"
      and Q\<^sub>1: "Q = q\<^sub>1"
      and T\<^sub>1: "Q\<^sub>1 = p\<^sub>1"
      and A\<^sub>1: "A = (\<lambda>j. if off \<le> j \<and> j < off + k
                              then a\<^sub>1 (j - off) else c\<^sub>1 j)"
      and W\<^sub>1: "A\<^sub>1 = (\<lambda>j. if off \<le> j \<and> j < off + k
                              then b\<^sub>1 (j - off) else c\<^sub>1 j)"
      and M\<^sub>1: "E\<^sub>1 = (\<lambda>j. if off \<le> j \<and> j < off + k
                              then d\<^sub>1 (j - off) else MoveN)"
    by (auto simp: embed_delta_def)
  from tr\<^sub>2 obtain q\<^sub>2 a\<^sub>2 p\<^sub>2 b\<^sub>2 d\<^sub>2 c\<^sub>2
    where in\<^sub>2: "(q\<^sub>2, a\<^sub>2, p\<^sub>2, b\<^sub>2, d\<^sub>2) \<in> D"
      and c\<^sub>2: "c\<^sub>2 \<in> free_context \<Gamma> bl k'"
      and Q\<^sub>2: "Q = q\<^sub>2"
      and T\<^sub>2: "Q\<^sub>2 = p\<^sub>2"
      and A\<^sub>2: "A = (\<lambda>j. if off \<le> j \<and> j < off + k
                              then a\<^sub>2 (j - off) else c\<^sub>2 j)"
      and W\<^sub>2: "A\<^sub>2 = (\<lambda>j. if off \<le> j \<and> j < off + k
                              then b\<^sub>2 (j - off) else c\<^sub>2 j)"
      and M\<^sub>2: "E\<^sub>2 = (\<lambda>j. if off \<le> j \<and> j < off + k
                              then d\<^sub>2 (j - off) else MoveN)"
    by (auto simp: embed_delta_def)
  have qeq: "q\<^sub>1 = q\<^sub>2" using Q\<^sub>1 Q\<^sub>2 by simp
  have aread: "a\<^sub>1 = a\<^sub>2"
  proof (rule ext)
    fix j
    show "a\<^sub>1 j = a\<^sub>2 j"
    proof (cases "j < k")
      case True
      have x\<^sub>1: "A (j + off) = a\<^sub>1 j"
        using fun_cong [OF A\<^sub>1, of "j + off"] True by simp
      have x\<^sub>2: "A (j + off) = a\<^sub>2 j"
        using fun_cong [OF A\<^sub>2, of "j + off"] True by simp
      from x\<^sub>1 x\<^sub>2 show ?thesis by simp
    next
      case False
      have jge: "k \<le> j" using False by simp
      have s\<^sub>1: "a\<^sub>1 j = bl"
        using supp [OF in\<^sub>1] jge by blast
      have s\<^sub>2: "a\<^sub>2 j = bl"
        using supp [OF in\<^sub>2] jge by blast
      from s\<^sub>1 s\<^sub>2 show ?thesis by simp
    qed
  qed
  have in\<^sub>2': "(q\<^sub>1, a\<^sub>1, p\<^sub>2, b\<^sub>2, d\<^sub>2) \<in> D"
    using in\<^sub>2 qeq aread by simp
  have out: "(p\<^sub>1, b\<^sub>1, d\<^sub>1) = (p\<^sub>2, b\<^sub>2, d\<^sub>2)"
    by (rule det [OF in\<^sub>1 in\<^sub>2'])
  have beq: "b\<^sub>1 = b\<^sub>2" using out by (simp add: prod_eq_iff)
  have deq: "d\<^sub>1 = d\<^sub>2" using out by (simp add: prod_eq_iff)
  have ceq: "\<And>j. \<not> (off \<le> j \<and> j < off + k)
                    \<Longrightarrow> c\<^sub>1 j = c\<^sub>2 j"
  proof -
    fix j
    assume outside: "\<not> (off \<le> j \<and> j < off + k)"
    have x\<^sub>1: "A j = c\<^sub>1 j"
      using fun_cong [OF A\<^sub>1, of j] outside by simp
    have x\<^sub>2: "A j = c\<^sub>2 j"
      using fun_cong [OF A\<^sub>2, of j] outside by simp
    from x\<^sub>1 x\<^sub>2 show "c\<^sub>1 j = c\<^sub>2 j" by simp
  qed
  have Weq: "A\<^sub>1 = A\<^sub>2"
  proof (rule ext)
    fix j
    show "A\<^sub>1 j = A\<^sub>2 j"
    proof (cases "off \<le> j \<and> j < off + k")
      case True
      have w\<^sub>1j: "A\<^sub>1 j = b\<^sub>1 (j - off)"
        using fun_cong [OF W\<^sub>1, of j] True by simp
      have w\<^sub>2j: "A\<^sub>2 j = b\<^sub>2 (j - off)"
        using fun_cong [OF W\<^sub>2, of j] True by simp
      from w\<^sub>1j w\<^sub>2j beq show ?thesis by simp
    next
      case False
      have w\<^sub>1j: "A\<^sub>1 j = c\<^sub>1 j"
        using fun_cong [OF W\<^sub>1, of j] False by simp
      have w\<^sub>2j: "A\<^sub>2 j = c\<^sub>2 j"
        using fun_cong [OF W\<^sub>2, of j] False by simp
      from w\<^sub>1j w\<^sub>2j ceq [OF False] show ?thesis by simp
    qed
  qed
  have Meq: "E\<^sub>1 = E\<^sub>2"
  proof (rule ext)
    fix j
    show "E\<^sub>1 j = E\<^sub>2 j"
    proof (cases "off \<le> j \<and> j < off + k")
      case True
      have m\<^sub>1j: "E\<^sub>1 j = d\<^sub>1 (j - off)"
        using fun_cong [OF M\<^sub>1, of j] True by simp
      have m\<^sub>2j: "E\<^sub>2 j = d\<^sub>2 (j - off)"
        using fun_cong [OF M\<^sub>2, of j] True by simp
      from m\<^sub>1j m\<^sub>2j deq show ?thesis by simp
    next
      case False
      have m\<^sub>1j: "E\<^sub>1 j = MoveN"
        using fun_cong [OF M\<^sub>1, of j] False by simp
      have m\<^sub>2j: "E\<^sub>2 j = MoveN"
        using fun_cong [OF M\<^sub>2, of j] False by simp
      from m\<^sub>1j m\<^sub>2j show ?thesis by simp
    qed
  qed
  from out have "p\<^sub>1 = p\<^sub>2" by simp
  with Q\<^sub>1 Q\<^sub>2 T\<^sub>1 T\<^sub>2 Weq Meq show ?thesis by simp
qed

definition tag_delta ::
  "('q \<Rightarrow> 'r) \<Rightarrow> ('q \<Rightarrow> 'r)
     \<Rightarrow> ('q \<times> (nat \<Rightarrow> 'a) \<times> 'q \<times> (nat \<Rightarrow> 'a) \<times> (nat \<Rightarrow> move)) set
     \<Rightarrow> ('r \<times> (nat \<Rightarrow> 'a) \<times> 'r \<times> (nat \<Rightarrow> 'a) \<times> (nat \<Rightarrow> move)) set" where
  "tag_delta u v D = (\<lambda>(q, a, q', a', d). (u q, a, v q', a', d)) ` D"

text \<open>Tagging keeps a functional relation functional when the source tag is
  injective: the tagged source names the untagged one, and the rest of a
  tuple is carried unchanged.\<close>

lemma tag_delta_det:
  assumes u: "inj u"
      and det:
    "\<And>q a p\<^sub>1 b\<^sub>1 d\<^sub>1 p\<^sub>2 b\<^sub>2 d\<^sub>2.
       (q, a, p\<^sub>1, b\<^sub>1, d\<^sub>1) \<in> D \<Longrightarrow>
       (q, a, p\<^sub>2, b\<^sub>2, d\<^sub>2) \<in> D \<Longrightarrow>
       (p\<^sub>1, b\<^sub>1, d\<^sub>1) = (p\<^sub>2, b\<^sub>2, d\<^sub>2)"
      and tr\<^sub>1: "(Q, A, Q\<^sub>1, A\<^sub>1, E\<^sub>1) \<in> tag_delta u v D"
      and tr\<^sub>2: "(Q, A, Q\<^sub>2, A\<^sub>2, E\<^sub>2) \<in> tag_delta u v D"
  shows "(Q\<^sub>1, A\<^sub>1, E\<^sub>1) = (Q\<^sub>2, A\<^sub>2, E\<^sub>2)"
proof -
  from tr\<^sub>1 obtain q\<^sub>1 q\<^sub>1' where t\<^sub>1: "(q\<^sub>1, A, q\<^sub>1', A\<^sub>1, E\<^sub>1) \<in> D"
      and Q\<^sub>1: "Q = u q\<^sub>1" and T\<^sub>1: "Q\<^sub>1 = v q\<^sub>1'"
    unfolding tag_delta_def by auto
  from tr\<^sub>2 obtain q\<^sub>2 q\<^sub>2' where t\<^sub>2: "(q\<^sub>2, A, q\<^sub>2', A\<^sub>2, E\<^sub>2) \<in> D"
      and Q\<^sub>2: "Q = u q\<^sub>2" and T\<^sub>2: "Q\<^sub>2 = v q\<^sub>2'"
    unfolding tag_delta_def by auto
  from Q\<^sub>1 Q\<^sub>2 have "u q\<^sub>2 = u q\<^sub>1" by simp
  then have "q\<^sub>2 = q\<^sub>1" by (rule injD [OF u])
  with t\<^sub>2 have "(q\<^sub>1, A, q\<^sub>2', A\<^sub>2, E\<^sub>2) \<in> D" by simp
  from det [OF t\<^sub>1 this] have "(q\<^sub>1', A\<^sub>1, E\<^sub>1) = (q\<^sub>2', A\<^sub>2, E\<^sub>2)" .
  with T\<^sub>1 T\<^sub>2 show ?thesis by simp
qed

lemma ktc_set_state_Config [simp]: "ktc_set_state p (KConfig q ts n) = KConfig p ts n"
  by (simp add: ktc_set_state_def)

lemma ktc_set_state_state [simp]: "ktc_state (ktc_set_state p C) = p"
  by (simp add: ktc_set_state_def)

lemma ktc_set_state_pos [simp]: "ktc_pos (ktc_set_state p C) = ktc_pos C"
  by (simp add: ktc_set_state_def)

lemma ktc_set_state_tape [simp]: "ktc_tape (ktc_set_state p C) = ktc_tape C"
  by (cases C) simp

text \<open>\<^bold>\<open>Re-stating commutes with everything on the tape side, and saying so
  once is what keeps it out of the way.\<close>  A composite argument alternates
  between the two: the tape machinery moves a factor's window, and
  \<^const>\<open>ktc_set_state\<close> puts the composite's state back on top.  Left alone the two
  interleave, and a \<^const>\<open>ktc_set_state\<close> sitting between \<^const>\<open>proj_config\<close> and
  its argument blocks every rewrite underneath it --- the simplifier cannot see
  past it to the window at all.

  The four rules below push \<^const>\<open>ktc_set_state\<close> outwards until it meets either
  another \<^const>\<open>ktc_set_state\<close> or the state it already carries, at which point it
  disappears.  \<^const>\<open>embed_update\<close> and \<^const>\<open>proj_config\<close> read only tapes and
  head positions, and \<^const>\<open>ktc_set_state\<close> changes neither, so all four are
  immediate once unfolded; the value is entirely in their being oriented and
  \<^theory_text>\<open>simp\<close>.\<close>

lemma ktc_set_state_set_state [simp]: "ktc_set_state p (ktc_set_state q C) = ktc_set_state p C"
  by (simp add: ktc_set_state_def)

lemma ktc_set_state_self [simp]: "ktc_set_state (ktc_state C) C = C"
  by (cases C) (simp add: ktc_set_state_def)

lemma embed_update_set_state [simp]:
  "embed_update off k (ktc_set_state q C) c' = embed_update off k C c'"
  by (simp add: embed_update_def fun_eq_iff)

lemma proj_config_set_state [simp]:
  "proj_config off k bl (ktc_set_state q C) = ktc_set_state q (proj_config off k bl C)"
  by (simp add: proj_config_def ktc_set_state_def fun_eq_iff)

text \<open>\<open>ktc_set_state_self\<close> does not reach the shape an arm step actually produces.
  \<^term>\<open>embed_update off k C c'\<close> carries the factor's new state, so re-stating
  it to \<^term>\<open>ktc_state c'\<close> is a no-op --- but the two state terms are not
  syntactically equal, and \<open>embed_update_state\<close> points the wrong way to make
  them so.  Hence a rule of its own.\<close>

lemma ktc_set_state_embed_update [simp]:
  "ktc_set_state (ktc_state c') (embed_update off k C c') = embed_update off k C c'"
  by (simp add: embed_update_def ktc_set_state_def)

text \<open>The other half of what a composite needs: a window the update did not
  touch reads exactly as it did before.  \<open>embed_step_outside\<close> says this one
  index at a time about a \<^emph>\<open>step\<close>; this says it about the whole window at
  once, for the update the forward direction produces, and it is the fact that
  makes one arm's move invisible to the other factor's projection.

  One statement covers both arms because the two windows can be disjoint in
  either order: one factor updates below the other's window, and the other
  above it.

  \<^bold>\<open>The \<^const>\<open>ktc_set_state\<close> is not decoration --- without it the statement is
  false.\<close>  Disjoint windows make the tapes and the head positions agree, but
  \<^const>\<open>proj_config\<close> also copies the state through, and \<^const>\<open>embed_update\<close>
  replaces it with the moving factor's.  So the two projections genuinely
  differ, in exactly the one component the composite was going to overwrite
  anyway.  The wrapper is what every consumer has around it in any case, since
  a factor's projection may not carry a composite state.\<close>

lemma proj_embed_update_disjoint:
  assumes disj: "off + k \<le> off' \<or> off' + k' \<le> off"
  shows "ktc_set_state q (proj_config off' k' bl (embed_update off k C c'))
           = ktc_set_state q (proj_config off' k' bl C)"
proof -
  have "\<not> (off \<le> j + off' \<and> j + off' < off + k)" if "j < k'" for j
    using disj that by auto
  then show ?thesis
    by (auto simp: ktc_set_state_def proj_config_def embed_update_def fun_eq_iff)
qed

text \<open>The connectors to the tape side.  Tagging rewrites only the two state
  components, so a hypothesis about the reads, the writes and the directions
  passes straight through --- which is what lets an arm be built as
  \<open>tag_delta u v (embed_delta \<dots>)\<close> and still satisfy everything
  \<open>ktm_step_frozen_tape\<close> and \<^const>\<open>valid_ktm\<close> ask of it.\<close>

lemma tag_delta_frozen:
  assumes "\<forall>q a q' a' d. (q, a, q', a', d) \<in> D \<longrightarrow> a' j = a j \<and> d j = MoveN"
  shows "\<forall>q a q' a' d. (q, a, q', a', d) \<in> tag_delta u v D
            \<longrightarrow> a' j = a j \<and> d j = MoveN"
  using assms by (auto simp: tag_delta_def)

text \<open>The support connector is proved by hand rather than by \<^theory_text>\<open>auto\<close>, and
  the reason is worth recording.  Its conclusion mentions the free variable
  \<open>bl\<close>, so the simplifier orients the instance \<open>a j = bl\<close> it derives from the
  hypothesis as a rewrite \<^emph>\<open>toward\<close> \<open>bl\<close> --- eliminating \<open>bl\<close> from the goal
  and leaving the second conjunct as \<open>a' j = a j\<close>, which does not follow.  The
  frozen connector above escapes this because its conclusion has no free
  variable to rewrite away.\<close>

lemma tag_delta_support:
  assumes sup: "\<forall>q a q' a' d. (q, a, q', a', d) \<in> D
                   \<longrightarrow> a j = bl \<and> a' j = bl \<and> d j = MoveN"
  shows "\<forall>q a q' a' d. (q, a, q', a', d) \<in> tag_delta u v D
            \<longrightarrow> a j = bl \<and> a' j = bl \<and> d j = MoveN"
proof (intro allI impI)
  fix q a q' a' d
  assume "(q, a, q', a', d) \<in> tag_delta u v D"
  then obtain p p' where "(p, a, p', a', d) \<in> D"
    by (auto simp: tag_delta_def)
  from sup [rule_format, OF this]
  show "a j = bl \<and> a' j = bl \<and> d j = MoveN" .
qed

text \<open>The endmarker discipline is a statement about the reads and the writes
  alone, so tagging leaves it exactly where it was.  It is stated in the
  per-tuple form \<open>embed_delta_le_unique\<close> produces and consumes, so an arm's
  two layers compose by \<^theory_text>\<open>OF\<close>.\<close>

lemma tag_delta_le_unique:
  assumes lu: "\<forall>q a q' a' d j. (q, a, q', a', d) \<in> D
                  \<longrightarrow> a' j = le \<longrightarrow> a j = le"
  shows "\<forall>q a q' a' d j. (q, a, q', a', d) \<in> tag_delta u v D
            \<longrightarrow> a' j = le \<longrightarrow> a j = le"
proof (intro allI impI)
  fix q a q' a' d and j :: nat
  assume "(q, a, q', a', d) \<in> tag_delta u v D" and w: "a' j = le"
  \<comment> \<open>read back to the tuple it came from before the discipline is applied;
      handed the image directly, \<^theory_text>\<open>auto\<close> rewrites with \<open>w\<close> and loses \<open>le\<close>\<close>
  then obtain p p' where "(p, a, p', a', d) \<in> D"
    by (auto simp: tag_delta_def)
  with lu w show "a j = le" by blast
qed

lemma tag_delta_finite:
  assumes "finite D"
  shows "finite (tag_delta u v D)"
  using assms by (simp add: tag_delta_def)

lemma tag_delta_states:
  assumes "(Q, a, Q', a', d) \<in> tag_delta u v D"
  shows "Q \<in> range u \<and> Q' \<in> range v"
  using assms by (auto simp: tag_delta_def)

text \<open>The two step correspondences.  Both are stated with \<^const>\<open>ktc_set_state\<close>
  rather than on constructor patterns, because the consumer meets its
  configurations as opaque terms; the constructor forms follow by
  \<^theory_text>\<open>simp\<close>.\<close>

lemma tag_step:
  assumes step: "(c, c') \<in> ktm_step D"
  shows "(ktc_set_state (u (ktc_state c)) c, ktc_set_state (v (ktc_state c')) c')
           \<in> ktm_step (tag_delta u v D)"
proof -
  from step obtain q ts n q' a dr where
      c_eq:  "c = KConfig q ts n"
    and c'_eq: "c' = KConfig q'
                       (\<lambda>k. (ts k)(n k := a k))
                       (\<lambda>k. go_move (dr k) (n k))"
    and tr: "(q, \<lambda>k. ts k (n k), q', a, dr) \<in> D"
    by (auto elim: ktm_step.cases)
  have "(KConfig (u q) ts n,
         KConfig (v q')
           (\<lambda>k. (ts k)(n k := a k))
           (\<lambda>k. go_move (dr k) (n k)))
          \<in> ktm_step (tag_delta u v D)"
  proof (rule ktm_step.step)
    show "(u q, \<lambda>k. ts k (n k), v q', a, dr) \<in> tag_delta u v D"
      using tr by (force simp: tag_delta_def)
  qed
  then show ?thesis by (simp add: c_eq c'_eq)
qed

lemma tag_step_rev:
  assumes step: "(C, C') \<in> ktm_step (tag_delta u v D)"
  obtains q q' where "ktc_state C = u q" and "ktc_state C' = v q'"
    and "(ktc_set_state q C, ktc_set_state q' C') \<in> ktm_step D"
proof -
  from step obtain Q ts n Q' a dr where
      C_eq:  "C = KConfig Q ts n"
    and C'_eq: "C' = KConfig Q'
                       (\<lambda>k. (ts k)(n k := a k))
                       (\<lambda>k. go_move (dr k) (n k))"
    and tr: "(Q, \<lambda>k. ts k (n k), Q', a, dr) \<in> tag_delta u v D"
    by (auto elim: ktm_step.cases)
  from tr obtain q q' where inD: "(q, \<lambda>k. ts k (n k), q', a, dr) \<in> D"
    and uq: "Q = u q" and vq': "Q' = v q'"
    by (auto simp: tag_delta_def)
  have inner: "(KConfig q ts n,
                KConfig q'
                  (\<lambda>k. (ts k)(n k := a k))
                  (\<lambda>k. go_move (dr k) (n k)))
                 \<in> ktm_step D"
  proof (rule ktm_step.step)
    show "(q, \<lambda>k. ts k (n k), q', a, dr) \<in> D" by (rule inD)
  qed
  show ?thesis
  proof (rule that)
    show "ktc_state C = u q" by (simp add: C_eq uq)
    show "ktc_state C' = v q'" by (simp add: C'_eq vq')
    show "(ktc_set_state q C, ktc_set_state q' C') \<in> ktm_step D"
      using inner by (simp add: C_eq C'_eq)
  qed
qed

text \<open>The forward correspondence iterated.  Only the same-tag case is wanted:
  a run stays inside the tagged copy, so its two ends carry the same
  injection, and that is exactly what lets the steps chain --- the
  configuration each step ends on is the one the next begins on, tag and
  all.  With two different tags the endpoints would not meet and there would
  be no run to state.\<close>

lemma tag_run:
  assumes run: "(C, C') \<in> (ktm_step D) ^^ n"
  shows "(ktc_set_state (u (ktc_state C)) C, ktc_set_state (u (ktc_state C')) C')
           \<in> (ktm_step (tag_delta u u D)) ^^ n"
  by (rule relpow_map [where h = "\<lambda>C. ktc_set_state (u (ktc_state C)) C", OF _ run])
     (erule tag_step)

text \<open>The reverse correspondence iterated, and the one hypothesis it needs
  that the single step does not: the tag must be injective.  \<open>tag_step_rev\<close>
  hands back \<^emph>\<open>some\<close> untagged state at each end, and chaining two of them
  requires the state the first leg arrives at to be the state the second leg
  departs from --- which is a fact about the untagged copy, and only
  injectivity gets it back across the tag.  Every consumer tags with a
  datatype constructor, so it is free where it is spent.

  The starting state is a hypothesis rather than an output because the caller
  always knows it: a run inverted this way begins at a configuration the
  forward direction built.\<close>

lemma tag_run_rev:
  assumes inj: "\<And>x y. u x = u y \<Longrightarrow> x = y"
      and run: "(C, C') \<in> (ktm_step (tag_delta u u D)) ^^ n"
      and st: "ktc_state C = u q"
  shows "\<exists>q'. ktc_state C' = u q'
                \<and> (ktc_set_state q C, ktc_set_state q' C') \<in> (ktm_step D) ^^ n"
  using run
proof (induction n arbitrary: C')
  case 0
  then have "C' = C" by simp
  with st show ?case by auto
next
  case (Suc n)
  from Suc.prems obtain d where d1: "(C, d) \<in> (ktm_step (tag_delta u u D)) ^^ n"
    and d2: "(d, C') \<in> ktm_step (tag_delta u u D)" by auto
  from Suc.IH [OF d1] obtain p
    where p: "ktc_state d = u p"
      and left: "(ktc_set_state q C, ktc_set_state p d) \<in> (ktm_step D) ^^ n" by blast
  from d2 obtain r r' where r: "ktc_state d = u r" and r': "ktc_state C' = u r'"
    and right: "(ktc_set_state r d, ktc_set_state r' C') \<in> ktm_step D"
    by (rule tag_step_rev)
  from p r have "u p = u r" by simp
  then have "p = r" by (rule inj)
  with left right have "(ktc_set_state q C, ktc_set_state r' C') \<in> (ktm_step D) ^^ Suc n"
    by (auto intro: relpow_Suc_I)
  with r' show ?case by blast
qed

text \<open>An arm read back to the tuple it came from.  The two combinators are
  images, so this is nothing but their two definitions composed and
  \<^theory_text>\<open>auto\<close> would find it each time --- but each time it would leave the caller
  to name the six components by hand, and the caller is checking
  \<^const>\<open>valid_ktm\<close>, where every clause needs them.  It is the arm-shaped
  counterpart of \<open>relabel_source\<close>, and stated in the same style.

  The order of the two combinators is fixed by the arm's own shape ---
  placement inside, tagging outside --- because \<^const>\<open>tag_delta\<close> changes the
  state type and \<^const>\<open>embed_delta\<close> would then be embedding tuples of the
  wrong one.\<close>

lemma arm_source:
  assumes "(Q, A, Q', A', E) \<in> tag_delta u v (embed_delta off k k' \<Gamma> bl D)"
  obtains q a q' a' d b
  where "(q, a, q', a', d) \<in> D"
    and "b \<in> free_context \<Gamma> bl k'"
    and "Q = u q" and "Q' = v q'"
    and "A = (\<lambda>j. if off \<le> j \<and> j < off + k then a (j - off) else b j)"
    and "A' = (\<lambda>j. if off \<le> j \<and> j < off + k then a' (j - off) else b j)"
    and "E = (\<lambda>j. if off \<le> j \<and> j < off + k then d (j - off) else MoveN)"
  using assms by (auto simp: tag_delta_def embed_delta_def)


subsection \<open>What a run leaves behind\<close>

text \<open>\<^const>\<open>free_context\<close> is a hypothesis of every step lemma that carries a
  factor's step into an arm, so
  something has to supply it, and what supplies it is an invariant of the run
  rather than a fact about any one configuration.  \<open>ktc_tapes_fit\<close> is that
  invariant: every cell of every tape holds a symbol of the alphabet, and
  every tape above the count is blank throughout --- not merely at the head,
  which is what makes it survive a step whose head has moved.

  \<^bold>\<open>It is the substrate's \<^const>\<open>valid_config_ktm\<close>, two clauses of it,
  detached from the machine.\<close>  The detachment is the point and not an
  oversight: a composite carries its two factors' tapes side by side, and the
  configuration this has to hold of is not a configuration of either factor,
  so there is no machine to name.  \<open>valid_config_tapes_fit\<close> is the bridge, and
  it is one-way --- the substrate's predicate also pins the state and the
  endmarker column, neither of which a bare carrier has.  Everything about
  \<^emph>\<open>establishing\<close> it therefore stays upstream, in \<open>valid_reach_ktm\<close> and
  \<open>valid_reach_relpow_ktm\<close>; nothing here re-proves it.

  \<open>heads_parked\<close> is the one genuinely missing half.  \<^const>\<open>valid_config_ktm\<close>
  says nothing about head positions, and \<open>proj_embed_update\<close> needs the tapes
  above the count to be blank \<^emph>\<open>and\<close> their heads parked, so this much has to
  be proved here.  \<open>frame_tail\<close> is the two together, in the shape that lemma
  asks for.\<close>

definition ktc_tapes_fit :: "'a set \<Rightarrow> 'a \<Rightarrow> nat \<Rightarrow> ('a, 'q) ktc_config \<Rightarrow> bool"
  where
  "ktc_tapes_fit \<Gamma> bl k C \<longleftrightarrow>
     (\<forall>j m. ktc_tape C j m \<in> \<Gamma>)
     \<and> (\<forall>j m. k \<le> j \<longrightarrow> ktc_tape C j m = bl)"

lemma ktc_tapes_fit_set_state [simp]:
  "ktc_tapes_fit \<Gamma> bl k (ktc_set_state p C) = ktc_tapes_fit \<Gamma> bl k C"
  by (simp add: ktc_tapes_fit_def)

lemma ktc_tapes_fit_context:
  assumes "ktc_tapes_fit \<Gamma> bl k C"
  shows "(\<lambda>j. ktc_tape C j (ktc_pos C j)) \<in> free_context \<Gamma> bl k"
  using assms by (auto simp: ktc_tapes_fit_def free_context_def)

lemma valid_config_tapes_fit:
  assumes "valid_config_ktm M C"
  shows "ktc_tapes_fit (\<Gamma>_ktm M) (bl_ktm M) (k_ktm M) C"
  using assms
  by (cases M; cases C) (auto simp: ktc_tapes_fit_def image_subset_iff)

lemma valid_config_state:
  assumes "valid_config_ktm M C"
  shows "ktc_state C \<in> Q_ktm M"
  using assms by (cases M; cases C) auto

text \<open>The two together, in the shape \<open>proj_embed_update\<close> asks for: beyond
  the machine's own tape count the configuration is blank with a parked head,
  so the window carries no information the projection has to invent.\<close>

lemma frame_tail:
  assumes T: "ktc_tapes_fit \<Gamma> bl k C" and H: "heads_parked k C"
  shows "\<forall>i \<ge> k. ktc_tape C i = (\<lambda>_. bl) \<and> ktc_pos C i = 0"
  using T H by (auto simp: ktc_tapes_fit_def heads_parked_def fun_eq_iff)

text \<open>The forward run, which is what the last three subsections were for: a
  run of the factor is a run of the arm, and the composite configuration moves
  only inside the window.  \<open>embed_step\<close> iterated, with the two things
  iteration needs supplied at each stage.

  \<^bold>\<open>Every hypothesis is the factor's, and that is the whole point.\<close>  The
  induction re-establishes \<open>ctx\<close> at each intermediate composite configuration
  from \<open>embed_update_context\<close>, whose alphabet side is
  \<^term>\<open>\<Gamma>_ktm M \<subseteq> \<Gamma>\<close> and whose blank side is the starting \<open>ctx\<close> untouched;
  and it re-establishes the projection from \<open>proj_embed_update\<close>, whose tail
  hypothesis is \<open>frame_tail\<close> of the factor's own validity.  So the composite
  is never required to be a valid machine --- it is never required to be a
  machine.  \<^const>\<open>valid_config_ktm\<close> appears once, applied to \<open>M\<close>.

  \<open>fit\<close> is the only hypothesis relating the two frames, and it is needed for
  one thing: the window must sit below \<open>k'\<close> so that the blank tail of \<open>ctx\<close>
  is never a claim about the factor.\<close>

lemma embed_run:
  assumes vM: "valid_ktm M"
      and vc: "valid_config_ktm M c"
      and hc: "heads_parked (k_ktm M) c"
      and proj: "proj_config off (k_ktm M) (bl_ktm M) X = c"
      and ctx: "(\<lambda>j. ktc_tape X j (ktc_pos X j))
                  \<in> free_context \<Gamma> (bl_ktm M) k'"
      and gam: "\<Gamma>_ktm M \<subseteq> \<Gamma>"
      and fit: "off + k_ktm M \<le> k'"
      and run: "(c, c') \<in> (ktm_step (delta_ktm M)) ^^ n"
  shows "(X, embed_update off (k_ktm M) X c')
           \<in> (ktm_step
                (embed_delta off (k_ktm M) k' \<Gamma> (bl_ktm M) (delta_ktm M))) ^^ n"
  using run
proof (induction n arbitrary: c')
  case 0
  then have "c' = c" by simp
  moreover have "embed_update off (k_ktm M) X c = X"
    using proj embed_update_proj_config [of off "k_ktm M" X "bl_ktm M"] by simp
  ultimately show ?case by simp
next
  case (Suc n)
  from Suc.prems obtain d
    where cd: "(c, d) \<in> (ktm_step (delta_ktm M)) ^^ n"
      and dc': "(d, c') \<in> ktm_step (delta_ktm M)" by auto
  note IH = Suc.IH [OF cd]
  from valid_reach_relpow_ktm [OF vM vc cd] have vd: "valid_config_ktm M d" .
  from valid_config_tapes_fit [OF vd]
  have Td: "ktc_tapes_fit (\<Gamma>_ktm M) (bl_ktm M) (k_ktm M) d" .
  from proj_embed_update [OF frame_tail [OF Td heads_parked_run [OF vM hc cd]]]
  have pd: "proj_config off (k_ktm M) (bl_ktm M)
              (embed_update off (k_ktm M) X d) = d" .
  have ctxd: "(\<lambda>j. ktc_tape (embed_update off (k_ktm M) X d) j
                     (ktc_pos (embed_update off (k_ktm M) X d) j))
                \<in> free_context \<Gamma> (bl_ktm M) k'"
  proof (rule embed_update_context [OF ctx _ fit])
    fix j p
    show "ktc_tape d j p \<in> \<Gamma>" using Td gam by (auto simp: ktc_tapes_fit_def)
  qed
  from dc' pd
  have "(proj_config off (k_ktm M) (bl_ktm M) (embed_update off (k_ktm M) X d), c')
          \<in> ktm_step (delta_ktm M)" by simp
  from embed_step [OF this ctxd]
  have "(embed_update off (k_ktm M) X d, embed_update off (k_ktm M) X c')
          \<in> ktm_step
               (embed_delta off (k_ktm M) k' \<Gamma> (bl_ktm M) (delta_ktm M))"
    by (simp add: embed_update_embed_update)
  from relpow_Suc_I [OF IH this] show ?case .
qed


subsection \<open>Two machines taking turns\<close>

text \<open>What the previous two subsections were for.  A composite whose
  transition relation is \<open>\<delta>\<^sub>A \<union> \<delta>\<^sub>B\<close>, where every \<open>A\<close>-tuple runs from a state
  whose turn flag is set to one where it is clear and every \<open>B\<close>-tuple does the
  reverse, has runs that alternate strictly --- and a run of \<open>N\<close> steps from an
  \<open>A\<close>-turn state therefore contains \<open>\<lceil>N/2\<rceil>\<close> steps of \<open>A\<close> and \<open>\<lfloor>N/2\<rfloor>\<close> of \<open>B\<close>,
  at the even and odd ticks respectively.

  \<^bold>\<open>Which arm took a step is decided by the state alone, not searched for.\<close>
  That is the entire dividend of the union shape: \<open>ktm_step_Un\<close> turns the
  composite step into a disjunction, and \<open>ktm_step_state_rel\<close> kills whichever
  disjunct disagrees with the turn flag.  Neither is available for a lockstep
  product, where a step is one joint transition that has to be taken apart.

  The conclusion hands back an indexed sequence rather than a pair of runs.
  Induction on the iteration count peels from one end, which is the wrong shape
  for a claim about \<^emph>\<open>positions\<close>; \<open>relpow_fun_conv\<close> converts once and parity is
  ordinary induction on the index.  Extracting the two factor runs from the
  sequence is the composite's job, because only it knows the windows.

  \<^bold>\<open>The asymmetry at odd \<open>N\<close> is the point, not an artefact.\<close>  Starting on
  \<open>A\<close>'s turn, \<open>A\<close> is never behind: after \<open>2m\<close> steps each factor has
  taken \<open>m\<close>, and after \<open>2m + 1\<close> the factor \<open>A\<close> has taken one more.  A
  composite that counts one factor's steps can therefore read off the other's
  exactly.

  \<^bold>\<open>A step may end the run.\<close>  A step into a state with no successors
  --- \<open>final\<close>, which no tuple of either arm leaves --- may land on either turn
  flag, so both arms can share an accepting or rejecting state.  Such a state
  can only be the last of a run, so the alternation is untouched, and parity
  is claimed only at the states that are not final.\<close>

lemma arms_alternate:
  assumes A_turn: "\<forall>q a q' a' d. (q, a, q', a', d) \<in> \<delta>\<^sub>A
                      \<longrightarrow> turn q \<and> \<not> final q \<and> (turn q' \<longrightarrow> final q')"
    and B_turn: "\<forall>q a q' a' d. (q, a, q', a', d) \<in> \<delta>\<^sub>B
                    \<longrightarrow> \<not> turn q \<and> \<not> final q \<and> (\<not> turn q' \<longrightarrow> final q')"
    and run: "(C, C') \<in> ktm_step (\<delta>\<^sub>A \<union> \<delta>\<^sub>B) ^^ N"
    and start: "turn (ktc_state C)"
  obtains f where "f 0 = C" and "f N = C'"
    and "\<And>i. i \<le> N \<Longrightarrow> \<not> final (ktc_state (f i))
               \<Longrightarrow> turn (ktc_state (f i)) = even i"
    and "\<And>i. i < N \<Longrightarrow> even i \<Longrightarrow> (f i, f (Suc i)) \<in> ktm_step \<delta>\<^sub>A"
    and "\<And>i. i < N \<Longrightarrow> odd i \<Longrightarrow> (f i, f (Suc i)) \<in> ktm_step \<delta>\<^sub>B"
proof -
  let ?RA = "\<lambda>q q'. turn q \<and> \<not> final q \<and> (turn q' \<longrightarrow> final q')"
  let ?RB = "\<lambda>q q'. \<not> turn q \<and> \<not> final q \<and> (\<not> turn q' \<longrightarrow> final q')"
  from run obtain f where f0: "f 0 = C" and fN: "f N = C'"
    and fstep: "\<And>i. i < N \<Longrightarrow> (f i, f (Suc i)) \<in> ktm_step (\<delta>\<^sub>A \<union> \<delta>\<^sub>B)"
    by (auto simp: relpow_fun_conv)
  have split: "(f i, f (Suc i)) \<in> ktm_step \<delta>\<^sub>A
                 \<or> (f i, f (Suc i)) \<in> ktm_step \<delta>\<^sub>B"
    if "i < N" for i
    using fstep [OF that] by (simp add: ktm_step_Un)
  \<comment> \<open>every step leaves a state that is not final, whichever arm took it\<close>
  have live: "\<not> final (ktc_state (f i))" if iN: "i < N" for i
  proof -
    from split [OF iN] show ?thesis
    proof
      assume "(f i, f (Suc i)) \<in> ktm_step \<delta>\<^sub>A"
      from ktm_step_state_rel [where R = ?RA, OF this A_turn] show ?thesis by simp
    next
      assume "(f i, f (Suc i)) \<in> ktm_step \<delta>\<^sub>B"
      from ktm_step_state_rel [where R = ?RB, OF this B_turn] show ?thesis by simp
    qed
  qed
  have parity: "i \<le> N \<longrightarrow> \<not> final (ktc_state (f i))
                  \<longrightarrow> turn (ktc_state (f i)) = even i" for i
  proof (induction i)
    case 0
    show ?case using f0 start by simp
  next
    case (Suc i)
    show ?case
    proof (intro impI)
      assume sN: "Suc i \<le> N" and nf: "\<not> final (ktc_state (f (Suc i)))"
      then have iN: "i < N" by simp
      from Suc.IH iN live [OF iN] have ih: "turn (ktc_state (f i)) = even i" by simp
      from split [OF iN] show "turn (ktc_state (f (Suc i))) = even (Suc i)"
      proof
        assume "(f i, f (Suc i)) \<in> ktm_step \<delta>\<^sub>A"
        from ktm_step_state_rel [where R = ?RA, OF this A_turn]
        have "turn (ktc_state (f i))" and "\<not> turn (ktc_state (f (Suc i)))"
          using nf by simp_all
        with ih show ?thesis by simp
      next
        assume "(f i, f (Suc i)) \<in> ktm_step \<delta>\<^sub>B"
        from ktm_step_state_rel [where R = ?RB, OF this B_turn]
        have "turn (ktc_state (f (Suc i)))" and "\<not> turn (ktc_state (f i))"
          using nf by simp_all
        with ih show ?thesis by simp
      qed
    qed
  qed
  have selA: "(f i, f (Suc i)) \<in> ktm_step \<delta>\<^sub>A"
    if iN: "i < N" and ev: "even i" for i
  proof (cases "(f i, f (Suc i)) \<in> ktm_step \<delta>\<^sub>A")
    case True
    then show ?thesis .
  next
    case False
    with split [OF iN] have inB: "(f i, f (Suc i)) \<in> ktm_step \<delta>\<^sub>B" by blast
    from ktm_step_state_rel [where R = ?RB, OF inB B_turn]
    have "\<not> turn (ktc_state (f i))" by simp
    moreover have "turn (ktc_state (f i))" using parity live [OF iN] iN ev by simp
    ultimately show ?thesis by simp
  qed
  have selB: "(f i, f (Suc i)) \<in> ktm_step \<delta>\<^sub>B"
    if iN: "i < N" and od: "odd i" for i
  proof (cases "(f i, f (Suc i)) \<in> ktm_step \<delta>\<^sub>B")
    case True
    then show ?thesis .
  next
    case False
    with split [OF iN] have inA: "(f i, f (Suc i)) \<in> ktm_step \<delta>\<^sub>A" by blast
    from ktm_step_state_rel [where R = ?RA, OF inA A_turn]
    have "turn (ktc_state (f i))" by simp
    moreover have "\<not> turn (ktc_state (f i))" using parity live [OF iN] iN od by simp
    ultimately show ?thesis by simp
  qed
  show thesis
  proof (rule that)
    show "f 0 = C" by (rule f0)
    show "f N = C'" by (rule fN)
    show "\<And>i. i \<le> N \<Longrightarrow> \<not> final (ktc_state (f i))
               \<Longrightarrow> turn (ktc_state (f i)) = even i" using parity by simp
    show "\<And>i. i < N \<Longrightarrow> even i \<Longrightarrow> (f i, f (Suc i)) \<in> ktm_step \<delta>\<^sub>A"
      by (rule selA)
    show "\<And>i. i < N \<Longrightarrow> odd i \<Longrightarrow> (f i, f (Suc i)) \<in> ktm_step \<delta>\<^sub>B"
      by (rule selB)
  qed
qed


end
