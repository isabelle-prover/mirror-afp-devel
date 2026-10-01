theory Multitape_Substrate_Core
  imports "HOL-Library.FuncSet"
begin

section \<open>Substrate core (Dalvit--Thiemann definition surface)\<close>

text \<open>The \<^emph>\<open>definition surface\<close> of the substrate, deliberately isolated
  in this theory: the datatypes, selectors, step relation, and the validity /
  configuration / language definitions --- and no proofs.  This is the part
  of the development that corresponds to the Dalvit--Thiemann AFP entry
  \<open>Multitape_To_Singletape_TM\<close> (its files \<open>Multitape_TM\<close> and
  \<open>TM_Common\<close>, about 180 lines), kept small so a reader can diff it
  directly against that source.  Every lemma --- the \<open>valid_mttm\<close>
  axiom-extraction toolkit, the validity-preservation and reachability
  results, and the displacement / left-endmarker tape tools, all
  \<^emph>\<open>our\<close> additions --- lives in the parent theory \<open>Multitape_Substrate\<close>,
  which imports this one.

  The datatypes (\<open>mttm\<close>, \<open>mt_config\<close>, \<open>dir\<close>) and the step
  relation are adapted from that entry \<^cite>\<open>"Dalvit2022:verified"\<close>;
  \<open>valid_mttm\<close> is a direct conjunction of the substrate's structural
  axioms (no locale wrapping), tightened beyond the AFP entry's
  \<open>\<delta>LE\<close> axiom by an additional LE-write conjunct (see the
  validity predicate below).

  The number of tapes is a \<^emph>\<open>value\<close>: a machine carries its tape count
  as a \<open>nat\<close> field \<open>k\<close>, and head contents are a total function
  \<open>nat \<Rightarrow> 'a\<close> with a \<^emph>\<open>blank tail\<close> beyond \<open>k\<close> (the
  support invariant).  This departs from the AFP source, where the
  tape count is trapped in a finite type parameter \<open>'k\<close>; the value
  form is what makes \<open>\<exists> M\<close> / \<open>\<forall> M\<close> over machines of all
  arities a single HOL proposition.\<close>


subsection \<open>TM-direction primitive (forked from AFP \<open>TM_Common\<close>)\<close>

text \<open>Three-valued TM head movement: right (R), left (L), or
  neutral / stay (N).  Used positionally as the fifth component
  of every transition tuple; functions \<open>nat \<Rightarrow> dir\<close> encode the
  per-tape head movement.\<close>

datatype dir = R | L | N

fun go_dir :: "dir \<Rightarrow> nat \<Rightarrow> nat" where
  "go_dir R n = Suc n"
| "go_dir L n = n - 1"
| "go_dir N n = n"


subsection \<open>Multitape-TM datatypes (forked from AFP \<open>Multitape_TM\<close>)\<close>

text \<open>Multi-tape Turing-machine descriptor.  Ten components: state
  set \<open>Q\<close>, input alphabet \<open>\<Sigma>\<close>, tape alphabet \<open>\<Gamma>\<close>, blank symbol,
  left endmarker, transition relation \<open>\<delta>\<close>, start state, accept
  state, reject state, and tape count \<open>k\<close>.  The shape mirrors the
  AFP source (the \<open>mttm\<close> type abbreviations are a conscious
  near-copy), except the tape count, trapped in the AFP source's
  finite type parameter \<open>'k\<close>, is here the value-level \<open>nat\<close> field
  \<open>k\<close>; transition tuples index the tapes by \<open>nat\<close>, blank beyond \<open>k\<close>.
  Only the \<open>Q_tm\<close> and \<open>\<Gamma>_tm\<close> accessors are record-style — the
  others are positional with custom selectors below.\<close>

datatype ('q, 'a) mttm = MTTM
  (Q_tm: "'q set")        \<comment> \<open>Q — states\<close>
  "'a set"                \<comment> \<open>\<open>\<Sigma>\<close> — input alphabet\<close>
  (\<Gamma>_tm: "'a set")        \<comment> \<open>\<open>\<Gamma>\<close> — tape alphabet\<close>
  'a                      \<comment> \<open>blank\<close>
  'a                      \<comment> \<open>left endmarker\<close>
  "('q \<times> (nat \<Rightarrow> 'a) \<times> 'q \<times> (nat \<Rightarrow> 'a) \<times> (nat \<Rightarrow> dir)) set"
                          \<comment> \<open>transitions \<open>\<delta>\<close>\<close>
  'q                      \<comment> \<open>start state\<close>
  'q                      \<comment> \<open>accept state\<close>
  'q                      \<comment> \<open>reject state\<close>
  nat                     \<comment> \<open>\<open>k\<close> — tape count\<close>

text \<open>Multitape-TM configuration: state, per-tape contents (each a
  function \<open>nat \<Rightarrow> 'a\<close> of cell positions), per-tape head positions.
  Tapes and heads are indexed by \<open>nat\<close>; tapes beyond the machine's
  count \<open>k\<close> are all-blank in a valid configuration.\<close>

datatype ('a, 'q) mt_config = Config\<^sub>M
  (mt_state: 'q)
  "nat \<Rightarrow> nat \<Rightarrow> 'a"
  (mt_pos: "nat \<Rightarrow> nat")


subsection \<open>Substrate selectors\<close>

text \<open>Positional selectors for the @{type mttm} datatype's
  components.  The datatype declares record-style accessors for
  @{const Q_tm} and @{const \<Gamma>_tm} only; the others
  (\<open>\<Sigma>\<close>, \<open>blank\<close>, \<open>LE\<close>, \<open>\<delta>\<close>, \<open>s\<close>, \<open>t\<close>, \<open>r\<close>, \<open>k\<close>) are positional.
  These selectors are simple positional pattern matches, named
  on the \<open>*_tm\<close> convention to match @{const Q_tm} / @{const \<Gamma>_tm}.\<close>

fun bl_tm :: "('q, 'a) mttm \<Rightarrow> 'a" where
  "bl_tm (MTTM _ _ _ bl _ _ _ _ _ _) = bl"

fun le_tm :: "('q, 'a) mttm \<Rightarrow> 'a" where
  "le_tm (MTTM _ _ _ _ le _ _ _ _ _) = le"

fun delta_tm ::
  "('q, 'a) mttm
    \<Rightarrow> ('q \<times> (nat \<Rightarrow> 'a) \<times> 'q \<times> (nat \<Rightarrow> 'a) \<times> (nat \<Rightarrow> dir)) set" where
  "delta_tm (MTTM _ _ _ _ _ \<delta> _ _ _ _) = \<delta>"

fun s_tm :: "('q, 'a) mttm \<Rightarrow> 'q" where
  "s_tm (MTTM _ _ _ _ _ _ s _ _ _) = s"

fun t_tm :: "('q, 'a) mttm \<Rightarrow> 'q" where
  "t_tm (MTTM _ _ _ _ _ _ _ t _ _) = t"

fun r_tm :: "('q, 'a) mttm \<Rightarrow> 'q" where
  "r_tm (MTTM _ _ _ _ _ _ _ _ r _) = r"

fun Sigma_tm :: "('q, 'a) mttm \<Rightarrow> 'a set" where
  "Sigma_tm (MTTM _ \<Sigma> _ _ _ _ _ _ _ _) = \<Sigma>"

fun k_tm :: "('q, 'a) mttm \<Rightarrow> nat" where
  "k_tm (MTTM _ _ _ _ _ _ _ _ _ k) = k"

text \<open>Tape-content selector for substrate configurations.  The
  substrate datatype names @{const mt_state} and @{const mt_pos}
  via record-style accessors but leaves the tape function
  unnamed; we add it positionally for symmetry.\<close>

fun mt_tape :: "('a, 'q) mt_config \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a" where
  "mt_tape (Config\<^sub>M _ ts _) = ts"


subsection \<open>Step relation\<close>

text \<open>Inductive characterisation of the multitape-TM step
  relation, parametrised by the transition relation \<open>\<delta>\<close> alone.
  Body verbatim equivalent to the AFP source (only the tape index
  moves from the type \<open>'k\<close> to \<open>nat\<close>); functional layer, so
  downstream Hoare-triple proofs invoke
  \<open>mttm_step.intros\<close> directly without any locale routing.\<close>

inductive_set mttm_step ::
  "('q \<times> (nat \<Rightarrow> 'a) \<times> 'q \<times> (nat \<Rightarrow> 'a) \<times> (nat \<Rightarrow> dir)) set
    \<Rightarrow> ('a, 'q) mt_config rel"
  for \<delta>
where
  step: "(q, (\<lambda>k. ts k (n k)), q', a, dir) \<in> \<delta> \<Longrightarrow>
   (Config\<^sub>M q ts n,
    Config\<^sub>M q' (\<lambda>k. (ts k)(n k := a k)) (\<lambda>k. go_dir (dir k) (n k)))
     \<in> mttm_step \<delta>"


subsection \<open>Substrate validity (functional axiom bundle)\<close>

text \<open>Functional bundle of the substrate's structural axioms.  This
  predicate enumerates the standard well-formedness conditions of
  Hopcroft and Ullman \<^cite>\<open>\<open>\S7.3\<close> in "Hopcroft1979:introduction"\<close>:
  finiteness of @{term Q} and @{term \<Gamma>}, alphabet inclusion, state
  membership for the start, accept, and reject states, blank /
  left-endmarker tape-alphabet membership (with @{term \<Sigma>}
  disjointness), accept @{text "\<noteq>"} reject, a positive tape count
  (the input tape \<open>0\<close> must exist), the range typing of the
  transition relation, the LE read-discipline, and the
  \<^emph>\<open>support invariant\<close>.

  The LE-discipline kept here is the read direction only: every
  \<open>\<delta>\<close>-transition reading the left endmarker on tape \<open>j\<close> rewrites the
  LE position with itself and moves only \<open>N\<close> or \<open>R\<close> (boundary
  preservation).  The converse write direction — a transition writes
  the left endmarker on tape \<open>j\<close> only where it was already reading
  it — is \<^emph>\<open>not\<close> a validity requirement: it is factored out as the
  separate predicate \<open>le_unique\<close> (below), which well-formed machines
  carry but a machine that deliberately plants a fresh \<open>le\<close> — the
  origin-floating wrapper for the faithful Hopcroft--Ullman speed-up bound
  \<^cite>\<open>\<open>Theorem 12.4\<close> in "Hopcroft1979:introduction"\<close> — may forgo
  while staying valid.  Keeping the write direction out of validity is
  exactly what lets that wrapper's output be a legal machine.

  The support invariant — every transition is blank on reads and
  writes and stationary (\<open>N\<close>) on moves at every tape index \<open>j \<ge> k\<close>
  — is the value-level replacement for the AFP source's finite tape
  type: it confines a \<open>k\<close>-tape machine's transitions to tapes
  \<open>0 \<dots> k - 1\<close> and, with @{term \<Gamma>} finite, makes \<open>\<delta>\<close> finite
  (@{text "valid_mttm_finite_delta"}).\<close>

fun valid_mttm :: "('q, 'a) mttm \<Rightarrow> bool" where
  "valid_mttm (MTTM Q \<Sigma> \<Gamma> bl le \<delta> s t r k) =
     (finite Q \<and>
      finite \<Gamma> \<and>
      \<Sigma> \<subseteq> \<Gamma> \<and>
      s \<in> Q \<and>
      t \<in> Q \<and>
      r \<in> Q \<and>
      bl \<in> \<Gamma> \<and>
      bl \<notin> \<Sigma> \<and>
      le \<in> \<Gamma> \<and>
      le \<notin> \<Sigma> \<and>
      t \<noteq> r \<and>
      0 < k \<and>
      \<delta> \<subseteq> (Q - {t, r}) \<times> (UNIV \<rightarrow> \<Gamma>) \<times> Q \<times> (UNIV \<rightarrow> \<Gamma>) \<times> (UNIV \<rightarrow> UNIV) \<and>
      (\<forall>q a q' a' d j. (q, a, q', a', d) \<in> \<delta> \<longrightarrow> a j = le \<longrightarrow>
                         a' j = le \<and> d j \<in> {dir.N, dir.R}) \<and>
      (\<forall>q a q' a' d. (q, a, q', a', d) \<in> \<delta> \<longrightarrow>
                       (\<forall>j \<ge> k. a j = bl \<and> a' j = bl \<and> d j = dir.N)))"

text \<open>The left-endmarker write discipline, as a standalone predicate:
  a transition writes the left endmarker @{term "le_tm M"} on a tape
  only where it was already reading it — the endmarker is never freshly
  planted.  This was formerly a clause of @{const valid_mttm}; it is
  kept separate precisely so a machine that *does* plant a fresh \<open>le\<close> —
  the origin-floating wrapper for the faithful Theorem 12.4 bound — is still
  @{const valid_mttm}, while the alphabet-transformation chain, which
  needs the property of the machine it simulates, carries it explicitly
  (folded into \<open>well_formed_mttm\<close> and threaded to the simulation
  lemmas through \<open>valid_mttm_deltaLE_no_write\<close>).\<close>

definition le_unique :: "('q, 'a) mttm \<Rightarrow> bool" where
  "le_unique M =
     (\<forall>q a q' a' d j. (q, a, q', a', d) \<in> delta_tm M \<longrightarrow>
                        a' j = le_tm M \<longrightarrow> a j = le_tm M)"

text \<open>Strengthening of @{const valid_mttm} with the three
  non-degeneracy conditions used by every linear-speedup-style
  theorem — distinct start / accept / reject states and distinct
  left-endmarker / blank tape symbols — plus the left-endmarker
  write discipline @{const le_unique}.  Bundles
  @{term "valid_mttm M"}, @{term "s_tm M \<noteq> t_tm M"},
  @{term "s_tm M \<noteq> r_tm M"}, @{term "le_tm M \<noteq> bl_tm M"}, and
  @{term "le_unique M"} into a single predicate so downstream
  statements need only one assumption clause instead of five.  Since
  @{const le_unique} is no longer implied by @{const valid_mttm} — it is
  exactly the clause the faithful-12.4 wrapper forgoes — it is
  load-bearing here: \<open>well_formed_mttm\<close> is the
  alphabet-transformation chain's carrier of LE-uniqueness, threaded to
  the simulation lemmas that need it.\<close>

abbreviation well_formed_mttm
  :: "('q, 'a) mttm \<Rightarrow> bool"
where
  "well_formed_mttm M \<equiv>
     valid_mttm M
     \<and> s_tm M \<noteq> t_tm M
     \<and> s_tm M \<noteq> r_tm M
     \<and> le_tm M \<noteq> bl_tm M
     \<and> le_unique M"


subsection \<open>Configuration validity\<close>

text \<open>Functional re-exposition of the substrate's per-configuration
  validity invariant: state in @{term Q}, every tape's contents
  drawn from @{term \<Gamma>}, every \<^emph>\<open>active\<close> tape (index \<open>i < k\<close>)
  carries the left endmarker at position 0, and every \<^emph>\<open>inactive\<close>
  tape (index \<open>i \<ge> k\<close>) is all-blank (the configuration-level support
  invariant — inactive tapes carry the blank symbol everywhere, not
  the left endmarker, since \<open>bl \<noteq> le\<close>).\<close>

fun valid_config_mttm ::
  "('q, 'a) mttm \<Rightarrow> ('a, 'q) mt_config \<Rightarrow> bool"
where
  "valid_config_mttm (MTTM Q _ \<Gamma> bl le _ _ _ _ k) (Config\<^sub>M q ts _) =
     (q \<in> Q
      \<and> (\<forall>i. range (ts i) \<subseteq> \<Gamma>)
      \<and> (\<forall>i<k. ts i 0 = le)
      \<and> (\<forall>i\<ge>k. \<forall>p. ts i p = bl))"

text \<open>Functional initial configuration: take \<open>M\<close> as parameter,
  pull start state, blank, left endmarker, and tape count
  positionally.  Active tapes (index \<open>i < k\<close>) carry the left
  endmarker at position 0 and, on the input tape \<open>0\<close>, the input
  \<open>w\<close>; inactive tapes (index \<open>i \<ge> k\<close>) are all-blank.\<close>

fun init_config_mttm ::
  "('q, 'a) mttm \<Rightarrow> 'a list \<Rightarrow> ('a, 'q) mt_config"
where
  "init_config_mttm (MTTM _ _ _ bl le _ s _ _ k) w =
     Config\<^sub>M s
       (\<lambda>i n. if i < k
              then (if n = 0 then le
                    else if i = 0 \<and> n \<le> length w then w ! (n - 1)
                    else bl)
              else bl)
       (\<lambda>_. 0)"


subsection \<open>Language and time-bound predicates\<close>

text \<open>Functional analogues of the AFP's @{text "Lang_mttm"}
  and @{text "det_mttm"} top-level wrappers, plus the
  weak-acceptance predicate @{text "accepts_in_time_mttm"}.
  @{text "Lang_mttm"} is the set of inputs over @{term "Sigma_tm M"}
  that drive @{term M} from its initial configuration to the accept
  state @{term "t_tm M"}.  @{text "det_mttm"} says the transition
  relation is single-valued: each source state together with the
  symbols read admits at most one outcome — one next state, one
  written-symbol tuple, one head-move tuple — so a configuration has
  at most one successor.  This is the determinism hypothesis on
  which the alphabet-enlargement reverse direction turns.  Bodies
  routed through the functional @{const init_config_mttm} and
  @{const mttm_step} rather than through locale-internal
  definitions.  Used by the AE / AR language- and time-preservation
  theorems.\<close>

definition Lang_mttm :: "('q, 'a) mttm \<Rightarrow> 'a list set" where
  "Lang_mttm M =
     {w. set w \<subseteq> Sigma_tm M \<and>
         (\<exists>w' n. (init_config_mttm M w, Config\<^sub>M (t_tm M) w' n)
                    \<in> (mttm_step (delta_tm M))\<^sup>*)}"

definition det_mttm :: "('q, 'a) mttm \<Rightarrow> bool" where
  "det_mttm M =
     (\<forall>q a p\<^sub>1 b\<^sub>1 d\<^sub>1 p\<^sub>2 b\<^sub>2 d\<^sub>2.
        (q, a, p\<^sub>1, b\<^sub>1, d\<^sub>1) \<in> delta_tm M \<longrightarrow>
        (q, a, p\<^sub>2, b\<^sub>2, d\<^sub>2) \<in> delta_tm M \<longrightarrow>
        (p\<^sub>1, b\<^sub>1, d\<^sub>1) = (p\<^sub>2, b\<^sub>2, d\<^sub>2))"

text \<open>Weak time-bounded acceptance: M accepts input @{term w} in
  time at most @{term t} iff some accepting path of length @{term
  "n \<le> t"} exists from @{const init_config_mttm} to a config in
  state @{term "t_tm M"}.  This matches the existential
  accepting-path shape that the alphabet-enlargement top-level
  theorems preserve.  Non-accepting paths are not constrained,
  in contrast to a universal worst-case bound that would
  constrain every path regardless of acceptance.

  Used by @{text "alphabet_enlarge_language"} and
  @{text "alphabet_enlarge_time"}.\<close>

definition accepts_in_time_mttm ::
  "('q, 'a) mttm \<Rightarrow> 'a list \<Rightarrow> nat \<Rightarrow> bool" where
  "accepts_in_time_mttm M w t =
     (\<exists>n cM_n. n \<le> t
                \<and> (init_config_mttm M w, cM_n) \<in> (mttm_step (delta_tm M))^^n
                \<and> mt_state cM_n = t_tm M)"

end
