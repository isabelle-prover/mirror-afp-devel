theory Multitape_Substrate_Core
  imports "HOL-Library.FuncSet"
begin

section \<open>Machines, configurations and runs (after Dalvit and Thiemann)\<close>

text \<open>The \<^emph>\<open>definition surface\<close> of the substrate, deliberately isolated
  in this theory: the datatypes, selectors, step relation, and the validity /
  configuration / language definitions --- and no proofs.  This is the part
  of the development that corresponds to the Dalvit--Thiemann AFP entry
  \<open>Multitape_To_Singletape_TM\<close> (its files \<open>Multitape_TM\<close> and
  \<open>TM_Common\<close>, about 180 lines), kept small so a reader can diff it
  directly against that source.  Every lemma --- the \<open>valid_ktm\<close>
  axiom-extraction toolkit, the validity-preservation and reachability
  results, and the displacement / left-endmarker tape tools, all
  \<^emph>\<open>our\<close> additions --- lives in the parent theory \<open>Multitape_Substrate\<close>,
  which imports this one.

  The datatypes (\<open>ktm\<close>, \<open>ktc_config\<close>, \<open>move\<close>) and the step
  relation are adapted from that entry \<^cite>\<open>"Dalvit2022:verified"\<close>;
  \<open>valid_ktm\<close> is a direct conjunction of the substrate's structural
  axioms (no locale wrapping), tightened beyond the AFP entry's
  \<open>\<delta>LE\<close> axiom by an additional LE-write conjunct (see the
  validity predicate below).

  The names are not the source's: its \<open>mttm\<close>, \<open>mt_config\<close>, \<open>dir\<close>,
  the selectors \<open>Q_tm\<close>, \<open>\<Gamma>_tm\<close> and the predicates \<open>valid_mttm\<close>,
  \<open>Lang_mttm\<close>, \<open>det_mttm\<close> are \<open>ktm\<close> (a \<open>k\<close>-tape machine),
  \<open>ktc_config\<close>, \<open>move\<close>, \<open>Q_ktm\<close>, \<open>\<Gamma>_ktm\<close>, \<open>valid_ktm\<close>, \<open>Lang_ktm\<close> and
  \<open>det_ktm\<close> here, so that a theory can import both developments.

  The number of tapes is a \<^emph>\<open>value\<close>: a machine carries its tape count
  as a \<open>nat\<close> field \<open>k\<close>, and head contents are a total function
  \<open>nat \<Rightarrow> 'a\<close> with a \<^emph>\<open>blank tail\<close> beyond \<open>k\<close> (the
  support invariant).  This departs from the AFP source, where the
  tape count is trapped in a finite type parameter \<open>'k\<close>; the value
  form is what makes \<open>\<exists> M\<close> / \<open>\<forall> M\<close> over machines of all
  arities a single HOL proposition.\<close>


subsection \<open>Head movements (adapted from \<open>TM_Common\<close>)\<close>

text \<open>Three-valued TM head movement: right (\<open>MoveR\<close>), left (\<open>MoveL\<close>), or
  neutral / stay (\<open>MoveN\<close>).  Used positionally as the fifth component
  of every transition tuple; functions \<open>nat \<Rightarrow> move\<close> encode the
  per-tape head movement.  The source's type \<open>dir\<close> has constructors
  \<open>R\<close>, \<open>L\<close> and \<open>N\<close>; the names here differ so that both can be imported
  together.\<close>

datatype move = MoveR | MoveL | MoveN

fun go_move :: "move \<Rightarrow> nat \<Rightarrow> nat" where
  "go_move MoveR n = Suc n"
| "go_move MoveL n = n - 1"
| "go_move MoveN n = n"


subsection \<open>Machines and configurations (adapted from \<open>Multitape_TM\<close>)\<close>

text \<open>Multi-tape Turing-machine descriptor.  Ten components: state
  set \<open>Q\<close>, input alphabet \<open>\<Sigma>\<close>, tape alphabet \<open>\<Gamma>\<close>, blank symbol,
  left endmarker, transition relation \<open>\<delta>\<close>, start state, accept
  state, reject state, and tape count \<open>k\<close>.  The shape mirrors the
  AFP source (the \<open>ktm\<close> type abbreviations are a conscious
  near-copy), except the tape count, trapped in the AFP source's
  finite type parameter \<open>'k\<close>, is here the value-level \<open>nat\<close> field
  \<open>k\<close>; transition tuples index the tapes by \<open>nat\<close>, blank beyond \<open>k\<close>.
  Only the \<open>Q_ktm\<close> and \<open>\<Gamma>_ktm\<close> accessors are record-style — the
  others are positional with custom selectors below.\<close>

datatype ('q, 'a) ktm = KTM
  (Q_ktm: "'q set")        \<comment> \<open>Q — states\<close>
  "'a set"                \<comment> \<open>\<open>\<Sigma>\<close> — input alphabet\<close>
  (\<Gamma>_ktm: "'a set")        \<comment> \<open>\<open>\<Gamma>\<close> — tape alphabet\<close>
  'a                      \<comment> \<open>blank\<close>
  'a                      \<comment> \<open>left endmarker\<close>
  "('q \<times> (nat \<Rightarrow> 'a) \<times> 'q \<times> (nat \<Rightarrow> 'a) \<times> (nat \<Rightarrow> move)) set"
                          \<comment> \<open>transitions \<open>\<delta>\<close>\<close>
  'q                      \<comment> \<open>start state\<close>
  'q                      \<comment> \<open>accept state\<close>
  'q                      \<comment> \<open>reject state\<close>
  nat                     \<comment> \<open>\<open>k\<close> — tape count\<close>

text \<open>Multitape-TM configuration: state, per-tape contents (each a
  function \<open>nat \<Rightarrow> 'a\<close> of cell positions), per-tape head positions.
  Tapes and heads are indexed by \<open>nat\<close>; tapes beyond the machine's
  count \<open>k\<close> are all-blank in a valid configuration.\<close>

datatype ('a, 'q) ktc_config = KConfig
  (ktc_state: 'q)
  (ktc_tape: "nat \<Rightarrow> nat \<Rightarrow> 'a")
  (ktc_pos: "nat \<Rightarrow> nat")


subsection \<open>Component selectors\<close>

text \<open>Positional selectors for the @{type ktm} datatype's
  components.  The datatype declares record-style accessors for
  @{const Q_ktm} and @{const \<Gamma>_ktm} only; the others
  (\<open>\<Sigma>\<close>, \<open>blank\<close>, \<open>LE\<close>, \<open>\<delta>\<close>, \<open>s\<close>, \<open>t\<close>, \<open>r\<close>, \<open>k\<close>) are positional.
  These selectors are simple positional pattern matches, named
  on the \<open>*_ktm\<close> convention to match @{const Q_ktm} / @{const \<Gamma>_ktm}.\<close>

fun bl_ktm :: "('q, 'a) ktm \<Rightarrow> 'a" where
  "bl_ktm (KTM _ _ _ bl _ _ _ _ _ _) = bl"

fun le_ktm :: "('q, 'a) ktm \<Rightarrow> 'a" where
  "le_ktm (KTM _ _ _ _ le _ _ _ _ _) = le"

fun delta_ktm ::
  "('q, 'a) ktm
    \<Rightarrow> ('q \<times> (nat \<Rightarrow> 'a) \<times> 'q \<times> (nat \<Rightarrow> 'a) \<times> (nat \<Rightarrow> move)) set" where
  "delta_ktm (KTM _ _ _ _ _ \<delta> _ _ _ _) = \<delta>"

fun s_ktm :: "('q, 'a) ktm \<Rightarrow> 'q" where
  "s_ktm (KTM _ _ _ _ _ _ s _ _ _) = s"

fun t_ktm :: "('q, 'a) ktm \<Rightarrow> 'q" where
  "t_ktm (KTM _ _ _ _ _ _ _ t _ _) = t"

fun r_ktm :: "('q, 'a) ktm \<Rightarrow> 'q" where
  "r_ktm (KTM _ _ _ _ _ _ _ _ r _) = r"

fun Sigma_ktm :: "('q, 'a) ktm \<Rightarrow> 'a set" where
  "Sigma_ktm (KTM _ \<Sigma> _ _ _ _ _ _ _ _) = \<Sigma>"

fun k_ktm :: "('q, 'a) ktm \<Rightarrow> nat" where
  "k_ktm (KTM _ _ _ _ _ _ _ _ _ k) = k"


subsection \<open>Step relation\<close>

text \<open>Inductive characterisation of the multitape-TM step
  relation, parametrised by the transition relation \<open>\<delta>\<close> alone.
  Body verbatim equivalent to the AFP source (only the tape index
  moves from the type \<open>'k\<close> to \<open>nat\<close>); functional layer, so
  downstream Hoare-triple proofs invoke
  \<open>ktm_step.intros\<close> directly without any locale routing.\<close>

inductive_set ktm_step ::
  "('q \<times> (nat \<Rightarrow> 'a) \<times> 'q \<times> (nat \<Rightarrow> 'a) \<times> (nat \<Rightarrow> move)) set
    \<Rightarrow> ('a, 'q) ktc_config rel"
  for \<delta>
where
  step: "(q, (\<lambda>k. ts k (n k)), q', a, move) \<in> \<delta> \<Longrightarrow>
   (KConfig q ts n,
    KConfig q' (\<lambda>k. (ts k)(n k := a k)) (\<lambda>k. go_move (move k) (n k)))
     \<in> ktm_step \<delta>"


subsection \<open>Machine validity\<close>

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
  carry but a machine that deliberately writes a fresh \<open>le\<close> may forgo
  while staying valid.  The machine for the Hopcroft--Ullman speed-up
  bound \<^cite>\<open>\<open>Theorem 12.4\<close> in "Hopcroft1979:introduction"\<close> in the
  alphabet-enlargement entry is one: it writes a fresh \<open>le\<close> past the
  input it has consumed instead of rewinding over it, and keeping the
  write direction out of validity is what makes it a legal machine.

  The support invariant — every transition is blank on reads and
  writes and stationary (\<open>N\<close>) on moves at every tape index \<open>j \<ge> k\<close>
  — is the value-level replacement for the AFP source's finite tape
  type: it confines a \<open>k\<close>-tape machine's transitions to tapes
  \<open>0 \<dots> k - 1\<close> and, with @{term \<Gamma>} finite, makes \<open>\<delta>\<close> finite
  (@{text "valid_ktm_finite_delta"}).\<close>

fun valid_ktm :: "('q, 'a) ktm \<Rightarrow> bool" where
  "valid_ktm (KTM Q \<Sigma> \<Gamma> bl le \<delta> s t r k) =
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
                         a' j = le \<and> d j \<in> {MoveN, MoveR}) \<and>
      (\<forall>q a q' a' d. (q, a, q', a', d) \<in> \<delta> \<longrightarrow>
                       (\<forall>j \<ge> k. a j = bl \<and> a' j = bl \<and> d j = MoveN)))"

text \<open>The left-endmarker write discipline, as a standalone predicate:
  a transition writes the left endmarker @{term "le_ktm M"} on a tape
  only where it was already reading it — the endmarker is never freshly
  planted.  It is kept out of @{const valid_ktm} so that a machine that
  \<^emph>\<open>does\<close> write a fresh \<open>le\<close>, such as the Theorem 12.4 speed-up machine,
  is still @{const valid_ktm}, while the alphabet transformations, which
  need the property of the machine they simulate, carry it explicitly
  (folded into \<open>well_formed_ktm\<close> and threaded to the simulation
  lemmas through \<open>valid_ktm_deltaLE_no_write\<close>).\<close>

definition le_unique :: "('q, 'a) ktm \<Rightarrow> bool" where
  "le_unique M =
     (\<forall>q a q' a' d j. (q, a, q', a', d) \<in> delta_ktm M \<longrightarrow>
                        a' j = le_ktm M \<longrightarrow> a j = le_ktm M)"

text \<open>Strengthening of @{const valid_ktm} with the three
  non-degeneracy conditions used by every linear-speedup-style
  theorem — distinct start / accept / reject states and distinct
  left-endmarker / blank tape symbols — plus the left-endmarker
  write discipline @{const le_unique}.  Bundles
  @{term "valid_ktm M"}, @{term "s_ktm M \<noteq> t_ktm M"},
  @{term "s_ktm M \<noteq> r_ktm M"}, @{term "le_ktm M \<noteq> bl_ktm M"}, and
  @{term "le_unique M"} into a single predicate so downstream
  statements need only one assumption clause instead of five.  Since
  @{const valid_ktm} does not imply @{const le_unique}, this is where
  the alphabet transformations get it from: \<open>well_formed_ktm\<close> is
  the hypothesis through which they learn that the machine they
  simulate never writes a fresh \<open>le\<close>.\<close>

abbreviation well_formed_ktm
  :: "('q, 'a) ktm \<Rightarrow> bool"
where
  "well_formed_ktm M \<equiv>
     valid_ktm M
     \<and> s_ktm M \<noteq> t_ktm M
     \<and> s_ktm M \<noteq> r_ktm M
     \<and> le_ktm M \<noteq> bl_ktm M
     \<and> le_unique M"


subsection \<open>Configuration validity\<close>

text \<open>Functional re-exposition of the substrate's per-configuration
  validity invariant: state in @{term Q}, every tape's contents
  drawn from @{term \<Gamma>}, every \<^emph>\<open>active\<close> tape (index \<open>i < k\<close>)
  carries the left endmarker at position 0, and every \<^emph>\<open>inactive\<close>
  tape (index \<open>i \<ge> k\<close>) is all-blank (the configuration-level support
  invariant — inactive tapes carry the blank symbol everywhere, not
  the left endmarker, since \<open>bl \<noteq> le\<close>).\<close>

fun valid_config_ktm ::
  "('q, 'a) ktm \<Rightarrow> ('a, 'q) ktc_config \<Rightarrow> bool"
where
  "valid_config_ktm (KTM Q _ \<Gamma> bl le _ _ _ _ k) (KConfig q ts _) =
     (q \<in> Q
      \<and> (\<forall>i. range (ts i) \<subseteq> \<Gamma>)
      \<and> (\<forall>i<k. ts i 0 = le)
      \<and> (\<forall>i\<ge>k. \<forall>p. ts i p = bl))"

text \<open>Functional initial configuration: take \<open>M\<close> as parameter,
  pull start state, blank, left endmarker, and tape count
  positionally.  Active tapes (index \<open>i < k\<close>) carry the left
  endmarker at position 0 and, on the input tape \<open>0\<close>, the input
  \<open>w\<close>; inactive tapes (index \<open>i \<ge> k\<close>) are all-blank.\<close>

fun init_config_ktm ::
  "('q, 'a) ktm \<Rightarrow> 'a list \<Rightarrow> ('a, 'q) ktc_config"
where
  "init_config_ktm (KTM _ _ _ bl le _ s _ _ k) w =
     KConfig s
       (\<lambda>i n. if i < k
              then (if n = 0 then le
                    else if i = 0 \<and> n \<le> length w then w ! (n - 1)
                    else bl)
              else bl)
       (\<lambda>_. 0)"


subsection \<open>Language and time-bound predicates\<close>

text \<open>Functional analogues of the AFP's @{text "Lang_ktm"}
  and @{text "det_ktm"} top-level wrappers, plus the
  weak-acceptance predicate @{text "accepts_in_time_ktm"}.
  @{text "Lang_ktm"} is the set of inputs over @{term "Sigma_ktm M"}
  that drive @{term M} from its initial configuration to the accept
  state @{term "t_ktm M"}.  @{text "det_ktm"} says the transition
  relation is single-valued: each source state together with the
  symbols read admits at most one outcome — one next state, one
  written-symbol tuple, one head-move tuple — so a configuration has
  at most one successor.  This is the determinism hypothesis on
  which the alphabet-enlargement reverse direction turns.  Bodies
  routed through the functional @{const init_config_ktm} and
  @{const ktm_step} rather than through locale-internal
  definitions.  Used by the AE / AR language- and time-preservation
  theorems.\<close>

definition Lang_ktm :: "('q, 'a) ktm \<Rightarrow> 'a list set" where
  "Lang_ktm M =
     {w. set w \<subseteq> Sigma_ktm M \<and>
         (\<exists>w' n. (init_config_ktm M w, KConfig (t_ktm M) w' n)
                    \<in> (ktm_step (delta_ktm M))\<^sup>*)}"

definition det_ktm :: "('q, 'a) ktm \<Rightarrow> bool" where
  "det_ktm M =
     (\<forall>q a p\<^sub>1 b\<^sub>1 d\<^sub>1 p\<^sub>2 b\<^sub>2 d\<^sub>2.
        (q, a, p\<^sub>1, b\<^sub>1, d\<^sub>1) \<in> delta_ktm M \<longrightarrow>
        (q, a, p\<^sub>2, b\<^sub>2, d\<^sub>2) \<in> delta_ktm M \<longrightarrow>
        (p\<^sub>1, b\<^sub>1, d\<^sub>1) = (p\<^sub>2, b\<^sub>2, d\<^sub>2))"

text \<open>Weak time-bounded acceptance: M accepts input @{term w} in
  time at most @{term t} iff some accepting path of length @{term
  "n \<le> t"} exists from @{const init_config_ktm} to a config in
  state @{term "t_ktm M"}.  This matches the existential
  accepting-path shape that the alphabet-enlargement top-level
  theorems preserve.  Non-accepting paths are not constrained,
  in contrast to a universal worst-case bound that would
  constrain every path regardless of acceptance.

  Used by @{text "alphabet_enlarge_language"} and
  @{text "alphabet_enlarge_time"}.\<close>

definition accepts_in_time_ktm ::
  "('q, 'a) ktm \<Rightarrow> 'a list \<Rightarrow> nat \<Rightarrow> bool" where
  "accepts_in_time_ktm M w t =
     (\<exists>n cM_n. n \<le> t
                \<and> (init_config_ktm M w, cM_n) \<in> (ktm_step (delta_ktm M))^^n
                \<and> ktc_state cM_n = t_ktm M)"

end
