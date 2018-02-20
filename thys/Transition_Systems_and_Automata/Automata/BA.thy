section {* Büchi Automata *}

theory BA
imports
  "../Basic/Sequence_Zip"
  "../Transition_Systems/Transition_System"
  "../Transition_Systems/Transition_System_Extra"
  "../Transition_Systems/Transition_System_Construction"
begin

  record ('label, 'state) ba =
    alphabet :: "'label set"
    initial :: "'state set"
    succ :: "'label \<Rightarrow> 'state \<Rightarrow> 'state set"
    accepting :: "'state \<Rightarrow> bool"

  global_interpretation ba: transition_system_initial
    "\<lambda> a p. snd a" "\<lambda> a p. fst a \<in> alphabet A \<and> snd a \<in> succ A (fst a) p" "\<lambda> p. p \<in> initial A"
    for A
    defines path = ba.path and run = ba.run and reachable = ba.reachable and nodes = ba.nodes and
      enableds = ba.enableds and paths = ba.paths and runs = ba.runs
    by this

  abbreviation "target \<equiv> ba.target"
  abbreviation "states \<equiv> ba.states"
  abbreviation "trace \<equiv> ba.trace"

  lemma states_alt_def: "states r p = map snd r" by (induct r arbitrary: p) (auto)
  lemma trace_alt_def: "trace r p = smap snd r" by (coinduction arbitrary: r p) (auto)

  abbreviation successors :: "('label, 'state, 'more) ba_scheme \<Rightarrow> 'state \<Rightarrow> 'state set" where
    "successors \<equiv> ba.successors TYPE('label) TYPE('more)"

  lemma successors_alt_def: "successors A p = (\<Union> a \<in> alphabet A. succ A a p)" by auto

  abbreviation "pred A a q \<equiv> {p. q \<in> succ A a p}"

  lemma reachable_succ[intro]:
    assumes "a \<in> alphabet A" "q \<in> reachable A p" "r \<in> succ A a q"
    shows "r \<in> reachable A p"
    using ba.reachable.execute assms by force
  lemma nodes_succ[intro]:
    assumes "a \<in> alphabet A" "p \<in> nodes A" "q \<in> succ A a p"
    shows "q \<in> nodes A"
    using ba.nodes.execute assms by force

  definition language :: "('label, 'state, 'more) ba_scheme \<Rightarrow> 'label stream set" where
    "language A \<equiv> {w |w r p. p \<in> initial A \<and> run A (w ||| r) p \<and> infs (accepting A) (trace (w ||| r) p)}"

  lemma language[intro]:
    assumes "p \<in> initial A" "run A (w ||| r) p" "infs (accepting A) (trace (w ||| r) p)"
    shows "w \<in> language A"
    using assms unfolding language_def by auto
  lemma language_elim[elim]:
    assumes "w \<in> language A"
    obtains r p
    where "p \<in> initial A" "run A (w ||| r) p" "infs (accepting A) (trace (w ||| r) p)"
    using assms unfolding language_def by auto

  lemma run_alphabet:
    assumes "run A (w ||| r) p"
    shows "w \<in> streams (alphabet A)"
    using assms by (coinduction arbitrary: w r p) (metis ba.run.cases stream.map szip_smap szip_smap_fst)
  lemma language_alphabet: "language A \<subseteq> streams (alphabet A)"
    unfolding language_def by (auto dest: run_alphabet)

end