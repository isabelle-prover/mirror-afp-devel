section {* Büchi Automata *}

theory BA
imports
  "../Basic/Sequence_Zip"
  "../Transition_Systems/Transition_System"
  "../Transition_Systems/Transition_System_Extra"
  "../Transition_Systems/Transition_System_Construction"
begin

  record ('label, 'state) ba =
    succ :: "'label \<Rightarrow> 'state \<Rightarrow> 'state set"
    initial :: "'state set"
    accepting :: "'state \<Rightarrow> bool"

  global_interpretation ba: transition_system_initial
    "\<lambda> (a, q) p. q" "\<lambda> (a, q) p. q \<in> succ A a p" "\<lambda> p. p \<in> initial A"
    for A
    defines path = ba.path and run = ba.run and reachable = ba.reachable and nodes = ba.nodes
    by this

  abbreviation "target \<equiv> ba.target"
  abbreviation "states \<equiv> ba.states"
  abbreviation "trace \<equiv> ba.trace"

  abbreviation successors :: "('label, 'state, 'more) ba_scheme \<Rightarrow> 'state \<Rightarrow> 'state set" where
    "successors \<equiv> ba.successors TYPE('label) TYPE('more)"

  lemma states_alt_def: "states r p = map snd r" by (induct r arbitrary: p) (auto)
  lemma trace_alt_def: "trace r p = smap snd r" by (coinduction arbitrary: r p) (auto split: prod.splits)

  abbreviation "pred A a q \<equiv> {p. q \<in> succ A a p}"

  definition language :: "('label, 'state) ba \<Rightarrow> 'label stream set" where
    "language A \<equiv> {smap fst r |r p. run A r p \<and> p \<in> initial A \<and> infs (accepting A) (trace r p)}"

  lemma language[intro]:
    assumes "run A (w ||| r) p" "p \<in> initial A" "infs (accepting A) (trace (w ||| r) p)"
    shows "w \<in> language A"
    using assms unfolding language_def by (auto iff: split_szip_ex)
  lemma language_elim[elim]:
    assumes "w \<in> language A"
    obtains r p
    where "run A (w ||| r) p" "p \<in> initial A" "infs (accepting A) (trace (w ||| r) p)"
    using assms unfolding language_def by (auto iff: split_szip_ex)

end
