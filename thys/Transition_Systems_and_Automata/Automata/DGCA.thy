section {* Deterministic Co-Generalized Co-Büchi Automata *}

theory DGCA
imports
  "DCA"
  "../Transition_Systems/Transition_System_Degeneralization"
begin

  datatype ('label, 'state) dgca = dgca
    (alphabet: "'label set")
    (initial: "'state")
    (succ: "'label \<Rightarrow> 'state \<Rightarrow> 'state")
    (rejecting: "'state pred gen")

  global_interpretation dgca: transition_system_initial_generalized
    "succ A" "\<lambda> a p. a \<in> alphabet A" "\<lambda> p. p = initial A" "rejecting A"
    for A
    defines path = dgca.path and run = dgca.run and reachable = dgca.reachable and nodes = dgca.nodes and
      enableds = dgca.enableds and paths = dgca.paths and runs = dgca.runs and
      dexecute = dgca.dexecute and denabled = dgca.denabled and dinitial = dgca.dinitial and
      drejecting = dgca.dcondition
    by this

  abbreviation target where "target \<equiv> dgca.target"
  abbreviation states where "states \<equiv> dgca.states"
  abbreviation trace where "trace \<equiv> dgca.trace"

  abbreviation successors :: "('label, 'state) dgca \<Rightarrow> 'state \<Rightarrow> 'state set" where
    "successors \<equiv> dgca.successors TYPE('label)"

  lemma path_alt_def: "path A w p \<longleftrightarrow> set w \<subseteq> alphabet A"
  unfolding lists_iff_set[symmetric]
  proof
    show "w \<in> lists (alphabet A)" if "path A w p" using that by (induct arbitrary: p) (auto)
    show "path A w p" if "w \<in> lists (alphabet A)" using that by (induct arbitrary: p) (auto)
  qed
  lemma run_alt_def: "run A w p \<longleftrightarrow> sset w \<subseteq> alphabet A"
  unfolding streams_iff_sset[symmetric]
  proof
    show "w \<in> streams (alphabet A)" if "run A w p"
      using that by (coinduction arbitrary: w p) (force elim: dgca.run.cases)
    show "run A w p" if "w \<in> streams (alphabet A)"
      using that by (coinduction arbitrary: w p) (force elim: streams.cases)
  qed

  definition language :: "('label, 'state) dgca \<Rightarrow> 'label stream set" where
    "language A \<equiv> {w. run A w (initial A) \<and> cogen fins (rejecting A) (trace A w (initial A))}"

  lemma language[intro]:
    assumes "run A w (initial A)" "cogen fins (rejecting A) (trace A w (initial A))"
    shows "w \<in> language A"
    using assms unfolding language_def by auto
  lemma language_elim[elim]:
    assumes "w \<in> language A"
    obtains "run A w (initial A)" "cogen fins (rejecting A) (trace A w (initial A))"
    using assms unfolding language_def by auto

  lemma language_alphabet: "language A \<subseteq> streams (alphabet A)"
    unfolding language_def run_alt_def using sset_streams by auto

  definition degen :: "('label, 'state) dgca \<Rightarrow> ('label, 'state degen) dca" where
    "degen A \<equiv> dca (alphabet A) (The (dinitial A)) (dexecute A) (drejecting A)"

  lemma degen_language: "DCA.language (degen A) = DGCA.language A"
  proof -
    have 1: "dca.trace (degen A) = dgca.degen.trace A" unfolding degen_def by simp
    have 2: "dca.run (degen A) = dgca.degen.run A"
      unfolding degen_def DCA.run_def DGCA.run_def dgca.denabled_def by (simp add: cond_case_prod_eta)
    have 3: "dca.initial (degen A) = (dgca.initial A, 0)" unfolding degen_def dgca.dinitial_def by auto
    have 4: "dca.rejecting (degen A) = drejecting A" unfolding degen_def by simp
    show ?thesis
      unfolding DCA.language_def DGCA.language_def 1 2 3 4
      unfolding dgca.degen_run dgca.degen_infs run_def cogen_def
      by auto
  qed

end