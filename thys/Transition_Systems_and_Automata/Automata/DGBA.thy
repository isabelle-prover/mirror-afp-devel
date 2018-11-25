section {* Deterministic Generalized Büchi Automata *}

theory DGBA
imports
  "DBA"
  "../Transition_Systems/Transition_System_Degeneralization"
begin

  datatype ('label, 'state) dgba = dgba
    (alphabet: "'label set")
    (initial: "'state")
    (succ: "'label \<Rightarrow> 'state \<Rightarrow> 'state")
    (accepting: "'state pred gen")

  global_interpretation dgba: transition_system_initial_generalized
    "succ A" "\<lambda> a p. a \<in> alphabet A" "\<lambda> p. p = initial A" "accepting A"
    for A
    defines path = dgba.path and run = dgba.run and reachable = dgba.reachable and nodes = dgba.nodes and
      enableds = dgba.enableds and paths = dgba.paths and runs = dgba.runs and
      dexecute = dgba.dexecute and denabled = dgba.denabled and dinitial = dgba.dinitial and
      daccepting = dgba.dcondition
    by this

  abbreviation target where "target \<equiv> dgba.target"
  abbreviation states where "states \<equiv> dgba.states"
  abbreviation trace where "trace \<equiv> dgba.trace"

  abbreviation successors :: "('label, 'state) dgba \<Rightarrow> 'state \<Rightarrow> 'state set" where
    "successors \<equiv> dgba.successors TYPE('label)"

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
      using that by (coinduction arbitrary: w p) (force elim: dgba.run.cases)
    show "run A w p" if "w \<in> streams (alphabet A)"
      using that by (coinduction arbitrary: w p) (force elim: streams.cases)
  qed

  definition language :: "('label, 'state) dgba \<Rightarrow> 'label stream set" where
    "language A \<equiv> {w. run A w (initial A) \<and> gen infs (accepting A) (trace A w (initial A))}"

  lemma language[intro]:
    assumes "run A w (initial A)" "gen infs (accepting A) (trace A w (initial A))"
    shows "w \<in> language A"
    using assms unfolding language_def by auto
  lemma language_elim[elim]:
    assumes "w \<in> language A"
    obtains "run A w (initial A)" "gen infs (accepting A) (trace A w (initial A))"
    using assms unfolding language_def by auto

  lemma language_alphabet: "language A \<subseteq> streams (alphabet A)"
    unfolding language_def run_alt_def using sset_streams by auto

  definition degen :: "('label, 'state) dgba \<Rightarrow> ('label, 'state degen) dba" where
    "degen A \<equiv> dba (alphabet A) (The (dinitial A)) (dexecute A) (daccepting A)"

  lemma degen_language: "DBA.language (degen A) = DGBA.language A"
  proof -
    have 1: "dba.trace (degen A) = dgba.degen.trace A" unfolding degen_def by simp
    have 2: "dba.run (degen A) = dgba.degen.run A"
      unfolding degen_def DBA.run_def DGBA.run_def dgba.denabled_def by (simp add: cond_case_prod_eta)
    have 3: "dba.initial (degen A) = (dgba.initial A, 0)" unfolding degen_def dgba.dinitial_def by auto
    have 4: "dba.accepting (degen A) = daccepting A" unfolding degen_def by simp
    show ?thesis
      unfolding DBA.language_def DGBA.language_def 1 2 3 4
      unfolding dgba.degen_run dgba.degen_infs run_def gen_def
      by rule
  qed

end