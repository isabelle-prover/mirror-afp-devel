section \<open>Deterministic Generalized Büchi Automata\<close>

theory DGBA
imports
  "DBA"
  "../../Basic/Degeneralization"
begin

  datatype ('label, 'state) dgba = dgba
    (alphabet: "'label set")
    (initial: "'state")
    (succ: "'label \<Rightarrow> 'state \<Rightarrow> 'state")
    (accepting: "'state pred gen")

  global_interpretation dgba: transition_system_initial
    "succ A" "\<lambda> a p. a \<in> alphabet A" "\<lambda> p. p = initial A"
    for A
    defines path = dgba.path and run = dgba.run and reachable = dgba.reachable and nodes = dgba.nodes and
      enableds = dgba.enableds and paths = dgba.paths and runs = dgba.runs
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

  definition dgbad :: "('label, 'state) dgba \<Rightarrow> ('label, 'state degen) dba" where
    "dgbad A \<equiv> dba
      (alphabet A)
      (initial A, 0)
      (\<lambda> a (p, k). (succ A a p, count (accepting A) p k))
      (degen (accepting A))"

  lemma dgbad_simps[simp]:
    "dba.alphabet (dgbad A) = alphabet A"
    "dba.initial (dgbad A) = (initial A, 0)"
    "dba.succ (dgbad A) a (p, k) = (succ A a p, count (accepting A) p k)"
    "dba.accepting (dgbad A) = degen (accepting A)"
    unfolding dgbad_def by auto

  lemma dgbad_target[simp]: "dba.target (dgbad A) w (p, k) =
    (dgba.target A w p, fold (count (accepting A)) (butlast (p # dgba.states A w p)) k)"
    by (induct w arbitrary: p k) (auto)
  lemma dgbad_states[simp]: "dba.states (dgbad A) w (p, k) =
    dgba.states A w p || scan (count (accepting A)) (p # dgba.states A w p) k"
    by (induct w arbitrary: p k) (auto)
  lemma dgbad_trace[simp]: "dba.trace (dgbad A) w (p, k) =
    dgba.trace A w p ||| sscan (count (accepting A)) (p ## dgba.trace A w p) k"
    by (coinduction arbitrary: w p k) (auto)
  lemma dgbad_path[iff]: "dba.path (dgbad A) w (p, k) \<longleftrightarrow> dgba.path A w p"
    unfolding DBA.path_alt_def DGBA.path_alt_def by simp
  lemma dgbad_run[iff]: "dba.run (dgbad A) w (p, k) \<longleftrightarrow> dgba.run A w p"
    unfolding DBA.run_alt_def DGBA.run_alt_def by simp

  (* TODO: revise *)
  lemma dgbad_nodes_fst[simp]: "fst ` DBA.nodes (dgbad A) = DGBA.nodes A"
    unfolding dba.nodes_alt_def dba.reachable_alt_def
    unfolding dgba.nodes_alt_def dgba.reachable_alt_def
    unfolding image_def by simp
  lemma dgbad_nodes_snd_empty:
    assumes "accepting A = []"
    shows "snd ` DBA.nodes (dgbad A) \<subseteq> {0}"
  proof -
    have 2: "snd (dba.succ (dgbad A) a (p, k)) = 0" for a p k using assms by auto
    show ?thesis using 2 by (auto elim: dba.nodes.cases)
  qed
  lemma dgbad_nodes_snd_nonempty:
    assumes "accepting A \<noteq> []"
    shows "snd ` DBA.nodes (dgbad A) \<subseteq> {0 ..< length (accepting A)}"
  proof -
    have 1: "snd (dba.initial (dgbad A)) < length (accepting A)"
      using assms by simp
    have 2: "snd (dba.succ (dgbad A) a (p, k)) < length (accepting A)" for a p k
      using assms by auto
    show ?thesis using 1 2 by (auto elim: dba.nodes.cases)
  qed
  lemma dgbad_nodes_empty:
    assumes "accepting A = []"
    shows "DBA.nodes (dgbad A) = DGBA.nodes A \<times> {0}"
  proof -
    have "(p, k) \<in> DBA.nodes (dgbad A) \<longleftrightarrow> p \<in> fst ` DBA.nodes (dgbad A) \<and> k = 0" for p k
      using dgbad_nodes_snd_empty[OF assms] by (force simp del: dgbad_nodes_fst)
    then show ?thesis by auto
  qed
  lemma dgbad_nodes_nonempty:
    assumes "accepting A \<noteq> []"
    shows "DBA.nodes (dgbad A) \<subseteq> DGBA.nodes A \<times> {0 ..< length (accepting A)}"
    using subset_fst_snd dgbad_nodes_fst[of A] dgbad_nodes_snd_nonempty[OF assms] by blast
  lemma dgbad_nodes: "DBA.nodes (dgbad A) \<subseteq> DGBA.nodes A \<times> {0 ..< max 1 (length (accepting A))}"
    using dgbad_nodes_empty dgbad_nodes_nonempty by force

  lemma dgbad_language[simp]: "DBA.language (dgbad A) = DGBA.language A" by force

  lemma dgbad_nodes_finite[iff]: "finite (DBA.nodes (dgbad A)) \<longleftrightarrow> finite (DGBA.nodes A)"
  proof
    show "finite (DGBA.nodes A)" if "finite (DBA.nodes (dgbad A))"
      using that by (auto simp flip: dgbad_nodes_fst)
    show "finite (DBA.nodes (dgbad A))" if "finite (DGBA.nodes A)"
      using dgbad_nodes that finite_subset by fastforce
  qed
  lemma dgbad_nodes_card: "card (DBA.nodes (dgbad A)) \<le> max 1 (length (accepting A)) * card (DGBA.nodes A)"
  proof (cases "finite (DGBA.nodes A)")
    case True
    have "card (DBA.nodes (dgbad A)) \<le> card (DGBA.nodes A \<times> {0 ..< max 1 (length (accepting A))})"
      using dgbad_nodes True by (blast intro: card_mono)
    also have "\<dots> = max 1 (length (accepting A)) * card (DGBA.nodes A)" unfolding card_cartesian_product by simp
    finally show ?thesis by this
  next
    case False
    then have "card (DGBA.nodes A) = 0" "card (DBA.nodes (dgbad A)) = 0" by auto
    then show ?thesis by simp
  qed

end