section \<open>Deterministic Co-Generalized Co-Büchi Automata\<close>

theory DGCA
imports
  "DCA"
  "../../Basic/Degeneralization"
begin

  datatype ('label, 'state) dgca = dgca
    (alphabet: "'label set")
    (initial: "'state")
    (succ: "'label \<Rightarrow> 'state \<Rightarrow> 'state")
    (rejecting: "'state pred gen")

  global_interpretation dgca: transition_system_initial
    "succ A" "\<lambda> a p. a \<in> alphabet A" "\<lambda> p. p = initial A"
    for A
    defines path = dgca.path and run = dgca.run and reachable = dgca.reachable and nodes = dgca.nodes and
      enableds = dgca.enableds and paths = dgca.paths and runs = dgca.runs
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

  definition dgcad :: "('label, 'state) dgca \<Rightarrow> ('label, 'state degen) dca" where
    "dgcad A \<equiv> dca
      (alphabet A)
      (initial A, 0)
      (\<lambda> a (p, k). (succ A a p, count (rejecting A) p k))
      (degen (rejecting A))"

  lemma dgcad_simps[simp]:
    "dca.alphabet (dgcad A) = alphabet A"
    "dca.initial (dgcad A) = (initial A, 0)"
    "dca.succ (dgcad A) a (p, k) = (succ A a p, count (rejecting A) p k)"
    "dca.rejecting (dgcad A) = degen (rejecting A)"
    unfolding dgcad_def by auto

  lemma dgcad_target[simp]: "dca.target (dgcad A) w (p, k) =
    (dgca.target A w p, fold (count (rejecting A)) (butlast (p # dgca.states A w p)) k)"
    by (induct w arbitrary: p k) (auto)
  lemma dgcad_states[simp]: "dca.states (dgcad A) w (p, k) =
    dgca.states A w p || scan (count (rejecting A)) (p # dgca.states A w p) k"
    by (induct w arbitrary: p k) (auto)
  lemma dgcad_trace[simp]: "dca.trace (dgcad A) w (p, k) =
    dgca.trace A w p ||| sscan (count (rejecting A)) (p ## dgca.trace A w p) k"
    by (coinduction arbitrary: w p k) (auto)
  lemma dgcad_path[iff]: "dca.path (dgcad A) w (p, k) \<longleftrightarrow> dgca.path A w p"
    unfolding DCA.path_alt_def DGCA.path_alt_def by simp
  lemma dgcad_run[iff]: "dca.run (dgcad A) w (p, k) \<longleftrightarrow> dgca.run A w p"
    unfolding DCA.run_alt_def DGCA.run_alt_def by simp

  (* TODO: revise *)
  lemma dgcad_nodes_fst[simp]: "fst ` DCA.nodes (dgcad A) = DGCA.nodes A"
    unfolding dca.nodes_alt_def dca.reachable_alt_def
    unfolding dgca.nodes_alt_def dgca.reachable_alt_def
    unfolding image_def by simp
  lemma dgcad_nodes_snd_empty:
    assumes "rejecting A = []"
    shows "snd ` DCA.nodes (dgcad A) \<subseteq> {0}"
  proof -
    have 2: "snd (dca.succ (dgcad A) a (p, k)) = 0" for a p k using assms by auto
    show ?thesis using 2 by (auto elim: dca.nodes.cases)
  qed
  lemma dgcad_nodes_snd_nonempty:
    assumes "rejecting A \<noteq> []"
    shows "snd ` DCA.nodes (dgcad A) \<subseteq> {0 ..< length (rejecting A)}"
  proof -
    have 1: "snd (dca.initial (dgcad A)) < length (rejecting A)"
      using assms by simp
    have 2: "snd (dca.succ (dgcad A) a (p, k)) < length (rejecting A)" for a p k
      using assms by auto
    show ?thesis using 1 2 by (auto elim: dca.nodes.cases)
  qed
  lemma dgcad_nodes_empty:
    assumes "rejecting A = []"
    shows "DCA.nodes (dgcad A) = DGCA.nodes A \<times> {0}"
  proof -
    have "(p, k) \<in> DCA.nodes (dgcad A) \<longleftrightarrow> p \<in> fst ` DCA.nodes (dgcad A) \<and> k = 0" for p k
      using dgcad_nodes_snd_empty[OF assms] by (force simp del: dgcad_nodes_fst)
    then show ?thesis by auto
  qed
  lemma dgcad_nodes_nonempty:
    assumes "rejecting A \<noteq> []"
    shows "DCA.nodes (dgcad A) \<subseteq> DGCA.nodes A \<times> {0 ..< length (rejecting A)}"
    using subset_fst_snd dgcad_nodes_fst[of A] dgcad_nodes_snd_nonempty[OF assms] by blast
  lemma dgcad_nodes: "DCA.nodes (dgcad A) \<subseteq> DGCA.nodes A \<times> {0 ..< max 1 (length (rejecting A))}"
    using dgcad_nodes_empty dgcad_nodes_nonempty by force

  lemma dgcad_language[simp]: "DCA.language (dgcad A) = DGCA.language A" by force

  lemma dgcad_nodes_finite[iff]: "finite (DCA.nodes (dgcad A)) \<longleftrightarrow> finite (DGCA.nodes A)"
  proof
    show "finite (DGCA.nodes A)" if "finite (DCA.nodes (dgcad A))"
      using that by (auto simp flip: dgcad_nodes_fst)
    show "finite (DCA.nodes (dgcad A))" if "finite (DGCA.nodes A)"
      using dgcad_nodes that finite_subset by fastforce
  qed
  lemma dgcad_nodes_card: "card (DCA.nodes (dgcad A)) \<le> max 1 (length (rejecting A)) * card (DGCA.nodes A)"
  proof (cases "finite (DGCA.nodes A)")
    case True
    have "card (DCA.nodes (dgcad A)) \<le> card (DGCA.nodes A \<times> {0 ..< max 1 (length (rejecting A))})"
      using dgcad_nodes True by (blast intro: card_mono)
    also have "\<dots> = max 1 (length (rejecting A)) * card (DGCA.nodes A)" unfolding card_cartesian_product by simp
    finally show ?thesis by this
  next
    case False
    then have "card (DGCA.nodes A) = 0" "card (DCA.nodes (dgcad A)) = 0" by auto
    then show ?thesis by simp
  qed

end