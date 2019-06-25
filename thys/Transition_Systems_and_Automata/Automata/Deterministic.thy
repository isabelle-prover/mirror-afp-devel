theory Deterministic
imports
  "../Transition_Systems/Transition_System"
  "../Transition_Systems/Transition_System_Extra"
  "../Transition_Systems/Transition_System_Construction"
  "../Basic/Degeneralization"
begin

  type_synonym ('label, 'state) trans = "'label \<Rightarrow> 'state \<Rightarrow> 'state"

  (* TODO: is there a way to be less verbose in these locales? do we need to specify all the types? *)
  locale automaton =
    fixes automaton :: "'label set \<Rightarrow> 'state \<Rightarrow> ('label, 'state) trans \<Rightarrow> 'condition \<Rightarrow> 'automaton"
    fixes alphabet :: "'automaton \<Rightarrow> 'label set"
    fixes initial :: "'automaton \<Rightarrow> 'state"
    fixes transition :: "'automaton \<Rightarrow> ('label, 'state) trans"
    fixes condition :: "'automaton \<Rightarrow> 'condition"
    assumes automaton[simp]: "automaton (alphabet A) (initial A) (transition A) (condition A) = A"
    assumes alphabet[simp]: "alphabet (automaton a i t c) = a"
    assumes initial[simp]: "initial (automaton a i t c) = i"
    assumes transition[simp]: "transition (automaton a i t c) = t"
    assumes condition[simp]: "condition (automaton a i t c) = c"
  begin

    (* TODO: is there a way to use defines without renaming the constants? *)
    sublocale transition_system_initial
      "transition A" "\<lambda> a p. a \<in> alphabet A" "\<lambda> p. p = initial A"
      for A
      defines path' = path and run' = run and reachable' = reachable and nodes' = nodes
      by this

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
        using that by (coinduction arbitrary: w p) (force elim: run.cases)
      show "run A w p" if "w \<in> streams (alphabet A)"
        using that by (coinduction arbitrary: w p) (force elim: streams.cases)
    qed

  end

  (* TODO: create analogous locale for DFAs (automaton_target) *)
  locale automaton_trace =
    automaton automaton alphabet initial transition condition
    for automaton :: "'label set \<Rightarrow> 'state \<Rightarrow> ('label, 'state) trans \<Rightarrow> 'condition \<Rightarrow> 'automaton"
    and alphabet :: "'automaton \<Rightarrow> 'label set"
    and initial :: "'automaton \<Rightarrow> 'state"
    and transition :: "'automaton \<Rightarrow> ('label, 'state) trans"
    and condition :: "'automaton \<Rightarrow> 'condition"
    +
    fixes test :: "'condition \<Rightarrow> 'state stream \<Rightarrow> bool"
  begin

    definition language :: "'automaton \<Rightarrow> 'label stream set" where
      "language A \<equiv> {w. run A w (initial A) \<and> test (condition A) (trace A w (initial A))}"
  
    lemma language[intro]:
      assumes "run A w (initial A)" "test (condition A) (trace A w (initial A))"
      shows "w \<in> language A"
      using assms unfolding language_def by auto
    lemma language_elim[elim]:
      assumes "w \<in> language A"
      obtains "run A w (initial A)" "test (condition A) (trace A w (initial A))"
      using assms unfolding language_def by auto
  
    lemma language_alphabet: "language A \<subseteq> streams (alphabet A)"
      unfolding language_def run_alt_def using sset_streams by auto

  end

  locale automaton_degeneralization =
    a: automaton automaton\<^sub>1 alphabet\<^sub>1 initial\<^sub>1 transition\<^sub>1 condition\<^sub>1 +
    b: automaton automaton\<^sub>2 alphabet\<^sub>2 initial\<^sub>2 transition\<^sub>2 condition\<^sub>2
    for automaton\<^sub>1 :: "'label set \<Rightarrow> 'state \<Rightarrow> ('label, 'state) trans \<Rightarrow> 'state pred gen \<Rightarrow> 'automaton\<^sub>1"
    and alphabet\<^sub>1 :: "'automaton\<^sub>1 \<Rightarrow> 'label set"
    and initial\<^sub>1 :: "'automaton\<^sub>1 \<Rightarrow> 'state"
    and transition\<^sub>1 :: "'automaton\<^sub>1 \<Rightarrow> ('label, 'state) trans"
    and condition\<^sub>1 :: "'automaton\<^sub>1 \<Rightarrow> 'state pred gen"
    and automaton\<^sub>2 :: "'label set \<Rightarrow> 'state degen \<Rightarrow> ('label, 'state degen) trans \<Rightarrow> 'state degen pred \<Rightarrow> 'automaton\<^sub>2"
    and alphabet\<^sub>2 :: "'automaton\<^sub>2 \<Rightarrow> 'label set"
    and initial\<^sub>2 :: "'automaton\<^sub>2 \<Rightarrow> 'state degen"
    and transition\<^sub>2 :: "'automaton\<^sub>2 \<Rightarrow> ('label, 'state degen) trans"
    and condition\<^sub>2 :: "'automaton\<^sub>2 \<Rightarrow> 'state degen pred"
  begin

    definition degeneralize :: "'automaton\<^sub>1 \<Rightarrow> 'automaton\<^sub>2" where
      "degeneralize A \<equiv> automaton\<^sub>2
        (alphabet\<^sub>1 A)
        (initial\<^sub>1 A, 0)
        (\<lambda> a (p, k). (transition\<^sub>1 A a p, count (condition\<^sub>1 A) p k))
        (degen (condition\<^sub>1 A))"

    lemma degeneralize_simps[simp]:
      "alphabet\<^sub>2 (degeneralize A) = alphabet\<^sub>1 A"
      "initial\<^sub>2 (degeneralize A) = (initial\<^sub>1 A, 0)"
      "transition\<^sub>2 (degeneralize A) a (p, k) = (transition\<^sub>1 A a p, count (condition\<^sub>1 A) p k)"
      "condition\<^sub>2 (degeneralize A) = degen (condition\<^sub>1 A)"
      unfolding degeneralize_def by auto

    lemma degeneralize_target[simp]: "b.target (degeneralize A) w (p, k) =
      (a.target A w p, fold (count (condition\<^sub>1 A)) (butlast (p # a.states A w p)) k)"
      by (induct w arbitrary: p k) (auto)
    lemma degeneralize_states[simp]: "b.states (degeneralize A) w (p, k) =
      a.states A w p || scan (count (condition\<^sub>1 A)) (p # a.states A w p) k"
      by (induct w arbitrary: p k) (auto)
    lemma degeneralize_trace[simp]: "b.trace (degeneralize A) w (p, k) =
      a.trace A w p ||| sscan (count (condition\<^sub>1 A)) (p ## a.trace A w p) k"
      by (coinduction arbitrary: w p k) (auto)

    lemma degeneralize_path[iff]: "b.path (degeneralize A) w (p, k) \<longleftrightarrow> a.path A w p"
      unfolding a.path_alt_def b.path_alt_def by simp
    lemma degeneralize_run[iff]: "b.run (degeneralize A) w (p, k) \<longleftrightarrow> a.run A w p"
      unfolding a.run_alt_def b.run_alt_def by simp

    lemma degeneralize_reachable_fst[simp]: "fst ` b.reachable (degeneralize A) (p, k) = a.reachable A p"
      unfolding a.reachable_alt_def b.reachable_alt_def image_def by simp
    lemma degeneralize_reachable_snd_empty[simp]:
      assumes "condition\<^sub>1 A = []"
      shows "snd ` b.reachable (degeneralize A) (p, k) = {k}"
    proof -
      have "snd ql = k" if "ql \<in> b.reachable (degeneralize A) (p, k)" for ql
        using that assms by induct auto
      then show ?thesis by auto
    qed
    lemma degeneralize_reachable_empty[simp]:
      assumes "condition\<^sub>1 A = []"
      shows "b.reachable (degeneralize A) (p, k) = a.reachable A p \<times> {k}"
      using degeneralize_reachable_fst degeneralize_reachable_snd_empty assms
      by (metis prod_singleton(2))
    lemma degeneralize_reachable_snd:
      "snd ` b.reachable (degeneralize A) (p, k) \<subseteq> insert k {0 ..< length (condition\<^sub>1 A)}"
      by (cases "condition\<^sub>1 A = []") (auto)
    lemma degeneralize_reachable:
      "b.reachable (degeneralize A) (p, k) \<subseteq> a.reachable A p \<times> insert k {0 ..< length (condition\<^sub>1 A)}"
      by (cases "condition\<^sub>1 A = []") (auto 0 3)

    lemma degeneralize_nodes_fst[simp]: "fst ` b.nodes (degeneralize A) = a.nodes A"
      unfolding a.nodes_alt_def b.nodes_alt_def by simp
    lemma degeneralize_nodes_snd_empty:
      assumes "condition\<^sub>1 A = []"
      shows "snd ` b.nodes (degeneralize A) = {0}"
      using assms unfolding b.nodes_alt_def by auto
    lemma degeneralize_nodes_empty:
      assumes "condition\<^sub>1 A = []"
      shows "b.nodes (degeneralize A) = a.nodes A \<times> {0}"
      using assms unfolding b.nodes_alt_def by auto
    lemma degeneralize_nodes_snd:
      "snd ` b.nodes (degeneralize A) \<subseteq> insert 0 {0 ..< length (condition\<^sub>1 A)}"
      using degeneralize_reachable_snd unfolding b.nodes_alt_def by auto
    lemma degeneralize_nodes:
      "b.nodes (degeneralize A) \<subseteq> a.nodes A \<times> insert 0 {0 ..< length (condition\<^sub>1 A)}"
      using degeneralize_reachable unfolding a.nodes_alt_def b.nodes_alt_def by simp
  
    lemma degeneralize_nodes_finite[iff]: "finite (b.nodes (degeneralize A)) \<longleftrightarrow> finite (a.nodes A)"
    proof
      show "finite (a.nodes A)" if "finite (b.nodes (degeneralize A))"
        using that by (auto simp flip: degeneralize_nodes_fst)
      show "finite (b.nodes (degeneralize A))" if "finite (a.nodes A)"
        using degeneralize_nodes that finite_subset by fastforce
    qed
    lemma degeneralize_nodes_card: "card (b.nodes (degeneralize A)) \<le>
      max 1 (length (condition\<^sub>1 A)) * card (a.nodes A)"
    proof (cases "finite (a.nodes A)")
      case True
      have "card (b.nodes (degeneralize A)) \<le> card (a.nodes A \<times> insert 0 {0 ..< length (condition\<^sub>1 A)})"
        using degeneralize_nodes True by (blast intro: card_mono)
      also have "\<dots> = card (insert 0 {0 ..< length (condition\<^sub>1 A)}) * card (a.nodes A)"
        unfolding card_cartesian_product by simp
      also have "card (insert 0 {0 ..< length (condition\<^sub>1 A)}) = max 1 (length (condition\<^sub>1 A))"
        by (simp add: card_insert_if Suc_leI max_absorb2)
      finally show ?thesis by this
    next
      case False
      then have "card (a.nodes A) = 0" "card (b.nodes (degeneralize A)) = 0" by auto
      then show ?thesis by simp
    qed

  end

  locale automaton_degeneralization_trace =
    automaton_degeneralization
      automaton\<^sub>1 alphabet\<^sub>1 initial\<^sub>1 transition\<^sub>1 condition\<^sub>1
      automaton\<^sub>2 alphabet\<^sub>2 initial\<^sub>2 transition\<^sub>2 condition\<^sub>2 +
    a: automaton_trace automaton\<^sub>1 alphabet\<^sub>1 initial\<^sub>1 transition\<^sub>1 condition\<^sub>1 test\<^sub>1 +
    b: automaton_trace automaton\<^sub>2 alphabet\<^sub>2 initial\<^sub>2 transition\<^sub>2 condition\<^sub>2 test\<^sub>2
    for automaton\<^sub>1 :: "'label set \<Rightarrow> 'state \<Rightarrow> ('label, 'state) trans \<Rightarrow> 'state pred gen \<Rightarrow> 'automaton\<^sub>1"
    and alphabet\<^sub>1 :: "'automaton\<^sub>1 \<Rightarrow> 'label set"
    and initial\<^sub>1 :: "'automaton\<^sub>1 \<Rightarrow> 'state"
    and transition\<^sub>1 :: "'automaton\<^sub>1 \<Rightarrow> ('label, 'state) trans"
    and condition\<^sub>1 :: "'automaton\<^sub>1 \<Rightarrow> 'state pred gen"
    and test\<^sub>1 :: "'state pred gen \<Rightarrow> 'state stream \<Rightarrow> bool"
    and automaton\<^sub>2 :: "'label set \<Rightarrow> 'state degen \<Rightarrow> ('label, 'state degen) trans \<Rightarrow> 'state degen pred \<Rightarrow> 'automaton\<^sub>2"
    and alphabet\<^sub>2 :: "'automaton\<^sub>2 \<Rightarrow> 'label set"
    and initial\<^sub>2 :: "'automaton\<^sub>2 \<Rightarrow> 'state degen"
    and transition\<^sub>2 :: "'automaton\<^sub>2 \<Rightarrow> ('label, 'state degen) trans"
    and condition\<^sub>2 :: "'automaton\<^sub>2 \<Rightarrow> 'state degen pred"
    and test\<^sub>2 :: "'state degen pred \<Rightarrow> 'state degen stream \<Rightarrow> bool"
    +
    assumes test[iff]: "test\<^sub>2 (degen cs) (r ||| sscan (count cs) (p ## r) k) \<longleftrightarrow> test\<^sub>1 cs r"
  begin

    lemma degeneralize_language[simp]: "b.language (degeneralize A) = a.language A"
      by (force simp del: sscan_scons)

  end

  locale automaton_combination =
    a: automaton automaton\<^sub>1 alphabet\<^sub>1 initial\<^sub>1 transition\<^sub>1 condition\<^sub>1 +
    b: automaton automaton\<^sub>2 alphabet\<^sub>2 initial\<^sub>2 transition\<^sub>2 condition\<^sub>2 +
    c: automaton automaton\<^sub>3 alphabet\<^sub>3 initial\<^sub>3 transition\<^sub>3 condition\<^sub>3
    for automaton\<^sub>1 :: "'label set \<Rightarrow> 'state\<^sub>1 \<Rightarrow> ('label, 'state\<^sub>1) trans \<Rightarrow> 'condition\<^sub>1 \<Rightarrow> 'automaton\<^sub>1"
    and alphabet\<^sub>1 :: "'automaton\<^sub>1 \<Rightarrow> 'label set"
    and initial\<^sub>1 :: "'automaton\<^sub>1 \<Rightarrow> 'state\<^sub>1"
    and transition\<^sub>1 :: "'automaton\<^sub>1 \<Rightarrow> ('label, 'state\<^sub>1) trans"
    and condition\<^sub>1 :: "'automaton\<^sub>1 \<Rightarrow> 'condition\<^sub>1"
    and automaton\<^sub>2 :: "'label set \<Rightarrow> 'state\<^sub>2 \<Rightarrow> ('label, 'state\<^sub>2) trans \<Rightarrow> 'condition\<^sub>2 \<Rightarrow> 'automaton\<^sub>2"
    and alphabet\<^sub>2 :: "'automaton\<^sub>2 \<Rightarrow> 'label set"
    and initial\<^sub>2 :: "'automaton\<^sub>2 \<Rightarrow> 'state\<^sub>2"
    and transition\<^sub>2 :: "'automaton\<^sub>2 \<Rightarrow> ('label, 'state\<^sub>2) trans"
    and condition\<^sub>2 :: "'automaton\<^sub>2 \<Rightarrow> 'condition\<^sub>2"
    and automaton\<^sub>3 :: "'label set \<Rightarrow> 'state\<^sub>1 \<times> 'state\<^sub>2 \<Rightarrow> ('label, 'state\<^sub>1 \<times> 'state\<^sub>2) trans \<Rightarrow>
      'condition\<^sub>3 \<Rightarrow> 'automaton\<^sub>3"
    and alphabet\<^sub>3 :: "'automaton\<^sub>3 \<Rightarrow> 'label set"
    and initial\<^sub>3 :: "'automaton\<^sub>3 \<Rightarrow> 'state\<^sub>1 \<times> 'state\<^sub>2"
    and transition\<^sub>3 :: "'automaton\<^sub>3 \<Rightarrow> ('label, 'state\<^sub>1 \<times> 'state\<^sub>2) trans"
    and condition\<^sub>3 :: "'automaton\<^sub>3 \<Rightarrow> 'condition\<^sub>3"
    +
    fixes condition :: "'condition\<^sub>1 \<Rightarrow> 'condition\<^sub>2 \<Rightarrow> 'condition\<^sub>3"
  begin

    definition combine :: "'automaton\<^sub>1 \<Rightarrow> 'automaton\<^sub>2 \<Rightarrow> 'automaton\<^sub>3" where
      "combine A B \<equiv> automaton\<^sub>3
        (alphabet\<^sub>1 A \<inter> alphabet\<^sub>2 B)
        (initial\<^sub>1 A, initial\<^sub>2 B)
        (\<lambda> a (p, q). (transition\<^sub>1 A a p, transition\<^sub>2 B a q))
        (condition (condition\<^sub>1 A) (condition\<^sub>2 B))"

    lemma combine_simps[simp]:
      "alphabet\<^sub>3 (combine A B) = alphabet\<^sub>1 A \<inter> alphabet\<^sub>2 B"
      "initial\<^sub>3 (combine A B) = (initial\<^sub>1 A, initial\<^sub>2 B)"
      "transition\<^sub>3 (combine A B) a (p, q) = (transition\<^sub>1 A a p, transition\<^sub>2 B a q)"
      "condition\<^sub>3 (combine A B) = condition (condition\<^sub>1 A) (condition\<^sub>2 B)"
      unfolding combine_def by auto

    lemma combine_target[simp]: "c.target (combine A B) w (p, q) = (a.target A w p, b.target B w q)"
      by (induct w arbitrary: p q) (auto)
    lemma combine_states[simp]: "c.states (combine A B) w (p, q) = a.states A w p || b.states B w q"
      by (induct w arbitrary: p q) (auto)
    lemma combine_trace[simp]: "c.trace (combine A B) w (p, q) = a.trace A w p ||| b.trace B w q"
      by (coinduction arbitrary: w p q) (auto)

    lemma combine_path[iff]: "c.path (combine A B) w (p, q) \<longleftrightarrow> a.path A w p \<and> b.path B w q"
      unfolding a.path_alt_def b.path_alt_def c.path_alt_def by simp
    lemma combine_run[iff]: "c.run (combine A B) w (p, q) \<longleftrightarrow> a.run A w p \<and> b.run B w q"
      unfolding a.run_alt_def b.run_alt_def c.run_alt_def by simp

    lemma combine_reachable[simp]: "c.reachable (combine A B) (p, q) \<subseteq> a.reachable A p \<times> b.reachable B q"
      unfolding c.reachable_alt_def by auto
    lemma combine_nodes[simp]: "c.nodes (combine A B) \<subseteq> a.nodes A \<times> b.nodes B"
      unfolding a.nodes_alt_def b.nodes_alt_def c.nodes_alt_def by auto
    lemma combine_reachable_fst[simp]:
      assumes "alphabet\<^sub>1 A \<subseteq> alphabet\<^sub>2 B"
      shows "fst ` c.reachable (combine A B) (p, q) = a.reachable A p"
      using assms
      unfolding a.reachable_alt_def a.path_alt_def
      unfolding b.reachable_alt_def b.path_alt_def
      unfolding c.reachable_alt_def c.path_alt_def
      by auto force
    lemma combine_reachable_snd[simp]:
      assumes "alphabet\<^sub>1 A \<supseteq> alphabet\<^sub>2 B"
      shows "snd ` c.reachable (combine A B) (p, q) = b.reachable B q"
      using assms
      unfolding a.reachable_alt_def a.path_alt_def
      unfolding b.reachable_alt_def b.path_alt_def
      unfolding c.reachable_alt_def c.path_alt_def
      by auto force
    lemma combine_nodes_fst[simp]:
      assumes "alphabet\<^sub>1 A \<subseteq> alphabet\<^sub>2 B"
      shows "fst ` c.nodes (combine A B) = a.nodes A"
      using assms combine_reachable_fst
      unfolding a.nodes_alt_def b.nodes_alt_def c.nodes_alt_def
      by fastforce
    lemma combine_nodes_snd[simp]:
      assumes "alphabet\<^sub>1 A \<supseteq> alphabet\<^sub>2 B"
      shows "snd ` c.nodes (combine A B) = b.nodes B"
      using assms combine_reachable_snd
      unfolding a.nodes_alt_def b.nodes_alt_def c.nodes_alt_def
      by fastforce

    lemma combine_nodes_finite[intro]:
      assumes "finite (a.nodes A)" "finite (b.nodes B)"
      shows "finite (c.nodes (combine A B))"
    proof (rule finite_subset)
      show "c.nodes (combine A B) \<subseteq> a.nodes A \<times> b.nodes B" using combine_nodes by this
      show "finite (a.nodes A \<times> b.nodes B)" using assms by simp
    qed
    lemma combine_nodes_finite_strong[iff]:
      assumes "alphabet\<^sub>1 A = alphabet\<^sub>2 B"
      shows "finite (c.nodes (combine A B)) \<longleftrightarrow> finite (a.nodes A) \<and> finite (b.nodes B)"
    proof safe
      show "finite (a.nodes A)" if "finite (c.nodes (combine A B))"
        using combine_nodes_fst assms that by (metis finite_imageI equalityD1)
      show "finite (b.nodes B)" if "finite (c.nodes (combine A B))"
        using combine_nodes_snd assms that by (metis finite_imageI equalityD2)
      show "finite (c.nodes (combine A B))" if "finite (a.nodes A)" "finite (b.nodes B)"
        using that by rule
    qed
    lemma combine_nodes_card[intro]:
      assumes "finite (a.nodes A)" "finite (b.nodes B)"
      shows "card (c.nodes (combine A B)) \<le> card (a.nodes A) * card (b.nodes B)"
    proof -
      have "card (c.nodes (combine A B)) \<le> card (a.nodes A \<times> b.nodes B)"
      proof (rule card_mono)
        show "finite (a.nodes A \<times> b.nodes B)" using assms by simp
        show "c.nodes (combine A B) \<subseteq> a.nodes A \<times> b.nodes B" using combine_nodes by this
      qed
      also have "\<dots> = card (a.nodes A) * card (b.nodes B)" using card_cartesian_product by this
      finally show ?thesis by this
    qed
    lemma combine_nodes_card_strong[intro]:
      assumes "alphabet\<^sub>1 A = alphabet\<^sub>2 B"
      shows "card (c.nodes (combine A B)) \<le> card (a.nodes A) * card (b.nodes B)"
    proof (cases "finite (a.nodes A) \<and> finite (b.nodes B)")
      case True
      show ?thesis using True by auto
    next
      case False
      have 1: "card (c.nodes (combine A B)) = 0" using False assms by simp
      have 2: "card (a.nodes A) * card (b.nodes B) = 0" using False by auto
      show ?thesis using 1 2 by simp
    qed

  end

  locale automaton_intersection_trace =
    automaton_combination
      automaton\<^sub>1 alphabet\<^sub>1 initial\<^sub>1 transition\<^sub>1 condition\<^sub>1
      automaton\<^sub>2 alphabet\<^sub>2 initial\<^sub>2 transition\<^sub>2 condition\<^sub>2
      automaton\<^sub>3 alphabet\<^sub>3 initial\<^sub>3 transition\<^sub>3 condition\<^sub>3 condition +
    a: automaton_trace automaton\<^sub>1 alphabet\<^sub>1 initial\<^sub>1 transition\<^sub>1 condition\<^sub>1 test\<^sub>1 +
    b: automaton_trace automaton\<^sub>2 alphabet\<^sub>2 initial\<^sub>2 transition\<^sub>2 condition\<^sub>2 test\<^sub>2 +
    c: automaton_trace automaton\<^sub>3 alphabet\<^sub>3 initial\<^sub>3 transition\<^sub>3 condition\<^sub>3 test\<^sub>3
    for automaton\<^sub>1 :: "'label set \<Rightarrow> 'state\<^sub>1 \<Rightarrow> ('label, 'state\<^sub>1) trans \<Rightarrow> 'condition\<^sub>1 \<Rightarrow> 'automaton\<^sub>1"
    and alphabet\<^sub>1 :: "'automaton\<^sub>1 \<Rightarrow> 'label set"
    and initial\<^sub>1 :: "'automaton\<^sub>1 \<Rightarrow> 'state\<^sub>1"
    and transition\<^sub>1 :: "'automaton\<^sub>1 \<Rightarrow> ('label, 'state\<^sub>1) trans"
    and condition\<^sub>1 :: "'automaton\<^sub>1 \<Rightarrow> 'condition\<^sub>1"
    and test\<^sub>1 :: "'condition\<^sub>1 \<Rightarrow> 'state\<^sub>1 stream \<Rightarrow> bool"
    and automaton\<^sub>2 :: "'label set \<Rightarrow> 'state\<^sub>2 \<Rightarrow> ('label, 'state\<^sub>2) trans \<Rightarrow> 'condition\<^sub>2 \<Rightarrow> 'automaton\<^sub>2"
    and alphabet\<^sub>2 :: "'automaton\<^sub>2 \<Rightarrow> 'label set"
    and initial\<^sub>2 :: "'automaton\<^sub>2 \<Rightarrow> 'state\<^sub>2"
    and transition\<^sub>2 :: "'automaton\<^sub>2 \<Rightarrow> ('label, 'state\<^sub>2) trans"
    and condition\<^sub>2 :: "'automaton\<^sub>2 \<Rightarrow> 'condition\<^sub>2"
    and test\<^sub>2 :: "'condition\<^sub>2 \<Rightarrow> 'state\<^sub>2 stream \<Rightarrow> bool"
    and automaton\<^sub>3 :: "'label set \<Rightarrow> 'state\<^sub>1 \<times> 'state\<^sub>2 \<Rightarrow> ('label, 'state\<^sub>1 \<times> 'state\<^sub>2) trans \<Rightarrow>
      'condition\<^sub>3 \<Rightarrow> 'automaton\<^sub>3"
    and alphabet\<^sub>3 :: "'automaton\<^sub>3 \<Rightarrow> 'label set"
    and initial\<^sub>3 :: "'automaton\<^sub>3 \<Rightarrow> 'state\<^sub>1 \<times> 'state\<^sub>2"
    and transition\<^sub>3 :: "'automaton\<^sub>3 \<Rightarrow> ('label, 'state\<^sub>1 \<times> 'state\<^sub>2) trans"
    and condition\<^sub>3 :: "'automaton\<^sub>3 \<Rightarrow> 'condition\<^sub>3"
    and test\<^sub>3 :: "'condition\<^sub>3 \<Rightarrow> ('state\<^sub>1 \<times> 'state\<^sub>2) stream \<Rightarrow> bool"
    and condition :: "'condition\<^sub>1 \<Rightarrow> 'condition\<^sub>2 \<Rightarrow> 'condition\<^sub>3"
    +
    assumes test[iff]: "test\<^sub>3 (condition c\<^sub>1 c\<^sub>2) (u ||| v) \<longleftrightarrow> test\<^sub>1 c\<^sub>1 u \<and> test\<^sub>2 c\<^sub>2 v"
  begin

    lemma combine_language[simp]: "c.language (combine A B) = a.language A \<inter> b.language B" by force

  end

  locale automaton_union_trace =
    automaton_combination
      automaton\<^sub>1 alphabet\<^sub>1 initial\<^sub>1 transition\<^sub>1 condition\<^sub>1
      automaton\<^sub>2 alphabet\<^sub>2 initial\<^sub>2 transition\<^sub>2 condition\<^sub>2
      automaton\<^sub>3 alphabet\<^sub>3 initial\<^sub>3 transition\<^sub>3 condition\<^sub>3 condition +
    a: automaton_trace automaton\<^sub>1 alphabet\<^sub>1 initial\<^sub>1 transition\<^sub>1 condition\<^sub>1 test\<^sub>1 +
    b: automaton_trace automaton\<^sub>2 alphabet\<^sub>2 initial\<^sub>2 transition\<^sub>2 condition\<^sub>2 test\<^sub>2 +
    c: automaton_trace automaton\<^sub>3 alphabet\<^sub>3 initial\<^sub>3 transition\<^sub>3 condition\<^sub>3 test\<^sub>3
    for automaton\<^sub>1 :: "'label set \<Rightarrow> 'state\<^sub>1 \<Rightarrow> ('label, 'state\<^sub>1) trans \<Rightarrow> 'condition\<^sub>1 \<Rightarrow> 'automaton\<^sub>1"
    and alphabet\<^sub>1 :: "'automaton\<^sub>1 \<Rightarrow> 'label set"
    and initial\<^sub>1 :: "'automaton\<^sub>1 \<Rightarrow> 'state\<^sub>1"
    and transition\<^sub>1 :: "'automaton\<^sub>1 \<Rightarrow> ('label, 'state\<^sub>1) trans"
    and condition\<^sub>1 :: "'automaton\<^sub>1 \<Rightarrow> 'condition\<^sub>1"
    and test\<^sub>1 :: "'condition\<^sub>1 \<Rightarrow> 'state\<^sub>1 stream \<Rightarrow> bool"
    and automaton\<^sub>2 :: "'label set \<Rightarrow> 'state\<^sub>2 \<Rightarrow> ('label, 'state\<^sub>2) trans \<Rightarrow> 'condition\<^sub>2 \<Rightarrow> 'automaton\<^sub>2"
    and alphabet\<^sub>2 :: "'automaton\<^sub>2 \<Rightarrow> 'label set"
    and initial\<^sub>2 :: "'automaton\<^sub>2 \<Rightarrow> 'state\<^sub>2"
    and transition\<^sub>2 :: "'automaton\<^sub>2 \<Rightarrow> ('label, 'state\<^sub>2) trans"
    and condition\<^sub>2 :: "'automaton\<^sub>2 \<Rightarrow> 'condition\<^sub>2"
    and test\<^sub>2 :: "'condition\<^sub>2 \<Rightarrow> 'state\<^sub>2 stream \<Rightarrow> bool"
    and automaton\<^sub>3 :: "'label set \<Rightarrow> 'state\<^sub>1 \<times> 'state\<^sub>2 \<Rightarrow> ('label, 'state\<^sub>1 \<times> 'state\<^sub>2) trans \<Rightarrow>
      'condition\<^sub>3 \<Rightarrow> 'automaton\<^sub>3"
    and alphabet\<^sub>3 :: "'automaton\<^sub>3 \<Rightarrow> 'label set"
    and initial\<^sub>3 :: "'automaton\<^sub>3 \<Rightarrow> 'state\<^sub>1 \<times> 'state\<^sub>2"
    and transition\<^sub>3 :: "'automaton\<^sub>3 \<Rightarrow> ('label, 'state\<^sub>1 \<times> 'state\<^sub>2) trans"
    and condition\<^sub>3 :: "'automaton\<^sub>3 \<Rightarrow> 'condition\<^sub>3"
    and test\<^sub>3 :: "'condition\<^sub>3 \<Rightarrow> ('state\<^sub>1 \<times> 'state\<^sub>2) stream \<Rightarrow> bool"
    and condition :: "'condition\<^sub>1 \<Rightarrow> 'condition\<^sub>2 \<Rightarrow> 'condition\<^sub>3"
    +
    assumes test[iff]: "test\<^sub>3 (condition c\<^sub>1 c\<^sub>2) (u ||| v) \<longleftrightarrow> test\<^sub>1 c\<^sub>1 u \<or> test\<^sub>2 c\<^sub>2 v"
  begin

    lemma combine_language[simp]:
      assumes "alphabet\<^sub>1 A = alphabet\<^sub>2 B"
      shows "c.language (combine A B) = a.language A \<union> b.language B"
      using assms by (force simp: a.run_alt_def b.run_alt_def)

  end

  (* TODO: complete this in analogy to the pair case *)
  locale automaton_combination_list =
    a: automaton automaton\<^sub>1 alphabet\<^sub>1 initial\<^sub>1 transition\<^sub>1 condition\<^sub>1 +
    b: automaton automaton\<^sub>2 alphabet\<^sub>2 initial\<^sub>2 transition\<^sub>2 condition\<^sub>2
    for automaton\<^sub>1 :: "'label set \<Rightarrow> 'state \<Rightarrow> ('label, 'state) trans \<Rightarrow> 'condition\<^sub>1 \<Rightarrow> 'automaton\<^sub>1"
    and alphabet\<^sub>1 :: "'automaton\<^sub>1 \<Rightarrow> 'label set"
    and initial\<^sub>1 :: "'automaton\<^sub>1 \<Rightarrow> 'state"
    and transition\<^sub>1 :: "'automaton\<^sub>1 \<Rightarrow> ('label, 'state) trans"
    and condition\<^sub>1 :: "'automaton\<^sub>1 \<Rightarrow> 'condition\<^sub>1"
    and automaton\<^sub>2 :: "'label set \<Rightarrow> 'state list \<Rightarrow> ('label, 'state list) trans \<Rightarrow>
      'condition\<^sub>2 \<Rightarrow> 'automaton\<^sub>2"
    and alphabet\<^sub>2 :: "'automaton\<^sub>2 \<Rightarrow> 'label set"
    and initial\<^sub>2 :: "'automaton\<^sub>2 \<Rightarrow> 'state list"
    and transition\<^sub>2 :: "'automaton\<^sub>2 \<Rightarrow> ('label, 'state list) trans"
    and condition\<^sub>2 :: "'automaton\<^sub>2 \<Rightarrow> 'condition\<^sub>2"
    +
    fixes condition :: "'condition\<^sub>1 list \<Rightarrow> 'condition\<^sub>2"
  begin

    definition combine :: "'automaton\<^sub>1 list \<Rightarrow> 'automaton\<^sub>2" where
      "combine AA \<equiv> automaton\<^sub>2
        (\<Inter> (alphabet\<^sub>1 ` set AA))
        (map initial\<^sub>1 AA)
        (\<lambda> a pp. map2 (\<lambda> A p. transition\<^sub>1 A a p) AA pp)
        (condition (map condition\<^sub>1 AA))"

    lemma combine_simps[simp]:
      "alphabet\<^sub>2 (combine AA) = \<Inter> (alphabet\<^sub>1 ` set AA)"
      "initial\<^sub>2 (combine AA) = map initial\<^sub>1 AA"
      "transition\<^sub>2 (combine AA) a pp = map2 (\<lambda> A p. transition\<^sub>1 A a p) AA pp"
      "condition\<^sub>2 (combine AA) = condition (map condition\<^sub>1 AA)"
      unfolding combine_def by auto

    (* TODO: get rid of indices, express this using stranspose *)
    lemma combine_trace_smap:
      assumes "length pp = length AA" "k < length AA"
      shows "smap (\<lambda> pp. pp ! k) (b.trace (combine AA) w pp) = a.trace (AA ! k) w (pp ! k)"
      using assms by (coinduction arbitrary: w pp) (force)
    lemma combine_nodes_length:
      assumes "pp \<in> b.nodes (combine AA)"
      shows "length pp = length AA"
      using assms by induct auto
    lemma combine_nodes[intro]:
      assumes "pp \<in> b.nodes (combine AA)" "k < length pp"
      shows "pp ! k \<in> a.nodes (AA ! k)"
      using assms by induct auto

    lemma combine_nodes_finite[intro]:
      assumes "list_all (finite \<circ> a.nodes) AA"
      shows "finite (b.nodes (combine AA))"
    proof (rule finite_subset)
      show "b.nodes (combine AA) \<subseteq> listset (map a.nodes AA)"
        by (force simp: listset_member list_all2_conv_all_nth combine_nodes_length)
      have "finite (listset (map a.nodes AA)) \<longleftrightarrow> list_all finite (map a.nodes AA)"
        by (rule listset_finite) (auto simp: list_all_iff)
      then show "finite (listset (map a.nodes AA))" using assms by (simp add: list.pred_map)
    qed
    lemma combine_nodes_card:
      assumes "list_all (finite \<circ> a.nodes) AA"
      shows "card (b.nodes (combine AA)) \<le> prod_list (map (card \<circ> a.nodes) AA)"
    proof -
      have "card (b.nodes (combine AA)) \<le> card (listset (map a.nodes AA))"
      proof (rule card_mono)
        have "finite (listset (map a.nodes AA)) \<longleftrightarrow> list_all finite (map a.nodes AA)"
          by (rule listset_finite) (auto simp: list_all_iff)
        then show "finite (listset (map a.nodes AA))" using assms by (simp add: list.pred_map)
        show "b.nodes (combine AA) \<subseteq> listset (map a.nodes AA)"
          by (force simp: listset_member list_all2_conv_all_nth combine_nodes_length)
      qed
      also have "\<dots> = prod_list (map (card \<circ> a.nodes) AA)" by simp
      finally show ?thesis by this
    qed

  end

  locale automaton_intersection_list_trace =
    automaton_combination_list
      automaton\<^sub>1 alphabet\<^sub>1 initial\<^sub>1 transition\<^sub>1 condition\<^sub>1
      automaton\<^sub>2 alphabet\<^sub>2 initial\<^sub>2 transition\<^sub>2 condition\<^sub>2 condition +
    a: automaton_trace automaton\<^sub>1 alphabet\<^sub>1 initial\<^sub>1 transition\<^sub>1 condition\<^sub>1 test\<^sub>1 +
    b: automaton_trace automaton\<^sub>2 alphabet\<^sub>2 initial\<^sub>2 transition\<^sub>2 condition\<^sub>2 test\<^sub>2
    for automaton\<^sub>1 :: "'label set \<Rightarrow> 'state \<Rightarrow> ('label, 'state) trans \<Rightarrow> 'condition\<^sub>1 \<Rightarrow> 'automaton\<^sub>1"
    and alphabet\<^sub>1 :: "'automaton\<^sub>1 \<Rightarrow> 'label set"
    and initial\<^sub>1 :: "'automaton\<^sub>1 \<Rightarrow> 'state"
    and transition\<^sub>1 :: "'automaton\<^sub>1 \<Rightarrow> ('label, 'state) trans"
    and condition\<^sub>1 :: "'automaton\<^sub>1 \<Rightarrow> 'condition\<^sub>1"
    and test\<^sub>1 :: "'condition\<^sub>1 \<Rightarrow> 'state stream \<Rightarrow> bool"
    and automaton\<^sub>2 :: "'label set \<Rightarrow> 'state list \<Rightarrow> ('label, 'state list) trans \<Rightarrow>
      'condition\<^sub>2 \<Rightarrow> 'automaton\<^sub>2"
    and alphabet\<^sub>2 :: "'automaton\<^sub>2 \<Rightarrow> 'label set"
    and initial\<^sub>2 :: "'automaton\<^sub>2 \<Rightarrow> 'state list"
    and transition\<^sub>2 :: "'automaton\<^sub>2 \<Rightarrow> ('label, 'state list) trans"
    and condition\<^sub>2 :: "'automaton\<^sub>2 \<Rightarrow> 'condition\<^sub>2"
    and test\<^sub>2 :: "'condition\<^sub>2 \<Rightarrow> 'state list stream \<Rightarrow> bool"
    and condition :: "'condition\<^sub>1 list \<Rightarrow> 'condition\<^sub>2"
    +
    assumes test[iff]: "test\<^sub>2 (condition cs) w \<longleftrightarrow>
      (\<forall> k < length cs. test\<^sub>1 (cs ! k) (smap (\<lambda> pp. pp ! k) w))"
  begin

    lemma combine_language[simp]: "b.language (combine AA) = \<Inter> (a.language ` set AA)"
      unfolding a.language_def b.language_def
      unfolding a.run_alt_def b.run_alt_def
      by (auto simp: combine_trace_smap iff: in_set_conv_nth)

  end

  locale automaton_union_list_trace =
    automaton_combination_list
      automaton\<^sub>1 alphabet\<^sub>1 initial\<^sub>1 transition\<^sub>1 condition\<^sub>1
      automaton\<^sub>2 alphabet\<^sub>2 initial\<^sub>2 transition\<^sub>2 condition\<^sub>2 condition +
    a: automaton_trace automaton\<^sub>1 alphabet\<^sub>1 initial\<^sub>1 transition\<^sub>1 condition\<^sub>1 test\<^sub>1 +
    b: automaton_trace automaton\<^sub>2 alphabet\<^sub>2 initial\<^sub>2 transition\<^sub>2 condition\<^sub>2 test\<^sub>2
    for automaton\<^sub>1 :: "'label set \<Rightarrow> 'state \<Rightarrow> ('label, 'state) trans \<Rightarrow> 'condition\<^sub>1 \<Rightarrow> 'automaton\<^sub>1"
    and alphabet\<^sub>1 :: "'automaton\<^sub>1 \<Rightarrow> 'label set"
    and initial\<^sub>1 :: "'automaton\<^sub>1 \<Rightarrow> 'state"
    and transition\<^sub>1 :: "'automaton\<^sub>1 \<Rightarrow> ('label, 'state) trans"
    and condition\<^sub>1 :: "'automaton\<^sub>1 \<Rightarrow> 'condition\<^sub>1"
    and test\<^sub>1 :: "'condition\<^sub>1 \<Rightarrow> 'state stream \<Rightarrow> bool"
    and automaton\<^sub>2 :: "'label set \<Rightarrow> 'state list \<Rightarrow> ('label, 'state list) trans \<Rightarrow>
      'condition\<^sub>2 \<Rightarrow> 'automaton\<^sub>2"
    and alphabet\<^sub>2 :: "'automaton\<^sub>2 \<Rightarrow> 'label set"
    and initial\<^sub>2 :: "'automaton\<^sub>2 \<Rightarrow> 'state list"
    and transition\<^sub>2 :: "'automaton\<^sub>2 \<Rightarrow> ('label, 'state list) trans"
    and condition\<^sub>2 :: "'automaton\<^sub>2 \<Rightarrow> 'condition\<^sub>2"
    and test\<^sub>2 :: "'condition\<^sub>2 \<Rightarrow> 'state list stream \<Rightarrow> bool"
    and condition :: "'condition\<^sub>1 list \<Rightarrow> 'condition\<^sub>2"
    +
    assumes test[iff]: "test\<^sub>2 (condition cs) w \<longleftrightarrow>
      (\<exists> k < length cs. test\<^sub>1 (cs ! k) (smap (\<lambda> pp. pp ! k) w))"
  begin

    lemma combine_language[simp]:
      assumes "\<Inter> (alphabet\<^sub>1 ` set AA) = \<Union> (alphabet\<^sub>1 ` set AA)"
      shows "b.language (combine AA) = \<Union> (a.language ` set AA)"
      using assms
      unfolding a.language_def b.language_def
      unfolding a.run_alt_def b.run_alt_def
      by (auto simp: combine_trace_smap iff: in_set_conv_nth) (metis INT_subset_iff in_set_conv_nth)

  end

end