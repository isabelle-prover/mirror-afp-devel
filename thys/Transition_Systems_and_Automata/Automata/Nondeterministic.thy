theory Nondeterministic
imports
  "../Transition_Systems/Transition_System"
  "../Transition_Systems/Transition_System_Extra"
  "../Transition_Systems/Transition_System_Construction"
  "../Basic/Degeneralization"
begin

  type_synonym ('label, 'state) trans = "'label \<Rightarrow> 'state \<Rightarrow> 'state set"

  locale automaton =
    fixes automaton :: "'label set \<Rightarrow> 'state set \<Rightarrow> ('label, 'state) trans \<Rightarrow> 'condition \<Rightarrow> 'automaton"
    fixes alphabet :: "'automaton \<Rightarrow> 'label set"
    fixes initial :: "'automaton \<Rightarrow> 'state set"
    fixes transition :: "'automaton \<Rightarrow> ('label, 'state) trans"
    fixes condition :: "'automaton \<Rightarrow> 'condition"
    assumes automaton[simp]: "automaton (alphabet A) (initial A) (transition A) (condition A) = A"
    assumes alphabet[simp]: "alphabet (automaton a i t c) = a"
    assumes initial[simp]: "initial (automaton a i t c) = i"
    assumes transition[simp]: "transition (automaton a i t c) = t"
    assumes condition[simp]: "condition (automaton a i t c) = c"
  begin

    sublocale transition_system_initial
      "\<lambda> a p. snd a" "\<lambda> a p. fst a \<in> alphabet A \<and> snd a \<in> transition A (fst a) p" "\<lambda> p. p \<in> initial A"
      for A
      defines path' = path and run' = run and reachable' = reachable and nodes' = nodes
      by this

    lemma states_alt_def: "states r p = map snd r" by (induct r arbitrary: p) (auto)
    lemma trace_alt_def: "trace r p = smap snd r" by (coinduction arbitrary: r p) (auto)

    lemma successors_alt_def: "successors A p = (\<Union> a \<in> alphabet A. transition A a p)" by auto

    lemma reachable_transition[intro]:
      assumes "a \<in> alphabet A" "q \<in> reachable A p" "r \<in> transition A a q"
      shows "r \<in> reachable A p"
      using reachable.execute assms by force
    lemma nodes_transition[intro]:
      assumes "a \<in> alphabet A" "p \<in> nodes A" "q \<in> transition A a p"
      shows "q \<in> nodes A"
      using nodes.execute assms by force

    lemma run_alphabet:
      assumes "run A (w ||| r) p"
      shows "w \<in> streams (alphabet A)"
      using assms by (coinduction arbitrary: w r p) (metis run.cases stream.map szip_smap szip_smap_fst)

    definition restrict :: "'automaton \<Rightarrow> 'automaton" where
      "restrict A \<equiv> automaton
        (alphabet A)
        (initial A)
        (\<lambda> a p. if a \<in> alphabet A then transition A a p else {})
        (condition A)"

    lemma restrict_simps[simp]:
      "alphabet (restrict A) = alphabet A"
      "initial (restrict A) = initial A"
      "transition (restrict A) a p = (if a \<in> alphabet A then transition A a p else {})"
      "condition (restrict A) = condition A"
      unfolding restrict_def by auto

    lemma restrict_path[simp]: "path (restrict A) = path A"
    proof (intro ext iffI)
      show "path A wr p" if "path (restrict A) wr p" for wr p using that by induct auto
      show "path (restrict A) wr p" if "path A wr p" for wr p using that by induct auto
    qed
    lemma restrict_run[simp]: "run (restrict A) = run A"
    proof (intro ext iffI)
      show "run A wr p" if "run (restrict A) wr p" for wr p using that by coinduct auto
      show "run (restrict A) wr p" if "run A wr p" for wr p using that by coinduct auto
    qed

  end

  (* TODO: create analogous thing for NFAs (automaton_path) *)
  (* TODO: adjust deterministic theory to the same test type *)
  locale automaton_run =
    automaton automaton alphabet initial transition condition
    for automaton :: "'label set \<Rightarrow> 'state set \<Rightarrow> ('label, 'state) trans \<Rightarrow> 'condition \<Rightarrow> 'automaton"
    and alphabet :: "'automaton \<Rightarrow> 'label set"
    and initial :: "'automaton \<Rightarrow> 'state set"
    and transition :: "'automaton \<Rightarrow> ('label, 'state) trans"
    and condition :: "'automaton \<Rightarrow> 'condition"
    +
    fixes test :: "'condition \<Rightarrow> 'label stream \<Rightarrow> 'state stream \<Rightarrow> 'state \<Rightarrow> bool"
  begin

    definition language :: "'automaton \<Rightarrow> 'label stream set" where
      "language A \<equiv> {w |w r p. p \<in> initial A \<and> run A (w ||| r) p \<and> test (condition A) w r p}"

    lemma language[intro]:
      assumes "p \<in> initial A" "run A (w ||| r) p" "test (condition A) w r p"
      shows "w \<in> language A"
      using assms unfolding language_def by auto
    lemma language_elim[elim]:
      assumes "w \<in> language A"
      obtains r p
      where "p \<in> initial A" "run A (w ||| r) p" "test (condition A) w r p"
      using assms unfolding language_def by auto

    lemma language_alphabet: "language A \<subseteq> streams (alphabet A)" by (auto dest: run_alphabet)

    lemma restrict_language[simp]: "language (restrict A) = language A" by force

  end

  locale automaton_degeneralization =
    a: automaton automaton\<^sub>1 alphabet\<^sub>1 initial\<^sub>1 transition\<^sub>1 condition\<^sub>1 +
    b: automaton automaton\<^sub>2 alphabet\<^sub>2 initial\<^sub>2 transition\<^sub>2 condition\<^sub>2
    for automaton\<^sub>1 :: "'label set \<Rightarrow> 'state set \<Rightarrow> ('label, 'state) trans \<Rightarrow> 'state pred gen \<Rightarrow> 'automaton\<^sub>1"
    and alphabet\<^sub>1 :: "'automaton\<^sub>1 \<Rightarrow> 'label set"
    and initial\<^sub>1 :: "'automaton\<^sub>1 \<Rightarrow> 'state set"
    and transition\<^sub>1 :: "'automaton\<^sub>1 \<Rightarrow> ('label, 'state) trans"
    and condition\<^sub>1 :: "'automaton\<^sub>1 \<Rightarrow> 'state pred gen"
    and automaton\<^sub>2 :: "'label set \<Rightarrow> 'state degen set \<Rightarrow> ('label, 'state degen) trans \<Rightarrow> 'state degen pred \<Rightarrow> 'automaton\<^sub>2"
    and alphabet\<^sub>2 :: "'automaton\<^sub>2 \<Rightarrow> 'label set"
    and initial\<^sub>2 :: "'automaton\<^sub>2 \<Rightarrow> 'state degen set"
    and transition\<^sub>2 :: "'automaton\<^sub>2 \<Rightarrow> ('label, 'state degen) trans"
    and condition\<^sub>2 :: "'automaton\<^sub>2 \<Rightarrow> 'state degen pred"
  begin

    definition degeneralize :: "'automaton\<^sub>1 \<Rightarrow> 'automaton\<^sub>2" where
      "degeneralize A \<equiv> automaton\<^sub>2
        (alphabet\<^sub>1 A)
        (initial\<^sub>1 A \<times> {0})
        (\<lambda> a (p, k). transition\<^sub>1 A a p \<times> {count (condition\<^sub>1 A) p k})
        (degen (condition\<^sub>1 A))"

    lemma degeneralize_simps[simp]:
      "alphabet\<^sub>2 (degeneralize A) = alphabet\<^sub>1 A"
      "initial\<^sub>2 (degeneralize A) = initial\<^sub>1 A \<times> {0}"
      "transition\<^sub>2 (degeneralize A) a (p, k) = transition\<^sub>1 A a p \<times> {count (condition\<^sub>1 A) p k}"
      "condition\<^sub>2 (degeneralize A) = degen (condition\<^sub>1 A)"
      unfolding degeneralize_def by auto

    lemma run_degeneralize:
      assumes "a.run A (w ||| r) p"
      shows "b.run (degeneralize A) (w ||| r ||| sscan (count (condition\<^sub>1 A)) (p ## r) k) (p, k)"
      using assms by (coinduction arbitrary: w r p k) (force elim: a.run.cases)
    lemma degeneralize_run:
      assumes "b.run (degeneralize A) (w ||| rs) pk"
      obtains r s p k
      where "rs = r ||| s" "pk = (p, k)" "a.run A (w ||| r) p" "s = sscan (count (condition\<^sub>1 A)) (p ## r) k"
    proof
      show "rs = smap fst rs ||| smap snd rs" "pk = (fst pk, snd pk)" by auto
      show "a.run A (w ||| smap fst rs) (fst pk)"
        using assms by (coinduction arbitrary: w rs pk) (force elim: b.run.cases)
      show "smap snd rs = sscan (count (condition\<^sub>1 A)) (fst pk ## smap fst rs) (snd pk)"
        using assms by (coinduction arbitrary: w rs pk) (force elim: b.run.cases)
    qed

    lemma degeneralize_nodes:
      "b.nodes (degeneralize A) \<subseteq> a.nodes A \<times> insert 0 {0 ..< length (condition\<^sub>1 A)}"
    proof
      fix pk
      assume "pk \<in> b.nodes (degeneralize A)"
      then show "pk \<in> a.nodes A \<times> insert 0 {0 ..< length (condition\<^sub>1 A)}"
        by (induct) (force, cases "condition\<^sub>1 A = []", auto)
    qed
    lemma nodes_degeneralize: "a.nodes A \<subseteq> fst ` b.nodes (degeneralize A)"
    proof
      fix p
      assume "p \<in> a.nodes A"
      then show "p \<in> fst ` b.nodes (degeneralize A)"
      proof induct
        case (initial p)
        have "(p, 0) \<in> b.nodes (degeneralize A)" using initial by auto
        then show ?case using image_iff fst_conv by force
      next
        case (execute p aq)
        obtain k where "(p, k) \<in> b.nodes (degeneralize A)" using execute(2) by auto
        then have "(snd aq, count (condition\<^sub>1 A) p k) \<in> b.nodes (degeneralize A)"
          using execute(3) by auto
        then show ?case using image_iff snd_conv by force
      qed
    qed

    lemma degeneralize_nodes_finite[iff]: "finite (b.nodes (degeneralize A)) \<longleftrightarrow> finite (a.nodes A)"
    proof
      show "finite (a.nodes A)" if "finite (b.nodes (degeneralize A))"
        using finite_subset nodes_degeneralize that by blast
      show "finite (b.nodes (degeneralize A))" if "finite (a.nodes A)"
        using finite_subset degeneralize_nodes that by blast
    qed

  end

  locale automaton_degeneralization_run =
    automaton_degeneralization
      automaton\<^sub>1 alphabet\<^sub>1 initial\<^sub>1 transition\<^sub>1 condition\<^sub>1
      automaton\<^sub>2 alphabet\<^sub>2 initial\<^sub>2 transition\<^sub>2 condition\<^sub>2 +
    a: automaton_run automaton\<^sub>1 alphabet\<^sub>1 initial\<^sub>1 transition\<^sub>1 condition\<^sub>1 test\<^sub>1 +
    b: automaton_run automaton\<^sub>2 alphabet\<^sub>2 initial\<^sub>2 transition\<^sub>2 condition\<^sub>2 test\<^sub>2
    for automaton\<^sub>1 :: "'label set \<Rightarrow> 'state set \<Rightarrow> ('label, 'state) trans \<Rightarrow> 'state pred gen \<Rightarrow> 'automaton\<^sub>1"
    and alphabet\<^sub>1 :: "'automaton\<^sub>1 \<Rightarrow> 'label set"
    and initial\<^sub>1 :: "'automaton\<^sub>1 \<Rightarrow> 'state set"
    and transition\<^sub>1 :: "'automaton\<^sub>1 \<Rightarrow> ('label, 'state) trans"
    and condition\<^sub>1 :: "'automaton\<^sub>1 \<Rightarrow> 'state pred gen"
    and test\<^sub>1 :: "'state pred gen \<Rightarrow> 'label stream \<Rightarrow> 'state stream \<Rightarrow> 'state \<Rightarrow> bool"
    and automaton\<^sub>2 :: "'label set \<Rightarrow> 'state degen set \<Rightarrow> ('label, 'state degen) trans \<Rightarrow> 'state degen pred \<Rightarrow> 'automaton\<^sub>2"
    and alphabet\<^sub>2 :: "'automaton\<^sub>2 \<Rightarrow> 'label set"
    and initial\<^sub>2 :: "'automaton\<^sub>2 \<Rightarrow> 'state degen set"
    and transition\<^sub>2 :: "'automaton\<^sub>2 \<Rightarrow> ('label, 'state degen) trans"
    and condition\<^sub>2 :: "'automaton\<^sub>2 \<Rightarrow> 'state degen pred"
    and test\<^sub>2 :: "'state degen pred \<Rightarrow> 'label stream \<Rightarrow> 'state degen stream \<Rightarrow> 'state degen \<Rightarrow> bool"
    +
    assumes test[iff]: "test\<^sub>2 (degen cs) w (r ||| sscan (count cs) (p ## r) k) (p, k) \<longleftrightarrow> test\<^sub>1 cs w r p"
  begin

    lemma degeneralize_language[simp]: "b.language (degeneralize A) = a.language A"
      unfolding a.language_def b.language_def by (auto dest: run_degeneralize elim!: degeneralize_run)

  end

  locale automaton_intersection =
    a: automaton automaton\<^sub>1 alphabet\<^sub>1 initial\<^sub>1 transition\<^sub>1 condition\<^sub>1 +
    b: automaton automaton\<^sub>2 alphabet\<^sub>2 initial\<^sub>2 transition\<^sub>2 condition\<^sub>2 +
    c: automaton automaton\<^sub>3 alphabet\<^sub>3 initial\<^sub>3 transition\<^sub>3 condition\<^sub>3
    for automaton\<^sub>1 :: "'label set \<Rightarrow> 'state\<^sub>1 set \<Rightarrow> ('label, 'state\<^sub>1) trans \<Rightarrow> 'condition\<^sub>1 \<Rightarrow> 'automaton\<^sub>1"
    and alphabet\<^sub>1 :: "'automaton\<^sub>1 \<Rightarrow> 'label set"
    and initial\<^sub>1 :: "'automaton\<^sub>1 \<Rightarrow> 'state\<^sub>1 set"
    and transition\<^sub>1 :: "'automaton\<^sub>1 \<Rightarrow> ('label, 'state\<^sub>1) trans"
    and condition\<^sub>1 :: "'automaton\<^sub>1 \<Rightarrow> 'condition\<^sub>1"
    and automaton\<^sub>2 :: "'label set \<Rightarrow> 'state\<^sub>2 set \<Rightarrow> ('label, 'state\<^sub>2) trans \<Rightarrow> 'condition\<^sub>2 \<Rightarrow> 'automaton\<^sub>2"
    and alphabet\<^sub>2 :: "'automaton\<^sub>2 \<Rightarrow> 'label set"
    and initial\<^sub>2 :: "'automaton\<^sub>2 \<Rightarrow> 'state\<^sub>2 set"
    and transition\<^sub>2 :: "'automaton\<^sub>2 \<Rightarrow> ('label, 'state\<^sub>2) trans"
    and condition\<^sub>2 :: "'automaton\<^sub>2 \<Rightarrow> 'condition\<^sub>2"
    and automaton\<^sub>3 :: "'label set \<Rightarrow> ('state\<^sub>1 \<times> 'state\<^sub>2) set \<Rightarrow> ('label, 'state\<^sub>1 \<times> 'state\<^sub>2) trans \<Rightarrow>
      'condition\<^sub>3 \<Rightarrow> 'automaton\<^sub>3"
    and alphabet\<^sub>3 :: "'automaton\<^sub>3 \<Rightarrow> 'label set"
    and initial\<^sub>3 :: "'automaton\<^sub>3 \<Rightarrow> ('state\<^sub>1 \<times> 'state\<^sub>2) set"
    and transition\<^sub>3 :: "'automaton\<^sub>3 \<Rightarrow> ('label, 'state\<^sub>1 \<times> 'state\<^sub>2) trans"
    and condition\<^sub>3 :: "'automaton\<^sub>3 \<Rightarrow> 'condition\<^sub>3"
    +
    fixes condition :: "'condition\<^sub>1 \<Rightarrow> 'condition\<^sub>2 \<Rightarrow> 'condition\<^sub>3"
  begin

    definition intersect :: "'automaton\<^sub>1 \<Rightarrow> 'automaton\<^sub>2 \<Rightarrow> 'automaton\<^sub>3" where
      "intersect A B \<equiv> automaton\<^sub>3
        (alphabet\<^sub>1 A \<inter> alphabet\<^sub>2 B)
        (initial\<^sub>1 A \<times> initial\<^sub>2 B)
        (\<lambda> a (p, q). transition\<^sub>1 A a p \<times> transition\<^sub>2 B a q)
        (condition (condition\<^sub>1 A) (condition\<^sub>2 B))"

    lemma intersect_simps[simp]:
      "alphabet\<^sub>3 (intersect A B) = alphabet\<^sub>1 A \<inter> alphabet\<^sub>2 B"
      "initial\<^sub>3 (intersect A B) = initial\<^sub>1 A \<times> initial\<^sub>2 B"
      "transition\<^sub>3 (intersect A B) a (p, q) = transition\<^sub>1 A a p \<times> transition\<^sub>2 B a q"
      "condition\<^sub>3 (intersect A B) = condition (condition\<^sub>1 A) (condition\<^sub>2 B)"
      unfolding intersect_def by auto

    lemma intersect_path[iff]:
      assumes "length w = length r" "length r = length s"
      shows "c.path (intersect A B) (w || r || s) (p, q) \<longleftrightarrow>
        a.path A (w || r) p \<and> b.path B (w || s) q"
      using assms by (induct arbitrary: p q rule: list_induct3) (auto)
    lemma intersect_run[iff]: "c.run (intersect A B) (w ||| r ||| s) (p, q) \<longleftrightarrow>
      a.run A (w ||| r) p \<and> b.run B (w ||| s) q"
    proof safe
      show "a.run A (w ||| r) p" if "c.run (intersect A B) (w ||| r ||| s) (p, q)"
        using that by (coinduction arbitrary: w r s p q) (force elim: c.run.cases)
      show "b.run B (w ||| s) q" if "c.run (intersect A B) (w ||| r ||| s) (p, q)"
        using that by (coinduction arbitrary: w r s p q) (force elim: c.run.cases)
      show "c.run (intersect A B) (w ||| r ||| s) (p, q)" if "a.run A (w ||| r) p" "b.run B (w ||| s) q"
        using that by (coinduction arbitrary: w r s p q) (auto elim: a.run.cases b.run.cases)
    qed

    lemma intersect_nodes: "c.nodes (intersect A B) \<subseteq> a.nodes A \<times> b.nodes B"
    proof
      fix pq
      assume "pq \<in> c.nodes (intersect A B)"
      then show "pq \<in> a.nodes A \<times> b.nodes B" by induct auto
    qed

    lemma intersect_nodes_finite[intro]:
      assumes "finite (a.nodes A)" "finite (b.nodes B)"
      shows "finite (c.nodes (intersect A B))"
      using finite_subset intersect_nodes assms by blast

  end

  locale automaton_intersection_run =
    automaton_intersection
      automaton\<^sub>1 alphabet\<^sub>1 initial\<^sub>1 transition\<^sub>1 condition\<^sub>1
      automaton\<^sub>2 alphabet\<^sub>2 initial\<^sub>2 transition\<^sub>2 condition\<^sub>2
      automaton\<^sub>3 alphabet\<^sub>3 initial\<^sub>3 transition\<^sub>3 condition\<^sub>3 condition +
    a: automaton_run automaton\<^sub>1 alphabet\<^sub>1 initial\<^sub>1 transition\<^sub>1 condition\<^sub>1 test\<^sub>1 +
    b: automaton_run automaton\<^sub>2 alphabet\<^sub>2 initial\<^sub>2 transition\<^sub>2 condition\<^sub>2 test\<^sub>2 +
    c: automaton_run automaton\<^sub>3 alphabet\<^sub>3 initial\<^sub>3 transition\<^sub>3 condition\<^sub>3 test\<^sub>3
    for automaton\<^sub>1 :: "'label set \<Rightarrow> 'state\<^sub>1 set \<Rightarrow> ('label, 'state\<^sub>1) trans \<Rightarrow> 'condition\<^sub>1 \<Rightarrow> 'automaton\<^sub>1"
    and alphabet\<^sub>1 :: "'automaton\<^sub>1 \<Rightarrow> 'label set"
    and initial\<^sub>1 :: "'automaton\<^sub>1 \<Rightarrow> 'state\<^sub>1 set"
    and transition\<^sub>1 :: "'automaton\<^sub>1 \<Rightarrow> ('label, 'state\<^sub>1) trans"
    and condition\<^sub>1 :: "'automaton\<^sub>1 \<Rightarrow> 'condition\<^sub>1"
    and test\<^sub>1 :: "'condition\<^sub>1 \<Rightarrow> 'label stream \<Rightarrow> 'state\<^sub>1 stream \<Rightarrow> 'state\<^sub>1 \<Rightarrow> bool"
    and automaton\<^sub>2 :: "'label set \<Rightarrow> 'state\<^sub>2 set \<Rightarrow> ('label, 'state\<^sub>2) trans \<Rightarrow> 'condition\<^sub>2 \<Rightarrow> 'automaton\<^sub>2"
    and alphabet\<^sub>2 :: "'automaton\<^sub>2 \<Rightarrow> 'label set"
    and initial\<^sub>2 :: "'automaton\<^sub>2 \<Rightarrow> 'state\<^sub>2 set"
    and transition\<^sub>2 :: "'automaton\<^sub>2 \<Rightarrow> ('label, 'state\<^sub>2) trans"
    and condition\<^sub>2 :: "'automaton\<^sub>2 \<Rightarrow> 'condition\<^sub>2"
    and test\<^sub>2 :: "'condition\<^sub>2 \<Rightarrow> 'label stream \<Rightarrow> 'state\<^sub>2 stream \<Rightarrow> 'state\<^sub>2 \<Rightarrow> bool"
    and automaton\<^sub>3 :: "'label set \<Rightarrow> ('state\<^sub>1 \<times> 'state\<^sub>2) set \<Rightarrow> ('label, 'state\<^sub>1 \<times> 'state\<^sub>2) trans \<Rightarrow>
      'condition\<^sub>3 \<Rightarrow> 'automaton\<^sub>3"
    and alphabet\<^sub>3 :: "'automaton\<^sub>3 \<Rightarrow> 'label set"
    and initial\<^sub>3 :: "'automaton\<^sub>3 \<Rightarrow> ('state\<^sub>1 \<times> 'state\<^sub>2) set"
    and transition\<^sub>3 :: "'automaton\<^sub>3 \<Rightarrow> ('label, 'state\<^sub>1 \<times> 'state\<^sub>2) trans"
    and condition\<^sub>3 :: "'automaton\<^sub>3 \<Rightarrow> 'condition\<^sub>3"
    and test\<^sub>3 :: "'condition\<^sub>3 \<Rightarrow> 'label stream \<Rightarrow> ('state\<^sub>1 \<times> 'state\<^sub>2) stream \<Rightarrow> 'state\<^sub>1 \<times> 'state\<^sub>2 \<Rightarrow> bool"
    and condition :: "'condition\<^sub>1 \<Rightarrow> 'condition\<^sub>2 \<Rightarrow> 'condition\<^sub>3"
    +
    assumes test[iff]: "test\<^sub>3 (condition c\<^sub>1 c\<^sub>2) w (u ||| v) (p, q) \<longleftrightarrow> test\<^sub>1 c\<^sub>1 w u p \<and> test\<^sub>2 c\<^sub>2 w v q"
  begin

    lemma intersect_language[simp]: "c.language (intersect A B) = a.language A \<inter> b.language B"
      unfolding a.language_def b.language_def c.language_def by (fastforce iff: split_szip)

  end

  locale automaton_intersection_list =
    a: automaton automaton\<^sub>1 alphabet\<^sub>1 initial\<^sub>1 transition\<^sub>1 condition\<^sub>1 +
    b: automaton automaton\<^sub>2 alphabet\<^sub>2 initial\<^sub>2 transition\<^sub>2 condition\<^sub>2
    for automaton\<^sub>1 :: "'label set \<Rightarrow> 'state set \<Rightarrow> ('label, 'state) trans \<Rightarrow> 'condition\<^sub>1 \<Rightarrow> 'automaton\<^sub>1"
    and alphabet\<^sub>1 :: "'automaton\<^sub>1 \<Rightarrow> 'label set"
    and initial\<^sub>1 :: "'automaton\<^sub>1 \<Rightarrow> 'state set"
    and transition\<^sub>1 :: "'automaton\<^sub>1 \<Rightarrow> ('label, 'state) trans"
    and condition\<^sub>1 :: "'automaton\<^sub>1 \<Rightarrow> 'condition\<^sub>1"
    and automaton\<^sub>2 :: "'label set \<Rightarrow> 'state list set \<Rightarrow> ('label, 'state list) trans \<Rightarrow> 'condition\<^sub>2 \<Rightarrow> 'automaton\<^sub>2"
    and alphabet\<^sub>2 :: "'automaton\<^sub>2 \<Rightarrow> 'label set"
    and initial\<^sub>2 :: "'automaton\<^sub>2 \<Rightarrow> 'state list set"
    and transition\<^sub>2 :: "'automaton\<^sub>2 \<Rightarrow> ('label, 'state list) trans"
    and condition\<^sub>2 :: "'automaton\<^sub>2 \<Rightarrow> 'condition\<^sub>2"
    +
    fixes condition :: "'condition\<^sub>1 list \<Rightarrow> 'condition\<^sub>2"
  begin

    definition intersect :: "'automaton\<^sub>1 list \<Rightarrow> 'automaton\<^sub>2" where
      "intersect AA \<equiv> automaton\<^sub>2
        (\<Inter> (alphabet\<^sub>1 ` set AA))
        (listset (map initial\<^sub>1 AA))
        (\<lambda> a ps. listset (map2 (\<lambda> A p. transition\<^sub>1 A a p) AA ps))
        (condition (map condition\<^sub>1 AA))"

    lemma intersect_simps[simp]:
      "alphabet\<^sub>2 (intersect AA) = \<Inter> (alphabet\<^sub>1 ` set AA)"
      "initial\<^sub>2 (intersect AA) = listset (map initial\<^sub>1 AA)"
      "transition\<^sub>2 (intersect AA) a ps = listset (map2 (\<lambda> A p. transition\<^sub>1 A a p) AA ps)"
      "condition\<^sub>2 (intersect AA) = condition (map condition\<^sub>1 AA)"
      unfolding intersect_def by auto

    lemma intersect_run_length:
      assumes "length ps = length AA"
      assumes "b.run (intersect AA) (w ||| r) ps"
      assumes "qs \<in> sset r"
      shows "length qs = length AA"
    proof -
      have "pred_stream (\<lambda> qs. length qs = length AA) r"
        using assms(1, 2) by (coinduction arbitrary: w r ps)
          (force elim: b.run.cases simp: listset_member list_all2_conv_all_nth)
      then show ?thesis using assms(3) unfolding stream.pred_set by auto
    qed
    lemma intersect_run_stranspose:
      assumes "length ps = length AA"
      assumes "b.run (intersect AA) (w ||| r) ps"
      obtains rs where "r = stranspose rs" "length rs = length AA"
    proof
      define rs where "rs \<equiv> map (\<lambda> k. smap (\<lambda> ps. ps ! k) r) [0 ..< length AA]"
      have "length qs = length AA" if "qs \<in> sset r" for qs using intersect_run_length assms that by this
      then show "r = stranspose rs"
        unfolding rs_def by (coinduction arbitrary: r) (auto intro: nth_equalityI simp: comp_def)
      show "length rs = length AA" unfolding rs_def by auto
    qed

    lemma run_intersect:
      assumes "length rs = length AA" "length ps = length AA"
      assumes "\<And> k. k < length AA \<Longrightarrow> a.run (AA ! k) (w ||| rs ! k) (ps ! k)"
      shows "b.run (intersect AA) (w ||| stranspose rs) ps"
    using assms
    proof (coinduction arbitrary: w rs ps)
      case (run ap r)
      then show ?case
      proof (intro conjI exI)
        show "fst ap \<in> alphabet\<^sub>2 (intersect AA)"
          using run by (force elim: a.run.cases simp: set_conv_nth)
        show "snd ap \<in> transition\<^sub>2 (intersect AA) (fst ap) ps"
          using run by (force elim: a.run.cases simp: listset_member list_all2_conv_all_nth)
        show "\<forall> k < length AA. a.run' (AA ! k) (stl w ||| map stl rs ! k) (map shd rs ! k)"
          using run by (force elim: a.run.cases)
      qed auto
    qed
    lemma intersect_run:
      assumes "length rs = length AA" "length ps = length AA"
      assumes "b.run (intersect AA) (w ||| stranspose rs) ps"
      shows "k < length AA \<Longrightarrow> a.run (AA ! k) (w ||| rs ! k) (ps ! k)"
    using assms
    proof (coinduction arbitrary: w rs ps)
      case (run ap wr)
      then show ?case
      proof (intro exI conjI)
        show "fst ap \<in> alphabet\<^sub>1 (AA ! k)"
          using run by (force elim: b.run.cases)
        show "snd ap \<in> transition\<^sub>1 (AA ! k) (fst ap) (ps ! k)"
          using run by (force elim: b.run.cases simp: listset_member list_all2_conv_all_nth)
        show "b.run' (intersect AA) (stl w ||| stranspose (map stl rs)) (shd (stranspose rs))"
          using run by (force elim: b.run.cases)
      qed auto
    qed

    lemma intersect_nodes: "b.nodes (intersect AA) \<subseteq> listset (map a.nodes AA)"
    proof
      show "ps \<in> listset (map a.nodes AA)" if "ps \<in> b.nodes (intersect AA)" for ps
        using that by (induct) (auto 0 3 simp: listset_member list_all2_conv_all_nth)
    qed

    lemma intersect_nodes_finite[intro]:
      assumes "list_all (finite \<circ> a.nodes) AA"
      shows "finite (b.nodes (intersect AA))"
    proof (rule finite_subset)
      show "b.nodes (intersect AA) \<subseteq> listset (map a.nodes AA)" using intersect_nodes by this
      show "finite (listset (map a.nodes AA))" using list.pred_map assms by auto
    qed

  end

  locale automaton_intersection_list_run =
    automaton_intersection_list
      automaton\<^sub>1 alphabet\<^sub>1 initial\<^sub>1 transition\<^sub>1 condition\<^sub>1
      automaton\<^sub>2 alphabet\<^sub>2 initial\<^sub>2 transition\<^sub>2 condition\<^sub>2 condition +
    a: automaton_run automaton\<^sub>1 alphabet\<^sub>1 initial\<^sub>1 transition\<^sub>1 condition\<^sub>1 test\<^sub>1 +
    b: automaton_run automaton\<^sub>2 alphabet\<^sub>2 initial\<^sub>2 transition\<^sub>2 condition\<^sub>2 test\<^sub>2
    for automaton\<^sub>1 :: "'label set \<Rightarrow> 'state set \<Rightarrow> ('label, 'state) trans \<Rightarrow> 'condition\<^sub>1 \<Rightarrow> 'automaton\<^sub>1"
    and alphabet\<^sub>1 :: "'automaton\<^sub>1 \<Rightarrow> 'label set"
    and initial\<^sub>1 :: "'automaton\<^sub>1 \<Rightarrow> 'state set"
    and transition\<^sub>1 :: "'automaton\<^sub>1 \<Rightarrow> ('label, 'state) trans"
    and condition\<^sub>1 :: "'automaton\<^sub>1 \<Rightarrow> 'condition\<^sub>1"
    and test\<^sub>1 :: "'condition\<^sub>1 \<Rightarrow> 'label stream \<Rightarrow> 'state stream \<Rightarrow> 'state \<Rightarrow> bool"
    and automaton\<^sub>2 :: "'label set \<Rightarrow> 'state list set \<Rightarrow> ('label, 'state list) trans \<Rightarrow> 'condition\<^sub>2 \<Rightarrow> 'automaton\<^sub>2"
    and alphabet\<^sub>2 :: "'automaton\<^sub>2 \<Rightarrow> 'label set"
    and initial\<^sub>2 :: "'automaton\<^sub>2 \<Rightarrow> 'state list set"
    and transition\<^sub>2 :: "'automaton\<^sub>2 \<Rightarrow> ('label, 'state list) trans"
    and condition\<^sub>2 :: "'automaton\<^sub>2 \<Rightarrow> 'condition\<^sub>2"
    and test\<^sub>2 :: "'condition\<^sub>2 \<Rightarrow> 'label stream \<Rightarrow> 'state list stream \<Rightarrow> 'state list \<Rightarrow> bool"
    and condition :: "'condition\<^sub>1 list \<Rightarrow> 'condition\<^sub>2"
    +
    assumes test[iff]: "length rs = length cs \<Longrightarrow> length ps = length cs \<Longrightarrow>
      test\<^sub>2 (condition cs) w (stranspose rs) ps \<longleftrightarrow> list_all (\<lambda> (c, r, p). test\<^sub>1 c w r p) (cs || rs || ps)"
  begin

    lemma intersect_language[simp]: "b.language (intersect AA) = \<Inter> (a.language ` set AA)"
    proof safe
      fix A w
      assume 1: "w \<in> b.language (intersect AA)" "A \<in> set AA"
      obtain r ps where 2:
        "ps \<in> initial\<^sub>2 (intersect AA)"
        "b.run (intersect AA) (w ||| r) ps"
        "test\<^sub>2 (condition\<^sub>2 (intersect AA)) w r ps"
        using 1(1) by auto
      have 3: "length ps = length AA" using 2(1) by (simp add: listset_member list_all2_conv_all_nth)
      obtain rs where 4: "r = stranspose rs" "length rs = length AA"
        using intersect_run_stranspose 3 2(2) by this
      obtain k where 5: "k < length AA" "A = AA ! k" using 1(2) unfolding set_conv_nth by auto
      show "w \<in> a.language A"
      proof
        show "ps ! k \<in> initial\<^sub>1 A" using 2(1) 5 by (auto simp: listset_member list_all2_conv_all_nth)
        show "a.run A (w ||| rs ! k) (ps ! k)" using 2(2) 3 4 5 by (auto intro: intersect_run)
        show "test\<^sub>1 (condition\<^sub>1 A) w (rs ! k) (ps ! k)" using 2(3) 3 4 5 by (simp add: list_all_length)
      qed
    next
      fix w
      assume 1: "w \<in> \<Inter> (a.language ` set AA)"
      have 2: "\<forall> A \<in> set AA. \<exists> r p. p \<in> initial\<^sub>1 A \<and> a.run A (w ||| r) p \<and> test\<^sub>1 (condition\<^sub>1 A) w r p"
        using 1 by blast
      obtain rs ps where 3:
        "length rs = length AA" "length ps = length AA"
        "\<And> k. k < length AA \<Longrightarrow> ps ! k \<in> initial\<^sub>1 (AA ! k)"
        "\<And> k. k < length AA \<Longrightarrow> a.run (AA ! k) (w ||| rs ! k) (ps ! k)"
        "\<And> k. k < length AA \<Longrightarrow> test\<^sub>1 (condition\<^sub>1 (AA ! k)) w (rs ! k) (ps ! k)"
        using 2
        unfolding Ball_set list_choice_zip list_choice_pair
        unfolding list.pred_set set_conv_nth
        by force
      show "w \<in> b.language (intersect AA)"
      proof
        show "ps \<in> initial\<^sub>2 (intersect AA)" using 3 by (auto simp: listset_member list_all2_conv_all_nth)
        show "b.run (intersect AA) (w ||| stranspose rs) ps" using 3 by (auto intro: run_intersect)
        show "test\<^sub>2 (condition\<^sub>2 (intersect AA)) w (stranspose rs) ps" using 3 by (auto simp: list_all_length)
      qed
    qed

  end

  locale automaton_union =
    a: automaton automaton\<^sub>1 alphabet\<^sub>1 initial\<^sub>1 transition\<^sub>1 condition\<^sub>1 +
    b: automaton automaton\<^sub>2 alphabet\<^sub>2 initial\<^sub>2 transition\<^sub>2 condition\<^sub>2 +
    c: automaton automaton\<^sub>3 alphabet\<^sub>3 initial\<^sub>3 transition\<^sub>3 condition\<^sub>3
    for automaton\<^sub>1 :: "'label set \<Rightarrow> 'state\<^sub>1 set \<Rightarrow> ('label, 'state\<^sub>1) trans \<Rightarrow> 'condition\<^sub>1 \<Rightarrow> 'automaton\<^sub>1"
    and alphabet\<^sub>1 :: "'automaton\<^sub>1 \<Rightarrow> 'label set"
    and initial\<^sub>1 :: "'automaton\<^sub>1 \<Rightarrow> 'state\<^sub>1 set"
    and transition\<^sub>1 :: "'automaton\<^sub>1 \<Rightarrow> ('label, 'state\<^sub>1) trans"
    and condition\<^sub>1 :: "'automaton\<^sub>1 \<Rightarrow> 'condition\<^sub>1"
    and automaton\<^sub>2 :: "'label set \<Rightarrow> 'state\<^sub>2 set \<Rightarrow> ('label, 'state\<^sub>2) trans \<Rightarrow> 'condition\<^sub>2 \<Rightarrow> 'automaton\<^sub>2"
    and alphabet\<^sub>2 :: "'automaton\<^sub>2 \<Rightarrow> 'label set"
    and initial\<^sub>2 :: "'automaton\<^sub>2 \<Rightarrow> 'state\<^sub>2 set"
    and transition\<^sub>2 :: "'automaton\<^sub>2 \<Rightarrow> ('label, 'state\<^sub>2) trans"
    and condition\<^sub>2 :: "'automaton\<^sub>2 \<Rightarrow> 'condition\<^sub>2"
    and automaton\<^sub>3 :: "'label set \<Rightarrow> ('state\<^sub>1 + 'state\<^sub>2) set \<Rightarrow> ('label, 'state\<^sub>1 + 'state\<^sub>2) trans \<Rightarrow>
      'condition\<^sub>3 \<Rightarrow> 'automaton\<^sub>3"
    and alphabet\<^sub>3 :: "'automaton\<^sub>3 \<Rightarrow> 'label set"
    and initial\<^sub>3 :: "'automaton\<^sub>3 \<Rightarrow> ('state\<^sub>1 + 'state\<^sub>2) set"
    and transition\<^sub>3 :: "'automaton\<^sub>3 \<Rightarrow> ('label, 'state\<^sub>1 + 'state\<^sub>2) trans"
    and condition\<^sub>3 :: "'automaton\<^sub>3 \<Rightarrow> 'condition\<^sub>3"
    +
    fixes condition :: "'condition\<^sub>1 \<Rightarrow> 'condition\<^sub>2 \<Rightarrow> 'condition\<^sub>3"
  begin

    definition union :: "'automaton\<^sub>1 \<Rightarrow> 'automaton\<^sub>2 \<Rightarrow> 'automaton\<^sub>3" where
      "union A B \<equiv> automaton\<^sub>3
        (alphabet\<^sub>1 A \<union> alphabet\<^sub>2 B)
        (initial\<^sub>1 A <+> initial\<^sub>2 B)
        (\<lambda> a. \<lambda> Inl p \<Rightarrow> Inl ` transition\<^sub>1 A a p | Inr q \<Rightarrow> Inr ` transition\<^sub>2 B a q)
        (condition (condition\<^sub>1 A) (condition\<^sub>2 B))"

    lemma union_simps[simp]:
      "alphabet\<^sub>3 (union A B) = alphabet\<^sub>1 A \<union> alphabet\<^sub>2 B"
      "initial\<^sub>3 (union A B) = initial\<^sub>1 A <+> initial\<^sub>2 B"
      "transition\<^sub>3 (union A B) a (Inl p) = Inl ` transition\<^sub>1 A a p"
      "transition\<^sub>3 (union A B) a (Inr q) = Inr ` transition\<^sub>2 B a q"
      "condition\<^sub>3 (union A B) = condition (condition\<^sub>1 A) (condition\<^sub>2 B)"
      unfolding union_def by auto

    lemma run_union_a:
      assumes "a.run A (w ||| r) p"
      shows "c.run (union A B) (w ||| smap Inl r) (Inl p)"
      using assms by (coinduction arbitrary: w r p) (force elim: a.run.cases)
    lemma run_union_b:
      assumes "b.run B (w ||| s) q"
      shows "c.run (union A B) (w ||| smap Inr s) (Inr q)"
      using assms by (coinduction arbitrary: w s q) (force elim: b.run.cases)
    lemma run_union:
      assumes "alphabet\<^sub>1 A = alphabet\<^sub>2 B"
      assumes "c.run (union A B) (w ||| rs) pq"
      obtains
        (a) r p where "rs = smap Inl r" "pq = Inl p" "a.run A (w ||| r) p" |
        (b) s q where "rs = smap Inr s" "pq = Inr q" "b.run B (w ||| s) q"
    proof (cases pq)
      case (Inl p)
      have 1: "rs = smap Inl (smap projl rs)"
        using assms(2) unfolding Inl by (coinduction arbitrary: w rs p) (force elim: c.run.cases)
      have 2: "a.run A (w ||| smap projl rs) p"
        using assms unfolding Inl by (coinduction arbitrary: w rs p) (force elim: c.run.cases)
      show ?thesis using a 1 Inl 2 by this
    next
      case (Inr q)
      have 1: "rs = smap Inr (smap projr rs)"
        using assms(2) unfolding Inr by (coinduction arbitrary: w rs q) (force elim: c.run.cases)
      have 2: "b.run B (w ||| smap projr rs) q"
        using assms unfolding Inr by (coinduction arbitrary: w rs q) (force elim: c.run.cases)
      show ?thesis using b 1 Inr 2 by this
    qed

    lemma union_nodes:
      assumes "alphabet\<^sub>1 A = alphabet\<^sub>2 B"
      shows "c.nodes (union A B) \<subseteq> a.nodes A <+> b.nodes B"
    proof
      fix pq
      assume "pq \<in> c.nodes (union A B)"
      then show "pq \<in> a.nodes A <+> b.nodes B" using assms by (induct) (auto 0 3)
    qed

    lemma union_nodes_finite[intro]:
      assumes "alphabet\<^sub>1 A = alphabet\<^sub>2 B"
      assumes "finite (a.nodes A)" "finite (b.nodes B)"
      shows "finite (c.nodes (union A B))"
      using finite_subset union_nodes assms by (auto intro: finite_Plus)

  end

  locale automaton_union_run =
    automaton_union
      automaton\<^sub>1 alphabet\<^sub>1 initial\<^sub>1 transition\<^sub>1 condition\<^sub>1
      automaton\<^sub>2 alphabet\<^sub>2 initial\<^sub>2 transition\<^sub>2 condition\<^sub>2
      automaton\<^sub>3 alphabet\<^sub>3 initial\<^sub>3 transition\<^sub>3 condition\<^sub>3 condition +
    a: automaton_run automaton\<^sub>1 alphabet\<^sub>1 initial\<^sub>1 transition\<^sub>1 condition\<^sub>1 test\<^sub>1 +
    b: automaton_run automaton\<^sub>2 alphabet\<^sub>2 initial\<^sub>2 transition\<^sub>2 condition\<^sub>2 test\<^sub>2 +
    c: automaton_run automaton\<^sub>3 alphabet\<^sub>3 initial\<^sub>3 transition\<^sub>3 condition\<^sub>3 test\<^sub>3
    for automaton\<^sub>1 :: "'label set \<Rightarrow> 'state\<^sub>1 set \<Rightarrow> ('label, 'state\<^sub>1) trans \<Rightarrow> 'condition\<^sub>1 \<Rightarrow> 'automaton\<^sub>1"
    and alphabet\<^sub>1 :: "'automaton\<^sub>1 \<Rightarrow> 'label set"
    and initial\<^sub>1 :: "'automaton\<^sub>1 \<Rightarrow> 'state\<^sub>1 set"
    and transition\<^sub>1 :: "'automaton\<^sub>1 \<Rightarrow> ('label, 'state\<^sub>1) trans"
    and condition\<^sub>1 :: "'automaton\<^sub>1 \<Rightarrow> 'condition\<^sub>1"
    and test\<^sub>1 :: "'condition\<^sub>1 \<Rightarrow> 'label stream \<Rightarrow> 'state\<^sub>1 stream \<Rightarrow> 'state\<^sub>1 \<Rightarrow> bool"
    and automaton\<^sub>2 :: "'label set \<Rightarrow> 'state\<^sub>2 set \<Rightarrow> ('label, 'state\<^sub>2) trans \<Rightarrow> 'condition\<^sub>2 \<Rightarrow> 'automaton\<^sub>2"
    and alphabet\<^sub>2 :: "'automaton\<^sub>2 \<Rightarrow> 'label set"
    and initial\<^sub>2 :: "'automaton\<^sub>2 \<Rightarrow> 'state\<^sub>2 set"
    and transition\<^sub>2 :: "'automaton\<^sub>2 \<Rightarrow> ('label, 'state\<^sub>2) trans"
    and condition\<^sub>2 :: "'automaton\<^sub>2 \<Rightarrow> 'condition\<^sub>2"
    and test\<^sub>2 :: "'condition\<^sub>2 \<Rightarrow> 'label stream \<Rightarrow> 'state\<^sub>2 stream \<Rightarrow> 'state\<^sub>2 \<Rightarrow> bool"
    and automaton\<^sub>3 :: "'label set \<Rightarrow> ('state\<^sub>1 + 'state\<^sub>2) set \<Rightarrow> ('label, 'state\<^sub>1 + 'state\<^sub>2) trans \<Rightarrow>
      'condition\<^sub>3 \<Rightarrow> 'automaton\<^sub>3"
    and alphabet\<^sub>3 :: "'automaton\<^sub>3 \<Rightarrow> 'label set"
    and initial\<^sub>3 :: "'automaton\<^sub>3 \<Rightarrow> ('state\<^sub>1 + 'state\<^sub>2) set"
    and transition\<^sub>3 :: "'automaton\<^sub>3 \<Rightarrow> ('label, 'state\<^sub>1 + 'state\<^sub>2) trans"
    and condition\<^sub>3 :: "'automaton\<^sub>3 \<Rightarrow> 'condition\<^sub>3"
    and test\<^sub>3 :: "'condition\<^sub>3 \<Rightarrow> 'label stream \<Rightarrow> ('state\<^sub>1 + 'state\<^sub>2) stream \<Rightarrow> 'state\<^sub>1 + 'state\<^sub>2 \<Rightarrow> bool"
    and condition :: "'condition\<^sub>1 \<Rightarrow> 'condition\<^sub>2 \<Rightarrow> 'condition\<^sub>3"
    +
    assumes test\<^sub>1[iff]: "test\<^sub>3 (condition c\<^sub>1 c\<^sub>2) w (smap Inl u) (Inl p) \<longleftrightarrow> test\<^sub>1 c\<^sub>1 w u p"
    assumes test\<^sub>2[iff]: "test\<^sub>3 (condition c\<^sub>1 c\<^sub>2) w (smap Inr v) (Inr q) \<longleftrightarrow> test\<^sub>2 c\<^sub>2 w v q"
  begin

    lemma union_language[simp]:
      assumes "alphabet\<^sub>1 A = alphabet\<^sub>2 B"
      shows "c.language (union A B) = a.language A \<union> b.language B"
      using assms
      unfolding a.language_def b.language_def c.language_def
      by (auto dest: run_union_a run_union_b elim!: run_union)

  end

  locale automaton_union_list =
    a: automaton automaton\<^sub>1 alphabet\<^sub>1 initial\<^sub>1 transition\<^sub>1 condition\<^sub>1 +
    b: automaton automaton\<^sub>2 alphabet\<^sub>2 initial\<^sub>2 transition\<^sub>2 condition\<^sub>2
    for automaton\<^sub>1 :: "'label set \<Rightarrow> 'state set \<Rightarrow> ('label, 'state) trans \<Rightarrow> 'condition\<^sub>1 \<Rightarrow> 'automaton\<^sub>1"
    and alphabet\<^sub>1 :: "'automaton\<^sub>1 \<Rightarrow> 'label set"
    and initial\<^sub>1 :: "'automaton\<^sub>1 \<Rightarrow> 'state set"
    and transition\<^sub>1 :: "'automaton\<^sub>1 \<Rightarrow> ('label, 'state) trans"
    and condition\<^sub>1 :: "'automaton\<^sub>1 \<Rightarrow> 'condition\<^sub>1"
    and automaton\<^sub>2 :: "'label set \<Rightarrow> (nat \<times> 'state) set \<Rightarrow> ('label, nat \<times> 'state) trans \<Rightarrow> 'condition\<^sub>2 \<Rightarrow> 'automaton\<^sub>2"
    and alphabet\<^sub>2 :: "'automaton\<^sub>2 \<Rightarrow> 'label set"
    and initial\<^sub>2 :: "'automaton\<^sub>2 \<Rightarrow> (nat \<times> 'state) set"
    and transition\<^sub>2 :: "'automaton\<^sub>2 \<Rightarrow> ('label, nat \<times> 'state) trans"
    and condition\<^sub>2 :: "'automaton\<^sub>2 \<Rightarrow> 'condition\<^sub>2"
    +
    fixes condition :: "'condition\<^sub>1 list \<Rightarrow> 'condition\<^sub>2"
  begin

    definition union :: "'automaton\<^sub>1 list \<Rightarrow> 'automaton\<^sub>2" where
      "union AA \<equiv> automaton\<^sub>2
        (\<Union> (alphabet\<^sub>1 ` set AA))
        (\<Union> k < length AA. {k} \<times> initial\<^sub>1 (AA ! k))
        (\<lambda> a (k, p). {k} \<times> transition\<^sub>1 (AA ! k) a p)
        (condition (map condition\<^sub>1 AA))"

    lemma union_simps[simp]:
      "alphabet\<^sub>2 (union AA) = \<Union> (alphabet\<^sub>1 ` set AA)"
      "initial\<^sub>2 (union AA) = (\<Union> k < length AA. {k} \<times> initial\<^sub>1 (AA ! k))"
      "transition\<^sub>2 (union AA) a (k, p) = {k} \<times> transition\<^sub>1 (AA ! k) a p"
      "condition\<^sub>2 (union AA) = condition (map condition\<^sub>1 AA)"
      unfolding union_def by auto

    lemma run_union:
      assumes "\<Inter> (alphabet\<^sub>1 ` set AA) = \<Union> (alphabet\<^sub>1 ` set AA)"
      assumes "A \<in> set AA"
      assumes "a.run A (w ||| s) p"
      obtains k where "k < length AA" "A = AA ! k" "b.run (union AA) (w ||| sconst k ||| s) (k, p)"
    proof -
      obtain k where 1: "k < length AA" "A = AA ! k" using assms(2) unfolding set_conv_nth by auto
      show ?thesis
      proof
        show "k < length AA" "A = AA ! k" using 1 by this
        show "b.run (union AA) (w ||| sconst k ||| s) (k, p)"
          using assms 1(2) by (coinduction arbitrary: w s p) (force elim: a.run.cases)
      qed
    qed
    lemma union_run:
      assumes "\<Inter> (alphabet\<^sub>1 ` set AA) = \<Union> (alphabet\<^sub>1 ` set AA)"
      assumes "k < length AA"
      assumes "b.run (union AA) (w ||| r) (k, p)"
      obtains s where "r = sconst k ||| s" "a.run (AA ! k) (w ||| s) p"
    proof
      show "r = sconst k ||| smap snd r"
        using assms by (coinduction arbitrary: w r p) (force elim: b.run.cases)
      show "a.run (AA ! k) (w ||| smap snd r) p"
        using assms by (coinduction arbitrary: w r p) (force elim: b.run.cases)
    qed

    lemma union_nodes:
      assumes "\<Inter> (alphabet\<^sub>1 ` set AA) = \<Union> (alphabet\<^sub>1 ` set AA)"
      shows "b.nodes (union AA) \<subseteq> (\<Union> k < length AA. {k} \<times> a.nodes (AA ! k))"
    proof
      show "kp \<in> (\<Union> k < length AA. {k} \<times> a.nodes (AA ! k))" if "kp \<in> b.nodes (union AA)" for kp
        using that assms by (induct) (auto 0 4)
    qed

    lemma union_nodes_finite[intro]:
      assumes "\<Inter> (alphabet\<^sub>1 ` set AA) = \<Union> (alphabet\<^sub>1 ` set AA)"
      assumes "list_all (finite \<circ> a.nodes) AA"
      shows "finite (b.nodes (union AA))"
    proof (rule finite_subset)
      show "b.nodes (union AA) \<subseteq> (\<Union> k < length AA. {k} \<times> a.nodes (AA ! k))"
        using union_nodes assms(1) by this
      show "finite (\<Union> k < length AA. {k} \<times> a.nodes' (AA ! k))"
        using assms(2) unfolding list_all_length by auto
    qed

  end

  locale automaton_union_list_run =
    automaton_union_list
      automaton\<^sub>1 alphabet\<^sub>1 initial\<^sub>1 transition\<^sub>1 condition\<^sub>1
      automaton\<^sub>2 alphabet\<^sub>2 initial\<^sub>2 transition\<^sub>2 condition\<^sub>2 condition +
    a: automaton_run automaton\<^sub>1 alphabet\<^sub>1 initial\<^sub>1 transition\<^sub>1 condition\<^sub>1 test\<^sub>1 +
    b: automaton_run automaton\<^sub>2 alphabet\<^sub>2 initial\<^sub>2 transition\<^sub>2 condition\<^sub>2 test\<^sub>2
    for automaton\<^sub>1 :: "'label set \<Rightarrow> 'state set \<Rightarrow> ('label, 'state) trans \<Rightarrow> 'condition\<^sub>1 \<Rightarrow> 'automaton\<^sub>1"
    and alphabet\<^sub>1 :: "'automaton\<^sub>1 \<Rightarrow> 'label set"
    and initial\<^sub>1 :: "'automaton\<^sub>1 \<Rightarrow> 'state set"
    and transition\<^sub>1 :: "'automaton\<^sub>1 \<Rightarrow> ('label, 'state) trans"
    and condition\<^sub>1 :: "'automaton\<^sub>1 \<Rightarrow> 'condition\<^sub>1"
    and test\<^sub>1 :: "'condition\<^sub>1 \<Rightarrow> 'label stream \<Rightarrow> 'state stream \<Rightarrow> 'state \<Rightarrow> bool"
    and automaton\<^sub>2 :: "'label set \<Rightarrow> (nat \<times> 'state) set \<Rightarrow> ('label, nat \<times> 'state) trans \<Rightarrow> 'condition\<^sub>2 \<Rightarrow> 'automaton\<^sub>2"
    and alphabet\<^sub>2 :: "'automaton\<^sub>2 \<Rightarrow> 'label set"
    and initial\<^sub>2 :: "'automaton\<^sub>2 \<Rightarrow> (nat \<times> 'state) set"
    and transition\<^sub>2 :: "'automaton\<^sub>2 \<Rightarrow> ('label, nat \<times> 'state) trans"
    and condition\<^sub>2 :: "'automaton\<^sub>2 \<Rightarrow> 'condition\<^sub>2"
    and test\<^sub>2 :: "'condition\<^sub>2 \<Rightarrow> 'label stream \<Rightarrow> (nat \<times> 'state) stream \<Rightarrow> nat \<times> 'state \<Rightarrow> bool"
    and condition :: "'condition\<^sub>1 list \<Rightarrow> 'condition\<^sub>2"
    +
    assumes test[iff]: "k < length cs \<Longrightarrow> test\<^sub>2 (condition cs) w (sconst k ||| r) (k, p) \<longleftrightarrow> test\<^sub>1 (cs ! k) w r p"
  begin

    lemma union_language[simp]:
      assumes "\<Inter> (alphabet\<^sub>1 ` set AA) = \<Union> (alphabet\<^sub>1 ` set AA)"
      shows "b.language (union AA) = \<Union> (a.language ` set AA)"
    proof
      show "b.language (union AA) \<subseteq> \<Union> (a.language ` set AA)"
        using assms unfolding a.language_def b.language_def by (force elim: union_run)
      show "\<Union> (a.language ` set AA) \<subseteq> b.language (union AA)"
        using assms unfolding a.language_def b.language_def by (force elim!: run_union)
    qed

  end

end