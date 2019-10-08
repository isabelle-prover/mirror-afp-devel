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

  (* TODO: create analogous thing for NFAs (automaton_target) *)
  locale automaton_trace =
    automaton automaton alphabet initial transition condition
    for automaton :: "'label set \<Rightarrow> 'state set \<Rightarrow> ('label, 'state) trans \<Rightarrow> 'condition \<Rightarrow> 'automaton"
    and alphabet :: "'automaton \<Rightarrow> 'label set"
    and initial :: "'automaton \<Rightarrow> 'state set"
    and transition :: "'automaton \<Rightarrow> ('label, 'state) trans"
    and condition :: "'automaton \<Rightarrow> 'condition"
    +
    fixes test :: "'condition \<Rightarrow> 'state stream \<Rightarrow> bool"
  begin

    definition language :: "'automaton \<Rightarrow> 'label stream set" where
      "language A \<equiv> {w |w r p. p \<in> initial A \<and> run A (w ||| r) p \<and> test (condition A) (trace (w ||| r) p)}"

    lemma language[intro]:
      assumes "p \<in> initial A" "run A (w ||| r) p" "test (condition A) (trace (w ||| r) p)"
      shows "w \<in> language A"
      using assms unfolding language_def by auto
    lemma language_elim[elim]:
      assumes "w \<in> language A"
      obtains r p
      where "p \<in> initial A" "run A (w ||| r) p" "test (condition A) (trace (w ||| r) p)"
      using assms unfolding language_def by auto

    lemma run_alphabet:
      assumes "run A (w ||| r) p"
      shows "w \<in> streams (alphabet A)"
      using assms by (coinduction arbitrary: w r p) (metis run.cases stream.map szip_smap szip_smap_fst)
    lemma language_alphabet: "language A \<subseteq> streams (alphabet A)"
      unfolding language_def by (auto dest: run_alphabet)

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

  locale automaton_degeneralization_trace =
    automaton_degeneralization
      automaton\<^sub>1 alphabet\<^sub>1 initial\<^sub>1 transition\<^sub>1 condition\<^sub>1
      automaton\<^sub>2 alphabet\<^sub>2 initial\<^sub>2 transition\<^sub>2 condition\<^sub>2 +
    a: automaton_trace automaton\<^sub>1 alphabet\<^sub>1 initial\<^sub>1 transition\<^sub>1 condition\<^sub>1 test\<^sub>1 +
    b: automaton_trace automaton\<^sub>2 alphabet\<^sub>2 initial\<^sub>2 transition\<^sub>2 condition\<^sub>2 test\<^sub>2
    for automaton\<^sub>1 :: "'label set \<Rightarrow> 'state set \<Rightarrow> ('label, 'state) trans \<Rightarrow> 'state pred gen \<Rightarrow> 'automaton\<^sub>1"
    and alphabet\<^sub>1 :: "'automaton\<^sub>1 \<Rightarrow> 'label set"
    and initial\<^sub>1 :: "'automaton\<^sub>1 \<Rightarrow> 'state set"
    and transition\<^sub>1 :: "'automaton\<^sub>1 \<Rightarrow> ('label, 'state) trans"
    and condition\<^sub>1 :: "'automaton\<^sub>1 \<Rightarrow> 'state pred gen"
    and test\<^sub>1 :: "'state pred gen \<Rightarrow> 'state stream \<Rightarrow> bool"
    and automaton\<^sub>2 :: "'label set \<Rightarrow> 'state degen set \<Rightarrow> ('label, 'state degen) trans \<Rightarrow> 'state degen pred \<Rightarrow> 'automaton\<^sub>2"
    and alphabet\<^sub>2 :: "'automaton\<^sub>2 \<Rightarrow> 'label set"
    and initial\<^sub>2 :: "'automaton\<^sub>2 \<Rightarrow> 'state degen set"
    and transition\<^sub>2 :: "'automaton\<^sub>2 \<Rightarrow> ('label, 'state degen) trans"
    and condition\<^sub>2 :: "'automaton\<^sub>2 \<Rightarrow> 'state degen pred"
    and test\<^sub>2 :: "'state degen pred \<Rightarrow> 'state degen stream \<Rightarrow> bool"
    +
    assumes test[iff]: "test\<^sub>2 (degen cs) (r ||| sscan (count cs) (p ## r) k) \<longleftrightarrow> test\<^sub>1 cs r"
  begin

    lemma degeneralize_language[simp]: "b.language (degeneralize A) = a.language A"
      unfolding a.language_def b.language_def
      unfolding a.trace_alt_def b.trace_alt_def
      by (auto dest: run_degeneralize elim!: degeneralize_run)

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

  locale automaton_intersection_trace =
    automaton_intersection
      automaton\<^sub>1 alphabet\<^sub>1 initial\<^sub>1 transition\<^sub>1 condition\<^sub>1
      automaton\<^sub>2 alphabet\<^sub>2 initial\<^sub>2 transition\<^sub>2 condition\<^sub>2
      automaton\<^sub>3 alphabet\<^sub>3 initial\<^sub>3 transition\<^sub>3 condition\<^sub>3 condition +
    a: automaton_trace automaton\<^sub>1 alphabet\<^sub>1 initial\<^sub>1 transition\<^sub>1 condition\<^sub>1 test\<^sub>1 +
    b: automaton_trace automaton\<^sub>2 alphabet\<^sub>2 initial\<^sub>2 transition\<^sub>2 condition\<^sub>2 test\<^sub>2 +
    c: automaton_trace automaton\<^sub>3 alphabet\<^sub>3 initial\<^sub>3 transition\<^sub>3 condition\<^sub>3 test\<^sub>3
    for automaton\<^sub>1 :: "'label set \<Rightarrow> 'state\<^sub>1 set \<Rightarrow> ('label, 'state\<^sub>1) trans \<Rightarrow> 'condition\<^sub>1 \<Rightarrow> 'automaton\<^sub>1"
    and alphabet\<^sub>1 :: "'automaton\<^sub>1 \<Rightarrow> 'label set"
    and initial\<^sub>1 :: "'automaton\<^sub>1 \<Rightarrow> 'state\<^sub>1 set"
    and transition\<^sub>1 :: "'automaton\<^sub>1 \<Rightarrow> ('label, 'state\<^sub>1) trans"
    and condition\<^sub>1 :: "'automaton\<^sub>1 \<Rightarrow> 'condition\<^sub>1"
    and test\<^sub>1 :: "'condition\<^sub>1 \<Rightarrow> 'state\<^sub>1 stream \<Rightarrow> bool"
    and automaton\<^sub>2 :: "'label set \<Rightarrow> 'state\<^sub>2 set \<Rightarrow> ('label, 'state\<^sub>2) trans \<Rightarrow> 'condition\<^sub>2 \<Rightarrow> 'automaton\<^sub>2"
    and alphabet\<^sub>2 :: "'automaton\<^sub>2 \<Rightarrow> 'label set"
    and initial\<^sub>2 :: "'automaton\<^sub>2 \<Rightarrow> 'state\<^sub>2 set"
    and transition\<^sub>2 :: "'automaton\<^sub>2 \<Rightarrow> ('label, 'state\<^sub>2) trans"
    and condition\<^sub>2 :: "'automaton\<^sub>2 \<Rightarrow> 'condition\<^sub>2"
    and test\<^sub>2 :: "'condition\<^sub>2 \<Rightarrow> 'state\<^sub>2 stream \<Rightarrow> bool"
    and automaton\<^sub>3 :: "'label set \<Rightarrow> ('state\<^sub>1 \<times> 'state\<^sub>2) set \<Rightarrow> ('label, 'state\<^sub>1 \<times> 'state\<^sub>2) trans \<Rightarrow>
      'condition\<^sub>3 \<Rightarrow> 'automaton\<^sub>3"
    and alphabet\<^sub>3 :: "'automaton\<^sub>3 \<Rightarrow> 'label set"
    and initial\<^sub>3 :: "'automaton\<^sub>3 \<Rightarrow> ('state\<^sub>1 \<times> 'state\<^sub>2) set"
    and transition\<^sub>3 :: "'automaton\<^sub>3 \<Rightarrow> ('label, 'state\<^sub>1 \<times> 'state\<^sub>2) trans"
    and condition\<^sub>3 :: "'automaton\<^sub>3 \<Rightarrow> 'condition\<^sub>3"
    and test\<^sub>3 :: "'condition\<^sub>3 \<Rightarrow> ('state\<^sub>1 \<times> 'state\<^sub>2) stream \<Rightarrow> bool"
    and condition :: "'condition\<^sub>1 \<Rightarrow> 'condition\<^sub>2 \<Rightarrow> 'condition\<^sub>3"
    +
    assumes test[iff]: "test\<^sub>3 (condition c\<^sub>1 c\<^sub>2) (u ||| v) \<longleftrightarrow> test\<^sub>1 c\<^sub>1 u \<and> test\<^sub>2 c\<^sub>2 v"
  begin

    lemma intersect_language[simp]: "c.language (intersect A B) = a.language A \<inter> b.language B"
      unfolding a.language_def b.language_def c.language_def
      unfolding a.trace_alt_def b.trace_alt_def c.trace_alt_def
      by (fastforce iff: split_szip)

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

  end

  locale automaton_union_trace =
    automaton_union
      automaton\<^sub>1 alphabet\<^sub>1 initial\<^sub>1 transition\<^sub>1 condition\<^sub>1
      automaton\<^sub>2 alphabet\<^sub>2 initial\<^sub>2 transition\<^sub>2 condition\<^sub>2
      automaton\<^sub>3 alphabet\<^sub>3 initial\<^sub>3 transition\<^sub>3 condition\<^sub>3 condition +
    a: automaton_trace automaton\<^sub>1 alphabet\<^sub>1 initial\<^sub>1 transition\<^sub>1 condition\<^sub>1 test\<^sub>1 +
    b: automaton_trace automaton\<^sub>2 alphabet\<^sub>2 initial\<^sub>2 transition\<^sub>2 condition\<^sub>2 test\<^sub>2 +
    c: automaton_trace automaton\<^sub>3 alphabet\<^sub>3 initial\<^sub>3 transition\<^sub>3 condition\<^sub>3 test\<^sub>3
    for automaton\<^sub>1 :: "'label set \<Rightarrow> 'state\<^sub>1 set \<Rightarrow> ('label, 'state\<^sub>1) trans \<Rightarrow> 'condition\<^sub>1 \<Rightarrow> 'automaton\<^sub>1"
    and alphabet\<^sub>1 :: "'automaton\<^sub>1 \<Rightarrow> 'label set"
    and initial\<^sub>1 :: "'automaton\<^sub>1 \<Rightarrow> 'state\<^sub>1 set"
    and transition\<^sub>1 :: "'automaton\<^sub>1 \<Rightarrow> ('label, 'state\<^sub>1) trans"
    and condition\<^sub>1 :: "'automaton\<^sub>1 \<Rightarrow> 'condition\<^sub>1"
    and test\<^sub>1 :: "'condition\<^sub>1 \<Rightarrow> 'state\<^sub>1 stream \<Rightarrow> bool"
    and automaton\<^sub>2 :: "'label set \<Rightarrow> 'state\<^sub>2 set \<Rightarrow> ('label, 'state\<^sub>2) trans \<Rightarrow> 'condition\<^sub>2 \<Rightarrow> 'automaton\<^sub>2"
    and alphabet\<^sub>2 :: "'automaton\<^sub>2 \<Rightarrow> 'label set"
    and initial\<^sub>2 :: "'automaton\<^sub>2 \<Rightarrow> 'state\<^sub>2 set"
    and transition\<^sub>2 :: "'automaton\<^sub>2 \<Rightarrow> ('label, 'state\<^sub>2) trans"
    and condition\<^sub>2 :: "'automaton\<^sub>2 \<Rightarrow> 'condition\<^sub>2"
    and test\<^sub>2 :: "'condition\<^sub>2 \<Rightarrow> 'state\<^sub>2 stream \<Rightarrow> bool"
    and automaton\<^sub>3 :: "'label set \<Rightarrow> ('state\<^sub>1 + 'state\<^sub>2) set \<Rightarrow> ('label, 'state\<^sub>1 + 'state\<^sub>2) trans \<Rightarrow>
      'condition\<^sub>3 \<Rightarrow> 'automaton\<^sub>3"
    and alphabet\<^sub>3 :: "'automaton\<^sub>3 \<Rightarrow> 'label set"
    and initial\<^sub>3 :: "'automaton\<^sub>3 \<Rightarrow> ('state\<^sub>1 + 'state\<^sub>2) set"
    and transition\<^sub>3 :: "'automaton\<^sub>3 \<Rightarrow> ('label, 'state\<^sub>1 + 'state\<^sub>2) trans"
    and condition\<^sub>3 :: "'automaton\<^sub>3 \<Rightarrow> 'condition\<^sub>3"
    and test\<^sub>3 :: "'condition\<^sub>3 \<Rightarrow> ('state\<^sub>1 + 'state\<^sub>2) stream \<Rightarrow> bool"
    and condition :: "'condition\<^sub>1 \<Rightarrow> 'condition\<^sub>2 \<Rightarrow> 'condition\<^sub>3"
    +
    assumes test\<^sub>1[iff]: "test\<^sub>3 (condition c\<^sub>1 c\<^sub>2) (smap Inl u) \<longleftrightarrow> test\<^sub>1 c\<^sub>1 u"
    assumes test\<^sub>2[iff]: "test\<^sub>3 (condition c\<^sub>1 c\<^sub>2) (smap Inr v) \<longleftrightarrow> test\<^sub>2 c\<^sub>2 v"
  begin

    lemma union_language[simp]:
      assumes "alphabet\<^sub>1 A = alphabet\<^sub>2 B"
      shows "c.language (union A B) = a.language A \<union> b.language B"
      using assms
      unfolding a.language_def b.language_def c.language_def
      unfolding a.trace_alt_def b.trace_alt_def c.trace_alt_def
      by (auto dest: run_union_a run_union_b elim!: run_union)

  end

end