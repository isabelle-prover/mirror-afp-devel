section \<open>Simulations for Buechi Properties\<close>
theory Simulation_Graphs2
  imports Timed_Automata.Simulation_Graphs "HOL-Eisbach.Eisbach"
begin

text \<open>
This theory essentially formalizes the concepts from Guangyuan Li's FORMATS 2009 paper
``Checking Timed Büchi Automata Emptiness Using LU-Abstractions'' \<^cite>\<open>"Li:FORMATS:2009"\<close>.
However, instead of formalizing this directly for the notions of timed Büchi automata,
time-abstract simulations, and zone graphs with abstractions,
we use general notions of simulation graphs with certain properties.
\<close>

subsection \<open>Misc\<close>
lemma map_eq_append_conv:
  "(map f xs = ys @ zs) = (\<exists>as bs. xs = as @ bs \<and> map f as = ys \<and> map f bs = zs)"
  by (induction ys arbitrary: xs; simp add: map_eq_Cons_conv; metis append_Cons)

lemma Cons_subseq_iff:
  "subseq (x # xs) ys \<longleftrightarrow> (\<exists>as bs. ys = as @ x # bs \<and> subseq xs bs)"
  using list_emb_ConsD list_emb_append2 by fastforce

lemma append_subseq_iff:
  "subseq (as @ bs) xs \<longleftrightarrow> (\<exists>ys zs. xs = ys @ zs \<and> subseq as ys \<and> subseq bs zs)"
  by (meson list_emb_appendD list_emb_append_mono)

context Graph_Defs
begin

lemma steps_append_singleE:
  assumes "steps (xs @ [x])"
  obtains "xs = []" | ys y where "xs = ys @ [y]" "steps xs" "y \<rightarrow> x"
  using assms by (metis append_butlast_last_id list.distinct(1) list.sel(1) steps_decomp)

lemma steps_alt_induct2[consumes 1, case_names Single Snoc]:
  assumes
    "steps (a # xs @ [b])" "(\<And>b. E a b \<Longrightarrow> P a [] b)"
    "\<And>y x xs. E y x \<Longrightarrow> steps (a # xs @ [y]) \<Longrightarrow> P a xs y \<Longrightarrow> P a (xs @ [y]) x"
  shows "P a xs b"
  using assms(1)
  apply (induction "a # xs @ [b]" arbitrary: xs b rule: steps_alt_induct)
  subgoal
    apply auto
    done
  subgoal for y x xs ys b
    apply (cases "ys = []")
     apply (force intro: assms(2); fail)
    apply (simp, metis append.simps(2) append1_eq_conv append_butlast_last_id assms(3))
    done
  done

lemma steps_singleI:
  "steps [a,b]" if "a \<rightarrow> b"
  using that steps.intros by blast

end

subsection \<open>Backward Simulations\<close>
locale Backward_Simulation = Simulation where A = E and B = E and sim = sim
  for E :: "'a \<Rightarrow> 'a \<Rightarrow> bool" and sim (infix "\<preceq>" 60) +
  fixes G :: "'a set \<Rightarrow> 'a set \<Rightarrow> bool"
  assumes simulation: "b \<in> B \<Longrightarrow> G A B \<Longrightarrow> \<exists>a \<in> A. \<exists>b'. a \<rightarrow> b' \<and> b \<preceq> b'"
      and refl[intro, simp]: "a \<preceq> a" and trans: "transp (\<preceq>)"
begin

lemmas A_simulation_steps = simulation_steps

sublocale Graph_Defs G .

lemmas sim_transD[intro] = transpD[OF trans]

lemma backward_simulation_reaches:
  "\<exists>a \<in> A. \<exists>b'. E\<^sup>*\<^sup>* a b' \<and> b \<preceq> b'" if "G\<^sup>*\<^sup>* A B" "b \<in> B"
  using that
proof (induction arbitrary: b rule: rtranclp_induct)
  case base
  then show ?case
    by auto
next
  case (step Y Z)
  from simulation[OF \<open>b \<in> Z\<close> \<open>G Y Z\<close>] obtain a b' where "a \<in> Y" "a \<rightarrow> b'" "b \<preceq> b'"
    by safe
  from step.IH[OF \<open>a \<in> Y\<close>] obtain a0 a' where "a0 \<in> A" "a0 \<rightarrow>* a'" "a \<preceq> a'"
    by safe
  moreover from A_B_step[OF \<open>a \<rightarrow> b'\<close> \<open>a \<preceq> a'\<close>] obtain b'' where "a' \<rightarrow> b''" "b' \<preceq> b''"
    by safe
  with \<open>a0 \<in> A\<close> \<open>a0 \<rightarrow>* a'\<close> \<open>b \<preceq> b'\<close> show ?case
    by (auto intro: rtranclp.intros(2))
qed

lemma backward_simulation_steps:
  "\<exists>a \<in> A. \<exists>as b'. A.steps (a # as @ [b']) \<and> b \<preceq> b'" if "steps (A # As @ [B])" "b \<in> B"
  using that
proof (induction A As B arbitrary: b rule: steps_alt_induct2)
  case (Single x)
  from simulation[OF this(2,1)] show ?case
    by (safe, intro bexI exI[where x = "[]"]) auto
next
  case (Snoc B C As c)
  from simulation[OF \<open>c \<in> C\<close> \<open>G B C\<close>] obtain b c' where "b \<in> B" "b \<rightarrow> c'" "c \<preceq> c'"
    by safe
  with Snoc.IH obtain a as b' where "a \<in> A" "A.steps (a # as @ [b'])" "b \<preceq> b'"
    by blast
  moreover from \<open>b \<preceq> b'\<close> \<open>b \<rightarrow> c'\<close> obtain c'' where "b' \<rightarrow> c''" "c' \<preceq> c''"
    by (auto dest: A_B_step)
  ultimately have "a \<in> A" "c \<preceq> c''" "A.steps (a # (as @ [b']) @ [c''])"
    using \<open>c \<preceq> c'\<close> by auto (metis A.steps_appendI append_Cons)
  then show ?case
    by blast
qed

lemma backward_simulation_reaches1:
  "\<exists>a \<in> A. \<exists>b'. E\<^sup>+\<^sup>+ a b' \<and> b \<preceq> b'" if "G\<^sup>+\<^sup>+ A B" "b \<in> B"
  using that unfolding A.reaches1_steps_iff reaches1_steps_iff
  by (auto dest!: backward_simulation_steps)

text \<open>Corresponds to lemma 8 of \<^cite>\<open>"Li:FORMATS:2009"\<close>.\<close>
lemma steps_repeat:
  assumes "steps (A # As @ [A])" "a \<in> A" "\<forall>a \<in> A. P a" "\<forall>x y. x \<preceq> y \<and> x \<in> A \<and> P x \<longrightarrow> P y"
  obtains x y as xs where
    "subseq as xs" "list_all P as" "A.steps (x # xs @ [y])" "length as = n" "a \<preceq> y" "x \<in> A"
  using \<open>a \<in> A\<close>
proof (atomize_elim, induction n arbitrary: a)
  case 0
  from backward_simulation_steps[OF \<open>steps (A # As @ [A])\<close> \<open>a \<in> A\<close>] obtain a' as b where
    "a' \<in> A" "A.steps (a' # as @ [b])" "a \<preceq> b"
    by auto
  then show ?case
    by (auto 4 4 intro: exI[where x = "[]"])
next
  case (Suc n b)
  from backward_simulation_steps[OF assms(1) \<open>b \<in> A\<close>] obtain a as b' where
    "a \<in> A" "A.steps (a # as @ [b'])" "b \<preceq> b'"
    by auto
  from Suc.IH[OF \<open>a \<in> A\<close> \<open>a \<in> A\<close>] obtain as' xs x y where
    "subseq as' xs" "list_all P as'" "A.steps (x # xs @ [y])" "n = length as'" "a \<preceq> y" "x \<in> A"
    by auto
  moreover from A_simulation_steps[OF \<open>A.steps (a # _)\<close> \<open>a \<preceq> y\<close>] \<open>b \<preceq> b'\<close> obtain b'' bs where
    "A.steps (y # bs @ [b''])" "list_all2 (\<preceq>) as bs" "b \<preceq> b''"
    unfolding list_all2_append1 list_all2_Cons1 by auto
  ultimately show ?case
    using assms(3,4) \<open>a \<in> A\<close>
    by (inst_existentials "as' @ [y]" "xs @ [y] @ bs" x b'')
       (auto simp: list_emb_append_mono, metis A.steps_append2 append_Cons)
qed

end

subsection \<open>Self Simulation for a Finite Simulation Relation\<close>
text \<open>
This section makes the following abstractions:
  \<^item> The timed automata semantics correspond to the transition system \<open>\<rightarrow>\<close> (\<open>E\<close>).
  \<^item> The finite time-abstract bisimulation \<open>\<equiv>\<^sub>M\<close> from the classic region construction
    corresponds to the simulation \<open>\<preceq>\<close>.
\<close>

locale Self_Simulation =
  Simulation_Invariant where A = E and B = E and sim = sim and PA = P and PB = P
  for E :: "'a \<Rightarrow> 'a \<Rightarrow> bool" and sim (infix "\<preceq>" 60) and P +
  assumes refl: "reflp (\<preceq>)" and trans: "transp (\<preceq>)"
begin

lemma sim_reflI[intro, simp]:
  "x \<preceq> x"
  using refl unfolding reflp_def by auto

lemmas sim_transD[intro] = transpD[OF trans]

text \<open>Corresponds to lemma 3 of \<^cite>\<open>"Li:FORMATS:2009"\<close>.\<close>
lemma pre_cycle_infinite_cycle:
  assumes "A.steps (x # xs @ [y])" "x \<preceq> y" "P x" "P y"
  obtains w where
    "A.run (x ## w)" "stream_all2 (\<preceq>) (cycle (x # xs)) (x ## w)"
proof -
  let ?R = "\<lambda>a b. a \<preceq> b \<and> P a \<and> P b"
  define nxt where
    "nxt \<equiv> \<lambda>(xs, y). SOME (ys, z). A.steps (y # ys @ [z]) \<and> list_all2 ?R xs ys \<and> y \<preceq> z"
  have *: "A.steps (y # ys @ [z]) \<and> list_all2 ?R xs ys \<and> y \<preceq> z"
    if "nxt (xs, y) = (ys, z)" "A.steps(x # xs @ [y])" "x \<preceq> y" "P x" "P y" for x y xs ys z
  proof -
    from simulation_steps[OF that(2) \<open>x \<preceq> y\<close>] \<open>P x\<close> \<open>P y\<close> obtain ws y' where
      "A.steps (y # ws @ [y'])" "list_all2 ?R xs ws" "y \<preceq> y'"
      by (smt list_all2_Cons1 list_all2_Nil list_all2_append1)
    then show ?thesis
      using \<open>nxt _ = _\<close> unfolding nxt_def by (auto dest!: verit_sko_ex_indirect[OF sym])
  qed
  let ?w = "flat (smap (\<lambda>(xs, y). xs @ [y]) (siterate nxt (xs, y)))"
  from assms have "A.run ?w"
  proof (coinduction arbitrary: x xs y rule: A.run_flat_coinduct)
    case (run_shift as bs xss x xs y)
    obtain ys z where "nxt (xs, y) = (ys, z)"
      by (cases "nxt (xs, y)")
    with run_shift have "as = xs @ [y]" "bs = ys @ [z]"
      "bs ## xss = smap (\<lambda>(xs, y). xs @ [y]) (siterate nxt (ys, z))"
      by auto
    with *[OF \<open>nxt _ = _\<close> \<open>A.steps (x # _)\<close> \<open>x \<preceq> y\<close>] run_shift(2-) show ?case
      by (inst_existentials ys z)
         (auto 4 3 dest: A.steps_ConsD PA_invariant.invariant_steps elim: A.steps.cases)
  qed
  with assms(1) have "A.run (x ## ?w)"
    apply -
    apply (cases "smap (\<lambda>(xs, y). xs @ [y]) (siterate nxt (xs, y))")
    apply (simp only:)
    apply clarsimp
    by (smt A.run.cases A.run.intros A.steps.cases shift_simps(1) stream.sel(1)
          append_Nil append_is_Nil_conv hd_append2 list.distinct(1) list.sel)
  obtain x' xs' where eqs: "xs = xs'" "x = x'"
    by auto
  with assms have "A.steps (x' # xs' @ [y])" "list_all2 (\<preceq>) xs xs'" "x \<preceq> x'" "x' \<preceq> y" "P x'" "P y"
    by (auto simp: zip_same list_all2_iff)
  then have "stream_all2 (\<preceq>) (cycle (xs @ [x])) ?w"
  proof (rewrite in \<open>(xs, y)\<close> eqs, coinduction arbitrary: x' xs' y rule: stream_rel_coinduct_shift)
    case stream_rel
    obtain ys z where "nxt (xs', y) = (ys, z)"
      by (cases "nxt (xs', y)")
    with stream_rel show ?case
      apply -
      apply (frule (4) *)
      apply (inst_existentials "xs @ [x]" "cycle (xs @ [x])" "xs' @ [y]"
              "flat (smap (\<lambda>(xs, y). xs @ [y]) (siterate nxt (ys, z)))")
      subgoal
        by simp
           (metis cycle_Cons cycle_decomp cycle_rotated list.distinct(1) list.sel(1) list.sel(3))
      subgoal
        by (cases "smap (\<lambda>(xs, y). xs @ [y]) (siterate nxt (xs', y))") (simp only:, auto)
      apply (solves \<open>auto simp: list_all2_iff\<close>)+
      apply (auto 4 5 elim: list_all2_trans[rotated] dest: PA_invariant.invariant_steps)
      done
  qed
  then have "stream_all2 (\<preceq>) (cycle (x # xs)) (x ## ?w)"
    by (simp add: cycle_Cons)
  with \<open>A.run (x ## ?w)\<close> show ?thesis
    by (auto intro: that)
qed

end

locale Self_Simulation_Finite =
  Simulation_Invariant where A = E and B = E and sim = sim and PA = P and PB = P
  for E :: "'a \<Rightarrow> 'a \<Rightarrow> bool" and sim (infix "\<preceq>" 60) and P +
  assumes equiv_sim: "equivp (\<preceq>)" and finite_quotient: "finite (UNIV // {(x, y). x \<preceq> y})"
begin

sublocale Self_Simulation
  apply standard
  using equiv_sim apply (simp add: equivp_reflp_symp_transp)+
  done

text \<open>Roughly corresponds to lemmas 9, 10, and 11 of \<^cite>\<open>"Li:FORMATS:2009"\<close>.\<close>
lemma steps_cycle_run:
  assumes "A.steps (x # xs)" "subseq as xs" "P x" "length as > card (UNIV // {(x, y). x \<preceq> y})"
    "\<forall>x \<in> set as. \<phi> x" "\<forall>x \<in> set as. \<forall>y. x \<preceq> y \<and> \<phi> x \<longrightarrow> \<phi> y"
  obtains w where "A.run (x ## w)" "infs \<phi> w"
proof -
  from assms(3) obtain a b as' ys cs' where *: "xs = as' @ a # ys @ b # cs'" "a \<preceq> b" "a \<in> set as"
  proof -
    let ?f = "\<lambda>x. {y. x \<preceq> y}"
    let ?as = "map ?f as"
    have "card (set ?as) \<le> card (UNIV // {(x, y). x \<preceq> y})"
      using quotientI[of _ _ "{(x, y). x \<preceq> y}"]
      by (auto intro: finite_quotient surj_card_le[where f = id])
    also have "\<dots> < length as"
      by (rule assms)
    finally have "card (set ?as) < length ?as"
      by simp
    then have "\<not> distinct ?as"
      using distinct_card[of ?as] by auto
    then obtain a b as' ys cs' where "as = as' @ a # ys @ b # cs'" "a \<preceq> b"
      using that
      by (clarsimp simp: map_eq_append_conv map_eq_Cons_conv dest!: not_distinct_decomp) blast
    then show ?thesis
      using that[where a = a and b = b] \<open>subseq as xs\<close>
      by (simp add: append_subseq_iff Cons_subseq_iff) (metis append.assoc)
  qed
  have "A.steps (x # as' @ [a])" "A.steps (a # ys @ [b])"
  proof -
    from assms(1) * show "A.steps (x # as' @ [a])"
      using A.steps_appendD1 by auto
    from * have "as' @ (a # ys) @ b # cs' = xs"
        by simp
    have "b # cs' \<noteq> [] \<and> a # ys \<noteq> [] \<or> (a # ys) @ b # cs' \<noteq> [] \<and> \<not> A.steps ((a # ys) @ b # cs')
        \<or> A.steps ((a # ys) @ [b])"
      by blast
    with \<open>_ = xs\<close> assms(1) have "A.steps ((a # ys) @ [b])"
      by (metis (no_types) A.Single A.steps_ConsD A.steps_append_single A.steps_decomp
          Nil_is_append_conv list.sel(1) self_append_conv2)
    then show "A.steps (a # ys @ [b])"
      by simp
  qed
  with \<open>P x\<close> have "P a" "P b"
    by (auto 4 3 dest: PA_invariant.invariant_steps)
  from pre_cycle_infinite_cycle[OF \<open>A.steps (a # ys @ [b])\<close> \<open>a \<preceq> b\<close> this] obtain w where
    "A.run (a ## w)" "stream_all2 (\<preceq>) (cycle (a # ys)) (a ## w)" .
  from this(2) have "infs ((\<preceq>) a) (a ## w)"
    by (smt alw_ev_lockstep infs_cycle list.distinct(1) list.set_intros(1) sim_reflI sim_transD)
  then have "infs \<phi> (as' @- a ## w)"
    using assms(5) \<open>a \<in> set as\<close> unfolding \<open>xs = as' @ _\<close> apply simp
    using assms(6) by (elim infs_mono[rotated]) blast
  moreover from \<open>A.run _\<close> \<open>A.steps (x # as' @ [a])\<close> have "A.run (x ## as' @- a ## w)"
    by (metis A.extend_run A.steps_decomp append_Cons list.distinct(1) list.sel(1,3)
          shift_simps stream.exhaust stream.sel)
  ultimately show ?thesis
    by (rule that[rotated])
qed

end

subsection \<open>Combining Finite Simulation with Backward Simulation\<close>
text \<open>Here, \<open>\<preceq>\<close> is any time-abstract simulation \<open>\<preceq>\<close>, and \<open>\<preceq>'\<close> corresponds to \<open>\<equiv>\<^sub>M\<close>.\<close>

locale Backward_Double_Simulation = Backward_Simulation where E = E and sim = sim +
  finite: Self_Simulation_Finite where E = E and sim = sim'
  for E :: "'a \<Rightarrow> 'a \<Rightarrow> bool" and sim (infix "\<preceq>" 60) and sim' (infix "\<preceq>''" 60)
begin

text \<open>Corresponds to lemma 12 of \<^cite>\<open>"Li:FORMATS:2009"\<close>.\<close>
lemma cycle_Buechi_run:
  assumes "steps (A # As @ [A])" "a \<in> A" "\<forall>a \<in> A. P a" "\<forall>a \<in> A. \<phi> a"
    "\<forall>x y. x \<preceq> y \<and> x \<in> A \<and> \<phi> x \<longrightarrow> \<phi> y" "\<forall>x y. x \<preceq>' y \<and> \<phi> x \<longrightarrow> \<phi> y"
  obtains x xs where "A.run (x ## xs)" "infs \<phi> xs" "x \<in> A"
proof -
  let ?n = "card (UNIV // {(x, y). x \<preceq>' y}) + 1"
  from steps_repeat[OF assms(1,2,4-5), where n = ?n] obtain x y as ys where *:
    "subseq as ys" "list_all \<phi> as" "A.steps (x # ys @ [y])"
    "length as = ?n" "a \<preceq> y" "x \<in> A" .
  with assms(4) have "\<forall>x \<in> set as. \<phi> x"
    by (auto simp: list_all_iff)
  with * assms(3,6) obtain w where "A.run (x ## w)" "infs \<phi> w"
    by - (erule finite.steps_cycle_run[where \<phi> = \<phi>], auto)
  then show ?thesis
    using \<open>x \<in> A\<close> by (elim that) simp
qed

end

lemma (in Simulation_Invariant) simulation_run':
  assumes "A.run (x ## xs)" "x \<sim> y" "PA x" "PB y"
  shows "\<exists>ys. B.run (y ## ys) \<and> stream_all2 (\<lambda>a b. a \<sim> b \<and> PA a \<and> PB b) xs ys"
  using simulation_run assms unfolding equiv'_def by blast

(* XXX Move to graph library *)
context Graph_Invariant_Start
begin

lemma reachable_reaches_equiv: "G'.reaches x y \<longleftrightarrow> x \<rightarrow>* y" if "reachable x" for x y
  using invariant_reaches invariant_reaches_iff reachable_def that by auto

lemma reachable_reaches1_equiv: "G'.reaches1 x y \<longleftrightarrow> x \<rightarrow>\<^sup>+ y" if "reachable x" for x y
  using invariant_reaches invariant_reaches1_iff reachable_def that by auto

lemma reachable_steps_equiv:
  "G'.steps (x # xs) \<longleftrightarrow> steps (x # xs)" if "reachable x"
  using invariant_reaches invariant_steps_iff reachable_def that by auto

lemma reachable_run_equiv:
  "G'.run (x ## xs) \<longleftrightarrow> run (x ## xs)" if "reachable x"
  \<comment> \<open>This proof is bit clumsy due to the name clash for \<open>invariant_run\<close>\<close>
  by (metis reaches_steps_iff Graph_Invariant.invariant_run Graph_Invariant_axioms
        invariant_reaches reachable_steps subgraph_run_iff that)

lemmas invariant_subgraph_equivs =
  reachable_reaches_equiv reachable_reaches1_equiv reachable_steps_equiv reachable_run_equiv

end

text \<open>Adding the assumption that the abstracted zone graph is finite and complete.\<close>
locale Backward_Double_Simulation_Complete =
  A: Graph_Defs E + G: Graph_Defs G + G_inv: Graph_Defs "\<lambda>x y. G x y \<and> Q x \<and> Q y" +
  backward: Backward_Double_Simulation where E = E and G = "\<lambda>x y. G x y \<and> Q x \<and> Q y" +
  complete: Simulation_Invariant where A = E and B = G and PA = P and PB = Q and sim = "(\<in>)" +
  Finite_Graph where E = G and x\<^sub>0 = a\<^sub>0 +
  Graph_Invariant where E = G and P = Q
  for E :: "'a \<Rightarrow> 'a \<Rightarrow> bool" and G :: "'a set \<Rightarrow> 'a set \<Rightarrow> bool" and a\<^sub>0 and Q +
  assumes Q_P: "Q a \<Longrightarrow> \<forall>x \<in> a. P x" and a\<^sub>0_invariant: "Q a\<^sub>0"
begin

sublocale G: Graph_Invariant_Start where E = G and P = Q and s\<^sub>0 = a\<^sub>0
  by (standard) (rule a\<^sub>0_invariant)

lemmas G_invariant_subgraph_equivs =
  G.invariant_subgraph_equivs[unfolded complete.PB_invariant.E'_def]

text \<open>Corresponds to theorem 1 of \<^cite>\<open>"Li:FORMATS:2009"\<close>.\<close>
theorem Buechi_run_lasso_iff:
  assumes
    "\<forall>x y. x \<preceq>' y \<and> \<phi> x \<longrightarrow> \<phi> y"
    "\<forall>x y. x \<preceq> y  \<and> \<phi> x \<longrightarrow> \<phi> y"
    "\<forall>x y A. G.reaches a\<^sub>0 A \<and> x \<in> A \<and> y \<in> A \<and> \<phi> x \<longrightarrow> \<phi> y"
  shows
    "(\<exists>x\<^sub>0 xs. x\<^sub>0 \<in> a\<^sub>0 \<and> A.run (x\<^sub>0 ## xs) \<and> infs \<phi> (x\<^sub>0 ## xs))
    \<longleftrightarrow> (\<exists>as a bs. G.steps (a\<^sub>0 # as @ a # bs @ [a]) \<and> (\<forall>x \<in> a. \<phi> x) \<and> a \<noteq> {})"
    (is "?lhs \<longleftrightarrow> ?rhs")
proof
  assume ?lhs
  then obtain x\<^sub>0 xs where "x\<^sub>0 \<in> a\<^sub>0" "A.run (x\<^sub>0 ## xs)" "infs \<phi> xs"
    by auto
  have backward_reaches_A: "G.reaches a\<^sub>0 A" if "G_inv.reaches a\<^sub>0 A" for A
    using that by (simp add: G_invariant_subgraph_equivs[symmetric])
  from complete.simulation_run'[OF \<open>A.run _\<close> \<open>x\<^sub>0 \<in> _\<close>] a\<^sub>0_invariant \<open>x\<^sub>0 \<in> a\<^sub>0\<close> obtain as where
    "G.run (a\<^sub>0 ## as)" "stream_all2 (\<lambda>a b. a \<in> b \<and> P a \<and> Q b) xs as"
    by (auto dest: Q_P)
  from \<open>G.run (a\<^sub>0 ## as)\<close> have "G_inv.run (a\<^sub>0 ## as)"
    by (simp add: G_invariant_subgraph_equivs)
  from \<open>infs \<phi> _\<close> \<open>stream_all2 _ _ _\<close> have "infs (\<lambda>a. \<exists>x \<in> a. \<phi> x) as"
    by (rule alw_ev_lockstep) fast
  then have "infs (\<lambda>a. (\<forall>x \<in> a. \<phi> x) \<and> a \<noteq> {}) as"
    using assms(3) \<open>G_inv.run (a\<^sub>0 ## as)\<close>
    by (auto 4 5 simp: stream.pred_set dest!: G_inv.run_reachable backward_reaches_A
          elim!: infs_mono[rotated])
  with \<open>G.run _\<close> show ?rhs
    apply -
    apply (erule buechi_run_lasso)
     apply (simp; fail)
    by (metis (lifting)
          G.reaches1_steps_append G.reaches1_steps_iff G.reaches_stepsE G.steps_reaches1 list.sel(1))
next
  assume ?rhs
  then obtain as a x bs where "G.steps (a\<^sub>0 # as @ a # bs @ [a])" "\<forall>x \<in> a. \<phi> x" "x \<in> a"
    by auto
  then have "G.reaches a\<^sub>0 a" "G.reaches1 a\<^sub>0 a"
    apply -
    subgoal A
      by (smt G.steps_reaches append_Cons last_appendR last_snoc list.sel(1))
    subgoal
      by (metis A G.steps_ConsD G.steps_appendD2 G.steps_reaches1
            append_is_Nil_conv list.distinct(1) rtranclpD)
    done
  moreover from \<open>G.steps (a\<^sub>0 # as @ a # bs @ [a])\<close> have "G.steps (a # bs @ [a])"
    by (metis append_is_Nil_conv list.distinct(1) G.steps_ConsD G.steps_appendD2)
  ultimately have "G_inv.reaches1 a\<^sub>0 a" "G_inv.steps (a # bs @ [a])"
    by (simp add: G_invariant_subgraph_equivs G.reachable_def)+
  from \<open>G.reaches a\<^sub>0 a\<close> a\<^sub>0_invariant have "Q a"
    by (rule complete.PB_invariant.invariant_reaches)
  with assms(1,2) \<open>G.reaches _ _\<close> \<open>\<forall>x \<in> a. \<phi> x\<close> obtain x xs where
    "A.run (x ## xs)" "infs \<phi> xs" "x \<in> a"
    by - (rule backward.cycle_Buechi_run[OF \<open>G_inv.steps (a # bs @ [a])\<close> \<open>x \<in> a\<close>, where \<phi> = \<phi>],
          (blast dest: Q_P)+)
  from backward.backward_simulation_reaches1[OF \<open>G_inv.reaches1 a\<^sub>0 a\<close> \<open>x \<in> a\<close>] obtain x\<^sub>0 x' where
    "x\<^sub>0 \<in> a\<^sub>0" "x \<preceq> x'" "x\<^sub>0 \<rightarrow>\<^sup>+ x'"
    by auto
  then obtain ys where "A.steps (x\<^sub>0 # ys @ [x'])"
    using A.reaches1_steps_iff by auto
  from backward.simulation_run[OF \<open>A.run _\<close> \<open>x \<preceq> x'\<close>] obtain xs' where
    "A.run (x' ## xs')" "stream_all2 (\<preceq>) xs xs'"
    by (elim conjE exE)
  with \<open>A.steps _\<close> have "A.run (x\<^sub>0 ## ys @- x' ## xs')"
    by (metis A.extend_run A.steps_decomp
          append_Cons list.distinct(1) list.sel(1,3) shift_simps(1,2) stream.collapse)
  moreover from \<open>infs _ _\<close> \<open>stream_all2 _ _ _\<close> assms(2) have "infs \<phi> xs'"
    by (auto elim!: alw_ev_lockstep)
  ultimately show ?lhs
    using \<open>x\<^sub>0 \<in> a\<^sub>0\<close> by auto
qed

end

end (* Theory *)
