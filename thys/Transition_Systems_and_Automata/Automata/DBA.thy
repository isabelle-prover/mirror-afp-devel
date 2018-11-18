section {* Deterministic Büchi Automata *}

theory DBA
imports
  "../Basic/Sequence_Zip"
  "../Transition_Systems/Transition_System"
  "../Transition_Systems/Transition_System_Extra"
  "../Transition_Systems/Transition_System_Construction"
begin

  datatype ('label, 'state) dba = dba
    (alphabet: "'label set")
    (initial: "'state")
    (succ: "'label \<Rightarrow> 'state \<Rightarrow> 'state")
    (accepting: "'state \<Rightarrow> bool")

  global_interpretation dba: transition_system_initial
    "succ A" "\<lambda> a p. a \<in> alphabet A" "\<lambda> p. p = initial A"
    for A
    defines path = dba.path and run = dba.run and reachable = dba.reachable and nodes = dba.nodes and
      enableds = dba.enableds and paths = dba.paths and runs = dba.runs
    by this

  abbreviation "target \<equiv> dba.target"
  abbreviation "states \<equiv> dba.states"
  abbreviation "trace \<equiv> dba.trace"

  abbreviation successors :: "('label, 'state) dba \<Rightarrow> 'state \<Rightarrow> 'state set" where
    "successors \<equiv> dba.successors TYPE('label)"

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
      using that by (coinduction arbitrary: w p) (force elim: dba.run.cases)
    show "run A w p" if "w \<in> streams (alphabet A)"
      using that by (coinduction arbitrary: w p) (force elim: streams.cases)
  qed

  definition language :: "('label, 'state) dba \<Rightarrow> 'label stream set" where
    "language A \<equiv> {w. run A w (initial A) \<and> infs (accepting A) (trace A w (initial A))}"

  lemma language[intro]:
    assumes "run A w (initial A)" "infs (accepting A) (trace A w (initial A))"
    shows "w \<in> language A"
    using assms unfolding language_def by auto
  lemma language_elim[elim]:
    assumes "w \<in> language A"
    obtains "run A w (initial A)" "infs (accepting A) (trace A w (initial A))"
    using assms unfolding language_def by auto

  lemma language_alphabet: "language A \<subseteq> streams (alphabet A)"
    unfolding language_def run_alt_def using sset_streams by auto

  (* TODO: the following statements are equivalent:
      run A w p
      sset w \<subseteq> alphabet A
      w \<in> streams (alphabet A)
    figure out which is the most useful representation, try to use that everywhere *)

  (* TODO: extract acceptance into constant, have special case for empty set, remove assumption *)
  definition dbai :: "('label, 'state) dba list \<Rightarrow> ('label, 'state list \<times> nat) dba" where
    "dbai AA \<equiv> dba
      (\<Inter>(alphabet ` (set AA)))
      (map initial AA, 0)
      (\<lambda> a (pp, k). (map2 (\<lambda> A p. succ A a p) AA pp,
        if accepting (AA ! k) (pp ! k) then Suc k mod length AA else k))
      (\<lambda> (pp, k). accepting (AA ! k) (pp ! k))"

  lemma dbai_target:
    assumes "length pp = length AA"
    shows "fst (target (dbai AA) w (pp, k)) = map2 (\<lambda> A. target A w) AA pp"
  using assms
  proof (induct w arbitrary: pp k)
    case (Nil)
    show ?case using Nil by (simp add: case_prod_beta)
  next
    case (Cons a w)
    let ?qq = "map2 (\<lambda> A. succ A a) AA pp"
    let ?l = "if accepting (AA ! k) (pp ! k) then Suc k mod length AA else k"
    have "fst (target (dbai AA) (a # w) (pp, k)) = fst (target (dbai AA) w (?qq, ?l))"
      unfolding dbai_def by simp
    also have "\<dots> = map2 (\<lambda> A. target A w) AA ?qq" using Cons by simp
    also have "\<dots> = map2 (\<lambda> A. target A w \<circ> succ A a) AA pp"
      unfolding map_zip_map2 zip_assoc zip_same_conv_map map_zip_map by auto
    also have "\<dots> = map2 (\<lambda> A. target A (a # w)) AA pp" by simp
    finally show ?case by this
  qed
  lemma dbai_steady:
    assumes "length pp = length AA" "k < length AA"
    assumes "\<And> q. q \<in> set (butlast (pp ! k # states (AA ! k) w (pp ! k))) \<Longrightarrow> \<not> accepting (AA ! k) q"
    shows "snd (target (dbai AA) w (pp, k)) = k"
    using assms unfolding dbai_def by (induct w arbitrary: pp) (force+)
  lemma dbai_steady':
    assumes "\<And> qql. qql \<in> set (butlast (ppk # states (dbai AA) w ppk)) \<Longrightarrow> \<not> accepting (dbai AA) qql"
    shows "snd (target (dbai AA) w ppk) = snd ppk"
  using assms
  proof (induct w arbitrary: ppk)
    case (Nil)
    show ?case by simp
  next
    case (Cons a w)
    have "snd (target (dbai AA) (a # w) ppk) = snd (succ (dbai AA) a ppk)" using Cons by auto
    also have "\<dots> = snd ppk" using Cons(2) unfolding dbai_def by (auto simp: case_prod_beta)
    finally show ?case by this
  qed

  lemma dbai_skip_accepting:
    assumes "infs (accepting (dbai AA)) (trace (dbai AA) w (pp, k))"
    obtains u v qq
    where "w = u @- v" "target (dbai AA) u (pp, k) = (qq, k)" "accepting (dbai AA) (qq, k)"
  proof -
    have 1: "Collect (accepting (dbai AA)) \<inter> sset ((pp, k) ## trace (dbai AA) w (pp, k)) \<noteq> {}"
      using infs_any assms(1) by auto
    obtain ys a zs where 2:
      "(pp, k) ## trace (dbai AA) w (pp, k) = ys @- a ## zs"
      "Collect (accepting (dbai AA)) \<inter> set ys = {}"
      "a \<in> Collect (accepting (dbai AA))"
      using split_stream_first 1 by this
    obtain qq l where 3: "a = (qq, l)" by force
    define u where "u = stake (length ys) w"
    define v where "v = sdrop (length ys) w"
    have 4: "w = u @- v" unfolding u_def v_def by simp
    have "(pp, k) # states (dbai AA) u (pp, k) =
      stake (Suc (length ys)) ((pp, k) ## trace (dbai AA) w (pp, k))" unfolding u_def by simp
    also have "(pp, k) ## trace (dbai AA) w (pp, k) = ys @- a ## zs" using 2(1) by this
    also have "stake (Suc (length ys)) \<dots> = ys @ [a]" unfolding stake_Suc using eq_shift by auto
    finally have 5: "(pp, k) # states (dbai AA) u (pp, k) = ys @ [a]" by this
    have 6: "target (dbai AA) u (pp, k) = (qq, l)" unfolding dba.target_alt_def 3 5 by simp
    have 7: "Collect (accepting (dbai AA)) \<inter> set (butlast ((pp, k) # states (dbai AA) u (pp, k))) = {}"
      using 2(2) 5 unfolding dbai_def by simp
    have 8: "k = l" using dbai_steady' 6 7 by fastforce
    show ?thesis
    proof
      show "w = u @- v" using 4 by this
      show "target (dbai AA) u (pp, k) = (qq, k)" using 6 8 by simp
      show "accepting (dbai AA) (qq, k)" using 2(3) 3 8 by auto
    qed
  qed
  lemma dbai_skip_increment:
    assumes "infs (accepting (dbai AA)) (trace (dbai AA) w (pp, k))"
    obtains u v qq
    where "w = u @- v" "u \<noteq> []" "target (dbai AA) u (pp, k) = (qq, Suc k mod length AA)"
  proof -
    obtain u v qq where 1:
      "w = u @- v"
      "target (dbai AA) u (pp, k) = (qq, k)"
      "accepting (dbai AA) (qq, k)"
      using dbai_skip_accepting assms by this
    show ?thesis
    proof
      show "w = (u @ [shd v]) @- stl v" using 1 by simp
      show "u @ [shd v] \<noteq> []" by simp
      show "target (dbai AA) (u @ [shd v]) (pp, k) =
        (map2 (\<lambda> A p. succ A (shd v) p) AA qq, Suc k mod length AA)"
        using 1(2, 3) unfolding dbai_def by simp
    qed
  qed
  lemma dbai_skip_arbitrary:
    assumes "k < length AA" "l < length AA"
    assumes "infs (accepting (dbai AA)) (trace (dbai AA) w (pp, k))"
    obtains u v qq
    where "w = u @- v" "target (dbai AA) u (pp, k) = (qq, l)"
  using assms
  proof (induct "nat ((int l - int k) mod length AA)" arbitrary: thesis l)
    case (0)
    have 1: "length AA > 0" using assms(1) by auto
    have 2: "(int l - int k) mod length AA = 0"
    proof (rule antisym)
      show "(int l - int k) mod length AA \<le> 0" using 0(1) by simp
      show "(int l - int k) mod length AA \<ge> 0" using 1 by simp
    qed
    have 3: "int l mod length AA = int k mod length AA" using mod_eq_dvd_iff 2 by force
    have 4: "k = l" using 0(3, 4) 3 by simp
    show ?case
    proof (rule 0(2))
      show "w = [] @- w" by simp
      show "target (dbai AA) [] (pp, k) = (pp, l)" using 4 by simp
    qed
  next
    case (Suc n)
    have 1: "length AA > 0" using assms(1) by auto
    define l' where "l' = nat ((int l - 1) mod length AA)"
    obtain u v qq where 2: "w = u @- v" "target (dbai AA) u (pp, k) = (qq, l')"
    proof (rule Suc(1))
      have 2: "Suc n < length AA" using nat_less_iff Suc(2) 1 by simp
      have "n = nat (int n)" by simp
      also have "int n = (int (Suc n) - 1) mod length AA" using 2 by simp
      also have "\<dots> = (int l - int k - 1) mod length AA" using Suc(2) by (simp add: mod_simps)
      also have "\<dots> = (int l - 1 - int k) mod length AA" by (simp add: algebra_simps)
      also have "\<dots> = (int l' - int k) mod length AA" using l'_def 1 by (simp add: mod_simps)
      finally show "n = nat ((int l' - int k) mod length AA)" by this
      show "k < length AA" using Suc(4) by this
      show "l' < length AA" using nat_less_iff l'_def 1 by simp
      show "infs (accepting (dbai AA)) (trace (dbai AA) w (pp, k))" using Suc(6) by this
    qed
    obtain vu vv tt where 3: "v = vu @- vv" "target (dbai AA) vu (qq, l') = (tt, Suc l' mod length AA)"
    proof (rule dbai_skip_increment)
      show "infs (accepting (dbai AA)) (trace (dbai AA) v (qq, l'))" using Suc(6) 2 by simp
    qed
    show ?case
    proof (rule Suc(3))
      have "l = nat (int l)" by simp
      also have "int l = int l mod length AA" using Suc(5) by simp
      also have "\<dots> = int (Suc l') mod length AA" using l'_def 1 by (simp add: mod_simps)
      finally have 4: "l = Suc l' mod length AA" using nat_mod_as_int by metis
      show "w = (u @ vu) @- vv" unfolding 2(1) 3(1) by simp
      show "target (dbai AA) (u @ vu) (pp, k) = (tt, l)" using 2(2) 3(2) 4 by simp
    qed
  qed
  lemma dbai_skip_arbitrary_accepting:
    assumes "k < length AA" "l < length AA"
    assumes "infs (accepting (dbai AA)) (trace (dbai AA) w (pp, k))"
    obtains u v qq
    where "w = u @- v" "target (dbai AA) u (pp, k) = (qq, l)" "accepting (dbai AA) (qq, l)"
  proof -
    obtain u v qq where 1: "w = u @- v" "target (dbai AA) u (pp, k) = (qq, l)"
      using dbai_skip_arbitrary assms by this
    have 2: "infs (accepting (dbai AA)) (trace (dbai AA) v (qq, l))"
      using assms(3) 1(2) unfolding 1(1) by simp
    obtain vu vv tt where 3:
      "v = vu @- vv"
      "target (dbai AA) vu (qq, l) = (tt, l)"
      "accepting (dbai AA) (tt, l)"
      using dbai_skip_accepting 2 by this
    show ?thesis
    proof
      show "w = (u @ vu) @- vv" using 1(1) 3(1) by simp
      show "target (dbai AA) (u @ vu) (pp, k) = (tt, l)" using 1(2) 3(2) by simp
      show "accepting (dbai AA) (tt, l)" using 3(3) by this
    qed
  qed

  lemma infs_dbai_dba:
    assumes "length pp = length AA" "k < length AA"
    assumes "infs (accepting (dbai AA)) (trace (dbai AA) w (pp, k))"
    assumes "i < length AA"
    shows "infs (accepting (AA ! i)) (trace (AA ! i) w (pp ! i))"
  using assms(1, 2, 3)
  proof (coinduction arbitrary: w pp k rule: dba.infs_trace_coinduct)
    case (infs_trace w pp k)
    obtain u v qq where 1:
      "w = u @- v" "target (dbai AA) u (pp, k) = (qq, i)" "accepting (dbai AA) (qq, i)"
      using dbai_skip_arbitrary_accepting infs_trace(2) assms(4) infs_trace(3) by this
    have "target (AA ! i) u (pp ! i) = map2 (\<lambda> A. target A u) AA pp ! i"
      using infs_trace(1) assms(4) by simp
    also have "map2 (\<lambda> A. target A u) AA pp = fst (target (dbai AA) u (pp, k))"
      using dbai_target infs_trace(1) by force
    also have "\<dots> = qq" using 1(2) by simp
    finally have 2: "target (AA ! i) u (pp ! i) = qq ! i" by this
    obtain pp' l where 3: "succ (dbai AA) (shd w) (pp, k) = (pp', l)" by force
    have 4: "infs (accepting (dbai AA)) (trace (dbai AA) (shd w ## stl w) (pp, k))"
      using infs_trace(3) by simp
    show ?case
    proof (intro exI conjI bexI)
      show "w = u @- v" using 1(1) by this
      show "accepting (AA ! i) (target (AA ! i) u (pp ! i))" using 1(3) 2 unfolding dbai_def by simp
      show "w = [shd w] @- stl w" "[shd w] \<noteq> []" "stl w = stl w" by auto
      show "target (AA ! i) [shd w] (pp ! i) = pp' ! i"
        using infs_trace(1) assms(4) 3 unfolding dbai_def by auto
      show "infs (accepting (dbai AA)) (trace (dbai AA) (stl w) (pp', l))"
        using 3 4 unfolding sscan_scons by simp
      show "l < length AA" using mod_Suc infs_trace(2) 3 unfolding dbai_def by auto
      show "length pp' = length AA" using infs_trace(1) assms(3) 3 unfolding dbai_def by auto
    qed
  qed
  lemma infs_dba_dbai:
    assumes "length pp = length AA" "k < length AA"
    assumes "\<And> i. i < length AA \<Longrightarrow> infs (accepting (AA ! i)) (trace (AA ! i) w (pp ! i))"
    shows "infs (accepting (dbai AA)) (trace (dbai AA) w (pp, k))"
  using assms
  proof (coinduction arbitrary: w pp k rule: dba.infs_trace_coinduct)
    case (infs_trace w pp k)
    have 1: "infs (accepting (AA ! k)) (trace (AA ! k) w (pp ! k))" using infs_trace(2, 3) by simp
    have 2: "{q. accepting (AA ! k) q} \<inter> sset (pp ! k ## trace (AA ! k) w (pp ! k)) \<noteq> {}"
      using infs_any 1 by auto
    obtain ys q zs where 3:
      "pp ! k ## trace (AA ! k) w (pp ! k) = ys @- q ## zs"
      "{q. accepting (AA ! k) q} \<inter> set ys = {}"
      "q \<in> {q. accepting (AA ! k) q}"
      using split_stream_first 2 by this
    define u where "u = stake (length ys) w"
    define v where "v = sdrop (length ys) w"
    obtain qq l where 4: "target (dbai AA) u (pp, k) = (qq, l)" by force
    have "pp ! k # states (AA ! k) u (pp ! k) =
      stake (length (ys @ [q])) (pp ! k ## trace (AA ! k) w (pp ! k))" unfolding u_def by simp
    also have "pp ! k ## trace (AA ! k) w (pp ! k) = (ys @ [q]) @- zs" using 3(1) by simp
    also have "stake (length (ys @ [q])) \<dots> = ys @ [q]" unfolding stake_shift by simp
    finally have 5: "pp ! k # states (AA ! k) u (pp ! k) = ys @ [q]" by this
    have 6: "butlast (pp ! k # states (AA ! k) u (pp ! k)) = ys" using 5 by auto
    have "l = snd (target (dbai AA) u (pp, k))" unfolding 4 by simp
    also have "\<dots> = k" using dbai_steady infs_trace(1, 2) 3(2) 6 by blast
    finally have 7: "k = l" by rule
    have "qq = fst (target (dbai AA) u (pp, k))" unfolding 4 by simp
    also have "\<dots> = map2 (\<lambda> A. target A u) AA pp" using dbai_target infs_trace(1) by this
    also have "\<dots> ! l = target (AA ! k) u (pp ! k)" using infs_trace(1, 2) unfolding 7 by simp
    also have "\<dots> = last (pp ! k # states (AA ! k) u (pp ! k))" unfolding scan_last by rule
    also have "\<dots> = q" unfolding 5 by simp
    finally have 8: "qq ! l = q" by this
    have 9: "accepting (AA ! l) (qq ! l)" using 3(3) unfolding 7 8 by simp
    obtain x y where 10: "succ (dbai AA) (shd w) (pp, k) = (x, y)" by force
    have 11: "\<forall> i < length AA. infs (accepting (AA ! i)) (trace (AA ! i) (shd w ## stl w) (pp ! i))"
      using infs_trace(3) by simp
    have 12: "succ (AA ! i) (shd w) (pp ! i) = x ! i" if "i < length AA" for i
      using infs_trace(1) 10 that unfolding dbai_def by auto
    show ?case
    proof (intro exI conjI bexI)
      show "w = u @- v" unfolding u_def v_def by simp
      show "accepting (dbai AA) (target (dbai AA) u (pp, k))" using 4 9 unfolding dbai_def by auto
      show "w = [shd w] @- stl w" "[shd w] \<noteq> []" "stl w = stl w" by auto
      show "target (dbai AA) [shd w] (pp, k) = (x, y)" using 10 by simp
      show "y < length AA" using mod_Suc infs_trace(2) 10 unfolding dbai_def by auto
      show "length x = length AA" using infs_trace(1) 10 unfolding dbai_def by auto
      show "\<forall> i < length AA. infs (accepting (AA ! i)) (trace (AA ! i) (stl w) (x ! i))"
        using 11 12 unfolding sscan_scons by simp
    qed
  qed

  lemma dbai_language:
    assumes "AA \<noteq> []"
    shows "language (dbai AA) = \<Inter>(language ` (set AA))"
  proof safe
    fix w A
    assume 1: "w \<in> language (dbai AA)" "A \<in> set AA"
    obtain 2:
      "run (dbai AA) w (initial (dbai AA))"
      "infs (accepting (dbai AA)) (trace (dbai AA) w (initial (dbai AA)))"
      using 1(1) by rule
    obtain i where 3: "A = AA ! i" "i < length AA" using 1(2) unfolding in_set_conv_nth by auto
    obtain pp k where 4: "initial (dbai AA) = (pp, k)" by force
    have 5: "initial (AA ! i) = pp ! i" using 3(2) 4 unfolding dbai_def by auto
    show "w \<in> language A"
    proof
      show "run A w (initial A)" using 1(2) 2(1) unfolding run_alt_def dbai_def by auto
      show "infs (accepting A) (trace A w (initial A))"
      unfolding 3(1) 5
      proof (rule infs_dbai_dba)
        show "length pp = length AA" using 4 unfolding dbai_def by auto
        show "k < length AA" using assms 4 unfolding dbai_def by simp
        show "infs (accepting (dbai AA)) (trace (dbai AA) w (pp, k))" using 2(2) unfolding 4 by this
        show "i < length AA" using 3(2) by this
      qed
    qed
  next
    fix w
    assume 1: "w \<in> \<Inter>(language ` (set AA))"
    have 2: "run A w (initial A)" "infs (accepting A) (trace A w (initial A))"
      if "A \<in> set AA" for A using 1 that by auto
    obtain pp k where 3: "initial (dbai AA) = (pp, k)" by force
    show "w \<in> language (dbai AA)"
    proof
      show "run (dbai AA) w (initial (dbai AA))" using 2(1) unfolding run_alt_def dbai_def by auto
      show "infs (accepting (dbai AA)) (trace (dbai AA) w (initial (dbai AA)))"
      unfolding 3
      proof (rule infs_dba_dbai)
        show "length pp = length AA" using 3 unfolding dbai_def by auto
        show "k < length AA" using assms 3 unfolding dbai_def by auto
        show "infs (accepting (AA ! i)) (trace (AA ! i) w (pp ! i))" if "i < length AA" for i
          using 2(2) 3 that unfolding dbai_def by auto
      qed
    qed
  qed

end