section {* Deterministic Büchi Automata Combinations *}

theory DBA_Combine
imports "DBA" "DGBA"
begin

  definition dbgail :: "('label, 'state) dba list \<Rightarrow> ('label, 'state list) dgba" where
    "dbgail AA \<equiv> dgba
      (INTER (set AA) dba.alphabet)
      (map dba.initial AA)
      (\<lambda> a pp. map2 (\<lambda> A p. dba.succ A a p) AA pp)
      (map (\<lambda> k pp. dba.accepting (AA ! k) (pp ! k)) [0 ..< length AA])"

  lemma dbgail_trace_smap:
    assumes "length pp = length AA" "k < length AA"
    shows "smap (\<lambda> pp. pp ! k) (dgba.trace (dbgail AA) w pp) = dba.trace (AA ! k) w (pp ! k)"
    using assms unfolding dbgail_def by (coinduction arbitrary: w pp) (force)
  lemma dbgail_nodes_length:
    assumes "pp \<in> DGBA.nodes (dbgail AA)"
    shows "length pp = length AA"
    using assms unfolding dbgail_def by induct auto
  lemma dbgail_nodes[intro]:
    assumes "pp \<in> DGBA.nodes (dbgail AA)" "k < length pp"
    shows "pp ! k \<in> DBA.nodes (AA ! k)"
    using assms unfolding dbgail_def by induct auto

  lemma dbgail_finite[intro]:
    assumes "list_all (finite \<circ> DBA.nodes) AA"
    shows "finite (DGBA.nodes (dbgail AA))"
  proof (rule finite_subset)
    show "DGBA.nodes (dbgail AA) \<subseteq> listset (map DBA.nodes AA)"
      by (force simp: listset_member list_all2_conv_all_nth dbgail_nodes_length)
    have "finite (listset (map DBA.nodes AA)) \<longleftrightarrow> list_all finite (map DBA.nodes AA)"
      by (rule listset_finite) (auto simp: list_all_iff)
    then show "finite (listset (map DBA.nodes AA))" using assms by (simp add: list.pred_map)
  qed

  lemma dbgail_language[simp]: "DGBA.language (dbgail AA) = INTER (set AA) DBA.language"
  proof safe
    fix w A
    assume 1: "w \<in> DGBA.language (dbgail AA)" "A \<in> set AA"
    obtain 2:
      "dgba.run (dbgail AA) w (dgba.initial (dbgail AA))"
      "gen infs (dgba.accepting (dbgail AA)) (dgba.trace (dbgail AA) w (dgba.initial (dbgail AA)))"
      using 1(1) by rule
    obtain k where 3: "A = AA ! k" "k < length AA" using 1(2) unfolding in_set_conv_nth by auto
    have 4: "(\<lambda> pp. dba.accepting A (pp ! k)) \<in> set (dgba.accepting (dbgail AA))"
      using 3 unfolding dbgail_def by auto
    show "w \<in> DBA.language A"
    proof
      show "dba.run A w (dba.initial A)"
        using 1(2) 2(1) unfolding DBA.run_alt_def DGBA.run_alt_def dbgail_def by auto
      have "True \<longleftrightarrow> infs (\<lambda> pp. dba.accepting A (pp ! k)) (dgba.trace (dbgail AA) w (map dba.initial AA))"
        using 2(2) 4 unfolding dbgail_def by auto
      also have "\<dots> \<longleftrightarrow> infs (dba.accepting A) (smap (\<lambda> pp. pp ! k)
        (dgba.trace (dbgail AA) w (map dba.initial AA)))" by (simp add: comp_def)
      also have "smap (\<lambda> pp. pp ! k) (dgba.trace (dbgail AA) w (map dba.initial AA)) =
        dba.trace (AA ! k) w (map dba.initial AA ! k)" using 3(2) by (fastforce intro: dbgail_trace_smap)
      also have "\<dots> = dba.trace A w (dba.initial A)" using 3 by auto
      finally show "infs (dba.accepting A) (dba.trace A w (dba.initial A))" by simp
    qed
  next
    fix w
    assume 1: "w \<in> INTER (set AA) DBA.language"
    have 2: "dba.run A w (dba.initial A)" "infs (dba.accepting A) (dba.trace A w (dba.initial A))"
      if "A \<in> set AA" for A using 1 that by auto
    show "w \<in> DGBA.language (dbgail AA)"
    proof (intro DGBA.language ballI gen)
      show "dgba.run (dbgail AA) w (dgba.initial (dbgail AA))"
        using 2(1) unfolding DBA.run_alt_def DGBA.run_alt_def dbgail_def by auto
    next
      fix P
      assume 3: "P \<in> set (dgba.accepting (dbgail AA))"
      obtain k where 4: "P = (\<lambda> pp. dba.accepting (AA ! k) (pp ! k))" "k < length AA"
        using 3 unfolding dbgail_def by auto
      have "True \<longleftrightarrow> infs (dba.accepting (AA ! k)) (dba.trace (AA ! k) w (map dba.initial AA ! k))"
        using 2(2) 4(2) by auto
      also have "dba.trace (AA ! k) w (map dba.initial AA ! k) =
        smap (\<lambda> pp. pp ! k) (dgba.trace (dbgail AA) w (map dba.initial AA))"
        using 4(2) by (fastforce intro: dbgail_trace_smap[symmetric])
      also have "infs (dba.accepting (AA ! k)) \<dots> \<longleftrightarrow> infs P (dgba.trace (dbgail AA) w (map dba.initial AA))"
        unfolding 4(1) by (simp add: comp_def)
      also have "map dba.initial AA = dgba.initial (dbgail AA)" unfolding dbgail_def by simp
      finally show "infs P (dgba.trace (dbgail AA) w (dgba.initial (dbgail AA)))" by simp
    qed
  qed

  definition dbail :: "('label, 'state) dba list \<Rightarrow> ('label, 'state list degen) dba" where
    "dbail = degen \<circ> dbgail"

  lemma dbail_finite[intro]:
    assumes "list_all (finite \<circ> DBA.nodes) AA"
    shows "finite (DBA.nodes (dbail AA))"
    using dbgail_finite assms unfolding dbail_def by auto

  lemma dbail_language[simp]: "DBA.language (dbail AA) = INTER (set AA) DBA.language"
    unfolding dbail_def using degen_language dbgail_language by auto

  definition dbaul :: "('label, 'state) dba list \<Rightarrow> ('label, 'state list) dba" where
    "dbaul AA \<equiv> dba
      (UNION (set AA) dba.alphabet)
      (map dba.initial AA)
      (\<lambda> a pp. map2 (\<lambda> A p. dba.succ A a p) AA pp)
      (\<lambda> pp. \<exists> k < length AA. dba.accepting (AA ! k) (pp ! k))"

  lemma dbaul_trace_smap:
    assumes "length pp = length AA" "k < length AA"
    shows "smap (\<lambda> pp. pp ! k) (dba.trace (dbaul AA) w pp) = dba.trace (AA ! k) w (pp ! k)"
    using assms unfolding dbaul_def by (coinduction arbitrary: w pp) (force)
  lemma dbaul_nodes_length:
    assumes "pp \<in> DBA.nodes (dbaul AA)"
    shows "length pp = length AA"
    using assms unfolding dbaul_def by induct auto
  lemma dbaul_nodes[intro]:
    assumes "INTER (set AA) dba.alphabet = UNION (set AA) dba.alphabet"
    assumes "pp \<in> DBA.nodes (dbaul AA)" "k < length pp"
    shows "pp ! k \<in> DBA.nodes (AA ! k)"
    using assms(2, 3, 1) unfolding dbaul_def by induct force+

  lemma dbaul_finite[intro]:
    assumes "INTER (set AA) dba.alphabet = UNION (set AA) dba.alphabet"
    assumes "list_all (finite \<circ> DBA.nodes) AA"
    shows "finite (DBA.nodes (dbaul AA))"
  proof (rule finite_subset)
    show "DBA.nodes (dbaul AA) \<subseteq> listset (map DBA.nodes AA)"
      using assms(1) by (force simp: listset_member list_all2_conv_all_nth dbaul_nodes_length)
    have "finite (listset (map DBA.nodes AA)) \<longleftrightarrow> list_all finite (map DBA.nodes AA)"
      by (rule listset_finite) (auto simp: list_all_iff)
    then show "finite (listset (map DBA.nodes AA))" using assms(2) by (simp add: list.pred_map)
  qed

  lemma dbaul_language[simp]:
    assumes "INTER (set AA) dba.alphabet = UNION (set AA) dba.alphabet"
    shows "DBA.language (dbaul AA) = UNION (set AA) DBA.language"
  proof safe
    fix w
    assume 1: "w \<in> DBA.language (dbaul AA)"
    obtain 2:
      "dba.run (dbaul AA) w (dba.initial (dbaul AA))"
      "infs (dba.accepting (dbaul AA)) (dba.trace (dbaul AA) w (dba.initial (dbaul AA)))"
      using 1 by rule
    obtain k where 3:
      "k < length AA"
      "infs (\<lambda> pp. dba.accepting (AA ! k) (pp ! k)) (dba.trace (dbaul AA) w (map dba.initial AA))"
      using 2(2) unfolding dbaul_def by auto
    show "w \<in> UNION (set AA) DBA.language"
    proof (intro UN_I DBA.language)
      show "AA ! k \<in> set AA" using 3(1) by simp
      show "dba.run (AA ! k) w (dba.initial (AA ! k))"
        using assms 2(1) 3(1) unfolding DBA.run_alt_def DGBA.run_alt_def dbaul_def by force
      have "True \<longleftrightarrow> infs (\<lambda> pp. dba.accepting (AA ! k) (pp ! k))
        (dba.trace (dbaul AA) w (map dba.initial AA))" using 3(2) by auto
      also have "\<dots> \<longleftrightarrow> infs (dba.accepting (AA ! k))
        (smap (\<lambda> pp. pp ! k) (dba.trace (dbaul AA) w (map dba.initial AA)))" by (simp add: comp_def)
      also have "smap (\<lambda> pp. pp ! k) (dba.trace (dbaul AA) w (map dba.initial AA)) =
        dba.trace (AA ! k) w (map dba.initial AA ! k)" using 3(1) by (fastforce intro: dbaul_trace_smap)
      also have "\<dots> = dba.trace (AA ! k) w (dba.initial (AA ! k))" using 3 by auto
      finally show "infs (dba.accepting (AA ! k)) (dba.trace (AA ! k) w (dba.initial (AA ! k)))" by simp
    qed
  next
    fix A w
    assume 1: "A \<in> set AA" "w \<in> DBA.language A"
    obtain 2: "dba.run A w (dba.initial A)" "infs (dba.accepting A) (dba.trace A w (dba.initial A))"
      using 1(2) by rule
    obtain k where 3: "A = AA ! k" "k < length AA" using 1(1) unfolding in_set_conv_nth by auto
    show "w \<in> DBA.language (dbaul AA)"
    proof
      show "dba.run (dbaul AA) w (dba.initial (dbaul AA))"
        using 1(1) 2(1) unfolding DBA.run_alt_def DGBA.run_alt_def dbaul_def by auto
      have "True \<longleftrightarrow> infs (dba.accepting (AA ! k)) (dba.trace (AA ! k) w (map dba.initial AA ! k))"
        using 2(2) 3 by auto
      also have "dba.trace (AA ! k) w (map dba.initial AA ! k) =
        smap (\<lambda> pp. pp ! k) (dba.trace (dbaul AA) w (map dba.initial AA))"
        using 3(2) by (fastforce intro: dbaul_trace_smap[symmetric])
      also have "infs (dba.accepting (AA ! k)) \<dots> \<longleftrightarrow> infs (\<lambda> pp. dba.accepting (AA ! k) (pp ! k))
        (dba.trace (dbaul AA) w (map dba.initial AA))" by (simp add: comp_def)
      finally show "infs (dba.accepting (dbaul AA)) (dba.trace (dbaul AA) w (dba.initial (dbaul AA)))"
        using 3(2) unfolding dbaul_def by auto
    qed
  qed

end