section {* Deterministic Büchi Automata Combinations *}

theory DBA_Combine
imports "DBA" "DGBA"
begin

  definition dbai' :: "('label, 'state) dba list \<Rightarrow> ('label, 'state list) dgba" where
    "dbai' AA \<equiv> dgba
      (INTER (set AA) dba.alphabet)
      (map dba.initial AA)
      (\<lambda> a pp. map2 (\<lambda> A p. dba.succ A a p) AA pp)
      (map (\<lambda> k pp. dba.accepting (AA ! k) (pp ! k)) [0 ..< length AA])"

  lemma dbai'_trace_smap:
    assumes "length pp = length AA" "k < length AA"
    shows "smap (\<lambda> pp. pp ! k) (dgba.trace (dbai' AA) w pp) = dba.trace (AA ! k) w (pp ! k)"
    using assms unfolding dbai'_def by (coinduction arbitrary: w pp) (force)

  lemma dbai'_language: "DGBA.language (dbai' AA) = INTER (set AA) DBA.language"
  proof safe
    fix w A
    assume 1: "w \<in> DGBA.language (dbai' AA)" "A \<in> set AA"
    obtain 2:
      "dgba.run (dbai' AA) w (dgba.initial (dbai' AA))"
      "gen infs (dgba.accepting (dbai' AA)) (dgba.trace (dbai' AA) w (dgba.initial (dbai' AA)))"
      using 1(1) by rule
    obtain k where 3: "A = AA ! k" "k < length AA" using 1(2) unfolding in_set_conv_nth by auto
    have 4: "(\<lambda> pp. dba.accepting A (pp ! k)) \<in> set (dgba.accepting (dbai' AA))"
      using 3 unfolding dbai'_def by auto
    show "w \<in> DBA.language A"
    proof
      show "dba.run A w (dba.initial A)"
        using 1(2) 2(1) unfolding DBA.run_alt_def DGBA.run_alt_def dbai'_def by auto
      have "True \<longleftrightarrow> infs (\<lambda> pp. dba.accepting A (pp ! k)) (dgba.trace (dbai' AA) w (map dba.initial AA))"
        using 2(2) 4 unfolding dbai'_def by auto
      also have "\<dots> \<longleftrightarrow> infs (dba.accepting A) (smap (\<lambda> pp. pp ! k)
        (dgba.trace (dbai' AA) w (map dba.initial AA)))" by (simp add: comp_def)
      also have "smap (\<lambda> pp. pp ! k) (dgba.trace (dbai' AA) w (map dba.initial AA)) =
        dba.trace (AA ! k) w (map dba.initial AA ! k)" using 3(2) by (fastforce intro: dbai'_trace_smap)
      also have "\<dots> = dba.trace A w (dba.initial A)" using 3 by auto
      finally show "infs (dba.accepting A) (dba.trace A w (dba.initial A))" by simp
    qed
  next
    fix w
    assume 1: "w \<in> INTER (set AA) DBA.language"
    have 2: "dba.run A w (dba.initial A)" "infs (dba.accepting A) (dba.trace A w (dba.initial A))"
      if "A \<in> set AA" for A using 1 that by auto
    show "w \<in> DGBA.language (dbai' AA)"
    proof (intro DGBA.language ballI gen)
      show "dgba.run (dbai' AA) w (dgba.initial (dbai' AA))"
        using 2(1) unfolding DBA.run_alt_def DGBA.run_alt_def dbai'_def by auto
    next
      fix P
      assume 3: "P \<in> set (dgba.accepting (dbai' AA))"
      obtain k where 4: "P = (\<lambda> pp. dba.accepting (AA ! k) (pp ! k))" "k < length AA"
        using 3 unfolding dbai'_def by auto
      have "True \<longleftrightarrow> infs (dba.accepting (AA ! k)) (dba.trace (AA ! k) w (map dba.initial AA ! k))"
        using 2(2) 4(2) by auto
      also have "dba.trace (AA ! k) w (map dba.initial AA ! k) =
        smap (\<lambda> pp. pp ! k) (dgba.trace (dbai' AA) w (map dba.initial AA))"
        using 4(2) by (fastforce intro: dbai'_trace_smap[symmetric])
      also have "infs (dba.accepting (AA ! k)) \<dots> \<longleftrightarrow> infs P (dgba.trace (dbai' AA) w (map dba.initial AA))"
        unfolding 4(1) by (simp add: comp_def)
      also have "map dba.initial AA = dgba.initial (dbai' AA)" unfolding dbai'_def by simp
      finally show "infs P (dgba.trace (dbai' AA) w (dgba.initial (dbai' AA)))" by simp
    qed
  qed

  definition dbai :: "('label, 'state) dba list \<Rightarrow> ('label, 'state list degen) dba" where
    "dbai = degen \<circ> dbai'"

  lemma dbai_language: "DBA.language (dbai AA) = INTER (set AA) DBA.language"
    unfolding dbai_def using degen_language dbai'_language by auto

  definition dbau :: "('label, 'state) dba list \<Rightarrow> ('label, 'state list) dba" where
    "dbau AA \<equiv> dba
      (UNION (set AA) dba.alphabet)
      (map dba.initial AA)
      (\<lambda> a pp. map2 (\<lambda> A p. dba.succ A a p) AA pp)
      (\<lambda> pp. \<exists> k < length AA. dba.accepting (AA ! k) (pp ! k))"

  lemma dbau_trace_smap:
    assumes "length pp = length AA" "k < length AA"
    shows "smap (\<lambda> pp. pp ! k) (dba.trace (dbau AA) w pp) = dba.trace (AA ! k) w (pp ! k)"
    using assms unfolding dbau_def by (coinduction arbitrary: w pp) (force)

  lemma dbau_language:
    assumes "INTER (set AA) dba.alphabet = UNION (set AA) dba.alphabet"
    shows "DBA.language (dbau AA) = UNION (set AA) DBA.language"
  proof safe
    fix w
    assume 1: "w \<in> DBA.language (dbau AA)"
    obtain 2:
      "dba.run (dbau AA) w (dba.initial (dbau AA))"
      "infs (dba.accepting (dbau AA)) (dba.trace (dbau AA) w (dba.initial (dbau AA)))"
      using 1 by rule
    obtain k where 3:
      "k < length AA"
      "infs (\<lambda> pp. dba.accepting (AA ! k) (pp ! k)) (dba.trace (dbau AA) w (map dba.initial AA))"
      using 2(2) unfolding dbau_def by auto
    show "w \<in> UNION (set AA) DBA.language"
    proof (intro UN_I DBA.language)
      show "AA ! k \<in> set AA" using 3(1) by simp
      show "dba.run (AA ! k) w (dba.initial (AA ! k))"
        using assms 2(1) 3(1) unfolding DBA.run_alt_def DGBA.run_alt_def dbau_def by force
      have "True \<longleftrightarrow> infs (\<lambda> pp. dba.accepting (AA ! k) (pp ! k))
        (dba.trace (dbau AA) w (map dba.initial AA))" using 3(2) by auto
      also have "\<dots> \<longleftrightarrow> infs (dba.accepting (AA ! k))
        (smap (\<lambda> pp. pp ! k) (dba.trace (dbau AA) w (map dba.initial AA)))" by (simp add: comp_def)
      also have "smap (\<lambda> pp. pp ! k) (dba.trace (dbau AA) w (map dba.initial AA)) =
        dba.trace (AA ! k) w (map dba.initial AA ! k)" using 3(1) by (fastforce intro: dbau_trace_smap)
      also have "\<dots> = dba.trace (AA ! k) w (dba.initial (AA ! k))" using 3 by auto
      finally show "infs (dba.accepting (AA ! k)) (dba.trace (AA ! k) w (dba.initial (AA ! k)))" by simp
    qed
  next
    fix A w
    assume 1: "A \<in> set AA" "w \<in> DBA.language A"
    obtain 2: "dba.run A w (dba.initial A)" "infs (dba.accepting A) (dba.trace A w (dba.initial A))"
      using 1(2) by rule
    obtain k where 3: "A = AA ! k" "k < length AA" using 1(1) unfolding in_set_conv_nth by auto
    show "w \<in> DBA.language (dbau AA)"
    proof
      show "dba.run (dbau AA) w (dba.initial (dbau AA))"
        using 1(1) 2(1) unfolding DBA.run_alt_def DGBA.run_alt_def dbau_def by auto
      have "True \<longleftrightarrow> infs (dba.accepting (AA ! k)) (dba.trace (AA ! k) w (map dba.initial AA ! k))"
        using 2(2) 3 by auto
      also have "dba.trace (AA ! k) w (map dba.initial AA ! k) =
        smap (\<lambda> pp. pp ! k) (dba.trace (dbau AA) w (map dba.initial AA))"
        using 3(2) by (fastforce intro: dbau_trace_smap[symmetric])
      also have "infs (dba.accepting (AA ! k)) \<dots> \<longleftrightarrow> infs (\<lambda> pp. dba.accepting (AA ! k) (pp ! k))
        (dba.trace (dbau AA) w (map dba.initial AA))" by (simp add: comp_def)
      finally show "infs (dba.accepting (dbau AA)) (dba.trace (dbau AA) w (dba.initial (dbau AA)))"
        using 3(2) unfolding dbau_def by auto
    qed
  qed

end