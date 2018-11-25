section {* Deterministic Co-Büchi Automata Combinations *}

theory DCA_Combine
imports "DCA" "DGCA"
begin

  definition dcai :: "('label, 'state) dca list \<Rightarrow> ('label, 'state list) dca" where
    "dcai AA \<equiv> dca
      (INTER (set AA) dca.alphabet)
      (map dca.initial AA)
      (\<lambda> a pp. map2 (\<lambda> A p. dca.succ A a p) AA pp)
      (\<lambda> pp. \<exists> k < length AA. dca.rejecting (AA ! k) (pp ! k))"

  lemma dcai_trace_smap:
    assumes "length pp = length AA" "k < length AA"
    shows "smap (\<lambda> pp. pp ! k) (dca.trace (dcai AA) w pp) = dca.trace (AA ! k) w (pp ! k)"
    using assms unfolding dcai_def by (coinduction arbitrary: w pp) (force)

  lemma dcai_language: "DCA.language (dcai AA) = INTER (set AA) DCA.language"
  proof safe
    fix A w
    assume 1: "w \<in> DCA.language (dcai AA)" "A \<in> set AA"
    obtain 2:
      "dca.run (dcai AA) w (dca.initial (dcai AA))"
      "\<not> infs (dca.rejecting (dcai AA)) (dca.trace (dcai AA) w (dca.initial (dcai AA)))"
      using 1(1) by rule
    obtain k where 3: "A = AA ! k" "k < length AA" using 1(2) unfolding in_set_conv_nth by auto
    have 4: "\<not> infs (\<lambda> pp. dca.rejecting A (pp ! k)) (dca.trace (dcai AA) w (map dca.initial AA))"
      using 2(2) 3 unfolding dcai_def by auto
    show "w \<in> DCA.language A"
    proof
      show "dca.run A w (dca.initial A)"
        using 1(2) 2(1) unfolding DCA.run_alt_def dcai_def by auto
      have "True \<longleftrightarrow> \<not> infs (\<lambda> pp. dca.rejecting A (pp ! k)) (dca.trace (dcai AA) w (map dca.initial AA))"
        using 4 by simp
      also have "\<dots> \<longleftrightarrow> \<not> infs (dca.rejecting A) (smap (\<lambda> pp. pp ! k)
        (dca.trace (dcai AA) w (map dca.initial AA)))" by (simp add: comp_def)
      also have "smap (\<lambda> pp. pp ! k) (dca.trace (dcai AA) w (map dca.initial AA)) =
        dca.trace (AA ! k) w (map dca.initial AA ! k)" using 3(2) by (fastforce intro: dcai_trace_smap)
      also have "\<dots> = dca.trace A w (dca.initial A)" using 3 by auto
      finally show "\<not> infs (dca.rejecting A) (DCA.trace A w (dca.initial A))" by simp
    qed
  next
    fix w
    assume 1: "w \<in> INTER (set AA) DCA.language"
    have 2: "dca.run A w (dca.initial A)" "\<not> infs (dca.rejecting A) (dca.trace A w (dca.initial A))"
      if "A \<in> set AA" for A using 1 that by auto
    have 3: "\<not> infs (\<lambda> pp. dca.rejecting (AA ! k) (pp ! k)) (dca.trace (dcai AA) w (map dca.initial AA))"
      if "k < length AA" for k
    proof -
      have "True \<longleftrightarrow> \<not> infs (dca.rejecting (AA ! k)) (dca.trace (AA ! k) w (map dca.initial AA ! k))"
        using 2(2) that by auto
      also have "dca.trace (AA ! k) w (map dca.initial AA ! k) =
        smap (\<lambda> pp. pp ! k) (dca.trace (dcai AA) w (map dca.initial AA))"
        using that by (fastforce intro: dcai_trace_smap[symmetric])
      also have "infs (dca.rejecting (AA ! k)) \<dots> \<longleftrightarrow> infs (\<lambda> pp. dca.rejecting (AA ! k) (pp ! k))
        (dca.trace (dcai AA) w (map dca.initial AA))" by (simp add: comp_def)
      finally show ?thesis by simp
    qed
    show "w \<in> DCA.language (dcai AA)"
    proof
      show "dca.run (dcai AA) w (dca.initial (dcai AA))"
        using 2(1) unfolding DCA.run_alt_def dcai_def by auto
      show "\<not> infs (dca.rejecting (dcai AA)) (dca.trace (dcai AA) w (dca.initial (dcai AA)))"
        using 3 unfolding dcai_def by auto
    qed
  qed

  definition dcau' :: "('label, 'state) dca list \<Rightarrow> ('label, 'state list) dgca" where
    "dcau' AA \<equiv> dgca
      (UNION (set AA) dca.alphabet)
      (map dca.initial AA)
      (\<lambda> a pp. map2 (\<lambda> A p. dca.succ A a p) AA pp)
      (map (\<lambda> k pp. dca.rejecting (AA ! k) (pp ! k)) [0 ..< length AA])"

  lemma dcau'_trace_smap:
    assumes "length pp = length AA" "k < length AA"
    shows "smap (\<lambda> pp. pp ! k) (dgca.trace (dcau' AA) w pp) = dca.trace (AA ! k) w (pp ! k)"
    using assms unfolding dcau'_def by (coinduction arbitrary: w pp) (force)

  lemma dcau'_language:
    assumes "INTER (set AA) dca.alphabet = UNION (set AA) dca.alphabet"
    shows "DGCA.language (dcau' AA) = UNION (set AA) DCA.language"
  proof safe
    fix w
    assume 1: "w \<in> DGCA.language (dcau' AA)"
    obtain k where 2:
      "dgca.run (dcau' AA) w (dgca.initial (dcau' AA))"
      "k < length AA"
      "\<not> infs (\<lambda> pp. dca.rejecting (AA ! k) (pp ! k)) (dgca.trace (dcau' AA) w (dgca.initial (dcau' AA)))"
      using 1 unfolding dcau'_def by force
    show "w \<in> UNION (set AA) DCA.language"
    proof (intro UN_I DCA.language)
      show "AA ! k \<in> set AA" using 2(2) by simp
      show "dca.run (AA ! k) w (dca.initial (AA ! k))"
        using assms 2(1, 2) unfolding DCA.run_alt_def DGCA.run_alt_def dcau'_def by force
      have "True \<longleftrightarrow> \<not> infs (\<lambda> pp. dca.rejecting (AA ! k) (pp ! k))
        (dgca.trace (dcau' AA) w (map dca.initial AA))" using 2(3) unfolding dcau'_def by auto
      also have "\<dots> \<longleftrightarrow> \<not> infs (dca.rejecting (AA ! k))
        (smap (\<lambda> pp. pp ! k) (dgca.trace (dcau' AA) w (map dca.initial AA)))" by (simp add: comp_def)
      also have "smap (\<lambda> pp. pp ! k) (dgca.trace (dcau' AA) w (map dca.initial AA)) =
        dca.trace (AA ! k) w (map dca.initial AA ! k)" using 2(2) by (fastforce intro: dcau'_trace_smap)
      also have "\<dots> = dca.trace (AA ! k) w (dca.initial (AA ! k))" using 2(2) by auto
      finally show "\<not> infs (dca.rejecting (AA ! k)) (dca.trace (AA ! k) w (dca.initial (AA ! k)))" by simp
    qed
  next
    fix A w
    assume 1: "A \<in> set AA" "w \<in> DCA.language A"
    obtain 2: "dca.run A w (dca.initial A)" "\<not> infs (dca.rejecting A) (dca.trace A w (dca.initial A))"
      using 1(2) by rule
    obtain k where 3: "A = AA ! k" "k < length AA" using 1(1) unfolding in_set_conv_nth by auto
    show "w \<in> DGCA.language (dcau' AA)"
    proof (intro DGCA.language bexI cogen)
      show "dgca.run (dcau' AA) w (dgca.initial (dcau' AA))"
        using 1(1) 2(1) unfolding DCA.run_alt_def DGCA.run_alt_def dcau'_def by auto
      have "True \<longleftrightarrow> \<not> infs (dca.rejecting (AA ! k)) (dca.trace (AA ! k) w (map dca.initial AA ! k))"
        using 2(2) 3 by auto
      also have "dca.trace (AA ! k) w (map dca.initial AA ! k) =
        smap (\<lambda> pp. pp ! k) (dgca.trace (dcau' AA) w (map dca.initial AA))"
        using 3(2) by (fastforce intro: dcau'_trace_smap[symmetric])
      also have "\<not> infs (dca.rejecting (AA ! k)) \<dots> \<longleftrightarrow> \<not> infs (\<lambda> pp. dca.rejecting (AA ! k) (pp ! k))
        (dgca.trace (dcau' AA) w (map dca.initial AA))" by (simp add: comp_def)
      also have "map dca.initial AA = dgca.initial (dcau' AA)" unfolding dcau'_def by simp
      finally show "\<not> infs (\<lambda> pp. dca.rejecting (AA ! k) (pp ! k)) (dgca.trace (dcau' AA) w (dgca.initial (dcau' AA)))"
        by simp
      show "(\<lambda> pp. dca.rejecting (AA ! k) (pp ! k)) \<in> set (dgca.rejecting (dcau' AA))"
        unfolding dcau'_def using 3(2) by simp
    qed
  qed

  definition dcau :: "('label, 'state) dca list \<Rightarrow> ('label, 'state list degen) dca" where
    "dcau = degen \<circ> dcau'"

  lemma dcau_language:
    assumes "INTER (set AA) dca.alphabet = UNION (set AA) dca.alphabet"
    shows "DCA.language (dcau AA) = UNION (set AA) DCA.language"
    unfolding dcau_def using degen_language dcau'_language[OF assms] by auto

end