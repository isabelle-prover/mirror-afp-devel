section {* Deterministic Rabin Automata Combinations *}

theory DRA_Combine
imports "DBA" "DCA" "DRA"
begin

  definition from_dba :: "('label, 'state) dba \<Rightarrow> ('label, 'state) dra" where
    "from_dba A \<equiv> dra (dba.alphabet A) (dba.initial A) (dba.succ A) [(dba.accepting A, bot)]"

  lemma from_dba_language: "DRA.language (from_dba A) = DBA.language A"
    unfolding DBA.language_def DRA.language_def from_dba_def DBA.run_def DRA.run_def by (auto 0 3)

  definition from_dca :: "('label, 'state) dca \<Rightarrow> ('label, 'state) dra" where
    "from_dca A \<equiv> dra (dca.alphabet A) (dca.initial A) (dca.succ A) [(top, dca.rejecting A)]"

  lemma from_dca_language: "DRA.language (from_dca A) = DCA.language A"
    unfolding DCA.language_def DRA.language_def from_dca_def DCA.run_def DRA.run_def by (auto 0 3)

  definition dbcai :: "('label, 'state\<^sub>1) dba \<Rightarrow> ('label, 'state\<^sub>2) dca \<Rightarrow> ('label, 'state\<^sub>1 \<times> 'state\<^sub>2) dra" where
    "dbcai A B \<equiv> dra
      (dba.alphabet A \<inter> dca.alphabet B)
      (dba.initial A, dca.initial B)
      (\<lambda> a (p, q). (dba.succ A a p, dca.succ B a q))
      [(dba.accepting A \<circ> fst, dca.rejecting B \<circ> snd)]"

  lemma dbcai_fst[iff]: "infs (P \<circ> fst) (dra.trace (dbcai A B) w (p, q)) \<longleftrightarrow> infs P (dba.trace A w p)"
  proof -
    have "infs (P \<circ> fst) (dra.trace (dbcai A B) w (p, q)) \<longleftrightarrow>
      infs P (smap fst (dra.trace (dbcai A B) w (p, q)))" by simp
    also have "smap fst (dra.trace (dbcai A B) w (p, q)) = dba.trace A w p"
      unfolding dbcai_def by (coinduction arbitrary: w p q) (auto)
    finally show ?thesis by this
  qed
  lemma dbcai_snd[iff]: "infs (P \<circ> snd) (dra.trace (dbcai A B) w (p, q)) \<longleftrightarrow> infs P (dca.trace B w q)"
  proof -
    have "infs (P \<circ> snd) (dra.trace (dbcai A B) w (p, q)) \<longleftrightarrow>
      infs P (smap snd (dra.trace (dbcai A B) w (p, q)))" by simp
    also have "smap snd (dra.trace (dbcai A B) w (p, q)) = dca.trace B w q"
      unfolding dbcai_def by (coinduction arbitrary: w p q) (auto)
    finally show ?thesis by this
  qed

  lemma dbcai_language: "DRA.language (dbcai A B) = DBA.language A \<inter> DCA.language B"
  proof -
    have 0: "dra.alphabet (dbcai A B) = dba.alphabet A \<inter> dca.alphabet B" unfolding dbcai_def by simp
    have 1: "dra.initial (dbcai A B) = (dba.initial A, dca.initial B)" unfolding dbcai_def by simp
    have 2: "dra.accepting (dbcai A B) = [(dba.accepting A \<circ> fst, dca.rejecting B \<circ> snd)]"
      unfolding dbcai_def by simp
    have 3: "cogen rabin (dra.accepting (dbcai A B)) (DRA.trace (dbcai A B) w (p, q)) \<longleftrightarrow>
      infs (dba.accepting A) (DBA.trace A w p) \<and> fins (rejecting B) (DCA.trace B w q)" for w p q
      unfolding cogen_def rabin_def 2 by simp
    show ?thesis
      unfolding DRA.language_def DBA.language_def DCA.language_def
      unfolding DRA.run_alt_def DBA.run_alt_def DCA.run_alt_def
      unfolding 0 1 3 by auto
  qed

  abbreviation (input) "get k pp \<equiv> pp ! k"

  definition drau :: "('label, 'state) dra list \<Rightarrow> ('label, 'state list) dra" where
    "drau AA \<equiv> dra
      (UNION (set AA) dra.alphabet)
      (map dra.initial AA)
      (\<lambda> a pp. map2 (\<lambda> A p. dra.succ A a p) AA pp)
      (do { k \<leftarrow> [0 ..< length AA]; (f, g) \<leftarrow> dra.accepting (AA ! k); [(f \<circ> get k, g \<circ> get k)] })"

  lemma drau_trace:
    assumes "length pp = length AA" "k < length AA"
    shows "infs (P \<circ> get k) (dra.trace (drau AA) w pp) \<longleftrightarrow>
      infs P (dra.trace (AA ! k) w (pp ! k))"
  proof -
    have "infs (P \<circ> get k) (dra.trace (drau AA) w pp) \<longleftrightarrow>
      infs P (smap (get k) (dra.trace (drau AA) w pp))" by simp
    also have "smap (get k) (dra.trace (drau AA) w pp) = dra.trace (AA ! k) w (pp ! k)"
      using assms unfolding drau_def by (coinduction arbitrary: w pp) (force)
    finally show ?thesis by this
  qed

  lemma drau_language:
    assumes "INTER (set AA) dra.alphabet = UNION (set AA) dra.alphabet"
    shows "DRA.language (drau AA) = UNION (set AA) DRA.language"
  proof safe
    fix w
    assume 1: "w \<in> DRA.language (drau AA)"
    obtain 2:
      "dra.run (drau AA) w (dra.initial (drau AA))"
      "cogen rabin (dra.accepting (drau AA)) (dra.trace (drau AA) w (dra.initial (drau AA)))"
      using 1 by rule
    obtain I F where 3:
      "(I, F) \<in> set (dra.accepting (drau AA))"
      "infs I (dra.trace (drau AA) w (dra.initial (drau AA)))"
      "fins F (dra.trace (drau AA) w (dra.initial (drau AA)))"
      using 2(2) by blast
    obtain k P Q where 4:
      "k < length AA" "I = P \<circ> get k" "F = Q \<circ> get k" "(P, Q) \<in> set (dra.accepting (AA ! k))"
      using 3(1) unfolding drau_def List.bind_def by (auto simp: comp_def)
    show "w \<in> UNION (set AA) DRA.language"
    proof (intro UN_I DRA.language cogen rabin)
      show "AA ! k \<in> set AA" using 4(1) by auto
      show "DRA.run (AA ! k) w (dra.initial (AA ! k))"
        using assms 2(1) 4(1) unfolding DRA.run_alt_def drau_def by force
      show "(P, Q) \<in> set (dra.accepting (AA ! k))" using 4(4) by this
      show "(P, Q) = (P, Q)" by rule
      have "True \<longleftrightarrow> infs (P \<circ> get k) (dra.trace (drau AA) w (map dra.initial AA))"
        using 3(2) unfolding drau_def 4(2) by simp
      also have "\<dots> \<longleftrightarrow> infs P (dra.trace (AA ! k) w (map dra.initial AA ! k))"
        using 4(1) by (force intro!: drau_trace)
      also have "map dra.initial AA ! k = dra.initial (AA ! k)" using 4(1) by simp
      finally show "infs P (dra.trace (AA ! k) w (dra.initial (AA ! k)))" by simp
      have "False \<longleftrightarrow> infs (Q \<circ> get k) (dra.trace (drau AA) w (map dra.initial AA))"
        using 3(3) unfolding drau_def 4(3) by simp
      also have "\<dots> \<longleftrightarrow> infs Q (dra.trace (AA ! k) w (map dra.initial AA ! k))"
        using 4(1) by (force intro!: drau_trace)
      also have "map dra.initial AA ! k = dra.initial (AA ! k)" using 4(1) by simp
      finally show "fins Q (dra.trace (AA ! k) w (dra.initial (AA ! k)))" by simp
    qed
  next
    fix A w
    assume 1: "A \<in> set AA" "w \<in> DRA.language A"
    obtain 2:
      "dra.run A w (dra.initial A)"
      "cogen rabin (dra.accepting A) (dra.trace A w (dra.initial A))"
      using 1(2) by rule
    obtain I F where 3:
      "(I, F) \<in> set (dra.accepting A)"
      "infs I (dra.trace A w (dra.initial A))"
      "fins F (dra.trace A w (dra.initial A))"
      using 2(2) by blast
    obtain k where 4: "A = AA ! k" "k < length AA" using 1(1) unfolding in_set_conv_nth by auto
    show "w \<in> DRA.language (drau AA)"
    proof (intro DRA.language cogen rabin)
      show "dra.run (drau AA) w (dra.initial (drau AA))"
        using 1(1) 2(1) unfolding DRA.run_alt_def drau_def by auto
      show "(I \<circ> get k, F \<circ> get k) \<in> set (dra.accepting (drau AA))"
        unfolding drau_def List.bind_def using 3(1) 4 by (force simp: comp_def)
      show "(I \<circ> get k, F \<circ> get k) = (I \<circ> get k, F \<circ> get k)" by rule
      have "infs (I \<circ> get k) (dra.trace (drau AA) w (dra.initial (drau AA))) \<longleftrightarrow>
        infs (I \<circ> get k) (dra.trace (drau AA) w (map dra.initial AA))"
        unfolding drau_def by simp
      also have "\<dots> \<longleftrightarrow> infs I (dra.trace (AA ! k) w (map dra.initial AA ! k))"
        using 4(2) by (force intro!: drau_trace)
      also have "\<dots> \<longleftrightarrow> True" using 3(2) 4 by simp
      finally show "infs (I \<circ> get k) (dra.trace (drau AA) w (dra.initial (drau AA)))" by simp
      have "infs (F \<circ> get k) (dra.trace (drau AA) w (dra.initial (drau AA))) \<longleftrightarrow>
        infs (F \<circ> get k) (dra.trace (drau AA) w (map dra.initial AA))"
        unfolding drau_def by simp
      also have "\<dots> \<longleftrightarrow> infs F (dra.trace (AA ! k) w (map dra.initial AA ! k))"
        using 4(2) by (force intro!: drau_trace)
      also have "\<dots> \<longleftrightarrow> False" using 3(3) 4 by simp
      finally show "fins (F \<circ> get k) (dra.trace (drau AA) w (dra.initial (drau AA)))" by simp
    qed
  qed

end