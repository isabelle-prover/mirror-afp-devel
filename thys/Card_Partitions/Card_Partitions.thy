(*  Author: Lukas Bulwahn <lukas.bulwahn-at-gmail.com> *)

section {* Cardinality of Set Partitions *}

theory Card_Partitions
imports
  "../Discrete_Summation/Stirling"
begin

subsection {* Definition of Set Partitions *}

definition
  "partitions P A = ((\<forall>p \<in> P. p \<noteq> {}) \<and> \<Union>P = A \<and> (\<forall>p \<in> P. \<forall>p' \<in> P. p \<noteq> p' \<longrightarrow> p \<inter> p' = {}))"

lemma partitions_empty:
  "(partitions P {}) \<longleftrightarrow> (P = {})"
unfolding partitions_def by auto

subsection {* Finiteness of Set Partitions *}

lemma finitely_many_partitions:
  assumes "finite A"
  shows "finite {P. partitions P A}"
proof -
  have "{P. partitions P A} \<subseteq> Pow (Pow A)"
    unfolding partitions_def by auto
  moreover have "finite (Pow (Pow A))"
    using assms by simp
  ultimately show ?thesis by (meson finite_subset)
qed

lemma finite_elements:
  assumes "finite A"
  assumes "partitions P A"
  shows "finite P"
using assms unfolding partitions_def
by (simp add: finite_UnionD)

subsection {* Insertion of Elements into Set Partitions *}

lemma partitions_insert_rewrite1:
  assumes a: "a \<notin> A"
  assumes A: "finite A"
  shows "{P. partitions P (insert a A) \<and> card P = Suc k \<and> {a} \<in> P} = (\<lambda>P. insert {a} P) ` {P. partitions P A \<and> card P = k}"
    (is "?S = ?T")
proof
  {
    fix P
    assume partitions: "partitions P (insert a A)"
     and card: "card P = Suc k"
     and mem: "{a} \<in> P"
    from partitions have prop_partitions: "\<forall>p\<in>P. p \<noteq> {}" "\<Union>P = insert a A"
      "\<forall>p\<in>P. \<forall>p'\<in>P. p \<noteq> p' \<longrightarrow> p \<inter> p' = {}"
      unfolding partitions_def by auto
    from this(2, 3) a mem have A_eq: "A = \<Union>(P - {{a}})"
      by auto (metis Int_iff UnionI empty_iff insert_iff)
    from card mem have "card (P - {{a}}) = k"
      by (subst card_Diff_singleton) (auto intro: card_ge_0_finite)
    moreover from prop_partitions A_eq have "partitions (P - {{a}}) A"
      unfolding partitions_def by simp
    ultimately have "card (P - {{a}}) = k" "partitions (P - {{a}}) A" .
  } note P_without_a = this
  show "?S \<subseteq> ?T"
  proof
    fix p
    assume "p \<in> {P. partitions P (insert a A) \<and> card P = Suc k \<and> {a} \<in> P}"
    from P_without_a this show "p \<in> insert {a} ` {P. partitions P A \<and> card P = k}"
      by (intro image_eqI[where x = "p - {{a}}"]) fast+
  qed
next
  {
    fix P
    assume p: "partitions P A"
    assume c: "card P = k"
    from a p have not_mem: "{a} \<notin> P"
      unfolding partitions_def by auto
    from p A have "finite P" by (auto intro: finite_elements)
    from a c not_mem this have "card (insert {a} P) = Suc k"
      by (simp add: card_insert)
    moreover from a p have "partitions (insert {a} P) (insert a A)"
      unfolding partitions_def by auto
    ultimately have "card (insert {a} P) = Suc k" "partitions (insert {a} P) (insert a A)" .
  }
  from this show "?T \<subseteq> ?S" by auto
qed

lemma partitions_insert_rewrite2:
  assumes "a \<notin> A"
  shows "{P. partitions P (insert a A) \<and> card P = Suc k \<and> {a} \<notin> P} =
    \<Union>((\<lambda>P. (\<lambda>p. insert (insert a p) (P - {p})) ` P) ` {P. partitions P A \<and> card P = Suc k})"
  (is "?S = ?T")
proof
  {
    fix P
    assume p: "partitions P (insert a A)"
    assume c: "card P = Suc k"
    assume a: "{a} \<notin> P"
    from p obtain p where p_def: "p : P" "a : p"
      unfolding partitions_def by blast
    from p p_def have a_notmem: "\<forall>p'\<in> P - {p}. a \<notin> p'"
      unfolding partitions_def by blast
    from p p_def have p': "p - {a} \<notin> P"
      unfolding partitions_def
      by (metis Diff_insert_absorb Diff_subset inf.orderE mk_disjoint_insert)
    let ?P' = "insert (p - {a}) (P - {p})"
    from c have f: "finite P" by (simp add: card_ge_0_finite)
    from this have "card ?P' = Suc (card (P - {p} - {p - {a}}))"
      by (simp add: card_insert)
    also from f have "... = Suc (card (P - {p}))"
      by (subst card_Diff_singleton_if) (simp add: p')+
    also from c f have "... = Suc k"
      by (subst card_Diff_singleton) (simp add: p_def)+
    finally have 2: "card ?P' = Suc k" .
    from p' p_def have "P = insert (insert a (p - {a})) (?P' - {p - {a}})"
      by (simp add: insert_absorb)
    from this have 3: "P \<in> (\<lambda>p. insert (insert a p) (?P' - {p})) ` (insert (p - {a}) (P - {p}))"
      by simp
    have 1: "partitions (insert (p - {a}) (P - {p})) A"
    proof -
      from p have "(\<forall>p\<in>P. p \<noteq> {})"
        unfolding partitions_def by auto
      from this p_def a have 1: "\<forall>p\<in>insert (p - {a}) (P - {p}). p \<noteq> {}"
        using subset_singletonD by (simp; fastforce)
      from p have "\<Union>P = insert a A"
        unfolding partitions_def by auto
      from p_def this assms a_notmem have 2: "\<Union>insert (p - {a}) (P - {p}) = A"
        by auto
      from p p_def a_notmem have 3: "\<forall>pa\<in>insert (p - {a}) (P - {p}). \<forall>p'\<in>insert (p - {a}) (P - {p}). pa \<noteq> p' \<longrightarrow> pa \<inter> p' = {}"
        unfolding partitions_def by (metis disjoint_iff_not_equal insert_Diff insert_iff)
      from 1 2 3 show ?thesis unfolding partitions_def by simp
    qed
    from 1 2 3 have "\<exists>P'. partitions P' A \<and> card P' = Suc k \<and> P \<in> (\<lambda>p. insert (insert a p) (P' - {p})) ` P'" by blast
  }
  from this show "?S \<subseteq> ?T" by auto
next
  {
    fix P p
    assume partitions: "partitions P A"
    assume c: "card P = Suc k"
    assume p: "p \<in> P"
    from partitions p assms have p2: "p \<noteq> {}" "a \<notin> p"  and non_empty: "\<forall>p\<in>P. p \<noteq> {}"
      and a_notmem: "\<forall>p\<in>P. a \<notin> p" and a: "{a} \<notin> P"
      unfolding partitions_def by auto
    from partitions p have "\<Union>(P - {p}) \<subseteq> A" "p \<subseteq> A" "\<Union>P = A"
      unfolding partitions_def by auto
    from this have Un:"\<Union>insert (insert a p) (P - {p}) = insert a A" by auto
    {
      fix q q'
      assume 1: "q \<in> insert (insert a p) (P - {p})"
      assume 2: "q' \<in> insert (insert a p) (P - {p})"
      assume noteq: "q \<noteq> q'"
      from 1 have "q \<inter> q' = {}"
      proof
        assume q: "q = insert a p"
        from 2 show ?thesis
        proof
          assume "q' = insert a p"
          from noteq this q show ?thesis by simp
        next
          assume q': "q' \<in> P - {p}"
          from this p partitions have "\<forall>x\<in>p. x \<notin> q'"
            unfolding partitions_def by auto
          from this q q' a_notmem show ?thesis by auto
        qed
      next
        assume q: "q \<in> P - {p}"
        from 2 show ?thesis
        proof
          assume q': "q' = insert a p"
          from q p partitions have "\<forall>x\<in>p. x \<notin> q"
            unfolding partitions_def by auto
          from this q q' a_notmem show ?thesis by auto
        next
          assume q': "q' \<in> P - {p}"
          from q q' noteq partitions show ?thesis
            unfolding partitions_def by auto
        qed
      qed
    }
    from this have no_overlap: "(\<forall>pa\<in>insert (insert a p) (P - {p}). \<forall>p'\<in>insert (insert a p) (P - {p}). pa \<noteq> p' \<longrightarrow> pa \<inter> p' = {})"
      by blast
    from non_empty Un this have 1: "partitions (insert (insert a p) (P - {p})) (insert a A)"
      unfolding partitions_def by auto
    from c p a_notmem have 2: "card (insert (insert a p) (P - {p})) = Suc k"
      by (subst card.insert) (auto simp add: card_ge_0_finite)
    from p2 p a have 3: "{a} \<notin> insert (insert a p) (P - {p})" by auto
    from 1 2 3 have "partitions (insert (insert a p) (P - {p})) (insert a A)"
      "card (insert (insert a p) (P - {p})) = Suc k"
      "{a} \<notin> insert (insert a p) (P - {p})"
      by auto
  }
  from this show "?T \<subseteq> ?S" by blast
qed

subsection {* Cardinality of Set Partitions *}

theorem card_partitions:
  assumes "finite A"
  shows "card {P. partitions P A \<and> card P = k} = Stirling (card A) k"
using assms
proof (induct A arbitrary: k)
  case empty
    have eq: "{P. P = {} \<and> card P = 0} = {{}}" by auto
    show ?case by (cases k) (auto simp add: partitions_empty eq)
next
  case (insert a A)

  from this show ?case
  proof (cases k)
    case 0
    from insert(1) have empty: "{P. partitions P (insert a A) \<and> card P = 0} = {}"
      unfolding partitions_def by (auto simp add: card_eq_0_iff finite_UnionD)
    from 0 insert show ?thesis by (auto simp add: empty)
  next
    case (Suc k)
    let ?P1 = "{P. partitions P (insert a A) \<and> card P = Suc k \<and> {a} \<in> P}"
    let ?P2 = "{P. partitions P (insert a A) \<and> card P = Suc k \<and> {a} \<notin> P}"
    have fin1: "\<And>A k. finite A \<Longrightarrow> finite {P. partitions P A \<and> card P = k}"
      and fin2: "\<And>A k Q. finite A \<Longrightarrow> finite {P. partitions P A \<and> card P = k \<and> Q P}"
      by (simp add: finitely_many_partitions)+
    have finite_elements: "finite (\<Union>((\<lambda>P. (\<lambda>p. insert (insert a p) (P - {p})) ` P) ` {P. partitions P A \<and> card P = Suc k}))"
      using insert(1) by (auto intro: fin1 finite_elements)
    from insert(2) have split: "{P. partitions P (insert a A) \<and> card P = Suc k} = ?P1 \<union> ?P2"
      by fast

    have inj: "inj_on (insert {a}) {P. partitions P A \<and> card P = k}"
    proof (rule inj_onI; clarify)
      fix p q
      assume part: "partitions p A" "partitions q A"
      assume i: "insert {a} p = insert {a} q"
      from insert(2) part have "{a} \<notin> p" "{a} \<notin> q"
        unfolding partitions_def by auto
      from this i show "p = q" by (meson insert_ident)
    qed
    from insert(1, 2) inj have eq1: "card ?P1 = Stirling (card A) k"
      by (simp add: partitions_insert_rewrite1 card_image insert(3))

    have inj2: "\<And>P. partitions P A \<Longrightarrow> inj_on (\<lambda>p. insert (insert a p) (P - {p})) P"
    proof (rule inj_onI)
      fix P p q
      assume a: "partitions P A"
      assume P: "p : P" "q : P"
        and eq: "insert (insert a p) (P - {p}) = insert (insert a q) (P - {q})"
      from insert(2) a have "insert a p \<notin> P" "insert a q \<notin> P"
        unfolding partitions_def by auto
      from this eq P have "P - {p} = P - {q}" by (metis Diff_insert_absorb Set.set_insert insertE insertI2)
      from this P show "p = q" by blast
    qed

    have inj1: "inj_on (\<lambda>P. (\<lambda>p. insert (insert a p) (P - {p})) ` P) {P. partitions P A \<and> card P = Suc k}"
    proof -
      {
        fix P Q
        assume partitions: "partitions P A" "partitions Q A"
        assume card: "card P = Suc k" "card Q = Suc k"
        assume eq: "(\<lambda>p. insert (insert a p) (P - {p})) ` P = (\<lambda>p. insert (insert a p) (Q - {p})) ` Q"
        have "P = Q"
        proof (rule ccontr)
          from partitions insert(2) have a_notmem: "\<forall>p\<in>P. a \<notin> p" "\<forall>q\<in>Q. a \<notin> q"
            unfolding partitions_def by auto
          assume "P \<noteq> Q"
          from this have "(\<exists>x. x \<in> P \<and> x \<notin> Q) \<or> (\<exists>x. x \<notin> P \<and> x \<in> Q)"
            by auto
          from this have "(\<lambda>p. insert (insert a p) (P - {p})) ` P \<noteq> (\<lambda>p. insert (insert a p) (Q - {p})) ` Q"
          proof
            assume "(\<exists>x. x \<in> P \<and> x \<notin> Q)"
            from this obtain p where p: "p : P" "p \<notin> Q" by auto
            from p this a_notmem have "insert (insert a p) (P - {p}) \<notin> (\<lambda>p. insert (insert a p) (Q - {p})) ` Q"
              by clarify (metis Diff_insert_absorb insertCI insertE insertI1 insert_Diff)
            from p this show "(\<lambda>p. insert (insert a p) (P - {p})) ` P \<noteq> (\<lambda>p. insert (insert a p) (Q - {p})) ` Q"
              by blast
          next
            assume "(\<exists>x. x \<notin> P \<and> x \<in> Q)"
            from this obtain q where q: "q : Q" "q \<notin> P" by auto
            from this a_notmem have "insert (insert a q) (Q - {q}) \<notin> (\<lambda>p. insert (insert a p) (P - {p})) ` P"
              by clarify (metis Diff_insert_absorb insertCI insertE insertI1 insert_Diff)
            from q this show "(\<lambda>p. insert (insert a p) (P - {p})) ` P \<noteq> (\<lambda>p. insert (insert a p) (Q - {p})) ` Q"
              by blast
          qed
          from this eq show "False" by blast
        qed
      }
      from this show ?thesis
      unfolding inj_on_def by auto
    qed

    {
      fix c
      assume "c \<in> (\<lambda>P. (\<lambda>p. insert (insert a p) (P - {p})) ` P) ` {P. partitions P A \<and> card P = Suc k}"
      from this inj2 have "card c = Suc k"
        by (auto simp add: card_image)
    } note card = this

    {
      fix P Q
      let ?f = "(\<lambda>P. (\<lambda>p. insert (insert a p) (P - {p})))"
      assume partitions: "partitions P A" "partitions Q A"
      assume neq: "?f P ` P \<noteq> ?f Q ` Q"
      from insert(2) partitions have a: "\<forall>p \<in> P. a \<notin> p" "\<forall>q \<in> Q. a \<notin> q"
        unfolding partitions_def by auto
      have "?f P ` P \<inter> ?f Q ` Q = {}"
      proof (rule ccontr)
        assume "?f P ` P \<inter> ?f Q ` Q \<noteq> {}"
        from this obtain q where q: "q \<in> ?f P ` P" "q \<in> ?f Q ` Q" by auto
        from q(2) obtain p where p: "insert a p \<in> q" "p \<in> Q" by auto
        from q(1) obtain p' where p': "insert a p' \<in> q" "p' \<in> P" by auto
        from q p p' a have eq: "p = p'" by clarify (metis insert_Diff insert_ident insert_iff)
        from q p a have "q - {insert a p} = P - {p}" "q - {insert a p} = Q - {p}"
          by (clarify; metis (no_types, hide_lams) Diff_iff Diff_insert_absorb insert_iff)+
        from this p p' eq have "P = Q" by auto
        from this neq show "False" by blast
      qed
    } note no_intersect = this

    from insert(2) have "card {P. partitions P (insert a A) \<and> card P = Suc k \<and> {a} \<notin> P} =
      card (\<Union>((\<lambda>P. (\<lambda>p. insert (insert a p) (P - {p})) ` P) ` {P. partitions P A \<and> card P = Suc k}))"
      by (simp add: partitions_insert_rewrite2)
    also have "... = Suc k * card ((\<lambda>P. (\<lambda>p. insert (insert a p) (P - {p})) ` P) ` {P. partitions P A \<and> card P = Suc k})"
      using card insert(1) no_intersect
      by (subst card_partition[symmetric]) (force intro: fin1)+
    also have "... = Suc k * Stirling (card A) (Suc k)"
      using inj1 insert(3) by (subst card_image) auto
    finally have eq2: "card {P. partitions P (insert a A) \<and> card P = Suc k \<and> {a} \<notin> P} = Suc k * Stirling (card A) (Suc k)" .

    have "card {P. partitions P (insert a A) \<and> card P = Suc k} = card ?P1 + card ?P2"
      by (subst split; subst card_Un_disjoint) (auto intro: fin2 insert(1))
    also have "... = Stirling (card (insert a A)) (Suc k)"
      using insert(1, 2) by (simp add: eq1 eq2)
    finally show ?thesis using Suc by auto
  qed
qed

end