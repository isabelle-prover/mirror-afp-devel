(*  Author: Lukas Bulwahn <lukas.bulwahn-at-gmail.com> *)

section {* Cardinality of Set Partitions *}

theory Card_Partitions
imports
  "~~/src/HOL/Library/Stirling"
  "~~/src/HOL/Library/Disjoint_Sets"
begin

subsection {* Insertion of Elements into Set Partitions *}

lemma partition_onD4: "partition_on A P \<Longrightarrow> p \<in> P \<Longrightarrow> q \<in> P \<Longrightarrow> x \<in> p \<Longrightarrow> x \<in> q \<Longrightarrow> p = q"
  by (auto simp: partition_on_def disjoint_def)

lemma partition_on_Diff:
  assumes P: "partition_on A P" shows "Q \<subseteq> P \<Longrightarrow> partition_on (A - \<Union>Q) (P - Q)"
  using P P[THEN partition_onD4] by (auto simp: partition_on_def disjoint_def)

lemma partition_on_UN:
  assumes A: "partition_on A B" and B: "\<And>b. b \<in> B \<Longrightarrow> partition_on b (P b)"
  shows "partition_on A (\<Union>b\<in>B. P b)"
proof (rule partition_onI)
  show "\<Union>(\<Union>b\<in>B. P b) = A"
    using B[THEN partition_onD1] A[THEN partition_onD1] by blast
  show "{} \<notin> (\<Union>i\<in>B. P i)"
    using B[THEN partition_onD3] by simp
next
  fix p q assume "p \<in> (\<Union>i\<in>B. P i)" "q \<in> (\<Union>i\<in>B. P i)" and "p \<noteq> q"
  then obtain i j where i: "p \<in> P i" "i \<in> B" and j: "q \<in> P j" "j \<in> B"
    by auto
  show "disjnt p q"
  proof cases
    assume "i = j" then show ?thesis
      using i j \<open>p \<noteq> q\<close> B[THEN partition_onD2, of i] by (auto simp: pairwise_def)
  next
    assume "i \<noteq> j"
    then have "disjnt i j"
      using i j A[THEN partition_onD2] by (auto simp: pairwise_def)
    moreover have "p \<subseteq> i" "q \<subseteq> j"
      using B[THEN partition_onD1, of i, symmetric] B[THEN partition_onD1, of j, symmetric] i j by auto
    ultimately show ?thesis
      by (auto simp: disjnt_def)
  qed
qed

lemma partition_on_insert:
  "partition_on A B \<Longrightarrow> disjnt A A' \<Longrightarrow> A' \<noteq> {} \<Longrightarrow> partition_on (A \<union> A') (insert A' B)"
  by (auto simp: partition_on_def disjoint_def disjnt_def)

lemma partition_on_insert_rewrite1:
  assumes a: "a \<notin> A"
  assumes A: "finite A"
  shows "{P. partition_on (insert a A) P \<and> card P = Suc k \<and> {a} \<in> P} = (\<lambda>P. insert {a} P) ` {P. partition_on A P \<and> card P = k}"
    (is "?S = ?T")
proof
  {
    fix P
    assume partition_on: "partition_on (insert a A) P"
      and card: "card P = Suc k"
      and mem: "{a} \<in> P"
    from card mem have "card (P - {{a}}) = k"
      by (subst card_Diff_singleton) (auto intro: card_ge_0_finite)
    moreover have "partition_on A (P - {{a}})"
      using mem partition_on[THEN partition_on_Diff, of "{{a}}"] a by auto
    ultimately have "card (P - {{a}}) = k" "partition_on A (P - {{a}})" .
  } note P_without_a = this
  show "?S \<subseteq> ?T"
  proof
    fix p
    assume "p \<in> {P. partition_on (insert a A) P \<and> card P = Suc k \<and> {a} \<in> P}"
    from P_without_a this show "p \<in> insert {a} ` {P. partition_on A P \<and> card P = k}"
      by (intro image_eqI[where x = "p - {{a}}"]) fast+
  qed
next
  {
    fix P
    assume p: "partition_on A P"
    assume c: "card P = k"
    from a p have not_mem: "{a} \<notin> P"
      unfolding partition_on_def by auto
    from p A have "finite P" by (auto intro: finite_elements)
    from a c not_mem this have "card (insert {a} P) = Suc k"
      by (simp add: card_insert)
    moreover from a p have "partition_on (insert a A) (insert {a} P)"
      using partition_on_insert[of A P "{a}"] by (auto simp: disjnt_def)
    ultimately have "card (insert {a} P) = Suc k" "partition_on (insert a A) (insert {a} P)" .
  }
  from this show "?T \<subseteq> ?S" by auto
qed

lemma partition_on_insert_rewrite2:
  assumes "a \<notin> A"
  shows "{P. partition_on (insert a A) P \<and> card P = Suc k \<and> {a} \<notin> P} =
    \<Union>((\<lambda>P. (\<lambda>p. insert (insert a p) (P - {p})) ` P) ` {P. partition_on A P \<and> card P = Suc k})"
  (is "?S = ?T")
proof
  {
    fix P
    assume p: "partition_on (insert a A) P"
    assume c: "card P = Suc k"
    assume a: "{a} \<notin> P"
    from p obtain p where p_def: "p : P" "a : p"
      unfolding partition_on_def by blast
    from p p_def have a_notmem: "\<forall>p'\<in> P - {p}. a \<notin> p'"
      unfolding partition_on_def disjoint_def by blast
    from p p_def have p': "p - {a} \<notin> P"
      unfolding partition_on_def disjoint_def
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
    have 1: "partition_on A (insert (p - {a}) (P - {p}))"
    proof -
      from p have "{} \<notin> P"
        unfolding partition_on_def by auto
      from this p_def a have 1: "{} \<notin> insert (p - {a}) (P - {p})"
        using subset_singletonD[of p a] by auto
      from p have "\<Union>P = insert a A"
        unfolding partition_on_def by auto
      from p_def this assms a_notmem have 2: "\<Union>insert (p - {a}) (P - {p}) = A"
        by auto
      from p p_def a_notmem have 3: "\<forall>pa\<in>insert (p - {a}) (P - {p}). \<forall>p'\<in>insert (p - {a}) (P - {p}). pa \<noteq> p' \<longrightarrow> pa \<inter> p' = {}"
        unfolding partition_on_def disjoint_def by (metis disjoint_iff_not_equal insert_Diff insert_iff)
      from 1 2 3 show ?thesis unfolding partition_on_def disjoint_def by simp
    qed
    from 1 2 3 have "\<exists>P'. partition_on A P' \<and> card P' = Suc k \<and> P \<in> (\<lambda>p. insert (insert a p) (P' - {p})) ` P'" by blast
  }
  from this show "?S \<subseteq> ?T" by auto
next
  {
    fix P p
    assume partition_on: "partition_on A P"
    assume c: "card P = Suc k"
    assume p: "p \<in> P"
    from partition_on p assms have p2: "p \<noteq> {}" "a \<notin> p"  and non_empty: "\<forall>p\<in>P. p \<noteq> {}"
      and a_notmem: "\<forall>p\<in>P. a \<notin> p" and a: "{a} \<notin> P"
      unfolding partition_on_def by auto
    from partition_on p have "\<Union>(P - {p}) \<subseteq> A" "p \<subseteq> A" "\<Union>P = A"
      unfolding partition_on_def by auto
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
          from this p partition_on have "\<forall>x\<in>p. x \<notin> q'"
            unfolding partition_on_def disjoint_def by auto
          from this q q' a_notmem show ?thesis by auto
        qed
      next
        assume q: "q \<in> P - {p}"
        from 2 show ?thesis
        proof
          assume q': "q' = insert a p"
          from q p partition_on have "\<forall>x\<in>p. x \<notin> q"
            unfolding partition_on_def disjoint_def by auto
          from this q q' a_notmem show ?thesis by auto
        next
          assume q': "q' \<in> P - {p}"
          from q q' noteq partition_on show ?thesis
            unfolding partition_on_def disjoint_def by auto
        qed
      qed
    }
    from this have no_overlap: "(\<forall>pa\<in>insert (insert a p) (P - {p}). \<forall>p'\<in>insert (insert a p) (P - {p}). pa \<noteq> p' \<longrightarrow> pa \<inter> p' = {})"
      by blast
    from non_empty Un this have 1: "partition_on (insert a A) (insert (insert a p) (P - {p}))"
      unfolding partition_on_def disjoint_def by auto
    from c p a_notmem have 2: "card (insert (insert a p) (P - {p})) = Suc k"
      by (subst card.insert) (auto simp add: card_ge_0_finite)
    from p2 p a have 3: "{a} \<notin> insert (insert a p) (P - {p})" by auto
    from 1 2 3 have "partition_on (insert a A) (insert (insert a p) (P - {p}))"
      "card (insert (insert a p) (P - {p})) = Suc k"
      "{a} \<notin> insert (insert a p) (P - {p})"
      by auto
  }
  from this show "?T \<subseteq> ?S" by blast
qed

subsection {* Cardinality of Set Partitions *}

theorem card_partition_on:
  assumes "finite A"
  shows "card {P. partition_on A P \<and> card P = k} = Stirling (card A) k"
using assms
proof (induct A arbitrary: k)
  case empty
    have eq: "{P. P = {} \<and> card P = 0} = {{}}" by auto
    show ?case by (cases k) (auto simp add: partition_on_empty eq)
next
  case (insert a A)

  from this show ?case
  proof (cases k)
    case 0
    from insert(1) have empty: "{P. partition_on (insert a A) P \<and> card P = 0} = {}"
      unfolding partition_on_def by (auto simp add: card_eq_0_iff finite_UnionD)
    from 0 insert show ?thesis by (auto simp add: empty)
  next
    case (Suc k)
    let ?P1 = "{P. partition_on (insert a A) P \<and> card P = Suc k \<and> {a} \<in> P}"
    let ?P2 = "{P. partition_on (insert a A) P \<and> card P = Suc k \<and> {a} \<notin> P}"
    have fin1: "\<And>A k. finite A \<Longrightarrow> finite {P. partition_on A P \<and> card P = k}"
      and fin2: "\<And>A k Q. finite A \<Longrightarrow> finite {P. partition_on A P \<and> card P = k \<and> Q P}"
      by (simp add: finitely_many_partition_on)+
    have finite_elements: "finite (\<Union>((\<lambda>P. (\<lambda>p. insert (insert a p) (P - {p})) ` P) ` {P. partition_on A P \<and> card P = Suc k}))"
      using insert(1) by (auto intro: fin1 finite_elements)
    from insert(2) have split: "{P. partition_on (insert a A) P \<and> card P = Suc k} = ?P1 \<union> ?P2"
      by fast

    have inj: "inj_on (insert {a}) {P. partition_on A P \<and> card P = k}"
    proof (rule inj_onI; clarify)
      fix p q
      assume part: "partition_on A p" "partition_on A q"
      assume i: "insert {a} p = insert {a} q"
      from insert(2) part have "{a} \<notin> p" "{a} \<notin> q"
        unfolding partition_on_def by auto
      from this i show "p = q" by (meson insert_ident)
    qed
    from insert(1, 2) inj have eq1: "card ?P1 = Stirling (card A) k"
      by (simp add: partition_on_insert_rewrite1 card_image insert(3))

    have inj2: "\<And>P. partition_on A P \<Longrightarrow> inj_on (\<lambda>p. insert (insert a p) (P - {p})) P"
    proof (rule inj_onI)
      fix P p q
      assume a: "partition_on A P"
      assume P: "p \<in> P" "q \<in> P"
        and eq: "insert (insert a p) (P - {p}) = insert (insert a q) (P - {q})"
      from insert(2) a have "insert a p \<notin> P" "insert a q \<notin> P"
        unfolding partition_on_def by auto
      from this eq P have "P - {p} = P - {q}" by (metis Diff_insert_absorb Set.set_insert insertE insertI2)
      from this P show "p = q" by blast
    qed

    have inj1: "inj_on (\<lambda>P. (\<lambda>p. insert (insert a p) (P - {p})) ` P) {P. partition_on A P \<and> card P = Suc k}"
    proof -
      {
        fix P Q
        assume partition_on: "partition_on A P" "partition_on A Q"
        assume card: "card P = Suc k" "card Q = Suc k"
        assume eq: "(\<lambda>p. insert (insert a p) (P - {p})) ` P = (\<lambda>p. insert (insert a p) (Q - {p})) ` Q"
        have "P = Q"
        proof (rule ccontr)
          from partition_on insert(2) have a_notmem: "\<forall>p\<in>P. a \<notin> p" "\<forall>q\<in>Q. a \<notin> q"
            unfolding partition_on_def by auto
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
      assume "c \<in> (\<lambda>P. (\<lambda>p. insert (insert a p) (P - {p})) ` P) ` {P. partition_on A P \<and> card P = Suc k}"
      from this inj2 have "card c = Suc k"
        by (auto simp add: card_image)
    } note card = this

    {
      fix P Q
      let ?f = "(\<lambda>P. (\<lambda>p. insert (insert a p) (P - {p})))"
      assume partition_on: "partition_on A P" "partition_on A Q"
      assume neq: "?f P ` P \<noteq> ?f Q ` Q"
      from insert(2) partition_on have a: "\<forall>p \<in> P. a \<notin> p" "\<forall>q \<in> Q. a \<notin> q"
        unfolding partition_on_def by auto
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

    from insert(2) have "card {P. partition_on (insert a A) P \<and> card P = Suc k \<and> {a} \<notin> P} =
      card (\<Union>((\<lambda>P. (\<lambda>p. insert (insert a p) (P - {p})) ` P) ` {P. partition_on A P \<and> card P = Suc k}))"
      by (simp add: partition_on_insert_rewrite2)
    also have "... = Suc k * card ((\<lambda>P. (\<lambda>p. insert (insert a p) (P - {p})) ` P) ` {P. partition_on A P \<and> card P = Suc k})"
      using card insert(1) no_intersect
      by (subst card_partition[symmetric]) (force intro: fin1)+
    also have "... = Suc k * Stirling (card A) (Suc k)"
      using inj1 insert(3) by (subst card_image) auto
    finally have eq2: "card {P. partition_on (insert a A) P \<and> card P = Suc k \<and> {a} \<notin> P} = Suc k * Stirling (card A) (Suc k)" .

    have "card {P. partition_on (insert a A) P \<and> card P = Suc k} = card ?P1 + card ?P2"
      by (subst split; subst card_Un_disjoint) (auto intro: fin2 insert(1))
    also have "... = Stirling (card (insert a A)) (Suc k)"
      using insert(1, 2) by (simp add: eq1 eq2)
    finally show ?thesis using Suc by auto
  qed
qed

theorem card_partition_on_at_most_size:
  assumes "finite A"
  shows "card {P. partition_on A P \<and> card P \<le> k} = (\<Sum>j\<le>k. Stirling (card A) j)"
proof -
  have "card {P. partition_on A P \<and> card P \<le> k} = card (\<Union>j\<le>k. {P. partition_on A P \<and> card P = j})"
    by (rule arg_cong[where f="card"]) auto
  also have "\<dots> = (\<Sum>j\<le>k. card {P. partition_on A P \<and> card P = j})"
    by (subst card_UN_disjoint) (auto simp add: \<open>finite A\<close> finitely_many_partition_on)
  also have "(\<Sum>j\<le>k. card {P. partition_on A P \<and> card P = j}) = (\<Sum>j\<le>k. Stirling (card A) j)"
    using `finite A` by (simp add: card_partition_on)
  finally show ?thesis .
qed

theorem partition_on_size1:
  assumes "finite A"
  shows "{P. partition_on A P \<and> (\<forall>X\<in>P. card X = 1)} = {(\<lambda>a. {a}) ` A}"
proof
  show "{P. partition_on A P \<and> (\<forall>X\<in>P. card X = 1)} \<subseteq> {(\<lambda>a. {a}) ` A}"
  proof
    fix P
    assume P: "P \<in> {P. partition_on A P \<and> (\<forall>X\<in>P. card X = 1)}"
    have "P = (\<lambda>a. {a}) ` A"
    proof
      show "P \<subseteq> (\<lambda>a. {a}) ` A"
      proof
        fix X
        assume "X \<in> P"
        from P this obtain x where "X = {x}"
           by (auto simp add: card_Suc_eq)
        from this \<open>X \<in> P\<close> have "x \<in> A"
          using P unfolding partition_on_def by blast
        from this \<open>X = {x}\<close> show "X \<in>(\<lambda>a. {a}) ` A" by auto
      qed
    next
      show "(\<lambda>a. {a}) ` A \<subseteq> P"
      proof
        fix X
        assume "X \<in> (\<lambda>a. {a}) ` A"
        from this obtain x where X: "X = {x}" "x \<in> A" by auto
        have "\<Union>P = A"
          using P unfolding partition_on_def by blast
        from this \<open>x \<in> A\<close> obtain X' where "x \<in> X'" and "X' \<in> P"
          using UnionE by blast
        from \<open>X' \<in> P\<close> have "card X' = 1"
          using P unfolding partition_on_def by auto
        from this \<open>x \<in> X'\<close> have "X' = {x}"
          using card_1_singletonE by blast
        from this X(1) \<open>X' \<in> P\<close> show "X \<in> P" by auto
      qed
    qed
    from this show "P \<in> {(\<lambda>a. {a}) ` A}" by auto
  qed
next
  show "{(\<lambda>a. {a}) ` A} \<subseteq> {P. partition_on A P \<and> (\<forall>X\<in>P. card X = 1)}"
  proof
    fix P
    assume "P \<in> {(\<lambda>a. {a}) ` A}"
    from this have P: "P = (\<lambda>a. {a}) ` A" by auto
    from this have "partition_on A P" by (auto intro: partition_onI)
    from P this show "P \<in> {P. partition_on A P \<and> (\<forall>X\<in>P. card X = 1)}" by auto
  qed
qed

theorem card_partition_on_size1:
  assumes "finite A"
  shows "card {P. partition_on A P \<and> (\<forall>X\<in>P. card X = 1)} = 1"
using assms partition_on_size1 by fastforce

lemma card_partition_on_size1_eq_1:
  assumes "finite A"
  assumes "card A \<le> k"
  shows "card {P. partition_on A P \<and> card P \<le> k \<and> (\<forall>X\<in>P. card X = 1)} = 1"
proof -
  {
    fix P
    assume "partition_on A P" "\<forall>X\<in>P. card X = 1"
    from this have "P \<in> {P. partition_on A P \<and> (\<forall>X\<in>P. card X = 1)}" by simp
    from this have "P \<in> {(\<lambda>a. {a}) ` A}"
      using partition_on_size1 \<open>finite A\<close> by auto
    from this have "P = (\<lambda>a. {a}) ` A" by auto
    moreover from this have "card P = card A"
      by (auto intro: card_image)
  }
  from this have "{P. partition_on A P \<and> card P \<le> k \<and> (\<forall>X\<in>P. card X = 1)} = {P. partition_on A P \<and> (\<forall>X\<in>P. card X = 1)}"
    using \<open>card A \<le> k\<close> by auto
  from this show ?thesis
    using \<open>finite A\<close> by (simp only: card_partition_on_size1)
qed

lemma card_partition_on_size1_eq_0:
  assumes "finite A"
  assumes "k < card A"
  shows "card {P. partition_on A P \<and> card P \<le> k \<and> (\<forall>X\<in>P. card X = 1)} = 0"
proof -
  {
    fix P
    assume "partition_on A P" "\<forall>X\<in>P. card X = 1"
    from this have "P \<in> {P. partition_on A P \<and> (\<forall>X\<in>P. card X = 1)}" by simp
    from this have "P \<in> {(\<lambda>a. {a}) ` A}"
      using partition_on_size1 \<open>finite A\<close> by auto
    from this have "P = (\<lambda>a. {a}) ` A" by auto
    from this have "card P = card A"
      by (auto intro: card_image)
  }
  from this assms(2) have "{P. partition_on A P \<and> card P \<le> k \<and> (\<forall>X\<in>P. card X = 1)} = {}"
    using Collect_empty_eq leD by fastforce
  from this show ?thesis by (simp only: card_empty)
qed

end
