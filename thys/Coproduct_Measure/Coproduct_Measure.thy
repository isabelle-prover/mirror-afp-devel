(*  Title:   Coproduct_Measure.thy
    Author:  Michikazu Hirata, Tokyo Institute of Technology
*)

theory Coproduct_Measure
  imports "Lemmas_Coproduct_Measure"
          "HOL-Analysis.Analysis"
begin

section \<open> Binary Coproduct Measures \<close>
definition copair_measure :: "['a measure, 'b measure] \<Rightarrow> ('a + 'b) measure" (infixr \<open>\<Oplus>\<^sub>M\<close> 65) where
"M \<Oplus>\<^sub>M N = measure_of (space M <+> space N)
                      ({Inl ` A |A. A \<in> sets M} \<union> {Inr ` A|A. A \<in> sets N})
                      (\<lambda>A. emeasure M (Inl -` A) + emeasure N (Inr -` A))"

subsection \<open>The Measurable Space and Measurability\<close>
lemma
  shows space_copair_measure: "space (copair_measure M N) = space M <+> space N"
    and sets_copair_measure_sigma:
       "sets (copair_measure M N)
         = sigma_sets (space M <+> space N) ({Inl ` A |A. A \<in> sets M} \<union> {Inr ` A|A. A \<in> sets N})"
    and Inl_measurable[measurable]: "Inl \<in> M \<rightarrow>\<^sub>M M \<Oplus>\<^sub>M N"
    and Inr_measurable[measurable]: "Inr \<in> N \<rightarrow>\<^sub>M M \<Oplus>\<^sub>M N"
proof -
  have 1:"({Inl ` A |A. A \<in> sets M} \<union> {Inr ` A|A. A \<in> sets N}) \<subseteq> Pow (space M <+> space N)"
    using sets.sets_into_space[of _ M] sets.sets_into_space[of _ N] by fastforce
  show "space (copair_measure M N) = space M <+> space N"
 and 2:"sets (copair_measure M N)
        = sigma_sets (space M <+> space N) ({Inl ` A |A. A \<in> sets M} \<union> {Inr ` A|A. A \<in> sets N})"
    by(simp_all add: copair_measure_def sets_measure_of[OF 1] space_measure_of[OF 1])
  show "Inl \<in> M \<rightarrow>\<^sub>M M \<Oplus>\<^sub>M N" "Inr \<in> N \<rightarrow>\<^sub>M M \<Oplus>\<^sub>M N"
    by(auto intro!: measurable_sigma_sets[OF 2 1] simp: vimage_def image_def)
qed

lemma sets_copair_measure_cong:
  "sets M1 = sets M2 \<Longrightarrow> sets N1 = sets N2 \<Longrightarrow> sets (M1 \<Oplus>\<^sub>M N1) = sets (M2 \<Oplus>\<^sub>M N2)"
  by(simp cong: sets_eq_imp_space_eq add: sets_copair_measure_sigma)

lemma measurable_image_Inl[measurable]: "A \<in> sets M \<Longrightarrow> Inl ` A \<in> sets (M \<Oplus>\<^sub>M N)"
  using sets_copair_measure_sigma by fastforce

lemma measurable_image_Inr[measurable]: "A \<in> sets N \<Longrightarrow> Inr ` A \<in> sets (M \<Oplus>\<^sub>M N)"
  using sets_copair_measure_sigma by fastforce

lemma measurable_vimage_Inl:
  assumes [measurable]:"A \<in> sets (M \<Oplus>\<^sub>M N)"
  shows "Inl -` A \<in> sets M"
proof -
  have "Inl -` A = Inl -` A \<inter> space M"
    using sets.sets_into_space[OF assms]
    by(auto simp add: space_copair_measure)
  also have "... \<in> sets M"
    by simp
  finally show ?thesis .
qed

lemma measurable_vimage_Inr:
  assumes [measurable]:"A \<in> sets (M \<Oplus>\<^sub>M N)"
  shows "Inr -` A \<in> sets N"
proof -
  have "Inr -` A = Inr -` A \<inter> space N"
    using sets.sets_into_space[OF assms]
    by(auto simp add: space_copair_measure)
  also have "... \<in> sets N"
    by simp
  finally show ?thesis .
qed

lemma in_sets_copair_measure_iff:
 "A \<in> sets (copair_measure M N) \<longleftrightarrow> Inl -` A \<in> sets M \<and> Inr -` A \<in> sets N"
proof safe
  assume [measurable]: "Inl -` A \<in> sets M" "Inr -` A \<in> sets N"
  have "A = ((Inl ` Inl -` A) \<union> (Inr ` Inr -` A))"
    by(simp add: vimage_def image_def) (safe, metis obj_sumE)
  also have "... \<in> sets (copair_measure M N)"
    by measurable
  finally show "A  \<in> sets (copair_measure M N)" .
qed(use measurable_vimage_Inl measurable_vimage_Inr in auto)

lemma measurable_copair_Inl_Inr:
  assumes [measurable]:"(\<lambda>x. f (Inl x)) \<in> M \<rightarrow>\<^sub>M L" "(\<lambda>x. f (Inr x)) \<in> N \<rightarrow>\<^sub>M L"
  shows "f \<in> M \<Oplus>\<^sub>M N \<rightarrow>\<^sub>M L"
proof(rule measurableI)
  fix A
  assume [measurable]:"A \<in> sets L"
  have "f -` A = Inl ` ((\<lambda>x. f (Inl x)) -` A) \<union> Inr ` ((\<lambda>x. f (Inr x)) -` A)"
    by(simp add: image_def vimage_def) (safe, metis obj_sumE)
  hence "f -` A \<inter> space (M \<Oplus>\<^sub>M N)
         = Inl ` ((\<lambda>x. f (Inl x)) -` A \<inter> space M) \<union> Inr ` ((\<lambda>x. f (Inr x)) -` A \<inter> space N)"
    by(auto simp: space_copair_measure)
  also have "... \<in> sets (M \<Oplus>\<^sub>M N)"
    by measurable
  finally show "f -` A \<inter> space (M \<Oplus>\<^sub>M N) \<in> sets (M \<Oplus>\<^sub>M N)" .
next
  show "\<And>x. x \<in> space (M \<Oplus>\<^sub>M N) \<Longrightarrow> f x \<in> space L"
    using measurable_space[OF assms(1)] measurable_space[OF assms(2)]
    by(auto simp add: space_copair_measure)
qed

corollary measurable_copair_measure_iff:
 "f \<in> M \<Oplus>\<^sub>M N \<rightarrow>\<^sub>M L \<longleftrightarrow> (\<lambda>x. f (Inl x)) \<in> M \<rightarrow>\<^sub>M L \<and> (\<lambda>x. f (Inr x)) \<in> N \<rightarrow>\<^sub>M L"
  by(auto simp add: measurable_copair_Inl_Inr)

lemma measurable_copair_dest1:
  assumes [measurable]:"f \<in> L \<rightarrow>\<^sub>M M \<Oplus>\<^sub>M N" and "f -` (Inl ` space M) \<inter> space L = space L"
  obtains f' where "f' \<in> L \<rightarrow>\<^sub>M M" "\<And>x. x \<in> space L \<Longrightarrow> f x = Inl (f' x)"
proof -
  define f' where "f' \<equiv> (\<lambda>x. SOME y. f x = Inl y)"
  have f':"\<And>x. x \<in> space L \<Longrightarrow> f x = Inl (f' x)"
    unfolding f'_def by(rule someI_ex) (use assms(2) in blast)
  moreover have "f' \<in> L \<rightarrow>\<^sub>M M"
  proof(rule measurableI)
    show "\<And>x. x \<in> space L \<Longrightarrow> f' x \<in> space M"
      using f' measurable_space[OF assms(1)]
      by(auto simp: space_copair_measure)
  next
    fix A
    assume A[measurable]:"A \<in> sets M"
    have [simp]:"f' -` A \<inter> space L = f -` (Inl ` A) \<inter> space L"
      using f' sets.sets_into_space[OF A] by auto
    show "f' -` A \<inter> space L \<in> sets L"
      by auto
  qed
  ultimately show ?thesis
    using that by blast
qed

lemma measurable_copair_dest2:
  assumes [measurable]:"f \<in> L \<rightarrow>\<^sub>M M \<Oplus>\<^sub>M N" and "f -` (Inr ` space N) \<inter> space L = space L"
  obtains f' where "f' \<in> L \<rightarrow>\<^sub>M N" "\<And>x. x \<in> space L \<Longrightarrow> f x = Inr (f' x)"
proof -
  define f' where "f' \<equiv> (\<lambda>x. SOME y. f x = Inr y)"
  have f':"\<And>x. x \<in> space L \<Longrightarrow> f x = Inr (f' x)"
    unfolding f'_def by(rule someI_ex) (use assms(2) in blast)
  moreover have "f' \<in> L \<rightarrow>\<^sub>M N"
  proof(rule measurableI)
    show "\<And>x. x \<in> space L \<Longrightarrow> f' x \<in> space N"
      using f' measurable_space[OF assms(1)]
      by(auto simp: space_copair_measure)
  next
    fix A
    assume A[measurable]:"A \<in> sets N"
    have [simp]:"f' -` A \<inter> space L = f -` (Inr ` A) \<inter> space L"
      using f' sets.sets_into_space[OF A] by auto
    show "f' -` A \<inter> space L \<in> sets L"
      by auto
  qed
  ultimately show ?thesis
    using that by blast
qed

lemma measurable_copair_dest3:
  assumes [measurable]:"f \<in> L \<rightarrow>\<^sub>M M \<Oplus>\<^sub>M N"
    and "f -` (Inl ` space M) \<inter> space L \<subset> space L" "f -` (Inr ` space N) \<inter> space L \<subset> space L"
  obtains f' f'' where "f' \<in> L \<rightarrow>\<^sub>M M"  "f'' \<in> L \<rightarrow>\<^sub>M N"
    "\<And>x. x \<in> space L \<Longrightarrow> x \<in> f -` Inl ` space M \<Longrightarrow> f x = Inl (f' x)"
    "\<And>x. x \<in> space L \<Longrightarrow> x \<notin> f -` Inl ` space M \<Longrightarrow> f x = Inr (f'' x)"
proof -
  have ne:"space M \<noteq> {}" "space N \<noteq> {}"
    using assms(2,3) measurable_space[OF assms(1)] by(fastforce simp: space_copair_measure)+
  define m where "m \<equiv> SOME y. y \<in> space M"
  define n where "n \<equiv> SOME y. y \<in> space N"
  have m[measurable, simp]:"m \<in> space M" and n[measurable, simp]:"n \<in> space N"
    using ne by(auto simp: n_def m_def some_in_eq)
  define f' where "f' \<equiv> (\<lambda>x. if x \<in> f -` Inl ` space M then SOME y. f x = Inl y else m)"
  have "\<And>x. x \<in> space L \<Longrightarrow> x \<in> f -` Inl ` space M \<Longrightarrow> f x = Inl (SOME y. f x = Inl y)"
    unfolding f'_def by(rule someI_ex) (use assms(2) in blast)
  hence f':"\<And>x. x \<in> space L \<Longrightarrow>  x \<in> f -` Inl ` space M \<Longrightarrow> f x = Inl (f' x)"
    by(simp add: f'_def)
  hence f'_space: "x \<in> space L \<Longrightarrow> f' x \<in> space M" for x
    using measurable_space[OF assms(1)]
    by(cases "x \<in> f -` Inl ` space M") (auto simp: space_copair_measure f'_def)
  define f'' where "f'' \<equiv> (\<lambda>x. if x \<notin> f -` Inl ` space M then SOME y. f x = Inr y else n)"
  have *:"\<And>x. x \<in> space L \<Longrightarrow> x \<notin> f -` Inl ` space M \<Longrightarrow> x \<in> f -` Inr ` space N"
    using measurable_space[OF assms(1)] by(fastforce simp: space_copair_measure)
  have "\<And>x. x \<in> space L \<Longrightarrow> x \<notin> f -` Inl ` space M \<Longrightarrow> f x = Inr ( SOME y. f x = Inr y)"
    unfolding f''_def by(rule someI_ex) (use * in blast)
  hence f'':"\<And>x. x \<in> space L \<Longrightarrow> x \<notin> f -` Inl ` space M \<Longrightarrow> f x = Inr (f'' x)"
    by(simp add: f''_def)
  hence f''_space:"x \<in> space L \<Longrightarrow>  f'' x \<in> space N" for x
    using measurable_space[OF assms(1),of x]
    by(cases "x \<notin> f -` Inl ` space M") (auto simp add: space_copair_measure f''_def)
  have "f' \<in> L \<rightarrow>\<^sub>M M"
  proof -
    have "f' = (\<lambda>x. if x \<in> f -` Inl ` space M then f' x else m)"
      by(auto simp add: f'_def)
    also have "... \<in> L \<rightarrow>\<^sub>M M"
    proof(intro measurable_restrict_space_iff[THEN iffD1] measurableI)
      fix A
      assume A[measurable]:"A \<in> sets M"
      have [measurable]:"f \<in> restrict_space L (f -` Inl ` space M) \<rightarrow>\<^sub>M M \<Oplus>\<^sub>M N"
        by(auto intro!: measurable_restrict_space1)
      have [simp]:"f' -` A \<inter> space (restrict_space L (f -` Inl ` space M))
                   = f -` (Inl ` A) \<inter> space (restrict_space L (f -` Inl ` space M))"
        using f' sets.sets_into_space[OF A] by(fastforce simp: space_restrict_space)
      show "f' -` A \<inter> space (restrict_space L (f -` Inl ` space M))
            \<in> sets (restrict_space L (f -` Inl ` space M))"
        by simp
    next
      show "\<And>x. x \<in> space (restrict_space L (f -` Inl ` space M)) \<Longrightarrow> f' x \<in> space M"
        by(auto simp: space_restrict_space f'_space)
    qed simp_all
    finally show ?thesis .
  qed
  moreover have "f'' \<in> L \<rightarrow>\<^sub>M N"
  proof -
    have "f'' = (\<lambda>x. if x \<notin> f -` Inl ` space M then f'' x else n)"
      by(auto simp add: f''_def)
    also have "... \<in> L \<rightarrow>\<^sub>M N"
    proof(rule measurable_If_restrict_space_iff[THEN iffD2,OF _ conjI[OF measurableI]])
      fix A
      assume A[measurable]:"A \<in> sets N"
      have f:"f \<in> restrict_space L {x. x \<notin> f -` Inl ` space M} \<rightarrow>\<^sub>M M \<Oplus>\<^sub>M N"
        by(auto intro!: measurable_restrict_space1)
      have 1:"f'' -` A \<inter> space (restrict_space L {x. x \<notin> f -` Inl ` space M})
               = f -` (Inr ` A) \<inter> space (restrict_space L {x. x \<notin> f -` Inl ` space M})"
        using f'' sets.sets_into_space[OF A] by(fastforce simp: space_restrict_space)
      show "f'' -` A \<inter> space (restrict_space L {x. x \<notin> f -` Inl ` space M})
            \<in> sets (restrict_space L {x. x \<notin> f -` Inl ` space M})"
        unfolding 1 using f by simp
    next
      show "\<And>x. x \<in> space (restrict_space L {x. x \<notin> f -` Inl ` space M}) \<Longrightarrow> f'' x \<in> space N"
        by(auto simp: space_restrict_space f''_space)
    qed simp_all
    finally show ?thesis .
  qed
  ultimately show ?thesis
    using that f' f'' by blast
qed      

subsection \<open> Measures \<close>
lemma emeasure_copair_measure:
  assumes [measurable]: "A \<in> sets (M \<Oplus>\<^sub>M N)"
  shows "emeasure (M \<Oplus>\<^sub>M N) A = emeasure M (Inl -` A) + emeasure N (Inr -` A)"
proof(rule emeasure_measure_of)
  show "{Inl ` A |A. A \<in> sets M} \<union> {Inr ` A|A. A \<in> sets N} \<subseteq> Pow (space M <+> space N)"
    using sets.sets_into_space[of _ M] sets.sets_into_space[of _ N] by fastforce
  show "A \<in> sets (M \<Oplus>\<^sub>M N)"
    by fact
  show "countably_additive (sets (M \<Oplus>\<^sub>M N)) (\<lambda>a. emeasure M (Inl -` a) + emeasure N (Inr -` a))"
  proof(safe intro!: countably_additiveI)
    note [measurable] =  measurable_vimage_Inl[of _ M N] measurable_vimage_Inr[of _ M N]
    fix A :: "nat \<Rightarrow> _ set"
    assume h:"range A \<subseteq> sets (M \<Oplus>\<^sub>M N)" "disjoint_family A"
    then have [measurable]: "\<And>i. A i \<in> sets (M \<Oplus>\<^sub>M N)"
      by blast
    have disj:"disjoint_family (\<lambda>i. Inl -` A i)" "disjoint_family (\<lambda>i. Inr -` A i)"
      using h by(auto simp: disjoint_family_on_def)
    show "(\<Sum>i. emeasure M (Inl -` A i) + emeasure N (Inr -` A i))
           = emeasure M (Inl -` \<Union> (range A)) + emeasure N (Inr -` \<Union> (range A))" (is "?lhs = ?rhs")
    proof -
      have "?lhs = (\<Sum>i. emeasure M (Inl -` A i)) + (\<Sum>i. emeasure N (Inr -` A i))"
        by(simp add: suminf_add)
      also have "... = emeasure M (\<Union>i. (Inl -` A i)) + emeasure N (\<Union>i. (Inr -` A i))"
      proof -
        have "(\<Sum>i. emeasure M (Inl -` A i)) = emeasure M (\<Union>i. (Inl -` A i))"
             "(\<Sum>i. emeasure N (Inr -` A i)) = emeasure N (\<Union>i. (Inr -` A i))"
          by(auto intro!: suminf_emeasure disj)
        thus ?thesis
          by argo
      qed
      also have "... = ?rhs"
        by(simp add: vimage_UN)
      finally show ?thesis .
    qed
  qed
qed(auto simp: positive_def copair_measure_def)

lemma emeasure_copair_measure_space:
 "emeasure (M \<Oplus>\<^sub>M N) (space (M \<Oplus>\<^sub>M N)) = emeasure M (space M) + emeasure N (space N)"
proof -
  have [simp]:"Inl -` space (M \<Oplus>\<^sub>M N) = space M" "Inr -` space (M \<Oplus>\<^sub>M N) = space N"
    by(auto simp: space_copair_measure)
  show ?thesis
    by(simp add: emeasure_copair_measure)
qed

corollary
  shows emeasure_copair_measure_Inl: "A \<in> sets M \<Longrightarrow> emeasure (M \<Oplus>\<^sub>M N) (Inl ` A) = emeasure M A"
    and emeasure_copair_measure_Inr: "B \<in> sets N \<Longrightarrow> emeasure (M \<Oplus>\<^sub>M N) (Inr ` B) = emeasure N B"
proof -
  have [simp]:"Inl -` Inl ` A = A" "Inr -` Inl ` A = {}" "Inl -` Inr ` B = {}" "Inr -` Inr ` B = B"
    by auto
  show "A \<in> sets M \<Longrightarrow> emeasure (M \<Oplus>\<^sub>M N) (Inl ` A) = emeasure M A"
       "B \<in> sets N \<Longrightarrow> emeasure (M \<Oplus>\<^sub>M N) (Inr ` B) = emeasure N B"
    by(simp_all add: emeasure_copair_measure)
qed

lemma measure_copair_measure:
  assumes [measurable]:"A \<in> sets (M \<Oplus>\<^sub>M N)" "emeasure (M \<Oplus>\<^sub>M N) A < \<infinity>"
  shows "measure (M \<Oplus>\<^sub>M N) A = measure M (Inl -` A) + measure N (Inr -` A)"
  using assms(2) by(auto simp add: emeasure_copair_measure measure_def intro!: enn2real_plus)

lemma
  shows measure_copair_measure_Inl: "A \<in> sets M \<Longrightarrow> measure (M \<Oplus>\<^sub>M N) (Inl ` A) = measure M A"
    and measure_copair_measure_Inr: "B \<in> sets N \<Longrightarrow> measure (M \<Oplus>\<^sub>M N) (Inr ` B) = measure N B"
  by(auto simp: emeasure_copair_measure_Inl measure_def emeasure_copair_measure_Inr)

subsection \<open> Finiteness \<close>
lemma finite_measure_copair_measure: "finite_measure M \<Longrightarrow> finite_measure N \<Longrightarrow> finite_measure (M \<Oplus>\<^sub>M N)"
  by(auto intro!: finite_measureI simp: emeasure_copair_measure_space finite_measure.finite_emeasure_space)

subsection \<open> $\sigma$-Finiteness \<close>
lemma sigma_finite_measure_copair_measure:
  assumes "sigma_finite_measure M" "sigma_finite_measure N"
  shows "sigma_finite_measure (M \<Oplus>\<^sub>M N)"
proof -
  obtain A B where AB[measurable]: "\<And>i. A i \<in> sets M" "(\<Union> (range A)) = space M" "\<And>i::nat. emeasure M (A i) \<noteq> \<infinity>"
      "\<And>i. B i \<in> sets N" "(\<Union> (range B)) = space N" "\<And>i::nat. emeasure N (B i) \<noteq> \<infinity>"
    by (metis range_subsetD sigma_finite_measure.sigma_finite assms)
  then have *:"(\<Union> (range (\<lambda>i. Inl ` (A i) \<union> Inr ` (B i)))) = space (M \<Oplus>\<^sub>M N)"
    unfolding space_copair_measure Plus_def by fastforce
  have [simp]: "\<And>i. Inl -` Inl ` A i \<union> Inl -` Inr ` B i = A i" "\<And>i. Inr -` Inl ` A i \<union> Inr -` Inr ` B i = B i"
    using sets.sets_into_space AB(1,4) by blast+  
  show ?thesis
    apply standard
    using AB * by(auto intro!: exI[where x="range (\<lambda>i. Inl ` (A i) \<union> Inr ` (B i))"]
                         simp: space_copair_measure emeasure_copair_measure)
qed

subsection \<open>Non-Negative Integral\<close>
lemma nn_integral_copair_measure:
  assumes "f \<in> borel_measurable (M \<Oplus>\<^sub>M N)"
  shows "(\<integral>\<^sup>+x. f x \<partial>(M \<Oplus>\<^sub>M N)) = (\<integral>\<^sup>+x. f (Inl x) \<partial>M) + (\<integral>\<^sup>+x. f (Inr x) \<partial>N)"
  using assms
proof induction
  case (cong f g)
  moreover hence "\<And>x. x \<in> space M \<Longrightarrow> f (Inl x) = g (Inl x)"
                 "\<And>x. x \<in> space N \<Longrightarrow> f (Inr x) = g (Inr x)"
    by(auto simp: space_copair_measure)
  ultimately show ?case
    by(simp cong: nn_integral_cong)
next
  case [measurable]:(set A)
  note [measurable] = measurable_vimage_Inl[of _ M N] measurable_vimage_Inr[of _ M N]
  show ?case
    by (simp add: indicator_vimage[symmetric] emeasure_copair_measure)
next
  case (mult u c)
  then show ?case
    by(simp add: measurable_copair_measure_iff nn_integral_cmult distrib_left)
next
  case (add u v)
  then show ?case
    by(simp add: nn_integral_add)
next
  case h[measurable]:(seq U)
  have inc:"\<And>x. incseq (\<lambda>i. U i x)"
    by (metis h(3) incseq_def le_funE)
  have lim:"(\<lambda>i. U i x) \<longlonglongrightarrow> Sup (range U) x" for x
    by (metis SUP_apply LIMSEQ_SUP[OF inc[of x]])
  have "(\<lambda>i. (\<integral>\<^sup>+ x. U i x \<partial>(M \<Oplus>\<^sub>M N))) \<longlonglongrightarrow> (\<integral>\<^sup>+ x. (Sup (range U)) x \<partial>(M \<Oplus>\<^sub>M N))"
    by(intro nn_integral_LIMSEQ[OF _ _ lim]) (auto simp: h)
  moreover have "(\<lambda>i. (\<integral>\<^sup>+ x. U i x \<partial>(M \<Oplus>\<^sub>M N))) \<longlonglongrightarrow> (\<integral>\<^sup>+ x. Sup (range U) (Inl x) \<partial>M) + (\<integral>\<^sup>+ x. Sup (range U) (Inr x) \<partial>N)"
  proof -
    have "(\<lambda>i. (\<integral>\<^sup>+ x. U i x \<partial>(M \<Oplus>\<^sub>M N))) = (\<lambda>i. (\<integral>\<^sup>+ x. U i (Inl x) \<partial>M) + (\<integral>\<^sup>+ x. U i (Inr x) \<partial>N))"
      by(simp add: h)
    also have "... \<longlonglongrightarrow> (\<integral>\<^sup>+ x. Sup (range U) (Inl x) \<partial>M) + (\<integral>\<^sup>+ x. Sup (range U) (Inr x) \<partial>N)"
    proof(rule tendsto_add)
      have inc:"\<And>x. incseq (\<lambda>i. U i (Inl x))"
        by (metis h(3) incseq_def le_funE)
      have lim:"(\<lambda>i. U i (Inl x)) \<longlonglongrightarrow> Sup (range U) (Inl x)" for x
        by (metis SUP_apply LIMSEQ_SUP[OF inc[of x]])
      show "(\<lambda>i. (\<integral>\<^sup>+ x. U i (Inl x) \<partial>M)) \<longlonglongrightarrow> (\<integral>\<^sup>+ x. Sup (range U) (Inl x) \<partial>M)"
        using inc by(intro nn_integral_LIMSEQ[OF _ _ lim]) (auto simp: incseq_def intro!: le_funI)
    next
      have inc:"\<And>x. incseq (\<lambda>i. U i (Inr x))"
        by (metis h(3) incseq_def le_funE)
      have lim:"(\<lambda>i. U i (Inr x)) \<longlonglongrightarrow> Sup (range U) (Inr x)" for x
        by (metis SUP_apply LIMSEQ_SUP[OF inc[of x]])
      show "(\<lambda>i. (\<integral>\<^sup>+ x. U i (Inr x) \<partial>N)) \<longlonglongrightarrow> (\<integral>\<^sup>+ x. Sup (range U) (Inr x) \<partial>N)"
        using inc by(intro nn_integral_LIMSEQ[OF _ _ lim]) (auto simp: incseq_def intro!: le_funI)
    qed
    finally show ?thesis .
  qed
  ultimately show ?case
    using LIMSEQ_unique by blast 
qed

subsection \<open> Integrability \<close>
lemma integrable_copair_measure_iff:
  fixes f :: "'a + 'b \<Rightarrow> 'c::{banach, second_countable_topology}"
  shows "integrable (M \<Oplus>\<^sub>M N) f \<longleftrightarrow> integrable M (\<lambda>x. f (Inl x)) \<and> integrable N (\<lambda>x. f (Inr x))"
  by(auto simp add: measurable_copair_measure_iff nn_integral_copair_measure integrable_iff_bounded)

corollary interable_copair_measureI:
  fixes f :: "'a + 'b \<Rightarrow> 'c::{banach, second_countable_topology}"
  shows "integrable M (\<lambda>x. f (Inl x)) \<Longrightarrow> integrable N (\<lambda>x. f (Inr x)) \<Longrightarrow> integrable (M \<Oplus>\<^sub>M N) f"
  by(simp add: integrable_copair_measure_iff)

subsection \<open> The Lebesgue Integral \<close>
lemma integral_copair_measure:
  fixes f :: "'a + 'b \<Rightarrow> 'c::{banach, second_countable_topology}"
  assumes "integrable (M \<Oplus>\<^sub>M N) f"
  shows "(\<integral>x. f x \<partial>(M \<Oplus>\<^sub>M N)) = (\<integral>x. f (Inl x) \<partial>M) + (\<integral>x. f (Inr x) \<partial>N)"
  using assms
proof induction
  case h[measurable]:(base A c)
  note [measurable] = measurable_vimage_Inl[of _ M N] measurable_vimage_Inr[of _ M N]
  have [simp]:"integrable (M \<Oplus>\<^sub>M N) (indicat_real A)" "integrable M (indicat_real (Inl -` A))"
              "integrable N (indicat_real (Inr -` A))"
    using h(2) by(auto simp: emeasure_copair_measure)
  show ?case
    by(cases "c = 0")
      (simp_all add: indicator_vimage[symmetric] measure_copair_measure measure_copair_measure[OF _ h(2)] scaleR_left_distrib)
next
  case (add f g)
  then show ?case
    by(simp add: integrable_copair_measure_iff)
next
  case ih:(lim f s)
  have "(\<lambda>n. (\<integral>x. s n x \<partial>(M \<Oplus>\<^sub>M N))) \<longlonglongrightarrow> (\<integral>x. f x \<partial>(M \<Oplus>\<^sub>M N))"
    using ih(1-4) by(auto intro!: integral_dominated_convergence[where w="\<lambda>x. 2 * norm (f x)"])
  moreover have "(\<lambda>n. (\<integral>x. s n x \<partial>(M \<Oplus>\<^sub>M N))) \<longlonglongrightarrow> (\<integral>x. f (Inl x) \<partial>M) + (\<integral>x. f (Inr x) \<partial>N)"
    using ih(1-4)
    by(auto intro!: integral_dominated_convergence[where w="\<lambda>x. 2 * norm (f (Inl x))"]
                    integral_dominated_convergence[where w="\<lambda>x. 2 * norm (f (Inr x))"] tendsto_add
              simp: ih(5) integrable_copair_measure_iff measurable_copair_measure_iff
                    borel_measurable_integrable space_copair_measure InlI InrI)
  ultimately show ?case
    using LIMSEQ_unique by blast
qed

section \<open> Coproduct Measures \<close>
definition coPiM :: "['i set, 'i \<Rightarrow> 'a measure] \<Rightarrow> ('i \<times> 'a) measure" where
"coPiM I Mi \<equiv> measure_of
                (SIGMA i:I. space (Mi i))
                {A. A\<subseteq>(SIGMA i:I. space (Mi i)) \<and> (\<forall>i\<in>I. Pair i -` A \<in> sets (Mi i))}
                (\<lambda>A. (\<Sum>\<^sub>\<infinity>i\<in>I. emeasure (Mi i) (Pair i -` A)))"

syntax
 "_coPiM" :: "pttrn \<Rightarrow> 'i set \<Rightarrow> 'a measure \<Rightarrow> ('i \<times> 'a) measure" (\<open>(3\<amalg>\<^sub>M _\<in>_./ _)\<close>  10)
translations
 "\<amalg>\<^sub>M x\<in>I. M" \<rightleftharpoons> "CONST coPiM I (\<lambda>x. M)"

subsection \<open> The Measurable Space and Measurability \<close>
lemma
  shows space_coPiM: "space (coPiM I Mi) = (SIGMA i:I. space (Mi i))"
    and sets_coPiM:
    "sets (coPiM I Mi) = sigma_sets (SIGMA i:I. space (Mi i)) {A. A\<subseteq>(SIGMA i:I. space (Mi i)) \<and> (\<forall>i\<in>I. Pair i -` A \<in> sets (Mi i))}"
    and sets_coPiM_eq:"sets (coPiM I Mi) = {A. A\<subseteq>(SIGMA i:I. space (Mi i)) \<and> (\<forall>i\<in>I. Pair i -` A \<in> sets (Mi i))}"
proof -
  have 1:"{A. A\<subseteq>(SIGMA i:I. space (Mi i)) \<and> (\<forall>i\<in>I. Pair i -` A \<in> sets (Mi i))} \<subseteq> Pow (SIGMA i:I. space (Mi i))"
    using sets.sets_into_space by auto
  show "space (coPiM I Mi) = (SIGMA i:I. space (Mi i))"
 and 2:"sets (coPiM I Mi)
        = sigma_sets (SIGMA i:I. space (Mi i)) {A. A\<subseteq>(SIGMA i:I. space (Mi i)) \<and> (\<forall>i\<in>I. Pair i -` A \<in> sets (Mi i))}"
    by(auto simp: sets_measure_of[OF 1] space_measure_of[OF 1] coPiM_def)
  show "sets (coPiM I Mi) = {A. A\<subseteq>(SIGMA i:I. space (Mi i)) \<and> (\<forall>i\<in>I. Pair i -` A \<in> sets (Mi i))}"
  proof -
    have "sigma_algebra (SIGMA i:I. space (Mi i)) {A. A \<subseteq> (SIGMA i:I. space (Mi i)) \<and> (\<forall>i\<in>I. Pair i -` A \<in> sets (Mi i))}"
    proof(subst Dynkin_system.sigma_algebra_eq_Int_stable)
      show "Dynkin_system (SIGMA i:I. space (Mi i)) {A. A \<subseteq> (SIGMA i:I. space (Mi i)) \<and> (\<forall>i\<in>I. Pair i -` A \<in> sets (Mi i))}"
        by unfold_locales (auto simp: Pair_vimage_Sigma sets.Diff vimage_Diff vimage_Union 1)
    qed (auto intro!: Int_stableI)
    thus ?thesis
      by(auto simp: 2 intro!: sigma_algebra.sigma_sets_eq)
  qed
qed

lemma sets_coPiM_cong:
 "I = J \<Longrightarrow> (\<And>i. i \<in> I \<Longrightarrow> sets (Mi i) = sets (Ni i)) \<Longrightarrow> sets (coPiM I Mi) = sets (coPiM J Ni)"
  by(simp cong: sets_eq_imp_space_eq Sigma_cong add: sets_coPiM)

lemma measurable_coPiM2:
  assumes [measurable]:"\<And>i. i \<in> I \<Longrightarrow> f i \<in> Mi i \<rightarrow>\<^sub>M N"
  shows "(\<lambda>(i,x). f i x) \<in> coPiM I Mi \<rightarrow>\<^sub>M N"
proof(rule measurableI)
  fix A
  assume [measurable]: "A \<in> sets N"
  have [simp]:
    "\<And>i. i \<in> I
    \<Longrightarrow> Pair i -` (\<lambda>(x, y). f x y) -` A \<inter> Pair i -` (SIGMA i:I. space (Mi i)) = f i -` A \<inter> space (Mi i)"
    by auto
  show "(\<lambda>(i, x). f i x) -` A \<inter> space (coPiM I Mi) \<in> sets (coPiM I Mi)"
    by(auto simp: sets_coPiM space_coPiM)
qed(auto simp: space_coPiM measurable_space[OF assms])

lemma measurable_Pair_coPiM[measurable (raw)]:
  assumes "i \<in> I"
  shows "Pair i \<in> Mi i \<rightarrow>\<^sub>M coPiM I Mi"
proof(rule measurable_sigma_sets)
  show "{A. A\<subseteq>(SIGMA i:I. space (Mi i)) \<and> (\<forall>i\<in>I. Pair i -` A \<in> sets (Mi i))}
         \<subseteq> Pow (SIGMA i:I. space (Mi i))"
    by blast
qed (auto simp: assms sets_coPiM)

lemma measurable_Pair_coPiM':
  assumes "i \<in> I" "(\<lambda>(i,x). f i x) \<in> coPiM I Mi \<rightarrow>\<^sub>M N"
  shows "f i \<in> Mi i \<rightarrow>\<^sub>M N"
  using measurable_compose[OF measurable_Pair_coPiM assms(2)] assms(1) by fast

lemma measurable_copair_iff: "(\<lambda>(i,x). f i x) \<in> coPiM I Mi \<rightarrow>\<^sub>M N \<longleftrightarrow> (\<forall>i\<in>I. f i \<in> Mi i \<rightarrow>\<^sub>M N)"
  by(auto intro!: measurable_coPiM2 simp: measurable_Pair_coPiM')

lemma measurable_copair_iff': "f \<in> coPiM I Mi \<rightarrow>\<^sub>M N \<longleftrightarrow> (\<forall>i\<in>I. (\<lambda>x. f (i, x)) \<in> Mi i \<rightarrow>\<^sub>M N)"
  using measurable_copair_iff[of "curry f"] by(simp add: split_beta' curry_def)

lemma coPair_inverse_space_unit:
  "i \<in> I \<Longrightarrow> A \<in> sets (coPiM I Mi) \<Longrightarrow> Pair i -` A \<inter> space (Mi i) = Pair i -` A"
  using sets.sets_into_space by(fastforce simp: space_coPiM)

lemma measurable_Pair_vimage:
  assumes "i \<in> I" "A \<in> sets (coPiM I Mi)"
  shows "Pair i -` A \<in> sets (Mi i)"
  using measurable_sets[OF measurable_Pair_coPiM[OF assms(1)] assms(2)]
  by (simp add: coPair_inverse_space_unit[OF assms])

lemma measurable_Sigma_singleton[measurable (raw)]:
 "\<And>i A. i \<in> I \<Longrightarrow> A \<in> sets (Mi i) \<Longrightarrow> {i} \<times> A \<in> sets (coPiM I Mi)"
  using sets.sets_into_space sets_coPiM by fastforce

lemma sets_coPiM_countable:
  assumes "countable I"
  shows "sets (coPiM I Mi) = sigma_sets (SIGMA i:I. space (Mi i)) (\<Union>i\<in>I. (\<times>) {i} ` (sets (Mi i)))"
  unfolding sets_coPiM
proof(safe intro!: sigma_sets_eqI)
  fix a
  assume h:"a \<subseteq> (SIGMA i:I. space (Mi i))" "\<forall>i\<in>I. Pair i -` a \<in> sets (Mi i)"
  then have "a = (\<Union>i\<in>I. {i} \<times> Pair i -` a)"
    by auto
  moreover have "(\<Union>i\<in>I. {i} \<times> Pair i -` a) \<in> sigma_sets (SIGMA i:I. space (Mi i)) (\<Union>i\<in>I. (\<times>) {i} ` (sets (Mi i)))"
    using h(2) by(auto intro!: sigma_sets_UNION[OF countable_image[OF assms]])
  ultimately show "a \<in> sigma_sets (SIGMA i:I. space (Mi i)) (\<Union>i\<in>I. (\<times>) {i} ` (sets (Mi i)))"
    by argo
qed(use sets.sets_into_space in fastforce)

lemma measurable_coPiM1':
  assumes "countable I"
    and [measurable]: "a \<in> N \<rightarrow>\<^sub>M count_space I" "\<And>i. i \<in> a ` (space N) \<Longrightarrow> g i \<in> N \<rightarrow>\<^sub>M Mi i"
  shows "(\<lambda>x. (a x, g (a x) x)) \<in> N \<rightarrow>\<^sub>M coPiM I Mi"
proof(safe intro!: measurable_sigma_sets[OF sets_coPiM_countable[OF assms(1)]])
  fix i B
  assume iB[measurable]:"i \<in> I" "B \<in> sets (Mi i)"
  show  "(\<lambda>x. (a x, g (a x) x)) -` ({i} \<times> B) \<inter> space N \<in> sets N"
  proof(cases "i \<in> a ` (space N)")
    assume [measurable]:"i \<in> a ` (space N)"
    have "(\<lambda>x. (a x, g (a x) x)) -` ({i} \<times> B) \<inter> space N = (a -` {i} \<inter> space N) \<inter> (g i -` B \<inter> space N)"
      by auto
    also have "... \<in> sets N"
      by simp
    finally show ?thesis .
  next
    assume"i \<notin> a ` (space N)"
    then have "(\<lambda>x. (a x, g (a x) x)) -` ({i} \<times> B) \<inter> space N = {}"
      using measurable_space[OF assms(2)] by blast
    thus ?thesis
      by simp
  qed
qed(use measurable_space[OF assms(2)] measurable_space[OF assms(3)] sets.sets_into_space in fastforce)+

lemma measurable_coPiM1:
  assumes "countable I"
    and "a \<in> N \<rightarrow>\<^sub>M count_space I" "\<And>i. i \<in> I \<Longrightarrow> g i \<in> N \<rightarrow>\<^sub>M Mi i"
  shows "(\<lambda>x. (a x, g (a x) x)) \<in> N \<rightarrow>\<^sub>M coPiM I Mi"
  using measurable_space[OF assms(2)] by(auto intro!: measurable_coPiM1' assms)

lemma measurable_coPiM1_elements:
  assumes "countable I" and [measurable]:"f \<in> N \<rightarrow>\<^sub>M coPiM I Mi"
  obtains a g
  where "a \<in> N \<rightarrow>\<^sub>M count_space I"
        "\<And>i. i \<in> I \<Longrightarrow> space (Mi i) \<noteq> {} \<Longrightarrow> g i \<in> N \<rightarrow>\<^sub>M Mi i"
        "f = (\<lambda>x. (a x, g (a x) x))"
proof -
  define a where "a \<equiv> fst \<circ> f"
  have 1[measurable]:"a \<in> N \<rightarrow>\<^sub>M count_space I"
  proof(safe intro!: measurable_count_space_eq_countable[THEN iffD2] assms)
    fix i
    assume i:"i \<in> I"
    have "a -` {i} \<inter> space N = f -` ({i} \<times> space (Mi i)) \<inter> space N"
      using measurable_space[OF assms(2)] by(fastforce simp: a_def space_coPiM)
    also have "... \<in> sets N"
      using i by auto
    finally show "a -` {i} \<inter> space N \<in> sets N" .
  next
    show "\<And>x. x \<in> space N \<Longrightarrow> a x \<in> I"
      using measurable_space[OF assms(2)] by(fastforce simp: space_coPiM a_def)
  qed
  define g where "g \<equiv> (\<lambda>i x. if a x = i then snd (f x) else (SOME y. y \<in> space (Mi i)))"
  have 2:"g i \<in> N \<rightarrow>\<^sub>M Mi i" if i:"i \<in> I" and ne:"space (Mi i) \<noteq> {}" for i
    unfolding g_def
  proof(safe intro!: measurable_If_restrict_space_iff[THEN iffD2] measurable_const some_in_eq[THEN iffD2] ne)
    show "(\<lambda>x. snd (f x))  \<in> restrict_space N {x. a x = i} \<rightarrow>\<^sub>M Mi i"
    proof(safe intro!: measurableI)
      show "\<And>x. x \<in> space (restrict_space N {x. a x = i}) \<Longrightarrow> snd (f x) \<in> space (Mi i)"
        using measurable_space[OF assms(2)] by(fastforce simp: space_restrict_space a_def space_coPiM)
    next
      fix A
      assume [measurable]:"A \<in> sets (Mi i)"
      have "(\<lambda>x. snd (f x)) -` A \<inter> space (restrict_space N {x. a x = i}) = f -` ({i} \<times> A) \<inter> space N"
        using i measurable_space[OF assms(2)] by(fastforce simp: space_restrict_space a_def space_coPiM)
      also have "... \<in> sets N"
        using i by simp
      finally show "(\<lambda>x. snd (f x)) -` A \<inter> space (restrict_space N {x. a x = i})
                     \<in> sets (restrict_space N {x. a x = i})"
        by(auto simp: sets_restrict_space space_restrict_space)
    qed
  qed(use i ne in auto)
  have 3:"f = (\<lambda>x. (a x, g (a x) x))"
    by(auto simp: a_def g_def)
  show ?thesis
    using 1 2 3 that by blast
qed

subsection \<open> Measures \<close>
lemma emeasure_coPiM:
  assumes "A \<in> sets (coPiM I Mi)"
  shows "emeasure (coPiM I Mi) A = (\<Sum>\<^sub>\<infinity>i\<in>I. emeasure (Mi i) (Pair i -` A))"
proof(rule emeasure_measure_of)
  show "{A. A\<subseteq>(SIGMA i:I. space (Mi i)) \<and> (\<forall>i\<in>I. Pair i -` A \<in> sets (Mi i))} \<subseteq> Pow (SIGMA i:I. space (Mi i))"
    by blast
next
  note measurable_Pair_vimage[of _ I _ Mi,measurable (raw)]
  show "countably_additive (sets (coPiM I Mi)) (\<lambda>a. \<Sum>\<^sub>\<infinity>i\<in>I. emeasure (Mi i) (Pair i -` a))"
    unfolding countably_additive_def
  proof safe
    fix A :: "nat \<Rightarrow> _"
    assume A:"range A \<subseteq> sets (coPiM I Mi)" "disjoint_family A"
    then have [measurable]:"\<And>n. A n \<in> sets (coPiM I Mi)"
      by blast
    show "(\<Sum>n. \<Sum>\<^sub>\<infinity>i\<in>I. emeasure (Mi i) (Pair i -` A n))
           = (\<Sum>\<^sub>\<infinity>i\<in>I. emeasure (Mi i) (Pair i -` \<Union> (range A)))" (is "?lhs = ?rhs")
    proof -
      have "?lhs = (\<Sum>\<^sub>\<infinity>n\<in>UNIV. \<Sum>\<^sub>\<infinity>i\<in>I. emeasure (Mi i) (Pair i -` A n))"
        by(auto intro!: infsum_eq_suminf[symmetric] nonneg_summable_on_complete)
      also have "... = (\<Sum>\<^sub>\<infinity>i\<in>I. \<Sum>\<^sub>\<infinity>n\<in>UNIV. emeasure (Mi i) (Pair i -` A n))"
        by(rule infsum_swap_ennreal)
      also have "... = ?rhs"
      proof(rule infsum_cong)
        fix i
        assume "i \<in> I"
        then have "(\<Sum>n. Mi i (Pair i -` A n)) = Mi i (\<Union>n. Pair i -` A n)"
          using A(2) by(intro suminf_emeasure) (auto simp: disjoint_family_on_def)
        also have "... = Mi i (Pair i -` \<Union> (range A))"
          by (metis vimage_UN)
        finally show "(\<Sum>\<^sub>\<infinity>n. emeasure (Mi i) (Pair i -` A n)) = emeasure (Mi i) (Pair i -` \<Union> (range A))"
          by(auto simp: infsum_eq_suminf[OF nonneg_summable_on_complete])
      qed
      finally show ?thesis .
    qed
  qed
next
  show "A \<in> sets (coPiM I Mi)"
    by fact
qed(auto simp: positive_def coPiM_def)

corollary emeasure_coPiM_space:
 "emeasure (coPiM I Mi) (space (coPiM I Mi)) = (\<Sum>\<^sub>\<infinity>i\<in>I. emeasure (Mi i) (space (Mi i)))"
proof -
  have [simp]: "\<And>i. i \<in> I \<Longrightarrow> Pair i -` space (coPiM I Mi) = space (Mi i)"
    by(auto simp: space_coPiM)
  show ?thesis
    by(auto simp: emeasure_coPiM intro!: infsum_cong)
qed

lemma emeasure_coPiM_coproj:
  assumes [measurable]: "i \<in> I" "A \<in> sets (Mi i)"
  shows "emeasure (coPiM I Mi) ({i} \<times> A) = emeasure (Mi i) A"
proof -
  have "emeasure (coPiM I Mi) ({i} \<times> A) = (\<Sum>\<^sub>\<infinity>j\<in>I. emeasure (Mi j) (if j = i then A else {}))"
    by(simp add: emeasure_coPiM)
  also have "... = (\<Sum>\<^sub>\<infinity>j\<in>(I - {i}) \<union> {i}. emeasure (Mi j) (if j = i then A else {}))"
    by(rule arg_cong[where f="infsum _"]) (use assms in auto)
  also have "... = (\<Sum>\<^sub>\<infinity>j\<in>I - {i}. emeasure (Mi j) (if j = i then A else {}))
                    + (\<Sum>\<^sub>\<infinity>j\<in>{i}. emeasure (Mi j) (if j = i then A else {}))"
    by(rule infsum_Un_disjoint) (auto intro!: nonneg_summable_on_complete)
  also have "... = emeasure (Mi i) A"
  proof -
    have "(\<Sum>\<^sub>\<infinity>j\<in>I - {i}. emeasure (Mi j) (if j = i then A else {})) = 0"
      by (rule infsum_0) simp
    thus ?thesis by simp
  qed
  finally show ?thesis .
qed

lemma measure_coPiM_coproj: "i \<in> I \<Longrightarrow> A \<in> sets (Mi i) \<Longrightarrow> measure (coPiM I Mi) ({i} \<times> A) = measure (Mi i) A"
  by(simp add: emeasure_coPiM_coproj measure_def)

lemma emeasure_coPiM_less_top_summable:
  assumes [measurable]:"A \<in> sets (coPiM I Mi)" "emeasure (coPiM I Mi) A < \<infinity>"
  shows"(\<lambda>i. measure (Mi i) (Pair i -` A)) summable_on I"
proof -
  have *:"(\<Sum>\<^sub>\<infinity>i\<in>I. emeasure (Mi i) (Pair i -` A)) < top"
    using assms(2) by(simp add: emeasure_coPiM)
  from infsum_less_top_dest[OF this] have ifin:"\<And>i. i \<in> I \<Longrightarrow> emeasure (Mi i) (Pair i -` A) < top"
    by simp
  with * have "(\<Sum>\<^sub>\<infinity>i\<in>I. ennreal (measure (Mi i) (Pair i -` A))) < top"
    by (metis (mono_tags, lifting) emeasure_eq_ennreal_measure infsum_cong top.not_eq_extremum)
  thus ?thesis
    by(auto intro!: bounded_infsum_summable)
qed

lemma measure_coPiM:
  assumes [measurable]:"A \<in> sets (coPiM I Mi)" "emeasure (coPiM I Mi) A < \<infinity>"
  shows "measure (coPiM I Mi) A = (\<Sum>\<^sub>\<infinity>i\<in>I. measure (Mi i) (Pair i -` A))"
proof(subst ennreal_inj[symmetric])
  have *:"(\<Sum>\<^sub>\<infinity>i\<in>I. emeasure (Mi i) (Pair i -` A)) < top"
    using assms(2) by(simp add: emeasure_coPiM)
  from infsum_less_top_dest[OF this] have ifin:"\<And>i. i \<in> I \<Longrightarrow> emeasure (Mi i) (Pair i -` A) < top"
    by simp
  show "ennreal (measure (coPiM I Mi) A) = ennreal (\<Sum>\<^sub>\<infinity>i\<in>I. measure (Mi i) (Pair i -` A))" (is "?lhs = ?rhs")
  proof -
    have "?lhs = emeasure (coPiM I Mi) A"
      using assms by(auto intro!: emeasure_eq_ennreal_measure[symmetric])
    also have "... = (\<Sum>\<^sub>\<infinity>i\<in>I. emeasure (Mi i) (Pair i -` A))"
      by(simp add: emeasure_coPiM)
    also have "... = (\<Sum>\<^sub>\<infinity>i\<in>I. ennreal (measure (Mi i) (Pair i -` A)))"
      using ifin by(fastforce intro!: infsum_cong  emeasure_eq_ennreal_measure)
    also have "... = ?rhs"
      by(simp add: infsum_ennreal_eq[OF emeasure_coPiM_less_top_summable[OF assms]])
    finally show ?thesis .
  qed
qed(auto intro!: infsum_nonneg)

subsection \<open>Non-Negative Integral\<close>
lemma nn_integral_coPiM:
  assumes "f \<in> borel_measurable (coPiM I Mi)"
  shows "(\<integral>\<^sup>+x. f x \<partial>coPiM I Mi) = (\<Sum>\<^sub>\<infinity>i\<in>I. (\<integral>\<^sup>+x. f (i, x) \<partial>Mi i))"
  using assms
proof induction
  case (cong f g)
  moreover hence "\<And>i x. i \<in> I \<Longrightarrow> x \<in> space (Mi i) \<Longrightarrow> f (i, x) = g (i, x)"
    by(auto simp: space_coPiM)
  ultimately show ?case
    by(simp cong: nn_integral_cong infsum_cong)
next
  case [measurable]:(set A)
  note [measurable] = measurable_Pair_vimage[OF _ this]
  show ?case
    by(simp add: indicator_vimage[symmetric] emeasure_coPiM cong: infsum_cong)
next
  case (add u v)
  then show ?case
    by(simp add: nn_integral_add infsum_add nonneg_summable_on_complete cong: infsum_cong)
next
  case (mult u c)
  then show ?case
    by(simp add: nn_integral_cmult infsum_cmult_right_ennreal cong: infsum_cong)
next
  case ih[measurable]:(seq U)
  show ?case (is "?lhs = ?rhs")
  proof -
    have "?lhs = (\<integral>\<^sup>+ x. (SUP j. U j x) \<partial>coPiM I Mi)"
      by(auto intro!: nn_integral_cong simp: SUP_apply[symmetric])
    also have "... = (SUP j. (\<integral>\<^sup>+ x. U j x \<partial>coPiM I Mi))"
      by(auto intro!: nn_integral_monotone_convergence_SUP ih(3))
    also have "... = (SUP j. (\<Sum>\<^sub>\<infinity>i\<in>I. (\<integral>\<^sup>+ x. U j (i, x) \<partial>Mi i)))"
      by(simp add: ih)
    also have "... = (\<Sum>\<^sub>\<infinity>i\<in>I. (SUP j. (\<integral>\<^sup>+ x. U j (i, x) \<partial>Mi i)))"
      using ih(3) by(auto intro!: ennreal_infsum_Sup_eq[symmetric] incseq_nn_integral simp: mono_compose)
    also have "... = (\<Sum>\<^sub>\<infinity>i\<in>I. (\<integral>\<^sup>+ x. (SUP j. U j (i, x)) \<partial>Mi i))"
      using ih(3) by(auto intro!: infsum_cong nn_integral_monotone_convergence_SUP[symmetric] mono_compose)
    also have "... = ?rhs"
      by(simp add: SUP_apply[symmetric])
    finally show ?thesis .
  qed
qed

subsection \<open> Integrability \<close>
lemma
  fixes f :: "_ \<Rightarrow> 'b::{banach, second_countable_topology}"
  assumes "integrable (coPiM I Mi) f"
  shows integrable_coPiM_dest_sum:"(\<Sum>\<^sub>\<infinity>i\<in>I. (\<integral>\<^sup>+ x. norm (f (i, x)) \<partial>Mi i)) < \<infinity>"
    and integrable_coPiM_dest_integrable: "\<And>i. i \<in> I \<Longrightarrow> integrable (Mi i) (\<lambda>x. f (i, x))"
    and integrable_coPiM_summable_norm: "(\<lambda>i. (\<integral>x. norm (f (i, x)) \<partial>Mi i)) summable_on I"
    and integrable_coPiM_abs_summable: "Infinite_Sum.abs_summable_on (\<lambda>i. (\<integral>x. f (i, x) \<partial>Mi i)) I"
    and integrable_coPiM_summable: "(\<lambda>i. (\<integral>x. f (i, x) \<partial>Mi i)) summable_on I"
proof -
  show fin:"(\<Sum>\<^sub>\<infinity>i\<in>I. (\<integral>\<^sup>+ x. norm (f (i, x)) \<partial>Mi i)) < \<infinity>"
    using assms by(auto simp: integrable_iff_bounded nn_integral_coPiM)
  thus integ:"i \<in> I \<Longrightarrow> integrable (Mi i) (\<lambda>x. f (i, x))" for i
    using assms by(auto simp: integrable_iff_bounded intro!: infsum_less_top_dest[of _ _ i])
  show summable:"(\<lambda>i. (\<integral>x. norm (f (i, x)) \<partial>Mi i)) summable_on I"
    using nn_integral_eq_integral[OF integrable_norm[OF integ]] fin
    by(auto intro!: bounded_infsum_summable cong: infsum_cong)
  show "Infinite_Sum.abs_summable_on (\<lambda>i. (\<integral>x. f (i, x) \<partial>Mi i)) I"
    by(rule summable_on_comparison_test[OF summable]) auto
  thus "(\<lambda>i. (\<integral>x. f (i, x) \<partial>Mi i)) summable_on I"
    using abs_summable_summable by fastforce
qed

subsection \<open> The Lebesgue Integral \<close>
lemma integral_coPiM:
  fixes f :: "_ \<Rightarrow> 'b::{banach, second_countable_topology}"
  assumes "integrable (coPiM I Mi) f"
  shows "(\<integral>x. f x \<partial>coPiM I Mi) = (\<Sum>\<^sub>\<infinity>i\<in>I. (\<integral>x. f (i, x) \<partial>Mi i))"
  using assms
proof induction
  case h[measurable]:(base A c)
  note [measurable] = measurable_Pair_vimage[OF _ this(1)]
  have [simp]: "integrable (coPiM I Mi) (indicat_real A)"
    "\<And>i. i \<in> I \<Longrightarrow> integrable (Mi i) (indicat_real (Pair i -` A))"
    using h(2) by(auto simp: emeasure_coPiM dest: infsum_less_top_dest)
  show ?case
    using h(2) emeasure_coPiM_less_top_summable[OF h]
    by(cases "c = 0")
      (auto simp: measure_coPiM indicator_vimage[symmetric] infsum_scaleR_left[symmetric] cong: infsum_cong)
next
  case h:(add f g)
  show ?case (is "?lhs = ?rhs")
  proof -
    have "?lhs = (\<Sum>\<^sub>\<infinity>i\<in>I. (\<integral>x. f (i, x) \<partial>Mi i)) + (\<Sum>\<^sub>\<infinity>i\<in>I. (\<integral>x. g (i, x) \<partial>Mi i))"
      using h by simp
    also have "... = (\<Sum>\<^sub>\<infinity>i\<in>I. (\<integral>x. f (i, x) \<partial>Mi i) + (\<integral>x. g (i, x) \<partial>Mi i))"
      by(auto intro!: infsum_add[symmetric] integrable_coPiM_summable h)
    also have "... = ?rhs"
      using h
      by(auto intro!: infsum_cong Bochner_Integration.integral_add[symmetric] integrable_coPiM_dest_integrable)
    finally show ?thesis .
  qed
next
  case ih:(lim f fn)
  note [measurable,simp] = ih(1-4)
  show ?case (is "?lhs = ?rhs")
  proof -
    have "?lhs = lim (\<lambda>n. (\<integral>x. fn n x \<partial>(coPiM I Mi)))"
      by(auto intro!: limI[symmetric] integral_dominated_convergence[where w="\<lambda>x. 2 * norm (f x)"])
    also have "... = lim (\<lambda>n. (\<Sum>\<^sub>\<infinity>i\<in>I.  (\<integral>x. fn n (i, x) \<partial>Mi i)))"
      by(simp add: ih(5))
    also have "... = lim (\<lambda>n. (\<integral>i. (\<integral>x. fn n (i, x) \<partial>Mi i)\<partial>count_space I))"
      by(simp add: integrable_coPiM_abs_summable infsum_eq_integral)
    also have "... = (\<integral>i. (\<integral>x. f (i, x) \<partial>Mi i)\<partial>count_space I)"
    proof(intro limI integral_dominated_convergence[where w="\<lambda>i. (\<integral>x. 2 * norm (f (i, x)) \<partial>Mi i)"] AE_I2 )
      show "integrable (count_space I) (\<lambda>i. (\<integral>x. 2 * norm (f (i, x)) \<partial>Mi i))"
        by(auto simp: abs_summable_on_integrable_iff[symmetric] integrable_coPiM_summable_norm[OF ih(4)])
    next
      show "i \<in> space (count_space I) \<Longrightarrow> (\<lambda>n. (\<integral>x. fn n (i, x) \<partial>Mi i)) \<longlonglongrightarrow> (\<integral>x. f (i, x) \<partial>Mi i)" for i
        by(auto intro!: integral_dominated_convergence[where w="\<lambda>x. 2*norm (f (i, x))"] integrable_coPiM_dest_integrable
                  simp: space_coPiM)
    next
      show "i \<in> space (count_space I) \<Longrightarrow> norm ((\<integral>x. fn n (i, x) \<partial>Mi i)) \<le> (\<integral>x.  2 * norm (f (i, x)) \<partial>Mi i)" for n i
        by(rule order.trans[where b="(\<integral>x. norm (fn n (i, x)) \<partial>Mi i)"])
          (auto simp: space_coPiM
            simp del: Bochner_Integration.integral_mult_right_zero Bochner_Integration.integral_mult_right
              intro!: integral_mono integrable_coPiM_dest_integrable)
    qed simp_all
    also have "... = ?rhs"
      by(simp add: infsum_eq_integral integrable_coPiM_abs_summable)
    finally show ?thesis .
  qed
qed

subsection \<open> Finite Coproduct Measures \<close>
lemma emeasure_coPiM_finite:
  assumes "finite I" "A \<in> sets (coPiM I Mi)"
  shows "emeasure (coPiM I Mi) A = (\<Sum>i\<in>I. emeasure (Mi i) (Pair i -` A))"
  using assms by(simp add: emeasure_coPiM)

lemma emeasure_coPiM_finite_space:
 "finite I \<Longrightarrow> emeasure (coPiM I Mi) (space (coPiM I Mi)) = (\<Sum>i\<in>I. emeasure (Mi i) (space (Mi i)))"
  by(simp add: emeasure_coPiM_space)

lemma measure_coPiM_finite:
  assumes "finite I" "A \<in> sets (coPiM I Mi)" "emeasure (coPiM I Mi) A < \<infinity>"
  shows "measure (coPiM I Mi) A = (\<Sum>i\<in>I. measure (Mi i) (Pair i -` A))"
  using assms(3) by(simp add: emeasure_coPiM_finite[OF assms(1,2)] measure_def enn2real_sum assms(1))

lemma nn_integral_coPiM_finite:
  assumes "finite I" "f \<in> borel_measurable (coPiM I Mi)"
  shows "(\<integral>\<^sup>+x. f x \<partial>(coPiM I Mi)) = (\<Sum>i\<in>I. (\<integral>\<^sup>+x. f (i, x) \<partial>(Mi i)))"
  by(simp add: nn_integral_coPiM assms)

lemma integrable_coPiM_finite_iff:
  fixes f :: "_ \<Rightarrow> 'c::{banach, second_countable_topology}"
  shows "finite I \<Longrightarrow> integrable (coPiM I Mi) f \<longleftrightarrow> (\<forall>i\<in>I. integrable (Mi i) (\<lambda>x. f (i, x)))"
  using measurable_copair_iff'[of f I Mi borel]
  by(auto simp: integrable_iff_bounded nn_integral_coPiM_finite)

lemma integral_coPiM_finite:
  fixes f :: "_ \<Rightarrow> 'c::{banach, second_countable_topology}"
  assumes "finite I" "integrable (coPiM I Mi) f"
  shows "(\<integral>x. f x \<partial>(coPiM I Mi)) = (\<Sum>i\<in>I. (\<integral>x. f (i, x) \<partial>(Mi i)))"
  by(auto simp: assms integral_coPiM)

subsection \<open> Countable Infinite Coproduct Measures \<close>
lemma emeasure_coPiM_countable_infinite:
  assumes [measurable]: "bij_betw from_n (UNIV :: nat set) I" "A \<in> sets (coPiM I Mi)"
  shows "emeasure (coPiM I Mi) A = (\<Sum>n. emeasure (Mi (from_n n)) (Pair (from_n n) -` A))"
proof -
  have I:"countable I"
    using assms(1) countableI_bij by blast
  have [measurable,simp]:"Pair (from_n n) -` A \<in> sets (Mi (from_n n))" "from_n n \<in> I" for n
    using bij_betwE[OF assms(1)] by(auto intro!: measurable_Pair_vimage[where I=I])
  have "emeasure (coPiM I Mi) A = emeasure (coPiM I Mi) (\<Union>n. {from_n n} \<times> Pair (from_n n) -` A)"
    using sets.sets_into_space[OF assms(2)] assms(1)
    by(fastforce intro!: arg_cong[where f="emeasure (coPiM I Mi)"]
                   simp: space_coPiM  bij_betw_def)
  also have "... = (\<Sum>n. emeasure (Mi (from_n n)) (Pair (from_n n) -` A))"
    using injD[OF bij_betw_imp_inj_on[OF assms(1)]]
    by(subst suminf_emeasure[symmetric])
      (auto simp: disjoint_family_on_def emeasure_coPiM_coproj intro!: suminf_cong)
  finally show ?thesis .
qed

lemmas emeasure_coPiM_countable_infinite' = emeasure_coPiM_countable_infinite[OF bij_betw_from_nat_into]
lemmas emeasure_coPiM_nat = emeasure_coPiM_countable_infinite[OF bij_id,simplified]

lemma measure_coPiM_countable_infinite:
  assumes [measurable,simp]: "bij_betw from_n (UNIV :: nat set) I" "A \<in> sets (coPiM I Mi)"
    and "emeasure (coPiM I Mi) A < \<infinity>"
  shows "measure (coPiM I Mi) A = (\<Sum>n. measure (Mi (from_n n)) (Pair (from_n n) -` A))" (is "?lhs = ?rhs")
    and "summable (\<lambda>n. measure (Mi (from_n n)) (Pair (from_n n) -` A))"
proof -
  have "ennreal ?lhs = emeasure (coPiM I Mi) A"
    using assms(3) by(auto intro!: emeasure_eq_ennreal_measure[symmetric])
  also have "... = (\<Sum>n. emeasure (Mi (from_n n)) (Pair (from_n n) -` A))"
    by(simp add: emeasure_coPiM_countable_infinite)
  also have "... = (\<Sum>n. ennreal (measure (Mi (from_n n)) (Pair (from_n n) -` A)))"
    using assms(3) ennreal_suminf_lessD top.not_eq_extremum
    by(auto intro!: suminf_cong emeasure_eq_ennreal_measure
              simp: emeasure_coPiM_countable_infinite[OF assms(1)])
  finally have *:"ennreal ?lhs = (\<Sum>n. ennreal (measure (Mi (from_n n)) (Pair (from_n n) -` A)))" .
  thus **[simp]: "summable (\<lambda>n. measure (Mi (from_n n)) (Pair (from_n n) -` A))"
    by(auto intro!: summable_suminf_not_top)
  show "?lhs = ?rhs"
  proof(subst ennreal_inj[symmetric])
    have "ennreal ?lhs = (\<Sum>n. ennreal (measure (Mi (from_n n)) (Pair (from_n n) -` A)))"
      by fact
    also have "... = ennreal ?rhs"
      using assms(3) by(auto intro!: suminf_ennreal2)
    finally show "ennreal ?lhs = ennreal ?rhs" .
  qed(simp_all add: suminf_nonneg)
qed

lemmas measure_coPiM_countable_infinite' = measure_coPiM_countable_infinite[OF bij_betw_from_nat_into]
lemmas measure_coPiM_nat = measure_coPiM_countable_infinite[OF bij_id,simplified id_apply]

lemma nn_integral_coPiM_countable_infinite:
  assumes [measurable]:"bij_betw from_n (UNIV :: nat set) I" "f \<in> borel_measurable (coPiM I Mi)"
  shows "(\<integral>\<^sup>+x. f x \<partial>(coPiM I Mi)) = (\<Sum>n. (\<integral>\<^sup>+x. f (from_n n, x) \<partial>(Mi (from_n n))))" (is "_ = ?rhs")
proof -
  have "(\<integral>\<^sup>+x. f x \<partial>(coPiM I Mi)) = (\<Sum>\<^sub>\<infinity>i\<in>I. (\<integral>\<^sup>+x. f (i, x) \<partial>Mi i))"
    by(simp add: nn_integral_coPiM)
  also have "... = (\<Sum>\<^sub>\<infinity>i\<in>from_n ` UNIV. (\<integral>\<^sup>+x. f (i, x) \<partial>Mi i))"
    by(rule arg_cong[where f="infsum _"]) (metis assms(1) bij_betw_def)
  also have "... = (\<Sum>\<^sub>\<infinity>n\<in>UNIV. (\<integral>\<^sup>+x. f (from_n n, x) \<partial>(Mi (from_n n))))"
    by(rule infsum_reindex[simplified comp_def]) (use assms(1) bij_betw_imp_inj_on in blast)
  also have "... = ?rhs"
    by(auto intro!: infsum_eq_suminf nonneg_summable_on_complete)
  finally show ?thesis .
qed
lemmas nn_integral_coPiM_countable_infinite' = nn_integral_coPiM_countable_infinite[OF bij_betw_from_nat_into]
lemmas nn_integral_coPiM_nat = nn_integral_coPiM_countable_infinite[OF bij_id,simplified]

lemma 
  fixes f :: "_ \<Rightarrow> 'b::{banach, second_countable_topology}"
  assumes "bij_betw from_n (UNIV :: nat set) I" "integrable (coPiM I Mi) f"
  shows integrable_coPiM_countable_infinite_dest_sum:"(\<Sum>n. (\<integral>\<^sup>+ x. norm (f (from_n n, x)) \<partial>(Mi (from_n n)))) < \<infinity>"
    and integrable_coPiM_countable_infinite_dest': "\<And>n. integrable (Mi (from_n n)) (\<lambda>x. f (from_n n, x))"
  using ennreal_suminf_lessD assms(1,2) bij_betwE[OF assms(1)]
  by(auto simp: integrable_iff_bounded nn_integral_coPiM_countable_infinite)

lemmas integrable_coPiM_countable_infinite_dest_sum' = integrable_coPiM_countable_infinite_dest_sum[OF bij_betw_from_nat_into]
lemmas integrable_coPiM_countable_infinite_dest'' = integrable_coPiM_countable_infinite_dest'[OF bij_betw_from_nat_into]
lemmas integrable_coPiM_nat_dest_sum = integrable_coPiM_countable_infinite_dest_sum[OF bij_id,simplified id_apply]
lemmas integrable_coPiM_nat_dest = integrable_coPiM_countable_infinite_dest'[OF bij_id,simplified id_apply]

lemma 
  fixes f :: "_ \<Rightarrow> 'b::{banach, second_countable_topology}"
  assumes "bij_betw from_n (UNIV :: nat set) I" "integrable (coPiM I Mi) f"
  shows integrable_coPiM_countable_infinite_summable_norm: "summable (\<lambda>n. (\<integral>x. norm (f (from_n n, x)) \<partial>(Mi (from_n n))))"
    and integrable_coPiM_countable_infinite_summable_norm': "summable (\<lambda>n. norm (\<integral>x. f (from_n n, x) \<partial>(Mi (from_n n))))"
    and integrable_coPiM_countable_infinite_summable: "summable (\<lambda>n. (\<integral>x. f (from_n n, x) \<partial>(Mi (from_n n))))"
proof -
  show *:"summable (\<lambda>n. (\<integral>x. norm (f (from_n n, x)) \<partial>(Mi (from_n n))))"
    using integrable_coPiM_countable_infinite_dest_sum[OF assms]
      nn_integral_eq_integral[OF integrable_norm[OF integrable_coPiM_countable_infinite_dest'[OF assms]]]
    by (auto intro!: summable_suminf_not_top)
  show "summable (\<lambda>n. norm (\<integral>x. f (from_n n, x) \<partial>(Mi (from_n n))))"
    by(rule summable_comparison_test_ev[OF _ *]) auto
  thus "summable (\<lambda>n. (\<integral>x. f (from_n n, x) \<partial>(Mi (from_n n))))"
    using summable_norm_cancel by force
qed

lemmas integrable_coPiM_countable_infinite_summable_norm''
  = integrable_coPiM_countable_infinite_summable_norm[OF bij_betw_from_nat_into]
lemmas integrable_coPiM_countable_infinite_summable_norm'''
  = integrable_coPiM_countable_infinite_summable_norm'[OF bij_betw_from_nat_into]
lemmas integrable_coPiM_countable_infinite_summable'
  = integrable_coPiM_countable_infinite_summable[OF bij_betw_from_nat_into]
lemmas integrable_coPiM_nat_summable_norm
  = integrable_coPiM_countable_infinite_summable_norm[OF bij_id,simplified id_apply]
lemmas integrable_coPiM_nat_summable_norm'
  = integrable_coPiM_countable_infinite_summable_norm'[OF bij_id,simplified id_apply]
lemmas integrable_coPiM_nat_summable
  = integrable_coPiM_countable_infinite_summable[OF bij_id,simplified id_apply]

lemma
  fixes f :: "_ \<Rightarrow> 'b::{banach, second_countable_topology}"
  assumes "countable I" "infinite I" "integrable (coPiM I Mi) f"
  shows integrable_coPiM_countable_infinite_dest:"\<And>i. i \<in> I \<Longrightarrow> integrable (Mi i) (\<lambda>x. f (i, x))"
  using integrable_coPiM_countable_infinite_dest'[OF bij_betw_from_nat_into[OF assms(1,2)] assms(3)]
  by (meson assms(1) countable_all)

lemma integrable_coPiM_countable_infiniteI:
  fixes f :: "_ \<Rightarrow> 'b::{banach, second_countable_topology}"
  assumes "bij_betw from_n (UNIV :: nat set) I" "\<And>i. i \<in> I \<Longrightarrow> (\<lambda>x. f (i,x)) \<in> borel_measurable (Mi i)"
    and "(\<Sum>n. (\<integral>\<^sup>+ x. norm (f (from_n n, x)) \<partial>(Mi (from_n n)))) < \<infinity>"
  shows "integrable (coPiM I Mi) f"
  using nn_integral_coPiM_countable_infinite[OF assms(1),of _ Mi] assms(2,3)
  by(auto simp: measurable_copair_iff' integrable_iff_bounded)

lemmas integrable_coPiM_countable_infiniteI' = integrable_coPiM_countable_infiniteI[OF bij_betw_from_nat_into]
lemmas integrable_coPiM_natI = integrable_coPiM_countable_infiniteI[OF bij_id, simplified id_apply]

lemma integral_coPiM_countable_infinite:
  fixes f :: "_ \<Rightarrow> 'b::{banach, second_countable_topology}"
  assumes "bij_betw from_n (UNIV :: nat set) I" "integrable (coPiM I Mi) f"
  shows "(\<integral>x. f x \<partial>(coPiM I Mi)) = (\<Sum>n. (\<integral>x. f (from_n n, x) \<partial>(Mi (from_n n))))" (is "?lhs = ?rhs")
proof -
  have "?lhs = (\<Sum>\<^sub>\<infinity>i\<in>I. (\<integral>x. f (i, x) \<partial>Mi i))"
    by(simp add: integral_coPiM assms)
  also have "... = (\<Sum>\<^sub>\<infinity>i\<in>from_n ` UNIV. (\<integral>x. f (i, x) \<partial>Mi i))"
    by(rule arg_cong[where f="infsum _"]) (metis assms(1) bij_betw_def)
  also have "... = (\<Sum>\<^sub>\<infinity>n\<in>UNIV. (\<integral>x. f (from_n n, x) \<partial>(Mi (from_n n))))"
    by(rule infsum_reindex[simplified comp_def]) (use assms(1) bij_betw_imp_inj_on in blast)
  also have "... = ?rhs"
    by(auto intro!: infsum_eq_suminf norm_summable_imp_summable_on integrable_coPiM_countable_infinite_summable_norm' assms)
  finally show ?thesis .
qed

lemmas integral_coPiM_countable_infinite' = integral_coPiM_countable_infinite[OF bij_betw_from_nat_into]
lemmas integral_coPiM_nat = integral_coPiM_countable_infinite[OF bij_id,simplified id_apply]

subsection \<open> Finiteness \<close>
lemma finite_measure_coPiM:
  assumes "finite I" "\<And>i. i \<in> I \<Longrightarrow> finite_measure (Mi i)"
  shows "finite_measure (coPiM I Mi)"
  by(rule finite_measureI) (auto simp: emeasure_coPiM_finite finite_measure.emeasure_finite assms)

subsection \<open> $\sigma$-Finiteness \<close>
lemma sigma_finite_measure_coPiM:
  assumes "countable I" "\<And>i. i \<in> I \<Longrightarrow> sigma_finite_measure (Mi i)"
  shows "sigma_finite_measure (coPiM I Mi)"
proof
  have "\<exists>A. range A \<subseteq> sets (Mi i) \<and> (\<Union>n. A n) = space (Mi i) \<and> (\<forall>n::nat. emeasure (Mi i) (A n) \<noteq> \<infinity>)"
       if "i \<in> I" for i
    using sigma_finite_measure.sigma_finite[OF assms(2)[OF that]] by metis
  hence "\<exists>A. \<forall>i\<in>I. range (A i) \<subseteq> sets (Mi i) \<and> (\<Union>n. A i n) = space (Mi i) \<and> (\<forall>n::nat. emeasure (Mi i) (A i n) \<noteq> \<infinity>)"
    by metis
  then obtain Ai
    where Ai[measurable]: "\<And>i n. i \<in> I \<Longrightarrow> Ai i n \<in> sets (Mi i)"
      "\<And>i. i \<in> I \<Longrightarrow> (\<Union>n::nat. (Ai i n)) = space (Mi i)"
      "\<And>i n. i \<in> I \<Longrightarrow> emeasure (Mi i) (Ai i n) \<noteq> \<infinity>"
    by (metis UNIV_I sets_range) 
  show "\<exists>A. countable A \<and> A \<subseteq> sets (coPiM I Mi) \<and> \<Union> A = space (coPiM I Mi) \<and> (\<forall>a\<in>A. emeasure (coPiM I Mi) a \<noteq> \<infinity>)"
  proof(intro exI[where x="\<Union>n. (\<Union>i \<in> I. {{i} \<times> Ai i n})"] conjI ballI)
    show "countable (\<Union>n. (\<Union>i \<in> I. {{i} \<times> Ai i n}))"
      using assms(1) by auto
  next
    show "(\<Union>n. \<Union>i\<in>I. {{i} \<times> Ai i n}) \<subseteq> sets (coPiM I Mi)"
      by auto
  next
    show "\<Union> (\<Union>n. \<Union>i\<in>I. {{i} \<times> Ai i n}) = space (coPiM I Mi)"
      using sets.sets_into_space[OF Ai(1)] Ai(2) by(fastforce simp: space_coPiM)
  next
    fix a
    assume "a \<in> (\<Union>n. \<Union>i\<in>I. {{i} \<times> Ai i n})"
    then obtain n i where a: "i \<in> I" "a = {i} \<times> Ai i n"
      by blast
    show "emeasure (coPiM I Mi) a \<noteq> \<infinity>"
      using a(1) Ai(3) assms by(auto simp: a(2) emeasure_coPiM_coproj)
  qed
qed

end