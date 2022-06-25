subsection "Factorization"

theory Finite_Fields_Factorization_Ext
  imports Finite_Fields_Preliminary_Results
begin

text \<open>This section contains additional results building on top of the development in
@{theory "HOL-Algebra.Divisibility"} about factorization in a @{locale "factorial_monoid"}.\<close>

definition factor_mset where "factor_mset G x = 
  (THE f. (\<exists> as. f = fmset G as \<and> wfactors G as x \<and> set as \<subseteq> carrier G))"

text \<open>In @{theory "HOL-Algebra.Divisibility"} it is already verified that the multiset representing
the factorization of an element of a factorial monoid into irreducible factors is well-defined.
With these results it is then possible to define @{term "factor_mset"} and show its properties,
without referring to a factorization in list form first.\<close>

definition multiplicity where
  "multiplicity G d g = Max {(n::nat). (d [^]\<^bsub>G\<^esub> n) divides\<^bsub>G\<^esub> g}"

definition canonical_irreducibles where 
  "canonical_irreducibles G A = (
    A \<subseteq> {a. a \<in> carrier G \<and> irreducible G a} \<and>
    (\<forall>x y. x \<in> A \<longrightarrow> y \<in> A \<longrightarrow> x \<sim>\<^bsub>G\<^esub> y \<longrightarrow> x = y) \<and>
    (\<forall>x \<in> carrier G. irreducible G x \<longrightarrow> (\<exists>y \<in> A. x \<sim>\<^bsub>G\<^esub> y)))"

text \<open>A set of irreducible elements that contains exactly one element from each equivalence class
of an irreducible element formed by association, is called a set of 
@{term "canonical_irreducibles"}. An example is the set of monic irreducible polynomials as
representatives of all irreducible polynomials.\<close>

context factorial_monoid
begin

lemma assoc_as_fmset_eq:
  assumes "wfactors G as a"
    and "wfactors G bs b"
    and "a \<in> carrier G"
    and "b \<in> carrier G"
    and "set as \<subseteq> carrier G"
    and "set bs \<subseteq> carrier G"
  shows "a \<sim> b \<longleftrightarrow> (fmset G as = fmset G bs)"
proof -
  have "a \<sim> b \<longleftrightarrow> (a divides b \<and> b divides a)"
    by (simp add:associated_def)
  also have "... \<longleftrightarrow> 
    (fmset G as \<subseteq># fmset G bs \<and> fmset G bs \<subseteq># fmset G as)"
    using divides_as_fmsubset assms by blast
  also have "... \<longleftrightarrow> (fmset G as = fmset G bs)" by auto
  finally show ?thesis by simp
qed

lemma factor_mset_aux_1:
  assumes "a \<in> carrier G" "set as \<subseteq> carrier G" "wfactors G as a"
  shows "factor_mset G a = fmset G as"
proof -
  define H where "H = {as. wfactors G as a \<and> set as \<subseteq> carrier G}"
  have b:"as \<in> H"
    using H_def assms by simp

  have c: "x \<in> H \<Longrightarrow> y \<in> H \<Longrightarrow> fmset G x = fmset G y" for x y
    unfolding H_def using assoc_as_fmset_eq 
    using associated_refl assms by blast 

  have "factor_mset G a = (THE f. \<exists>as \<in> H. f= fmset G as)"
    by (simp add:factor_mset_def H_def, metis) 

  also have "... = fmset G as"
    using b c
    by (intro the1_equality) blast+
  finally have "factor_mset G a = fmset G as" by simp

  thus ?thesis
    using b unfolding H_def by auto
qed

lemma factor_mset_aux:
  assumes "a \<in> carrier G"
  shows "\<exists>as. factor_mset G a = fmset G as \<and> wfactors G as a \<and> 
    set as \<subseteq> carrier G"
proof -
  obtain as where as_def: "wfactors G as a" "set as \<subseteq> carrier G"
    using wfactors_exist assms by blast
  thus ?thesis using factor_mset_aux_1 assms by blast
qed

lemma factor_mset_set:
  assumes "a \<in> carrier G"
  assumes "x \<in># factor_mset G a" 
  obtains y where 
    "y \<in> carrier G" 
    "irreducible G y" 
    "assocs G y = x" 
proof -
  obtain as where as_def: 
    "factor_mset G a = fmset G as" 
    "wfactors G as a" "set as \<subseteq> carrier G"
    using factor_mset_aux assms by blast
  hence "x \<in># fmset G as"
    using assms by simp
  hence "x \<in> assocs G ` set as"
    using assms as_def by (simp add:fmset_def)
  hence "\<exists>y. y \<in> set as \<and> x = assocs G y"
    by auto
  moreover have "y \<in> carrier G \<and> irreducible G y" 
    if "y \<in> set as" for y
    using as_def that wfactors_def
    by (simp add: wfactors_def) auto
  ultimately show ?thesis
    using that by blast
qed

lemma factor_mset_mult:
  assumes "a \<in> carrier G" "b \<in> carrier G"
  shows "factor_mset G (a \<otimes> b) = factor_mset G a + factor_mset G b"
proof -
  obtain as where as_def: 
    "factor_mset G a = fmset G as" 
    "wfactors G as a" "set as \<subseteq> carrier G"
    using factor_mset_aux assms by blast
  obtain bs where bs_def: 
    "factor_mset G b = fmset G bs" 
    "wfactors G bs b" "set bs \<subseteq> carrier G"
    using factor_mset_aux assms(2) by blast
  have "a \<otimes> b \<in> carrier G" using assms by auto
  then obtain cs where cs_def:
    "factor_mset G (a \<otimes> b) = fmset G cs" 
    "wfactors G cs (a \<otimes> b)" 
    "set cs \<subseteq> carrier G"
    using factor_mset_aux assms by blast
  have "fmset G cs = fmset G as + fmset G bs"
    using as_def bs_def cs_def assms 
    by (intro  mult_wfactors_fmset[where a="a" and b="b"]) auto
  thus ?thesis
    using as_def bs_def cs_def by auto
qed

lemma factor_mset_unit: "factor_mset G \<one> = {#}"
proof -
  have "factor_mset G \<one> = factor_mset G (\<one> \<otimes> \<one>)"
    by simp
  also have "... = factor_mset G \<one> + factor_mset G \<one>"
    by (intro factor_mset_mult, auto)
  finally show "factor_mset G \<one> = {#}"
    by simp
qed

lemma factor_mset_irred: 
  assumes "x \<in> carrier G" "irreducible G x"
  shows "factor_mset G x = image_mset (assocs G) {#x#}"
proof -
  have "wfactors G [x] x"
    using assms by (simp add:wfactors_def)
  hence "factor_mset G x = fmset G [x]"
    using factor_mset_aux_1 assms by simp
  also have "... = image_mset (assocs G) {#x#}"
    by (simp add:fmset_def)
  finally show ?thesis by simp
qed

lemma factor_mset_divides:
  assumes "a \<in> carrier G" "b \<in> carrier G"
  shows "a divides b \<longleftrightarrow> factor_mset G a \<subseteq># factor_mset G b"
proof -
  obtain as where as_def: 
    "factor_mset G a = fmset G as" 
    "wfactors G as a" "set as \<subseteq> carrier G"
    using factor_mset_aux assms by blast
  obtain bs where bs_def: 
    "factor_mset G b = fmset G bs" 
    "wfactors G bs b" "set bs \<subseteq> carrier G"
    using factor_mset_aux assms(2) by blast
  hence "a divides b \<longleftrightarrow> fmset G as \<subseteq># fmset G bs"
    using as_def bs_def assms
    by (intro divides_as_fmsubset) auto
  also have "... \<longleftrightarrow> factor_mset G a \<subseteq># factor_mset G b"
    using as_def bs_def by simp
  finally show ?thesis by simp
qed

lemma factor_mset_sim:
  assumes "a \<in> carrier G" "b \<in> carrier G"
  shows "a \<sim> b \<longleftrightarrow> factor_mset G a = factor_mset G b"
  using factor_mset_divides assms
  by (simp add:associated_def) auto

lemma factor_mset_prod:
  assumes "finite A"
  assumes "f ` A \<subseteq> carrier G" 
  shows "factor_mset G (\<Otimes>a \<in> A. f a) = 
    (\<Sum>a \<in> A. factor_mset G (f a))"
  using assms
proof (induction A rule:finite_induct)
  case empty
  then show ?case by (simp add:factor_mset_unit)
next
  case (insert x F)
  have "factor_mset G (finprod G f (insert x F)) = 
    factor_mset G (f x \<otimes> finprod G f F)"
    using insert by (subst finprod_insert) auto
  also have "... = factor_mset G (f x) + factor_mset G (finprod G f F)"
    using insert by (intro factor_mset_mult finprod_closed) auto
  also have 
    "... = factor_mset G (f x) + (\<Sum>a \<in> F. factor_mset G (f a))"
    using insert by simp
  also have "... = (\<Sum>a\<in>insert x F. factor_mset G (f a))"
    using insert by simp
  finally show ?case by simp
qed

lemma factor_mset_pow:
  assumes "a \<in> carrier G"
  shows "factor_mset G (a [^] n) = repeat_mset n (factor_mset G a)"
proof (induction n)
  case 0
  then show ?case by (simp add:factor_mset_unit)
next
  case (Suc n)
  have "factor_mset G (a [^] Suc n) = factor_mset G (a [^] n \<otimes> a)"
    by simp
  also have "... = factor_mset G (a [^] n) + factor_mset G a"
    using assms by (intro factor_mset_mult) auto
  also have "... = repeat_mset n (factor_mset G a) + factor_mset G a"
    using Suc by simp
  also have "... = repeat_mset (Suc n) (factor_mset G a)"
    by simp
  finally show ?case by simp
qed

lemma image_mset_sum:
  assumes "finite F"
  shows 
    "image_mset h (\<Sum>x \<in> F. f x) = (\<Sum>x \<in> F. image_mset h (f x))"
  using assms
  by (induction F rule:finite_induct, simp, simp)

lemma decomp_mset: 
  "(\<Sum>x\<in>set_mset R. replicate_mset (count R x) x) = R"
  by (rule multiset_eqI, simp add:count_sum count_eq_zero_iff)

lemma factor_mset_count:
  assumes "a \<in> carrier G" "d \<in> carrier G" "irreducible G d"
  shows "count (factor_mset G a) (assocs G d) = multiplicity G d a"
proof -
  have a: 
    "count (factor_mset G a) (assocs G d) \<ge> m \<longleftrightarrow> d [^] m divides a"
    (is "?lhs \<longleftrightarrow> ?rhs") for m
  proof -
    have "?lhs \<longleftrightarrow> replicate_mset m (assocs G d) \<subseteq># factor_mset G a"
      by (simp add:count_le_replicate_mset_subset_eq)
    also have "... \<longleftrightarrow> factor_mset G (d [^] m) \<subseteq># factor_mset G a"
      using assms(2,3) by (simp add:factor_mset_pow factor_mset_irred)
    also have "... \<longleftrightarrow> ?rhs"
      using assms(1,2) by (subst factor_mset_divides) auto
    finally show ?thesis by simp
  qed

  define M where "M = {(m::nat). d [^] m divides a}"

  have M_alt: "M = {m. m \<le> count (factor_mset G a) (assocs G d)}"
    using a by (simp add:M_def)

  hence "Max M = count (factor_mset G a) (assocs G d)"
    by (intro Max_eqI, auto)
  thus ?thesis
    unfolding multiplicity_def M_def by auto
qed

lemma multiplicity_ge_iff:
  assumes "d \<in> carrier G" "irreducible G d" "a \<in> carrier G"
  shows "multiplicity G d a \<ge> k \<longleftrightarrow> d [^] k divides a" 
    (is "?lhs \<longleftrightarrow> ?rhs")
proof -
  have "?lhs \<longleftrightarrow> count (factor_mset G a) (assocs G d) \<ge> k"
    using factor_mset_count[OF assms(3,1,2)] by simp
  also have "... \<longleftrightarrow> replicate_mset k (assocs G d) \<subseteq># factor_mset G a"
    by (subst count_le_replicate_mset_subset_eq, simp) 
  also have "... \<longleftrightarrow>
    repeat_mset k (factor_mset G d) \<subseteq># factor_mset G a" 
    by (subst factor_mset_irred[OF assms(1,2)], simp)
  also have "... \<longleftrightarrow> factor_mset G (d [^]\<^bsub>G\<^esub> k) \<subseteq># factor_mset G a" 
    by (subst factor_mset_pow[OF assms(1)], simp)
  also have "... \<longleftrightarrow> (d [^] k) divides\<^bsub>G\<^esub> a"
    using assms(1) factor_mset_divides[OF _ assms(3)] by simp
  finally show ?thesis by simp
qed

lemma multiplicity_gt_0_iff:
  assumes "d \<in> carrier G" "irreducible G d" "a \<in> carrier G"
  shows "multiplicity G d a > 0 \<longleftrightarrow> d divides a"
  using multiplicity_ge_iff[OF assms(1,2,3), where k="1"] assms
  by auto

lemma factor_mset_count_2:
  assumes "a \<in> carrier G" 
  assumes "\<And>z. z \<in> carrier G \<Longrightarrow> irreducible G z \<Longrightarrow> y \<noteq> assocs G z"
  shows "count (factor_mset G a) y = 0"
  using factor_mset_set [OF assms(1)] assms(2) by (metis count_inI)

lemma factor_mset_choose:
  assumes "a \<in> carrier G" "set_mset R \<subseteq> carrier G"
  assumes "image_mset (assocs G) R = factor_mset G a" 
  shows "a \<sim> (\<Otimes>x\<in>set_mset R. x [^] count R x)" (is "a \<sim> ?rhs")
proof -
  have b:"irreducible G x" if a:"x \<in># R" for x
  proof -
    have x_carr: "x \<in> carrier G" 
      using a assms(2) by auto
    have "assocs G x \<in> assocs G ` set_mset R"
      using a by simp
    hence "assocs G x \<in># factor_mset G a"
      using assms(3) a in_image_mset by metis
    then obtain z where z_def: 
      "z \<in> carrier G" "irreducible G z" "assocs G x = assocs G z"
      using factor_mset_set assms(1) by metis
    have "z \<sim> x" using z_def(1,3) assocs_eqD x_carr by simp 
    thus ?thesis using z_def(1,2) x_carr irreducible_cong by simp
  qed

  have "factor_mset G ?rhs = 
    (\<Sum>x\<in>set_mset R. factor_mset G (x [^] count R x))"
    using assms(2) by (subst factor_mset_prod, auto) 
  also have "... = 
    (\<Sum>x\<in>set_mset R. repeat_mset (count R x) (factor_mset G x))"
    using assms(2) by (intro sum.cong, auto simp add:factor_mset_pow)
  also have "... = (\<Sum>x\<in>set_mset R. 
    repeat_mset (count R x) (image_mset (assocs G) {#x#}))"
    using assms(2) b by (intro sum.cong, auto simp add:factor_mset_irred)
  also have "... = (\<Sum>x\<in>set_mset R. 
    image_mset (assocs G) (replicate_mset (count R x) x))"
    by simp
  also have "... = image_mset (assocs G) 
    (\<Sum>x\<in>set_mset R. (replicate_mset (count R x) x))"
    by (simp add: image_mset_sum)
  also have "... = image_mset (assocs G) R"
    by (simp add:decomp_mset)
  also have "... = factor_mset G a"
    using assms by simp
  finally have "factor_mset G ?rhs = factor_mset G a" by simp
  moreover have "(\<Otimes>x\<in>set_mset R. x [^] count R x) \<in> carrier G"
    using assms(2) by (intro finprod_closed, auto)
  ultimately show ?thesis 
    using assms(1) by (subst factor_mset_sim) auto
qed

lemma divides_iff_mult_mono:
  assumes "a \<in> carrier G" "b \<in> carrier G" 
  assumes "canonical_irreducibles G R"
  assumes "\<And>d. d \<in> R \<Longrightarrow> multiplicity G d a \<le> multiplicity G d b"
  shows "a divides b"
proof -
  have "count (factor_mset G a) d \<le> count (factor_mset G b) d" for d
  proof (cases "\<exists>y \<in> carrier G. irreducible G y \<and> d = assocs G y")
    case True
    then obtain y where y_def: 
      "irreducible G y" "y \<in> carrier G" "d = assocs G y"
      by blast
    then obtain z where z_def: "z \<in> R" "y \<sim> z"
      using assms(3) unfolding canonical_irreducibles_def by metis
    have z_more: "irreducible G z" "z \<in> carrier G"
      using z_def(1) assms(3)
      unfolding canonical_irreducibles_def by auto
    have "y \<in> assocs G z" using z_def(2) z_more(2) y_def(2) 
      by (simp add: closure_ofI2)
    hence d_def: "d = assocs G z"
      using y_def(2,3) z_more(2) assocs_repr_independence
      by blast
    have "count (factor_mset G a) d = multiplicity G z a"
      unfolding d_def
      by (intro factor_mset_count[OF assms(1) z_more(2,1)])
    also have "... \<le> multiplicity G z b"
      using assms(4) z_def(1) by simp
    also have "... = count (factor_mset G b) d"
      unfolding d_def
      by (intro factor_mset_count[symmetric, OF assms(2) z_more(2,1)])
    finally show ?thesis by simp 
  next
    case False
    have "count (factor_mset G a) d = 0" using False
      by (intro factor_mset_count_2[OF assms(1)], simp)
    moreover have "count (factor_mset G b) d = 0" using False
      by (intro factor_mset_count_2[OF assms(2)], simp)
    ultimately show ?thesis by simp
  qed

  hence "factor_mset G a \<subseteq># factor_mset G b" 
    unfolding subseteq_mset_def by simp
  thus ?thesis using factor_mset_divides assms(1,2) by simp
qed

lemma count_image_mset_inj:
  assumes "inj_on f R" "x \<in> R" "set_mset A \<subseteq> R"
  shows "count (image_mset f A) (f x) = count A x"
proof (cases "x \<in># A")
  case True
  hence "(f y = f x \<and> y \<in># A) = (y = x)" for y 
    by (meson assms(1) assms(3) inj_onD subsetD)
  hence "(f -` {f x} \<inter> set_mset A) = {x}" 
    by (simp add:set_eq_iff)
  thus ?thesis
    by (subst count_image_mset, simp)
next
  case False
  hence "x \<notin> set_mset A" by simp
  hence "f x \<notin> f ` set_mset A" using assms
    by (simp add: inj_on_image_mem_iff)
  hence "count (image_mset f A) (f x) = 0" 
    by (simp add:count_eq_zero_iff)
  thus ?thesis by (metis count_inI False)
qed

text \<open>Factorization of an element from a @{locale "factorial_monoid"} using a selection of representatives 
from each equivalence class formed by @{term "(\<sim>)"}.\<close>

lemma split_factors:
  assumes "canonical_irreducibles G R"
  assumes "a \<in> carrier G"
  shows 
    "finite {d. d \<in> R \<and> multiplicity G d a > 0}"
    "a \<sim> (\<Otimes>d\<in>{d. d \<in> R \<and> multiplicity G d a > 0}. 
          d [^] multiplicity G d a)" (is "a \<sim> ?rhs")
proof -
  have r_1: "R \<subseteq> {x. x \<in> carrier G \<and> irreducible G x}" 
    using assms(1) unfolding canonical_irreducibles_def by simp
  have r_2: "\<And>x y. x \<in> R \<Longrightarrow> y \<in> R \<Longrightarrow> x \<sim> y \<Longrightarrow> x = y" 
    using assms(1) unfolding canonical_irreducibles_def by simp
  
  have assocs_inj: "inj_on (assocs G) R"
    using r_1 r_2 assocs_eqD by (intro inj_onI, blast) 
  
  define R' where
    "R' = (\<Sum>d\<in> {d. d \<in> R \<and> multiplicity G d a > 0}.
    replicate_mset (multiplicity G d a) d)"

  have "count (factor_mset G a) (assocs G x) > 0" 
    if "x \<in> R" "0 < multiplicity G x a" for x
    using assms r_1 r_2 that
    by (subst factor_mset_count[OF assms(2)]) auto
  hence "assocs G ` {d \<in> R. 0 < multiplicity G d a} 
    \<subseteq> set_mset (factor_mset G a)"
    by (intro image_subsetI, simp)
  hence a:"finite (assocs G ` {d \<in> R. 0 < multiplicity G d a})"
    using finite_subset by auto

  show "finite {d \<in> R. 0 < multiplicity G d a}" 
    using assocs_inj inj_on_subset[OF assocs_inj]
    by (intro finite_imageD[OF a], simp)

  hence count_R': 
    "count R' d = (if d \<in> R then multiplicity G d a else 0)"
    for d
    by (auto simp add:R'_def count_sum) 

  have set_R': "set_mset R' = {d \<in> R. 0 < multiplicity G d a}"
    unfolding set_mset_def using count_R' by auto

  have "count (image_mset (assocs G) R') x = 
    count (factor_mset G a) x" for x
  proof (cases "\<exists>x'. x' \<in> R \<and> x = assocs G x'")
    case True
    then obtain x' where x'_def: "x' \<in> R" "x = assocs G x'"
      by blast
    have "count (image_mset (assocs G) R') x = count R' x'"
      using assocs_inj inj_on_subset[OF assocs_inj] x'_def
      by (subst x'_def(2), subst count_image_mset_inj[OF assocs_inj])
        (auto simp:set_R') 
    also have "... = multiplicity G x' a"
      using count_R' x'_def by simp
    also have "... = count (factor_mset G a) (assocs G x')"
      using x'_def(1) r_1
      by (subst factor_mset_count[OF assms(2)]) auto
    also have "... = count (factor_mset G a) x"
      using x'_def(2) by simp
    finally show ?thesis by simp
  next
    case False
    have a:"x \<noteq> assocs G z" 
      if a1: "z \<in> carrier G" and a2: "irreducible G z" for z
    proof -
      obtain v where v_def: "v \<in> R" "z \<sim> v"
        using a1 a2 assms(1)
        unfolding canonical_irreducibles_def by auto
      hence "z \<in> assocs G v"
        using a1 r_1 v_def(1) by (simp add: closure_ofI2)
      hence "assocs G z = assocs G v"
        using a1 r_1 v_def(1)  assocs_repr_independence
        by auto
      moreover have "x \<noteq> assocs G v"
        using False v_def(1) by simp
      ultimately show ?thesis by simp
    qed

    have "count (image_mset (assocs G) R') x = 0"
      using False count_R' by (simp add: count_image_mset) auto
    also have "... = count (factor_mset G a) x"
      using a
      by (intro factor_mset_count_2[OF assms(2), symmetric]) auto 
    finally show ?thesis by simp
  qed

  hence "image_mset (assocs G) R' = factor_mset G a"
    by (rule multiset_eqI)

  moreover have "set_mset R' \<subseteq> carrier G" 
    using r_1 by (auto simp add:set_R') 
  ultimately have "a \<sim> (\<Otimes>x\<in>set_mset R'. x [^] count R' x)"
    using assms(2) by (intro factor_mset_choose, auto)
  also have "... = ?rhs"
    using set_R' assms r_1 r_2
    by (intro finprod_cong', auto simp add:count_R')
  finally show "a \<sim> ?rhs" by simp
qed

end

end