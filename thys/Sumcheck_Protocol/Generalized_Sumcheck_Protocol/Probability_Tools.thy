(*******************************************************************************

  Project: Sumcheck Protocol

  Authors: Azucena Garvia Bosshard <zucegb@gmail.com>
           Christoph Sprenger, ETH Zurich <sprenger@inf.ethz.ch>
           Jonathan Bootle, IBM Research Europe <jbt@zurich.ibm.com>

*******************************************************************************)

section \<open>Auxiliary Lemmas Related to Probability Theory\<close>

theory Probability_Tools
  imports "HOL-Probability.Probability"
begin

subsection \<open>Tuples\<close>

definition tuples :: \<open>'a set \<Rightarrow> nat \<Rightarrow> 'a list set\<close> where
  \<open>tuples S n = {xs. set xs \<subseteq> S \<and> length xs = n}\<close>

lemma tuplesI: \<open>\<lbrakk> set xs \<subseteq> S; length xs = n \<rbrakk> \<Longrightarrow> xs \<in> tuples S n\<close> 
  by (simp add: tuples_def)

lemma tuplesE [elim]: \<open>\<lbrakk> xs \<in> tuples S n; \<lbrakk> set xs \<subseteq> S; length xs = n \<rbrakk> \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P\<close> 
  by (simp add: tuples_def)

lemma tuples_Zero: \<open>tuples S 0 = {[]}\<close>
  by (auto simp add: tuples_def)

lemma tuples_Suc: \<open>tuples S (Suc n) = (\<lambda>(x, xs). x # xs) ` (S \<times> tuples S n)\<close>
  by (fastforce simp add: tuples_def image_def Suc_length_conv dest: sym)

lemma tuples_non_empty [simp]: \<open>S \<noteq> {} \<Longrightarrow> tuples S n \<noteq> {}\<close>
  by (induction n) (auto simp add: tuples_Zero tuples_Suc)

lemma tuples_finite [simp]: \<open>\<lbrakk> finite (S::'a set); S \<noteq> {} \<rbrakk> \<Longrightarrow> finite (tuples S n :: 'a list set)\<close>
  by (auto simp add: tuples_def dest: finite_lists_length_eq)


subsection \<open>Congruence and monotonicity\<close>

lemma prob_cong:                        \<comment> \<open>adapted from Joshua\<close>
  assumes \<open>\<And>x. x \<in> set_pmf M \<Longrightarrow> x \<in> A \<longleftrightarrow> x \<in> B\<close> 
  shows \<open>measure_pmf.prob M A = measure_pmf.prob M B\<close>
  using assms
  by (simp add: measure_pmf.finite_measure_eq_AE AE_measure_pmf_iff)

lemma prob_mono: 
  assumes \<open>\<And>x. x \<in> set_pmf M \<Longrightarrow> x \<in> A \<Longrightarrow> x \<in> B\<close> 
  shows \<open>measure_pmf.prob M A \<le> measure_pmf.prob M B\<close>
  using assms
  by (simp add: measure_pmf.finite_measure_mono_AE AE_measure_pmf_iff)


subsection \<open>Some simple derived lemmas\<close>

lemma prob_empty: 
  assumes \<open>A = {}\<close>
  shows \<open>measure_pmf.prob M A = 0\<close>
  using assms
  by (simp)   \<comment> \<open>uses @{thm [source] "measure_empty"}: @{thm "measure_empty"}\<close>

lemma prob_pmf_of_set_geq_1:
  assumes "finite S" and "S \<noteq> {}"
  shows "measure_pmf.prob (pmf_of_set S) A \<ge> 1 \<longleftrightarrow> S \<subseteq> A" using assms
  by (auto simp add: measure_pmf.measure_ge_1_iff measure_pmf.prob_eq_1 AE_measure_pmf_iff)


subsection \<open>Intersection and union lemmas\<close>

lemma prob_disjoint_union:
  assumes \<open>A \<inter> B = {}\<close> 
  shows \<open>measure_pmf.prob M (A \<union> B) = measure_pmf.prob M A + measure_pmf.prob M B\<close>
  using assms
  by (fact measure_pmf.finite_measure_Union[simplified])

lemma prob_finite_Union:
  assumes \<open>disjoint_family_on A I\<close> \<open>finite I\<close>
  shows \<open>measure_pmf.prob M (\<Union>i\<in>I. A i) = (\<Sum>i\<in>I. measure_pmf.prob M (A i))\<close>
  using assms
  by (intro measure_pmf.finite_measure_finite_Union) (simp_all)

lemma prob_disjoint_cases:
  assumes \<open>B \<union> C = A\<close> \<open>B \<inter> C = {}\<close>
  shows \<open>measure_pmf.prob M A = measure_pmf.prob M B + measure_pmf.prob M C\<close>
proof - 
  have \<open>measure_pmf.prob M A = measure_pmf.prob M (B \<union> C)\<close> using \<open>B \<union> C = A\<close> 
    by (auto intro: prob_cong)
  also have \<open>... = measure_pmf.prob M B + measure_pmf.prob M C\<close> using \<open>B \<inter> C = {}\<close>
    by (simp add: prob_disjoint_union)
  finally show ?thesis .
qed

lemma prob_finite_disjoint_cases:
  assumes \<open>(\<Union>i\<in>I. B i) = A\<close> \<open>disjoint_family_on B I\<close> \<open>finite I\<close>
  shows \<open>measure_pmf.prob M A = (\<Sum>i\<in>I. measure_pmf.prob M (B i))\<close>
proof - 
  have \<open>measure_pmf.prob M A = measure_pmf.prob M (\<Union>i\<in>I. B i)\<close> using assms(1)
    by (auto intro: prob_cong) 
  also have \<open>... = (\<Sum>i\<in>I. measure_pmf.prob M (B i))\<close> using assms(2,3) 
    by (intro prob_finite_Union) 
  finally show ?thesis .
qed


subsection \<open>Independent probabilities for head and tail of a tuple\<close>

lemma pmf_of_set_Times:   \<comment> \<open>by Andreas Lochbihler\<close>
  "pmf_of_set (A \<times> B) = pair_pmf (pmf_of_set A) (pmf_of_set B)"
  if "finite A" "finite B" "A \<noteq> {}" "B \<noteq> {}"   
  by(rule pmf_eqI)(auto simp add: that pmf_pair indicator_def)


lemma prob_tuples_hd_tl_indep:
  assumes \<open>S \<noteq> {}\<close> 
  shows
    \<open>measure_pmf.prob (pmf_of_set (tuples S (Suc n))) {(r::'a::finite) # rs | r rs. P r \<and> Q rs}
   = measure_pmf.prob (pmf_of_set (S::'a set)) {r. P r} * 
     measure_pmf.prob (pmf_of_set (tuples S n)) {rs. Q rs}\<close> 
    (is "?lhs = ?rhs")
proof -                  \<comment> \<open>mostly by Andreas Lochbihler\<close>
  text \<open>
    Step 1: Split the random variable @{term "pmf_of_set (tuples S (Suc n))"} into
    two independent (@{term "pair_pmf"}) random variables, one producing the head and one 
    producing the tail of the list, and then @{term Cons} the two random variables using 
    @{term "map_pmf"}.
  \<close>
  have *: "pmf_of_set (tuples S (Suc n)) 
         = map_pmf (\<lambda>(x :: 'a, xs). x # xs) (pair_pmf (pmf_of_set S) (pmf_of_set (tuples S n)))"
    unfolding tuples_Suc using \<open>S \<noteq> {}\<close> 
    by (auto simp add: map_pmf_of_set_inj[symmetric] inj_on_def pmf_of_set_Times) 
  text \<open>
    Step 2: Transform the event by move the @{term Cons} from the random variable into the event.
    This corresponds to using @{term distr} on measures.
  \<close>
  have "?lhs = measure_pmf.prob (pair_pmf (pmf_of_set S) (pmf_of_set (tuples S n))) 
                                ((\<lambda>(x :: 'a, xs). x # xs) -` {r # rs | r rs. P r \<and> Q rs})"
    unfolding * measure_map_pmf by (rule refl)

  text \<open>
    Step 3: Rewrite the event as a pair of events. Then we apply independence of the head 
    from the tail.
  \<close>
  also have "((\<lambda>(x, xs). x # xs) -` {r # rs | r rs. P r \<and> Q rs}) = {r. P r} \<times> {rs. Q rs}" by auto
  also have "measure_pmf.prob (pair_pmf (pmf_of_set S) (pmf_of_set (tuples S n))) \<dots> =
               measure_pmf.prob (pmf_of_set S) {r. P r} 
             * measure_pmf.prob (pmf_of_set (tuples S n)) {rs. Q rs}"
   by(rule measure_pmf_prob_product) simp_all

  finally show ?thesis .
qed

lemma prob_tuples_fixed_hd:
  \<open>measure_pmf.prob (pmf_of_set (tuples UNIV (Suc n))) {rs::'a list. P rs} 
   = (\<Sum>a \<in> UNIV. measure_pmf.prob (pmf_of_set (tuples UNIV n)) {rs. P (a # rs)}) / real(CARD('a::finite))\<close>
  (is "?lhs = ?rhs")
proof -
  {
    fix a
    have \<open>measure_pmf.prob (pmf_of_set (tuples UNIV (Suc n))) ({rs. P rs} \<inter> {rs. hd rs = a})
        = measure_pmf.prob (pmf_of_set (tuples UNIV (Suc n))) ({r#rs | r rs. r = a \<and> P (a#rs)})\<close>
      by (intro prob_cong) (auto simp add: tuples_Suc)
    also have \<open>... = measure_pmf.prob (pmf_of_set (UNIV::'a set)) {r. r = a} * 
                     measure_pmf.prob (pmf_of_set (tuples UNIV n)) {rs. P (a#rs)}\<close> 
      by (intro prob_tuples_hd_tl_indep) simp
    also have \<open>... = measure_pmf.prob (pmf_of_set (tuples UNIV n)) {rs. P (a#rs)} / real (CARD ('a))\<close>
      by (simp add: measure_pmf_single)
    finally 
    have \<open>measure_pmf.prob (pmf_of_set (tuples UNIV (Suc n))) ({rs. P rs} \<inter> {rs. hd rs = a}) 
        = measure_pmf.prob (pmf_of_set (tuples UNIV n)) {rs. P (a#rs)} / real (CARD ('a))\<close> .
  }
  note A1 = this

  have \<open>?lhs = (\<Sum>a \<in> UNIV. measure_pmf.prob (pmf_of_set (tuples UNIV (Suc n))) ({rs. P rs} \<inter> {rs. hd rs = a}))\<close>
    by (intro prob_finite_disjoint_cases) (auto simp add: disjoint_family_on_def)
  also have \<open>... = ?rhs\<close> using A1 
    by (simp add: sum_divide_distrib)
  finally show ?thesis .
qed


end
