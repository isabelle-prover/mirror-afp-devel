(* Author: Ujkan Sulejmani *)

section \<open>Center Selection\<close>

theory Center_Selection
  imports Complex_Main "HOL-Hoare.Hoare_Logic"
begin

text \<open>The Center Selection (or metric k-center) problem. Given a set of \textit{sites} \<open>S\<close>
in a metric space, find a subset \<open>C \<subseteq> S\<close> that minimizes the maximal distance from any \<open>s \<in> S\<close>
to some \<open>c \<in> C\<close>. This theory presents a verified 2-approximation algorithm.
It is based on Section 11.2 in the book by Kleinberg and Tardos \<^cite>\<open>"KleinbergT06"\<close>.
In contrast to the proof in the book, our proof is a standard invariant proof.\<close>

locale Center_Selection =
  fixes S :: "('a :: metric_space) set"
    and k :: nat
  assumes finite_sites: "finite S"
  and     non_empty_sites: "S \<noteq> {}"
and       non_zero_k: "k > 0"
begin

definition distance :: "('a::metric_space) set \<Rightarrow> ('a::metric_space) \<Rightarrow> real" where
"distance C s = Min (dist s ` C)"

definition radius :: "('a :: metric_space) set \<Rightarrow> real" where
"radius C = Max (distance C ` S)"

lemma distance_mono:
assumes "C\<^sub>1 \<subseteq> C\<^sub>2" and "C\<^sub>1 \<noteq> {}" and "finite C\<^sub>2"
shows "distance C\<^sub>1 s \<ge> distance C\<^sub>2 s"
by (simp add: Min.subset_imp assms distance_def image_mono)

lemma finite_distances: "finite (distance C ` S)"
  using finite_sites by simp

lemma non_empty_distances: "distance C ` S \<noteq> {}"
  using non_empty_sites by simp

lemma radius_contained: "radius C \<in> distance C ` S"
  using finite_distances non_empty_distances Max_in radius_def by simp

lemma radius_def2: "\<exists>s \<in> S. distance C s = radius C"
  using radius_contained image_iff by metis

lemma dist_lemmas_aux:
  assumes  "finite C"
      and  "C \<noteq> {}"
  shows  "finite (dist s ` C)"
    and "finite (dist s ` C) \<Longrightarrow> distance C s \<in> dist s ` C"
    and "distance C s \<in> dist s ` C \<Longrightarrow> \<exists>c \<in> C. dist s c = distance C s"
and "\<exists>c \<in> C. dist s c = distance C s \<Longrightarrow> distance C s \<ge> 0"
proof
  show "finite C" using assms(1) by simp
next
  assume "finite (dist s ` C)"
  then show "distance C s \<in> dist s ` C" using distance_def eq_Min_iff assms(2) by blast
next
  assume "distance C s \<in> dist s ` C" 
  then show "\<exists>c \<in> C. dist s c = distance C s" by auto
next
  assume "\<exists>c \<in> C. dist s c = distance C s"
  then show "distance C s \<ge> 0" by (metis zero_le_dist)
qed

lemma dist_lemmas:
  assumes "finite C"
      and "C \<noteq> {}"
  shows "finite (dist s ` C)"
    and "distance C s \<in> dist s ` C"
    and "\<exists>c \<in> C. dist s c = distance C s"
    and "distance C s \<ge> 0"
  using dist_lemmas_aux assms by auto

lemma radius_max_prop: "(\<forall>s \<in> S. distance C s \<le> r) \<Longrightarrow> (radius C \<le> r)"
  by (metis image_iff radius_contained)

lemma dist_ins:
assumes "\<forall>c\<^sub>1 \<in> C. \<forall>c\<^sub>2 \<in> C. c\<^sub>1 \<noteq> c\<^sub>2 \<longrightarrow> x < dist c\<^sub>1 c\<^sub>2"
and "distance C s > x"
and "finite C"
and "C \<noteq> {}"
shows "\<forall>c\<^sub>1 \<in> (C \<union> {s}). \<forall>c\<^sub>2 \<in> (C \<union> {s}). c\<^sub>1 \<noteq> c\<^sub>2 \<longrightarrow> x < dist c\<^sub>1 c\<^sub>2"
proof (rule+)
  fix c\<^sub>1 c\<^sub>2
  assume local_assms: "c\<^sub>1\<in>C \<union> {s}" "c\<^sub>2\<in>C \<union> {s}" "c\<^sub>1 \<noteq> c\<^sub>2"
  then have "c\<^sub>1 \<in> C  \<and> c\<^sub>2 \<in> C  \<or> c\<^sub>1 \<in>C  \<and> c\<^sub>2\<in> {s} \<or> c\<^sub>2\<in>C  \<and> c\<^sub>1 \<in> {s} \<or> c\<^sub>1 \<in> {s} \<and> c\<^sub>2\<in> {s}" by auto
  then show "x < dist c\<^sub>1 c\<^sub>2"
  proof (elim disjE)
    assume "c\<^sub>1 \<in>C  \<and> c\<^sub>2\<in>C"
    then show ?thesis using assms(1) local_assms(3) by simp
  next
    assume case_assm: "c\<^sub>1 \<in> C \<and> c\<^sub>2 \<in> {s}"
    have "x < distance C c\<^sub>2" using assms(2) case_assm by simp
    also have " ... \<le> dist c\<^sub>2 c\<^sub>1"
      using Min.coboundedI distance_def assms(3,4) dist_lemmas(1, 2) case_assm by simp
    also have " ... = dist c\<^sub>1 c\<^sub>2" using dist_commute by metis
    finally show ?thesis .
  next
    assume case_assm: "c\<^sub>2 \<in> C \<and> c\<^sub>1 \<in> {s}"
    have "x < distance C c\<^sub>1" using assms(2) case_assm by simp
    also have " ... \<le> dist c\<^sub>1 c\<^sub>2"
      using Min.coboundedI distance_def assms(3,4) dist_lemmas(1, 2) case_assm by simp
    finally show ?thesis .
  next
    assume "c\<^sub>1 \<in> {s} \<and> c\<^sub>2 \<in> {s}" 
    then have False using local_assms by simp
    then show ?thesis by simp
  qed
qed

subsection \<open>A Preliminary Algorithm and Proof\<close>

text \<open>This subsection verifies an auxiliary algorithm by Kleinberg and Tardos.
Our proof of the main algorithm does not does not rely on this auxiliary algorithm at all
but we do reuse part off its invariant proof later on.\<close>

definition inv :: "('a :: metric_space) set \<Rightarrow> ('a :: metric_space set) \<Rightarrow> real \<Rightarrow> bool" where
"inv S' C r =
  ((\<forall>s \<in> (S - S'). distance C s \<le> 2*r) \<and> S' \<subseteq> S \<and> C \<subseteq> S \<and>
   (\<forall>c \<in> C. \<forall>s \<in> S'. S' \<noteq> {} \<longrightarrow> dist c s > 2 * r) \<and> (S' = S \<or> C \<noteq> {}) \<and>
   (\<forall>c\<^sub>1 \<in> C. \<forall>c\<^sub>2 \<in> C. c\<^sub>1 \<noteq> c\<^sub>2 \<longrightarrow> dist c\<^sub>1 c\<^sub>2 > 2 * r))" 

lemma inv_init: "inv S {} r"
  unfolding inv_def non_empty_sites by simp
lemma inv_step:
  assumes "S' \<noteq> {}"
and IH: "inv S' C r"
defines[simp]: "s \<equiv> (SOME s. s \<in> S')"
shows "inv (S' - {s' . s' \<in> S' \<and> dist s s' \<le> 2*r}) (C \<union> {s}) r"
proof -
  have s_def: "s \<in> S'" using assms(1) some_in_eq by auto

  have "finite (C \<union> {s})" using IH finite_subset[OF _ finite_sites] by (simp add: inv_def)

  moreover

  have "(\<forall>s' \<in> (S - (S' - {s' . s' \<in> S' \<and> dist s s' \<le> 2*r})). distance (C \<union> {s}) s' \<le> 2*r)"
  proof 
    fix s''
    assume "s'' \<in> S - (S' - {s' . s' \<in> S' \<and> dist s s' \<le> 2*r})"
    then have "s'' \<in> S - S' \<or> s'' \<in> {s' . s' \<in> S' \<and> dist s s' \<le> 2*r}" by simp
    then show "distance (C \<union> {s}) s'' \<le> 2 * r"
    proof (elim disjE)
      assume local_assm: "s'' \<in> S - S'"
      have "S' = S \<or> C \<noteq> {}" using IH by (simp add: inv_def)
      then show ?thesis
      proof (elim disjE)
        assume "S' = S"
        then have "s'' \<in> {}" using local_assm by simp
        then show ?thesis by simp
      next
        assume C_not_empty: "C \<noteq> {}"
        have "finite C" using IH finite_subset[OF _ finite_sites] by (simp add: inv_def)
        then have "distance (C \<union> {s}) s'' \<le> distance C s''"
          using distance_mono C_not_empty by (meson Un_upper1 calculation)
        also have " ...  \<le> 2 * r" using IH local_assm inv_def by simp
        finally show ?thesis .
      qed
    next
      assume local_assm: "s'' \<in> {s' . s' \<in> S' \<and> dist s s' \<le> 2*r}"
      then have "distance (C \<union> {s}) s'' \<le> dist s'' s"
        using Min.coboundedI distance_def dist_lemmas calculation by auto
      also have " ... \<le> 2 * r" using local_assm by (smt dist_self dist_triangle2 mem_Collect_eq)
      finally show ?thesis .
    qed
  qed

  moreover

  have "S' - {s' . s' \<in> S' \<and> dist s s' \<le> 2*r} \<subseteq> S" using IH by (auto simp: inv_def)

  moreover
  {
    have "s \<in> S" using IH inv_def s_def by auto
    then have "C \<union> {s} \<subseteq> S" using IH by (simp add: inv_def)
  }
  moreover

  have "(\<forall>c\<in>C \<union> {s}. \<forall>c\<^sub>2\<in>C \<union> {s}. c \<noteq> c\<^sub>2 \<longrightarrow> 2 * r < dist c c\<^sub>2)"
  proof (rule+)
    fix c\<^sub>1 c\<^sub>2
    assume local_assms: "c\<^sub>1 \<in> C \<union> {s}" "c\<^sub>2 \<in> C \<union> {s}" "c\<^sub>1 \<noteq> c\<^sub>2"
    then have "(c\<^sub>1 \<in> C \<and> c\<^sub>2 \<in> C) \<or> (c\<^sub>1 = s \<and> c\<^sub>2 \<in> C) \<or> (c\<^sub>1 \<in> C \<and> c\<^sub>2 = s) \<or> (c\<^sub>1 = s \<and> c\<^sub>2 = s)"
      using assms by auto
    then show "2 * r < dist c\<^sub>1 c\<^sub>2"
    proof (elim disjE)
      assume "c\<^sub>1 \<in> C \<and> c\<^sub>2 \<in> C"
      then show "2 * r < dist c\<^sub>1 c\<^sub>2" using IH inv_def local_assms by simp
    next
      assume case_assm: "c\<^sub>1 = s \<and> c\<^sub>2 \<in> C"
      have "(\<forall>c \<in> C. \<forall>s\<in>S'. S' \<noteq> {} \<longrightarrow> 2 * r < dist c s)" using IH inv_def by simp
      then show ?thesis by (smt case_assm s_def assms(1) dist_self dist_triangle3 singletonD)
    next
      assume case_assm: "c\<^sub>1 \<in> C \<and> c\<^sub>2 = s"
      have "(\<forall>c \<in> C. \<forall>s\<in>S'. S' \<noteq> {} \<longrightarrow> 2 * r < dist c s)" using IH inv_def by simp
      then show ?thesis by (smt case_assm s_def assms(1) dist_self dist_triangle3 singletonD)
    next
      assume "c\<^sub>1 = s \<and> c\<^sub>2 = s"
      then have False using local_assms(3) by simp
      then show ?thesis by simp
    qed
  qed

  moreover

  have "(\<forall>c\<in>C \<union> {s}. \<forall>s'' \<in> S' - {s' \<in> S'. dist s s' \<le> 2 * r}.
           S' - {s' \<in> S'. dist s s' \<le> 2 * r} \<noteq> {} \<longrightarrow> 2 * r < dist c s'')"
    using IH inv_def by fastforce

  moreover

  have "(S' - {s' \<in> S'. dist s s' \<le> 2 * r} = S \<or> C \<union> {s} \<noteq> {})" by simp

  ultimately show ?thesis unfolding inv_def by blast
qed

lemma inv_last_1: 
  assumes "\<forall>s \<in> (S - S'). distance C s \<le> 2*r"
    and "S' = {}"
  shows "radius C \<le> 2*r"
  by (metis Diff_empty assms image_iff radius_contained)

lemma inv_last_2: 
  assumes "finite C"
  and "card C > n"
  and "C \<subseteq> S"
  and "\<forall>c\<^sub>1 \<in> C. \<forall>c\<^sub>2 \<in> C. c\<^sub>1 \<noteq> c\<^sub>2 \<longrightarrow> dist c\<^sub>1 c\<^sub>2 > 2*r"
  shows "\<forall>C'. card C' \<le> n \<and> card C' > 0 \<longrightarrow> radius C' > r" (is ?P)
proof (rule ccontr)
  assume "\<not> ?P"
  then obtain C' where card_C': "card C' \<le> n \<and> card C' > 0" and radius_C': "radius C' \<le> r" by auto
  have "\<forall>c \<in> C. (\<exists>c'. c' \<in> C' \<and> dist c c' \<le> r)"
  proof
    fix c
    assume "c \<in> C"
    then have "c \<in> S" using assms(3) by blast
    then have "distance C' c \<le> radius C'" using finite_distances by (simp add: radius_def)
    then have "distance C' c \<le> r" using radius_C' by simp
    then show "\<exists>c'. c' \<in> C' \<and> dist c c' \<le> r" using dist_lemmas
      by (metis card_C' card_gt_0_iff)
  qed
  then obtain f where f: "\<forall>c\<in>C. f c \<in> C' \<and> dist c (f c) \<le> r" by metis
  have "\<not>inj_on f C"
  proof
    assume "inj_on f C"
    then have "card C' \<ge> card C" using \<open>inj_on f C\<close> card_inj_on_le card_ge_0_finite card_C' f by blast
    then show False using card_C' \<open>n < card C\<close> by linarith
  qed
  then obtain c1 c2 where defs: "c1 \<in> C \<and> c2 \<in> C \<and> c1 \<noteq> c2 \<and> f c1 = f c2" using inj_on_def by blast
  then have *: "dist c1 (f c1) \<le> r \<and> dist c2 (f c1) \<le> r" using f by auto

  have "2 * r < dist c1 c2" using assms defs by simp
  also have " ... \<le> dist c1 (f c1) + dist (f c1) c2" by(rule dist_triangle)
  also have " ... = dist c1 (f c1) + dist c2 (f c1)" using dist_commute by simp
  also have " ... \<le> 2 * r" using * by simp
  finally show False by simp
qed

lemma inv_last:
  assumes "inv {} C r"
  shows "(card C \<le> k \<longrightarrow> radius C \<le> 2*r) \<and> (card C > k \<longrightarrow> (\<forall>C'. card C' > 0 \<and> card C' \<le> k \<longrightarrow> radius C' > r))"
  using assms inv_def inv_last_1 inv_last_2 finite_subset[OF _ finite_sites] by auto

theorem Center_Selection_r:
  "VARS (S' :: ('a :: metric_space) set) (C :: ('a :: metric_space) set) (r :: real) (s :: 'a)
  {True}
  S' := S;
  C := {};
  WHILE S' \<noteq> {} INV {inv S' C r} DO
    s := (SOME s. s \<in> S');
    C := C \<union> {s};
    S' := S' - {s' . s' \<in> S' \<and> dist s s' \<le> 2*r}
    OD
  {(card C \<le> k \<longrightarrow> radius C \<le> 2*r) \<and> (card C > k \<longrightarrow> (\<forall>C'. card C' > 0 \<and> card C' \<le> k \<longrightarrow> radius C' > r))}"
proof (vcg, goal_cases)
  case (1 S' C r)
  then show ?case using inv_init by simp
next
  case (2 S' C r)
  then show ?case using inv_step by simp
next
  case (3 S' C r)
  then show ?case using inv_last by blast
qed


subsection \<open>The Main Algorithm\<close>

definition invar :: "('a :: metric_space) set \<Rightarrow> bool" where
"invar C = (C \<noteq> {} \<and> card C \<le> k \<and> C \<subseteq> S \<and>
  (\<forall>C'. (\<forall>c\<^sub>1 \<in> C. \<forall>c\<^sub>2 \<in> C. c\<^sub>1 \<noteq> c\<^sub>2 \<longrightarrow> dist c\<^sub>1 c\<^sub>2 > 2 * radius C')
        \<or> (\<forall>s \<in> S. distance C s \<le> 2 * radius C')))"

abbreviation some where "some A \<equiv> (SOME s. s \<in> A)"

lemma invar_init: "invar {some S}"
proof -
  let ?s = "some S"
  have s_in_S: "?s \<in> S" using some_in_eq non_empty_sites by blast

  have "{?s} \<noteq> {}" by simp

  moreover

  have "{SOME s. s \<in> S} \<subseteq> S" using s_in_S by simp

  moreover

  have "card {SOME s. s \<in> S} \<le> k" using non_zero_k by simp

  ultimately show ?thesis by (auto simp: invar_def)
qed

abbreviation furthest_from where
"furthest_from C \<equiv> (SOME s. s \<in> S \<and> distance C s = Max (distance C ` S))" 

lemma invar_step:
assumes "invar C"
and "card C < k"
shows "invar (C \<union> {furthest_from C})"
proof -
  have furthest_from_C_props: "furthest_from C \<in> S \<and> distance C (furthest_from C) = radius C "
    using someI_ex[of "\<lambda>x. x \<in> S \<and> distance C x = radius C"] radius_def2 radius_def by auto
  have C_props: "finite C \<and> C \<noteq> {}"
    using finite_subset[OF _ finite_sites] assms(1) unfolding invar_def by blast
  {
    have "card (C \<union> {furthest_from C}) \<le> card C + 1"
      using assms(1) C_props unfolding invar_def by (simp add: card_insert_if)
    then have "card (C \<union> {furthest_from C}) < k + 1" using assms(2) by simp
    then have "card (C \<union> {furthest_from C}) \<le> k" by simp
  }
  moreover

  have "C \<union> {furthest_from C} \<noteq> {}" by simp

  moreover

  have "(C \<union> {furthest_from C}) \<subseteq> S" using assms(1) furthest_from_C_props unfolding invar_def by simp

  moreover

  have "\<forall>C'. (\<forall>s \<in> S. distance (C \<union> {furthest_from C}) s \<le> 2 * radius C')
          \<or> (\<forall>c\<^sub>1 \<in> C \<union> {furthest_from C}. \<forall>c\<^sub>2 \<in> C \<union> {furthest_from C}. c\<^sub>1 \<noteq> c\<^sub>2 \<longrightarrow> 2 * radius C' < dist c\<^sub>1 c\<^sub>2)"
  proof 
    fix C'
    have "distance C (furthest_from C) > 2 * radius C' \<or> distance C (furthest_from C) \<le> 2 * radius C'" by auto
    then show "(\<forall>s \<in> S. distance (C \<union> {furthest_from C}) s \<le> 2 * radius C')
               \<or> (\<forall>c\<^sub>1 \<in> C \<union> {furthest_from C}. \<forall>c\<^sub>2 \<in> C \<union> {furthest_from C}. c\<^sub>1 \<noteq> c\<^sub>2 \<longrightarrow> 2 * radius C' < dist c\<^sub>1 c\<^sub>2)"
    proof (elim disjE)
      assume asm: "distance C (furthest_from C) > 2 * radius C'"
      then have "\<not>(\<forall>s \<in> S. distance C s \<le> 2 * radius C')" using furthest_from_C_props by force
      then have IH: "\<forall>c\<^sub>1 \<in> C. \<forall>c\<^sub>2 \<in> C. c\<^sub>1 \<noteq> c\<^sub>2 \<longrightarrow> 2 * radius C' < dist c\<^sub>1 c\<^sub>2"
        using assms(1) unfolding invar_def by blast
      have "(\<forall>c\<^sub>1 \<in> C \<union> {furthest_from C}. (\<forall>c\<^sub>2 \<in> C \<union> {furthest_from C}. c\<^sub>1 \<noteq> c\<^sub>2 \<longrightarrow> 2 * radius C' < dist c\<^sub>1 c\<^sub>2))"
        using dist_ins[of "C" "2 * radius C'" "furthest_from C"] IH C_props asm by simp
      then show ?thesis by simp
    next
      assume main_assm: "2 * radius C' \<ge> distance C (furthest_from C)"
      have "(\<forall>s \<in> S. distance (C \<union> {furthest_from C}) s \<le> 2 * radius C')"
      proof
        fix s
        assume local_assm: "s \<in> S"
        then show "distance (C \<union> {furthest_from C}) s \<le> 2 * radius C'"
        proof -
          have "distance (C \<union> {furthest_from C}) s \<le> distance C s"
            using distance_mono[of C "C \<union> {furthest_from C}"] C_props by auto
          also have " ... \<le> distance C (furthest_from C)"
            using Max.coboundedI local_assm finite_distances radius_def furthest_from_C_props by auto
          also have " ... \<le> 2 * radius C'" using main_assm by simp
          finally show ?thesis .
        qed
      qed
      then show ?thesis by blast
    qed
  qed

  ultimately show ?thesis unfolding invar_def by blast
qed

lemma invar_last:
assumes "invar C" and "\<not>card C < k"
shows "card C = k" and "card C' > 0 \<and> card C' \<le> k \<longrightarrow> radius C \<le> 2 * radius C'"
proof -
  show "card C = k" using assms(1, 2) unfolding invar_def by simp
next
  have C_props: "finite C \<and> C \<noteq> {}" using finite_sites assms(1) unfolding invar_def by (meson finite_subset)
  show "card C' > 0 \<and> card C' \<le> k \<longrightarrow> radius C \<le> 2 * radius C'"
  proof (rule impI)
    assume C'_assms: "0 < card (C' :: 'a set) \<and> card C' \<le> k"
    let ?r = "radius C'"
    have "(\<forall>c\<^sub>1 \<in> C. \<forall>c\<^sub>2 \<in> C. c\<^sub>1 \<noteq> c\<^sub>2 \<longrightarrow> 2 * ?r < dist c\<^sub>1 c\<^sub>2) \<or> (\<forall>s \<in> S. distance C s \<le> 2 * ?r)"
      using assms(1) unfolding invar_def by simp
    then show "radius C \<le> 2 * ?r"
    proof
      assume case_assm: "\<forall>c\<^sub>1\<in>C. \<forall>c\<^sub>2\<in>C. c\<^sub>1 \<noteq> c\<^sub>2 \<longrightarrow> 2 * ?r < dist c\<^sub>1 c\<^sub>2"
      obtain s where s_def: "radius C = distance C s \<and> s \<in> S" using radius_def2 by metis
      show ?thesis
      proof (rule ccontr)
        assume contr_assm: "\<not> radius C \<le> 2 * ?r"
        then have s_prop: "distance C s > 2 * ?r" using s_def by simp
        then have \<open>\<forall>c\<^sub>1 \<in> C \<union> {s}. \<forall>c\<^sub>2 \<in> C \<union> {s}. c\<^sub>1 \<noteq> c\<^sub>2 \<longrightarrow> dist c\<^sub>1 c\<^sub>2 > 2 * ?r\<close>
          using C_props dist_ins[of "C" "2*?r" "s"] case_assm by blast
        moreover
        {
          have "s \<notin> C"
          proof
            assume "s \<in> C"
            then have "distance C s \<le> dist s s" using Min.coboundedI[of "distance C ` S" "dist s s"] 
              by (simp add: distance_def C_props)
            also have " ... = 0" by simp
            finally have "distance C s = 0" using dist_lemmas(4) by (smt C_props)
            then have radius_le_zero: "2 * ?r < 0" using contr_assm s_def by simp
            obtain x where x_def: "?r = distance C' x" using radius_def2 by metis
            obtain l where l_def: "distance C' x = dist x l" using dist_lemmas(3) by (metis C'_assms card_gt_0_iff)
            then have "dist x l = ?r" by (simp add: x_def)
            also have "...  < 0" using C'_assms radius_le_zero by simp
            finally show False by simp
          qed
          then have "card (C \<union> {s}) > k" using assms(1,2) C_props unfolding invar_def by simp
        }
        moreover
          have "C \<union> {s} \<subseteq> S" using assms(1) s_def unfolding invar_def by simp
        moreover
          have "finite (C \<union> {s})" using calculation(3) finite_subset finite_sites by auto
        ultimately have "\<forall>C. card C \<le> k \<and> card C > 0 \<longrightarrow> radius C > ?r" using inv_last_2 by metis
        then have "?r > ?r" using C'_assms by blast
        then show False by simp
      qed
    next
      assume "\<forall>s\<in>S. distance C s \<le> 2 * radius C'"
      then show ?thesis by (metis image_iff radius_contained)
    qed
  qed
qed

theorem Center_Selection: 
"VARS (C :: ('a :: metric_space) set) (s :: ('a :: metric_space))
  {k \<le> card S}
  C := {some S};
  WHILE card C < k INV {invar C} DO
    C := C \<union> {furthest_from C}
  OD
  {card C = k \<and> (\<forall>C'. card C' > 0 \<and> card C' \<le> k \<longrightarrow> radius C \<le> 2 * radius C')}"
proof (vcg, goal_cases)
  case (1 C s)
  show ?case using invar_init by simp
next
  case (2 C s)
  then show ?case using invar_step by blast
next
  case (3 C s)
  then show ?case using invar_last by blast
qed

end
end