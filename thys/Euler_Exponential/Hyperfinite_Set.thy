(*  Title:  Hyperfinite_Set.thy
    Author: Jacques D. Fleuriot, University of Edinburgh, 2026
*)

theory Hyperfinite_Set
imports "HOL-Nonstandard_Analysis.NatStar" Internal
begin

section\<open>Hyperfinite sets\<close> 

definition 
  hyperfinite :: "'a star set \<Rightarrow> bool" where 
  "hyperfinite S \<equiv> unstar (star_n (\<lambda>n. finite ((*ns* S) n))) "

text\<open>Usual definition of a hyperfinite set\<close>

lemma hyperfinite_iff:
  "hyperfinite S =  (eventually (\<lambda>n. finite ((*ns* S) n)) \<U>)"
by (simp add: hyperfinite_def unstar_def star_of_def star_n_eq_iff)

lemma hyperfinite_starset_n_iff:
  "hyperfinite (*sn* X) =  (eventually (\<lambda>n. finite (X n)) \<U>)"
by (simp add: hyperfinite_def unstar_def star_of_def star_n_eq_iff 
       P_n_starset_starset_n_ultra_iff)

lemma hyperfinite_empty [simp]: "hyperfinite {}"
  using eventually_mono hyperfinite_starset_n_iff n_starset_empty_ultra 
  by force

lemma hyperfinite_Iset_iff_starP_finite:
   "hyperfinite (Iset X) = (*p* finite) X"
  by (metis (full_types) hyperfinite_starset_n_iff starP_star_n 
       star_n_star starset_n_def)

lemma finite_hyperfinite_starset:
   "finite X \<Longrightarrow> hyperfinite (*s* X)"
by (simp add: hyperfinite_Iset_iff_starP_finite starset_def)

lemma hyperfinite_starset_finite:
   "hyperfinite (*s* X) \<Longrightarrow> finite X"
by (simp add: hyperfinite_Iset_iff_starP_finite starset_def)

lemma hyperfinite_starset_iff_finite:
   "hyperfinite (*s* X) = finite X"
by (blast intro: finite_hyperfinite_starset hyperfinite_starset_finite)

subsection\<open>Properties of hyperfinite sets\<close>

lemma hyperfinite_UnI: 
  "\<lbrakk> X \<in> InternalSets; Y \<in> InternalSets; 
     hyperfinite X; hyperfinite Y \<rbrakk> \<Longrightarrow> hyperfinite (X \<union> Y)"
by (auto simp add: hyperfinite_iff InternalSets_def starset_n_Un [symmetric] 
       P_n_starset_starset_n_ultra_iff eventually_conj_iff)

lemma hyperfinite_starset_n_UnI: 
  "\<lbrakk> hyperfinite (*sn* X); hyperfinite (*sn* Y) \<rbrakk> \<Longrightarrow> hyperfinite (*sn* X \<union> *sn* Y)"
by (auto intro: hyperfinite_UnI)

lemma hyperfinite_starset_n_Un [iff]:
  "hyperfinite ((*sn* X) \<union> (*sn* Y)) \<longleftrightarrow> hyperfinite (*sn* X) \<and> hyperfinite (*sn* Y)"
by (simp add: starset_n_Un [symmetric] hyperfinite_starset_n_iff eventually_conj_iff)

lemma hyperfinite_singleton [simp]: "hyperfinite {x}"
proof -
  obtain X where starx: "x = star_n X"
    using star_cases by blast
  have "\<And>f fa. \<forall>\<^sub>F n in fa. finite {f (n::nat)::'a}"
    by simp
  then have "hyperfinite (*sn* (\<lambda>n. {X n}))"
    using hyperfinite_starset_n_iff by blast
  then show ?thesis
    by (simp add: starx) 
qed

lemma finite_hyperfinite:
  assumes "finite X" 
  shows "hyperfinite X"
proof (rule finite_induct)
  show "finite X" using assms .
next
  show "hyperfinite {}" by simp
next 
  fix x::"'a star" and A::"'a star set"
  assume As: "finite A" "x \<notin> A" "hyperfinite A"
  then have "A \<in> InternalSets" using finite_InternalSets by blast
  moreover have "{xa. xa = x} \<in> InternalSets" by simp
  moreover have "hyperfinite {xa. xa = x}" by simp
  ultimately have " hyperfinite ({xa. xa = x} \<union> A)"
    using hyperfinite_UnI As by blast
  then show "hyperfinite (insert x A)" by simp
qed

lemma hyperfinite_insert [simp]: 
   "A \<in> InternalSets \<Longrightarrow> hyperfinite (insert a A) \<longleftrightarrow> hyperfinite A"
by (metis InternalSets_singleton InternalSets_starset_n_starset 
          hyperfinite_singleton hyperfinite_starset_n_Un insert_def singleton_conv)

lemma hyperfinite_starset_n_insert [simp]: 
   "hyperfinite (insert a (*sn* A)) \<longleftrightarrow> hyperfinite (*sn* A)"
by simp

lemma hyperfinite_subset:
  assumes "A \<in> InternalSets" and "B \<in> InternalSets" and
          "hyperfinite B" and "A \<subseteq> B"
  shows "hyperfinite A"
proof -
  have "\<forall>S. (S::'a star set) \<notin> InternalSets \<or> *sn* *ns* S = S"
    using InternalSets_starset_n_starset by blast
  then show ?thesis
    by (metis (no_types) assms hyperfinite_starset_n_Un le_iff_sup)
qed

lemma hyperfinite_starset_n_subset:
  "\<lbrakk> hyperfinite (*sn* Y); (*sn* X) \<subseteq> (*sn* Y) \<rbrakk> \<Longrightarrow> hyperfinite (*sn* X)"
by (force intro: hyperfinite_subset)

lemma hyperfinite_Int [simp, intro]: 
  "\<lbrakk> X \<in> InternalSets; Y \<in> InternalSets; 
     hyperfinite X \<or> hyperfinite Y \<rbrakk> \<Longrightarrow> hyperfinite (X \<inter> Y)" 
 by (blast intro: hyperfinite_subset InternalSets_Int)

(* Some redundancy but it seems useful *)
lemma hyperfinite_IntI1: 
  "\<lbrakk> X \<in> InternalSets; Y \<in> InternalSets; hyperfinite X \<rbrakk> \<Longrightarrow> hyperfinite (X \<inter> Y)" 
by (blast intro: hyperfinite_subset InternalSets_Int)

lemma hyperfinite_IntI2: 
  "\<lbrakk> X \<in> InternalSets; Y \<in> InternalSets; hyperfinite Y \<rbrakk> \<Longrightarrow> hyperfinite (X \<inter> Y)" 
by (blast intro: hyperfinite_subset InternalSets_Int)

lemma hyperfinite_starset_n_Int [simp, intro]: 
  "hyperfinite (*sn* X) \<or> hyperfinite (*sn* Y) \<Longrightarrow> hyperfinite (*sn* X \<inter> *sn* Y)" 
by simp

lemma hyperfinite_starset_n_IntI1: 
  "hyperfinite (*sn* X) \<Longrightarrow> hyperfinite (*sn* X \<inter> *sn* Y)" 
by simp

lemma hyperfinite_starset_n_IntI2: 
  "hyperfinite (*sn* Y) \<Longrightarrow> hyperfinite (*sn* X \<inter> *sn* Y)" 
by simp

lemma hyperfinite_Diff [simp, intro]:
  "\<lbrakk> X \<in> InternalSets; Y \<in> InternalSets; hyperfinite X \<rbrakk> \<Longrightarrow> hyperfinite (X - Y)"
by (blast intro: hyperfinite_subset InternalSets_diff)

lemma hyperfinite_starset_n_Diff [simp, intro]:
  "hyperfinite (*sn* X) \<Longrightarrow> hyperfinite (*sn* X - *sn* Y)"
by simp

lemma hyperfinite_Diff2 [simp]:
  assumes "X \<in> InternalSets" 
  and "Y \<in> InternalSets" 
  and "hyperfinite Y" 
  shows "hyperfinite (X - Y) \<longleftrightarrow> hyperfinite X"
proof 
  assume hyp: "hyperfinite (X - Y)"
  from assms obtain Xa Ya where XY: "X = *sn* Xa" "Y = *sn* Ya"
    by (metis InternalSets_starset_n_starset) 
  then have "hyperfinite (*sn* Xa \<inter> *sn* Ya)"
    using assms(3) by blast
  moreover have "hyperfinite (*sn* Xa - *sn* Ya)"
    using hyp XY by simp
  ultimately have " hyperfinite (*sn* (\<lambda>n. Xa n - Ya n) \<union> *sn* (\<lambda>n. Xa n \<inter> Ya n))"
    using hyperfinite_starset_n_UnI 
    by (force simp only: starset_n_diff [symmetric]  starset_n_Int [symmetric])
  then  show "hyperfinite X" using XY(1)
    by (auto simp only: starset_n_Un [symmetric] Un_Diff_Int Int_commute)
next 
  assume "hyperfinite X" 
  then show "hyperfinite (X - Y)"
    by (simp add: assms(1) assms(2))
qed

lemma hyperfinite_starset_n_Diff2 [simp]:
  "hyperfinite (*sn* X) 
    \<Longrightarrow> hyperfinite (*sn* X - *sn* Y) \<longleftrightarrow> hyperfinite (*sn* X)"
by simp

lemma hyperfinite_Diff_insert [iff]:
  "\<lbrakk> X \<in> InternalSets; Y \<in> InternalSets \<rbrakk> 
   \<Longrightarrow> hyperfinite (X - insert a Y) \<longleftrightarrow> hyperfinite (X - Y)"
by (metis Diff_insert InternalSets_diff InternalSets_singleton 
    hyperfinite_singleton hyperfinite_Diff2)

lemma hyperfinite_starset_n_Diff_insert [iff]:
   "hyperfinite (*sn* X - insert a (*sn* Y)) \<longleftrightarrow> hyperfinite (*sn* X - *sn* Y)"
by simp

lemma hyperfinite_Compl[simp]:
  "\<lbrakk> X \<in> InternalSets; hyperfinite (X :: 'a star set) \<rbrakk> 
   \<Longrightarrow> hyperfinite (- X) \<longleftrightarrow> hyperfinite (UNIV :: 'a star set)"
  by (metis Compl_eq_Diff_UNIV NatStar.InternalSets_starset_n hyperfinite_Diff2 starset_UNIV)

lemma hyperfinite_starset_n_Compl[simp]:
  "hyperfinite (*sn* X :: 'a star set) 
   \<Longrightarrow> hyperfinite (- (*sn* X)) \<longleftrightarrow> hyperfinite (UNIV :: 'a star set)"
by simp

lemma hyperfinite_Collect_not[simp]:
  "\<lbrakk> {x :: 'a star. P x} \<in> InternalSets; hyperfinite {x :: 'a star. P x} \<rbrakk> 
   \<Longrightarrow> hyperfinite {x. \<not> P x} \<longleftrightarrow> hyperfinite (UNIV :: 'a star set)"
by (simp add: Collect_neg_eq)

lemma hyperfinite_starset_Collect_not[simp]:
  "hyperfinite {x :: 'a star. (*p* P) x} 
   \<Longrightarrow> hyperfinite {x. \<not> (*p* P) x} \<longleftrightarrow> hyperfinite (UNIV :: 'a star set)"
by (simp add: Collect_starP_starset_eq)

lemma hypnat_hyperfinite_atLeastLessThan [simp]: 
  "hyperfinite {M::hypnat..<N}"
proof (cases M, cases N, simp)
  fix X Xa
  assume "M = star_n X" "N = star_n Xa"
  then show "hyperfinite {star_n X..<star_n Xa}"
    by (simp add: hyperfinite_iff starset_n_atLeastLessThan_eq [symmetric] 
            P_n_starset_starset_n_ultra_iff)
qed

lemma hyperfinite_hypnat_set_atLeastAtMost:
   "hyperfinite ({of_nat m .. of_nat n} :: hypnat set)"
by (metis finite_atLeastAtMost hyperfinite_starset_iff_finite starset_atLeastAtMost)

subsection\<open>Hyperfold function\<close>

definition hyperfold :: "('a star \<Rightarrow> 'b star \<Rightarrow> 'b star) \<Rightarrow> 'b star \<Rightarrow> 'a star set => 'b star" where
  "hyperfold f z A =  star_n (\<lambda>n. Finite_Set.fold ((*nf2* f) n) (n_star z n) ((*ns* A) n))"

text\<open>hypefold is indeed an internal function\<close>

lemma hyperfold:
  "hyperfold (*fn2* Fs) (star_n Zs) (*sn* As) = 
   star_n (\<lambda>n. Finite_Set.fold (Fs n) (Zs n) (As n))"
proof(simp add: hyperfold_def star_n_eq_iff)
  have "\<forall>\<^sub>F n in \<U>. (*nf2* *fn2* Fs) n = Fs n" (is "eventually ?A \<U>")
    by (simp add: n_starfun2_starfun2_n_eq_ultra) 
  moreover have "\<forall>\<^sub>F n in \<U>. (*ns* *sn* As) n = As n" (is "eventually ?B \<U>")
    by (simp add: n_starset_starset_n_eq_ultra)
  moreover have "\<forall>\<^sub>F n in \<U>. n_star (star_n Zs) n = Zs n" (is "eventually ?C \<U>")
    by (simp add: n_star_star_n_eq_ultra)
  ultimately have "eventually (\<lambda>n. ?A n \<and> ?B n \<and> ?C n) \<U>" 
    by (simp add: eventually_conj_iff)
  then show "\<forall>\<^sub>F n in \<U>.
       Finite_Set.fold ((*nf2* *fn2* Fs) n) (n_star (star_n Zs) n) ((*ns* *sn* As) n) =
       Finite_Set.fold (Fs n) (Zs n) (As n)"
    using eventually_mono by force
qed

(* An obvious transferred property for internal functions, 
   although it's not needed for the current development.
*)
lemma hyperfold_empty [simp]: "f \<in> InternalFuns2 \<Longrightarrow> hyperfold f z {} = z"
proof -
  obtain Z where starz: "z = star_n Z"
    using star_cases by blast
  moreover assume "f \<in> InternalFuns2"
  then obtain F where starf: "f = *fn2* F"
    by (metis InternalFuns2_starfun2_n_starfun2) 
  moreover have "\<forall>\<^sub>F n in \<U>. n_star (star_n Z) n = Z n"
    using n_star_star_n_eq_ultra by blast
  moreover have "\<forall>\<^sub>F n in \<U>. (*nf2* *fn2* F) n = F n"
    by (simp add: n_starfun2_starfun2_n_eq_ultra)
  moreover have "eventually (\<lambda>n. (*ns* {}) n = ({} :: 'a set)) \<U>"
    using n_starset_empty_ultra by blast
  ultimately show ?thesis 
    by (auto elim!: eventually_rev_mp simp add: hyperfold_def star_n_eq_iff )
qed

definition hyperfold_image ::
    "('b star \<Rightarrow> 'b star \<Rightarrow> 'b star) \<Rightarrow> ('a star \<Rightarrow> 'b star) \<Rightarrow> 'b star \<Rightarrow> 'a star set \<Rightarrow> 'b star"
    where "hyperfold_image f g = hyperfold (\<lambda>x y. f (g x) y)"

end