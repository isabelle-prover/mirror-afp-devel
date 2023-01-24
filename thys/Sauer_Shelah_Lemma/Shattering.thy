(*  Title:      Shattering.thy
    Author:     Ata Keskin, TU München
*)

section \<open>Definitions and lemmas about shattering\<close>

text \<open>In this section, we introduce the predicate @{term "shatters"} and the term for the family of sets that a family shatters @{term "shattered_by"}.\<close>

theory Shattering
  imports Main
begin

subsection \<open>Intersection of a family of sets with a set\<close>

abbreviation IntF :: "'a set set \<Rightarrow> 'a set \<Rightarrow> 'a set set" (infixl "\<inter>*" 60)
  where "F \<inter>* S \<equiv> ((\<inter>) S) ` F"

lemma idem_IntF:
  assumes "\<Union>A \<subseteq> Y"
  shows "A \<inter>* Y = A"
proof -
  from assms have "A \<subseteq> A \<inter>* Y" by blast
  thus ?thesis by fastforce
qed

lemma subset_IntF: 
  assumes "A \<subseteq> B"
  shows "A \<inter>* X \<subseteq> B \<inter>* X"
  using assms by (rule image_mono)

lemma Int_IntF: "(A \<inter>* Y) \<inter>* X = A \<inter>* (Y \<inter> X)"
proof
  show "A \<inter>* Y \<inter>* X \<subseteq> A \<inter>* (Y \<inter> X)"
  proof
    fix S
    assume "S \<in> A \<inter>* Y \<inter>* X"
    then obtain a_y where A_Y0: "a_y \<in> A \<inter>* Y" and A_Y1: "a_y \<inter> X = S" by blast
    from A_Y0 obtain a where A0: "a \<in> A" and A1: "a \<inter> Y = a_y" by blast
    from A_Y1 A1 have "a \<inter> (Y \<inter> X) = S" by fast
    with A0 show "S \<in> A \<inter>* (Y \<inter> X)" by blast
  qed
next
  show "A \<inter>* (Y \<inter> X) \<subseteq> A \<inter>* Y \<inter>* X"
  proof
    fix S
    assume "S \<in> A \<inter>* (Y \<inter> X)"
    then obtain a where A0: "a \<in> A" and A1: "a \<inter> (Y \<inter> X) = S" by blast
    from A0 have "a \<inter> Y \<in> A \<inter>* Y" by blast
    with A1 show "S \<in> (A \<inter>* Y) \<inter>* X" by blast
  qed
qed

text \<open>@{term insert} distributes over @{term IntF}\<close>
lemma insert_IntF: 
  shows "insert x ` (H \<inter>* S) = (insert x ` H) \<inter>* (insert x S)"
proof
  show "insert x ` (H \<inter>* S) \<subseteq> (insert x ` H) \<inter>* (insert x S)"
  proof
    fix y_x
    assume "y_x \<in> insert x ` (H \<inter>* S)"
    then obtain y where 0: "y \<in> (H \<inter>* S)" and 1: "y_x = y \<union> {x}" by blast
    from 0 obtain yh where 2: "yh \<in> H" and 3: "y = yh \<inter> S" by blast
    from 1 3 have "y_x = (yh \<union> {x}) \<inter> (S \<union> {x})" by simp
    with 2 show "y_x \<in> (insert x ` H) \<inter>* (insert x S)" by blast
  qed
next
  show "insert x ` H \<inter>* (insert x S) \<subseteq> insert x ` (H \<inter>* S)"
  proof
    fix y_x
    assume "y_x \<in> insert x ` H \<inter>* (insert x S)"
    then obtain yh_x where 0: "yh_x \<in> (\<lambda>Y. Y \<union> {x}) ` H" and 1: "y_x = yh_x \<inter> (S \<union> {x})" by blast
    from 0 obtain yh where 2: "yh \<in> H" and 3: "yh_x = yh \<union> {x}" by blast
    from 1 3 have "y_x = (yh \<inter> S) \<union> {x}" by simp
    with 2 show "y_x \<in> insert x ` (H \<inter>* S)" by blast
  qed
qed

subsection \<open>Definition of @{term shatters}, @{term VC_dim} and @{term shattered_by}\<close>

abbreviation shatters :: "'a set set \<Rightarrow> 'a set \<Rightarrow> bool" (infixl "shatters" 70)
  where "H shatters A \<equiv> H \<inter>* A = Pow A"

definition VC_dim :: "'a set set \<Rightarrow> nat"
  where "VC_dim F = Sup {card S | S. F shatters S}"

definition shattered_by :: "'a set set \<Rightarrow> 'a set set"
  where "shattered_by F \<equiv> {A. F shatters A}"

lemma shattered_by_in_Pow:
  shows "shattered_by F \<subseteq> Pow (\<Union> F)"
  unfolding shattered_by_def by blast

lemma subset_shatters:
  assumes "A \<subseteq> B" and "A shatters X"
  shows "B shatters X"
proof -
  from assms(1) have "A \<inter>* X \<subseteq> B \<inter>* X" by blast
  with assms(2) have "Pow X \<subseteq> B \<inter>* X"  by presburger
  thus ?thesis by blast
qed

lemma supset_shatters:
  assumes "Y \<subseteq> X" and "A shatters X"
  shows "A shatters Y"
proof -
  have h: "\<Union>(Pow Y) \<subseteq> Y" by simp
  from assms have 0: "Pow Y \<subseteq> A \<inter>* X" by auto
  from subset_IntF[OF 0, of Y] Int_IntF[of Y X A] idem_IntF[OF h] have "Pow Y \<subseteq> A \<inter>* (X \<inter> Y)" by argo
  with Int_absorb2[OF assms(1)] Int_commute[of X Y] have "Pow Y \<subseteq> A \<inter>* Y" by presburger
  then show ?thesis by fast
qed

lemma shatters_empty:
  assumes "F \<noteq> {}"
  shows "F shatters {}" 
using assms by fastforce

lemma subset_shattered_by:
  assumes "A \<subseteq> B"
  shows "shattered_by A \<subseteq> shattered_by B" 
unfolding shattered_by_def using subset_shatters[OF assms] by force

lemma finite_shattered_by:
  assumes "finite (\<Union> F)"
  shows "finite (shattered_by F)"
  using assms rev_finite_subset[OF _ shattered_by_in_Pow, of F] by fast

text \<open>The following example shows that requiring finiteness of a family of sets is not enough, to ensure that @{term "shattered_by"} also stays finite.\<close>

lemma "\<exists>F::nat set set. finite F \<and> infinite (shattered_by F)"
proof -           
  let ?F = "{odd -` {True}, odd -` {False}}"
  have 0: "finite ?F" by simp

  let ?f = "\<lambda>n::nat. {n}" 
  let ?N = "range ?f"
  have "inj (\<lambda>n. {n})" by simp
  with infinite_iff_countable_subset[of ?N] have infinite_N: "infinite ?N" by blast
  have F_shatters_any_singleton: "?F shatters {n::nat}" for n
  proof -
    have Pow_n: "Pow {n} = {{n}, {}}" by blast
    have 1: "Pow {n} \<subseteq> ?F \<inter>* {n}" 
    proof (cases "odd n")
      case True
      from True have "(odd -` {False}) \<inter> {n} = {}" by blast
      hence 0: "{} \<in> ?F \<inter>* {n}"  by blast
      from True have "(odd -` {True}) \<inter> {n} = {n}" by blast
      hence 1: "{n} \<in> ?F \<inter>* {n}"  by blast
      from 0 1 Pow_n show ?thesis by simp
    next
      case False
      from False have "(odd -` {True}) \<inter> {n} = {}" by blast
      hence 0: "{} \<in> ?F \<inter>* {n}" by blast
      from False have "(odd -` {False}) \<inter> {n} = {n}" by blast
      hence 1: "{n} \<in> ?F \<inter>* {n}" by blast
      from 0 1 Pow_n show ?thesis by simp
    qed
    thus ?thesis by fastforce
  qed
  then have "?N \<subseteq> shattered_by ?F" unfolding shattered_by_def by force
  from 0 infinite_super[OF this infinite_N] show ?thesis by blast
qed

end
