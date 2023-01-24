section\<open>Background material in additive combinatorics\<close>

text \<open>This section outlines some background definitions and basic lemmas in additive combinatorics
based on the notes by Gowers \cite{Gowersnotes}. \<close>
(*
  Session: Balog_Szemeredi_Gowers
  Title:   Additive_Combinatorics_Preliminaries.thy
  Authors: Angeliki Koutsoukou-Argyraki, Mantas Bakšys, and Chelsea Edmonds 
  Affiliation: University of Cambridge
  Date: August 2022.
*)

theory Additive_Combinatorics_Preliminaries
  imports 
    Pluennecke_Ruzsa_Inequality.Pluennecke_Ruzsa_Inequality
begin

subsection\<open>Additive quadruples and additive energy\<close>

context additive_abelian_group

begin

definition additive_quadruple:: "'a \<Rightarrow>'a \<Rightarrow>'a \<Rightarrow> 'a \<Rightarrow> bool" where 
  "additive_quadruple a b c d  \<equiv> a \<in> G \<and> b \<in> G \<and> c \<in> G \<and> d \<in> G \<and> a \<oplus> b = c \<oplus> d"

lemma additive_quadruple_aux:
  assumes "additive_quadruple a b c d"
  shows "d = a \<oplus> b \<ominus> c"
  by (metis additive_quadruple_def assms associative commutative inverse_closed invertible 
    invertible_right_inverse2)

lemma additive_quadruple_diff:
  assumes "additive_quadruple a b c d"
  shows "a \<ominus> c = d \<ominus> b"
  by (smt (verit, del_insts) additive_quadruple_def assms associative commutative 
      composition_closed inverse_closed invertible invertible_inverse_inverse invertible_right_inverse2)

definition additive_quadruple_set:: "'a set \<Rightarrow> ('a \<times> 'a \<times> 'a \<times> 'a) set" where 
  "additive_quadruple_set A \<equiv> {(a, b, c, d) | a b c d. a \<in> A \<and> b \<in> A \<and> c \<in> A \<and> d \<in> A \<and> 
  additive_quadruple a b c d}"

lemma additive_quadruple_set_sub:
  "additive_quadruple_set A \<subseteq> {(a, b, c, d) | a b c d. d = a \<oplus> b \<ominus> c \<and> a \<in> A \<and> b \<in> A \<and> 
    c \<in> A \<and> d \<in> A}" using additive_quadruple_set_def additive_quadruple_def additive_quadruple_aux 
  by auto

definition additive_energy:: "'a set \<Rightarrow> real" where 
  "additive_energy A \<equiv> card (additive_quadruple_set A) / (card A)^3" 

lemma card_ineq_aux_quadruples:
  assumes "finite A"
  shows "card (additive_quadruple_set A) \<le> (card A)^3"

proof-
  define f:: "'a \<times> 'a \<times> 'a \<times> 'a \<Rightarrow> 'a \<times> 'a \<times> 'a" where "f = (\<lambda> (a, b, c, d) . (a, b, c))"
  have hinj: "inj_on f {(a, b, c, d) | a b c d. d = a \<oplus> b \<ominus> c \<and> a \<in> A \<and> b \<in> A \<and> c \<in> A \<and> d \<in> A}"
  unfolding inj_on_def f_def by auto
  moreover have himage: "f ` {(a, b, c, d) | a b c d. d = a \<oplus> b \<ominus> c \<and> a \<in> A \<and> b \<in> A \<and> c \<in> A \<and> d \<in> A} \<subseteq> A \<times> A \<times> A"
    unfolding f_def by auto
  ultimately have "card (additive_quadruple_set A) \<le> card ({(a, b, c, d) | a b c d. d = a \<oplus> b \<ominus> c \<and> a \<in> A \<and> b \<in> A \<and> c \<in> A \<and> d \<in> A})"
    using card_mono inj_on_finite[of "f"] assms additive_quadruple_set_sub finite_SigmaI
    by (metis (no_types, lifting))
  also have "... \<le> card (A \<times> A \<times> A)" using himage hinj assms card_inj_on_le finite_SigmaI
    by (metis (no_types, lifting))
  finally show ?thesis by (simp add: card_cartesian_product power3_eq_cube)
qed
  
lemma additive_energy_upper_bound: "additive_energy A \<le> 1"

proof (cases "finite A")
  assume hA: "finite A"
  show ?thesis unfolding additive_energy_def using card_ineq_aux_quadruples hA 
    card_cartesian_product power3_eq_cube by (simp add: divide_le_eq)
next
  assume "infinite A"
  thus ?thesis unfolding additive_energy_def by simp
qed


subsection\<open>On sums\<close>

definition f_sum:: "'a \<Rightarrow>'a set \<Rightarrow> nat" where
  "f_sum d A \<equiv> card {(a, b) | a b. a \<in> A \<and> b \<in> A \<and> a \<oplus> b = d}"


lemma pairwise_disjnt_sum_1:
  "pairwise (\<lambda>s t. disjnt ((\<lambda> d .{(a, b) | a b. a \<in> A \<and> b \<in> A \<and> (a \<oplus> b = d)}) s) 
    ((\<lambda> d .{(a, b) | a b. a \<in> A \<and> b \<in> A \<and> (a \<oplus> b = d)}) t)) (sumset A A)"
  unfolding disjnt_def by (intro pairwiseI) (auto)

lemma pairwise_disjnt_sum_2: 
  "pairwise disjnt ((\<lambda> d. {(a, b) | a b. a \<in> A \<and> b \<in> A \<and> a \<oplus> b = d}) ` (sumset A A))"
  unfolding disjnt_def by (intro pairwiseI) (auto)

lemma sum_Union_span:
  assumes "A \<subseteq> G"
  shows "\<Union> ((\<lambda> d .{(a, b) | a b. a \<in> A \<and> b \<in> A \<and> (a \<oplus> b = d)}) ` (sumset A A)) = A \<times> A"

proof
  show "\<Union> ((\<lambda> d .{(a, b) | a b. a \<in> A \<and> b \<in> A \<and> (a \<oplus> b = d)}) ` (sumset A A)) \<subseteq> A \<times> A" by blast
next
  show "A \<times> A \<subseteq> \<Union> ((\<lambda> d .{(a, b) | a b. a \<in> A \<and> b \<in> A \<and> (a \<oplus> b = d)}) ` (sumset A A))"
  proof (intro subsetI)
    fix x assume hxA: "x \<in> A \<times> A"
    then obtain y z where hxyz: "x = (y, z)" and hy: "y \<in> A" and hz:"z \<in> A" by blast
    show "x \<in> (\<Union>d\<in>(sumset A A).{(a, b) |a b. a \<in> A \<and> b \<in> A \<and> a \<oplus> b = d})"
      using hy hz assms hxA hxyz by auto
  qed
qed

lemma f_sum_le_card:
  assumes "finite A" and "A \<subseteq> G"
  shows "f_sum d A \<le> card A"

proof-
  define f:: "('a \<times> 'a) \<Rightarrow> 'a" where "f \<equiv> (\<lambda> (a, b). a)"
  have "inj_on f {(a, b) | a b. a \<in> A \<and> b \<in> A \<and> a \<oplus> b = d}"
  unfolding f_def proof (intro inj_onI)
  fix x y assume "x \<in> {(a, b) | a b. a \<in> A \<and> b \<in> A \<and> a \<oplus> b = d}" and
    "y \<in> {(a, b) |a b. a \<in> A \<and> b \<in> A \<and> a \<oplus> b = d}" and
    hcase: "(case x of (a, b) \<Rightarrow> a) = (case y of (a, b) \<Rightarrow> a)"
  then obtain x1 x2 y1 y2 where hx: "x = (x1, x2)" and hy:"y = (y1, y2)" and h1: "x1 \<oplus> x2 = d" and
    h2: "y1 \<oplus> y2 = d" and hx1: "x1 \<in> A" and hx2: "x2 \<in> A" and hy1: "y1 \<in> A" and hy2: "y2 \<in> A" by blast
  have hxsub: "x2 = d \<ominus> x1"
    using h1 hx1 hx2 assms by (metis additive_abelian_group.inverse_closed composition_closed 
     additive_abelian_group_axioms commutative invertible invertible_left_inverse2 subsetD)
  have hysub: "y2 = d \<ominus> y1"  
    using h2 hy1 hy2 assms by (metis inverse_closed commutative composition_closed hy1 hy2 
        invertible invertible_left_inverse2 subset_iff)
  show "x = y" using hx hy hxsub hysub hcase by auto
  qed
  moreover have "f ` {(a, b) | a b. a \<in> A \<and> b \<in> A \<and> a \<oplus> b = d} \<subseteq> A" using f_def by auto
  ultimately show ?thesis using card_mono assms f_sum_def card_image[of "f"] 
    by (metis (mono_tags, lifting))
qed

lemma f_sum_card:
  assumes "A \<subseteq> G" and hA: "finite A"
  shows "(\<Sum> d \<in> (sumset A A). (f_sum d A)) = (card A)^2"

proof-
  have fin: "\<forall> X \<in> ((\<lambda> d. {(a, b) | a b. a \<in> A \<and> b \<in> A \<and> (a \<oplus> b = d) }) ` (sumset A A)). finite X"
  proof 
    fix X assume hX: "X \<in> (\<lambda>d. {(a, b) | a b. a \<in> A \<and> b \<in> A \<and> a \<oplus> b = d}) ` (sumset A A)"
    then obtain d where hXd: "X = {(a, b) | a b. a \<in> A \<and> b \<in> A \<and> a \<oplus> b = d}" by blast
    show "finite X" using hA hXd finite_subset finite_cartesian_product
      by (smt (verit, best) mem_Collect_eq mem_Sigma_iff rev_finite_subset subrelI)
  qed
  have "(\<Sum>d\<in>(sumset A A). f_sum d A) = card (A \<times> A)"
    unfolding f_sum_def
    using sum_card_image[of "sumset A A" "(\<lambda> d .{(a, b) | a b. a \<in> A \<and> b \<in> A \<and> (a \<oplus> b = d)})"] 
      pairwise_disjnt_sum_1 hA finite_sumset card_Union_disjoint[of "((\<lambda>d. {(a, b) |a b. a \<in> A \<and> b \<in> A \<and> a \<oplus> b = d}) ` sumset A A)"] 
      fin pairwise_disjnt_sum_2 hA finite_sumset sum_Union_span assms by auto
  thus ?thesis using card_cartesian_product power2_eq_square by metis
qed
    
lemma f_sum_card_eq:
  assumes "A \<subseteq> G"
  shows "\<forall> x \<in> sumset A A.  (f_sum x A)^2 = 
    card {(a, b, c, d) | a b c d. a \<in> A \<and> b \<in> A \<and> c \<in> A \<and> d \<in> A \<and> 
    additive_quadruple a b c d \<and> a \<oplus> b = x \<and> c \<oplus> d = x}"

proof
  fix x assume "x \<in> sumset A A"
  define C where hC: "C = {(a, b, c, d) | a b c d. a \<in> A \<and> b \<in> A \<and> c \<in> A \<and> d \<in> A \<and>
    additive_quadruple a b c d \<and> a \<oplus> b = x \<and> c \<oplus> d = x}"
  define f:: "'a \<times> 'a \<times> 'a \<times> 'a \<Rightarrow> ('a \<times> 'a) \<times> ('a \<times> 'a)" where "f = (\<lambda> (a, b, c, d). ((a, b), (c, d)))"
  have hfinj: "inj_on f C" unfolding f_def by (intro inj_onI) (auto)
  have "f ` C = {((a,b), (c,d)) | a b c d. a \<in> A \<and> b \<in> A \<and> c \<in> A \<and> d \<in> A \<and> a \<oplus> b = x \<and> c \<oplus> d = x}"
  proof
    show "f ` C \<subseteq> {((a, b), (c, d)) |a b c d. a \<in> A \<and> b \<in> A \<and> c \<in> A \<and> d \<in> A \<and> a \<oplus> b = x \<and> c \<oplus> d = x}"
      unfolding f_def hC by auto
  next
    show "{((a, b), c, d) |a b c d. a \<in> A \<and> b \<in> A \<and> c \<in> A \<and> d \<in> A \<and> a \<oplus> b = x \<and> c \<oplus> d = x} \<subseteq> f ` C"
    proof
      fix z assume "z \<in> {((a, b), (c, d)) | a b c d. a \<in> A \<and> b \<in> A \<and> c \<in> A \<and> d \<in> A \<and> a \<oplus> b = x \<and> c \<oplus> d = x}"
      then obtain a b c d where hz: "z = ((a, b), (c, d))" and ha: "a \<in> A" and hb: "b \<in> A" and hc: "c \<in> A" and hd: "d \<in> A" 
      and hab: "a \<oplus> b = x" and hcd: "c \<oplus> d = x" by blast
      then have habcd: "(a, b, c, d) \<in> C" using additive_quadruple_def assms hC by auto
      show "z \<in> f ` C" using hz f_def habcd by force
    qed
  qed
  moreover have "{((a, b), c, d) |a b c d. a \<in> A \<and> b \<in> A \<and> c \<in> A \<and> d \<in> A \<and> a \<oplus> b = x \<and> c \<oplus> d = x} = 
    {(a, b) | a b. a \<in> A \<and> b \<in> A \<and> a \<oplus> b = x} \<times> {(c, d) | c d. c \<in> A \<and> d \<in> A \<and> c \<oplus> d = x}" by blast
  ultimately have "card C = card ({(a, b) | a b. a \<in> A \<and> b \<in> A \<and> a \<oplus> b = x}) ^ 2"
    using hfinj card_image[of "f"]  card_cartesian_product by (metis (no_types, lifting) Sigma_cong power2_eq_square)
  thus "(f_sum x A)^2 = card ({(a, b, c, d) | a b c d. a \<in> A \<and> b \<in> A \<and> c \<in> A \<and> d \<in> A \<and> 
    additive_quadruple a b c d \<and> a \<oplus> b = x \<and> c \<oplus> d = x})" using hC f_sum_def by auto
qed

lemma pairwise_disjoint_sum:
  "pairwise (\<lambda>s t. disjnt ((\<lambda> x. {(a, b, c, d) | a b c d. a \<in> A \<and> b \<in> A \<and> c \<in> A \<and> d \<in> A \<and>
     additive_quadruple a b c d \<and> a \<oplus> b = x \<and> c \<oplus> d = x}) s) 
     ((\<lambda> x. {(a, b, c, d) | a b c d. a \<in> A \<and> b \<in> A \<and> c \<in> A \<and> d \<in> A \<and>
     additive_quadruple a b c d \<and> a \<oplus> b = x \<and> c \<oplus> d = x}) t)) (sumset A A)"
  unfolding disjnt_def by (intro pairwiseI) (auto)


lemma pairwise_disjnt_quadruple_sum:
  "pairwise disjnt ((\<lambda> x. {(a, b, c, d) | a b c d. a \<in> A \<and> b \<in> A \<and> c \<in> A \<and> d \<in> A \<and> additive_quadruple a b c d \<and> a \<oplus> b = x \<and> c \<oplus> d = x}) ` (sumset A A))"
  unfolding disjnt_def by (intro pairwiseI) (auto)

lemma quadruple_sum_Union_eq:
   "\<Union> ((\<lambda> x. {(a, b, c, d) | a b c d. a \<in> A \<and> b \<in> A \<and> c \<in> A \<and> d \<in> A \<and> 
    additive_quadruple a b c d \<and> a \<oplus> b = x \<and> c \<oplus> d = x}) ` (sumset A A)) = additive_quadruple_set A"

proof
  show "(\<Union>x\<in>sumset A A.
    {(a, b, c, d) |a b c d. a \<in> A \<and> b \<in> A \<and> c \<in> A \<and> d \<in> A \<and> additive_quadruple a b c d \<and>
    a \<oplus> b = x \<and> c \<oplus> d = x}) \<subseteq> additive_quadruple_set A"
    unfolding additive_quadruple_set_def by (intro Union_least) (auto)
next
  show "additive_quadruple_set A \<subseteq> (\<Union>x\<in>sumset A A.
    {(a, b, c, d) |a b c d. a \<in> A \<and> b \<in> A \<and> c \<in> A \<and> d \<in> A \<and>
    additive_quadruple a b c d \<and> a \<oplus> b = x \<and> c \<oplus> d = x})"
  unfolding additive_quadruple_set_def additive_quadruple_def by (intro subsetI) (auto)
qed

lemma f_sum_card_quadruple_set: 
  assumes hAG: "A \<subseteq> G" and hA: "finite A"
  shows "(\<Sum> d \<in> (sumset A A). (f_sum d A)^2) = card (additive_quadruple_set A)"

proof-
  have fin: "\<forall> X \<in> ((\<lambda> x. {(a, b, c, d) | a b c d. a \<in> A \<and> b \<in> A \<and> c \<in> A \<and> d \<in> A \<and>
   additive_quadruple a b c d \<and> a \<oplus> b = x \<and> c \<oplus> d = x}) ` (sumset A A)). finite X"
  proof
    fix X assume "X \<in>  (\<lambda>x. {(a, b, c, d) | a b c d. a \<in> A \<and> b \<in> A \<and> c \<in> A \<and> d \<in> A \<and> 
      additive_quadruple a b c d \<and> a \<oplus> b = x \<and> c \<oplus> d = x}) ` sumset A A"
    then obtain x where hX: "X = {(a, b, c, d) | a b c d. a \<in> A \<and> b \<in> A \<and> c \<in> A \<and> d \<in> A \<and> 
      additive_quadruple a b c d \<and> a \<oplus> b = x \<and> c \<oplus> d = x}" 
      by blast
    show "finite X" using hA hX finite_subset finite_cartesian_product
      by (smt (verit, best) mem_Collect_eq mem_Sigma_iff rev_finite_subset subrelI)
  qed
  have "(\<Sum>d\<in>sumset A A. (f_sum d A)\<^sup>2) = 
    card (\<Union> ((\<lambda> x. {(a, b, c, d) | a b c d. a \<in> A \<and> b \<in> A \<and> c \<in> A \<and> d \<in> A \<and> 
    additive_quadruple a b c d \<and> a \<oplus> b = x \<and> c \<oplus> d = x}) ` (sumset A A)))"
    using f_sum_card_eq hAG sum_card_image[of "sumset A A" "(\<lambda>x. {(a, b, c, d) |a b c d.
      a \<in> A \<and> b \<in> A \<and> c \<in> A \<and> d \<in> A \<and> additive_quadruple a b c d \<and> a \<oplus> b = x \<and> c \<oplus> d = x})"] 
      pairwise_disjoint_sum card_Union_disjoint[of "(\<lambda> x. {(a, b, c, d) | a b c d. a \<in> A \<and> b \<in> A \<and>
      c \<in> A \<and> d \<in> A \<and> additive_quadruple a b c d \<and> a \<oplus> b = x \<and> c \<oplus> d = x}) ` (sumset A A)"] 
      fin pairwise_disjnt_quadruple_sum hA finite_sumset by auto
  then show ?thesis using quadruple_sum_Union_eq by auto
qed


lemma  f_sum_card_quadruple_set_additive_energy: assumes "A \<subseteq> G" and "finite A"
  shows "(\<Sum> d \<in> sumset A A. (f_sum d A)^2) = additive_energy A * (card A)^3"
  using assms f_sum_card_quadruple_set additive_energy_def by force


definition popular_sum:: "'a \<Rightarrow> real \<Rightarrow> 'a set \<Rightarrow> bool" where
  "popular_sum d \<theta> A  \<equiv> f_sum d A \<ge> \<theta> * of_real (card A)"

definition popular_sum_set:: "real \<Rightarrow> 'a set \<Rightarrow> 'a set" where
  "popular_sum_set \<theta> A \<equiv> {d \<in> sumset A A. popular_sum d \<theta> A}"


subsection\<open>On differences\<close>

text\<open>The following material is directly analogous to the material given previously on sums.
All definitions and lemmas are the corresponding ones for differences.
E.g. @{term f_diff} corresponds to  @{term f_sum}. \<close>

definition f_diff:: "'a \<Rightarrow>'a set \<Rightarrow> nat" where
  "f_diff d A \<equiv> card {(a, b) | a b. a \<in> A \<and> b \<in> A \<and> a \<ominus> b = d}"

lemma pairwise_disjnt_diff_1:
  "pairwise (\<lambda>s t. disjnt ((\<lambda> d .{(a, b) | a b. a \<in> A \<and> b \<in> A \<and> (a \<ominus> b = d)}) s) 
    ((\<lambda> d. {(a, b) | a b. a \<in> A \<and> b \<in> A \<and> (a \<ominus> b = d)}) t)) (differenceset A A)"
  using disjnt_def by (intro pairwiseI) (auto)

lemma pairwise_disjnt_diff_2: 
  "pairwise disjnt ((\<lambda> d. {(a, b) | a b. a \<in> A \<and> b \<in> A \<and> a \<ominus> b = d}) ` (differenceset A A))"
  unfolding disjnt_def by (intro pairwiseI) (auto)

lemma diff_Union_span:
  assumes "A \<subseteq> G"
  shows "\<Union> ((\<lambda> d .{(a, b) | a b. a \<in> A \<and> b \<in> A \<and> (a \<ominus> b = d)}) ` (differenceset A A)) = A \<times> A"

proof
  show "\<Union> ((\<lambda> d .{(a, b) | a b. a \<in> A \<and> b \<in> A \<and> (a \<ominus> b = d)}) ` (differenceset A A)) \<subseteq> A \<times> A"
    by blast
next
  show "A \<times> A \<subseteq> \<Union> ((\<lambda> d .{(a, b) | a b. a \<in> A \<and> b \<in> A \<and> (a \<ominus> b = d)}) ` (differenceset A A))"
  proof (intro subsetI)
    fix x assume hxA: "x \<in> A \<times> A"
    then obtain y z where hxyz: "x = (y, z)" and hy: "y \<in> A" and hz:"z \<in> A" by blast
    show "x \<in> (\<Union>d\<in>(differenceset A A).{(a, b) |a b. a \<in> A \<and> b \<in> A \<and> a \<ominus> b = d})"
      using hy hz assms hxA hxyz by auto
  qed
qed

lemma f_diff_le_card:
  assumes "finite A" and "A \<subseteq> G"
  shows "f_diff d A \<le> card A"

proof-
define f:: "('a \<times> 'a) \<Rightarrow> 'a" where "f \<equiv> (\<lambda> (a, b). a)"
  have "inj_on f {(a, b) | a b. a \<in> A \<and> b \<in> A \<and> a \<ominus> b = d}"
  unfolding f_def proof (intro inj_onI)
  fix x y assume "x \<in> {(a, b) |a b. a \<in> A \<and> b \<in> A \<and> a \<ominus> b = d}" and
    "y \<in> {(a, b) |a b. a \<in> A \<and> b \<in> A \<and> a \<ominus> b = d}" and
    hcase: "(case x of (a, b) \<Rightarrow> a) = (case y of (a, b) \<Rightarrow> a)"
  then obtain x1 x2 y1 y2 where hx: "x = (x1, x2)" and hy:"y = (y1, y2)" and h1: "x1 \<ominus> x2 = d" and
    h2: "y1 \<ominus> y2 = d" and hx1: "x1 \<in> A" and hx2: "x2 \<in> A" and hy1: "y1 \<in> A" and hy2: "y2 \<in> A" by blast
  have hxsub: "x2 = x1 \<ominus> d"
    using h1 assms associative commutative composition_closed hx1 hx2
    by (smt (verit, best) inverse_closed invertible invertible_left_inverse2 subset_iff)
  have hysub: "y2 = y1 \<ominus> d"
    using h2 assms associative commutative composition_closed hy1 hy2
    by (smt (verit, best) inverse_closed invertible invertible_left_inverse2 subset_iff)
  show "x = y" using hx hy hxsub hysub hcase by auto
  qed
  moreover have "f ` {(a, b) | a b. a \<in> A \<and> b \<in> A \<and> a \<ominus> b = d} \<subseteq> A" using f_def by auto
  ultimately show ?thesis using card_mono assms f_diff_def card_image[of "f"] 
    by (metis (mono_tags, lifting))
qed

lemma f_diff_card:
  assumes "A \<subseteq> G" and hA: "finite A"
  shows "(\<Sum> d \<in> (differenceset A A). f_diff d A) = (card A)^2"

proof-
  have fin: "\<forall> X \<in> ((\<lambda> d. {(a, b) | a b. a \<in> A \<and> b \<in> A \<and> (a \<ominus> b = d) }) ` (differenceset A A)). 
    finite X"
  proof
      fix X assume hX: "X \<in> (\<lambda>d. {(a, b) |a b. a \<in> A \<and> b \<in> A \<and> a \<ominus> b = d}) ` (differenceset A A)"
      then obtain d where hXd: "X = {(a, b) | a b. a \<in> A \<and> b \<in> A \<and> a \<ominus> b = d}" and
        "d \<in> (differenceset A A)" by blast
      have hXA: "X \<subseteq> A \<times> A" using hXd by blast
      show "finite X" using hXA hA finite_subset by blast
    qed
  have "(\<Sum>d\<in>(differenceset A A). f_diff d A) = card (A \<times> A)"
    unfolding f_diff_def using sum_card_image[of "differenceset A A" 
    "(\<lambda> d .{(a, b) | a b. a \<in> A \<and> b \<in> A \<and> (a \<ominus> b = d) })"] pairwise_disjnt_diff_1 
    card_Union_disjoint[of "((\<lambda>d. {(a, b) |a b. a \<in> A \<and> b \<in> A \<and> a \<ominus> b = d}) ` differenceset A A)"]
    fin pairwise_disjnt_diff_2 diff_Union_span assms hA finite_minusset finite_sumset by auto
  thus ?thesis using card_cartesian_product power2_eq_square by metis
qed
    
lemma f_diff_card_eq:
  assumes "A \<subseteq> G"
  shows "\<forall> x \<in> differenceset A A. (f_diff x A)^2 = 
    card {(a, b, c, d) | a b c d. a \<in> A \<and> b \<in> A \<and> c \<in> A \<and> d \<in> A \<and> 
    additive_quadruple a b c d \<and> a \<ominus> c = x \<and> d \<ominus> b = x}"

proof
  fix x assume "x \<in> differenceset A A"
  define C where hC: "C= {(a, b, c, d) | a b c d. a \<in> A \<and> b \<in> A \<and> c \<in> A \<and> d \<in> A \<and> additive_quadruple a b c d \<and> a \<ominus> c = x \<and> d \<ominus> b = x }"
  define f:: "'a \<times> 'a \<times> 'a \<times> 'a \<Rightarrow> ('a \<times> 'a) \<times> ('a \<times> 'a)" where "f = (\<lambda> (a, b, c, d). ((a, c), (d, b)))"
  have hfinj: "inj_on f C" using f_def by (intro inj_onI) (auto)
  have "f ` C = {((a,c), (d,b)) | a b c d. 
    a \<in> A \<and> b \<in> A \<and> c \<in> A \<and> d \<in> A \<and> a \<ominus> c = x \<and> d \<ominus> b = x}"
  proof
    show "f ` C \<subseteq> {((a, c), (d, b)) |a b c d. a \<in> A \<and> b \<in> A \<and> c \<in> A \<and> d \<in> A \<and> a \<ominus> c = x \<and> d \<ominus> b = x}"
      unfolding f_def hC by auto
  next
    show "{((a, c), d, b) |a b c d. a \<in> A \<and> b \<in> A \<and> c \<in> A \<and> d \<in> A \<and> a \<ominus> c = x \<and> d \<ominus> b = x} \<subseteq> f ` C"
    proof
      fix z assume "z \<in> {((a, c), (d, b)) |a b c d. a \<in> A \<and> b \<in> A \<and> c \<in> A \<and> d \<in> A \<and> a \<ominus> c = x \<and> d \<ominus> b = x}"
      then obtain a b c d where hz: "z = ((a, c), (d, b))" and ha: "a \<in> A" and hb: "b \<in> A" and hc: "c \<in> A" and hd: "d \<in> A" 
        and hab: "a \<ominus> c = x" and hcd: "d \<ominus> b = x" by blast
      have "additive_quadruple a b c d"
        using assms by (metis (no_types, lifting) ha hb hc hd additive_quadruple_def associative 
        commutative composition_closed hab hcd inverse_closed invertible invertible_right_inverse2 subset_eq)
      then have habcd: "(a, b, c, d) \<in> C" using hab hcd hC ha hb hc hd by blast
      show "z \<in> f ` C" using hz f_def habcd image_iff by fastforce
    qed
  qed
  moreover have "{((a, c), (d, b))|a b c d. a \<in> A \<and> b \<in> A \<and> c \<in> A \<and> d \<in> A \<and> a \<ominus> c = x \<and> d \<ominus> b = x} =
  {(a, c) | a c. a \<in> A \<and> c \<in> A \<and> a \<ominus> c = x} \<times> {(d, b) | d b. d \<in> A \<and> b \<in> A \<and> d \<ominus> b = x}" by blast
  moreover have "card C = card (f ` C)" using hfinj card_image[of "f"] by auto
  ultimately have "card C =  card ({(a, c) | a c. a \<in> A \<and> c \<in> A \<and> a \<ominus> c = x}) ^ 2" 
    using hfinj card_image[of "f"] card_cartesian_product Sigma_cong power2_eq_square by (smt (verit, best))
  thus "(f_diff x A)\<^sup>2 = card  {(a, b, c, d) |a b c d. a \<in> A \<and> b \<in> A \<and> c \<in> A \<and> d \<in> A \<and> additive_quadruple a b c d \<and> a \<ominus> c = x \<and> d \<ominus> b = x}" 
    using f_diff_def hC by simp
qed

lemma pairwise_disjoint_diff:
  "pairwise (\<lambda>s t. disjnt ((\<lambda> x. {(a, b, c, d) | a b c d. a \<in> A \<and> b \<in> A \<and> c \<in> A \<and> d \<in> A \<and> additive_quadruple a b c d \<and> a \<ominus> c = x \<and> d \<ominus> b = x}) s) 
    ((\<lambda> x. {(a, b, c, d) | a b c d. a \<in> A \<and> b \<in> A \<and> c \<in> A \<and> d \<in> A \<and> additive_quadruple a b c d \<and> a \<ominus> c = x \<and> d \<ominus> b = x}) t)) (differenceset A A)"
  unfolding disjnt_def by (intro pairwiseI) (auto)

lemma pairwise_disjnt_quadruple_diff:
 "pairwise disjnt ((\<lambda> x. {(a, b, c, d) | a b c d. a \<in> A \<and> b \<in> A \<and> c \<in> A \<and> d \<in> A \<and> additive_quadruple a b c d \<and> a \<ominus> c = x \<and> d \<ominus> b = x}) ` (differenceset A A))"
  unfolding disjnt_def by (intro pairwiseI) (auto)

lemma quadruple_diff_Union_eq:
  "\<Union> ((\<lambda> x. {(a, b, c, d) | a b c d. a \<in> A \<and> b \<in> A \<and> c \<in> A \<and> d \<in> A \<and> additive_quadruple a b c d \<and> a \<ominus> c = x \<and> d \<ominus> b = x}) ` (differenceset A A)) = 
    additive_quadruple_set A"

proof
  show "(\<Union>x\<in>differenceset A A. {(a, b, c, d) |a b c d. a \<in> A \<and> b \<in> A \<and> c \<in> A \<and> d \<in> A \<and> 
    additive_quadruple a b c d \<and> a \<ominus> c = x \<and> d \<ominus> b = x}) \<subseteq> additive_quadruple_set A"
    unfolding additive_quadruple_set_def by (intro Union_least)(auto)
next
  show "additive_quadruple_set A \<subseteq> (\<Union>x\<in>differenceset A A. 
    {(a, b, c, d) |a b c d. a \<in> A \<and> b \<in> A \<and> c \<in> A \<and> d \<in> A \<and> additive_quadruple a b c d \<and> a \<ominus> c = x \<and> d \<ominus> b = x})"
  proof (intro subsetI)
    fix x assume"x \<in> additive_quadruple_set A"
    then obtain x1 x2 x3 x4 where hx: "x = (x1, x2, x3, x4)" and hx1: "x1 \<in> A" and hx2: "x2 \<in> A" and hx3: "x3 \<in> A" 
      and hx4: "x4 \<in> A" and hxadd: "additive_quadruple x1 x2 x3 x4" 
      using additive_quadruple_set_def by auto
    have hxmem: "(x1, x2, x3, x4) \<in> {(a, b, c, d) |a b c d. a \<in> A \<and> b \<in> A \<and> c \<in> A \<and> d \<in> A \<and> 
      additive_quadruple a b c d \<and> a \<ominus> c = x1 \<ominus> x3 \<and> d \<ominus> b = x1 \<ominus> x3}"
      using additive_quadruple_diff hx1 hx2 hx3 hx4 hxadd by auto
    show "x \<in> (\<Union>x\<in>differenceset A A. {(a, b, c, d) |a b c d. a \<in> A \<and> b \<in> A \<and> c \<in> A \<and> d \<in> A \<and> 
      additive_quadruple a b c d \<and> a \<ominus> c = x \<and> d \<ominus> b = x})"
      using hx hxmem hx1 hx3 additive_quadruple_def hxadd by auto
  qed
qed

lemma f_diff_card_quadruple_set: 
  assumes hAG: "A \<subseteq> G" and hA: "finite A"
  shows "(\<Sum> d \<in> (differenceset A A). (f_diff d A)^2) = card (additive_quadruple_set A)"

proof-
  have fin: "\<forall> X \<in> ((\<lambda> x. {(a, b, c, d) | a b c d. a \<in> A \<and> b \<in> A \<and> c \<in> A \<and> d \<in> A \<and> 
    additive_quadruple a b c d \<and> a \<ominus> c = x \<and> d \<ominus> b = x}) ` (differenceset A A)). finite X"
  proof
    fix X assume "X \<in> (\<lambda>x. {(a, b, c, d) |a b c d. a \<in> A \<and> b \<in> A \<and> c \<in> A \<and> d \<in> A \<and> 
      additive_quadruple a b c d \<and> a \<ominus> c = x \<and> d \<ominus> b = x}) ` differenceset A A"
    then obtain x where hX: "X = {(a, b, c, d) | a b c d. a \<in> A \<and> b \<in> A \<and> c \<in> A \<and> d \<in> A \<and> 
      additive_quadruple a b c d \<and> a \<ominus> c = x \<and> d \<ominus> b = x}" and "x \<in> differenceset A A" by blast
    show "finite X" using hX hA finite_subset finite_cartesian_product 
      by (smt (verit, best) mem_Collect_eq mem_Sigma_iff rev_finite_subset subrelI) (*slow*)
  qed
  have "(\<Sum>d\<in>differenceset A A. (f_diff d A)\<^sup>2) = card (\<Union> ((\<lambda> x. {(a, b, c, d) | a b c d. a \<in> A \<and>
    b \<in> A \<and> c \<in> A \<and> d \<in> A \<and> additive_quadruple a b c d \<and> a \<ominus> c = x \<and> d \<ominus> b = x}) ` (differenceset A A)))"
    using f_diff_card_eq hAG sum_card_image[of "differenceset A A" "(\<lambda>x. {(a, b, c, d) |a b c d. 
      a \<in> A \<and> b \<in> A \<and> c \<in> A \<and> d \<in> A \<and> additive_quadruple a b c d \<and> a \<ominus> c = x \<and> d \<ominus> b = x})"] 
      pairwise_disjoint_diff card_Union_disjoint[of "(\<lambda> x. {(a, b, c, d) | a b c d. a \<in> A \<and> 
      b \<in> A \<and> c \<in> A \<and> d \<in> A \<and> additive_quadruple a b c d \<and> a \<ominus> c = x \<and> d \<ominus> b = x}) ` 
      (differenceset A A)"] fin pairwise_disjnt_quadruple_diff hA finite_minusset finite_sumset by auto
  thus ?thesis using quadruple_diff_Union_eq by auto
qed


lemma f_diff_card_quadruple_set_additive_energy: assumes "A \<subseteq> G" and "finite A"
  shows "(\<Sum> d \<in> differenceset A A. (f_diff d A)^2) = additive_energy A * (card A)^3"
  using assms f_diff_card_quadruple_set additive_energy_def by force

definition popular_diff:: "'a \<Rightarrow> real \<Rightarrow> 'a set \<Rightarrow> bool" where
  "popular_diff d \<theta> A  \<equiv> f_diff d A \<ge> \<theta> * of_real (card A)"

definition popular_diff_set:: "real \<Rightarrow> 'a set \<Rightarrow> 'a set" where
  "popular_diff_set \<theta> A \<equiv> {d \<in> differenceset A A. popular_diff d \<theta> A}"

end
end