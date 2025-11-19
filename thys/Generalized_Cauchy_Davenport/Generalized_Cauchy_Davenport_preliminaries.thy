section\<open>Preliminaries on well-orderings, groups, and sumsets\<close>

(*
  Session: Generalized_Cauchy_Davenport
  Title: Generalized_Cauchy_Davenport_preliminaries.thy
  Authors: Mantas Bakšys
  Affiliation: University of Cambridge
  Date: April 2023.
*)


theory Generalized_Cauchy_Davenport_preliminaries
  imports 
    Complex_Main
    "Jacobson_Basic_Algebra.Group_Theory" 
    "HOL-Library.Extended_Nat"

begin

subsection\<open>Well-ordering lemmas\<close>

lemma wf_prod_lex_fibers_inter: 
  fixes r :: "('a \<times> 'a) set" and s :: "('b \<times> 'b) set" and f :: "'c \<Rightarrow> 'a" and g :: "'c \<Rightarrow> 'b" and
  t :: "('c \<times> 'c) set"
  assumes h1: "wf ((inv_image r f) \<inter> t)" and
  h2: "\<And> a. a \<in> range f \<Longrightarrow> wf (({x. f x = a} \<times> {x. f x = a} \<inter> (inv_image s g)) \<inter> t)" and
  h3: "trans t"
  shows "wf ((inv_image (r <*lex*> s) (\<lambda> c. (f c, g c))) \<inter> t)"
proof-
  have h4: "(\<Union> a \<in> range f. ({x. f x = a} \<times> {x. f x = a} \<inter> (inv_image s g)) \<inter> t) = 
    (\<Union> a \<in> range f. ({x. f x = a} \<times> {x. f x = a} \<inter> (inv_image s g))) \<inter> t" by blast 
  have "(inv_image (r <*lex*> s) (\<lambda> c. (f c, g c))) \<inter> t = (inv_image r f \<inter> t) \<union>
    (\<Union> a \<in> range f. {x. f x = a} \<times> {x. f x = a} \<inter> (inv_image s g) \<inter> t)"
  proof
    show "inv_image (r <*lex*> s) (\<lambda>c. (f c, g c)) \<inter> t
    \<subseteq> inv_image r f \<inter> t \<union> (\<Union>a\<in>range f. {x. f x = a} \<times> {x. f x = a} \<inter> inv_image s g \<inter> t)"
    proof
      fix y assume hy: "y \<in> inv_image (r <*lex*> s) (\<lambda>c. (f c, g c)) \<inter> t"
      then obtain a b where hx: "y = (a, b)" and "(f a, f b) \<in> r \<or> (f a = f b \<and> (g a, g b) \<in> s)"
        using in_inv_image in_lex_prod Int_iff SigmaE UNIV_Times_UNIV inf_top_right by (smt (z3))
      then show "y \<in> inv_image r f \<inter> t \<union> (\<Union>a\<in>range f. {x. f x = a} \<times> {x. f x = a} \<inter> inv_image s g \<inter> t)" 
        using hy by auto
    qed
    show "inv_image r f \<inter> t \<union> (\<Union>a\<in>range f. {x. f x = a} \<times> {x. f x = a} \<inter> inv_image s g \<inter> t) \<subseteq> 
      inv_image (r <*lex*> s) (\<lambda>c. (f c, g c)) \<inter> t" using Int_iff SUP_le_iff SigmaD1 SigmaD2 
      in_inv_image in_lex_prod mem_Collect_eq subrelI by force
  qed
  moreover have "((inv_image r f) \<inter> t) O
    (\<Union> a \<in> range f. ({x. f x = a} \<times> {x. f x = a} \<inter> (inv_image s g)) \<inter> t) \<subseteq> (inv_image r f) \<inter> t"
   using h3 trans_O_subset by fastforce
  moreover have "wf (\<Union> a \<in> range f. {x. f x = a} \<times> {x. f x = a} \<inter> (inv_image s g) \<inter> t)"
    apply(rule wf_UN, auto simp add: h2)
    done
  ultimately show "wf (inv_image (r <*lex*> s) (\<lambda> c. (f c, g c)) \<inter> t)" 
    using wf_union_compatible[OF h1] by fastforce
qed

lemma wf_prod_lex_fibers: 
  fixes r :: "('a \<times> 'a) set" and s :: "('b \<times> 'b) set" and f :: "'c \<Rightarrow> 'a" and g :: "'c \<Rightarrow> 'b"
  assumes h1: "wf (inv_image r f)" and
  h2: "\<And> a. a \<in> range f \<Longrightarrow> wf ({x. f x = a} \<times> {x. f x = a} \<inter> (inv_image s g))"
  shows "wf (inv_image (r <*lex*> s) (\<lambda> c. (f c, g c)))"
  using assms trans_def wf_prod_lex_fibers_inter[of r f UNIV s g] inf_top_right
  by (metis (mono_tags, lifting) iso_tuple_UNIV_I)

context monoid

begin

subsection\<open>Pointwise set multiplication in a monoid: definition and key lemmas\<close>

inductive_set smul :: "'a set \<Rightarrow> 'a set \<Rightarrow> 'a set" for A B 
  where
    smulI[intro]: "\<lbrakk>a \<in> A; a \<in> M; b \<in> B; b \<in> M\<rbrakk> \<Longrightarrow> a \<cdot> b \<in> smul A B"

syntax "smul" ::  "'a set \<Rightarrow> 'a set \<Rightarrow> 'a set" ("(_ \<cdots> _)")

lemma smul_eq: "smul A B = {c. \<exists>a \<in> A \<inter> M. \<exists>b \<in> B \<inter> M. c = a \<cdot> b}"
  by (auto simp: smul.simps elim!: smul.cases)

lemma smul: "smul A B = (\<Union>a \<in> A \<inter> M. \<Union>b \<in> B \<inter> M. {a \<cdot> b})"
  by (auto simp: smul_eq)

lemma smul_subset_carrier: "smul A B \<subseteq> M"
  by (auto simp: smul_eq)

lemma smul_Int_carrier [simp]: "smul A B \<inter> M = smul A B"
  by (simp add: Int_absorb2 smul_subset_carrier)

lemma smul_mono: "\<lbrakk>A' \<subseteq> A; B' \<subseteq> B\<rbrakk> \<Longrightarrow> smul A' B' \<subseteq> smul A B"
  by (auto simp: smul_eq)

lemma smul_insert1: "NO_MATCH {} A \<Longrightarrow> smul (insert x A) B = smul {x} B \<union> smul A B"
  by (auto simp: smul_eq)

lemma smul_insert2: "NO_MATCH {} B \<Longrightarrow> smul A (insert x B) = smul A {x} \<union> smul A B"
  by (auto simp: smul_eq)

lemma smul_subset_Un1: "smul (A \<union> A') B = smul A B \<union> smul A' B"
  by (auto simp: smul_eq)

lemma smul_subset_Un2: "smul A (B \<union> B') = smul A B \<union> smul A B'"
  by (auto simp: smul_eq)

lemma smul_subset_Union1: "smul (\<Union> A) B = (\<Union> a \<in> A. smul a B)"
  by (auto simp: smul_eq)

lemma smul_subset_Union2: "smul A (\<Union> B) = (\<Union> b \<in> B. smul A b)"
  by (auto simp: smul_eq)

lemma smul_subset_insert: "smul A B \<subseteq> smul A (insert x B)" "smul A B \<subseteq> smul (insert x A) B"
  by (auto simp: smul_eq)

lemma smul_subset_Un: "smul A B \<subseteq> smul A (B\<union>C)" "smul A B \<subseteq> smul (A\<union>C) B"
  by (auto simp: smul_eq)

lemma smul_empty [simp]: "smul A {} = {}" "smul {} A = {}"
  by (auto simp: smul_eq)

lemma smul_empty':
  assumes "A \<inter> M = {}"
  shows "smul B A = {}" "smul A B = {}"
  using assms by (auto simp: smul_eq)

lemma smul_is_empty_iff [simp]: "smul A B = {} \<longleftrightarrow> A \<inter> M = {} \<or> B \<inter> M = {}"
  by (auto simp: smul_eq)

lemma smul_D [simp]: "smul A {\<one>} = A \<inter> M" "smul {\<one>} A = A \<inter> M"
  by (auto simp: smul_eq)

lemma smul_Int_carrier_eq [simp]: "smul A (B \<inter> M) = smul A B" "smul (A \<inter> M) B = smul A B"
  by (auto simp: smul_eq)

lemma smul_assoc:
  shows "smul (smul A B) C = smul A (smul B C)"
  by (fastforce simp add: smul_eq associative Bex_def)

lemma finite_smul:
  assumes "finite A" "finite B"  shows "finite (smul A B)"
  using assms by (auto simp: smul_eq)

lemma finite_smul':
  assumes "finite (A \<inter> M)" "finite (B \<inter> M)"
    shows "finite (smul A B)"
  using assms by (auto simp: smul_eq)

subsection \<open>Exponentiation in a monoid: definitions and lemmas\<close>
primrec power :: "'a \<Rightarrow> nat \<Rightarrow> 'a" (infix "^" 100)
  where
  power0: "power g 0 = \<one>"
| power_suc: "power g (Suc n) = power g n \<cdot> g"

lemma power_one:
  assumes "g \<in> M"
  shows "power g 1 = g" using power_def power0 assms by simp

lemma power_mem_carrier:
  fixes n
  assumes "g \<in> M"
  shows "g ^ n \<in> M"
  apply (induction n, auto simp add: assms power_def)
  done

lemma power_mult:
  assumes "g \<in> M"
  shows "g ^ n \<cdot> g ^ m = g ^ (n + m)"
proof(induction m)
  case 0
  then show ?case using assms power0 right_unit power_mem_carrier by simp
next
  case (Suc m)
  assume "g ^ n \<cdot> g ^ m = g ^ (n + m)"
  then show ?case using power_def by (smt (verit) add_Suc_right assms associative 
    power_mem_carrier power_suc)
qed

lemma mult_inverse_power:
  assumes "g \<in> M" and "invertible g"
  shows "g ^ n \<cdot> ((inverse g) ^ n) = \<one>"
proof(induction n)
  case 0
  then show ?case using power_0 by auto
next
  case (Suc n)
  assume hind: "g ^ n \<cdot> local.inverse g ^ n = \<one>"
  then have "g ^ Suc n \<cdot> inverse g ^ Suc n = (g \<cdot> g ^ n) \<cdot> (inverse g ^ n \<cdot> inverse g)" 
    using power_def power_mult assms by (smt (z3) add.commute invertible_inverse_closed 
    invertible_right_inverse left_unit monoid.associative monoid_axioms power_mem_carrier power_suc)
  then show ?case using associative power_mem_carrier assms hind by (smt (verit, del_insts) 
    composition_closed invertible_inverse_closed invertible_right_inverse right_unit)
qed

lemma inverse_mult_power:
  assumes "g \<in> M" and "invertible g"
  shows "((inverse g) ^ n) \<cdot> g ^ n = \<one>" using assms by (metis invertible_inverse_closed 
    invertible_inverse_inverse invertible_inverse_invertible mult_inverse_power)

lemma inverse_mult_power_eq:
  assumes "g \<in> M" and "invertible g"
  shows "inverse (g ^ n) = (inverse g) ^ n"
  using assms inverse_equality by (simp add: inverse_mult_power mult_inverse_power power_mem_carrier)

definition power_int :: "'a \<Rightarrow> int \<Rightarrow> 'a" (infixr "powi" 80) where
  "power_int g n = (if n \<ge> 0 then g ^ (nat n) else (inverse g) ^ (nat (-n)))"

definition nat_powers :: "'a \<Rightarrow> 'a set" where "nat_powers g = ((\<lambda> n. g ^ n) ` UNIV)"

lemma nat_powers_eq_Union: "nat_powers g = (\<Union> n. {g ^ n})" using nat_powers_def by auto

definition powers :: "'a \<Rightarrow> 'a set" where "powers g = ((\<lambda> n. g powi n) ` UNIV)"

lemma nat_powers_subset:
  "nat_powers g \<subseteq> powers g"
proof
  fix x assume "x \<in> nat_powers g"
  then obtain n where "x = g ^ n" and "nat n = n" using nat_powers_def by auto
  then show "x \<in> powers g" using powers_def power_int_def 
    by (metis UNIV_I image_iff of_nat_0_le_iff)
qed

lemma inverse_nat_powers_subset:
  "nat_powers (inverse g) \<subseteq> powers g"
proof
  fix x assume "x \<in> nat_powers (inverse g)"
  then obtain n where hx: "x = (inverse g) ^ n" using nat_powers_def by blast
  then show "x \<in> powers g"
  proof(cases "n = 0")
    case True
    then show ?thesis using hx power0 powers_def
      by (metis nat_powers_def nat_powers_subset rangeI subsetD)
  next
    case False
    then have hpos: "\<not> (- int n) \<ge> 0" by auto
    then have "x = g powi (- int n)" using hx hpos power_int_def by simp
    then show ?thesis using powers_def by auto
  qed
qed

lemma powers_eq_union_nat_powers:
  "powers g = nat_powers g \<union> nat_powers (inverse g)"
proof
  show "powers g \<subseteq> nat_powers g \<union> nat_powers (local.inverse g)"
    using powers_def nat_powers_def power_int_def by auto
next 
  show "nat_powers g \<union> nat_powers (inverse g) \<subseteq> powers g"
    by (simp add: inverse_nat_powers_subset nat_powers_subset)
qed

lemma one_mem_nat_powers: "\<one> \<in> nat_powers g"
  using rangeI power0 nat_powers_def by metis

lemma nat_powers_subset_carrier:
  assumes "g \<in> M"
  shows "nat_powers g \<subseteq> M"
  using nat_powers_def power_mem_carrier assms by auto

lemma nat_powers_mult_closed:
  assumes "g \<in> M"
  shows "\<And> x y. x \<in> nat_powers g \<Longrightarrow> y \<in> nat_powers g \<Longrightarrow> x \<cdot> y \<in> nat_powers g"
  using nat_powers_def power_mult assms by auto

lemma nat_powers_inv_mult:
  assumes "g \<in> M" and "invertible g"
  shows "\<And> x y. x \<in> nat_powers g \<Longrightarrow> y \<in> nat_powers (inverse g) \<Longrightarrow> x \<cdot> y \<in> powers g"
proof-
  fix x y assume "x \<in> nat_powers g" and "y \<in> nat_powers (inverse g)"
  then obtain n m where hx: "x = g ^ n" and hy: "y = (inverse g) ^ m" using nat_powers_def by blast
  show "x \<cdot> y \<in> powers g"
  proof(cases "n \<ge> m")
    case True
    then obtain k where "n = k + m" using add.commute le_Suc_ex by blast
    then have "g ^ n \<cdot> (inverse g) ^ m = g ^ k" using mult_inverse_power assms associative 
      by (smt (verit) invertible_inverse_closed local.power_mult power_mem_carrier right_unit)
    then show ?thesis using hx hy powers_eq_union_nat_powers nat_powers_def by auto
  next
    case False
    then obtain k where "m = n + k" by (metis leI less_imp_add_positive)
    then have "g ^ n \<cdot> (inverse g) ^ m = (inverse g) ^ k" using inverse_mult_power assms associative 
      by (smt (verit) left_unit local.power_mult monoid.invertible_inverse_closed monoid_axioms 
        mult_inverse_power power_mem_carrier)
    then show ?thesis using hx hy powers_eq_union_nat_powers nat_powers_def by auto
  qed
qed

lemma inv_nat_powers_mult:
  assumes "g \<in> M" and "invertible g"
  shows "\<And> x y. x \<in> nat_powers (inverse g) \<Longrightarrow> y \<in> nat_powers g \<Longrightarrow> x \<cdot> y \<in> powers g"
  by (metis assms invertible_inverse_closed invertible_inverse_inverse invertible_inverse_invertible
    nat_powers_inv_mult powers_eq_union_nat_powers sup_commute)

lemma powers_mult_closed:
  assumes "g \<in> M" and "invertible g"
  shows "\<And> x y. x \<in> powers g \<Longrightarrow> y \<in> powers g \<Longrightarrow> x \<cdot> y \<in> powers g"
  using powers_eq_union_nat_powers assms 
    nat_powers_mult_closed nat_powers_inv_mult inv_nat_powers_mult by fastforce

lemma nat_powers_submonoid:
  assumes "g \<in> M"
  shows "submonoid (nat_powers g) M (\<cdot>) \<one>"
  apply(unfold_locales)
  apply(auto simp add: assms nat_powers_mult_closed one_mem_nat_powers nat_powers_subset_carrier)
  done

lemma nat_powers_monoid:
  assumes "g \<in> M"
  shows "Group_Theory.monoid (nat_powers g) (\<cdot>) \<one>"
  using nat_powers_submonoid assms by (smt (verit) monoid.intro associative left_unit 
      one_mem_nat_powers nat_powers_mult_closed right_unit submonoid.sub)

lemma powers_submonoid:
  assumes "g \<in> M" and "invertible g"
  shows "submonoid (powers g) M (\<cdot>) \<one>"
proof
  show "powers g \<subseteq> M" using powers_eq_union_nat_powers nat_powers_subset_carrier assms by auto
next
  show "\<And>a b. a \<in> powers g \<Longrightarrow> b \<in> powers g \<Longrightarrow> a \<cdot> b \<in> powers g" 
    using powers_mult_closed assms by auto
next
  show "\<one> \<in> powers g" using powers_eq_union_nat_powers one_mem_nat_powers by auto
qed

lemma powers_monoid:
  assumes "g \<in> M" and "invertible g"
  shows "Group_Theory.monoid (powers g) (\<cdot>) \<one>"
  by (smt (verit) monoid.intro Un_iff assms associative in_mono invertible_inverse_closed 
      monoid.left_unit monoid.right_unit nat_powers_monoid powers_eq_union_nat_powers 
      powers_mult_closed powers_submonoid submonoid.sub_unit_closed submonoid.subset)

lemma mem_nat_powers_invertible:
  assumes "g \<in> M" and "invertible g" and "u \<in> nat_powers g"
  shows "monoid.invertible (powers g) (\<cdot>) \<one> u"
proof-
  obtain n where hu: "u = g ^ n" using assms nat_powers_def by blast
  then have "inverse u \<in> powers g" using assms inverse_mult_power_eq 
      powers_eq_union_nat_powers nat_powers_def by auto
  then show ?thesis using hu assms by (metis in_mono inverse_mult_power inverse_mult_power_eq 
    monoid.invertibleI monoid.nat_powers_subset monoid.powers_monoid monoid_axioms mult_inverse_power)
qed

lemma mem_nat_inv_powers_invertible:
  assumes "g \<in> M" and "invertible g" and "u \<in> nat_powers (inverse g)"
  shows "monoid.invertible (powers g) (\<cdot>) \<one> u"
  using assms by (metis inf_sup_aci(5) invertible_inverse_closed invertible_inverse_inverse 
    invertible_inverse_invertible mem_nat_powers_invertible powers_eq_union_nat_powers)

lemma powers_group:
  assumes "g \<in> M" and "invertible g"
  shows "Group_Theory.group (powers g) (\<cdot>) \<one>"
proof-
  have "\<And>u. u \<in> powers g \<Longrightarrow> monoid.invertible (powers g) (\<cdot>) \<one> u" using assms 
    mem_nat_inv_powers_invertible mem_nat_powers_invertible powers_eq_union_nat_powers by auto
  then show ?thesis using group_def Group_Theory.group_axioms_def assms powers_monoid by metis
qed

lemma nat_powers_ne_one:
  assumes "g \<in> M" and "g \<noteq> \<one>"
  shows "nat_powers g \<noteq> {\<one>}"
proof-
  have "g \<in> nat_powers g" using power_one nat_powers_def assms rangeI by metis
  then show ?thesis using assms by blast
qed

lemma powers_ne_one: 
  assumes "g \<in> M" and "g \<noteq> \<one>"
  shows "powers g \<noteq> {\<one>}" using assms nat_powers_ne_one 
  by (metis all_not_in_conv nat_powers_subset one_mem_nat_powers subset_singleton_iff)

end

context group

begin

lemma powers_subgroup:
  assumes "g \<in> G"
  shows "subgroup (powers g) G (\<cdot>) \<one>" 
  by (simp add: assms powers_group powers_submonoid subgroup.intro)

end

context monoid

begin

subsection\<open>Definition of the order of an element in a monoid\<close>
definition order 
  where "order g = (if (\<exists> n. n > 0 \<and> g ^ n = \<one>) then Min {n. g ^ n = \<one> \<and> n > 0} else \<infinity>)"

definition min_order where "min_order = Min ((order ` M) - {0})"

end 

subsection\<open>Sumset scalar multiplication cardinality lemmas\<close>
context group

begin

lemma card_smul_singleton_right_eq:
  assumes "finite A" shows "card (smul A {a}) = (if a \<in> G then card (A \<inter> G) else 0)"
proof (cases "a \<in> G")
  case True
  then have "smul A {a} = (\<lambda>x. x \<cdot> a) ` (A \<inter> G)"
    by (auto simp: smul_eq)
  moreover have "inj_on (\<lambda>x. x \<cdot> a) (A \<inter> G)"
    by (auto simp: inj_on_def True)
  ultimately show ?thesis
    by (metis True card_image)
qed (auto simp: smul_eq)

lemma card_smul_singleton_left_eq:
  assumes "finite A" shows "card (smul {a} A) = (if a \<in> G then card (A \<inter> G) else 0)"
proof (cases "a \<in> G")
  case True
  then have "smul {a} A = (\<lambda>x. a \<cdot> x) ` (A \<inter> G)"
    by (auto simp: smul_eq)
  moreover have "inj_on (\<lambda>x. a \<cdot> x) (A \<inter> G)"
    by (auto simp: inj_on_def True)
  ultimately show ?thesis
    by (metis True card_image)
qed (auto simp: smul_eq)

lemma card_smul_sing_right_le:
  assumes "finite A" shows "card (smul A {a}) \<le> card A"
  by (simp add: assms card_mono card_smul_singleton_right_eq)

lemma card_smul_sing_left_le:
  assumes "finite A" shows "card (smul {a} A) \<le> card A"
  by (simp add: assms card_mono card_smul_singleton_left_eq)

lemma card_le_smul_right:
  assumes A: "finite A" "a \<in> A" "a \<in> G"
    and   B: "finite B" "B \<subseteq> G"
  shows "card B \<le> card (smul A B)"
proof -
  have "B \<subseteq> (\<lambda> x.  (inverse a) \<cdot> x) ` smul A B"
    using A B
    apply (clarsimp simp: smul image_iff)
    using Int_absorb2 Int_iff invertible invertible_left_inverse2 by metis
  with A B show ?thesis
    by (meson  finite_smul surj_card_le)
qed

lemma card_le_smul_left:
  assumes A: "finite A" "b \<in> B" "b \<in> G"
    and   B: "finite B" "A \<subseteq> G"
  shows "card A \<le> card (smul A B)"
proof -
  have "A \<subseteq> (\<lambda> x. x \<cdot> (inverse b)) ` smul A B"
    using A B
    apply (clarsimp simp: smul image_iff associative)     
    using Int_absorb2 Int_iff invertible invertible_right_inverse assms(5) by (metis right_unit)
  with A B show ?thesis
    by (meson  finite_smul surj_card_le)
qed


lemma infinite_smul_right:
  assumes "A \<inter> G \<noteq> {}" and "infinite (B \<inter> G)"
  shows "infinite (A \<cdots> B)" 
proof
  assume hfin: "finite (smul A B)"
  obtain a where ha: "a \<in> A \<inter> G" using assms by auto
  then have "finite (smul {a} B)" using hfin by (metis Int_Un_eq(1) finite_subset insert_is_Un 
    mk_disjoint_insert smul_subset_Un(2))
  moreover have "B \<inter> G \<subseteq> (\<lambda> x. inverse a \<cdot> x) ` smul {a} B" 
  proof
    fix b assume hb: "b \<in> B \<inter> G"
    then have "b = inverse a \<cdot> (a \<cdot> b)" using associative ha by (simp add: invertible_left_inverse2)
    then show "b \<in> (\<lambda> x. inverse a \<cdot> x) ` smul {a} B" using smul.simps hb ha by blast
  qed
  ultimately show False using assms using finite_surj by blast
qed

lemma infinite_smul_left:
  assumes "B \<inter> G \<noteq> {}" and "infinite (A \<inter> G)"
  shows "infinite (A \<cdots> B)"
proof
  assume hfin: "finite (smul A B)"
  obtain b where hb: "b \<in> B \<inter> G" using assms by auto
  then have "finite (smul A {b})" using hfin by (simp add: rev_finite_subset smul_mono)
  moreover have "A \<inter> G \<subseteq> (\<lambda> x. x \<cdot> inverse b) ` smul A {b}"
  proof
    fix a assume ha: "a \<in> A \<inter> G"
    then have "a = (a \<cdot> b) \<cdot> inverse b" using associative hb
      by (metis IntD2 invertible invertible_inverse_closed invertible_right_inverse right_unit)
    then show "a \<in> (\<lambda> x. x \<cdot> inverse b) ` smul A {b}" using smul.simps hb ha by blast
  qed
  ultimately show False using assms using finite_surj by blast
qed

subsection\<open>Pointwise set multiplication in a group: auxiliary lemmas\<close>
lemma set_inverse_composition_commute:
  assumes "X \<subseteq> G" and "Y \<subseteq> G"
  shows "inverse ` (X \<cdots> Y) = (inverse ` Y) \<cdots> (inverse ` X)"
proof
  show "inverse ` (X \<cdots> Y) \<subseteq> (inverse ` Y) \<cdots> (inverse ` X)"
  proof
    fix z assume "z \<in> inverse ` (X \<cdots> Y)"
    then obtain x y where "z = inverse (x \<cdot> y)" and "x \<in> X" and "y \<in> Y" 
      by (smt (verit) image_iff smul.cases)
    then show "z \<in> (inverse ` Y) \<cdots> (inverse ` X)" 
      using inverse_composition_commute assms 
      by (smt (verit) image_eqI in_mono inverse_equality invertible invertibleE smul.simps)
  qed
  show "(inverse ` Y) \<cdots> (inverse ` X) \<subseteq> inverse ` (X \<cdots> Y)"
  proof
    fix z assume "z \<in> (inverse ` Y) \<cdots> (inverse ` X)"
    then obtain x y where "x \<in> X" and "y \<in> Y" and "z = inverse y \<cdot> inverse x" 
      using smul.cases image_iff by blast
    then show "z \<in> inverse ` (X \<cdots> Y)" using inverse_composition_commute assms smul.simps
      by (smt (verit) image_iff in_mono invertible)
  qed
qed

lemma smul_singleton_eq_contains_nat_powers:
  fixes n :: nat
  assumes "X \<subseteq> G" and "g \<in> G" and "X \<cdots> {g} = X"
  shows "X \<cdots> {g ^ n} = X"
proof(induction n)
  case 0
  then show ?case using power_def assms by auto
next
  case (Suc n)
  assume hXn: "X \<cdots> {g ^ n} = X"
  moreover have "X \<cdots> {g ^ Suc n} = (X \<cdots> {g ^ n}) \<cdots> {g}"
  proof
    show "X \<cdots> {g ^ Suc n} \<subseteq> (X \<cdots> {g ^ n}) \<cdots> {g}"
    proof
      fix z assume "z \<in> X \<cdots> {g ^ Suc n}"
      then obtain x where "z = x \<cdot> (g ^ Suc n)" and hx: "x \<in> X"  using smul.simps by auto
      then have "z = (x \<cdot> g ^ n) \<cdot> g" using assms associative by (simp add: in_mono power_mem_carrier) 
      then show "z \<in> (X \<cdots> {g ^ n}) \<cdots> {g}" using hx assms 
        by (simp add: power_mem_carrier smul.smulI subsetD)
    qed
  next
    show "(X \<cdots> {g ^ n}) \<cdots> {g} \<subseteq> X \<cdots> {g ^ Suc n}"
    proof
      fix z assume "z \<in> (X \<cdots> {g ^ n}) \<cdots> {g}"
      then obtain x where "z = (x \<cdot> g ^ n) \<cdot> g" and hx: "x \<in> X" using smul.simps by auto
      then have "z = x \<cdot> g ^ Suc n" 
        using power_def associative power_mem_carrier assms by (simp add: in_mono)
      then show "z \<in> X \<cdots> {g ^ Suc n}" using hx assms 
        by (simp add: power_mem_carrier smul.smulI subsetD)
    qed
  qed
  ultimately show ?case using assms by simp
qed

lemma smul_singleton_eq_contains_inverse_nat_powers:
  fixes n :: nat
  assumes "X \<subseteq> G" and "g \<in> G" and "X \<cdots> {g} = X"
  shows "X \<cdots> {(inverse g) ^ n} = X"
proof-
  have "(X \<cdots> {g}) \<cdots> {inverse g} = X"
  proof
    show "(X \<cdots> {g}) \<cdots> {inverse g} \<subseteq> X"
    proof
      fix z assume "z \<in> (X \<cdots> {g}) \<cdots> {inverse g}"
      then obtain y x where "y \<in> X \<cdots> {g}" and "z = y \<cdot> inverse g" and "x \<in> X"  and "y = x \<cdot> g" 
        using assms smul.simps by (metis empty_iff insert_iff)
      then show "z \<in> X" using assms by (simp add: associative subset_eq)
    qed
  next
    show "X \<subseteq> (X \<cdots> {g}) \<cdots> {inverse g}" 
    proof
      fix x assume hx: "x \<in> X"
      then have "x = x \<cdot> g \<cdot> inverse g" using assms by (simp add: associative subset_iff)
      then show "x \<in> (X \<cdots> {g}) \<cdots> {inverse g}" using assms smul.simps hx by auto
    qed
  qed
  then have "X \<cdots> {inverse g} = X" using assms by auto
  then show ?thesis using assms by (simp add: smul_singleton_eq_contains_nat_powers)
qed

lemma smul_singleton_eq_contains_powers:
  fixes n :: nat
  assumes "X \<subseteq> G" and "g \<in> G" and "X \<cdots> {g} = X"
  shows "X \<cdots> (powers g) = X" using powers_eq_union_nat_powers smul_subset_Union2 
    nat_powers_eq_Union smul_singleton_eq_contains_nat_powers 
    smul_singleton_eq_contains_inverse_nat_powers assms smul_subset_Un2 by auto

end

subsection\<open>$ecard$ -- extended definition of cardinality of a set\<close>

text\<open>$ecard$ -- definition of a cardinality of a set taking values in $enat$ -- extended natural numbers, defined to be $\infty$ for infinite sets\<close>
definition ecard where "ecard A = (if finite A then card A else \<infinity>)"

lemma ecard_eq_card_finite:
  assumes "finite A"
  shows "ecard A = card A" 
  using assms ecard_def by metis


context monoid
begin

text\<open>$orderOf$ -- abbreviation for the order of a monoid \<close>
abbreviation orderOf where "orderOf == ecard"


end

end



