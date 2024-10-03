section \<open>Executable Structures\<close>

theory Finite_Fields_Indexed_Algebra_Code
  imports "HOL-Algebra.Ring" "HOL-Algebra.Coset"
begin

text \<open>In the following, we introduce records for executable operations for algebraic structures,
which can be used for code-generation and evaluation. These are then shown to be equivalent to the
(not-necessarily constructive) definitions using \<^verbatim>\<open>HOL-Algebra\<close>. A more direct approach, i.e.,
instantiating the structures in the framework with effective operations fails. For example the
structure records represent the domain of the algebraic structure as a set, which implies the
evaluation of @{term "(\<oplus>\<^bsub>residue_ring (10^100)\<^esub>)"} requires the construction of
@{term "{0..10^100-1}"}. This is technically constructive but very impractical.
Moreover, the additive/multiplicative inverse is defined non-constructively using the
description operator \<^verbatim>\<open>THE\<close> in \<^verbatim>\<open>HOL-Algebra\<close>.

The above could be avoided, if it were possible to introduce code equations conditionally, e.g.,
for example for @{term "a_inv (residue_ring n) x y"} (if @{term "x y"} are in the carrier of the
structure, but this does not seem to be possible.

Note that, the algebraic structures defined in \<^verbatim>\<open>HOL-Computational_Algebra\<close> are type-based,
which prevents using them in some algorithmic settings. For example, choosing an
irreducible polynomial dynamically and performing operations in the factoring ring with respect to
it is not possible in the type-based approach.\<close>

record 'a idx_ring =
  idx_pred :: "'a \<Rightarrow> bool"
  idx_uminus :: "'a \<Rightarrow> 'a"
  idx_plus :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"
  idx_udivide :: "'a \<Rightarrow> 'a"
  idx_mult :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"
  idx_zero :: "'a"
  idx_one :: "'a"

record 'a idx_ring_enum = "'a idx_ring" +
  idx_size :: nat
  idx_enum :: "nat \<Rightarrow> 'a"
  idx_enum_inv :: "'a \<Rightarrow> nat"

fun idx_pow :: "('a,'b) idx_ring_scheme  \<Rightarrow> 'a \<Rightarrow> nat \<Rightarrow> 'a" where
  "idx_pow E x 0 = idx_one E" |
  "idx_pow E x (Suc n) = idx_mult E (idx_pow E x n) x"

open_bundle index_algebra_syntax
begin
notation idx_zero (\<open>0\<^sub>C\<index>\<close>)
notation idx_one (\<open>1\<^sub>C\<index>\<close>)
notation idx_plus (infixl \<open>+\<^sub>C\<index>\<close> 65)
notation idx_mult (infixl \<open>*\<^sub>C\<index>\<close> 70)
notation idx_uminus (\<open>-\<^sub>C\<index> _\<close> [81] 80)
notation idx_udivide (\<open>_ \<inverse>\<^sub>C\<index>\<close> [81] 80)
notation idx_pow  (infixr \<open>^\<^sub>C\<index>\<close> 75)
end

bundle no_index_algebra_syntax
begin
no_notation idx_zero (\<open>0\<^sub>C\<index>\<close>)
no_notation idx_one (\<open>1\<^sub>C\<index>\<close>)
no_notation idx_plus (infixl \<open>+\<^sub>C\<index>\<close> 65)
no_notation idx_mult (infixl \<open>*\<^sub>C\<index>\<close> 70)
no_notation idx_uminus (\<open>-\<^sub>C\<index> _\<close> [81] 80)
no_notation idx_udivide (\<open>_ \<inverse>\<^sub>C\<index>\<close> [81] 80)
no_notation idx_pow  (infixr \<open>^\<^sub>C\<index>\<close> 75)
end

definition ring_of :: "('a,'b) idx_ring_scheme \<Rightarrow> 'a ring"
  where "ring_of A = \<lparr>
    carrier = {x. idx_pred A x},
    mult = (\<lambda> x y. x *\<^sub>C\<^bsub>A\<^esub> y),
    one = 1\<^sub>C\<^bsub>A\<^esub>,
    zero = 0\<^sub>C\<^bsub>A\<^esub>,
    add = (\<lambda> x y. x +\<^sub>C\<^bsub>A\<^esub> y) \<rparr>"

definition ring\<^sub>C where
  "ring\<^sub>C A = (ring (ring_of A) \<and> (\<forall>x. idx_pred A x \<longrightarrow> -\<^sub>C\<^bsub>A\<^esub> x = \<ominus>\<^bsub>ring_of A\<^esub> x) \<and>
    (\<forall>x. x \<in> Units (ring_of A) \<longrightarrow> x \<inverse>\<^sub>C\<^bsub>A\<^esub> = inv\<^bsub>ring_of A\<^esub> x))"

lemma ring_cD_aux:
  "x ^\<^sub>C\<^bsub>A\<^esub> n = x [^]\<^bsub>ring_of A\<^esub> n"
  by (induction n) (auto simp:ring_of_def)

lemma ring_cD:
  assumes "ring\<^sub>C A"
  shows
    "0\<^sub>C\<^bsub>A\<^esub> = \<zero>\<^bsub>ring_of A\<^esub>"
    "1\<^sub>C\<^bsub>A\<^esub> = \<one>\<^bsub>ring_of A\<^esub>"
    "\<And>x y. x *\<^sub>C\<^bsub>A\<^esub> y = x \<otimes>\<^bsub>ring_of A\<^esub> y"
    "\<And>x y. x +\<^sub>C\<^bsub>A\<^esub> y = x \<oplus>\<^bsub>ring_of A\<^esub> y"
    "\<And>x. x \<in> carrier (ring_of A) \<Longrightarrow>  -\<^sub>C\<^bsub>A\<^esub> x = \<ominus>\<^bsub>ring_of A\<^esub> x"
    "\<And>x. x \<in> Units (ring_of A) \<Longrightarrow>  x \<inverse>\<^sub>C\<^bsub>A\<^esub> = inv\<^bsub>ring_of A\<^esub> x"
    "\<And>x. x ^\<^sub>C\<^bsub>A\<^esub> n = x [^]\<^bsub>ring_of A\<^esub> n"
  using assms ring_cD_aux unfolding ring\<^sub>C_def ring_of_def by auto

lemma ring_cI:
  assumes "ring (ring_of A)"
  assumes "\<And>x. x \<in> carrier (ring_of A) \<Longrightarrow>  -\<^sub>C\<^bsub>A\<^esub> x = \<ominus>\<^bsub>ring_of A\<^esub> x"
  assumes "\<And>x. x \<in> Units (ring_of A) \<Longrightarrow>  x\<inverse>\<^sub>C\<^bsub>A\<^esub> = inv\<^bsub>ring_of A\<^esub> x"
  shows "ring\<^sub>C A"
proof -
  have " x \<in> carrier (ring_of A) \<longleftrightarrow> idx_pred A x" for x unfolding ring_of_def by auto
  thus ?thesis using assms unfolding ring\<^sub>C_def by auto
qed

definition cring\<^sub>C where "cring\<^sub>C A = (ring\<^sub>C A \<and> cring (ring_of A))"

lemma cring_cI:
  assumes "cring (ring_of A)"
  assumes "\<And>x. x \<in> carrier (ring_of A) \<Longrightarrow>  -\<^sub>C\<^bsub>A\<^esub> x = \<ominus>\<^bsub>ring_of A\<^esub> x"
  assumes "\<And>x. x \<in> Units (ring_of A) \<Longrightarrow> x\<inverse>\<^sub>C\<^bsub>A\<^esub> = inv\<^bsub>ring_of A\<^esub> x"
  shows "cring\<^sub>C A"
  unfolding cring\<^sub>C_def by (intro ring_cI conjI assms cring.axioms(1))

lemma cring_c_imp_ring: "cring\<^sub>C A \<Longrightarrow> ring\<^sub>C A"
  unfolding cring\<^sub>C_def by simp

lemmas cring_cD = ring_cD[OF cring_c_imp_ring]

definition domain\<^sub>C where "domain\<^sub>C A = (cring\<^sub>C A \<and> domain (ring_of A))"

lemma domain_cI:
  assumes "domain (ring_of A)"
  assumes "\<And>x. x \<in> carrier (ring_of A) \<Longrightarrow>  -\<^sub>C\<^bsub>A\<^esub> x = \<ominus>\<^bsub>ring_of A\<^esub> x"
  assumes "\<And>x. x \<in> Units (ring_of A) \<Longrightarrow> x\<inverse>\<^sub>C\<^bsub>A\<^esub> = inv\<^bsub>ring_of A\<^esub> x"
  shows "domain\<^sub>C A"
  unfolding domain\<^sub>C_def by (intro conjI cring_cI assms domain.axioms(1))

lemma domain_c_imp_ring: "domain\<^sub>C A \<Longrightarrow> ring\<^sub>C A"
  unfolding cring\<^sub>C_def domain\<^sub>C_def by simp

lemmas domain_cD = ring_cD[OF domain_c_imp_ring]

definition field\<^sub>C where "field\<^sub>C A = (domain\<^sub>C A \<and> field (ring_of A))"

lemma field_cI:
  assumes "field (ring_of A)"
  assumes "\<And>x. x \<in> carrier (ring_of A) \<Longrightarrow>  -\<^sub>C\<^bsub>A\<^esub> x = \<ominus>\<^bsub>ring_of A\<^esub> x"
  assumes "\<And>x. x \<in> Units (ring_of A) \<Longrightarrow>  x\<inverse>\<^sub>C\<^bsub>A\<^esub> = inv\<^bsub>ring_of A\<^esub> x"
  shows "field\<^sub>C A"
  unfolding field\<^sub>C_def by (intro conjI domain_cI assms field.axioms(1))

lemma field_c_imp_ring: "field\<^sub>C A \<Longrightarrow> ring\<^sub>C A"
  unfolding field\<^sub>C_def cring\<^sub>C_def domain\<^sub>C_def by simp

lemmas field_cD = ring_cD[OF field_c_imp_ring]

definition enum\<^sub>C where "enum\<^sub>C A = (
  finite (carrier (ring_of A)) \<and>
  idx_size A = order (ring_of A) \<and>
  bij_betw (idx_enum A) {..<order (ring_of A)} (carrier (ring_of A)) \<and>
  (\<forall>x < order (ring_of A). idx_enum_inv A (idx_enum A x) = x))"

lemma enum_cI:
  assumes "finite (carrier (ring_of A))"
  assumes "idx_size A = order (ring_of A)"
  assumes "bij_betw (idx_enum A) {..<order (ring_of A)} (carrier (ring_of A))"
  assumes "\<And>x. x < order (ring_of A) \<Longrightarrow> idx_enum_inv A (idx_enum A x) = x"
  shows "enum\<^sub>C A"
  using assms unfolding enum\<^sub>C_def by auto

lemma enum_cD:
  assumes "enum\<^sub>C R"
  shows "finite (carrier (ring_of R))"
    and "idx_size R = order (ring_of R)"
    and "bij_betw (idx_enum R) {..<order (ring_of R)} (carrier (ring_of R))"
    and "bij_betw (idx_enum_inv R) (carrier (ring_of R)) {..<order (ring_of R)}"
    and "\<And>x. x < order (ring_of R) \<Longrightarrow> idx_enum_inv R (idx_enum R x) = x"
    and "\<And>x. x \<in> carrier (ring_of R) \<Longrightarrow> idx_enum R (idx_enum_inv R x) = x"
  using assms
proof -
  let ?n = "order (ring_of R)"
  have a:"idx_enum_inv R x = the_inv_into {..<?n} (idx_enum R) x"
    if x_carr: "x \<in> carrier (ring_of R)" for x
  proof -
    have "idx_enum R ` {..<order (ring_of R)} = carrier (ring_of R)"
      using assms unfolding bij_betw_def enum\<^sub>C_def by simp
    then obtain y where y_carr: "y \<in> {..< order (ring_of R)}" and x_def: "x = idx_enum R y"
      using x_carr by auto
    have "idx_enum_inv R x = y" using assms y_carr unfolding x_def enum\<^sub>C_def by simp
    also have "... = the_inv_into {..<?n} (idx_enum R) x"
      using assms unfolding bij_betw_def enum\<^sub>C_def unfolding x_def
      by (intro the_inv_into_f_f[symmetric] y_carr) auto
    finally show ?thesis by simp
  qed

  have "bij_betw (the_inv_into {..<?n} (idx_enum R)) (carrier (ring_of R)) {..<?n}"
    using assms unfolding enum\<^sub>C_def by (intro bij_betw_the_inv_into) auto
  thus "bij_betw (idx_enum_inv R) (carrier (ring_of R)) {..<order (ring_of R)}"
    by (subst bij_betw_cong[OF a]) auto
  show "idx_enum R (idx_enum_inv R x) = x" if "x \<in> carrier (ring_of R)" for x
    using that assms unfolding a[OF that] enum\<^sub>C_def bij_betw_def by (intro f_the_inv_into_f) auto
qed (use assms enum\<^sub>C_def in auto)

end