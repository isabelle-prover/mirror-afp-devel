theory Representation

imports Stone_Relation_Algebras.Matrix_Relation_Algebras

begin

section \<open>Representation of Stone Relation Algebras\<close>

text \<open>
We show that Stone relation algebras can be represented by matrices if we assume a point axiom.
The matrix indices and entries and the point axiom are based on the concepts of ideals and ideal-points.
We start with general results about sets and finite suprema.
\<close>

lemma finite_ne_subset_induct' [consumes 3, case_names singleton insert]:
  assumes "finite F"
      and "F \<noteq> {}"
      and "F \<subseteq> S"
      and singleton: "\<And>x . x \<in> S \<Longrightarrow> P {x}"
      and insert: "\<And>x F . finite F \<Longrightarrow> F \<noteq> {} \<Longrightarrow> F \<subseteq> S \<Longrightarrow> x \<in> S \<Longrightarrow> x \<notin> F \<Longrightarrow> P F \<Longrightarrow> P (insert x F)"
    shows "P F"
  using assms(1-3)
  apply (induct rule: finite_ne_induct)
  apply (simp add: singleton)
  by (simp add: insert)

context order_bot
begin

abbreviation atom :: "'a \<Rightarrow> bool"
  where "atom x \<equiv> x \<noteq> bot \<and> (\<forall>y . y \<noteq> bot \<and> y \<le> x \<longrightarrow> y = x)"

end

context semilattice_sup
begin

lemma nested_sup_fin:
  assumes "finite X"
      and "X \<noteq> {}"
      and "finite Y"
      and "Y \<noteq> {}"
    shows "Sup_fin { Sup_fin { f x y | x . x \<in> X } | y . y \<in> Y } = Sup_fin { f x y | x y . x \<in> X \<and> y \<in> Y }"
proof (rule order.antisym)
  have 1: "finite { f x y | x y . x \<in> X \<and> y \<in> Y }"
  proof -
    have "finite (X \<times> Y)"
      by (simp add: assms(1,3))
    hence "finite { f (fst z) (snd z) | z . z \<in> X \<times> Y }"
      by (metis (mono_tags) Collect_mem_eq finite_image_set)
    thus ?thesis
      by auto
  qed
  show "Sup_fin { Sup_fin { f x y | x . x \<in> X } | y . y \<in> Y } \<le> Sup_fin { f x y | x y . x \<in> X \<and> y \<in> Y }"
    apply (rule Sup_fin.boundedI)
    subgoal by (simp add: assms(3))
    subgoal using assms(4) by blast
    subgoal for a
    proof -
      assume "a \<in> { Sup_fin { f x y | x . x \<in> X } | y . y \<in> Y }"
      from this obtain y where 2: "y \<in> Y \<and> a = Sup_fin { f x y | x . x \<in> X }"
        by auto
      have "Sup_fin { f x y | x . x \<in> X } \<le> Sup_fin { f x y | x y . x \<in> X \<and> y \<in> Y }"
        apply (rule Sup_fin.boundedI)
        subgoal by (simp add: assms(1))
        subgoal using assms(2) by blast
        subgoal using Sup_fin.coboundedI 1 2 by blast
        done
      thus ?thesis
        using 2 by simp
    qed
    done
  show "Sup_fin { f x y | x y . x \<in> X \<and> y \<in> Y } \<le> Sup_fin { Sup_fin { f x y | x . x \<in> X } | y . y \<in> Y }"
    apply (rule Sup_fin.boundedI)
    subgoal using 1 by simp
    subgoal using assms(2,4) by blast
    subgoal for a
    proof -
      assume "a \<in> { f x y | x y . x \<in> X \<and> y \<in> Y }"
      from this obtain x y where 3: "x \<in> X \<and> y \<in> Y \<and> a = f x y"
        by auto
      have "a \<le> Sup_fin { f x y | x . x \<in> X }"
        apply (rule Sup_fin.coboundedI)
        apply (simp add: assms(1))
        using 3 by blast
      also have "... \<le> Sup_fin { Sup_fin { f x y | x . x \<in> X } | y . y \<in> Y }"
        apply (rule Sup_fin.coboundedI)
        apply (simp add: assms(3))
        using 3 by blast
      finally show "a \<le> Sup_fin { Sup_fin { f x y | x . x \<in> X } | y . y \<in> Y }"
        .
    qed
    done
qed

end

context bounded_semilattice_sup_bot
begin

lemma one_point_sup_fin:
  assumes "finite X"
      and "y \<in> X"
    shows "Sup_fin { (if x = y then f x else bot) | x . x \<in> X } = f y"
proof (rule order.antisym)
  show "Sup_fin { (if x = y then f x else bot) | x . x \<in> X } \<le> f y"
    apply (rule Sup_fin.boundedI)
    apply (simp add: assms(1))
    using assms(2) apply blast
    by auto
  show "f y \<le> Sup_fin { (if x = y then f x else bot) | x . x \<in> X }"
    apply (rule Sup_fin.coboundedI)
    using assms by auto
qed

end

subsection \<open>Ideals and Ideal-Points\<close>

text \<open>
We study ideals in Stone relation algebras, which are elements that are both a vector and a covector.
We include general results about Stone relation algebras.
\<close>

context times_top
begin

abbreviation ideal :: "'a \<Rightarrow> bool" where "ideal x \<equiv> vector x \<and> covector x"

end

context bounded_non_associative_left_semiring
begin

lemma ideal_fixpoint:
  "ideal x \<longleftrightarrow> top * x * top = x"
  by (metis order.antisym top_left_mult_increasing top_right_mult_increasing)

lemma ideal_top_closed:
  "ideal top"
  by simp

end

context bounded_idempotent_left_semiring
begin

lemma ideal_mult_closed:
  "ideal x \<Longrightarrow> ideal y \<Longrightarrow> ideal (x * y)"
  by (metis mult_assoc)

end

context bounded_idempotent_left_zero_semiring
begin

lemma ideal_sup_closed:
  "ideal x \<Longrightarrow> ideal y \<Longrightarrow> ideal (x \<squnion> y)"
  by (simp add: covector_sup_closed vector_sup_closed)

end

context idempotent_semiring
begin

lemma sup_fin_sum:
  fixes f :: "'b::finite \<Rightarrow> 'a"
  shows "Sup_fin { f x | x . x \<in> UNIV } = (\<Squnion>\<^sub>x f x)"
proof (rule order.antisym)
  show "Sup_fin { f x | x . x \<in> UNIV } \<le> (\<Squnion>\<^sub>x f x)"
    apply (rule Sup_fin.boundedI)
    apply (metis (mono_tags) finite finite_image_set)
    apply blast
    using ub_sum by auto
next
  show "(\<Squnion>\<^sub>x f x) \<le> Sup_fin { f x | x . x \<in> UNIV }"
    apply (rule lub_sum, rule allI)
    apply (rule Sup_fin.coboundedI)
    apply (metis (mono_tags) finite finite_image_set)
    by auto
qed

end

context stone_relation_algebra
begin

lemma dedekind_univalent:
  assumes "univalent y"
    shows "x * y \<sqinter> z = (x \<sqinter> z * y\<^sup>T) * y"
proof (rule order.antisym)
  show "x * y \<sqinter> z \<le> (x \<sqinter> z * y\<^sup>T) * y"
    by (simp add: dedekind_2)
next
  have "(x \<sqinter> z * y\<^sup>T) * y \<le> x * y \<sqinter> z * y\<^sup>T * y"
    using comp_left_subdist_inf by auto
  also have "... \<le> x * y \<sqinter> z"
    by (metis assms comp_associative comp_inf.mult_right_isotone comp_right_one mult_right_isotone)
  finally show "(x \<sqinter> z * y\<^sup>T) * y \<le> x * y \<sqinter> z"
    .
qed

lemma dedekind_injective:
  assumes "injective x"
    shows "x * y \<sqinter> z = x * (y \<sqinter> x\<^sup>T * z)"
proof (rule order.antisym)
  show "x * y \<sqinter> z \<le> x * (y \<sqinter> x\<^sup>T * z)"
    by (simp add: dedekind_1)
next
  have "x * (y \<sqinter> x\<^sup>T * z) \<le> x * y \<sqinter> x * x\<^sup>T * z"
    using comp_associative comp_right_subdist_inf by auto
  also have "... \<le> x * y \<sqinter> z"
    by (metis assms coreflexive_comp_top_inf inf.boundedE inf.boundedI inf.cobounded2 inf_le1)
  finally show "x * (y \<sqinter> x\<^sup>T * z) \<le> x * y \<sqinter> z"
    .
qed

lemma domain_vector_conv:
  "1 \<sqinter> x * top = 1 \<sqinter> x * x\<^sup>T"
  by (metis comp_right_one dedekind_eq ex231a inf.sup_monoid.add_commute inf_top.right_neutral total_conv_surjective vector_conv_covector vector_top_closed)

lemma domain_vector_covector:
  "1 \<sqinter> x * top = 1 \<sqinter> top * x\<^sup>T"
  by (metis conv_dist_comp one_inf_conv symmetric_top_closed)

lemma domain_covector_conv:
  "1 \<sqinter> top * x\<^sup>T = 1 \<sqinter> x * x\<^sup>T"
  using domain_vector_conv domain_vector_covector by auto

lemma ideal_bot_closed:
  "ideal bot"
  by simp

lemma ideal_inf_closed:
  "ideal x \<Longrightarrow> ideal y \<Longrightarrow> ideal (x \<sqinter> y)"
  by (simp add: covector_comp_inf vector_inf_comp)

lemma ideal_conv_closed:
  "ideal x \<Longrightarrow> ideal (x\<^sup>T)"
  using covector_conv_vector vector_conv_covector by blast

lemma ideal_complement_closed:
  "ideal x \<Longrightarrow> ideal (-x)"
  by (simp add: covector_complement_closed vector_complement_closed)

lemma ideal_conv_id:
  "ideal x \<Longrightarrow> x = x\<^sup>T"
  by (metis covector_comp_inf_1 inf.sup_monoid.add_commute inf_top.right_neutral mult_left_one vector_inf_comp)

lemma ideal_mult_inf:
  "ideal x \<Longrightarrow> ideal y \<Longrightarrow> x * y = x \<sqinter> y"
  by (metis inf_top_right vector_inf_comp)

lemma ideal_mult_import:
  "ideal x \<Longrightarrow> y * z \<sqinter> x = (y \<sqinter> x) * (z \<sqinter> x)"
  using covector_comp_inf inf.sup_monoid.add_commute vector_inf_comp by auto

lemma point_meet_one:
  "point x \<Longrightarrow> x * x\<^sup>T = x \<sqinter> 1"
  by (metis domain_vector_conv inf.absorb2 inf.sup_monoid.add_commute)

lemma below_point_eq_domain:
  "point x \<Longrightarrow> y \<le> x \<Longrightarrow> y = x * x\<^sup>T * y"
  by (metis inf.absorb2 vector_export_comp_unit point_meet_one)

lemma covector_mult_vector_ideal:
  "vector x \<Longrightarrow> vector z \<Longrightarrow> ideal (x\<^sup>T * y * z)"
  by (metis comp_associative vector_conv_covector)

abbreviation ideal_point :: "'a \<Rightarrow> bool" where "ideal_point x \<equiv> point x \<and> (\<forall>y z . point y \<and> ideal z \<and> z \<noteq> bot \<and> y * z \<le> x \<longrightarrow> y \<le> x)"

lemma different_ideal_points_disjoint:
  assumes "ideal_point p"
      and "ideal_point q"
      and "p \<noteq> q"
    shows "p \<sqinter> q = bot"
proof (rule ccontr)
  let ?r = "p\<^sup>T * (p \<sqinter> q)"
  assume 1: "p \<sqinter> q \<noteq> bot"
  have 2: "p \<sqinter> q = p * ?r"
    by (metis assms(1) comp_associative inf.left_idem vector_export_comp_unit point_meet_one)
  have "ideal ?r"
    by (meson assms(1,2) covector_mult_closed vector_conv_covector vector_inf_closed vector_mult_closed)
  hence "p \<le> q"
    using 1 2 by (metis assms(1,2) inf_le2 semiring.mult_not_zero)
  thus "False"
    by (metis assms dual_order.eq_iff epm_3)
qed

lemma points_disjoint_iff:
  assumes "vector x"
    shows "x \<sqinter> y = bot \<longleftrightarrow> x\<^sup>T * y = bot"
  by (metis assms inf_top_right schroeder_1)

lemma different_ideal_points_disjoint_2:
  assumes "ideal_point p"
      and "ideal_point q"
      and "p \<noteq> q"
    shows "p\<^sup>T * q = bot"
  using assms different_ideal_points_disjoint points_disjoint_iff by blast

lemma mult_right_dist_sup_fin:
  assumes "finite X"
      and "X \<noteq> {}"
    shows "Sup_fin { f x | x::'b . x \<in> X } * y = Sup_fin { f x * y | x . x \<in> X }"
proof (rule finite_ne_induct[where F="X"])
  show "finite X"
    using assms(1) by simp
  show "X \<noteq> {}"
    using assms(2) by simp
  show "\<And>z . Sup_fin { f x | x . x \<in> {z} } * y = Sup_fin { f x * y | x . x \<in> {z} }"
    by auto
  fix z F
  assume 1: "finite F" "F \<noteq> {}" "z \<notin> F" "Sup_fin { f x | x . x \<in> F } * y = Sup_fin { f x * y | x . x \<in> F }"
  have "{ f x | x . x \<in> insert z F } = insert (f z) { f x | x . x \<in> F }"
    by auto
  hence "Sup_fin { f x | x . x \<in> insert z F } * y = (f z \<squnion> Sup_fin { f x | x . x \<in> F }) * y"
    using Sup_fin.insert 1 by auto
  also have "... = f z * y \<squnion> Sup_fin { f x | x . x \<in> F } * y"
    using mult_right_dist_sup by blast
  also have "... = f z * y \<squnion> Sup_fin { f x * y | x . x \<in> F }"
    using 1 by simp
  also have "... = Sup_fin (insert (f z * y) { f x * y | x . x \<in> F })"
    using 1 by auto
  also have "... = Sup_fin { f x * y | x . x \<in> insert z F }"
    by (rule arg_cong[where f = "Sup_fin"], auto)
  finally show "Sup_fin { f x | x . x \<in> insert z F } * y = Sup_fin { f x * y | x . x \<in> insert z F }"
    .
qed

lemma mult_left_dist_sup_fin:
  assumes "finite X"
      and "X \<noteq> {}"
    shows "y * Sup_fin { f x | x::'b . x \<in> X } = Sup_fin { y * f x | x . x \<in> X }"
proof (rule finite_ne_induct[where F="X"])
  show "finite X"
    using assms(1) by simp
  show "X \<noteq> {}"
    using assms(2) by simp
  show "\<And>z . y * Sup_fin { f x | x . x \<in> {z} } = Sup_fin { y * f x | x . x \<in> {z} }"
    by auto
  fix z F
  assume 1: "finite F" "F \<noteq> {}" "z \<notin> F" "y * Sup_fin { f x | x . x \<in> F } = Sup_fin { y * f x | x . x \<in> F }"
  have "{ f x | x . x \<in> insert z F } = insert (f z) { f x | x . x \<in> F }"
    by auto
  hence "y * Sup_fin { f x | x . x \<in> insert z F } = y * (f z \<squnion> Sup_fin { f x | x . x \<in> F })"
    using Sup_fin.insert 1 by auto
  also have "... = y * f z \<squnion> y * Sup_fin { f x | x . x \<in> F }"
    using mult_left_dist_sup by blast
  also have "... = y * f z \<squnion> Sup_fin { y * f x | x . x \<in> F }"
    using 1 by simp
  also have "... = Sup_fin (insert (y * f z) { y * f x | x . x \<in> F })"
    using 1 by auto
  also have "... = Sup_fin { y * f x | x . x \<in> insert z F }"
    by (rule arg_cong[where f = "Sup_fin"], auto)
  finally show "y * Sup_fin { f x | x . x \<in> insert z F } = Sup_fin { y * f x | x . x \<in> insert z F }"
    .
qed

lemma inf_left_dist_sup_fin:
  assumes "finite X"
      and "X \<noteq> {}"
    shows "y \<sqinter> Sup_fin { f x | x::'b . x \<in> X } = Sup_fin { y \<sqinter> f x | x . x \<in> X }"
proof (rule finite_ne_induct[where F="X"])
  show "finite X"
    using assms(1) by simp
  show "X \<noteq> {}"
    using assms(2) by simp
  show "\<And>z . y \<sqinter> Sup_fin { f x | x . x \<in> {z} } = Sup_fin { y \<sqinter> f x | x . x \<in> {z} }"
    by auto
  fix z F
  assume 1: "finite F" "F \<noteq> {}" "z \<notin> F" "y \<sqinter> Sup_fin { f x | x . x \<in> F } = Sup_fin { y \<sqinter> f x | x . x \<in> F }"
  have "{ f x | x . x \<in> insert z F } = insert (f z) { f x | x . x \<in> F }"
    by auto
  hence "y \<sqinter> Sup_fin { f x | x . x \<in> insert z F } = y \<sqinter> (f z \<squnion> Sup_fin { f x | x . x \<in> F })"
    using Sup_fin.insert 1 by auto
  also have "... = (y \<sqinter> f z) \<squnion> (y \<sqinter> Sup_fin { f x | x . x \<in> F })"
    using inf_sup_distrib1 by auto
  also have "... = (y \<sqinter> f z) \<squnion> Sup_fin { y \<sqinter> f x | x . x \<in> F }"
    using 1 by simp
  also have "... = Sup_fin (insert (y \<sqinter> f z) { y \<sqinter> f x | x . x \<in> F })"
    using 1 by auto
  also have "... = Sup_fin { y \<sqinter> f x | x . x \<in> insert z F }"
    by (rule arg_cong[where f = "Sup_fin"], auto)
  finally show "y \<sqinter> Sup_fin { f x | x . x \<in> insert z F } = Sup_fin { y \<sqinter> f x | x . x \<in> insert z F }"
    .
qed

lemma top_one_sup_fin_iff:
  assumes "finite P"
      and "P \<noteq> {}"
      and "\<forall>p\<in>P . point p"
    shows "top = Sup_fin P \<longleftrightarrow> 1 = Sup_fin { p * p\<^sup>T | p . p \<in> P }"
proof
  assume "top = Sup_fin P"
  hence "1 = 1 \<sqinter> Sup_fin P"
    using inf_top_right by auto
  also have "... = Sup_fin { 1 \<sqinter> p | p . p \<in> P }"
    using inf_Sup1_distrib assms(1,2) by simp
  also have "... = Sup_fin { p * p\<^sup>T | p . p \<in> P }"
    by (metis (no_types, opaque_lifting) point_meet_one assms(3) inf.sup_monoid.add_commute)
  finally show "1 = Sup_fin { p * p\<^sup>T | p . p \<in> P }"
    .
next
  assume "1 = Sup_fin { p * p\<^sup>T | p . p \<in> P }"
  hence "top = Sup_fin { p * p\<^sup>T | p . p \<in> P } * top"
    using total_one_closed by auto
  also have "... = Sup_fin { 1 \<sqinter> p | p . p \<in> P } * top"
    by (metis (no_types, opaque_lifting) point_meet_one assms(3) inf.sup_monoid.add_commute)
  also have "... = Sup_fin { (1 \<sqinter> p) * top | p . p \<in> P }"
    using mult_right_dist_sup_fin assms(1,2) by auto
  also have "... = Sup_fin { p | p . p \<in> P }"
    by (metis (no_types, opaque_lifting) assms(3) inf.sup_monoid.add_commute inf_top.right_neutral vector_inf_one_comp)
  finally show "top = Sup_fin P"
    by simp
qed

abbreviation ideals :: "'a set" where "ideals \<equiv> { x . ideal x }"
abbreviation ideal_points :: "'a set" where "ideal_points \<equiv> { x . ideal_point x }"

lemma surjective_vector_top:
  "surjective x \<Longrightarrow> vector x \<Longrightarrow> x\<^sup>T * x = top"
  by (metis domain_vector_conv covector_inf_comp_3 ex231a inf.sup_monoid.add_commute inf_top.left_neutral vector_export_comp_unit)

lemma point_mult_top:
  "point x \<Longrightarrow> x\<^sup>T * x = top"
  using surjective_vector_top by blast

end

subsection \<open>Point Axiom\<close>

text \<open>
The following class captures the point axiom for Stone relation algebras.
\<close>

class stone_relation_algebra_pa = stone_relation_algebra +
  assumes finite_ideal_points: "finite ideal_points"
  assumes ne_ideal_points: "ideal_points \<noteq> {}"
  assumes top_sup_ideal_points: "top = Sup_fin ideal_points"
begin

lemma one_sup_ideal_points:
  "1 = Sup_fin { p * p\<^sup>T | p . ideal_point p }"
proof -
  have "1 = Sup_fin { p * p\<^sup>T | p . p \<in> ideal_points }"
    using top_one_sup_fin_iff finite_ideal_points ne_ideal_points top_sup_ideal_points by blast
  also have "... = Sup_fin { p * p\<^sup>T | p . ideal_point p }"
    by simp
  finally show ?thesis
    .
qed

lemma ideal_point_rep_1:
  "x = Sup_fin { p * p\<^sup>T * x * q * q\<^sup>T | p q . ideal_point p \<and> ideal_point q }"
proof -
  let ?p = "{ p * p\<^sup>T | p . p \<in> ideal_points }"
  have "x = Sup_fin ?p * (x * Sup_fin ?p)"
    using one_sup_ideal_points by auto
  also have "... = Sup_fin { p * p\<^sup>T * (x * Sup_fin ?p) | p . p \<in> ideal_points }"
    apply (rule mult_right_dist_sup_fin)
    using finite_ideal_points ne_ideal_points by simp_all
  also have "... = Sup_fin { p * p\<^sup>T * x * Sup_fin ?p | p . p \<in> ideal_points }"
    using mult_assoc by simp
  also have "... = Sup_fin { Sup_fin { p * p\<^sup>T * x * q * q\<^sup>T | q . q \<in> ideal_points } | p . p \<in> ideal_points }"
  proof -
    have "\<And>p . p * p\<^sup>T * x * Sup_fin ?p = Sup_fin { p * p\<^sup>T * x * (q * q\<^sup>T) | q . q \<in> ideal_points }"
      apply (rule mult_left_dist_sup_fin)
      using finite_ideal_points ne_ideal_points by simp_all
    thus ?thesis
      using mult_assoc by simp
  qed
  also have "... = Sup_fin { p * p\<^sup>T * x * q * q\<^sup>T | q p . q \<in> ideal_points \<and> p \<in> ideal_points }"
    apply (rule nested_sup_fin)
    using finite_ideal_points ne_ideal_points by simp_all
  also have "... = Sup_fin { p * p\<^sup>T * x * q * q\<^sup>T | p q . p \<in> ideal_points \<and> q \<in> ideal_points }"
    by meson
  also have "... = Sup_fin { p * p\<^sup>T * x * q * q\<^sup>T | p q . ideal_point p \<and> ideal_point q }"
    by auto
  finally show ?thesis
    .
qed

lemma atom_below_ideal_point:
  assumes "atom a"
    shows "\<exists>p . ideal_point p \<and> a \<le> p"
proof -
  have "a = a \<sqinter> Sup_fin { p | p . p \<in> ideal_points }"
    using top_sup_ideal_points by auto
  also have "... = Sup_fin { a \<sqinter> p | p . p \<in> ideal_points }"
    apply (rule inf_left_dist_sup_fin)
    using finite_ideal_points apply blast
    using ne_ideal_points by blast
  finally have 1: "Sup_fin { a \<sqinter> p | p . p \<in> ideal_points } \<noteq> bot"
    using assms by auto
  have "\<exists>p\<in>ideal_points . a \<sqinter> p \<noteq> bot"
  proof (rule ccontr)
    assume "\<not> (\<exists>p\<in>ideal_points . a \<sqinter> p \<noteq> bot)"
    hence "\<forall>p\<in>ideal_points . a \<sqinter> p = bot"
      by auto
    hence "{ a \<sqinter> p | p . p \<in> ideal_points } = { bot | p . p \<in> ideal_points }"
      by auto
    hence "Sup_fin { a \<sqinter> p | p . p \<in> ideal_points } = Sup_fin { bot | p . p \<in> ideal_points }"
      by simp
    also have "... \<le> bot"
      apply (rule Sup_fin.boundedI)
      apply (simp add: finite_ideal_points)
      using ne_ideal_points apply simp
      by blast
    finally show "False"
      using 1 le_bot by blast
  qed
  from this obtain p where "p \<in> ideal_points \<and> a \<sqinter> p \<noteq> bot"
    by auto
  hence "ideal_point p \<and> a \<le> p"
    using assms inf.absorb_iff1 inf_le1 by blast
  thus ?thesis
    by auto
qed

end

subsection \<open>Ideals, Ideal-Points and Matrices as Types\<close>

text \<open>
Stone relation algebras will be represented by matrices with ideal-points as entries and ideals as indices.
To define the type of such matrices, we first derive types for the set of ideals and ideal-points.
\<close>

typedef (overloaded) 'a ideal = "ideals::'a::stone_relation_algebra_pa set"
  using surjective_top_closed by blast

setup_lifting type_definition_ideal

instantiation ideal :: (stone_relation_algebra_pa) stone_algebra
begin

lift_definition uminus_ideal :: "'a ideal \<Rightarrow> 'a ideal" is uminus
  using ideal_complement_closed by blast

lift_definition inf_ideal :: "'a ideal \<Rightarrow> 'a ideal \<Rightarrow> 'a ideal" is inf
  by (simp add: ideal_inf_closed)

lift_definition sup_ideal :: "'a ideal \<Rightarrow> 'a ideal \<Rightarrow> 'a ideal" is sup
  by (simp add: ideal_sup_closed)

lift_definition bot_ideal :: "'a ideal" is bot
  by (simp add: ideal_bot_closed)

lift_definition top_ideal :: "'a ideal" is top
  by simp

lift_definition less_eq_ideal :: "'a ideal \<Rightarrow> 'a ideal \<Rightarrow> bool" is less_eq .

lift_definition less_ideal :: "'a ideal \<Rightarrow> 'a ideal \<Rightarrow> bool" is less .

instance
  apply intro_classes
  subgoal apply transfer by (simp add: less_le_not_le)
  subgoal apply transfer by simp
  subgoal apply transfer by simp
  subgoal apply transfer by simp
  subgoal apply transfer by simp
  subgoal apply transfer by simp
  subgoal apply transfer by simp
  subgoal apply transfer by simp
  subgoal apply transfer by simp
  subgoal apply transfer by simp
  subgoal apply transfer by simp
  subgoal apply transfer by simp
  subgoal apply transfer by (simp add: sup_inf_distrib1)
  subgoal apply transfer by (simp add: pseudo_complement)
  subgoal apply transfer by simp
  done

end

instantiation ideal :: (stone_relation_algebra_pa) stone_relation_algebra
begin

lift_definition conv_ideal :: "'a ideal \<Rightarrow> 'a ideal" is id
  by simp

lift_definition times_ideal :: "'a ideal \<Rightarrow> 'a ideal \<Rightarrow> 'a ideal" is inf
  by (simp add: ideal_inf_closed)

lift_definition one_ideal :: "'a ideal" is top
  by simp

instance
  apply intro_classes
  apply (metis comp_inf.comp_associative inf_ideal_def times_ideal_def)
  apply (metis inf_commute inf_ideal_def inf_sup_distrib1 times_ideal_def)
  apply (metis (mono_tags, lifting) comp_inf.mult_left_zero inf_ideal_def times_ideal_def)
  apply (metis (mono_tags, opaque_lifting) comp_inf.mult_1_left inf_ideal_def one_ideal.abs_eq times_ideal_def top_ideal.abs_eq)
  using Rep_ideal_inject conv_ideal.rep_eq apply fastforce
  apply (metis (mono_tags) Rep_ideal_inverse conv_ideal.rep_eq)
  apply (metis (mono_tags) Rep_ideal_inverse conv_ideal.rep_eq inf_commute inf_ideal_def times_ideal_def)
  apply (metis (mono_tags, opaque_lifting) Rep_ideal_inverse conv_ideal.rep_eq inf_ideal_def le_inf_iff order_refl times_ideal_def)
  apply (metis inf_ideal_def p_dist_inf p_dist_sup times_ideal_def)
  by (metis (mono_tags) one_ideal.abs_eq regular_closed_top top_ideal_def)

end

typedef (overloaded) 'a ideal_point = "ideal_points::'a::stone_relation_algebra_pa set"
  using ne_ideal_points by blast

instantiation ideal_point :: (stone_relation_algebra_pa) finite
begin

instance
proof
  have "Abs_ideal_point ` ideal_points = UNIV"
    using type_definition.Abs_image type_definition_ideal_point by blast
  thus "finite (UNIV::'a ideal_point set)"
    by (metis (mono_tags, lifting) finite_ideal_points finite_imageI)
qed

end

type_synonym 'a ideal_matrix = "('a ideal_point,'a ideal) square"

interpretation ideal_matrix_stone_relation_algebra: stone_relation_algebra where sup = sup_matrix and inf = inf_matrix and less_eq = less_eq_matrix and less = less_matrix and bot = "bot_matrix::'a::stone_relation_algebra_pa ideal_matrix" and top = top_matrix and uminus = uminus_matrix and one = one_matrix and times = times_matrix and conv = conv_matrix
  by (rule matrix_stone_relation_algebra.stone_relation_algebra_axioms)

lemma ideal_point_rep_2:
  assumes "x = Sup_fin { Rep_ideal_point p * Rep_ideal (f p q) * (Rep_ideal_point q)\<^sup>T | p q . True }"
    shows "f r s = Abs_ideal ((Rep_ideal_point r)\<^sup>T * x * (Rep_ideal_point s))"
proof -
  let ?r = "Rep_ideal_point r"
  let ?s = "Rep_ideal_point s"
  have "?r\<^sup>T * x * ?s = ?r\<^sup>T * Sup_fin { Rep_ideal_point p * Rep_ideal (f p q) * (Rep_ideal_point q)\<^sup>T | p q . True } * ?s"
    using assms by simp
  also have "... = ?r\<^sup>T * Sup_fin { Rep_ideal_point p * Rep_ideal (f p q) * (Rep_ideal_point q)\<^sup>T | p q . p \<in> UNIV \<and> q \<in> UNIV } * ?s"
    by simp
  also have "... = ?r\<^sup>T * Sup_fin { Sup_fin { Rep_ideal_point p * Rep_ideal (f p q) * (Rep_ideal_point q)\<^sup>T | p . p \<in> UNIV } | q . q \<in> UNIV } * ?s"
  proof -
    have "Sup_fin { Rep_ideal_point p * Rep_ideal (f p q) * (Rep_ideal_point q)\<^sup>T | p q . p \<in> UNIV \<and> q \<in> UNIV } = Sup_fin { Sup_fin { Rep_ideal_point p * Rep_ideal (f p q) * (Rep_ideal_point q)\<^sup>T | p . p \<in> UNIV } | q . q \<in> UNIV }"
      by (rule nested_sup_fin[symmetric], simp_all)
    thus ?thesis
      by simp
  qed
  also have "... = Sup_fin { Sup_fin { ?r\<^sup>T * Rep_ideal_point p * Rep_ideal (f p q) * (Rep_ideal_point q)\<^sup>T | p . p \<in> UNIV } | q . q \<in> UNIV } * ?s"
  proof -
    have 1: "?r\<^sup>T * Sup_fin { Sup_fin { Rep_ideal_point p * Rep_ideal (f p q) * (Rep_ideal_point q)\<^sup>T | p . p \<in> UNIV } | q . q \<in> UNIV } = Sup_fin { ?r\<^sup>T * Sup_fin { Rep_ideal_point p * Rep_ideal (f p q) * (Rep_ideal_point q)\<^sup>T | p . p \<in> UNIV } | q . q \<in> UNIV }"
      by (rule mult_left_dist_sup_fin, simp_all)
    have 2: "\<And>q . ?r\<^sup>T * Sup_fin { Rep_ideal_point p * Rep_ideal (f p q) * (Rep_ideal_point q)\<^sup>T | p . p \<in> UNIV } = Sup_fin { ?r\<^sup>T * (Rep_ideal_point p * Rep_ideal (f p q) * (Rep_ideal_point q)\<^sup>T) | p . p \<in> UNIV }"
      by (rule mult_left_dist_sup_fin, simp_all)
    have "\<And>p q . ?r\<^sup>T * (Rep_ideal_point p * Rep_ideal (f p q) * (Rep_ideal_point q)\<^sup>T) = ?r\<^sup>T * Rep_ideal_point p * Rep_ideal (f p q) * (Rep_ideal_point q)\<^sup>T"
      by (simp add: mult.assoc)
    thus ?thesis
      using 1 2 by simp
  qed
  also have "... = Sup_fin { Sup_fin { ?r\<^sup>T * Rep_ideal_point p * Rep_ideal (f p q) * (Rep_ideal_point q)\<^sup>T * ?s | p . p \<in> UNIV } | q . q \<in> UNIV }"
  proof -
    have 3: "Sup_fin { Sup_fin { ?r\<^sup>T * Rep_ideal_point p * Rep_ideal (f p q) * (Rep_ideal_point q)\<^sup>T | p . p \<in> UNIV } | q . q \<in> UNIV } * ?s = Sup_fin { Sup_fin { ?r\<^sup>T * Rep_ideal_point p * Rep_ideal (f p q) * (Rep_ideal_point q)\<^sup>T | p . p \<in> UNIV } * ?s | q . q \<in> UNIV }"
      by (rule mult_right_dist_sup_fin, simp_all)
    have "\<And>q . Sup_fin { ?r\<^sup>T * Rep_ideal_point p * Rep_ideal (f p q) * (Rep_ideal_point q)\<^sup>T | p . p \<in> UNIV } * ?s = Sup_fin { ?r\<^sup>T * Rep_ideal_point p * Rep_ideal (f p q) * (Rep_ideal_point q)\<^sup>T * ?s | p . p \<in> UNIV }"
      by (rule mult_right_dist_sup_fin, simp_all)
    thus ?thesis
      using 3 by simp
  qed
  also have "... = Sup_fin { Sup_fin { if p = r then ?r\<^sup>T * Rep_ideal_point p * Rep_ideal (f p q) * (Rep_ideal_point q)\<^sup>T * ?s else bot | p . p \<in> UNIV } | q . q \<in> UNIV }"
  proof -
    have "\<And>p . ?r\<^sup>T * Rep_ideal_point p = (if p = r then ?r\<^sup>T * Rep_ideal_point p else bot)"
    proof -
      fix p
      show "?r\<^sup>T * Rep_ideal_point p = (if p = r then ?r\<^sup>T * Rep_ideal_point p else bot)"
      proof (cases "p = r")
        case True
        thus ?thesis
          by auto
      next
        case False
        have "?r\<^sup>T * Rep_ideal_point p = bot"
          apply (rule different_ideal_points_disjoint_2)
          using Rep_ideal_point apply blast
          using Rep_ideal_point apply blast
          using False by (simp add: Rep_ideal_point_inject)
        thus ?thesis
          using False by simp
      qed
    qed
    hence "\<And>p q . ?r\<^sup>T * Rep_ideal_point p * Rep_ideal (f p q) * (Rep_ideal_point q)\<^sup>T * ?s = (if p = r then ?r\<^sup>T * Rep_ideal_point p * Rep_ideal (f p q) * (Rep_ideal_point q)\<^sup>T * ?s else bot)"
      by (metis semiring.mult_zero_left)
    thus ?thesis
      by simp
  qed
  also have "... = Sup_fin { ?r\<^sup>T * ?r * Rep_ideal (f r q) * (Rep_ideal_point q)\<^sup>T * ?s | q . q \<in> UNIV }"
    by (subst one_point_sup_fin, simp_all)
  also have "... = Sup_fin { if q = s then ?r\<^sup>T * ?r * Rep_ideal (f r q) * (Rep_ideal_point q)\<^sup>T * ?s else bot | q . q \<in> UNIV }"
  proof -
    have "\<And>q . (Rep_ideal_point q)\<^sup>T * ?s = (if q = s then (Rep_ideal_point q)\<^sup>T * ?s else bot)"
    proof -
      fix q
      show "(Rep_ideal_point q)\<^sup>T * ?s = (if q = s then (Rep_ideal_point q)\<^sup>T * ?s else bot)"
      proof (cases "q = s")
        case True
        thus ?thesis
          by auto
      next
        case False
        have "(Rep_ideal_point q)\<^sup>T * ?s = bot"
          apply (rule different_ideal_points_disjoint_2)
          using Rep_ideal_point apply blast
          using Rep_ideal_point apply blast
          using False by (simp add: Rep_ideal_point_inject)
        thus ?thesis
          using False by simp
      qed
    qed
    hence "\<And>q . ?r\<^sup>T * ?r * Rep_ideal (f r q) * (Rep_ideal_point q)\<^sup>T * ?s = (if q = s then ?r\<^sup>T * ?r * Rep_ideal (f r q) * (Rep_ideal_point q)\<^sup>T * ?s else bot)"
      by (metis comp_associative mult_right_zero)
    thus ?thesis
      by simp
  qed
  also have "... = ?r\<^sup>T * ?r * Rep_ideal (f r s) * ?s\<^sup>T * ?s"
    by (subst one_point_sup_fin, simp_all)
  also have "... = top * Rep_ideal (f r s) * top"
  proof -
    have "?r\<^sup>T * ?r = top \<and> ?s\<^sup>T * ?s = top"
      using point_mult_top Rep_ideal_point by blast
    thus ?thesis
      by (simp add: mult.assoc)
  qed
  also have "... = Rep_ideal (f r s)"
    by (metis (mono_tags, lifting) Rep_ideal mem_Collect_eq)
  finally show ?thesis
    by (simp add: Rep_ideal_inverse)
qed

subsection \<open>Isomorphism\<close>

text \<open>
The following two functions comprise the isomorphism between Stone relation algebras and matrices.
We prove that they are inverses of each other and that the first one is a homomorphism.
\<close>

definition sra_to_mat :: "'a::stone_relation_algebra_pa \<Rightarrow> 'a ideal_matrix"
  where "sra_to_mat x \<equiv> \<lambda>(p,q) . Abs_ideal ((Rep_ideal_point p)\<^sup>T * x * Rep_ideal_point q)"

definition mat_to_sra :: "'a::stone_relation_algebra_pa ideal_matrix \<Rightarrow> 'a"
  where "mat_to_sra f \<equiv> Sup_fin { Rep_ideal_point p * Rep_ideal (f (p,q)) * (Rep_ideal_point q)\<^sup>T | p q . True }"

lemma sra_mat_sra:
  "mat_to_sra (sra_to_mat x) = x"
proof -
  have "mat_to_sra (sra_to_mat x) = Sup_fin { Rep_ideal_point p * Rep_ideal (Abs_ideal ((Rep_ideal_point p)\<^sup>T * x * Rep_ideal_point q)) * (Rep_ideal_point q)\<^sup>T | p q . True }"
    by (unfold sra_to_mat_def mat_to_sra_def, simp)
  also have "... = Sup_fin { Rep_ideal_point p * (Rep_ideal_point p)\<^sup>T * x * Rep_ideal_point q * (Rep_ideal_point q)\<^sup>T | p q . True }"
  proof -
    have "\<And>p q . ideal ((Rep_ideal_point p)\<^sup>T * x * Rep_ideal_point q)"
      using Rep_ideal_point covector_mult_vector_ideal by force
    hence "\<And>p q . Rep_ideal (Abs_ideal ((Rep_ideal_point p)\<^sup>T * x * Rep_ideal_point q)) = (Rep_ideal_point p)\<^sup>T * x * Rep_ideal_point q"
      using Abs_ideal_inverse by blast
    thus ?thesis
      by (simp add: mult.assoc)
  qed
  also have "... = Sup_fin { p * p\<^sup>T * x * q * q\<^sup>T | p q . ideal_point p \<and> ideal_point q }"
  proof -
    have "{ Rep_ideal_point p * (Rep_ideal_point p)\<^sup>T * x * Rep_ideal_point q * (Rep_ideal_point q)\<^sup>T | p q . True } = { p * p\<^sup>T * x * q * q\<^sup>T | p q . ideal_point p \<and> ideal_point q }"
    proof (rule set_eqI)
      fix z
      show "z \<in> { Rep_ideal_point p * (Rep_ideal_point p)\<^sup>T * x * Rep_ideal_point q * (Rep_ideal_point q)\<^sup>T | p q . True } \<longleftrightarrow> z \<in> { p * p\<^sup>T * x * q * q\<^sup>T | p q . ideal_point p \<and> ideal_point q }"
      proof
        assume "z \<in> { Rep_ideal_point p * (Rep_ideal_point p)\<^sup>T * x * Rep_ideal_point q * (Rep_ideal_point q)\<^sup>T | p q . True }"
        from this obtain p q where "z = Rep_ideal_point p * (Rep_ideal_point p)\<^sup>T * x * Rep_ideal_point q * (Rep_ideal_point q)\<^sup>T"
          by auto
        thus "z \<in> { p * p\<^sup>T * x * q * q\<^sup>T | p q . ideal_point p \<and> ideal_point q }"
          using Rep_ideal_point by blast
      next
        assume "z \<in> { p * p\<^sup>T * x * q * q\<^sup>T | p q . ideal_point p \<and> ideal_point q }"
        from this obtain p q where 1: "ideal_point p \<and> ideal_point q \<and> z = p * p\<^sup>T * x * q * q\<^sup>T"
          by auto
        hence "Rep_ideal_point (Abs_ideal_point p) = p \<and> Rep_ideal_point (Abs_ideal_point q) = q"
          using Abs_ideal_point_inverse by auto
        thus "z \<in> { Rep_ideal_point p * (Rep_ideal_point p)\<^sup>T * x * Rep_ideal_point q * (Rep_ideal_point q)\<^sup>T | p q . True }"
          using 1 by (metis (mono_tags, lifting) mem_Collect_eq)
      qed
    qed
    thus ?thesis
      by simp
  qed
  also have "... = x"
    by (rule ideal_point_rep_1[symmetric])
  finally show ?thesis
    .
qed

lemma mat_sra_mat:
  "sra_to_mat (mat_to_sra f) = f"
  by (unfold sra_to_mat_def mat_to_sra_def, simp add: ideal_point_rep_2[symmetric])

lemma sra_to_mat_sup_homomorphism:
  "sra_to_mat (x \<squnion> y) = sra_to_mat x \<squnion> sra_to_mat y"
proof (rule ext,unfold split_paired_all)
  fix p q
  have "sra_to_mat (x \<squnion> y) (p,q) = Abs_ideal ((Rep_ideal_point p)\<^sup>T * (x \<squnion> y) * Rep_ideal_point q)"
    by (unfold sra_to_mat_def, simp)
  also have "... = Abs_ideal ((Rep_ideal_point p)\<^sup>T * x * Rep_ideal_point q \<squnion> (Rep_ideal_point p)\<^sup>T * y * Rep_ideal_point q)"
    by (simp add: comp_right_dist_sup idempotent_left_zero_semiring_class.semiring.distrib_left)
  also have "... = Abs_ideal ((Rep_ideal_point p)\<^sup>T * x * Rep_ideal_point q) \<squnion> Abs_ideal ((Rep_ideal_point p)\<^sup>T * y * Rep_ideal_point q)"
  proof (rule sup_ideal.abs_eq[symmetric])
    have 1: "\<And>x . ideal_point (Rep_ideal_point x::'a)"
      using Rep_ideal_point by blast
    hence 2: "covector ((Rep_ideal_point p)\<^sup>T)"
      using vector_conv_covector by blast
    thus "eq_onp ideal ((Rep_ideal_point p)\<^sup>T * x * Rep_ideal_point q) ((Rep_ideal_point p)\<^sup>T * x * Rep_ideal_point q)"
      using 1 by (simp add: comp_associative covector_mult_closed eq_onp_same_args)
    show "eq_onp ideal ((Rep_ideal_point p)\<^sup>T * y * Rep_ideal_point q) ((Rep_ideal_point p)\<^sup>T * y * Rep_ideal_point q)"
      using 1 2 by (simp add: comp_associative covector_mult_closed eq_onp_same_args)
  qed
  also have "... = sra_to_mat x (p,q) \<squnion> sra_to_mat y (p,q)"
    by (unfold sra_to_mat_def, simp)
  finally show "sra_to_mat (x \<squnion> y) (p,q) = (sra_to_mat x \<squnion> sra_to_mat y) (p,q)"
    by simp
qed

lemma sra_to_mat_inf_homomorphism:
  "sra_to_mat (x \<sqinter> y) = sra_to_mat x \<sqinter> sra_to_mat y"
proof (rule ext,unfold split_paired_all)
  fix p q
  have "sra_to_mat (x \<sqinter> y) (p,q) = Abs_ideal ((Rep_ideal_point p)\<^sup>T * (x \<sqinter> y) * Rep_ideal_point q)"
    by (unfold sra_to_mat_def, simp)
  also have "... = Abs_ideal ((Rep_ideal_point p)\<^sup>T * x * Rep_ideal_point q \<sqinter> (Rep_ideal_point p)\<^sup>T * y * Rep_ideal_point q)"
    by (metis (no_types, lifting) Rep_ideal_point conv_involutive injective_comp_right_dist_inf mem_Collect_eq univalent_comp_left_dist_inf)
  also have "... = Abs_ideal ((Rep_ideal_point p)\<^sup>T * x * Rep_ideal_point q) \<sqinter> Abs_ideal ((Rep_ideal_point p)\<^sup>T * y * Rep_ideal_point q)"
  proof (rule inf_ideal.abs_eq[symmetric])
    have 1: "\<And>x . ideal_point (Rep_ideal_point x::'a)"
      using Rep_ideal_point by blast
    hence 2: "covector ((Rep_ideal_point p)\<^sup>T)"
      using vector_conv_covector by blast
    thus "eq_onp ideal ((Rep_ideal_point p)\<^sup>T * x * Rep_ideal_point q) ((Rep_ideal_point p)\<^sup>T * x * Rep_ideal_point q)"
      using 1 by (simp add: comp_associative covector_mult_closed eq_onp_same_args)
    show "eq_onp ideal ((Rep_ideal_point p)\<^sup>T * y * Rep_ideal_point q) ((Rep_ideal_point p)\<^sup>T * y * Rep_ideal_point q)"
      using 1 2 by (simp add: comp_associative covector_mult_closed eq_onp_same_args)
  qed
  also have "... = sra_to_mat x (p,q) \<sqinter> sra_to_mat y (p,q)"
    by (unfold sra_to_mat_def, simp)
  finally show "sra_to_mat (x \<sqinter> y) (p,q) = (sra_to_mat x \<sqinter> sra_to_mat y) (p,q)"
    by simp
qed

lemma sra_to_mat_conv_homomorphism:
  "sra_to_mat (x\<^sup>T) = (sra_to_mat x)\<^sup>t"
proof (rule ext,unfold split_paired_all)
  fix p q
  have "sra_to_mat (x\<^sup>T) (p,q) = Abs_ideal ((Rep_ideal_point p)\<^sup>T * (x\<^sup>T) * Rep_ideal_point q)"
    by (unfold sra_to_mat_def, simp)
  also have "... = Abs_ideal (((Rep_ideal_point q)\<^sup>T * x * Rep_ideal_point p)\<^sup>T)"
    by (simp add: conv_dist_comp mult.assoc)
  also have "... = Abs_ideal ((Rep_ideal_point q)\<^sup>T * x * Rep_ideal_point p)"
  proof -
    have "ideal_point (Rep_ideal_point p) \<and> ideal_point (Rep_ideal_point q)"
      using Rep_ideal_point by blast
    thus ?thesis
      by (metis (full_types) covector_mult_vector_ideal ideal_conv_id)
  qed
  also have "... = (Abs_ideal ((Rep_ideal_point q)\<^sup>T * x * Rep_ideal_point p))\<^sup>T"
    by (metis Rep_ideal_inject conv_ideal.rep_eq)
  also have "... = (sra_to_mat x (q,p))\<^sup>T"
    by (unfold sra_to_mat_def, simp)
  finally show "sra_to_mat (x\<^sup>T) (p,q) = ((sra_to_mat x)\<^sup>t) (p,q)"
    by (simp add: conv_matrix_def)
qed

lemma sra_to_mat_complement_homomorphism:
  "sra_to_mat (-x) = -(sra_to_mat x)"
proof (rule ext,unfold split_paired_all)
  fix p q
  have "sra_to_mat (-x) (p,q) = Abs_ideal ((Rep_ideal_point p)\<^sup>T * -x * Rep_ideal_point q)"
    by (unfold sra_to_mat_def, simp)
  also have "... = Abs_ideal (-((Rep_ideal_point p)\<^sup>T * x * Rep_ideal_point q))"
  proof -
    have 1: "(Rep_ideal_point p)\<^sup>T * -x = -((Rep_ideal_point p)\<^sup>T * x)"
      using Rep_ideal_point comp_mapping_complement surjective_conv_total by force
    have "-((Rep_ideal_point p)\<^sup>T * x) * Rep_ideal_point q = -((Rep_ideal_point p)\<^sup>T * x * Rep_ideal_point q)"
      using Rep_ideal_point comp_bijective_complement by blast
    thus ?thesis
      using 1 by simp
  qed
  also have "... = -Abs_ideal ((Rep_ideal_point p)\<^sup>T * x * Rep_ideal_point q)"
  proof (rule uminus_ideal.abs_eq[symmetric])
    have 1: "\<And>x . ideal_point (Rep_ideal_point x::'a)"
      using Rep_ideal_point by blast
    hence "covector ((Rep_ideal_point p)\<^sup>T)"
      using vector_conv_covector by blast
    thus "eq_onp ideal ((Rep_ideal_point p)\<^sup>T * x * Rep_ideal_point q) ((Rep_ideal_point p)\<^sup>T * x * Rep_ideal_point q)"
      using 1 by (simp add: comp_associative covector_mult_closed eq_onp_same_args)
  qed
  also have "... = -sra_to_mat x (p,q)"
    by (unfold sra_to_mat_def, simp)
  finally show "sra_to_mat (-x) (p,q) = (-sra_to_mat x) (p,q)"
    by simp
qed

lemma sra_to_mat_bot_homomorphism:
  "sra_to_mat bot = bot"
proof (rule ext,unfold split_paired_all)
  fix p q :: "'a ideal_point"
  have "sra_to_mat bot (p,q) = Abs_ideal ((Rep_ideal_point p)\<^sup>T * bot * Rep_ideal_point q)"
    by (unfold sra_to_mat_def, simp)
  also have "... = bot"
    by (simp add: bot_ideal.abs_eq)
  finally show "sra_to_mat bot (p,q) = bot (p,q)"
    by simp
qed

lemma sra_to_mat_top_homomorphism:
  "sra_to_mat top = top"
proof (rule ext,unfold split_paired_all)
  fix p q :: "'a ideal_point"
  have "sra_to_mat top (p,q) = Abs_ideal ((Rep_ideal_point p)\<^sup>T * top * Rep_ideal_point q)"
    by (unfold sra_to_mat_def, simp)
  also have "... = top"
  proof -
    have "\<And>x . ideal_point (Rep_ideal_point x::'a)"
      using Rep_ideal_point by blast
    thus ?thesis
      by (metis (full_types) conv_dist_comp symmetric_top_closed top_ideal.abs_eq)
  qed
  finally show "sra_to_mat top (p,q) = top (p,q)"
    by simp
qed

lemma sra_to_mat_one_homomorphism:
  "sra_to_mat 1 = one_matrix"
proof (rule ext,unfold split_paired_all)
  fix p q :: "'a ideal_point"
  have "sra_to_mat 1 (p,q) = Abs_ideal ((Rep_ideal_point p)\<^sup>T * Rep_ideal_point q)"
    by (unfold sra_to_mat_def, simp)
  also have "... = one_matrix (p,q)"
  proof (cases "p = q")
    case True
    hence "(Rep_ideal_point p)\<^sup>T * Rep_ideal_point q = top"
      using Rep_ideal_point point_mult_top by auto
    hence "Abs_ideal ((Rep_ideal_point p)\<^sup>T * Rep_ideal_point q) = Abs_ideal top"
      by simp
    also have "... = one_matrix (p,q)"
      by (unfold one_matrix_def, simp add: True one_ideal_def)
    finally show ?thesis
      .
  next
    case False
    have "(Rep_ideal_point p)\<^sup>T * Rep_ideal_point q = bot"
      apply (rule different_ideal_points_disjoint_2)
      using Rep_ideal_point apply blast
      using Rep_ideal_point apply blast
      by (simp add: False Rep_ideal_point_inject)
    also have "... = one_matrix (p,q)"
      by (unfold one_matrix_def, simp add: False)
    finally show ?thesis
      by (simp add: False bot_ideal_def one_matrix_def)
  qed
  finally show "sra_to_mat 1 (p,q) = one_matrix (p,q)"
    by simp
qed

lemma Abs_ideal_dist_sup_fin:
  assumes "finite X"
      and "X \<noteq> {}"
      and "\<forall>x\<in>X . ideal (f x)"
    shows "Abs_ideal (Sup_fin { f x | x . x \<in> X }) = Sup_fin { Abs_ideal (f x) | x . x \<in> X }"
proof (rule finite_ne_subset_induct'[where F="X"])
  show "finite X"
    using assms(1) by simp
  show "X \<noteq> {}"
    using assms(2) by simp
  show "X \<subseteq> X"
    by simp
  fix y
  assume 1: "y \<in> X"
  thus "Abs_ideal (Sup_fin { f x | x . x \<in> {y} }) = Sup_fin { Abs_ideal (f x) | x . x \<in> {y} }"
    by auto
  fix F
  assume 2: "finite F" "F \<noteq> {}" "F \<subseteq> X" "y \<notin> F" "Abs_ideal (Sup_fin { f x | x . x \<in> F }) = Sup_fin { Abs_ideal (f x) | x . x \<in> F }"
  have "Abs_ideal (Sup_fin { f x | x . x \<in> insert y F }) = Abs_ideal (f y \<squnion> Sup_fin { f x | x . x \<in> F })"
  proof -
    have "Sup_fin { f x | x . x \<in> insert y F } = f y \<squnion> Sup_fin { f x | x . x \<in> F }"
      apply (subst Sup_fin.insert[symmetric])
      using 2 apply simp
      using 2 apply simp
      by (auto intro: arg_cong[where f="Sup_fin"])
    thus ?thesis
      by simp
  qed
  also have "... = Abs_ideal (f y) \<squnion> Abs_ideal (Sup_fin { f x | x . x \<in> F })"
  proof (rule sup_ideal.abs_eq[symmetric])
    show "eq_onp ideal (f y) (f y)"
      using 1 by (simp add: assms(3) eq_onp_same_args)
    have "top * Sup_fin { f x | x . x \<in> F } = Sup_fin { top * f x | x . x \<in> F }"
      using 2 mult_left_dist_sup_fin by fastforce
    hence "top * Sup_fin { f x | x . x \<in> F } * top = Sup_fin { top * f x | x . x \<in> F } * top"
      by simp
    also have "... = Sup_fin { top * f x * top | x . x \<in> F }"
      using 2 mult_right_dist_sup_fin by force
    also have "... = Sup_fin { f x | x . x \<in> F }"
      using 2 by (metis assms(3) subset_iff)
    finally have "top * Sup_fin { f x | x . x \<in> F } * top = Sup_fin { f x | x . x \<in> F }"
      .
    hence "ideal (Sup_fin { f x | x . x \<in> F })"
      using ideal_fixpoint by blast
    thus "eq_onp ideal (Sup_fin { f x | x . x \<in> F }) (Sup_fin { f x | x . x \<in> F })"
      by (simp add: eq_onp_def)
  qed
  also have "... = Abs_ideal (f y) \<squnion> Sup_fin { Abs_ideal (f x) | x . x \<in> F }"
    using 2 by simp
  also have "... = Sup_fin { Abs_ideal (f x) | x . x \<in> insert y F }"
    apply (subst Sup_fin.insert[symmetric])
    using 2 apply simp
    using 2 apply simp
    by (auto intro: arg_cong[where f="Sup_fin"])
  finally show "Abs_ideal (Sup_fin { f x | x . x \<in> insert y F }) = Sup_fin { Abs_ideal (f x) | x . x \<in> insert y F }"
    .
qed

lemma sra_to_mat_mult_homomorphism:
  "sra_to_mat (x * y) = sra_to_mat x \<odot> sra_to_mat y"
proof (rule ext,unfold split_paired_all)
  fix p q
  have "sra_to_mat (x * y) (p,q) = Abs_ideal ((Rep_ideal_point p)\<^sup>T * (x * y) * Rep_ideal_point q)"
    by (unfold sra_to_mat_def, simp)
  also have "... = Abs_ideal ((Rep_ideal_point p)\<^sup>T * x * 1 * y * Rep_ideal_point q)"
    by (simp add: mult.assoc)
  also have "... = Abs_ideal ((Rep_ideal_point p)\<^sup>T * x * Sup_fin { r * r\<^sup>T | r . ideal_point r } * y * Rep_ideal_point q)"
    by (unfold one_sup_ideal_points[symmetric], simp)
  also have "... = Abs_ideal ((Rep_ideal_point p)\<^sup>T * x * Sup_fin { Rep_ideal_point r * (Rep_ideal_point r)\<^sup>T | r . r \<in> UNIV } * y * Rep_ideal_point q)"
  proof -
    have "{ r * r\<^sup>T | r::'a . ideal_point r } = { Rep_ideal_point r * (Rep_ideal_point r)\<^sup>T | r . r \<in> UNIV }"
    proof (rule set_eqI)
      fix x
      show "x \<in> { r * r\<^sup>T | r::'a . ideal_point r } \<longleftrightarrow> x \<in> { Rep_ideal_point r * (Rep_ideal_point r)\<^sup>T | r . r \<in> UNIV }"
      proof
        assume "x \<in> { r * r\<^sup>T | r::'a . ideal_point r }"
        from this obtain r where 1: "ideal_point r \<and> x = r * r\<^sup>T"
          by auto
        hence "Rep_ideal_point (Abs_ideal_point r) = r"
          using Abs_ideal_point_inverse by auto
        thus "x \<in> { Rep_ideal_point r * (Rep_ideal_point r)\<^sup>T | r . r \<in> UNIV }"
          using 1 by (metis (mono_tags, lifting) UNIV_I mem_Collect_eq)
      next
        assume "x \<in> { Rep_ideal_point r * (Rep_ideal_point r)\<^sup>T | r . r \<in> UNIV }"
        from this obtain r where "x = Rep_ideal_point r * (Rep_ideal_point r)\<^sup>T"
          by auto
        thus "x \<in> { r * r\<^sup>T | r::'a . ideal_point r }"
          using Rep_ideal_point by blast
      qed
    qed
    thus ?thesis
      by simp
  qed
  also have "... = Abs_ideal (Sup_fin { (Rep_ideal_point p)\<^sup>T * x * Rep_ideal_point r * (Rep_ideal_point r)\<^sup>T | r . r \<in> UNIV } * (y * Rep_ideal_point q))"
    by (subst mult_left_dist_sup_fin, simp_all add: mult.assoc)
  also have "... = Abs_ideal (Sup_fin { (Rep_ideal_point p)\<^sup>T * x * Rep_ideal_point r * (Rep_ideal_point r)\<^sup>T * y * Rep_ideal_point q | r . r \<in> UNIV })"
    by (subst mult_right_dist_sup_fin, simp_all add: mult.assoc)
  also have "... = Sup_fin { Abs_ideal ((Rep_ideal_point p)\<^sup>T * x * Rep_ideal_point r * (Rep_ideal_point r)\<^sup>T * y * Rep_ideal_point q) | r . r \<in> UNIV }"
  proof -
    have 1: "\<And>r . ideal ((Rep_ideal_point p)\<^sup>T * x * Rep_ideal_point r * (Rep_ideal_point r)\<^sup>T * y * Rep_ideal_point q)"
    proof -
      fix r :: "'a ideal_point"
      have "\<And>x . ideal_point (Rep_ideal_point x::'a)"
        using Rep_ideal_point by blast
      thus "ideal ((Rep_ideal_point p)\<^sup>T * x * Rep_ideal_point r * (Rep_ideal_point r)\<^sup>T * y * Rep_ideal_point q)"
        by (simp add: covector_mult_closed vector_conv_covector vector_mult_closed)
    qed
    show ?thesis
      apply (rule Abs_ideal_dist_sup_fin)
      using 1 by simp_all
  qed
  also have "... = (\<Squnion>\<^sub>r Abs_ideal ((Rep_ideal_point p)\<^sup>T * x * Rep_ideal_point r * (Rep_ideal_point r)\<^sup>T * y * Rep_ideal_point q))"
    by (rule sup_fin_sum)
  also have "... = (\<Squnion>\<^sub>r Abs_ideal ((Rep_ideal_point p)\<^sup>T * x * Rep_ideal_point r \<sqinter> (Rep_ideal_point r)\<^sup>T * y * Rep_ideal_point q))"
  proof -
    have "\<And>r . (Rep_ideal_point p)\<^sup>T * x * Rep_ideal_point r * ((Rep_ideal_point r)\<^sup>T * y * Rep_ideal_point q) = (Rep_ideal_point p)\<^sup>T * x * Rep_ideal_point r \<sqinter> (Rep_ideal_point r)\<^sup>T * y * Rep_ideal_point q"
    proof (rule ideal_mult_inf)
      fix r :: "'a ideal_point"
      have 2: "\<And>x . ideal_point (Rep_ideal_point x::'a)"
        using Rep_ideal_point by blast
      thus "ideal ((Rep_ideal_point p)\<^sup>T * x * Rep_ideal_point r)"
        by (simp add: covector_mult_closed vector_conv_covector vector_mult_closed)
      show "ideal ((Rep_ideal_point r)\<^sup>T * y * Rep_ideal_point q)"
        using 2 by (simp add: covector_mult_closed vector_conv_covector vector_mult_closed)
    qed
    thus ?thesis
      by (simp add: mult.assoc)
  qed
  also have "... = (\<Squnion>\<^sub>r Abs_ideal ((Rep_ideal_point p)\<^sup>T * x * Rep_ideal_point r) * Abs_ideal ((Rep_ideal_point r)\<^sup>T * y * Rep_ideal_point q))"
  proof -
    have "\<And>r . Abs_ideal ((Rep_ideal_point p)\<^sup>T * x * Rep_ideal_point r \<sqinter> (Rep_ideal_point r)\<^sup>T * y * Rep_ideal_point q) = Abs_ideal ((Rep_ideal_point p)\<^sup>T * x * Rep_ideal_point r) * Abs_ideal ((Rep_ideal_point r)\<^sup>T * y * Rep_ideal_point q)"
    proof (rule times_ideal.abs_eq[symmetric])
      fix r :: "'a ideal_point"
      have 3: "\<And>x . ideal_point (Rep_ideal_point x::'a)"
        using Rep_ideal_point by blast
      hence 4: "covector ((Rep_ideal_point p)\<^sup>T) \<and> covector ((Rep_ideal_point r)\<^sup>T)"
        using vector_conv_covector by blast
      thus "eq_onp ideal ((Rep_ideal_point p)\<^sup>T * x * Rep_ideal_point r) ((Rep_ideal_point p)\<^sup>T * x * Rep_ideal_point r)"
        using 3 by (simp add: comp_associative covector_mult_closed eq_onp_same_args)
      show "eq_onp ideal ((Rep_ideal_point r)\<^sup>T * y * Rep_ideal_point q) ((Rep_ideal_point r)\<^sup>T * y * Rep_ideal_point q)"
        using 3 4 by (simp add: comp_associative covector_mult_closed eq_onp_same_args)
    qed
    thus ?thesis
      by simp
  qed
  also have "... = (\<Squnion>\<^sub>r sra_to_mat x (p,r) * sra_to_mat y (r,q))"
    by (unfold sra_to_mat_def, simp)
  finally show "sra_to_mat (x * y) (p,q) = (sra_to_mat x \<odot> sra_to_mat y) (p,q)"
    by (simp add: times_matrix_def)
qed

end

