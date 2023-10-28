theory Cardinality

imports "List-Infinite.InfiniteSet2" Representation

begin

context uminus
begin

no_notation uminus ("- _" [81] 80)

end

section \<open>Atoms Below an Element in Partial Orders\<close>

text \<open>
We define the set and the number of atoms below an element in a partial order.
To handle infinitely many atoms we use \<open>enat\<close>, which are natural numbers with infinity, and \<open>icard\<close>, which modifies \<open>card\<close> by giving a separate option of being infinite.
We include general results about \<open>enat\<close>, \<open>icard\<close>, sets functions and atoms.
\<close>

lemma enat_mult_strict_mono:
  assumes "a < b" "c < d" "(0::enat) < b" "0 \<le> c"
  shows "a * c < b * d"
proof -
  have "a \<noteq> \<infinity> \<and> c \<noteq> \<infinity>"
    using assms(1,2) linorder_not_le by fastforce
  thus ?thesis
    using assms by (smt (verit, del_insts) enat_0_less_mult_iff idiff_eq_conv_enat ileI1 imult_ile_mono imult_is_infinity_enat less_eq_idiff_eq_sum less_le_not_le mult_eSuc_right order.strict_trans1 order_le_neq_trans zero_enat_def)
qed

lemma enat_mult_strict_mono':
  assumes "a < b" and "c < d" and "(0::enat) \<le> a" and "0 \<le> c"
  shows "a * c < b * d"
  using assms by (auto simp add: enat_mult_strict_mono)

lemma finite_icard_card:
  "finite A \<Longrightarrow> icard A = icard B \<Longrightarrow> card A = card B"
  by (metis icard_def icard_eq_enat_imp_card)

lemma icard_eq_sum:
  "finite A \<Longrightarrow> icard A = sum (\<lambda>x. 1) A"
  by (simp add: icard_def of_nat_eq_enat)

lemma icard_sum_constant_function:
  assumes "\<forall>x\<in>A . f x = c"
      and "finite A"
    shows "sum f A = (icard A) * c"
  by (metis assms icard_finite_conv of_nat_eq_enat sum.cong sum_constant)

lemma icard_le_finite:
  assumes "icard A \<le> icard B"
      and "finite B"
    shows "finite A"
  by (metis assms enat_ord_simps(5) icard_infinite_conv)

lemma bij_betw_same_icard:
  "bij_betw f A B \<Longrightarrow> icard A = icard B"
  by (simp add: bij_betw_finite bij_betw_same_card icard_def)

lemma surj_icard_le: "B \<subseteq> f ` A \<Longrightarrow> icard B \<le> icard A"
  by (meson icard_image_le icard_mono preorder_class.order_trans)

lemma icard_image_part_le:
  assumes "\<forall>x\<in>A . f x \<subseteq> B"
      and "\<forall>x\<in>A . f x \<noteq> {}"
      and "\<forall>x\<in>A . \<forall>y\<in>A . x \<noteq> y \<longrightarrow> f x \<inter> f y = {}"
    shows "icard A \<le> icard B"
proof -
  have "\<forall>x\<in>A . \<exists>y . y \<in> f x \<inter> B"
    using assms(1,2) by fastforce
  hence "\<exists>g . \<forall>x\<in>A . g x \<in> f x \<inter> B"
    using bchoice by simp
  from this obtain g where 1: "\<forall>x\<in>A . g x \<in> f x \<inter> B"
    by auto
  hence "inj_on g A"
    by (metis Int_iff assms(3) empty_iff inj_onI)
  thus "icard A \<le> icard B"
    using 1 icard_inj_on_le by fastforce
qed

lemma finite_image_part_le:
  assumes "\<forall>x\<in>A . f x \<subseteq> B"
      and "\<forall>x\<in>A . f x \<noteq> {}"
      and "\<forall>x\<in>A . \<forall>y\<in>A . x \<noteq> y \<longrightarrow> f x \<inter> f y = {}"
      and "finite B"
    shows "finite A"
  by (metis assms icard_image_part_le icard_le_finite)

context semiring_1
begin

lemma sum_constant_function:
  assumes "\<forall>x\<in>A . f x = c"
    shows "sum f A = of_nat (card A) * c"
proof (cases "finite A")
  case True
  show ?thesis
  proof (rule finite_subset_induct)
    show "finite A"
      using True by simp
    show "A \<subseteq> A"
      by simp
    show "sum f {} = of_nat (card {}) * c"
      by simp
    fix a F
    assume "finite F" "a \<in> A" "a \<notin> F" "sum f F = of_nat (card F) * c"
    thus "sum f (insert a F) = of_nat (card (insert a F)) * c"
      using assms by (metis sum.insert sum_constant)
  qed
next
  case False
  thus ?thesis
    by simp
qed

end

context order
begin

lemma ne_finite_has_minimal:
  assumes "finite S"
      and "S \<noteq> {}"
    shows "\<exists>m\<in>S . \<forall>x\<in>S . x \<le> m \<longrightarrow> x = m"
proof (rule finite_ne_induct)
  show "finite S"
    using assms(1) by simp
  show "S \<noteq> {}"
    using assms(2) by simp
  show "\<And>x . \<exists>m\<in>{x}. \<forall>y\<in>{x}. y \<le> m \<longrightarrow> y = m"
    by auto
  show "\<And>x F . finite F \<Longrightarrow> F \<noteq> {} \<Longrightarrow> x \<notin> F \<Longrightarrow> (\<exists>m\<in>F . \<forall>y\<in>F . y \<le> m \<longrightarrow> y = m) \<Longrightarrow> (\<exists>m\<in>insert x F . \<forall>y\<in>insert x F . y \<le> m \<longrightarrow> y = m)"
    by (metis finite_insert insert_not_empty finite_has_minimal)
qed

end

context order_bot
begin

abbreviation atoms_below :: "'a \<Rightarrow> 'a set" ("AB")
  where "atoms_below x \<equiv> { a . atom a \<and> a \<le> x }"

definition num_atoms_below :: "'a \<Rightarrow> enat" ("nAB")
  where "num_atoms_below x \<equiv> icard (atoms_below x)"

lemma AB_iso:
  "x \<le> y \<Longrightarrow> AB x \<subseteq> AB y"
  by (simp add: Collect_mono dual_order.trans)

lemma AB_bot:
  "AB bot = {}"
  by (simp add: bot_unique)

lemma nAB_bot:
  "nAB bot = 0"
proof -
  have "nAB bot = icard (AB bot)"
    by (simp add: num_atoms_below_def)
  also have "... = 0"
    by (metis (mono_tags, lifting) AB_bot icard_empty)
  finally show ?thesis
    .
qed

lemma AB_atom:
  "atom a \<longleftrightarrow> AB a = {a}"
  by blast

lemma nAB_atom:
  "atom a \<Longrightarrow> nAB a = 1"
proof -
  assume "atom a"
  hence "AB a = {a}"
    using AB_atom by meson
  thus "nAB a = 1"
    by (simp add: num_atoms_below_def one_eSuc)
qed

lemma nAB_iso:
  "x \<le> y \<Longrightarrow> nAB x \<le> nAB y"
  using icard_mono AB_iso num_atoms_below_def by auto

end

context bounded_semilattice_sup_bot
begin

lemma nAB_iso_sup:
  "nAB x \<le> nAB (x \<squnion> y)"
  by (simp add: nAB_iso)

end

context bounded_lattice
begin

lemma different_atoms_disjoint:
  "atom x \<Longrightarrow> atom y \<Longrightarrow> x \<noteq> y \<Longrightarrow> x \<sqinter> y = bot"
  using inf_le1 le_iff_inf by auto

lemma AB_dist_inf:
  "AB (x \<sqinter> y) = AB x \<inter> AB y"
  by auto

lemma AB_iso_inf:
  "AB (x \<sqinter> y) \<subseteq> AB x"
  by (simp add: Collect_mono)

lemma AB_iso_sup:
  "AB x \<subseteq> AB (x \<squnion> y)"
  by (simp add: Collect_mono le_supI1)

lemma AB_disjoint:
  assumes "x \<sqinter> y = bot"
    shows "AB x \<inter> AB y = {}"
proof (rule Int_emptyI)
  fix a
  assume "a \<in> AB x" "a \<in> AB y"
  hence "atom a \<and> a \<le> x \<and> a \<le> y"
    by simp
  thus False
    using assms bot_unique by fastforce
qed

lemma nAB_iso_inf:
  "nAB (x \<sqinter> y) \<le> nAB x"
  by (simp add: nAB_iso)

end

context distrib_lattice_bot
begin

lemma atom_in_sup:
  assumes "atom a"
      and "a \<le> x \<squnion> y"
    shows "a \<le> x \<or> a \<le> y"
proof -
  have 1: "a = (a \<sqinter> x) \<squnion> (a \<sqinter> y)"
    using assms(2) inf_sup_distrib1 le_iff_inf by force
  have "a \<sqinter> x = bot \<or> a \<sqinter> x = a"
    using assms(1) by fastforce
  thus ?thesis
    using 1 le_iff_inf sup_bot_left by fastforce
qed

lemma atom_in_sup_iff:
  assumes "atom a"
    shows "a \<le> x \<squnion> y \<longleftrightarrow> a \<le> x \<or> a \<le> y"
  using assms atom_in_sup le_supI1 le_supI2 by blast

lemma atom_in_sup_xor:
  "atom a \<Longrightarrow> a \<le> x \<squnion> y \<Longrightarrow> x \<sqinter> y = bot \<Longrightarrow> (a \<le> x \<and> \<not> a \<le> y) \<or> (\<not> a \<le> x \<and> a \<le> y)"
  using atom_in_sup bot_unique le_inf_iff by blast

lemma atom_in_sup_xor_iff:
  assumes "atom a"
      and "x \<sqinter> y = bot"
    shows "a \<le> x \<squnion> y \<longleftrightarrow> (a \<le> x \<and> \<not> a \<le> y) \<or> (\<not> a \<le> x \<and> a \<le> y)"
  using assms atom_in_sup_xor le_supI1 le_supI2 by auto

lemma AB_dist_sup:
  "AB (x \<squnion> y) = AB x \<union> AB y"
proof
  show "AB (x \<squnion> y) \<subseteq> AB x \<union> AB y"
    using atom_in_sup by fastforce
next
  show "AB x \<union> AB y \<subseteq> AB (x \<squnion> y)"
    using le_supI1 le_supI2 by fastforce
qed

end

context bounded_distrib_lattice
begin

lemma nAB_add:
  "nAB x + nAB y = nAB (x \<squnion> y) + nAB (x \<sqinter> y)"
proof -
  have "nAB x + nAB y = icard (AB x \<union> AB y) + icard (AB x \<inter> AB y)"
    using num_atoms_below_def icard_Un_Int by auto
  also have "... = nAB (x \<squnion> y) + nAB (x \<sqinter> y)"
    using num_atoms_below_def AB_dist_inf AB_dist_sup by auto
  finally show ?thesis
    .
qed

lemma nAB_split_disjoint:
  assumes "x \<sqinter> y = bot"
    shows "nAB (x \<squnion> y) = nAB x + nAB y"
  by (simp add: assms nAB_add nAB_bot)

end

context p_algebra
begin

lemma atom_in_p:
  "atom a \<Longrightarrow> a \<le> x \<or> a \<le> -x"
  using inf.orderI pseudo_complement by force

lemma atom_in_p_xor:
  "atom a \<Longrightarrow> (a \<le> x \<and> \<not> a \<le> -x) \<or> (\<not> a \<le> x \<and> a \<le> -x)"
  by (metis atom_in_p le_iff_inf pseudo_complement)

text \<open>
The following two lemmas also hold in distributive lattices with a least element (see above).
However, p-algebras are not necessarily distributive, so the following results are indepenent.
\<close>

lemma atom_in_sup':
  "atom a \<Longrightarrow> a \<le> x \<squnion> y \<Longrightarrow> a \<le> x \<or> a \<le> y"
  by (metis inf.absorb_iff2 inf.sup_ge2 pseudo_complement sup_least)

lemma AB_dist_sup':
  "AB (x \<squnion> y) = AB x \<union> AB y"
proof
  show "AB (x \<squnion> y) \<subseteq> AB x \<union> AB y"
    using atom_in_sup' by fastforce
next
  show "AB x \<union> AB y \<subseteq> AB (x \<squnion> y)"
    using le_supI1 le_supI2 by fastforce
qed

lemma AB_split_1:
  "AB x = AB ((x \<sqinter> y) \<squnion> (x \<sqinter> -y))"
proof
  show "AB x \<subseteq> AB ((x \<sqinter> y) \<squnion> (x \<sqinter> -y))"
  proof
    fix a
    assume "a \<in> AB x"
    hence "atom a \<and> a \<le> x"
      by simp
    hence "atom a \<and> a \<le> (x \<sqinter> y) \<squnion> (x \<sqinter> -y)"
      by (metis atom_in_p_xor inf.boundedI le_supI1 le_supI2)
    thus "a \<in> AB ((x \<sqinter> y) \<squnion> (x \<sqinter> -y))"
      by simp
  qed
next
  show "AB ((x \<sqinter> y) \<squnion> (x \<sqinter> -y)) \<subseteq> AB x"
    using atom_in_sup' inf.boundedE by blast
qed

lemma AB_split_2:
  "AB x = AB (x \<sqinter> y) \<union> AB (x \<sqinter> -y)"
  using AB_dist_sup' AB_split_1 by auto

lemma AB_split_2_disjoint:
  "AB (x \<sqinter> y) \<inter> AB (x \<sqinter> -y) = {}"
  using atom_in_p_xor by fastforce

lemma AB_pp:
  "AB (--x) = AB x"
  by (metis (opaque_lifting) atom_in_p_xor)

lemma nAB_pp:
  "nAB (--x) = nAB x"
  using AB_pp num_atoms_below_def by auto

lemma nAB_split_1:
  "nAB x = nAB ((x \<sqinter> y) \<squnion> (x \<sqinter> - y))"
  using AB_split_1 num_atoms_below_def by simp

lemma nAB_split_2:
  "nAB x = nAB (x \<sqinter> y) + nAB (x \<sqinter> -y)"
proof -
  have "icard (AB (x \<sqinter> y)) + icard (AB (x \<sqinter> -y)) = icard (AB (x \<sqinter> y) \<union> AB (x \<sqinter> -y)) + icard (AB (x \<sqinter> y) \<inter> AB (x \<sqinter> -y))"
    using icard_Un_Int by auto
  also have "... = icard (AB x)"
    using AB_split_2 AB_split_2_disjoint by auto
  finally show ?thesis
    using num_atoms_below_def by auto
qed

end

section \<open>Atoms Below an Element in Stone Relation Algebras\<close>

text \<open>
We extend our study of atoms below an element to Stone relation algebras.
We consider combinations of the following five assumptions: the Stone relation algebra is atomic, atom-rectangular, atom-simple, a relation algebra, or has finitely many atoms.
We include general properties of atoms, rectangles and simple elements.
\<close>

context stone_relation_algebra
begin

abbreviation rectangle :: "'a \<Rightarrow> bool" where "rectangle x \<equiv> x * top * x \<le> x"
abbreviation simple    :: "'a \<Rightarrow> bool" where "simple x    \<equiv> top * x * top = top"

lemma rectangle_eq:
  "rectangle x \<longleftrightarrow> x * top * x = x"
  by (simp add: order.eq_iff ex231d)

lemma arc_univalent_injective_rectangle_simple:
  "arc a \<longleftrightarrow> univalent a \<and> injective a \<and> rectangle a \<and> simple a"
  by (smt (z3) arc_top_arc comp_associative conv_dist_comp conv_involutive ideal_top_closed surjective_vector_top rectangle_eq)

lemma conv_atom:
  "atom x \<Longrightarrow> atom (x\<^sup>T)"
  by (metis conv_involutive conv_isotone symmetric_bot_closed)

lemma conv_atom_iff:
  "atom x \<longleftrightarrow> atom (x\<^sup>T)"
  by (metis conv_atom conv_involutive)

lemma counterexample_different_atoms_top_disjoint:
  "atom x \<Longrightarrow> atom y \<Longrightarrow> x \<noteq> y \<Longrightarrow> x * top \<sqinter> y = bot"
  nitpick[expect=genuine,card=4]
  oops

lemma counterexample_different_univalent_atoms_top_disjoint:
  "atom x \<Longrightarrow> univalent x \<Longrightarrow> atom y \<Longrightarrow> univalent y \<Longrightarrow> x \<noteq> y \<Longrightarrow> x * top \<sqinter> y = bot"
  nitpick[expect=genuine,card=4]
  oops

lemma AB_card_4_1:
  "a \<le> x \<and> a \<le> y \<longleftrightarrow> a \<le> x \<squnion> y \<and> a \<le> x \<sqinter> y"
  using le_supI1 by auto

lemma AB_card_4_2:
  assumes "atom a"
    shows "(a \<le> x \<and> \<not> a \<le> y) \<or> (\<not> a \<le> x \<and> a \<le> y) \<longleftrightarrow> a \<le> x \<squnion> y \<and> \<not> a \<le> x \<sqinter> y"
  using assms atom_in_sup le_supI1 le_supI2 by auto

lemma AB_card_4_3:
  assumes "atom a"
    shows "\<not> a \<le> x \<and> \<not> a \<le> y \<longleftrightarrow> \<not> a \<le> x \<squnion> y \<and> \<not> a \<le> x \<sqinter> y"
  using assms AB_card_4_2 by auto

lemma AB_card_5_1:
  assumes "atom a"
      and "a \<le> x\<^sup>T * y \<sqinter> z"
    shows "x * a \<sqinter> y \<le> x * z \<sqinter> y"
      and "x * a \<sqinter> y \<noteq> bot"
proof -
  show "x * a \<sqinter> y \<le> x * z \<sqinter> y"
    using assms(2) comp_inf.mult_left_isotone mult_right_isotone by auto
  show "x * a \<sqinter> y \<noteq> bot"
    by (smt assms inf.left_commute inf.left_idem inf_absorb1 schroeder_1)
qed

lemma AB_card_5_2:
  assumes "univalent x"
      and "atom a"
      and "atom b"
      and "b \<le> x\<^sup>T * y \<sqinter> z"
      and "a \<noteq> b"
    shows "(x * a \<sqinter> y) \<sqinter> (x * b \<sqinter> y) = bot"
      and "x * a \<sqinter> y \<noteq> x * b \<sqinter> y"
proof -
  show "(x * a \<sqinter> y) \<sqinter> (x * b \<sqinter> y) = bot"
    by (metis assms(1-3,5) comp_inf.semiring.mult_zero_left inf.cobounded1 inf.left_commute inf.sup_monoid.add_commute semiring.mult_not_zero univalent_comp_left_dist_inf)
  thus "x * a \<sqinter> y \<noteq> x * b \<sqinter> y"
    using AB_card_5_1(2) assms(3,4) by fastforce
qed

lemma AB_card_6_0:
  assumes "univalent x"
      and "atom a"
      and "a \<le> x"
      and "atom b"
      and "b \<le> x"
      and "a \<noteq> b"
    shows "a * top \<sqinter> b * top = bot"
proof -
  have "a\<^sup>T * b \<le> 1"
    by (meson assms(1,3,5) comp_isotone conv_isotone dual_order.trans)
  hence "a * top \<sqinter> b = bot"
    by (metis assms(2,4,6) comp_inf.semiring.mult_zero_left comp_right_one inf.cobounded1 inf.cobounded2 inf.orderE schroeder_1)
  thus ?thesis
    using vector_bot_closed vector_export_comp by force
qed

lemma AB_card_6_1:
  assumes "atom a"
      and "a \<le> x \<sqinter> y * z\<^sup>T"
    shows "a * z \<sqinter> y \<le> x * z \<sqinter> y"
      and "a * z \<sqinter> y \<noteq> bot"
proof -
  show "a * z \<sqinter> y \<le> x * z \<sqinter> y"
    using assms(2) inf.sup_left_isotone mult_left_isotone by auto
  show "a * z \<sqinter> y \<noteq> bot"
    by (metis assms inf.absorb2 inf.boundedE schroeder_2)
qed

lemma AB_card_6_2:
  assumes "univalent x"
      and "atom a"
      and "a \<le> x \<sqinter> y * z\<^sup>T"
      and "atom b"
      and "b \<le> x \<sqinter> y * z\<^sup>T"
      and "a \<noteq> b"
    shows "(a * z \<sqinter> y) \<sqinter> (b * z \<sqinter> y) = bot"
      and "a * z \<sqinter> y \<noteq> b * z \<sqinter> y"
proof -
  have "(a * z \<sqinter> y) \<sqinter> (b * z \<sqinter> y) \<le> a * top \<sqinter> b * top"
    by (meson comp_inf.comp_isotone comp_inf.ex231d inf.boundedE mult_right_isotone)
  also have "... = bot"
    using AB_card_6_0 assms by force
  finally show "(a * z \<sqinter> y) \<sqinter> (b * z \<sqinter> y) = bot"
    using le_bot by blast
  thus "a * z \<sqinter> y \<noteq> b * z \<sqinter> y"
    using AB_card_6_1(2) assms(4,5) by fastforce
qed

lemma nAB_conv:
  "nAB x = nAB (x\<^sup>T)"
proof (unfold num_atoms_below_def, rule bij_betw_same_icard)
  show "bij_betw conv (AB x) (AB (x\<^sup>T))"
  proof (unfold bij_betw_def, rule conjI)
    show "inj_on conv (AB x)"
      by (metis (mono_tags, lifting) inj_onI conv_involutive)
    show "conv ` AB x = AB (x\<^sup>T)"
    proof
      show "conv ` AB x \<subseteq> AB (x\<^sup>T)"
        using conv_atom_iff conv_isotone by force
      show "AB (x\<^sup>T) \<subseteq> conv ` AB x"
      proof
        fix y
        assume "y \<in> AB (x\<^sup>T)"
        hence "atom y \<and> y \<le> x\<^sup>T"
          by auto
        hence "atom (y\<^sup>T) \<and> y\<^sup>T \<le> x"
          using conv_atom_iff conv_order by force
        hence "y\<^sup>T \<in> AB x"
          by auto
        thus "y \<in> conv ` AB x"
          by (metis (no_types, lifting) image_iff conv_involutive)
      qed
    qed
  qed
qed

lemma domain_atom:
  assumes "atom a"
    shows "atom (a * top \<sqinter> 1)"
proof
  show "a * top \<sqinter> 1 \<noteq> bot"
    by (metis assms domain_vector_conv ex231a inf_vector_comp mult_left_zero vector_export_comp_unit)
next
  show "\<forall>y. y \<noteq> bot \<and> y \<le> a * top \<sqinter> 1 \<longrightarrow> y = a * top \<sqinter> 1"
  proof (rule allI, rule impI)
    fix y
    assume 1: "y \<noteq> bot \<and> y \<le> a * top \<sqinter> 1"
    hence 2: "y = 1 \<sqinter> y * a * top"
      using dedekind_injective comp_associative coreflexive_idempotent coreflexive_symmetric inf.absorb2 inf.sup_monoid.add_commute by auto
    hence "y * a \<noteq> bot"
      using 1 comp_inf.semiring.mult_zero_right vector_bot_closed by force
    hence "a = y * a"
      using 1 by (metis assms comp_right_one coreflexive_comp_top_inf inf.boundedE mult_sub_right_one)
    thus "y = a * top \<sqinter> 1"
      using 2 inf.sup_monoid.add_commute by auto
  qed
qed

lemma codomain_atom:
  assumes "atom a"
    shows "atom (top * a \<sqinter> 1)"
proof -
  have "top * a \<sqinter> 1 = a\<^sup>T * top \<sqinter> 1"
    by (simp add: domain_vector_covector inf.sup_monoid.add_commute)
  thus ?thesis
    using domain_atom conv_atom assms by auto
qed

lemma atom_rectangle_atom_one_rep:
  "(\<forall>a . atom a \<longrightarrow> a * top * a \<le> a) \<longleftrightarrow> (\<forall>a . atom a \<and> a \<le> 1 \<longrightarrow> a * top * a \<le> 1)"
proof
  assume "\<forall>a . atom a \<longrightarrow> a * top * a \<le> a"
  thus "\<forall>a . atom a \<and> a \<le> 1 \<longrightarrow> a * top * a \<le> 1"
    by auto
next
  assume 1: "\<forall>a . atom a \<and> a \<le> 1 \<longrightarrow> a * top * a \<le> 1"
  show "\<forall>a . atom a \<longrightarrow> a * top * a \<le> a"
  proof (rule allI, rule impI)
    fix a
    assume "atom a"
    hence "atom (a * top \<sqinter> 1)"
      by (simp add: domain_atom)
    hence "(a * top \<sqinter> 1) * top * (a * top \<sqinter> 1) \<le> 1"
      using 1 by simp
    hence "a * top * a\<^sup>T \<le> 1"
      by (smt comp_associative conv_dist_comp coreflexive_symmetric ex231e inf_top.right_neutral symmetric_top_closed vector_export_comp_unit)
    thus "a * top * a \<le> a"
      by (smt comp_associative conv_dist_comp domain_vector_conv order.eq_iff ex231e inf.absorb2 inf.sup_monoid.add_commute mapping_one_closed symmetric_top_closed top_right_mult_increasing vector_export_comp_unit)
  qed
qed

lemma AB_card_2_1:
  assumes "a * top * a \<le> a"
    shows "(a * top \<sqinter> 1) * top * (top * a \<sqinter> 1) = a"
  by (metis assms comp_inf.vector_top_closed covector_comp_inf ex231d order.antisym inf_commute surjective_one_closed vector_export_comp_unit vector_top_closed mult_assoc)

lemma atomsimple_atom1simple:
  "(\<forall>a . atom a \<longrightarrow> top * a * top = top) \<longleftrightarrow> (\<forall>a . atom a \<and> a \<le> 1 \<longrightarrow> top * a * top = top)"
proof
  assume "\<forall>a . atom a \<longrightarrow> top * a * top = top"
  thus "\<forall>a . atom a \<and> a \<le> 1 \<longrightarrow> top * a * top = top"
    by simp
next
  assume 1: "\<forall>a . atom a \<and> a \<le> 1 \<longrightarrow> top * a * top = top"
  show "\<forall>a . atom a \<longrightarrow> top * a * top = top"
  proof (rule allI, rule impI)
    fix a
    assume "atom a"
    hence 2: "atom (a * top \<sqinter> 1)"
      by (simp add: domain_atom)
    have "top * (a * top \<sqinter> 1) * top = top * a * top"
      using comp_associative vector_export_comp_unit by auto
    thus "top * a * top = top"
      using 1 2 by auto
  qed
qed

lemma AB_card_2_2:
  assumes "atom a"
      and "a \<le> 1"
      and "atom b"
      and "b \<le> 1"
      and "\<forall>a . atom a \<longrightarrow> top * a * top = top"
    shows "a * top * b * top \<sqinter> 1 = a" and "top * a * top * b \<sqinter> 1 = b"
proof -
  show "a * top * b * top \<sqinter> 1 = a"
    using assms(2,3,5) comp_associative coreflexive_comp_top_inf_one by auto
  show "top * a * top * b \<sqinter> 1 = b"
    using assms(1,4,5) epm_3 inf.sup_monoid.add_commute by auto
qed

abbreviation dom_cod :: "'a \<Rightarrow> 'a \<times> 'a"
  where "dom_cod a \<equiv> (a * top \<sqinter> 1, top * a \<sqinter> 1)"

lemma dom_cod_atoms_1:
  "dom_cod ` AB top \<subseteq> AB 1 \<times> AB 1"
proof
  fix x
  assume "x \<in> dom_cod ` AB top"
  from this obtain a where 1: "atom a \<and> x = dom_cod a"
    by auto
  hence "a * top \<sqinter> 1 \<in> AB 1 \<and> top * a \<sqinter> 1 \<in> AB 1"
    using domain_atom codomain_atom by auto
  thus "x \<in> AB 1 \<times> AB 1"
    using 1 by auto
qed

end

subsection \<open>Atomic\<close>

class stone_relation_algebra_atomic = stone_relation_algebra +
  assumes atomic: "x \<noteq> bot \<longrightarrow> (\<exists>a . atom a \<and> a \<le> x)"
begin

lemma AB_nonempty:
  "x \<noteq> bot \<Longrightarrow> AB x \<noteq> {}"
  using atomic by fastforce

lemma AB_nonempty_iff:
  "x \<noteq> bot \<longleftrightarrow> AB x \<noteq> {}"
  using AB_nonempty AB_bot by blast

lemma atomsimple_simple:
  "(\<forall>a . a \<noteq> bot \<longrightarrow> top * a * top = top) \<longleftrightarrow> (\<forall>a . atom a \<longrightarrow> top * a * top = top)"
proof
  assume "\<forall>a . a \<noteq> bot \<longrightarrow> top * a * top = top"
  thus "\<forall>a . atom a \<longrightarrow> top * a * top = top"
    by simp
next
  assume 1: "\<forall>a . atom a \<longrightarrow> top * a * top = top"
  show "\<forall>a . a \<noteq> bot \<longrightarrow> top * a * top = top"
  proof (rule allI, rule impI)
    fix a
    assume "a \<noteq> bot"
    from this atomic obtain b where 2: "atom b \<and> b \<le> a"
      by auto
    hence "top * b * top = top"
      using 1 by auto
    thus "top * a * top = top"
      using 2 by (metis order.antisym mult_left_isotone mult_right_isotone top.extremum)
  qed
qed

lemma AB_card_2_3:
  assumes "a \<noteq> bot"
      and "a \<le> 1"
      and "b \<noteq> bot"
      and "b \<le> 1"
      and "\<forall>a . a \<noteq> bot \<longrightarrow> top * a * top = top"
    shows "a * top * b * top \<sqinter> 1 = a" and "top * a * top * b \<sqinter> 1 = b"
proof -
  show "a * top * b * top \<sqinter> 1 = a"
    using assms(2,3,5) comp_associative coreflexive_comp_top_inf_one by auto
  show "top * a * top * b \<sqinter> 1 = b"
    using assms(1,4,5) epm_3 inf.sup_monoid.add_commute by auto
qed

lemma injective_down_closed:
  "x \<le> y \<Longrightarrow> injective y \<Longrightarrow> injective x"
  using conv_isotone mult_isotone by fastforce

lemma univalent_down_closed:
  "x \<le> y \<Longrightarrow> univalent y \<Longrightarrow> univalent x"
  using conv_isotone mult_isotone by fastforce

lemma nAB_bot_iff:
  "x = bot \<longleftrightarrow> nAB x = 0"
  by (smt (verit, best) icard_0_eq AB_nonempty_iff num_atoms_below_def)

text \<open>
It is unclear if \<open>atomic\<close> is necessary for the following two results, but it seems likely.
\<close>

lemma nAB_univ_comp_meet:
  assumes "univalent x"
    shows "nAB (x\<^sup>T * y \<sqinter> z) \<le> nAB (x * z \<sqinter> y)"
proof (unfold num_atoms_below_def, rule icard_image_part_le)
  show "\<forall>a \<in> AB (x\<^sup>T * y \<sqinter> z) . AB (x * a \<sqinter> y) \<subseteq> AB (x * z \<sqinter> y)"
  proof
    fix a
    assume "a \<in> AB (x\<^sup>T * y \<sqinter> z)"
    hence "x * a \<sqinter> y \<le> x * z \<sqinter> y"
      using AB_card_5_1(1) by auto
    thus "AB (x * a \<sqinter> y) \<subseteq> AB (x * z \<sqinter> y)"
      using AB_iso by blast
  qed
next
  show "\<forall>a \<in> AB (x\<^sup>T * y \<sqinter> z) . AB (x * a \<sqinter> y) \<noteq> {}"
  proof
    fix a
    assume "a \<in> AB (x\<^sup>T * y \<sqinter> z)"
    hence "x * a \<sqinter> y \<noteq> bot"
      using AB_card_5_1(2) by auto
    thus "AB (x * a \<sqinter> y) \<noteq> {}"
      using atomic by fastforce
  qed
next
  show "\<forall>a \<in> AB (x\<^sup>T * y \<sqinter> z) . \<forall>b \<in> AB (x\<^sup>T * y \<sqinter> z) . a \<noteq> b \<longrightarrow> AB (x * a \<sqinter> y) \<inter> AB (x * b \<sqinter> y) = {}"
  proof (intro ballI, rule impI)
    fix a b
    assume "a \<in> AB (x\<^sup>T * y \<sqinter> z)" "b \<in> AB (x\<^sup>T * y \<sqinter> z)" "a \<noteq> b"
    hence "(x * a \<sqinter> y) \<sqinter> (x * b \<sqinter> y) = bot"
      using assms AB_card_5_2(1) by auto
    thus "AB (x * a \<sqinter> y) \<inter> AB (x * b \<sqinter> y) = {}"
      using AB_bot AB_dist_inf by blast
  qed
qed

lemma nAB_univ_meet_comp:
  assumes "univalent x"
    shows "nAB (x \<sqinter> y * z\<^sup>T) \<le> nAB (x * z \<sqinter> y)"
proof (unfold num_atoms_below_def, rule icard_image_part_le)
  show "\<forall>a \<in> AB (x \<sqinter> y * z\<^sup>T) . AB (a * z \<sqinter> y) \<subseteq> AB (x * z \<sqinter> y)"
  proof
    fix a
    assume "a \<in> AB (x \<sqinter> y * z\<^sup>T)"
    hence "a * z \<sqinter> y \<le> x * z \<sqinter> y"
      using AB_card_6_1(1) by auto
    thus "AB (a * z \<sqinter> y) \<subseteq> AB (x * z \<sqinter> y)"
      using AB_iso by blast
  qed
next
  show "\<forall>a \<in> AB (x \<sqinter> y * z\<^sup>T) . AB (a * z \<sqinter> y) \<noteq> {}"
  proof
    fix a
    assume "a \<in> AB (x \<sqinter> y * z\<^sup>T)"
    hence "a * z \<sqinter> y \<noteq> bot"
      using AB_card_6_1(2) by auto
    thus "AB (a * z \<sqinter> y) \<noteq> {}"
      using atomic by fastforce
  qed
next
  show "\<forall>a \<in> AB (x \<sqinter> y * z\<^sup>T) . \<forall>b \<in> AB (x \<sqinter> y * z\<^sup>T) . a \<noteq> b \<longrightarrow> AB (a * z \<sqinter> y) \<inter> AB (b * z \<sqinter> y) = {}"
  proof (intro ballI, rule impI)
    fix a b
    assume "a \<in> AB (x \<sqinter> y * z\<^sup>T)" "b \<in> AB (x \<sqinter> y * z\<^sup>T)" "a \<noteq> b"
    hence "(a * z \<sqinter> y) \<sqinter> (b * z \<sqinter> y) = bot"
      using assms AB_card_6_2(1) by auto
    thus "AB (a * z \<sqinter> y) \<inter> AB (b * z \<sqinter> y) = {}"
      using AB_bot AB_dist_inf by blast
  qed
qed

end

subsection \<open>Atom-rectangular\<close>

class stone_relation_algebra_atomrect = stone_relation_algebra +
  assumes atomrect: "atom a \<longrightarrow> rectangle a"
begin

lemma atomrect_eq:
  "atom a \<Longrightarrow> a * top * a = a"
  by (simp add: order.antisym ex231d atomrect)

lemma AB_card_2_4:
  assumes "atom a"
    shows "(a * top \<sqinter> 1) * top * (top * a \<sqinter> 1) = a"
  by (simp add: assms AB_card_2_1 atomrect)

lemma simple_atom_2:
  assumes "atom a"
      and "a \<le> 1"
      and "atom b"
      and "b \<le> 1"
      and "x \<noteq> bot"
      and "x \<le> a * top * b"
    shows "x = a * top * b"
proof -
  have 1: "x * top \<sqinter> 1 \<noteq> bot"
    by (metis assms(5) inf_top_right le_bot top_right_mult_increasing vector_bot_closed vector_export_comp_unit)
  have "x * top \<sqinter> 1 \<le> a * top * b * top \<sqinter> 1"
    using assms(6) comp_inf.comp_isotone comp_isotone by blast
  also have "... \<le> a * top \<sqinter> 1"
    by (metis comp_associative comp_inf.mult_right_isotone inf.sup_monoid.add_commute mult_right_isotone top.extremum)
  also have "... = a"
    by (simp add: assms(2) coreflexive_comp_top_inf_one)
  finally have 2: "x * top \<sqinter> 1 = a"
    using 1 by (simp add: assms(1) domain_atom)
  have 3: "top * x \<sqinter> 1 \<noteq> bot"
    using 1 by (metis schroeder_1 schroeder_2 surjective_one_closed symmetric_top_closed total_one_closed)
  have "top * x \<sqinter> 1 \<le> top * a * top * b \<sqinter> 1"
    by (metis assms(6) comp_associative comp_inf.comp_isotone mult_right_isotone reflexive_one_closed)
  also have "... \<le> top * b \<sqinter> 1"
    using inf.sup_mono mult_left_isotone top_greatest by blast
  also have "... = b"
    using assms(4) epm_3 inf.sup_monoid.add_commute by auto
  finally have "top * x \<sqinter> 1 = b"
    using 3 by (simp add: assms(3) codomain_atom)
  hence "a * top * b = x * top * x"
    using 2 by (smt abel_semigroup.commute covector_comp_inf inf.abel_semigroup_axioms inf_top_right surjective_one_closed vector_export_comp_unit vector_top_closed mult_assoc)
  also have "... = a * top * b * top * (x \<sqinter> a * top * b)"
    using assms(6) calculation inf_absorb1 by auto
  also have "... \<le> a * top * (x \<sqinter> a * top * b)"
    by (metis comp_associative comp_inf_covector inf.idem inf.order_iff mult_right_isotone)
  also have "... \<le> a * top * (x \<sqinter> a * top)"
    using comp_associative comp_inf.mult_right_isotone mult_right_isotone by auto
  also have "... = a * top * a\<^sup>T * x"
    by (metis comp_associative comp_inf_vector inf_top.left_neutral)
  also have "... = a * top * a * x"
    by (simp add: assms(2) coreflexive_symmetric)
  also have "... = a * x"
    by (simp add: assms(1) atomrect_eq)
  also have "... \<le> x"
    using assms(2) mult_left_isotone by fastforce
  finally show ?thesis
    using assms(6) order.antisym by blast
qed

lemma dom_cod_inj_atoms:
  "inj_on dom_cod (AB top)"
proof
  fix a b
  assume 1: "a \<in> AB top" "b \<in> AB top" "dom_cod a = dom_cod b"
  have "a = a * top * a"
    using 1 atomrect_eq by auto
  also have "... = (a * top \<sqinter> 1) * top * (top * a \<sqinter> 1)"
    using calculation AB_card_2_1 by auto
  also have "... = (b * top \<sqinter> 1) * top * (top * b \<sqinter> 1)"
    using 1 by simp
  also have "... = b * top * b"
    using abel_semigroup.commute comp_inf_covector inf.abel_semigroup_axioms vector_export_comp_unit mult_assoc by fastforce
  also have "... = b"
    using 1 atomrect_eq by auto
  finally show "a = b"
    .
qed

lemma finite_AB_iff:
  "finite (AB top) \<longleftrightarrow> finite (AB 1)"
proof
  have "AB 1 \<subseteq> AB top"
    by auto
  thus "finite (AB top) \<Longrightarrow> finite (AB 1)"
    by (meson finite_subset)
next
  assume 1: "finite (AB 1)"
  show "finite (AB top)"
  proof (rule inj_on_finite)
    show "inj_on dom_cod (AB top)"
      using dom_cod_inj_atoms by blast
    show "dom_cod ` AB top \<subseteq> AB 1 \<times> AB 1"
      using dom_cod_atoms_1 by blast
    show "finite (AB 1 \<times> AB 1)"
      using 1 by blast
  qed
qed

lemma nAB_top_1:
  "nAB top \<le> nAB 1 * nAB 1"
proof (unfold num_atoms_below_def icard_cartesian_product[THEN sym], rule icard_inj_on_le)
  show "inj_on dom_cod (AB top)"
    using dom_cod_inj_atoms by blast
  show "dom_cod ` AB top \<subseteq> AB 1 \<times> AB 1"
    using dom_cod_atoms_1 by blast
qed

lemma atom_vector_injective:
  assumes "atom x"
    shows "injective (x * top)"
proof -
  have "atom (x * top \<sqinter> 1)"
    by (simp add: assms domain_atom)
  hence "(x * top \<sqinter> 1) * top * (x * top \<sqinter> 1) \<le> 1"
    using atom_rectangle_atom_one_rep atomrect by auto
  hence "x * top * x\<^sup>T \<le> 1"
    by (smt comp_associative conv_dist_comp coreflexive_symmetric ex231e inf_top.right_neutral symmetric_top_closed vector_export_comp_unit)
  thus "injective (x * top)"
    by (metis comp_associative conv_dist_comp symmetric_top_closed vector_top_closed)
qed

lemma atom_injective:
  "atom x \<Longrightarrow> injective x"
  by (metis atom_vector_injective comp_associative conv_dist_comp dual_order.trans mult_right_isotone symmetric_top_closed top_left_mult_increasing)

lemma atom_covector_univalent:
  "atom x \<Longrightarrow> univalent (top * x)"
  by (metis comp_associative conv_involutive atom_vector_injective conv_atom_iff conv_dist_comp symmetric_top_closed)

lemma atom_univalent:
  "atom x \<Longrightarrow> univalent x"
  using atom_injective conv_atom_iff univalent_conv_injective by blast

lemma counterexample_atom_simple:
  "atom x \<Longrightarrow> simple x"
  nitpick[expect=genuine,card=3]
  oops

lemma symmetric_atom_below_1:
  assumes "atom x"
      and "x = x\<^sup>T"
    shows "x \<le> 1"
proof -
  have "x = x * top * x\<^sup>T"
    using assms atomrect_eq by auto
  also have "... \<le> 1"
    by (metis assms(1) atom_vector_injective conv_dist_comp equivalence_top_closed ideal_top_closed mult_assoc)
  finally show ?thesis
    .
qed

end

subsection \<open>Atomic and Atom-Rectangular\<close>

class stone_relation_algebra_atomic_atomrect = stone_relation_algebra_atomic + stone_relation_algebra_atomrect
begin

lemma point_dense:
  assumes "x \<noteq> bot"
      and "x \<le> 1"
    shows "\<exists>a . a \<noteq> bot \<and> a * top * a \<le> 1 \<and> a \<le> x"
proof -
  from atomic obtain a where 1: "atom a \<and> a \<le> x"
    using assms(1) by auto
  hence "a * top * a \<le> a"
    by (simp add: atomrect)
  also have "... \<le> 1"
    using 1 assms(2) order_trans by blast
  finally show ?thesis
    using 1 by blast
qed

end

subsection \<open>Atom-simple\<close>

class stone_relation_algebra_atomsimple = stone_relation_algebra +
  assumes atomsimple: "atom a \<longrightarrow> simple a"
begin

lemma AB_card_2_5:
  assumes "atom a"
      and "a \<le> 1"
      and "atom b"
      and "b \<le> 1"
    shows "a * top * b * top \<sqinter> 1 = a" and "top * a * top * b \<sqinter> 1 = b"
  using assms AB_card_2_2 atomsimple by auto

lemma simple_atom_1:
  "atom a \<Longrightarrow> atom b \<Longrightarrow> a * top * b \<noteq> bot"
  by (metis order.antisym atomsimple bot_least comp_associative mult_left_zero top_right_mult_increasing)

end

subsection \<open>Atomic and Atom-simple\<close>

class stone_relation_algebra_atomic_atomsimple = stone_relation_algebra_atomic + stone_relation_algebra_atomsimple
begin

lemma simple:
  "a \<noteq> bot \<Longrightarrow> top * a * top = top"
  using atomsimple atomsimple_simple by blast

lemma AB_card_2_6:
  assumes "a \<noteq> bot"
      and "a \<le> 1"
      and "b \<noteq> bot"
      and "b \<le> 1"
    shows "a * top * b * top \<sqinter> 1 = a" and "top * a * top * b \<sqinter> 1 = b"
  using assms AB_card_2_3 simple atomsimple_simple by auto

lemma dom_cod_atoms_2:
  "AB 1 \<times> AB 1 \<subseteq> dom_cod ` AB top"
proof
  fix x
  assume "x \<in> AB 1 \<times> AB 1"
  from this obtain a b where 1: "atom a \<and> a \<le> 1 \<and> atom b \<and> b \<le> 1 \<and> x = (a,b)"
    by auto
  hence "a * top * b \<noteq> bot"
    by (simp add: simple_atom_1)
  from this obtain c where 2: "atom c \<and> c \<le> a * top * b"
    using atomic by blast
  hence "c * top \<sqinter> 1 \<le> a * top \<sqinter> 1"
    by (smt comp_inf.comp_isotone inf.boundedE inf.orderE inf_vector_comp reflexive_one_closed top_right_mult_increasing)
  also have "... = a"
    using 1 by (simp add: coreflexive_comp_top_inf_one)
  finally have 3: "c * top \<sqinter> 1 = a"
    using 1 2 domain_atom by simp
  have "top * c \<le> top * b"
    using 2 3 by (smt comp_associative comp_inf.reflexive_top_closed comp_inf.vector_top_closed comp_inf_covector comp_isotone simple vector_export_comp_unit)
  hence "top * c \<sqinter> 1 \<le> b"
    using 1 by (smt epm_3 inf.cobounded1 inf.left_commute inf.orderE injective_one_closed reflexive_one_closed)
  hence "top * c \<sqinter> 1 = b"
    using 1 2 codomain_atom by simp
  hence "dom_cod c = x"
    using 1 3 by simp
  thus "x \<in> dom_cod ` AB top"
    using 2 by auto
qed

lemma dom_cod_atoms:
  "AB 1 \<times> AB 1 = dom_cod ` AB top"
  using dom_cod_atoms_2 dom_cod_atoms_1 by blast

end

subsection \<open>Atom-rectangular and Atom-simple\<close>

class stone_relation_algebra_atomrect_atomsimple = stone_relation_algebra_atomrect + stone_relation_algebra_atomsimple
begin

lemma simple_atom:
  assumes "atom a"
      and "a \<le> 1"
      and "atom b"
      and "b \<le> 1"
    shows "atom (a * top * b)"
  using assms simple_atom_1 simple_atom_2 by auto

lemma nAB_top_2:
  "nAB 1 * nAB 1 \<le> nAB top"
proof (unfold num_atoms_below_def icard_cartesian_product[THEN sym], rule icard_inj_on_le)
  let ?f = "\<lambda>(a,b) . a * top * b"
  show "inj_on ?f (AB 1 \<times> AB 1)"
  proof
    fix x y
    assume "x \<in> AB 1 \<times> AB 1" "y \<in> AB 1 \<times> AB 1"
    from this obtain a b c d where 1: "atom a \<and> a \<le> 1 \<and> atom b \<and> b \<le> 1 \<and> x = (a,b) \<and> atom c \<and> c \<le> 1 \<and> atom d \<and> d \<le> 1 \<and> y = (c,d)"
      by auto
    assume "?f x = ?f y"
    hence 2: "a * top * b = c * top * d"
      using 1 by auto
    hence 3: "a = c"
      using 1 by (smt atomsimple comp_associative coreflexive_comp_top_inf_one)
    have "b = d"
      using 1 2 by (smt atomsimple comp_associative epm_3 injective_one_closed)
    thus "x = y"
      using 1 3 by simp
  qed
  show "?f ` (AB 1 \<times> AB 1) \<subseteq> AB top"
  proof
    fix x
    assume "x \<in> ?f ` (AB 1 \<times> AB 1)"
    from this obtain a b where 4: "atom a \<and> a \<le> 1 \<and> atom b \<and> b \<le> 1 \<and> x = a * top * b"
      by auto
    hence "a * top * b \<in> AB top"
      using simple_atom by simp
    thus "x \<in> AB top"
      using 4 by simp
  qed
qed

lemma nAB_top:
  "nAB 1 * nAB 1 = nAB top"
  using nAB_top_1 nAB_top_2 by auto

lemma atom_covector_mapping:
  "atom a \<Longrightarrow> mapping (top * a)"
  using atom_covector_univalent atomsimple by blast

lemma atom_covector_regular:
  "atom a \<Longrightarrow> regular (top * a)"
  by (simp add: atom_covector_mapping mapping_regular)

lemma atom_vector_bijective:
  "atom a \<Longrightarrow> bijective (a * top)"
  using atom_vector_injective comp_associative atomsimple by auto

lemma atom_vector_regular:
  "atom a \<Longrightarrow> regular (a * top)"
  by (simp add: atom_vector_bijective bijective_regular)

lemma atom_rectangle_regular:
  "atom a \<Longrightarrow> regular (a * top * a)"
  by (smt atom_covector_regular atom_vector_regular comp_associative pp_dist_comp regular_closed_top)

lemma atom_regular:
  "atom a \<Longrightarrow> regular a"
  using atom_rectangle_regular atomrect_eq by auto

end

subsection \<open>Atomic, Atom-rectangular and Atom-simple\<close>

class stone_relation_algebra_atomic_atomrect_atomsimple = stone_relation_algebra_atomic + stone_relation_algebra_atomrect + stone_relation_algebra_atomsimple
begin

subclass stone_relation_algebra_atomic_atomrect ..
subclass stone_relation_algebra_atomic_atomsimple ..
subclass stone_relation_algebra_atomrect_atomsimple ..

lemma nAB_atom_iff:
  "atom a \<longleftrightarrow> nAB a = 1"
proof
  assume "atom a"
  thus "nAB a = 1"
    by (simp add: nAB_atom)
next
  assume "nAB a = 1"
  from this obtain b where 1: "AB a = {b}"
    using icard_1_imp_singleton num_atoms_below_def one_eSuc by fastforce
  hence 2: "atom b \<and> b \<le> a"
    by auto
  hence 3: "AB (a \<sqinter> b) = {b}"
    by fastforce
  have "AB (a \<sqinter> b) \<union> AB (a \<sqinter> -b) = AB a \<and> AB (a \<sqinter> b) \<inter> AB (a \<sqinter> -b) = {}"
    using AB_split_2 AB_split_2_disjoint by simp
  hence "{b} \<union> AB (a \<sqinter> -b) = {b} \<and> {b} \<inter> AB (a \<sqinter> -b) = {}"
    using 1 3 by simp
  hence "AB (a \<sqinter> -b) = {}"
    by auto
  hence "a \<sqinter> -b = bot"
    using AB_nonempty_iff by blast
  hence "a \<le> b"
    using 2 atom_regular pseudo_complement by auto
  thus "atom a"
    using 2 by auto
qed

end

subsection \<open>Finitely Many Atoms\<close>

class stone_relation_algebra_finiteatoms = stone_relation_algebra +
  assumes finiteatoms: "finite { a . atom a }"
begin

lemma finite_AB:
  "finite (AB x)"
  using finite_Collect_conjI finiteatoms by force

lemma nAB_top_finite:
  "nAB top \<noteq> \<infinity>"
  by (smt (verit, best) finite_AB icard_infinite_conv num_atoms_below_def)

end

subsection \<open>Atomic and Finitely Many Atoms\<close>

class stone_relation_algebra_atomic_finiteatoms = stone_relation_algebra_atomic + stone_relation_algebra_finiteatoms
begin

lemma finite_ideal_points:
  "finite { p . ideal_point p }"
proof (cases "bot = top")
  case True
  hence "\<And>p . ideal_point p \<Longrightarrow> p = bot"
    using le_bot top.extremum by blast
  hence "{ p . ideal_point p } \<subseteq> {bot}"
    by auto
  thus ?thesis
    using finite_subset by auto
next
  case False
  let ?p = "{ p . ideal_point p }"
  show 0: "finite ?p"
  proof (rule finite_image_part_le)
    show "\<forall>x\<in>?p . AB x \<subseteq> AB top"
      using top.extremum by auto
    have "\<forall>x\<in>?p . x \<noteq> bot"
      using False by auto
    thus "\<forall>x\<in>?p . AB x \<noteq> {}"
      using AB_nonempty by auto
    show "\<forall>x\<in>?p . \<forall>y\<in>?p . x \<noteq> y \<longrightarrow> AB x \<inter> AB y = {}"
    proof (intro ballI, rule impI, rule ccontr)
      fix x y
      assume "x \<in> ?p" "y \<in> ?p" "x \<noteq> y"
      hence 1: "x \<sqinter> y = bot"
        by (simp add: different_ideal_points_disjoint)
      assume "AB x \<inter> AB y \<noteq> {}"
      from this obtain a where "atom a \<and> a \<le> x \<and> a \<le> y"
        by auto
      thus False
        using 1 by (metis comp_inf.semiring.mult_zero_left inf.absorb2 inf.sup_monoid.add_assoc)
    qed
    show "finite (AB top)"
      using finite_AB by blast
  qed
qed

end

subsection \<open>Atom-rectangular and Finitely Many Atoms\<close>

class stone_relation_algebra_atomrect_finiteatoms = stone_relation_algebra_atomrect + stone_relation_algebra_finiteatoms

subsection \<open>Atomic, Atom-rectangular and Finitely Many Atoms\<close>

class stone_relation_algebra_atomic_atomrect_finiteatoms = stone_relation_algebra_atomic + stone_relation_algebra_atomrect + stone_relation_algebra_finiteatoms
begin

subclass stone_relation_algebra_atomic_atomrect ..
subclass stone_relation_algebra_atomic_finiteatoms ..
subclass stone_relation_algebra_atomrect_finiteatoms ..

lemma counterexample_nAB_atom_iff:
  "atom x \<longleftrightarrow> nAB x = 1"
  nitpick[expect=genuine,card=3]
  oops

lemma counterexample_nAB_top_iff_eq:
  "nAB x = nAB top \<longleftrightarrow> x = top"
  nitpick[expect=genuine,card=3]
  oops

lemma counterexample_nAB_top_iff_leq:
  "nAB top \<le> nAB x \<longleftrightarrow> x = top"
  nitpick[expect=genuine,card=3]
  oops

end

subsection \<open>Atom-simple and Finitely Many Atoms\<close>

class stone_relation_algebra_atomsimple_finiteatoms = stone_relation_algebra_atomsimple + stone_relation_algebra_finiteatoms

subsection \<open>Atomic, Atom-simple and Finitely Many Atoms\<close>

class stone_relation_algebra_atomic_atomsimple_finiteatoms = stone_relation_algebra_atomic + stone_relation_algebra_atomsimple + stone_relation_algebra_finiteatoms
begin

subclass stone_relation_algebra_atomic_atomsimple ..
subclass stone_relation_algebra_atomic_finiteatoms ..
subclass stone_relation_algebra_atomsimple_finiteatoms ..

lemma nAB_top_2:
  "nAB 1 * nAB 1 \<le> nAB top"
proof (unfold num_atoms_below_def icard_cartesian_product[THEN sym], rule surj_icard_le)
  show "AB 1 \<times> AB 1 \<subseteq> dom_cod ` AB top"
    using dom_cod_atoms_2 by blast
qed

lemma counterexample_nAB_atom_iff_2:
  "atom x \<longleftrightarrow> nAB x = 1"
  nitpick[expect=genuine,card=6]
  oops

lemma counterexample_nAB_top_iff_eq_2:
  "nAB x = nAB top \<longleftrightarrow> x = top"
  nitpick[expect=genuine,card=6]
  oops

lemma counterexample_nAB_top_iff_leq_2:
  "nAB top \<le> nAB x \<longleftrightarrow> x = top"
  nitpick[expect=genuine,card=6]
  oops

end

subsection \<open>Atom-rectangular, Atom-simple and Finitely Many Atoms\<close>

class stone_relation_algebra_atomrect_atomsimple_finiteatoms = stone_relation_algebra_atomrect + stone_relation_algebra_atomsimple + stone_relation_algebra_finiteatoms
begin

subclass stone_relation_algebra_atomrect_atomsimple ..
subclass stone_relation_algebra_atomrect_finiteatoms ..
subclass stone_relation_algebra_atomsimple_finiteatoms ..

end

subsection \<open>Atomic, Atom-rectangular, Atom-simple and Finitely Many Atoms\<close>

class stone_relation_algebra_atomic_atomrect_atomsimple_finiteatoms = stone_relation_algebra_atomic + stone_relation_algebra_atomrect + stone_relation_algebra_atomsimple + stone_relation_algebra_finiteatoms
begin

subclass stone_relation_algebra_atomic_atomrect_atomsimple ..
subclass stone_relation_algebra_atomic_atomrect_finiteatoms ..
subclass stone_relation_algebra_atomic_atomsimple_finiteatoms ..
subclass stone_relation_algebra_atomrect_atomsimple_finiteatoms ..

lemma all_regular:
  "regular x"
proof (cases "x = bot")
  case True
  thus ?thesis
    by simp
next
  case False
  hence 1: "AB x \<noteq> {}"
    using AB_nonempty by blast
  have 2: "finite (AB x)"
    using finite_AB by blast
  have 3: "regular (Sup_fin (AB x))"
  proof -
    have "--Sup_fin (AB x) \<le> Sup_fin (AB x)"
    proof (rule finite_ne_subset_induct')
      show "finite (AB x)"
        using 2 by simp
      show "AB x \<noteq> {}"
        using 1 by simp
      show "AB x \<subseteq> AB top"
        by auto
      show "\<And>a . a \<in> AB top \<Longrightarrow> --Sup_fin {a} \<le> Sup_fin {a}"
        using atom_regular by auto
      show "\<And>a F . finite F \<Longrightarrow> F \<noteq> {} \<Longrightarrow> F \<subseteq> AB top \<Longrightarrow> a \<in> AB top \<Longrightarrow> a \<notin> F \<Longrightarrow> --Sup_fin F \<le> Sup_fin F \<Longrightarrow> --Sup_fin (insert a F) \<le> Sup_fin (insert a F)"
      proof -
        fix a F
        assume 4: "finite F" "F \<noteq> {}" "F \<subseteq> AB top" "a \<in> AB top" "a \<notin> F" "--Sup_fin F \<le> Sup_fin F"
        hence "--Sup_fin (insert a F) = a \<squnion> --Sup_fin F"
          using 4 atom_regular by auto
        also have "... \<le> a \<squnion> Sup_fin F"
          using 4 sup_mono by fastforce
        also have "... = Sup_fin (insert a F)"
          using 4 by auto
        finally show "--Sup_fin (insert a F) \<le> Sup_fin (insert a F)"
          .
      qed
    qed
    thus ?thesis
      using inf.antisym_conv pp_increasing by blast
  qed
  have "x \<sqinter> -Sup_fin (AB x) = bot"
  proof (rule ccontr)
    assume "x \<sqinter> -Sup_fin (AB x) \<noteq> bot"
    from this obtain b where 5: "atom b \<and> b \<le> x \<sqinter> -Sup_fin (AB x)"
      using atomic by blast
    hence "b \<le> Sup_fin (AB x)"
      using Sup_fin.coboundedI 2 by force
    thus "False"
      using 5 atom_in_p_xor by auto
  qed
  hence 6: "x \<le> Sup_fin (AB x)"
    using 3 by (simp add: pseudo_complement)
  have "Sup_fin (AB x) \<le> x"
    using 1 2 Sup_fin.boundedI by fastforce
  thus ?thesis
    using 3 6 order.antisym by force
qed

sublocale ra: relation_algebra where minus = "\<lambda>x y . x \<sqinter> - y"
proof
  show "\<And>x . x \<sqinter> - x = bot"
    by simp
  show "\<And>x . x \<squnion> - x = top"
    using all_regular pp_sup_p by fast
  show "\<And>x y . x \<sqinter> - y = x \<sqinter> - y"
    by simp
qed

end

class stone_relation_algebra_finite = stone_relation_algebra + finite
begin

subclass stone_relation_algebra_atomic_finiteatoms
proof
  show "finite { a . atom a }"
    by simp
  show "\<And>x. x \<noteq> bot \<longrightarrow> (\<exists>a. atom a \<and> a \<le> x)"
  proof
    fix x
    assume 1: "x \<noteq> bot"
    let ?s = "{ y . y \<le> x \<and> y \<noteq> bot }"
    have 2: "finite ?s"
      by auto
    have 3: "?s \<noteq> {}"
      using 1 by blast
    from ne_finite_has_minimal obtain m where "m\<in>?s \<and> (\<forall>x\<in>?s . x \<le> m \<longrightarrow> x = m)"
      using 2 3 by meson
    hence "atom m \<and> m \<le> x"
      using order_trans by blast
    thus "\<exists>a. atom a \<and> a \<le> x"
      by auto
  qed
qed

end

subsection \<open>Relation Algebra and Atomic\<close>

class relation_algebra_atomic = relation_algebra + stone_relation_algebra_atomic
begin

lemma nAB_atom_iff:
  "atom a \<longleftrightarrow> nAB a = 1"
proof
  assume "atom a"
  thus "nAB a = 1"
    by (simp add: nAB_atom)
next
  assume "nAB a = 1"
  from this obtain b where 1: "AB a = {b}"
    using icard_1_imp_singleton num_atoms_below_def one_eSuc by fastforce
  hence 2: "atom b \<and> b \<le> a"
    by auto
  hence 3: "AB (a \<sqinter> b) = {b}"
    by fastforce
  have "AB (a \<sqinter> b) \<union> AB (a \<sqinter> -b) = AB a \<and> AB (a \<sqinter> b) \<inter> AB (a \<sqinter> -b) = {}"
    using AB_split_2 AB_split_2_disjoint by simp
  hence "{b} \<union> AB (a \<sqinter> -b) = {b} \<and> {b} \<inter> AB (a \<sqinter> -b) = {}"
    using 1 3 by simp
  hence "AB (a \<sqinter> -b) = {}"
    by auto
  hence "a \<sqinter> -b = bot"
    using AB_nonempty_iff by blast
  hence "a \<le> b"
    by (simp add: shunting_1)
  thus "atom a"
    using 2 by auto
qed

end

subsection \<open>Relation Algebra, Atomic and Finitely Many Atoms\<close>

class relation_algebra_atomic_finiteatoms = relation_algebra_atomic + stone_relation_algebra_atomic_finiteatoms
begin

text \<open>
\<open>Sup_fin\<close> only works for non-empty finite sets.
\<close>

lemma atomistic:
  assumes "x \<noteq> bot"
    shows "x = Sup_fin (AB x)"
proof (rule order.antisym)
  show "x \<le> Sup_fin (AB x)"
  proof (rule ccontr)
    assume "\<not> x \<le> Sup_fin (AB x)"
    hence "x \<sqinter> -Sup_fin (AB x) \<noteq> bot"
      using shunting_1 by blast
    from this obtain a where 1: "atom a \<and> a \<le> x \<sqinter> -Sup_fin (AB x)"
      using atomic by blast
    hence "a \<in> AB x"
      by simp
    hence "a \<le> Sup_fin (AB x)"
      using Sup_fin.coboundedI finite_AB by auto
    thus "False"
      using 1 atom_in_p_xor by auto
  qed
  show "Sup_fin (AB x) \<le> x"
  proof (rule Sup_fin.boundedI)
    show "finite (AB x)"
      using finite_AB by auto
    show "AB x \<noteq> {}"
      using assms atomic by blast
    show "\<And>a. a \<in> AB x \<Longrightarrow> a \<le> x"
      by auto
  qed
qed

lemma counterexample_nAB_top:
  "1 \<noteq> top \<Longrightarrow> nAB top = nAB 1 * nAB 1"
  nitpick[expect=genuine,card=4]
  oops

end

class relation_algebra_atomic_atomsimple_finiteatoms = relation_algebra_atomic_finiteatoms + stone_relation_algebra_atomic_atomsimple_finiteatoms
begin

lemma counterexample_atom_rectangle:
  "atom x \<longrightarrow> rectangle x"
  nitpick[expect=genuine,card=4]
  oops

lemma counterexample_atom_univalent:
  "atom x \<longrightarrow> univalent x"
  nitpick[expect=genuine,card=4]
  oops

lemma counterexample_point_dense:
  assumes "x \<noteq> bot"
      and "x \<le> 1"
    shows "\<exists>a . a \<noteq> bot \<and> a * top * a \<le> 1 \<and> a \<le> x"
  nitpick[expect=genuine,card=4]
  oops

end

class relation_algebra_atomic_atomrect_atomsimple_finiteatoms = relation_algebra_atomic_atomsimple_finiteatoms + stone_relation_algebra_atomic_atomrect_atomsimple_finiteatoms

section \<open>Cardinality in Stone Relation Algebras\<close>

text \<open>
We study various axioms for a cardinality operation in Stone relation algebras.
\<close>

class card =
  fixes cardinality :: "'a \<Rightarrow> enat" ("#_" [100] 100)

class sra_card = stone_relation_algebra + card
begin

abbreviation card_bot              :: "'a \<Rightarrow> bool" where "card_bot              _ \<equiv> #bot = 0"
abbreviation card_bot_iff          :: "'a \<Rightarrow> bool" where "card_bot_iff          _ \<equiv> \<forall>x::'a . #x = 0 \<longleftrightarrow> x = bot"
abbreviation card_top              :: "'a \<Rightarrow> bool" where "card_top              _ \<equiv> #top = #1 * #1"
abbreviation card_conv             :: "'a \<Rightarrow> bool" where "card_conv             _ \<equiv> \<forall>x::'a . #(x\<^sup>T) = #x"
abbreviation card_add              :: "'a \<Rightarrow> bool" where "card_add              _ \<equiv> \<forall>x y::'a . #x + #y = #(x \<squnion> y) + #(x \<sqinter> y)"
abbreviation card_iso              :: "'a \<Rightarrow> bool" where "card_iso              _ \<equiv> \<forall>x y::'a . x \<le> y \<longrightarrow> #x \<le> #y"
abbreviation card_univ_comp_meet   :: "'a \<Rightarrow> bool" where "card_univ_comp_meet   _ \<equiv> \<forall>x y z::'a . univalent x \<longrightarrow> #(x\<^sup>T * y \<sqinter> z) \<le> #(x * z \<sqinter> y)"
abbreviation card_univ_meet_comp   :: "'a \<Rightarrow> bool" where "card_univ_meet_comp   _ \<equiv> \<forall>x y z::'a . univalent x \<longrightarrow> #(x \<sqinter> y * z\<^sup>T) \<le> #(x * z \<sqinter> y)"
abbreviation card_comp_univ        :: "'a \<Rightarrow> bool" where "card_comp_univ        _ \<equiv> \<forall>x y::'a . univalent x \<longrightarrow> #(y * x) \<le> #y"
abbreviation card_univ_meet_vector :: "'a \<Rightarrow> bool" where "card_univ_meet_vector _ \<equiv> \<forall>x y::'a . univalent x \<longrightarrow> #(x \<sqinter> y * top) \<le> #y"
abbreviation card_univ_meet_conv   :: "'a \<Rightarrow> bool" where "card_univ_meet_conv   _ \<equiv> \<forall>x y::'a . univalent x \<longrightarrow> #(x \<sqinter> y * y\<^sup>T) \<le> #y"
abbreviation card_domain_sym       :: "'a \<Rightarrow> bool" where "card_domain_sym       _ \<equiv> \<forall>x::'a . #(1 \<sqinter> x * x\<^sup>T) \<le> #x"
abbreviation card_domain_sym_conv  :: "'a \<Rightarrow> bool" where "card_domain_sym_conv  _ \<equiv> \<forall>x::'a . #(1 \<sqinter> x\<^sup>T * x) \<le> #x"
abbreviation card_domain           :: "'a \<Rightarrow> bool" where "card_domain           _ \<equiv> \<forall>x::'a . #(1 \<sqinter> x * top) \<le> #x"
abbreviation card_domain_conv      :: "'a \<Rightarrow> bool" where "card_domain_conv      _ \<equiv> \<forall>x::'a . #(1 \<sqinter> x\<^sup>T * top) \<le> #x"
abbreviation card_codomain         :: "'a \<Rightarrow> bool" where "card_codomain         _ \<equiv> \<forall>x::'a . #(1 \<sqinter> top * x) \<le> #x"
abbreviation card_codomain_conv    :: "'a \<Rightarrow> bool" where "card_codomain_conv    _ \<equiv> \<forall>x::'a . #(1 \<sqinter> top * x\<^sup>T) \<le> #x"
abbreviation card_univ             :: "'a \<Rightarrow> bool" where "card_univ             _ \<equiv> \<forall>x::'a . univalent x \<longrightarrow> #x \<le> #(x * top)"
abbreviation card_atom             :: "'a \<Rightarrow> bool" where "card_atom             _ \<equiv> \<forall>x::'a . atom x \<longrightarrow> #x = 1"
abbreviation card_atom_iff         :: "'a \<Rightarrow> bool" where "card_atom_iff         _ \<equiv> \<forall>x::'a . atom x \<longleftrightarrow> #x = 1"
abbreviation card_top_iff_eq       :: "'a \<Rightarrow> bool" where "card_top_iff_eq       _ \<equiv> \<forall>x::'a . #x = #top \<longleftrightarrow> x = top"
abbreviation card_top_iff_leq      :: "'a \<Rightarrow> bool" where "card_top_iff_leq      _ \<equiv> \<forall>x::'a . #top \<le> #x \<longleftrightarrow> x = top"
abbreviation card_top_finite       :: "'a \<Rightarrow> bool" where "card_top_finite       _ \<equiv> #top \<noteq> \<infinity>"

lemma card_domain_iff:
  "card_domain _ \<longleftrightarrow> card_domain_sym _"
  by (simp add: domain_vector_conv)

lemma card_codomain_conv_iff:
  "card_codomain_conv _ \<longleftrightarrow> card_domain _"
  by (simp add: domain_vector_covector)

lemma card_codomain_iff:
  assumes card_conv: "card_conv _"
    shows "card_codomain _ \<longleftrightarrow> card_codomain_conv _"
  by (metis card_conv conv_involutive)

lemma card_domain_conv_iff:
  "card_codomain _ \<longleftrightarrow> card_domain_conv _"
  using domain_vector_covector by auto

lemma card_domain_sym_conv_iff:
  "card_domain_conv _ \<longleftrightarrow> card_domain_sym_conv _"
  by (simp add: domain_vector_conv)

lemma card_bot:
  assumes card_bot_iff: "card_bot_iff _"
    shows "card_bot _"
  using card_bot_iff by auto

lemma card_comp_univ_implies_card_univ_comp_meet:
  assumes card_conv: "card_conv _"
      and card_comp_univ: "card_comp_univ _"
    shows "card_univ_comp_meet _"
proof (intro allI, rule impI)
  fix x y z
  assume 1: "univalent x"
  have "#(x\<^sup>T * y \<sqinter> z) = #(y\<^sup>T * x \<sqinter> z\<^sup>T)"
    by (metis card_conv conv_dist_comp conv_dist_inf conv_involutive)
  also have "... = #((y\<^sup>T \<sqinter> z\<^sup>T * x\<^sup>T) * x)"
    using 1 by (simp add: dedekind_univalent)
  also have "... \<le> #(y\<^sup>T \<sqinter> z\<^sup>T * x\<^sup>T)"
    using 1 card_comp_univ by blast
  also have "... = #(x * z \<sqinter> y)"
    by (metis card_conv conv_dist_comp conv_dist_inf inf.sup_monoid.add_commute)
  finally show "#(x\<^sup>T * y \<sqinter> z) \<le> #(x * z \<sqinter> y)"
    .
qed

lemma card_univ_meet_conv_implies_card_domain_sym:
  assumes card_univ_meet_conv: "card_univ_meet_conv _"
    shows "card_domain_sym _"
  by (simp add: card_univ_meet_conv)

lemma card_add_disjoint:
  assumes card_bot: "card_bot _"
      and card_add: "card_add _"
      and "x \<sqinter> y = bot"
    shows "#(x \<squnion> y) = #x + #y"
  by (simp add: assms(3) card_add card_bot)

lemma card_dist_sup_disjoint:
  assumes card_bot: "card_bot _"
      and card_add: "card_add _"
      and "A \<noteq> {}"
      and "finite A"
      and "\<forall>x\<in>A . \<forall>y\<in>A . x \<noteq> y \<longrightarrow> x \<sqinter> y = bot"
    shows "#Sup_fin A = sum cardinality A"
proof (rule finite_ne_subset_induct')
  show "finite A"
    using assms(4) by simp
  show "A \<noteq> {}"
    using assms(3) by simp
  show "A \<subseteq> A"
    by simp
  show "\<And>x . x \<in> A \<Longrightarrow> #Sup_fin {x} = sum cardinality {x}"
    by auto
  fix x F
  assume 1: "finite F" "F \<noteq> {}" "F \<subseteq> A" "x \<in> A" "x \<notin> F" "#Sup_fin F = sum cardinality F"
  have "#Sup_fin (insert x F) = #(x \<squnion> Sup_fin F)"
    using 1 by simp
  also have "... = #x + #Sup_fin F"
  proof -
    have "x \<sqinter> Sup_fin F = Sup_fin { x \<sqinter> y | y . y \<in> F }"
      using 1 inf_Sup1_distrib by simp
    also have "... = Sup_fin { bot | y . y \<in> F }"
      using 1 assms(5) by (metis (mono_tags, opaque_lifting) subset_iff)
    also have "... \<le> bot"
      by (rule Sup_fin.boundedI, simp_all add: 1)
    finally have "x \<sqinter> Sup_fin F = bot"
      by (simp add: order.antisym)
    thus ?thesis
      using card_add_disjoint assms by auto
  qed
  also have "... = sum cardinality (insert x F)"
    using 1 by simp
  finally show "#Sup_fin (insert x F) = sum cardinality (insert x F)"
    .
qed

lemma card_dist_sup_atoms:
  assumes card_bot: "card_bot _"
      and card_add: "card_add _"
      and "A \<noteq> {}"
      and "finite A"
      and "A \<subseteq> AB top"
    shows "#Sup_fin A = sum cardinality A"
proof -
  have "\<forall>x\<in>A . \<forall>y\<in>A . x \<noteq> y \<longrightarrow> x \<sqinter> y = bot"
    using different_atoms_disjoint assms(5) by auto
  thus ?thesis
    using card_dist_sup_disjoint assms(1-4) by auto
qed

lemma card_univ_meet_comp_implies_card_domain_sym:
  assumes card_univ_meet_comp: "card_univ_meet_comp _"
    shows "card_domain_sym _"
  by (metis card_univ_meet_comp inf.idem mult_1_left univalent_one_closed)

lemma card_top_greatest:
  assumes card_iso: "card_iso _"
    shows "#x \<le> #top"
  by (simp add: card_iso)

lemma card_pp_increasing:
  assumes card_iso: "card_iso _"
    shows "#x \<le> #(--x)"
  by (simp add: card_iso pp_increasing)

lemma card_top_iff_eq_leq:
  assumes card_iso: "card_iso _"
    shows "card_top_iff_eq _ \<longleftrightarrow> card_top_iff_leq _"
  using card_iso card_top_greatest nle_le by blast

lemma card_univ_comp_meet_implies_card_comp_univ:
  assumes card_iso: "card_iso _"
      and card_conv: "card_conv _"
      and card_univ_comp_meet: "card_univ_comp_meet _"
    shows "card_comp_univ _"
proof (intro allI, rule impI)
  fix x y
  assume 1: "univalent x"
  have "#(y * x) = #(x\<^sup>T * y\<^sup>T)"
    by (metis card_conv conv_dist_comp)
  also have "... = #(top \<sqinter> x\<^sup>T * y\<^sup>T)"
    by simp
  also have "... \<le> #(x * top \<sqinter> y\<^sup>T)"
    using 1 by (metis card_univ_comp_meet inf.sup_monoid.add_commute)
  also have "... \<le> #(y\<^sup>T)"
    using card_iso by simp
  also have "... = #y"
    by (simp add: card_conv)
  finally show "#(y * x) \<le> #y"
    .
qed

lemma card_comp_univ_iff_card_univ_comp_meet:
  assumes card_iso: "card_iso _"
      and card_conv: "card_conv _"
    shows "card_comp_univ _ \<longleftrightarrow> card_univ_comp_meet _"
  using card_iso card_univ_comp_meet_implies_card_comp_univ card_conv card_comp_univ_implies_card_univ_comp_meet by blast

lemma card_univ_meet_vector_implies_card_univ_meet_comp:
  assumes card_iso: "card_iso _"
      and card_univ_meet_vector: "card_univ_meet_vector _"
    shows "card_univ_meet_comp _"
proof (intro allI, rule impI)
  fix x y z
  assume 1: "univalent x"
  have "#(x \<sqinter> y * z\<^sup>T) = #(x \<sqinter> (y \<sqinter> x * z) * (z\<^sup>T \<sqinter> y\<^sup>T * x))"
    by (metis conv_involutive dedekind_eq inf.sup_monoid.add_commute)
  also have "... \<le> #(x \<sqinter> (y \<sqinter> x * z) * top)"
    using card_iso inf.sup_right_isotone mult_isotone by auto
  also have "... \<le> #(x * z \<sqinter> y)"
    using 1 by (simp add: card_univ_meet_vector inf.sup_monoid.add_commute)
  finally show "#(x \<sqinter> y * z\<^sup>T) \<le> #(x * z \<sqinter> y)"
    .
qed

lemma card_univ_meet_comp_implies_card_univ_meet_vector:
  assumes card_iso: "card_iso _"
      and card_univ_meet_comp: "card_univ_meet_comp _"
    shows "card_univ_meet_vector _"
proof (intro allI, rule impI)
  fix x y z
  assume 1: "univalent x"
  have "#(x \<sqinter> y * top) \<le> #(x * top \<sqinter> y)"
    using 1 by (metis card_univ_meet_comp symmetric_top_closed)
  also have "... \<le> #y"
    using card_iso by auto
  finally show "#(x \<sqinter> y * top) \<le> #y"
    .
qed

lemma card_univ_meet_vector_iff_card_univ_meet_comp:
  assumes card_iso: "card_iso _"
    shows "card_univ_meet_vector _ \<longleftrightarrow> card_univ_meet_comp _"
  using card_iso card_univ_meet_comp_implies_card_univ_meet_vector card_univ_meet_vector_implies_card_univ_meet_comp by blast

lemma card_univ_meet_vector_implies_card_univ_meet_conv:
  assumes card_iso: "card_iso _"
      and card_univ_meet_vector: "card_univ_meet_vector _"
    shows "card_univ_meet_conv _"
proof (intro allI, rule impI)
  fix x y z
  assume 1: "univalent x"
  have "#(x \<sqinter> y * y\<^sup>T) \<le> #(x \<sqinter> y * top)"
    using card_iso comp_inf.mult_right_isotone mult_right_isotone by auto
  also have "... \<le> #y"
    using 1 by (simp add: card_univ_meet_vector)
  finally show "#(x \<sqinter> y * y\<^sup>T) \<le> #y"
    .
qed

lemma card_domain_sym_implies_card_univ_meet_vector:
  assumes card_comp_univ: "card_comp_univ _"
      and card_domain_sym: "card_domain_sym _"
    shows "card_univ_meet_vector _"
proof (intro allI, rule impI)
  fix x y z
  assume 1: "univalent x"
  have "#(x \<sqinter> y * top) = #((y * top \<sqinter> 1) * (x \<sqinter> y * top))"
    by (simp add: inf.absorb2 vector_export_comp_unit)
  also have "... \<le> #(y * top \<sqinter> 1)"
    using 1 by (simp add: card_comp_univ univalent_inf_closed)
  also have "... \<le> #y"
    using card_domain_sym card_domain_iff inf.sup_monoid.add_commute by auto
  finally show "#(x \<sqinter> y * top) \<le> #y"
    .
qed

lemma card_domain_sym_iff_card_univ_meet_vector:
  assumes card_iso: "card_iso _"
      and card_comp_univ: "card_comp_univ _"
    shows "card_domain_sym _ \<longleftrightarrow> card_univ_meet_vector _"
  using card_iso card_comp_univ card_domain_sym_implies_card_univ_meet_vector card_univ_meet_vector_implies_card_univ_meet_conv card_univ_meet_conv_implies_card_domain_sym by blast

lemma card_univ_meet_conv_iff_card_univ_meet_comp:
  assumes card_iso: "card_iso _"
      and card_comp_univ: "card_comp_univ _"
    shows "card_univ_meet_conv _ \<longleftrightarrow> card_univ_meet_comp _"
  using card_iso card_comp_univ card_domain_sym_implies_card_univ_meet_vector card_univ_meet_vector_iff_card_univ_meet_comp card_univ_meet_vector_implies_card_univ_meet_conv univalent_one_closed by blast

lemma card_domain_sym_iff_card_univ_meet_comp:
  assumes card_iso: "card_iso _"
      and card_comp_univ: "card_comp_univ _"
    shows "card_domain_sym _ \<longleftrightarrow> card_univ_meet_comp _"
  using card_iso card_comp_univ card_domain_sym_implies_card_univ_meet_vector card_univ_meet_conv_iff_card_univ_meet_comp card_univ_meet_vector_iff_card_univ_meet_comp card_univ_meet_conv_implies_card_domain_sym by blast

lemma card_univ_comp_mapping:
  assumes card_comp_univ: "card_comp_univ _"
      and card_univ_meet_comp: "card_univ_meet_comp _"
      and "univalent x"
      and "mapping y"
    shows "#(x * y) = #x"
proof -
  have "#x = #(x \<sqinter> top * y\<^sup>T)"
    using assms(4) total_conv_surjective by auto
  also have "... \<le> #(x * y \<sqinter> top)"
    using assms(3) card_univ_meet_comp by blast
  finally have "#x \<le> #(x * y)"
    by simp
  thus ?thesis
    using assms(4) card_comp_univ nle_le by blast
qed

lemma card_point_one:
  assumes card_comp_univ: "card_comp_univ _"
      and card_univ_meet_comp: "card_univ_meet_comp _"
      and card_conv: "card_conv _"
      and "point x"
    shows "#x = #1"
proof -
  have "mapping (x\<^sup>T)"
    using assms(4) surjective_conv_total by auto
  thus ?thesis
    by (smt card_univ_comp_mapping card_comp_univ card_conv card_univ_meet_comp coreflexive_comp_top_inf inf.absorb2 reflexive_one_closed top_right_mult_increasing total_one_closed univalent_one_closed)
qed

end

subsection \<open>Cardinality in Relation Algebras\<close>

class ra_card = sra_card + relation_algebra
begin

lemma card_iso:
  assumes card_bot: "card_bot _"
      and card_add: "card_add _"
    shows "card_iso _"
proof (intro allI, rule impI)
  fix x y
  assume "x \<le> y"
  hence "#y = #(x \<squnion> (-x \<sqinter> y))"
    by (simp add: sup_absorb2)
  also have "... = #(x \<squnion> (-x \<sqinter> y)) + #(x \<sqinter> (-x \<sqinter> y))"
    by (simp add: card_bot)
  also have "... = #x + #(-x \<sqinter> y)"
    by (metis card_add)
  finally show "#x \<le> #y"
    using le_iff_add by blast
qed

lemma card_top_iff_eq:
  assumes card_bot_iff: "card_bot_iff _"
      and card_add: "card_add _"
      and card_top_finite: "card_top_finite _"
    shows "card_top_iff_eq _"
proof (rule allI, rule iffI)
  fix x
  assume 1: "#x = #top"
  have "#top = #(x \<squnion> -x)"
    by simp
  also have "... = #x + #(-x)"
    using card_add card_bot_iff card_add_disjoint inf_p by blast
  also have "... = #top + #(-x)"
    using 1 by simp
  finally have "#(-x) = 0"
    by (simp add: card_top_finite)
  hence "-x = bot"
    using card_bot_iff by blast
  thus "x = top"
    using comp_inf.pp_total by auto
next
  fix x
  assume "x = top"
  thus "#x = #top"
    by simp
qed

end

class ra_card_atomic_finiteatoms = ra_card + relation_algebra_atomic_finiteatoms
begin

lemma card_nAB:
  assumes card_bot: "card_bot _"
      and card_add: "card_add _"
      and card_atom: "card_atom _"
    shows "#x = nAB x"
proof (cases "x = bot")
  case True
  thus ?thesis
    by (simp add: card_bot nAB_bot)
next
  case False
  have 1: "finite (AB x)"
    using finite_AB by blast
  have 2: "AB x \<noteq> {}"
    using False AB_nonempty_iff by blast
  have "#x = #Sup_fin (AB x)"
    using atomistic False by auto
  also have "... = sum cardinality (AB x)"
    using 1 2 card_bot card_add card_dist_sup_disjoint different_atoms_disjoint by force
  also have "... = sum (\<lambda>x . 1) (AB x)"
    using card_atom by simp
  also have "... = icard (AB x)"
    by (metis (mono_tags, lifting) icard_eq_sum finite_AB)
  also have "... = nAB x"
    by (simp add: num_atoms_below_def)
  finally show ?thesis
    .
qed

end

class card_ab = sra_card +
  assumes card_nAB': "#x = nAB x"

class sra_card_ab_atomsimple_finiteatoms = sra_card + card_ab + stone_relation_algebra_atomsimple_finiteatoms +
  assumes card_bot_iff: "card_bot_iff _"
  assumes card_top: "card_top _"
begin

subclass stone_relation_algebra_atomic_atomsimple_finiteatoms
proof
  show "\<And>x . x \<noteq> bot \<longrightarrow> (\<exists>a . atom a \<and> a \<le> x)"
  proof
    fix x
    assume "x \<noteq> bot"
    hence "#x \<noteq> 0"
      using card_bot_iff by auto
    hence "nAB x \<noteq> 0"
      by (simp add: card_nAB')
    hence "AB x \<noteq> {}"
      by (metis (mono_tags, lifting) icard_empty num_atoms_below_def)
    thus "\<exists>a . atom a \<and> a \<le> x"
      by auto
  qed
qed

lemma dom_cod_inj_atoms:
  "inj_on dom_cod (AB top)"
proof (rule eq_card_imp_inj_on)
  show 1: "finite (AB top)"
    using finite_AB by blast
  have "icard (dom_cod ` AB top) = icard (AB 1 \<times> AB 1)"
    using dom_cod_atoms by auto
  also have "... = icard (AB 1) * icard (AB 1)"
    using icard_cartesian_product by blast
  also have "... = #1 * #1"
    by (simp add: card_nAB' num_atoms_below_def)
  also have "... = #top"
    by (simp add: card_top)
  also have "... = icard (AB top)"
    by (simp add: card_nAB' num_atoms_below_def)
  finally have "icard (dom_cod ` AB top) = icard (AB top)"
    .
  thus "card (dom_cod ` AB top) = card (AB top)"
    using 1 by (smt (z3) finite_icard_card)
qed

subclass stone_relation_algebra_atomic_atomrect_atomsimple_finiteatoms
proof
  have "\<And>a . atom a \<and> a \<le> 1 \<longrightarrow> a * top * a \<le> 1"
  proof
    fix a
    let ?ca = "top * a \<sqinter> 1"
    assume 1: "atom a \<and> a \<le> 1"
    have "a\<^sup>T * top * a \<le> 1"
    proof (rule ccontr)
      assume "\<not> a\<^sup>T * top * a \<le> 1"
      hence "a\<^sup>T * top * a \<sqinter> -1 \<noteq> bot"
        by (simp add: pseudo_complement)
      from this obtain b where 2: "atom b \<and> b \<le> a\<^sup>T * top * a \<sqinter> -1"
        using atomic by blast
      hence "b * top \<le> a\<^sup>T * top"
        by (metis comp_associative dual_order.trans inf.boundedE mult_left_isotone mult_right_isotone top.extremum)
      hence "b * top \<sqinter> 1 \<le> ?ca"
        by (metis comp_inf.comp_isotone conv_dist_comp conv_dist_inf coreflexive_symmetric inf.cobounded2 reflexive_one_closed symmetric_top_closed)
      hence 3: "b * top \<sqinter> 1 = ?ca"
        using 1 2 domain_atom codomain_atom by simp
      hence "top * b \<le> top * a"
        using 2 by (metis comp_associative comp_inf.vector_top_closed comp_inf_covector inf.boundedE mult_right_isotone vector_export_comp_unit vector_top_closed)
      hence "top * b \<sqinter> 1 \<le> ?ca"
        using inf_mono by blast
      hence "top * b \<sqinter> 1 = ?ca"
        using 1 2 codomain_atom by simp
      hence 4: "dom_cod b = dom_cod ?ca"
        using 3 by (metis comp_inf_covector comp_right_one inf.sup_monoid.add_commute inf_top.left_neutral vector_export_comp_unit)
      have "b \<in> AB top \<and> ?ca \<in> AB top"
        using 1 2 codomain_atom by simp
      hence "b = ?ca"
        using inj_onD dom_cod_inj_atoms 2 4 by smt
      thus "False"
        using 2 by (metis comp_inf.mult_right_isotone inf.boundedE inf.idem inf.left_commute inf_p le_bot)
    qed
    thus "a * top * a \<le> 1"
      using 1 by (simp add: coreflexive_symmetric)
  qed
  thus "\<And>a . atom a \<longrightarrow> a * top * a \<le> a"
    by (metis atom_rectangle_atom_one_rep)
qed

lemma atom_rectangle_card:
  assumes "atom a"
    shows "#(a * top * a) = 1"
  by (simp add: assms atomrect_eq card_nAB' nAB_atom)

lemma atom_regular_rectangle:
  assumes "atom a"
    shows "--a = a * top * a"
proof (rule order.antisym)
  show "--a \<le> a * top * a"
    using assms atom_rectangle_regular ex231d pp_dist_comp by auto
  show "a * top * a \<le> --a"
  proof (rule ccontr)
    assume "\<not> a * top * a \<le> --a"
    hence "a * top * a \<sqinter> -a \<noteq> bot"
      by (simp add: pseudo_complement)
    from this obtain b where 1: "atom b \<and> b \<le> a * top * a \<sqinter> -a"
      using atomic by blast
    hence 2: "b \<noteq> a"
      using inf.absorb2 by fastforce
    have 3: "a \<in> AB (a * top * a) \<and> b \<in> AB (a * top * a)"
      using 1 assms ex231d by auto
    from atom_rectangle_card obtain c where "AB (a * top * a) = {c}"
      using card_nAB' num_atoms_below_def assms icard_1_imp_singleton one_eSuc by fastforce
    thus "False"
      using 2 3 by auto
  qed
qed

sublocale ra_atom: relation_algebra_atomic where minus = "\<lambda>x y . x \<sqinter> - y" ..

end

class ra_card_atomic_atomsimple_finiteatoms = ra_card + relation_algebra_atomic_atomsimple_finiteatoms +
  assumes card_bot: "card_bot _"
  assumes card_add: "card_add _"
  assumes card_atom: "card_atom _"
  assumes card_top: "card_top _"
begin

subclass ra_card_atomic_finiteatoms
  ..

subclass sra_card_ab_atomsimple_finiteatoms
  apply unfold_locales
  using card_add card_atom card_bot card_nAB apply blast
  using card_add card_atom card_bot card_nAB nAB_bot_iff apply presburger
  using card_top by auto

subclass relation_algebra_atomic_atomrect_atomsimple_finiteatoms
  ..

end

subsection \<open>Counterexamples\<close>

class ra_card_notop = ra_card +
  assumes card_bot_iff: "card_bot_iff _"
  assumes card_conv: "card_conv _"
  assumes card_add: "card_add _"
  assumes card_atom_iff: "card_atom_iff _"
  assumes card_univ_comp_meet: "card_univ_comp_meet _"
  assumes card_univ_meet_comp: "card_univ_meet_comp _"

class ra_card_all = ra_card_notop +
  assumes card_top: "card_top _"
  assumes card_top_finite: "card_top_finite _"

class ra_card_notop_atomic_finiteatoms = ra_card_atomic_finiteatoms + ra_card_notop

class ra_card_all_atomic_finiteatoms = ra_card_notop_atomic_finiteatoms + ra_card_all

abbreviation r0000 :: "bool \<Rightarrow> bool \<Rightarrow> bool" where "r0000 x y \<equiv> False"
abbreviation r1000 :: "bool \<Rightarrow> bool \<Rightarrow> bool" where "r1000 x y \<equiv> \<not>x \<and> \<not>y"
abbreviation r0001 :: "bool \<Rightarrow> bool \<Rightarrow> bool" where "r0001 x y \<equiv> x \<and> y"
abbreviation r1001 :: "bool \<Rightarrow> bool \<Rightarrow> bool" where "r1001 x y \<equiv> x = y"
abbreviation r0110 :: "bool \<Rightarrow> bool \<Rightarrow> bool" where "r0110 x y \<equiv> x \<noteq> y"
abbreviation r1111 :: "bool \<Rightarrow> bool \<Rightarrow> bool" where "r1111 x y \<equiv> True"

lemma r_all_different:
                  "r0000 \<noteq> r1000" "r0000 \<noteq> r0001" "r0000 \<noteq> r1001" "r0000 \<noteq> r0110" "r0000 \<noteq> r1111"
  "r1000 \<noteq> r0000"                 "r1000 \<noteq> r0001" "r1000 \<noteq> r1001" "r1000 \<noteq> r0110" "r1000 \<noteq> r1111"
  "r0001 \<noteq> r0000" "r0001 \<noteq> r1000"                 "r0001 \<noteq> r1001" "r0001 \<noteq> r0110" "r0001 \<noteq> r1111"
  "r1001 \<noteq> r0000" "r1001 \<noteq> r1000" "r1001 \<noteq> r0001"                 "r1001 \<noteq> r0110" "r1001 \<noteq> r1111"
  "r0110 \<noteq> r0000" "r0110 \<noteq> r1000" "r0110 \<noteq> r0001" "r0110 \<noteq> r1001"                 "r0110 \<noteq> r1111"
  "r1111 \<noteq> r0000" "r1111 \<noteq> r1000" "r1111 \<noteq> r0001" "r1111 \<noteq> r1001" "r1111 \<noteq> r0110"
  by metis+

typedef (overloaded) ra1 = "{r0000,r1001,r0110,r1111}"
  by auto

typedef (overloaded) ra2 = "{r0000,r1000,r0001,r1001}"
  by auto

setup_lifting type_definition_ra1
setup_lifting type_definition_ra2
setup_lifting type_definition_prod

instantiation Enum.finite_4 :: ra_card_atomic_finiteatoms
begin

definition one_finite_4 :: Enum.finite_4 where "one_finite_4 = finite_4.a\<^sub>2"
definition conv_finite_4 :: "Enum.finite_4 \<Rightarrow> Enum.finite_4" where "conv_finite_4 x = x"
definition times_finite_4 :: "Enum.finite_4 \<Rightarrow> Enum.finite_4 \<Rightarrow> Enum.finite_4" where "times_finite_4 x y = (case (x,y) of (finite_4.a\<^sub>1,_) \<Rightarrow> finite_4.a\<^sub>1 | (_,finite_4.a\<^sub>1) \<Rightarrow> finite_4.a\<^sub>1 | (finite_4.a\<^sub>2,y) \<Rightarrow> y | (x,finite_4.a\<^sub>2) \<Rightarrow> x | _ \<Rightarrow> finite_4.a\<^sub>4)"
definition cardinality_finite_4 :: "Enum.finite_4 \<Rightarrow> enat" where "cardinality_finite_4 x = (case x of finite_4.a\<^sub>1 \<Rightarrow> 0 | finite_4.a\<^sub>4 \<Rightarrow> 2 | _ \<Rightarrow> 1)"

instance
  apply intro_classes
  subgoal by (simp add: times_finite_4_def split: finite_4.splits)
  subgoal by (simp add: times_finite_4_def sup_finite_4_def split: finite_4.splits)
  subgoal by (simp add: times_finite_4_def)
  subgoal by (simp add: times_finite_4_def one_finite_4_def split: finite_4.splits)
  subgoal by (simp add: conv_finite_4_def)
  subgoal by (simp add: sup_finite_4_def conv_finite_4_def)
  subgoal by (simp add: times_finite_4_def conv_finite_4_def split: finite_4.splits)
  subgoal by (simp add: times_finite_4_def inf_finite_4_def conv_finite_4_def less_eq_finite_4_def split: finite_4.splits)
  subgoal by (simp add: times_finite_4_def)
  subgoal by simp
  subgoal by (auto simp add: less_eq_finite_4_def split: finite_4.splits)
  subgoal by simp
  done

end

instantiation Enum.finite_4 :: ra_card_notop_atomic_finiteatoms
begin

instance
  apply intro_classes
  subgoal 1
    apply (clarsimp simp: cardinality_finite_4_def split: finite_4.splits)
    by (metis enat_0 one_neq_zero zero_neq_numeral)
  subgoal 2 by (simp add: conv_finite_4_def)
  subgoal 3 by (simp add: cardinality_finite_4_def sup_finite_4_def inf_finite_4_def split: finite_4.splits)
  subgoal 4 using zero_one_enat_neq(2) by (auto simp add: cardinality_finite_4_def less_eq_finite_4_def split: finite_4.splits)
  subgoal 5 using 1 3 4 by (metis (no_types, lifting) card_nAB nAB_univ_comp_meet)
  subgoal 6 using 1 3 4 by (metis (no_types, lifting) card_nAB nAB_univ_meet_comp)
  done

end

instantiation ra1 :: ra_card_atomic_finiteatoms
begin

lift_definition bot_ra1 :: ra1 is "r0000" by simp
lift_definition one_ra1 :: ra1 is "r1001" by simp
lift_definition top_ra1 :: ra1 is "r1111" by simp
lift_definition conv_ra1 :: "ra1 \<Rightarrow> ra1" is id by simp
lift_definition uminus_ra1 :: "ra1 \<Rightarrow> ra1" is "\<lambda>r x y . \<not> r x y" by auto
lift_definition sup_ra1 :: "ra1 \<Rightarrow> ra1 \<Rightarrow> ra1" is "\<lambda>q r x y . q x y \<or> r x y" by auto
lift_definition inf_ra1 :: "ra1 \<Rightarrow> ra1 \<Rightarrow> ra1" is "\<lambda>q r x y . q x y \<and> r x y" by auto
lift_definition times_ra1 :: "ra1 \<Rightarrow> ra1 \<Rightarrow> ra1" is "\<lambda>q r x y . \<exists>z . q x z \<and> r z y" by fastforce
lift_definition minus_ra1 :: "ra1 \<Rightarrow> ra1 \<Rightarrow> ra1" is "\<lambda>q r x y . q x y \<and> \<not> r x y" by auto
lift_definition less_eq_ra1 :: "ra1 \<Rightarrow> ra1 \<Rightarrow> bool" is "\<lambda>q r . \<forall>x y . q x y \<longrightarrow> r x y" .
lift_definition less_ra1 :: "ra1 \<Rightarrow> ra1 \<Rightarrow> bool" is "\<lambda>q r . (\<forall>x y . q x y \<longrightarrow> r x y) \<and> q \<noteq> r" .
lift_definition cardinality_ra1 :: "ra1 \<Rightarrow> enat" is "\<lambda>q . if q = r0000 then 0 else if q = r1111 then 2 else 1" .

instance
  apply intro_classes
  subgoal apply transfer by blast
  subgoal apply transfer by simp
  subgoal apply transfer by simp
  subgoal apply transfer by auto
  subgoal apply transfer by simp
  subgoal apply transfer by simp
  subgoal apply transfer by simp
  subgoal apply transfer by simp
  subgoal apply transfer by simp
  subgoal apply transfer by simp
  subgoal apply transfer by simp
  subgoal apply transfer by simp
  subgoal apply transfer by auto
  subgoal apply transfer by meson
  subgoal apply transfer by simp
  subgoal apply transfer by auto
  subgoal apply transfer by auto
  subgoal apply transfer by simp
  subgoal apply transfer by simp
  subgoal apply transfer by simp
  subgoal apply transfer by simp
  subgoal apply transfer by fastforce
  subgoal apply transfer by auto
  subgoal apply transfer by simp
  subgoal apply transfer by simp
  subgoal apply transfer by simp
  subgoal apply transfer by simp
  subgoal apply transfer by simp
  subgoal apply transfer by blast
  subgoal apply transfer by simp
  done

end

lemma four_cases:
  assumes "P x1" "P x2" "P x3" "P x4"
    shows "\<forall>y \<in> { x . x \<in> {x1, x2, x3, x4} } . P y"
  using assms by auto

lemma r_aux:
  "(\<lambda>x y. r1001 x y \<or> r0110 x y) = r1111" "(\<lambda>x y. r1001 x y \<and> r0110 x y) = r0000"
  "(\<lambda>x y. r0110 x y \<or> r1001 x y) = r1111" "(\<lambda>x y. r0110 x y \<and> r1001 x y) = r0000"
  "(\<lambda>x y. r1000 x y \<or> r0001 x y) = r1001" "(\<lambda>x y. r1000 x y \<and> r0001 x y) = r0000"
  "(\<lambda>x y. r1000 x y \<or> r1001 x y) = r1001" "(\<lambda>x y. r1000 x y \<and> r1001 x y) = r1000"
  "(\<lambda>x y. r0001 x y \<or> r1000 x y) = r1001" "(\<lambda>x y. r0001 x y \<and> r1000 x y) = r0000"
  "(\<lambda>x y. r0001 x y \<or> r1001 x y) = r1001" "(\<lambda>x y. r0001 x y \<and> r1001 x y) = r0001"
  "(\<lambda>x y. r1001 x y \<or> r1000 x y) = r1001" "(\<lambda>x y. r1001 x y \<and> r1000 x y) = r1000"
  "(\<lambda>x y. r1001 x y \<or> r0001 x y) = r1001" "(\<lambda>x y. r1001 x y \<and> r0001 x y) = r0001"
  by meson+

instantiation ra1 :: ra_card_notop_atomic_finiteatoms
begin

instance
  apply intro_classes
  subgoal 1 apply transfer by (metis zero_neq_numeral zero_one_enat_neq(1))
  subgoal 2 apply transfer by simp
  subgoal 3 apply transfer using r_aux r_all_different by auto
  subgoal 4 apply transfer using r_all_different zero_one_enat_neq(1) by auto
  subgoal 5 using 1 3 4 card_nAB nAB_univ_comp_meet by (metis (no_types, lifting) card_nAB nAB_univ_comp_meet)
  subgoal 6 using 1 3 4 by (metis (no_types, lifting) card_nAB nAB_univ_meet_comp)
  done

end

instantiation ra2 :: ra_card_atomic_finiteatoms
begin

lift_definition bot_ra2 :: ra2 is "r0000" by simp
lift_definition one_ra2 :: ra2 is "r1001" by simp
lift_definition top_ra2 :: ra2 is "r1001" by simp
lift_definition conv_ra2 :: "ra2 \<Rightarrow> ra2" is id by simp
lift_definition uminus_ra2 :: "ra2 \<Rightarrow> ra2" is "\<lambda>r x y . x = y \<and> \<not> r x y" by auto
lift_definition sup_ra2 :: "ra2 \<Rightarrow> ra2 \<Rightarrow> ra2" is "\<lambda>q r x y . q x y \<or> r x y" by auto
lift_definition inf_ra2 :: "ra2 \<Rightarrow> ra2 \<Rightarrow> ra2" is "\<lambda>q r x y . q x y \<and> r x y" by auto
lift_definition times_ra2 :: "ra2 \<Rightarrow> ra2 \<Rightarrow> ra2" is "\<lambda>q r x y . \<exists>z . q x z \<and> r z y" by auto
lift_definition minus_ra2 :: "ra2 \<Rightarrow> ra2 \<Rightarrow> ra2" is "\<lambda>q r x y . q x y \<and> \<not> r x y" by auto
lift_definition less_eq_ra2 :: "ra2 \<Rightarrow> ra2 \<Rightarrow> bool" is "\<lambda>q r . \<forall>x y . q x y \<longrightarrow> r x y" .
lift_definition less_ra2 :: "ra2 \<Rightarrow> ra2 \<Rightarrow> bool" is "\<lambda>q r . (\<forall>x y . q x y \<longrightarrow> r x y) \<and> q \<noteq> r" .
lift_definition cardinality_ra2 :: "ra2 \<Rightarrow> enat" is "\<lambda>q . if q = r0000 then 0 else if q = r1001 then 2 else 1" .

instance
  apply intro_classes
  subgoal apply transfer by blast
  subgoal apply transfer by simp
  subgoal apply transfer by simp
  subgoal apply transfer by auto
  subgoal apply transfer by simp
  subgoal apply transfer by simp
  subgoal apply transfer by simp
  subgoal apply transfer by simp
  subgoal apply transfer by simp
  subgoal apply transfer by simp
  subgoal apply transfer by simp
  subgoal apply transfer by auto
  subgoal apply transfer by auto
  subgoal apply transfer by (clarsimp, metis (full_types))
  subgoal apply transfer by auto
  subgoal apply transfer by auto
  subgoal apply transfer by auto
  subgoal apply transfer by simp
  subgoal apply transfer by simp
  subgoal apply transfer by simp
  subgoal apply transfer by simp
  subgoal apply transfer by auto
  subgoal apply transfer by auto
  subgoal apply transfer by auto
  subgoal apply transfer by auto
  subgoal apply transfer by auto
  subgoal apply transfer by auto
  subgoal apply transfer by auto
  subgoal apply transfer by auto
  subgoal apply transfer by simp
  done

end

instantiation ra2 :: ra_card_notop_atomic_finiteatoms
begin

instance
  apply intro_classes
  subgoal 1 apply transfer by (metis one_neq_zero zero_neq_numeral)
  subgoal 2 apply transfer by simp
  subgoal 3 apply transfer
    apply (rule four_cases)
    subgoal using r_all_different by auto
    subgoal apply (rule four_cases) using r_aux r_all_different by auto
    subgoal apply (rule four_cases) using r_aux r_all_different by auto
    subgoal using r_aux r_all_different by auto
    done
  subgoal 4 apply transfer using r_all_different zero_one_enat_neq(1) by auto
  subgoal 5 using 1 3 4 by (metis (no_types, lifting) card_nAB nAB_univ_comp_meet)
  subgoal 6 using 1 3 4 by (metis (no_types, lifting) card_nAB nAB_univ_meet_comp)
  done

end

instantiation prod :: (stone_relation_algebra,stone_relation_algebra) stone_relation_algebra
begin

lift_definition bot_prod :: "'a \<times> 'b" is "(bot::'a,bot::'b)" .
lift_definition one_prod :: "'a \<times> 'b" is "(1::'a,1::'b)" .
lift_definition top_prod :: "'a \<times> 'b" is "(top::'a,top::'b)" .
lift_definition conv_prod :: "'a \<times> 'b \<Rightarrow> 'a \<times> 'b" is "\<lambda>(u,v) . (conv u,conv v)" .
lift_definition uminus_prod :: "'a \<times> 'b \<Rightarrow> 'a \<times> 'b" is "\<lambda>(u,v) . (uminus u,uminus v)" .
lift_definition sup_prod :: "'a \<times> 'b \<Rightarrow> 'a \<times> 'b \<Rightarrow> 'a \<times> 'b" is "\<lambda>(u,v) (w,x) . (u \<squnion> w,v \<squnion> x)" .
lift_definition inf_prod :: "'a \<times> 'b \<Rightarrow> 'a \<times> 'b \<Rightarrow> 'a \<times> 'b" is "\<lambda>(u,v) (w,x) . (u \<sqinter> w,v \<sqinter> x)" .
lift_definition times_prod :: "'a \<times> 'b \<Rightarrow> 'a \<times> 'b \<Rightarrow> 'a \<times> 'b" is "\<lambda>(u,v) (w,x) . (u * w,v * x)" .
lift_definition less_eq_prod :: "'a \<times> 'b \<Rightarrow> 'a \<times> 'b \<Rightarrow> bool" is "\<lambda>(u,v) (w,x) . u \<le> w \<and> v \<le> x" .
lift_definition less_prod :: "'a \<times> 'b \<Rightarrow> 'a \<times> 'b \<Rightarrow> bool" is "\<lambda>(u,v) (w,x) . u \<le> w \<and> v \<le> x \<and> \<not>(u = w \<and> v = x)" .

instance
  apply intro_classes
  subgoal apply transfer by auto
  subgoal apply transfer by auto
  subgoal apply transfer by auto
  subgoal by (unfold less_eq_prod_def, clarsimp)
  subgoal apply transfer by auto
  subgoal apply transfer by auto
  subgoal apply transfer by auto
  subgoal apply transfer by auto
  subgoal apply transfer by auto
  subgoal apply transfer by auto
  subgoal apply transfer by auto
  subgoal apply transfer by auto
  subgoal apply transfer by (clarsimp, simp add: sup_inf_distrib1)
  subgoal apply transfer by (clarsimp, simp add: pseudo_complement)
  subgoal apply transfer by auto
  subgoal apply transfer by (clarsimp, simp add: mult.assoc)
  subgoal apply transfer by (clarsimp, simp add: mult_right_dist_sup)
  subgoal apply transfer by simp
  subgoal apply transfer by simp
  subgoal apply transfer by auto
  subgoal apply transfer by (clarsimp, simp add: conv_dist_sup)
  subgoal apply transfer by (clarsimp, simp add: conv_dist_comp)
  subgoal apply transfer by (clarsimp, simp add: dedekind_1)
  subgoal apply transfer by (clarsimp, simp add: pp_dist_comp)
  subgoal apply transfer by simp
  done

end

instantiation prod :: (relation_algebra,relation_algebra) relation_algebra
begin

lift_definition minus_prod :: "'a \<times> 'b \<Rightarrow> 'a \<times> 'b \<Rightarrow> 'a \<times> 'b" is "\<lambda>(u,v) (w,x) . (u - w,v - x)" .

instance
  apply intro_classes
  subgoal apply transfer by auto
  subgoal apply transfer by auto
  subgoal apply transfer by (clarsimp, simp add: diff_eq)
  done

end

instantiation prod :: (relation_algebra_atomic_finiteatoms,relation_algebra_atomic_finiteatoms) relation_algebra_atomic_finiteatoms
begin

instance
  apply intro_classes
  subgoal apply transfer by (clarsimp, metis atomic bot.extremum inf.antisym_conv)
  subgoal
  proof -
    have 1: "\<forall>a::'a . \<forall>b::'b . atom (a,b) \<longrightarrow> (a = bot \<and> atom b) \<or> (atom a \<and> b = bot)"
    proof (intro allI, rule impI)
      fix a :: 'a and b :: 'b
      assume 2: "atom (a,b)"
      show "(a = bot \<and> atom b) \<or> (atom a \<and> b = bot)"
      proof (cases "a = bot")
        case 3: True
        show ?thesis
        proof (cases "b = bot")
          case True
          thus ?thesis
            using 2 3 by (simp add: bot_prod.abs_eq)
        next
          case False
          from this obtain c where 4: "atom c \<and> c \<le> b"
            using atomic by auto
          hence "(bot,c) \<le> (a,b) \<and> (bot,c) \<noteq> bot"
            by (simp add: less_eq_prod_def bot_prod.abs_eq)
          hence "(bot,c) = (a,b)"
            using 2 by auto
          thus ?thesis
            using 4 by auto
        qed
      next
        case False
        from this obtain c where 5: "atom c \<and> c \<le> a"
          using atomic by auto
        hence "(c,bot) \<le> (a,b) \<and> (c,bot) \<noteq> bot"
          by (simp add: less_eq_prod_def bot_prod.abs_eq)
        hence "(c,bot) = (a,b)"
          using 2 by auto
        thus ?thesis
          using 5 by auto
      qed
    qed
    have 6: "{ (a,b) | a b . atom (a,b) } \<subseteq> { (bot,b) | b::'b . atom b } \<union> { (a,bot) | a::'a . atom a }"
    proof
      fix x :: "'a \<times> 'b"
      assume "x \<in> { (a,b) | a b . atom (a,b) }"
      from this obtain a b where 7: "x = (a,b) \<and> atom (a,b)"
        by auto
      hence "(a = bot \<and> atom b) \<or> (atom a \<and> b = bot)"
        using 1 by simp
      thus "x \<in> { (bot,b) | b . atom b } \<union> { (a,bot) | a . atom a }"
        using 7 by auto
    qed
    have "finite { (bot,b) | b::'b . atom b } \<and> finite { (a,bot) | a::'a . atom a }"
      by (simp add: finiteatoms)
    hence 8: "finite ({ (bot,b) | b::'b . atom b } \<union> { (a,bot) | a::'a . atom a })"
      by blast
    have 9: "finite { (a,b) | a b . atom (a::'a,b::'b) }"
      by (rule rev_finite_subset, rule 8, rule 6)
    have "{ (a,b) | a b . atom (a,b) } = { x :: 'a \<times> 'b . atom x }"
      by auto
    thus "finite { x :: 'a \<times> 'b . atom x }"
      using 9 by simp
  qed
  done

end

instantiation prod :: (ra_card_notop_atomic_finiteatoms,ra_card_notop_atomic_finiteatoms) ra_card_notop_atomic_finiteatoms
begin

lift_definition cardinality_prod :: "'a \<times> 'b \<Rightarrow> enat" is "\<lambda>(u,v) . #u + #v" .

instance
  apply intro_classes
  subgoal apply transfer by (smt (verit) card_bot_iff case_prod_conv surj_pair zero_eq_add_iff_both_eq_0)
  subgoal apply transfer by (simp add: card_conv)
  subgoal apply transfer by (clarsimp, metis card_add semiring_normalization_rules(20))
  subgoal apply transfer apply (clarsimp, rule iffI)
    subgoal by (metis add.commute add.right_neutral bot.extremum card_atom_iff card_bot_iff dual_order.refl)
    subgoal for a b proof -
      assume 1: "#a + #b = 1"
      show ?thesis
      proof (cases "#a = 0")
        case True
        hence "#b = 1"
          using 1 by auto
        thus ?thesis
          by (metis True bot.extremum_unique card_atom_iff card_bot_iff)
      next
        case False
        hence "#a \<ge> 1"
          by (simp add: ileI1 one_eSuc)
        hence 2: "#a = 1"
          using 1 by (metis ile_add1 order_antisym)
        hence "#b = 0"
          using 1 by auto
        thus ?thesis
          using 2 by (metis bot.extremum_unique card_atom_iff card_bot_iff)
      qed
    qed
    done
  subgoal apply transfer by (simp add: add_mono card_univ_comp_meet)
  subgoal apply transfer by (simp add: add_mono card_univ_meet_comp)
  done

end

type_synonym finite_4_square = "Enum.finite_4 \<times> Enum.finite_4"

interpretation finite_4_square: ra_card_atomic_finiteatoms where cardinality = "cardinality" and inf = "(\<sqinter>)" and less_eq = "(\<le>)" and less = "(<)" and sup = "(\<squnion>)" and bot = "bot::finite_4_square" and top = "top" and uminus = "uminus" and one = "1" and times = "(*)" and conv = "conv" and minus = "(-)" ..

interpretation finite_4_square: ra_card_all_atomic_finiteatoms where cardinality = "cardinality" and inf = "(\<sqinter>)" and less_eq = "(\<le>)" and less = "(<)" and sup = "(\<squnion>)" and bot = "bot::finite_4_square" and top = "top" and uminus = "uminus" and one = "1" and times = "(*)" and conv = "conv" and minus = "(-)"
  apply unfold_locales
  subgoal apply transfer by (simp add: cardinality_finite_4_def one_finite_4_def)
  subgoal apply transfer by (smt (verit) card_add card_atom_iff card_bot_iff card_nAB cardinality_prod.abs_eq nAB_top_finite top_prod.abs_eq)
  done

lemma counterexample_atom_rectangle_2:
  "atom a \<longrightarrow> a * top * a \<le> (a::finite_4_square)"
  nitpick[expect=genuine]
  oops

lemma counterexample_atom_univalent_2:
  "atom a \<longrightarrow> univalent (a::finite_4_square)"
  nitpick[expect=genuine]
  oops

lemma counterexample_point_dense_2:
  assumes "x \<noteq> bot"
      and "x \<le> 1"
    shows "\<exists>a::finite_4_square . a \<noteq> bot \<and> a * top * a \<le> 1 \<and> a \<le> x"
  nitpick[expect=genuine]
  oops

type_synonym ra11 = "ra1 \<times> ra1"

interpretation ra11: ra_card_atomic_finiteatoms where cardinality = "cardinality" and inf = "(\<sqinter>)" and less_eq = "(\<le>)" and less = "(<)" and sup = "(\<squnion>)" and bot = "bot::ra11" and top = "top" and uminus = "uminus" and one = "1" and times = "(*)" and conv = "conv" and minus = "(-)" ..

interpretation ra11: ra_card_all_atomic_finiteatoms where cardinality = "cardinality" and inf = "(\<sqinter>)" and less_eq = "(\<le>)" and less = "(<)" and sup = "(\<squnion>)" and bot = "bot::ra11" and top = "top" and uminus = "uminus" and one = "1" and times = "(*)" and conv = "conv" and minus = "(-)"
  apply unfold_locales
  subgoal apply transfer apply transfer using r_all_different by auto
  subgoal apply transfer apply transfer using numeral_ne_infinity by fastforce
  done

interpretation ra11: stone_relation_algebra_atomrect where inf = "(\<sqinter>)" and less_eq = "(\<le>)" and less = "(<)" and sup = "(\<squnion>)" and bot = "bot::ra11" and top = "top" and uminus = "uminus" and one = "1" and times = "(*)" and conv = "conv"
  apply unfold_locales
  apply transfer apply transfer
  nitpick[expect=genuine]
  oops

lemma "\<not> (\<forall>a::ra1\<times>ra1 . atom a \<longrightarrow> a * top * a \<le> a)"
proof -
  let ?a = "(1::ra1,bot::ra1)"
  have 1: "atom ?a"
  proof
    show "?a \<noteq> bot"
      by (metis (full_types) bot_prod.transfer bot_ra1.rep_eq one_ra1.rep_eq prod.inject)
    have "\<And>(a :: ra1) (b :: ra1) . (a,b) \<le> ?a \<Longrightarrow> (a,b) \<noteq> bot \<Longrightarrow> a = 1 \<and> b = bot"
    proof -
      fix a b :: ra1
      assume "(a,b) \<le> ?a"
      hence 2: "a \<le> 1 \<and> b \<le> bot"
        by (simp add: less_eq_prod_def)
      assume "(a,b) \<noteq> bot"
      hence 3: "a \<noteq> bot \<and> b = bot"
        using 2 by (simp add: bot.extremum_unique bot_prod.abs_eq)
      have "atom (1::ra1)"
        apply transfer apply (rule conjI)
        subgoal by (simp add: r_all_different)
        subgoal by auto
        done
      thus "a = 1 \<and> b = bot"
        using 2 3 by blast
    qed
    thus "\<forall>y . y \<noteq> bot \<and> y \<le> ?a \<longrightarrow> y = ?a"
      by clarsimp
  qed
  have "\<not> ?a * top * ?a \<le> ?a"
    apply (unfold top_prod_def times_prod_def less_eq_prod_def)
    apply transfer
    by auto
  thus ?thesis
    using 1 by auto
qed

end

