section \<open>The graded ring structure of level 1 modular forms\<close>
theory Modular_Forms_Structure
imports 
  Meromorphic_Forms_Valence_Formula
  Basic_Modular_Forms_Mero_UHP
  "Elliptic_Functions.Dedekind_Eta"
begin

text \<open>
  In this section, we will use the valence formula for the full modular group
  $\text{SL}(2,\mathbb{Z})$ to analyse the structure of the vector space of modular forms on it.
\<close>

subsection \<open>Auxiliary material\<close>

(* TODO Move *)

subsubsection \<open>Linear diophantine inequalities in two variables\<close>

text \<open>
  We first need some simple number-theoretic facts related to linear diophantine equations with
  two variables, i.e.\  $ax + by = l$, where $a,b,l$ are integer parameters with $a$ and $b$ not
  both $0$ and $x$ and $y$ are integer variables.
\<close>

lemma bezout_imp_coprime:
  assumes "a * u + b * v = 1"
  shows   "Rings.coprime a b"
  unfolding Rings.coprime_def
proof safe
  fix d assume "d dvd a" "d dvd b"
  then obtain a' b' where *: "a = d * a'" "b = d * b'"
    by (elim dvdE)
  from assms have "d * (a' * u + b' * v) = 1"
    by (simp add: * algebra_simps)
  thus "d dvd 1"
    by (metis dvd_triv_left)
qed

text \<open>
  The solutions to the equation $ax + by = l$ are freely generated as 
  $(x,y) = (u + b/d k, v - a/d k)$ with $k$ ranging over the integers, where 
  $d = \text{gcd}(a,b)$ and $(u,v)$ is an arbitrary particular solution of the equation.

  Due to B\'{e}zout's theorems, such a particular solution exists iff $d \mid l$, but we do not 
  show that here.
\<close>
lemma gen_bezout_solutions:
  fixes u v a b :: "'a :: ring_gcd"
  assumes "a * u + b * v = l" and nz: "a \<noteq> 0 \<or> b \<noteq> 0"
  shows   "bij_betw (\<lambda>k. (u + b div gcd a b * k, v - a div gcd a b * k)) UNIV
             {(x,y). a * x + b * y = l}"
proof -
  define D where "D = gcd a b"
  define a' where "a' = a div D"
  define b' where "b' = b div D"
  have ab_eq: "a = a' * D" "b = b' * D" and [simp]: "D \<noteq> 0"
    using nz by (auto simp: a'_def b'_def D_def)
  have coprime: "Rings.coprime a' b'"
    unfolding a'_def b'_def D_def by (metis nz div_gcd_coprime)

  have eq: "a * u = l - b * v"
    using assms by (simp add: algebra_simps)
  have "(\<lambda>k. (u + b' * k, v - a' * k)) ` UNIV \<subseteq> {(x,y). a * x + b * y = l}"
  proof safe
    fix k :: 'a
    have "a * (u + b' * k) + b * (v - a' * k) = a * u + a * b' * k + b * (v - a' * k)"
      by (simp add: algebra_simps)
    also have "\<dots> = l"
      by (subst eq) (auto simp: ab_eq algebra_simps)
    finally show "a * (u + b' * k) + b * (v - a' * k) = l" .
  qed
  moreover have "{(x,y). a * x + b * y = l} \<subseteq> (\<lambda>k. (u + b' * k, v - a' * k)) ` UNIV"
  proof
    fix xy assume xy: "xy \<in> {(x,y). a * x + b * y = l}"
    obtain x y where [simp]: "xy = (x, y)"
      by (cases xy)
    have "a * (x - u) = b * (v - y)"
      using xy assms by (simp add: algebra_simps)
    hence "D * (a' * (x - u)) = D * (b' * (v - y))"
      by (simp add: ab_eq mult_ac)
    hence eq: "a' * (x - u) = b' * (v - y)"
      by (subst (asm) mult_cancel_left) auto
    have "b' dvd (x - u) \<and> a' dvd (v - y)"
      using eq coprime by (metis Rings.coprime_commute coprime_dvd_mult_right_iff dvdI)
    then obtain c d where "x - u = b' * c" "v - y = a' * d"
      by (elim dvdE conjE)
    hence xy_eq: "x = u + b' * c" "y = v - a' * d"
      by (auto simp: algebra_simps)

    consider "a = 0" "b \<noteq> 0" | "a \<noteq> 0" "b = 0" | "a \<noteq> 0" "b \<noteq> 0"
      using nz by blast
    thus "xy \<in> range (\<lambda>k. (u + b' * k, v - a' * k))"
    proof cases
      assume "a = 0" "b \<noteq> 0"
      thus ?thesis using assms
        by (intro range_eqI[of _ _ "c"]) (auto simp: xy_eq ab_eq)
    next
      assume "a \<noteq> 0" "b = 0"
      thus ?thesis
        by (intro range_eqI[of _ _ d]) (auto simp: xy_eq ab_eq)
    next
      assume nz: "a \<noteq> 0" "b \<noteq> 0"
      have "a * b * c = a * b * d"
        using eq by (simp add: xy_eq algebra_simps ab_eq)
      hence "d = c"
        by (subst (asm) mult_left_cancel) (use nz in auto)
      thus ?thesis 
        by (intro range_eqI[of _ _ c]) (auto simp: xy_eq)
    qed
  qed
  moreover have "inj (\<lambda>k. (u + b' * k, v - a' * k))"
    using assms nz by (auto intro!: injI simp: ab_eq)
  ultimately show ?thesis
    unfolding bij_betw_def unfolding a'_def b'_def D_def by blast
qed


subsubsection \<open>Independent families of vectors and indexed bases\<close>

text \<open>
  We define independent families of vectors and indexed bases, which is more convenient for
  our purposes than looking at a basis only as a set of vectors.
\<close>
lemma (in vector_space) dim_ge_card_imp_independent:
  assumes "finite X" "dim X \<ge> card X"
  shows   "independent X"
proof -
  obtain B where B: "B \<subseteq> X" "local.independent B" "X \<subseteq> local.span B" "card B = local.dim X"
    using basis_exists[of X] by blast
  have "B = X"
  proof (rule card_subset_eq)
    have "card X \<ge> dim X"
      by (rule dim_le_card') fact+
    hence "card X = dim X"
      using assms(2) by linarith
    thus "card B = card X"
      using B by simp
  qed (use B assms in auto)
  with B show ?thesis
    by simp
qed

lemma (in vector_space) dim_trivial_eq_0 [simp]: "dim {0} = 0"
proof -
  have "dim {0} = dim (span {})"
    by simp
  also have "\<dots> = card ({} :: 'b set)"
    by (rule dim_span_eq_card_independent) (auto simp: independent_empty)
  finally show ?thesis by simp
qed


locale vector_space_independent_family = vector_space +
  fixes f :: "'c \<Rightarrow> 'b" and I :: "'c set"
  assumes inj: "inj_on f I"
  assumes independent: "independent (f ` I)"

locale vector_space_indexed_basis = vector_space_independent_family +
  fixes X :: "'b set"
  assumes span: "span (f ` I) = X"

abbreviation (in vector_space) independent_family :: "('c \<Rightarrow> 'b) \<Rightarrow> 'c set \<Rightarrow> bool" where
  "independent_family \<equiv> vector_space_independent_family scale"

abbreviation (in vector_space) indexed_basis :: "('c \<Rightarrow> 'b) \<Rightarrow> 'c set \<Rightarrow> 'b set \<Rightarrow> bool" where
  "indexed_basis \<equiv> vector_space_indexed_basis scale"

lemma (in vector_space) independent_familyI:
  assumes "\<And>J c. J \<subseteq> I \<Longrightarrow> finite J \<Longrightarrow> (\<Sum>x\<in>J. scale (c x) (f x)) = 0 \<Longrightarrow> (\<forall>x\<in>J. c x = 0)"
  shows   "independent_family f I"
proof
  have False if xy: "x \<in> I" "y \<in> I" "x \<noteq> y" "f x = f y" for x y
  proof -
    define c where "c = (\<lambda>z. if z = x then 1 else -1 :: 'a)"
    have "(\<forall>z\<in>{x,y}. c z = 0)"
      by (rule assms) (use xy in \<open>auto simp: c_def\<close>)
    thus False
      using xy by (auto simp: c_def)
  qed
  thus inj: "inj_on f I"
    by (auto simp: inj_on_def)

  define g where "g = inv_into I f"
  have [simp]: "g (f x) = x" if "x \<in> I" for x
    using that inj by (auto simp:g_def)

  show "local.independent (f ` I)"
  proof
    assume "local.dependent (f ` I)"
    then obtain J c where *: "finite J" "J \<subseteq> f ` I" "(\<Sum>v\<in>J. scale (c v) v) = 0" "\<exists>v\<in>J. c v \<noteq> 0"
      unfolding local.dependent_explicit by blast
    define J' where "J' = g ` J"
    have "J' \<subseteq> I"
      using * inj unfolding J'_def g_def by fastforce

    have bij: "bij_betw f J' J"
    proof (rule bij_betw_subset)
      show "bij_betw f I (f ` I)"
        using inj by (rule inj_on_imp_bij_betw)
      show "f ` J' = J"
        unfolding J'_def g_def using inj * by (meson image_inv_into_cancel)
    qed (use \<open>J' \<subseteq> I\<close> in auto)

    have "\<forall>x\<in>J'. c (f x) = 0"
    proof (rule assms)
      have "(\<Sum>v\<in>J. scale (c v) v) = (\<Sum>x\<in>J'. scale (c (f x)) (f x))"
        by (rule sum.reindex_bij_betw[OF bij, symmetric])
      with * show "(\<Sum>x\<in>J'. scale (c (f x)) (f x)) = 0"
        by simp
    qed (use bij_betw_finite[OF bij] * \<open>J' \<subseteq> I\<close> in simp_all)
    hence "\<forall>x\<in>f`J'. c x = 0"
      by blast
    also have "f ` J' = J"
      using bij by (auto simp: bij_betw_def)
    finally have "\<forall>x\<in>J. c x = 0" .
    with *(4) show False by blast
  qed
qed

lemma (in vector_space) independent_familyI_finite:
  assumes "\<And>c. (\<Sum>x\<in>I. scale (c x) (f x)) = 0 \<Longrightarrow> (\<forall>x\<in>I. c x = 0)"
  assumes "finite I"
  shows   "local.independent_family f I"
proof (rule independent_familyI)
  fix J c assume *: "J \<subseteq> I" "finite J" "(\<Sum>x\<in>J. scale (c x) (f x)) = 0"
  define c' where "c' = (\<lambda>x. if x \<in> J then c x else 0)"
  have "(\<Sum>x\<in>J. scale (c x) (f x)) = 0"
    by fact
  also have "(\<Sum>x\<in>J. scale (c x) (f x)) = (\<Sum>x\<in>I. scale (c' x) (f x))"
    by (rule sum.mono_neutral_cong_left) (use * assms(2) in \<open>auto simp: c'_def\<close>)
  finally have "\<forall>x\<in>I. c' x = 0"
    by (rule assms(1))
  thus "\<forall>x\<in>J. c x = 0"
    using *(1) by (auto simp: c'_def split: if_splits)
qed

lemma (in vector_space_independent_family) representation_0_iff:
  assumes "J \<subseteq> I" "finite J"
  shows   "(\<Sum>x\<in>J. scale (c x) (f x)) = 0 \<longleftrightarrow> (\<forall>x\<in>J. c x = 0)"
proof -
  define g where "g = inv_into J f"
  have [simp]: "g (f x) = x" if "x \<in> J" for x
    using that assms inj unfolding g_def by (meson inj_on_subset inv_into_f_f)
  from inj have "bij_betw f J (f ` J)"
    by (meson assms(1) bij_betw_def inj_on_subset)
  hence g: "bij_betw g (f ` J) J"
    unfolding g_def by (rule bij_betw_inv_into)
  define c' where "c' = c \<circ> g"

  have "(\<Sum>x\<in>J. scale (c x) (f x)) = (\<Sum>x\<in>f ` J. scale (c (g x)) (f (g x)))"
    by (subst sum.reindex_bij_betw[OF g, symmetric]) auto
  also have "\<dots> = (\<Sum>x\<in>f ` J. scale (c' x) x)"
    by (intro sum.cong) (use assms in \<open>auto simp: c'_def\<close>)
  also have "\<dots> = 0 \<longleftrightarrow> (\<forall>x\<in>f`J. c' x = 0)"
  proof
    assume "(\<Sum>x\<in>f ` J. scale (c' x) x) = 0"
    thus "\<forall>x\<in>f`J. c' x = 0"
      using independentD[of "f ` I" "f ` J" c'] assms independent by auto
  next
    assume "\<forall>x\<in>f`J. c' x = 0"
    thus "(\<Sum>x\<in>f ` J. scale (c' x) x) = 0"
      by (intro sum.neutral) auto
  qed
  also have "\<dots> \<longleftrightarrow> (\<forall>x\<in>J. c x = 0)"
    by (auto simp: c'_def)
  finally show ?thesis .
qed

lemma (in vector_space_independent_family) independent_family_subset:
  assumes "J \<subseteq> I"
  shows   "independent_family f J"
proof
  show "inj_on f J"
    using inj assms inj_on_subset by blast
  show "independent (f ` J)"
    using independent assms dependent_mono[of "f ` J" "f ` I"]  by blast
qed

lemma (in vector_space_independent_family) indexed_basisI:
  assumes "subspace X"
  assumes "\<And>i. i \<in> I \<Longrightarrow> f i \<in> X"
  assumes "\<And>x. x \<in> X \<Longrightarrow> \<exists>J c. finite J \<and> J \<subseteq> I \<and> x = (\<Sum>y\<in>J. scale (c y) (f y))"
  shows   "indexed_basis f I X"
proof
  have "local.span (f ` I) \<subseteq> X"
    by (rule span_minimal) (use assms(1,2) in auto)
  moreover have "X \<subseteq> local.span (f ` I)"
  proof
    fix x assume "x \<in> X"
    then obtain J c where *: "finite J" "J \<subseteq> I" "x = (\<Sum>y\<in>J. scale (c y) (f y))"
      using assms(3) by blast

    define g where "g = inv_into J f"
    have [simp]: "g (f x) = x" if "x \<in> J" for x
      using that * inj unfolding g_def by (meson inj_on_subset inv_into_f_f)
    from inj and *(2) have "bij_betw f J (f ` J)"
      by (meson bij_betw_def inj_on_subset)
    hence g: "bij_betw g (f ` J) J"
      unfolding g_def by (rule bij_betw_inv_into)
    define c' where "c' = c \<circ> g"

    have "(\<Sum>y\<in>f`J. scale (c' y) y) \<in> span (f ` I)"
      by (intro span_sum span_scale) (use * in \<open>auto intro: span_base\<close>)
    also have "(\<Sum>y\<in>f`J. scale (c' y) y) = (\<Sum>y\<in>J. scale (c' (f y)) (f y))"
      by (subst sum.reindex) (use inj * in \<open>auto simp: inj_on_subset\<close>)
    also have "\<dots> = (\<Sum>y\<in>J. scale (c y) (f y))"
      by (rule sum.cong) (use * in \<open>auto simp: c'_def\<close>)
    also have "\<dots> = x"
      using * by simp
    finally show "x \<in> local.span (f ` I)" .
  qed
  ultimately show "local.span (f ` I) = X"
    by blast
qed 

lemma (in vector_space_independent_family) indexed_basisI_finite:
  assumes "subspace X" "finite I"
  assumes "\<And>i. i \<in> I \<Longrightarrow> f i \<in> X"
  assumes "\<And>x. x \<in> X \<Longrightarrow> \<exists>c. x = (\<Sum>y\<in>I. scale (c y) (f y))"
  shows   "indexed_basis f I X"
proof (rule indexed_basisI)
  fix x assume "x \<in> X"
  then obtain c where *: "x = (\<Sum>y\<in>I. scale (c y) (f y))"
    using assms by blast
  thus "\<exists>J c. finite J \<and> J \<subseteq> I \<and> x = (\<Sum>y\<in>J. scale (c y) (f y))"
    by (intro exI[of _ I] exI[of _ c]) (use assms * in auto)
qed (use assms in auto)

lemma (in vector_space_indexed_basis) indexed_basis_imp_representation:
  assumes "x \<in> X"
  obtains J c where "J \<subseteq> I" "finite J" "x = (\<Sum>y\<in>J. scale (c y) (f y))"
proof -
  define g where "g = inv_into I f"
  have [simp]: "g (f x) = x" if "x \<in> I" for x
    using that inj by (auto simp: g_def)

  from assms have "x \<in> span (f ` I)"
    using span by auto
  then obtain c J where *: "finite J" "J \<subseteq> f ` I" "x = (\<Sum>y\<in>J. scale (c y) y)"
    unfolding span_explicit by blast
  define c' where "c' = (\<lambda>x. c (f x))"
  define J' where "J' = g ` J"
  have "J' \<subseteq> I"
    using * inj unfolding J'_def g_def by fastforce

  have bij: "bij_betw f J' J"
  proof (rule bij_betw_subset)
    show "bij_betw f I (f ` I)"
      using inj by (rule inj_on_imp_bij_betw)
    show "f ` J' = J"
      unfolding J'_def g_def using inj * by (meson image_inv_into_cancel)
  qed (use \<open>J' \<subseteq> I\<close> in auto)

  have "x = (\<Sum>x\<in>J'. scale (c' x) (f x))"
    using * by (subst (asm) sum.reindex_bij_betw[OF bij, symmetric]) (auto simp: c'_def)
  thus ?thesis
    by (intro that[of J' c']) (use \<open>J' \<subseteq> I\<close> bij_betw_finite[OF bij] \<open>finite J\<close> in simp_all)
qed

lemma (in vector_space_indexed_basis) indexed_basis_imp_representation_finite:
  assumes "x \<in> X" "finite I"
  obtains c where "x = (\<Sum>y\<in>I. scale (c y) (f y))"
proof -
  obtain J c where *: "J \<subseteq> I" "finite J" "x = (\<Sum>y\<in>J. scale (c y) (f y))"
    using assms by (elim indexed_basis_imp_representation)
  define c' where "c' = (\<lambda>y. if y \<in> J then c y else 0)"
  have "(\<Sum>y\<in>J. scale (c y) (f y)) = (\<Sum>y\<in>I. scale (c' y) (f y))"
    by (rule sum.mono_neutral_cong_left) (use * \<open>finite I\<close> in \<open>auto simp: c'_def\<close>)
  thus ?thesis
    using *(3) by (intro that[of c']) auto
qed

lemma (in vector_space_indexed_basis) indexed_basis_imp_dim:
  assumes "finite I"
  shows   "dim X = card I"
proof -
  have "dim X = dim (span (f ` I))"
    by (simp add: span)
  also have "\<dots> = card (f ` I)"
    using independent by (rule dim_span_eq_card_independent)
  also have "\<dots> = card I"
    using inj by (rule card_image)
  finally show ?thesis .
qed

(* END TODO *)


subsection \<open>Basic structure lemmas\<close>

text \<open>
  We first derive a few facts about the structure of low-weight modular forms on 
  $\text{SL}(2,\mathbb{Z})$, all of which follow directly from the valence formula.
\<close>

unbundle modgrp_notation

lemmas (in cong_subgroup) [intro] = cong_subgroup_axioms

interpretation modgrp: cong_subgroup UNIV
  by standard

text \<open>
  The following four theorems constitute Apostol's Theorem 6.2.

  First, the modular forms of weight 0 are exactly the constant functions.
\<close>
theorem MForms_0_eq_constant: "MForms[0] = range const_mero_uhp"
proof safe
  show "const_mero_uhp c \<in> MForms[0]" for c
    by (auto intro: mform_intros)
next
  fix g assume g: "g \<in> MForms[0]"
  define f where "f = g - const_mero_uhp (g \<i>)"
  have f: "f \<in> MForms[0]"
    by (auto simp: f_def intro!: mform_intros g)
  have [simp]: "\<not>is_pole (eval_mero_uhp g) \<i>"
    using g no_poles_MForms by blast
  interpret f: modular_form f 0 UNIV
    using f by auto

  have "f = 0"
  proof (rule ccontr)
    assume "f \<noteq> 0"
    with f have f: "f \<in> MForms[0] - {0}"
      by auto
    have zorder_ge: "zorder_mero_uhp f z \<ge> 0" if "Im z > 0" for z
      using that f by blast
    have zorder_ge': "zorder_at_ii_inf 1 f \<ge> 0"
      using f.zorder_at_ii_inf_ge_0 by simp
    have zorder_ge'': "zorder_mero_uhp f \<^bold>\<rho> \<ge> 0" "zorder_mero_uhp f \<i> \<ge> 0"
      using zorder_ge[of "\<^bold>\<rho>"] zorder_ge[of \<i>] f by auto
    define C where "C = sum (zorder_mero_uhp f) (zeros_mero_uhp f - {\<i>, \<^bold>\<rho>})"
    have "C \<ge> 0" unfolding C_def
      by (intro sum_nonneg zorder_ge) (auto simp: inv_image_mero_uhp_def in_std_fund_region'_iff)
    have "zorder_mero_uhp f \<i> = 0"
      using MForms_valence_formula'[OF f] zorder_ge' zorder_ge'' \<open>C \<ge> 0\<close>
      unfolding C_def [symmetric] by linarith+
    hence "f \<i> \<noteq> 0"
      using f by auto
    also have "f \<i> = 0"
      by (simp add: f_def eval_mero_uhp_diff)
    finally show False
      by simp
  qed
  thus "g \<in> range const_mero_uhp"
    by (auto simp: f_def)
qed

text \<open>
  The weight of a non-zero modular form must be even and at least 4.
\<close>
theorem MForms_eq_0:
  assumes "k < 0 \<or> k = 2 \<or> odd k"
  shows   "MForms[k] = {0}"
proof -
  have "0 \<in> MForms[k]"
    by auto
  moreover have "f = 0" if f: "f \<in> MForms[k]" for f
  proof (rule ccontr)
    assume "f \<noteq> 0"
    with f have f: "f \<in> MForms[k] - {0}"
      by auto
    interpret f: modular_form f k UNIV
      using f by blast
    have zorder_ge: "zorder_mero_uhp f z \<ge> 0" if "Im z > 0" for z
      using that f by blast
    have zorder_ge': "zorder_at_ii_inf 1 f \<ge> 0"
      using f.zorder_at_ii_inf_ge_0 by simp
    have zorder_ge'': "zorder_mero_uhp f \<^bold>\<rho> \<ge> 0" "zorder_mero_uhp f \<i> \<ge> 0"
      using zorder_ge[of "\<^bold>\<rho>"] zorder_ge[of \<i>] f by auto
    define C where "C = sum (zorder_mero_uhp f) (zeros_mero_uhp f - {\<i>, \<^bold>\<rho>})"
    have "C \<ge> 0" unfolding C_def
      by (intro sum_nonneg zorder_ge) (auto simp: inv_image_mero_uhp_def in_std_fund_region'_iff)
    from f and \<open>f \<noteq> 0\<close> have "f \<in> MForms[k] - {0}"
      by auto
    note valence = MForms_valence_formula'[OF this, folded C_def]
    have "k \<ge> 0"
      using valence zorder_ge' zorder_ge'' \<open>C \<ge> 0\<close> by linarith
    moreover have "even k"
      using valence zorder_ge' zorder_ge'' \<open>C \<ge> 0\<close> by presburger
    moreover have "k \<noteq> 2"
      using valence zorder_ge' zorder_ge'' \<open>C \<ge> 0\<close> by presburger
    ultimately show False
      using assms by linarith
  qed
  ultimately show ?thesis by blast
qed

lemma MForms_weight_even: "f \<in> MForms[k] - {0} \<Longrightarrow> even k"
  using MForms_eq_0[of k] by auto

theorem MForms_weight_ge_4: 
  assumes "f \<in> MForms[k]" "\<not>is_const_mero_uhp f"
  shows   "k \<ge> 4"
proof -
  from assms have "k \<noteq> 0"
    by (auto simp: MForms_0_eq_constant)
  have "MForms[k] \<noteq> {0}"
    using assms by force
  with MForms_eq_0[of k] have "k \<ge> 0 \<and> k \<noteq> 2 \<and> even k"
    by linarith
  with \<open>k \<noteq> 0\<close> show ?thesis
    by auto
qed

text \<open>
  The following lemma lists the zeros of all non-zero modular forms up to weight 15 
  (except weight 12), including multiplicities.
\<close>
lemma zeros_MForms_upto_15:
  assumes f [mform_intros]: "f \<in> MForms[k]" and k: "k \<in> {1..15} - {12}"
  assumes [simp]: "f \<noteq> 0"
  shows   "Im z > 0 \<Longrightarrow> \<not>z \<sim>\<^sub>\<Gamma> \<^bold>\<rho> \<Longrightarrow> \<not>z \<sim>\<^sub>\<Gamma> \<i> \<Longrightarrow> eval_mero_uhp f z \<noteq> 0"
    and   "z \<sim>\<^sub>\<Gamma> \<^bold>\<rho> \<Longrightarrow> zorder_mero_uhp f z = (if k = 6 then 0 else if k \<in> {8, 14} then 2 else 1)"
    and   "z \<sim>\<^sub>\<Gamma> \<i> \<Longrightarrow> zorder_mero_uhp f z = (if k \<in> {4, 8} then 0 else 1)"
proof -
  interpret f: modular_form f k UNIV
    using f by blast
  from assms interpret modular_form f k UNIV
    by auto
  from k have k: "k > 0" "k \<le> 15" "k \<noteq> 12"
    by auto
  define m where "m = nat (zorder_mero_uhp f \<^bold>\<rho>)"
  define n where "n = nat (zorder_mero_uhp f \<i>)"
  have zorder_ge_aux: "zorder_mero_uhp f z \<ge> 0" if "Im z > 0" for z
    using that f by (intro zorder_MForms_nonneg[OF f] that) auto
  have zorder_ge': "zorder_at_ii_inf (Suc 0) f \<ge> 0" using f
    using f.zorder_at_ii_inf_ge_0 by simp
  have zorder_ge'': "zorder_mero_uhp f \<^bold>\<rho> \<ge> 0" "zorder_mero_uhp f \<i> \<ge> 0"
    using zorder_ge_aux[of "\<^bold>\<rho>"] zorder_ge_aux[of \<i>] f by auto
  define C where "C = sum (zorder_mero_uhp f) (zeros_mero_uhp f - {\<i>, \<^bold>\<rho>})"
  have "C \<ge> 0" unfolding C_def
    by (intro sum_nonneg zorder_ge_aux) (auto simp: inv_image_mero_uhp_def in_std_fund_region'_iff)
  define l where "l = nat (zorder_at_ii_inf (Suc 0) f) + nat C"
  note zorder_ge = zorder_ge' zorder_ge'' \<open>C \<ge> 0\<close>
  from f have f: "f \<in> MForms[k] - {0}"
    by auto
  have "12 * l + 4 * m + 6 * n = k"
    using MForms_valence_formula'[OF f] \<open>C \<ge> 0\<close> zorder_ge
    unfolding l_def C_def m_def n_def by simp
  moreover from this have "l = 0"
    using \<open>k \<noteq> 12\<close> \<open>k \<le> 15\<close> by presburger
  ultimately have valence: "4 * m + 6 * n = k"
    by simp
  from \<open>l = 0\<close> have "C = 0"
    unfolding l_def using zorder_ge by linarith

  have False if z: "z \<in> zeros_mero_uhp f - {\<i>, \<^bold>\<rho>}" for z
  proof -
    have z': "Im z > 0"
      using z by (auto simp: inv_image_mero_uhp_def in_std_fund_region'_iff)
    have "zorder_mero_uhp f z = 0"
    proof (rule sum_nonneg_0[of _ "zorder_mero_uhp f"])
      show "sum (zorder_mero_uhp f) (zeros_mero_uhp f - {\<i>, \<^bold>\<rho>}) = 0"
        using \<open>C = 0\<close> unfolding C_def by simp
      show "finite (zeros_mero_uhp f - {\<i>, \<^bold>\<rho>})"
      proof -
        interpret modular_form f k UNIV
          using f by auto
        show ?thesis
          by auto
      qed
      show "z \<in> zeros_mero_uhp f - {\<i>, \<^bold>\<rho>}"
        by fact
      show "zorder_mero_uhp f z \<ge> 0" if "z \<in> zeros_mero_uhp f - {\<i>, \<^bold>\<rho>}" for z
        using that by (auto simp: inv_image_mero_uhp_def in_std_fund_region'_iff)
    qed
    hence "eval_mero_uhp f z \<noteq> 0" using z' by force
    thus False
      using z by (auto simp: inv_image_mero_uhp_def)
  qed
  hence zeros_subset: "zeros_mero_uhp f \<subseteq> {\<i>, \<^bold>\<rho>}"
    by blast

  show "eval_mero_uhp f z \<noteq> 0" if "Im z > 0" "\<not>z \<sim>\<^sub>\<Gamma> \<^bold>\<rho>" "\<not>z \<sim>\<^sub>\<Gamma> \<i>"
  proof -
    obtain z' where z': "z \<sim>\<^sub>\<Gamma> z'" "z' \<in> \<R>\<^sub>\<Gamma>'"
      using \<open>0 < Im z\<close> canonical_point_in_std_fund_region' by blast
    then obtain h where h: "z' = apply_modgrp h z"
      by (auto simp: modular_group.rel_def)
    have not_equiv: "z' \<noteq> \<^bold>\<rho>" "z' \<noteq> \<i>"
      using that z' by auto
    have "eval_mero_uhp f z' \<noteq> 0"
    proof
      assume "eval_mero_uhp f z' = 0"
      hence "z' \<in> zeros_mero_uhp f - {\<i>, \<^bold>\<rho>}"
        using z' not_equiv f f.no_poles
        by (auto simp: inv_image_mero_uhp_def)
      with zeros_subset show False
        by blast
    qed
    also have "eval_mero_uhp f z' = automorphy_factor h z powi k * eval_mero_uhp f z"
      using z' h by simp
    finally show ?thesis
      using \<open>Im z > 0\<close> by auto
  qed

  from valence and k have "m \<le> 2 \<and> n \<le> 1"
    by presburger
  hence "(m = 0 \<or> m = 1 \<or> m = 2) \<and> (n = 0 \<or> n = 1)"
    by fastforce
  hence mn: "(m, n) \<in> {(1, 0), (0, 1), (2, 0), (1, 1), (2, 1)}"
    using valence k unfolding insert_iff empty_iff prod.inject
    by (elim disjE conjE) simp_all

  show "zorder_mero_uhp f z = (if k = 6 then 0 else if k \<in> {8, 14} then 2 else 1)" if "z \<sim>\<^sub>\<Gamma> \<^bold>\<rho>"
  proof -
    have "zorder_mero_uhp f z = m"
      unfolding m_def using that by (auto intro: f.rel_imp_zorder_eq)
    also have "m = (if k = 6 then 0 else if k \<in> {8, 14} then 2 else 1)"
      using valence mn by auto
    finally show ?thesis by simp
  qed

  show "zorder_mero_uhp f z = (if k \<in> {4, 8} then 0 else 1)" if "z \<sim>\<^sub>\<Gamma> \<i>"
  proof -
    have "zorder_mero_uhp f z = n"
      unfolding n_def using that by (auto intro: f.rel_imp_zorder_eq)
    also have "n = (if k \<in> {4, 8} then 0 else 1)"
      using valence mn by auto
    finally show ?thesis by simp
  qed
qed

text \<open>
  The zeros of $G_4$ and $G_6$ are exactly the points equivalent to $i$ and $\rho$, respectively,
  and they have multiplicity 1 (in the normal complex analysis sense, not factoring in the
  elliptic order).
\<close>
lemma Eisenstein_E_4_zero_iff [simp]:
  assumes "Im z > 0"
  shows   "Eisenstein_E 4 z = 0 \<longleftrightarrow> z \<sim>\<^sub>\<Gamma> \<^bold>\<rho>"
proof
  assume "z \<sim>\<^sub>\<Gamma> \<^bold>\<rho>"
  thus "Eisenstein_E 4 z = 0" using Eisenstein_E_4_rho assms
    by (metis Eisenstein_E4.not_2 Eisenstein_E_apply_modgrp
        modular_group.rel_def modular_group.rel_sym mult_eq_0_iff)
next
  assume *: "Eisenstein_E 4 z = 0"
  have **: "\<E>\<^sub>4 \<in> MForms[4]"
    by (rule mform_intros) auto
  from zeros_MForms_upto_15[OF **, of z] * assms show "z \<sim>\<^sub>\<Gamma> \<^bold>\<rho>"
    by auto
qed

lemma Eisenstein_E_6_zero_iff [simp]:
  assumes "Im z > 0"
  shows   "Eisenstein_E 6 z = 0 \<longleftrightarrow> z \<sim>\<^sub>\<Gamma> \<i>"
proof
  assume "z \<sim>\<^sub>\<Gamma> \<i>"
  thus "Eisenstein_E 6 z = 0" using Eisenstein_E_6_ii assms
    by (metis Eisenstein_E6.not_2 Eisenstein_E_apply_modgrp
        modular_group.rel_def modular_group.rel_sym mult_eq_0_iff)
next
  assume *: "Eisenstein_E 6 z = 0"
  have **: "\<E>\<^sub>6 \<in> MForms[6]"
    by (rule mform_intros) auto
  from zeros_MForms_upto_15[OF **, of z] * assms show "z \<sim>\<^sub>\<Gamma> \<i>"
    by auto
qed

lemma zorder_Eisenstein_E4_rho: "zorder \<E>\<^sub>4 \<^bold>\<rho> = 1"
  using zeros_MForms_upto_15[of "\<E>\<^sub>4" 4 "\<^bold>\<rho>"] E_in_MForms[of 4 4] by simp_all

lemma zorder_Eisenstein_E6_ii: "zorder \<E>\<^sub>6 \<i> = 1"
  using zeros_MForms_upto_15[of "\<E>\<^sub>6" 6 "\<i>"] E_in_MForms[of 6 6] by simp_all

lemma MForms_zorder_ge_imp_same:
  assumes "f \<in> MForms[k]" "g \<in> MForms[k]" "g \<noteq> 0"
  assumes "\<And>z. f \<noteq> 0 \<Longrightarrow> Im z > 0 \<Longrightarrow> zorder_mero_uhp f z \<ge> zorder_mero_uhp g z"
  assumes "\<And>h. f \<noteq> 0 \<Longrightarrow> zorder_at_ii_inf 1 f \<ge> zorder_at_ii_inf 1 g"
  shows "\<exists>c. f = \<langle>c\<rangle> * g"
proof -
  have "f / g \<in> MForms[0]"
    by (rule MForms_UNIV_divide[OF assms(1,2)]) (use assms(3-) in \<open>auto intro!: assms(1,2)\<close>)
  then obtain c where "f / g = \<langle>c\<rangle>"
    using MForms_0_eq_constant by auto
  with \<open>g \<noteq> 0\<close> show ?thesis by (intro exI[of _ c]) (auto simp: field_simps)
qed

text \<open>
  Any modular form of weight $k \leq 15$ and $k\neq 12$ is a constant multiple of $G_k$.
\<close>
lemma MForms_upto_15:
  assumes f: "f \<in> MForms[k]" and "k \<in> {0..15} - {12}"
  shows   "\<exists>c. f = \<langle>c\<rangle> * \<E> (nat k)"
proof (cases "k = 0")
  case True
  thus ?thesis using assms
    by (auto simp: MForms_0_eq_constant)
next
  case False
  with assms have k: "k \<in> {1..15} - {12}"
    by auto
  interpret f: modular_form f k UNIV rewrites "cusp_width\<^sub>\<infinity> UNIV = Suc 0"
    using f by auto
  show ?thesis
  proof (cases "f = 0")
    case False
    show ?thesis
    proof (cases "odd k \<or> k < 4")
      case True
      have *: "k < 0 \<or> k = 2 \<or> odd k"
        using \<open>k \<noteq> 0\<close> k True by auto
      thus ?thesis using MForms_eq_0[OF *] k f
        by (intro exI[of _ 0]) simp_all
    next
      case k': False
      show ?thesis
      proof (rule MForms_zorder_ge_imp_same)
        show "f \<in> MForms[k]" by fact
        show g: "\<E> (nat k) \<in> MForms[k]" by (rule mform_intros) (use k k' in auto)
        show nz: "\<E> (nat k) \<noteq> 0" 
          using k k' by (auto simp: even_nat_iff)

        fix z assume z: "Im z > 0" and [simp]: "f \<noteq> 0"
        show "zorder_mero_uhp (\<E> (nat k)) z \<le> zorder_mero_uhp f z"
        proof (cases "eval_mero_uhp (\<E> (nat k)) z = 0")
          case False
          hence "zorder_mero_uhp (\<E> (nat k)) z = 0"
            by (subst zorder_mero_uhp_eq_0_iff) (use z k' assms(2) in \<open>auto simp: even_nat_iff\<close>)
          moreover have "zorder_mero_uhp f z \<ge> 0"
            by (intro zorder_MForms_nonneg[OF f]) (use z in auto)
          ultimately show ?thesis
            by simp
        next
          case True
          note zeros_f = zeros_MForms_upto_15[OF f k \<open>f \<noteq> 0\<close>, of z]
          note zeros_g = zeros_MForms_upto_15[OF g k nz, of z]
          from zeros_g and z and True have "z \<sim>\<^sub>\<Gamma> \<^bold>\<rho> \<or> z \<sim>\<^sub>\<Gamma> \<i>" by blast
          hence "zorder_mero_uhp (\<E> (nat k)) z = zorder_mero_uhp f z"
            using zeros_f(2,3) zeros_g(2,3) by argo
          thus "zorder_mero_uhp (\<E> (nat k)) z \<le> zorder_mero_uhp f z"
            by simp  
        qed
      qed (use False in \<open>auto simp: even_nat_iff\<close>)
    qed
  qed (auto intro: exI[of _ 0])
qed

text \<open>
  There are no non-zero cusp forms of weight below 12.
\<close>
theorem CForms_eq_0_weak:
  assumes "k < 12"
  shows   "CForms[k] = {0}"
  using assms
proof -
  have "0 \<in> CForms[k]"
    by auto
  moreover have "f = 0" if f: "f \<in> CForms[k]" for f
  proof (rule ccontr)
    assume "f \<noteq> 0"
    with f have f: "f \<in> CForms[k] - {0}"
      by (auto simp: CForms_def)
    interpret f: cusp_form f k UNIV
      using f by blast
    have zorder_ge: "zorder_mero_uhp f z \<ge> 0" if "Im z > 0" for z
      using that f by blast
    have zorder_ge': "zorder_at_ii_inf 1 f > 0" using f
      using f.zorder_at_ii_inf_pos by simp
    have zorder_ge'': "zorder_mero_uhp f \<^bold>\<rho> \<ge> 0" "zorder_mero_uhp f \<i> \<ge> 0"
      using zorder_ge[of "\<^bold>\<rho>"] zorder_ge[of \<i>] f by auto
    define C where "C = sum (zorder_mero_uhp f) (zeros_mero_uhp f - {\<i>, \<^bold>\<rho>})"
    have "C \<ge> 0" unfolding C_def
      by (intro sum_nonneg zorder_ge) (auto simp: inv_image_mero_uhp_def in_std_fund_region'_iff)
    from f have "f \<in> MForms[k] - {0}"
      by auto
    note valence = MForms_valence_formula'[OF this, folded C_def]
    show False
      using valence zorder_ge' zorder_ge'' \<open>C \<ge> 0\<close> \<open>k < 12\<close> by linarith
  qed
  ultimately show ?thesis
    by blast
qed

text \<open>
  Every cusp form of level $k$ can be written as a product of $\Delta$ and a modular form
  of level $k-12$.
\<close>
lemma CForms_split:
  assumes "f \<in> CForms[k]"
  obtains g where "g \<in> MForms[k-12]" "f = g * \<Delta>"
proof (cases "f = 0")
  case True
  thus ?thesis
    by (intro that[of 0]) auto
next
  case [simp]: False
  hence k: "k \<ge> 12"
    using CForms_eq_0_weak[of k] assms by (cases "k \<ge> 12") auto
  interpret f: modular_form f k UNIV rewrites "cusp_width\<^sub>\<infinity> UNIV \<equiv> Suc 0"
    using assms by auto
  show ?thesis
  proof (rule that[of "f / \<Delta>"])
    have [mform_intros]: "f \<in> MForms[k]"
      using assms by blast
    have *: "zorder_at_ii_inf (Suc 0) f \<ge> 1"
      using assms zorder_at_ii_inf_CForms[OF assms] by simp
    show "f / \<Delta> \<in> MForms[k - 12]"
    proof (rule MForms_UNIV_divide)
      show "f \<in> MForms[k]"
        by fact
      show "\<Delta> \<in> MForms[12]"
        by (rule mform_intros)
    qed (use * in auto)
  qed (auto simp: field_simps)
qed

lemma CForms_eq_0:
  assumes "k < 12 \<or> odd k \<or> k = 14"
  shows   "CForms[k] = {0}"
  using assms
proof (elim disjE)
  assume "k < 12"
  thus ?thesis
    by (simp add: CForms_eq_0_weak)
next
  assume "odd k"
  have "CForms[k] \<subseteq> MForms[k]"
    by auto
  also have "\<dots> = {0}"
    using \<open>odd k\<close> by (simp add: MForms_eq_0)
  finally show ?thesis
    by auto
next
  assume [simp]: "k = 14"
  show ?thesis
  proof (intro equalityI subsetI)
    fix f assume "f \<in> CForms[k]"
    then obtain g where "g \<in> MForms[2]" "f = g * \<Delta>"
      using CForms_split[of f 14] by auto
    moreover have "MForms[2] = {0}"
      by (subst MForms_eq_0) auto
    ultimately show "f \<in> {0}"
      by auto
  qed auto
qed

hide_fact CForms_eq_0_weak

text \<open>
  All cusp forms of weight 12 are multiples of the modular discriminant.
\<close>
lemma CForms_12:
  assumes "f \<in> CForms[12]"
  obtains c where "f = \<langle>c\<rangle> * \<Delta>"
  using CForms_split[of f 12] assms by (auto simp: MForms_0_eq_constant)


subsection \<open>The standard basis $E_{k-12i} \Delta^i$\<close>

text \<open>
  The vector space of modular forms of weight $k$ (for even $k \geq 0$) is spanned by basis
  elements of the form $E_{k-12i} \Delta^i$, where $12i \leq k$ and $k - 12i \neq 2$.
  This also directly leads to the dimension formula: the dimension of the space is
  $\lfloor k / 12\rfloor$ if $k = 2\ (\text{mod}\ 12)$ and $\lfloor k / 12\rfloor + 1$ otherwise.

  The basis element for $i = 0$ is the ``Eisenstein part'' and the parts for $i > 0$ span the space
  of cusp forms.
\<close>
locale modular_forms_UNIV_std_basis =
  fixes k :: int
  assumes even_weight: "even k"
  assumes nonneg_weight: "k \<ge> 0"
begin

definition basis :: "nat \<Rightarrow> mero_uhp" where "basis r = \<E> (nat k - 12 * r) * \<Delta> ^ r"
definition idxs :: "nat set" where "idxs = {r. 12 * int r \<le> k \<and> k - 12 * int r \<noteq> 2}"

lemma finite_idxs [intro]: "finite idxs"
proof (rule finite_subset)
  show "idxs \<subseteq> {..nat k div 12}"
    unfolding idxs_def by auto
qed auto

lemma idxs_altdef: "idxs = (if [k = 2] (mod 12) then {..<nat k div 12} else {..nat k div 12})"
proof -
  have "idxs = {r. 12 * int r \<le> k} - {r. k - 12 * int r = 2}"
    by (auto simp: idxs_def)
  also have "{r. 12 * int r \<le> k} = {..nat k div 12}"
    using nonneg_weight by auto
  also have "{r. k - 12 * int r = 2} = (if [k = 2] (mod 12) then {nat k div 12} else {})"
  proof -
    define q r where "q = k div 12" and "r = k mod 12"
    have k_eq: "k = 12 * q + r"
      by (auto simp: q_def r_def)
    have q: "q \<ge> 0"
      using nonneg_weight by (auto simp: r_def q_def)

    have *: "k - 12 * int a = 2 \<longleftrightarrow> int a = q \<and> r = 2" for a
    proof safe
      assume *: "k - 12 * int a = 2"
      have "[k - 12 * int a = 0 * q + r - 0 * int a] (mod 12)"
        unfolding k_eq by (intro cong_diff cong_mult cong_refl) (auto simp: cong_def)
      hence "r mod 12 = 2"
        unfolding * by (simp add: k_eq cong_def)
      also have "r mod 12 = r"
        by (simp add: r_def)
      finally show [simp]: "r = 2" .
      from * show "int a = q"
        by (simp add: k_eq)
    qed (auto simp: k_eq)

    have "{r. k - 12 * int r = 2} = (if r = 2 then {nat q} else {})"
      by (subst *) (use q in auto)
    also have "\<dots> = (if [k = 2] (mod 12) then {nat k div 12} else {})"
      by (auto simp: q_def r_def cong_def)
    finally show ?thesis .
  qed
  also have "{..nat k div 12} - \<dots> = 
               (if [k = 2] (mod 12) then {..<nat k div 12} else {..nat k div 12})"
    by auto
  finally show ?thesis .
qed

lemma card_idxs: "card idxs = nat k div 12 + (if [k = 2] (mod 12) then 0 else 1)"
  by (subst idxs_altdef) (use nonneg_weight in auto)

sublocale vector_space_independent_family "\<lambda>c f. \<langle>c\<rangle> * f" basis idxs
proof (rule mero_uhp.independent_familyI_finite)
  fix c :: "nat \<Rightarrow> complex"
  define l where "l = nat k"
  define I where "I = (\<lambda>k. {r. 12 * r \<le> k \<and> k - 12 * r \<noteq> 2} :: nat set)"
  define B where "B = (\<lambda>k r. \<E> (k - 12 * r) * \<Delta> ^ r)"

  have subset: "I l \<subseteq> {..l div 12}" for l
    by (auto simp: I_def)
  have fin: "finite (I l)" for l
    by (rule finite_subset[of _ "{..l div 12}"]) (auto simp: I_def)
  have idxs_eq: "idxs = I l"
    using nonneg_weight by (auto simp: I_def idxs_def l_def)
  have basis_eq: "basis = B l"
    by (simp add: basis_def [abs_def] B_def l_def)

  assume "(\<Sum>i\<in>idxs. \<langle>c i\<rangle> * basis i) = 0"
  moreover have "even l"
    using even_weight nonneg_weight by (simp add: l_def even_nat_iff)
  ultimately show "\<forall>i\<in>idxs. c i = 0" unfolding idxs_eq basis_eq
  proof (induction l arbitrary: c rule: less_induct)
    case (less l)
    assume "(\<Sum>i\<in>I l. \<langle>c i\<rangle> * B l i) = 0"
    define F where "F = (\<Sum>i\<in>I l. fps_const (c i) * (fps_Eisenstein_E (l - 12 * i) * fps_modular_discr ^ i))"
    have "(\<Sum>i\<in>I l. \<langle>c i\<rangle> * B l i) has_fps_expansion_at_\<i>\<infinity> F"
      unfolding B_def F_def by (intro fps_expansion_intros) auto
    also have "(\<Sum>i\<in>I l. \<langle>c i\<rangle> * B l i) = 0"
      by fact
    finally have "F = 0"
      by (auto simp: zero_has_fps_expansion_at_ii_inf_iff)

    show ?case
    proof (cases "I l = {}")
      case True
      thus ?thesis by blast
    next
      case False
      have [simp]: "l \<noteq> 2"
      proof
        assume [simp]: "l = 2"
        have "I l \<subseteq> {0}"
          using subset[of l] by simp
        moreover have "0 \<notin> I l"
          by (auto simp: I_def)
        ultimately have "I l = {}"
          by auto
        thus False
          using \<open>I l \<noteq> {}\<close> by simp
      qed

      have "fps_nth F 0 = 0"
        by (subst \<open>F = 0\<close>) auto
      also have "fps_nth F 0 = (\<Sum>i\<in>I l. c i * fps_nth (fps_Eisenstein_E (l - 12 * i)) 0 * 
                                           fps_nth fps_modular_discr 0 ^ i)"
        by (simp add: F_def fps_sum_nth mult.assoc fps_nth_power_0)
      also have "\<dots> = (\<Sum>i\<in>{0}. c i)"
        using fin[of l] subset[of l] \<open>even l\<close>
        by (intro sum.mono_neutral_cong_right)
           (auto simp: I_def fps_Eisenstein_E_def  fps_modular_discr_def split: if_splits)
      finally have [simp]: "c 0 = 0"
        by simp

      have "c i = 0" if "i \<in> I l" for i
      proof (cases i)
        case (Suc j)
        have "l \<ge> 12"
          using that Suc by (auto simp: I_def)
        have "\<forall>i\<in>I (l - 12). c (Suc i) = 0"
        proof (rule less.IH)
          have "0 = (\<Sum>i\<in>I l. \<langle>c i\<rangle> * B l i)"
            by (rule sym, fact)
          also have "\<dots> = (\<Sum>i\<in>I l-{0}. \<langle>c i\<rangle> * B l i)"
            by (intro sum.mono_neutral_right fin) auto
          also have "\<dots> = (\<Sum>i\<in>I (l - 12). \<langle>c (Suc i)\<rangle> * B l (Suc i))"
            using \<open>l \<ge> 12\<close>
            by (intro sum.reindex_bij_witness[of _ "\<lambda>i. i + 1" "\<lambda>i. i - 1"]) (auto simp: I_def)
          also have "\<dots> = (\<Sum>i\<in>I (l - 12). \<Delta> * (\<langle>c (Suc i)\<rangle> * B (l - 12) i))"
            using \<open>l \<ge> 12\<close> by (intro sum.cong) (auto simp: B_def algebra_simps)
          also have "\<dots> = \<Delta> * (\<Sum>i\<in>I (l - 12). \<langle>c (Suc i)\<rangle> * B (l - 12) i)"
            by (subst sum_distrib_left) auto
          finally show "(\<Sum>i\<in>I (l - 12). \<langle>c (Suc i)\<rangle> * B (l - 12) i) = 0"
            by simp
        qed (use \<open>even l\<close> \<open>l \<ge> 12\<close> in auto)
        moreover have "j \<in> I (l - 12)"
          using that by (auto simp: Suc I_def)
        ultimately have "c (Suc j) = 0"
          by blast          
        thus ?thesis using Suc by simp
      qed auto
      thus ?thesis
        by blast
    qed
  qed
qed (fact finite_idxs)

sublocale vector_space_indexed_basis "\<lambda>c f. \<langle>c\<rangle> * f" basis idxs "MForms[k]"
proof (rule indexed_basisI_finite)
  show "mero_uhp.subspace MForms[k]"
    by (rule subspace_MForms) auto
next
  show "basis i \<in> MForms[k]" if "i \<in> idxs" for i
    using that by (auto simp: basis_def idxs_def intro!: mform_intros)
next
  define l where "l = nat k"
  define I where "I = (\<lambda>k. {r. 12 * r \<le> k \<and> k - 12 * r \<noteq> 2} :: nat set)"
  define B where "B = (\<lambda>k r. \<E> (k - 12 * r) * \<Delta> ^ r)"

  have subset: "I l \<subseteq> {..l div 12}" for l
    by (auto simp: I_def)
  have fin: "finite (I l)" for l
    by (rule finite_subset[of _ "{..l div 12}"]) (auto simp: I_def)
  have idxs_eq: "idxs = I l"
    using nonneg_weight by (auto simp: I_def idxs_def l_def)
  have basis_eq: "basis = B l"
    by (simp add: basis_def [abs_def] B_def l_def)
  have k_eq: "k = int l"
    using nonneg_weight by (simp add: l_def)

  fix f assume "f \<in> MForms[k]"
  moreover have "even l"
    using even_weight nonneg_weight by (simp add: l_def even_nat_iff)
  ultimately show "\<exists>c. f = (\<Sum>i\<in>idxs. \<langle>c i\<rangle> * basis i)"
    unfolding idxs_eq basis_eq unfolding k_eq
  proof (induction l arbitrary: f rule: less_induct)
    case (less l f)
    show ?case
    proof (cases "f = 0")
      case True
      thus ?thesis
        by (auto intro!: exI[of _ "\<lambda>_. 0"])
    next
      case False
      hence [simp]: "l \<noteq> 2"
        using less.prems(1) MForms_eq_0[of "int l"] by force

      define C where "C = eval_mero_uhp_at_ii_inf f"
      define f' where "f' = f - \<langle>C\<rangle> * \<E> l"
      have "f' \<in> MForms[l]"
        unfolding f'_def using less.prems by (auto intro!: mform_intros)
      moreover have "eval_mero_uhp_at_ii_inf f' = 0"
      proof -
        define F where "F = fps_expansion_at_\<i>\<infinity> (Suc 0) f"
        have 1: "f has_fps_expansion_at_\<i>\<infinity> F"
          unfolding F_def by (rule MForms_UNIV_has_fps_expansion_at_ii_inf) fact
        hence 2: "f' has_fps_expansion_at_\<i>\<infinity> F - fps_const C * fps_Eisenstein_E l"
          unfolding f'_def by (intro fps_expansion_intros) auto
        show "eval_mero_uhp_at_ii_inf f' = 0"
          using has_fps_expansion_at_ii_inf_at_0[OF 1] has_fps_expansion_at_ii_inf_at_0[OF 2] \<open>even l\<close>
          by (simp add: C_def)
      qed
      ultimately have "f' \<in> CForms[l]"
        by (auto simp: CForms_UNIV_altdef)
      then obtain g where g: "g \<in> MForms[int l - 12]" "f' = g * \<Delta>"
        using CForms_split by blast

      show ?thesis
      proof (cases "l \<ge> 12")
        case False
        with g have "g = 0"
          using MForms_eq_0[of "int l - 12"] by auto
        moreover from False have "I l = {0}"
          by (auto simp: I_def)
        ultimately show ?thesis
          by (intro exI[of _ "\<lambda>_. C"]) (use g(2) in \<open>simp_all add: B_def f'_def\<close>)
      next
        case True
        have "\<exists>c. g = (\<Sum>i\<in>I (l - 12). \<langle>c i\<rangle> * B (l - 12) i)"
          by (rule less.IH) (use g(1) \<open>even l\<close> \<open>l \<ge> 12\<close> in auto)
        then obtain c where c: "g = (\<Sum>i\<in>I (l - 12). \<langle>c i\<rangle> * B (l - 12) i)"
          by blast

        define c' where "c' = (\<lambda>i. if i = 0 then C else c (i - 1))"
        have "0 \<in> I l"
          by (auto simp: I_def)
        hence "(\<Sum>i\<in>I l. \<langle>c' i\<rangle> * B l i) = (\<Sum>i\<in>insert 0 (I l-{0}). \<langle>c' i\<rangle> * B l i)"
          by (simp add: insert_absorb)
        also have "\<dots> = \<langle>C\<rangle> * \<E> l + (\<Sum>i\<in>I l-{0}. \<langle>c' i\<rangle> * B l i)"
          using fin[of l] by (subst sum.insert) (auto simp: c'_def B_def)
        also have "(\<Sum>i\<in>I l-{0}. \<langle>c' i\<rangle> * B l i) = (\<Sum>i\<in>I (l - 12). \<langle>c i\<rangle> * B l (Suc i))"
          by (rule sum.reindex_bij_witness[of _ "\<lambda>i. i + 1" "\<lambda>i. i - 1"])
             (use \<open>l \<ge> 12\<close> in \<open>auto simp: I_def c'_def\<close>)
        also have "\<dots> = \<Delta> * g"
          unfolding c sum_distrib_left by (rule sum.cong) (auto simp: B_def)
        also have "\<langle>C\<rangle> * \<E> l + \<Delta> * g = f"
          using g(2) by (simp add: f'_def algebra_simps)
        finally show ?thesis
          by blast
      qed
    qed
  qed
qed (fact finite_idxs)

lemma dim_eq: "mero_uhp.dim MForms[k] = nat k div 12 + (if [k = 2] (mod 12) then 0 else 1)"
proof -
  have "mero_uhp.dim MForms[k] = card idxs"
    by (rule indexed_basis_imp_dim) auto
  also have "\<dots> = nat k div 12 + (if [k = 2] (mod 12) then 0 else 1)"
    by (rule card_idxs)
  finally show ?thesis .
qed

end


theorem dim_MForms_UNIV:
  "mero_uhp.dim MForms[k] =
     (if even k \<and> k \<ge> 0 then nat k div 12 + (if [k = 2] (mod 12) then 0 else 1) else 0)"
proof (cases "even k \<and> k \<ge> 0")
  case True
  then interpret modular_forms_UNIV_std_basis k
    by unfold_locales auto
  show ?thesis
    by (subst dim_eq) (use True in auto)
next
  case False
  hence "MForms[k] = {0}"
    using MForms_eq_0[of k] by auto
  also have "mero_uhp.dim \<dots> = 0"
    by simp
  finally show ?thesis
    using False by auto
qed


subsection \<open>The alternative basis $E_4^i E_6^j$\<close>

text \<open>
  An alternative basis for the modular forms of weight $k$ (for even $k\geq 0$) is given by the
  elements of the form $E_4^i E_6^j$ with $4i + 6j = k$.
\<close>
locale modular_forms_UNIV_E46_basis =
  fixes k :: int
  assumes even_weight: "even k"
  assumes nonneg_weight: "k \<ge> 0"
begin

definition basis :: "nat \<times> nat \<Rightarrow> mero_uhp" where "basis = (\<lambda>(i,j). \<E> 4 ^ i * \<E> 6 ^ j)"
definition idxs :: "(nat \<times> nat) set" where "idxs = {(i,j). 4 * i + 6 * j = k}"

lemma finite_idxs [intro]: "finite idxs"
proof (rule finite_subset)
  show "idxs \<subseteq> {..nat k} \<times> {..nat k}"
    unfolding idxs_def by auto
qed auto

lemma card_idxs: "card idxs = nat k div 12 + (if [k = 2] (mod 12) then 0 else 1)"
proof -
  define l where "l = nat k div 2"
  have k_eq: "k = 2 * int l"
    using even_weight nonneg_weight by (auto simp: l_def)

  define f where "f = (\<lambda>i. (-int l + 3 * i, int l - 2 * i))"
  have bij_f: "bij_betw f UNIV {(i,j). 2 * i + 3 * j = int l}"
    using gen_bezout_solutions[of 2 "-l" 3 l l] by (simp add: f_def)

  have bij_f': 
    "bij_betw f {(int l + 2) div 3..int l div 2} {(i,j). 2 * i + 3 * j = int l \<and> i \<ge> 0 \<and> j \<ge> 0}"
  proof (rule bij_betw_subset [OF bij_f])
    have "f ` {i. int l \<le> 3 * i \<and> 2 * i \<le> int l} = {(i,j). 2 * i + 3 * j = int l \<and> i \<ge> 0 \<and> j \<ge> 0}"
    proof (intro equalityI subsetI)
      fix x assume "x \<in> f ` {i. int l \<le> 3 * i \<and> 2 * i \<le> int l}"
      thus "x \<in> {(i,j). 2 * i + 3 * j = int l \<and> i \<ge> 0 \<and> j \<ge> 0}"
        by (auto simp: f_def)
    next
      fix x assume x: "x \<in> {(i,j). 2 * i + 3 * j = int l \<and> i \<ge> 0 \<and> j \<ge> 0}"
      then obtain i where "x = f i"
        using bij_f by (auto simp: bij_betw_def)
      moreover from this and x have "i \<in> {i. l \<le> 3 * i \<and> 2 * i \<le> l}"
        by (auto simp: f_def)
      ultimately show "x \<in> f ` {i. int l \<le> 3 * i \<and> 2 * i \<le> int l}"
        by blast
    qed
    also have "{i. int l \<le> 3 * i \<and> 2 * i \<le> int l} = {(int l + 2) div 3..int l div 2}"
      by fastforce
    finally show "f ` \<dots> = {(i,j). 2 * i + 3 * j = int l \<and> i \<ge> 0 \<and> j \<ge> 0}" .
  qed auto

  note [trans] = bij_betw_trans
  note bij_f'
  also have "bij_betw (map_prod nat nat) ({(i,j). 2 * i + 3 * j = int l \<and> i \<ge> 0 \<and> j \<ge> 0}) {(i,j). 2 * i + 3 * j = l}"
    by (rule bij_betwI[of _ _ _ "map_prod int int"]) auto
  also have "{(i,j). 2 * i + 3 * j = l} = {(i,j). 4 * int i + 6 * int j = k}"
    by (auto simp: k_eq)
  finally have "card {(int l + 2) div 3..int l div 2} = card {(i,j). 4 * int i + 6 * int j = k}"
    by (rule bij_betw_same_card)
  also have "card {(int l + 2) div 3..int l div 2} = nat (int l div 2 - (int l + 2) div 3 + 1)"
    by simp
  also have "int l div 2 - (int l + 2) div 3 + 1 = int l div 6 + (if [l = 1] (mod 6) then 0 else 1)"
  proof -
    define q r where "q = l div 6" and "r = l mod 6"
    have l_eq: "l = 6 * q + r" and r: "r < 6"
      by (auto simp: q_def r_def)
    have "int l div 2 - (int l + 2) div 3 + 1 = 
            (6 * int q + int r) div 2 - (6 * int q + (int r + 2)) div 3 + 1"
      by (simp add: l_eq)
    also have "\<dots> = int q + (int r div 2 - (int r + 2) div 3) + 1"
      using r by (subst (1 2) div_plus_div_distrib_dvd_left) auto
    also have "r \<in> {0,1,2,3,4,5}"
      using r by auto
    hence "int r div 2 - (int r + 2) div 3 = (if r = 1 then -1 else 0)"
      by (elim insertE emptyE) auto
    also have "int q + \<dots> + 1 = int l div 6 + (if [l = 1] (mod 6) then 0 else 1)"
      by (auto simp: q_def r_def cong_def)
    finally show ?thesis .
  qed
  also have "\<dots> = nat k div 12 + (if l mod 6 = 1 then 0 else 1)"
    by (auto simp: k_eq cong_def)
  also have "l mod 6 = 1 \<longleftrightarrow> (2 * l) mod 12 = 2"
    using mult_mod_right[of 2 l 6, symmetric] by simp
  also have "(2 * l) mod 12 = 2 \<longleftrightarrow> [int (2 * l) = int 2] (mod int 12)"
    by (subst cong_int_iff) (auto simp: cong_def)
  also have "\<dots> \<longleftrightarrow> [k = 2] (mod 12)"
    by (simp add: k_eq)
  finally show "card idxs = nat k div 12 + (if [k = 2] (mod 12) then 0 else 1)"
    using nonneg_weight by (simp add: idxs_def)
qed

sublocale vector_space_indexed_basis "\<lambda>c f. \<langle>c\<rangle> * f" basis idxs "MForms[k]"
proof
  interpret std: modular_forms_UNIV_std_basis k
    by standard (use even_weight nonneg_weight in auto)
  define d where "d = nat k div 12 + (if [k = 2] (mod 12) then 0 else 1)"

  show span: "mero_uhp.span (basis ` idxs) = MForms[k]"
  proof
    show "mero_uhp.span (basis ` idxs) \<subseteq> MForms[k]"
    proof (intro mero_uhp.span_minimal subspace_MForms)
      show "basis ` idxs \<subseteq> MForms[k]"
        by (auto simp: basis_def idxs_def intro!: mform_intros)
    qed auto
  next
    have "MForms[k] = mero_uhp.span (std.basis ` std.idxs)"
      by (simp add: std.span)
    also have "\<dots> \<subseteq> mero_uhp.span (basis ` idxs)"
    proof (intro mero_uhp.span_minimal mero_uhp.subspace_span)
      have "std.basis i \<in> mero_uhp.span (basis ` idxs)" if i: "i \<in> std.idxs" for i
      proof -
        define c where "c = ((4 / 3) ^ 3 * complex_of_real pi ^ 12) ^ i"
        have "\<E> (nat k - 12 * i) * (\<E> 4 ^ 3 - \<E> 6 ^ 2) ^ i \<in> mero_uhp.span (basis ` idxs)"
        proof -
          interpret map1: map_poly_comm_ring_hom "of_rat :: rat \<Rightarrow> mero_uhp"
            by standard auto
          interpret map2: map_poly_comm_ring_hom "map_poly (of_rat :: rat \<Rightarrow> mero_uhp)"
            by standard auto
          define eval where "eval = (\<lambda>p. poly2 (map_poly2 of_rat p) \<E>\<^sub>4 \<E>\<^sub>6)"
          interpret comm_ring_hom eval
            by standard (simp_all add: eval_def hom_distribs map_poly2_def poly2_def)

          define l where "l = nat k div 2"
          have k_eq: "k = 2 * int l"
            using nonneg_weight even_weight by (auto simp: l_def)
          define Q :: "rat poly poly" where "Q = ([:Polynomial.monom 1 3:] - Polynomial.monom 1 2)"
          have "is_46_poly (12*i) (Q ^ i)"
            using is_46_poly_x_power[of 12 3 1] is_46_poly_y_power[of 12 2 1]
            by (auto intro!: is_46_poly_power[of 12] is_46_poly_diff simp: Q_def)
          have [simp]: "eval Q = \<E>\<^sub>4 ^ 3 - \<E>\<^sub>6\<^sup>2"
            by (simp add: Q_def hom_distribs eval_def map_poly2_def poly2_def poly_monom)

          obtain P where P: 
            "is_46_poly (2*l) P" "eval P = \<E> (nat k - 12 * i) * (\<E> 4 ^ 3 - \<E> 6 ^ 2) ^ i"
          proof (cases "nat k = 12 * i")
            case True
            hence k_eq': "k = 12 * int i"
              using nonneg_weight by auto
            show ?thesis
            proof (rule that)
              show "is_46_poly (2 * l) (Q ^ i)"
                using \<open>is_46_poly (12*i) (Q ^ i)\<close> by (simp add: k_eq' l_def nat_mult_distrib)
              show "eval (Q ^ i) = \<E> (nat k - 12 * i) * (\<E>\<^sub>4 ^ 3 - \<E>\<^sub>6\<^sup>2) ^ i"
                by (simp add: hom_distribs k_eq' nat_mult_distrib l_def)
            qed
          next
            case False
            define n where "n = l - 6 * i - 2"
            have "l \<noteq> 6 * i" "6 * int i \<le> int l" "2 * int l - 12 * int i \<noteq> 2"
              using False i unfolding std.idxs_def by (auto simp: k_eq nat_mult_distrib)
            hence l_ge: "l \<ge> 6 * i + 2"
              by presburger
  
            define P where "P = eisenstein_series_poly' n * Q ^ i"
            have "is_46_poly (2 * l) P"
              unfolding P_def
            proof (rule is_46_poly_mult)
              show "is_46_poly (2 * n + 4) (eisenstein_series_poly' n)"
                by (rule is_46_poly_eisenstein_series_poly')
            next
              show "2 * l = 2 * n + 4 + 12 * i"
                using l_ge by (auto simp: n_def k_eq)
            qed (use \<open>is_46_poly (12 * i) (Q ^ i)\<close> in auto)

            moreover have "eval P = \<E> (nat k - 12 * i) * (\<E>\<^sub>4 ^ 3 - \<E>\<^sub>6\<^sup>2) ^ i"
            proof -
              have "eval (eisenstein_series_poly' n) = \<E> (2 * n + 4)"
                unfolding eval_def using eisenstein_series_poly'_mero_uhp[of n] .
              also have "2 * n + 4 = nat k - 12 * i"
                using l_ge by (auto simp: n_def k_eq nat_mult_distrib algebra_simps)
              finally show "eval P = \<E> (nat k - 12 * i) * (\<E>\<^sub>4 ^ 3 - \<E>\<^sub>6\<^sup>2) ^ i"
                by (simp add: P_def hom_distribs)
                   (simp add: eval_def hom_distribs poly_monom map_poly2_def poly2_def)?
            qed

            ultimately show ?thesis
              by (intro that[of P])
          qed

          from P(1) have "eval P \<in> mero_uhp.span (basis ` idxs)"
          proof (induction P rule: is_46_poly_induct)
            fix p and c :: rat assume p: "eval p \<in> mero_uhp.span (basis ` idxs)"
            have "eval (Polynomial.smult [:c:] p) = \<langle>of_rat c\<rangle> * eval p"
              by (simp add: eval_def poly2_def map_poly2_def hom_distribs of_rat_mero_uhp)
            also have "\<dots> \<in> mero_uhp.span (basis ` idxs)"
              by (rule mero_uhp.span_scale) fact
            finally show "eval (Polynomial.smult [:c:] p) \<in> mero_uhp.span (basis ` idxs)" .
          next
            fix i j assume *: "4 * i + 6 * j = 2 * l"
            have "eval (Polynomial.monom (Polynomial.monom 1 i) j) = basis (i, j)"
              by (simp add: eval_def map_poly_monom poly2_def map_poly2_def hom_distribs poly_monom basis_def)
            also have "\<dots> \<in> basis ` idxs"
              unfolding idxs_def by (intro imageI) (use * in \<open>auto simp: k_eq\<close>)
            also have "\<dots> \<subseteq> mero_uhp.span (basis ` idxs)"
              using mero_uhp.span_base by force
            finally show "eval (Polynomial.monom (Polynomial.monom 1 i) j) \<in> \<dots>" .
          qed (auto intro!: mero_uhp.span_add mero_uhp.span_zero simp: hom_distribs)
          also have "eval P = \<E> (nat k - 12 * i) * (\<E>\<^sub>4 ^ 3 - \<E>\<^sub>6\<^sup>2) ^ i"
            by fact
          finally show ?thesis .
        qed
        hence "\<langle>c\<rangle> * (\<E> (nat k - 12 * i) * (\<E> 4 ^ 3 - \<E> 6 ^ 2) ^ i) \<in> mero_uhp.span (basis ` idxs)"
          by (rule mero_uhp.span_scale)
        also have "\<langle>c\<rangle> * (\<E> (nat k - 12 * i) * (\<E> 4 ^ 3 - \<E> 6 ^ 2) ^ i) = std.basis i"
          by (simp add: std.basis_def modular_discr_mero_uhp_def c_def hom_distribs power_mult_distrib)
        finally show ?thesis .
      qed
      thus "std.basis ` std.idxs \<subseteq> mero_uhp.span (basis ` idxs)"
        by blast
    qed
    finally show "MForms[k] \<subseteq> mero_uhp.span (basis ` idxs)" .
  qed

  have "mero_uhp.dim (basis ` idxs) = mero_uhp.dim (mero_uhp.span (basis ` idxs))"
    by (rule mero_uhp.dim_span [symmetric])
  also have "mero_uhp.span (basis ` idxs) = MForms[k]"
    by (simp add: span)
  also have "mero_uhp.dim \<dots> = d"
    unfolding d_def by (rule std.dim_eq)
  finally have dim: "mero_uhp.dim (basis ` idxs) = d" .

  have card: "card idxs = d"
    unfolding d_def card_idxs ..

  show inj: "inj_on basis idxs"
  proof (rule eq_card_imp_inj_on)
    have "card idxs = mero_uhp.dim (basis ` idxs)"
      using card dim by simp
    also have "mero_uhp.dim (basis ` idxs) \<le> card (basis ` idxs)"
      by (rule mero_uhp.dim_le_card') auto
    finally have "card idxs \<le> card (basis ` idxs)" .
    moreover have "card (basis ` idxs) \<le> card idxs"
      by (rule card_image_le) auto
    ultimately show "card (basis ` idxs) = card idxs"
      by linarith
  qed auto

  have "mero_uhp.dim (basis ` idxs) = card (basis ` idxs)"
    using card dim inj by (simp add: card_image)
  thus "mero_uhp.independent (basis ` idxs)"
    by (intro mero_uhp.dim_ge_card_imp_independent) auto
qed

end



subsection \<open>A basis for cusp forms\<close>

context modular_forms_UNIV_std_basis
begin

sublocale cusp: vector_space_independent_family "\<lambda>c f. \<langle>c\<rangle> * f" basis "idxs - {0}"
  by (rule independent_family_subset) auto

sublocale cusp: vector_space_indexed_basis "\<lambda>c f. \<langle>c\<rangle> * f" basis "idxs - {0}" "CForms[k]"
proof
  have "span (basis ` (idxs - {0})) \<subseteq> CForms[k]"
  proof (rule span_minimal)
    have "basis i \<in> CForms[k]" if i: "i \<in> idxs - {0}" for i
    proof (cases i)
      case (Suc j)
      have "basis i = \<E> (nat k - (12 + 12 * j)) * \<Delta> ^ j * \<Delta>"
        by (simp add: basis_def Suc)
      also have "\<dots> \<in> CForms[k]"
      proof (rule CForms_mult_right)
        show "\<E> (nat k - (12 + 12 * j)) * \<Delta> ^ j \<in> MForms[k - 12]"
          using i by (auto intro!: mform_intros simp: Suc idxs_def)
        show "\<Delta> \<in> CForms[12]"
          by (rule mform_intros)
      qed auto
      finally show "basis i \<in> CForms[k]" .
    qed (use i in auto)
    thus "basis ` (idxs - {0}) \<subseteq> CForms[k]"
      by blast
  qed (use subspace_CForms in auto)

  moreover have "CForms[k] \<subseteq> span (basis ` (idxs - {0}))"
  proof (cases "k < 12 \<or> k = 14")
    case True
    hence "CForms[k] = {0}"
      using CForms_eq_0 by blast
    also have "\<dots> \<subseteq> span (basis ` (idxs - {0}))"
      by (auto intro: span_zero)
    finally show "CForms[k] \<subseteq> span (basis ` (idxs - {0}))" .
  next
    case k: False
    show ?thesis
    proof
      fix f assume f: "f \<in> CForms[k]"
      then obtain g where g: "g \<in> MForms[k - 12]" "f = g * \<Delta>"
        using CForms_split[of f k] by blast
      interpret new: modular_forms_UNIV_std_basis "k - 12"
        by standard (use k even_weight in auto)
      obtain c where c: "g = (\<Sum>y\<in>new.idxs. \<langle>c y\<rangle> * new.basis y)"
        using new.indexed_basis_imp_representation_finite[of g] g(1) new.finite_idxs by blast
      define c' where "c' = (\<lambda>i. if i = 0 then 0 else c (i - 1))"

      have "f = g * \<Delta>"
        by fact
      also have "\<dots> = (\<Sum>y\<in>new.idxs. \<langle>c y\<rangle> * new.basis y * \<Delta>)"
        unfolding c sum_distrib_right by simp
      also have "\<dots> = (\<Sum>y\<in>idxs - {0}. \<langle>c' y\<rangle> * basis y)"
        by (rule sum.reindex_bij_witness[of _ "\<lambda>i. i - 1" "\<lambda>i. i + 1"]) 
           (auto simp: new.idxs_def idxs_def c'_def basis_def new.basis_def nat_diff_distrib)
      also have "\<dots> \<in> span (basis ` (idxs - {0}))"
        by (intro span_sum span_scale) (auto intro: span_base)
      finally show "f \<in> local.span (basis ` (idxs \<setminus> {0}))" .
    qed
  qed

  ultimately show "span (basis ` (idxs \<setminus> {0})) = CForms[k]"
    by blast
qed

lemma dim_CForms_eq:
  "mero_uhp.dim CForms[k] = mero_uhp.dim MForms[k] - 1"
proof -
  have "mero_uhp.dim CForms[k] = card (idxs - {0})"
    by (rule cusp.indexed_basis_imp_dim) auto
  also have "\<dots> = card idxs - 1"
  proof (cases "k = 2")
    case True
    have "idxs = {}"
      unfolding idxs_def by (auto simp: True)
    thus ?thesis
      by simp
  next
    case False
    thus ?thesis
      by (subst card_Diff_subset) (use nonneg_weight in \<open>auto simp: idxs_def\<close>)
  qed
  finally show ?thesis using indexed_basis_imp_dim finite_idxs
    by simp
qed

end


text \<open>
  The dimension of cusp forms is one less than that of modular forms. Note due to behaviour
  of Isabelle's subtraction on natural numbers, there is a subtlety hidden here: when the dimension
  of modular forms is already 0 (i.e.\ for $k$ odd, $k < 0$, or $k = 2$), the dimension of cusp
  forms is of course also 0.
\<close>
theorem dim_CForms_UNIV:
  "mero_uhp.dim CForms[k] = mero_uhp.dim MForms[k] - 1"
proof (cases "even k \<and> k \<ge> 0")
  case True
  then interpret modular_forms_UNIV_std_basis k
    by unfold_locales auto
  show ?thesis
    using dim_CForms_eq by blast
next
  case False
  thus ?thesis
    by (auto simp: CForms_eq_0 MForms_eq_0)
qed


subsection \<open>Connection to Dedekind's $\eta$ function\<close>

text \<open>
  We already have the transformation laws for Dedekind's eta function, namely
  $\eta(z+1) = e^{i\pi/12}\eta(z)$ and $\eta(-1/z) = \sqrt{-iz}\eta(z)$. This corresponds to
  a kind of ``weight $\frac{1}{2}$'' transformation, including a 24-th root of unity.

  Raising $\eta$ to the 24-th power clears these roots of unity, giving us a modular form of
  weight 12. The Fourier expansion of $\eta^{24}$ is, by definition, $q\varphi(q)^{24}$, where
  $\varphi$ denotes the Euler function. This means that $\eta^{24}$ is a cusp form.

  Since all the space of cusp forms of weight 12 is one-dimensional, there must be some constant 
  $c$ such that $\eta^{24} = c\Delta$. This constant can easily be determined to be 
  $c = (2\pi)^{-12}$ by comparing the coefficients of the $q^1$ term in the Fourier expansions
  of $\eta^{24}$ and $\Delta$.
\<close>
theorem modular_discr_conv_dedekind_eta:
  assumes "Im z > 0"
  shows   "modular_discr z = (2 * pi) ^ 12 * dedekind_eta z ^ 24"
proof -
  define F where "F = (fps_X * fps_euler_phi ^ 24 :: complex fps)"
  define f where "f = mero_uhp (\<lambda>z. dedekind_eta z ^ 24)"
  have [mero_uhp_rel_intros]: "mero_uhp_rel f (\<lambda>z. dedekind_eta z ^ 24)" unfolding f_def
    by (rule mero_uhp_rel_mero_uhp) (auto intro!: analytic_on_imp_meromorphic_on analytic_intros)
  have eval_f: "eval_mero_uhp f z = dedekind_eta z ^ 24" if "Im z > 0" for z
    unfolding f_def using that
    by (intro eval_mero_uhp_mero_uhp) (auto intro!: analytic_on_imp_meromorphic_on analytic_intros)

  interpret f: weakly_meromorphic_form f 12 UNIV
    rewrites "cusp_width\<^sub>\<infinity> UNIV = Suc 0"
  proof (rule weakly_meromorphic_formI_generators)
    show "mero_uhp_rel (eval_mero_uhp f) (\<lambda>z. dedekind_eta z ^ 24)"
      by mero_uhp_rel
  next
    fix z assume z: "Im z > 0"
    from z show "dedekind_eta (z + 1) ^ 24 = dedekind_eta z ^ 24"
      by (simp add: dedekind_eta_plus1 power_mult_distrib Complex.DeMoivre)
    from z show "dedekind_eta (- (1 / z)) ^ 24 = z powi 12 * dedekind_eta z ^ 24"
      by (subst dedekind_eta_minus_one_over) (auto simp: power_mult_distrib csqrt_power_even)
  qed auto

  interpret f: fourier_expansion_holomorphic_explicit "Suc 0" f F
    rewrites "cusp_width\<^sub>\<infinity> UNIV = Suc 0"
  proof unfold_locales
    have "mero_uhp_rel f (\<lambda>z. dedekind_eta z ^ 24)"
      by mero_uhp_rel
    thus "holo_uhp f"
      by (rule holo_uhp_mero_uhp_rel_transfer) (auto intro!: analytic_intros)
  next
    have "(\<lambda>q. q * euler_phi q ^ 24) has_laurent_expansion fps_to_fls F"
      unfolding F_def by (intro has_laurent_expansion_fps fps_expansion_intros)
    also have "\<forall>\<^sub>F z in at_\<i>\<infinity>. to_q (Suc 0) z * euler_phi (to_q (Suc 0) z) ^ 24 = 
                                fourier_expansion (Suc 0) f (to_q (Suc 0) z)"
      using eventually_at_ii_inf[of 0]
    proof eventually_elim
      case (elim z)
      from elim have "fourier_expansion (Suc 0) f (to_q (Suc 0) z) = 
                        to_nome (2 * z) * euler_phi (to_nome (2 * z)) ^ 24 "
        by (simp add: eval_f dedekind_eta_def power_mult_distrib to_nome_power)
      also have "to_nome (2 * z) = to_q 1 z"
        by (simp add: to_q_conv_to_nome)
      finally show ?case by simp
    qed
    hence "eventually (\<lambda>q. q * euler_phi q ^ 24 = fourier_expansion (Suc 0) f q) (at 0)"
      by (subst eventually_at_ii_inf_to_q[of 1]) simp_all
    hence "(\<lambda>q. q * euler_phi q ^ 24) has_laurent_expansion fps_to_fls F \<longleftrightarrow>
           fourier_expansion (Suc 0) f has_laurent_expansion fps_to_fls F"
      by (rule has_laurent_expansion_cong) auto
    finally show "f has_laurent_expansion_at_\<i>\<infinity> fps_to_fls F"
      using f.fourier_expansion_locale_axioms has_laurent_expansion_at_ii_inf_def by blast
  qed auto

  interpret f: cusp_form f 12 UNIV
    rewrites "cusp_width\<^sub>\<infinity> UNIV = Suc 0"
  proof unfold_locales
    have "eval_mero_uhp_at_ii_inf f = 0"
      using f.eval_mero_uhp_at_ii_inf_eq by (simp add: F_def)
    thus "eval_mero_uhp_at_ii_inf (slash_mero_uhp 12 h f) = 0" for h
      by (simp add: f.invariant_slash_modgrp)
  qed (use f.holo_uhp f.holomorphic_at_infinity_explicit in \<open>simp_all add: f.invariant_slash_modgrp\<close>)

  have "f \<in> CForms[12]"
    using f.cusp_form_axioms by (auto simp: CForms_def)
  then obtain c where c: "f = \<langle>c\<rangle> * \<Delta>"
    using CForms_12 by blast

  have "f - \<langle>c\<rangle> * \<Delta> has_fps_expansion_at_\<i>\<infinity> F - fps_const c * fps_modular_discr"
    by (intro fps_expansion_intros f.has_fps_expansion_at_ii_inf_explicit) auto
  also have "f - \<langle>c\<rangle> * \<Delta> = 0"
    by (simp add: c)
  finally have "F - fps_const c * fps_modular_discr = 0"
    using has_fps_expansion_at_ii_inf_unique has_fps_expansion_at_ii_inf_0 by blast
  hence "0 = fps_nth (F - fps_const c * fps_modular_discr) 1"
    by simp
  also have "\<dots> = 1 - c * (4096 * of_real pi ^ 12)"
    by (simp add: F_def fps_modular_discr_def fps_nth_power_0)
  finally have c_eq: "c = 1 / (2 * of_real pi) ^ 12"
    by (simp add: field_simps)

  have "dedekind_eta z ^ 24 = eval_mero_uhp f z"
    using assms by (simp add: eval_f)
  also have "\<dots> = modular_discr z / (2 * of_real pi) ^ 12"
    unfolding c c_eq using assms by simp
  finally show ?thesis
    by (simp add: field_simps)
qed 

end