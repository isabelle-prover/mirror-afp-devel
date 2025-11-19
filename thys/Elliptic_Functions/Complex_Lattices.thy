section \<open>Complex lattices\<close>
theory Complex_Lattices
  imports "HOL-Complex_Analysis.Complex_Analysis" Parallelogram_Paths
begin

(* TODO Move *)
lemmas [simp del] = div_mult_self1 div_mult_self2 div_mult_self3 div_mult_self4


subsection \<open>Basic definitions and useful lemmas\<close>

text \<open>
  We define a complex lattice with two generators $\omega_1, \omega_2\in\mathbb{C}$ as the set
  $\Lambda(\omega_1, \omega_2) = \omega_1\mathbb{Z} + \omega_2\mathbb{Z}$.
  For now, we make no restrictions on the generators, but for most of our results we will require
  that they be independent (i.e.\ neither is a multiple of the other, or, in terms of complex
  numbers, their quotient is not real).
\<close>
locale pre_complex_lattice =
  fixes \<omega>1 \<omega>2 :: complex
begin

text \<open>
  The following function convergs from lattice coordinates into cartesian coordinates.
\<close>
definition of_\<omega>12_coords :: "real \<times> real \<Rightarrow> complex" where
  "of_\<omega>12_coords = (\<lambda>(x,y). of_real x * \<omega>1 + of_real y * \<omega>2)"

sublocale of_\<omega>12_coords: linear of_\<omega>12_coords
  unfolding of_\<omega>12_coords_def by (auto simp: linear_iff algebra_simps scaleR_conv_of_real)

sublocale of_\<omega>12_coords: bounded_linear of_\<omega>12_coords
  using of_\<omega>12_coords.linear_axioms linear_conv_bounded_linear by auto

lemmas [continuous_intros] = of_\<omega>12_coords.continuous_on of_\<omega>12_coords.continuous
lemmas [tendsto_intros] = of_\<omega>12_coords.tendsto

lemmas [simp] = of_\<omega>12_coords.add of_\<omega>12_coords.diff of_\<omega>12_coords.neg of_\<omega>12_coords.scaleR

lemma of_\<omega>12_coords_fst [simp]: "of_\<omega>12_coords (a, 0) = of_real a * \<omega>1"
  and of_\<omega>12_coords_snd [simp]: "of_\<omega>12_coords (0, a) = of_real a * \<omega>2"
  and of_\<omega>12_coords_scaleR': "of_\<omega>12_coords (c *\<^sub>R z) = of_real c * of_\<omega>12_coords z"
  by (simp_all add: of_\<omega>12_coords_def algebra_simps case_prod_unfold 
                    scaleR_prod_def scaleR_conv_of_real)

text \<open>
  The following is our lattice as a set of lattice points.
\<close>
definition lattice :: "complex set" ("\<Lambda>") where
  "lattice = of_\<omega>12_coords ` (\<int> \<times> \<int>)"

definition lattice0 :: "complex set" ("\<Lambda>\<^sup>*") where
  "lattice0 = lattice - {0}"

lemma countable_lattice [intro]: "countable lattice"
  unfolding lattice_def by (intro countable_image countable_SIGMA countable_int)

lemma latticeI: "of_\<omega>12_coords (x, y) = z \<Longrightarrow> x \<in> \<int> \<Longrightarrow> y \<in> \<int> \<Longrightarrow> z \<in> \<Lambda>"
  by (auto simp: lattice_def)

lemma latticeE:
  assumes "z \<in> \<Lambda>"
  obtains x y where "z = of_\<omega>12_coords (of_int x, of_int y)"
  using assms unfolding lattice_def Ints_def by auto

lemma lattice0I [intro]: "z \<in> \<Lambda> \<Longrightarrow> z \<noteq> 0 \<Longrightarrow> z \<in> \<Lambda>\<^sup>*"
  by (auto simp: lattice0_def)

lemma lattice0E [elim]: "\<And>P. z \<in> \<Lambda>\<^sup>* \<Longrightarrow> (z \<in> \<Lambda> \<Longrightarrow> z \<noteq> 0 \<Longrightarrow> P) \<Longrightarrow> P"
  by (auto simp: lattice0_def)

lemma in_lattice0_iff: "z \<in> \<Lambda>\<^sup>* \<longleftrightarrow> z \<in> \<Lambda> \<and> z \<noteq> 0"
  by (auto simp: lattice0_def)


named_theorems lattice_intros

lemma zero_in_lattice [lattice_intros, simp]: "0 \<in> lattice"
  by (rule latticeI[of 0 0]) (auto simp: of_\<omega>12_coords_def)

lemma generator_in_lattice [lattice_intros, simp]: "\<omega>1 \<in> lattice" "\<omega>2 \<in> lattice"
  by (auto intro: latticeI[of 0 1] latticeI[of 1 0] simp: of_\<omega>12_coords_def)

lemma uminus_in_lattice [lattice_intros]: "z \<in> \<Lambda> \<Longrightarrow> -z \<in> \<Lambda>"
proof -
  assume "z \<in> \<Lambda>"
  then obtain x y where "z = of_\<omega>12_coords (of_int x, of_int y)"
    by (elim latticeE)
  thus ?thesis
    by (intro latticeI[of "-x" "-y"]) (auto simp: of_\<omega>12_coords_def)
qed

lemma uminus_in_lattice_iff: "-z \<in> \<Lambda> \<longleftrightarrow> z \<in> \<Lambda>"
  using uminus_in_lattice minus_minus by metis

lemma uminus_in_lattice0_iff: "-z \<in> \<Lambda>\<^sup>* \<longleftrightarrow> z \<in> \<Lambda>\<^sup>*"
  by (auto simp: lattice0_def uminus_in_lattice_iff)

lemma add_in_lattice [lattice_intros]: "z \<in> \<Lambda> \<Longrightarrow> w \<in> \<Lambda> \<Longrightarrow> z + w \<in> \<Lambda>"
proof -
  assume "z \<in> \<Lambda>" "w \<in> \<Lambda>"
  then obtain a b c d
    where "z = of_\<omega>12_coords (of_int a, of_int b)" "w = of_\<omega>12_coords (of_int c, of_int d)"
    by (elim latticeE)
  thus ?thesis
    by (intro latticeI[of "a + c" "b + d"]) (auto simp: of_\<omega>12_coords_def algebra_simps)
qed

lemma lattice_lattice0: "\<Lambda> = insert 0 \<Lambda>\<^sup>*"
  by (auto simp: lattice0_def)

lemma mult_of_nat_left_in_lattice [lattice_intros]: "z \<in> \<Lambda> \<Longrightarrow> of_nat n * z \<in> \<Lambda>"
  by (induction n) (auto intro!: lattice_intros simp: ring_distribs)

lemma mult_of_nat_right_in_lattice [lattice_intros]: "z \<in> \<Lambda> \<Longrightarrow> z * of_nat n \<in> \<Lambda>"
  using mult_of_nat_left_in_lattice[of z n] by (simp add: mult.commute)

lemma mult_of_int_left_in_lattice [lattice_intros]: "z \<in> \<Lambda> \<Longrightarrow> of_int n * z \<in> \<Lambda>"
  using mult_of_nat_left_in_lattice[of z "nat n"]
        uminus_in_lattice[OF mult_of_nat_left_in_lattice[of z "nat (-n)"]]
  by (cases "n \<ge> 0") auto

lemma mult_of_int_right_in_lattice [lattice_intros]: "z \<in> \<Lambda> \<Longrightarrow> z * of_int n \<in> \<Lambda>"
  using mult_of_int_left_in_lattice[of z n] by (simp add: mult.commute)

lemma diff_in_lattice [lattice_intros]: "z \<in> \<Lambda> \<Longrightarrow> w \<in> \<Lambda> \<Longrightarrow> z - w \<in> \<Lambda>"
  using add_in_lattice[OF _ uminus_in_lattice, of z w] by simp

lemma diff_in_lattice_commute: "z - w \<in> \<Lambda> \<longleftrightarrow> w - z \<in> \<Lambda>"
  using uminus_in_lattice_iff[of "z - w"] by simp

lemma of_\<omega>12_coords_in_lattice [lattice_intros]: "ab \<in> \<int> \<times> \<int> \<Longrightarrow> of_\<omega>12_coords ab \<in> \<Lambda>"
  unfolding lattice_def by auto

lemma lattice_plus_right_cancel [simp]: "y \<in> \<Lambda> \<Longrightarrow> x + y \<in> \<Lambda> \<longleftrightarrow> x \<in> \<Lambda>"
  by (metis add_diff_cancel_right' add_in_lattice diff_in_lattice)

lemma lattice_plus_left_cancel [simp]: "x \<in> \<Lambda> \<Longrightarrow> x + y \<in> \<Lambda> \<longleftrightarrow> y \<in> \<Lambda>"
  by (metis add.commute lattice_plus_right_cancel)

lemma lattice_induct [consumes 1, case_names zero gen1 gen2 add uminus]:
  assumes "z \<in> \<Lambda>"
  assumes zero: "P 0" 
  assumes gens: "P \<omega>1" "P \<omega>2" 
  assumes plus: "\<And>w z. P w \<Longrightarrow> P z \<Longrightarrow> P (w + z)" 
  assumes uminus: "\<And>w. P w \<Longrightarrow> P (-w)"
  shows   "P z"
proof -
  from assms(1) obtain a b where z_eq: "z = of_\<omega>12_coords (of_int a, of_int b)"
    by (elim latticeE)
  have nat1: "P (of_\<omega>12_coords (of_nat n, 0))" for n
    by (induction n) (auto simp: of_\<omega>12_coords_def ring_distribs intro: zero plus gens)
  have int1: "P (of_\<omega>12_coords (of_int n, 0))" for n
    using nat1[of "nat n"] uminus[OF nat1[of "nat (-n)"]]
    by (cases "n \<ge> 0") (auto simp: of_\<omega>12_coords_def)
  have nat2: "P (of_\<omega>12_coords (of_int a, of_nat n))" for a n
  proof (induction n)
    case 0
    thus ?case
      using int1[of a] by simp
  next
    case (Suc n)
    from plus[OF Suc gens(2)] show ?case
      by (simp add: of_\<omega>12_coords_def algebra_simps)
  qed
  have int2: "P (of_\<omega>12_coords (of_int a, of_int b))" for a b
    using nat2[of a "nat b"] uminus[OF nat2[of "-a" "nat (-b)"]]
    by (cases "b \<ge> 0") (auto simp: of_\<omega>12_coords_def)
  from this[of a b] and z_eq show ?thesis
    by simp
qed


text \<open>
  The following equivalence relation equates two points if they differ by a lattice point.
\<close>
definition rel :: "complex \<Rightarrow> complex \<Rightarrow> bool" where
  "rel x y \<longleftrightarrow> (x - y) \<in> \<Lambda>"

lemma rel_refl [simp, intro]: "rel x x"
  by (auto simp: rel_def)

lemma relE: 
  assumes "rel x y"
  obtains z where "z \<in> \<Lambda>" "y = x + z"
  using assms unfolding rel_def using pre_complex_lattice.uminus_in_lattice by force

lemma rel_symI: "rel x y \<Longrightarrow> rel y x"
  by (auto simp: rel_def diff_in_lattice_commute)

lemma rel_sym: "rel x y \<longleftrightarrow> rel y x"
  by (auto simp: rel_def diff_in_lattice_commute)

lemma rel_0_right_iff: "rel x 0 \<longleftrightarrow> x \<in> \<Lambda>"
  by (simp add: rel_def)

lemma rel_0_left_iff: "rel 0 x \<longleftrightarrow> x \<in> \<Lambda>"
  by (simp add: rel_def uminus_in_lattice_iff)

lemma rel_trans [trans]: "rel x y \<Longrightarrow> rel y z \<Longrightarrow> rel x z"
  using add_in_lattice rel_def by fastforce

lemma rel_minus [lattice_intros]: "rel a b \<Longrightarrow> rel (-a) (-b)"
  unfolding rel_def by (simp add: diff_in_lattice_commute)

lemma rel_minus_iff: "rel (-a) (-b) \<longleftrightarrow> rel a b"
  by (auto simp: rel_def diff_in_lattice_commute)

lemma rel_add [lattice_intros]: "rel a b \<Longrightarrow> rel c d \<Longrightarrow> rel (a + c) (b + d)"
  unfolding rel_def by (simp add: add_diff_add add_in_lattice)

lemma rel_diff [lattice_intros]: "rel a b \<Longrightarrow> rel c d \<Longrightarrow> rel (a - c) (b - d)"
  by (metis rel_add rel_minus uminus_add_conv_diff)

lemma rel_mult_of_nat_left [lattice_intros]: "rel a b \<Longrightarrow> rel (of_nat n * a) (of_nat n * b)"
  by (induction n) (auto intro!: lattice_intros simp: ring_distribs)

lemma rel_mult_of_nat_right [lattice_intros]: "rel a b \<Longrightarrow> rel (a * of_nat n) (b * of_nat n)"
  by (induction n) (auto intro!: lattice_intros simp: ring_distribs)

lemma rel_mult_of_int_left [lattice_intros]: "rel a b \<Longrightarrow> rel (of_int n * a) (of_int n * b)"
  by (induction n) (auto intro!: lattice_intros simp: ring_distribs)

lemma rel_mult_of_int_right [lattice_intros]: "rel a b \<Longrightarrow> rel (a * of_int n) (b * of_int n)"
  by (induction n) (auto intro!: lattice_intros simp: ring_distribs)

lemma rel_sum [lattice_intros]:
  "(\<And>i. i \<in> A \<Longrightarrow> rel (f i) (g i)) \<Longrightarrow> rel (\<Sum>i\<in>A. f i) (\<Sum>i\<in>A. g i)"
  by (induction A rule: infinite_finite_induct) (auto intro!: lattice_intros)

lemma rel_sum_list [lattice_intros]:
  "list_all2 rel xs ys \<Longrightarrow> rel (sum_list xs) (sum_list ys)"
  by (induction rule: list_all2_induct) (auto intro!: lattice_intros)

lemma rel_lattice_trans_left [trans]: "x \<in> \<Lambda> \<Longrightarrow> rel x y \<Longrightarrow> y \<in> \<Lambda>"
  using rel_0_left_iff rel_trans by blast

lemma rel_lattice_trans_right [trans]: "rel x y \<Longrightarrow> y \<in> \<Lambda> \<Longrightarrow> x \<in> \<Lambda>"
  using rel_lattice_trans_left rel_sym by blast

end



text \<open>
  Exchanging the two generators clearly does not change the underlying lattice.
\<close>

locale pre_complex_lattice_swap = pre_complex_lattice
begin

sublocale swap: pre_complex_lattice \<omega>2 \<omega>1 .

lemma swap_of_\<omega>12_coords [simp]: "swap.of_\<omega>12_coords = of_\<omega>12_coords \<circ> prod.swap"
  by (auto simp: fun_eq_iff swap.of_\<omega>12_coords_def of_\<omega>12_coords_def add_ac)

lemma swap_lattice [simp]: "swap.lattice = lattice"
  unfolding swap.lattice_def lattice_def swap_of_\<omega>12_coords image_comp [symmetric] product_swap ..

lemma swap_lattice0 [simp]: "swap.lattice0 = lattice0"
  unfolding swap.lattice0_def lattice0_def swap_lattice ..

lemma swap_rel [simp]: "swap.rel = rel"
  unfolding swap.rel_def rel_def swap_lattice ..

end




text \<open>
  A pair \<open>(\<omega>\<^sub>1, \<omega>\<^sub>2)\<close> of complex numbers with \<open>\<omega>\<^sub>2 / \<omega>\<^sub>1 \<notin> \<real>\<close> is called a \<^emph>\<open>fundamental pair\<close>.
  Two such pairs are called \<^emph>\<open>equivalent\<close> if
\<close>
definition fundpair :: "complex \<times> complex \<Rightarrow> bool" where
  "fundpair = (\<lambda>(a, b). b / a \<notin> \<real>)"

lemma fundpair_swap: "fundpair ab \<longleftrightarrow> fundpair (prod.swap ab)"
  unfolding fundpair_def prod.swap_def case_prod_unfold fst_conv snd_conv
  by (metis Un_insert_right collinear_iff_Reals insert_is_Un)

lemma fundpair_cnj_iff [simp]: "fundpair (cnj a, cnj b) = fundpair (a, b)"
  by (auto simp: fundpair_def complex_is_Real_iff simp flip: complex_cnj_divide)

lemma fundpair_altdef: "fundpair = (\<lambda>(a,b). a / b \<notin> \<real>)"
proof
  fix ab :: "complex \<times> complex"
  show "fundpair ab = (case ab of (a, b) \<Rightarrow> a / b \<notin> \<real>)"
    using fundpair_swap[of ab] by (auto simp: fundpair_def)
qed

lemma
  assumes "fundpair (a, b)"
  shows   fundpair_imp_nonzero [dest]: "a \<noteq> 0" "b \<noteq> 0"
  and     fundpair_imp_neq: "a \<noteq> b" "b \<noteq> a"
  using assms unfolding fundpair_def by (auto split: if_splits)

lemma fundpair_imp_independent:
  assumes "fundpair (\<omega>1, \<omega>2)"
  shows   "independent {\<omega>1, \<omega>2}"
proof
  assume "dependent {\<omega>1, \<omega>2}"
  then obtain a b where ab: "a *\<^sub>R \<omega>1 + b *\<^sub>R \<omega>2 = 0" and "a \<noteq> 0 \<or> b \<noteq> 0"
    by (subst (asm) real_vector.dependent_finite) (use assms in \<open>auto dest: fundpair_imp_neq\<close>)
  with assms have [simp]: "a \<noteq> 0" "b \<noteq> 0"
    by auto
  from ab have "\<omega>2 / \<omega>1 = of_real (-a / b)"
    using assms by (auto simp: field_simps scaleR_conv_of_real add_eq_0_iff)
  also have "\<dots> \<in> \<real>"
    by simp
  finally show False
    using assms by (auto simp: fundpair_def)
qed

lemma fundpair_imp_basis:
  assumes "fundpair (\<omega>1, \<omega>2)"
  shows   "span {\<omega>1, \<omega>2} = UNIV"
proof -
  have "dim (span {\<omega>1, \<omega>2}) = card {\<omega>1, \<omega>2}"
    using fundpair_imp_independent[OF assms] by (rule dim_span_eq_card_independent)
  hence "dim (span {\<omega>1, \<omega>2}) = DIM(complex)"
    using fundpair_imp_neq(1)[OF assms] by simp
  thus ?thesis
    using dim_eq_full span_span by blast
qed

text \<open>
  We now introduce the assumption that the generators be independent. This makes 
  $\{\omega_1,\omega_2\}$ a basis of $\mathbb{C}$ (in the sense of an $\mathbb{R}$-vector space),
  and we define a few functions to help us convert between these two views.
\<close>
locale complex_lattice = pre_complex_lattice +
  assumes fundpair: "fundpair (\<omega>1, \<omega>2)"
begin

lemma \<omega>1_neq_\<omega>2 [simp]: "\<omega>1 \<noteq> \<omega>2" and \<omega>2_neq_\<omega>1 [simp]: "\<omega>2 \<noteq> \<omega>1"
  using fundpair fundpair_imp_neq by blast+

lemma \<omega>1_nonzero [simp]: "\<omega>1 \<noteq> 0" and \<omega>2_nonzero [simp]: "\<omega>2 \<noteq> 0"
  using fundpair by auto

lemma lattice0_nonempty [simp]: "lattice0 \<noteq> {}"
proof -
  have "\<omega>1 \<in> lattice0"
    by auto
  thus ?thesis
    by blast
qed

lemma \<omega>12_independent': "independent {\<omega>1, \<omega>2}"
  using fundpair by (rule fundpair_imp_independent)

lemma span_\<omega>12: "span {\<omega>1, \<omega>2} = UNIV"
  using fundpair by (rule fundpair_imp_basis)

text \<open>
  The following converts complex numbers into lattice coordinates, i.e.\ as a linear
  combination of the two generators.
\<close>
definition \<omega>1_coord :: "complex \<Rightarrow> real" where
  "\<omega>1_coord z = representation {\<omega>1, \<omega>2} z \<omega>1"

definition \<omega>2_coord :: "complex \<Rightarrow> real" where
  "\<omega>2_coord z = representation {\<omega>1, \<omega>2} z \<omega>2"

definition \<omega>12_coords :: "complex \<Rightarrow> real \<times> real" where
  "\<omega>12_coords z = (\<omega>1_coord z, \<omega>2_coord z)"

sublocale \<omega>1_coord: bounded_linear \<omega>1_coord
  unfolding \<omega>1_coord_def using \<omega>12_independent' span_\<omega>12
  by (rule bounded_linear_representation)

sublocale \<omega>2_coord: bounded_linear \<omega>2_coord
  unfolding \<omega>2_coord_def using \<omega>12_independent' span_\<omega>12
  by (rule bounded_linear_representation)

sublocale \<omega>12_coords: linear \<omega>12_coords
  unfolding \<omega>12_coords_def
  by (auto simp: linear_iff \<omega>1_coord.add \<omega>2_coord.add \<omega>1_coord.scaleR \<omega>2_coord.scaleR)

sublocale \<omega>12_coords: bounded_linear \<omega>12_coords
  using \<omega>12_coords.linear_axioms linear_conv_bounded_linear by auto

lemmas [continuous_intros] = 
  \<omega>1_coord.continuous_on \<omega>1_coord.continuous
  \<omega>2_coord.continuous_on \<omega>2_coord.continuous
  \<omega>12_coords.continuous_on \<omega>12_coords.continuous

lemmas [tendsto_intros] = \<omega>1_coord.tendsto \<omega>2_coord.tendsto \<omega>12_coords.tendsto

lemma \<omega>1_coord_\<omega>1 [simp]: "\<omega>1_coord \<omega>1 = 1"
  and \<omega>1_coord_\<omega>2 [simp]: "\<omega>1_coord \<omega>2 = 0"
  and \<omega>2_coord_\<omega>1 [simp]: "\<omega>2_coord \<omega>1 = 0"
  and \<omega>2_coord_\<omega>2 [simp]: "\<omega>2_coord \<omega>2 = 1"
  unfolding \<omega>1_coord_def \<omega>2_coord_def using \<omega>1_neq_\<omega>2
  by (simp_all add: \<omega>12_independent' representation_basis)

lemma \<omega>12_coords_\<omega>1 [simp]: "\<omega>12_coords \<omega>1 = (1, 0)"
  and \<omega>12_coords_\<omega>2 [simp]: "\<omega>12_coords \<omega>2 = (0, 1)"
  by (simp_all add: \<omega>12_coords_def)

lemma \<omega>12_coords_of_\<omega>12_coords [simp]: "\<omega>12_coords (of_\<omega>12_coords z) = z"
  by (simp add: of_\<omega>12_coords_def case_prod_unfold \<omega>12_coords.add \<omega>12_coords.scaleR
           flip: scaleR_conv_of_real)

lemma \<omega>1_coord_of_\<omega>12_coords [simp]: "\<omega>1_coord (of_\<omega>12_coords z) = fst z"
  and \<omega>2_coord_of_\<omega>12_coords [simp]: "\<omega>2_coord (of_\<omega>12_coords z) = snd z"
  using \<omega>12_coords_of_\<omega>12_coords[of z]
  by (auto simp del: \<omega>12_coords_of_\<omega>12_coords simp add: \<omega>12_coords_def prod_eq_iff)  

lemma of_\<omega>12_coords_\<omega>12_coords [simp]: "of_\<omega>12_coords (\<omega>12_coords z) = z"
proof -
  have "(\<Sum>b\<in>{\<omega>1, \<omega>2}. representation {\<omega>1, \<omega>2} z b *\<^sub>R b) = z"
    by (rule real_vector.sum_representation_eq) (use \<omega>12_independent' span_\<omega>12 in simp_all)
  thus ?thesis
    by (simp add: \<omega>12_coords_def of_\<omega>12_coords_def scaleR_conv_of_real
                  \<omega>1_coord_def \<omega>2_coord_def \<omega>1_neq_\<omega>2)
qed

lemma \<omega>12_coords_eqI:
  assumes "of_\<omega>12_coords a = b"
  shows   "\<omega>12_coords b = a"
  unfolding assms[symmetric] by auto

lemmas [simp] = \<omega>1_coord.scaleR \<omega>2_coord.scaleR \<omega>12_coords.scaleR

lemma \<omega>12_coords_times_\<omega>1 [simp]: "\<omega>12_coords (of_real a * \<omega>1) = (a, 0)"
  and \<omega>12_coords_times_\<omega>2 [simp]: "\<omega>12_coords (of_real a * \<omega>2) = (0, a)"
  and \<omega>12_coords_times_\<omega>1' [simp]: "\<omega>12_coords (\<omega>1 * of_real a) = (a, 0)"
  and \<omega>12_coords_times_\<omega>2' [simp]: "\<omega>12_coords (\<omega>2 * of_real a) = (0, a)"
  and \<omega>12_coords_mult_of_real [simp]: "\<omega>12_coords (of_real c * z) = c *\<^sub>R  \<omega>12_coords z"
  and \<omega>12_coords_mult_of_int [simp]: "\<omega>12_coords (of_int i * z) = of_int i *\<^sub>R  \<omega>12_coords z"
  and \<omega>12_coords_mult_of_nat [simp]: "\<omega>12_coords (of_nat n * z) = of_nat n *\<^sub>R  \<omega>12_coords z"
  and \<omega>12_coords_divide_of_real [simp]: "\<omega>12_coords (z / of_real c) = \<omega>12_coords z /\<^sub>R c"
  and \<omega>12_coords_mult_numeral [simp]: "\<omega>12_coords (numeral num * z) = numeral num *\<^sub>R  \<omega>12_coords z"
  and \<omega>12_coords_divide_numeral [simp]: "\<omega>12_coords (z / numeral num) = \<omega>12_coords z /\<^sub>R numeral num"
  by (rule \<omega>12_coords_eqI; simp add: scaleR_conv_of_real field_simps; fail)+

lemma of_\<omega>12_coords_eq_iff: "of_\<omega>12_coords z1 = of_\<omega>12_coords z2 \<longleftrightarrow> z1 = z2"
  using \<omega>12_coords_eqI by blast

lemma \<omega>12_coords_eq_iff: "\<omega>12_coords z1 = \<omega>12_coords z2 \<longleftrightarrow> z1 = z2"
  by (metis of_\<omega>12_coords_\<omega>12_coords)

lemma of_\<omega>12_coords_eq_0_iff [simp]: "of_\<omega>12_coords z = 0 \<longleftrightarrow> z = (0,0)"
  unfolding zero_prod_def [symmetric]
  by (metis \<omega>12_coords.zero \<omega>12_coords_eqI of_\<omega>12_coords_\<omega>12_coords)

lemma \<omega>12_coords_eq_0_0_iff [simp]: "\<omega>12_coords x = (0, 0) \<longleftrightarrow> x = 0"
  by (metis \<omega>12_coords.zero \<omega>12_coords_eq_iff zero_prod_def)

lemma bij_of_\<omega>12_coords: "bij of_\<omega>12_coords"
proof -
  have "\<exists>z'. z = of_\<omega>12_coords z'" for z
    by (rule exI[of _ "\<omega>12_coords z"]) auto
  hence "surj of_\<omega>12_coords"
    by blast
  thus ?thesis
    unfolding bij_def by (auto intro!: injI simp: of_\<omega>12_coords_eq_iff)
qed

lemma bij_betw_lattice: "bij_betw of_\<omega>12_coords (\<int> \<times> \<int>) lattice"
  unfolding lattice_def using bij_of_\<omega>12_coords unfolding bij_betw_def inj_on_def by blast

lemma bij_betw_lattice0: "bij_betw of_\<omega>12_coords (\<int> \<times> \<int> - {(0,0)}) lattice0"
  unfolding lattice0_def by (intro bij_betw_DiffI bij_betw_singletonI bij_betw_lattice) auto

lemma bij_betw_lattice': "bij_betw (of_\<omega>12_coords \<circ> map_prod of_int of_int) UNIV lattice"
  by (rule bij_betw_trans[OF _ bij_betw_lattice]) (auto simp: Ints_def bij_betw_def inj_on_def)

lemma bij_betw_lattice0': "bij_betw (of_\<omega>12_coords \<circ> map_prod of_int of_int) (-{(0,0)}) lattice0"
  by (rule bij_betw_trans[OF _ bij_betw_lattice0]) (auto simp: Ints_def bij_betw_def inj_on_def)

lemma infinite_lattice: "\<not>finite lattice"
proof -
  have "finite (UNIV :: (int \<times> int) set) \<longleftrightarrow> finite lattice"
    by (rule bij_betw_finite[OF bij_betw_lattice'])
  moreover have "\<not>finite (UNIV :: (int \<times> int) set)"
    by (simp add: finite_prod)
  ultimately show ?thesis
    by blast
qed

lemma \<omega>12_coords_image_eq: "\<omega>12_coords ` X = of_\<omega>12_coords -` X"
  using bij_of_\<omega>12_coords image_iff by fastforce

lemma of_\<omega>12_coords_image_eq: "of_\<omega>12_coords ` X = \<omega>12_coords -` X"
  by (metis UNIV_I \<omega>12_coords_eqI \<omega>12_coords_image_eq bij_betw_imp_surj_on
      bij_of_\<omega>12_coords rangeI subsetI subset_antisym surj_image_vimage_eq)

lemma of_\<omega>12_coords_linepath:
   "of_\<omega>12_coords (linepath a b x) = linepath (of_\<omega>12_coords a) (of_\<omega>12_coords b) x"
  by (simp add: linepath_def scaleR_prod_def scaleR_conv_of_real
                 of_\<omega>12_coords_def algebra_simps case_prod_unfold)

lemma of_\<omega>12_coords_linepath':
  "of_\<omega>12_coords o (linepath a b) =
      linepath (of_\<omega>12_coords a) (of_\<omega>12_coords b)"
  unfolding comp_def using of_\<omega>12_coords_linepath
  by auto

lemma \<omega>12_coords_linepath:
   "\<omega>12_coords (linepath a b x) = linepath (\<omega>12_coords a) (\<omega>12_coords b) x"
  by (rule \<omega>12_coords_eqI) (simp add: of_\<omega>12_coords_linepath)

lemma of_\<omega>12_coords_in_lattice_iff:
  "of_\<omega>12_coords z \<in> \<Lambda> \<longleftrightarrow> fst z \<in> \<int> \<and> snd z \<in> \<int>"
proof
  assume "of_\<omega>12_coords z \<in> \<Lambda>"
  then obtain m n where mn: "of_\<omega>12_coords z = of_\<omega>12_coords (of_int m, of_int n)"
    by (elim latticeE)
  hence "z = (of_int m, of_int n)"
    by (simp only: of_\<omega>12_coords_eq_iff)
  thus "fst z \<in> \<int> \<and> snd z \<in> \<int>"
    by auto
next
  assume "fst z \<in> \<int> \<and> snd z \<in> \<int>"
  thus "of_\<omega>12_coords z \<in> \<Lambda>"
    by (simp add: latticeI of_\<omega>12_coords_def split_def)
qed

lemma of_\<omega>12_coords_in_lattice [simp, intro]:
  "fst z \<in> \<int> \<Longrightarrow> snd z \<in> \<int> \<Longrightarrow> of_\<omega>12_coords z \<in> \<Lambda>"
  by (subst of_\<omega>12_coords_in_lattice_iff) auto

lemma in_lattice_conv_\<omega>12_coords: "z \<in> \<Lambda> \<longleftrightarrow> \<omega>12_coords z \<in> \<int> \<times> \<int>"
  using of_\<omega>12_coords_in_lattice_iff[of "\<omega>12_coords z"] by (auto simp: mem_Times_iff)

lemma \<omega>12_coords_in_Z_times_Z: "z \<in> \<Lambda> \<Longrightarrow> \<omega>12_coords z \<in> \<int> \<times> \<int>"
  by (subst (asm) in_lattice_conv_\<omega>12_coords) auto

lemma half_periods_notin_lattice [simp]:
  "\<omega>1 / 2 \<notin> \<Lambda>" "\<omega>2 / 2 \<notin> \<Lambda>" "(\<omega>1 + \<omega>2) / 2 \<notin> \<Lambda>"
  by (auto simp: in_lattice_conv_\<omega>12_coords \<omega>12_coords.add)

end


locale complex_lattice_swap = complex_lattice
begin

sublocale pre_complex_lattice_swap \<omega>1 \<omega>2 .

sublocale swap: complex_lattice \<omega>2 \<omega>1
proof
  show "fundpair (\<omega>2, \<omega>1)"
    using fundpair by (subst (asm) fundpair_swap) auto
qed

lemma swap_\<omega>12_coords [simp]: "swap.\<omega>12_coords = prod.swap \<circ> \<omega>12_coords"
  by (metis (no_types, lifting) ext comp_apply of_\<omega>12_coords_\<omega>12_coords
      pre_complex_lattice_swap.swap_of_\<omega>12_coords swap.\<omega>12_coords_eqI)

lemma swap_\<omega>1_coord [simp]: "swap.\<omega>1_coord = \<omega>2_coord"
  and swap_\<omega>2_coord [simp]: "swap.\<omega>2_coord = \<omega>1_coord"
  using swap_\<omega>12_coords unfolding swap.\<omega>12_coords_def[abs_def] \<omega>12_coords_def[abs_def]
  by (auto simp: fun_eq_iff)

end



subsection \<open>Period parallelograms\<close>

context pre_complex_lattice
begin

text \<open>
  The period parallelogram at a vertex \<open>z\<close> is the parallelogram with the vertices
  \<open>z\<close>, \<open>z + \<omega>\<^sub>1\<close>, \<open>z + \<omega>\<^sub>2\<close>, and \<open>z + \<omega>\<^sub>1 + \<omega>\<^sub>2\<close>. For convenience, we define the parallelogram to
  be contain only two of its four sides, so that one can obtain an exact covering of the complex
  plane with period parallelograms.

  We will occasionally need the full parallelogram with all four sides, or the interior of the
  parallelogram without its four sides, but these are easily obtained from this using the
  \<^const>\<open>closure\<close> and \<^const>\<open>interior\<close> operators, while the border itself (which is of interest
  for integration) is obtained with the \<^const>\<open>frontier\<close> operator.
\<close>
definition period_parallelogram :: "complex \<Rightarrow> complex set" where
  "period_parallelogram z = (+) z ` of_\<omega>12_coords ` ({0..<1} \<times> {0..<1})"

text \<open>
  The following is a path along the border of a period parallelogram, starting
  at the vertex \<open>z\<close> and going in direction \<open>\<omega>1\<close>.
\<close>
definition period_parallelogram_path :: "complex \<Rightarrow> real \<Rightarrow> complex" where
  "period_parallelogram_path z \<equiv> parallelogram_path z \<omega>1 \<omega>2"

lemma bounded_period_parallelogram [intro]: "bounded (period_parallelogram z)"
  unfolding period_parallelogram_def
  by (rule bounded_translation bounded_linear_image bounded_Times)+
     (auto intro: of_\<omega>12_coords.bounded_linear_axioms)

lemma convex_period_parallelogram [intro]:
  "convex (period_parallelogram z)"
  unfolding period_parallelogram_def
  by (intro convex_translation convex_linear_image of_\<omega>12_coords.linear_axioms convex_Times) auto

lemma closure_period_parallelogram:
  "closure (period_parallelogram z) = (+) z ` of_\<omega>12_coords ` (cbox (0,0) (1,1))"
proof -
  have "closure (period_parallelogram z) = (+) z ` closure (of_\<omega>12_coords ` ({0..<1} \<times> {0..<1}))"
    unfolding period_parallelogram_def by (subst closure_translation) auto
  also have "closure (of_\<omega>12_coords ` ({0..<1} \<times> {0..<1})) =
             of_\<omega>12_coords ` (closure ({0..<1} \<times> {0..<1}))"
    by (rule closure_bounded_linear_image [symmetric])
       (auto intro: bounded_Times of_\<omega>12_coords.linear_axioms)
  also have "closure ({0..<1::real} \<times> {0..<1::real}) = {0..1} \<times> {0..1}"
    by (simp add: closure_Times)
  also have "\<dots> = cbox (0,0) (1,1)"
    by auto
  finally show ?thesis .
qed

lemma compact_closure_period_parallelogram [intro]: "compact (closure (period_parallelogram z))"
  unfolding closure_period_parallelogram
  by (intro compact_translation compact_continuous_image continuous_intros compact_Times) auto

lemma vertex_in_period_parallelogram [simp, intro]: "z \<in> period_parallelogram z"
  unfolding period_parallelogram_def image_image
  by (rule image_eqI[of _ _ "(0,0)"]) auto
  
lemma nonempty_period_parallelogram: "period_parallelogram z \<noteq> {}"
  using vertex_in_period_parallelogram[of z] by blast

end


lemma (in pre_complex_lattice_swap) 
  swap_period_parallelogram [simp]: "swap.period_parallelogram = period_parallelogram"
  unfolding swap.period_parallelogram_def period_parallelogram_def swap_of_\<omega>12_coords
            image_comp [symmetric] product_swap ..


context complex_lattice
begin

lemma simple_path_parallelogram: "simple_path (parallelogram_path z \<omega>1 \<omega>2)"
  unfolding parallelogram_path_altdef
proof (rule simple_path_continuous_image)
  let ?h = "\<lambda>w. z + Re w *\<^sub>R \<omega>1 + Im w *\<^sub>R \<omega>2"
  show "simple_path (rectpath 0 (1 + \<i>))"
    by (intro simple_path_rectpath) auto
  show "continuous_on (path_image (rectpath 0 (1 + \<i>))) ?h"
    by (intro continuous_intros)
  show "inj_on ?h (path_image (rectpath 0 (1 + \<i>)))"
  proof
    fix x y assume "?h x = ?h y"
    hence "of_\<omega>12_coords (Re x, Im x) = of_\<omega>12_coords (Re y, Im y)"
      by (simp add: of_\<omega>12_coords_def scaleR_conv_of_real)
    thus "x = y"
      by (intro complex_eqI) (simp_all add: of_\<omega>12_coords_eq_iff)
  qed
qed

lemma (in -) image_plus_conv_vimage_plus:
  fixes c :: "'a :: group_add"
  shows "(+) c ` A = (+) (-c) -` A"
proof safe
  fix z assume "-c + z \<in> A"
  thus "z \<in> (+) c ` A"
    by (intro image_eqI[of _ _ "-c + z"]) (auto simp: algebra_simps)
qed auto

lemma period_parallelogram_altdef:
  "period_parallelogram z = {w. \<omega>12_coords (w - z) \<in> {0..<1} \<times> {0..<1}}"
  unfolding period_parallelogram_def of_\<omega>12_coords_image_eq image_plus_conv_vimage_plus
  by auto

lemma interior_period_parallelogram:
  "interior (period_parallelogram z) = (+) z ` of_\<omega>12_coords ` box (0,0) (1,1)"
proof -
  have bij: "bij of_\<omega>12_coords"
    by (simp add: bij_of_\<omega>12_coords)
  have "interior (period_parallelogram z) = (+) z ` interior (of_\<omega>12_coords ` ({0..<1} \<times> {0..<1}))"
    unfolding period_parallelogram_def by (subst interior_translation) auto
  also have "interior (of_\<omega>12_coords ` ({0..<1} \<times> {0..<1})) =
             of_\<omega>12_coords ` (interior ({0..<1} \<times> {0..<1}))"
    using of_\<omega>12_coords.linear_axioms bij
     by (rule interior_bijective_linear_image)
  also have "interior ({0..<1::real} \<times> {0..<1::real}) = {0<..<1} \<times> {0<..<1}"
    by (subst interior_Times) simp_all
  finally show ?thesis by (auto simp: box_prod)
qed

lemma path_image_parallelogram_path':
  "path_image (parallelogram_path z \<omega>1 \<omega>2) = 
     (+) z ` of_\<omega>12_coords ` (cbox (0,0) (1,1) - box (0,0) (1,1))"
proof -
  define f where "f = (\<lambda>x. (Re x, Im x))"
  have "bij f"
    by (rule bij_betwI[of _ _ _ "\<lambda>(x,y). Complex x y"]) (auto simp: f_def)
  hence "inj f" "surj f"
    using bij_is_inj bij_is_surj by auto
  have "path_image (parallelogram_path z \<omega>1 \<omega>2) = 
          (\<lambda>w. z + Re w *\<^sub>R \<omega>1 + Im w *\<^sub>R \<omega>2) ` (cbox 0 (1 + \<i>) - box 0 (1 + \<i>))"
    (is "_ = _ ` ?S")
    unfolding parallelogram_path_altdef period_parallelogram_altdef path_image_compose
    by (subst path_image_rectpath_cbox_minus_box) auto
  also have "(\<lambda>w. z + Re w *\<^sub>R \<omega>1 + Im w *\<^sub>R \<omega>2) = (+) z \<circ> of_\<omega>12_coords \<circ> f"
    by (auto simp: of_\<omega>12_coords_def fun_eq_iff scaleR_conv_of_real f_def)
  also have "\<dots> ` (cbox 0 (1 + \<i>) - box 0 (1 + \<i>)) = 
            (+) z ` of_\<omega>12_coords ` f ` ((cbox 0 (1 + \<i>) - box 0 (1 + \<i>)))"
    by (simp add: image_image)
  also have "f ` ((cbox 0 (1 + \<i>) - box 0 (1 + \<i>))) = f ` cbox 0 (1 + \<i>) - f ` box 0 (1 + \<i>)"
    by (rule image_set_diff[OF \<open>inj f\<close>])
  also have "cbox 0 (1 + \<i>) = f -` cbox (0,0) (1,1)"
    by (auto simp: f_def cbox_complex_eq)
  also have "f ` \<dots> = cbox (0,0) (1,1)"
    by (rule surj_image_vimage_eq[OF \<open>surj f\<close>]) 
  also have "box 0 (1 + \<i>) = f -` box (0,0) (1,1)"
    by (auto simp: f_def box_complex_eq box_prod)
  also have "f ` \<dots> = box (0,0) (1,1)"
    by (rule surj_image_vimage_eq[OF \<open>surj f\<close>]) 
  finally show ?thesis .
qed

lemma fund_period_parallelogram_in_lattice_iff:
  assumes "z \<in> period_parallelogram 0"
  shows   "z \<in> \<Lambda> \<longleftrightarrow> z = 0"
proof
  assume "z \<in> \<Lambda>"
  then obtain m n where mn: "z = of_\<omega>12_coords (of_int m, of_int n)"
    by (elim latticeE)
  show "z = 0"
    using assms unfolding mn period_parallelogram_altdef  by auto
qed auto

lemma path_image_parallelogram_path:
  "path_image (parallelogram_path z \<omega>1 \<omega>2) = frontier (period_parallelogram z)"
  unfolding frontier_def closure_period_parallelogram interior_period_parallelogram
            path_image_parallelogram_path' 
  by (subst image_set_diff) (auto intro!: inj_onI simp: of_\<omega>12_coords_eq_iff)

lemma path_image_parallelogram_subset_closure:
  "path_image (parallelogram_path z \<omega>1 \<omega>2) \<subseteq> closure (period_parallelogram z)"
  unfolding path_image_parallelogram_path' closure_period_parallelogram by (intro image_mono) auto

lemma path_image_parallelogram_disjoint_interior:
  "path_image (parallelogram_path z \<omega>1 \<omega>2) \<inter> interior (period_parallelogram z) = {}"
  unfolding path_image_parallelogram_path' interior_period_parallelogram
  by (auto simp: of_\<omega>12_coords_eq_iff box_prod)

lemma winding_number_parallelogram_outside:
  assumes "w \<notin> closure (period_parallelogram z)"
  shows "winding_number (parallelogram_path z \<omega>1 \<omega>2) w = 0"
  by (rule winding_number_zero_outside[OF _ _ _ assms])
     (use path_image_parallelogram_subset_closure[of z] in auto)

text \<open>
  The path we take around the period parallelogram is clearly a simple path, and its orientation
  depends on the angle between our generators.
\<close>
lemma winding_number_parallelogram_inside:
  assumes "w \<in> interior (period_parallelogram z)"
  shows   "winding_number (parallelogram_path z \<omega>1 \<omega>2) w = sgn (Im (\<omega>2 / \<omega>1))"
proof -
  let ?P = "parallelogram_path z \<omega>1 \<omega>2"
  have w: "w \<notin> path_image ?P"
    using assms unfolding interior_period_parallelogram path_image_parallelogram_path'
    by (auto simp: of_\<omega>12_coords_eq_iff box_prod)
  define ind where "ind = (\<lambda>a b. winding_number (linepath (z + a) (z +b)) w)"
  define u where "u = w - z"
  define x y where "x = \<omega>1_coord u" and "y = \<omega>2_coord u"
  have u_eq: "u = of_\<omega>12_coords (x, y)"
    by (simp_all add: x_def y_def flip: \<omega>12_coords_def)
  have xy: "x \<in> {0<..<1}" "y \<in> {0<..<1}" using assms(1)
    unfolding interior_period_parallelogram image_plus_conv_vimage_plus of_\<omega>12_coords_image_eq
    by (auto simp: x_def y_def \<omega>12_coords_def u_def box_prod)
  have w_eq: "w = z + of_\<omega>12_coords (x, y)"
    using u_eq by (simp add: u_def algebra_simps)

  define W where "W = winding_number (parallelogram_path z \<omega>1 \<omega>2) w"
  have Re_W_eq: "Re W = Re (ind 0 \<omega>1) + Re (ind \<omega>1 (\<omega>1 + \<omega>2)) + Re (ind (\<omega>1 + \<omega>2) \<omega>2) + Re (ind \<omega>2 0)"
    using w unfolding W_def parallelogram_path_def
    by (simp add: winding_number_join ind_def path_image_join add_ac)

  show ?thesis
  proof (cases "Im (\<omega>2 / \<omega>1)" "0::real" rule: linorder_cases)
    case equal
    hence False
      using fundpair complex_is_Real_iff by (auto simp: fundpair_def)
    thus ?thesis ..

  next
    case greater
    have "W = 1"
      unfolding W_def
    proof (rule simple_closed_path_winding_number_pos; (fold W_def)?)
      from greater have neg: "Im (\<omega>1 * cnj \<omega>2) < 0"
        by (subst (asm) Im_complex_div_gt_0) (auto simp: mult_ac)
  
      have pos1: "Re (ind 0 \<omega>1) > 0"
      proof -
        have "Im ((z + \<omega>1 - (z + 0)) * cnj (z + \<omega>1 - w)) = y * (-Im (\<omega>1 * cnj \<omega>2))"
          by (simp add: w_eq algebra_simps of_\<omega>12_coords_def)
        also have "\<dots> > 0"
          using neg xy by (intro mult_pos_pos) auto
        finally show ?thesis
          unfolding ind_def by (rule winding_number_linepath_pos_lt)
      qed
  
      have pos2: "Re (ind \<omega>1 (\<omega>1 + \<omega>2)) > 0"
      proof -
        have "Im ((z + (\<omega>1 + \<omega>2) - (z + \<omega>1)) * cnj (z + (\<omega>1 + \<omega>2) - w)) =
                (1 - x) * (-Im (\<omega>1 * cnj \<omega>2))"
          by (simp add: w_eq algebra_simps of_\<omega>12_coords_def)
        also have "\<dots> > 0"
          using neg xy by (intro mult_pos_pos) auto
        finally show ?thesis
          unfolding ind_def by (rule winding_number_linepath_pos_lt)
      qed
    
      have pos3: "Re (ind (\<omega>1 + \<omega>2) \<omega>2) > 0"
      proof -
        have "Im ((z + \<omega>2 - (z + (\<omega>1 + \<omega>2))) * cnj (z + \<omega>2 - w)) =
                (1 - y) * (-Im (\<omega>1 * cnj \<omega>2))"
          by (simp add: w_eq algebra_simps of_\<omega>12_coords_def)
        also have "\<dots> > 0"
          using neg xy by (intro mult_pos_pos) auto
        finally show ?thesis
          unfolding ind_def by (rule winding_number_linepath_pos_lt)
      qed
    
      have pos4: "Re (ind \<omega>2 0) > 0"
      proof -
        have "Im ((z + 0 - (z + \<omega>2)) * cnj (z + 0 - w)) =
                x * (-Im (\<omega>1 * cnj \<omega>2))"
          by (simp add: w_eq algebra_simps of_\<omega>12_coords_def)
        also have "\<dots> > 0"
          using neg xy by (intro mult_pos_pos) auto
        finally show ?thesis
          unfolding ind_def by (rule winding_number_linepath_pos_lt)
      qed

      show "Re W > 0"
        using pos1 pos2 pos3 pos4 unfolding Re_W_eq by linarith
    qed (use w in \<open>auto intro: simple_path_parallelogram\<close>)

    thus ?thesis
      using greater by (simp add: W_def)

  next
    case less
  
    have "W = -1"
      unfolding W_def
    proof (rule simple_closed_path_winding_number_neg; (fold W_def)?)
      from less have neg: "Im (\<omega>2 * cnj \<omega>1) < 0"
        by (simp add: Im_complex_div_lt_0)
  
      have neg1: "Re (ind 0 \<omega>1) < 0"
      proof -
        have "Im ((z + 0 - (z + \<omega>1)) * cnj (z + 0 - w)) = y * (-Im (\<omega>2 * cnj \<omega>1))"
          by (simp add: w_eq algebra_simps of_\<omega>12_coords_def)
        also have "\<dots> > 0"
          using neg xy by (intro mult_pos_pos) auto
        finally show ?thesis
          unfolding ind_def by (rule winding_number_linepath_neg_lt)
      qed
    
      have neg2: "Re (ind \<omega>1 (\<omega>1 + \<omega>2)) < 0"
      proof -
        have "Im ((z + \<omega>1 - (z + (\<omega>1 + \<omega>2))) * cnj (z + \<omega>1 - w)) =
                (1 - x) * (-Im (\<omega>2 * cnj \<omega>1))"
          by (simp add: w_eq algebra_simps of_\<omega>12_coords_def)
        also have "\<dots> > 0"
          using neg xy by (intro mult_pos_pos) auto
        finally show ?thesis
          unfolding ind_def by (rule winding_number_linepath_neg_lt)
      qed
    
      have neg3: "Re (ind (\<omega>1 + \<omega>2) \<omega>2) < 0"
      proof -
        have "Im ((z + (\<omega>1 + \<omega>2) - (z + \<omega>2)) * cnj (z + (\<omega>1 + \<omega>2) - w)) =
                (1 - y) * (-Im (\<omega>2 * cnj \<omega>1))"
          by (simp add: w_eq algebra_simps of_\<omega>12_coords_def)
        also have "\<dots> > 0"
          using neg xy by (intro mult_pos_pos) auto
        finally show ?thesis
          unfolding ind_def by (rule winding_number_linepath_neg_lt)
      qed
    
      have neg4: "Re (ind \<omega>2 0) < 0"
      proof -
        have "Im ((z + \<omega>2 - (z + 0)) * cnj (z + \<omega>2 - w)) =
                x * (-Im (\<omega>2 * cnj \<omega>1))"
          by (simp add: w_eq algebra_simps of_\<omega>12_coords_def)
        also have "\<dots> > 0"
          using neg xy by (intro mult_pos_pos) auto
        finally show ?thesis
          unfolding ind_def by (rule winding_number_linepath_neg_lt)
      qed
  
      show "Re W < 0"
        using neg1 neg2 neg3 neg4 unfolding Re_W_eq by linarith
    qed (use w in \<open>auto intro: simple_path_parallelogram\<close>)

    thus ?thesis
      using less by (simp add: W_def)
  qed
qed

end



subsection \<open>Canonical representatives and the fundamental parallelogram\<close>

context complex_lattice
begin

text \<open>
  The following function maps any complex number \<open>z\<close> to its canonical representative \<open>z'\<close> 
  in the fundamental period parallelogram.
\<close>
definition to_fund_parallelogram :: "complex \<Rightarrow> complex" where
  "to_fund_parallelogram z =
     (case \<omega>12_coords z of (a, b) \<Rightarrow> of_\<omega>12_coords (frac a, frac b))"

lemma to_fund_parallelogram_in_parallelogram [intro]:
  "to_fund_parallelogram z \<in> period_parallelogram 0"
  unfolding to_fund_parallelogram_def
  by (auto simp: period_parallelogram_altdef case_prod_unfold frac_lt_1)

lemma \<omega>1_coord_to_fund_parallelogram [simp]: "\<omega>1_coord (to_fund_parallelogram z) = frac (\<omega>1_coord z)"
  and \<omega>2_coord_to_fund_parallelogram [simp]: "\<omega>2_coord (to_fund_parallelogram z) = frac (\<omega>2_coord z)"
  by (auto simp: to_fund_parallelogram_def case_prod_unfold \<omega>12_coords_def)

lemma to_fund_parallelogramE:
  obtains m n where "to_fund_parallelogram z = z + of_int m * \<omega>1 + of_int n * \<omega>2"
proof -
  define m where "m = floor (fst (\<omega>12_coords z))"
  define n where "n = floor (snd (\<omega>12_coords z))"
  have "z - of_int m * \<omega>1 - of_int n * \<omega>2 =
         of_\<omega>12_coords (\<omega>12_coords z) - of_int m * \<omega>1 - of_int n * \<omega>2"
    by (simp add: m_def n_def)
  also have "\<dots> = to_fund_parallelogram z"
    unfolding of_\<omega>12_coords_def
    by (simp add: case_prod_unfold to_fund_parallelogram_def frac_def
                  m_def n_def of_\<omega>12_coords_def algebra_simps)
  finally show ?thesis
    by (intro that[of "-m" "-n"]) auto
qed

lemma rel_to_fund_parallelogram_left: "rel (to_fund_parallelogram z) z"
proof -
  obtain m n where "to_fund_parallelogram z = z + of_int m * \<omega>1 + of_int n * \<omega>2"
    by (elim to_fund_parallelogramE)
  hence "to_fund_parallelogram z - z = of_int m * \<omega>1 + of_int n * \<omega>2"
    by Groebner_Basis.algebra
  also have "\<dots> = of_\<omega>12_coords (of_int m, of_int n)"
    by (simp add: of_\<omega>12_coords_def)
  also have "\<dots> \<in> \<Lambda>"
    by (rule of_\<omega>12_coords_in_lattice) auto
  finally show ?thesis 
    by (simp add: rel_def)
qed

lemma rel_to_fund_parallelogram_right: "rel z (to_fund_parallelogram z)"
  using rel_to_fund_parallelogram_left[of z] by (simp add: rel_sym)

lemma rel_to_fund_parallelogram_left_iff [simp]: "rel (to_fund_parallelogram z) w \<longleftrightarrow> rel z w"
  using rel_sym rel_to_fund_parallelogram_right rel_trans by blast

lemma rel_to_fund_parallelogram_right_iff [simp]: "rel z (to_fund_parallelogram w) \<longleftrightarrow> rel z w"
  using rel_sym rel_to_fund_parallelogram_left rel_trans by blast

lemma to_fund_parallelogram_in_lattice_iff [simp]: 
  "to_fund_parallelogram z \<in> lattice \<longleftrightarrow> z \<in> lattice"
  using pre_complex_lattice.rel_0_left_iff rel_to_fund_parallelogram_right_iff by blast

lemma to_fund_parallelogram_in_lattice [lattice_intros]:
  "z \<in> lattice \<Longrightarrow> to_fund_parallelogram z \<in> lattice"
  by simp

text \<open>
  \<^const>\<open>to_fund_parallelogram\<close> is a bijective map from any period parallelogram to
  the standard period parallelogram:
\<close>
lemma bij_betw_to_fund_parallelogram:
  "bij_betw to_fund_parallelogram (period_parallelogram orig) (period_parallelogram 0)"
proof -
  have "bij_betw (of_\<omega>12_coords \<circ> map_prod frac frac \<circ> \<omega>12_coords) 
          (period_parallelogram orig) (period_parallelogram 0)"
  proof (intro bij_betw_trans)
    show "bij_betw of_\<omega>12_coords ({0..<1}\<times>{0..<1}) (period_parallelogram 0)"
      by (rule bij_betwI[of _ _ _ \<omega>12_coords]) (auto simp: period_parallelogram_altdef)
  next
    define a b where "a = \<omega>1_coord orig" "b = \<omega>2_coord orig"
    have orig_eq: "orig = of_\<omega>12_coords (a, b)"
      by (auto simp: a_b_def simp flip: \<omega>12_coords_def)

    show "bij_betw \<omega>12_coords (period_parallelogram orig)
            ({\<omega>1_coord orig..<\<omega>1_coord orig+1} \<times> {\<omega>2_coord orig..<\<omega>2_coord orig+1})"
    proof (rule bij_betwI[of _ _ _ of_\<omega>12_coords])
      show "\<omega>12_coords
              \<in> period_parallelogram orig \<rightarrow>
                {\<omega>1_coord orig..<\<omega>1_coord orig + 1} \<times> {\<omega>2_coord orig..<\<omega>2_coord orig + 1}"
        by (auto simp: orig_eq period_parallelogram_def period_parallelogram_altdef \<omega>12_coords.add)
    next
      show "of_\<omega>12_coords \<in> {\<omega>1_coord orig..<\<omega>1_coord orig + 1} \<times> {\<omega>2_coord orig..<\<omega>2_coord orig + 1} \<rightarrow>
              period_parallelogram orig"
      proof safe
        fix c d :: real
        assume c: "c \<in> {\<omega>1_coord orig..<\<omega>1_coord orig + 1}"
        assume d: "d \<in> {\<omega>2_coord orig..<\<omega>2_coord orig + 1}"
        have "of_\<omega>12_coords (c, d) = of_\<omega>12_coords (a, b) + of_\<omega>12_coords (c - a, d - b)"
          by (simp add: of_\<omega>12_coords_def algebra_simps)
        moreover have "(c - a, d - b) \<in> {0..<1} \<times> {0..<1}"
          using c d unfolding a_b_def [symmetric] by auto
        ultimately show "of_\<omega>12_coords (c, d) \<in> period_parallelogram orig"
          unfolding period_parallelogram_def period_parallelogram_altdef orig_eq image_image
          by auto
      qed
    qed auto
  next
    show "bij_betw (map_prod frac frac)
            ({\<omega>1_coord orig..<\<omega>1_coord orig + 1} \<times> {\<omega>2_coord orig..<\<omega>2_coord orig + 1})
            ({0..<1} \<times> {0..<1})"
      by (intro bij_betw_map_prod bij_betw_frac)
  qed
  also have "of_\<omega>12_coords \<circ> map_prod frac frac \<circ> \<omega>12_coords =
               to_fund_parallelogram"
    by (auto simp: o_def to_fund_parallelogram_def fun_eq_iff case_prod_unfold map_prod_def)
  finally show ?thesis .
qed

text \<open>
  There exists a bijection between any two period parallelograms that always maps points to
  equivalent points.
\<close>
lemma bij_betw_period_parallelograms:
  obtains f where
    "bij_betw f (period_parallelogram orig) (period_parallelogram orig')"
    "\<And>z. rel (f z) z"
proof -
  define h where "h = inv_into (period_parallelogram orig') to_fund_parallelogram"
  show ?thesis
  proof (rule that[of "h \<circ> to_fund_parallelogram"])
    show "bij_betw (h \<circ> to_fund_parallelogram)
            (period_parallelogram orig) (period_parallelogram orig')"
      unfolding h_def
      using bij_betw_to_fund_parallelogram bij_betw_inv_into[OF bij_betw_to_fund_parallelogram]
      by (rule bij_betw_trans)
  next
    fix z :: complex
    have "rel (to_fund_parallelogram (h (to_fund_parallelogram z))) (h (to_fund_parallelogram z))"
      by auto
    also have "to_fund_parallelogram (h (to_fund_parallelogram z)) = to_fund_parallelogram z"
      unfolding h_def using bij_betw_to_fund_parallelogram[of orig']
      by (subst f_inv_into_f[of _ to_fund_parallelogram])
         (simp_all add: bij_betw_def to_fund_parallelogram_in_parallelogram)
    finally have *: "rel (to_fund_parallelogram z) (h (to_fund_parallelogram z))" .
    have "rel ((to_fund_parallelogram z - z)) (to_fund_parallelogram z - h (to_fund_parallelogram z))"
      using * diff_in_lattice rel_def rel_to_fund_parallelogram_left by blast
    thus "rel ((h \<circ> to_fund_parallelogram) z) z"
      using * pre_complex_lattice.rel_sym by force
  qed
qed

lemma to_fund_parallelogram_0 [simp]: "to_fund_parallelogram 0 = 0"
  by (simp add: to_fund_parallelogram_def zero_prod_def)

lemma to_fund_parallelogram_lattice [simp]: "z \<in> \<Lambda> \<Longrightarrow> to_fund_parallelogram z = 0"
  by (auto simp: to_fund_parallelogram_def in_lattice_conv_\<omega>12_coords)

lemma to_fund_parallelogram_eq_iff [simp]:
  "to_fund_parallelogram u = to_fund_parallelogram v \<longleftrightarrow> rel u v"
proof
  assume "rel u v"
  then obtain z where z: "z \<in> \<Lambda>" "v = u + z"
    by (elim relE)
  from this(1) obtain m n where mn: "z = of_\<omega>12_coords (of_int m, of_int n)"
    by (elim latticeE)
  show "to_fund_parallelogram u = to_fund_parallelogram v" unfolding z(2)
    by (simp add: to_fund_parallelogram_def \<omega>12_coords.add in_lattice_conv_\<omega>12_coords mn case_prod_unfold)
next
  assume "to_fund_parallelogram u = to_fund_parallelogram v"
  thus "rel u v"
    by (metis rel_to_fund_parallelogram_right rel_to_fund_parallelogram_right_iff)
qed

lemma to_fund_parallelogram_eq_0_iff [simp]: "to_fund_parallelogram u = 0 \<longleftrightarrow> u \<in> \<Lambda>"
  using to_fund_parallelogram_eq_iff[of u 0]
  by (simp del: to_fund_parallelogram_eq_iff add: rel_0_right_iff)

lemma to_fund_parallelogram_of_fund_parallelogram:
  "z \<in> period_parallelogram 0 \<Longrightarrow> to_fund_parallelogram z = z"
  unfolding to_fund_parallelogram_def period_parallelogram_def
  by (auto simp: of_\<omega>12_coords_eq_iff frac_eq_id)

lemma to_fund_parallelogram_idemp [simp]:
  "to_fund_parallelogram (to_fund_parallelogram z) = to_fund_parallelogram z"
  by (rule to_fund_parallelogram_of_fund_parallelogram) auto

lemma to_fund_parallelogram_unique:
  assumes "rel z z'" "z' \<in> period_parallelogram 0"
  shows   "to_fund_parallelogram z = z'"
  using assms by (metis to_fund_parallelogram_eq_iff to_fund_parallelogram_of_fund_parallelogram)

lemma to_fund_parallelogram_unique':
  assumes "rel z z'" "z \<in> period_parallelogram 0" "z' \<in> period_parallelogram 0"
  shows   "z = z'"
  using assms
  by (metis to_fund_parallelogram_eq_iff to_fund_parallelogram_of_fund_parallelogram)


text \<open>
  The following is the ``left half'' of the fundamental parallelogram. The bottom border is
  contained, the top border is not. Of the frontier of this parallelogram only the upper half
  is 
\<close>
definition (in pre_complex_lattice) half_fund_parallelogram where
  "half_fund_parallelogram =
     of_\<omega>12_coords ` {(x,y). x \<in> {0..1/2} \<and> y \<in> {0..<1} \<and> (x \<in> {0, 1/2} \<longrightarrow> y \<le> 1/2)}"

lemma half_fund_parallelogram_altdef:
  "half_fund_parallelogram = \<omega>12_coords -` {(x,y). x \<in> {0..1/2} \<and> y \<in> {0..<1} \<and> (x \<in> {0, 1/2} \<longrightarrow> y \<le> 1/2)}"
  unfolding half_fund_parallelogram_def by (meson of_\<omega>12_coords_image_eq)

lemma zero_in_half_fund_parallelogram [simp, intro]: "0 \<in> half_fund_parallelogram"
  by (auto simp: half_fund_parallelogram_altdef zero_prod_def)

lemma half_fund_parallelogram_in_lattice_iff:
  assumes "z \<in> half_fund_parallelogram"
  shows   "z \<in> \<Lambda> \<longleftrightarrow> z = 0"
proof
  assume "z \<in> \<Lambda>"
  then obtain m n where z_eq: "z = of_\<omega>12_coords (of_int m, of_int n)"
    by (elim latticeE)
  thus "z = 0"
    using assms unfolding z_eq half_fund_parallelogram_altdef by auto
qed auto

definition to_half_fund_parallelogram :: "complex \<Rightarrow> complex" where
  "to_half_fund_parallelogram z =
     (let (x,y) = map_prod frac frac (\<omega>12_coords z);
          (x',y') = (if x > 1/2 \<or> (x \<in> {0, 1/2} \<and> y > 1 / 2) then (if x = 0 then 0 else 1 - x, if y = 0 then 0 else 1 - y) else (x, y))
      in  of_\<omega>12_coords (x',y'))"

lemma in_Ints_conv_floor: "x \<in> \<int> \<longleftrightarrow> x = of_int (floor x)"
  by (metis Ints_of_int of_int_floor)

lemma (in complex_lattice) rel_to_half_fund_parallelogram:
  "rel z (to_half_fund_parallelogram z) \<or> rel z (-to_half_fund_parallelogram z)"
  unfolding rel_def in_lattice_conv_\<omega>12_coords to_half_fund_parallelogram_def Let_def
             \<omega>1_coord.diff \<omega>2_coord.diff \<omega>1_coord.add \<omega>2_coord.add \<omega>1_coord.neg \<omega>2_coord.neg
             case_prod_unfold Let_def \<omega>12_coords_def frac_def map_prod_def
  by (simp flip: in_Ints_conv_floor)

lemma (in complex_lattice) to_half_fund_parallelogram_in_half_fund_parallelogram [intro]: 
  "to_half_fund_parallelogram z \<in> half_fund_parallelogram"
  unfolding half_fund_parallelogram_altdef to_half_fund_parallelogram_def to_half_fund_parallelogram_def Let_def
             \<omega>1_coord.diff \<omega>2_coord.diff \<omega>1_coord.add \<omega>2_coord.add \<omega>1_coord.neg \<omega>2_coord.neg
             case_prod_unfold Let_def \<omega>12_coords_def frac_def map_prod_def
  apply simp
  apply linarith
  done

lemma (in complex_lattice) half_fund_parallelogram_subset_period_parallelogram:
  "half_fund_parallelogram \<subseteq> period_parallelogram 0"
proof -
  have "of_\<omega>12_coords ` {(x, y). x \<in> {0..1 / 2} \<and> y \<in> {0..<1} \<and> (x \<in> {0,1/2} \<longrightarrow> y \<le> 1 / 2)} \<subseteq>
        of_\<omega>12_coords ` ({0..<1} \<times> {0..<1})"
    by (intro image_mono) (auto simp: not_less)
  also have "\<dots> = (+) 0 ` (of_\<omega>12_coords ` ({0..<1} \<times> {0..<1}))"
    by simp
  finally show ?thesis
    unfolding period_parallelogram_def half_fund_parallelogram_def .
qed

lemma to_half_fund_parallelogram_in_lattice_iff [simp]: "to_half_fund_parallelogram z \<in> \<Lambda> \<longleftrightarrow> z \<in> \<Lambda>"
  by (metis rel_lattice_trans_left rel_sym rel_to_half_fund_parallelogram uminus_in_lattice_iff)

lemma rel_in_half_fund_parallelogram_imp_eq:
  assumes "rel z w \<or> rel z (-w)" "z \<in> half_fund_parallelogram" "w \<in> half_fund_parallelogram"
  shows   "z = w"
  using assms(1)
proof
  assume "rel z w"
  moreover from assms have "z \<in> period_parallelogram 0" "w \<in> period_parallelogram 0"
    using half_fund_parallelogram_subset_period_parallelogram by blast+
  ultimately show "z = w"
    by (metis to_fund_parallelogram_eq_iff
        to_fund_parallelogram_of_fund_parallelogram)
next
  assume "rel z (-w)"
  hence "rel (-w) z"
    by (rule rel_symI)
  then obtain m n where z_eq: "z = -w + of_\<omega>12_coords (of_int m, of_int n)"
    by (elim relE latticeE) auto
  define x y where "x = \<omega>1_coord w" "y = \<omega>2_coord w"
  have w_eq: "w = of_\<omega>12_coords (x, y)"
    unfolding x_y_def \<omega>12_coords_def [symmetric] by simp
  have 1: "x \<ge> 0" "y \<ge> 0" "x \<le> 1/2" "y < 1" "x = 0 \<or> x = 1/2 \<Longrightarrow> y \<le> 1/2"
    using assms(3) unfolding half_fund_parallelogram_altdef w_eq by auto
  have 2: "of_int m - x \<ge> 0" "of_int n - y \<ge> 0" "of_int m - x \<le> 1/2" "of_int n - y < 1"
          "of_int m - x = 0 \<or> of_int m - x = 1/2 \<Longrightarrow> of_int n - y \<le> 1/2"
    using assms(2) unfolding half_fund_parallelogram_altdef z_eq w_eq 
    by (auto simp: \<omega>12_coords.diff)

  have "m \<in> {0,1}" "n \<in> {0,1}"
    using 1 2 by auto
  hence "real_of_int m = 2 * x \<and> real_of_int n = 2 * y"
    using 1 2 by auto
  hence "\<omega>12_coords z = \<omega>12_coords w"
    unfolding z_eq w_eq \<omega>12_coords.add \<omega>12_coords.diff \<omega>12_coords.neg \<omega>12_coords_of_\<omega>12_coords
    by simp
  thus ?thesis
    by (metis of_\<omega>12_coords_\<omega>12_coords)
qed  

lemma to_half_fund_parallelogram_of_half_fund_parallelogram:
  assumes "z \<in> half_fund_parallelogram"
  shows   "to_half_fund_parallelogram z = z"
  by (metis assms rel_to_half_fund_parallelogram to_half_fund_parallelogram_in_half_fund_parallelogram rel_in_half_fund_parallelogram_imp_eq)
  
lemma to_half_fund_parallelogram_idemp [simp]:
  "to_half_fund_parallelogram (to_half_fund_parallelogram z) = to_half_fund_parallelogram z"
  by (rule to_half_fund_parallelogram_of_half_fund_parallelogram) auto

lemma to_half_fund_parallelogram_unique:
  assumes "rel z z' \<or> rel z (-z')" "z' \<in> half_fund_parallelogram"
  shows   "to_half_fund_parallelogram z = z'"
proof (rule rel_in_half_fund_parallelogram_imp_eq)
  show "rel (to_half_fund_parallelogram z) z' \<or> rel (to_half_fund_parallelogram z) (- z')"
    using rel_to_half_fund_parallelogram[of z] assms rel_sym rel_trans rel_minus minus_minus
    by metis
qed (use to_half_fund_parallelogram_in_half_fund_parallelogram assms in auto)

lemma to_half_fund_parallelogram_eq_iff:
  "to_half_fund_parallelogram z = to_half_fund_parallelogram w \<longleftrightarrow> rel z w \<or> rel z (-w)"
proof
  assume eq: "to_half_fund_parallelogram z = to_half_fund_parallelogram w"
  define u where "u = to_half_fund_parallelogram w"
  have "rel z u \<or> rel z (-u)" "rel w u \<or> rel w (-u)"
    using rel_to_half_fund_parallelogram[of z] rel_to_half_fund_parallelogram[of w] eq unfolding u_def by auto
  hence "rel z w \<or> (rel z u \<and> rel w (-u) \<or> rel z (-u) \<and> rel w u)"
    using rel_trans rel_sym by blast
  moreover have "rel z (-w)" if "rel z u \<and> rel w (-u) \<or> rel z (-u) \<and> rel w u"
    using that by (metis minus_minus pre_complex_lattice.rel_minus rel_sym rel_trans)
  ultimately show "rel z w \<or> rel z (-w)" by blast
next
  assume *: "rel z w \<or> rel z (-w)"
  define u where "u = to_half_fund_parallelogram w"
  show "to_half_fund_parallelogram z = u"
  proof (rule to_half_fund_parallelogram_unique)
    have "rel w u \<or> rel w (-u)"
      unfolding u_def using rel_to_half_fund_parallelogram[of w] by blast
    with * have "rel z u \<or> (rel (-w) (-u) \<and> rel z (-w) \<or> rel w (-u) \<and> rel z w)"
      using rel_trans rel_sym rel_minus[of w "-u"] rel_minus[of z "-w"] rel_minus[of w u]
      unfolding minus_minus by blast
    thus "rel z u \<or> rel z (-u)"
      using rel_trans rel_sym by blast
  qed (auto simp: u_def)
qed

lemma in_half_fund_parallelogram_imp_half_lattice:
  assumes "z \<in> half_fund_parallelogram" "to_fund_parallelogram (-z) \<in> half_fund_parallelogram"
  shows   "2 * z \<in> \<Lambda>"
  using assms
  by (metis rel_in_half_fund_parallelogram_imp_eq diff_minus_eq_add mult_2
            pre_complex_lattice.rel_def rel_to_fund_parallelogram_left)

end



subsection \<open>Equivalence of fundamental pairs\<close>

text \<open>
  Two fundamental pairs are called \<^emph>\<open>equivalent\<close> if they generate the same complex lattice.
\<close>
definition equiv_fundpair :: "complex \<times> complex \<Rightarrow> complex \<times> complex \<Rightarrow> bool" where
  "equiv_fundpair = (\<lambda>(\<omega>1, \<omega>2) (\<omega>1', \<omega>2').
     pre_complex_lattice.lattice \<omega>1 \<omega>2 = pre_complex_lattice.lattice \<omega>1' \<omega>2')"

lemma equiv_fundpair_iff_aux:
  fixes p :: int
  assumes "p * c + q * a = 0" "p * d + q * b = 1"
          "r * c + s * a = 1" "r * d + s * b = 0"
  shows "\<bar>a * d - b * c\<bar> = 1"
proof -
  have "r * b * c + s * a * b = b"
    by (metis assms(3) distrib_left mult.left_commute mult.right_neutral)
  moreover have "r * a * d + s * a * b = 0"
    by (metis assms(4) distrib_left mult.commute mult.left_commute mult_zero_right)
  ultimately have "r dvd b"
    by (metis mult.assoc dvd_0_right dvd_add_right_iff dvd_triv_left)
  have "p * r * d + p * s * b = 0"
    by (metis assms(4) distrib_left mult.commute mult.left_commute mult_zero_right)
  moreover have "p * r * d + q * r * b = r"
    by (metis assms(2) int_distrib(2) mult.assoc mult.left_commute mult.right_neutral)
  ultimately have "b dvd r"
    by (metis dvd_0_right mult.commute zdvd_reduce)
  have "r * c * d + s * b * c = 0"
    by (metis assms(4) distrib_left mult.commute mult.left_commute mult_zero_right)
  moreover have "r * c * d + s * a * d = d"
    by (metis assms(3) distrib_left mult.commute mult.right_neutral)
  ultimately have "s dvd d"
    by (metis dvd_0_right dvd_add_times_triv_right_iff mult.assoc mult.commute)
  have "q * r * d + q * s * b = 0"
    by (metis mult.assoc assms(4) int_distrib(2) mult_not_zero)
  moreover have "p * s * d + q * s * b = s"
    by (metis assms(2) int_distrib(2) mult.assoc mult.left_commute mult.right_neutral)
  ultimately have "d dvd s"
    by (metis add.commute dvd_0_right mult.commute zdvd_reduce)
  have "\<bar>b\<bar> = \<bar>r\<bar>" "\<bar>d\<bar> = \<bar>s\<bar>"
    by (meson \<open>b dvd r\<close> \<open>r dvd b\<close> \<open>d dvd s\<close> \<open>s dvd d\<close> zdvd_antisym_abs)+
  then show ?thesis
    by (smt (verit, best) assms(3,4) mult.commute mult_cancel_left mult_eq_0_iff mult_minus_left)
qed

text \<open>
  The following fact is Theorem 1.2 in Apostol's book: two fundamental pairs are equivalent 
  iff there exists a unimodular transformation that maps one to the other.
\<close>
theorem equiv_fundpair_iff:
  fixes \<omega>1 \<omega>2 \<omega>1' \<omega>2' :: complex
  assumes "fundpair (\<omega>1, \<omega>2)" "fundpair (\<omega>1', \<omega>2')"
  shows "equiv_fundpair (\<omega>1, \<omega>2) (\<omega>1', \<omega>2') \<longleftrightarrow> 
         (\<exists>a b c d. \<bar>a*d - b*c\<bar> = 1 \<and> 
                    \<omega>2' = of_int a * \<omega>2 + of_int b * \<omega>1 \<and> \<omega>1' = of_int c * \<omega>2 + of_int d * \<omega>1)"
    (is "?lhs = ?rhs")
proof -
  interpret gl: complex_lattice \<omega>1 \<omega>2
    by standard fact
  interpret gl': complex_lattice \<omega>1' \<omega>2'
    by standard fact
  show ?thesis
  proof
    assume L: ?lhs
    hence lattices_eq: "gl.lattice = gl'.lattice"
      by (simp add: equiv_fundpair_def)

    have "\<omega>1' \<in> gl'.lattice" "\<omega>2' \<in> gl'.lattice"
      by auto
    hence "\<omega>1' \<in> gl.lattice" "\<omega>2' \<in> gl.lattice"
      by (simp_all add: lattices_eq)
    then obtain a b c d
      where ab: "\<omega>2' = of_int b * \<omega>1 + of_int a * \<omega>2"
        and cd: "\<omega>1' = of_int d * \<omega>1 + of_int c * \<omega>2"
      by (elim gl.latticeE) (auto simp: gl.of_\<omega>12_coords_def scaleR_conv_of_real)

    have "\<omega>1 \<in> gl.lattice" "\<omega>2 \<in> gl.lattice"
      by auto
    hence "\<omega>1 \<in> gl'.lattice" "\<omega>2 \<in> gl'.lattice"
      by (simp_all add: lattices_eq)
    then obtain p q r s
      where pq: "\<omega>1 = of_int p * \<omega>1' + of_int q * \<omega>2'" and
            rs: "\<omega>2 = of_int r * \<omega>1' + of_int s * \<omega>2'"
      by (elim gl'.latticeE) (auto simp: gl'.of_\<omega>12_coords_def scaleR_conv_of_real)

    have "\<omega>1 = p * (c * \<omega>2 + d * \<omega>1) + q * (a * \<omega>2 + b * \<omega>1)"
      using pq cd ab add.commute by metis
    also have "... = (p * c + q * a) * \<omega>2 + (p * d + q * b) * \<omega>1"
      by (simp add: algebra_simps)
    finally have "gl.of_\<omega>12_coords (1, 0) = gl.of_\<omega>12_coords (p*d+q*b, p*c+q*a)"
      by (simp_all add: gl.of_\<omega>12_coords_def add_ac)
    hence pc: "(p * c + q * a) = 0 \<and> p * d + q * b = 1"
      unfolding gl.of_\<omega>12_coords_eq_iff prod.case prod.inject by linarith
      
    have "\<omega>2 = r * (c * \<omega>2 + d * \<omega>1) + s * (a * \<omega>2 + b * \<omega>1)"
      using cd rs ab add.commute by metis
    also have "... = (r * c + s * a) * \<omega>2 + (r * d + s * b) * \<omega>1"
      by (simp add: algebra_simps)
    finally have "gl.of_\<omega>12_coords (0, 1) = gl.of_\<omega>12_coords (r*d+s*b, r*c+s*a)"
      by (simp_all add: gl.of_\<omega>12_coords_def add_ac)
    hence rc: "r * c + s * a = 1 \<and> r * d + s * b = 0"
      unfolding gl.of_\<omega>12_coords_eq_iff prod.case prod.inject by linarith
    with pc have "\<bar>a*d - b*c\<bar> = 1"
      by (meson equiv_fundpair_iff_aux)

    hence "\<bar>a*d - b*c\<bar> = 1 \<and> 
             \<omega>2' = of_int a * \<omega>2 + of_int b * \<omega>1 \<and> \<omega>1' = of_int c * \<omega>2 + of_int d * \<omega>1"
      using cd ab by auto
    thus ?rhs
      by blast
  next
    assume ?rhs
    then obtain a b c d :: int where 1: "\<bar>a * d - b * c\<bar> = 1"
      and eq: "\<omega>2' = of_int a * \<omega>2 + of_int b * \<omega>1" "\<omega>1' = of_int c * \<omega>2 + of_int d * \<omega>1"
      by blast
    define det where "det = a * d - b * c"
    define a' b' c' d' where "a' = det * d" "b' = -det * b" "c' = -det * c" "d' = det * a"
    have "\<bar>det\<bar> = 1"
      using 1 by (simp add: det_def)
    hence det_square: "det ^ 2 = 1"
      using abs_square_eq_1 by blast

    have eq': "\<omega>2 = of_int a' * \<omega>2' + of_int b' * \<omega>1'" "\<omega>1 = of_int c' * \<omega>2' + of_int d' * \<omega>1'"
    proof -
      have "of_int a' * \<omega>2' + of_int b' * \<omega>1' = det^2 * \<omega>2"
        by (simp add: eq algebra_simps det_def a'_b'_c'_d'_def power2_eq_square)
      thus "\<omega>2 = of_int a' * \<omega>2' + of_int b' * \<omega>1'"
        by (simp add: det_square)
    next
      have "of_int c' * \<omega>2' + of_int d' * \<omega>1' = det^2 * \<omega>1"
        by (simp add: eq algebra_simps det_def a'_b'_c'_d'_def power2_eq_square)
      thus "\<omega>1 = of_int c' * \<omega>2' + of_int d' * \<omega>1'"
        by (simp add: det_square)
    qed

    have "gl'.lattice \<subseteq> gl.lattice"
      by (safe elim!: gl'.latticeE, unfold gl'.of_\<omega>12_coords_def)
         (auto simp: eq ring_distribs intro!: gl'.lattice_intros)
    moreover have "gl.lattice \<subseteq> gl'.lattice"
      by (safe elim!: gl.latticeE, unfold gl.of_\<omega>12_coords_def)
         (auto simp: eq' ring_distribs intro!: gl.lattice_intros)
    ultimately show ?lhs
      unfolding equiv_fundpair_def by auto
  qed
qed



text \<open>
  We will now look at the triangle spanned by the origin and the generators.
  We will prove that the only points that lie in or on this triangle are its three vertices.

  Moreover, we shall prove that for any lattice \<open>\<Lambda>\<close>, if we have two points \<open>\<omega>\<^sub>1', \<omega>\<^sub>2' \<in> \<Lambda>\<close>
  then these two points generate \<open>\<Lambda>\<close> if and only if the triangle spanned by \<open>0\<close>, \<open>\<omega>\<^sub>1'\<close>, and \<open>\<omega>\<^sub>2'\<close>
  contains no other lattice points except \<open>0\<close>, \<open>\<omega>\<^sub>1'\<close>, and \<open>\<omega>\<^sub>2'\<close>.
\<close>
context complex_lattice
begin

lemma in_triangle_iff:
  fixes x
  defines "a \<equiv> \<omega>1_coord x" and "b \<equiv> \<omega>2_coord x"
  shows   "x \<in> convex hull {0, \<omega>1, \<omega>2} \<longleftrightarrow> a \<ge> 0 \<and> b \<ge> 0 \<and> a + b \<le> 1"
proof
  assume "x \<in> convex hull {0, \<omega>1, \<omega>2}"
  then obtain t u where tu: "u \<ge> 0" "t \<ge> 0" "u + t \<le> 1" "x = of_\<omega>12_coords (u, t)"
    unfolding convex_hull_3_alt by (auto simp: of_\<omega>12_coords_def scaleR_conv_of_real)
  have "a = u" "b = t"
    by (auto simp: a_def b_def tu(4))
  with tu show "a \<ge> 0 \<and> b \<ge> 0 \<and> a + b \<le> 1"
    by auto
next
  assume ab: "a \<ge> 0 \<and> b \<ge> 0 \<and> a + b \<le> 1"
  have "x = of_\<omega>12_coords (a, b)"
    by (auto simp: a_def b_def simp flip: \<omega>12_coords_def)
  hence "x = 0 + a *\<^sub>R (\<omega>1 - 0) + b *\<^sub>R (\<omega>2 - 0)" "0 \<le> a \<and> 0 \<le> b \<and> a + b \<le> 1"
    using ab by (auto simp: a_def b_def of_\<omega>12_coords_def scaleR_conv_of_real)
  thus "x \<in> convex hull {0, \<omega>1, \<omega>2}"
    unfolding convex_hull_3_alt by blast
qed

text \<open>
  The only lattice points inside the fundamental triangle are the generators and the origin.
\<close>
lemma lattice_Int_triangle: "convex hull {0, \<omega>1, \<omega>2} \<inter> \<Lambda> = {0, \<omega>1, \<omega>2}"
proof (intro equalityI subsetI)
  fix x assume x: "x \<in> convex hull {0, \<omega>1, \<omega>2} \<inter> \<Lambda>"
  then obtain a b :: real where ab: "a \<ge> 0" "b \<ge> 0" "a + b \<le> 1" "x = of_\<omega>12_coords (a, b)"
    unfolding convex_hull_3_alt by (auto simp: of_\<omega>12_coords_def scaleR_conv_of_real)
  from ab(4) and x have "a \<in> \<int>" "b \<in> \<int>"
    by (auto simp: of_\<omega>12_coords_in_lattice_iff)
  with ab(1-3) have "(a, b) \<in> {(0, 0), (0, 1), (1, 0)}"
    by (auto elim!: Ints_cases)
  with ab show "x \<in> {0, \<omega>1, \<omega>2}"
    by auto
qed (auto intro: hull_inc)

text \<open>
  The following fact is Theorem~1.1 in Apostol's book: given a fixed lattice \<open>\<Lambda>\<close>, a pair of
  non-collinear period vectors $\omega_1$, $\omega_2$ is fundamental (i.e.\ generates \<open>\<Lambda>\<close>) iff the 
  triangle spanned by $0$, $\omega_1$, $\omega_2$ contains no lattice points other than its
  three vertices.
\<close>
lemma equiv_fundpair_iff_triangle:
  assumes "fundpair (\<omega>1', \<omega>2')" "\<omega>1' \<in> \<Lambda>" "\<omega>2' \<in> \<Lambda>"
  shows   "equiv_fundpair (\<omega>1, \<omega>2) (\<omega>1', \<omega>2') \<longleftrightarrow> convex hull {0, \<omega>1', \<omega>2'} \<inter> \<Lambda> = {0, \<omega>1', \<omega>2'}"
proof -
  interpret lattice': complex_lattice \<omega>1' \<omega>2'
    by standard fact
  show ?thesis
  proof
    assume "equiv_fundpair (\<omega>1, \<omega>2) (\<omega>1', \<omega>2')"
    thus "convex hull {0, \<omega>1', \<omega>2'} \<inter> \<Lambda> = {0, \<omega>1', \<omega>2'}"
      using lattice'.lattice_Int_triangle by (simp add: equiv_fundpair_def)
  next
    assume triangle: "convex hull {0, \<omega>1', \<omega>2'} \<inter> \<Lambda> = {0, \<omega>1', \<omega>2'}"
    
    show "equiv_fundpair (\<omega>1, \<omega>2) (\<omega>1', \<omega>2')"
      unfolding equiv_fundpair_def prod.case
    proof
      show "lattice'.lattice \<subseteq> \<Lambda>"
        by (intro subsetI, elim lattice'.latticeE)
           (auto simp: lattice'.of_\<omega>12_coords_def intro!: lattice_intros assms)
    next
      show "\<Lambda> \<subseteq> lattice'.lattice"
      proof
        fix x assume x: "x \<in> \<Lambda>"
        define y where "y = lattice'.to_fund_parallelogram x"
        have y: "y \<in> \<Lambda>"
        proof -
          obtain a b where y_eq: "y = x + of_int a * \<omega>1' + of_int b * \<omega>2'"
            using lattice'.to_fund_parallelogramE[of x] unfolding y_def by blast
          show ?thesis by (auto simp: y_eq intro!: lattice_intros assms x)
        qed

        have "y \<in> lattice'.lattice"
        proof (cases "y \<in> convex hull {0, \<omega>1', \<omega>2'}")
          case True
          hence "y \<in> convex hull {0, \<omega>1', \<omega>2'} \<inter> \<Lambda>"
            using y by auto
          also note triangle
          finally show ?thesis
            by auto
        next
          case False
          define y' where "y' = \<omega>1' + \<omega>2' - y"
          have y_conv_y': "y = \<omega>1' + \<omega>2' - y'"
            by (simp add: y'_def)
          define a b where "a = lattice'.\<omega>1_coord x" and "b = lattice'.\<omega>2_coord x"
          have [simp]: "lattice'.\<omega>1_coord y = frac a" "lattice'.\<omega>2_coord y = frac b"
            by (simp_all add: y_def a_def b_def)
          from False have "frac a + frac b > 1"
            by (auto simp: lattice'.in_triangle_iff y'_def)
          hence "y' \<in> convex hull {0, \<omega>1', \<omega>2'}"
            by (auto simp: lattice'.in_triangle_iff y'_def less_imp_le[OF frac_lt_1]
                           lattice'.\<omega>1_coord.add lattice'.\<omega>2_coord.add
                           lattice'.\<omega>1_coord.diff lattice'.\<omega>2_coord.diff)
          hence "y' \<in> convex hull {0, \<omega>1', \<omega>2'} \<inter> \<Lambda>"
            using y assms by (auto simp: y'_def intro!: lattice_intros)
          also note triangle
          finally have "y' \<in> {0, \<omega>1', \<omega>2'}" .
          thus ?thesis
            by (auto simp: y_conv_y' intro!: lattice'.lattice_intros)
        qed
        thus "x \<in> lattice'.lattice"
          by (simp add: y_def)
      qed
    qed
  qed
qed

end


subsection \<open>Additional useful facts\<close>

context complex_lattice
begin

text \<open>
  The following partitions the lattice into countably many ``layers'', starting from the origin,
  which is the 0-th layer. The $k$-th layer consists of precisely those points in the lattice
  whose lattice coordinates $(m,n)$ satisfy $\max(|m|,|n|) = k$.
\<close>
definition lattice_layer :: "nat \<Rightarrow> complex set" where
  "lattice_layer k =
     of_\<omega>12_coords ` map_prod of_int of_int `
       ({int k, -int k} \<times> {-int k..int k} \<union> {-int k..int k} \<times> {-int k, int k})"

lemma in_lattice_layer_iff:
  "z \<in> lattice_layer k \<longleftrightarrow>
     \<omega>12_coords z \<in> \<int> \<times> \<int> \<inter> ({int k, -int k} \<times> {-int k..int k} \<union> {-int k..int k} \<times> {-int k, int k})"
  (is "?lhs = ?rhs")
proof
  assume ?lhs
  thus ?rhs
    unfolding lattice_layer_def of_\<omega>12_coords_image_eq by (auto simp: case_prod_unfold)
next
  assume ?rhs
  thus ?lhs unfolding lattice_layer_def image_Un map_prod_image of_\<omega>12_coords_image_eq
    by (auto elim!: Ints_cases)
qed

lemma of_\<omega>12_coords_of_int_in_lattice_layer:
  "of_\<omega>12_coords (of_int a, of_int b) \<in> lattice_layer (nat (max \<bar>a\<bar> \<bar>b\<bar>))"
  unfolding in_lattice_layer_iff by (auto simp flip: of_int_minus simp: max_def)

lemma lattice_layer_covers: "\<Lambda> = (\<Union>k. lattice_layer k)"
proof -
  have "(\<Union>k. lattice_layer k) = of_\<omega>12_coords ` map_prod real_of_int real_of_int ` 
          (\<Union>k. ({int k, - int k} \<times> {- int k..int k} \<union> {- int k..int k} \<times> {- int k, int k}))"
    (is "_ = _ ` _ ` (\<Union>k. ?A k)") unfolding lattice_layer_def by blast
  also have "(\<Union>k. ?A k) = UNIV"
  proof safe
    fix a b :: int
    have "(a, b) \<in> ?A (nat (max \<bar>a\<bar> \<bar>b\<bar>))"
      unfolding max_def by simp linarith
    thus "(a, b) \<in> (\<Union>k. ?A k)"
      by blast
  qed blast+
  also have "range (map_prod real_of_int real_of_int) = \<int> \<times> \<int>"
    by (auto elim!: Ints_cases)
  finally show ?thesis
    by (simp add: lattice_def)
qed

lemma finite_lattice_layer: "finite (lattice_layer k)"
  unfolding lattice_layer_def by auto

lemma lattice_layer_0: "lattice_layer 0 = {0}"
  by (auto simp: lattice_layer_def)

lemma zero_in_lattice_layer_iff [simp]: "0 \<in> lattice_layer k \<longleftrightarrow> k = 0"
  by (auto simp: in_lattice_layer_iff zero_prod_def)

lemma lattice_layer_disjoint:
  assumes "m \<noteq> n"
  shows   "lattice_layer m \<inter> lattice_layer n = {}"
  using assms by (auto simp: lattice_layer_def of_\<omega>12_coords_eq_iff)

(* lemma 1. p.7 *)
lemma lattice0_conv_layers: "\<Lambda>\<^sup>* = (\<Union>i\<in>{0<..}. lattice_layer i)" (is "?lhs = ?rhs")
proof -
  have "\<Lambda>\<^sup>* = (\<Union>i\<in>UNIV. lattice_layer i) - lattice_layer 0"
    by (simp add: lattice0_def lattice_layer_covers lattice_layer_0)
  also have "\<dots> = (\<Union>i\<in>UNIV-{0}. lattice_layer i)"
    using lattice_layer_disjoint by blast
  also have "UNIV-{0::nat} = {0<..}"
    by auto
  finally show ?thesis .
qed

lemma card_lattice_layer:
  assumes "k > 0"
  shows "card (lattice_layer k) = 8 * k"
proof -
  define f where "f = of_\<omega>12_coords \<circ> map_prod real_of_int real_of_int"
  have "lattice_layer k = f ` ({int k, - int k} \<times> {- int k..int k} \<union> {- int k..int k} \<times> {- int k, int k})"
    (is "_ = _ ` ?A") unfolding lattice_layer_def f_def image_image o_def ..
  also have "card \<dots> = card ?A"
    by (intro card_image)
       (auto simp: inj_on_def of_\<omega>12_coords_eq_iff f_def map_prod_def case_prod_unfold)
  also have "?A = {int k, -int k} \<times> {-int k..int k} \<union> {-int k+1..int k-1} \<times> {-int k, int k}"
    by auto
  also have "card \<dots> = 8 * k" using \<open>k > 0\<close>
    by (subst card_Un_disjoint)
       (auto simp: nat_diff_distrib nat_add_distrib nat_mult_distrib Suc_diff_Suc)
  finally show ?thesis .
qed

lemma lattice_layer_nonempty: "lattice_layer k \<noteq> {}"
  by (auto simp: lattice_layer_def)

definition lattice_layer_path :: "complex set" where
  "lattice_layer_path = of_\<omega>12_coords ` ({1, -1} \<times> {-1..1} \<union> {-1..1} \<times> {-1, 1})"

lemma in_lattice_layer_path_iff:
  "z \<in> lattice_layer_path \<longleftrightarrow> \<omega>12_coords z \<in> ({1, -1} \<times> {-1..1} \<union> {-1..1} \<times> {-1, 1})"
  unfolding lattice_layer_path_def of_\<omega>12_coords_image_eq by blast

lemma lattice_layer_path_nonempty: "lattice_layer_path \<noteq> {}"
proof -
  have "\<omega>1 \<in> lattice_layer_path"
    by (auto simp: in_lattice_layer_path_iff)
  thus ?thesis by blast
qed

lemma compact_lattice_layer_path [intro]: "compact lattice_layer_path"
  unfolding lattice_layer_path_def of_\<omega>12_coords_def case_prod_unfold
  by (intro compact_continuous_image continuous_intros compact_Un compact_Times) auto

lemma lattice_layer_subset: "lattice_layer k \<subseteq> (*) (of_nat k) ` lattice_layer_path"
proof
  fix x
  assume "x \<in> lattice_layer k"
  then obtain m n where x: "x = of_\<omega>12_coords (of_int m, of_int n)"
    "(m, n) \<in> ({int k, -int k} \<times> {-int k..int k} \<union> {-int k..int k} \<times> {-int k, int k})"
    unfolding lattice_layer_def by blast

  show "x \<in> (*) (of_nat k) ` lattice_layer_path"
  proof (cases "k > 0")
    case True
    have "x = of_nat k * of_\<omega>12_coords (of_int m / of_int k, of_int n / of_int k)"
         "(of_int m / of_int k, of_int n / of_int k) \<in> {1::real, -1} \<times> {-1..1} \<union> {-1..1} \<times> {-1::real, 1}"
      using x True by (auto simp: divide_simps of_\<omega>12_coords_def)
    thus ?thesis
      unfolding lattice_layer_path_def by blast
  qed (use x in \<open>auto simp: lattice_layer_path_def image_iff
                      intro!: exI[of _ "\<omega>1"] bexI[of _ "(1, 0)"]\<close>)
qed

text \<open>
  The shortest and longest distance of any point on the first layer from the origin,
  respectively.
\<close>
definition Inf_para :: real where \<comment>\<open>@{term r} in the proof of Lemma 1\<close>
  "Inf_para \<equiv> Inf (norm ` lattice_layer_path)"

lemma Inf_para_pos: "Inf_para > 0"
proof -
  have "compact (norm ` lattice_layer_path)"
    by (intro compact_continuous_image continuous_intros) auto
  hence "Inf_para \<in> norm ` lattice_layer_path"
    unfolding Inf_para_def
    by (intro closed_contains_Inf)
       (use lattice_layer_path_nonempty in \<open>auto simp: compact_imp_closed bdd_below_norm_image\<close>)
  moreover have "\<forall>x\<in>norm ` lattice_layer_path. x > 0"
    by (auto simp: in_lattice_layer_path_iff zero_prod_def)
  ultimately show ?thesis
    by blast
qed

lemma Inf_para_nonzero [simp]: "Inf_para \<noteq> 0"
  using Inf_para_pos by linarith

lemma Inf_para_le:
  assumes "z \<in> lattice_layer_path"
  shows   "Inf_para \<le> norm z"
  unfolding Inf_para_def by (rule cInf_lower) (use assms bdd_below_norm_image in auto)

lemma lattice_layer_le_norm: 
  assumes "\<omega> \<in> lattice_layer k"
  shows "k * Inf_para \<le> norm \<omega>"
proof -
  obtain z where z: "z \<in> lattice_layer_path" "\<omega> = of_nat k * z"
    using lattice_layer_subset[of k] assms by auto
  have "real k * Inf_para \<le> real k * norm z"
    by (intro mult_left_mono Inf_para_le z) auto
  also have "\<dots> = norm \<omega>"
    by (simp add: z norm_mult)
  finally show ?thesis .
qed

corollary Inf_para_le_norm: 
  assumes "\<omega> \<in> \<Lambda>\<^sup>*"
  shows "Inf_para \<le> norm \<omega>"
proof -
  from assms obtain k where \<omega>: "\<omega> \<in> lattice_layer k" and "k \<noteq> 0"
    unfolding lattice0_def by (metis DiffE UN_iff lattice_layer_0 lattice_layer_covers)
  with Inf_para_pos have "Inf_para \<le> real k * Inf_para"
    by auto
  then show ?thesis
    using \<omega> lattice_layer_le_norm by force
qed

text \<open>
  One easy corollary is now that our lattice is discrete in the sense that there is a positive
  real number that bounds the distance between any two points from below.
\<close>
lemma Inf_para_le_dist:
  assumes "x \<in> \<Lambda>" "y \<in> \<Lambda>" "x \<noteq> y"
  shows   "dist x y \<ge> Inf_para"
proof -
  have "x - y \<in> \<Lambda>" "x - y \<noteq> 0"
    using assms by (auto intro: diff_in_lattice)
  hence "x - y \<in> \<Lambda>\<^sup>*"
    by auto
  hence "Inf_para \<le> norm (x - y)"
    by (rule Inf_para_le_norm)
  thus ?thesis
    by (simp add: dist_norm)
qed


definition Sup_para :: real where \<comment>\<open>@{term R} in the proof of Lemma 1\<close>
  "Sup_para \<equiv> Sup (norm ` lattice_layer_path)"

lemma Sup_para_ge: 
  assumes "z \<in> lattice_layer_path"
  shows   "Sup_para \<ge> norm z"
  unfolding Sup_para_def
proof (rule cSup_upper)
  show "bdd_above (norm ` lattice_layer_path)"
    unfolding bdd_above_norm by (rule compact_imp_bounded) auto
qed (use assms in auto)

lemma Sup_para_pos: "Sup_para > 0"
proof -
  have "0 < norm \<omega>1"
    using \<omega>1_nonzero by auto
  also have "\<dots> \<le> Sup_para"
    by (rule Sup_para_ge) (auto simp: in_lattice_layer_path_iff)
  finally show ?thesis .
qed

lemma Sup_para_nonzero [simp]: "Sup_para \<noteq> 0"
  using Sup_para_pos by linarith

lemma lattice_layer_ge_norm: 
  assumes "\<omega> \<in> lattice_layer k"
  shows "norm \<omega> \<le> k * Sup_para"
proof -
  obtain z where z: "z \<in> lattice_layer_path" "\<omega> = of_nat k * z"
    using lattice_layer_subset[of k] assms by auto
  have "norm \<omega> = real k * norm z"
    by (simp add: z norm_mult)
  also have "\<dots> \<le> real k * Sup_para"
    by (intro mult_left_mono Sup_para_ge z) auto
  finally show ?thesis .
qed   

text \<open>
  We can now easily show that our lattice is a sparse set (i.e. it has no limit points).
  This also implies that it is closed.
\<close>
lemma not_islimpt_lattice: "\<not>z islimpt \<Lambda>"
proof (rule discrete_imp_not_islimpt[of Inf_para])
  fix x y assume "x \<in> \<Lambda>" "y \<in> \<Lambda>" "dist x y < Inf_para"
  with Inf_para_le_dist[of x y] show "x = y"
    by (cases "x = y") auto
qed (fact Inf_para_pos)

lemma closed_lattice: "closed lattice"
  unfolding closed_limpt by (auto simp: not_islimpt_lattice)

lemma lattice_sparse: "\<Lambda> sparse_in UNIV"
  using not_islimpt_lattice sparse_in_def by blast

text \<open>
  Any non-empty set of lattice points has one lattice point that is closer to the origin 
  than all others.
\<close>
lemma shortest_lattice_vector_exists:
  assumes "X \<subseteq> \<Lambda>" "X \<noteq> {}"
  obtains x where "x \<in> X" "\<And>y. y \<in> X \<Longrightarrow> norm x \<le> norm y"
proof -
  obtain x0 where x0: "x0 \<in> X"
    using assms by auto
  have "\<not>z islimpt X" for z
    using not_islimpt_lattice assms(1) islimpt_subset by blast
  hence "finite (cball 0 (norm x0) \<inter> X)"
    by (intro finite_not_islimpt_in_compact) auto
  moreover have "x0 \<in> cball 0 (norm x0) \<inter> X"
    using x0 by auto
  ultimately obtain x where x: "is_arg_min norm (\<lambda>x. x \<in> cball 0 (norm x0) \<inter> X) x"
    using ex_is_arg_min_if_finite[of "cball 0 (norm x0) \<inter> X" norm] by blast
  thus ?thesis
    by (intro that[of x]) (auto simp: is_arg_min_def)
qed

text \<open>
  If $x$ is a non-zero lattice point then there exists another lattice point that is
  not collinear with $x$, i.e.\ that does not lie on the line through $0$ and $x$.
\<close>
lemma noncollinear_lattice_point_exists:
  assumes "x \<in> \<Lambda>\<^sup>*"
  obtains y where "y \<in> \<Lambda>\<^sup>*" "y / x \<notin> \<real>"
proof -
  from assms obtain m n where x: "x = of_\<omega>12_coords (of_int m, of_int n)" and "x \<noteq> 0"
    by (elim latticeE lattice0E DiffE) auto
  define y where "y = of_\<omega>12_coords (of_int (-n), of_int m)"
  have "y \<in> \<Lambda>"
    by (auto simp: y_def)
  moreover have "y \<noteq> 0"
    using \<open>x \<noteq> 0\<close> by (auto simp: x y_def of_\<omega>12_coords_eq_0_iff prod_eq_iff)
  moreover have "y / x \<notin> \<real>"
  proof
    assume "y / x \<in> \<real>"
    then obtain a where "y / x = of_real a"
      by (elim Reals_cases)
    hence y: "y = a *\<^sub>R x"
      using assms \<open>x \<noteq> 0\<close> by (simp add: field_simps scaleR_conv_of_real)
    have "of_\<omega>12_coords (-real_of_int n, real_of_int m) =
          of_\<omega>12_coords (a * real_of_int m, a * real_of_int n)"
      using y by (simp add: x y_def algebra_simps flip: of_\<omega>12_coords.scaleR)
    hence eq: "-real_of_int n = a * real_of_int m" "real_of_int m = a * real_of_int n"
      unfolding of_\<omega>12_coords_eq_iff prod_eq_iff fst_conv snd_conv by blast+
    have "m \<noteq> 0 \<or> n \<noteq> 0"
      using \<open>x \<noteq> 0\<close> by (auto simp: x)
    with eq[symmetric] have nz: "m \<noteq> 0" "n \<noteq> 0"
      by auto
    have "a ^ 2 * real_of_int m = a * (a * real_of_int m)"
      by (simp add: power2_eq_square algebra_simps)
    also have "\<dots> = (-1) * real_of_int m"
      by (simp flip: eq)
    finally have "a ^ 2 = -1"
      using \<open>m \<noteq> 0\<close> by (subst (asm) mult_right_cancel) auto
    moreover have "a ^ 2 \<ge> 0"
      by simp
    ultimately show False
      by linarith
  qed
  ultimately show ?thesis
    by (intro that) auto
qed

text \<open>
  We can always easily find a period parallelogram whose border does not touch any given set
  of points we want to avoid, as long as that set is sparse.
\<close>
lemma shifted_period_parallelogram_avoid:
  assumes "countable avoid"
  obtains orig where "path_image (parallelogram_path orig \<omega>1 \<omega>2) \<inter> avoid = {}"
proof -
  define avoid' where "avoid' = \<omega>12_coords ` avoid"

  define avoid1 where "avoid1 = fst ` avoid'"
  define avoid2 where "avoid2 = snd ` avoid'"
  define avoid''
    where "avoid'' = (avoid1 \<union> (\<lambda>x. x - 1) ` avoid1) \<times> UNIV \<union> UNIV \<times> (avoid2 \<union> (\<lambda>x. x - 1) ` avoid2)"

  obtain orig where orig: "orig \<notin> avoid''"
  proof -
    have *: "avoid1 \<union> (\<lambda>x. x - 1) ` avoid1 \<in> null_sets lborel"
            "avoid2 \<union> (\<lambda>x. x - 1) ` avoid2 \<in> null_sets lborel"
      by (rule null_sets.Un; rule countable_imp_null_set_lborel;
          use assms in \<open>force simp: avoid1_def avoid2_def avoid'_def\<close>)+
    have "avoid'' \<in> null_sets lborel"
      unfolding lborel_prod[symmetric] avoid''_def using * by (intro null_sets.Un) auto
    hence "AE z in lborel. z \<notin> avoid''"
      using AE_not_in by blast
    from eventually_happens[OF this] show ?thesis using that
      by (auto simp: ae_filter_eq_bot_iff)
  qed

  have *: "(\<lambda>x. x - 1) ` X = ((+) 1) -` X" for X :: "real set"
    by force

  have fst_orig: "fst z \<notin> {fst orig, fst orig + 1}" if "z \<in> avoid'" for z
  proof
    assume "fst z \<in> {fst orig, fst orig + 1}"
    hence "orig \<in> (avoid1 \<union> (\<lambda>x. x - 1) ` avoid1) \<times> UNIV"
      using that unfolding avoid1_def * by (cases orig; cases z) force
    thus False using orig
      by (auto simp: avoid''_def)
  qed

  have snd_orig: "snd z \<notin> {snd orig, snd orig + 1}" if "z \<in> avoid'" for z
  proof
    assume "snd z \<in> {snd orig, snd orig + 1}"
    hence "orig \<in> UNIV \<times> (avoid2 \<union> (\<lambda>x. x - 1) ` avoid2)"
      using that unfolding avoid2_def * by (cases orig; cases z) force     
    thus False using orig
      by (auto simp: avoid''_def)
  qed

  show ?thesis
  proof (rule that[of "of_\<omega>12_coords orig"], safe)
    fix z assume z: "z \<in> path_image (parallelogram_path (of_\<omega>12_coords orig) \<omega>1 \<omega>2)" "z \<in> avoid"
    have "\<omega>12_coords z \<in> \<omega>12_coords `path_image (parallelogram_path (of_\<omega>12_coords orig) \<omega>1 \<omega>2)"
      using z(1) by blast
    thus "z \<in> {}" using z(2) fst_orig[of "\<omega>12_coords z"] snd_orig[of "\<omega>12_coords z"]
      unfolding path_image_parallelogram_path'
      by (auto simp: avoid'_def \<omega>12_coords.add box_prod)
  qed
qed

text \<open>
  We can also prove a rule that allows us to prove a property about period parallelograms while
  assuming w.l.o.g.\ that the border of the parallelogram does not touch an arbitrary sparse 
  set of points we want to avoid and the property we want to prove is invariant under shifting
  the parallelogram by an arbitrary amount.

  This will be useful later for the use case of showing that any period parallelograms contain
  the same number of zeros as poles, which is proven by integrating along the border of a period
  parallelogram that is assume w.l.o.g.\ not to have any zeros or poles on its border.
\<close>
lemma shifted_period_parallelogram_avoid_wlog [consumes 1, case_names shift avoid]:
  assumes "\<And>z. \<not>z islimpt avoid"
  assumes "\<And>orig d. finite (closure (period_parallelogram orig) \<inter> avoid) \<Longrightarrow>
                    finite (closure (period_parallelogram (orig + d)) \<inter> avoid) \<Longrightarrow> 
                    P orig \<Longrightarrow> P (orig + d)"
  assumes "\<And>orig. finite (closure (period_parallelogram orig) \<inter> avoid) \<Longrightarrow>
                   path_image (parallelogram_path orig \<omega>1 \<omega>2) \<inter> avoid = {} \<Longrightarrow>
                   P orig"
  shows   "P orig"
proof -
  from assms have countable: "countable avoid"
    using no_limpt_imp_countable by blast

  from shifted_period_parallelogram_avoid[OF countable]
  obtain orig' where orig': "path_image (parallelogram_path orig' \<omega>1 \<omega>2) \<inter> avoid = {}"
      by blast
  define d where "d = \<omega>12_coords (orig - orig')"

  have "compact (closure (period_parallelogram orig))" for orig
    by (rule compact_closure_period_parallelogram)
  hence fin: "finite (closure (period_parallelogram orig) \<inter> avoid)" for orig
    using assms by (intro finite_not_islimpt_in_compact) auto

  from orig' have "P orig'"
    by (intro assms fin)
  have "P (orig' + (orig - orig'))"
    by (rule assms(2)) fact+
  thus ?thesis
    by (simp add: algebra_simps)
qed

end



text \<open>
  The standard lattice is one that has been rotated and scaled such that the first generator
  is 1 and the second generator \<open>\<tau>\<close> lies in the upper half plane.
\<close>
locale std_complex_lattice =
  fixes \<tau> :: complex (structure)
  assumes Im_\<tau>_pos: "Im \<tau> > 0"
begin

sublocale complex_lattice 1 \<tau>
  by standard (use Im_\<tau>_pos in \<open>auto elim!: Reals_cases simp: fundpair_def\<close>)

lemma winding_number_parallelogram_inside':
  assumes "w \<in> interior (period_parallelogram z)"
  shows   "winding_number (parallelogram_path z 1 \<tau>) w = 1"
  using winding_number_parallelogram_inside[OF assms] Im_\<tau>_pos by simp

end


subsection \<open>Doubly-periodic functions\<close>

text \<open>
  The following locale can be useful to prove that certain things respect the equivalence
  relation defined by the lattice: it shows that a doubly periodic function gives the same
  value for all equivalent points. Note that this is useful even for functions \<open>f\<close> that are only
  doubly quasi-periodic, since one might then still be able to prove that the function
  \<^term>\<open>\<lambda>z. f z = 0\<close> or \<^term>\<open>zorder f\<close> or \<^term>\<open>is_pole f\<close> are doubly periodic, so the zeros
  and poles of \<open>f\<close> are distributed according to the lattice symmetry.
\<close>

locale pre_complex_lattice_periodic = pre_complex_lattice +
  fixes f :: "complex \<Rightarrow> 'a"
  assumes f_periodic: "f (z + \<omega>1) = f z" "f (z + \<omega>2) = f z"
begin

lemma lattice_cong:
  assumes "rel x y"
  shows   "f x = f y"
proof -
  define z where "z = y - x"
  from assms have z: "z \<in> \<Lambda>"
    using pre_complex_lattice.rel_def pre_complex_lattice.rel_sym z_def by blast
  have "f (x + z) = f x"
    using z
  proof (induction arbitrary: x rule: lattice_induct)
    case (uminus w x)
    show ?case
      using uminus[of "x - w"] by simp
  qed (auto simp: f_periodic simp flip: add.assoc)
  thus ?thesis
    by (simp add: z_def)
qed

end

locale complex_lattice_periodic =
  complex_lattice \<omega>1 \<omega>2 + pre_complex_lattice_periodic \<omega>1 \<omega>2 f
  for \<omega>1 \<omega>2 :: complex and f :: "complex \<Rightarrow> 'a"
begin

lemma eval_to_fund_parallelogram: "f (to_fund_parallelogram z) = f z"
  by (rule lattice_cong) auto

end

locale complex_lattice_periodic_compose =
  complex_lattice_periodic \<omega>1 \<omega>2 f for \<omega>1 \<omega>2 :: complex and f :: "complex \<Rightarrow> 'a" +
fixes h :: "'a \<Rightarrow> 'b"
begin

sublocale compose: complex_lattice_periodic \<omega>1 \<omega>2 "\<lambda>z. h (f z)"
  by standard (auto intro!: arg_cong[of _ _ h] lattice_cong simp: rel_def)

end

end
