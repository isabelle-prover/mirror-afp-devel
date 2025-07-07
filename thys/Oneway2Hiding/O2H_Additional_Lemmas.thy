theory O2H_Additional_Lemmas
  imports Registers.Pure_States
begin

unbundle cblinfun_syntax
unbundle lattice_syntax

text \<open>This theory contains additional lemmas on summability, trace, tensor product, sandwiching 
operator, arithmetic-quadratic mean inequality, matrices with norm less or equal one, projections
and more.\<close>

text \<open>An additional lemma\<close>
lemma abs_summable_on_reindex:
  assumes \<open>inj_on h A\<close>
  shows \<open>g abs_summable_on (h ` A) \<longleftrightarrow> (g \<circ> h) abs_summable_on A\<close>
proof -
  have "(norm \<circ> g) summable_on (h ` A) \<longleftrightarrow> ((norm \<circ> g) \<circ> h) summable_on A"
    by (rule summable_on_reindex[OF assms])
  then show ?thesis unfolding comp_def by auto
qed


lemma abs_summable_norm:
  assumes \<open>f abs_summable_on A\<close>
  shows \<open>(\<lambda>x. norm (f x)) abs_summable_on A\<close>
  using assms by simp


lemma abs_summable_on_add:
  assumes \<open>f abs_summable_on A\<close> and \<open>g abs_summable_on A\<close>
  shows \<open>(\<lambda>x. f x + g x) abs_summable_on A\<close>
proof -
  from assms have \<open>(\<lambda>x. norm (f x) + norm (g x)) summable_on A\<close>
    using summable_on_add by blast
  then show ?thesis
    apply (rule Infinite_Sum.abs_summable_on_comparison_test')
    using norm_triangle_ineq by blast
qed

lemma sandwich_tc_has_sum:
  assumes "(f has_sum x) A"
  shows "((sandwich_tc \<rho> o f) has_sum sandwich_tc \<rho> x) A"
  unfolding o_def by (intro has_sum_bounded_linear[OF _ assms]) 
    (auto simp add: bounded_clinear.bounded_linear bounded_clinear_sandwich_tc)

lemma sandwich_tc_abs_summable_on:
  assumes "f abs_summable_on A"
  shows "(sandwich_tc \<rho> o f) abs_summable_on A"
  by (intro abs_summable_on_bounded_linear) 
    (auto simp add: assms bounded_clinear.bounded_linear bounded_clinear_sandwich_tc)

lemma trace_tc_abs_summable_on:
  assumes "f abs_summable_on A"
  shows "(trace_tc o f) abs_summable_on A"
  by (intro abs_summable_on_bounded_linear) (auto simp add: assms bounded_clinear.bounded_linear)



text \<open>Defining a self butterfly on trace class.\<close>

lemma trace_selfbutter_norm:
  "trace (selfbutter A) = norm A ^2"
  by (simp add: power2_norm_eq_cinner trace_butterfly)


definition tc_selfbutter where "tc_selfbutter a = tc_butterfly a a"

lemma norm_tc_selfbutter[simp]:
  "norm (tc_selfbutter a) = (norm a)^2"
  unfolding tc_selfbutter_def using norm_tc_butterfly by (metis power2_eq_square)

lemma trace_tc_sandwich_tc_isometry: 
  assumes "isometry U" 
  shows "trace_tc (sandwich_tc U A) = trace_tc A"
  using assms by transfer auto

lemma norm_sandwich_tc_unitary:
  assumes "isometry U" "\<rho> \<ge> 0"
  shows "norm (sandwich_tc U \<rho>) = norm \<rho>"
  using trace_tc_sandwich_tc_isometry[OF assms(1)] assms
  by (simp add: norm_tc_pos_Re sandwich_tc_pos)




text \<open>Lemmas on \<^const>\<open>trace_tc\<close>\<close>

lemma trace_tc_minus:
  "trace_tc (a-b) = trace_tc a - trace_tc b"
  by (metis add_implies_diff diff_add_cancel trace_tc_plus)

lemma trace_tc_sum:
  "trace_tc (sum a I) = (\<Sum>i\<in>I. trace_tc (a i))"
  by (simp add: from_trace_class_sum trace_sum trace_tc.rep_eq)


lemma selfbutter_sandwich:
  fixes A :: "'a ell2 \<Rightarrow>\<^sub>C\<^sub>L 'a ell2" and B :: "'a ell2"
  shows "selfbutter (A *\<^sub>V B) = sandwich A *\<^sub>V selfbutter B"
  by (simp add: butterfly_comp_cblinfun cblinfun_comp_butterfly sandwich_apply)

lemma tc_tensor_sum_left:
  "tc_tensor (sum g S) x = (\<Sum>i\<in>S. tc_tensor (g i) x)"
  by transfer (auto simp add: tensor_op_cbilinear.sum_left)

lemma tc_tensor_sum_right:
  "tc_tensor x (sum g S) = (\<Sum>i\<in>S. tc_tensor x (g i))"
  by transfer (auto simp add: tensor_op_cbilinear.sum_right)

lemma complex_of_real_abs: "complex_of_real \<bar>f\<bar> = \<bar>complex_of_real f\<bar>"
  by (simp add: abs_complex_def)




text \<open>Additional Lemmas on Tensors\<close>

lemma tensor_op_padding: 
  "(A \<otimes>\<^sub>o B) *\<^sub>V v = (A \<otimes>\<^sub>o id_cblinfun) *\<^sub>V (id_cblinfun \<otimes>\<^sub>o B) *\<^sub>V v"
  by (metis cblinfun_apply_cblinfun_compose cblinfun_compose_id_left cblinfun_compose_id_right 
      comp_tensor_op)

lemma tensor_op_padding': 
  "(A \<otimes>\<^sub>o B) *\<^sub>V v = (id_cblinfun \<otimes>\<^sub>o B) *\<^sub>V (A \<otimes>\<^sub>o id_cblinfun) *\<^sub>V v"
  by (subst cblinfun_apply_cblinfun_compose[symmetric], subst comp_tensor_op) auto

lemma tensor_op_left_minus: "(x - y) \<otimes>\<^sub>o b = x \<otimes>\<^sub>o b - y \<otimes>\<^sub>o b"
  by (metis ordered_field_class.sign_simps(10) tensor_op_left_add)

lemma tensor_op_right_minus: "b \<otimes>\<^sub>o (x - y) = b \<otimes>\<^sub>o x - b \<otimes>\<^sub>o y"
  by (metis ordered_field_class.sign_simps(10) tensor_op_right_add)

lemma id_cblinfun_selfbutter_tensor_ell2_right:
  "id_cblinfun \<otimes>\<^sub>o selfbutter (ket i) = (tensor_ell2_right (ket i)) o\<^sub>C\<^sub>L (tensor_ell2_right (ket i)*)"
  by (intro equal_ket) (auto simp add: tensor_ell2_ket[symmetric] tensor_op_ell2 
      tensor_ell2_scaleC2 tensor_ell2_scaleC1)



text \<open>A lot lof lemmas on limit processes with several functions.\<close>

lemma tendsto_Re:
  assumes "(f \<longlongrightarrow> x) F"
  shows "((\<lambda>x. Re (f x)) \<longlongrightarrow> Re x) F"
  using assms by (simp add: tendsto_Re)

lemma tendsto_tc_tensor:
  assumes "(f \<longlongrightarrow> x) F"
  shows "((\<lambda>x. tc_tensor (f x) a) \<longlongrightarrow> tc_tensor x a) F"
  using bounded_linear.tendsto[OF bounded_clinear.bounded_linear[OF bounded_clinear_tc_tensor_left] assms]
  by auto


lemma tc_tensor_has_sum:
  assumes "(f has_sum x) A"
  shows "((\<lambda>y. tc_tensor y a) o f has_sum tc_tensor x a) A"
  unfolding o_def using has_sum_bounded_linear bounded_clinear_tc_tensor_left 
    assms bounded_clinear.bounded_linear by blast


lemma Re_has_sum:
  assumes "(f has_sum x) A"
  shows "((\<lambda>n. Re n) o f has_sum Re x) A"
  by (metis assms(1) has_sum_Re has_sum_cong o_def)

text \<open>Relationship norm and condition\<close>

lemma norm_1_to_cond:
  fixes A :: "'a ell2 \<Rightarrow>\<^sub>C\<^sub>L 'a ell2"
  assumes "norm A \<le> 1"
  shows "A* o\<^sub>C\<^sub>L A \<le> id_cblinfun"
proof -
  have "norm (A *\<^sub>V \<Psi>) \<le> norm \<Psi>" for \<Psi> :: "'a ell2"
    by (meson assms basic_trans_rules(23) mult_left_le_one_le norm_cblinfun norm_ge_zero)
  then have ineq: "norm (A *\<^sub>V \<Psi>)^2 \<le> norm \<Psi>^2" for  \<Psi> :: "'a ell2" by simp 
  have left: "norm (A *\<^sub>V \<Psi>)^2 = \<Psi> \<bullet>\<^sub>C ((A* o\<^sub>C\<^sub>L A) *\<^sub>V \<Psi>)" for \<Psi>:: "'a ell2"
    by (simp add: cdot_square_norm cinner_adj_right)
  have right: "norm \<Psi>^2 = \<Psi> \<bullet>\<^sub>C (id_cblinfun *\<^sub>V \<Psi>)" for \<Psi>:: "'a ell2"
    by (simp add: cdot_square_norm)
  have "\<Psi> \<bullet>\<^sub>C ((A* o\<^sub>C\<^sub>L A) *\<^sub>V \<Psi>) \<le> \<Psi> \<bullet>\<^sub>C (id_cblinfun *\<^sub>V \<Psi>)" for \<Psi>:: "'a ell2"
    using ineq left right by (simp add: cnorm_le)
  then show "A* o\<^sub>C\<^sub>L A \<le> id_cblinfun" using cblinfun_leI by blast
qed

lemma cond_to_norm_1:
  fixes A :: "'a ell2 \<Rightarrow>\<^sub>C\<^sub>L 'a ell2"
  assumes "A* o\<^sub>C\<^sub>L A \<le> id_cblinfun"
  shows "norm A \<le> 1"
proof -
  have left: "norm (A *\<^sub>V \<Psi>)^2 = \<Psi> \<bullet>\<^sub>C ((A* o\<^sub>C\<^sub>L A) *\<^sub>V \<Psi>)" for \<Psi>:: "'a ell2"
    by (simp add: cdot_square_norm cinner_adj_right)
  have right: "norm \<Psi>^2 = \<Psi> \<bullet>\<^sub>C (id_cblinfun *\<^sub>V \<Psi>)" for \<Psi>:: "'a ell2"
    by (simp add: cdot_square_norm)
  have "\<Psi> \<bullet>\<^sub>C ((A* o\<^sub>C\<^sub>L A) *\<^sub>V \<Psi>) \<le> \<Psi> \<bullet>\<^sub>C (id_cblinfun *\<^sub>V \<Psi>)" for \<Psi>:: "'a ell2"
    using assms less_eq_cblinfun_def by blast
  then have ineq: "norm (A *\<^sub>V \<Psi>)^2 \<le> norm \<Psi>^2" for  \<Psi> :: "'a ell2"
    by (metis complex_of_real_mono_iff left right)
  then have "norm (A *\<^sub>V \<Psi>) \<le> norm \<Psi>" for \<Psi> :: "'a ell2" by simp
  then show "norm A \<le> 1" by (simp add: norm_cblinfun_bound)
qed


text \<open>Arithmetic mean - quadratic mean inequality (AM-QM)\<close>

lemma arith_quad_mean_ineq:
  fixes n::nat and x :: "nat \<Rightarrow> real"
  assumes "\<And>i. i\<in>I \<Longrightarrow> x i \<ge> 0"
  shows "(\<Sum>i\<in>I. x i)^2 \<le> (card I) * (\<Sum>i\<in>I. (x i) ^2)"
  using Cauchy_Schwarz_ineq_sum[of "(\<lambda>_. 1)" x I] by auto

lemma sqrt_binom:
  assumes "a \<ge> 0" "b \<ge> 0"
  shows "\<bar>a - b\<bar> = \<bar>sqrt a - sqrt b\<bar> * \<bar>sqrt a + sqrt b\<bar>"
  by (metis abs_mult abs_pos assms(1) assms(2) cross3_simps(11) real_sqrt_abs2 real_sqrt_mult 
      square_diff_square_factored)





text \<open>Lemmas on \<^const>\<open>sandwich_tc\<close>\<close>

lemma sandwich_tc_compose':
  "sandwich_tc (A o\<^sub>C\<^sub>L B) \<rho> = sandwich_tc A (sandwich_tc B \<rho>)"
  using sandwich_tc_compose unfolding o_def by metis


lemma sandwich_tc_sum:
  "sandwich_tc E (sum f A) = sum (sandwich_tc E o f) A"
  by (metis sandwich_tc_0_right sandwich_tc_plus sum_comp_morphism)


lemma isCont_sandwich_tc:
  "isCont (sandwich_tc A) x"
  by (intro linear_continuous_at) 
    (simp add: bounded_clinear.bounded_linear bounded_clinear_sandwich_tc)

lemma bounded_linear_trace_norm_sandwich_tc:
  "bounded_linear (\<lambda>y. trace_tc (sandwich_tc E y))"
  unfolding bounded_linear_def by (metis bounded_clinear.bounded_linear bounded_clinear_sandwich_tc 
      bounded_clinear_trace_tc bounded_linear_compose bounded_linear_def)

lemma sandwich_add1:
  "sandwich (A+B) C = sandwich A C + sandwich B C + A o\<^sub>C\<^sub>L C o\<^sub>C\<^sub>L B* + B o\<^sub>C\<^sub>L C o\<^sub>C\<^sub>L A*"
  by (simp add: adj_plus cblinfun_compose_add_left cblinfun_compose_add_right sandwich.rep_eq)

lemma sandwich_tc_add1:
  "sandwich_tc (A+B) C = sandwich_tc A C + sandwich_tc B C + 
  compose_tcl (compose_tcr B C) (A*) + compose_tcl (compose_tcr A C) (B*)"
  unfolding sandwich_tc_def 
  by (auto simp add: compose_tcr.add_left compose_tcl.add_left compose_tcl.add_right adj_plus)

lemma sandwich_add2:
  "sandwich A (B+C) = sandwich A B + sandwich A C"
  by (simp add: cblinfun.add_right)


text \<open>On the spaces of projections with and/or or events.\<close>

lemma splitting_Proj_and:
  assumes "is_Proj P" "is_Proj Q"
  shows "Proj (((P \<otimes>\<^sub>o id_cblinfun) *\<^sub>S \<top>) \<sqinter> ((id_cblinfun \<otimes>\<^sub>o Q) *\<^sub>S \<top>)) = P \<otimes>\<^sub>o Q"
proof -
  have tensor1: "(P \<otimes>\<^sub>o (id_cblinfun::'b ell2 \<Rightarrow>\<^sub>C\<^sub>L 'b ell2)) *\<^sub>S \<top> = (P *\<^sub>S \<top>) \<otimes>\<^sub>S \<top>"
    and tensor2: "((id_cblinfun::'a ell2 \<Rightarrow>\<^sub>C\<^sub>L 'a ell2) \<otimes>\<^sub>o Q) *\<^sub>S \<top> = \<top> \<otimes>\<^sub>S (Q *\<^sub>S \<top>)"
    by (auto simp add: Proj_on_own_range assms tensor_ccsubspace_via_Proj)

  have "((P \<otimes>\<^sub>o id_cblinfun) *\<^sub>S \<top>) \<sqinter> ((id_cblinfun \<otimes>\<^sub>o Q) *\<^sub>S \<top>) =
    ((P *\<^sub>S \<top>) \<otimes>\<^sub>S \<top>) \<sqinter> (\<top> \<otimes>\<^sub>S (Q *\<^sub>S \<top>))"
    using tensor1 tensor2 by auto
  also have "\<dots> = (P *\<^sub>S \<top>) \<otimes>\<^sub>S (Q *\<^sub>S \<top>)"
    by (smt (z3) Proj_image_leq Proj_o_Proj_subspace_right Proj_on_own_range Proj_range assms 
        boolean_algebra_cancel.inf1 cblinfun_assoc_left(2) cblinfun_image_id inf.orderE 
        inf_commute inf_le2 is_Proj_id is_Proj_tensor_op isometry_cblinfun_image_inf_distrib' 
        tensor_ccsubspace_image tensor_ccsubspace_top)
  finally have rew: "((P \<otimes>\<^sub>o id_cblinfun) *\<^sub>S \<top>) \<sqinter> ((id_cblinfun \<otimes>\<^sub>o Q) *\<^sub>S \<top>) = 
    ((P \<otimes>\<^sub>o Q) *\<^sub>S \<top>)"
    by (simp add: tensor_ccsubspace_image)
  show ?thesis unfolding rew 
    by (simp add: Proj_on_own_range assms(1) assms(2) is_Proj_tensor_op)
qed


lemma splitting_Proj_or:
  assumes "is_Proj P" "is_Proj Q"
  shows "Proj (((P \<otimes>\<^sub>o id_cblinfun) *\<^sub>S \<top>) \<squnion> ((id_cblinfun \<otimes>\<^sub>o Q) *\<^sub>S \<top>)) = 
  P \<otimes>\<^sub>o (id_cblinfun - Q) + id_cblinfun \<otimes>\<^sub>o Q"
proof -
  have tensor1: "(P \<otimes>\<^sub>o (id_cblinfun::'b ell2 \<Rightarrow>\<^sub>C\<^sub>L 'b ell2)) *\<^sub>S \<top> = (P *\<^sub>S \<top>) \<otimes>\<^sub>S \<top>"
    and tensor2: "((id_cblinfun::'a ell2 \<Rightarrow>\<^sub>C\<^sub>L 'a ell2) \<otimes>\<^sub>o Q) *\<^sub>S \<top> = \<top> \<otimes>\<^sub>S (Q *\<^sub>S \<top>)"
    by (auto simp add: Proj_on_own_range assms tensor_ccsubspace_via_Proj)
  have "((P \<otimes>\<^sub>o id_cblinfun) *\<^sub>S \<top>) \<squnion> ((id_cblinfun \<otimes>\<^sub>o Q) *\<^sub>S \<top>) = 
    ((P *\<^sub>S \<top>) \<otimes>\<^sub>S \<top>) \<squnion> (\<top> \<otimes>\<^sub>S (Q *\<^sub>S \<top>))" using tensor1 tensor2 by auto
  also have "\<dots> = ((P *\<^sub>S \<top>) \<otimes>\<^sub>S (Q *\<^sub>S \<top>)) \<squnion> ((P *\<^sub>S \<top>) \<otimes>\<^sub>S - (Q *\<^sub>S \<top>)) \<squnion> 
    ((P *\<^sub>S \<top>) \<otimes>\<^sub>S (Q *\<^sub>S \<top>)) \<squnion> (-(P *\<^sub>S \<top>) \<otimes>\<^sub>S (Q *\<^sub>S \<top>))"
    by (smt (z3) cblinfun_image_id cblinfun_image_sup complemented_lattice_class.sup_compl_top 
        ortho_tensor_ccsubspace_left ortho_tensor_ccsubspace_right sup_aci(2) tensor1 tensor2 
        tensor_ccsubspace_image)
  also have "\<dots> = ((P *\<^sub>S \<top>) \<otimes>\<^sub>S - (Q *\<^sub>S \<top>)) \<squnion> ((P *\<^sub>S \<top>) \<otimes>\<^sub>S (Q *\<^sub>S \<top>)) \<squnion> 
    (-(P *\<^sub>S \<top>) \<otimes>\<^sub>S (Q *\<^sub>S \<top>))" by (simp add: inf_sup_aci(5))
  also have "\<dots> = ((P *\<^sub>S \<top>) \<otimes>\<^sub>S - (Q *\<^sub>S \<top>)) \<squnion> (\<top> \<otimes>\<^sub>S (Q *\<^sub>S \<top>))"
    by (smt (verit, del_insts) cblinfun_image_id cblinfun_image_sup complemented_lattice_class.compl_sup_top 
        inf_sup_aci(5) ortho_tensor_ccsubspace_left sup_aci(2) tensor2 tensor_ccsubspace_image)
  finally have rew: "((P \<otimes>\<^sub>o id_cblinfun) *\<^sub>S \<top>) \<squnion> ((id_cblinfun \<otimes>\<^sub>o Q) *\<^sub>S \<top>) = 
    ((P \<otimes>\<^sub>o (id_cblinfun - Q)) *\<^sub>S \<top>) \<squnion> ((id_cblinfun \<otimes>\<^sub>o Q) *\<^sub>S \<top>)"
    by (simp add: Proj_on_own_range assms(2) range_cblinfun_code_def tensor2 
        tensor_ccsubspace_image uminus_Span_code)
  have "Proj (((P \<otimes>\<^sub>o id_cblinfun) *\<^sub>S \<top>) \<squnion> ((id_cblinfun \<otimes>\<^sub>o Q) *\<^sub>S \<top>)) =
    Proj ((P \<otimes>\<^sub>o (id_cblinfun - Q)) *\<^sub>S \<top>) + Proj ((id_cblinfun \<otimes>\<^sub>o Q) *\<^sub>S \<top>)" 
    unfolding rew by (intro Proj_sup) (smt (verit, del_insts) Proj_image_leq Proj_on_own_range
        Proj_ortho_compl assms(1) assms(2) ortho_tensor_ccsubspace_right orthogonal_spaces_leq_compl 
        range_cblinfun_code_def tensor2 tensor_ccsubspace_mono tensor_ccsubspace_via_Proj top_greatest 
        uminus_Span_code)
  also have "\<dots> = P \<otimes>\<^sub>o (id_cblinfun - Q) + id_cblinfun \<otimes>\<^sub>o Q"
    by (simp add: Proj_on_own_range assms(1) assms(2) is_Proj_tensor_op)
  finally show ?thesis by auto
qed


text \<open>Additional stuff\<close>

lemma Union_cong:
  assumes "\<And>i. i\<in>A \<Longrightarrow> f i = g i"
  shows "(\<Union>i\<in>A. f i) = (\<Union> i\<in>A. g i)"
  using assms by auto


lemma proj_ket_apply:
  "proj (ket i) *\<^sub>V ket j = (if i=j then ket i else 0)"
  by (metis Proj_fixes_image ccspan_superset' insertI1 kernel_Proj kernel_memberD 
      mem_ortho_ccspanI orthogonal_ket singletonD)





text \<open>Missing lemmas for Kraus maps\<close>
  (* This is a subset of the Missing2.thy file from the qrhl-tool Kraus map implementation. *)

lemma infsum_in_finite:
  assumes "finite F"
  assumes \<open>Hausdorff_space T\<close>
  assumes \<open>sum f F \<in> topspace T\<close>
  shows "infsum_in T f F = sum f F"
  using has_sum_in_finite[OF assms(1,3)]
  using assms(2) has_sum_in_infsum_in has_sum_in_unique summable_on_in_def by blast


lemma bdd_above_transform_mono_pos:
  assumes bdd: \<open>bdd_above ((\<lambda>x. g x) ` M)\<close>
  assumes gpos: \<open>\<And>x. x \<in> M \<Longrightarrow> g x \<ge> 0\<close>
  assumes mono: \<open>mono_on (Collect ((\<le>) 0)) f\<close>
  shows \<open>bdd_above ((\<lambda>x. f (g x)) ` M)\<close>
proof (cases \<open>M = {}\<close>)
  case True
  then show ?thesis
    by simp
next
  case False
  from bdd obtain B where B: \<open>g x \<le> B\<close> if \<open>x \<in> M\<close> for x
    by (meson bdd_above.unfold imageI)
  with gpos False have \<open>B \<ge> 0\<close>
    using dual_order.trans by blast
  have \<open>f (g x) \<le> f B\<close> if \<open>x \<in> M\<close> for x
    using mono _ _ B
    apply (rule mono_onD)
    by (auto intro!: gpos that  \<open>B \<ge> 0\<close>)
  then show ?thesis
    by fast
qed

lemma clinear_of_complex[iff]: \<open>clinear of_complex\<close>
  by (simp add: clinearI)

lemma inj_on_CARD_1[iff]: \<open>inj_on f X\<close> for X :: \<open>'a::CARD_1 set\<close>
  by (auto intro!: inj_onI)

unbundle no cblinfun_syntax
unbundle no lattice_syntax


end