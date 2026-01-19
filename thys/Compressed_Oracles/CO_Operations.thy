section \<open>\<open>CO_Operations\<close> – Definition of the compressed oracle and related unitaries\<close>

theory CO_Operations imports
  Complex_Bounded_Operators.Complex_L2 
  HOL.Map
  Registers.Quantum_Extra2
    
  Misc_Compressed_Oracle
  Function_At
begin

unbundle cblinfun_syntax

subsection \<open>\<open>function_oracle\<close> - Querying a fixed function\<close>

definition function_oracle :: \<open>('x \<Rightarrow> 'y::ab_group_add) \<Rightarrow> (('x \<times> 'y) ell2 \<Rightarrow>\<^sub>C\<^sub>L ('x \<times> 'y) ell2)\<close> where
  \<open>function_oracle h = classical_operator (\<lambda>(x,y). Some (x, y + h x))\<close>

lemma function_oracle_apply: \<open>function_oracle h (ket (x, y)) = ket (x, y + h x)\<close>
  unfolding function_oracle_def
  apply (subst classical_operator_ket)
  by (auto intro!: classical_operator_exists_inj injI simp: inj_map_total[unfolded o_def] case_prod_unfold)

lemma function_oracle_adj_apply: \<open>function_oracle h* *\<^sub>V ket (x, y) = ket (x, y - h x)\<close>
proof -
  define f where \<open>f = (\<lambda>(x,y). (x, y + h x))\<close>
  define g where \<open>g = (\<lambda>(x,y). (x, y - h x))\<close>
  have gf: \<open>g \<circ> f = id\<close> and fg: \<open>f \<circ> g = id\<close>
    by (auto simp: f_def g_def)
  have [iff]: \<open>inj f\<close>
    by (metis fg gf injI isomorphism_expand)
  have \<open>inv f = g\<close>
    using fg gf inv_unique_comp by blast
  have inv_map_f: \<open>inv_map (Some o f) = (Some o g)\<close>
    by (metis \<open>inj f\<close> \<open>inv f = g\<close> fg fun.set_map inj_imp_surj_inv inv_map_total surj_id)
  have \<open>function_oracle h* = classical_operator (Some o f)*\<close>
    by (simp add: function_oracle_def f_def case_prod_unfold o_def)
  also have \<open>\<dots> = classical_operator (Some o g)\<close>
    using inv_map_f by (simp add: classical_operator_adjoint function_oracle_def)
  also have \<open>\<dots> *\<^sub>V ket (x,y) = ket (x, y - h x)\<close>
    apply (subst classical_operator_ket)
     apply (metis classical_operator_exists_inj inj_map_inv_map inv_map_f) 
    by (simp add: g_def)
  finally show ?thesis
    by -
qed

lemma unitary_function_oracle[iff]: \<open>unitary (function_oracle h)\<close>
proof -
  have \<open>bij (\<lambda>x. (fst x, snd x + h (fst x)))\<close>
    apply (rule o_bij[where g=\<open>(\<lambda>x. (fst x, snd x - h (fst x)))\<close>])
    by auto
  then show ?thesis
    by (auto intro!: unitary_classical_operator[unfolded o_def]
        simp add: function_oracle_def case_prod_unfold )
qed

lemma norm_function_oracle[simp]: \<open>norm (function_oracle h) = 1\<close>
  by (intro norm_isometry unitary_isometry unitary_function_oracle)

lemma function_oracle_adj[simp]: \<open>function_oracle h* = function_oracle (\<lambda>x. - h x)\<close> for h :: \<open>'x \<Rightarrow> 'y::ab_group_add\<close>
  apply (rule equal_ket)
  by (auto simp: function_oracle_apply function_oracle_adj_apply)


subsection \<open>Setup for compressed oracles\<close>

consts trafo :: \<open>'a ell2 \<Rightarrow>\<^sub>C\<^sub>L 'a::{zero,finite} ell2\<close>
specification (trafo) 
  unitary_trafo[simp]: \<open>unitary trafo\<close>
  trafo_0[simp]: \<open>trafo *\<^sub>V ket 0 = uniform_superpos UNIV\<close>
proof -
  wlog \<open>CARD('a) \<ge> 2\<close>
  proof -
    have \<open>CARD('a) \<noteq> 0\<close>
      by simp
    with negation have \<open>CARD('a) = 1\<close>
      by presburger
    then have [simp]: \<open>UNIV = {0::'a}\<close>
      by (metis UNIV_I card_1_singletonE singletonD)
    have \<open>uniform_superpos UNIV = ket (0::'a)\<close>
      by (simp add: uniform_superpos_def2)
    then show ?thesis
      by (auto intro!: exI[where x=id_cblinfun])
  qed

  let ?uniform = \<open>uniform_superpos (UNIV :: 'a set)\<close>
  define \<alpha> where \<open>\<alpha> = complex_of_real (1 / sqrt (of_nat CARD('a)))\<close>
  define p p2 p4 a c where \<open>p = cinner ?uniform (ket (0::'a))\<close> and \<open>p2 = 1 - p * p\<close>
    and \<open>p4 = p2 * p2\<close> and \<open>a = (1+p) / p2\<close> and \<open>c = (-1-p) / p2\<close>
  define T :: \<open>'a update\<close> where
    \<open>T = a *\<^sub>C butterfly (ket 0) ?uniform + a *\<^sub>C butterfly ?uniform (ket 0)
       + c *\<^sub>C selfbutter (ket 0) + c *\<^sub>C selfbutter ?uniform + id_cblinfun\<close>
  have p\<alpha>: \<open>p = \<alpha>\<close>
    apply (simp add: p_def cinner_ket_right \<alpha>_def)
    apply transfer
    by simp
  have p20: \<open>p2 \<noteq> 0\<close>
    unfolding \<alpha>_def p2_def p\<alpha> using \<open>CARD('a) \<ge> 2\<close> apply auto
    by (smt (verit) complex_of_real_leq_1_iff numeral_nat_le_iff of_real_1 of_real_power power2_eq_square real_sqrt_pow2
        rel_simps(26) semiring_norm(69))
  have h1: \<open>a * p + c + 1 = 0\<close>
    using p20 apply (simp add: a_def c_def)
    by (metis add.assoc add_divide_distrib add_neg_numeral_special(8) diff_add_cancel divide_eq_minus_1_iff minus_diff_eq mult.commute mult_1 p2_def ring_class.ring_distribs(2) uminus_add_conv_diff)
  have h2: \<open>a + c * p = 1\<close>
    using p20 apply (simp add: c_def)
    by (metis a_def ab_group_add_class.ab_diff_conv_add_uminus add.commute add.inverse_inverse add_neg_numeral_special(8) add_right_cancel c_def divide_minus_left h1 minus_add_distrib mult_minus_left times_divide_eq_left)

  have [simp]: \<open>?uniform \<bullet>\<^sub>C ?uniform = 1\<close>
    by (simp add: cdot_square_norm norm_uniform_superpos)
  have [simp]: \<open>ket (0::'a) \<bullet>\<^sub>C ?uniform = cnj p\<close>
    by (simp add: p_def)

  have \<open>T *\<^sub>V ket 0 = (a * p + c + 1) *\<^sub>C ket 0 + (a + c * p) *\<^sub>C ?uniform\<close>
    unfolding T_def
    by (auto simp: cblinfun.add_left scaleC_add_left simp flip: p_def)
  also have \<open>\<dots> = ?uniform\<close>
    by (simp add: h1 h2)
  finally have 1: \<open>T *\<^sub>V ket 0 = ?uniform\<close>
    by -

  have scaleC_add_left': \<open>v + scaleC x w + scaleC y w = v + scaleC (x+y) w\<close> for x y and v w :: \<open>'a update\<close>
    by (simp add: scaleC_add_left)
  have sort: 
    \<open>v + x *\<^sub>C butterfly ?uniform (ket 0) + y *\<^sub>C selfbutter (ket 0) = v + y *\<^sub>C selfbutter (ket 0) + x *\<^sub>C butterfly ?uniform (ket 0)\<close> 
    \<open>v + x *\<^sub>C selfbutter ?uniform + y *\<^sub>C butterfly (ket 0) ?uniform = v + y *\<^sub>C butterfly (ket 0) ?uniform + x *\<^sub>C selfbutter ?uniform\<close>
    \<open>v + x *\<^sub>C selfbutter ?uniform + y *\<^sub>C butterfly ?uniform (ket 0) = v + y *\<^sub>C butterfly ?uniform (ket 0) + x *\<^sub>C selfbutter ?uniform\<close>
    \<open>v + x *\<^sub>C selfbutter ?uniform + y *\<^sub>C selfbutter (ket 0) = v + y *\<^sub>C selfbutter (ket 0) + x *\<^sub>C selfbutter ?uniform\<close>
    \<open>v + x *\<^sub>C butterfly (ket 0) ?uniform + y *\<^sub>C selfbutter (ket 0) = v + y *\<^sub>C selfbutter (ket 0) + x *\<^sub>C butterfly (ket 0) ?uniform\<close>
    \<open>v + x *\<^sub>C butterfly (ket 0) ?uniform + y *\<^sub>C butterfly ?uniform (ket 0) = v + y *\<^sub>C butterfly ?uniform (ket 0) + x *\<^sub>C butterfly (ket 0) ?uniform\<close>
    for v :: \<open>'a update\<close> and x y
    by auto

  have aux: \<open>x = 0 \<longleftrightarrow> x * p4 = 0\<close> for x
    by (simp add: p20 p4_def)

  have [simp]: \<open>cnj p = p\<close>
    by (simp add: \<alpha>_def p\<alpha>)
  have [simp]: \<open>cnj c = c\<close>
    by (simp add: c_def p2_def)
  have [simp]: \<open>cnj a = a\<close>
    by (simp add: a_def p2_def)
  have [simp]: \<open>p4 \<noteq> 0\<close>
    by (simp add: p20 p4_def)
  have [simp]: \<open>x * p4 / p2 = x * p2\<close> for x
    by (simp add: p4_def)

  have h3: \<open>2 * c + (2 * (a * (c * p)) + (a * a + c * c)) = 0\<close>
    apply (subst aux)
    apply (simp add: a_def c_def distrib_right distrib_left p20 add_divide_distrib 
        right_diff_distrib left_diff_distrib diff_divide_distrib
        flip: p4_def add.assoc
        del: mult_eq_0_iff vector_space_over_itself.scale_eq_0_iff)
    by (simp add: p4_def p2_def right_diff_distrib left_diff_distrib flip: add.assoc)
  have h4: \<open>2 * a + (2 * (a * c) + (a * a * p + c * c * p)) = 0\<close>
    apply (subst aux)
    apply (simp add: a_def c_def distrib_right distrib_left p20 add_divide_distrib 
        right_diff_distrib left_diff_distrib diff_divide_distrib
        flip: p4_def add.assoc
        del: mult_eq_0_iff vector_space_over_itself.scale_eq_0_iff)
    by (simp add: p4_def p2_def right_diff_distrib left_diff_distrib flip: add.assoc)

  have 2: \<open>T o\<^sub>C\<^sub>L T* = id_cblinfun\<close>
    unfolding T_def
    apply (simp add: cblinfun_compose_add_left cblinfun_compose_add_right adj_plus
        scaleC_add_right flip: p_def add.assoc mult.assoc)
    apply (simp add: sort scaleC_add_left' flip: scaleC_add_left)
    by (simp add: h3 h4)

  have 3: \<open>T* = T\<close>
    unfolding T_def
    by (auto simp: adj_plus)

  from 2 3 have 4: \<open>unitary T\<close>
    by (simp add: unitary_def)

  from 1 4 show ?thesis
    by auto
qed

text \<open>Set of total functions\<close>
definition \<open>total_functions = {f::'x\<rightharpoonup>'y. None \<notin> range f}\<close>

lemma total_functions_def2: \<open>total_functions = (comp Some) ` UNIV\<close>
proof -
  have \<open>x \<in> range ((\<circ>) Some)\<close> if \<open>None \<notin> range x\<close> for x :: \<open>'x \<Rightarrow> 'y option\<close>
    by (metis function_factors_right option.collapse range_eqI that)
  then show ?thesis
    unfolding total_functions_def by auto
qed

lemma total_functions_def3: \<open>total_functions = {f. dom f = UNIV}\<close>
  by (force simp add: total_functions_def)

lemma card_total_functions: \<open>card (total_functions :: ('x \<Rightarrow> 'y option) set) = CARD('y) ^ CARD('x::finite)\<close>
proof -
  have \<open>card (total_functions :: ('x \<Rightarrow> 'y option) set) = CARD ('x \<Rightarrow> 'y)\<close>
    unfolding total_functions_def2
    by (simp add: card_image fun.inj_map) 
  also have \<open>\<dots> = CARD('y) ^ CARD('x)\<close>
    by (simp add: card_fun)
  finally show ?thesis
    by -
qed

abbreviation superpos_total :: \<open>('x::finite \<Rightarrow> 'y::finite option) ell2\<close> where \<open>superpos_total \<equiv> uniform_superpos total_functions\<close>


text \<open>Sets up the locale for defining the compressed oracle.
We use a locale because the compressed oracle can depend on some arbitrary unitary \<open>trafo\<close>.
The choice of \<open>trafo\<close> usually doesn't matter; in this case the default transformation \<^const>\<open>trafo\<close> above
can be used.\<close>

locale compressed_oracle =
  fixes dummy_constant :: \<open>('x::finite \<times> 'y::{finite,ab_group_add}) itself\<close>
  fixes trafo :: \<open>'y::{finite,ab_group_add} ell2 \<Rightarrow>\<^sub>C\<^sub>L 'y ell2\<close>
  assumes unitary_trafo[simp]: \<open>unitary trafo\<close>
  assumes trafo_0: \<open>trafo *\<^sub>V ket 0 = uniform_superpos UNIV\<close>
  assumes y_cancel[simp]: \<open>(y::'y) + y = 0\<close>
begin

(* This is a hack for defining N. If we define \<^term>\<open>N\<close> directly as \<^term>\<open>\<open>N = CARD('y)\<close>\<close>, Isabelle adds a type parameter to the constant N *)
definition dummy2 :: \<open>'y update \<Rightarrow> ('y set \<Rightarrow> nat) \<Rightarrow> ('y set \<Rightarrow> nat)\<close>
  where \<open>dummy2 x y = y\<close>
definition N_def0: \<open>N = dummy2 trafo card UNIV\<close>
text \<open>\<^term>\<open>N\<close> is the cardinality of the oracle outputs. (Intuitively, \<^term>\<open>N = 2^n\<close> for an \<^term>\<open>n\<close>-bit output.\<close>
lemma N_def: \<open>N = CARD('y)\<close>
  by (simp add: dummy2_def N_def0)

lemma Nneq0[iff]: \<open>N \<noteq> 0\<close>
  by (simp add: N_def)

definition \<open>\<alpha> = complex_of_real (1 / sqrt (of_nat N))\<close>
  \<comment> \<open>We use this term very often, so this abbreviation comes in handy.\<close>

lemma (in compressed_oracle) uminus_y[simp]: \<open>- y = y\<close> for y :: 'y
  by (metis add.right_inverse group_cancel.add1 group_cancel.rule0 y_cancel)

subsection \<open>\<open>switch0\<close> - Operator exchanging \<^term>\<open>ket (Some 0)\<close> and \<^term>\<open>ket None\<close>\<close>

text \<open>\<^term>\<open>switch0\<close> maps \<^term>\<open>ket None\<close> to \<^term>\<open>ket (Some 0)\<close> and vice versa. 
  It leaves all other \<^term>\<open>ket (Some y)\<close> unchanged.\<close>
definition switch0 :: \<open>'y option update\<close> where
  \<open>switch0 = classical_operator (Some o Fun.swap (Some 0) None id)\<close>

lemma switch0_None[simp]: \<open>switch0 *\<^sub>V ket None = ket (Some 0)\<close>
  unfolding switch0_def classical_operator_ket_finite
  by auto

lemma switch0_0[simp]: \<open>switch0 *\<^sub>V ket (Some 0) = ket None\<close>
  unfolding switch0_def classical_operator_ket_finite
  by auto

lemma switch0_other: \<open>switch0 *\<^sub>V ket (Some x) = ket (Some x)\<close> if \<open>x \<noteq> 0\<close>
  unfolding switch0_def classical_operator_ket_finite
  using that by auto

lemma unitary_switch0[simp]: \<open>unitary switch0\<close>
  unfolding switch0_def
  apply (rule unitary_classical_operator)
  by auto

lemma switch0_adj[simp]: \<open>switch0* = switch0\<close>
  unfolding switch0_def
  apply (subst classical_operator_adjoint)
   apply simp
  by (simp add: inv_map_total)


subsection \<open>\<open>compress1\<close> - Operator to compress a single RO-output\<close>

text \<open>This unitary maps \<^term>\<open>ket None\<close> onto the uniform superposition of all \<^term>\<open>ket (Some y)\<close> and vice versa,
and leaves everything orthogonal to these unchanged.

This is the operation that deals with compressing a single oracle output.\<close>

definition compress1 :: \<open>'y option ell2 \<Rightarrow>\<^sub>C\<^sub>L 'y option ell2\<close> where
  \<open>compress1 = lift_op trafo o\<^sub>C\<^sub>L switch0 o\<^sub>C\<^sub>L (lift_op trafo)*\<close>

lemma uniform_superpos_y_sum: \<open>uniform_superpos UNIV = (\<Sum>d\<in>UNIV. \<alpha> *\<^sub>C ket (d::'y))\<close>
  apply (subst ell2_sum_ket)
  by (simp add: uniform_superpos.rep_eq \<alpha>_def N_def)

lemma compress1_None[simp]: \<open>compress1 *\<^sub>V ket None = (\<Sum>d\<in>UNIV. \<alpha> *\<^sub>C ket (Some d))\<close>
  by (auto simp: cblinfun.sum_right compress1_def lift_op_adj trafo_0 uniform_superpos_y_sum  cblinfun.scaleC_right)

lemma compress1_Some[simp]: \<open>compress1 *\<^sub>V ket (Some d) = 
      ket (Some d) - (\<Sum>d\<in>UNIV. \<alpha>\<^sup>2 *\<^sub>C ket (Some d)) + \<alpha> *\<^sub>C ket None\<close>
proof -
  define c where \<open>c e = cinner (ket e) (trafo* *\<^sub>V ket d)\<close> for e
  have c0: \<open>c 0 = \<alpha>\<close>
    apply (simp add: c_def cinner_adj_right trafo_0)
    by (simp add: \<alpha>_def N_def cinner_ket_right uniform_superpos.rep_eq)

  have \<open>compress1 *\<^sub>V ket (Some d) = lift_op trafo *\<^sub>V switch0 *\<^sub>V lift_ell2 *\<^sub>V trafo* *\<^sub>V ket d\<close>
    by (auto simp: compress1_def lift_op_adj)
  also have \<open>\<dots> = lift_op trafo *\<^sub>V switch0 *\<^sub>V lift_ell2 *\<^sub>V (\<Sum>e\<in>UNIV. c e *\<^sub>C ket e)\<close>
    by (simp add: c_def cinner_ket_left flip: ell2_sum_ket)
  also have \<open>\<dots> = lift_op trafo *\<^sub>V switch0 *\<^sub>V (\<Sum>e\<in>UNIV. c e *\<^sub>C ket (Some e))\<close>
    by (auto simp: cblinfun.sum_right cblinfun.scaleC_right)
  also have \<open>\<dots> = lift_op trafo *\<^sub>V switch0 *\<^sub>V ((\<Sum>e\<in>-{0}. c e *\<^sub>C ket (Some e)) + c 0 *\<^sub>C ket (Some 0))\<close>
    apply (subst asm_rl[of \<open>UNIV = insert 0 (-{0})\<close>])
    by (auto simp add: add.commute)
  also have \<open>\<dots> = lift_op trafo *\<^sub>V ((\<Sum>e\<in>-{0}. c e *\<^sub>C (switch0 *\<^sub>V ket (Some e))) + c 0 *\<^sub>C switch0 *\<^sub>V ket (Some 0))\<close>
    by (simp add: cblinfun.add_right cblinfun.scaleC_right cblinfun.sum_right)
  also have \<open>\<dots> = lift_op trafo *\<^sub>V ((\<Sum>e\<in>-{0}. c e *\<^sub>C ket (Some e)) + c 0 *\<^sub>C ket None)\<close>
    by (simp add: switch0_other)
  also have \<open>\<dots> = lift_op trafo *\<^sub>V ((\<Sum>e\<in>UNIV. c e *\<^sub>C ket (Some e)) - c 0 *\<^sub>C ket (Some 0) + c 0 *\<^sub>C ket None)\<close>
    by (simp add: Compl_eq_Diff_UNIV sum_diff)
  also have \<open>\<dots> = (\<Sum>e\<in>UNIV. c e *\<^sub>C lift_ell2 *\<^sub>V trafo *\<^sub>V ket e) - c 0 *\<^sub>C lift_ell2 *\<^sub>V trafo *\<^sub>V ket 0 + c 0 *\<^sub>C ket None\<close>
    by (simp add: cblinfun.add_right cblinfun.diff_right cblinfun.scaleC_right cblinfun.sum_right)
  also have \<open>\<dots> = lift_ell2 *\<^sub>V trafo *\<^sub>V (\<Sum>e\<in>UNIV. c e *\<^sub>C ket e) - c 0 *\<^sub>C lift_ell2 *\<^sub>V uniform_superpos UNIV + c 0 *\<^sub>C ket None\<close>
    by (simp add: trafo_0 cblinfun.scaleC_right cblinfun.sum_right)
  also have \<open>\<dots> = lift_ell2 *\<^sub>V trafo *\<^sub>V trafo* *\<^sub>V ket d - c 0 *\<^sub>C lift_ell2 *\<^sub>V uniform_superpos UNIV + c 0 *\<^sub>C ket None\<close>
    by (simp add: c_def cinner_ket_left flip: ell2_sum_ket)
  also have \<open>\<dots> = lift_ell2 *\<^sub>V (trafo o\<^sub>C\<^sub>L trafo*) *\<^sub>V ket d - c 0 *\<^sub>C lift_ell2 *\<^sub>V uniform_superpos UNIV + c 0 *\<^sub>C ket None\<close>
    by (metis cblinfun_apply_cblinfun_compose)
  also have \<open>\<dots> = lift_ell2 *\<^sub>V ket d - c 0 *\<^sub>C lift_ell2 *\<^sub>V uniform_superpos UNIV + c 0 *\<^sub>C ket None\<close>
    by auto 
  also have \<open>\<dots> = ket (Some d) - c 0 *\<^sub>C (\<Sum>d\<in>UNIV. \<alpha> *\<^sub>C ket (Some d)) + c 0 *\<^sub>C ket None\<close>
    by (auto simp: uniform_superpos_y_sum mult.commute scaleC_sum_right cblinfun.scaleC_right cblinfun.sum_right)
  also have \<open>\<dots> = ket (Some d) - (\<Sum>d\<in>UNIV. \<alpha>\<^sup>2 *\<^sub>C ket (Some d)) + \<alpha> *\<^sub>C ket None\<close>
    by (simp add: c0 power2_eq_square scaleC_sum_right)

  finally show ?thesis
    by -
qed

lemma unitary_compress1[simp]: \<open>unitary compress1\<close>
  by (simp add: compress1_def)

lemma compress1_adj[simp]: \<open>compress1* = compress1\<close>
  by (simp add: compress1_def cblinfun_compose_assoc)

lemma compress1_square: \<open>compress1 o\<^sub>C\<^sub>L compress1 = id_cblinfun\<close>
  by (metis compress1_adj unitary_compress1 unitary_def)

subsection \<open>\<open>compress\<close> - Operator for compressing the RO\<close>

text \<open>This is the unitary that maps between the compressed representation of the random oracle
(in which the initial state is \<^term>\<open>ket (\<lambda>_. None)\<close>) and the uncompressed one
(in which the initial state is the uniform superposition of all total functions).

It works by simply applying \<^const>\<open>compress1\<close> to each output separately.\<close>

definition compress :: \<open>('x \<rightharpoonup> 'y) update\<close>
  where \<open>compress = apply_every UNIV (\<lambda>_. compress1)\<close>

lemma unitary_compress[simp]: \<open>unitary compress\<close>
  by (simp add: compress_def apply_every_unitary)

lemma compress_selfinverse: \<open>compress o\<^sub>C\<^sub>L compress = id_cblinfun\<close>
  by (simp add: compress_def apply_every_mult compress1_square)

lemma compress_adj: \<open>compress* = compress\<close>
  by (simp add: compress_def apply_every_adj)

lemma compress_empty: \<open>compress *\<^sub>V ket Map.empty = superpos_total\<close>
proof -
  have *: \<open>apply_every M (\<lambda>_. compress1) *\<^sub>V ket Map.empty = 
      (\<Sum>f|dom f = M. ket f /\<^sub>R sqrt (CARD('y) ^ card M))\<close> for M :: \<open>'x set\<close>
  proof (use finite[of M] in induction)
    case empty
    then show ?case
      by simp
  next
    case (insert x F)
    have \<open>apply_every (insert x F) (\<lambda>_. compress1) *\<^sub>V ket Map.empty
      = function_at x compress1 *\<^sub>V apply_every F (\<lambda>_. compress1) *\<^sub>V ket Map.empty\<close>
      using insert.hyps by (simp add: apply_every_insert)
    also have \<open>\<dots> = function_at x compress1 *\<^sub>V (\<Sum>f | dom f = F. ket f /\<^sub>R sqrt (real (CARD('y) ^ card F)))\<close>
      by (simp add: insert.IH)
    also have \<open>\<dots> = (\<Sum>f | dom f = F. (function_at x compress1 *\<^sub>V ket f) /\<^sub>R sqrt (real (CARD('y) ^ card F)))\<close>
      by (simp add: cblinfun.real.scaleR_right cblinfun.sum_right)
    also have \<open>\<dots> = (\<Sum>f | dom f = F. (\<Sum>y\<in>UNIV. Rep_ell2 (compress1 *\<^sub>V ket (f x)) y *\<^sub>C ket (f(x := y))) /\<^sub>R sqrt (real (CARD('y) ^ card F)))\<close>
      by (simp add: function_at_ket)
    also have \<open>\<dots> = (\<Sum>f | dom f = F. (\<Sum>y\<in>UNIV. Rep_ell2 (compress1 *\<^sub>V ket None) y *\<^sub>C ket (f(x := y))) /\<^sub>R sqrt (real (CARD('y) ^ card F)))\<close>
      by (smt (verit) Finite_Cartesian_Product.sum_cong_aux domIff local.insert(2) mem_Collect_eq)
    also have \<open>\<dots> = (\<Sum>f | dom f = F. (\<Sum>y\<in>UNIV. Rep_ell2 (\<Sum>d\<in>UNIV. \<alpha> *\<^sub>C ket (Some d)) y *\<^sub>C ket (f(x := y))) /\<^sub>R sqrt (real (CARD('y) ^ card F)))\<close>
      by simp
    also have \<open>\<dots> = (\<Sum>f | dom f = F. (\<Sum>y\<in>UNIV. (\<Sum>d\<in>UNIV. \<alpha> *\<^sub>C Rep_ell2 (ket (Some d)) y) *\<^sub>C ket (f(x := y))) /\<^sub>R sqrt (real (CARD('y) ^ card F)))\<close>
      apply (subst complex_vector.linear_sum[where f=\<open>\<lambda>x. Rep_ell2 x _\<close>])
       apply (simp add: clinearI plus_ell2.rep_eq scaleC_ell2.rep_eq)
      apply (subst clinear.scaleC[where f=\<open>\<lambda>x. Rep_ell2 x _\<close>])
      by (simp_all add: clinearI plus_ell2.rep_eq scaleC_ell2.rep_eq)
    also have \<open>\<dots> = (\<Sum>f | dom f = F. (\<Sum>y\<in>UNIV. (if y = None then 0 else \<alpha>) *\<^sub>C ket (f(x := y))) /\<^sub>R sqrt (real (CARD('y) ^ card F)))\<close>
      apply (rule sum.cong, simp)
      subgoal for f
        apply (rule arg_cong[where f=\<open>\<lambda>x. x /\<^sub>R _\<close>])
        apply (rule sum.cong, simp)
        subgoal for y
          apply (subst sum_single[where i=\<open>the y\<close>])
          by (auto simp: ket.rep_eq)
        by -
      by -
    also have \<open>\<dots> = (\<Sum>f | dom f = F. (\<Sum>y\<in>range Some. \<alpha> *\<^sub>C ket (f(x := y))) /\<^sub>R sqrt (real (CARD('y) ^ card F)))\<close>
      apply (rule sum.cong, simp)
      apply (subst sum.mono_neutral_cong_right[where S=\<open>range Some\<close> and h=\<open>\<lambda>y. \<alpha> *\<^sub>C ket (_(x := y))\<close>])
      by auto
    also have \<open>\<dots> = (\<Sum>f | dom f = F. \<Sum>y\<in>range Some. \<alpha> *\<^sub>C ket (f(x := y)) /\<^sub>R sqrt (real (CARD('y) ^ card F)))\<close>
      by (simp add: scaleR_right.sum)
    also have \<open>\<dots> = (\<Sum>(f, y)\<in>{f. dom f = F} \<times> range Some. 
                         \<alpha> *\<^sub>C ket (f(x := y)) /\<^sub>R sqrt (real (CARD('y) ^ card F)))\<close>
      by (simp add: sum.cartesian_product)
    also have \<open>\<dots> = (\<Sum>(f, y)\<in>(\<lambda>f. (f(x:=None), f x)) ` {f. dom f = insert x F}. 
                         \<alpha> *\<^sub>C ket (f(x := y))) /\<^sub>R sqrt (real (CARD('y) ^ card F))\<close>
    proof -
      have 1: \<open>{f. dom f = F} \<times> range Some = (\<lambda>f. (f(x := None), f x)) ` {f. dom f = insert x F}\<close>
      proof (rule Set.set_eqI, rule iffI)
        fix z :: \<open>('x \<Rightarrow> 'a option) \<times> 'a option\<close>
        assume asm: \<open>z \<in> {f. dom f = F} \<times> range Some\<close>
        define f where \<open>f = (fst z)(x := snd z)\<close>
        have \<open>f \<in> {f. dom f = insert x F}\<close>
          using asm by (auto simp: f_def)
        moreover have \<open>(\<lambda>f. (f(x := None), f x)) f = z\<close>
          using asm insert.hyps by (auto simp add: f_def)
        ultimately show \<open>z \<in> (\<lambda>f. (f(x := None), f x)) ` {f. dom f = insert x F}\<close>
          by auto
      next
        fix z :: \<open>('x \<Rightarrow> 'a option) \<times> 'a option\<close>
        assume \<open>z \<in> (\<lambda>f. (f(x := None), f x)) ` {f. dom f = insert x F}\<close>
        then obtain f where \<open>dom f = insert x F\<close> and \<open>z = (\<lambda>f. (f(x := None), f x)) f\<close>
          by auto
        then show \<open>z \<in> {f. dom f = F} \<times> range Some\<close>
          using insert.hyps by auto
      qed
      show ?thesis
        apply (subst scaleR_right.sum)
        apply (rule sum.cong)
        using 1 by auto
    qed
    also have \<open>\<dots> = (\<Sum>f| dom f = insert x F. \<alpha> *\<^sub>C ket f) /\<^sub>R sqrt (real (CARD('y) ^ card F))\<close>
      apply (subst sum.reindex)
       apply auto
      by (smt (verit) fun_upd_idem_iff fun_upd_upd inj_on_def prod.simps(1))
    also have \<open>\<dots> = (\<Sum>f| dom f = insert x F. ket f /\<^sub>R sqrt (real (CARD('y) ^ card (insert x F))))\<close>
      by (simp add: card_insert_disjoint insert.hyps real_sqrt_mult \<alpha>_def N_def scaleR_scaleC
        divide_inverse_commute flip: scaleC_sum_right)
    finally show ?case
      by -
  qed

  have \<open>(\<Sum>f|dom f = UNIV. ket f /\<^sub>R sqrt (CARD('y) ^ CARD('x))) = (superpos_total :: ('x \<Rightarrow> 'y option) ell2)\<close>
    unfolding uniform_superpos_def2
    apply (rule sum.cong)
     apply (simp add: total_functions_def3)
    by (simp add: card_total_functions scaleR_scaleC)

  with *[of UNIV]
  show ?thesis
    by (simp flip: compress_def)
qed

subsection \<open>\<open>standard_query1\<close> - Operator for uncompressed query of a single RO-output\<close>

text \<open>We define the operation \<^term>\<open>standard_query1\<close> of querying the oracle, but first in the special case
  of an oracle that has no input register. That is, the oracle state consists of just one output value (or \<^term>\<open>None\<close>)
  and this value is simply added to the query output register.

  Roughly speaking, it thus is the unitary $\lvert y,h\<rangle> \<mapsto> \lvert y\<oplus>h, h\<rangle>$.
  In comparison, a ``normal'' oracle query would be defined by $\lvert x,y,h\<rangle> \<mapsto> \lvert x, y\<oplus>h(x), h\<rangle>$.
    
  That is: If one starts with a three-partite state \<^term>\<open>\<psi> \<otimes>\<^sub>s ket 0 \<otimes>\<^sub>s superpos_total\<close> and keeps performing
  operations $U_i$ on the parts 1, 2 of the state, interleaved with \<^term>\<open>standard_query1\<close> invocations on parts 2, 3,
  this is a simulation of starting with state \<^term>\<open>\<psi> \<otimes>\<^sub>s 0\<close> and performing $U_i$ interleaved with
  invocations of the unitary $\ket{y} \<mapsto> \ket{y \<oplus> h}$  on part 2 where $h$ is chosen uniformly at random
  in the beginning.

  When \<^term>\<open>h=None\<close>, there are various natural choices how to define the behavior of \<^term>\<open>standard_query1\<close>.
  This is because intuitively, this should not happen, because this operation intended to be 
  applied to uncompressed oracles which are superpositions of total functions.
  Yet, due to errors introduced by projecting onto invariants, one can get situations where this is not perfectly the case,
  so the behavior on \<^term>\<open>None\<close> matters. Here, we choose to let \<^term>\<open>standard_query1\<close> be the identity
  in that case.
\<close>

definition standard_query1 :: \<open>('y \<times> 'y option) update\<close> where
  \<open>standard_query1 = classical_operator (Some o (\<lambda>(y,z). case z of None \<Rightarrow> (y,None) | Some z' \<Rightarrow> (y + z', z)))\<close>

text \<open>The operation \<^term>\<open>standard_query1'\<close> is defined like \<^term>\<open>standard_query1\<close>
  (and the motivation and properties mentioned there also hold here),
  except that in the case \<^term>\<open>h=None\<close> (see discussion for \<^term>\<open>standard_query1\<close>), instead of being the
  identify, \<^term>\<open>standard_query1'\<close> returns the 0-vector (not \<^term>\<open>ket 0\<close>!).
  In particular, this operation is not a unitary which can make some things more awkward.
  But on the plus side, we can achieve better bounds in some situations when using \<^term>\<open>standard_query1'\<close>.\<close>

definition standard_query1' :: \<open>('y \<times> 'y option) update\<close> where
  \<open>standard_query1' = classical_operator (\<lambda>(y,z). case z of None \<Rightarrow> None | Some z' \<Rightarrow> Some (y + z', z))\<close>

lemma standard_query1_Some[simp]: \<open>standard_query1 *\<^sub>V ket (y, Some z) = ket (y + z, Some z)\<close>
  by (simp add: standard_query1_def classical_operator_ket_finite)

lemma standard_query1_None[simp]: \<open>standard_query1 *\<^sub>V ket (y, None) = ket (y, None)\<close>
  by (simp add: standard_query1_def classical_operator_ket_finite)

lemma standard_query1'_Some[simp]: \<open>standard_query1' *\<^sub>V ket (y, Some z) = ket (y + z, Some z)\<close>
  by (simp add: standard_query1'_def classical_operator_ket_finite)

lemma standard_query1'_None[simp]: \<open>standard_query1' *\<^sub>V ket (y, None) = 0\<close>
  by (simp add: standard_query1'_def classical_operator_ket_finite)

lemma unitary_standard_query1[simp]: \<open>unitary standard_query1\<close>
  unfolding standard_query1_def
  apply (rule unitary_classical_operator)
  apply (rule o_bij[where g=\<open>\<lambda>(y,z). case z of None \<Rightarrow> (y,None) | Some z' \<Rightarrow> (y - z', z)\<close>])
  by (auto intro!: ext simp: case_prod_beta cong del: option.case_cong split!: option.split option.split_asm)

lemma norm_standard_query1'[simp]: \<open>norm standard_query1' = 1\<close>
proof (rule order.antisym)
  show \<open>norm standard_query1' \<le> 1\<close>
    unfolding standard_query1'_def
    apply (rule classical_operator_norm_inj)
    by (auto simp: inj_map_def split!: option.split_asm)
  show \<open>norm standard_query1' \<ge> 1\<close>
    apply (rule cblinfun_norm_geqI[where x=\<open>ket (undefined, Some undefined)\<close>])
    by simp
qed


lemma standard_query1_selfinverse[simp]: \<open>standard_query1 o\<^sub>C\<^sub>L standard_query1 = id_cblinfun\<close>
proof -
  have *: \<open>(Some \<circ> (\<lambda>(y::'y, z). case z of None \<Rightarrow> (y, None) | Some z' \<Rightarrow> (y + z', z)) \<circ>\<^sub>m
      (Some \<circ> (\<lambda>(y, z). case z of None \<Rightarrow> (y, None) | Some z' \<Rightarrow> (y + z', z)))) = Some\<close>
    by (auto intro!: ext, rename_tac a b, case_tac b, auto)
  show ?thesis
    by (auto simp: standard_query1_def classical_operator_mult *)
qed

subsection \<open>\<open>standard_query\<close> - Operator for uncompressed query of the RO\<close>

text \<open>We can now define the operation of querying the (non-compressed) oracle,
  i.e., the operation $\lvert x,y,h\<rangle> \<mapsto> \lvert x, y\<oplus>h(x), h\<rangle>$.
  Most of the work has already been done when defining \<^const>\<open>standard_query1\<close>.
  We just need to apply \<^const>\<open>standard_query1\<close> onto the \<^term>\<open>Y\<close>-register and the \<^term>\<open>x\<close>-output 
  of the \<^term>\<open>H\<close>-register, where \<^term>\<open>x\<close> is the content of the \<^term>\<open>X\<close>-register (in the computational basis).

  The various lemmas below (e.g., \<open>standard_query_ket\<close>) show that this definition actually achieves this.

  That is: If one starts with a four-partite state \<^term>\<open>\<psi> \<otimes>\<^sub>s ket 0 \<otimes>\<^sub>s ket 0 \<otimes>\<^sub>s superpos_total\<close> and keeps performing
  operations $U_i$ on the parts 1--3 of the state, interleaved with \<^term>\<open>standard_query\<close> invocations on parts 2--4,
  this is a simulation of starting with state \<^term>\<open>\<psi> \<otimes>\<^sub>s 0\<close> and performing $U_i$ interleaved with
  invocations of the unitary $\ket{x, y} \<mapsto> \ket{x, y \<oplus> h(x)}$  on parts 2, 3 where $h$ is a function 
  chosen uniformly at random in the beginning.\<close>

definition standard_query :: \<open>('x \<times> 'y \<times> ('x \<rightharpoonup> 'y)) ell2 \<Rightarrow>\<^sub>C\<^sub>L ('x \<times> 'y \<times> ('x \<rightharpoonup> 'y)) ell2\<close> where
  \<open>standard_query = controlled_op (\<lambda>x. (Fst; Snd o function_at x) standard_query1)\<close>

text \<open>Analogous to \<^const>\<open>standard_query\<close> but using the variant \<^const>\<open>standard_query1'\<close>.\<close>

definition standard_query' :: \<open>('x \<times> 'y \<times> ('x \<rightharpoonup> 'y)) ell2 \<Rightarrow>\<^sub>C\<^sub>L ('x \<times> 'y \<times> ('x \<rightharpoonup> 'y)) ell2\<close> where
  \<open>standard_query' = controlled_op (\<lambda>x. (Fst; Snd o function_at x) standard_query1')\<close>

lemma standard_query_ket: \<open>standard_query *\<^sub>V (ket x \<otimes>\<^sub>s \<psi>) = ket x \<otimes>\<^sub>s ((Fst; Snd o function_at x) standard_query1 *\<^sub>V \<psi>)\<close>
  by (auto simp: standard_query_def)

lemma standard_query_ket_full_Some: 
  assumes \<open>H x = Some z\<close>
  shows \<open>standard_query *\<^sub>V (ket (x,y,H)) = ket (x, y + z, H)\<close>
proof -
  obtain H' where pf_xH: \<open>puncture_function x H = (H x, H')\<close>
    by (metis fst_puncture_function prod.collapse)
  have \<open>standard_query *\<^sub>V (ket (x,y,H)) = ket x \<otimes>\<^sub>s sandwich (id_cblinfun \<otimes>\<^sub>o function_at_U x) ((id \<otimes>\<^sub>r Fst) standard_query1) *\<^sub>V ket y \<otimes>\<^sub>s ket H\<close>
    by (simp add: standard_query_ket function_at_def pair_o_tensor_right pair_Fst_Snd
        pair_o_tensor_right unitary_sandwich_register pair_o_tensor_right
        register_tensor_distrib_right id_tensor_sandwich
        flip: tensor_ell2_ket)
  also have \<open>\<dots> = ket x \<otimes>\<^sub>s (id_cblinfun \<otimes>\<^sub>o function_at_U x) *\<^sub>V (id \<otimes>\<^sub>r Fst) standard_query1 *\<^sub>V (ket y \<otimes>\<^sub>s ket (H x) \<otimes>\<^sub>s ket H')\<close>
            (is \<open>_ = _ \<otimes>\<^sub>s _ *\<^sub>V ?R standard_query1 *\<^sub>V _\<close>)
    by (simp add: sandwich_apply' tensor_op_adjoint tensor_op_ell2 pf_xH assms flip: tensor_ell2_ket)
  also have \<open>\<dots> = ket x \<otimes>\<^sub>s (id_cblinfun \<otimes>\<^sub>o function_at_U x) *\<^sub>V (ket (y + z) \<otimes>\<^sub>s ket (H x) \<otimes>\<^sub>s ket H')\<close>
    apply (subst asm_rl[of \<open>(id \<otimes>\<^sub>r Fst) = assoc o Fst\<close>])
    subgoal by (auto intro!: tensor_extensionality simp add: register_tensor_is_register Fst_def)
    apply (simp add: Fst_def assoc_ell2_sandwich sandwich_apply' assoc_ell2'_tensor tensor_op_ell2 assms)
    apply (simp add: tensor_ell2_ket del: function_at_U_ket)
    by (simp add: assoc_ell2_tensor tensor_op_ell2 flip: tensor_ell2_ket)
  also have \<open>\<dots> = ket x \<otimes>\<^sub>s ket (y + z) \<otimes>\<^sub>s ket H\<close>
    apply (simp add: tensor_op_ell2 flip: tensor_ell2_ket)
    by (simp flip: pf_xH add: tensor_ell2_ket)
  finally show ?thesis
    by (simp add: tensor_ell2_ket)
qed

lemma standard_query_ket_full_None: 
  assumes \<open>H x = None\<close>
  shows \<open>standard_query *\<^sub>V (ket (x,y,H)) = ket (x, y, H)\<close>
proof -
  obtain H' where pf_xH: \<open>puncture_function x H = (H x, H')\<close>
    by (metis fst_puncture_function prod.collapse)
  have \<open>standard_query *\<^sub>V (ket (x,y,H)) = ket x \<otimes>\<^sub>s sandwich (id_cblinfun \<otimes>\<^sub>o function_at_U x) ((id \<otimes>\<^sub>r Fst) standard_query1) *\<^sub>V ket y \<otimes>\<^sub>s ket H\<close>
    by (simp add: standard_query_ket function_at_def pair_o_tensor_right pair_Fst_Snd
        pair_o_tensor_right unitary_sandwich_register pair_o_tensor_right
        register_tensor_distrib_right id_tensor_sandwich
        flip: tensor_ell2_ket)
  also have \<open>\<dots> = ket x \<otimes>\<^sub>s (id_cblinfun \<otimes>\<^sub>o function_at_U x) *\<^sub>V (id \<otimes>\<^sub>r Fst) standard_query1 *\<^sub>V ket y \<otimes>\<^sub>s ket (H x) \<otimes>\<^sub>s ket H'\<close>
    by (simp add: sandwich_apply' tensor_op_adjoint tensor_op_ell2 pf_xH assms flip: tensor_ell2_ket)
  also have \<open>\<dots> = ket x \<otimes>\<^sub>s (id_cblinfun \<otimes>\<^sub>o function_at_U x) *\<^sub>V ket y \<otimes>\<^sub>s ket (H x) \<otimes>\<^sub>s ket H'\<close>
    apply (subst asm_rl[of \<open>(id \<otimes>\<^sub>r Fst) = assoc o Fst\<close>])
    subgoal by (auto intro!: tensor_extensionality simp add: register_tensor_is_register Fst_def)
    apply (simp add: Fst_def assoc_ell2_sandwich sandwich_apply' assoc_ell2'_tensor tensor_op_ell2 assms)
    apply (simp add: tensor_ell2_ket del: function_at_U_ket)
    by (simp add: assoc_ell2_tensor tensor_op_ell2 flip: tensor_ell2_ket)
  also have \<open>\<dots> = ket x \<otimes>\<^sub>s ket y \<otimes>\<^sub>s ket H\<close>
    apply (simp add: tensor_op_ell2 flip: tensor_ell2_ket)
    by (simp flip: pf_xH add: tensor_ell2_ket)
  finally show ?thesis
    by (simp add: tensor_ell2_ket)
qed

lemma standard_query'_ket: \<open>standard_query' *\<^sub>V (ket x \<otimes>\<^sub>s \<psi>) = ket x \<otimes>\<^sub>s ((Fst; Snd o function_at x) standard_query1' *\<^sub>V \<psi>)\<close>
  by (auto simp: standard_query'_def)

lemma standard_query'_ket_full_Some: 
  assumes \<open>H x = Some z\<close>
  shows \<open>standard_query' *\<^sub>V (ket (x,y,H)) = ket (x, y + z, H)\<close>
proof -
  obtain H' where pf_xH: \<open>puncture_function x H = (H x, H')\<close>
    by (metis fst_puncture_function prod.collapse)
  have \<open>standard_query' *\<^sub>V (ket (x,y,H)) = ket x \<otimes>\<^sub>s sandwich (id_cblinfun \<otimes>\<^sub>o function_at_U x) ((id \<otimes>\<^sub>r Fst) standard_query1') *\<^sub>V ket y \<otimes>\<^sub>s ket H\<close>
    by (simp add: standard_query'_ket function_at_def pair_o_tensor_right pair_Fst_Snd
        pair_o_tensor_right unitary_sandwich_register pair_o_tensor_right
        register_tensor_distrib_right id_tensor_sandwich
        flip: tensor_ell2_ket)
  also have \<open>\<dots> = ket x \<otimes>\<^sub>s (id_cblinfun \<otimes>\<^sub>o function_at_U x) *\<^sub>V (id \<otimes>\<^sub>r Fst) standard_query1' *\<^sub>V (ket y \<otimes>\<^sub>s ket (H x) \<otimes>\<^sub>s ket H')\<close>
            (is \<open>_ = _ \<otimes>\<^sub>s _ *\<^sub>V ?R standard_query1' *\<^sub>V _\<close>)
    by (simp add: sandwich_apply' tensor_op_adjoint tensor_op_ell2 pf_xH assms flip: tensor_ell2_ket)
  also have \<open>\<dots> = ket x \<otimes>\<^sub>s (id_cblinfun \<otimes>\<^sub>o function_at_U x) *\<^sub>V (ket (y + z) \<otimes>\<^sub>s ket (H x) \<otimes>\<^sub>s ket H')\<close>
    apply (subst asm_rl[of \<open>(id \<otimes>\<^sub>r Fst) = assoc o Fst\<close>])
    subgoal by (auto intro!: tensor_extensionality simp add: register_tensor_is_register Fst_def)
    apply (simp add: Fst_def assoc_ell2_sandwich sandwich_apply' assoc_ell2'_tensor tensor_op_ell2 assms)
    apply (simp add: tensor_ell2_ket del: function_at_U_ket)
    by (simp add: assoc_ell2_tensor tensor_op_ell2 flip: tensor_ell2_ket)
  also have \<open>\<dots> = ket x \<otimes>\<^sub>s ket (y + z) \<otimes>\<^sub>s ket H\<close>
    apply (simp add: tensor_op_ell2 flip: tensor_ell2_ket)
    by (simp flip: pf_xH add: tensor_ell2_ket)
  finally show ?thesis
    by (simp add: tensor_ell2_ket)
qed

lemma standard_query'_ket_full_None: 
  assumes \<open>H x = None\<close>
  shows \<open>standard_query' *\<^sub>V (ket (x,y,H)) = 0\<close>
proof -
  obtain H' where pf_xH: \<open>puncture_function x H = (H x, H')\<close>
    by (metis fst_puncture_function prod.collapse)
  have \<open>standard_query' *\<^sub>V (ket (x,y,H)) = ket x \<otimes>\<^sub>s sandwich (id_cblinfun \<otimes>\<^sub>o function_at_U x) ((id \<otimes>\<^sub>r Fst) standard_query1') *\<^sub>V ket y \<otimes>\<^sub>s ket H\<close>
    by (simp add: standard_query'_ket function_at_def pair_o_tensor_right pair_Fst_Snd
        pair_o_tensor_right unitary_sandwich_register pair_o_tensor_right
        register_tensor_distrib_right id_tensor_sandwich
        flip: tensor_ell2_ket)
  also have \<open>\<dots> = ket x \<otimes>\<^sub>s (id_cblinfun \<otimes>\<^sub>o function_at_U x) *\<^sub>V (id \<otimes>\<^sub>r Fst) standard_query1' *\<^sub>V ket y \<otimes>\<^sub>s ket (H x) \<otimes>\<^sub>s ket H'\<close>
    by (simp add: sandwich_apply' tensor_op_adjoint tensor_op_ell2 pf_xH assms flip: tensor_ell2_ket)
  also have \<open>\<dots> = 0\<close>
    apply (subst asm_rl[of \<open>(id \<otimes>\<^sub>r Fst) = assoc o Fst\<close>])
    subgoal by (auto intro!: tensor_extensionality simp add: register_tensor_is_register Fst_def)
    apply (simp add: Fst_def assoc_ell2_sandwich sandwich_apply' assoc_ell2'_tensor tensor_op_ell2 assms)
    by (simp add: tensor_ell2_ket del: function_at_U_ket)
  finally show ?thesis
    by -
qed


lemma standard_query_selfinverse[simp]: \<open>standard_query o\<^sub>C\<^sub>L standard_query = id_cblinfun\<close>
  by (simp add: standard_query_def controlled_op_compose register_mult)

lemma unitary_standard_query[simp]: \<open>unitary standard_query\<close>
  by (auto simp: standard_query_def intro!: controlled_op_unitary register_unitary[of \<open>(_;_)\<close>])

lemma contracting_standard'_query[simp]: \<open>norm standard_query' = 1\<close>
proof (rule antisym)
  show \<open>norm standard_query' \<le> 1\<close>
    unfolding standard_query'_def
    apply (rule controlled_op_norm_leq)
    by (smt (verit) norm_standard_query1' norm_zero register_norm register_pair_def register_pair_is_register)
  show \<open>norm standard_query' \<ge> 1\<close>
    apply (rule cblinfun_norm_geqI[where x=\<open>ket (undefined, undefined, \<lambda>_. Some undefined)\<close>])
    apply (subst standard_query'_ket_full_Some)
    by auto
qed

subsection \<open>\<open>query1\<close> - Query the compressed oracle at a single output\<close>

text \<open>Before we formulate the compressed oracle itself, we define a scaled down version where
  the function in the oracle has only a single output (and there's no input register).
  Cf.~\<^const>\<open>standard_query1\<close>. This is done by decompressing the oracle register,
  applying \<^const>\<open>standard_query1\<close>, and then recompressing the oracle register.

  That is: If one starts with a three-partite state \<^term>\<open>\<psi> \<otimes>\<^sub>s ket 0 \<otimes>\<^sub>s ket None\<close> and keeps performing
  operations $U_i$ on the parts 1, 2 of the state, interleaved with \<^term>\<open>query1\<close> invocations on parts 2, 3,
  this is a simulation of starting with state \<^term>\<open>\<psi> \<otimes>\<^sub>s 0\<close> and performing $U_i$ interleaved with
  invocations of the unitary $\ket{y} \<mapsto> \ket{y \<oplus> h}$  on part 2 where $h$ is chosen uniformly at random
  in the beginning.\<close>

definition query1 where \<open>query1 = Snd compress1 o\<^sub>C\<^sub>L standard_query1 o\<^sub>C\<^sub>L Snd compress1\<close>

text \<open>The operation \<^term>\<open>query1'\<close> is defined like \<^term>\<open>query1\<close>
  (and the motivation and properties mentioned there also hold here),
  except that it is based on \<^term>\<open>standard_query1'\<close> instead of \<^term>\<open>standard_query1\<close>.
  See the comment at \<^term>\<open>standard_query1'\<close> for a discussion of the difference.\<close>


definition query1' where \<open>query1' = Snd compress1 o\<^sub>C\<^sub>L standard_query1' o\<^sub>C\<^sub>L Snd compress1\<close>



lemma unitary_query1[simp]: \<open>unitary query1\<close>
  by (auto simp: query1_def register_unitary intro!: unitary_cblinfun_compose)

lemma norm_query1'[simp]: \<open>norm query1' = 1\<close>
  unfolding query1'_def
  apply (subst norm_isometry_compose')
   apply (simp add: Snd_def comp_tensor_op compress1_square isometry_def tensor_op_adjoint)
  apply (subst norm_isometry_compose)
   apply (simp add: Snd_def comp_tensor_op compress1_square isometry_def tensor_op_adjoint)
  by simp

text \<open>The following lemmas give explicit formulas for the result of applying \<^const>\<open>query1\<close> and \<^const>\<open>query1'\<close>
  to computational basis states (\<^term>\<open>ket \<dots>\<close>). While the definitions of \<^const>\<open>query1\<close> and \<^const>\<open>query1'\<close>
  are useful for showing structural properties of these operations (e.g., the fact that
  they actually simulate a random oracle), for doing computations in concrete cases (e.g.,
  the preservation of an invariant), the explicit formulas can be more useful.\<close>

lemma query1_None: \<open>query1 *\<^sub>V ket (y,None) = 
                        \<alpha> *\<^sub>C (\<Sum>d\<in>UNIV. ket (y + d, Some d))
                        - \<alpha>^3 *\<^sub>C (\<Sum>y'\<in>UNIV. \<Sum>d\<in>UNIV. ket (y', Some d))
                        + \<alpha>\<^sup>2 *\<^sub>C (\<Sum>d\<in>UNIV. ket (d, None))\<close> (is \<open>_ = ?rhs\<close>)
proof -
  have [simp]: \<open>\<alpha> * \<alpha> = \<alpha>\<^sup>2\<close> \<open>\<alpha> * \<alpha>\<^sup>2 = \<alpha>^3\<close>
    by (simp_all add: power2_eq_square numeral_2_eq_2 numeral_3_eq_3)

  have aux: \<open>a = a' \<Longrightarrow> b = b' \<Longrightarrow> c = c' \<Longrightarrow> a - b + c = a' - b' + c'\<close> for a b c a' b' c' :: \<open>'z::group_add\<close>
    by simp

  have \<open>Snd compress1 *\<^sub>V ket (y, None) = (\<Sum>d\<in>UNIV. \<alpha> *\<^sub>C ket (y, Some d))\<close>
    by (simp add: query1_def tensor_ell2_scaleC2 tensor_ell2_sum_right flip: tensor_ell2_ket)
  also have \<open>standard_query1 *\<^sub>V \<dots> = (\<Sum>d\<in>UNIV. \<alpha> *\<^sub>C ket (y + d, Some d))\<close>
    by (simp add: cblinfun.scaleC_right cblinfun.sum_right)
  also have \<open>Snd compress1 *\<^sub>V \<dots> = 
          \<alpha> *\<^sub>C (\<Sum>d\<in>UNIV. (ket (y + d) \<otimes>\<^sub>s ket (Some d)))
        - \<alpha>^3 *\<^sub>C (\<Sum>z\<in>UNIV. \<Sum>d\<in>UNIV. (ket (y + z) \<otimes>\<^sub>s ket (Some d)))
        + \<alpha>\<^sup>2 *\<^sub>C (\<Sum>z\<in>UNIV. (ket (y + z) \<otimes>\<^sub>s ket None))\<close>
    by (simp add: tensor_ell2_diff2 tensor_ell2_add2 scaleC_add_right sum.distrib tensor_ell2_sum_right
        tensor_ell2_scaleC2 sum_subtractf scaleC_diff_right scaleC_sum_right cblinfun.scaleC_right
        cblinfun.sum_right
        flip: tensor_ell2_ket)
  also have \<open>\<dots> = ?rhs\<close>
    apply (rule aux)
    subgoal 
      by (simp add: tensor_ell2_ket)
    subgoal
      apply (subst sum.reindex_bij_betw[where h=\<open>\<lambda>d. y + d\<close> and T=UNIV]) 
      by (simp_all add: tensor_ell2_ket)
    subgoal
      apply simp
      apply (subst sum.reindex_bij_betw[where h=\<open>\<lambda>d. y + d\<close> and T=UNIV])
      by (simp_all add: tensor_ell2_ket)
    by -
  finally show ?thesis
    unfolding query1_def by simp
qed

lemma query1_Some: \<open>query1 *\<^sub>V ket (y, Some d) = 
        ket (y + d, Some d)
        + \<alpha> *\<^sub>C ket (y + d, None)
        - \<alpha>^3 *\<^sub>C (\<Sum>y'\<in>UNIV. ket (y', None))
        - \<alpha>\<^sup>2 *\<^sub>C (\<Sum>d'\<in>UNIV. ket (y + d', Some d'))
        - \<alpha>\<^sup>2 *\<^sub>C (\<Sum>d'\<in>UNIV. ket (y + d, Some d'))
        + \<alpha>\<^sup>2 *\<^sub>C (\<Sum>d'\<in>UNIV. ket (y, Some d'))
        + \<alpha>^4 *\<^sub>C (\<Sum>y'\<in>UNIV. \<Sum>d'\<in>UNIV. ket (y', Some d'))\<close>
    (is \<open>_ = ?rhs\<close>)
proof -
  have [simp]: \<open>\<alpha> * \<alpha> = \<alpha>\<^sup>2\<close> \<open>\<alpha>\<^sup>2 * \<alpha> = \<alpha>^3\<close>
    by (simp_all add: power2_eq_square numeral_2_eq_2 numeral_3_eq_3)

  have aux: \<open>a=a' \<Longrightarrow> b=b' \<Longrightarrow> c=c' \<Longrightarrow> d=d' \<Longrightarrow> e=e' \<Longrightarrow> f=f' \<Longrightarrow> g=g'
        \<Longrightarrow>  a' - e' + b' + g' - d' - c' + f' = a + b - c - d - e + f + g\<close> 
    for a b c d e f g a' b' c' d' e' f' g' :: \<open>'z::ab_group_add\<close>
    by simp

  have \<open>Snd compress1 *\<^sub>V ket (y, Some d) =
              ket (y, Some d) - \<alpha>\<^sup>2 *\<^sub>C (\<Sum>d'\<in>UNIV. ket (y, Some d')) + \<alpha> *\<^sub>C ket (y, None)\<close>
    by (simp add: query1_def tensor_ell2_scaleC2 tensor_ell2_diff2 tensor_ell2_add2 tensor_ell2_sum_right
             flip: tensor_ell2_ket scaleC_sum_right)
  also have \<open>standard_query1 *\<^sub>V \<dots> = ket (y + d, Some d) - \<alpha>\<^sup>2 *\<^sub>C (\<Sum>d'\<in>UNIV. ket (y + d', Some d')) + \<alpha> *\<^sub>C ket (y, None)\<close>
    by (simp add: cblinfun.add_right cblinfun.diff_right cblinfun.scaleC_right cblinfun.sum_right)
  also have \<open>Snd compress1 *\<^sub>V \<dots> = 
                ket (y + d, Some d)
                - \<alpha>\<^sup>2 *\<^sub>C (\<Sum>d'\<in>UNIV. ket (y + d, Some d'))
                + \<alpha> *\<^sub>C ket (y + d, None)
                + \<alpha>^4 *\<^sub>C (\<Sum>z\<in>UNIV. \<Sum>d'\<in>UNIV. ket (y + z, Some d'))
                - \<alpha>\<^sup>2 *\<^sub>C (\<Sum>d'\<in>UNIV. ket (y + d', Some d'))
                - \<alpha>^3 *\<^sub>C (\<Sum>z\<in>UNIV. ket (y + z, None))
                + \<alpha>\<^sup>2 *\<^sub>C (\<Sum>d'\<in>UNIV. ket (y, Some d'))\<close>
    by (simp add: tensor_ell2_diff2 tensor_ell2_add2 scaleC_add_right sum.distrib
        tensor_ell2_scaleC2 sum_subtractf scaleC_diff_right scaleC_sum_right tensor_ell2_sum_right
        cblinfun.add_right cblinfun.diff_right diff_diff_eq2 cblinfun.scaleC_right cblinfun.sum_right
        flip: tensor_ell2_ket diff_diff_eq scaleC_sum_right)
  also have \<open>\<dots> = ?rhs\<close>
    apply (rule aux)
    subgoal by rule
    subgoal by rule
    subgoal
      apply (subst sum.reindex_bij_betw[where h=\<open>\<lambda>d. y + d\<close> and T=UNIV])
      by simp_all
    subgoal by rule
    subgoal by rule
    subgoal by rule
    subgoal
      apply (subst sum.reindex_bij_betw[where h=\<open>\<lambda>d. y + d\<close> and T=UNIV])
      by simp_all
    by -
  finally show ?thesis
    unfolding query1_def by simp
qed

lemma query1: 
  shows \<open>query1 *\<^sub>V (ket yd) = (case yd of
    (y, None) \<Rightarrow> 
        \<alpha> *\<^sub>C (\<Sum>d\<in>UNIV. ket (y + d, Some d))
        - \<alpha>^3 *\<^sub>C (\<Sum>y'\<in>UNIV. \<Sum>d\<in>UNIV. ket (y', Some d))
        + \<alpha>\<^sup>2 *\<^sub>C (\<Sum>d\<in>UNIV. ket (d, None))
    | (y, Some d) \<Rightarrow>
        ket (y + d, Some d)
        + \<alpha> *\<^sub>C ket (y + d, None)
        - \<alpha>^3 *\<^sub>C (\<Sum>y'\<in>UNIV. ket (y', None))
        - \<alpha>\<^sup>2 *\<^sub>C (\<Sum>d'\<in>UNIV. ket (y + d', Some d'))
        - \<alpha>\<^sup>2 *\<^sub>C (\<Sum>d'\<in>UNIV. ket (y + d, Some d'))
        + \<alpha>\<^sup>2 *\<^sub>C (\<Sum>d'\<in>UNIV. ket (y, Some d'))
        + \<alpha>^4 *\<^sub>C (\<Sum>y'\<in>UNIV. \<Sum>d'\<in>UNIV. ket (y', Some d')))\<close>
  apply (cases yd, rename_tac y d) apply (case_tac d)
   apply (simp_all add: )
   apply (subst query1_None)
   apply simp
  apply (subst query1_Some)
  by simp


lemma query1'_None: \<open>query1' *\<^sub>V ket (y,None) = 
                        \<alpha> *\<^sub>C (\<Sum>d\<in>UNIV. ket (y + d, Some d))
                        - \<alpha>^3 *\<^sub>C (\<Sum>y'\<in>UNIV. \<Sum>d\<in>UNIV. ket (y', Some d))
                        + \<alpha>\<^sup>2 *\<^sub>C (\<Sum>d\<in>UNIV. ket (d, None))\<close> (is \<open>_ = ?rhs\<close>)
proof -
  have [simp]: \<open>\<alpha> * \<alpha> = \<alpha>\<^sup>2\<close> \<open>\<alpha> * \<alpha>\<^sup>2 = \<alpha>^3\<close>
    by (simp_all add: power2_eq_square numeral_2_eq_2 numeral_3_eq_3)

  have aux: \<open>a = a' \<Longrightarrow> b = b' \<Longrightarrow> c = c' \<Longrightarrow> a - b + c = a' - b' + c'\<close> for a b c a' b' c' :: \<open>'z::group_add\<close>
    by simp

  have \<open>Snd compress1 *\<^sub>V ket (y, None) = (\<Sum>d\<in>UNIV. \<alpha> *\<^sub>C ket (y, Some d))\<close>
    by (simp add: query1_def tensor_ell2_scaleC2 tensor_ell2_sum_right flip: tensor_ell2_ket)
  also have \<open>standard_query1' *\<^sub>V \<dots> = (\<Sum>d\<in>UNIV. \<alpha> *\<^sub>C ket (y + d, Some d))\<close>
    by (simp add: cblinfun.scaleC_right cblinfun.sum_right)
  also have \<open>Snd compress1 *\<^sub>V \<dots> = 
          \<alpha> *\<^sub>C (\<Sum>d\<in>UNIV. (ket (y + d) \<otimes>\<^sub>s ket (Some d)))
        - \<alpha>^3 *\<^sub>C (\<Sum>z\<in>UNIV. \<Sum>d\<in>UNIV. (ket (y + z) \<otimes>\<^sub>s ket (Some d)))
        + \<alpha>\<^sup>2 *\<^sub>C (\<Sum>z\<in>UNIV. (ket (y + z) \<otimes>\<^sub>s ket None))\<close>
    by (simp add: tensor_ell2_diff2 tensor_ell2_add2 scaleC_add_right sum.distrib tensor_ell2_sum_right
        tensor_ell2_scaleC2 sum_subtractf scaleC_diff_right scaleC_sum_right cblinfun.scaleC_right
        cblinfun.sum_right
        flip: tensor_ell2_ket)
  also have \<open>\<dots> = ?rhs\<close>
    apply (rule aux)
    subgoal 
      by (simp add: tensor_ell2_ket)
    subgoal
      apply (subst sum.reindex_bij_betw[where h=\<open>\<lambda>d. y + d\<close> and T=UNIV]) 
      by (simp_all add: tensor_ell2_ket)
    subgoal
      apply simp
      apply (subst sum.reindex_bij_betw[where h=\<open>\<lambda>d. y + d\<close> and T=UNIV])
      by (simp_all add: tensor_ell2_ket)
    by -
  finally show ?thesis
    unfolding query1'_def by simp
qed

lemma query1'_Some: \<open>query1' *\<^sub>V ket (y, Some d) = 
        ket (y + d, Some d)
        + \<alpha> *\<^sub>C ket (y + d, None)
        - \<alpha>^3 *\<^sub>C (\<Sum>y'\<in>UNIV. ket (y', None))
        - \<alpha>\<^sup>2 *\<^sub>C (\<Sum>d'\<in>UNIV. ket (y + d', Some d'))
        - \<alpha>\<^sup>2 *\<^sub>C (\<Sum>d'\<in>UNIV. ket (y + d, Some d'))
        + \<alpha>^4 *\<^sub>C (\<Sum>y'\<in>UNIV. \<Sum>d'\<in>UNIV. ket (y', Some d'))\<close>
    (is \<open>_ = ?rhs\<close>)
proof -
  have [simp]: \<open>\<alpha> * \<alpha> = \<alpha>\<^sup>2\<close> \<open>\<alpha>\<^sup>2 * \<alpha> = \<alpha>^3\<close>
    by (simp_all add: power2_eq_square numeral_2_eq_2 numeral_3_eq_3)

  have aux: \<open>a=a' \<Longrightarrow> b=b' \<Longrightarrow> c=c' \<Longrightarrow> d=d' \<Longrightarrow> e=e' \<Longrightarrow> g=g'
        \<Longrightarrow>  a' - e' + b' + g' - d' - c' = a + b - c - d - e + g\<close> 
    for a b c d e f g a' b' c' d' e' f' g' :: \<open>'z::ab_group_add\<close>
    by simp

  have \<open>Snd compress1 *\<^sub>V ket (y, Some d) =
              ket (y, Some d) - \<alpha>\<^sup>2 *\<^sub>C (\<Sum>d'\<in>UNIV. ket (y, Some d')) + \<alpha> *\<^sub>C ket (y, None)\<close>
    by (simp add: query1_def tensor_ell2_scaleC2 tensor_ell2_diff2 tensor_ell2_add2 tensor_ell2_sum_right
             flip: tensor_ell2_ket scaleC_sum_right)
  also have \<open>standard_query1' *\<^sub>V \<dots> = ket (y + d, Some d) - \<alpha>\<^sup>2 *\<^sub>C (\<Sum>d'\<in>UNIV. ket (y + d', Some d'))\<close>
    by (simp add: cblinfun.add_right cblinfun.diff_right cblinfun.scaleC_right cblinfun.sum_right)
  also have \<open>Snd compress1 *\<^sub>V \<dots> = 
                ket (y + d, Some d)
                - \<alpha>\<^sup>2 *\<^sub>C (\<Sum>d'\<in>UNIV. ket (y + d, Some d'))
                + \<alpha> *\<^sub>C ket (y + d, None)
                + \<alpha>^4 *\<^sub>C (\<Sum>z\<in>UNIV. \<Sum>d'\<in>UNIV. ket (y + z, Some d'))
                - \<alpha>\<^sup>2 *\<^sub>C (\<Sum>d'\<in>UNIV. ket (y + d', Some d'))
                - \<alpha>^3 *\<^sub>C (\<Sum>z\<in>UNIV. ket (y + z, None))\<close>
    by (simp add: tensor_ell2_diff2 tensor_ell2_add2 scaleC_add_right sum.distrib tensor_ell2_sum_right
        tensor_ell2_scaleC2 sum_subtractf scaleC_diff_right scaleC_sum_right cblinfun.sum_right
        cblinfun.add_right cblinfun.diff_right diff_diff_eq2 cblinfun.scaleC_right
        flip: tensor_ell2_ket diff_diff_eq scaleC_sum_right)
  also have \<open>\<dots> = ?rhs\<close>
    apply (rule aux)
    subgoal by rule
    subgoal by rule
    subgoal
      apply (subst sum.reindex_bij_betw[where h=\<open>\<lambda>d. y + d\<close> and T=UNIV])
      by simp_all
    subgoal by rule
    subgoal by rule
    subgoal
      apply (subst sum.reindex_bij_betw[where h=\<open>\<lambda>d. y + d\<close> and T=UNIV])
      by simp_all
    by -
  finally show ?thesis
    unfolding query1'_def by simp
qed

lemma query1': 
  shows \<open>query1' *\<^sub>V (ket yd) = (case yd of
    (y, None) \<Rightarrow> 
        \<alpha> *\<^sub>C (\<Sum>d\<in>UNIV. ket (y + d, Some d))
        - \<alpha>^3 *\<^sub>C (\<Sum>y'\<in>UNIV. \<Sum>d\<in>UNIV. ket (y', Some d))
        + \<alpha>\<^sup>2 *\<^sub>C (\<Sum>d\<in>UNIV. ket (d, None))
    | (y, Some d) \<Rightarrow>
        ket (y + d, Some d)
        + \<alpha> *\<^sub>C ket (y + d, None)
        - \<alpha>^3 *\<^sub>C (\<Sum>y'\<in>UNIV. ket (y', None))
        - \<alpha>\<^sup>2 *\<^sub>C (\<Sum>d'\<in>UNIV. ket (y + d', Some d'))
        - \<alpha>\<^sup>2 *\<^sub>C (\<Sum>d'\<in>UNIV. ket (y + d, Some d'))
        + \<alpha>^4 *\<^sub>C (\<Sum>y'\<in>UNIV. \<Sum>d'\<in>UNIV. ket (y', Some d')))\<close>
  apply (cases yd, rename_tac y d) apply (case_tac d)
   apply (simp_all add: )
   apply (subst query1'_None)
   apply simp
  apply (subst query1'_Some)
  by simp

subsection \<open>\<open>query\<close> - Query the compressed oracle\<close>


text \<open>
  We define the compressed oracle itself.
  
  Analogous to the definition of \<^const>\<open>query1\<close> above (decompress, \<^const>\<open>standard_query1\<close>, recompress), 
  the compressed oracle is defined by decompressing the oracle register (now a superposition of functions),
  applying \<^const>\<open>standard_query\<close>, and recompressing.

  That is: If one starts with a four-partite state \<^term>\<open>\<psi> \<otimes>\<^sub>s ket 0 \<otimes>\<^sub>s ket 0 \<otimes>\<^sub>s ket None\<close> and keeps performing
  operations $U_i$ on the parts 1--3 of the state, interleaved with \<^term>\<open>query\<close> invocations on parts 2--4,
  this is a simulation of starting with state \<^term>\<open>\<psi> \<otimes>\<^sub>s 0\<close> and performing $U_i$ interleaved with
  invocations of the unitary $\ket{x, y} \<mapsto> \ket{x, y \<oplus> h(x)}$  on parts 2, 3 where $h$ is a function 
  chosen uniformly at random in the beginning.

  Note that there is an alternative way of defining the compressed oracle, namely by decompressing
  not the whole oracle register, but only the specific oracle output that we are querying.
  This is closer to an efficient implementation of the compressed oracle.
  We show that this definition is equivalent below (lemma \<open>query_local\<close>).\<close>

definition query where \<open>query = reg_3_3 compress o\<^sub>C\<^sub>L standard_query o\<^sub>C\<^sub>L reg_3_3 compress\<close>

text \<open>\<^term>\<open>query'\<close> is defined like \<^const>\<open>query\<close>, except that it's based on 
  \<^const>\<open>standard_query1'\<close> instead of \<^const>\<open>standard_query1\<close>.
  See the discussion of \<^const>\<open>standard_query1'\<close> for the difference.\<close>

definition query' where \<open>query' = reg_3_3 compress o\<^sub>C\<^sub>L standard_query' o\<^sub>C\<^sub>L reg_3_3 compress\<close>


lemma unitary_query[simp]: \<open>unitary query\<close>
  by (auto simp: query_def register_unitary intro!: unitary_cblinfun_compose)

lemma norm_query[simp]: \<open>norm query = 1\<close>
  using norm_isometry unitary_isometry unitary_query by blast

lemma norm_query'[simp]: \<open>norm query' = 1\<close>
  unfolding query'_def
  apply (subst norm_isometry_compose')
   apply (subst register_adjoint[OF register_3_3, symmetric])
   apply (rule register_isometry[OF register_3_3])
   apply simp
  apply (subst norm_isometry_compose)
   apply (rule register_isometry[OF register_3_3])
   apply simp
  by simp

lemma query_local_generic: 
  \<comment> \<open>A generalization of lemmas \<open>query_local\<close> and \<open>query'_local\<close> below.
      We prove this first because it avoids a duplication of the proof because \<open>query_local\<close> and \<open>query'_local\<close>
      have very similar proofs.\<close>
  fixes query :: \<open>('x \<times> 'y \<times> ('x \<rightharpoonup> 'y)) update\<close> and query1
    and standard_query and standard_query1
  assumes query_def: \<open>query = reg_3_3 compress o\<^sub>C\<^sub>L standard_query o\<^sub>C\<^sub>L reg_3_3 compress\<close>
  assumes query1_def: \<open>query1 = Snd compress1 o\<^sub>C\<^sub>L standard_query1 o\<^sub>C\<^sub>L Snd compress1\<close>
  assumes standard_query_ket: \<open>\<And>x \<psi>. standard_query *\<^sub>V (ket x \<otimes>\<^sub>s \<psi>) = ket x \<otimes>\<^sub>s ((Fst; Snd o function_at x) standard_query1 *\<^sub>V \<psi>)\<close>
  shows \<open>query = controlled_op (\<lambda>x. (Fst; Snd o function_at x) query1)\<close>
proof -
  have \<open>query *\<^sub>V ket x \<otimes>\<^sub>s \<psi> = controlled_op (\<lambda>x. (Fst;Snd \<circ> function_at x) query1) *\<^sub>V ket x \<otimes>\<^sub>s \<psi>\<close> for x \<psi>
  proof -
    have aux: \<open>(Snd ((Fst;Snd \<circ> function_at x) Q) o\<^sub>C\<^sub>L reg_3_3 (apply_every M R) :: ('x\<times>'y\<times>('x\<rightharpoonup>'y)) update)
              = reg_3_3 (apply_every M R) o\<^sub>C\<^sub>L Snd ((Fst;Snd \<circ> function_at x) Q)\<close> 
      if \<open>x\<notin>M\<close> for M and Q :: \<open>('y \<times> 'y option) update\<close> and R
      using finite[of M] that
    proof induction
      case empty
      show ?case 
        by simp
    next
      case (insert y F)
      have \<open>(Snd ((Fst;Snd \<circ> function_at x) Q) o\<^sub>C\<^sub>L reg_3_3 (apply_every (insert y F) R) :: ('x\<times>'y\<times>('x\<rightharpoonup>'y)) update) =
             ((Snd o (Fst;Snd \<circ> function_at x)) Q o\<^sub>C\<^sub>L (reg_3_3 o function_at y) (R y)) o\<^sub>C\<^sub>L reg_3_3 (apply_every F R)\<close>
        by (simp add: apply_every_insert insert register_mult[of reg_3_3, symmetric] cblinfun_compose_assoc)
      also have \<open>\<dots>  = (reg_3_3 \<circ> function_at y) (R y) o\<^sub>C\<^sub>L ((Snd ((Fst;Snd \<circ> function_at x) Q)) o\<^sub>C\<^sub>L reg_3_3 (apply_every F R))\<close>
        apply (subst swap_registers[of \<open>Snd o _\<close> \<open>reg_3_3 o _\<close>])
        using insert apply (simp add: reg_3_3_def add: comp_assoc)
        by (simp add: cblinfun_compose_assoc)
      also have \<open>\<dots> = ((reg_3_3 \<circ> function_at y) (R y) o\<^sub>C\<^sub>L reg_3_3 (apply_every F R)) o\<^sub>C\<^sub>L Snd ((Fst;Snd \<circ> function_at x) Q)\<close>
        apply (subst insert.IH)
        using insert by (auto simp: cblinfun_compose_assoc)
      also have \<open>\<dots> = (reg_3_3 (apply_every (insert y F) R)) o\<^sub>C\<^sub>L Snd ((Fst;Snd \<circ> function_at x) Q)\<close>
        by (simp add: apply_every_insert insert register_mult[of reg_3_3, symmetric] cblinfun_compose_assoc)
      finally show ?case
        by -
    qed

    have \<open>query *\<^sub>V (ket x \<otimes>\<^sub>s \<psi>) = reg_3_3 compress *\<^sub>V standard_query *\<^sub>V reg_3_3 compress *\<^sub>V (ket x \<otimes>\<^sub>s \<psi>)\<close>
      by (simp add: query_def)
    also have \<open>\<dots> = reg_3_3 compress *\<^sub>V
            standard_query *\<^sub>V (ket x \<otimes>\<^sub>s Snd compress *\<^sub>V \<psi>)\<close>
      apply (rule arg_cong[where f=\<open>\<lambda>x. _ *\<^sub>V _ *\<^sub>V x\<close>])
      by (auto simp: reg_3_3_def)
    also have \<open>\<dots> = reg_3_3 compress *\<^sub>V
            (ket x \<otimes>\<^sub>s (((Fst; Snd o function_at x) standard_query1 *\<^sub>V Snd compress *\<^sub>V \<psi>)))\<close>
      by (simp add: standard_query_ket)
    also have \<open>\<dots> = reg_3_3 compress *\<^sub>V
            (Snd ((Fst; Snd o function_at x) standard_query1)) *\<^sub>V (ket x \<otimes>\<^sub>s Snd compress *\<^sub>V \<psi>)\<close>
      by auto
    also have \<open>\<dots> = reg_3_3 compress *\<^sub>V
            (Snd ((Fst; Snd o function_at x) standard_query1)) *\<^sub>V reg_3_3 compress *\<^sub>V (ket x \<otimes>\<^sub>s \<psi>)\<close>
      apply (rule arg_cong[where f=\<open>\<lambda>x. _ *\<^sub>V _ *\<^sub>V x\<close>])
      by (auto simp: reg_3_3_def)
    also have \<open>\<dots> = (reg_3_3 compress o\<^sub>C\<^sub>L (Snd ((Fst; Snd o function_at x) standard_query1)) o\<^sub>C\<^sub>L reg_3_3 compress) *\<^sub>V (ket x \<otimes>\<^sub>s \<psi>)\<close>
      by auto
    also have \<open>\<dots> = (reg_3_3 (function_at x compress1) o\<^sub>C\<^sub>L (Snd ((Fst; Snd o function_at x) standard_query1)) o\<^sub>C\<^sub>L reg_3_3 (function_at x compress1)) *\<^sub>V (ket x \<otimes>\<^sub>s \<psi>)\<close>
      (is \<open>?lhs *\<^sub>V _ = ?rhs *\<^sub>V _\<close>)
    proof -
      have [simp]: \<open>insert x (- {x}) = UNIV\<close> for x :: 'x
        by auto
      have \<open>?lhs = reg_3_3 (apply_every ({x} \<union> -{x}) (\<lambda>_. compress1))
             o\<^sub>C\<^sub>L Snd ((Fst;Snd \<circ> function_at x) standard_query1)
             o\<^sub>C\<^sub>L reg_3_3 (apply_every (-{x} \<union> {x}) (\<lambda>_. compress1))\<close>
        by (simp add: compress_def)
      also have \<open>\<dots> = reg_3_3 (function_at x compress1) o\<^sub>C\<^sub>L reg_3_3 (apply_every (- {x}) (\<lambda>_. compress1))
         o\<^sub>C\<^sub>L (  Snd ((Fst;Snd \<circ> function_at x) standard_query1) o\<^sub>C\<^sub>L reg_3_3 (apply_every (- {x}) (\<lambda>_. compress1))  )
         o\<^sub>C\<^sub>L reg_3_3 (function_at x compress1)\<close>
        apply (subst apply_every_split[symmetric], simp)
        apply (subst apply_every_split[symmetric], simp)
        by (simp add: register_mult cblinfun_compose_assoc)
      also have \<open>\<dots> = reg_3_3 (function_at x compress1)
          o\<^sub>C\<^sub>L (  reg_3_3 (apply_every (- {x}) (\<lambda>_. compress1)) o\<^sub>C\<^sub>L reg_3_3 (apply_every (- {x}) (\<lambda>_. compress1))  )
          o\<^sub>C\<^sub>L Snd ((Fst;Snd \<circ> function_at x) standard_query1)
          o\<^sub>C\<^sub>L reg_3_3 (function_at x compress1)\<close>
        apply (subst aux)
        by (auto simp add: cblinfun_compose_assoc)
      also have \<open>\<dots> = reg_3_3 (function_at x compress1)
          o\<^sub>C\<^sub>L (reg_3_3 (apply_every (- {x}) (\<lambda>_. compress1 o\<^sub>C\<^sub>L compress1)))
          o\<^sub>C\<^sub>L Snd ((Fst;Snd \<circ> function_at x) standard_query1)
          o\<^sub>C\<^sub>L reg_3_3 (function_at x compress1)\<close>
        by (simp add: register_mult[of reg_3_3] apply_every_mult)
      also have \<open>\<dots> = reg_3_3 (function_at x compress1)
          o\<^sub>C\<^sub>L Snd ((Fst;Snd \<circ> function_at x) standard_query1)
          o\<^sub>C\<^sub>L reg_3_3 (function_at x compress1)\<close>
        by (simp add: compress1_square)
      finally show ?thesis
        by auto
    qed
    also have \<open>\<dots> = ket x \<otimes>\<^sub>s ((Snd (function_at x compress1) o\<^sub>C\<^sub>L ((Fst; Snd o function_at x) standard_query1) o\<^sub>C\<^sub>L Snd (function_at x compress1)) *\<^sub>V \<psi>)\<close>
      by (simp add: reg_3_3_def)
    also have \<open>\<dots> = controlled_op (\<lambda>x. Snd (function_at x compress1) o\<^sub>C\<^sub>L ((Fst; Snd o function_at x) standard_query1) o\<^sub>C\<^sub>L Snd (function_at x compress1)) *\<^sub>V
                  (ket x \<otimes>\<^sub>s \<psi>)\<close>
      by simp
    also have \<open>\<dots> = controlled_op (\<lambda>x. (Fst; Snd o function_at x) query1) (ket x \<otimes>\<^sub>s \<psi>)\<close>
      by (auto simp: query1_def register_mult[symmetric] register_pair_Snd[unfolded o_def, THEN fun_cong])
    finally show ?thesis
      by -
  qed

  from this[of _ \<open>ket _\<close>]
  show ?thesis
    by (auto intro!: equal_ket simp: tensor_ell2_ket)
qed

text \<open>We give an alternate (equivalent) definition of the compressed oracle \<^const>\<open>query\<close>.
  Instead of decompressing the whole oracle, we decompress only the output we need.
  Specifically, this is implemented by -- if the query register contains \<^term>\<open>ket x\<close> --
  performing \<^const>\<open>query1\<close> on the output register and on
  the register $H_x$ which is the part of the oracle register which corresponds to the 
  output for input $x$.

  And analogously for \<^const>\<open>query1'\<close>.\<close>

lemma query_local: \<open>query = controlled_op (\<lambda>x. (Fst; Snd o function_at x) query1)\<close>
  using query_def query1_def standard_query_ket by (rule query_local_generic)

lemma query'_local: \<open>query' = controlled_op (\<lambda>x. (Fst; Snd o function_at x) query1')\<close>
  using query'_def query1'_def standard_query'_ket by (rule query_local_generic)

lemma (in compressed_oracle) standard_query_compress: \<open>standard_query o\<^sub>C\<^sub>L reg_3_3 compress = reg_3_3 compress o\<^sub>C\<^sub>L query\<close>
  by (simp add: query_def register_mult compress_selfinverse flip: cblinfun_compose_assoc)

lemma (in compressed_oracle) standard_query'_compress: \<open>standard_query' o\<^sub>C\<^sub>L reg_3_3 compress = reg_3_3 compress o\<^sub>C\<^sub>L query'\<close>
  by (simp add: query'_def register_mult compress_selfinverse flip: cblinfun_compose_assoc)



end (* locale compressed_oracle *)

end
