(* Title:   Modules.thy
   Author:  Amine Chaieb, University of Cambridge
   Author:  Jose Divasón <jose.divasonm at unirioja.es>
   Author:  Jesús Aransay <jesus-maria.aransay at unirioja.es>
   Author:  Johannes Hölzl, VU Amsterdam
   Author:  Fabian Immler, TUM
*)
theory Cartesian_Space
  imports
    "HOL-Analysis.Cartesian_Euclidean_Space"
    "HOL-Analysis.Determinants"
    "HOL-Library.Permutations"
    Vector_Spaces
begin

lemma linear_eq_linear: "Real_Vector_Spaces.linear = Vector_Spaces.linear scaleR scaleR"
proof (safe intro!: ext)
  fix x::"'a \<Rightarrow> 'b"
  assume "Real_Vector_Spaces.linear x"
  interpret Real_Vector_Spaces.linear x by fact
  show "Vector_Spaces.linear ( *\<^sub>R) ( *\<^sub>R) x"
    by unfold_locales (auto simp: algebra_simps add scaleR)
next
  fix x::"'a \<Rightarrow> 'b"
  assume "Vector_Spaces.linear ( *\<^sub>R) ( *\<^sub>R) x"
  interpret Vector_Spaces.linear "( *\<^sub>R)" "( *\<^sub>R)" x by fact
  show "Real_Vector_Spaces.linear x"
    by unfold_locales (auto simp: algebra_simps add scale)
qed


definition "cart_basis = {axis i 1 | i. i\<in>UNIV}"

lemma finite_cart_basis: "finite (cart_basis)" unfolding cart_basis_def
  using finite_Atleast_Atmost_nat by fastforce

lemma card_cart_basis: "card (cart_basis::('a::zero_neq_one^'i) set) = CARD('i)"
  unfolding cart_basis_def Setcompr_eq_image
  by (rule card_image) (auto simp: inj_on_def axis_eq_axis)

interpretation vec: vector_space "( *s) "
  by (unfold_locales, simp_all)

lemma independent_cart_basis:
  "vec.independent (cart_basis)"
proof (rule vec.independent_if_scalars_zero)
  show "finite (cart_basis)" using finite_cart_basis .
  fix f::"('a, 'b) vec \<Rightarrow> 'a" and x::"('a, 'b) vec"
  assume eq_0: "(\<Sum>x\<in>cart_basis. f x *s x) = 0" and x_in: "x \<in> cart_basis"
  obtain i where x: "x = axis i 1" using x_in unfolding cart_basis_def by auto
  have sum_eq_0: "(\<Sum>x\<in>(cart_basis) - {x}. f x * (x $ i)) = 0"
  proof (rule sum.neutral, rule ballI)
    fix xa assume xa: "xa \<in> cart_basis - {x}"
    obtain a where a: "xa = axis a 1" and a_not_i: "a \<noteq> i"
      using xa x unfolding cart_basis_def by auto
    have "xa $ i = 0" unfolding a axis_def using a_not_i by auto
    thus "f xa * xa $ i = 0" by simp
  qed
  have "0 = (\<Sum>x\<in>cart_basis. f x *s x) $ i" using eq_0 by simp
  also have "... = (\<Sum>x\<in>cart_basis. (f x *s x) $ i)" unfolding sum_component ..
  also have "... = (\<Sum>x\<in>cart_basis. f x * (x $ i))" unfolding vector_smult_component ..
  also have "... = f x * (x $ i) + (\<Sum>x\<in>(cart_basis) - {x}. f x * (x $ i))"
    by (rule sum.remove[OF finite_cart_basis x_in])
  also have "... =  f x * (x $ i)" unfolding sum_eq_0 by simp
  also have "... = f x" unfolding x axis_def by auto
  finally show "f x = 0" ..
qed

lemma span_cart_basis:
  "vec.span (cart_basis) = UNIV"
proof (auto)
  fix x::"('a, 'b) vec"
  let ?f="\<lambda>v. x $ (THE i. v = axis i 1)"
  show "x \<in> vec.span (cart_basis)"
    apply (unfold vec.span_finite[OF finite_cart_basis])
    apply (rule image_eqI[of _ _ ?f])
     apply (subst  vec_eq_iff)
     apply clarify
  proof -
    fix i::'b
    let ?w = "axis i (1::'a)"
    have the_eq_i: "(THE a. ?w = axis a 1) = i"
      by (rule the_equality, auto simp: axis_eq_axis)
    have sum_eq_0: "(\<Sum>v\<in>(cart_basis) - {?w}. x $ (THE i. v = axis i 1) * v $ i) = 0"
    proof (rule sum.neutral, rule ballI)
      fix xa::"('a, 'b) vec"
      assume xa: "xa \<in> cart_basis - {?w}"
      obtain j where j: "xa = axis j 1" and i_not_j: "i \<noteq> j" using xa unfolding cart_basis_def by auto
      have the_eq_j: "(THE i. xa = axis i 1) = j"
      proof (rule the_equality)
        show "xa = axis j 1" using j .
        show "\<And>i. xa = axis i 1 \<Longrightarrow> i = j" by (metis axis_eq_axis j zero_neq_one)
      qed
      show "x $ (THE i. xa = axis i 1) * xa $ i = 0"
        apply (subst (2) j)
        unfolding the_eq_j unfolding axis_def using i_not_j by simp
    qed
    have "(\<Sum>v\<in>cart_basis. x $ (THE i. v = axis i 1) *s v) $ i =
  (\<Sum>v\<in>cart_basis. (x $ (THE i. v = axis i 1) *s v) $ i)" unfolding sum_component ..
    also have "... = (\<Sum>v\<in>cart_basis. x $ (THE i. v = axis i 1) * v $ i)"
      unfolding vector_smult_component ..
    also have "... = x $ (THE a. ?w = axis a 1) * ?w $ i + (\<Sum>v\<in>(cart_basis) - {?w}. x $ (THE i. v = axis i 1) * v $ i)"
      by (rule sum.remove[OF finite_cart_basis], auto simp add: cart_basis_def)
    also have "... = x $ (THE a. ?w = axis a 1) * ?w $ i" unfolding sum_eq_0 by simp
    also have "... = x $ i" unfolding the_eq_i unfolding axis_def by auto
    finally show "x $ i = (\<Sum>v\<in>cart_basis. x $ (THE i. v = axis i 1) *s v) $ i" by simp
  qed simp
qed

(*Some interpretations:*)
interpretation vec: finite_dimensional_vector_space "( *s)" "cart_basis"
  by (unfold_locales, auto simp add: finite_cart_basis independent_cart_basis span_cart_basis)

lemma matrix_vector_mul_linear:
  "linear ( *s) ( *s) (\<lambda>x. A *v (x::'a::{field} ^ _))"
  by unfold_locales
    (vector matrix_vector_mult_def sum.distrib algebra_simps)+

interpretation euclidean_space: vector_space "scaleR :: real => 'a => 'a::euclidean_space"
  by (unfold_locales, simp_all add: algebra_simps)

interpretation euclidean_space:
  finite_dimensional_vector_space "scaleR :: real => 'a => 'a::euclidean_space" "Basis"
\<comment>\<open>TODO: remove me!\<close>
proof unfold_locales
  show "finite (Basis::'a set)" by (metis finite_Basis)
  show "euclidean_space.independent (Basis::'a set)"
    unfolding euclidean_space.dependent_def
    apply (subst euclidean_space.span_finite)
    apply simp
    apply clarify
    apply (drule_tac f="inner a" in arg_cong)
    apply (simp add: inner_Basis inner_sum_right eq_commute)
    done
  show "euclidean_space.span (Basis::'a set) = UNIV"
    unfolding euclidean_space.span_finite [OF finite_Basis]
    by (auto intro!: euclidean_representation[symmetric])
qed

(****************** Generalized parts of the file Cartesian_Euclidean_Space.thy ******************)

lemma vector_mul_lcancel[simp]: "a *s x = a *s y \<longleftrightarrow> a = (0::'a::{field}) \<or> x = y"
  by (metis eq_iff_diff_eq_0 vector_mul_eq_0 vector_ssub_ldistrib)

lemma vector_mul_lcancel_imp: "a \<noteq> (0::'a::{field}) ==>  a *s x = a *s y ==> (x = y)"
  by (metis vector_mul_lcancel)

lemma linear_componentwise:
  fixes f:: "'a::field ^'m \<Rightarrow> 'a ^ 'n"
  assumes lf: "linear ( *s) ( *s) f"
  shows "(f x)$j = sum (\<lambda>i. (x$i) * (f (axis i 1)$j)) (UNIV :: 'm set)" (is "?lhs = ?rhs")
proof -
  interpret lf: linear "( *s)" "( *s)" f
    using lf .
  let ?M = "(UNIV :: 'm set)"
  let ?N = "(UNIV :: 'n set)"
  have fM: "finite ?M" by simp
  have "?rhs = (sum (\<lambda>i. (x$i) *s (f (axis i 1))) ?M)$j"
    unfolding sum_component by simp
  then show ?thesis
    unfolding lf.sum[symmetric] lf.scale[symmetric]
    unfolding basis_expansion by auto
qed

(*Two new interpretations*)
interpretation vec: linear "( *s)" "( *s)" "(\<lambda>x. A *v (x::'a::{field} ^ _))"
  using matrix_vector_mul_linear .

interpretation vec: linear "( *s)" "( *s)" "( *v) A"
  by unfold_locales

lemma matrix_works:
  assumes lf: "linear ( *s) ( *s) f"
  shows "matrix f *v x = f (x::'a::field ^ 'n)"
  apply (simp add: matrix_def matrix_vector_mult_def vec_eq_iff mult.commute)
  apply clarify
  apply (rule linear_componentwise[OF lf, symmetric])
  done

lemma matrix_vector_mul: "linear ( *s) ( *s) f ==> f = (\<lambda>x. matrix f *v (x::'a::{field}^ 'n))"
  by (simp add: ext matrix_works)

lemma matrix_of_matrix_vector_mul: "matrix(\<lambda>x. A *v (x :: 'a::{field} ^ 'n)) = A"
  by (simp add: matrix_eq matrix_vector_mul_linear matrix_works)

(*
lemma matrix_compose:
  assumes lf: "linear ( *s) ( *s) (f::'a::{field}^'n \<Rightarrow> 'a^'m)"
    and lg: "linear ( *s) ( *s) (g::'a^'m \<Rightarrow> 'a^_)"
  shows "matrix (g o f) = matrix g ** matrix f"
  thm lf[folded linear_eq_linear]
    linear_compose
  using lf lg linear_compose[OF lf lg] matrix_works[OF linear_compose[OF lf lg]]
  by (simp add: matrix_eq matrix_works matrix_vector_mul_assoc[symmetric] o_def)
*)

lemma matrix_left_invertible_injective:
  "(\<exists>B. (B::'a::{field}^'m^'n) ** (A::'a::{field}^'n^'m) = mat 1)
    \<longleftrightarrow> (\<forall>x y. A *v x = A *v y \<longrightarrow> x = y)"
proof -
  { fix B:: "'a^'m^'n" and x y assume B: "B ** A = mat 1" and xy: "A *v x = A*v y"
    from xy have "B*v (A *v x) = B *v (A*v y)" by simp
    hence "x = y"
      unfolding matrix_vector_mul_assoc B matrix_vector_mul_lid . }
  moreover
  { assume A: "\<forall>x y. A *v x = A *v y \<longrightarrow> x = y"
    hence i: "inj (( *v) A)" unfolding inj_on_def by auto
    from vec.exists_left_inverse_on[OF vec.subspace_UNIV i]
    obtain g where g: "linear ( *s) ( *s) g" "g o (( *v) A) = id" by (auto simp: id_def module_hom_iff_linear o_def)
    have "matrix g ** A = mat 1"
      unfolding matrix_eq matrix_vector_mul_lid matrix_vector_mul_assoc[symmetric] matrix_works[OF g(1)]
      using g(2) by (metis comp_apply id_apply)
    then have "\<exists>B. (B::'a::{field}^'m^'n) ** A = mat 1" by blast }
  ultimately show ?thesis by blast
qed

lemma matrix_left_invertible_ker:
  "(\<exists>B. (B::'a::{field} ^'m^'n) ** (A::'a::{field}^'n^'m) = mat 1) \<longleftrightarrow> (\<forall>x. A *v x = 0 \<longrightarrow> x = 0)"
  unfolding matrix_left_invertible_injective
  using vec.inj_on_iff_eq_0[OF vec.subspace_UNIV, of A]
  by (simp add: inj_on_def)

lemma matrix_left_invertible_independent_columns:
  fixes A :: "'a::{field}^'n^'m"
  shows "(\<exists>(B::'a ^'m^'n). B ** A = mat 1) \<longleftrightarrow>
      (\<forall>c. sum (\<lambda>i. c i *s column i A) (UNIV :: 'n set) = 0 \<longrightarrow> (\<forall>i. c i = 0))"
    (is "?lhs \<longleftrightarrow> ?rhs")
proof -
  let ?U = "UNIV :: 'n set"
  { assume k: "\<forall>x. A *v x = 0 \<longrightarrow> x = 0"
    { fix c i
      assume c: "sum (\<lambda>i. c i *s column i A) ?U = 0" and i: "i \<in> ?U"
      let ?x = "\<chi> i. c i"
      have th0:"A *v ?x = 0"
        using c
        by (vector matrix_mult_sum)
      from k[rule_format, OF th0] i
      have "c i = 0" by (vector vec_eq_iff)}
    hence ?rhs by blast }
  moreover
  { assume H: ?rhs
    { fix x assume x: "A *v x = 0"
      let ?c = "\<lambda>i. ((x$i ):: 'a)"
      from H[rule_format, of ?c, unfolded matrix_mult_sum[symmetric], OF x]
      have "x = 0" by vector }
  }
  ultimately show ?thesis unfolding matrix_left_invertible_ker by auto
qed


lemma matrix_right_invertible_independent_rows:
  fixes A :: "'a::{field}^'n^'m"
  shows "(\<exists>(B::'a^'m^'n). A ** B = mat 1) \<longleftrightarrow>
    (\<forall>c. sum (\<lambda>i. c i *s row i A) (UNIV :: 'm set) = 0 \<longrightarrow> (\<forall>i. c i = 0))"
  unfolding left_invertible_transpose[symmetric]
    matrix_left_invertible_independent_columns
  by (simp add:)

lemma matrix_left_right_inverse:
  fixes A A' :: "'a::{field}^'n^'n"
  shows "A ** A' = mat 1 \<longleftrightarrow> A' ** A = mat 1"
proof -
  { fix A A' :: "'a ^'n^'n"
    assume AA': "A ** A' = mat 1"
    have sA: "surj (( *v) A)"
      unfolding surj_def
      apply clarify
      apply (rule_tac x="(A' *v y)" in exI)
      apply (simp add: matrix_vector_mul_assoc AA' matrix_vector_mul_lid)
      done
    from vec.linear_surjective_isomorphism[OF matrix_vector_mul_linear sA]
    obtain f' :: "'a ^'n \<Rightarrow> 'a ^'n"
      where f': "linear ( *s) ( *s) f'" "\<forall>x. f' (A *v x) = x" "\<forall>x. A *v f' x = x" by blast
    have th: "matrix f' ** A = mat 1"
      by (simp add: matrix_eq matrix_works[OF f'(1)]
          matrix_vector_mul_assoc[symmetric] matrix_vector_mul_lid f'(2)[rule_format])
    hence "(matrix f' ** A) ** A' = mat 1 ** A'" by simp
    hence "matrix f' = A'"
      by (simp add: matrix_mul_assoc[symmetric] AA' matrix_mul_rid matrix_mul_lid)
    hence "matrix f' ** A = A' ** A" by simp
    hence "A' ** A = mat 1" by (simp add: th)
  }
  then show ?thesis by blast
qed

(***************** Here ends the generalization of Cartesian_Euclidean_Space.thy *****************)

(****************** Generalized parts of the file Convex_Euclidean_Space.thy ******************)

lemma (in linear) linear_injective_on_subspace_0:
  "inj_on f S \<longleftrightarrow> (\<forall>x \<in> S. f x = 0 \<longrightarrow> x = 0)" if "vs1.subspace S"
  using that by (simp add: module_hom_iff_linear[symmetric] inj_on_iff_eq_0)

lemma (in linear) linear_injective_0:
  "inj_on f UNIV \<longleftrightarrow> (\<forall>x. f x = 0 \<longrightarrow> x = 0)"
  by (subst linear_injective_on_subspace_0) (auto )

lemma (in vector_space) sum_constant_scale:
  \<comment>\<open>@{thm sum_constant_scaleR} @{thm sum_constant_ereal} @{thm sum_constant}\<close>
  shows "(\<Sum>x\<in>A. y) = scale (of_nat (card A)) y"
  by (induct A rule: infinite_finite_induct) (simp_all add: algebra_simps)

context finite_dimensional_vector_space
begin

lemma indep_card_eq_dim_span:
  assumes "independent B"
  shows "finite B \<and> card B = dim (span B)"
  using assms basis_card_eq_dim[of B "span B"] span_superset[of B] finiteI_independent by auto
end

context module
begin

lemmas independent_inj_on_image = independent_injective_image

end

context module
begin

lemma subspace_Inter: "\<forall>s \<in> f. subspace s \<Longrightarrow> subspace (Inter f)"
  unfolding subspace_def by auto

lemma span_eq[simp]: "span s = s \<longleftrightarrow> subspace s"
  unfolding span_def by (rule hull_eq) (rule subspace_Inter)

end

context finite_dimensional_vector_space
begin

lemma subspace_dim_equal:
  assumes "subspace S"
    and "subspace T"
    and "S \<subseteq> T"
    and "dim S \<ge> dim T"
  shows "S = T"
proof -
  from basis_exists[of S]
  obtain B where B: "B \<le> S" "S \<subseteq> span B" "independent B" "card B = dim S"
    by auto
  then have "span B \<subseteq> S"
    using span_mono[of B S] span_eq[of S] assms by metis
  then have "span B = S"
    using B by auto
  have "dim S = dim T"
    using assms dim_subset[of S T] by auto
  then have "T \<subseteq> span B"
    apply (intro card_ge_dim_independent)
    using B assms \<open>card B = dim S\<close> by auto
  then show ?thesis
    using assms `span B = S` by auto
qed

end
(***************** Here ends the generalization of Convex_Euclidean_Space.thy *****************)

(*********************** Generalized parts of the file Determinants.thy ***********************)

(*Here I generalize some lemmas, from the class linordered_idom to a comm_ring_1.
  Next proof follows the one presented in: http://hobbes.la.asu.edu/courses/site/442-f09/dets.pdf*)
lemma det_identical_columns:
  fixes A :: "'a::{comm_ring_1}^'n^'n"
  assumes jk: "j \<noteq> k"
  and r: "column j A = column k A"
  shows "det A = 0"
proof -
let ?U="UNIV::'n set"
let ?t_jk="Fun.swap j k id"
let ?PU="{p. p permutes ?U}"
let ?S1="{p. p\<in>?PU \<and> evenperm p}"
let ?S2="{(?t_jk \<circ> p) |p. p \<in>?S1}"
let ?f="\<lambda>p. of_int (sign p) * (\<Prod>i\<in>UNIV. A $ i $ p i)"
let ?g="\<lambda>p. ?t_jk \<circ> p"
have g_S1: "?S2 = ?g` ?S1" by auto
have inj_g: "inj_on ?g ?S1"
  proof (unfold inj_on_def, auto)
      fix x y assume x: "x permutes ?U" and even_x: "evenperm x"
        and y: "y permutes ?U" and even_y: "evenperm y" and eq: "?t_jk \<circ> x = ?t_jk \<circ> y"
      show "x = y" by (metis (hide_lams, no_types) comp_assoc eq id_comp swap_id_idempotent)
  qed
have tjk_permutes: "?t_jk permutes ?U" unfolding permutes_def swap_id_eq by (auto,metis)
have tjk_eq: "\<forall>i l. A $ i $ ?t_jk l  =  A $ i $ l"
  using r jk
  unfolding column_def vec_eq_iff swap_id_eq by fastforce
have sign_tjk: "sign ?t_jk = -1" using sign_swap_id[of j k] jk by auto
  {fix x
   assume x: "x\<in> ?S1"
   have "sign (?t_jk \<circ> x) = sign (?t_jk) * sign x"
    by (metis (lifting) finite_class.finite_UNIV mem_Collect_eq
        permutation_permutes permutation_swap_id sign_compose x)
   also have "... = - sign x" using sign_tjk by simp
   also have "... \<noteq> sign x" unfolding sign_def by simp
   finally have "sign (?t_jk \<circ> x) \<noteq> sign x" and "(?t_jk \<circ> x) \<in> ?S2"
   by (auto, metis (lifting, full_types) mem_Collect_eq x)
  }
hence disjoint: "?S1 \<inter> ?S2 = {}" by (auto, metis sign_def)
have PU_decomposition: "?PU = ?S1 \<union> ?S2"
  proof (auto)
    fix x
    assume x: "x permutes ?U" and "\<forall>p. p permutes ?U \<longrightarrow> x = Fun.swap j k id \<circ> p \<longrightarrow> \<not> evenperm p"
    from this obtain p where p: "p permutes UNIV" and x_eq: "x = Fun.swap j k id \<circ> p"
      and odd_p: "\<not> evenperm p"
      by (metis (no_types) comp_assoc id_comp inv_swap_id permutes_compose
          permutes_inv_o(1) tjk_permutes)
    thus "evenperm x"
      by (metis evenperm_comp evenperm_swap finite_class.finite_UNIV
        jk permutation_permutes permutation_swap_id)
   next
   fix p assume p: "p permutes ?U"
   show "Fun.swap j k id \<circ> p permutes UNIV" by (metis p permutes_compose tjk_permutes)
qed
have "sum ?f ?S2 = sum ((\<lambda>p. of_int (sign p) * (\<Prod>i\<in>UNIV. A $ i $ p i))
  \<circ> (\<circ>) (Fun.swap j k id)) {p \<in> {p. p permutes UNIV}. evenperm p}"
    unfolding g_S1 by (rule sum.reindex[OF inj_g])
also have "... = sum (\<lambda>p. of_int (sign (?t_jk \<circ> p)) * (\<Prod>i\<in>UNIV. A $ i $ p i)) ?S1"
  unfolding o_def by (rule sum.cong, auto simp add: tjk_eq)
also have "... = sum (\<lambda>p. - ?f p) ?S1"
  proof (rule sum.cong, auto)
     fix x assume x: "x permutes ?U"
     and even_x: "evenperm x"
     hence perm_x: "permutation x" and perm_tjk: "permutation ?t_jk"
      using permutation_permutes[of x] permutation_permutes[of ?t_jk] permutation_swap_id
      by (metis finite_code)+
     have "(sign (?t_jk \<circ> x)) = - (sign x)"
      unfolding sign_compose[OF perm_tjk perm_x] sign_tjk by auto
     thus "of_int (sign (?t_jk \<circ> x)) * (\<Prod>i\<in>UNIV. A $ i $ x i)
      = - (of_int (sign x) * (\<Prod>i\<in>UNIV. A $ i $ x i))"
      by auto
  qed
also have "...= - sum ?f ?S1" unfolding sum_negf ..
finally have *: "sum ?f ?S2 = - sum ?f ?S1" .
have "det A = (\<Sum>p | p permutes UNIV. of_int (sign p) * (\<Prod>i\<in>UNIV. A $ i $ p i))"
  unfolding det_def ..
also have "...= sum ?f ?S1 + sum ?f ?S2"
  by (subst PU_decomposition, rule sum.union_disjoint[OF _ _ disjoint], auto)
also have "...= sum ?f ?S1 - sum ?f ?S1 " unfolding * by auto
also have "...= 0" by simp
finally show "det A = 0" by simp
qed


lemma det_identical_rows:
  fixes A :: "'a::{comm_ring_1}^'n^'n"
  assumes ij: "i \<noteq> j"
  and r: "row i A = row j A"
  shows "det A = 0"
  apply (subst det_transpose[symmetric])
  apply (rule det_identical_columns[OF ij])
  apply (metis column_transpose r)
  done

(*The following two lemmas appear in the library with the restriction:

  lemma det_zero_row:
  fixes A :: "'a::{idom, ring_char_0}^'n^'n"
  assumes r: "row i A = 0"
  shows "det A = 0"

Now I will do the proof over a field in general. But that is not a generalization, since integers
are not a field, although they satisfy {idom, ring_char_0}. Nevertheless, in my case I'll work with
Z/Z2 (the field of integers modulo 2), which are a field but not a {idom, ring_char_0}.*)

lemma det_zero_row:
  fixes A :: "'a::{field}^'n^'n"
  assumes r: "row i A = 0"
  shows "det A = 0"
  using r
  apply (simp add: row_def det_def vec_eq_iff)
  apply (rule sum.neutral)
  apply (auto)
  done


lemma det_zero_column:
  fixes A :: "'a::{field}^'n^'n"
  assumes r: "column i A = 0"
  shows "det A = 0"
  apply (subst det_transpose[symmetric])
  apply (rule det_zero_row [of i])
  apply (metis row_transpose r)
  done

lemma det_row_operation:
  fixes A :: "'a::{comm_ring_1}^'n^'n"
  assumes ij: "i \<noteq> j"
  shows "det (\<chi> k. if k = i then row i A + c *s row j A else row k A) = det A"
proof -
  let ?Z = "(\<chi> k. if k = i then row j A else row k A) :: 'a ^'n^'n"
  have th: "row i ?Z = row j ?Z" by (vector row_def)
  have th2: "((\<chi> k. if k = i then row i A else row k A) :: 'a^'n^'n) = A"
    by (vector row_def)
  show ?thesis
    unfolding det_row_add [of i] det_row_mul[of i] det_identical_rows[OF ij th] th2
    by simp
qed

lemma det_row_span:
  fixes A :: "'a::{field}^'n^'n"
  assumes x: "x \<in> vec.span {row j A |j. j \<noteq> i}"
  shows "det (\<chi> k. if k = i then row i A + x else row k A) = det A"
  using x
proof (induction rule: vec.span_induct_alt)
  case 1
  then show ?case
    by (rule cong[of det, OF refl]) (vector row_def)
next
  case (2 c z y)
  note zS = 2(1)
    and Py = 2(2)
  let ?d = "\<lambda>x. det (\<chi> k. if k = i then x else row k A)"
  let ?P = "\<lambda>x. ?d (row i A + x) = det A"
  from zS obtain j where j: "z = row j A" "i \<noteq> j"
    by blast
  let ?w = "row i A + y"
  have th0: "row i A + (c*s z + y) = ?w + c*s z"
    by vector
  have thz: "?d z = 0"
    apply (rule det_identical_rows[OF j(2)])
    using j
    apply (vector row_def)
    done
  have "?d (row i A + (c*s z + y)) = ?d (?w + c*s z)"
    unfolding th0 ..
  then show ?case
    unfolding thz Py det_row_mul[of i] det_row_add[of i]
    by simp
qed

lemma det_dependent_rows:
  fixes A:: "'a::{field}^'n^'n"
  assumes d: "vec.dependent (rows A)"
  shows "det A = 0"
proof -
  let ?U = "UNIV :: 'n set"
  from d obtain i where i: "row i A \<in> vec.span (rows A - {row i A})"
    unfolding vec.dependent_def rows_def by blast
  {
    fix j k
    assume jk: "j \<noteq> k" and c: "row j A = row k A"
    from det_identical_rows[OF jk c] have ?thesis .
  }
  moreover
  {
    assume H: "\<And> i j. i \<noteq> j \<Longrightarrow> row i A \<noteq> row j A"
    have th0: "- row i A \<in> vec.span {row j A|j. j \<noteq> i}"
      apply (rule vec.span_neg)
      apply (rule set_rev_mp)
      apply (rule i)
      apply (rule vec.span_mono)
      using H i
      apply (auto simp add: rows_def)
      done
    from det_row_span[OF th0]
    have "det A = det (\<chi> k. if k = i then 0 *s 1 else row k A)"
      unfolding right_minus vector_smult_lzero ..
    with det_row_mul[of i "0::'a" "\<lambda>i. 1"]
    have "det A = 0" by simp
  }
  ultimately show ?thesis by blast
qed

lemma det_mul:
  fixes A B :: "'a::{comm_ring_1}^'n^'n"
  shows "det (A ** B) = det A * det B"
proof -
  let ?U = "UNIV :: 'n set"
  let ?F = "{f. (\<forall>i\<in> ?U. f i \<in> ?U) \<and> (\<forall>i. i \<notin> ?U \<longrightarrow> f i = i)}"
  let ?PU = "{p. p permutes ?U}"
  have fU: "finite ?U"
    by simp
  have fF: "finite ?F"
    by (rule finite)
  {
    fix p
    assume p: "p permutes ?U"
    have "p \<in> ?F" unfolding mem_Collect_eq permutes_in_image[OF p]
      using p[unfolded permutes_def] by simp
  }
  then have PUF: "?PU \<subseteq> ?F" by blast
  {
    fix f
    assume fPU: "f \<in> ?F - ?PU"
    have fUU: "f ` ?U \<subseteq> ?U"
      using fPU by auto
    from fPU have f: "\<forall>i \<in> ?U. f i \<in> ?U" "\<forall>i. i \<notin> ?U \<longrightarrow> f i = i" "\<not>(\<forall>y. \<exists>!x. f x = y)"
      unfolding permutes_def by auto

    let ?A = "(\<chi> i. A$i$f i *s B$f i) :: 'a^'n^'n"
    let ?B = "(\<chi> i. B$f i) :: 'a^'n^'n"
    {
      assume fni: "\<not> inj_on f ?U"
      then obtain i j where ij: "f i = f j" "i \<noteq> j"
        unfolding inj_on_def by blast
      from ij
      have rth: "row i ?B = row j ?B"
        by (vector row_def)
      from det_identical_rows[OF ij(2) rth]
      have "det (\<chi> i. A$i$f i *s B$f i) = 0"
        unfolding det_rows_mul by simp
    }
    moreover
    {
      assume fi: "inj_on f ?U"
      from f fi have fith: "\<And>i j. f i = f j \<Longrightarrow> i = j"
        unfolding inj_on_def by metis
      note fs = fi[unfolded surjective_iff_injective_gen[OF fU fU refl fUU, symmetric]]
      {
        fix y
        from fs f have "\<exists>x. f x = y"
          by blast
        then obtain x where x: "f x = y"
          by blast
        {
          fix z
          assume z: "f z = y"
          from fith x z have "z = x"
            by metis
        }
        with x have "\<exists>!x. f x = y"
          by blast
      }
      with f(3) have "det (\<chi> i. A$i$f i *s B$f i) = 0"
        by blast
    }
    ultimately have "det (\<chi> i. A$i$f i *s B$f i) = 0"
      by blast
  }
  then have zth: "\<forall> f\<in> ?F - ?PU. det (\<chi> i. A$i$f i *s B$f i) = 0"
    by simp
  {
    fix p
    assume pU: "p \<in> ?PU"
    from pU have p: "p permutes ?U"
      by blast
    let ?s = "\<lambda>p. of_int (sign p)"
    let ?f = "\<lambda>q. ?s p * (\<Prod>i\<in> ?U. A $ i $ p i) * (?s q * (\<Prod>i\<in> ?U. B $ i $ q i))"
    have "(sum (\<lambda>q. ?s q *
        (\<Prod>i\<in> ?U. (\<chi> i. A $ i $ p i *s B $ p i :: 'a^'n^'n) $ i $ q i)) ?PU) =
      (sum (\<lambda>q. ?s p * (\<Prod>i\<in> ?U. A $ i $ p i) * (?s q * (\<Prod>i\<in> ?U. B $ i $ q i))) ?PU)"
      unfolding sum_permutations_compose_right[OF permutes_inv[OF p], of ?f]
    proof (rule sum.cong)
      fix q
      assume qU: "q \<in> ?PU"
      then have q: "q permutes ?U"
        by blast
      from p q have pp: "permutation p" and pq: "permutation q"
        unfolding permutation_permutes by auto
      have th00: "of_int (sign p) * of_int (sign p) = (1::'a)"
        "\<And>a. of_int (sign p) * (of_int (sign p) * a) = a"
        unfolding mult.assoc[symmetric]
        unfolding of_int_mult[symmetric]
        by (simp_all add: sign_idempotent)
      have ths: "?s q = ?s p * ?s (q \<circ> inv p)"
        using pp pq permutation_inverse[OF pp] sign_inverse[OF pp]
        by (simp add:  th00 ac_simps sign_idempotent sign_compose)
      have th001: "prod (\<lambda>i. B$i$ q (inv p i)) ?U = prod ((\<lambda>i. B$i$ q (inv p i)) \<circ> p) ?U"
        by (rule prod_permute[OF p])
      have thp: "prod (\<lambda>i. (\<chi> i. A$i$p i *s B$p i :: 'a^'n^'n) $i $ q i) ?U =
        prod (\<lambda>i. A$i$p i) ?U * prod (\<lambda>i. B$i$ q (inv p i)) ?U"
          unfolding th001 prod.distrib[symmetric] o_def permutes_inverses[OF p]
          apply (rule prod.cong[OF refl])
          using permutes_in_image[OF q]
          apply vector
          done
      show "?s q * prod (\<lambda>i. (((\<chi> i. A$i$p i *s B$p i) :: 'a^'n^'n)$i$q i)) ?U =
        ?s p * (prod (\<lambda>i. A$i$p i) ?U) * (?s (q \<circ> inv p) * prod (\<lambda>i. B$i$(q \<circ> inv p) i) ?U)"
        using ths thp pp pq permutation_inverse[OF pp] sign_inverse[OF pp]
        by (simp add: sign_nz th00 field_simps sign_idempotent sign_compose)
    qed rule
  }
  then have th2: "sum (\<lambda>f. det (\<chi> i. A$i$f i *s B$f i)) ?PU = det A * det B"
    unfolding det_def sum_product
    by (rule sum.cong[OF refl])
  have "det (A**B) = sum (\<lambda>f.  det (\<chi> i. A $ i $ f i *s B $ f i)) ?F"
    unfolding matrix_mul_sum_alt det_linear_rows_sum[OF fU]
    by simp
  also have "\<dots> = sum (\<lambda>f. det (\<chi> i. A$i$f i *s B$f i)) ?PU"
    using sum.mono_neutral_cong_left[OF fF PUF zth, symmetric]
    unfolding det_rows_mul by auto
  finally show ?thesis unfolding th2 .
qed

lemma invertible_left_inverse:
  fixes A :: "'a::{field}^'n^'n"
  shows "invertible A \<longleftrightarrow> (\<exists>(B::'a^'n^'n). B ** A = mat 1)"
  by (metis invertible_def matrix_left_right_inverse)

  lemma invertible_righ_inverse:
  fixes A :: "'a::{field}^'n^'n"
  shows "invertible A \<longleftrightarrow> (\<exists>(B::'a^'n^'n). A** B = mat 1)"
  by (metis invertible_def matrix_left_right_inverse)

  lemma invertible_det_nz:
  fixes A::"'a::{field}^'n^'n"
  shows "invertible A \<longleftrightarrow> det A \<noteq> 0"
proof -
  {
    assume "invertible A"
    then obtain B :: "'a^'n^'n" where B: "A ** B = mat 1"
      unfolding invertible_righ_inverse by blast
    then have "det (A ** B) = det (mat 1 :: 'a^'n^'n)"
      by simp
    then have "det A \<noteq> 0"
      by (simp add: det_mul det_I) algebra
  }
  moreover
  {
    assume H: "\<not> invertible A"
    let ?U = "UNIV :: 'n set"
    have fU: "finite ?U"
      by simp
    from H obtain c i where c: "sum (\<lambda>i. c i *s row i A) ?U = 0"
      and iU: "i \<in> ?U"
      and ci: "c i \<noteq> 0"
      unfolding invertible_righ_inverse
      unfolding matrix_right_invertible_independent_rows
      by blast
    have *: "\<And>(a::'a^'n) b. a + b = 0 \<Longrightarrow> -a = b"
      apply (drule_tac f="(+) (- a)" in cong[OF refl])
      apply (simp only: ab_left_minus add.assoc[symmetric])
      apply simp
      done
    from c ci
    have thr0: "- row i A = sum (\<lambda>j. (1/ c i) *s (c j *s row j A)) (?U - {i})"
      unfolding sum.remove[OF fU iU] sum_cmul
      apply -
      apply (rule vector_mul_lcancel_imp[OF ci])
      apply (auto simp add: field_simps)
      unfolding *
      apply rule
      done
    have thr: "- row i A \<in> vec.span {row j A| j. j \<noteq> i}"
      unfolding thr0
      apply (rule vec.span_sum)
      apply simp
      apply (rule vec.span_scale[folded scalar_mult_eq_scaleR])+
      apply (rule vec.span_base)
      apply auto
      done
    let ?B = "(\<chi> k. if k = i then 0 else row k A) :: 'a^'n^'n"
    have thrb: "row i ?B = 0" using iU by (vector row_def)
    have "det A = 0"
      unfolding det_row_span[OF thr, symmetric] right_minus
      unfolding det_zero_row[OF thrb] ..
  }
  ultimately show ?thesis
    by blast
qed
(********************** Here ends the generalization of Determinants.thy **********************)

(*Finally, some interesting theorems and interpretations that don't appear in any file of the
  library.*)

locale linear_first_finite_dimensional_vector_space =
  l?: linear scaleB scaleC f +
  B?: finite_dimensional_vector_space scaleB BasisB
  for scaleB :: "('a::field => 'b::ab_group_add => 'b)" (infixr "*b" 75)
  and scaleC :: "('a => 'c::ab_group_add => 'c)" (infixr "*c" 75)
  and BasisB :: "('b set)"
  and f :: "('b=>'c)"

lemma vec_dim_card: "vec.dim (UNIV::('a::{field}^'n) set) = CARD ('n)"
proof -
  let ?f="\<lambda>i::'n. axis i (1::'a)"
  have "vec.dim (UNIV::('a::{field}^'n) set) = card (cart_basis::('a^'n) set)"
    unfolding vec.dim_UNIV ..
  also have "... = card ({i. i\<in> UNIV}::('n) set)"
    proof (rule bij_betw_same_card[of ?f, symmetric], unfold bij_betw_def, auto)
      show "inj (\<lambda>i::'n. axis i (1::'a))"  by (simp add: inj_on_def axis_eq_axis)
      fix i::'n
      show "axis i 1 \<in> cart_basis" unfolding cart_basis_def by auto
      fix x::"'a^'n"
      assume "x \<in> cart_basis"
      thus "x \<in> range (\<lambda>i. axis i 1)" unfolding cart_basis_def by auto
    qed
  also have "... = CARD('n)" by auto
  finally show ?thesis .
qed

interpretation vector_space_over_itself: vector_space "( *) :: 'a::field => 'a => 'a"
  by unfold_locales (simp_all add: algebra_simps)

lemma (in vector_space) dependent_single[simp]: "dependent {x} \<longleftrightarrow> x = 0"
  unfolding dependent_def by auto

interpretation vector_space_over_itself: finite_dimensional_vector_space
  "( *) :: 'a::field => 'a => 'a" "{1}"
  by unfold_locales (auto simp: vector_space_over_itself.span_singleton)

lemma dimension_eq_1[code_unfold]: "vector_space_over_itself.dimension TYPE('a::field)= 1"
  unfolding vector_space_over_itself.dimension_def by simp

interpretation complex_over_reals: finite_dimensional_vector_space "( *\<^sub>R)::real=>complex=>complex"
  "{1, \<i>}"
proof unfold_locales
  show "finite {1, \<i>}" by auto
  show "euclidean_space.independent {1, \<i>}"
    by (metis Basis_complex_def euclidean_space.independent_Basis)
  show "euclidean_space.span {1, \<i>} = UNIV"
    by (metis Basis_complex_def euclidean_space.span_Basis)
qed

lemma complex_over_reals_dimension[code_unfold]:
  "complex_over_reals.dimension = 2" unfolding complex_over_reals.dimension_def by auto

(* The following definition will be very useful in our formalization. The problem was that
  (op *\<^sub>R) has type real=>'a=>'a but (op *s) has type 'a \<Rightarrow> ('a, 'b) vec \<Rightarrow> ('a, 'b) vec,
  so we can't use (op *s) to multiply a matrix by a scalar.*)
(*
  definition matrix_scalar_mult :: "'a => ('a::semiring_1) ^'n^'m => ('a::semiring_1) ^'n^'m"
    (infixl "*k" 70)
  where "k *k A \<equiv> (\<chi> i j. k * A $ i $ j)"
*)

(*One example of the use of *\<^sub>R, *s and *k appears in the following theorem (obtained from AFP entry
  about Tarski's Geometry,
  see http://isa-afp.org/browser_info/devel/AFP/Tarskis_Geometry/Linear_Algebra2.html)*)
(*
  lemma scalar_matrix_vector_assoc:
  fixes A :: "real^('m::finite)^('n::finite)"
  shows "k *\<^sub>R (A *v v) = k *\<^sub>R A *v v"*)

(*Now, the generalization of the statement would be: *)

(*
  lemma scalar_matrix_vector_assoc:
  fixes A :: "'a::{field}^'m^'n"
  shows "k *s (A *v v) = k *k A *v v"
*)

end