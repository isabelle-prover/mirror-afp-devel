(* 
    Title:      Miscellaneous.thy
    Author:     Jose Divasón <jose.divasonm at unirioja.es>
    Author:     Jesús Aransay <jesus-maria.aransay at unirioja.es>
*)

section{*Miscellaneous*}

theory Miscellaneous
imports 
  Generalizations
  "$ISABELLE_HOME/src/HOL/Library/Bit"
  Mod_Type
begin

text{*In this file, we present some basic definitions and lemmas about linear algebra and matrices.*}

subsection{*Definitions of number of rows and columns of a matrix*}

definition nrows :: "'a^'columns^'rows => nat"
  where "nrows A = CARD('rows)"

definition ncols :: "'a^'columns^'rows => nat"
  where "ncols A = CARD('columns)"
  
definition matrix_scalar_mult :: "'a::ab_semigroup_mult => 'a ^'n^'m => 'a ^'n^'m"
    (infixl "*k" 70)
  where "k *k A \<equiv> (\<chi> i j. k * A $ i $ j)"

subsection{*Basic properties about matrices*}

lemma nrows_not_0[simp]:
  shows "0 \<noteq> nrows A" unfolding nrows_def by simp

lemma ncols_not_0[simp]:
  shows "0 \<noteq> ncols A" unfolding ncols_def by simp

lemma nrows_transpose: "nrows (transpose A) = ncols A"
  unfolding nrows_def ncols_def ..

lemma ncols_transpose: "ncols (transpose A) = nrows A"
  unfolding nrows_def ncols_def ..

lemma finite_rows: "finite (rows A)"
  using finite_Atleast_Atmost_nat[of "\<lambda>i. row i A"] unfolding rows_def .

lemma finite_columns: "finite (columns A)"
  using finite_Atleast_Atmost_nat[of "\<lambda>i. column i A"] unfolding columns_def .

lemma matrix_vector_zero: "A *v 0 = 0"
  unfolding matrix_vector_mult_def by (simp add: zero_vec_def)

lemma vector_matrix_zero: "0 v* A = 0"
  unfolding vector_matrix_mult_def by (simp add: zero_vec_def)

lemma vector_matrix_zero': "x v* 0 = 0"
  unfolding vector_matrix_mult_def by (simp add: zero_vec_def)

lemma transpose_vector: "x v* A = transpose A *v x"
  by (unfold matrix_vector_mult_def vector_matrix_mult_def transpose_def, auto)


lemma transpose_zero[simp]: "(transpose A = 0) = (A = 0)"
  unfolding transpose_def zero_vec_def vec_eq_iff by auto


subsection{*Theorems obtained from the AFP*}

text{*The following theorems and definitions have been obtained from the AFP 
@{url "http://afp.sourceforge.net/browser_info/current/HOL/Tarskis_Geometry/Linear_Algebra2.html"}.
I have removed some restrictions over the type classes.*}

lemma vector_matrix_left_distrib:
  (*fixes x y :: "real^('n::finite)" and A :: "real^('m::finite)^'n"*)
  shows "(x + y) v* A = x v* A + y v* A"
  unfolding vector_matrix_mult_def
  by (simp add: algebra_simps setsum.distrib vec_eq_iff)

lemma matrix_vector_right_distrib:
  (*fixes v w :: "real^('n::finite)" and M :: "real^'n^('m::finite)"*)
  shows "M *v (v + w) = M *v v + M *v w"
proof -
  have "M *v (v + w) = (v + w) v* transpose M" by (metis transpose_transpose transpose_vector)
  also have "\<dots> = v v* transpose M + w v* transpose M"
    by (rule vector_matrix_left_distrib [of v w "transpose M"])
  finally show "M *v (v + w) = M *v v + M *v w" by (metis transpose_transpose transpose_vector)
qed


lemma scalar_vector_matrix_assoc:
  fixes k :: "'a::{field}" and x :: "'a::{field}^'n" and A :: "'a^'m^'n"
  shows "(k *s x) v* A = k *s (x v* A)"
  unfolding vector_matrix_mult_def unfolding vec_eq_iff 
  by (auto simp add: setsum_right_distrib, rule setsum.cong, simp_all) 
 

lemma vector_scalar_matrix_ac:
  fixes k :: "'a::{field}" and x :: "'a::{field}^'n" and A :: "'a^'m^'n"
  shows "x v* (k *k A) = k *s (x v* A)"
  using scalar_vector_matrix_assoc 
  unfolding vector_matrix_mult_def matrix_scalar_mult_def vec_eq_iff 
  by (auto simp add: setsum_right_distrib)

lemma transpose_scalar: "transpose (k *k A) = k *k transpose A"
  unfolding transpose_def 
  by (vector, simp add: matrix_scalar_mult_def)

lemma scalar_matrix_vector_assoc:
  fixes A :: "'a::{field}^'m^'n"
  shows "k *s (A *v v) = k *k A *v v"
proof -
  have "k *s (A *v v) = k *s (v v* transpose A)" by (metis transpose_transpose transpose_vector)
  also have "\<dots> = v v* (k *k transpose A)"
    by (rule vector_scalar_matrix_ac [symmetric])
  also have "\<dots> = v v* transpose (k *k A)" unfolding transpose_scalar ..
  finally show "k *s (A *v v) = k *k A *v v" by (metis transpose_transpose transpose_vector)
qed

lemma matrix_scalar_vector_ac:
  fixes A :: "'a::{field}^'m^'n"
  shows "A *v (k *s v) = k *k A *v v"
proof -
  have "A *v (k *s v) = k *s (v v* transpose A)" 
    by (metis transpose_transpose scalar_vector_matrix_assoc transpose_vector)
  also have "\<dots> = v v* (k *k transpose A)"
    by (subst vector_scalar_matrix_ac) simp
  also have "\<dots> = v v* transpose (k *k A)" by (subst transpose_scalar) simp
  also have "\<dots> = k *k A *v v" by (metis transpose_transpose transpose_vector)
  finally show "A *v (k *s v) = k *k A *v v" .
qed


definition
  is_basis :: "('a::{field}^'n) set => bool" where
  "is_basis S \<equiv> vec.independent S \<and> vec.span S = UNIV"

lemma card_finite:
  assumes "card S = CARD('n::finite)"
  shows "finite S"
proof -
  from `card S = CARD('n)` have "card S \<noteq> 0" by simp
  with card_eq_0_iff [of S] show "finite S" by simp
qed

lemma independent_is_basis:
  fixes B :: "('a::{field}^'n) set"
  shows "vec.independent B \<and> card B = CARD('n) \<longleftrightarrow> is_basis B"
proof
  assume "vec.independent B \<and> card B = CARD('n)"
  hence "vec.independent B" and "card B = CARD('n)" by simp+
  from card_finite [of B, where 'n = 'n] and `card B = CARD('n)`
  have "finite B" by simp
  from `card B = CARD('n)`
  have "card B = vec.dim (UNIV :: (('a^'n) set))" unfolding vec_dim_card .
  with vec.card_eq_dim [of B UNIV] and `finite B` and `vec.independent B`
  have "vec.span B = UNIV" by auto
  with `vec.independent B` show "is_basis B" unfolding is_basis_def ..
next
  assume "is_basis B"
  hence "vec.independent B" unfolding is_basis_def ..
  moreover have "card B = CARD('n)"
  proof -
    have "B \<subseteq> UNIV" by simp
    moreover
    { from `is_basis B` have "UNIV \<subseteq> vec.span B" and "vec.independent B"
        unfolding is_basis_def
        by simp+ }
    ultimately have "card B = vec.dim (UNIV::((real^'n) set))"
      using vec.basis_card_eq_dim [of B UNIV]
      unfolding vec_dim_card
      by simp
    then show "card B = CARD('n)"
      by (metis vec_dim_card)
  qed
  ultimately show "vec.independent B \<and> card B = CARD('n)" ..
qed

lemma basis_finite:
  fixes B :: "('a::{field}^'n) set"
  assumes "is_basis B"
  shows "finite B"
proof -
  from independent_is_basis [of B] and `is_basis B` have "card B = CARD('n)"
    by simp
  with card_finite [of B, where 'n = 'n] show "finite B" by simp
qed

text{*Here ends the statements obtained from AFP: 
  @{url "http://afp.sourceforge.net/browser_info/current/HOL/Tarskis_Geometry/Linear_Algebra2.html"}
  which have been generalized.*}

subsection{*Basic properties involving span, linearity and dimensions*}

context finite_dimensional_vector_space
begin

text{*This theorem is the reciprocal theorem of @{thm "indep_card_eq_dim_span"}*}

lemma card_eq_dim_span_indep:
(*fixes A :: "('n::euclidean_space) set"*)
assumes "dim (span A) = card A" and "finite A"
shows "independent A" 
by (metis assms card_le_dim_spanning dim_subset equalityE span_inc)

lemma dim_zero_eq:
(*fixes A::"'a::euclidean_space set"*)
assumes dim_A: "dim A = 0"
shows "A = {} \<or> A = {0}"
proof -
obtain B where ind_B: "independent B" and A_in_span_B: "A \<subseteq> span B" 
  and card_B: "card B = 0" using basis_exists[of A] unfolding dim_A by blast
have finite_B: "finite B" using indep_card_eq_dim_span[OF ind_B] by simp
hence B_eq_empty: "B={}" using card_B unfolding card_eq_0_iff by simp
have "A \<subseteq> {0}" using A_in_span_B unfolding B_eq_empty span_empty .
thus ?thesis by blast
qed

lemma dim_zero_eq': 
  (*fixes A::"'a::euclidean_space set"*)
  assumes A: "A = {} \<or> A = {0}"
  shows "dim A = 0"
proof -
have "card ({}::'b set) = dim A"
  proof (rule basis_card_eq_dim[THEN conjunct2, of "{}::'b set" A])
     show "{} \<subseteq> A" by simp
     show "A \<subseteq> span {}" using A by fastforce
     show "independent {}" by (rule independent_empty)
  qed
thus ?thesis by simp
qed


lemma dim_zero_subspace_eq:
(*  fixes A::"'a::euclidean_space set"*)
assumes subs_A: "subspace A"
shows "(dim A = 0) = (A = {0})" using dim_zero_eq dim_zero_eq' subspace_0[OF subs_A] by auto

lemma span_0_imp_set_empty_or_0:
assumes "span A = {0}"
shows "A = {} \<or> A = {0}" by (metis assms span_inc subset_singletonD)
end

context linear
begin

lemma linear_injective_ker_0:
shows "inj f = ({x. f x = 0} = {0})"
unfolding linear_injective_0
using linear_0 by blast

end

lemma snd_if_conv:
shows "snd (if P then (A,B) else (C,D))=(if P then B else D)" by simp

subsection{*Basic properties about matrix multiplication*}

lemma row_matrix_matrix_mult:
fixes A::"'a::{comm_ring_1}^'n^'m"
shows "(P $ i) v* A = (P ** A) $ i"
unfolding vec_eq_iff
unfolding vector_matrix_mult_def unfolding matrix_matrix_mult_def
by (auto intro!: setsum.cong)

corollary row_matrix_matrix_mult':
fixes A::"'a::{comm_ring_1}^'n^'m"
shows "(row i P) v* A = row i (P ** A)"
using row_matrix_matrix_mult unfolding row_def vec_nth_inverse .

lemma column_matrix_matrix_mult:
shows "column i (P**A) = P *v (column i A)"
unfolding column_def matrix_vector_mult_def matrix_matrix_mult_def by fastforce

lemma matrix_matrix_mult_inner_mult:
shows "(A ** B) $ i $ j = row i A \<bullet> column j B"
unfolding inner_vec_def matrix_matrix_mult_def row_def column_def by auto


lemma matrix_vmult_column_sum:
  fixes A::"'a::{field}^'n^'m"
  shows "\<exists>f. A *v x = setsum (\<lambda>y. f y *s y) (columns A)"
proof (rule exI[of _ "\<lambda>y. setsum (\<lambda>i. x $ i) {i. y = column i A}"])
  let ?f="\<lambda>y. setsum (\<lambda>i. x $ i) {i. y = column i A}"  
  let ?g="(\<lambda>y. {i. y=column i (A)})"
  have inj: "inj_on ?g (columns (A))" unfolding inj_on_def unfolding columns_def by auto
  have union_univ: "\<Union> (?g`(columns (A))) = UNIV" unfolding columns_def by auto
  have "A *v x = (\<Sum>i\<in>UNIV. x $ i *s column i A)" unfolding matrix_mult_vsum ..
  also have "... = setsum (\<lambda>i.  x $ i *s column i A) (\<Union>(?g`(columns A)))" unfolding union_univ ..
  also have "... = setsum (setsum ((\<lambda>i.  x $ i *s column i A)))  (?g`(columns A))"
    by (rule setsum.Union_disjoint[unfolded o_def], auto) 
  also have "... = setsum ((setsum ((\<lambda>i.  x $ i *s column i A))) \<circ> ?g)  (columns A)" 
    by (rule setsum.reindex, simp add: inj)
  also have "... =  setsum (\<lambda>y. ?f y *s y) (columns A)"
  proof (rule setsum.cong, unfold o_def)
    fix xa
    have "setsum (\<lambda>i. x $ i *s column i A) {i. xa = column i A} 
      = setsum (\<lambda>i. x $ i *s xa) {i. xa = column i A}" by simp
    also have "... = setsum (\<lambda>i. x $ i) {i. xa = column i A} *s xa" 
      using vec.scale_setsum_left[of "(\<lambda>i. x $ i)" "{i. xa = column i A}" xa] ..
    finally show "(\<Sum>i | xa = column i A. x $ i *s column i A) = (\<Sum>i | xa = column i A. x $ i) *s xa" . 
  qed rule
  finally show "A *v x = (\<Sum>y\<in>columns A. (\<Sum>i | y = column i A. x $ i) *s y)" .
qed


subsection{*Properties about invertibility*}

lemma matrix_inv:
  assumes "invertible M"
  shows matrix_inv_left: "matrix_inv M ** M = mat 1"
  and matrix_inv_right: "M ** matrix_inv M = mat 1"
  using `invertible M` and someI_ex [of "\<lambda> N. M ** N = mat 1 \<and> N ** M = mat 1"]
  unfolding invertible_def and matrix_inv_def
  by simp_all

lemma invertible_mult:
  assumes inv_A: "invertible A"
  and inv_B: "invertible B"
  shows "invertible (A**B)"
proof -
  obtain A' where AA': "A ** A' = mat 1" and A'A: "A' ** A = mat 1" 
    using inv_A unfolding invertible_def by blast
  obtain B' where BB': "B ** B' = mat 1" and B'B: "B' ** B = mat 1" 
    using inv_B unfolding invertible_def by blast
  show ?thesis
  proof (unfold invertible_def, rule exI[of _ "B'**A'"], rule conjI)
    have "A ** B ** (B' ** A') = A ** (B ** (B' ** A'))" 
      using matrix_mul_assoc[of A B "(B' ** A')", symmetric] .
    also have "... = A ** (B ** B' ** A')" unfolding matrix_mul_assoc[of B "B'" "A'"] ..
    also have "... = A ** (mat 1 ** A')" unfolding BB' ..
    also have "... = A ** A'" unfolding matrix_mul_lid ..
    also have "... = mat 1" unfolding AA' ..
    finally show "A ** B ** (B' ** A') = mat (1::'a)" .    
    have "B' ** A' ** (A ** B) = B' ** (A' ** (A ** B))" using matrix_mul_assoc[of B' A' "(A ** B)", symmetric] .
    also have "... =  B' ** (A' ** A ** B)" unfolding matrix_mul_assoc[of A' A B] ..
    also have "... =  B' ** (mat 1 ** B)" unfolding A'A ..
    also have "... = B' ** B"  unfolding matrix_mul_lid ..
    also have "... = mat 1" unfolding B'B ..
    finally show "B' ** A' ** (A ** B) = mat 1" .
  qed
qed


text{*In the library, @{thm "matrix_inv_def"} allows the use of non squary matrices.
  The following lemma can be also proved fixing @{term "A::'a::{semiring_1}^'n^'m"}*}

lemma matrix_inv_unique:
  fixes A::"'a::{semiring_1}^'n^'n"
  assumes AB: "A ** B = mat 1" and BA: "B ** A = mat 1"
  shows "matrix_inv A = B" 
proof (unfold matrix_inv_def, rule some_equality)
  show "A ** B = mat (1::'a) \<and> B ** A = mat (1::'a)" using AB BA by simp
  fix C assume "A ** C = mat (1::'a) \<and> C ** A = mat (1::'a)"
  hence AC: "A ** C = mat (1::'a)" and CA: "C ** A = mat (1::'a)" by auto  
  have "B = B ** (mat 1)" unfolding matrix_mul_rid ..
  also have "... = B ** (A**C)" unfolding AC ..
  also have "... = B ** A ** C" unfolding matrix_mul_assoc ..
  also have "... = C" unfolding BA matrix_mul_lid ..
  finally show "C = B" ..
qed


lemma matrix_vector_mult_zero_eq:
assumes P: "invertible P"
shows "((P**A)*v x = 0) = (A *v x = 0)"
proof (rule iffI)
assume "P ** A *v x = 0" 
hence "matrix_inv P *v (P ** A *v x) = matrix_inv P *v 0" by simp
hence "matrix_inv P *v (P ** A *v x) =  0" by (metis matrix_vector_zero)
hence "(matrix_inv P ** P ** A) *v x =  0" by (metis matrix_vector_mul_assoc)
thus "A *v x =  0" by (metis assms matrix_inv_left matrix_mul_lid)
next
assume "A *v x = 0" 
thus "P ** A *v x = 0" by (metis matrix_vector_mul_assoc matrix_vector_zero)
qed

lemma inj_matrix_vector_mult:
fixes P::"'a::{field}^'n^'m"
assumes P: "invertible P"
shows "inj (op *v P)"
unfolding vec.linear_injective_0
using matrix_left_invertible_ker[of P] P unfolding invertible_def by blast

lemma independent_image_matrix_vector_mult:
fixes P::"'a::{field}^'n^'m"
assumes ind_B: "vec.independent B" and inv_P: "invertible P"
shows "vec.independent ((op *v P)` B)"
proof (rule vec.independent_injective_on_span_image)
  show "vec.independent B" using ind_B .
  show "inj_on (op *v P) (vec.span B)" 
    using inj_matrix_vector_mult[OF inv_P] unfolding inj_on_def by simp
qed

lemma independent_preimage_matrix_vector_mult:
fixes P::"'a::{field}^'n^'n"
assumes ind_B: "vec.independent ((op *v P)` B)" and inv_P: "invertible P"
shows "vec.independent B"
proof -
have "vec.independent ((op *v (matrix_inv P))` ((op *v P)` B))"
  proof (rule independent_image_matrix_vector_mult)
    show "vec.independent (op *v P ` B)" using ind_B .
    show "invertible (matrix_inv P)"
      by (metis matrix_inv_left matrix_inv_right inv_P invertible_def)
    qed
moreover have "(op *v (matrix_inv P))` ((op *v P)` B) = B"
    proof (auto)
      fix x assume x: "x \<in> B" show "matrix_inv P *v (P *v x) \<in> B" 
      by (metis (full_types) x inv_P matrix_inv_left matrix_vector_mul_assoc matrix_vector_mul_lid)
      thus "x \<in> op *v (matrix_inv P) ` op *v P ` B" 
      unfolding image_def 
      by (auto, metis  inv_P matrix_inv_left matrix_vector_mul_assoc matrix_vector_mul_lid)
     qed
ultimately show ?thesis by simp
qed

subsection{*Properties about the dimension of vectors*}

lemma dimension_vector[code_unfold]: "vec.dimension TYPE('a::{field}) TYPE('rows::{mod_type})=CARD('rows)"
proof -
let ?f="\<lambda>x. axis (from_nat x) 1::'a^'rows::{mod_type}"
have "vec.dimension TYPE('a::{field}) TYPE('rows::{mod_type}) = card (cart_basis::('a^'rows::{mod_type}) set)"
  unfolding vec.dimension_def ..
also have "... = card{..<CARD('rows)}" unfolding cart_basis_def 
  proof (rule bij_betw_same_card[symmetric, of ?f], unfold bij_betw_def, unfold inj_on_def axis_eq_axis, auto)
     fix x y assume x: "x < CARD('rows)" and y: "y < CARD('rows)" and eq: "from_nat x = (from_nat y::'rows)"
     show "x = y" using from_nat_eq_imp_eq[OF eq x y] .
     next
     fix i show "axis i 1 \<in> (\<lambda>x. axis (from_nat x::'rows) 1) ` {..<CARD('rows)}" unfolding image_def
     by (auto, metis lessThan_iff to_nat_from_nat to_nat_less_card)
  qed
also have "... = CARD('rows)" by (metis card_lessThan)
finally show ?thesis .
qed

subsection{*Instantiations and interpretations*}

text{*Functions between two real vector spaces form a real vector*}
instantiation "fun" :: (real_vector, real_vector) real_vector
begin

definition "plus_fun f g = (\<lambda>i. f i + g i)"
definition "zero_fun = (\<lambda>i. 0)"
definition "scaleR_fun a f = (\<lambda>i. a *\<^sub>R f i )"

instance proof
  fix a::"'a \<Rightarrow> 'b" and b::"'a \<Rightarrow> 'b" and c::"'a \<Rightarrow> 'b"
  show "a + b + c = a + (b + c)" unfolding fun_eq_iff unfolding plus_fun_def by auto
  show "a + b = b + a" unfolding fun_eq_iff unfolding plus_fun_def by auto
  show " (0::'a \<Rightarrow> 'b) + a = a"  unfolding fun_eq_iff unfolding plus_fun_def zero_fun_def by auto
  show "- a + a = (0::'a \<Rightarrow> 'b)" unfolding fun_eq_iff unfolding plus_fun_def zero_fun_def by auto
  show "a - b = a + - b" unfolding fun_eq_iff unfolding plus_fun_def zero_fun_def by auto
next
  fix a::real and x::"('a \<Rightarrow> 'b)" and y::"'a \<Rightarrow> 'b"
  show "a *\<^sub>R (x + y) = a *\<^sub>R x + a *\<^sub>R y" 
  unfolding fun_eq_iff plus_fun_def scaleR_fun_def scaleR_right.add by auto
next
  fix a::real and b::real and x::"'a \<Rightarrow> 'b" 
  show "(a + b) *\<^sub>R x = a *\<^sub>R x + b *\<^sub>R x" 
    unfolding fun_eq_iff unfolding plus_fun_def scaleR_fun_def unfolding  scaleR_left.add by auto
  show " a *\<^sub>R b *\<^sub>R x = (a * b) *\<^sub>R x" unfolding fun_eq_iff unfolding scaleR_fun_def by auto
  show "(1::real) *\<^sub>R x = x" unfolding fun_eq_iff unfolding scaleR_fun_def by auto
qed
end


instantiation vec :: (type, finite) equal
begin
definition equal_vec :: "('a, 'b::finite) vec => ('a, 'b::finite) vec => bool" 
  where "equal_vec x y = (\<forall>i. x$i = y$i)"
instance 
proof (intro_classes)
  fix x y::"('a, 'b::finite) vec"
  show "equal_class.equal x y = (x = y)" unfolding equal_vec_def using vec_eq_iff by auto
qed
end

instantiation bit :: linorder
begin

definition less_eq_bit :: "bit \<Rightarrow> bit \<Rightarrow> bool"
where "less_eq_bit x y = (y=1 \<or> x=0)"

definition less_bit :: "bit \<Rightarrow> bit \<Rightarrow> bool"
where "less_bit x y = (y=1 \<and> x=0)"

instance
proof (intro_classes, auto simp add: less_eq_bit_def less_bit_def)
qed
end

interpretation matrix: vector_space "(op *k)::'a::{field}=>'a^'cols^'rows=>'a^'cols^'rows"
proof (unfold_locales)
fix a::'a and x y::"'a^'cols^'rows"
show "a *k (x + y) = a *k x + a *k y"
  unfolding matrix_scalar_mult_def vec_eq_iff
  by (simp add: vector_space_over_itself.scale_right_distrib)
next
fix a b::'a and x::"'a^'cols^'rows"
show "(a + b) *k x = a *k x + b *k x"
unfolding matrix_scalar_mult_def vec_eq_iff
  by (simp add: comm_semiring_class.distrib)
show "a *k (b *k x) = a * b *k x"
  unfolding matrix_scalar_mult_def vec_eq_iff by auto
show"1 *k x = x" unfolding matrix_scalar_mult_def vec_eq_iff by auto
qed

subsection{*Properties about lists*}

text{*The following definitions and theorems are developed in order to compute setprods. 
  More theorems and properties can be demonstrated in a similar way to the ones
  about @{term "listsum"}.*}

definition (in monoid_mult) listprod :: "'a list => 'a" where
  "listprod xs = foldr times xs 1"

lemma (in monoid_mult) listprod_simps [simp]:
  "listprod [] = 1"
  "listprod (x # xs) = x * listprod xs"
  by (simp_all add: listprod_def)

lemma (in monoid_mult) listprod_append [simp]:
  "listprod (xs @ ys) = listprod xs * listprod ys"
  by (induct xs) (simp_all add: mult.assoc)

lemma (in comm_monoid_mult) listprod_rev [simp]:
  "listprod (rev xs) = listprod xs"
  by (simp add: listprod_def foldr_fold fold_rev fun_eq_iff ac_simps)

lemma (in monoid_mult) listprod_distinct_conv_setprod_set:
  "distinct xs ==> listprod (map f xs) = setprod f (set xs)"
  by (induct xs) simp_all

lemma setprod_code [code]:
  "setprod f (set xs) = listprod (map f (remdups xs))"
  by (simp add: listprod_distinct_conv_setprod_set)

end
