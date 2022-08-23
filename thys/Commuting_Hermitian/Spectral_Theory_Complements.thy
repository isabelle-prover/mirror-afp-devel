(*
Author: 
  Mnacho Echenim, Université Grenoble Alpes
*)

theory Spectral_Theory_Complements imports "HOL-Combinatorics.Permutations"
"Projective_Measurements.Linear_Algebra_Complements" 
  "Projective_Measurements.Projective_Measurements"

begin 
section \<open>Some preliminary results\<close>

subsection \<open>Roots of a polynomial\<close>

text \<open>Results on polynomials, the main one being that
the set of roots of a polynomial is uniquely defined.\<close>

lemma root_poly_linear:
  shows "poly (\<Prod>a\<leftarrow>L. [:- a, 1:]) (c::'a :: field) = 0 \<Longrightarrow> c\<in> set L"
proof (induct L)
  case Nil
  thus ?case using Nil by simp
next
  case (Cons a L)
  show ?case
  proof (cases "poly (\<Prod>a\<leftarrow>L. [:- a, 1:]) c = 0")
    case True
    then show ?thesis using Cons by auto
  next
    case False
    hence "poly [:- a, 1:] c = 0" using Cons by auto
    hence "a = c" by auto
    thus ?thesis by auto
  qed
qed

lemma poly_root_set_subseteq:
  assumes "(\<Prod>(a::'a::field)\<leftarrow>L. [:- a, 1:]) = (\<Prod>a\<leftarrow>M. [:- a, 1:])"
  shows "set L \<subseteq> set M"
proof
  fix x
  assume "x\<in> set L"
  hence "poly (\<Prod>(a::'a::field)\<leftarrow>L. [:- a, 1:]) x = 0" using linear_poly_root[of x] by simp
  hence "poly (\<Prod>(a::'a::field)\<leftarrow>M. [:- a, 1:]) x = 0" using assms by simp
  thus "x\<in> set M" using root_poly_linear[of M] by simp
qed

lemma poly_root_set_eq:
  assumes "(\<Prod>(a::'a::field)\<leftarrow>L. [:- a, 1:]) = (\<Prod>a\<leftarrow>M. [:- a, 1:])"
  shows "set L = set M" using assms poly_root_set_subseteq
  by (simp add: poly_root_set_subseteq equalityI)

subsection \<open>Linear algebra preliminaries\<close>

lemma minus_zero_vec_eq:
  fixes v::"'a::{ab_group_add} Matrix.vec"
  assumes "dim_vec v = n"
  and "dim_vec w = n" 
  and "v - w = 0\<^sub>v n"
shows "v = w" 
proof -
  have "v = v - w + w" using assms
    by (metis carrier_vec_dim_vec comm_add_vec left_zero_vec 
        minus_add_minus_vec minus_cancel_vec uminus_eq_vec 
        zero_minus_vec)
  also have "... = 0\<^sub>v n + w" using assms by simp
  also have "... = w" using assms left_zero_vec[of w n]
    by (metis carrier_vec_dim_vec)
  finally show ?thesis .
qed

lemma right_minus_zero_mat:
  fixes A::"'a::{group_add} Matrix.mat"
  shows "A - 0\<^sub>m (dim_row A) (dim_col A) = A"
  by (intro eq_matI, auto)

lemma smult_zero:
  shows "(0::'a::comm_ring) \<cdot>\<^sub>m A = 0\<^sub>m (dim_row A) (dim_col A)" by auto

lemma  rank_1_proj_col_carrier:
  assumes "i < dim_col A"
  shows "rank_1_proj (Matrix.col A i) \<in> carrier_mat (dim_row A) (dim_row A)"
proof -
  have "dim_vec (Matrix.col A i) = dim_row A" by simp
  thus ?thesis by (metis rank_1_proj_carrier) 
qed

lemma zero_adjoint:  
  shows "Complex_Matrix.adjoint (0\<^sub>m n m) = ((0\<^sub>m m n):: 'a::conjugatable_field Matrix.mat)"
  by (rule eq_matI, (auto simp add: adjoint_eval))

lemma assoc_mat_mult_vec':
  assumes "A \<in> carrier_mat n n"
  and "B\<in> carrier_mat n n"
  and "C\<in> carrier_mat n n"
and "v\<in> carrier_vec n"
shows "A * B * C *\<^sub>v v = A *\<^sub>v (B *\<^sub>v (C *\<^sub>v v))" using assms
  by (smt (z3) assoc_mult_mat_vec mult_carrier_mat mult_mat_vec_carrier)

lemma adjoint_dim':
  "A \<in> carrier_mat n m \<Longrightarrow> Complex_Matrix.adjoint A \<in> carrier_mat m n"
  using adjoint_dim_col adjoint_dim_row by blast

definition mat_conj where
"mat_conj U V = U * V * (Complex_Matrix.adjoint U)"

lemma mat_conj_adjoint:
  shows "mat_conj (Complex_Matrix.adjoint U) V = 
  Complex_Matrix.adjoint U * V * U" unfolding mat_conj_def
  by (simp add: Complex_Matrix.adjoint_adjoint)

lemma map2_mat_conj_exp:
  assumes "length A = length B"
  shows "map2 (*) (map2 (*) A B) (map Complex_Matrix.adjoint A) = 
    map2 mat_conj A B"  using assms
proof (induct A arbitrary: B)
  case Nil
  then show ?case by simp
next
  case (Cons a A)
  hence "0 < length B" by auto
  hence "B = hd B # (tl B)" by simp
  hence "length (tl B) = length A" using Cons by simp
  have "map2 (*) (map2 (*) (a # A) B) (map Complex_Matrix.adjoint (a # A)) =
    a * hd B * Complex_Matrix.adjoint a # 
    map2 (*) (map2 (*) A (tl B)) (map Complex_Matrix.adjoint A)"
    by (metis (no_types, lifting) \<open>B = hd B # tl B\<close> list.map(2) 
        split_conv zip_Cons_Cons)
  also have "... = mat_conj a (hd B) # map2 mat_conj A (tl B)" 
    using Cons \<open>length (tl B) = length A\<close> 
    unfolding mat_conj_def
    by presburger
  also have "... = map2 mat_conj (a#A) B" using \<open>B = hd B # (tl B)\<close>
    by (metis (no_types, opaque_lifting) list.map(2) prod.simps(2) 
        zip_Cons_Cons) 
  finally show ?case .
qed

lemma mat_conj_unit_commute:
  assumes "unitary U"
  and "U*A = A*U"
  and "A\<in> carrier_mat n n"
  and "U\<in> carrier_mat n n"
shows "mat_conj U A = A"
proof -
  have "mat_conj U A = A*U * Complex_Matrix.adjoint U" using assms 
    unfolding mat_conj_def by simp
  also have "... = A * (U * Complex_Matrix.adjoint U)"
  proof (rule assoc_mult_mat, auto simp add: assms)
    show "U \<in> carrier_mat (dim_col A) (dim_col U)"
      using assms(3) assms(4) by auto
  qed
  also have "... = A" using assms by simp
  finally show ?thesis .
qed

lemma hermitian_mat_conj:
  assumes "A\<in> carrier_mat n n"
  and "U \<in> carrier_mat n n"
  and "hermitian A"
shows "hermitian (mat_conj U A)" 
proof -
  have "Complex_Matrix.adjoint (U * A * Complex_Matrix.adjoint U) =
    U * Complex_Matrix.adjoint (U * A)"
    by (metis (no_types, lifting) Complex_Matrix.adjoint_adjoint adjoint_dim' 
        adjoint_mult assms(1) assms(2) mult_carrier_mat)
  also have "... = U * ((Complex_Matrix.adjoint A) *  Complex_Matrix.adjoint U)"
    by (metis adjoint_mult assms(1) assms(2))
  also have "... = U * A * Complex_Matrix.adjoint U"
    by (metis adjoint_dim' assms assoc_mult_mat hermitian_def)
  finally show ?thesis unfolding hermitian_def mat_conj_def .
qed

lemma hermitian_mat_conj':
  assumes "A\<in> carrier_mat n n"
  and "U \<in> carrier_mat n n"
  and "hermitian A"
shows "hermitian (mat_conj (Complex_Matrix.adjoint U) A)"
  by (metis Complex_Matrix.adjoint_adjoint adjoint_dim_col assms 
      carrier_matD(1) carrier_matD(2) carrier_mat_triv hermitian_mat_conj) 

lemma mat_conj_uminus_eq:
  assumes "A\<in> carrier_mat n n"
  and "U\<in> carrier_mat n n"
  and "B \<in> carrier_mat n n"
  and "A = mat_conj U B"  
shows "-A = mat_conj U (-B)" using assms unfolding mat_conj_def by auto

lemma mat_conj_smult:
  assumes "A\<in> carrier_mat n n"
  and "U\<in> carrier_mat n n"
  and "B \<in> carrier_mat n n"
  and "A = U * B * (Complex_Matrix.adjoint U)"  
shows "x  \<cdot>\<^sub>m A = U * (x  \<cdot>\<^sub>m B) * (Complex_Matrix.adjoint U)" using assms mult_smult_distrib
  by (smt (z3) adjoint_dim' mult_carrier_mat mult_smult_assoc_mat)

lemma mult_adjoint_hermitian:
  fixes A::"'a::conjugatable_field Matrix.mat"
  assumes "A\<in> carrier_mat n m"
  shows "hermitian ((Complex_Matrix.adjoint A) * A)" unfolding hermitian_def
proof -
  define C where "C = (Complex_Matrix.adjoint A) * A"
  have "Complex_Matrix.adjoint C = 
    Complex_Matrix.adjoint A * Complex_Matrix.adjoint (Complex_Matrix.adjoint A)" 
    using adjoint_mult assms C_def by (metis adjoint_dim' assms)
  also have "... = Complex_Matrix.adjoint A * A" using assms
    by (simp add: Complex_Matrix.adjoint_adjoint)
  finally show "Complex_Matrix.adjoint C = C" using C_def by simp
qed

lemma hermitian_square_hermitian: 
fixes A::"'a::conjugatable_field Matrix.mat"
  assumes "hermitian A"
  shows "hermitian (A * A)" 
proof -
  have "Complex_Matrix.adjoint (A * A) = Complex_Matrix.adjoint A * (Complex_Matrix.adjoint A)"
    using adjoint_mult by (metis assms hermitian_square)
  also have "... = A * A" using assms unfolding hermitian_def by simp
  finally show ?thesis unfolding hermitian_def .
qed

section \<open>Properties of the spectrum of a matrix\<close>

subsection \<open>Results on diagonal matrices\<close>

lemma diagonal_mat_uminus:
  fixes A::"'a::{ring} Matrix.mat"
  assumes "diagonal_mat A"
  shows "diagonal_mat (-A)" using assms unfolding diagonal_mat_def uminus_mat_def by auto

lemma diagonal_mat_smult:
  fixes A::"'a::{ring} Matrix.mat"
  assumes "diagonal_mat A"
  shows "diagonal_mat (x \<cdot>\<^sub>mA)" using assms unfolding diagonal_mat_def uminus_mat_def by auto


lemma diagonal_imp_upper_triangular:
  assumes "diagonal_mat A"
  and "A \<in> carrier_mat n n"
  shows "upper_triangular A"  unfolding  upper_triangular_def
proof (intro allI impI)
  fix i j
  assume "i < dim_row A" and "j < i"
  hence "j < dim_col A" "j \<noteq> i" using assms by auto
  thus "A $$ (i,j) = 0" using assms \<open>i < dim_row A\<close> unfolding diagonal_mat_def by simp
qed

lemma set_diag_mat_uminus:
  assumes "A\<in> carrier_mat n n"
  shows "set (diag_mat (-A)) = {-a |a. a\<in> set (diag_mat A)}" (is "?L = ?R")
proof
  show "?L \<subseteq> ?R"
  proof
    fix x
    assume "x \<in> set (diag_mat (- A))"
    hence "\<exists>i < length (diag_mat (-A)). nth (diag_mat (-A))  i = x" 
      using in_set_conv_nth[of x] by simp
    from this obtain i where "i < length (diag_mat (-A))" and "nth (diag_mat (-A))  i = x"
      by auto note iprop = this
    hence "i < dim_row (-A)" unfolding diag_mat_def by simp
    hence "i < n" using assms by simp
    have "x = (-A)$$(i,i)" using iprop unfolding diag_mat_def by simp
    also have "... = - A$$(i,i)" using \<open>i < n\<close> assms unfolding uminus_mat_def by auto
    also have "... \<in> ?R" using iprop assms \<open>i < n\<close> 
        in_set_conv_nth[of "A$$(i,i)"] by (metis (mono_tags, lifting) carrier_matD(1) 
        diag_elems_mem diag_elems_set_diag_mat mem_Collect_eq)
    finally show "x \<in> ?R" .
  qed
next
  show "?R \<subseteq> ?L"
  proof
    fix x
    assume "x\<in> ?R"
    hence "\<exists>i < length (diag_mat A). -(nth (diag_mat A)  i) = x" 
      using in_set_conv_nth[of x] by (smt (z3) in_set_conv_nth mem_Collect_eq)
    from this obtain i where "i < length (diag_mat A)" and "-(nth (diag_mat A)  i) = x"
      by auto note iprop = this
    hence "i < dim_row (-A)" unfolding diag_mat_def by simp
    hence "i < n" using assms by simp
    have "x = -A$$(i,i)" using iprop unfolding diag_mat_def by simp
    also have "... = (- A)$$(i,i)" using \<open>i < n\<close> assms unfolding uminus_mat_def by auto
    also have "... \<in> ?L" using iprop assms \<open>i < n\<close> 
        in_set_conv_nth[of "A$$(i,i)"]
      by (metis \<open>i < dim_row (- A)\<close> diag_elems_mem diag_elems_set_diag_mat)
    finally show "x \<in> ?L" .
  qed
qed

lemma set_diag_mat_smult:
  assumes "A\<in> carrier_mat n n"
  shows "set (diag_mat (x \<cdot>\<^sub>m A)) = {x * a |a. a\<in> set (diag_mat A)}" (is "?L = ?R")
proof
  show "?L \<subseteq> ?R"
  proof
    fix b
    assume "b \<in> set (diag_mat (x \<cdot>\<^sub>m A))"
    hence "\<exists>i < length (diag_mat (x \<cdot>\<^sub>m A)). nth (diag_mat (x \<cdot>\<^sub>m A))  i = b" 
      using in_set_conv_nth[of b] by simp
    from this obtain i where "i < length (diag_mat (x \<cdot>\<^sub>m A))" and "nth (diag_mat (x \<cdot>\<^sub>m A))  i = b"
      by auto note iprop = this
    hence "i < dim_row (x \<cdot>\<^sub>m A)" unfolding diag_mat_def by simp
    hence "i < n" using assms by simp
    have "b = (x \<cdot>\<^sub>m A)$$(i,i)" using iprop unfolding diag_mat_def by simp
    also have "... = x * A$$(i,i)" using \<open>i < n\<close> assms unfolding uminus_mat_def by auto
    also have "... \<in> ?R" using iprop assms \<open>i < n\<close> 
        in_set_conv_nth[of "A$$(i,i)"]
      by (metis (mono_tags, lifting) carrier_matD(1) diag_elems_mem diag_elems_set_diag_mat 
          mem_Collect_eq) 
    finally show "b \<in> ?R" .
  qed
next
  show "?R \<subseteq> ?L"
  proof
    fix b
    assume "b\<in> ?R"
    hence "\<exists>i < length (diag_mat A). x * (nth (diag_mat A)  i) = b" 
      using in_set_conv_nth[of x] by (smt (z3) in_set_conv_nth mem_Collect_eq)
    from this obtain i where "i < length (diag_mat A)" and "x * (nth (diag_mat A)  i) = b"
      by auto note iprop = this
    hence "i < dim_row (x \<cdot>\<^sub>m A)" unfolding diag_mat_def by simp
    hence "i < n" using assms by simp
    have "b = x *A$$(i,i)" using iprop unfolding diag_mat_def by simp
    also have "... = (x \<cdot>\<^sub>m A)$$(i,i)" using \<open>i < n\<close> assms unfolding uminus_mat_def by auto
    also have "... \<in> ?L" using iprop assms \<open>i < n\<close> 
        in_set_conv_nth[of "A$$(i,i)"]
      by (metis \<open>i < dim_row (x \<cdot>\<^sub>m A)\<close> diag_elems_mem diag_elems_set_diag_mat)
    finally show "b \<in> ?L" .
  qed
qed


lemma diag_mat_diagonal_eq:
  assumes "diag_mat A = diag_mat B"
and "diagonal_mat A"
and "diagonal_mat B"
and "dim_col A = dim_col B"
shows "A = B"
proof
  show c: "dim_col A = dim_col B" using assms by simp
  show r: "dim_row A = dim_row B" using assms unfolding diag_mat_def
  proof -
    assume "map (\<lambda>i. A $$ (i, i)) [0..<dim_row A] = map (\<lambda>i. B $$ (i, i)) [0..<dim_row B]"
    then show ?thesis
      by (metis (lifting) length_map length_upt verit_minus_simplify(2))
  qed
  fix i j
  assume "i < dim_row B" and "j < dim_col B"
  show "A $$ (i, j) = B $$ (i, j)"
  proof (cases "i = j")
    case False
    thus ?thesis using assms c r unfolding diagonal_mat_def
      by (simp add: \<open>dim_row A = dim_row B\<close> \<open>i \<noteq> j\<close> \<open>i < dim_row B\<close> \<open>j < dim_col B\<close>)
  next
    case True
    hence "A $$ (i,j) = A $$ (i,i)" by simp
    also have "... = (diag_mat A)!i" using c r \<open>i < dim_row B\<close> unfolding diag_mat_def by simp
    also have "... = (diag_mat B)!i" using assms by simp
    also have "... = B $$(i,i)"  using c r \<open>i < dim_row B\<close> unfolding diag_mat_def by simp
    also have "... = B $$ (i,j)" using True by simp
    finally show "A $$(i,j) = B $$(i,j)" .
  qed
qed


lemma diag_elems_ne:
  assumes "B \<in> carrier_mat n n"
  and "0 < n"
shows "diag_elems B \<noteq> {}"
proof -
  have "B $$(0,0) \<in> diag_elems B" using assms by simp
  thus ?thesis by auto
qed

lemma diagonal_mat_mult_vec:
  fixes B::"'a::conjugatable_field Matrix.mat"
  assumes "diagonal_mat B"
  and "B \<in> carrier_mat n n"
  and "v\<in> carrier_vec n"
  and "i < n"
shows "vec_index (B *\<^sub>v v) i = B $$ (i,i) * (vec_index v i)"
proof -
  have "vec_index (B *\<^sub>v v) i = Matrix.scalar_prod (Matrix.row B i)  v" using mult_mat_vec_def assms 
    by simp
  also have "... = (\<Sum> j \<in> {0 ..< n}. vec_index (Matrix.row B i) j * (vec_index v j))"
    using Matrix.scalar_prod_def assms(3) carrier_vecD by blast
  also have "... = (\<Sum> j \<in> {0 ..< n}. B $$ (i,j) * (vec_index v j))"
  proof -
    have "\<And>j. j < n \<Longrightarrow> vec_index (Matrix.row B i) j = B $$ (i,j)" using assms by auto
    thus ?thesis by auto
  qed
  also have "... = B $$ (i,i) * (vec_index v i)" 
  proof (rule sum_but_one, (auto simp add: assms)) 
    show "\<And>j. j < n \<Longrightarrow> j \<noteq> i \<Longrightarrow> B $$ (i, j) = 0" using assms unfolding diagonal_mat_def 
      by force
  qed
  finally show ?thesis .
qed

lemma diagonal_mat_mult_index:
  fixes B::"'a::{ring} Matrix.mat"
  assumes "diagonal_mat A"
  and "A\<in> carrier_mat n n"
  and "B \<in> carrier_mat n n"
  and "i < n"
  and "j < n"
  shows "(A * B) $$ (i,j) = A$$(i,i) * B$$(i,j)" unfolding diagonal_mat_def
proof -
  have "dim_row (A * B) = n" using assms by simp
  have "dim_col (A * B) = n" using  assms by simp
  have jvec: "\<And>j. j < n \<Longrightarrow> dim_vec (Matrix.col B j) = n" using assms by simp
  have "(A * B) $$ (i,j) = Matrix.scalar_prod (Matrix.row A i) (Matrix.col B j)" 
    using assms by (metis carrier_matD(1) carrier_matD(2) index_mult_mat(1))
  also have "... = 
    (\<Sum> k \<in> {0 ..< n}. vec_index (Matrix.row A i) k * 
      vec_index (Matrix.col B j) k)"
    using assms  jvec unfolding Matrix.scalar_prod_def by simp
  also have "... = vec_index (Matrix.row A i) i * vec_index (Matrix.col B j) i"     
  proof (rule sum_but_one)
    show "i < n" using assms \<open>dim_row (A * B) = n\<close> by simp
    show "\<forall>k<n. k \<noteq> i \<longrightarrow> vec_index (Matrix.row A i) k = 0" using assms \<open>i < n\<close> 
      unfolding diagonal_mat_def by auto 
  qed
  also have "... = A$$(i,i) * B$$(i,j)" using  assms
    by (metis carrier_matD(1) carrier_matD(2) index_col index_row(1))
  finally show ?thesis .
qed

lemma diagonal_mat_mult_index':
  fixes A::"'a::comm_ring Matrix.mat"
  assumes "A \<in> carrier_mat n n"
and "B\<in> carrier_mat n n"
and "diagonal_mat B"
and "j < n"
and "i < n"
shows "(A*B) $$(i,j) = B$$(j,j) *A $$ (i, j)"
    (*"(B*A) $$(i,j) = B$$(i,i) *A $$ (i, j)"*)
proof -
  have "(A*B) $$ (i,j) = Matrix.scalar_prod (Matrix.row A i) (Matrix.col B j)" using assms 
      times_mat_def[of A] by simp
  also have "... = Matrix.scalar_prod (Matrix.col B j) (Matrix.row A i)" 
    using comm_scalar_prod[of "Matrix.row A i" n] assms by auto
  also have "... = (Matrix.vec_index (Matrix.col B j) j) * (Matrix.vec_index  (Matrix.row A i) j)" 
    unfolding Matrix.scalar_prod_def 
  proof (rule sum_but_one)
    show "j < dim_vec (Matrix.row A i)" using assms by simp
    show "\<forall>ia<dim_vec (Matrix.row A i). ia \<noteq> j \<longrightarrow> Matrix.vec_index (Matrix.col B j) ia = 0" 
      using assms
      by (metis carrier_matD(1) carrier_matD(2) diagonal_mat_def index_col index_row(2))
  qed
  also have "... = B $$(j,j) * A $$(i,j)" using assms by auto
  finally show "(A * B) $$ (i, j) = B $$ (j, j) * A $$ (i, j)" .
qed

lemma diagonal_mat_times_diag:
  assumes "A\<in> carrier_mat n n"
  and "B\<in> carrier_mat n n"
  and "diagonal_mat A"
and "diagonal_mat B"
shows "diagonal_mat (A*B)"  unfolding diagonal_mat_def
proof (intro allI impI)
  fix i j
  assume "i < dim_row (A * B)" and "j < dim_col (A * B)" and "i \<noteq> j"
  thus "(A * B) $$ (i, j) = 0" using assms diag_mat_mult_diag_mat[of A n B]
    by simp
qed

lemma diagonal_mat_commute:
  fixes A::"'a::{comm_ring} Matrix.mat"
  assumes "A\<in> carrier_mat n n"
  and "B\<in> carrier_mat n n"
  and "diagonal_mat A"
and "diagonal_mat B"
shows "A * B = B * A"
proof (rule eq_matI)
  show "dim_row (A * B) = dim_row (B * A)" using assms by simp
  show "dim_col (A * B) = dim_col (B * A)" using assms by simp
  have bac: "B*A \<in> carrier_mat n n" using assms by simp
  fix i j
  assume "i < dim_row (B*A)" and "j < dim_col (B*A)" note ij = this
  have "(A * B) $$ (i, j) = A $$ (i, j) * B$$(i,j)" 
    using ij diagonal_mat_mult_index assms bac
    by (metis carrier_matD(1) carrier_matD(2) diagonal_mat_def mult_zero_right)
  also have "... = B$$(i,j) * A $$ (i, j)"
    by (simp add: Groups.mult_ac(2))
  also have "... = (B*A) $$ (i,j)" using ij diagonal_mat_mult_index assms bac
    by (metis carrier_matD(1) carrier_matD(2) diagonal_mat_def mult_not_zero)
  finally show "(A * B) $$ (i, j) = (B*A) $$ (i,j)" .
qed

lemma diagonal_mat_sq_index:
  fixes B::"'a::{ring} Matrix.mat"
  assumes "diagonal_mat B"
  and "B \<in> carrier_mat n n"
  and "i < n"
  and "j < n"
  shows "(B * B) $$ (i,j) = B$$(i,i) * B$$(j,i)" 
proof -
  have "(B * B) $$ (i,j) = B$$(i,i) * B$$(i,j)" 
    using assms diagonal_mat_mult_index[of B] by simp
  also have "... = B$$(i,i) * B$$(j,i)" using assms unfolding diagonal_mat_def
    by (metis carrier_matD(1) carrier_matD(2))
  finally show ?thesis .
qed

lemma diagonal_mat_sq_index':
  fixes B::"'a::{ring} Matrix.mat"
  assumes "diagonal_mat B"
  and "B \<in> carrier_mat n n"
  and "i < n"
  and "j < n"
  shows "(B * B) $$ (i,j) = B$$(i,j) * B$$(i,j)" 
proof -
  have eq: "(B * B) $$ (i,j) = B$$(i,i) * B$$(j,i)" 
    using assms diagonal_mat_sq_index by metis
  show ?thesis
  proof (cases "i = j")
    case True
    then show ?thesis using eq by simp
  next
    case False
    hence "B$$(i,j) = 0" using assms unfolding diagonal_mat_def by simp
    hence "(B * B) $$ (i,j) = 0" using eq
      by (metis assms diagonal_mat_mult_index mult_not_zero) 
    thus ?thesis using eq \<open>B$$(i,j) = 0\<close> by simp
  qed
qed

lemma diagonal_mat_sq_diag:
  fixes B::"'a::{ring} Matrix.mat"
  assumes "diagonal_mat B"
  and "B \<in> carrier_mat n n"
  shows "diagonal_mat (B * B)" unfolding diagonal_mat_def
proof (intro allI impI)
  have "dim_row (B * B) = n" using assms by simp
  have "dim_col (B * B) = n" using  assms by simp
  have jvec: "\<And>j. j < n \<Longrightarrow> dim_vec (Matrix.col B j) = n" using assms by simp
  fix i j
  assume "i < dim_row (B * B)" 
  and "j < dim_col (B * B)" 
  and "i \<noteq> j" note ijprops = this
  thus "(B * B) $$ (i,j) = 0" using diagonal_mat_sq_index
    by (metis \<open>dim_col (B * B) = n\<close> \<open>dim_row (B * B) = n\<close> assms(1) assms(2) carrier_matD(1) 
        carrier_matD(2) diagonal_mat_def mult_not_zero)
qed

lemma real_diagonal_hermitian:
  fixes B::"complex Matrix.mat"
  assumes "B\<in> carrier_mat n n"
  and "diagonal_mat B"
  and "\<forall>i < dim_row B. B$$(i, i) \<in> Reals"
shows "hermitian B" unfolding hermitian_def
proof (rule eq_matI)
  show "dim_row (Complex_Matrix.adjoint B) = dim_row B" using assms by auto
  show "dim_col (Complex_Matrix.adjoint B) = dim_col B" using assms by auto
next
  fix i j
  assume "i < dim_row B"  and "j < dim_col B" note ij = this
  show "Complex_Matrix.adjoint B $$ (i, j) = B $$ (i, j)"
  proof (cases "i = j")
    case True
    thus ?thesis  using assms ij Reals_cnj_iff
      unfolding diagonal_mat_def Complex_Matrix.adjoint_def by simp    
  next
    case False
    then show ?thesis using assms ij 
      unfolding diagonal_mat_def Complex_Matrix.adjoint_def by simp
  qed
qed

subsection \<open>Unitary equivalence\<close>

definition unitarily_equiv where
"unitarily_equiv A B U \<equiv> (unitary U \<and> 
  similar_mat_wit A B U (Complex_Matrix.adjoint U))"

lemma unitarily_equivD:
  assumes "unitarily_equiv A B U"
  shows "unitary U" 
    "similar_mat_wit A B U (Complex_Matrix.adjoint U)" using assms
  unfolding unitarily_equiv_def by auto

lemma unitarily_equivI:
  assumes "similar_mat_wit A B U (Complex_Matrix.adjoint U)"
  and "unitary U"
shows "unitarily_equiv A B U" using assms 
  unfolding unitarily_equiv_def by simp

lemma unitarily_equivI':
  assumes "A =  mat_conj U B"
  and "unitary U"
  and "A\<in> carrier_mat n n"
  and "B\<in> carrier_mat n n"
shows "unitarily_equiv A B U" using assms 
  unfolding unitarily_equiv_def similar_mat_wit_def
  by (metis (mono_tags, opaque_lifting) Complex_Matrix.unitary_def 
      carrier_matD(1) empty_subsetI index_mult_mat(2) index_one_mat(2) 
      insert_commute insert_subset unitary_adjoint unitary_simps(1) 
      unitary_simps(2) mat_conj_def) 

lemma unitarily_equiv_carrier:
  assumes "A\<in> carrier_mat n n"
  and "unitarily_equiv A B U"
shows "B \<in> carrier_mat n n" "U\<in> carrier_mat n n"
proof -
  show "B \<in> carrier_mat n n"
    by (metis assms carrier_matD(1) similar_mat_witD(5) unitarily_equivD(2))
  show "U \<in> carrier_mat n n"
    by (metis assms similar_mat_witD2(6) unitarily_equivD(2))
qed

lemma unitarily_equiv_carrier':
  assumes "unitarily_equiv A B U"
  shows "A \<in> carrier_mat (dim_row A) (dim_row A)"
    "B \<in> carrier_mat (dim_row A) (dim_row A)" 
    "U\<in> carrier_mat (dim_row A) (dim_row A)"
proof -
  show "A \<in> carrier_mat (dim_row A) (dim_row A)"
    by (metis assms carrier_mat_triv similar_mat_witD2(4) unitarily_equivD(2))
  thus "U \<in> carrier_mat (dim_row A) (dim_row A)"
    using assms unitarily_equiv_carrier(2) by blast
  show "B \<in> carrier_mat (dim_row A) (dim_row A)"
    by (metis assms similar_mat_witD(5) unitarily_equivD(2))
qed

lemma unitarily_equiv_eq:
  assumes "unitarily_equiv A B U"
  shows "A = U * B * (Complex_Matrix.adjoint U)" using assms 
  unfolding unitarily_equiv_def similar_mat_wit_def by meson

lemma unitarily_equiv_smult:
  assumes "A\<in> carrier_mat n n" 
  and "unitarily_equiv A B U"
  shows "unitarily_equiv (x \<cdot>\<^sub>m A) (x \<cdot>\<^sub>m B) U"
proof (rule unitarily_equivI)
  show "similar_mat_wit (x \<cdot>\<^sub>m A) (x \<cdot>\<^sub>m B) U (Complex_Matrix.adjoint U)" 
    using mat_conj_smult assms
    by (simp add: similar_mat_wit_smult unitarily_equivD(2))
  show "unitary U" using assms unitarily_equivD(1)[of A] by simp
qed

lemma unitarily_equiv_uminus:
  assumes "A\<in> carrier_mat n n" 
  and "unitarily_equiv A B U"
  shows "unitarily_equiv (-A) (-B) U"
proof (rule unitarily_equivI)
  show "similar_mat_wit (-A) (-B) U (Complex_Matrix.adjoint U)" 
    using mat_conj_uminus_eq assms
    by (smt (z3) adjoint_dim_col adjoint_dim_row carrier_matD(1)
        carrier_matD(2) carrier_mat_triv index_uminus_mat(2)
        index_uminus_mat(3) similar_mat_witI unitarily_equivD(1)
        unitarily_equiv_carrier(1) unitarily_equiv_carrier(2)
        unitarily_equiv_eq unitary_simps(1) unitary_simps(2) mat_conj_def)
  show "unitary U" using assms unitarily_equivD(1)[of A] by simp
qed

lemma unitarily_equiv_adjoint:
  assumes "unitarily_equiv A B U"
  shows "unitarily_equiv B A (Complex_Matrix.adjoint U)" 
  unfolding unitarily_equiv_def
proof
  show "Complex_Matrix.unitary (Complex_Matrix.adjoint U)"
    using Complex_Matrix.unitary_def assms unitarily_equiv_def unitary_adjoint 
    by blast
  have "similar_mat_wit B A (Complex_Matrix.adjoint U) U" 
    unfolding similar_mat_wit_def Let_def
  proof (intro conjI)
    show car: "{B, A, Complex_Matrix.adjoint U, U} \<subseteq> 
      carrier_mat (dim_row B) (dim_row B)"
      by (metis assms insert_commute similar_mat_wit_def 
          similar_mat_wit_dim_row unitarily_equivD(2))
    show "Complex_Matrix.adjoint U * U = 1\<^sub>m (dim_row B)" using car
      by (meson assms insert_subset unitarily_equivD(1) unitary_simps(1))
    show "U * Complex_Matrix.adjoint U = 1\<^sub>m (dim_row B)"
      by (meson assms similar_mat_wit_def similar_mat_wit_sym 
          unitarily_equivD(2)) 
    have "Complex_Matrix.adjoint U * A * U =
      Complex_Matrix.adjoint U * (U * B * Complex_Matrix.adjoint U) * U"
      using assms unitarily_equiv_eq by auto
    also have "... = B"
      by (metis assms similar_mat_wit_def similar_mat_wit_sym unitarily_equivD(2))
    finally show "B = Complex_Matrix.adjoint U * A * U" by simp
  qed
  thus "similar_mat_wit B A (Complex_Matrix.adjoint U) 
    (Complex_Matrix.adjoint (Complex_Matrix.adjoint U))"
    by (simp add: Complex_Matrix.adjoint_adjoint)
qed

lemma unitary_mult_conjugate:
  assumes "A \<in> carrier_mat n n"
  and "V\<in> carrier_mat n n"
  and "U\<in> carrier_mat n n"
  and "B\<in> carrier_mat n n"
  and "unitary V"
  and "mat_conj (Complex_Matrix.adjoint V) A = mat_conj U B"
  shows "A = V* U * B * Complex_Matrix.adjoint (V * U)"
proof -
  have "Complex_Matrix.adjoint V *A * V \<in> carrier_mat n n" using assms
    by (metis adjoint_dim_row carrier_matD(2) carrier_mat_triv 
        index_mult_mat(2) index_mult_mat(3)) 
  have "A * V = V * (Complex_Matrix.adjoint V) *  (A * V)" using assms by simp
  also have "... = V * (Complex_Matrix.adjoint V *(A * V))" 
  proof (rule assoc_mult_mat, auto simp add: assms)
    show "A * V \<in> carrier_mat (dim_row V) (dim_row V)" using assms by auto
  qed
  also have "... = V * (Complex_Matrix.adjoint V *A * V)"
    by (metis adjoint_dim' assms(1) assms(2) assoc_mult_mat)
  also have "... = V * (U * B * (Complex_Matrix.adjoint U))" using assms
    by (simp add: Complex_Matrix.adjoint_adjoint mat_conj_def)
  also have "... = V * (U * (B * (Complex_Matrix.adjoint U)))"
    by (metis adjoint_dim' assms(3) assms(4) assoc_mult_mat)
  also have "... = V * U * (B * (Complex_Matrix.adjoint U))" 
  proof (rule assoc_mult_mat[symmetric], auto simp add: assms)
    show "U \<in> carrier_mat (dim_col V) (dim_row B)" using assms by auto
  qed
  also have "... = V * U * B * (Complex_Matrix.adjoint U)" 
  proof (rule assoc_mult_mat[symmetric], auto simp add: assms)
    show "B \<in> carrier_mat (dim_col U) (dim_col U)" using assms by auto
  qed
  finally have eq: "A * V = V * U * B * (Complex_Matrix.adjoint U)" .
  have "A = A * (V * Complex_Matrix.adjoint V)" using assms by simp
  also have "... = A * V * Complex_Matrix.adjoint V" 
  proof (rule assoc_mult_mat[symmetric], auto simp add: assms)
    show "V \<in> carrier_mat (dim_col A) (dim_col V)" using assms by auto
  qed
  also have "... = V * U * B * (Complex_Matrix.adjoint U) * 
    (Complex_Matrix.adjoint V)" using eq by simp
  also have "... = V * U * B * ((Complex_Matrix.adjoint U) * 
    (Complex_Matrix.adjoint V))"
  proof (rule assoc_mult_mat, auto simp add: assms)
    show "Complex_Matrix.adjoint U \<in> carrier_mat (dim_col B) (dim_col V)"
      using adjoint_dim' assms by auto
  qed
  also have "... = V* U * B * Complex_Matrix.adjoint (V * U)"
    by (metis adjoint_mult assms(2) assms(3))
  finally show ?thesis .
qed

lemma unitarily_equiv_conjugate:
  assumes "A\<in> carrier_mat n n"
  and "V\<in> carrier_mat n n"
  and "U \<in> carrier_mat n n"
  and "B\<in> carrier_mat n n"
  and "unitarily_equiv (mat_conj (Complex_Matrix.adjoint V) A) B U"
  and "unitary V"
  shows "unitarily_equiv A B (V * U)" 
  unfolding unitarily_equiv_def
proof
  show "Complex_Matrix.unitary (V*U)" using assms
    by (simp add: unitarily_equivD(1) unitary_times_unitary)
  show "similar_mat_wit A B (V*U) (Complex_Matrix.adjoint (V*U))"
    unfolding similar_mat_wit_def Let_def
  proof (intro conjI)
    show "{A, B, V*U, Complex_Matrix.adjoint (V*U)} \<subseteq> 
      carrier_mat (dim_row A) (dim_row A)" using assms by auto
    show "V*U * Complex_Matrix.adjoint (V*U) = 1\<^sub>m (dim_row A)"
      by (metis Complex_Matrix.unitary_def \<open>Complex_Matrix.unitary (V * U)\<close> 
          assms(1) assms(2) carrier_matD(1) index_mult_mat(2) inverts_mat_def)
    show "Complex_Matrix.adjoint (V * U) * (V * U) = 1\<^sub>m (dim_row A)"
      by (metis Complex_Matrix.unitary_def \<open>Complex_Matrix.unitary (V * U)\<close> 
          \<open>V * U * Complex_Matrix.adjoint (V * U) = 1\<^sub>m (dim_row A)\<close> 
          index_mult_mat(2) index_one_mat(2) unitary_simps(1))
    show "A = V * U * B * Complex_Matrix.adjoint (V * U)"
    proof (rule unitary_mult_conjugate[of _ n], auto simp add: assms)
      show "mat_conj (Complex_Matrix.adjoint V) A = mat_conj U B" using assms
        by (simp add: mat_conj_def unitarily_equiv_eq)
    qed
  qed
qed

lemma mat_conj_commute:
  assumes "A \<in> carrier_mat n n"
  and "B\<in> carrier_mat n n"
  and "U \<in> carrier_mat n n"
  and "unitary U"
  and "A*B = B*A"
shows "(mat_conj (Complex_Matrix.adjoint U) A) * 
  (mat_conj (Complex_Matrix.adjoint U) B) = 
  (mat_conj (Complex_Matrix.adjoint U) B) * 
  (mat_conj (Complex_Matrix.adjoint U) A)" (is "?L*?R = ?R* ?L")
proof -
  have u: "Complex_Matrix.adjoint U \<in> carrier_mat n n" using assms 
    by (simp add: adjoint_dim')
  have ca: "Complex_Matrix.adjoint U * A * U \<in> carrier_mat n n"
    using assms by auto
  have cb: "Complex_Matrix.adjoint U * B * U \<in> carrier_mat n n"
    using assms by auto
  have  "?L * ?R = 
    ?L * (Complex_Matrix.adjoint U * (B * U))"
  proof -
    have "Complex_Matrix.adjoint U * B * U = 
      Complex_Matrix.adjoint U * (B * U)"
      using assoc_mult_mat[of _ n n B n U] assms
      by (meson adjoint_dim')
    thus ?thesis using mat_conj_adjoint by metis
  qed
  also have "... = ?L * Complex_Matrix.adjoint U * (B*U)"
  proof -
    have "\<exists>na nb. Complex_Matrix.adjoint U \<in> carrier_mat n na \<and> 
      B * U \<in> carrier_mat na nb"
      by (metis (no_types) assms(2) carrier_matD(1) carrier_mat_triv index_mult_mat(2) u)
    then show ?thesis using ca
      by (metis assoc_mult_mat mat_conj_adjoint)
  qed 
  also have "... = Complex_Matrix.adjoint U * A* 
    (U * (Complex_Matrix.adjoint U)) * (B * U)" 
  proof -
    have "Complex_Matrix.adjoint U * A * U * Complex_Matrix.adjoint U =
      Complex_Matrix.adjoint U * A * (U * Complex_Matrix.adjoint U)"
      using assoc_mult_mat[of "Complex_Matrix.adjoint U * A" n n]
      by (metis assms(1) assms(3) mult_carrier_mat u)
    thus ?thesis by (simp add: mat_conj_adjoint)
  qed
  also have "... = Complex_Matrix.adjoint U * A*  (B * U)"
    using assms by auto
  also have "... = Complex_Matrix.adjoint U * A * B * U" 
  proof (rule assoc_mult_mat[symmetric], auto simp add: assms)
    show "B \<in> carrier_mat (dim_col A) (dim_row U)" using assms by simp
  qed
  also have "... = Complex_Matrix.adjoint U * (A * B) * U"
    using assms u by auto
  also have "... = Complex_Matrix.adjoint U * (B * A) * U" using assms by simp
  also have "... = Complex_Matrix.adjoint U * B * A * U"
    using assms u by auto 
  also have "... = Complex_Matrix.adjoint U * B * (A * U)"
  proof (rule assoc_mult_mat, auto simp add: assms)
    show "A \<in> carrier_mat (dim_col B) (dim_row U)"
      using assms by simp 
  qed
  also have "... = Complex_Matrix.adjoint U * B* 
    (U * (Complex_Matrix.adjoint U)) * (A * U)" 
    using assms by auto
  also have "... = Complex_Matrix.adjoint U * B* 
    U * (Complex_Matrix.adjoint U) * (A * U)" 
  proof -
    have "Complex_Matrix.adjoint U * B * U * Complex_Matrix.adjoint U =
      Complex_Matrix.adjoint U * B * (U * Complex_Matrix.adjoint U)"
    proof (rule assoc_mult_mat, auto simp add: assms)
      show "U \<in> carrier_mat (dim_col B) (dim_col U)" using assms by simp
    qed
    thus ?thesis by simp
  qed
  also have "... = Complex_Matrix.adjoint U * B* 
    U * ((Complex_Matrix.adjoint U) * (A * U))"
  proof (rule assoc_mult_mat, auto simp add: u cb)
    show "A * U \<in> carrier_mat (dim_row U) n" using assms by simp
  qed 
  also have "... = Complex_Matrix.adjoint U * B* 
    U * ((Complex_Matrix.adjoint U) * A * U)"
  proof -
    have "(Complex_Matrix.adjoint U) * (A * U) = 
      (Complex_Matrix.adjoint U) * A * U" 
    proof (rule assoc_mult_mat[symmetric], auto simp add: assms u)
      show "A \<in> carrier_mat (dim_row U) (dim_row U)" using assms by simp
    qed
    thus ?thesis by simp
  qed
  finally show ?thesis by (metis mat_conj_adjoint)
qed

lemma unitarily_equiv_commute:
  assumes "unitarily_equiv A B U"
  and "A*C = C*A"
shows "B * (Complex_Matrix.adjoint U * C * U) = 
Complex_Matrix.adjoint U * C * U * B"
proof -
  note car = unitarily_equiv_carrier'[OF assms(1)]
  have cr: "dim_row C = dim_col A"
    by (metis assms(2) car(1) carrier_matD(2) index_mult_mat(2))
  have cd: "dim_col C = dim_row A"
    by (metis \<open>dim_row C = dim_col A\<close> assms(2) index_mult_mat(2) 
        index_mult_mat(3)) 
  have "Complex_Matrix.adjoint U * A * U = B" 
    using assms unitarily_equiv_adjoint
    by (metis Complex_Matrix.adjoint_adjoint unitarily_equiv_eq)
  thus ?thesis using mat_conj_commute assms car
    by (metis carrier_matD(2) carrier_matI cd cr mat_conj_adjoint 
        unitarily_equivD(1))
qed

definition unitary_diag where
"unitary_diag A B U \<equiv> unitarily_equiv A B U \<and>  diagonal_mat B"

lemma unitary_diagI:
  assumes "similar_mat_wit A B U (Complex_Matrix.adjoint U)"
  and "diagonal_mat B"
  and "unitary U"
shows "unitary_diag A B U" using assms 
  unfolding unitary_diag_def unitarily_equiv_def by simp

lemma unitary_diagI':
  assumes "A\<in> carrier_mat n n"
  and "B\<in> carrier_mat n n"
  and "diagonal_mat B"
  and "unitary U"
  and "A = mat_conj U B"
shows "unitary_diag A B U" unfolding unitary_diag_def
proof
  show "diagonal_mat B" using assms by simp
  show "unitarily_equiv A B U" using assms unitarily_equivI' by metis
qed

lemma unitary_diagD:
  assumes "unitary_diag A B U"
  shows "similar_mat_wit A B U (Complex_Matrix.adjoint U)" 
    "diagonal_mat B" "unitary U" using assms 
  unfolding unitary_diag_def unitarily_equiv_def
  by simp+

lemma unitary_diag_imp_unitarily_equiv[simp]:
assumes "unitary_diag A B U"
shows "unitarily_equiv A B U" using assms unfolding unitary_diag_def by simp

lemma unitary_diag_diagonal[simp]:
  assumes "unitary_diag A B U"
  shows "diagonal_mat B" using assms unfolding unitary_diag_def by simp

lemma unitary_diag_carrier:
  assumes "A\<in> carrier_mat n n"
  and "unitary_diag A B U"
shows "B \<in> carrier_mat n n" "U\<in> carrier_mat n n"
proof -
  show "B \<in> carrier_mat n n" 
    using assms unitarily_equiv_carrier(1)[of A n B U] by simp
  show "U \<in> carrier_mat n n"
    using assms unitarily_equiv_carrier(2)[of A n B U] by simp
qed

lemma unitary_mult_square_eq:
  assumes "A\<in> carrier_mat n n"
  and "U\<in> carrier_mat n n"
  and "B \<in> carrier_mat n n"
  and "A = mat_conj U B"
  and "(Complex_Matrix.adjoint U) * U = 1\<^sub>m n"
shows "A * A = mat_conj U (B*B)"
proof -
  have "A * A = U * B * (Complex_Matrix.adjoint U) * (U * B * (Complex_Matrix.adjoint U))" 
    using assms unfolding mat_conj_def by simp
  also have "... = U * B * ((Complex_Matrix.adjoint U) * U) * (B * (Complex_Matrix.adjoint U))"
    by (smt (z3) adjoint_dim_col adjoint_dim_row assms(3) assms(5) assoc_mult_mat carrier_matD(2) 
        carrier_mat_triv index_mult_mat(2) index_mult_mat(3) right_mult_one_mat')
  also have "... = U * B * (B * (Complex_Matrix.adjoint U))" using assms by simp
  also have "... = U * (B * B) * (Complex_Matrix.adjoint U)"
    by (smt (z3) adjoint_dim_row assms(2) assms(3) assoc_mult_mat carrier_matD(2) 
        carrier_mat_triv index_mult_mat(3)) 
  finally show ?thesis unfolding mat_conj_def .
qed

lemma hermitian_square_similar_mat_wit:
  fixes A::"complex Matrix.mat"
  assumes "hermitian A"
  and "A\<in> carrier_mat n n"
and "unitary_diag A B U"
shows "similar_mat_wit (A * A) (B * B) U (Complex_Matrix.adjoint U)" 
proof -
  have "B\<in> carrier_mat n n" using unitary_diag_carrier[of A] assms by metis
  hence "B * B\<in> carrier_mat n n" by simp
  have "unitary U" using assms unitary_diagD[of A] by simp
  have "A *  A= mat_conj U (B*B)" using assms unitary_mult_square_eq[of A n]
    by (metis \<open>B \<in> carrier_mat n n\<close> \<open>Complex_Matrix.unitary U\<close> mat_conj_def 
        unitarily_equiv_carrier(2) unitarily_equiv_eq unitary_diag_def 
        unitary_simps(1))
  moreover have "{A * A, B * B, U, Complex_Matrix.adjoint U} \<subseteq> carrier_mat n n"
    by (metis \<open>B * B \<in> carrier_mat n n\<close> adjoint_dim' assms(2) assms(3) empty_subsetI 
        insert_subsetI mult_carrier_mat unitary_diag_carrier(2))
  moreover have "U * Complex_Matrix.adjoint U = 1\<^sub>m n \<and> Complex_Matrix.adjoint U * U = 1\<^sub>m n"
    by (meson \<open>Complex_Matrix.unitary U\<close> calculation(2) insert_subset unitary_simps(1) 
        unitary_simps(2))
  ultimately show ?thesis unfolding similar_mat_wit_def mat_conj_def by auto
qed

lemma unitarily_equiv_square:
  assumes "A\<in> carrier_mat n n" 
  and "unitarily_equiv A B U"
  shows "unitarily_equiv (A*A) (B*B) U"
proof (rule unitarily_equivI)
  show "unitary U" using assms unitarily_equivD(1)[of A] by simp
  show "similar_mat_wit (A * A) (B * B) U (Complex_Matrix.adjoint U)"
    by (smt (z3) \<open>Complex_Matrix.unitary U\<close> assms carrier_matD(1) 
        carrier_matD(2) carrier_mat_triv index_mult_mat(2) 
        index_mult_mat(3) similar_mat_witI unitarily_equiv_carrier(1) 
        unitarily_equiv_carrier(2) unitarily_equiv_eq unitary_mult_square_eq 
        unitary_simps(1) unitary_simps(2) mat_conj_def)
qed

lemma conjugate_eq_unitarily_equiv:
  assumes "A\<in> carrier_mat n n"
  and "V\<in> carrier_mat n n"
  and "unitarily_equiv A B U"
  and "unitary V"
  and "V * B * (Complex_Matrix.adjoint V) = B"
shows "unitarily_equiv A B (U*V)" 
  unfolding unitarily_equiv_def similar_mat_wit_def Let_def
proof (intro conjI)
  have "B\<in> carrier_mat n n"
    using assms(1) assms(3) unitarily_equiv_carrier(1) by blast
  have "U\<in> carrier_mat n n"
    using assms(1) assms(3) unitarily_equiv_carrier(2) by auto
  show u: "unitary (U*V)"
    by (metis Complex_Matrix.unitary_def adjoint_dim_col assms(1) assms(2) 
        assms(3) assms(4) carrier_matD(2) index_mult_mat(3) unitarily_equivD(1)
        unitarily_equiv_eq unitary_times_unitary)
  thus l: "U * V * Complex_Matrix.adjoint (U * V) = 1\<^sub>m (dim_row A)"
    by (metis Complex_Matrix.unitary_def assms(1) assms(2) carrier_matD(1) 
        carrier_matD(2) index_mult_mat(3) inverts_mat_def)
  thus r: "Complex_Matrix.adjoint (U * V) * (U * V) = 1\<^sub>m (dim_row A)" using u
    by (metis Complex_Matrix.unitary_def index_mult_mat(2) index_one_mat(2) 
        unitary_simps(1))
  show "{A, B, U * V, Complex_Matrix.adjoint (U * V)} \<subseteq> 
    carrier_mat (dim_row A) (dim_row A)"
    using \<open>B \<in> carrier_mat n n\<close> \<open>U \<in> carrier_mat n n\<close> adjoint_dim' assms 
    by auto
  have "U * V * B * Complex_Matrix.adjoint (U * V) = 
    U * V * B * (Complex_Matrix.adjoint V * Complex_Matrix.adjoint U)"
    by (metis \<open>U \<in> carrier_mat n n\<close> adjoint_mult assms(2))
  also have "... = U * V * B * Complex_Matrix.adjoint V * 
    Complex_Matrix.adjoint U"
  proof (rule assoc_mult_mat[symmetric], auto simp add: assms)
    show "Complex_Matrix.adjoint V \<in> carrier_mat (dim_col B) (dim_col U)"
      using \<open>B \<in> carrier_mat n n\<close> \<open>U \<in> carrier_mat n n\<close> adjoint_dim assms(2) 
      by auto
  qed
  also have "... = U * V * B * (Complex_Matrix.adjoint V * 
    Complex_Matrix.adjoint U)" 
  proof (rule assoc_mult_mat, auto simp add: assms)
    show "Complex_Matrix.adjoint V \<in> carrier_mat (dim_col B) (dim_col U)"
      by (metis \<open>B \<in> carrier_mat n n\<close> \<open>U \<in> carrier_mat n n\<close> adjoint_dim' 
          assms(2) carrier_matD(2))
  qed
  also have "... = U * V * (B * (Complex_Matrix.adjoint V * 
    Complex_Matrix.adjoint U))"
  proof (rule assoc_mult_mat, auto simp add: assms)
    show "B \<in> carrier_mat (dim_col V) (dim_col V)"
      by (metis \<open>B \<in> carrier_mat n n\<close> assms(2) carrier_matD(2))
  qed
  also have "... = U * (V * (B * (Complex_Matrix.adjoint V * 
    Complex_Matrix.adjoint U)))"
  proof (rule assoc_mult_mat, auto simp add: assms)
    show "V \<in> carrier_mat (dim_col U) (dim_row B)"
      using \<open>B \<in> carrier_mat n n\<close> \<open>U \<in> carrier_mat n n\<close> assms(2) by auto
  qed
  finally have eq: "U * V * B * Complex_Matrix.adjoint (U * V) = 
    U * (V * (B * (Complex_Matrix.adjoint V * Complex_Matrix.adjoint U)))" .
  have "V * (B * (Complex_Matrix.adjoint V * Complex_Matrix.adjoint U)) =
    V * B * (Complex_Matrix.adjoint V * Complex_Matrix.adjoint U)"
  proof (rule assoc_mult_mat[symmetric], auto simp add: assms)
    show "B \<in> carrier_mat (dim_col V) (dim_col V)"
      using \<open>B \<in> carrier_mat n n\<close> assms(2) by auto
  qed
  also have "... = V * B * Complex_Matrix.adjoint V * Complex_Matrix.adjoint U"
  proof (rule assoc_mult_mat[symmetric], auto simp add: assms)
    show "Complex_Matrix.adjoint V \<in> carrier_mat (dim_col B) (dim_col U)"
      by (metis \<open>B \<in> carrier_mat n n\<close> \<open>U \<in> carrier_mat n n\<close> 
          adjoint_dim_row assms(2) assms(5) carrier_matD(2) carrier_mat_triv 
          index_mult_mat(3))
  qed
  also have "... = B * Complex_Matrix.adjoint U" using assms by simp
  finally have "V *(B *(Complex_Matrix.adjoint V * Complex_Matrix.adjoint U)) =
    B* Complex_Matrix.adjoint U" .
  hence "U * V * B * Complex_Matrix.adjoint (U * V) = U * B * 
    Complex_Matrix.adjoint U"  using eq
    by (metis \<open>B \<in> carrier_mat n n\<close> \<open>U \<in> carrier_mat n n\<close> adjoint_dim' assoc_mult_mat)
  also have "... = A" using assms unitarily_equiv_eq[of A B U] by simp
  finally show "A = U * V * B * Complex_Matrix.adjoint (U * V)" by simp
qed

definition real_diag_decomp where
"real_diag_decomp A B U \<equiv> unitary_diag A B U  \<and> 
  (\<forall>i < dim_row B. B$$(i, i) \<in> Reals)"

lemma real_diag_decompD[simp]:
  assumes "real_diag_decomp A B U"
  shows "unitary_diag A B U" 
    "(\<forall>i < dim_row B. B$$(i, i) \<in> Reals)" using assms 
  unfolding real_diag_decomp_def unitary_diag_def by auto


lemma hermitian_decomp_decomp':
  fixes A::"complex Matrix.mat"
  assumes "hermitian_decomp A B U"
  shows "real_diag_decomp A B U" 
  using assms unfolding hermitian_decomp_def
  by (metis real_diag_decomp_def unitarily_equiv_def unitary_diag_def) 

lemma real_diag_decomp_hermitian:
  fixes A::"complex Matrix.mat"
  assumes "real_diag_decomp A B U"
  shows "hermitian A" 
proof -
  have ud: "unitary_diag A B U" using assms real_diag_decompD by simp
  hence "A = U * B * (Complex_Matrix.adjoint U)"
    by (simp add: unitarily_equiv_eq)
  have "Complex_Matrix.adjoint A = 
    Complex_Matrix.adjoint (U * B * (Complex_Matrix.adjoint U))"
    using ud assms unitarily_equiv_eq unitary_diag_imp_unitarily_equiv by blast 
  also have "... = Complex_Matrix.adjoint (Complex_Matrix.adjoint U) * 
    Complex_Matrix.adjoint B * Complex_Matrix.adjoint U"
    by (smt (z3) ud Complex_Matrix.adjoint_adjoint Complex_Matrix.unitary_def 
        adjoint_dim_col adjoint_mult assms assoc_mult_mat calculation 
        carrier_matD(2) carrier_mat_triv index_mult_mat(2) index_mult_mat(3) 
        similar_mat_witD2(5) similar_mat_wit_dim_row unitary_diagD(1) 
        unitary_diagD(3))
  also have "... = U * Complex_Matrix.adjoint B * Complex_Matrix.adjoint U"
    by (simp add: Complex_Matrix.adjoint_adjoint)
  also have "... = U * B * Complex_Matrix.adjoint U" 
    using real_diagonal_hermitian
    by (metis assms hermitian_def real_diag_decomp_def similar_mat_witD(5) 
        unitary_diagD(1) unitary_diagD(2))
  also have "... = A" using \<open>A = U * B * (Complex_Matrix.adjoint U)\<close> by simp
  finally show ?thesis unfolding hermitian_def by simp
qed

lemma unitary_conjugate_real_diag_decomp:
  assumes "A\<in> carrier_mat n n"
  and "Us\<in> carrier_mat n n"
  and "unitary Us"
  and "real_diag_decomp (mat_conj (Complex_Matrix.adjoint Us) A) B U"
  shows "real_diag_decomp A B (Us * U)" unfolding real_diag_decomp_def
proof (intro conjI allI impI)
  show "\<And>i. i < dim_row B \<Longrightarrow> B $$ (i, i) \<in> \<real>" using assms 
    unfolding real_diag_decomp_def by simp
  show "unitary_diag A B (Us * U)" unfolding unitary_diag_def
  proof (rule conjI)
    show "diagonal_mat B" using assms real_diag_decompD(1) unitary_diagD(2) 
      by metis
    show "unitarily_equiv A B (Us * U)" 
    proof (rule unitarily_equiv_conjugate)
      show "A\<in> carrier_mat n n" using assms by simp
      show "unitary Us" using assms by simp
      show "Us \<in> carrier_mat n n" using assms by simp
      show "unitarily_equiv (mat_conj (Complex_Matrix.adjoint Us) A) B U"
        using assms real_diag_decompD(1) unfolding unitary_diag_def by metis
      thus "U \<in> carrier_mat n n"
        by (metis (mono_tags) adjoint_dim' assms(2) carrier_matD(1) 
            index_mult_mat(2) mat_conj_def unitarily_equiv_carrier'(3))
      show "B\<in> carrier_mat n n"
        using \<open>unitarily_equiv (mat_conj (Complex_Matrix.adjoint Us) A) B U\<close> 
          assms(2) unitarily_equiv_carrier'(2)
        by (metis \<open>U \<in> carrier_mat n n\<close> carrier_matD(2) 
            unitarily_equiv_carrier'(3))
    qed
  qed
qed

subsection \<open>On the spectrum of a matrix\<close>

lemma similar_spectrum_eq:
  fixes A::"complex Matrix.mat"
  assumes "A\<in> carrier_mat n n"
  and "similar_mat A B"
  and "upper_triangular B"
  shows "spectrum A = set (diag_mat B)" 
proof -
  have "(\<Prod>a\<leftarrow>(eigvals A). [:- a, 1:]) = char_poly A" 
    using eigvals_poly_length assms by simp
  also have "... = char_poly B"
  proof (rule char_poly_similar)
    show "similar_mat A B" using assms real_diag_decompD(1)
      using similar_mat_def by blast
  qed
  also have "... = (\<Prod>a\<leftarrow>diag_mat B. [:- a, 1:])" 
  proof (rule char_poly_upper_triangular)
    show "B\<in> carrier_mat n n" using assms similar_matD by auto
    thus "upper_triangular B" using assms by simp
  qed
  finally have "(\<Prod>a\<leftarrow>(eigvals A). [:- a, 1:]) = (\<Prod>a\<leftarrow>diag_mat B. [:- a, 1:])" .
  thus ?thesis using poly_root_set_eq unfolding spectrum_def by metis
qed

lemma unitary_diag_spectrum_eq:
  fixes A::"complex Matrix.mat"
  assumes "A\<in> carrier_mat n n"
  and "unitary_diag A B U"
shows "spectrum A = set (diag_mat B)" 
proof (rule similar_spectrum_eq)
  show "A \<in> carrier_mat n n" using assms by simp
  show "similar_mat A B" using assms unitary_diagD(1) 
    by (metis similar_mat_def)
  show "upper_triangular B" using assms
    unitary_diagD(2) unitary_diagD(1)  diagonal_imp_upper_triangular
    by (metis similar_mat_witD2(5))
qed

lemma unitary_diag_spectrum_eq':
  fixes A::"complex Matrix.mat"
  assumes "A\<in> carrier_mat n n"
  and "unitary_diag A B U"
shows "spectrum A = diag_elems B" 
proof -
  have "spectrum A = set (diag_mat B)" using assms unitary_diag_spectrum_eq 
    by simp
  also have "... = diag_elems B" using diag_elems_set_diag_mat[of B] by simp
  finally show "spectrum A = diag_elems B" .
qed

lemma hermitian_real_diag_decomp:
  fixes A::"complex Matrix.mat"
  assumes "A\<in> carrier_mat n n" 
  and "0 < n"
  and "hermitian A"
obtains B U where "real_diag_decomp A B U" 
proof -
  {
    have es: "char_poly A = (\<Prod> (e :: complex) \<leftarrow> (eigvals A). [:- e, 1:])" 
      using assms  eigvals_poly_length by auto
    obtain B U Q where us: "unitary_schur_decomposition A (eigvals A) = (B,U,Q)" 
      by (cases "unitary_schur_decomposition A (eigvals A)")
    hence pr: "similar_mat_wit A B U (Complex_Matrix.adjoint U) \<and> diagonal_mat B \<and> 
      diag_mat B = (eigvals A) \<and> unitary U \<and> (\<forall>i < n. B$$(i, i) \<in> Reals)" 
      using hermitian_eigenvalue_real assms  es by auto
    moreover have "dim_row B = n" using assms similar_mat_wit_dim_row[of A]  
        pr by auto
    ultimately have "real_diag_decomp A B U" using unitary_diagI[of A] 
      unfolding real_diag_decomp_def by simp
    hence "\<exists> B U. real_diag_decomp A B U" by auto
  }
  thus ?thesis using that by auto 
qed
  
lemma  spectrum_smult:
  fixes A::"complex Matrix.mat"
  assumes "hermitian A"
  and "A\<in> carrier_mat n n"
  and "0 < n"
shows "spectrum (x \<cdot>\<^sub>m A) = {x * a|a. a\<in> spectrum A}"
proof -  
  obtain B U where bu: "real_diag_decomp A B U" 
    using assms hermitian_real_diag_decomp[of A] by auto
  hence "spectrum (x \<cdot>\<^sub>m A) = set (diag_mat (x \<cdot>\<^sub>m B))" 
    using assms unitary_diag_spectrum_eq[of "x \<cdot>\<^sub>m A"] 
      unitarily_equiv_smult[of A]
    by (meson  diagonal_mat_smult real_diag_decompD(1) real_diag_decompD(2) 
        smult_carrier_mat unitary_diag_def)
  also have "... = {x * a |a. a \<in> set (diag_mat B)}" 
    using assms set_diag_mat_smult[of B n x ]
    by (meson bu real_diag_decompD(1) unitary_diag_carrier(1))
  also have "... = {x * a|a. a\<in> spectrum A}" 
    using assms unitary_diag_spectrum_eq[of A] bu real_diag_decompD(1)
    by metis
  finally show ?thesis .
qed

lemma  spectrum_uminus:
  fixes A::"complex Matrix.mat"
  assumes "hermitian A"
  and "A\<in> carrier_mat n n"
  and "0 < n"
shows "spectrum (-A) = {-a|a. a\<in> spectrum A}"
proof -  
  obtain B U where bu: "real_diag_decomp A B U" 
    using assms hermitian_real_diag_decomp[of A] by auto
  hence "spectrum (-A) = set (diag_mat (-B))" 
    using assms unitary_diag_spectrum_eq[of "-A"] 
      unitarily_equiv_uminus[of A]
    by (meson diagonal_mat_uminus real_diag_decompD uminus_carrier_iff_mat 
        unitary_diag_def)
  also have "... = {-a |a. a \<in> set (diag_mat B)}" 
    using assms set_diag_mat_uminus[of B n]
    by (meson bu real_diag_decompD(1) unitary_diag_carrier(1))
  also have "... = {-a|a. a\<in> spectrum A}" 
    using assms unitary_diag_spectrum_eq[of A] bu real_diag_decompD(1)
    by metis
  finally show ?thesis .
qed

section \<open>Properties of the inner product\<close>

subsection \<open>Some analysis complements\<close>

lemma add_conj_le:
  shows "z + cnj z \<le> 2 * cmod z"
proof -
  have z: "z + cnj z = 2 * Re z" by (simp add: complex_add_cnj)
  have "Re z \<le> cmod z" by (simp add: complex_Re_le_cmod)
  hence "2 *complex_of_real (Re z) \<le> 2 * complex_of_real (cmod z)"
    using less_eq_complex_def by auto
  thus ?thesis using z by simp
qed

lemma abs_real:
  fixes x::complex
  assumes "x\<in> Reals"
  shows "abs x \<in> Reals" unfolding abs_complex_def by auto

lemma csqrt_cmod_square:
  shows "csqrt ((cmod z)\<^sup>2) = cmod z"
proof -
  have "csqrt ((cmod z)\<^sup>2) = sqrt (Re ((cmod z)\<^sup>2))" by force
  also have "... = cmod z" by simp
  finally show ?thesis .
qed

lemma cpx_real_le:
  fixes z::complex
  assumes "0 \<le> z"
  and "0 \<le> u"
  and "z\<^sup>2 \<le> u\<^sup>2"
shows "z \<le> u"
proof -
  have "z^2 = Re (z^2)" "u^2 = Re (u^2)" using assms
    by (metis Im_complex_of_real Im_power_real Re_complex_of_real 
        complex_eq_iff less_eq_complex_def zero_complex.sel(2))+
  hence rl: "Re (z^2) \<le> Re (u^2)" using assms less_eq_complex_def by simp
  have "sqrt (Re (z^2)) = z" "sqrt (Re (u^2)) = u"   using assms complex_eqI 
      less_eq_complex_def by auto
  have "z = sqrt (Re (z^2))" using assms complex_eqI less_eq_complex_def 
    by auto
  also have "... \<le> sqrt (Re (u^2))" using rl less_eq_complex_def by simp
  finally show "z \<le> u" using assms complex_eqI less_eq_complex_def by auto
qed

lemma mult_conj_real:
  fixes v::complex
  shows "v * (conjugate v) \<in> Reals"
proof -
  have "0 \<le> v * (conjugate v)" using less_eq_complex_def by simp
  thus ?thesis by (simp add: complex_is_Real_iff) 
qed

lemma real_sum_real:
  assumes "\<And>i. i < n \<Longrightarrow> ((f i)::complex) \<in> Reals"
  shows "(\<Sum> i \<in> {0 ..< n}. f i) \<in> Reals"
  using assms atLeastLessThan_iff by blast

lemma real_mult_re:
  assumes "a\<in> Reals" and "b\<in> Reals"
  shows "Re (a * b) = Re a * Re b" using assms
  by (metis Re_complex_of_real Reals_cases of_real_mult)


lemma complex_positive_Im:
  fixes b::complex
  assumes "0 \<le> b"
  shows "Im b = 0"
  by (metis assms less_eq_complex_def zero_complex.simps(2)) 

lemma cmod_pos:
  fixes z::complex
  assumes "0 \<le> z"
  shows "cmod z = z"
proof -
  have "Im z = 0" using assms complex_positive_Im by simp
  thus ?thesis using complex_norm
    by (metis assms complex.exhaust_sel complex_of_real_def less_eq_complex_def norm_of_real 
        real_sqrt_abs real_sqrt_pow2 real_sqrt_power zero_complex.simps(1))
qed

lemma cpx_pos_square_pos:
  fixes z::complex
  assumes "0 \<le> z"
  shows "0 \<le> z\<^sup>2"
proof -
  have "Im z = 0" using assms by (simp add: complex_positive_Im)
  hence "Re (z\<^sup>2) = (Re z)\<^sup>2" by simp
  moreover have "Im (z\<^sup>2) = 0" by (simp add: \<open>Im z = 0\<close>)
  ultimately show ?thesis by (simp add: less_eq_complex_def) 
qed

lemma cmod_mult_pos:
  fixes b:: complex
  fixes z::complex
  assumes "0 \<le> b"
  shows "cmod (b * z) =  Re b * cmod z" using complex_positive_Im
    Im_complex_of_real Re_complex_of_real abs_of_nonneg  assms cmod_Im_le_iff 
    less_eq_complex_def  norm_mult of_real_0
    by (metis (full_types) cmod_eq_Re)
  


lemma cmod_conjugate_square_eq:
  fixes z::complex
  shows "cmod (z *  (conjugate z)) = z * (conjugate z)"
proof -
  have "0 \<le> z * (conjugate z)" 
    using conjugate_square_positive less_eq_complex_def by auto
  thus ?thesis using cmod_pos by simp
qed


lemma pos_sum_gt_comp:
  assumes "finite I"
and "\<And>i. i \<in> I \<Longrightarrow> (0::real) \<le> f i"
and "j\<in> I"
and "c < f j"
shows "c < sum f I"
proof -
  have "c < f j" using assms by simp
  also have "... \<le> f j + sum f (I -{j})"
    by (smt (z3) DiffD1 assms(2) sum_nonneg)
  also have "... = sum f I" using assms
    by (simp add: sum_diff1)
  finally show ?thesis .
qed

lemma pos_sum_le_comp:
  assumes "finite I"
and "\<And>i. i \<in> I \<Longrightarrow> (0::real) \<le> f i"
and "sum f I \<le> c"
shows "\<forall>i \<in> I. f i \<le> c"
proof (rule ccontr)
  assume "\<not> (\<forall>i\<in>I. f i \<le> c)"
  hence "\<exists>j\<in> I. c < f j" by fastforce
  from this obtain j where "j\<in> I" and "c < f j" by auto
  hence "c < sum f I" using assms pos_sum_gt_comp[of I] by simp
  thus False using assms by simp
qed


lemma square_pos_mult_le:
  assumes "finite I"
  and "\<And>i. i \<in> I \<Longrightarrow> ((0::real) \<le> f i \<and> f i \<le> 1)"
shows "sum (\<lambda>x. f x * f x) I \<le> sum f I" using assms
proof (induct rule:finite_induct)
case empty
  then show ?case by simp
next
  case (insert x F)
  have "sum (\<lambda>x. f x * f x) (insert x F) = f x * f x + sum (\<lambda>x. f x * f x) F"
    by (simp add: insert) 
  also have "... \<le> f x * f x + sum f F" using insert by simp
  also have "... \<le> f x + sum f F" using insert mult_left_le[of "f x" "f x"]  
    by simp
  also have "... = sum f (insert x F)" using insert by simp
  finally show ?case .
qed



lemma square_pos_mult_lt:
  assumes "finite I"
  and "\<And>i. i \<in> I \<Longrightarrow> ((0::real) \<le> f i \<and> f i \<le> 1)"
  and "j \<in> I"
  and "f j < 1"
  and "0 < f j"
shows "sum (\<lambda>x. f x * f x) I < sum f I" using assms
proof -
  have "sum (\<lambda>x. f x * f x) I = 
    sum (\<lambda>x. f x * f x) {j} + sum (\<lambda>x. f x * f x) (I-{j})"
    using assms sum.remove by fastforce
  also have "... = f j * f j + sum (\<lambda>x. f x * f x) (I-{j})" by simp
  also have "... < f j + sum (\<lambda>x. f x * f x) (I-{j})" using assms by simp
  also have "... \<le> f j + sum f (I - {j})" 
    using assms square_pos_mult_le[of "I - {j}"] by simp
  also have "... = sum f I"
    by (metis assms(1) assms(3) sum.remove)
  finally show ?thesis .
qed

subsection \<open>Inner product results\<close>

text \<open>In particular we prove the triangle inequality, i.e. that for vectors $u$ and $v$
we have $\| u+ v \| \leq \| u \| + \| v \|$.\<close>

lemma inner_prod_vec_norm_pow2:
  shows "(vec_norm v)\<^sup>2 = v \<bullet>c v" using vec_norm_def
  by (metis power2_csqrt)

lemma inner_prod_mult_mat_vec_left:
  assumes "v \<in> carrier_vec n"
  and "w \<in> carrier_vec n'"
  and "A \<in> carrier_mat m n"
  and "B \<in> carrier_mat m n'"
shows "inner_prod (A *\<^sub>v v) (B *\<^sub>v w) = 
  inner_prod (((Complex_Matrix.adjoint B) * A) *\<^sub>v v) w" 
proof -
  have "inner_prod (A *\<^sub>v v) (B *\<^sub>v w) = 
    inner_prod (Complex_Matrix.adjoint B *\<^sub>v (A *\<^sub>v v)) w"
    using adjoint_def_alter by (metis assms mult_mat_vec_carrier)
  also have "... = inner_prod (((Complex_Matrix.adjoint B) * A) *\<^sub>v v) w"
  proof -
    have "Complex_Matrix.adjoint B *\<^sub>v (A *\<^sub>v v) = 
      ((Complex_Matrix.adjoint B) * A) *\<^sub>v v"
    proof (rule assoc_mult_mat_vec[symmetric], (auto simp add: assms))
      show "v \<in> carrier_vec n" using assms by simp
      show "A \<in> carrier_mat (dim_row B) n" using assms by auto
    qed
    thus ?thesis by simp
  qed
  finally show ?thesis .
qed

lemma rank_1_proj_trace_inner:
  fixes A :: "'a::conjugatable_field Matrix.mat" and v :: "'a Matrix.vec"
  assumes A: "A \<in> carrier_mat n n"
    and v: "v \<in> carrier_vec n"
  shows "Complex_Matrix.trace (A * (rank_1_proj v)) = Complex_Matrix.inner_prod v (A *\<^sub>v v)"
  using assms trace_outer_prod_right[of A] unfolding rank_1_proj_def by simp

lemma unitary_inner_prod:
  assumes "v\<in> carrier_vec n"
  and "w \<in> carrier_vec n"
  and "U \<in> carrier_mat n n"
  and "Complex_Matrix.unitary U"
shows "inner_prod (U *\<^sub>v v) (U *\<^sub>v w) = inner_prod v w"
proof -
  have "inner_prod (U *\<^sub>v v) (U *\<^sub>v w) = 
    inner_prod (((Complex_Matrix.adjoint U) * U) *\<^sub>v v) w"
    using assms by (simp add: inner_prod_mult_mat_vec_left)
  also have "... = inner_prod (1\<^sub>m n *\<^sub>v v) w" using assms by simp
  also have "... = inner_prod v w" using assms by simp
  finally show ?thesis .
qed

lemma unitary_vec_norm:
  assumes "v\<in> carrier_vec n"
  and "U \<in> carrier_mat n n"
  and "Complex_Matrix.unitary U"
shows "vec_norm (U *\<^sub>v v) = vec_norm v" using unitary_inner_prod assms unfolding vec_norm_def
  by metis

lemma unitary_col_norm_square:
  assumes "unitary U"
and "U\<in> carrier_mat n n"
  and "i < n"
shows "\<parallel>Matrix.col U i\<parallel>\<^sup>2 = 1"
proof -
  define vn::"complex Matrix.vec" where "vn = unit_vec n i"
  have "\<parallel>Matrix.col U i\<parallel>\<^sup>2 = (vec_norm (Matrix.col U i))\<^sup>2" using vec_norm_sq_cpx_vec_length_sq by simp
  also have "... = (vec_norm vn)\<^sup>2" using assms unitary_vec_norm
    by (metis mat_unit_vec_col unit_vec_carrier vn_def)
  also have "... = \<parallel>vn\<parallel>\<^sup>2" using vec_norm_sq_cpx_vec_length_sq by simp
  also have "... = 1" using assms unfolding vn_def by simp
  finally show ?thesis by blast
qed 

lemma unitary_col_norm:
  assumes "unitary U"
and "U\<in> carrier_mat n n"
  and "i < n"
shows "\<parallel>Matrix.col U i\<parallel> = 1" using assms unitary_col_norm_square cpx_vec_length_inner_prod 
    inner_prod_csqrt by (metis csqrt_1 of_real_eq_1_iff)

lemma inner_mult_diag_expand:
  fixes B::"complex Matrix.mat"
  assumes "diagonal_mat B"
  and "B \<in> carrier_mat n n"
  and "v \<in> carrier_vec n"
shows "inner_prod (B *\<^sub>v v) v = 
  (\<Sum> i \<in> {0 ..< n}. (conjugate (B $$ (i,i))) * (vec_index v i *  
      (conjugate (vec_index v i))))"
proof -
  have  idx: "\<And>i. i < n \<Longrightarrow> vec_index (B *\<^sub>v v) i = B $$ (i,i) * (vec_index v i)"
    using assms diagonal_mat_mult_vec by blast
  have "inner_prod (B *\<^sub>v v) v = 
    (\<Sum> i \<in> {0 ..< n}. vec_index v i * vec_index (conjugate (B *\<^sub>v v)) i)" 
    unfolding Matrix.scalar_prod_def using assms by fastforce  
  also have "... = (\<Sum> i \<in> {0 ..< n}. vec_index v i * conjugate (vec_index (B *\<^sub>v v) i))" 
    using assms by force
  also have "... = (\<Sum> i \<in> {0 ..< n}. (conjugate (B $$ (i,i))) * (vec_index v i *  
      (conjugate (vec_index v i))))" 
  proof (rule sum.cong, simp)
    show "\<And>i. i \<in> {0 ..< n} \<Longrightarrow> vec_index v i * conjugate (vec_index (B *\<^sub>v v) i) = 
      (conjugate (B $$ (i,i))) * (vec_index v i * (conjugate (vec_index v i)))" 
      by (simp add:  idx)
  qed
  finally show ?thesis .
qed

lemma inner_mult_diag_expand':
  fixes B::"complex Matrix.mat"
  assumes "diagonal_mat B"
  and "B \<in> carrier_mat n n"
  and "v \<in> carrier_vec n"
shows "inner_prod v (B *\<^sub>v v) = 
  (\<Sum> i \<in> {0 ..< n}. B $$ (i,i) * (vec_index v i *  
      (conjugate (vec_index v i))))"
proof -
  have  idx: "\<And>i. i < n \<Longrightarrow> vec_index (B *\<^sub>v v) i = B $$ (i,i) * (vec_index v i)"
    using assms diagonal_mat_mult_vec by blast
  have "inner_prod v (B *\<^sub>v v)  = 
    (\<Sum> i \<in> {0 ..< n}. vec_index (B *\<^sub>v v) i * vec_index (conjugate v) i)" 
    unfolding Matrix.scalar_prod_def using assms by fastforce  
  also have "... = 
    (\<Sum> i \<in> {0 ..< n}. vec_index (B *\<^sub>v v) i * conjugate (vec_index v i))" 
    using assms by force
  also have "... = (\<Sum> i \<in> {0 ..< n}. (B $$ (i,i)) * (vec_index v i *  
      (conjugate (vec_index v i))))" 
  proof (rule sum.cong, simp)
    show "\<And>i. i \<in> {0 ..< n} \<Longrightarrow> 
      vec_index (B *\<^sub>v v) i * conjugate (vec_index v i) = 
      (B $$ (i,i)) * (vec_index v i * (conjugate (vec_index v i)))" 
      by (simp add:  idx)
  qed
  finally show ?thesis .
qed

lemma self_inner_prod_real:
  fixes v::"complex Matrix.vec"
  shows "Complex_Matrix.inner_prod v v \<in> Reals"
proof -
  have "Im (Complex_Matrix.inner_prod v v) = 0" 
    using self_cscalar_prod_geq_0 by simp
  thus ?thesis using complex_is_Real_iff by auto
qed

lemma inner_mult_diag_real:
  fixes B::"complex Matrix.mat"
  assumes "diagonal_mat B"
  and "B \<in> carrier_mat n n"
  and "\<forall>i < n. B$$(i, i) \<in> Reals"
  and "v \<in> carrier_vec n"
shows "inner_prod (B *\<^sub>v v) v \<in> Reals"
proof -
  have  "inner_prod (B *\<^sub>v v) v = 
    (\<Sum> i \<in> {0 ..< n}. (conjugate (B $$ (i,i))) * (vec_index v i *  
    (conjugate (vec_index v i))))" using inner_mult_diag_expand assms 
    by simp
  also have "... \<in> Reals"
  proof (rule real_sum_real)
    show "\<And>i. i < n \<Longrightarrow> 
      conjugate (B $$ (i, i)) * 
      ((vec_index v i) * conjugate (vec_index v i)) \<in> \<real>" 
      using assms mult_conj_real by auto
  qed
  finally show ?thesis .
qed

lemma inner_mult_diag_real':
  fixes B::"complex Matrix.mat"
  assumes "diagonal_mat B"
  and "B \<in> carrier_mat n n"
  and "\<forall>i < n. B$$(i, i) \<in> Reals"
  and "v \<in> carrier_vec n"
shows "inner_prod v (B *\<^sub>v v)  \<in> Reals"
proof -
  have  "inner_prod v (B *\<^sub>v v)  = 
    (\<Sum> i \<in> {0 ..< n}. B $$ (i,i) * (vec_index v i *  
    (conjugate (vec_index v i))))" 
    using inner_mult_diag_expand' assms by simp
  also have "... \<in> Reals"
  proof (rule real_sum_real)
    show "\<And>i. i < n \<Longrightarrow> 
      B $$ (i, i) * ((vec_index v i) * conjugate (vec_index v i)) \<in> \<real>" 
      using assms mult_conj_real by auto
  qed
  finally show ?thesis .
qed

lemma inner_prod_mult_mat_vec_right:
assumes "v \<in> carrier_vec n"
  and "w \<in> carrier_vec n'"
  and "A \<in> carrier_mat m n"
  and "B \<in> carrier_mat m n'"
shows "inner_prod (A *\<^sub>v v) (B *\<^sub>v w) = 
  inner_prod v (((Complex_Matrix.adjoint A) * B) *\<^sub>v w)"
proof -
  have "inner_prod (A *\<^sub>v v) (B *\<^sub>v w) = 
    inner_prod ((Complex_Matrix.adjoint (Complex_Matrix.adjoint A)) *\<^sub>v v) 
      (B *\<^sub>v w)" 
    by (simp add: Complex_Matrix.adjoint_adjoint)
  also have "... = inner_prod v ((Complex_Matrix.adjoint A) *\<^sub>v (B *\<^sub>v w))"
  proof (rule adjoint_def_alter[symmetric])
    show "v \<in> carrier_vec n" using assms by simp
    show "B *\<^sub>v w \<in> carrier_vec m" using assms by simp
    show "Complex_Matrix.adjoint A \<in> carrier_mat n m" 
      using assms adjoint_dim'[of A] by simp
  qed    
  also have "... = inner_prod v (((Complex_Matrix.adjoint A) * B) *\<^sub>v w)" 
    using assms 
  proof -
    have "(Complex_Matrix.adjoint A) *\<^sub>v (B *\<^sub>v w) = 
      ((Complex_Matrix.adjoint A) * B) *\<^sub>v w"
    proof (rule assoc_mult_mat_vec[symmetric], (auto simp add: assms))
      show "w \<in> carrier_vec n'" using assms by simp
      show "B \<in> carrier_mat (dim_row A) n'" using assms by auto
    qed
    thus ?thesis by simp
  qed
  finally show ?thesis .
qed

lemma Cauchy_Schwarz_complex_vec_norm:
assumes "dim_vec x = dim_vec y"
shows "cmod (inner_prod x y) \<le> vec_norm x * vec_norm y"
proof -
  have x: "x \<in> carrier_vec (dim_vec x)" by simp
  moreover have y: "y \<in> carrier_vec (dim_vec x)" using assms by simp
  ultimately have "(cmod (inner_prod x y))\<^sup>2 = inner_prod x y * inner_prod y x" 
    using complex_norm_square by (metis inner_prod_swap mult_conj_cmod_square)
  also have "... \<le> inner_prod x x * inner_prod y y" 
    using Cauchy_Schwarz_complex_vec x y by blast
  finally have "(cmod (inner_prod x y))\<^sup>2 \<le> inner_prod x x * inner_prod y y" .
  hence "(cmod (inner_prod x y))\<^sup>2 \<le> Re (inner_prod x x) * Re (inner_prod y y)"
    using less_eq_complex_def by simp
  hence "sqrt ((cmod (inner_prod x y))\<^sup>2) \<le> 
    sqrt (Re (inner_prod x x) * Re (inner_prod y y))"
    using real_sqrt_le_iff by blast
  also have "... =  sqrt (Re (inner_prod x x)) * sqrt (Re (inner_prod y y))"
    by (simp add: real_sqrt_mult)
  finally have "sqrt ((cmod (inner_prod x y))\<^sup>2) \<le> 
    sqrt (Re (inner_prod x x)) * sqrt (Re (inner_prod y y))" .
  thus ?thesis using less_eq_complex_def by (simp add: vec_norm_def)
qed

lemma vec_norm_triangle_sq:
  fixes u::"complex Matrix.vec"
  assumes "dim_vec u = dim_vec v"
  shows "(vec_norm (u+ v))\<^sup>2 \<le> (vec_norm u + vec_norm v)\<^sup>2"
proof -
  have "(vec_norm (u+v))\<^sup>2 = inner_prod (u+v) (u+v)" 
    by (simp add: inner_prod_vec_norm_pow2) 
  also have "... = inner_prod u u + inner_prod u v + inner_prod v u + 
    inner_prod v v"
    using assms add_scalar_prod_distrib conjugate_add_vec
    by (smt (z3) ab_semigroup_add_class.add_ac(1) carrier_vec_dim_vec 
        dim_vec_conjugate index_add_vec(2) scalar_prod_add_distrib)
  also have "... = (vec_norm u)^2 + inner_prod u v + inner_prod v u + 
    (vec_norm v)^2"
    by (simp add: inner_prod_vec_norm_pow2) 
  also have "... \<le> (vec_norm u)^2 + 2 * cmod (inner_prod u v) + (vec_norm v)^2"
    by (metis add_conj_le add_left_mono add_right_mono assms 
        carrier_vec_dim_vec conjugate_complex_def inner_prod_swap 
        is_num_normalize(1))
  also have "... \<le> (vec_norm u)^2 + 2 * ((vec_norm u)*(vec_norm v)) + 
    (vec_norm v)^2" 
    using Cauchy_Schwarz_complex_vec_norm[of u  v] assms less_eq_complex_def 
    by auto
  also have "... = (vec_norm u + vec_norm v)\<^sup>2" by (simp add: power2_sum)
  finally show ?thesis .
qed

lemma vec_norm_triangle:
fixes u::"complex Matrix.vec"
  assumes "dim_vec u = dim_vec v"
  shows "vec_norm (u+ v) \<le> vec_norm u + vec_norm v"
proof (rule cpx_real_le)
  show "(vec_norm (u + v))\<^sup>2 \<le> (vec_norm u + vec_norm v)\<^sup>2" 
    using assms vec_norm_triangle_sq by simp
  show "0 \<le> vec_norm (u + v)" using vec_norm_geq_0 by simp
  show "0 \<le> vec_norm u + vec_norm v" using vec_norm_geq_0 by simp
qed  


section \<open>Matrix decomposition\<close>

lemma (in cpx_sq_mat) sum_decomp_cols:
  fixes A::"complex Matrix.mat"
  assumes "hermitian A"
  and "A \<in> fc_mats"
  and "unitary_diag A B U" 
shows "sum_mat (\<lambda>i. (diag_mat B ! i) \<cdot>\<^sub>m rank_1_proj (Matrix.col U i))
  {..< dimR} = A"
proof -
  have "similar_mat_wit A B U (Complex_Matrix.adjoint U) \<and> diagonal_mat B \<and> 
    unitary U"
    by (metis assms(3) unitary_diagD(1) unitary_diagD(2) unitary_diagD(3)) 
  hence A: "A = U * B * (Complex_Matrix.adjoint U)" and dB: "diagonal_mat B"
    and dimB: "B \<in> carrier_mat dimR dimR" and dimP: "U \<in> carrier_mat dimR dimR" 
    and unit: "unitary U"
    unfolding similar_mat_wit_def Let_def using assms fc_mats_carrier by auto
  have pz: "\<And>i. i < dimR \<Longrightarrow> (Matrix.col U i) = zero_col U i" 
    unfolding zero_col_def by simp
  have "sum_mat (\<lambda>i. (diag_mat B ! i) \<cdot>\<^sub>m
    rank_1_proj (Matrix.col U i)) {..< dimR} = 
    U * B * Complex_Matrix.adjoint U" 
  proof (rule weighted_sum_rank_1_proj_unitary)
    show "diagonal_mat B" using dB .
    show "Complex_Matrix.unitary U" using unit .
    show "U \<in> fc_mats" using fc_mats_carrier dim_eq dimP by simp
    show "B\<in> fc_mats" using fc_mats_carrier dim_eq dimB by simp
  qed
  thus ?thesis using A by simp
qed

lemma unitary_col_inner_prod:
  assumes "A \<in> carrier_mat n n"
  and "0 < n"
and "Complex_Matrix.unitary A"
and "j < n"
and "k < n"
shows "Complex_Matrix.inner_prod (Matrix.col A j) (Matrix.col A k) = 
  (1\<^sub>m n) $$ (j,k)"
proof -
  have "Complex_Matrix.inner_prod (Matrix.col A j) (Matrix.col A k) = 
    (Complex_Matrix.adjoint A * A) $$ (j, k)" 
    using inner_prod_adjoint_comp[of A n A] assms 
    by simp
  also have "... = (1\<^sub>m n) $$ (j,k)" using assms 
    unfolding Complex_Matrix.unitary_def
    by (simp add: assms(3))
  finally show ?thesis .
qed

lemma (in cpx_sq_mat) sum_mat_ortho_proj:
  assumes "finite I"
  and "j \<in> I"
  and "A j * A j = A j"
  and "\<And>i. i\<in> I \<Longrightarrow> A i \<in> fc_mats"
  and "\<And> i . i\<in> I \<Longrightarrow> i\<noteq> j \<Longrightarrow> A i * (A j) = (0\<^sub>m dimR dimR)"
  shows "(sum_mat A I) * (A j) = (A j)" using assms
proof (induct rule:finite_induct)
  case empty
  then show ?case using dim_eq by auto
next
  case (insert x F)
  have "(sum_mat A (insert x F)) * (A j) = 
    (A x + sum_mat A F) * (A j)" using insert sum_mat_insert[of A]
    by (simp add: image_subset_iff) 
  also have "... = A x * (A j) + sum_mat A F * (A j)"
  proof (rule add_mult_distrib_mat)
    show "A x \<in> carrier_mat dimR dimC" using insert fc_mats_carrier by simp
    show "sum_mat A F \<in> carrier_mat dimR dimC" using insert
      by (metis insert_iff local.fc_mats_carrier sum_mat_carrier) 
    show "A j \<in> carrier_mat dimC dimC" using insert dim_eq fc_mats_carrier by force
  qed
  also have "... = A j"
  proof (cases "x = j")
    case True
    hence "j\<notin> F" using insert by auto
    hence "sum_mat A F * A j = 0\<^sub>m dimR dimR" using insert sum_mat_left_ortho_zero[of F A "A j"]
      using True ball_insert dim_eq by auto
    thus ?thesis using insert True dim_eq fc_mats_carrier by auto
  next
    case False
    hence "j\<in> F" using insert by auto
    moreover have "\<And>i. i \<in> F \<Longrightarrow> A i \<in> fc_mats" using insert by simp
    moreover have "\<And>i. i \<in> F \<Longrightarrow> i \<noteq> j \<Longrightarrow> A i * A j = 0\<^sub>m dimR dimR" using insert by simp
    ultimately have "sum_mat A F * A j = A j" using insert by simp
    thus ?thesis using False dim_eq fc_mats_carrier insert by auto 
  qed
  finally show ?case .
qed

lemma (in cpx_sq_mat) sum_mat_ortho_one:
  assumes "finite I"
  and "j\<in> I"
  and "B \<in> fc_mats"
  and "\<And>i. i\<in> I \<Longrightarrow> A i \<in> fc_mats"
  and "\<And> i . i\<in> I \<Longrightarrow> i\<noteq> j \<Longrightarrow> A i * B = (0\<^sub>m dimR dimR)"
  shows "(sum_mat A I) * B = A j * B" using assms
proof (induct rule:finite_induct)
  case empty
  then show ?case using dim_eq by auto
next
  case (insert x F)
  have "(sum_mat A (insert x F)) * B = 
    (A x + sum_mat A F) * B" using insert sum_mat_insert[of A]
    by (simp add: image_subset_iff) 
  also have "... = A x * B + sum_mat A F * B"
  proof (rule add_mult_distrib_mat)
    show "A x \<in> carrier_mat dimR dimC" using insert fc_mats_carrier by simp
    show "sum_mat A F \<in> carrier_mat dimR dimC" using insert
      by (metis insert_iff local.fc_mats_carrier sum_mat_carrier) 
    show "B \<in> carrier_mat dimC dimC" using insert dim_eq fc_mats_carrier by force
  qed
  also have "... = A j * B"
  proof (cases "x = j")
    case True
    hence "j\<notin> F" using insert by auto
    hence "sum_mat A F * B = 0\<^sub>m dimR dimR" using insert sum_mat_left_ortho_zero[of F A B]
      using True ball_insert dim_eq by auto
    thus ?thesis using insert True dim_eq fc_mats_carrier
      by (metis Complex_Matrix.right_add_zero_mat cpx_sq_mat_mult)
  next
    case False
    hence "j\<in> F" using insert by auto
    moreover have "\<And>i. i \<in> F \<Longrightarrow> A i \<in> fc_mats" using insert by simp
    moreover have "\<And>i. i \<in> F \<Longrightarrow> i \<noteq> j \<Longrightarrow> A i * B = 0\<^sub>m dimR dimR" using insert by simp
    ultimately have "sum_mat A F * B = A j * B" using insert by simp
    thus ?thesis using False dim_eq fc_mats_carrier insert
      by (metis add_zero cpx_sq_mat_mult insertI1) 
  qed
  finally show ?case .
qed

lemma unitarily_equiv_rank_1_proj_col_carrier:
  assumes "A\<in> carrier_mat n n"
and "unitarily_equiv A B U"
and "i < n"
shows  "rank_1_proj (Matrix.col U i) \<in> carrier_mat n n" 
  using rank_1_proj_col_carrier assms
  by (metis carrier_matD(1) carrier_matD(2) unitarily_equiv_carrier(2))

lemma decomp_eigenvector:
  fixes A::"complex Matrix.mat"
  assumes "A \<in> carrier_mat n n"
  and "0 < n"
  and "hermitian A"
  and "unitary_diag A B U" 
and "j < n"
shows "Complex_Matrix.trace (A * (rank_1_proj (Matrix.col U j))) = B $$(j,j)"
proof -
  define fc::"complex Matrix.mat set" where "fc = carrier_mat n n"
  interpret cpx_sq_mat n n fc  
  proof 
    show "0 < n" using assms by simp
  qed (auto simp add: fc_def)
  have rf: "\<And>i. i < n \<Longrightarrow> rank_1_proj (Matrix.col U i) \<in> fc" using 
      assms unitarily_equiv_rank_1_proj_col_carrier
    by (metis fc_def unitary_diag_imp_unitarily_equiv)
  hence sm: "\<And>i. i < n \<Longrightarrow> diag_mat B ! i \<cdot>\<^sub>m rank_1_proj (Matrix.col U i) \<in> fc" 
    using fc_mats_carrier dim_eq by simp
  have "A * (rank_1_proj (Matrix.col U j)) = 
    (sum_mat (\<lambda>i. (diag_mat B ! i) \<cdot>\<^sub>m (rank_1_proj (Matrix.col U i))) {..< n}) * 
      (rank_1_proj (Matrix.col U j))" using assms sum_decomp_cols 
    unfolding fc_def by simp
  also have "... = diag_mat B ! j \<cdot>\<^sub>m rank_1_proj (Matrix.col U j) * 
    rank_1_proj (Matrix.col U j)" 
  proof (rule  sum_mat_ortho_one, (auto simp add: assms))
    show "rank_1_proj (Matrix.col U j) \<in> fc" by (simp add: assms rf)
    show "\<And>i. i < n \<Longrightarrow> diag_mat B ! i \<cdot>\<^sub>m rank_1_proj (Matrix.col U i) \<in> fc"
      by (simp add: sm)
    show "\<And>i. i < n \<Longrightarrow> i \<noteq> j \<Longrightarrow> 
      diag_mat B ! i \<cdot>\<^sub>m rank_1_proj (Matrix.col U i) * 
      rank_1_proj (Matrix.col U j) = 0\<^sub>m n n"
    proof -
      fix i
      assume "i < n" and "i \<noteq> j"
      define OP where "OP = outer_prod (Matrix.col U i) (Matrix.col U j)"      
      have cm: "OP \<in> carrier_mat n n" unfolding OP_def 
      proof (rule outer_prod_dim)
        have "dim_row U = n" 
          using assms unitary_diag_carrier(2) fc_mats_carrier
          by (metis carrier_matD(1))
        thus "Matrix.col U i \<in> carrier_vec n" using\<open>i < n\<close> 
          by (simp add: carrier_vecI)
        show "Matrix.col U j \<in> carrier_vec n" using assms \<open>dim_row U = n\<close> 
          by (simp add: carrier_vecI)
      qed
      have "rank_1_proj (Matrix.col U i) * rank_1_proj (Matrix.col U j) = 
        1\<^sub>m n $$ (i, j) \<cdot>\<^sub>m outer_prod (Matrix.col U i) (Matrix.col U j)" 
      proof (rule rank_1_proj_unitary, (auto simp add: \<open>i < n\<close> assms))
        show "U \<in> fc" using assms unitary_diag_carrier(2)
          fc_mats_carrier by simp
        show "Complex_Matrix.unitary U" using assms unitary_diag_carrier
          unitary_diagD(3) by blast
      qed
      also have "... = 0 \<cdot>\<^sub>m outer_prod (Matrix.col U i) (Matrix.col U j)" 
        using \<open>i \<noteq> j\<close>
        by (metis \<open>i < n\<close> assms(5) index_one_mat(1))
      also have "... = 0\<^sub>m n n" using cm smult_zero unfolding OP_def by auto
      finally show "diag_mat B ! i \<cdot>\<^sub>m rank_1_proj (Matrix.col U i) * 
        rank_1_proj (Matrix.col U j) = 0\<^sub>m n n" 
        by (metis \<open>i < n\<close> \<open>rank_1_proj (Matrix.col U j) \<in> fc\<close>  
            fc_mats_carrier mult_smult_assoc_mat rf smult_zero_mat)
    qed
  qed
  also have "... = diag_mat B ! j \<cdot>\<^sub>m rank_1_proj (Matrix.col U j)"
  proof -
    have "diag_mat B ! j \<cdot>\<^sub>m rank_1_proj (Matrix.col U j) * 
            rank_1_proj (Matrix.col U j) =
         diag_mat B ! j \<cdot>\<^sub>m (rank_1_proj (Matrix.col U j) * 
            rank_1_proj (Matrix.col U j))"
    proof (rule mult_smult_assoc_mat)
      show "rank_1_proj (Matrix.col U j) \<in> carrier_mat n n" using \<open>j < n\<close>  rf 
          fc_mats_carrier by simp
      show "rank_1_proj (Matrix.col U j) \<in> carrier_mat n n" 
        using assms rf fc_mats_carrier by simp
    qed
    moreover have "rank_1_proj (Matrix.col U j) * rank_1_proj (Matrix.col U j)=
      rank_1_proj (Matrix.col U j)"
    proof (rule rank_1_proj_unitary_eq, (auto simp add: assms))
      show "U \<in> fc" using assms unitary_diag_carrier(2)
        using fc_mats_carrier by simp
      show "Complex_Matrix.unitary U" using assms unitary_diagD by blast
    qed
    ultimately show ?thesis by simp
  qed
  finally have "A * (rank_1_proj (Matrix.col U j)) = 
    diag_mat B ! j \<cdot>\<^sub>m rank_1_proj (Matrix.col U j)" .
  hence "Complex_Matrix.trace (A * (rank_1_proj (Matrix.col U j))) = 
    diag_mat B ! j * Complex_Matrix.trace (rank_1_proj (Matrix.col U j))"
    using \<open>j < n\<close> rf fc_mats_carrier trace_smult dim_eq by auto
  also have "... = diag_mat B ! j"
  proof -
    have "Complex_Matrix.trace (rank_1_proj (Matrix.col U j)) = 1"
    proof (rule rank_1_proj_trace)
      show "\<parallel>Matrix.col U j\<parallel> = 1" using unitary_col_norm[of U n j] assms
        unitary_diag_carrier(2) fc_mats_carrier
        by (metis unitary_diagD(3))
    qed
    thus ?thesis by simp
  qed
  also have "... = B $$ (j,j)"
  proof -
    have "dim_row B = n" using unitary_diag_carrier(1) assms fc_mats_carrier
      by (metis carrier_matD(1))
    thus ?thesis  using assms unfolding diag_mat_def by simp
  qed
  finally show ?thesis .
qed

lemma positive_unitary_diag_pos:
  fixes A::"complex Matrix.mat"
  assumes "A \<in> carrier_mat n n"
  and "Complex_Matrix.positive A"
  and "unitary_diag A B U" 
and "j < n" 
shows "0 \<le> B $$ (j, j)"
proof -
  define fc::"complex Matrix.mat set" where "fc = carrier_mat n n"
  interpret cpx_sq_mat n n fc  
  proof 
    show "0 < n" using assms by simp
  qed (auto simp add: fc_def)
  define Uj where "Uj = Matrix.col U j"
  have "dim_row U = n" using assms unitary_diag_carrier(2) by blast
  hence uj: "Matrix.col U j \<in> carrier_vec n" by (simp add: carrier_vecI)
  have "hermitian A" using assms positive_is_hermitian by simp
  have "0 \<le> Complex_Matrix.inner_prod Uj (A *\<^sub>v Uj)" using assms Complex_Matrix.positive_def
     by (metis Uj_def \<open>dim_row U = n\<close> carrier_matD(2) dim_col)
  also have "... = Complex_Matrix.trace (A * (rank_1_proj Uj))" using rank_1_proj_trace_inner uj
    assms unfolding Uj_def by metis
  also have "... = B $$ (j,j)" using decomp_eigenvector assms 
     \<open>hermitian A\<close> unfolding Uj_def fc_def by simp
  finally show ?thesis .
qed

lemma unitary_diag_trace_mult_sum:
  fixes A::"complex Matrix.mat"
  assumes "A \<in> carrier_mat n n"
  and "C \<in> carrier_mat n n"
  and "hermitian A"
  and "unitary_diag A B U" 
  and "0 < n"
shows "Complex_Matrix.trace (C * A) = 
  (\<Sum> i = 0 ..< n. B$$(i,i) * 
    Complex_Matrix.trace (C * rank_1_proj (Matrix.col U i)))"
proof -
  define fc::"complex Matrix.mat set" where "fc = carrier_mat n n"
  interpret cpx_sq_mat n n fc  
  proof 
    show "0 < n" using assms by simp
  qed (auto simp add: fc_def)
  have rf: "\<And>i. i < n \<Longrightarrow> rank_1_proj (Matrix.col U i) \<in> carrier_mat n n"
    using assms unitary_diag_imp_unitarily_equiv 
      unitarily_equiv_rank_1_proj_col_carrier 
    unfolding fc_def by blast
  have "C * A = 
    C * (sum_mat (\<lambda>i. (diag_mat B ! i) \<cdot>\<^sub>m 
      rank_1_proj (Matrix.col U i)) {..< n})"
    using sum_decomp_cols  assms \<open>hermitian A\<close> 
    unfolding fc_def by simp
  also have "... = sum_mat (\<lambda>i. C * ((diag_mat B ! i) \<cdot>\<^sub>m  
      rank_1_proj (Matrix.col U i))) {..< n}"  
    by (rule sum_mat_distrib_left[symmetric], 
        (auto simp add: assms rf smult_mem fc_def)) 
  also have "... = sum_mat (\<lambda>i. (diag_mat B ! i) \<cdot>\<^sub>m  
    (C * rank_1_proj (Matrix.col U i))) {..< n}" 
  proof (rule sum_mat_cong, 
      (auto simp add: rf smult_mem assms unitarily_equiv_rank_1_proj_col_carrier 
        fc_def))
    show "\<And>i. i < n \<Longrightarrow> diag_mat B ! i \<cdot>\<^sub>m (C * rank_1_proj (Matrix.col U i)) \<in> 
      carrier_mat n n"
      using assms unitarily_equiv_rank_1_proj_col_carrier cpx_sq_mat_mult smult_mem
      by (simp add: rf)
    show "\<And>i. i < n \<Longrightarrow> C * (diag_mat B ! i \<cdot>\<^sub>m rank_1_proj (Matrix.col U i)) \<in> 
      carrier_mat n n"
      using assms unitarily_equiv_rank_1_proj_col_carrier cpx_sq_mat_mult 
        smult_mem by (simp add: rf)
    show "\<And>i. i < n \<Longrightarrow> C * (diag_mat B ! i \<cdot>\<^sub>m rank_1_proj (Matrix.col U i)) = 
      diag_mat B ! i \<cdot>\<^sub>m (C * rank_1_proj (Matrix.col U i))"
      by (metis assms(2) fc_mats_carrier mult_smult_distrib rf)
  qed
  finally have ceq: "C * A = sum_mat (\<lambda>i. (diag_mat B ! i) \<cdot>\<^sub>m  
    (C * rank_1_proj (Matrix.col U i))) {..< n}" .
  have "Complex_Matrix.trace (sum_mat (\<lambda>i. (diag_mat B ! i) \<cdot>\<^sub>m  
    (C * rank_1_proj (Matrix.col U i))) {..< n}) = (\<Sum> i = 0 ..< n. 
      Complex_Matrix.trace ((diag_mat B ! i) \<cdot>\<^sub>m 
    (C * rank_1_proj (Matrix.col U i))))" 
    by (smt (z3) assms(2) atLeast0LessThan cpx_sq_mat_mult cpx_sq_mat_smult finite_lessThan 
        lessThan_iff rf sum.cong trace_sum_mat fc_def)
  also have "... = (\<Sum> i = 0 ..< n. (diag_mat B ! i) *
      Complex_Matrix.trace  (C * rank_1_proj (Matrix.col U i)))"
  proof (rule sum.cong, simp)
    show "\<And>x. x \<in> {0..<n} \<Longrightarrow>
         Complex_Matrix.trace (diag_mat B ! x \<cdot>\<^sub>m (C * rank_1_proj (Matrix.col U x))) =
         diag_mat B ! x * Complex_Matrix.trace (C * rank_1_proj (Matrix.col U x))" using trace_smult
      by (metis assms(2) atLeastLessThan_iff cpx_sq_mat_mult fc_mats_carrier rf)
  qed
  also have "... = (\<Sum> i = 0 ..< n. B $$ (i,i) *
      Complex_Matrix.trace  (C * rank_1_proj (Matrix.col U i)))"
  proof (rule sum.cong, simp)
    have "B \<in> carrier_mat n n" using unitary_diag_carrier(1) assms 
        fc_mats_carrier dim_eq by simp
    hence "\<And>x. x \<in> {0..<n} \<Longrightarrow> diag_mat B!x = B$$(x,x)" unfolding diag_mat_def by simp
    thus "\<And>x. x \<in> {0..<n} \<Longrightarrow>
         diag_mat B ! x * Complex_Matrix.trace (C * rank_1_proj (Matrix.col U x)) =
         B $$ (x, x) * Complex_Matrix.trace (C * rank_1_proj (Matrix.col U x))" by simp
  qed
  finally have "Complex_Matrix.trace 
    (sum_mat (\<lambda>i. (diag_mat B ! i) \<cdot>\<^sub>m  (C * rank_1_proj (Matrix.col U i))) {..< n}) = 
    (\<Sum> i = 0 ..< n. B $$ (i,i) * Complex_Matrix.trace  (C * rank_1_proj (Matrix.col U i)))" .
  thus ?thesis using ceq by simp
qed

lemma  unitarily_equiv_trace:
  assumes "A \<in> carrier_mat n n"
  and "unitarily_equiv A B U"
shows "Complex_Matrix.trace A = Complex_Matrix.trace B"
proof -
  have "Complex_Matrix.trace A = Complex_Matrix.trace (U * B * (Complex_Matrix.adjoint U))"
    using assms unitarily_equiv_eq[of A] unitary_diag_imp_unitarily_equiv[of A] by simp
  also have "... = Complex_Matrix.trace (Complex_Matrix.adjoint U * (U * B))" 
    using trace_comm assms
    by (metis adjoint_dim' carrier_matD(2) carrier_matI index_mult_mat(2) 
        index_mult_mat(3) unitarily_equiv_carrier(1) unitarily_equiv_carrier(2))
  also have "... = Complex_Matrix.trace B" using assms
    by (smt (z3) Complex_Matrix.unitary_def adjoint_dim_col assoc_mult_mat
        carrier_matD(2) carrier_mat_triv index_mult_mat(3) left_mult_one_mat 
        unitarily_equivD(1) unitarily_equiv_carrier(1) unitarily_equiv_eq 
        unitary_simps(1))
  finally show ?thesis .
qed

lemma  unitarily_equiv_trace':
  assumes "A \<in> carrier_mat n n"
  and "unitarily_equiv A B U"
shows "Complex_Matrix.trace A = (\<Sum> i = 0 ..< dim_row A. B $$ (i,i))"
proof -
  have "Complex_Matrix.trace A = Complex_Matrix.trace B" using assms unitarily_equiv_trace[of A]
    by (meson unitary_diag_imp_unitarily_equiv)
  also have "... = (\<Sum> i = 0 ..< dim_row A. B $$ (i,i))" using assms 
    by (metis Complex_Matrix.trace_def carrier_matD(1) unitarily_equiv_carrier(1))
  finally show ?thesis .
qed

lemma positive_decomp_cmod_le:
  fixes A::"complex Matrix.mat"
  assumes "A\<in> carrier_mat n n"
  and "C\<in> carrier_mat n n"
  and "0 < n"
and "Complex_Matrix.positive A"
and "unitary_diag A B U"
and "\<And>i. i < n \<Longrightarrow> cmod (Complex_Matrix.trace (C * rank_1_proj (Matrix.col U i))) \<le> M"
shows "cmod (Complex_Matrix.trace (C * A)) \<le> Re (Complex_Matrix.trace A) * M"
proof -
  have "dim_row B = n" using assms unitary_diag_carrier(1) 
    by (metis carrier_matD(1))
  have "hermitian A" using assms positive_is_hermitian by simp  
  hence "cmod (Complex_Matrix.trace (C * A)) = 
    cmod (\<Sum> i = 0 ..< n. B$$(i,i) * Complex_Matrix.trace (C * rank_1_proj (Matrix.col U i)))"
    using assms unitary_diag_trace_mult_sum by simp
  also have "... \<le> (\<Sum> i = 0 ..< n. 
    cmod (B$$(i,i) * Complex_Matrix.trace (C * rank_1_proj (Matrix.col U i))))" 
    by (simp add: sum_norm_le)
  also have "... = (\<Sum> i = 0 ..< n. 
    Re (B$$(i,i)) * cmod (Complex_Matrix.trace (C * rank_1_proj (Matrix.col U i))))"
  proof (rule sum.cong, simp)
    show "\<And>x. x \<in> {0..<n} \<Longrightarrow>
         cmod (B $$ (x, x) * Complex_Matrix.trace (C * rank_1_proj (Matrix.col U x))) =
          Re (B $$ (x, x)) * cmod (Complex_Matrix.trace (C * rank_1_proj (Matrix.col U x)))"
      using cmod_mult_pos positive_unitary_diag_pos assms by (metis atLeastLessThan_iff) 
  qed
  also have "... \<le> (\<Sum> i = 0 ..< n. Re (B$$(i,i)) * M)"
  proof -
    have "\<And>i. i < n \<Longrightarrow> 0 \<le> Re (B$$(i,i))" using assms positive_unitary_diag_pos
      less_eq_complex_def by simp
    thus ?thesis using assms by (meson atLeastLessThan_iff mult_left_mono sum_mono) 
  qed
  also have "... = (\<Sum> i = 0 ..< n. Re (B$$(i,i))) * M" by (simp add: sum_distrib_right)
  also have "... = Re (\<Sum> i = 0 ..< n. B$$(i,i)) * M"  by (metis Re_sum)
  also have "... = Re (Complex_Matrix.trace B) * M" unfolding Complex_Matrix.trace_def
    using \<open>dim_row B = n\<close> by simp
  finally show ?thesis using assms unitarily_equiv_trace[of A]
    by (metis unitary_diag_imp_unitarily_equiv)
qed
end