(*
Author: 
  Mnacho Echenim, Université Grenoble Alpes
*)

theory Commuting_Hermitian imports Spectral_Theory_Complements Commuting_Hermitian_Misc
"Projective_Measurements.Linear_Algebra_Complements" 
"Projective_Measurements.Projective_Measurements" begin 

section \<open>Additional results on block decompositions of matrices\<close>

subsection \<open>Split block results\<close>

lemma split_block_diag_carrier:
  assumes "D \<in> carrier_mat n n"
  and "a \<le> n"
  and "split_block D a a = (D1, D2, D3, D4)"
shows "D1\<in> carrier_mat a a" "D4\<in> carrier_mat (n-a) (n-a)"
proof -
  show "D1\<in> carrier_mat a a" using assms unfolding split_block_def
    by (metis Pair_inject mat_carrier)
  show "D4 \<in> carrier_mat (n-a) (n-a)" using assms unfolding split_block_def
    by (metis Pair_inject carrier_matD(1) carrier_matD(2) mat_carrier)
qed

lemma split_block_diagonal:
  assumes "diagonal_mat D"
  and "D \<in> carrier_mat n n"
and "a \<le> n"
and "split_block D a a = (D1, D2, D3, D4)"
shows "diagonal_mat D1 \<and> diagonal_mat D4" unfolding diagonal_mat_def
proof (intro allI conjI impI)
  have "D1 \<in> carrier_mat a a" using assms unfolding split_block_def Let_def 
    by fastforce
  fix i j
  assume "i < dim_row D1"
  and "j < dim_col D1"
  and "i \<noteq> j"
  have "D1 $$ (i,j) = D $$(i,j)" using assms unfolding split_block_def Let_def
    using \<open>i < dim_row D1\<close> \<open>j < dim_col D1\<close> by fastforce
  also have "... = 0" using assms \<open>i \<noteq> j\<close>  \<open>D1 \<in> carrier_mat a a\<close> 
    \<open>i < dim_row D1\<close> \<open>j < dim_col D1\<close> unfolding diagonal_mat_def by fastforce
  finally show "D1 $$(i,j) = 0" .
next
  have "D4 \<in> carrier_mat (n-a) (n-a)" using assms 
    unfolding split_block_def Let_def by fastforce
  fix i j
  assume "i < dim_row D4"
  and "j < dim_col D4"
  and "i \<noteq> j"
  have "D4 $$ (i,j) = D $$(i + a,j + a)" using assms unfolding split_block_def Let_def
    using \<open>i < dim_row D4\<close> \<open>j < dim_col D4\<close> by fastforce
  also have "... = 0" using assms \<open>i \<noteq> j\<close>  \<open>D4 \<in> carrier_mat (n-a) (n-a)\<close> 
    \<open>i < dim_row D4\<close> \<open>j < dim_col D4\<close> unfolding diagonal_mat_def by fastforce
  finally show "D4 $$(i,j) = 0" .
qed

lemma split_block_times_diag_index:
  fixes B::"'a::comm_ring Matrix.mat"
  assumes "diagonal_mat D"
  and "D\<in> carrier_mat n n"
  and "B\<in> carrier_mat n n"
  and "a \<le> n"
  and "split_block B a a = (B1, B2, B3, B4)"
  and "split_block D a a = (D1, D2, D3, D4)"
  and "i < dim_row (D4 * B4)"
  and "j < dim_col (D4 * B4)"
shows "(B4 * D4) $$ (i, j) = (B*D) $$ (i+a, j+a)"
      "(D4 * B4) $$ (i, j) = (D*B) $$ (i+a, j+a)"
proof -
  have d4: "D4 \<in> carrier_mat (n-a) (n-a)" using assms  
      split_block(4)[of D] by simp
  have b4: "B4 \<in> carrier_mat (n-a) (n-a)" using assms  
      split_block(4)[of B] by simp
  have "diagonal_mat D4" using assms split_block_diagonal[of D] by blast
  have "i < n-a" using \<open>i < dim_row (D4 * B4)\<close> b4 d4 by simp
  have "j < n-a" using \<open>j < dim_col (D4 * B4)\<close> b4 d4 by simp
  have "(B4 * D4) $$ (i, j) = D4 $$ (j,j) * B4 $$ (i,j)" 
  proof (rule  diagonal_mat_mult_index') 
    show "diagonal_mat D4" using \<open>diagonal_mat D4\<close> .
    show "B4 \<in> carrier_mat (n-a) (n-a)" using b4 .
    show "D4 \<in> carrier_mat (n - a) (n - a)" using d4 .
    show "i < n-a" using \<open>i < n-a\<close> .
    show "j < n-a" using \<open>j < n-a\<close> .
  qed
  also have "... = D $$ (j+a, j+a) * B $$ (i+a, j+a)" 
    using assms \<open>i < n-a\<close> \<open>j < n-a\<close> 
    unfolding split_block_def Let_def by fastforce 
  also have "... = (B*D) $$ (i+a, j+a)" using diagonal_mat_mult_index' assms
    by (metis \<open>i < n - a\<close> \<open>j < n - a\<close> less_diff_conv)
  finally show "(B4 * D4) $$ (i, j) = (B*D) $$ (i+a, j+a)" .
  have "(D4 * B4) $$ (i, j) = D4 $$ (i,i) * B4 $$ (i,j)" 
    using diagonal_mat_mult_index \<open>diagonal_mat D4\<close> \<open>i < n - a\<close> \<open>j < n - a\<close> b4 d4 
    by blast
  also have "... = D $$ (i+a, i+a) * B $$ (i+a, j+a)" 
    using assms \<open>i < n-a\<close> \<open>j < n-a\<close> 
    unfolding split_block_def Let_def by fastforce
  also have "... = (D*B) $$ (i+a, j+a)" using diagonal_mat_mult_index assms
    by (metis \<open>i < n - a\<close> \<open>j < n - a\<close> less_diff_conv)
  finally show "(D4 * B4) $$ (i, j) = (D*B) $$ (i+a, j+a)" .
qed

lemma split_block_commute_subblock:
  fixes B::"'a::comm_ring Matrix.mat"
  assumes "diagonal_mat D"
  and "D\<in> carrier_mat n n"
  and "B\<in> carrier_mat n n"
  and "a \<le> n"
  and "split_block B a a = (B1, B2, B3, B4)"
  and "split_block D a a = (D1, D2, D3, D4)"
  and "B * D = D * B"
shows "B4 * D4 = D4 * B4"
proof
  have d4: "D4 \<in> carrier_mat (n-a) (n-a)" using assms  
      split_block(4)[of D] by simp
  have b4: "B4 \<in> carrier_mat (n-a) (n-a)" using assms  
      split_block(4)[of B] by simp
  have "diagonal_mat D4" using assms split_block_diagonal[of D] by blast
  show "dim_row (B4 * D4) = dim_row (D4 * B4)" using d4 b4 by simp
  show "dim_col (B4 * D4) = dim_col (D4 * B4)" using d4 b4 by simp
  fix i j
  assume "i < dim_row (D4 * B4)"
  and "j < dim_col (D4 * B4)"
  have "(B4*D4) $$(i,j) = (B*D) $$(i+a, j+a)"
    using split_block_times_diag_index[of D n B a] assms
      \<open>i < dim_row (D4 * B4)\<close> \<open>j < dim_col (D4 * B4)\<close> by blast
  also have "... = (D*B) $$ (i+a, j+a)" using assms by simp
  also have "... = (D4*B4) $$ (i, j)"
    using split_block_times_diag_index[of D n B a] assms
    by (metis \<open>i < dim_row (D4 * B4)\<close> \<open>j < dim_col (D4 * B4)\<close>)
  finally show "(B4*D4) $$(i,j) = (D4*B4) $$ (i, j)" .
qed

lemma commute_diag_mat_zero_comp:
  fixes D::"'a::{field} Matrix.mat"
  assumes "diagonal_mat D"
  and "D\<in> carrier_mat n n"
  and "B\<in> carrier_mat n n"
  and" B* D = D * B"
  and "i < n"
  and "j < n"
  and "D$$(i,i) \<noteq> D$$(j,j)"
shows "B $$(i,j) = 0"
proof -
  have "B$$(i,j) * D$$(j,j) = (B*D) $$(i,j)" 
    using diagonal_mat_mult_index'[of B n D] assms by simp
  also have "... = (D*B) $$ (i,j)" using assms by simp
  also have "... = B$$(i,j) * D$$(i,i)" 
    using diagonal_mat_mult_index  assms
    by (metis Groups.mult_ac(2))
  finally have "B$$(i,j) * D$$(j,j) = B$$(i,j) * D$$(i,i)" .
  hence "B$$(i,j) * (D$$(j,j) - D$$(i,i)) = 0" by auto
  thus "B$$(i,j) = 0" using assms by simp
qed

lemma commute_diag_mat_split_block:
  fixes D::"'a::{field} Matrix.mat"
  assumes "diagonal_mat D"
  and "D\<in> carrier_mat n n"
  and "B\<in> carrier_mat n n"
  and" B* D = D * B"
  and "k \<le> n"
  and "\<forall>i j. (i < k \<and> k \<le> j \<and> j < n) \<longrightarrow> D$$(i,i) \<noteq> D$$(j,j)"
  and "(B1, B2, B3, B4) = split_block B k k"
shows "B2 = 0\<^sub>m k (n-k)" "B3 = 0\<^sub>m (n-k) k"
proof (intro eq_matI)
  show "dim_row B2 = dim_row (0\<^sub>m k (n - k))" 
    using assms unfolding split_block_def Let_def by simp
  show "dim_col B2 = dim_col (0\<^sub>m k (n - k))" 
    using assms unfolding split_block_def Let_def by simp
  fix i j
  assume "i < dim_row (0\<^sub>m k (n - k))"
  and "j < dim_col (0\<^sub>m k (n - k))" note ijprop = this
  have "B2 $$ (i, j) = B $$ (i, j+k)" using assms ijprop 
    unfolding split_block_def Let_def by simp
  also have "... = 0" 
  proof (rule commute_diag_mat_zero_comp[of D n], (auto simp add: assms))
    show "i < n" using ijprop assms by simp
    show "j + k < n" using ijprop assms by simp
    show "D $$ (i, i) = D $$ (j + k, j + k) \<Longrightarrow> False" using ijprop assms
      by (metis \<open>j + k < n\<close> index_zero_mat(2) le_add2)
  qed
  finally show "B2 $$ (i, j) = 0\<^sub>m k (n - k) $$ (i, j)" using ijprop by simp
next 
  show "B3 = 0\<^sub>m (n-k) k"
  proof (intro eq_matI)
    show "dim_row B3 = dim_row (0\<^sub>m (n - k) k)" 
      using assms unfolding split_block_def Let_def by simp
    show "dim_col B3 = dim_col (0\<^sub>m (n - k) k)" 
      using assms unfolding split_block_def Let_def by simp
    fix i j
    assume "i < dim_row (0\<^sub>m (n - k) k)"
    and "j < dim_col (0\<^sub>m (n - k) k)" note ijprop = this
    have "B3 $$ (i, j) = B $$ (i+k, j)" using assms ijprop 
      unfolding split_block_def Let_def by simp
    also have "... = 0" 
    proof (rule commute_diag_mat_zero_comp[of D n], (auto simp add: assms))
      show "i + k < n" using ijprop assms by simp
      show "j < n" using ijprop assms by simp
      show "D $$ (i+k, i+k) = D $$ (j, j) \<Longrightarrow> False" using ijprop assms
        by (metis \<open>i + k < n\<close> index_zero_mat(3) le_add2)
    qed
    finally show "B3 $$ (i, j) = 0\<^sub>m (n - k) k $$ (i, j)" using ijprop by simp
  qed
qed

lemma split_block_hermitian_1:
  assumes "hermitian A"
  and "n \<le> dim_row A"
and "(A1, A2, A3, A4) = split_block A n n"
shows "hermitian A1"  unfolding hermitian_def
proof (rule eq_matI, auto)
  have "dim_row A = dim_col A" using assms
    by (metis carrier_matD(2) hermitian_square) 
  show "dim_col A1 = dim_row A1" using assms unfolding split_block_def Let_def 
    by simp
  thus "dim_row A1 = dim_col A1" by simp
  show "\<And>i j. i < dim_row A1 \<Longrightarrow> j < dim_col A1 \<Longrightarrow> 
    Complex_Matrix.adjoint A1 $$ (i, j) = A1 $$ (i, j)"
  proof -
    fix i j
    assume "i < dim_row A1" and "j < dim_col A1" note ij = this
    have r: "dim_row A1 = n" using assms unfolding split_block_def Let_def 
      by simp
    have c: "dim_col A1 = n" using assms unfolding split_block_def Let_def 
      by simp
    have "Complex_Matrix.adjoint A1 $$ (i, j) = conjugate (A1 $$ (j,i))"
      using ij r c unfolding Complex_Matrix.adjoint_def by simp
    also have "... = conjugate (A $$ (j,i))" using assms ij r c
      unfolding split_block_def Let_def by simp
    also have "... = A $$ (i,j)" using assms ij r c \<open>dim_row A = dim_col A\<close>
      unfolding hermitian_def Complex_Matrix.adjoint_def
      by (metis adjoint_eval assms(1) hermitian_def order_less_le_trans)
    also have "... = A1 $$(i,j)" using assms ij r c 
      unfolding split_block_def Let_def by simp
    finally show "Complex_Matrix.adjoint A1 $$ (i, j) = A1 $$ (i, j)" .
  qed
qed

lemma split_block_hermitian_4:
  assumes "hermitian A"
  and "n \<le> dim_row A"
and "(A1, A2, A3, A4) = split_block A n n"
shows "hermitian A4"  unfolding hermitian_def
proof (rule eq_matI, auto)
  have arc: "dim_row A = dim_col A" using assms
    by (metis carrier_matD(2) hermitian_square) 
  thus "dim_col A4 = dim_row A4" using assms unfolding split_block_def Let_def 
    by simp
  thus "dim_row A4 = dim_col A4" by simp
  show "\<And>i j. i < dim_row A4 \<Longrightarrow> j < dim_col A4 \<Longrightarrow> 
    Complex_Matrix.adjoint A4 $$ (i, j) = A4 $$ (i, j)"
  proof -
    fix i j
    assume "i < dim_row A4" and "j < dim_col A4" note ij = this
    have r: "dim_row A4 = dim_row A - n" using assms 
      unfolding split_block_def Let_def by simp
    have c: "dim_col A4 = dim_col A - n" using assms 
      unfolding split_block_def Let_def by simp
    have "Complex_Matrix.adjoint A4 $$ (i, j) = conjugate (A4 $$ (j,i))"
      using ij r c arc unfolding Complex_Matrix.adjoint_def by simp
    also have "... = conjugate (A $$ (j +n ,i+n))" using assms ij r c arc
      unfolding split_block_def Let_def by simp
    also have "... = A $$ (i+n,j+n)" using assms ij r c arc 
      unfolding hermitian_def Complex_Matrix.adjoint_def
      by (metis index_mat(1) less_diff_conv split_conv)      
    also have "... = A4 $$(i,j)" using assms ij r c 
      unfolding split_block_def Let_def by simp
    finally show "Complex_Matrix.adjoint A4 $$ (i, j) = A4 $$ (i, j)" .
  qed
qed

lemma diag_block_split_block:
  assumes "B\<in> carrier_mat n n"
  and "k < n"
  and "(B1, B2, B3, B4) = split_block B k k"
  and "B2 = 0\<^sub>m k (n-k)" 
  and "B3 = 0\<^sub>m (n-k) k"
shows "B = diag_block_mat [B1,B4]"
proof -
  have dr: "dim_row B = k + (n-k)" using assms by simp
  have dc: "dim_col B = k + (n-k)" using assms by simp
  have c1: "B1 \<in> carrier_mat k k" using assms 
    split_block(1)[of B, OF _ dr dc] by metis
  have c4: "B4 \<in> carrier_mat (n-k) (n-k)" using assms 
    split_block(4)[of B, OF _ dr dc] by metis
  have d4: "diag_block_mat [B4] = B4" using diag_block_mat_singleton[of B4] 
    by simp
  have "B = four_block_mat B1 B2 B3 B4" using assms split_block(3)[of B k ]
    by (metis carrier_matD(1) carrier_matD(2) diff_is_0_eq 
        le_add_diff_inverse nat_le_linear semiring_norm(137) 
        split_block(5) zero_less_diff) 
  also have "... = four_block_mat B1 (0\<^sub>m k (n-k)) (0\<^sub>m (n-k) k) B4" 
    using assms by simp
  also have "... = four_block_mat B1 (0\<^sub>m k (n-k)) (0\<^sub>m (n-k) k) 
    (diag_block_mat [B4])" using diag_block_mat_singleton[of B4] by simp
  also have "... = diag_block_mat [B1, B4]" 
    using diag_block_mat.simps(2)[of B1 "[B4]"] c1 c4 
    unfolding Let_def by auto
  finally show ?thesis .
qed

subsection \<open>Diagonal block matrices\<close>

abbreviation four_block_diag where
"four_block_diag B1 B2 \<equiv>
  (four_block_mat B1 (0\<^sub>m (dim_row B1) (dim_col B2)) 
  (0\<^sub>m (dim_row B2) (dim_col B1)) B2)"

lemma four_block_diag_cong_comp:
  assumes "dim_row A1 = dim_row B1"
  and "dim_col A1 = dim_col B1"
  and "four_block_diag A1 A2 = four_block_diag B1 B2"
shows "A1 = B1"
proof (rule eq_matI, auto simp:assms)
  define A where "A = four_block_diag A1 A2"
  define B where "B = four_block_diag B1 B2"
  fix i j
  assume "i < dim_row B1" and "j<dim_col B1" note ij=this
  hence "i <dim_row A1" "j<dim_col A1" using assms by auto
  hence "A1$$(i,j) = A$$(i, j)" 
    unfolding A_def four_block_mat_def Let_def by force 
  also have "... = B$$(i, j)" using assms unfolding A_def B_def by simp
  also have "... = B1$$(i,j)" 
    using ij unfolding B_def four_block_mat_def Let_def by force 
  finally show "A1$$(i,j) = B1$$(i,j)" .
qed

lemma four_block_diag_cong_comp':
  assumes "dim_row A1 = dim_row B1"
  and "dim_col A1 = dim_col B1"
  and "four_block_diag A1 A2 = four_block_diag B1 B2"
shows "A2 = B2"
proof (rule eq_matI)
  define n where "n=dim_row A1"
  define m where "m = dim_col A1"
  define A where "A = four_block_diag A1 A2"
  define B where "B = four_block_diag B1 B2"
  show "dim_row A2 = dim_row B2" 
    using assms unfolding four_block_mat_def Let_def
    by (metis assms(3) diff_add_inverse index_mat_four_block(2)) 
  show "dim_col A2 = dim_col B2"
    using assms unfolding four_block_mat_def Let_def
    by (metis assms(3) diff_add_inverse index_mat_four_block(3))
  fix i j
  assume "i < dim_row B2" and "j<dim_col B2" note ij=this
  hence "i+n < dim_row A" 
    unfolding A_def n_def m_def four_block_mat_def Let_def
    by (simp add: \<open>dim_row A2 = dim_row B2\<close>)
  have "j+m < dim_col A"
    unfolding A_def n_def m_def four_block_mat_def Let_def
    by (simp add: \<open>dim_col A2 = dim_col B2\<close> ij)
  {
    have "n \<le> i+n" by simp
    have "m\<le> j+m" by simp
    have "i + n - n = i" by simp
    have "j + m - m = j" by simp
  } note ijeq = this
  have "A2$$(i,j) = A$$(i+n, j+m)" using ijeq
    using A_def \<open>i + n < dim_row A\<close> \<open>j + m < dim_col A\<close> m_def n_def by force 
  also have "... = B$$(i+n, j+m)" using assms unfolding A_def B_def by simp
  also have "... = B2$$(i,j)" using ijeq
    by (metis A_def B_def \<open>i + n < dim_row A\<close> \<open>j + m < dim_col A\<close> 
        add_implies_diff assms(1) assms(2) assms(3) index_mat_four_block(1) 
        index_mat_four_block(2) index_mat_four_block(3) m_def n_def 
        not_add_less2)
  finally show "A2$$(i,j) = B2$$(i,j)" .
qed

lemma four_block_mat_real_diag:
  assumes "\<forall>i < dim_row B1. B1$$(i,i) \<in> Reals"
  and "\<forall>i < dim_row B2. B2$$(i,i) \<in> Reals"
  and "dim_row B1 = dim_col B1"
  and "dim_row B2 = dim_col B2"
  and "i < dim_row (four_block_diag B1 B2)"
shows "(four_block_diag B1 B2) $$ (i,i) \<in> Reals" 
proof (cases "i < dim_row B1")
  case True  
  then show ?thesis using assms  by simp
next
  case False
  then show ?thesis using assms by force
qed

lemma four_block_diagonal:
  assumes "dim_row B1 = dim_col B1"
  and "dim_row B2 = dim_col B2"
  and "diagonal_mat B1"
  and "diagonal_mat B2"
shows "diagonal_mat (four_block_diag B1 B2)" unfolding diagonal_mat_def 
proof (intro allI impI)
  fix i j
  assume "i < dim_row (four_block_diag B1 B2)"
  and "j < dim_col (four_block_diag B1 B2)"
  and "i \<noteq> j" note ijprops = this
  show "(four_block_diag B1 B2) $$ (i,j) = 0" 
  proof (cases "i < dim_row B1")
    case True
    then show ?thesis 
      using assms(3) diagonal_mat_def ijprops(2) ijprops(3)
      by (metis add_less_imp_less_left  
          ijprops(1) index_mat_four_block(1) index_mat_four_block(2) 
          index_mat_four_block(3) index_zero_mat(1) 
          linordered_semidom_class.add_diff_inverse) 
  next
    case False
    then show ?thesis using ijprops 
      by (metis (no_types, lifting) add_less_cancel_left assms(1) 
          assms(4) diagonal_mat_def index_mat_four_block(1) 
          index_mat_four_block(2) index_mat_four_block(3) 
          index_zero_mat(1) linordered_semidom_class.add_diff_inverse)
  qed
qed

lemma four_block_diag_zero:
  assumes "B\<in> carrier_mat 0 0"
  shows "four_block_diag A B = A"
proof (rule eq_matI, auto)
  show "dim_row B = 0" using assms by simp
  show "dim_col B = 0" using assms by simp
qed

lemma four_block_diag_zero':
  assumes "B\<in> carrier_mat 0 0"
  shows "four_block_diag B A = A"
proof (rule eq_matI)
  show "dim_row (four_block_diag B A) = dim_row A" using assms by simp
  show "dim_col (four_block_diag B A) = dim_col A" using assms by simp
  fix i j
  assume "i < dim_row A" and "j < dim_col A"
  thus "four_block_diag B A $$ (i, j) = A $$ (i, j)"
    using \<open>dim_col (four_block_diag B A) = dim_col A\<close> 
      \<open>dim_row (four_block_diag B A) = dim_row A\<close> 
  by auto
qed

lemma mult_four_block_diag:
  assumes "A1 \<in> carrier_mat nr1 n1" "D1 \<in> carrier_mat nr2 n2" 
  and "A2 \<in> carrier_mat n1 nc1" "D2 \<in> carrier_mat n2 nc2"
shows "four_block_diag A1 D1 * 
  four_block_diag A2  D2
  = four_block_diag (A1 * A2) (D1 * D2)" 
proof -
  define fb1 where "fb1 = four_block_mat A1 (0\<^sub>m nr1 n2) (0\<^sub>m nr2 n1) D1"
  define fb2 where "fb2 = four_block_mat A2 (0\<^sub>m n1 nc2) (0\<^sub>m n2 nc1) D2"
  have "fb1 * fb2 = four_block_mat (A1 * A2 + 0\<^sub>m nr1 n2 * 0\<^sub>m n2 nc1) 
    (A1 * 0\<^sub>m n1 nc2 + 0\<^sub>m nr1 n2 * D2) (0\<^sub>m nr2 n1 * A2 + D1 * 0\<^sub>m n2 nc1)
    (0\<^sub>m nr2 n1 * 0\<^sub>m n1 nc2 + D1 * D2)" unfolding fb1_def fb2_def
  proof (rule mult_four_block_mat)
    show "A1 \<in> carrier_mat nr1 n1" using assms by simp
    show "D1 \<in> carrier_mat nr2 n2" using assms by simp
    show "A2 \<in> carrier_mat n1 nc1" "D2 \<in> carrier_mat n2 nc2" using assms by auto
  qed auto  
  also have "... = four_block_mat (A1 * A2) (0\<^sub>m nr1 nc2) (0\<^sub>m nr2 nc1) (D1 * D2)" 
    using assms by simp
  finally show ?thesis unfolding fb1_def fb2_def  
    using assms by simp
qed

lemma four_block_diag_adjoint:
  shows  "(Complex_Matrix.adjoint (four_block_diag A1 A2)) = 
    (four_block_diag (Complex_Matrix.adjoint A1) 
    (Complex_Matrix.adjoint A2))" 
    by (rule eq_matI, 
        auto simp: four_block_mat_adjoint zero_adjoint adjoint_eval)

lemma four_block_diag_unitary:
  assumes "unitary U1"
  and "unitary U2"
shows "unitary
  (four_block_diag U1 U2)"
(is "unitary ?fU")
  unfolding unitary_def
proof
  show "?fU \<in> carrier_mat (dim_row ?fU) (dim_row ?fU)" 
    by (metis Complex_Matrix.unitary_def assms(1) assms(2) 
        four_block_carrier_mat index_mat_four_block(2))
  define n where "n = dim_row ?fU"
  show "inverts_mat ?fU (Complex_Matrix.adjoint ?fU)"
  proof -
    have "(Complex_Matrix.adjoint ?fU) = 
      (four_block_mat (Complex_Matrix.adjoint U1) 
      (0\<^sub>m (dim_col U1) (dim_row U2)) 
      (0\<^sub>m (dim_col U2) (dim_row U1)) 
      (Complex_Matrix.adjoint U2))" 
      by (rule eq_matI, 
          auto simp: four_block_mat_adjoint zero_adjoint adjoint_eval)
    hence "?fU * (Complex_Matrix.adjoint ?fU) = 
      ?fU * (four_block_diag (Complex_Matrix.adjoint U1) 
      (Complex_Matrix.adjoint U2))"  by simp
    also have "... = four_block_diag
      (U1 * (Complex_Matrix.adjoint U1))
      (U2 * (Complex_Matrix.adjoint U2))"
      by (rule mult_four_block_diag, (auto simp add: assms))
    also have "... = four_block_mat
      (1\<^sub>m (dim_row U1))
      (0\<^sub>m (dim_row U1)  (dim_row U2))
      (0\<^sub>m (dim_row U2)  (dim_row U1))
      (1\<^sub>m (dim_row U2))" using assms 
      unfolding unitary_def inverts_mat_def 
      by simp
    also have "... = 1\<^sub>m (dim_row U1 + dim_row U2)" by simp
    finally show ?thesis unfolding inverts_mat_def  by simp
  qed
qed

lemma four_block_diag_similar:
  assumes "unitarily_equiv A1 B1 U1"
  and "unitarily_equiv A2 B2 U2"
  and "dim_row A1 = dim_col A1"
  and "dim_row A2 = dim_col A2"
shows "similar_mat_wit 
  (four_block_diag A1 A2)
  (four_block_diag B1 B2)
  (four_block_diag U1 U2)
  (Complex_Matrix.adjoint (four_block_diag U1 U2))"
  unfolding similar_mat_wit_def
proof (simp add: Let_def, intro conjI)
  define n where "n = dim_row A1 + dim_row A2"
  show "four_block_diag A1 A2 \<in> carrier_mat n n" unfolding n_def using assms 
    by auto
  show "four_block_diag B1 B2 \<in> carrier_mat n n" unfolding n_def using assms
    by (metis carrier_matI four_block_carrier_mat unitarily_equiv_carrier(1))
  show u: "four_block_diag U1 U2 \<in> carrier_mat n n" unfolding n_def using assms
    by (metis carrier_matI four_block_carrier_mat unitarily_equiv_carrier(2))
  thus cu: "Complex_Matrix.adjoint (four_block_diag U1 U2) \<in> carrier_mat n n" 
    unfolding n_def using adjoint_dim' by blast
  show "four_block_diag U1 U2*Complex_Matrix.adjoint (four_block_diag U1 U2) =
    1\<^sub>m n" unfolding n_def
    using u assms four_block_diag_unitary n_def 
      unitarily_equiv_def unitary_simps(2) by blast
  thus "Complex_Matrix.adjoint (four_block_diag U1 U2)*four_block_diag U1 U2 = 
    1\<^sub>m n"
    using cu mat_mult_left_right_inverse u by blast 
  have "four_block_diag A1 A2 = 
    four_block_diag (U1 * B1 * (Complex_Matrix.adjoint U1))
    (U2 * B2 * (Complex_Matrix.adjoint U2))"
    using assms unitarily_equiv_eq by blast
  also have "... = (four_block_diag (U1*B1) (U2*B2)) *
    (four_block_diag (Complex_Matrix.adjoint U1)
    (Complex_Matrix.adjoint U2))"  
  proof (rule mult_four_block_diag[symmetric])
    show "U1 * B1 \<in> carrier_mat (dim_row A1) (dim_row A1)"
      by (metis assms(1) assms(3) carrier_mat_triv mult_carrier_mat 
          unitarily_equiv_carrier(1) unitarily_equiv_carrier(2))
    show "U2 * B2 \<in> carrier_mat (dim_row A2) (dim_row A2)"
      by (metis assms(2) assms(4) carrier_mat_triv mult_carrier_mat 
          unitarily_equiv_carrier(1) unitarily_equiv_carrier(2))
    show "Complex_Matrix.adjoint U1 \<in> carrier_mat (dim_row A1) (dim_row A1)"
      by (metis Complex_Matrix.unitary_def adjoint_dim assms(1) 
          index_mult_mat(2) unitarily_equivD(1) unitarily_equiv_eq)
    show "Complex_Matrix.adjoint U2 \<in> carrier_mat (dim_row A2) (dim_row A2)"
      by (meson assms(2) carrier_mat_triv similar_mat_witD2(7) 
          unitarily_equiv_def)
  qed
  also have "... = four_block_diag U1 U2 * four_block_diag B1 B2 * 
    Complex_Matrix.adjoint (four_block_diag U1 U2)"
  proof -
    have "four_block_diag (U1*B1) (U2*B2) = 
      four_block_diag U1 U2 * four_block_diag B1 B2" 
    proof (rule mult_four_block_diag[symmetric])
      show "U1 \<in> carrier_mat (dim_row A1) (dim_row A1)"
        by (metis assms(1) assms(3) carrier_mat_triv 
            unitarily_equiv_carrier(2))
      show "B1 \<in> carrier_mat (dim_row A1) (dim_row A1)"
        by (metis assms(1) assms(3) carrier_mat_triv 
            unitarily_equiv_carrier(1))
      show "U2 \<in> carrier_mat (dim_row A2) (dim_row A2)"
        by (metis assms(2) assms(4) carrier_mat_triv 
            unitarily_equiv_carrier(2))
      show "B2 \<in> carrier_mat (dim_row A2) (dim_row A2)"
        by (metis assms(2) assms(4) carrier_mat_triv 
            unitarily_equiv_carrier(1))
    qed
    moreover have "four_block_diag (Complex_Matrix.adjoint U1)
     (Complex_Matrix.adjoint U2) = 
      Complex_Matrix.adjoint (four_block_diag U1 U2)" 
      by (rule four_block_diag_adjoint[symmetric])
    ultimately show ?thesis by simp
  qed
  finally show "four_block_diag A1 A2 = 
    four_block_diag U1 U2 * four_block_diag B1 B2 * 
    Complex_Matrix.adjoint (four_block_diag U1 U2)" .
qed

lemma four_block_unitarily_equiv:
  assumes "unitarily_equiv A1 B1 U1"
  and "unitarily_equiv A2 B2 U2"
  and "dim_row A1 = dim_col A1"
  and "dim_row A2 = dim_col A2"
shows "unitarily_equiv 
  (four_block_diag A1 A2)
  (four_block_diag B1 B2)
  (four_block_diag U1 U2)"
(is "unitarily_equiv ?fA ?fB ?fU")
  unfolding unitarily_equiv_def
proof 
  show "unitary ?fU" using four_block_diag_unitary assms unitarily_equivD(1) 
    by blast  
  show "similar_mat_wit ?fA ?fB ?fU (Complex_Matrix.adjoint ?fU)" 
    using assms four_block_diag_similar[of A1] by simp
qed

lemma four_block_unitary_diag:
  assumes "unitary_diag A1 B1 U1"
  and "unitary_diag A2 B2 U2"
  and "dim_row A1 = dim_col A1"
  and "dim_row A2 = dim_col A2"
shows "unitary_diag 
  (four_block_diag A1 A2)
  (four_block_diag B1 B2)
  (four_block_diag U1 U2)"
(is "unitary_diag ?fA ?fB ?fU")
  unfolding unitary_diag_def
proof
  show "unitarily_equiv ?fA ?fB ?fU" 
    using four_block_unitarily_equiv[of A1] assms by simp
  have "dim_row B1 = dim_col B1" unfolding unitary_diag_def
    by (metis assms(1) assms(3) carrier_matD(1) carrier_matD(2) 
          carrier_mat_triv unitary_diag_carrier(1))
  moreover have "dim_row B2 = dim_col B2"  unfolding unitary_diag_def
    by (metis assms(2) assms(4) carrier_matD(1) carrier_matD(2) 
        carrier_mat_triv unitary_diag_carrier(1))
  ultimately show "diagonal_mat ?fB" using four_block_diagonal assms 
    unfolding unitary_diag_def by blast
qed

lemma four_block_real_diag_decomp:
  assumes "real_diag_decomp A1 B1 U1"
  and "real_diag_decomp A2 B2 U2"
  and "dim_row A1 = dim_col A1"
  and "dim_row A2 = dim_col A2"
shows "real_diag_decomp 
  (four_block_diag A1 A2)
  (four_block_diag B1 B2)
  (four_block_diag U1 U2)"
(is "real_diag_decomp ?fA ?fB ?fU")
  unfolding real_diag_decomp_def
proof (intro conjI allI impI)
  show "unitary_diag ?fA ?fB ?fU" using four_block_unitary_diag assms 
    unfolding real_diag_decomp_def by blast
  fix i
  assume "i < dim_row ?fB" 
  show "?fB $$ (i,i) \<in> Reals" 
  proof (rule four_block_mat_real_diag)
    show "i < dim_row ?fB" using \<open>i < dim_row ?fB\<close> .
    show "\<forall>i<dim_row B1. B1 $$ (i, i) \<in> \<real>" using assms 
      unfolding real_diag_decomp_def by simp
    show "\<forall>i<dim_row B2. B2 $$ (i, i) \<in> \<real>" using assms 
      unfolding real_diag_decomp_def by simp
    show "dim_row B1 = dim_col B1"  unfolding unitary_diag_def
      by (metis assms(1) assms(3) carrier_matD(1) carrier_matD(2) 
          carrier_mat_triv real_diag_decompD(1) unitary_diag_carrier(1))
    show "dim_row B2 = dim_col B2"  unfolding unitary_diag_def
      by (metis assms(2) assms(4) carrier_matD(1) carrier_matD(2) 
          carrier_mat_triv real_diag_decompD(1) unitary_diag_carrier(1))
  qed
qed

lemma diag_block_mat_mult:
  assumes "length Al = length Bl"
  and "\<forall>i < length Al. dim_col (Al!i) = dim_row (Bl!i)"
shows "diag_block_mat Al * (diag_block_mat Bl) = 
  (diag_block_mat (map2 (*) Al Bl))" using assms
proof (induct Al arbitrary: Bl)
  case Nil
  then show ?case by simp
next
  case (Cons a Al)
  define A where "A = diag_block_mat Al"
  define B where "B = diag_block_mat (tl Bl)"
  have "0 < length Bl" using Cons by auto
  hence "Bl = hd Bl # (tl Bl)" by simp
  have "length (tl Bl) = length Al" using Cons by simp
  have dim: "\<forall>i<length Al. dim_col (Al ! i) = dim_row (tl Bl ! i)"
  proof (intro allI impI)
    fix i
    assume "i < length Al"
    hence "dim_col (Al ! i) = dim_col ((a#Al)!(Suc i))" by simp
    also have "... = dim_row (Bl!(Suc i))" using Cons
      by (metis Suc_lessI \<open>i < length Al\<close> length_Cons less_Suc_eq)
    also have "... = dim_row (tl Bl!i)"
      by (metis \<open>Bl = hd Bl # tl Bl\<close> nth_Cons_Suc) 
    finally show "dim_col (Al ! i) = dim_row (tl Bl!i)" .
  qed
  define C where "C = map2 (*) (a # Al) Bl"
  have "hd C = a * hd Bl" using \<open>Bl = hd Bl # tl Bl\<close> unfolding C_def
    by (metis list.map(2) list.sel(1) prod.simps(2) zip_Cons_Cons)
  have "tl C = map2 (*) Al (tl Bl)"
    by (metis (no_types, lifting) C_def \<open>Bl = hd Bl # tl Bl\<close> list.sel(3) 
        map_tl zip_Cons_Cons)
  have "C = hd C # (tl C)" unfolding C_def
    by (metis Nil_eq_zip_iff Nil_is_map_conv \<open>Bl = hd Bl # tl Bl\<close> 
        list.exhaust_sel list.simps(3))
  have "dim_row B = sum_list (map dim_row (tl Bl))" unfolding B_def
    by (simp add: dim_diag_block_mat(1))
  also have "... = sum_list (map dim_col Al)" 
  proof (rule sum_list_cong)
    show "length (map dim_row (tl Bl)) = length (map dim_col Al)"  
      using  \<open>length (tl Bl) = length Al\<close> by simp
    show "\<forall>i<length (map dim_row (tl Bl)). 
      map dim_row (tl Bl) ! i = map dim_col Al ! i"
      by (metis \<open>length (tl Bl) = length Al\<close> dim length_map nth_map)
  qed
  also have "... = dim_col A" unfolding A_def
    by (simp add: dim_diag_block_mat(2))
  finally have ba: "dim_row B = dim_col A" .  
  have "diag_block_mat (a#Al) * (diag_block_mat Bl) = 
    four_block_diag a A * (four_block_diag (hd Bl) B)" 
    using diag_block_mat.simps(2) \<open>Bl = hd Bl # (tl Bl)\<close> 
    unfolding Let_def A_def B_def by metis
  also have "... = four_block_diag (a * hd Bl) (A * B)"     
  proof (rule mult_four_block_diag)
    show "a\<in> carrier_mat (dim_row a) (dim_col a)" by simp 
    show "hd Bl \<in> carrier_mat (dim_col a) (dim_col (hd Bl))"
      using Cons
      by (metis \<open>0 < length Bl\<close> \<open>Bl = hd Bl # tl Bl\<close> carrier_mat_triv nth_Cons_0)
    show "A \<in> carrier_mat (dim_row A) (dim_col A)" by simp
    show " B \<in> carrier_mat (dim_col A) (dim_col B)" using ba by auto
  qed
  also have "... = four_block_diag (hd C) (diag_block_mat (tl C))" 
    unfolding A_def B_def 
    using C_def \<open>hd C = a * hd Bl\<close> \<open>length (tl Bl) = length Al\<close> 
      \<open>tl C = map2 (*) Al (tl Bl)\<close> dim local.Cons(1) 
    by presburger
  also have "... = diag_block_mat C" 
    using \<open>C = hd C#(tl C)\<close> diag_block_mat.simps(2) unfolding Let_def by metis
  finally show ?case unfolding C_def .
qed

lemma real_diag_decomp_block:
  fixes Al::"complex Matrix.mat list"
  assumes "Al \<noteq> []"
  and "list_all (\<lambda>A. 0 < dim_row A \<and> hermitian A)  Al"
shows "\<exists> Bl Ul. length Ul = length Al \<and>
  (\<forall>i < length Al. 
    Ul!i \<in> carrier_mat (dim_row (Al!i)) (dim_col (Al!i)) \<and> unitary (Ul!i) \<and>
    Bl!i \<in> carrier_mat (dim_row (Al!i)) (dim_col (Al!i))) \<and>
  real_diag_decomp (diag_block_mat Al) (diag_block_mat Bl) (diag_block_mat Ul)"
  using assms
proof (induct Al)
  case Nil
  then show ?case by simp
next
  case (Cons A Al)
  hence "hermitian A" "0 < dim_row A" by auto
  hence "A \<in> carrier_mat (dim_row A) (dim_row A)"
    by (simp add: hermitian_square)
  from this obtain B U where r: "real_diag_decomp A B U" 
    using hermitian_real_diag_decomp \<open>hermitian A\<close> \<open>0 < dim_row A\<close> by blast
  have bcar: "B \<in> carrier_mat (dim_row A) (dim_col A)" 
      using real_diag_decompD(1)
      by (metis \<open>A \<in> carrier_mat (dim_row A) (dim_row A)\<close> carrier_matD(2) r 
          unitary_diag_carrier(1))
    have ucar: "U \<in> carrier_mat (dim_row A) (dim_col A)" 
      using real_diag_decompD(1)
      by (metis \<open>A \<in> carrier_mat (dim_row A) (dim_row A)\<close> carrier_matD(2) r 
          unitary_diag_carrier(2))
    have unit: "unitary U"
      by (meson r real_diag_decompD(1) unitary_diagD(3))
  show ?case
  proof (cases "Al = []")
    case True
    hence "diag_block_mat (Cons A Al) = A" by auto
    moreover have "diag_block_mat [B] = B" by auto
    moreover have "diag_block_mat [U] = U" by auto
    moreover have "unitary U"
      using r real_diag_decompD(1) unitary_diagD(3) by blast
    ultimately have 
      "real_diag_decomp (diag_block_mat (Cons A Al)) 
        (diag_block_mat [B]) (diag_block_mat [U])"
      using \<open>real_diag_decomp A B U\<close> by auto
    moreover have "(\<forall>i<length (A # Al).
      [U]!i \<in> carrier_mat (dim_row ((A # Al) ! i)) (dim_col ((A # Al) ! i)) \<and>
      Complex_Matrix.unitary ([U] ! i) \<and> [B] ! i \<in> 
      carrier_mat (dim_row ((A # Al) ! i)) (dim_col ((A # Al) ! i)))" using True
      by (simp add: bcar ucar unit)
    ultimately show ?thesis 
      using True \<open>Complex_Matrix.unitary U\<close> bcar  less_one ucar
      by (metis length_list_update list_update_code(2))
  next
    case False
    have "list_all (\<lambda>A. 0 < dim_row A \<and> hermitian A) Al" using Cons by auto
    hence "\<exists>Bl Ul. length Ul = length Al \<and>
       (\<forall>i<length Al.
           Ul ! i \<in> carrier_mat (dim_row (Al ! i)) (dim_col (Al ! i)) \<and> 
           unitary (Ul!i) \<and> 
            Bl ! i \<in> carrier_mat (dim_row (Al ! i)) (dim_col (Al ! i))) \<and>
       real_diag_decomp (diag_block_mat Al) (diag_block_mat Bl) (diag_block_mat Ul)"
      using Cons False by simp 
    from this obtain Bl Ul where "length Ul  =length Al" and  
      rl: "real_diag_decomp (diag_block_mat Al) 
      (diag_block_mat Bl) (diag_block_mat Ul)"
      and "\<forall>i<length Al.
           Ul ! i \<in> carrier_mat (dim_row (Al ! i)) (dim_col (Al ! i)) \<and> 
            unitary (Ul!i) \<and> 
            Bl ! i \<in> carrier_mat (dim_row (Al ! i)) (dim_col (Al ! i))"
      by auto note bu = this
    have "real_diag_decomp (diag_block_mat (A # Al)) 
      (diag_block_mat (B # Bl)) (diag_block_mat (U # Ul))" 
      using four_block_real_diag_decomp[OF r rl] 
      by (metis \<open>A \<in> carrier_mat (dim_row A) (dim_row A)\<close> 
          carrier_matD(2) diag_block_mat.simps(2) hermitian_square 
          real_diag_decomp_hermitian rl)
    moreover have "length (U#Ul) = length (A#Al)" using bu by simp
    moreover have "\<forall>i<length (A # Al).
           (U#Ul) ! i \<in> carrier_mat (dim_row ((A # Al) ! i)) (dim_col ((A # Al) ! i)) \<and>
           unitary ((U#Ul)!i) \<and>
           (B#Bl) ! i \<in> carrier_mat (dim_row ((A # Al) ! i)) (dim_col ((A # Al) ! i))" 
    proof (intro allI impI)
      fix i
      assume "i < length (A#Al)"
      show "(U # Ul) ! i \<in> carrier_mat (dim_row ((A # Al) ! i)) 
        (dim_col ((A # Al) ! i)) \<and> unitary ((U#Ul)!i) \<and>
        (B # Bl) ! i \<in> carrier_mat (dim_row ((A # Al) ! i)) 
        (dim_col ((A # Al) ! i))"
      proof (cases "i = 0")
        case True
        then show ?thesis by (simp add: bcar ucar unit) 
      next
        case False
        hence "\<exists>j. i = Suc j" by (simp add: not0_implies_Suc)
        from this obtain j where j: "i = Suc j" by auto
        hence "j < length Al" using \<open>i < length (A#Al)\<close> by simp
        have "(A#Al)!i = Al!j" "(U # Ul) ! i = Ul!j" "(B#Bl) ! i = Bl!j" 
          using j by auto
        then show ?thesis using Cons \<open>j < length Al\<close> bu(3) by presburger
      qed
    qed
    ultimately show ?thesis by blast
  qed
qed

lemma diag_block_mat_adjoint:
  shows "Complex_Matrix.adjoint (diag_block_mat Al) =
    diag_block_mat (map Complex_Matrix.adjoint Al)"
proof (induct Al)
  case Nil
  then show ?case using zero_adjoint by simp
next
  case (Cons a Al)
  have "Complex_Matrix.adjoint (diag_block_mat (a # Al)) =
    Complex_Matrix.adjoint (four_block_diag a (diag_block_mat Al))" 
    using diag_block_mat.simps(2)[of a] unfolding Let_def by simp
  also have "... = four_block_diag (Complex_Matrix.adjoint a)
    (Complex_Matrix.adjoint (diag_block_mat Al))" 
    using four_block_diag_adjoint[of a] by simp
  also have "... = four_block_diag (Complex_Matrix.adjoint a)
    (diag_block_mat (map Complex_Matrix.adjoint Al))" using Cons by simp
  also have "... = diag_block_mat (map Complex_Matrix.adjoint (a#Al))" 
    using diag_block_mat.simps(2) unfolding Let_def 
    by (metis (no_types) diag_block_mat.simps(2) list.map(2))
  finally show ?case .
qed

lemma diag_block_mat_mat_conj:
  assumes "length Al = length Bl"
  and "\<forall>i < length Al. dim_col (Al!i) = dim_row (Bl!i)"
  and "\<forall>i < length Al. dim_row (Bl!i) = dim_col (Bl!i)"
  shows "mat_conj (diag_block_mat Al) (diag_block_mat Bl) =
    diag_block_mat (map2 mat_conj Al Bl)"
proof -
  have "mat_conj (diag_block_mat Al) (diag_block_mat Bl) =
    diag_block_mat Al * diag_block_mat Bl * 
    diag_block_mat (map Complex_Matrix.adjoint Al)" 
    using diag_block_mat_adjoint[of Al] unfolding mat_conj_def by simp
  also have "... = diag_block_mat (map2 (*) Al Bl) * 
    diag_block_mat (map Complex_Matrix.adjoint Al)" 
    using diag_block_mat_mult[OF assms(1) assms(2)] by simp
  also have "... = diag_block_mat (map2 (*) (map2 (*) Al Bl)
    (map Complex_Matrix.adjoint Al))"
  proof (rule diag_block_mat_mult)
    show "length (map2 (*) Al Bl) = length (map Complex_Matrix.adjoint Al)"
      by (simp add: assms(1))
    show "\<forall>i<length (map2 (*) Al Bl). dim_col (map2 (*) Al Bl ! i) = 
      dim_row (map Complex_Matrix.adjoint Al ! i)"
      by (simp add: assms(2) assms(3))
  qed
  also have "... = diag_block_mat (map2 mat_conj Al Bl)" 
    using map2_mat_conj_exp[OF assms(1)] by simp
  finally show ?thesis .
qed

lemma diag_block_mat_commute:
  assumes "length Al = length Bl"
  and "\<forall>i < length Al. Al!i * (Bl!i) = Bl!i * (Al!i)"
  and "\<forall>i<length Al. dim_col (Al ! i) = dim_row (Bl ! i)"
  and "\<forall>i<length Al. dim_col (Bl ! i) = dim_row (Al ! i)"
shows "diag_block_mat Al * (diag_block_mat Bl) = 
  diag_block_mat Bl * (diag_block_mat Al)"
proof -
  have "diag_block_mat Al * diag_block_mat Bl =
    diag_block_mat (map2 (*) Al Bl)" 
    using diag_block_mat_mult[of Al Bl] assms by simp
  also have "... = diag_block_mat (map2 (*) Bl Al)" 
  proof -
    have "map2 (*) Al Bl = map2 (*) Bl Al"     
      by (rule map2_commute, auto simp add: assms)
    thus ?thesis by simp
  qed
  also have "... = diag_block_mat Bl * (diag_block_mat Al)"
    using diag_block_mat_mult[of Bl Al] assms by simp
  finally show ?thesis .
qed

lemma diag_block_mat_length_1:
  assumes "length Al = 1"
  shows "diag_block_mat Al = Al!0" 
proof -
  have "Al = [Al!0]" using assms
    by (metis One_nat_def length_0_conv length_Suc_conv nth_Cons_0)
  thus ?thesis
    by (metis diag_block_mat_singleton) 
qed

lemma diag_block_mat_cong_hd:
  assumes "0 < length Al"
  and "length Al = length Bl"
  and "dim_row (hd Al) = dim_row (hd Bl)"
  and "dim_col (hd Al) = dim_col (hd Bl)"
  and "diag_block_mat Al = diag_block_mat Bl"
shows "hd Al = hd Bl" 
proof -
  have "Al \<noteq> []" using assms by blast
  hence "Al = hd Al#(tl Al)" by simp
  hence da:"diag_block_mat Al = 
    four_block_diag (hd Al) (diag_block_mat (tl Al))"
    using diag_block_mat.simps(2)[of "hd Al" "tl Al"] unfolding Let_def by simp
  have  "Bl \<noteq> []" using assms by simp
  hence "Bl = hd Bl#(tl Bl)" by simp
  hence "diag_block_mat Bl = four_block_diag (hd Bl) (diag_block_mat (tl Bl))"
    using diag_block_mat.simps(2)[of "hd Bl" "tl Bl"] unfolding Let_def by simp
  hence "four_block_diag (hd Al) (diag_block_mat (tl Al)) = 
    four_block_diag (hd Bl) (diag_block_mat (tl Bl))" using da assms by simp
  thus ?thesis using four_block_diag_cong_comp assms by metis
qed

lemma diag_block_mat_cong_tl:
  assumes "0 < length Al"
  and "length Al = length Bl"
  and "dim_row (hd Al) = dim_row (hd Bl)"
  and "dim_col (hd Al) = dim_col (hd Bl)"
  and "diag_block_mat Al = diag_block_mat Bl"
shows "diag_block_mat (tl Al) = diag_block_mat (tl Bl)" 
proof -
  have "Al \<noteq> []" using assms by blast
  hence "Al = hd Al#(tl Al)" by simp
  hence da:"diag_block_mat Al = 
    four_block_diag (hd Al) (diag_block_mat (tl Al))"
    using diag_block_mat.simps(2)[of "hd Al" "tl Al"] unfolding Let_def by simp
  have  "Bl \<noteq> []" using assms by simp
  hence "Bl = hd Bl#(tl Bl)" by simp
  hence "diag_block_mat Bl = four_block_diag (hd Bl) (diag_block_mat (tl Bl))"
    using diag_block_mat.simps(2)[of "hd Bl" "tl Bl"] unfolding Let_def by simp
  hence "four_block_diag (hd Al) (diag_block_mat (tl Al)) = 
    four_block_diag (hd Bl) (diag_block_mat (tl Bl))" using da assms by simp
  thus ?thesis using four_block_diag_cong_comp' assms by metis
qed

lemma diag_block_mat_cong_comp:
  assumes "length Al = length Bl"
  and "\<forall>i<length Al. dim_row (Al ! i) = dim_row (Bl ! i)"
  and "\<forall>i<length Al. dim_col (Al ! i) = dim_col (Bl ! i)"
  and "diag_block_mat Al = diag_block_mat Bl"
and "j < length Al"
shows "Al!j = Bl!j" using assms
proof (induct Al arbitrary: Bl j)
  case Nil
  then show ?case by simp
next
  case (Cons a Al)
  hence "0 <length Bl" by linarith
  hence "Bl = hd Bl#(tl Bl)" by simp
  then show ?case 
  proof (cases "j = 0")
    case True
    hence "(a#Al)!j = hd(a#Al)" by simp
    have "Bl!j= hd Bl" using \<open>j = 0\<close>
      by (metis \<open>Bl = hd Bl # tl Bl\<close> nth_Cons_0)
    have da: "diag_block_mat (a#Al) = four_block_diag a (diag_block_mat Al)"
      using diag_block_mat.simps(2)[of a Al] unfolding Let_def by simp
    have db: "diag_block_mat (hd Bl#(tl Bl)) = 
      four_block_diag (hd Bl) (diag_block_mat (tl Bl))"
      using diag_block_mat.simps(2)[of "hd Bl" "tl Bl"] 
      unfolding Let_def by simp
    have "hd (a#Al) = hd Bl"
    proof (rule diag_block_mat_cong_hd)
      show "0 < length (a # Al)" by simp
      show "length (a # Al) = length Bl" using Cons by simp
      show "diag_block_mat (a # Al) = diag_block_mat Bl" using Cons by simp
      show "dim_row (hd (a # Al)) = dim_row (hd Bl)"
        by (metis True \<open>0 < length Bl\<close> \<open>Bl ! j = hd Bl\<close> list.sel(1) Cons(2) 
            Cons(3) nth_Cons_0)
      show "dim_col (hd (a # Al)) = dim_col (hd Bl)"
        by (metis True \<open>0 < length Bl\<close> \<open>Bl ! j = hd Bl\<close> list.sel(1) Cons(2) 
            Cons(4) nth_Cons_0)
    qed
    thus "(a # Al) ! j = Bl ! j" using \<open>j = 0\<close> \<open>Bl ! j = hd Bl\<close> by fastforce
  next
    case False
    hence "\<exists>k. j = Suc k" by (simp add: not0_implies_Suc) 
    from this obtain k where "j = Suc k" by auto
    hence "(a#Al)!j = Al!k" by simp
    have "Bl!j = (tl Bl)!k" using \<open>j = Suc k\<close> \<open>Bl = hd Bl#(tl Bl)\<close>
      by (metis nth_Cons_Suc)
    have "Al!k = (tl Bl)!k"
    proof (rule Cons(1))
      show "length Al = length (tl Bl)" using Cons
        by (metis diff_Suc_1 length_Cons length_tl)
      show "k < length Al"
        by (metis Cons.prems(5) Suc_less_SucD \<open>j = Suc k\<close> length_Cons) 
      show "\<forall>i<length Al. dim_row (Al ! i) = dim_row (tl Bl ! i)"
        by (metis Suc_less_eq \<open>length Al = length (tl Bl)\<close> length_Cons 
            local.Cons(3) nth_Cons_Suc nth_tl)
      show "\<forall>i<length Al. dim_col (Al ! i) = dim_col (tl Bl ! i)"
        by (metis Suc_mono \<open>Bl = hd Bl # tl Bl\<close> length_Cons local.Cons(4) 
            nth_Cons_Suc)
      have "diag_block_mat (tl (a#Al)) = diag_block_mat (tl Bl)"
      proof (rule diag_block_mat_cong_tl)
        show "length (a # Al) = length Bl" using Cons by simp
        show "dim_row (hd (a # Al)) = dim_row (hd Bl)"
          by (metis \<open>Bl = hd Bl # tl Bl\<close> length_Cons list.sel(1) local.Cons(3) 
              nth_Cons_0 zero_less_Suc)
        show "dim_col (hd (a # Al)) = dim_col (hd Bl)"
          by (metis \<open>0 < length Bl\<close> \<open>Bl = hd Bl # tl Bl\<close> list.sel(1) 
              local.Cons(2) local.Cons(4) nth_Cons_0)
        show "diag_block_mat (a # Al) = diag_block_mat Bl" using Cons by simp
        show "0 < length (a#Al)" by simp
      qed
      thus "diag_block_mat Al = diag_block_mat (tl Bl)" by simp
    qed
    then show ?thesis
      by (simp add: \<open>(a # Al) ! j = Al ! k\<close> \<open>Bl ! j = tl Bl ! k\<close>) 
  qed
qed

lemma diag_block_mat_commute_comp:
  assumes "length Al = length Bl"
  and "\<forall>i<length Al. dim_row (Al ! i) = dim_col (Al ! i)"
  and "\<forall>i<length Al. dim_row (Al ! i) = dim_row (Bl ! i)"
  and "\<forall>i<length Al. dim_col (Al ! i) = dim_col (Bl ! i)"
  and "diag_block_mat Al * (diag_block_mat Bl) = 
    diag_block_mat Bl * (diag_block_mat Al)"
  and "i < length Al"
shows "Al!i * Bl!i = Bl!i * Al!i" 
proof -
  have "diag_block_mat (map2 (*) Al Bl)=diag_block_mat Al * diag_block_mat Bl"
    using diag_block_mat_mult[of Al] assms by simp
  also have "... = diag_block_mat Bl * diag_block_mat Al" using assms by simp
  also have "... = diag_block_mat (map2 (*) Bl Al)" 
    using diag_block_mat_mult[of Bl] assms by simp
  finally have eq: "diag_block_mat (map2 (*) Al Bl) = 
    diag_block_mat (map2 (*) Bl Al)" .
  have "(map2 (*) Al Bl)!i = (map2 (*) Bl Al)!i" 
  proof (rule diag_block_mat_cong_comp) 
    show "length (map2 (*) Al Bl) = length (map2 (*) Bl Al)" 
      using map2_length assms by metis
    show "i < length (map2 (*) Al Bl)" using map2_length assms by metis 
    show "diag_block_mat (map2 (*) Al Bl) = diag_block_mat (map2 (*) Bl Al)"
      using eq .
    show "\<forall>i<length (map2 (*) Al Bl). dim_row (map2 (*) Al Bl ! i) = 
      dim_row (map2 (*) Bl Al ! i)"
      by (simp add: assms(3))
    show "\<forall>i<length (map2 (*) Al Bl). dim_col (map2 (*) Al Bl ! i) = 
      dim_col (map2 (*) Bl Al ! i)"
      by (simp add: assms(4))
  qed
  moreover have "(map2 (*) Al Bl)!i = Al!i * Bl!i" using assms by simp
  moreover have "(map2 (*) Bl Al)!i = Bl!i * Al!i" using assms by simp
  ultimately show ?thesis by simp
qed

lemma diag_block_mat_dim_row_cong:
  assumes "length Ul = length Bl"
  and "\<forall>i < length Bl. dim_row (Bl!i) = dim_row (Ul!i)"
  shows "dim_row (diag_block_mat Ul) = dim_row (diag_block_mat Bl)"
proof -
  have "dim_row (diag_block_mat Ul) = sum_list (map dim_row Ul)" 
    by (simp add: dim_diag_block_mat(1))
  also have "... = sum_list (map dim_row Bl)" using assms 
    by (metis nth_map_conv)
  also have "... = dim_row (diag_block_mat Bl)"
    by (simp add: dim_diag_block_mat(1))
  finally show ?thesis .
qed

lemma diag_block_mat_dim_col_cong:
  assumes "length Ul = length Bl"
  and "\<forall>i < length Bl. dim_col (Bl!i) = dim_col (Ul!i)"
  shows "dim_col (diag_block_mat Ul) = dim_col (diag_block_mat Bl)"
proof -
  have "dim_col (diag_block_mat Ul) = sum_list (map dim_col Ul)" 
    by (simp add: dim_diag_block_mat(2))
  also have "... = sum_list (map dim_col Bl)" using assms 
    by (metis nth_map_conv)
  also have "... = dim_col (diag_block_mat Bl)"
    by (simp add: dim_diag_block_mat(2))
  finally show ?thesis .
qed

lemma diag_block_mat_dim_row_col_eq:
  assumes "\<forall>i < length Al. dim_row (Al!i) = dim_col (Al!i)"
  shows "dim_row (diag_block_mat Al) = dim_col (diag_block_mat Al)"
proof -
  have "dim_row (diag_block_mat Al) = sum_list (map dim_row Al)"
    by (simp add:dim_diag_block_mat(1))
  also have "... = sum_list (map dim_col Al)" using assms
    by (metis nth_map_conv)
  also have "... = dim_col (diag_block_mat Al)"
    by (simp add:dim_diag_block_mat(2))
  finally show ?thesis .
qed

section \<open>Block matrix decomposition\<close>

subsection \<open>Subdiagonal extraction\<close>
text \<open>\verb+extract_subdiags+ returns a list of diagonal sub-blocks, the sizes of which are
specified by the list of integers provided as parameters.\<close>

fun extract_subdiags where
  "extract_subdiags B [] = []"
| "extract_subdiags B (x#xs) = 
    (let (B1, B2, B3, B4) = (split_block B x x) in 
      B1 # (extract_subdiags B4 xs))"

lemma extract_subdiags_not_emp:
  fixes x::nat and l::"nat list"
  assumes "(B1, B2, B3, B4) = (split_block B x x)"
  shows "hd (extract_subdiags B (x#l)) = B1" 
    "tl (extract_subdiags B (x#l)) = extract_subdiags B4 l" 
proof -
  show "hd (extract_subdiags B (x#l)) = B1" unfolding  Let_def 
    by (metis (no_types) assms extract_subdiags.simps(2) list.sel(1) split_conv) 
  show "tl (extract_subdiags B (x # l)) = extract_subdiags B4 l" 
    using assms extract_subdiags.simps(2) unfolding Let_def
    by (metis (no_types, lifting) list.sel(3) split_conv)
qed

lemma extract_subdiags_neq_Nil:
  shows "extract_subdiags B (a#l) \<noteq> []" 
  using extract_subdiags.simps(2)[of B] 
  unfolding Let_def split_block_def by simp

lemma extract_subdiags_length:
  shows "length (extract_subdiags B l) = length l"
proof (induct l arbitrary: B)
  case Nil
  then show ?case by simp
next
  case (Cons a l)
  define B1 where "B1 = fst (split_block B a a)"
  define B2 where "B2 = fst (snd (split_block B a a))"
  define B3 where "B3 = fst (snd (snd (split_block B a a)))"
  define B4 where "B4 = snd (snd (snd (split_block B a a)))"
  have sp: "split_block B a a = (B1, B2, B3, B4)" using fst_conv snd_conv 
    unfolding B1_def B2_def B3_def B4_def by simp
  then show ?case using Cons extract_subdiags.simps(2)[of B a l] 
    unfolding Let_def by simp 
qed

lemma extract_subdiags_carrier:
  assumes "i < length l"
  shows "(extract_subdiags B l)!i \<in> carrier_mat (l!i) (l!i)" using assms
proof (induct i arbitrary: l B)  
  case 0
  define B1 where "B1 = fst (split_block B (hd l) (hd l))"
  define B2 where "B2 = fst (snd (split_block B (hd l) (hd l)))"
  define B3 where "B3 = fst (snd (snd (split_block B (hd l) (hd l))))"
  define B4 where "B4 = snd (snd (snd (split_block B (hd l) (hd l))))"
  have sp: "split_block B (hd l) (hd l) = (B1, B2, B3, B4)" using fst_conv snd_conv 
    unfolding B1_def B2_def B3_def B4_def by simp
  have "l = hd l # (tl l)" using 0 by auto
  have "(extract_subdiags B l)!0 = B1" 
    using extract_subdiags.simps(2)[of B "hd l" "tl l"] \<open>l = hd l # tl l\<close> sp
    unfolding Let_def by auto
  also have "... \<in> carrier_mat (hd l) (hd l)" 
    unfolding B1_def split_block_def Let_def by simp
  finally show ?case
    by (metis \<open>l = hd l # tl l\<close> hd_conv_nth list.sel(2) not_Cons_self) 
next
  case (Suc i)  
  define B1 where "B1 = fst (split_block B (hd l) (hd l))"
  define B2 where "B2 = fst (snd (split_block B (hd l) (hd l)))"
  define B3 where "B3 = fst (snd (snd (split_block B (hd l) (hd l))))"
  define B4 where "B4 = snd (snd (snd (split_block B (hd l) (hd l))))"
  have sp: "split_block B (hd l) (hd l) = (B1, B2, B3, B4)" using fst_conv snd_conv 
    unfolding B1_def B2_def B3_def B4_def by simp
  have "l = hd l # (tl l)" using Suc
    by (metis Cons_nth_drop_Suc drop_Nil list.exhaust_sel not_Cons_self)
  hence "l! Suc i = (tl l)!i" by (metis nth_Cons_Suc)
  have "tl (extract_subdiags B l) = extract_subdiags B4 (tl l)" 
    using extract_subdiags_not_emp(2)[OF sp[symmetric]] \<open>l = hd l # (tl l)\<close> 
    by metis
  hence "extract_subdiags B l = B1 # extract_subdiags B4 (tl l)" 
    using extract_subdiags_not_emp(1)[OF sp[symmetric]]
    by (metis \<open>l = hd l # tl l\<close> extract_subdiags_neq_Nil list.exhaust_sel)
  hence "extract_subdiags B l ! Suc i = (extract_subdiags B4 (tl l))!i" 
    using nth_Cons_Suc by simp
  also have "... \<in> carrier_mat (tl l!i) (tl l!i)" using Suc
    by (metis \<open>l = hd l # tl l\<close> length_Cons not_less_eq)
  also have "... = carrier_mat (l!Suc i) (l! Suc i)" 
    using nth_Cons_Suc[of "hd l" "tl l" i] \<open>l = hd l # tl l\<close> by simp
  finally show ?case .
qed

lemma extract_subdiags_diagonal:
  assumes "diagonal_mat B"
  and "B \<in> carrier_mat n n"
  and "l \<noteq> []"
  and "sum_list l \<le> n"
  and "i < length l"
shows "diagonal_mat ((extract_subdiags B l)!i)" using assms
proof (induct i arbitrary: l B n)
  case 0
  define a where "a = hd l"
  have "l = a#(tl l)" unfolding a_def using 0 by simp
  have "a \<le> n" using 0 unfolding a_def
    by (metis a_def dual_order.strict_trans2 elem_le_sum_list 
        hd_conv_nth less_le_not_le nat_le_linear)
  define B1 where "B1 = fst (split_block B a a)"
  define B2 where "B2 = fst (snd (split_block B a a))"
  define B3 where "B3 = fst (snd (snd (split_block B a a)))"
  define B4 where "B4 = snd (snd (snd (split_block B a a)))"
  have sp: "split_block B a a = (B1, B2, B3, B4)" using fst_conv snd_conv 
    unfolding B1_def B2_def B3_def B4_def by simp
  hence "extract_subdiags B l!0 = B1" unfolding a_def 
    using hd_conv_nth 0 
    by (metis \<open>l = a # tl l\<close> sp extract_subdiags_neq_Nil 
        extract_subdiags_not_emp(1))
  moreover have "diagonal_mat B1" using sp split_block_diagonal assms \<open>a \<le> n\<close> 0
    by blast
  ultimately show ?case by simp
next
  case (Suc i)
  show ?case
  proof (cases "length l = 1")
    case True
    hence "Suc i = 0" using Suc by presburger
    then show ?thesis by simp
  next
    case False
    define a where "a = hd l"
    have "l = a#(tl l)" unfolding a_def using Suc by simp
    have "a \<le> n" using Suc unfolding a_def
      by (metis dual_order.trans elem_le_sum_list hd_conv_nth 
          length_greater_0_conv)
    define B1 where "B1 = fst (split_block B a a)"
    define B2 where "B2 = fst (snd (split_block B a a))"
    define B3 where "B3 = fst (snd (snd (split_block B a a)))"
    define B4 where "B4 = snd (snd (snd (split_block B a a)))"
    have sp: "split_block B a a = (B1, B2, B3, B4)" using fst_conv snd_conv 
      unfolding B1_def B2_def B3_def B4_def by simp
    have "extract_subdiags B l ! Suc i = 
      extract_subdiags B4 (tl l)! i"  using sp
      by (metis Suc(6) Suc_less_SucD \<open>l = a # tl l\<close> length_Cons nth_tl 
          extract_subdiags_length extract_subdiags_not_emp(2))
    moreover have "diagonal_mat (extract_subdiags B4 (tl l)! i)"
    proof (rule Suc(1))
      show "tl l \<noteq> []" using False Suc
        by (metis \<open>l = a # tl l\<close> length_Cons list.size(3) numeral_nat(7)) 
      show "i < length (tl l)" using False Suc
        by (metis Suc_lessD \<open>l = a # tl l\<close> le_neq_implies_less length_Cons 
            less_Suc_eq_le)
      show "B4 \<in> carrier_mat (n-a) (n-a)" 
        using sp split_block_diag_carrier(2) Suc(3) \<open>a \<le> n\<close> by blast 
      show "diagonal_mat B4" 
        using split_block_diagonal sp Suc \<open>a \<le> n\<close> by blast
      show "sum_list (tl l) \<le> n - a" using Suc(5) \<open>a \<le> n\<close> sum_list_tl_leq
        by (simp add: Suc(4) a_def)
    qed
    ultimately show ?thesis by simp
  qed
qed

lemma extract_subdiags_diag_elem:
  fixes B::"complex Matrix.mat"
  assumes "B\<in> carrier_mat n n"
  and "0 < n"
  and "l \<noteq> []"
  and "i < length l"
  and "j< l!i"
  and "sum_list l \<le> n"
  and "\<forall>j < length l. 0 < l!j"
  shows "extract_subdiags B l!i $$ (j,j) = 
    diag_mat B!(n_sum i l + j)" using assms
proof (induct i arbitrary: l B n)
  case 0
  define a where "a = hd l"
  have "l = a#(tl l)" unfolding a_def using 0 by simp
  have "a \<le> n" using 0 unfolding a_def
    by (metis a_def dual_order.strict_trans2 elem_le_sum_list 
        hd_conv_nth less_le_not_le nat_le_linear)
  define B1 where "B1 = fst (split_block B a a)"
  define B2 where "B2 = fst (snd (split_block B a a))"
  define B3 where "B3 = fst (snd (snd (split_block B a a)))"
  define B4 where "B4 = snd (snd (snd (split_block B a a)))"
  have sp: "split_block B a a = (B1, B2, B3, B4)" using fst_conv snd_conv 
    unfolding B1_def B2_def B3_def B4_def by simp
  hence "extract_subdiags B l!0 = B1" 
    using  hd_conv_nth unfolding Let_def 
    by (metis \<open>l = a # tl l\<close> extract_subdiags_neq_Nil 
        extract_subdiags_not_emp(1))
  hence "extract_subdiags B l!0 $$ (j,j) = B$$ (j,j)" 
    using sp 0 unfolding split_block_def
    by (metis (no_types, lifting) carrier_matD(2) dim_col_mat(1) 
        index_mat(1) prod.sel(1) extract_subdiags_carrier)
  also have "... = diag_mat B!j" 
    using 0 \<open>a \<le> n\<close> hd_conv_nth unfolding diag_mat_def a_def
    by fastforce
  also have "... = diag_mat B!(n_sum 0 l + j)" by simp
  finally show ?case .
next
  case (Suc i)
  show ?case
  proof (cases "length l = 1")
    case True
    hence "Suc i < 0" using Suc by simp
    then show ?thesis by simp
  next
    case False
    hence "1 < length l" using Suc by presburger
    define a where "a = hd l"
    have "l = a#(tl l)" unfolding a_def using Suc by simp
    have "a \<le> n" using Suc unfolding a_def
      by (metis add_le_same_cancel1 elem_le_sum_list hd_conv_nth 
          le_add2 le_trans verit_comp_simplify1(3))
    define B1 where "B1 = fst (split_block B a a)"
    define B2 where "B2 = fst (snd (split_block B a a))"
    define B3 where "B3 = fst (snd (snd (split_block B a a)))"
    define B4 where "B4 = snd (snd (snd (split_block B a a)))"
    have sp: "split_block B a a = (B1, B2, B3, B4)" using fst_conv snd_conv 
      unfolding B1_def B2_def B3_def B4_def by simp
    have "B4 \<in> carrier_mat (n-a) (n-a)" 
      using sp split_block_diag_carrier(2) Suc \<open>a \<le> n\<close> by blast
    have "B1 \<in> carrier_mat a a" 
      using sp split_block_diag_carrier(1) Suc \<open>a \<le> n\<close> by blast
    have "n_sum (Suc i) l + j < n_sum (Suc (Suc i)) l" 
      using Suc  n_sum_last_lt by metis
    hence "a + n_sum i (tl l) + j < n_sum (Suc (Suc i)) l" 
      unfolding a_def by simp
    also have "... \<le> sum_list l"
    proof (rule n_sum_sum_list)
      show "\<forall>j<length l. 0 \<le> l ! j" using Suc by simp
      show "Suc (Suc i) \<le> length l" using Suc by simp
    qed
    also have "... \<le> n" using Suc by simp
    finally have "a + n_sum i (tl l) + j < n" .
    hence "n_sum i (tl l) +j < n - a" by simp
    have "extract_subdiags B l!(Suc i) = 
      extract_subdiags B4 (tl l)!i" 
      using sp \<open>l = a#(tl l)\<close> unfolding  Let_def 
      by (metis list.exhaust_sel nth_Cons_Suc extract_subdiags_neq_Nil 
          extract_subdiags_not_emp(2))
    hence "extract_subdiags B l!(Suc i) $$(j,j) = 
      extract_subdiags B4 (tl l)!i $$(j,j)" by simp
    also have "... = diag_mat B4!(n_sum i (tl l) + j)" 
    proof (rule Suc(1))
      show "tl l \<noteq> []" using False Suc
        by (metis \<open>l = a # tl l\<close> length_Cons list.size(3) numeral_nat(7)) 
      show "i < length (tl l)" using False Suc
        by (metis Suc_lessD \<open>l = a # tl l\<close> le_neq_implies_less length_Cons 
            less_Suc_eq_le)
      show "B4 \<in> carrier_mat (n-a) (n-a)" 
        using \<open>B4 \<in> carrier_mat (n-a) (n-a)\<close> .
      show "sum_list (tl l) \<le> n - a" using Suc(5) \<open>a \<le> n\<close> sum_list_tl_leq
        by (simp add: Suc a_def)
      show "0 < n - a"
        by (metis Suc.prems(4) Suc.prems(7) \<open>i < length (tl l)\<close> 
            \<open>l = a # tl l\<close> \<open>sum_list (tl l) \<le> n - a\<close> bot_nat_0.extremum_uniqueI
            elem_le_sum_list gr_zeroI nth_Cons_Suc)
      show "\<forall>j<length (tl l). 0 < tl l ! j"
        by (simp add: Suc(8) nth_tl)
      show "j < tl l ! i"
        by (metis Suc(6) \<open>i < length (tl l)\<close> nth_tl)
    qed
    also have "... = B4$$(n_sum i (tl l)+j, n_sum i (tl l)+j)" 
    proof -
      have "n_sum i (tl l) +j < n - a" using \<open>n_sum i (tl l) +j < n - a\<close> .
      thus ?thesis 
        using \<open>B4 \<in> carrier_mat (n-a) (n-a)\<close>  
        unfolding diag_mat_def by simp
    qed
    also have "... = B$$(n_sum i (tl l) + j + a, n_sum i (tl l) + j + a)" 
      using sp \<open>B1 \<in> carrier_mat a a\<close> \<open>n_sum i (tl l) +j < n - a\<close> 
        \<open>B4 \<in> carrier_mat (n-a) (n-a)\<close> carrier_matD(2) dim_col_mat(1) Suc
        index_mat(1) prod.sel 
      unfolding split_block_def Let_def by force
    also have "... = diag_mat B!(n_sum i (tl l) + j + a)" 
    proof -
      have "n_sum i (tl l) + j + a < n" using \<open>n_sum i (tl l) +j < n - a\<close> 
        by simp
      thus ?thesis using Suc unfolding diag_mat_def by simp
    qed
    also have "... = diag_mat B ! (n_sum (Suc i) l + j)"
    proof -
      have "n_sum i (tl l) + a = n_sum (Suc i) l" unfolding a_def by simp
      thus ?thesis
        by (simp add: add.commute add.left_commute)
    qed
    finally show ?thesis .
  qed
qed

lemma hermitian_extract_subdiags:
  assumes "hermitian A"
  and "sum_list l \<le> dim_row A"
  and "list_all (\<lambda>a. 0 < a) l"
  shows "list_all (\<lambda>B. 0 < dim_row B \<and> hermitian B) (extract_subdiags A l)"
  using assms
proof (induct l arbitrary: A)
  case Nil
  then show ?case by simp
next
  case (Cons a l)
  define es where "es = extract_subdiags A (a#l)"
  define B1 where "B1 = fst (split_block A a a)"
  define B2 where "B2 = fst (snd (split_block A a a))"
  define B3 where "B3 = fst (snd (snd (split_block A a a)))"
  define B4 where "B4 = snd (snd (snd (split_block A a a)))"
  have sp: "split_block A a a = (B1, B2, B3, B4)" using fst_conv snd_conv 
    unfolding B1_def B2_def B3_def B4_def by simp
  have "0 < a" using Cons by simp
  have "es \<noteq> []" using extract_subdiags_neq_Nil[of A] 
    unfolding es_def by simp
  hence "es = hd es # (tl es)"  by simp 
  have "hd es = B1" unfolding es_def 
    using extract_subdiags_not_emp(1)[OF sp[symmetric]] by simp
  have "dim_row B1 = a" unfolding B1_def split_block_def Let_def by simp
  have "tl es = extract_subdiags B4 l" unfolding es_def
    using extract_subdiags_not_emp(2)[OF sp[symmetric]] by simp
  have "list_all (\<lambda>B. 0 < dim_row B \<and> hermitian B) (hd es # (tl es))"
  proof (rule list_all_simps(1)[THEN iffD2], intro conjI)
    show "hermitian (hd es)" 
    proof (rule split_block_hermitian_1)
      show "hermitian A" using Cons by simp
      show "(hd es, B2, B3, B4) = split_block A a a" using sp \<open>hd es = B1\<close> 
        by simp
      show "a \<le> dim_row A" using Cons by simp
    qed
    have "list_all (\<lambda>B. 0 < dim_row B \<and> hermitian B) (extract_subdiags B4 l)" 
    proof (rule Cons(1))
      show "hermitian B4" 
      proof (rule split_block_hermitian_4)
        show "hermitian A" using Cons by simp
        show "a \<le> dim_row A" using Cons by simp
        show "(B1, B2, B3, B4) = split_block A a a" using sp by simp
      qed
      show "sum_list l \<le> dim_row B4" using Cons sp 
        unfolding split_block_def Let_def by force
      show "list_all ((<) 0) l" using Cons(4) by auto
    qed
    thus "list_all (\<lambda>B. 0 < dim_row B \<and> hermitian B) (tl es)" 
      using \<open>tl es = extract_subdiags B4 l\<close> by simp
    show "0 < dim_row (hd es)" 
      using \<open>hd es = B1\<close> \<open>0 < a\<close> \<open>dim_row B1 = a\<close> by simp
  qed
  thus ?case using \<open>es = hd es # (tl es)\<close> unfolding es_def by metis
qed

subsection \<open>Predicates on diagonal block matrices\<close>
text \<open>The predicate \verb+diag_compat+ ensures that the provided matrix, when decomposed
according to the list of integers provided as an input, is indeed a diagonal block matrix.\<close>

fun diag_compat where
  "diag_compat B [] = (dim_row B = 0 \<and> dim_col B = 0)"
| "diag_compat B (x#xs) = 
    (x \<le> dim_row B \<and>
    (let n = dim_row B; (B1, B2, B3, B4) = (split_block B x x) in 
      B2 = (0\<^sub>m x (n - x)) \<and> B3 = (0\<^sub>m (n - x) x) \<and> diag_compat B4 xs))"

text \<open>When this is the case, the decomposition of a matrix leaves it unchanged.\<close>

lemma diag_compat_extract_subdiag:
  assumes "B\<in> carrier_mat n n"
  and "diag_compat B l"
  shows "B = diag_block_mat (extract_subdiags B l)" using assms
proof (induct l arbitrary:B n)
  case Nil
  have "extract_subdiags B Nil = []" by simp
  have "B = 0\<^sub>m 0 0"
  proof (rule eq_matI, auto simp add: assms)
    show "dim_row B = 0" using Nil by simp
    show "dim_col B = 0" using Nil by simp
  qed
  then show ?case using diag_block_mat_singleton[of B] by simp
next
  case (Cons a l)
  define B1 where "B1 = fst (split_block B a a)"
  define B2 where "B2 = fst (snd (split_block B a a))"
  define B3 where "B3 = fst (snd (snd (split_block B a a)))"
  define B4 where "B4 = snd (snd (snd (split_block B a a)))"
  have sp: "split_block B a a = (B1, B2, B3, B4)" using fst_conv snd_conv 
    unfolding B1_def B2_def B3_def B4_def by simp
  have "a \<le> n" using assms Cons by simp
  have "diag_compat B4 l" using sp Cons by (simp add: Let_def)
  have "B1 \<in> carrier_mat a a" using sp Cons split_block(1)[OF sp]
    by (metis \<open>a \<le> n\<close> carrier_matD(1) carrier_matD(2) le_add_diff_inverse)
  have "B2 \<in> carrier_mat a (n-a)" using sp Cons by (simp add: Let_def)
  have "B3 \<in> carrier_mat (n-a) a" using sp Cons by (simp add: Let_def)
  have "B4 \<in> carrier_mat (n-a) (n-a)" using assms \<open>a \<le> n\<close> Cons 
      split_block(4)[OF sp] by simp
  have b2: "0\<^sub>m (dim_row B1) (dim_col B4) = B2" 
    using diag_compat.simps(2)[THEN iffD1, OF \<open>diag_compat B (a#l)\<close>]     
    \<open>B4 \<in> carrier_mat (n-a) (n-a)\<close> \<open>B1 \<in> carrier_mat a a\<close> 
    \<open>B2 \<in> carrier_mat a (n-a)\<close> sp unfolding Let_def
    Cons(2) by force
  have b3: "0\<^sub>m (dim_row B4) (dim_col B1) = B3" 
    using diag_compat.simps(2)[THEN iffD1, OF \<open>diag_compat B (a#l)\<close>]     
    \<open>B4 \<in> carrier_mat (n-a) (n-a)\<close> \<open>B1 \<in> carrier_mat a a\<close> 
    \<open>B2 \<in> carrier_mat a (n-a)\<close> sp unfolding Let_def
    Cons(2) by force
  have "extract_subdiags B (a#l) = B1 # (extract_subdiags B4 l)" 
    using fst_conv snd_conv extract_subdiags.simps(2)[of B]
    unfolding B1_def B4_def Let_def by (simp add: split_def) 
  also have "diag_block_mat ... = 
    (let
     C = diag_block_mat (extract_subdiags B4 l)
     in four_block_mat B1 (0\<^sub>m (dim_row B1) (dim_col C)) 
        (0\<^sub>m (dim_row C) (dim_col B1)) C)" by simp
  also have "... = four_block_mat B1 (0\<^sub>m (dim_row B1) (dim_col B4)) 
    (0\<^sub>m (dim_row B4) (dim_col B1)) B4" using Cons \<open>diag_compat B4 l\<close> 
    \<open>B4 \<in> carrier_mat (n-a) (n-a)\<close> by (simp add:Let_def)
  also have "... = four_block_mat B1 B2 B3 B4" using b2 b3 by simp
  also have "... = B" using split_block(5)[OF sp, of "n-a" "n-a"] Cons by simp
  finally show ?case by simp
qed

text \<open>Predicate \verb+diag_diff+ holds when the decomposition of the considered
matrix based on the list of integers provided as a parameter, is such that the diagonal
elements of separate components are pairwise distinct.\<close>

fun diag_diff where
  "diag_diff D [] = (dim_row D = 0 \<and> dim_col D = 0)"
| "diag_diff D (x#xs) =
    (x \<le> dim_row D \<and> 
      (let (D1, D2, D3, D4) = (split_block D x x) in 
        (\<forall>i j. i < dim_row D1 \<and> j < dim_row D4 \<longrightarrow> D1$$(i,i) \<noteq> D4 $$ (j,j)) \<and> 
        diag_diff D4 xs))"

lemma diag_diff_hd_diff:
  assumes "diag_diff D (a#xs)"
  and "D\<in> carrier_mat n n"
  and "i < a"
  and "a \<le> j"
  and "j < n"
shows "D$$(i,i) \<noteq> D $$ (j,j)"
proof -
  define D1 where "D1 = fst (split_block D a a)"
  define D2 where "D2 = fst (snd (split_block D a a))"
  define D3 where "D3 = fst (snd (snd (split_block D a a)))"
  define D4 where "D4 = snd (snd (snd (split_block D a a)))"
  have spd: "split_block D a a = (D1, D2, D3, D4)" using fst_conv snd_conv 
    unfolding D1_def D2_def D3_def D4_def by simp
  have c1: "D1 \<in> carrier_mat a a" using split_block(1)[OF spd, of "n-a" "n-a"] 
      assms by simp
  have c4: "D4 \<in> carrier_mat (n-a) (n-a)" using assms  
      split_block(4)[OF spd] by simp
  hence "j - a < dim_row D4" using assms by simp
  have "D $$ (i,i) = D1 $$ (i,i)" using assms spd 
    unfolding split_block_def Let_def by force
  moreover have "D $$ (j,j) = D4 $$ (j-a, j - a)" using assms spd 
    unfolding split_block_def Let_def by force
  moreover have "D1 $$ (i,i) \<noteq> D4 $$ (j-a, j - a)" 
    using assms \<open>j - a < dim_row D4\<close> spd c1 c4 
      diag_diff.simps(2)[THEN iffD1, OF assms(1)] unfolding Let_def by simp
  ultimately show ?thesis by simp
qed

lemma diag_compat_diagonal:
  assumes "B\<in> carrier_mat (dim_row B) (dim_row B)"
  and "diagonal_mat B"
  and "dim_row B = sum_list l"
shows "diag_compat B l" using assms
proof (induct l  arbitrary: B)
  case Nil
  then show ?case by simp
next
  case (Cons a l)
  define B1 where "B1 = fst (split_block B a a)"
  define B2 where "B2 = fst (snd (split_block B a a))"
  define B3 where "B3 = fst (snd (snd (split_block B a a)))"
  define B4 where "B4 = snd (snd (snd (split_block B a a)))"
  have sp: "split_block B a a = (B1, B2, B3, B4)" using fst_conv snd_conv 
    unfolding B1_def B2_def B3_def B4_def by simp
  have "diagonal_mat B1 \<and> diagonal_mat B4"
  proof (rule split_block_diagonal)
    show "split_block B a a = (B1, B2, B3, B4)" using sp .
    show "diagonal_mat B" using Cons by simp
    show "B\<in> carrier_mat (dim_row B) (dim_row B)" using Cons by simp
    show "a \<le> dim_row B" using Cons by simp
  qed
  define n where "n = dim_row B"
  have "diag_compat B4 l" 
  proof (rule Cons(1)) 
    show "diagonal_mat B4" using \<open>diagonal_mat B1 \<and> diagonal_mat B4\<close> by simp
    show "B4 \<in> carrier_mat (dim_row B4) (dim_row B4)" using sp Cons 
      unfolding split_block_def Let_def by auto
    show "dim_row B4 = sum_list l" using Cons sp 
      unfolding split_block_def Let_def by auto
  qed
  have "B2 = 0\<^sub>m a (n - a)"
  proof (rule eq_matI, auto)
    show "dim_row B2 = a" using sp unfolding split_block_def Let_def n_def 
      by auto
    show "dim_col B2 = n-a" using sp Cons 
      unfolding split_block_def Let_def n_def by auto
    fix i j
    assume "i < a" and "j < n-a"
    thus "B2 $$(i,j) = 0" using sp Cons 
      unfolding split_block_def Let_def n_def diagonal_mat_def by force
  qed
  have "B3 = 0\<^sub>m (n - a) a" 
  proof (rule eq_matI, auto)
    show "dim_row B3 = n-a" using sp Cons 
      unfolding split_block_def Let_def n_def by auto
    show "dim_col B3 = a" using sp Cons 
      unfolding split_block_def Let_def n_def by auto
    fix i j
    assume "i < n-a" and "j < a" 
    thus "B3 $$(i,j) = 0" using sp Cons 
      unfolding split_block_def Let_def n_def diagonal_mat_def by force
  qed
  show ?case 
  proof (rule diag_compat.simps(2)[THEN iffD2], intro conjI)
    show "a \<le> dim_row B" using Cons by simp
    show "let n = dim_row B; 
      (B1, B2, B3, B4) = split_block B a a in B2 = 0\<^sub>m a (n - a) \<and> 
      B3 = 0\<^sub>m (n - a) a \<and> diag_compat B4 l" 
      using sp \<open>B3 = 0\<^sub>m (n - a) a\<close> \<open>B2 = 0\<^sub>m a (n - a)\<close> 
        \<open>diag_compat B4 l\<close> unfolding Let_def n_def by auto
  qed
qed

text \<open>The following lemma provides a sufficient condition for the \verb+diag_compat+ predicate
to hold.\<close>

lemma commute_diag_compat:
  fixes D::"'a::{field} Matrix.mat"
  assumes "diagonal_mat D"
  and "D\<in> carrier_mat n n"
  and "B\<in> carrier_mat n n"
  and "B* D = D * B"
  and "diag_diff D l"
shows "diag_compat B l" using assms
proof (induct l arbitrary: B D n)
  case Nil
  hence "D \<in> carrier_mat 0 0" using assms by simp
  hence "n = 0" using assms using Nil(2) by auto 
  hence "B \<in> carrier_mat 0 0" using Nil by simp 
  then show ?case by simp
next
  case (Cons a l)
  define B1 where "B1 = fst (split_block B a a)"
  define B2 where "B2 = fst (snd (split_block B a a))"
  define B3 where "B3 = fst (snd (snd (split_block B a a)))"
  define B4 where "B4 = snd (snd (snd (split_block B a a)))"
  have spb: "split_block B a a = (B1, B2, B3, B4)" using fst_conv snd_conv 
    unfolding B1_def B2_def B3_def B4_def by simp
  define D1 where "D1 = fst (split_block D a a)"
  define D2 where "D2 = fst (snd (split_block D a a))"
  define D3 where "D3 = fst (snd (snd (split_block D a a)))"
  define D4 where "D4 = snd (snd (snd (split_block D a a)))"
  have spd: "split_block D a a = (D1, D2, D3, D4)" using fst_conv snd_conv 
    unfolding D1_def D2_def D3_def D4_def by simp
  have "a \<le> n" using Cons by simp
  moreover have "diag_compat B4 l" 
  proof (rule Cons(1)) 
    show "diagonal_mat D4" using spd Cons \<open>a \<le> n\<close> 
      split_block_diagonal[of D n a] by blast
    show "D4\<in> carrier_mat (n-a) (n-a)" using spd Cons(3) 
      unfolding split_block_def Let_def by fastforce
    show "diag_diff D4 l" using spd Cons by simp
    show "B4 \<in> carrier_mat (n - a) (n - a)" using spb Cons(4) 
      unfolding split_block_def Let_def by fastforce
    show "B4 * D4 = D4 * B4" using spb Cons \<open>a \<le> n\<close>  
      split_block_commute_subblock[of D] by (meson spd)
  qed
  moreover have "B2 = 0\<^sub>m a (n - a)" 
  proof (rule commute_diag_mat_split_block(1)[of D n B a B1 B2 B3 B4], 
      (auto simp add: spb Cons \<open>a \<le> n\<close>))
    fix i j
    assume "i < a" and "a \<le> j" and "j < n"
    thus "D $$ (i, i) = D $$ (j, j) \<Longrightarrow> False"
      using diag_diff_hd_diff[OF Cons(6) Cons(3), of i j] by simp 
  qed
  moreover have "B3 = 0\<^sub>m (n - a) a" 
  proof (rule commute_diag_mat_split_block(2)[of D n B a B1 B2 B3 B4], 
      (auto simp add: spb Cons \<open>a \<le> n\<close>))
    fix i j
    assume "i < a" and "a \<le> j" and "j < n"
    thus "D $$ (i, i) = D $$ (j, j) \<Longrightarrow> False"
      using diag_diff_hd_diff[OF Cons(6) Cons(3), of i j] by simp 
  qed
  ultimately show ?case 
    using spb diag_compat.simps(2)[THEN iffD2, of a B l] Cons
    unfolding Let_def by force
qed

subsection \<open>Counting similar neighbours in a list\<close>
text \<open>The function \verb+eq_comps+ takes a list as an input and counts the number of
adjacent elements that are identical.\<close>

fun eq_comps where
  "eq_comps [] = []"
| "eq_comps [x] = [1]"
| "eq_comps (x#y#l) = (let tmp = (eq_comps (y#l)) in
    if x = y then Suc (hd tmp) # (tl tmp)
    else 1 # tmp)"

lemma eq_comps_not_empty:
  assumes "l\<noteq> []"
  shows "eq_comps l \<noteq> []" using assms
proof (induct l rule: eq_comps.induct)
  case 1
  then show ?case by simp
next
  case (2 x)
  then show ?case by simp
next
  case (3 x y l)
  then show ?case by (cases "x = y", (auto simp add: Let_def))
qed

lemma eq_comps_empty_if:
  assumes "eq_comps l = []"
  shows "l = []" 
proof (rule ccontr)
  assume "l\<noteq> []"
  hence "eq_comps l \<noteq> []" using eq_comps_not_empty[of l] by simp
  thus False using assms by simp
qed

lemma eq_comps_hd_eq_tl:
  assumes "x = y"
  shows "tl (eq_comps (x#y#l)) = tl (eq_comps (y#l))" using assms by (simp add: Let_def)

lemma eq_comps_hd_neq_tl:
  assumes "x \<noteq> y"
  shows "tl (eq_comps (x#y#l)) = eq_comps (y#l)" using assms by (simp add:Let_def)

lemma eq_comps_drop:
  assumes "x#xs = eq_comps l"
  shows "xs = eq_comps (drop x l)" using assms
proof (induct l arbitrary:x xs rule: eq_comps.induct)
case 1
  then show ?case by simp
next
  case (2 u)
  hence "x = 1" by simp
  hence "drop x [u] = []" by simp 
  then show ?case using "2" by fastforce 
next
  case (3 u v l)
  define ec where "ec = eq_comps (v#l)"
    have "ec = hd ec # (tl ec)" using eq_comps_not_empty[of "v#l"] unfolding ec_def 
      by simp
  show ?case
  proof (cases "u = v")
    case True   
    have "xs = tl ec" using 3 eq_comps_hd_eq_tl[OF True] ec_def
      by (metis list.sel(3))
    moreover have "x = Suc (hd ec)" using True 3 eq_comps.simps(3)[of u v ] 
      unfolding ec_def Let_def by simp
    hence "drop (hd ec) (v#l) = drop x (u#v#l)" by simp
    moreover have "tl ec = eq_comps (drop (hd ec) (v#l))" using 3 ec_def
      \<open>ec = hd ec # (tl ec)\<close> by simp
    ultimately show ?thesis using 3 by simp
  next
    case False
    hence "x = 1" using 3 unfolding Let_def by simp
    moreover have "xs = ec" using 3 eq_comps_hd_neq_tl[OF False] ec_def 
      by (metis list.sel(3))
    ultimately show ?thesis unfolding ec_def by simp
  qed
qed

lemma eq_comps_neq_0:
  assumes "a#m = eq_comps l"
  shows "a \<noteq> 0" using assms
proof (induct l rule:eq_comps.induct)
  case 1
  then show ?case by simp
next
  case (2 x)
  then show ?case by simp
next
  case (3 x y l)
  then show ?case by (cases "x = y", (auto simp add: Let_def))
qed

lemma eq_comps_gt_0:
  assumes "l \<noteq> []"
  shows "list_all (\<lambda>a. 0 < a) (eq_comps l)"
proof (induct l rule:eq_comps.induct)
  case 1
  then show ?case by simp
next
  case (2 x)
  then show ?case by simp
next
  case (3 x y l)
  then show ?case 
  proof (cases "x = y")
    case True
    then show ?thesis 
      using 3 eq_comps.simps(3)[of x y l] list_all_simps(1) unfolding Let_def
      by (metis eq_comps_not_empty hd_Cons_tl list.discI zero_less_Suc) 
  next
    case False
    then show ?thesis 
      using 3 eq_comps.simps(3)[of x y l] list_all_simps(1) unfolding Let_def 
      by auto
  qed
qed

lemma eq_comps_elem_le_length:
  assumes "a#m = eq_comps l"
  shows "a \<le> length l" using assms
proof (induct l arbitrary: a rule:eq_comps.induct)
  case 1
  then show ?case by simp
next
  case (2 x)
  then show ?case by auto
next
  case (3 x y l)
  then show ?case 
  proof (cases "x = y")
    case True
    define ec where "ec = eq_comps (y#l)"
    have "ec = hd ec # (tl ec)" using eq_comps_not_empty[of "y#l"] unfolding ec_def 
      by simp
    have "a = Suc (hd ec)" using True 3 eq_comps.simps(3)[of x y] 
      unfolding ec_def Let_def by simp
    then show ?thesis using 3
      by (metis True \<open>ec = hd ec # tl ec\<close> ec_def eq_comps_hd_eq_tl length_Cons 
          list.sel(3) not_less_eq_eq) 
  next
    case False
    hence "a = 1" using 3 by (simp add: Let_def)
    then show ?thesis by simp
  qed
qed

lemma eq_comps_length:
  shows "length (eq_comps l) \<le> length l"
proof (induct l rule:eq_comps.induct)
  case 1
  then show ?case by simp
next
  case (2 x)
  then show ?case by auto
next
  case (3 x y l)
  define ec where "ec = eq_comps (y#l)"
    have ec: "ec = hd ec # (tl ec)" using eq_comps_not_empty[of "y#l"] unfolding ec_def 
      by simp
  then show ?case 
  proof (cases "x = y")
    case True    
    then show ?thesis using ec 3 eq_comps.simps(3) True unfolding Let_def
      by (metis ec_def le_SucI length_Cons)
  next
    case False
    then show ?thesis using ec 3 by simp
  qed
qed

lemma eq_comps_eq:
  assumes "a#m = eq_comps l"
  and "i < a"
shows "nth l i = hd l" using assms
proof (induct l arbitrary: a m i rule: eq_comps.induct)
  case 1
  then show ?case by simp
next
  case (2 u)
  then show ?case by simp
next
  case (3 u v l)
  show ?case
  proof (cases "u = v")
    case False
    thus ?thesis using 3 by (simp add: Let_def)
  next
    case True
    define ec where "ec = eq_comps (v#l)"
    have "ec = hd ec # (tl ec)" using eq_comps_not_empty[of "v#l"] 
      unfolding ec_def by simp
    have "a = Suc (hd ec)" using True 3 eq_comps.simps(3)[of u v] 
      unfolding ec_def Let_def by simp
    hence "i \<le> hd ec" using 3 by simp
    show ?thesis
    proof (cases "i = 0")
      case True
      thus ?thesis by simp
    next
      case False
      hence "\<exists>i'. i = Suc i'"  by (simp add: not0_implies_Suc)
      from this obtain i' where "i = Suc i'" by auto
      hence "i' < hd ec" using \<open>i \<le> hd ec\<close> by simp
      have "(u # v # l) ! i = (v#l) ! i'" using \<open>i = Suc i'\<close> by simp
      also have "... = v" using 3 \<open>ec = eq_comps (v#l)\<close> \<open>ec = hd ec # (tl ec)\<close>
        by (metis \<open>i' < hd ec\<close> list.sel(1)) 
      also have "... = hd (u#v#l)" using \<open>u = v\<close> by simp
      finally show ?thesis .
    qed
  qed
qed

lemma eq_comps_singleton:
  assumes "[a] = eq_comps l"
  shows "a = length l" using assms
proof (induct l arbitrary: a rule: eq_comps.induct)
case 1
then show ?case by simp
next
  case (2 x)
  then show ?case by simp
next
  case (3 x y l)
  define ec where "ec = eq_comps (y#l)"
  have "ec = hd ec # (tl ec)" using eq_comps_not_empty[of "y#l"] 
    unfolding ec_def by simp
  show ?case
  proof (cases "x = y")
    case True
    hence "a = Suc (hd ec)" using 3 eq_comps.simps(3)[of x y] 
      unfolding ec_def Let_def by simp
    have "tl ec = []" using 3 True eq_comps.simps(3)[of x y] 
      unfolding ec_def Let_def by simp
    hence "ec = [hd ec]" using \<open>ec = hd ec # tl ec\<close> by simp
    hence "hd ec = length (y#l)" using 3 ec_def by simp
    then show ?thesis using \<open>a = Suc (hd ec)\<close> by simp
  next
    case False
    then show ?thesis using eq_comps_hd_neq_tl 3
      \<open>ec = hd ec # tl ec\<close> ec_def by fastforce 
  qed
qed

lemma eq_comps_leq:
  assumes "a#b#m = eq_comps l"
  and "sorted l"
shows "hd l < hd (drop a l)" using assms
proof (induct l arbitrary: a b m  rule: eq_comps.induct)
case 1
  then show ?case by simp
next
  case (2 x)
  then show ?case by simp
next
  case (3 x y l)
  show ?case
  proof (cases "x = y")
    case True
    hence "hd (x#y#l) = y" by simp
    define ec where "ec = eq_comps (y#l)"
    have "a = Suc (hd (ec))" using True ec_def 3
      eq_comps.simps(3)[of x y] unfolding Let_def by simp
    have "b#m = tl ec" using True ec_def 3
      eq_comps.simps(3)[of x y] unfolding Let_def by simp
    hence eceq: "ec = hd ec # (hd (tl ec)) # (tl (tl ec))" unfolding ec_def
      by (metis eq_comps_not_empty list.exhaust_sel list.simps(3))
    have dra: "drop a (x#y#l) = drop (hd ec) (y#l)" using \<open>a = Suc (hd (ec))\<close> 
      by simp
    have "sorted (y#l)" using 3 by simp
    hence "y < hd (drop (hd ec) (y#l))" using 3(1) eceq unfolding ec_def
      by (metis list.sel(1))
    thus ?thesis using True dra by simp
  next
    case False
    hence "a = 1" using 3 by (simp add: Let_def)
    have "hd (x#y#l) = x" by simp
    moreover have "hd (drop a (x # y # l)) = y" using \<open>a = 1\<close> by simp
    ultimately show ?thesis using False 3
      by (metis order_le_imp_less_or_eq sorted2_simps(2))
  qed
qed

lemma eq_comps_compare:
  assumes "sorted l"
  and "a#m = eq_comps l"
  and "i < a"
  and "a \<le> j"
  and "j < length l"
shows "nth l i < nth l j" using assms
proof (cases "m =[]")
  case True
  hence "[a] = eq_comps l" using assms by simp
    hence "a = length l" using eq_comps_singleton[of a "l"] by simp
    then show ?thesis using assms by simp
next
  case False
  hence "m = hd m # (tl m)" by simp
  have "l!i = hd l" using assms eq_comps_eq by metis
  also have "... < hd (drop a l)" using eq_comps_leq assms \<open>m = hd m # (tl m)\<close> 
    by metis
  also have "... \<le> l!j" using assms
    by (metis hd_drop_conv_nth le_less_trans sorted_nth_mono)
  finally show ?thesis .
qed

lemma eq_comps_singleton_elems:
  assumes "eq_comps l = [a]"
  shows "\<forall>i < length l. l!i = l!0" using eq_comps_eq eq_comps_singleton
  by (metis assms bot_nat_0.not_eq_extremum eq_comps_neq_0)

lemma eq_comp_Re:
  assumes "\<forall> z \<in> set l. z \<in> Reals"
  and "m = eq_comps l"
shows "m = eq_comps (map Re l)" using assms 
proof (induct l arbitrary:m rule:eq_comps.induct)
  case 1
  then show ?case by simp
next
  case (2 x)
  then show ?case by simp
next
  case (3 x y l)
  define ec where "ec = eq_comps (y#l)"
  have ecr: "ec = eq_comps (map Re (y # l))" using ec_def 3 by simp
  show ?case
  proof (cases "x = y")
    case True
    hence "Re x = Re y" by simp
    have "m = Suc (hd ec) # (tl ec)" using ec_def 3 True
      by (simp add: Let_def)
    also have "... = eq_comps (map Re (x#y # l))" using ecr \<open>Re x = Re y\<close> 
      by (simp add: Let_def)
    finally show ?thesis .
  next
    case False
    hence "Re x \<noteq> Re y" using 3
      by (metis list.set_intros(1) list.set_intros(2) of_real_Re)
    have "m = 1#ec" using ec_def 3 False
      by (simp add: Let_def)
    also have "... = eq_comps (map Re (x#y # l))" using ecr \<open>Re x \<noteq> Re y\<close> 
      by (simp add: Let_def)
    finally show ?thesis using ecr unfolding Let_def by simp
  qed
qed

lemma eq_comps_sum_list:
  shows "sum_list (eq_comps l) = length l" 
proof (induct l  rule: eq_comps.induct)
  case 1
  then show ?case unfolding diag_mat_def by simp
next
  case (2 x)
  have "eq_comps [x] = [1]" using eq_comps.simps(2)[of x] by simp
  then show ?case by simp
next
  case (3 x y l)
  then show ?case 
  proof (cases "x = y")
    case True
    then show ?thesis using eq_comps.simps(3)[of x y l] 3
      by (cases \<open>eq_comps (y # l)\<close>) simp_all
  next
    case False
    then show ?thesis using eq_comps.simps(3)[of x y l]  3 
      unfolding Let_def by simp
  qed
qed

lemma eq_comps_elem_lt:
  assumes "1 < length (eq_comps l)"
  shows "hd (eq_comps l) < length l"
proof -
  define a where "a = hd (eq_comps l)"
  define b where "b = hd (tl (eq_comps l))"
  define c where "c = tl (tl (eq_comps l))"
  have "eq_comps l = a#b#c" using assms unfolding a_def b_def c_def
    by (metis eq_comps.simps(2) eq_comps_singleton length_0_conv 
        less_irrefl_nat less_nat_zero_code list.exhaust_sel)
  hence "b#c = eq_comps (drop a l)" using eq_comps_drop by metis
  hence "0 < b" using eq_comps_neq_0 by auto 
  moreover have "0 < a" using \<open>eq_comps l = a#b#c\<close> eq_comps_neq_0
    by (metis gr0I) 
  moreover have "a+b \<le> length l" using eq_comps_sum_list
    by (metis \<open>eq_comps l = a # b # c\<close> le_add1 nat_add_left_cancel_le 
        sum_list_simps(2))
  ultimately show ?thesis unfolding a_def by auto
qed

lemma eq_comp_sum_diag_mat:
  shows "sum_list (eq_comps (diag_mat A)) = dim_row A" 
  using eq_comps_sum_list[of "diag_mat A"] diag_mat_length by simp

lemma nsum_Suc_elem:
  assumes "1 < length (eq_comps l)"
  shows "l!(n_sum (Suc i) (eq_comps l)) = 
    (drop (hd (eq_comps l)) l)!(n_sum i (tl (eq_comps l)))" using assms
proof (induct i arbitrary: l)
  case 0
  hence "1 < length l" using eq_comps_length[of l] by presburger
  hence "l \<noteq> []" by fastforce
  hence "l ! n_sum (Suc 0) (eq_comps l) = l ! hd (eq_comps l)"  
    by (simp add: "0.prems" eq_comps_not_empty hd_conv_nth)
  also have "... = hd (drop (hd (eq_comps l)) l)"
    by (metis "0.prems" eq_comps_elem_lt hd_drop_conv_nth)
  finally show ?case using 0
    by (metis (no_types, opaque_lifting) \<open>l ! hd (eq_comps l) = 
      hd (drop (hd (eq_comps l)) l)\<close> \<open>l \<noteq> []\<close> append_Nil2 
      eq_comps.simps(1) eq_comps_drop eq_comps_empty_if eq_comps_singleton 
      hd_conv_nth list.exhaust_sel n_sum.simps(1) nat_arith.rule0 
      nth_append_length_plus) 
next
  case (Suc i)
  have "l!(n_sum (Suc (Suc i)) (eq_comps l)) = 
    l!(hd (eq_comps l) + (n_sum (Suc i) (tl (eq_comps l))))" by simp
  also have "... = (drop (hd (eq_comps l)) l)!
    (n_sum (Suc i) (tl (eq_comps l)))" 
    using less_or_eq_imp_le
    by (metis Suc.prems eq_comps_elem_lt nth_drop)
  finally show ?case .
qed

lemma eq_comps_elems_eq:
  assumes "l\<noteq>[]"
  and "i < length (eq_comps l)"
  and "j < (eq_comps l)!i"
shows "l!(n_sum i (eq_comps l)) = l!(n_sum i (eq_comps l) + j)" using assms
proof (induct i arbitrary: l)
  case 0
  hence "eq_comps l = hd (eq_comps l)#(tl (eq_comps l))" by simp
  have "l ! n_sum 0 (eq_comps l) = hd l"
    by (simp add: "0"(1) hd_conv_nth)
  also have "... = l!j" using 0 eq_comps_eq
    by (metis \<open>eq_comps l = hd (eq_comps l) # tl (eq_comps l)\<close> nth_Cons_0)
  finally show ?case by simp
next
  case (Suc i)
  show ?case
  proof (cases "length (eq_comps l) = 1")
    case True
    hence "Suc i = 0" using Suc.prems(2) by fastforce 
    then show ?thesis by simp
  next
    case False
    hence "1 < length (eq_comps l)" using Suc eq_comps_not_empty[of l] 
      by presburger
    hence "l!(n_sum (Suc i) (eq_comps l)) = 
    (drop (hd (eq_comps l)) l)!(n_sum i (tl (eq_comps l)))"
      using nsum_Suc_elem by simp
    also have "... = (drop (hd (eq_comps l)) l)!
      (n_sum i (eq_comps (drop (hd (eq_comps l)) l)))" 
      using eq_comps_drop[of "hd (eq_comps l)"] eq_comps_empty_if list.collapse
      by fastforce
    also have "... = (drop (hd (eq_comps l)) l)!
      (n_sum i (eq_comps (drop (hd (eq_comps l)) l)) + j)" 
    proof (rule Suc(1))
      show "drop (hd (eq_comps l)) l \<noteq> []"
        by (metis Cons_nth_drop_Suc \<open>1 < length (eq_comps l)\<close> eq_comps_elem_lt 
            list.distinct(1)) 
      show "i < length (eq_comps (drop (hd (eq_comps l)) l))" using Suc
        by (metis (no_types, lifting) Suc_lessD eq_comps_drop 
            eq_comps_not_empty length_Suc_conv list.collapse 
            not_less_less_Suc_eq) 
      show "j < eq_comps (drop (hd (eq_comps l)) l) ! i" using Suc
        by (metis eq_comps_drop length_Suc_conv less_natE list.exhaust_sel 
            list.simps(3) nth_Cons_Suc) 
    qed
    also have "... = (drop (hd (eq_comps l)) l)!
      (n_sum i (tl (eq_comps l)) + j)"
      by (metis Suc(2) eq_comps_drop eq_comps_not_empty hd_Cons_tl) 
    also have "... = l!(n_sum (Suc i) (eq_comps l) + j)"
      by (metis (no_types, opaque_lifting) Groups.add_ac(2) 
          Groups.add_ac(3) \<open>1 < length (eq_comps l)\<close> eq_comps_elem_lt 
          less_or_eq_imp_le n_sum.simps(2) nth_drop) 
    finally show ?thesis .
  qed
qed

text \<open>When the diagonal block matrices are extracted using \verb+eq_comp+, each extracted 
matrix is a multiple of the identity.\<close>

lemma extract_subdiags_eq_comp:
  fixes A::"complex Matrix.mat"
  assumes "diagonal_mat A"
  and "A\<in> carrier_mat n n"
  and "0 < n"
  and "i < length (eq_comps (diag_mat A))"
  shows "\<exists>k. (extract_subdiags A (eq_comps (diag_mat A)))!i = 
    k \<cdot>\<^sub>m (1\<^sub>m ((eq_comps (diag_mat A))!i))"
proof 
  define l where "l = diag_mat A"
  define k where "k = l!(n_sum i (eq_comps l))"
  show "extract_subdiags A (eq_comps (diag_mat A)) ! i = 
    k \<cdot>\<^sub>m 1\<^sub>m (eq_comps (diag_mat A) ! i)"
  proof (rule eq_matI, auto simp add: assms)
    show dr: "dim_row (extract_subdiags A (eq_comps (diag_mat A)) ! i) = 
      eq_comps (diag_mat A) ! i" 
      using extract_subdiags_carrier assms carrier_matD(1) by blast
    show dc: "dim_col (extract_subdiags A (eq_comps (diag_mat A)) ! i) = 
      eq_comps (diag_mat A) ! i"
      using extract_subdiags_carrier assms carrier_matD by blast
    fix m np
    assume "m < eq_comps (diag_mat A)!i" and "np < eq_comps (diag_mat A)!i" 
      and "m\<noteq> np" note mnp=this
    have "diagonal_mat (extract_subdiags A (eq_comps (diag_mat A)) !i)"
    proof (rule extract_subdiags_diagonal)
      show "diagonal_mat A" using assms by simp
      show "A\<in> carrier_mat n n" using assms by simp
      show "eq_comps (diag_mat A) \<noteq> []" using assms unfolding diag_mat_def
        by auto
      show "sum_list (eq_comps (diag_mat A)) \<le> n" 
        using assms eq_comps_sum_list unfolding diag_mat_def
        by (metis carrier_matD(1) carrier_matD(2) length_cols_mat_to_cols_list 
            length_map order.eq_iff)
      show "i < length (eq_comps (diag_mat A))" using assms by simp
    qed
    thus "extract_subdiags A (eq_comps (diag_mat A)) ! i $$ (m, np) = 0" 
      using mnp dr dc by (metis diagonal_mat_def)
  next
    fix p
    assume "p < eq_comps (diag_mat A) ! i"
    have "extract_subdiags A (eq_comps (diag_mat A)) ! i $$ (p, p) = 
      diag_mat A! (n_sum i (eq_comps (diag_mat A)) + p)" 
    proof (rule extract_subdiags_diag_elem)
      show "A\<in> carrier_mat n n" "0 < n" "i < length (eq_comps (diag_mat A))" 
        using assms by auto
      show ne: "eq_comps (diag_mat A) \<noteq> []" using assms by auto
      show "p < eq_comps (diag_mat A) ! i" 
        using \<open>p < eq_comps (diag_mat A) ! i\<close> .
      show "sum_list (eq_comps (diag_mat A)) \<le> n" 
        using assms eq_comps_sum_list[of "diag_mat A"] 
        unfolding diag_mat_def by simp
      show "\<forall>j<length (eq_comps (diag_mat A)). 0 < eq_comps (diag_mat A) ! j" 
        using eq_comps_gt_0 ne
        by (metis eq_comps.simps(1) list_all_length)
    qed 
    also have "... = k" unfolding k_def l_def 
    proof (rule eq_comps_elems_eq[symmetric])
      show "diag_mat A \<noteq> []" using assms unfolding diag_mat_def by simp
      show "p < eq_comps (diag_mat A) ! i" 
        using \<open>p < eq_comps (diag_mat A) ! i\<close> .
      show "i < length (eq_comps (diag_mat A))" using assms by simp
    qed
    finally show 
      "extract_subdiags A (eq_comps (diag_mat A)) ! i $$ (p, p) = k" .
  qed
qed

lemma extract_subdiags_comp_commute:
  fixes A::"complex Matrix.mat"
  assumes "diagonal_mat A"
  and "A\<in> carrier_mat n n"
  and "0 < n"
  and "i < length (eq_comps (diag_mat A))"
  and "B \<in> carrier_mat ((eq_comps (diag_mat A))!i) ((eq_comps (diag_mat A))!i)"
  shows "(extract_subdiags A (eq_comps (diag_mat A)))!i * B = 
    B * (extract_subdiags A (eq_comps (diag_mat A)))!i"
proof -
  define m where "m = (eq_comps (diag_mat A))!i" 
  have "\<exists>k. (extract_subdiags A (eq_comps (diag_mat A)))!i = 
    k \<cdot>\<^sub>m (1\<^sub>m ((eq_comps (diag_mat A))!i))" 
    using assms extract_subdiags_eq_comp by simp
  from this obtain k where 
    "(extract_subdiags A (eq_comps (diag_mat A)))!i = 
    k \<cdot>\<^sub>m (1\<^sub>m m)" unfolding m_def by auto note kprop = this
  hence "(extract_subdiags A (eq_comps (diag_mat A)))!i * B =
    k \<cdot>\<^sub>m (1\<^sub>m m) * B" by simp
  also have "... = B * (k \<cdot>\<^sub>m (1\<^sub>m m))" using assms m_def
    by (metis left_mult_one_mat mult_smult_assoc_mat 
        mult_smult_distrib one_carrier_mat right_mult_one_mat)
  finally show ?thesis using kprop by simp
qed

text \<open>In particular, extracting the diagonal sub-blocks of a diagonal matrix leaves
it unchanged. \<close>

lemma diagonal_extract_eq:
  assumes "B\<in> carrier_mat n n"
  and "diagonal_mat B"
shows "B = diag_block_mat (extract_subdiags B (eq_comps (diag_mat B)))" 
proof (rule diag_compat_extract_subdiag)
  define eqcl where "eqcl= eq_comps (diag_mat B)"
  show "B \<in> carrier_mat n n" using assms by simp
  show  "diag_compat B eqcl" 
  proof (rule diag_compat_diagonal)
    show "B \<in> carrier_mat (dim_row B) (dim_row B)" 
      using assms by simp
    show "diagonal_mat B" using assms by simp
    have "dim_row B = length (diag_mat B)" unfolding diag_mat_def by simp
    also have "... = sum_list eqcl" using eq_comps_sum_list[of "diag_mat B"] 
      unfolding eqcl_def by simp
    finally show "dim_row B = sum_list eqcl".
  qed
qed

fun lst_diff where
  "lst_diff l [] = (l = [])"
| "lst_diff  l (x#xs) = (x \<le> length l \<and>
    (\<forall>i j. i < x \<and> x \<le> j \<and> j < length l \<longrightarrow> nth l i < nth l j) \<and>
    lst_diff (drop x l) xs)"

lemma sorted_lst_diff:
  assumes "sorted l"
  and "m = eq_comps l"
shows "lst_diff l m" using assms
proof (induct m arbitrary: l)
  case Nil
  hence "l = []" using eq_comps_empty_if[of l] by simp
  then show ?case by simp
next
  case (Cons a m)
  have "sorted (drop a l)" using Cons sorted_wrt_drop by simp
  moreover have "m = eq_comps (drop a l)" using eq_comps_drop Cons by simp
  ultimately have "lst_diff (drop a l) m" using Cons by simp
  have "a \<le> length l" using eq_comps_elem_le_length Cons by simp
  have "(\<forall>i j. i < a \<and> a \<le> j \<and> j < length l \<longrightarrow> nth l i < nth l j)" 
    using Cons eq_comps_compare by blast 
  then show ?case using \<open>a \<le> length l\<close> \<open>lst_diff (drop a l) m\<close> by fastforce
qed

lemma lst_diff_imp_diag_diff:
  fixes D::"'a::preorder Matrix.mat"
  assumes "D\<in> carrier_mat n n"
  and "lst_diff (diag_mat D) m"
  shows "diag_diff D m" using assms
proof (induct arbitrary: n rule:diag_diff.induct)
  case (1 D)
  hence "diag_mat D = []"  by simp
  hence "dim_row D = 0" unfolding diag_mat_def by simp
  hence "n= 0" using 1 by simp
  hence "dim_col D = 0" using 1 by simp
  then show ?case using \<open>dim_row D = 0\<close> by simp
next
  case (2 D a xs)
  define D1 where "D1 = fst (split_block D a a)"
  define D2 where "D2 = fst (snd (split_block D a a))"
  define D3 where "D3 = fst (snd (snd (split_block D a a)))"
  define D4 where "D4 = snd (snd (snd (split_block D a a)))"
  have spd: "split_block D a a = (D1, D2, D3, D4)" using fst_conv snd_conv 
    unfolding D1_def D2_def D3_def D4_def by simp
  have "length (diag_mat D) = n" using 2 unfolding diag_mat_def by simp
  hence "a \<le> n" using 2 by simp
  hence c1: "D1 \<in> carrier_mat a a" 
    using split_block(1)[OF spd, of "n-a" "n-a"] 2 by simp
  have c4: "D4 \<in> carrier_mat (n-a) (n-a)" 
    using 2  split_block(4)[OF spd] \<open>a \<le> n\<close> by simp
  have "diag_mat D = diag_mat D1 @ (diag_mat D4)" 
    using diag_four_block_mat split_block(5)
    by (metis "2"(2) \<open>a \<le> n\<close> c1 c4 carrier_matD(1) carrier_matD(2) 
        le_Suc_ex spd)
  have "length (diag_mat D1) = a" using c1 unfolding diag_mat_def by simp
  hence "diag_mat D4 = drop a (diag_mat D)" 
    using \<open>diag_mat D = diag_mat D1 @ (diag_mat D4)\<close> by simp
  hence "lst_diff (diag_mat D4) xs" using 2 by simp
  hence "diag_diff D4 xs" using 2(1)[OF spd[symmetric]] spd c4 
    by blast
  have  "(\<forall>i j. i < dim_row D1 \<and> j < dim_row D4 \<longrightarrow> D1$$(i,i) < D4 $$ (j,j))" 
  proof (intro allI impI)
    fix i j
    assume ijp: "i < dim_row D1 \<and> j < dim_row D4"
    hence "i < a" using c1 by simp
    have "j+a < n" using c4 ijp by (metis carrier_matD(1) less_diff_conv) 
    have "D1 $$ (i,i) = D $$ (i,i)" using spd \<open>i < a\<close> 
      unfolding split_block_def Let_def by force
    also have "... = (diag_mat D)!i" using \<open>i < a\<close> \<open>a \<le> n\<close> 2 
      unfolding diag_mat_def by simp
    also have "... < (diag_mat D)!(j+a)" using 2 \<open>j+a < n\<close>
      by (metis \<open>i < a\<close> \<open>length (diag_mat D) = n\<close> 
          le_add2 lst_diff.simps(2))
    also have "... = D $$ (j+a, j+a)" using \<open>j+a < n\<close> 2 
      unfolding diag_mat_def by simp
    also have "... = D4 $$ (j,j)" using spd ijp 2
      unfolding split_block_def Let_def by force
    finally show "D1$$(i,i) < D4 $$ (j,j)" .
  qed
  hence "(\<forall>i j. i < dim_row D1 \<and> j < dim_row D4 \<longrightarrow> D1$$(i,i) \<noteq> D4 $$ (j,j))"  
    by (metis order_less_irrefl)
  thus ?case using \<open>diag_diff D4 xs\<close> \<open>a \<le> n\<close> 2 spd by simp
qed

lemma sorted_diag_diff:
  fixes D::"'a::linorder Matrix.mat"
  assumes "D\<in> carrier_mat n n"
  and "sorted (diag_mat D)"
shows "diag_diff D (eq_comps (diag_mat D))" 
proof (rule lst_diff_imp_diag_diff)
  show "D \<in> carrier_mat n n" using assms by simp
  show "lst_diff (diag_mat D) (eq_comps (diag_mat D))"
    using sorted_lst_diff[of "diag_mat D"] assms by simp
qed

lemma Re_sorted_lst_diff:
  fixes l::"complex list"
  assumes "\<forall> z \<in> set l. z \<in> Reals"
  and "sorted (map Re l)"
  and "m = eq_comps l"
shows "lst_diff l m" using assms 
proof (induct m arbitrary: l)
  case Nil
  hence "l = []" using eq_comps_empty_if[of l] by simp
  then show ?case by simp
next
  case (Cons a m)  
  have "sorted (map Re (drop a l))" using Cons sorted_wrt_drop
    by (metis drop_map)
  moreover have "m = eq_comps (drop a l)" using eq_comps_drop Cons by simp
  ultimately have "lst_diff (drop a l) m" using Cons
    by (metis in_set_dropD)
  have "a \<le> length l" using eq_comps_elem_le_length Cons by simp
  have "(\<forall>i j. i < a \<and> a \<le> j \<and> j < length l \<longrightarrow> nth l i < nth l j)" 
  proof (intro allI impI)
    fix i j
    assume asm: "i < a \<and> a \<le> j \<and> j < length l"
    hence "Re (l!i) < Re (l!j)"
      using Cons eq_comps_compare eq_comp_Re
      by (smt (z3) dual_order.strict_trans dual_order.strict_trans1 length_map 
          nth_map)
    moreover have "l!i \<in> Reals" using asm Cons by simp
    moreover have "l!j \<in> Reals" using asm Cons by simp
    ultimately show "nth l i < nth l j" using less_complex_def
      by (simp add: complex_is_Real_iff)
  qed
  then show ?case using \<open>a \<le> length l\<close> \<open>lst_diff (drop a l) m\<close> by fastforce
qed

text \<open>The following lemma states a sufficient condition for the \verb+diag_diff+ predicate
to hold.\<close>

lemma cpx_sorted_diag_diff:
  fixes D::"complex Matrix.mat"
  assumes "D\<in> carrier_mat n n"
  and "\<forall> i < n. D$$(i,i) \<in> Reals"
  and "sorted (map Re (diag_mat D))"
shows "diag_diff D (eq_comps (diag_mat D))" 
proof (rule lst_diff_imp_diag_diff)
  show "D \<in> carrier_mat n n" using assms by simp
  have "\<forall>z\<in>set (diag_mat D). z \<in> \<real>" using assms unfolding diag_mat_def by auto
  thus "lst_diff (diag_mat D) (eq_comps (diag_mat D))"
    using Re_sorted_lst_diff[of "diag_mat D"] assms by simp
qed

section \<open>Sorted hermitian decomposition\<close>
text \<open>We prove that any Hermitian matrix $A$ can be decomposed into a product 
$U^\dagger \cdot B \cdot U$, where $U$ is a unitary matrix and $B$ is a diagonal matrix
containing only real components which are ordered along the diagonal.\<close>

definition per_col where
"per_col A f = Matrix.mat (dim_row A) (dim_col A) (\<lambda> (i,j). A $$(i, (f j)))"

lemma per_col_carrier:
  assumes "A \<in> carrier_mat n m"
  shows "per_col A f \<in> carrier_mat n m" using assms unfolding per_col_def 
  by simp

lemma per_col_col:
  assumes "A \<in> carrier_mat n m"
  and "j < m"  
shows "Matrix.col (per_col A f) j = Matrix.col A (f j)" 
proof
  show dim: "dim_vec (Matrix.col (per_col A f) j) = 
    dim_vec (Matrix.col A (f j))"
    using per_col_carrier by (metis assms(1) carrier_matD(1) dim_col)
  fix i
  assume "i < dim_vec (Matrix.col A (f j))"
  hence "i < dim_vec (Matrix.col (per_col A f) j)" using dim by simp
  hence "vec_index (Matrix.col (per_col A f) j) i = (per_col A f)$$(i,j)"
    unfolding Matrix.col_def by simp
  also have "... = A $$(i, (f j))" unfolding per_col_def
    using \<open>i < dim_vec (Matrix.col A (f j))\<close> assms by fastforce
  also have "... = vec_index (Matrix.col A (f j)) i" unfolding Matrix.col_def
    using \<open>i < dim_vec (Matrix.col A (f j))\<close> by auto
  finally show "vec_index (Matrix.col (per_col A f) j) i = 
    vec_index (Matrix.col A (f j)) i" .
qed

lemma per_col_adjoint_row:
  assumes "A \<in> carrier_mat n n"
  and "i < n"  
  and "f i < n"
shows "Matrix.row (Complex_Matrix.adjoint (per_col A f)) i = 
  Matrix.row (Complex_Matrix.adjoint A) (f i)" 
proof -
  have "per_col A f \<in> carrier_mat n n" using assms per_col_carrier[of A] 
    by simp
  hence "Matrix.row (Complex_Matrix.adjoint (per_col A f)) i = 
    conjugate (Matrix.col (per_col A f) i)" 
    using assms adjoint_row[of i "per_col A f"] by simp
  also have "... = conjugate (Matrix.col A (f i))" using assms per_col_col 
    by simp
  also have "... = Matrix.row (Complex_Matrix.adjoint A) (f i)" using assms 
    adjoint_row[of "f i" A] by simp
  finally show ?thesis .
qed

lemma per_col_mult_adjoint:
  assumes "A \<in> carrier_mat n n"
  and "i < n"
  and "j < n"
  and "f i < n"
  and "f j < n"
shows "((Complex_Matrix.adjoint (per_col A f)) * (per_col A f))$$(i,j) = 
  ((Complex_Matrix.adjoint A) * A)$$(f i, f j)"
proof -
  have "((Complex_Matrix.adjoint (per_col A f)) * (per_col A f))$$(i,j) = 
    Matrix.scalar_prod (Matrix.row (Complex_Matrix.adjoint (per_col A f)) i)
      (Matrix.col A (f j))" using assms per_col_col unfolding times_mat_def
    by (metis adjoint_dim_row carrier_matD(2) dim_col_mat(1) index_mat(1) 
        old.prod.case per_col_def)
  also have "... = Matrix.scalar_prod 
      (Matrix.row (Complex_Matrix.adjoint A) (f i))
      (Matrix.col A (f j))" using assms per_col_adjoint_row by metis
  also have "... = ((Complex_Matrix.adjoint A) * A)$$(f i, f j)" using assms 
    unfolding times_mat_def by simp
  finally show ?thesis .
qed

lemma idty_index:
  assumes "bij_betw f {..< n} {..< n}"
  and "i < n"
  and "j < n"
shows "(1\<^sub>m n)$$(i,j) = (1\<^sub>m n)$$(f i, f j)"
proof -
  have "f i < n" "f j < n" using assms bij_betwE by auto
  show ?thesis
  proof (cases "i = j")
    case True
    then show ?thesis using \<open>f i < n\<close> assms by simp
  next
    case False
    hence "f i \<noteq> f j" using assms
      by (metis bij_betw_iff_bijections lessThan_iff)
    then show ?thesis
      by (metis \<open>f i < n\<close> \<open>f j < n\<close> assms(2) assms(3) index_one_mat(1))
  qed
qed

lemma per_col_unitary:
  assumes "A\<in> carrier_mat n n"
  and "unitary A"
  and "bij_betw f {..< n} {..< n}"
shows "unitary (per_col A f)" unfolding unitary_def
proof
  show pc: "per_col A f \<in> 
    carrier_mat (dim_row (per_col A f)) (dim_row (per_col A f))"
    using assms per_col_carrier by (metis carrier_matD(1))
  have "dim_row (per_col A f) = n" using assms per_col_carrier
    by (metis carrier_matD(1))
  moreover have "(Complex_Matrix.adjoint (per_col A f)) * (per_col A f) = 1\<^sub>m n" 
  proof (rule eq_matI)
    show "dim_row (Complex_Matrix.adjoint (per_col A f) * per_col A f) = 
      dim_row (1\<^sub>m n)" using pc
      by (metis adjoint_dim_row calculation carrier_matD(2) index_mult_mat(2) 
          index_one_mat(2))
    thus "dim_col (Complex_Matrix.adjoint (per_col A f) * per_col A f) = 
      dim_col (1\<^sub>m n)" by auto
    fix i j
    assume "i < dim_row (1\<^sub>m n)" and "j < dim_col (1\<^sub>m n)" note ij = this
    have "(Complex_Matrix.adjoint (per_col A f) * per_col A f) $$ (i, j) = 
      (Complex_Matrix.adjoint A * A) $$ (f i, f j)"
    proof (rule per_col_mult_adjoint)
      show "A\<in> carrier_mat n n" using assms by simp
      show "i < n" "j < n" using ij by auto
      thus "f i < n" using assms by (meson bij_betw_apply lessThan_iff)
      show "f j < n" using \<open>j < n\<close> assms by (meson bij_betw_apply lessThan_iff)
    qed
    also have "... = (1\<^sub>m n) $$ (f i, f j)" using assms 
      unfolding Complex_Matrix.unitary_def 
      by (metis  assms(2) unitary_simps(1))
    also have "... = (1\<^sub>m n) $$ (i,j)" using idty_index[of f n i j] assms ij 
      by auto
    finally show "(Complex_Matrix.adjoint (per_col A f) * 
      per_col A f) $$ (i, j) = 1\<^sub>m n $$ (i, j)" .
  qed
  ultimately show "inverts_mat (per_col A f) 
    (Complex_Matrix.adjoint (per_col A f))" 
    using inverts_mat_symm inverts_mat_def
    by (metis (no_types, lifting) adjoint_dim_col adjoint_dim_row 
        carrier_mat_triv index_mult_mat(3) index_one_mat(3))
qed

definition per_diag where
"per_diag A f = Matrix.mat (dim_row A) (dim_col A) (\<lambda> (i,j). A $$(f i, (f j)))"

lemma per_diag_carrier:
  shows "per_diag A f \<in> carrier_mat (dim_row A) (dim_col A)" 
  unfolding per_diag_def by simp

lemma per_diag_diagonal:
  assumes "D\<in> carrier_mat n n"
  and "diagonal_mat D"
  and "bij_betw f {..< n} {..< n}"
shows "diagonal_mat (per_diag D f)" unfolding diagonal_mat_def
proof (intro allI impI)
  fix i j
  assume  "i < dim_row (per_diag D f)" and "j < dim_col (per_diag D f)"
  and "i\<noteq> j" note asm = this
  hence "f i \<noteq> f j" using assms
    by (metis bij_betw_iff_bijections carrier_matD(1) carrier_matD(2) 
        lessThan_iff per_diag_carrier) 
  moreover have "f i < n" using assms asm
    by (metis bij_betwE carrier_matD(1) lessThan_iff per_diag_carrier)
  moreover have "f j < n" using assms asm
    by (metis bij_betwE carrier_matD(2) lessThan_iff per_diag_carrier)
  ultimately show "per_diag D f $$ (i, j) = 0" using assms
    unfolding per_diag_def diagonal_mat_def
    by (metis asm(1) asm(2) carrier_matD(1) carrier_matD(2) 
        dim_col_mat(1) dim_row_mat(1) index_mat(1) old.prod.case per_diag_def) 
qed

lemma per_diag_diag_mat:
  assumes "A \<in> carrier_mat n n"
  and "i < n"
  and "f i < n"
shows "diag_mat (per_diag A f)!i = diag_mat A ! (f i)" 
  using assms unfolding diag_mat_def per_diag_def by auto

lemma per_diag_diag_mat_Re:
  assumes "A \<in> carrier_mat n n"
  and "i < n"
  and "f i < n"
shows "map Re (diag_mat (per_diag A f))!i = map Re (diag_mat A) ! (f i)" 
proof -
  have "map Re (diag_mat (per_diag A f))!i = Re (diag_mat (per_diag A f)!i)" 
  proof (rule nth_map)
    show "i < length (diag_mat (per_diag A f))" 
      using assms unfolding diag_mat_def
      by (metis carrier_matD(1) carrier_matD(2) length_cols_mat_to_cols_list 
          length_map per_diag_carrier)
  qed
  also have "... = Re (diag_mat A ! (f i))" using assms per_diag_diag_mat 
    by metis
  also have "... = map Re (diag_mat A) ! (f i)" unfolding diag_mat_def
    using assms by auto
  finally show ?thesis .
qed

lemma per_diag_real:
  fixes B::"complex Matrix.mat"
  assumes "B\<in> carrier_mat n n"
  and "\<forall>i< n. B$$(i,i) \<in> Reals"
  and "bij_betw f {..<n} {..<n}"
shows "\<forall>j<n. (per_diag B f)$$(j,j) \<in> Reals" 
proof (intro allI impI)
  fix j
  assume "j < n"
  hence "per_diag B f $$ (j,j) = B $$ (f j, f j)" 
    using assms unfolding per_diag_def by simp
  also have "... \<in> Reals" using assms \<open>j < n\<close> bij_betwE by blast
  finally show "per_diag B f $$ (j,j) \<in> Reals" .
qed

lemma per_col_mult_unitary:
  fixes A::"complex Matrix.mat"
  assumes "A \<in> carrier_mat n n"
  and "unitary A"
  and "D\<in> carrier_mat n n"
  and "diagonal_mat D"
  and "0 < n"
  and "bij_betw f {..< n} {..< n}"
shows "A * D * (Complex_Matrix.adjoint A) = 
  (per_col A f) * (per_diag D f) * (Complex_Matrix.adjoint (per_col A f))" 
  (is "?L = ?R")
proof  -
  have row: "dim_row ?L = dim_row ?R" using per_col_carrier assms
    by (metis carrier_matD(1) index_mult_mat(2)) 
  have col: "dim_col ?L = dim_col ?R" using per_col_carrier assms
    by (metis adjoint_dim carrier_matD(2) index_mult_mat(3))
  define fc::"complex Matrix.mat set" where "fc = carrier_mat n n"
  interpret cpx_sq_mat n n fc 
  proof 
    show "0 < n" using assms by simp
  qed (auto simp add: fc_def)
  define h where 
    "h = (\<lambda>i. (if i < n then diag_mat D ! i \<cdot>\<^sub>m rank_1_proj (Matrix.col A i) 
      else (0\<^sub>m n n)))"
  define g where
    "g = (\<lambda>i. (if i < n 
      then diag_mat D ! (f i) \<cdot>\<^sub>m rank_1_proj (Matrix.col A (f i)) 
      else (0\<^sub>m n n)))"
  have "f ` {..<n} = {..<n}" using assms
    by (simp add: bij_betw_imp_surj_on)
  have g: "\<forall>i. g i \<in> fc" unfolding g_def fc_def
    by (metis adjoint_dim_col assms(1) carrier_matD(1) carrier_matI 
        dim_col fc_mats_carrier rank_1_proj_adjoint rank_1_proj_dim 
        smult_carrier_mat zero_mem)
  moreover have h:"\<forall>i. h i \<in> fc" unfolding h_def fc_def
    by (metis assms(1) carrier_matD(1) dim_col fc_mats_carrier 
        rank_1_proj_carrier smult_carrier_mat zero_mem)
  moreover have "inj_on f {..<n}" using assms(6) bij_betw_def by auto 
  moreover have "\<And>x. x \<in> {..<n} \<Longrightarrow> h (f x) = g x" unfolding h_def g_def
    by (meson assms(6) bij_betwE lessThan_iff)
  ultimately have "sum_mat g {..<n} = sum_mat h (f`{..<n})" 
    using sum_with_reindex_cong[of h g f "{..<n}"] 
    unfolding  sum_mat_def by simp
  also have "... = sum_mat h {..<n}" using \<open>f ` {..<n} = {..<n}\<close> by simp
  also have "... =sum_mat (\<lambda>i. diag_mat D ! i \<cdot>\<^sub>m rank_1_proj (Matrix.col A i))
    {..<n}"
  proof (rule sum_mat_cong, (auto simp add:h h_def))
    show "\<And>i. i < n \<Longrightarrow> diag_mat D ! i \<cdot>\<^sub>m rank_1_proj (Matrix.col A i) \<in> fc"
      using assms unfolding fc_def by (metis fc_mats_carrier h h_def) 
    show "\<And>i. i < n \<Longrightarrow> diag_mat D ! i \<cdot>\<^sub>m rank_1_proj (Matrix.col A i) \<in> fc"
      using assms unfolding fc_def by (metis fc_mats_carrier h h_def) 
  qed
  also have "... = A * D * (Complex_Matrix.adjoint A)" 
    using weighted_sum_rank_1_proj_unitary assms unfolding fc_def by simp
  finally have sg: "sum_mat g {..<n} = A * D * (Complex_Matrix.adjoint A)" .
  have "(per_col A f) * (per_diag D f) * 
    (Complex_Matrix.adjoint (per_col A f)) = 
    sum_mat (\<lambda>i. diag_mat (per_diag D f) ! i \<cdot>\<^sub>m 
    rank_1_proj (Matrix.col (per_col A f) i)) {..<n}"
  proof (rule weighted_sum_rank_1_proj_unitary[symmetric])
    show "per_col A f \<in> fc" using per_col_carrier[of A] assms unfolding fc_def 
      by simp
    show "per_diag D f \<in> fc" using per_diag_carrier[of D] assms
      unfolding fc_def by simp
    show "diagonal_mat (per_diag D f)" using assms per_diag_diagonal[of D] 
      by simp
    show "unitary (per_col A f)" using per_col_unitary[of A] assms by simp
  qed
  also have "... = sum_mat g {..<n}"
  proof (rule sum_mat_cong, (auto simp add: g_def))
    show "\<And>i. i < n \<Longrightarrow> diag_mat (per_diag D f) ! i \<cdot>\<^sub>m 
      rank_1_proj (Matrix.col (per_col A f) i) \<in> fc" 
    proof -
      fix i
      assume "i < n"
      have "dim_vec (Matrix.col (per_col A f) i) = n" using assms per_col_col
        by (metis carrier_matD(1) dim_col)
      hence "rank_1_proj (Matrix.col (per_col A f) i) \<in> fc" unfolding fc_def
        using rank_1_proj_carrier by blast
      thus "diag_mat (per_diag D f) ! i \<cdot>\<^sub>m 
        rank_1_proj (Matrix.col (per_col A f) i) \<in> fc" unfolding fc_def by simp
    qed
    show "\<And>i. i < n \<Longrightarrow> diag_mat D ! f i \<cdot>\<^sub>m 
      rank_1_proj (Matrix.col A (f i)) \<in> fc"
    proof -
      fix i
      assume "i < n"
      hence "f i < n" using \<open>f ` {..<n} = {..<n}\<close> by auto 
      hence "dim_vec (Matrix.col A (f i)) = n" using assms 
        by (metis carrier_matD(1) dim_col)
      hence "rank_1_proj (Matrix.col A (f i)) \<in> fc" unfolding fc_def
        using rank_1_proj_carrier by blast
      thus "diag_mat D ! f i \<cdot>\<^sub>m rank_1_proj (Matrix.col A (f i)) \<in> fc"
        unfolding fc_def by simp
    qed
    show "\<And>i. i < n \<Longrightarrow>
         diag_mat (per_diag D f) ! i \<cdot>\<^sub>m 
           rank_1_proj (Matrix.col (per_col A f) i) =
         diag_mat D ! f i \<cdot>\<^sub>m rank_1_proj (Matrix.col A (f i))"
    proof-
      fix i
      assume "i < n"
      hence "f i < n" using \<open>f ` {..<n} = {..<n}\<close> by auto 
      have "Matrix.col (per_col A f) i = Matrix.col A (f i)"
        using per_col_col assms \<open>i < n\<close> by simp
      hence "rank_1_proj (Matrix.col (per_col A f) i) = 
        rank_1_proj (Matrix.col A (f i))"  by simp
      thus "diag_mat (per_diag D f) ! i \<cdot>\<^sub>m 
        rank_1_proj (Matrix.col (per_col A f) i) =
        diag_mat D ! f i \<cdot>\<^sub>m rank_1_proj (Matrix.col A (f i))" 
        using assms per_diag_diag_mat[of D] \<open>i < n\<close> \<open>f i < n\<close> by simp
    qed
  qed
  also have "... = A * D * (Complex_Matrix.adjoint A)" using sg by simp
  finally have "(per_col A f) * (per_diag D f) * 
    (Complex_Matrix.adjoint (per_col A f)) = 
    A * D * (Complex_Matrix.adjoint A)" .
  thus ?thesis by simp
qed

lemma sort_permutation:
  assumes "m = sort l"
  obtains f where "bij_betw f {..<length l} {..<length l} \<and> 
    (\<forall>i<length l. l ! f i = m ! i)"
proof -
  have "length l = length m" using assms by simp
   have "mset l = mset m" using assms by simp
  from this obtain p where "p permutes {..<length m}" "permute_list p l = m" 
    by (metis \<open>length l = length m\<close> mset_eq_permutation) note pprop = this
  have "bij_betw p {..<length l} {..<length l}" 
    using pprop \<open>length l = length m\<close>
    by (simp add: permutes_imp_bij)
  moreover have "\<forall>i<length l. l ! p i = m ! i" using pprop
    by (metis \<open>length l = length m\<close> permute_list_nth)
  ultimately have "\<exists>f. bij_betw f {..<length l} {..<length l} \<and> 
    (\<forall>i<length l. l ! f i = m ! i)" by auto
  thus ?thesis using that by auto
qed

lemma per_diag_sorted_Re:
  fixes B::"complex Matrix.mat"
  assumes "B\<in> carrier_mat n n"
  obtains f where "bij_betw f {..< n} {..< n} \<and> 
    map Re (diag_mat (per_diag B f)) = sort (map Re (diag_mat B))"
proof -
  define m where "m = sort (map Re (diag_mat B))"
  have "length m = length (map Re (diag_mat B))" unfolding m_def by simp
  also have "... = length (diag_mat B)" by simp
  also have "... = n" using assms unfolding diag_mat_def by simp
  finally have "length m = n" .
  from this obtain f where "bij_betw f {..<n} {..<n} \<and> 
    (\<forall>i<n. (map Re (diag_mat B)) ! f i = m ! i)" 
    using sort_permutation[of m "map Re (diag_mat B)"] m_def by auto
    note fprop = this
  have l: "length (diag_mat (per_diag B f)) = length m" 
      using per_diag_carrier assms \<open>length m = n\<close> unfolding diag_mat_def
      by (metis carrier_matD(1) length_map map_nth)
  have "map Re (diag_mat (per_diag B f)) = m" 
  proof (rule list_eq_iff_nth_eq[THEN iffD2], intro conjI)
    show "length (map Re (diag_mat (per_diag B f))) = length m" using l by simp
    have "\<forall>i<n. (map Re (diag_mat (per_diag B f)))!i = m!i"
    proof (intro allI impI)
      fix i
      assume "i< n"
      have "(map Re (diag_mat (per_diag B f)))!i = (map Re (diag_mat B))!(f i)"
      proof (rule per_diag_diag_mat_Re)
        show "B\<in> carrier_mat n n" using assms by simp
        show "i < n" using \<open>i < n\<close> .
        thus "f i < n" using fprop bij_betwE by blast
      qed
      also have "... = m!i" using fprop \<open>i < n\<close> by simp
      finally show "(map Re (diag_mat (per_diag B f)))!i = m!i" .
    qed 
    thus "\<forall>i<length (map Re (diag_mat (per_diag B f))). 
      (map Re (diag_mat (per_diag B f)))!i = m ! i" using l \<open>length m = n\<close> by simp
  qed 
  thus ?thesis using that fprop unfolding m_def by auto
qed

lemma bij_unitary_diag:
  fixes A::"complex Matrix.mat"
  assumes "unitary_diag A B U"
  and "A \<in> carrier_mat  n n"
  and "bij_betw f {..<n} {..<n}"
  and "0 < n"
shows "unitary_diag A (per_diag B f) (per_col U f)" 
proof (intro unitary_diagI)
  show "unitary (per_col U f)" using assms unitary_diagD(1) 
    unitary_diagD(3) per_col_unitary by (metis similar_mat_witD2(6))
  show "diagonal_mat (per_diag B f)" 
    using assms unitary_diagD(2) per_diag_diagonal
    by (metis similar_mat_witD2(5) unitary_diagD(1))
  have "A = U *  B * (Complex_Matrix.adjoint U)" using assms
    unitary_diagD similar_mat_witD2(3) unitary_diagD(1) by blast
  also have "... = (per_col U f) * (per_diag B f)
    * (Complex_Matrix.adjoint (per_col U f))" using assms per_col_mult_unitary
    by (meson similar_mat_witD2(5) similar_mat_witD2(6) unitary_diagD(1) 
        unitary_diagD(2) unitary_diagD(3))
  finally have eq: "A = per_col U f * per_diag B f * 
    Complex_Matrix.adjoint (per_col U f)" .
  show "similar_mat_wit A (per_diag B f) (per_col U f) 
    (Complex_Matrix.adjoint (per_col U f))" 
    unfolding similar_mat_wit_def Let_def
  proof (intro conjI)
    have "A\<in> carrier_mat n n" using assms by simp
    moreover have "per_diag B f \<in> carrier_mat n n" using assms unitary_diagD(1) 
      per_diag_carrier[of B]
      by (metis carrier_matD(1) carrier_matD(2) similar_mat_witD2(5))
    moreover have "per_col U f \<in> carrier_mat n n" using assms unitary_diagD(1)
      per_col_carrier[of U]
      by (metis similar_mat_witD2(6))
    moreover hence "Complex_Matrix.adjoint (per_col U f) \<in> carrier_mat n n"
      by (simp add: adjoint_dim) 
    ultimately show 
      "{A, per_diag B f, per_col U f, Complex_Matrix.adjoint (per_col U f)} \<subseteq>
      carrier_mat (dim_row A) (dim_row A)" by auto
    show "per_col U f * Complex_Matrix.adjoint (per_col U f) = 1\<^sub>m (dim_row A)"
      using \<open>Complex_Matrix.unitary (per_col U f)\<close> assms(2)
        \<open>per_col U f \<in> carrier_mat n n\<close> by auto
    show "Complex_Matrix.adjoint (per_col U f) * per_col U f = 1\<^sub>m (dim_row A)"
      using \<open>Complex_Matrix.unitary (per_col U f)\<close> assms 
        \<open>per_col U f \<in> carrier_mat n n\<close>  by auto
  qed (simp add: eq)
qed

lemma hermitian_real_diag_sorted:
  assumes "A \<in> carrier_mat n n"
  and "0 < n"
  and "hermitian A"
  obtains Bs Us where "real_diag_decomp A Bs Us \<and> sorted (map Re (diag_mat Bs))"
proof -
  obtain U1 B1 where "real_diag_decomp A B1 U1" 
    using hermitian_real_diag_decomp[of A] assms by auto note ubprop = this
  hence "B1 \<in> carrier_mat n n" using assms unfolding real_diag_decomp_def
    by (meson unitary_diag_carrier(1))
  from this obtain f where "bij_betw f {..< n} {..< n} \<and> 
      map Re (diag_mat (per_diag B1 f)) = sort (map Re (diag_mat B1))" 
    using per_diag_sorted_Re by auto note fprop = this
  define Bs where "Bs = per_diag B1 f"
  define Us where "Us = per_col U1 f"
  have "unitary_diag A Bs Us" unfolding Bs_def Us_def
  proof (rule bij_unitary_diag)
    show "unitary_diag A B1 U1" using ubprop unfolding real_diag_decomp_def 
      by simp
    show "A \<in> carrier_mat n n" using assms by simp
    show "bij_betw f {..<n} {..<n}" using fprop by simp
    show "0 < n" using assms by simp
  qed
  have "real_diag_decomp A Bs Us" unfolding real_diag_decomp_def 
  proof (simp add: \<open>unitary_diag A Bs Us\<close>)
    show "\<forall>i<dim_row Bs. Bs $$ (i, i) \<in> \<real>" unfolding Bs_def 
    proof (rule per_diag_real)  
      show br: "B1 \<in> carrier_mat (dim_row (per_diag B1 f)) 
        (dim_row (per_diag B1 f))"
        by (metis \<open>B1 \<in> carrier_mat n n\<close> carrier_matD(1) per_diag_carrier)
      thus "\<forall>i<dim_row (per_diag B1 f). B1 $$ (i, i) \<in> \<real>" using ubprop by auto
      show "bij_betw f {..<dim_row (per_diag B1 f)} 
        {..<dim_row (per_diag B1 f)}" using fprop
        by (metis br \<open>B1 \<in> carrier_mat n n\<close> carrier_matD(1)) 
    qed
  qed
  moreover have "sorted (map Re (diag_mat Bs))" using fprop unfolding Bs_def 
    by simp
  ultimately show ?thesis using that by simp
qed

section \<open>Commuting Hermitian families\<close>
text \<open>This part is devoted to the proof that a finite family of commuting Hermitian matrices
is simultaneously diagonalizable.\<close>

subsection \<open>Intermediate properties\<close>

lemma real_diag_decomp_mult_dbm_unit:
  assumes "A \<in> carrier_mat n n"
  and "real_diag_decomp A B U"
  and "B = diag_block_mat Bl"
  and "length Ul = length Bl"
  and "\<forall>i < length Bl. dim_col (Bl!i) = dim_row (Bl!i)"
  and "\<forall>i < length Bl. dim_row (Bl!i) = dim_row (Ul!i)"
  and "\<forall>i < length Bl. dim_col (Bl!i) = dim_col (Ul!i)"
  and "unitary (diag_block_mat Ul)"
  and "\<forall>i<length Ul. Ul ! i * Bl ! i = Bl ! i * Ul ! i" 
shows "real_diag_decomp A B (U * (diag_block_mat Ul))"
  unfolding real_diag_decomp_def
proof (intro conjI allI impI)
  have "B\<in> carrier_mat n n"
    by (meson assms(1) assms(2) real_diag_decompD(1) unitary_diag_carrier(1))
  have "dim_row (diag_block_mat Ul) = dim_row B" 
    using diag_block_mat_dim_row_cong assms by blast
  moreover have "dim_col (diag_block_mat Ul) = dim_col B" 
    using diag_block_mat_dim_col_cong assms by blast
  ultimately have "diag_block_mat Ul \<in> carrier_mat n n" using assms
    by (metis \<open>B \<in> carrier_mat n n\<close> carrier_matD(1) carrier_matD(2) 
        carrier_mat_triv) 
  define Uf where "Uf = U * (diag_block_mat Ul)"
  show "\<And>i. i < dim_row B \<Longrightarrow> B $$ (i, i) \<in> \<real>"
    using assms real_diag_decompD(2) \<open>B \<in> carrier_mat n n\<close> by auto
  show "unitary_diag A B Uf" unfolding unitary_diag_def
  proof
    show "diagonal_mat B" using assms real_diag_decompD(2)
      real_diag_decompD(1) unitary_diagD(2) by blast
    show "unitarily_equiv A B Uf" unfolding Uf_def
    proof (rule conjugate_eq_unitarily_equiv)
      show "A\<in> carrier_mat n n" using assms by simp
      show "unitarily_equiv A B U" using assms real_diag_decompD(1) 
        unfolding unitary_diag_def by simp
      show "diag_block_mat Ul \<in> carrier_mat n n"
        using \<open>diag_block_mat Ul \<in> carrier_mat n n\<close> .
      show "unitary (diag_block_mat Ul)" using assms by simp
      have  "mat_conj (diag_block_mat Ul)  (diag_block_mat Bl) = 
        diag_block_mat Bl" 
      proof (rule mat_conj_unit_commute)
        show "unitary (diag_block_mat Ul)" using \<open>unitary (diag_block_mat Ul)\<close> .
        show "diag_block_mat Bl \<in> carrier_mat n n" 
          using assms \<open>B \<in> carrier_mat n n\<close> by simp
        show "diag_block_mat Ul \<in> carrier_mat n n" 
          using \<open>diag_block_mat Ul \<in> carrier_mat n n\<close> .
        show "diag_block_mat Ul * diag_block_mat Bl = 
          diag_block_mat Bl * diag_block_mat Ul"
        proof (rule diag_block_mat_commute)
          show "length Ul = length Bl" using assms
            by simp
          show comm: "\<forall>i<length Ul. Ul ! i * Bl ! i = Bl ! i * Ul ! i" 
            using assms by simp
          show "\<forall>i<length Ul. dim_col (Ul ! i) = dim_row (Bl ! i)"
            using assms by presburger  
          thus "\<forall>i<length Ul. dim_col (Bl ! i) = dim_row (Ul ! i)"
            by (metis comm index_mult_mat(2) index_mult_mat(3))   
        qed
      qed
      thus "diag_block_mat Ul * B * 
        Complex_Matrix.adjoint (diag_block_mat Ul) = B" 
        using \<open>B = diag_block_mat Bl\<close> unfolding mat_conj_def by simp
    qed
  qed
qed

lemma real_diag_decomp_block_set:
  assumes "Als \<noteq> {}"
  and "0 < n"
  and "\<forall> Al \<in> Als. length Al = n"
  and "\<forall>i < n. \<forall> Al \<in> Als. dim_row (Al!i) = dim_col (Al!i)"
  and "\<forall>i < n. \<exists>U. \<forall> Al \<in> Als.  \<exists>B. real_diag_decomp (Al!i) B U"
shows "\<exists>Ul. (length Ul = n \<and> (\<forall>i <n. \<forall>Al \<in> Als. 
  (dim_row (Ul!i) = dim_row (Al!i) \<and> dim_col (Ul!i) = dim_col (Al!i)))\<and>
  (\<forall> Al \<in> Als. \<exists>Bl. (length Bl = n \<and> 
  real_diag_decomp (diag_block_mat Al) (diag_block_mat Bl) (diag_block_mat Ul))))"  
  using assms
proof (induct n arbitrary: Als)
  case 0
  then show ?case by simp
next
  case (Suc n)
  hence "\<exists>U. \<forall> Al \<in> Als.  \<exists>B. real_diag_decomp (Al!0) B U" by simp
  from this obtain U0 where "\<forall> Al \<in> Als.  \<exists>B. real_diag_decomp (Al!0) B U0" 
    by auto note u0 = this
  have u0_dim: "\<forall>Al\<in>Als. 
      dim_row ([U0] ! 0) = dim_row (Al ! 0) \<and> 
      dim_col ([U0] ! 0) = dim_col (Al ! 0)"
  proof (intro allI impI ballI)
    fix Al
    assume  "Al \<in> Als"
    have "[U0]!0 = U0" by simp
    have "\<exists>B. real_diag_decomp (Al!0) B U0" using u0 \<open>Al \<in> Als\<close> 
      by simp
    from this obtain B where "real_diag_decomp (Al!0) B U0" by auto
    moreover have "dim_row (Al!0) = dim_col (Al!0)" using \<open>Al\<in> Als\<close> Suc 
      by simp
    ultimately have "dim_row U0 = dim_row (Al!0)" 
      using unitary_diag_carrier(2)
      by (metis carrier_matD(1) carrier_matI real_diag_decompD(1))
    moreover have "dim_col U0 = dim_col (Al!0)" 
      using \<open>real_diag_decomp (Al!0) B U0\<close> \<open>dim_row (Al!0) = dim_col (Al!0)\<close>
      using real_diag_decompD(1) unitary_diag_carrier(2)
      by (metis carrier_matD(2) carrier_mat_triv)
    ultimately show "dim_row ([U0] ! 0) = dim_row (Al ! 0) \<and> 
      dim_col ([U0] ! 0) = dim_col (Al ! 0)"
      by simp
  qed
  show ?case
  proof (cases "n = 0")
    case True
    hence "\<forall> Al \<in> Als. diag_block_mat Al = Al!0" using Suc 
      by (simp add: diag_block_mat_length_1)
    have "\<forall> Al \<in> Als. \<exists>Bl. (length Bl = 1 \<and>
      real_diag_decomp (diag_block_mat Al) (diag_block_mat Bl) 
      (diag_block_mat [U0]))"
    proof 
      fix Al
      assume "Al \<in> Als"
      hence "\<exists>B. real_diag_decomp (Al!0) B U0" using u0 by simp
      from this obtain B where "real_diag_decomp (Al!0) B U0" by auto
      hence "real_diag_decomp (diag_block_mat Al) (diag_block_mat [B]) 
        (diag_block_mat [U0])"
        by (metis \<open>Al \<in> Als\<close> \<open>\<forall>Al\<in>Als. diag_block_mat Al = Al ! 0\<close> 
            diag_block_mat_singleton)
      moreover have "length [B] = 1" by simp
      ultimately show "\<exists>Bl. (length Bl = 1 \<and>
        real_diag_decomp (diag_block_mat Al) (diag_block_mat Bl) 
        (diag_block_mat [U0]))" 
        by blast
    qed
    moreover have "length [U0] = 1" by simp
    moreover have "\<forall>i<Suc n. \<forall>Al\<in>Als. 
      dim_row ([U0] ! i) = dim_row (Al ! i) \<and> 
      dim_col ([U0] ! i) = dim_col (Al ! i)"
      using u0_dim \<open>n = 0\<close> by simp
    ultimately have "length [U0] = Suc 0 \<and> 
      (\<forall>i<Suc n. \<forall>Al\<in>Als. dim_row ([U0] ! i) = dim_row (Al ! i) \<and> 
        dim_col ([U0] ! i) = dim_col (Al ! i)) \<and> 
      (\<forall>Al\<in>Als. \<exists>Bl. length Bl = Suc n \<and> real_diag_decomp 
        (diag_block_mat Al) (diag_block_mat Bl) (diag_block_mat [U0]))" 
      using \<open>n=0\<close> One_nat_def by metis
    thus ?thesis by (metis True) 
  next
    case False
    hence "0 < n" by simp
    define tAls where "tAls = tl `Als"
    have tex: "\<forall>tAl\<in> tAls. \<exists>Al \<in> Als. tAl = tl Al" unfolding tAls_def by auto
    have "\<exists>Ul. length Ul = n \<and> 
      (\<forall>i <n. \<forall>Al \<in> tAls. 
      (dim_row (Ul!i) = dim_row (Al!i) \<and> dim_col (Ul!i) = dim_col (Al!i)))\<and>
        (\<forall>Al\<in>tAls. \<exists>Bl. length Bl = n \<and> 
      real_diag_decomp (diag_block_mat Al) (diag_block_mat Bl) 
      (diag_block_mat Ul))" 
    proof (rule Suc(1))
      show "tAls \<noteq> {}" "0 < n" unfolding tAls_def by (auto simp add: \<open>0 < n\<close> Suc)
      show "\<forall>tAl\<in>tAls. length tAl = n"
        using Suc(4) tex by fastforce
      show "\<forall>i<n. \<exists>U. \<forall>Al\<in>tAls. \<exists>B. real_diag_decomp (Al ! i) B U"
      proof (intro allI impI)
        fix i
        assume "i < n"
        hence "\<exists>U. \<forall>Al\<in>Als. \<exists>B. real_diag_decomp (Al ! (Suc i)) B U" 
          using Suc Suc_mono by presburger
        from this obtain U where 
          tu: "\<forall>Al\<in>Als. \<exists>B. real_diag_decomp (Al ! (Suc i)) B U" by auto
        have "\<forall>tAl\<in>tAls. \<exists>B. real_diag_decomp (tAl ! i) B U"
        proof 
          fix tAl
          assume "tAl \<in> tAls"
          hence "\<exists>Al \<in> Als. tAl = tl Al" using tex by simp
          from this obtain Al where "Al \<in> Als" and "tAl = tl Al" by auto
          hence "tAl!i = Al!(Suc i)" by (simp add: Suc(4) \<open>i < n\<close> nth_tl) 
          moreover have "\<exists>B. real_diag_decomp (Al!(Suc i)) B U" 
            using tu \<open>Al \<in> Als\<close> by simp
          ultimately show "\<exists>B. real_diag_decomp (tAl ! i) B U" by simp
        qed
        thus "\<exists>U. \<forall>Al\<in>tAls. \<exists>B. real_diag_decomp (Al ! i) B U" by auto
      qed
      show "\<forall>i < n. \<forall>Al\<in>tAls.  dim_row (Al!i) = dim_col (Al!i)"
        by (metis Suc(5) \<open>\<forall>tAl\<in>tAls. length tAl = n\<close> not_less_eq nth_tl tex)
    qed
    from this obtain Ul where "length Ul = n" and 
      "\<forall>i <n. \<forall>Al \<in> tAls. 
        (dim_row (Ul!i) = dim_row (Al!i) \<and> dim_col (Ul!i) = dim_col (Al!i))"
      "(\<forall>Al\<in>tAls. \<exists>Bl. length Bl = n \<and> 
      real_diag_decomp (diag_block_mat Al) (diag_block_mat Bl) 
      (diag_block_mat Ul))" by auto note ulprop = this
    have "\<forall>Al\<in>Als. \<exists>Bl. length Bl = Suc n \<and> 
      real_diag_decomp (diag_block_mat Al) (diag_block_mat Bl) 
      (diag_block_mat (U0#Ul))" 
    proof
      fix Al
      assume "Al \<in> Als"
      hence "0 < length Al" using Suc by simp
      hence "Al = hd Al # (tl Al)" by simp
      have "\<exists>B. real_diag_decomp (Al!0) B U0" using u0 \<open>Al\<in> Als\<close> by simp
      from this obtain B0 where b0: "real_diag_decomp (Al!0) B0 U0" by auto
      hence "real_diag_decomp (hd Al) B0 U0"
        by (metis \<open>Al = hd Al # tl Al\<close> nth_Cons_0)
      have "tl Al \<in> tAls" using \<open>Al \<in> Als\<close> unfolding tAls_def by simp
      hence "\<exists>Bl. length Bl = n \<and> 
        real_diag_decomp (diag_block_mat (tl Al)) (diag_block_mat Bl) 
        (diag_block_mat Ul)" using ulprop by simp 
      from this obtain Bl where "length Bl = n" and 
        rl: "real_diag_decomp (diag_block_mat (tl Al)) (diag_block_mat Bl) 
        (diag_block_mat Ul)" by auto
      have "dim_row (diag_block_mat (tl Al)) = dim_col (diag_block_mat (tl Al))" 
        using Suc \<open>Al \<in> Als\<close> diag_block_mat_dim_row_col_eq
        by (metis (no_types, lifting) \<open>Al = hd Al # tl Al\<close> length_Cons lessI 
            less_trans_Suc nth_tl)
      moreover have "dim_row (Al ! 0) = dim_col (Al ! 0)" 
        using Suc \<open>Al \<in> Als\<close> by simp
      ultimately have "real_diag_decomp (diag_block_mat ((hd Al)#(tl Al))) 
        (diag_block_mat (B0#Bl)) (diag_block_mat (U0#Ul))" 
        using  four_block_real_diag_decomp[OF rl b0] diag_block_mat.simps(2)  
          real_diag_decomp_hermitian
        by (metis \<open>Al = hd Al # tl Al\<close> b0 four_block_real_diag_decomp nth_Cons_0 rl)
      moreover have "length (B0#Bl) = Suc n" using \<open>length Bl = n\<close> by simp
      ultimately show "\<exists>Bl. length Bl = Suc n \<and> 
      real_diag_decomp (diag_block_mat Al) (diag_block_mat Bl) 
      (diag_block_mat (U0#Ul))" using \<open>Al = hd Al # tl Al\<close> by metis
    qed
    moreover have "length (U0#Ul) = Suc n" using ulprop by simp
    moreover have "\<forall>i<Suc n. \<forall>Al\<in>Als. dim_row ((U0#Ul) ! i) = dim_row (Al ! i) \<and> 
      dim_col ((U0#Ul) ! i) = dim_col (Al ! i)"
    proof (intro allI impI ballI)
      fix i Al
      assume "i < Suc n" and "Al \<in> Als"
      show "dim_row ((U0 # Ul) ! i) = dim_row (Al ! i) \<and> 
        dim_col ((U0 # Ul) ! i) = dim_col (Al ! i)"
      proof (cases "i = 0")
        case True
        then show ?thesis using \<open>Al \<in> Als\<close> u0_dim by simp
      next
        case False
        hence "\<exists>j. i = Suc j" by (simp add: not0_implies_Suc)
        from this obtain j where "i = Suc j" by auto
        hence "(U0#Ul)!i = Ul!j" by simp
        have "tl Al \<in> tAls" using \<open>Al \<in> Als\<close> unfolding tAls_def by simp
        moreover have "Al!i = (tl Al)!j" using \<open>i = Suc j\<close>
          by (metis Suc.prems(3) Zero_not_Suc \<open>Al \<in> Als\<close> diag_block_mat.cases 
              list.sel(3) list.size(3) nth_Cons_Suc) 
        ultimately show ?thesis using \<open>(U0#Ul)!i = Ul!j\<close>
          by (metis Suc_less_SucD \<open>i < Suc n\<close> \<open>i = Suc j\<close> ulprop(2)) 
      qed
    qed
    ultimately show ?thesis by blast
  qed
qed

lemma real_diag_decomp_eq_comps_props:
  assumes "Ap\<in> carrier_mat n n"
  and "0 < n"
  and "real_diag_decomp Ap Bs Us \<and> sorted (map Re (diag_mat Bs))"
shows "Bs \<in> carrier_mat n n" "diagonal_mat Bs" "unitary Us"
  "Us \<in> carrier_mat n n" "diag_diff Bs (eq_comps (diag_mat Bs))"
  "eq_comps (diag_mat Bs) \<noteq> []" "diag_mat Bs \<noteq> []"
proof -
  show  "Bs \<in> carrier_mat n n" 
    using assms real_diag_decompD(1) unitary_diag_carrier(1) 
    by blast
  thus "diag_mat Bs \<noteq> []" using \<open>0 < n\<close> unfolding diag_mat_def by simp
  show "diagonal_mat Bs" using assms
    using real_diag_decompD(1) unitary_diagD(2) by blast
  show "unitary Us" 
    using  unitary_diagD(3) assms unfolding real_diag_decomp_def by auto
  show "Us \<in> carrier_mat n n" 
    using assms real_diag_decompD(1) unitary_diag_carrier(2)      
    by blast 
  define eqcl where "eqcl = eq_comps (diag_mat Bs)"
  show "diag_diff Bs eqcl" unfolding eqcl_def
  proof (rule cpx_sorted_diag_diff)
    show "Bs \<in> carrier_mat n n" using \<open>Bs \<in> carrier_mat n n\<close> .
    show "sorted (map Re (diag_mat Bs))" using assms by simp
    show "\<forall>i<n. Bs $$ (i, i) \<in> \<real>" 
      using assms real_diag_decompD(2) \<open>Bs \<in> carrier_mat n n\<close> by auto
  qed  
  show "eqcl \<noteq> []" using eq_comps_not_empty[of "diag_mat Bs"] 
    \<open>Bs \<in> carrier_mat n n\<close> assms 
    unfolding eqcl_def diag_mat_def
    by (simp add: assms)
qed

lemma commuting_conj_mat_set_props:
  fixes As::"'a::conjugatable_field Matrix.mat set" 
    and U::"'a Matrix.mat"
  assumes "finite As"
  and "card As \<le> i"
  and "\<forall>A\<in> As. hermitian A \<and> A\<in> carrier_mat n n"
  and "\<forall> A\<in> As. \<forall> B \<in> As. A*B = B*A"
  and "unitary U"
  and "U \<in> carrier_mat n n"
  and "CjA = (\<lambda>A2. mat_conj (Complex_Matrix.adjoint U) A2)`As"
shows "finite CjA" "card CjA \<le> i"
  "\<forall>A\<in> CjA. A\<in> carrier_mat n n \<and> hermitian A" 
  "\<forall> C1\<in> CjA. \<forall>C2\<in> CjA. C1*C2 = C2*C1"
proof -
  define Cj where "Cj = (\<lambda>A2. mat_conj (Complex_Matrix.adjoint U) A2)"
  have "CjA = Cj`As" using assms unfolding Cj_def by simp
  show "finite CjA"  using assms  by simp
  show "card CjA \<le> i"  
    using \<open>card As \<le> i\<close> \<open>finite As\<close> card_image_le dual_order.trans assms
     by blast
  show "\<forall>A\<in> CjA. A\<in> carrier_mat n n \<and> hermitian A" 
  proof(intro ballI conjI)
    fix A
    assume "A\<in> CjA"
    hence "\<exists>nA \<in> As. A = Cj nA" using assms unfolding Cj_def by auto
    from this obtain nA where "nA\<in> As" and "A = Cj nA" by auto
    have "hermitian nA" using assms \<open>nA \<in> As\<close> by auto
    thus "hermitian A"  
      using assms \<open>A = Cj nA\<close> hermitian_mat_conj'[of nA n U] \<open>nA\<in> As\<close> Cj_def
        mat_conj_adjoint by fastforce       
    show "A\<in> carrier_mat n n" using \<open>nA\<in> As\<close> \<open>A = Cj nA\<close> unfolding Cj_def
      by (metis \<open>hermitian A\<close> adjoint_dim_row assms(6) carrier_matD(2) 
          hermitian_square index_mult_mat(2) mat_conj_adjoint)
  qed
  show "\<forall> C1\<in> CjA. \<forall>C2\<in> CjA. C1*C2 = C2*C1"
  proof (intro ballI)
    fix C1 C2
    assume "C1 \<in> CjA" and "C2\<in> CjA"
    hence "\<exists> A1\<in> As. C1 = mat_conj (Complex_Matrix.adjoint U) A1" 
      using assms unfolding Cj_def by auto
    from this obtain A1 where "A1\<in> As" and
      "C1 = mat_conj (Complex_Matrix.adjoint U) A1" 
      by auto
    have "\<exists> A2\<in> As. C2 = mat_conj (Complex_Matrix.adjoint U) A2" 
      using \<open>C2\<in> CjA\<close> assms unfolding  Cj_def by auto
    from this obtain A2 where "A2\<in> As" and
      "C2 = mat_conj (Complex_Matrix.adjoint U) A2" 
      by auto
    have "mat_conj (Complex_Matrix.adjoint U) A1 * 
      mat_conj (Complex_Matrix.adjoint U) A2 =
      mat_conj (Complex_Matrix.adjoint U) A2 * 
      mat_conj (Complex_Matrix.adjoint U) A1"
    proof (rule mat_conj_commute)
      show "unitary U" using \<open>unitary U\<close> .
      show "A1\<in> carrier_mat n n" using \<open>A1\<in> As\<close> assms by simp
      show "A2\<in> carrier_mat n n" using \<open>A2\<in> As\<close> assms by simp
      show "U \<in> carrier_mat n n" using \<open>U \<in> carrier_mat n n\<close> .
      show "A1 * A2 = A2 * A1" using \<open>A1\<in> As\<close> \<open>A2\<in> As\<close> assms by simp
    qed
    thus "C1 * C2 = C2 * C1"
      using \<open>C1 = mat_conj (Complex_Matrix.adjoint U) A1\<close>
        \<open>C2 = mat_conj (Complex_Matrix.adjoint U) A2\<close>
      by simp
  qed
qed

lemma commute_extract_diag_block_eq:
  fixes Ap::"complex Matrix.mat"
  assumes "Ap\<in> carrier_mat n n"
  and "0 < n"
  and "real_diag_decomp Ap Bs Us \<and> sorted (map Re (diag_mat Bs))"
  and "finite Afp"
  and "card Afp \<le> i"
  and "\<forall>A\<in>Afp. hermitian A \<and> A \<in> carrier_mat n n"
  and "\<forall>A\<in>Afp. \<forall>B\<in>Afp. A * B = B * A"
  and "\<forall>A\<in> Afp. Ap * A = A * Ap"
  and "CjA = (\<lambda>A2. mat_conj (Complex_Matrix.adjoint Us) A2)`Afp"
  and "eqcl = eq_comps (diag_mat Bs)"
  shows  "\<forall>C \<in> CjA. C = diag_block_mat (extract_subdiags C eqcl)"
proof
  note ubprops = real_diag_decomp_eq_comps_props[OF assms(1) assms(2) assms(3)]
  note cjprops = commuting_conj_mat_set_props[OF assms(4) assms(5) assms(6) 
      assms(7) ubprops(3) ubprops(4) assms(9)]
  fix C
  assume "C\<in> CjA"
  hence "\<exists>Ac \<in> Afp. C = mat_conj (Complex_Matrix.adjoint Us) Ac" 
    using assms by auto
  from this obtain Ac where "Ac \<in> Afp" and 
    "C = mat_conj (Complex_Matrix.adjoint Us) Ac" by auto
  show "C = diag_block_mat (extract_subdiags C eqcl)" 
  proof (rule diag_compat_extract_subdiag)
    show "C \<in> carrier_mat n n" using cjprops \<open>C\<in> CjA\<close> by simp
    show  "diag_compat C eqcl" 
    proof (rule commute_diag_compat)
      show "Bs \<in> carrier_mat n n" using \<open>Bs \<in> carrier_mat n n\<close> .
      show "diag_diff Bs eqcl" using ubprops assms by simp
      show "diagonal_mat Bs" using \<open>diagonal_mat Bs\<close> .
      show "C \<in> carrier_mat n n" using \<open>C \<in> carrier_mat n n\<close> .
      have "Bs * (Complex_Matrix.adjoint Us * Ac * Us) = 
        Complex_Matrix.adjoint Us * Ac * Us * Bs"
      proof (rule unitarily_equiv_commute)
        show "unitarily_equiv Ap Bs Us" using assms real_diag_decompD(1)
          by simp
        show "Ap * Ac = Ac * Ap" using assms \<open>Ac \<in> Afp\<close> by simp
      qed
      thus "C * Bs = Bs * C" 
        using \<open>C = mat_conj (Complex_Matrix.adjoint Us) Ac\<close>
        by (metis mat_conj_adjoint)
    qed
  qed
qed

lemma extract_dbm_eq_component_commute:
  assumes "\<forall>C\<in>Cs. C = diag_block_mat (extract_subdiags C l)"
  and "\<forall>C1\<in>Cs. \<forall>C2\<in>Cs. C1 * C2 = C2 * C1"
  and "ExC = (\<lambda>A. extract_subdiags A l)`Cs"
  and "j < length l"
  and "Exi = (\<lambda>A. (A!j))` ExC"
  and "Al \<in> Exi"
  and "Bl\<in> Exi"
  shows "Al * Bl = Bl * Al" 
proof -
  define ncl where "ncl = length l"
  have "\<forall>Al\<in>ExC. length Al = ncl"
    by (simp add: assms extract_subdiags_length ncl_def)
  have "\<exists>Ea \<in> ExC. Al = Ea!j" using assms by auto
  from this obtain Ea where "Ea\<in> ExC" and "Al = Ea!j" by auto
  have "\<exists>Eb \<in> ExC. Bl = Eb!j" using assms by auto
  from this obtain Eb where "Eb\<in> ExC" and "Bl = Eb!j" by auto
  have "\<forall>j<ncl. \<forall>E\<in>ExC. E ! j \<in> carrier_mat (l ! j) (l ! j)"
    by (metis (no_types, lifting) assms(3) extract_subdiags_carrier 
        imageE ncl_def)
  hence "\<forall>i < ncl. \<forall>Al\<in>ExC. dim_row (Al ! i) = dim_col (Al ! i)"
    by (metis carrier_matD(1) carrier_matD(2))
  have "Ea!j * Eb!j = Eb!j * Ea!j" 
  proof (rule diag_block_mat_commute_comp)
    show "length Ea = length Eb"
      by (simp add: \<open>Ea \<in> ExC\<close> \<open>Eb \<in> ExC\<close> \<open>\<forall>Al\<in>ExC. length Al = ncl\<close>)
    show "j < length Ea"
      by (metis \<open>Eb \<in> ExC\<close> \<open>\<forall>Al\<in>ExC. length Al = ncl\<close> \<open>j < length l\<close> 
          ncl_def \<open>length Ea = length Eb\<close>)
    show "\<forall>i<length Ea. dim_row (Ea ! i) = dim_col (Ea ! i)"
      by (simp add: \<open>Ea \<in> ExC\<close> \<open>\<forall>Al\<in>ExC. length Al = ncl\<close> 
          \<open>\<forall>i < ncl. \<forall>Al\<in>ExC. dim_row (Al ! i) = dim_col (Al ! i)\<close>)
    show "\<forall>i<length Ea. dim_row (Ea ! i) = dim_row (Eb ! i)"
      by (metis \<open>Ea \<in> ExC\<close> \<open>Eb \<in> ExC\<close> \<open>\<forall>Al\<in>ExC. length Al = ncl\<close> 
          \<open>\<forall>j<ncl. \<forall>E\<in>ExC. E ! j \<in> carrier_mat (l ! j) (l ! j)\<close> 
          carrier_matD(1))
    show "\<forall>i<length Ea. dim_col (Ea ! i) = dim_col (Eb ! i)"
      using \<open>Ea \<in> ExC\<close> \<open>Eb \<in> ExC\<close> \<open>\<forall>Al\<in>ExC. length Al = ncl\<close> 
        \<open>\<forall>i<length Ea. dim_row (Ea ! i) = dim_row (Eb ! i)\<close> 
        \<open>\<forall>i<ncl. \<forall>Al\<in>ExC. dim_row (Al ! i) = dim_col (Al ! i)\<close> by auto
    have "\<exists>Cea \<in> Cs. Ea = extract_subdiags Cea l" 
      using \<open>Ea \<in> ExC\<close> assms by auto
    from this obtain Cea where "Cea\<in> Cs" and 
      "Ea = extract_subdiags Cea l" by auto
    hence cea: "Cea = diag_block_mat Ea"
      by (simp add: \<open>\<forall>C\<in>Cs. C = 
        diag_block_mat (extract_subdiags C l)\<close>)
    have "\<exists>Ceb \<in> Cs. Eb = extract_subdiags Ceb l" 
      using \<open>Eb \<in> ExC\<close> assms by auto
    from this obtain Ceb where "Ceb\<in> Cs" and 
      "Eb = extract_subdiags Ceb l" by auto
    hence "Ceb = diag_block_mat Eb"
      by (simp add: \<open>\<forall>C\<in>Cs. C = 
        diag_block_mat (extract_subdiags C l)\<close>)
    moreover have "Cea * Ceb = Ceb * Cea"
      by (simp add: \<open>Cea \<in> Cs\<close> \<open>Ceb \<in> Cs\<close> 
          \<open>\<forall>C1\<in>Cs. \<forall>C2\<in>Cs. C1 * C2 = C2 * C1\<close>)
    ultimately show "diag_block_mat Ea * diag_block_mat Eb = 
      diag_block_mat Eb * diag_block_mat Ea" using cea by simp
  qed
  thus "Al * Bl = Bl * Al" using \<open>Al = Ea!j\<close> \<open>Bl = Eb!j\<close> by simp
qed

lemma extract_comm_real_diag_decomp:
  fixes CjA::"complex Matrix.mat set"
  assumes "\<And>(Af::complex Matrix.mat set) n . finite Af \<Longrightarrow>
    card Af \<le> i \<Longrightarrow>
    Af \<noteq> {} \<Longrightarrow>
    (\<And>A. A \<in> Af \<Longrightarrow> A \<in> carrier_mat n n) \<Longrightarrow>
    0 < n \<Longrightarrow> (\<And>A. A \<in> Af \<Longrightarrow> hermitian A) \<Longrightarrow> 
    (\<And>A B. A \<in> Af \<Longrightarrow> B \<in> Af \<Longrightarrow> A * B = B * A) \<Longrightarrow> 
    \<exists>U. \<forall>A\<in>Af. \<exists>B. real_diag_decomp A B U"
  and "finite CjA"
  and "CjA \<noteq> {}"
  and "card CjA \<le> i"
  and "\<forall>C\<in>CjA. C = diag_block_mat (extract_subdiags C eqcl)"
  and "\<forall>C1\<in>CjA. \<forall>C2\<in>CjA. C1 * C2 = C2 * C1"
  and "Exc = (\<lambda>A. extract_subdiags A eqcl)`CjA"
  and "\<forall> E\<in> Exc. list_all (\<lambda>B. 0 < dim_row B \<and> hermitian B) E"
  and "\<forall>i < length eqcl. 0 < eqcl!i"
  shows "\<forall>i<length eqcl. \<exists>U. \<forall>Al\<in>Exc. \<exists>B. real_diag_decomp (Al ! i) B U"
proof (intro allI impI)
  define ncl where "ncl = length eqcl"
  fix j
  assume "j < ncl"
  define Exi where "Exi = (\<lambda>l. l!j)`Exc"
  have "finite Exi" using assms unfolding Exi_def by simp
  have "card Exi \<le> i" using assms unfolding Exi_def
    by (metis card_image_le image_image le_trans)
  have exfl: "\<forall>Ej \<in> Exi. \<exists>Fj \<in> CjA. Ej = (extract_subdiags Fj eqcl)!j"
  proof
    fix Ej
    assume "Ej \<in> Exi"
    hence "\<exists>El \<in> Exc. Ej = El!j" unfolding Exi_def by auto
    from this obtain El where "El \<in> Exc" and "Ej = El!j" by auto
    hence "\<exists>Fl \<in> CjA. El = extract_subdiags Fl eqcl" 
      using assms by auto
    from this obtain Fl where "Fl \<in> CjA" and 
      "El = extract_subdiags Fl eqcl" by auto
    thus "\<exists>Fj \<in> CjA. Ej = (extract_subdiags Fj eqcl)!j" using \<open>Ej = El!j\<close> 
      by auto
  qed
  have "\<exists>U. \<forall>Al\<in>Exi. \<exists>B. real_diag_decomp (Al) B U" 
  proof (rule assms(1))
    show "finite Exi" using \<open>finite Exi\<close> .
    show "card Exi \<le> i" using \<open>card Exi <= i\<close> .
    show "Exi \<noteq> {}" using \<open>CjA \<noteq> {}\<close> using assms unfolding Exi_def by auto
    show "0 < eqcl!j" using \<open>j < ncl\<close> ncl_def assms by simp
    show "\<And>Al. Al \<in> Exi \<Longrightarrow> Al \<in> carrier_mat (eqcl ! j) (eqcl ! j)" 
    proof -
      fix Al
      assume "Al \<in> Exi"              
      hence "\<exists>Fl \<in> CjA. Al = (extract_subdiags Fl eqcl)!j" using exfl 
        by simp
      from this obtain Fl where "Fl \<in> CjA" and 
        "Al = (extract_subdiags Fl eqcl)!j" by auto
      thus "Al \<in> carrier_mat (eqcl ! j) (eqcl ! j)"
        using extract_subdiags_carrier[of j eqcl] \<open>j < ncl\<close> 
        unfolding Exi_def ncl_def by simp
    qed
    show "\<And>Al. Al \<in> Exi \<Longrightarrow> hermitian Al"
    proof -
      fix Al 
      assume "Al\<in> Exi"
      hence "\<exists>El \<in> Exc. Al = El!j" unfolding Exi_def by auto
      from this obtain El where "El \<in> Exc" and "Al = El!j" by auto
      thus "hermitian Al" using assms \<open>j < ncl\<close> ncl_def
        by (metis (no_types, lifting) extract_subdiags_length image_iff 
            list_all_length) 
    qed
    show "\<And>Al Bl. Al \<in> Exi \<Longrightarrow> Bl \<in> Exi \<Longrightarrow> Al * Bl = Bl * Al" 
    proof -
      fix Al Bl
      assume "Al \<in> Exi" and "Bl \<in> Exi"
      show "Al*Bl = Bl * Al" 
      proof (rule extract_dbm_eq_component_commute[of CjA eqcl])
        show "Al \<in> Exi" using \<open>Al \<in> Exi\<close> .
        show "Bl \<in> Exi" using \<open>Bl \<in> Exi\<close> .
        show "\<forall>C\<in>CjA. C = diag_block_mat (extract_subdiags C eqcl)"
          using \<open>\<forall>C\<in>CjA. C = diag_block_mat (extract_subdiags C eqcl)\<close> .
        show "\<forall>C1\<in>CjA. \<forall>C2\<in>CjA. C1 * C2 = C2 * C1" 
          using \<open>\<forall>C1\<in>CjA. \<forall>C2\<in>CjA. C1 * C2 = C2 * C1\<close> .
        show "j < length eqcl" using \<open>j < ncl\<close> ncl_def by simp
        show "Exi = (\<lambda>A. A ! j) ` Exc" using Exi_def by simp
        show "Exc = (\<lambda>A. extract_subdiags A eqcl) ` CjA" 
          using assms by simp
      qed
    qed
  qed
  thus "\<exists>U. \<forall>Al\<in>Exc. \<exists>B. real_diag_decomp (Al ! j) B U" unfolding Exi_def
    by simp
qed

subsection \<open>The main result\<close>

theorem commuting_hermitian_family_diag:
  fixes Af::"complex Matrix.mat set"
  assumes "finite Af"
  and "Af \<noteq> {}"
  and "\<And>A. A\<in> Af \<Longrightarrow> A\<in> carrier_mat n n"
  and "0 < n"
  and "\<And>A. A \<in> Af \<Longrightarrow> hermitian A"
  and "\<And>A B. A \<in> Af \<Longrightarrow> B\<in> Af \<Longrightarrow> A * B = B * A"
shows "\<exists> U. \<forall> A\<in> Af. \<exists>B. real_diag_decomp A B U" using assms
proof -
  define i where "i = card Af"
  have "card Af \<le> i"
    by (simp add: i_def)
  from assms(1) this assms(2-) show ?thesis
  proof (induct i arbitrary: Af n)
    case 0
    then have "Af = {}" by simp
    then show ?case using 0 by simp
  next
    case (Suc i)
    hence "\<exists> A. A\<in> Af" by blast
    from this obtain Ap where "Ap \<in> Af" by auto
    define Afp where "Afp = Af - {Ap}"
    have "finite Afp" using Suc unfolding Afp_def by simp
    have "card Afp \<le> i" using \<open>card Af \<le> Suc i\<close> \<open>Ap \<in> Af\<close> 
      unfolding Afp_def by simp
    have "\<forall>A\<in>Afp. hermitian A \<and> A \<in> carrier_mat n n" using Suc
      by (metis Afp_def Diff_subset subset_iff)
    have "\<forall>A\<in>Afp. \<forall>B\<in>Afp. A * B = B * A" using Suc 
      by (metis Afp_def Diff_subset subset_iff)
    have "\<forall>A\<in> Afp. Ap * A = A * Ap" using Suc
      by (simp add: Afp_def \<open>Ap \<in> Af\<close>)
    have "hermitian Ap" "Ap\<in> carrier_mat n n" "0 < n" using \<open>Ap \<in> Af\<close> Suc by auto
    from this obtain Bs Us where rd: "real_diag_decomp Ap Bs Us \<and> 
      sorted (map Re (diag_mat Bs))"
      using hermitian_real_diag_sorted[of Ap] by auto note ub = this
    note ubprops = real_diag_decomp_eq_comps_props[OF \<open>Ap \<in> carrier_mat n n\<close> \<open>0 < n\<close> ub]   
    define eqcl where "eqcl = eq_comps (diag_mat Bs)"
    have "diag_diff Bs eqcl" using ubprops unfolding eqcl_def by simp
    have "eqcl \<noteq> []" using ubprops unfolding eqcl_def by simp
    hence "eqcl = hd eqcl # (tl eqcl)" by simp
    define esubB where "esubB = extract_subdiags Bs eqcl"
    have ebcar: "\<forall>i < length esubB. esubB ! i \<in> carrier_mat (eqcl!i) (eqcl!i)" 
      using extract_subdiags_carrier[of _ eqcl Bs]
      by (simp add: esubB_def extract_subdiags_length)
    have "Bs = diag_block_mat esubB" unfolding esubB_def eqcl_def
    proof (rule diagonal_extract_eq)
      show "Bs \<in> carrier_mat n n" using \<open>Bs \<in> carrier_mat n n\<close> .
      show "diagonal_mat Bs" using ubprops real_diag_decompD(2)
          real_diag_decompD(1) unitary_diagD(2) by blast
    qed
    show ?case
    proof (cases "Afp = {}")
      case True
      hence "Af = {Ap}" using \<open>Afp = Af - {Ap}\<close>
        by (simp add: Suc(4) subset_singleton_iff)     
      then show ?thesis using rd \<open>Af = {Ap}\<close> by auto 
    next
      case False   
      define Cj where "Cj = (\<lambda>A2. mat_conj (Complex_Matrix.adjoint Us) A2)"
      define CjA where "CjA = Cj`Afp"
      have "CjA = (\<lambda>A2. (mat_conj (Complex_Matrix.adjoint Us) A2)) ` Afp" 
        using CjA_def Cj_def by simp
      note cjprops = commuting_conj_mat_set_props[OF \<open>finite Afp\<close> \<open>card Afp \<le> i\<close>
        \<open>\<forall>A\<in>Afp. hermitian A \<and> A \<in> carrier_mat n n\<close> 
        \<open>\<forall>A\<in>Afp. \<forall>B\<in>Afp. A * B = B * A\<close>
        \<open>unitary Us\<close> \<open>Us \<in> carrier_mat n n\<close>
        \<open>CjA = (\<lambda>A2. mat_conj (Complex_Matrix.adjoint Us) A2) ` Afp\<close>]    
      have "\<forall>C \<in> CjA. C = diag_block_mat (extract_subdiags C eqcl)" 
      proof (rule commute_extract_diag_block_eq[OF \<open>Ap\<in> carrier_mat n n\<close> 
            \<open>0 < n\<close> rd \<open>finite Afp\<close> _ 
            \<open>\<forall>A\<in>Afp. hermitian A \<and> A \<in> carrier_mat n n\<close>], 
            auto simp add: eqcl_def CjA_def Cj_def)
        show "\<And>A B. A \<in> Afp \<Longrightarrow> B \<in> Afp \<Longrightarrow> A * B = B * A"
          by (simp add: \<open>\<forall>A\<in>Afp. \<forall>B\<in>Afp. A * B = B * A\<close>)
        show "\<And>A. A \<in> Afp \<Longrightarrow> Ap * A = A * Ap" 
          using \<open>\<forall> A \<in> Afp. Ap * A = A * Ap\<close> by simp
      qed
      define Ex where "Ex = (\<lambda>A. extract_subdiags A eqcl)`CjA"
      have "finite Ex" using \<open>finite CjA\<close> unfolding Ex_def by simp
      have "Ex \<noteq> {}" using False unfolding Ex_def CjA_def by simp
      have "card Ex \<le> i" using \<open>card CjA \<le> i\<close> unfolding Ex_def
        by (metis \<open>finite CjA\<close> basic_trans_rules(23) card_image_le)
      have exall: "\<forall> E\<in> Ex. list_all (\<lambda>B. 0 < dim_row B \<and> hermitian B) E"
      proof
        fix E
        assume "E\<in> Ex"
        hence "\<exists>nA \<in> CjA. E = extract_subdiags nA eqcl" unfolding Ex_def by auto
        from this obtain nA where "nA\<in> CjA" and "E = extract_subdiags nA eqcl" 
          by auto
        have "list_all (\<lambda>B. 0 < dim_row B \<and> hermitian B) 
          (extract_subdiags nA eqcl)"
        proof (rule hermitian_extract_subdiags)
          show "hermitian nA" using \<open>\<forall>A\<in> CjA. A \<in> carrier_mat n n \<and> hermitian A\<close> 
              \<open>nA\<in> CjA\<close> by simp
          show "list_all ((<) 0) eqcl" unfolding eqcl_def
            by (metis \<open>eqcl \<noteq> []\<close> eq_comps.simps(1) eq_comps_gt_0 eqcl_def)
          show "sum_list eqcl \<le> dim_row nA" 
            using \<open>\<forall>A\<in> CjA. A \<in> carrier_mat n n \<and> hermitian A\<close> 
              \<open>nA\<in> CjA\<close> unfolding eqcl_def
            by (metis \<open>Bs \<in> carrier_mat n n\<close> carrier_matD(1) 
                eq_comp_sum_diag_mat le_refl)
        qed
        thus "list_all (\<lambda>B. 0 < dim_row B \<and> hermitian B) E" 
          using \<open>E = extract_subdiags nA eqcl\<close> by simp
      qed      
      define ncl where "ncl = length eqcl"
      have "\<forall>j < ncl. \<forall>E \<in> Ex. E!j \<in> carrier_mat (eqcl!j) (eqcl!j)"
      proof (intro allI impI ballI)
        fix E j
        assume "j < ncl" and "E \<in> Ex"
        thus "E ! j \<in> carrier_mat (eqcl ! j) (eqcl ! j)" unfolding Ex_def
          using extract_subdiags_carrier ncl_def by blast
      qed
      have "\<exists>Ul. (length Ul = ncl \<and>
        (\<forall>i <ncl. \<forall>Al \<in> Ex. 
        (dim_row (Ul!i) = dim_row (Al!i) \<and> dim_col (Ul!i) = dim_col (Al!i)))\<and>
        (\<forall> Al \<in> Ex. \<exists>Bl. (length Bl = ncl \<and> 
        real_diag_decomp (diag_block_mat Al) (diag_block_mat Bl) 
        (diag_block_mat Ul))))" 
      proof (rule real_diag_decomp_block_set)
        show "Ex \<noteq> {}" using \<open>Afp \<noteq> {}\<close> unfolding Ex_def CjA_def by auto
        show "0 < ncl" unfolding ncl_def using \<open>eqcl \<noteq>[]\<close> by simp
        show "\<forall>Al\<in>Ex. length Al = ncl" unfolding ncl_def Ex_def
          by (simp add: extract_subdiags_length)
        show "\<forall>i<ncl. \<forall>Al\<in>Ex. dim_row (Al ! i) = dim_col (Al ! i)"
        proof (intro allI impI ballI)
          fix i Al
          assume "i < ncl" and "Al \<in> Ex"
          thus "dim_row (Al ! i) = dim_col (Al ! i)" using exall
            by (metis (mono_tags, lifting) \<open>\<forall>Al\<in>Ex. length Al = ncl\<close> 
                carrier_matD(2) hermitian_square list_all_length)
        qed
        show " \<forall>i<ncl. \<exists>U. \<forall>Al\<in>Ex. \<exists>B. real_diag_decomp (Al ! i) B U" unfolding ncl_def 
        proof (rule extract_comm_real_diag_decomp[of i CjA, OF Suc(1)], 
            auto simp add: exall Ex_def)
          show "finite CjA" using \<open>finite CjA\<close> .
          show "card CjA \<le> i" using \<open>card CjA \<le> i\<close> .
          show "\<And>C. C \<in> CjA \<Longrightarrow> C = diag_block_mat (extract_subdiags C eqcl)"
            using \<open>\<forall>C \<in> CjA. C = diag_block_mat (extract_subdiags C eqcl)\<close> by simp
          show "\<And>C1 C2. C1 \<in> CjA \<Longrightarrow> C2 \<in> CjA \<Longrightarrow> C1 * C2 = C2 * C1" 
            using cjprops by simp
          show "\<And>i. i < length eqcl \<Longrightarrow> 0 < eqcl!i" 
          proof -
            fix il
            assume "il < length eqcl"
            thus "0 < eqcl!il" using eq_comps_gt_0[OF \<open>diag_mat Bs \<noteq> []\<close>]
                list_all_length[of "(<) 0" "eq_comps (diag_mat Bs)"] 
              unfolding eqcl_def by simp 
          qed
          show "CjA = {} \<Longrightarrow> False" by (simp add: CjA_def False)
        qed
      qed
      from this obtain Ul where "length Ul = ncl" and 
        dimul: "(\<forall>i <ncl. \<forall>Al \<in> Ex. 
        (dim_row (Ul!i) = dim_row (Al!i) \<and> dim_col (Ul!i) = dim_col (Al!i)))" and
        ul: "\<forall> Al \<in> Ex. \<exists>Bl. (length Bl = ncl \<and> 
          real_diag_decomp (diag_block_mat Al) (diag_block_mat Bl) 
          (diag_block_mat Ul))" 
        by auto
      define Uf where "Uf = Us * (diag_block_mat Ul)"
      have afp:"\<forall>A \<in> Afp. \<exists>Bl. real_diag_decomp A (diag_block_mat Bl) Uf"
      proof
        fix A
        assume "A\<in> Afp"
        define Ca where "Ca = mat_conj (Complex_Matrix.adjoint Us) A"
        define Eca where "Eca = extract_subdiags Ca eqcl"
        have "Ca \<in> CjA" using \<open>A\<in> Afp\<close>
          unfolding Ca_def CjA_def Cj_def by simp
        hence "Ca = diag_block_mat Eca" unfolding Eca_def
          using \<open>\<forall>C\<in> CjA. C = diag_block_mat (extract_subdiags C eqcl)\<close> by simp
        have "Eca \<in> Ex" unfolding Ex_def Eca_def using \<open>Ca \<in> CjA\<close> by simp
        hence "\<exists>Bl. (length Bl = ncl \<and> 
          real_diag_decomp (diag_block_mat Eca) (diag_block_mat Bl) 
          (diag_block_mat Ul))" using ul by simp
        from this obtain Ecb where "length Ecb = ncl" and
          "real_diag_decomp (diag_block_mat Eca) (diag_block_mat Ecb) 
          (diag_block_mat Ul)" by auto
        hence "real_diag_decomp Ca (diag_block_mat Ecb) 
          (diag_block_mat Ul)" using \<open>Ca = diag_block_mat Eca\<close> by simp
        have "real_diag_decomp A (diag_block_mat Ecb) Uf" unfolding Uf_def
        proof (rule unitary_conjugate_real_diag_decomp)
          show "A\<in> carrier_mat n n" using \<open>A\<in> Afp\<close> unfolding Afp_def
            by (simp add: Suc(5))
          show "Us \<in> carrier_mat n n" using \<open>Us \<in> carrier_mat n n\<close> .
          show "unitary Us" using \<open>unitary Us\<close> .
          show "real_diag_decomp (mat_conj (Complex_Matrix.adjoint Us) A) 
            (diag_block_mat Ecb) (diag_block_mat Ul)"
            using \<open>real_diag_decomp Ca (diag_block_mat Ecb) 
              (diag_block_mat Ul)\<close> unfolding Ca_def by simp
        qed
        thus "\<exists>Bl. real_diag_decomp A (diag_block_mat Bl) Uf" by blast
      qed
      have "real_diag_decomp Ap Bs Uf" unfolding Uf_def
      proof (rule real_diag_decomp_mult_dbm_unit)
        show "Ap\<in> carrier_mat n n" using \<open>Ap\<in> carrier_mat n n\<close> .
        show "real_diag_decomp Ap Bs Us" using ub by simp
        show "Bs = diag_block_mat esubB" using \<open>Bs = diag_block_mat esubB\<close> .
        show "length Ul = length esubB" using \<open>length Ul = ncl\<close>
          by (simp add: esubB_def extract_subdiags_length ncl_def) 
        show "\<forall>i<length esubB. dim_col (esubB ! i) = dim_row (esubB ! i)"
          by (metis carrier_matD(1) carrier_matD(2) ebcar)
        have "length esubB = ncl" using \<open>length Ul = length esubB\<close> 
              \<open>length Ul = ncl\<close> ncl_def by auto
        show roweq:"\<forall>i<length esubB. dim_row (esubB ! i) = dim_row (Ul ! i)" 
          using ebcar dimul \<open>length esubB = ncl\<close>  \<open>Ex\<noteq> {}\<close>
            \<open>\<forall>j < ncl. \<forall>E \<in> Ex. E!j \<in> carrier_mat (eqcl!j) (eqcl!j)\<close>           
          by (metis all_not_in_conv carrier_matD(1))        
        show coleq:"\<forall>i<length esubB. dim_col (esubB ! i) = dim_col (Ul ! i)"
          using ebcar dimul \<open>length esubB = ncl\<close>  \<open>Ex\<noteq> {}\<close>
            \<open>\<forall>j < ncl. \<forall>E \<in> Ex. E!j \<in> carrier_mat (eqcl!j) (eqcl!j)\<close>           
          by (metis all_not_in_conv carrier_matD(2))
        show "unitary (diag_block_mat Ul)" using ul
          by (metis CjA_def False all_not_in_conv image_is_empty Ex_def 
              real_diag_decompD(1) unitary_diagD(3))  
        show "\<forall>i<length Ul. Ul ! i * esubB ! i = esubB ! i * Ul ! i"
        proof (intro allI impI)
          fix i
          assume "i < length Ul"
          show "Ul ! i * esubB ! i = esubB ! i * Ul ! i" 
            unfolding esubB_def eqcl_def 
          proof (rule extract_subdiags_comp_commute[symmetric])
            show "diagonal_mat Bs" using \<open>diagonal_mat Bs\<close> .
            show "Bs\<in> carrier_mat n n" using \<open>Bs \<in> carrier_mat n n\<close> .
            show "0 < n" using \<open>0 < n\<close> .
            show "i < length (eq_comps (diag_mat Bs))" 
              using \<open>i < length Ul\<close> \<open>length Ul = length esubB\<close> 
                extract_subdiags_length 
              unfolding esubB_def eqcl_def by metis
            show "Ul ! i \<in> carrier_mat (eq_comps (diag_mat Bs) ! i) 
              (eq_comps (diag_mat Bs) ! i)"
              using dimul \<open>\<forall>j < ncl. \<forall>E \<in> Ex. E!j \<in> carrier_mat (eqcl!j) (eqcl!j)\<close> 
              \<open>Ex\<noteq> {}\<close> unfolding ncl_def eqcl_def
              by (metis coleq roweq 
                  \<open>\<forall>i<length esubB. dim_col (esubB ! i) = dim_row (esubB ! i)\<close>  
                  \<open>i < length Ul\<close> \<open>length Ul = length esubB\<close> carrier_matD(2) 
                  carrier_matI ebcar eqcl_def)
          qed
        qed
      qed
      hence "\<exists>B. real_diag_decomp Ap B Uf" by blast
      hence "\<forall> A\<in> Af. \<exists>B. real_diag_decomp A B Uf" using afp 
        unfolding Afp_def by auto
      thus "\<exists>U. \<forall>A\<in>Af. \<exists>B. real_diag_decomp A B U" by blast
    qed
  qed
qed

end