section {* Matrices\label{sec.mat} *}

theory Matrices
imports
  Main
  Determinants_extension 
begin

text{* This theory contains a number of notions and results about matrices, in
   particular the adjugate matrix and its fundamental property. *}

(* ------------------------------------------------------------------------- *)
subsection {* Minors *}
(* ------------------------------------------------------------------------- *)

text{* Kronecker - Delta *}
definition "\<delta> i j = (if i = j then 1 else 0)"

lemma delta_comm: "\<delta> i j = \<delta> j i"
 by(simp add: \<delta>_def)

text{* unit vector *}
definition "e i = (\<chi> j. \<delta> i j)"

text{* the minor-matrix *}
definition "minorM A i j =
  (\<chi> k l. if k = i \<and> l = j then 1 else
          if k = i \<or> l = j then 0 else
          A$k$l                         
  )"

lemma minorM_rows:
  fixes A :: "'a::comm_ring_1^'n^'n" and i j k :: 'n
  assumes "k \<noteq> i"
  shows "row i (minorM A i j) = e j"
        "row k (minorM A i j) = (\<chi> c. if c = j then 0 else (row k A) $ c)"
proof-
  show "row i (minorM A i j) = e j"
  by(simp_all add: minorM_def row_def e_def \<delta>_def vec_eq_iff)
next
  { fix l :: 'n
    have "(row k (minorM A i j)) $ l = (\<chi> c. if c = j then 0 else (row k A) $ c) $ l"
    proof cases
      assume caseass: "l = j"
      hence "(row k (minorM A i j)) $ l = 0"
        unfolding row_def minorM_def using assms by auto
      thus ?thesis
        using caseass by simp
    next
      assume caseass: "l \<noteq> j"
      hence "(row k (minorM A i j)) $ l = (row k A) $ l"
        unfolding row_def minorM_def using assms by simp
      thus ?thesis using caseass
        by simp
    qed
  }
  thus "row k (minorM A i j) = (\<chi> c. if c = j then 0 else (row k A) $ c)" 
    unfolding vec_eq_iff minorM_def by force 
qed

text{* more general than minorM\_zeros below *}
lemma minorM_eq:
  fixes A B :: "'a::comm_ring_1^'n^'n" and i j :: 'n
  assumes "\<And> k l. k \<noteq> i \<longrightarrow> l \<noteq> j \<longrightarrow> ( A $ k $ l ) = ( B $ k $ l )"
  shows "minorM A i j = minorM B i j"
proof-
  { fix k l :: 'n
    have "(minorM A i j) $ k $ l = (minorM B i j) $ k $ l"
    proof cases
      assume "k = i \<or> l = j"
      thus ?thesis
        unfolding minorM_def by simp
    next
      assume "\<not> ( k = i \<or> l = j)"
      thus ?thesis 
        using assms unfolding minorM_def by auto
    qed }
  thus ?thesis unfolding vec_eq_iff
    by blast
qed

lemma minorM_zeros:
  fixes A :: "'a::comm_ring_1^'n^'n" and i j :: 'n
  assumes "row i A = e j" "column j A = e i"
  shows "A = minorM A i j"
proof-
  { fix k l :: 'n
    have "A $ k $ l = (minorM A i j) $ k $ l"
    proof cases
      assume caseass: "k = i \<and> l = j"
      then have "A $ k $ l = 1"
        using assms e_def \<delta>_def row_def 
        by (metis vec_lambda_beta vec_nth_inverse)
      then show ?thesis
        using caseass minorM_def[of A i j] 
        by auto
    next
      assume caseass: "\<not> (k = i \<and> l = j)"
      show ?thesis
      proof cases
        assume caseass2: "k = i \<or> l = j"
        then have "(minorM A i j) $ k $ l = 0" 
          using caseass minorM_def[of A i j] by auto
        also have "A $ k $ l = 0"
          apply(cases "k = i")
          apply(metis vec_lambda_beta assms(1) e_def \<delta>_def caseass row_def[of i A]) 
          apply(metis (no_types) \<delta>_def assms(2) caseass2 column_def e_def vec_lambda_beta)
          done
        finally show ?thesis 
          by auto
      next
        assume caseass2: "\<not> (k = i \<or> l = j)"
        thus ?thesis
          using caseass minorM_def[of A i j] by auto
      qed
    qed
  }
  thus ?thesis 
    unfolding vec_eq_iff by fast
qed

(* ------------------------------------------------------------------------- *)
subsection {* Cofactors *}
(* ------------------------------------------------------------------------- *)
  
text{* the cofactors of A *}
definition "cofactor A i j = det (minorM A i j)"

text{* the cofactor-matrix *}
definition "cofactorM A = (\<chi> i j. cofactor A i j)"

text{* the number of rows in A (except the i-th row) where the j-th element different from 0 *}
definition "nonzerorows A i j = card { k . k \<noteq> i \<and> ( A $ k $ j ) \<noteq> 0 }"

lemma aux_det_minorM_row:
  fixes B :: "'a::comm_ring_1^'n^'n" and i j :: 'n
  assumes "row i B = e j"
  shows "det B = det (minorM B i j)"
proof-
  { fix n::nat
    have "\<forall> (B::'a^'n^'n) i j . nonzerorows B i j = n \<longrightarrow> row i B = e j
      \<longrightarrow> det B = det (minorM B i j)"
    proof (induct n)
      case 0
      { fix B :: "'a^'n^'n" and i j 
        let ?nzB = "{ k . k \<noteq> i \<and> B $ k $ j \<noteq> 0 }"
        assume caseass: "nonzerorows B i j = 0" "row i B = e j"
        hence "\<forall> k. k \<noteq> i \<longrightarrow> (B $ k $ j) = 0" 
          using nonzerorows_def[of B i j] by auto
        then have "column j B = e i"
          by(simp add: column_def[of j B] vec_eq_iff)
            (metis \<delta>_def caseass(2) e_def row_def vec_lambda_beta)
        hence "B = (minorM B i j)"
          using caseass minorM_zeros[of i B j] by blast } 
      thus ?case by force
    next
      case (Suc n)
      { txt{* Suc.hyps is @{term "\<forall> B i j. nonzerorows B i j = n \<longrightarrow> row i B = e j
          \<longrightarrow> det B = det (minorM B i j)"} *}
        fix B:: "'a^'n^'n" and i j 
        let ?nzB = "{ k . k \<noteq> i \<and> B $ k $ j \<noteq> 0 }"
        assume caseass: "nonzerorows B i j = Suc n" "row i B = e j"
        hence "card ?nzB \<noteq> 0" 
          using nonzerorows_def[of B i j] by simp
        then obtain r where rcond: "r \<noteq> i \<and> ( B $ r $ j ) \<noteq> 0"
          using caseass by auto
        hence "r \<noteq> i"
          by auto

        let ?B' = "(\<chi> l. if l = r then row r B + (- (B $ r $ j)) *s row i B else row l B)"

        have "nonzerorows ?B' i j = n"
        proof-
          let ?nzB' = "{ k . k \<noteq> i \<and> ?B'$ k $ j \<noteq> 0 }"
          have "?nzB' = ?nzB - { r }"
            using caseass by (auto simp add: row_def e_def \<delta>_def)
          thus ?thesis
            using rcond caseass(1) by(simp add: nonzerorows_def)
        qed
        moreover have "row i ?B' = e j"
          using caseass `r \<noteq> i`  
          by(simp add: nonzerorows_def row_def)  
            (metis vec_lambda_eta )
        ultimately have "det ?B' = det (minorM ?B' i j)" 
          using Suc.hyps by(simp add: nonzerorows_def row_def)  
        
        moreover have "(minorM B i j) = (minorM ?B' i j)"
          using minorM_eq[of i j B ?B'] `row i B = e j`
          by (simp add: e_def \<delta>_def row_def)
        ultimately have "det B = det (minorM B i j)" 
          using `r \<noteq> i` my_det_row_operation[of r i B "- B $ r $ j"] by simp
      }
      txt{* finished induction step *}
      thus ?case by fast 
    qed
  }
  thus ?thesis using assms by blast
qed

lemma det_minorM_row:
  fixes A :: "'a::comm_ring_1^'n^'n" and i j
  shows "det (minorM A i j) = det (\<chi> k. if k = i then (e j) else row k A)"
proof-
  let ?B = "(\<chi> k. if k = i then (e j) else row k A)"
  
  have "(minorM ?B i j) = (minorM A i j)"
    using minorM_eq[of i j ?B A] by(simp add: row_def)
  moreover have "det ?B = det (minorM ?B i j)"
    by(simp add: aux_det_minorM_row row_def[of i ?B] vec_lambda_eta)
  ultimately show ?thesis
    by auto
qed

lemma minorM_transpose: "minorM (transpose A) i j = transpose (minorM A j i)"
  by(simp add: minorM_def transpose_def conj_commute disj_commute cong del: if_cong)

lemma det_minorM_column:
  fixes A :: "'a::comm_ring_1^'n^'n" and i j 
  shows "det( minorM A i j ) = det (\<chi> r c. if c = j then \<delta> r i else A $ r $ c)"
  (is "?lm = det( ?B )" )
proof-
  have "(\<chi> r c . if r = j then (\<delta> c i) else (A $ c $ r) ) =
  (\<chi> r . if r = j then (e i) else row r (transpose A))"
    by(simp add: e_def delta_comm row_transpose column_def vec_eq_iff cong del: if_cong)
    
  hence "det( \<chi> r . if r = j then (e i) else row r (transpose A) ) = 
  det( transpose( \<chi> r c . if c = j then (\<delta> r i) else (A $ r $ c) ) )"
    by (simp add: transpose_def)
   
  thus ?thesis
    by (metis (no_types) det_minorM_row det_transpose minorM_transpose)
qed

lemma cofactorM_transpose: "cofactorM (transpose A) = transpose (cofactorM A)"
  (is "?lhs = ?rhs")
  by(simp only: cofactorM_def cofactor_def minorM_transpose det_transpose)
    (simp add: transpose_def)

(* ------------------------------------------------------------------------- *)
subsection {* Scalar-matrix multiplication *}                                                             
(* ------------------------------------------------------------------------- *)

definition scalar_matrix_mult :: "('a\<Colon>ab_semigroup_mult) \<Rightarrow> ('a^'n^'m) \<Rightarrow> ('a^'n^'m)" 
  (infixl "*ss" 70) where "c *ss A = (\<chi> i j. c * (A $ i $ j))"
    
lemma scalar_matrix_mult_monom: 
  fixes A :: "'a\<Colon>comm_ring_1 poly^'n^'n"
  shows "monom 1 0 *ss A = A"
  by (simp add: monom_0 one_poly_def scalar_matrix_mult_def vec_eq_iff)

lemma scalar_minus_left:
  fixes x :: "'a\<Colon>comm_ring_1"
  shows "- x *ss A = - (x *ss A)" 
  by (simp add: vec_eq_iff scalar_matrix_mult_def )

lemma one_scalar_mult_mat: 
  shows "1 *ss (A::'a\<Colon>comm_ring_1^'n^'n) = A"
  unfolding scalar_matrix_mult_def
  by(simp add: vec_lambda_eta) 

lemma scalar_mat_matrix_mult_left:
  "mat y ** A = y *ss A"
  by (simp add: vec_eq_iff mat_def scalar_matrix_mult_def matrix_matrix_mult_def
     if_distrib[where f="\<lambda>x. x * y" for y] setsum.If_cases)

lemma scalar_scalar_mult_assoc: "x1 *ss (x2 *ss A) = (x1 * x2) *ss A "
  unfolding scalar_matrix_mult_def 
  by(simp add: mult.assoc)

lemma matrix_scalar_assoc:
  fixes A B :: "'a\<Colon>comm_ring_1^'n\<Colon>finite^'n"
  shows "A ** (a *ss B) = a *ss (A ** B)"
  unfolding scalar_matrix_mult_def matrix_matrix_mult_def vec_eq_iff
  by(auto simp add: setsum_right_distrib intro!: Cartesian_Euclidean_Space.setsum_cong_aux)

lemma matrix_scalar_mat_one:
  fixes x1 and A :: "'a\<Colon>comm_ring_1^'n\<Colon>finite^'n"
  shows "A ** (x1 *ss mat 1) = x1 *ss A"
  by(simp add: matrix_scalar_assoc matrix_mul_rid)

lemma scalar_minus_ldistrib:
  fixes A and B :: "'a::comm_ring_1^'n\<Colon>finite^'n"
  and x1 :: "('a::comm_ring_1)"
  shows "x1 *ss (A - B) = (x1 *ss A) - (x1 *ss B)"
  unfolding scalar_matrix_mult_def vec_eq_iff
  by (simp add: mult_diff_mult)     

(* ------------------------------------------------------------------------- *)
subsection {* Adjugates *}                                                             
(* ------------------------------------------------------------------------- *)

definition "adjugate A = transpose (cofactorM A)"

lemma adjugate_transpose: "adjugate (transpose A) = transpose (adjugate A)"
  by (simp add: adjugate_def cofactorM_transpose)

lemma delta_id_matrix: "(\<chi> i j. (\<delta> i j) * c) = c *ss (mat 1)"
  by (simp add: scalar_matrix_mult_def mat_def \<delta>_def mult.commute)

lemma if_c_is_k: "(if c = k then A $ r $ k else A $ r $ c) = A $ r $ c"
  by simp

theorem adjugate_det:
  fixes A :: "'a::comm_ring_1^'n^'n"
  shows "adjugate A ** A = det A *ss mat 1"
proof-
  let ?U = "UNIV\<Colon>'n\<Colon>finite set"
  have adjprod: "adjugate A ** A = (\<chi> i k. (\<Sum> j\<in>?U. (cofactor A j i) * A $ j $ k))"
    by (simp add: cofactorM_def transpose_def adjugate_def matrix_matrix_mult_def)

  { fix i k :: 'n 
    
    have "(\<Sum>j\<in>?U. (cofactor A j i) * (A $ j $ k)) = 
    (\<Sum>j\<in>?U. (A $ j $ k) * det (\<chi> r c. if c = i then \<delta> r j else (A $ r $ c)))" 
      by (simp add: det_minorM_column cofactor_def comm_semiring_1_class.normalizing_semiring_rules)
      
    also have "\<dots> = (\<Sum>j\<in>?U. det (\<chi> r c. if c = i then \<delta> r j * A $ r $ k else A $ r $ c))"
    proof-
      { fix j 
        have "(A $ j $ k) * det (\<chi> r c. if c = i then \<delta> r j else (A $ r $ c)) =
        det (\<chi> r c. if c = i then \<delta> r j * (A $ r $ k) else A $ r $ c)"
        using det_col_mul[of i _ "\<chi> r c. if c = i then \<delta> r j else A $ r $ c", symmetric]
        by(simp add: \<delta>_def comm_semiring_1_class.normalizing_semiring_rules(7) cong: if_cong)
          (simp add: if_distrib[where x=1 and y = 0] cong: if_cong) }
      thus ?thesis
      by auto
    qed
    
    also have "\<dots> = det (\<chi> r c. if c = i then (\<Sum> j \<in> ?U. \<delta> r j * A $ r $ k) else A $ r $ c)"
      using det_linear_column_setsum[of ?U i "\<lambda>j. \<chi> r. \<delta> r j * A $ r $ k"]
      by(simp only: vec_lambda_beta finite[of ?U])
      
    also have "\<dots> = det (\<chi> r c. if c = i then A $ r $ k else A $ r $ c)"
    proof-
      { fix r and a :: "'a::comm_ring_1"
      have "(\<Sum>j\<in>?U. \<delta> r j * a) = a"
        by(subst setsum.remove)(auto simp add: \<delta>_def) }
      thus ?thesis
        by presburger
    qed
    
    also have "\<dots> = \<delta> i k * det A"
    by(cases "i=k")
      (auto simp add: \<delta>_def vec_lambda_eta if_c_is_k column_def 
               intro!: my_det_identical_columns[of i k])

    finally have "(\<Sum> j \<in> ?U. cofactor A j i * A $ j $ k) = \<delta> i k * det A"
      by(simp add: cofactor_def \<delta>_def)
  }
  thus ?thesis
    using adjprod delta_id_matrix[of "det A"] by auto
qed

lemma adjugate_det_symmetric:  
  shows "A ** adjugate A = det A *ss mat 1"
proof-
  have "transpose (A ** adjugate A) = det A *ss mat 1" 
    using matrix_transpose_mul[of A "adjugate A"] det_transpose[of A]
    adjugate_det[of "transpose A"] adjugate_transpose[of A]
    by auto
    
  also have "transpose (det A *ss mat 1) = det A *ss transpose (mat 1)"
    by(simp add: transpose_def scalar_matrix_mult_def)
  
  finally show ?thesis
    by(subst transpose_transpose[of "A ** adjugate A", symmetric])
      (simp add: transpose_mat)
qed

(* ------------------------------------------------------------------------- *)
subsection {* Matrix multiplication *}
(* ------------------------------------------------------------------------- *)

lemma matrix_mult_left_distributes_minus:
  fixes A B C :: "'a::comm_ring_1^'n^'n"
  shows "A ** (B - C) = A ** B - A ** C"  
  by (metis (hide_lams, no_types) add_diff_cancel diff_add_cancel matrix_add_ldistrib)

lemma matrix_mult_right_distributes_minus:
  fixes A B C :: "'a::comm_ring_1^'n^'n" 
  shows "(A - B) ** C = A ** C - B ** C"
  unfolding matrix_matrix_mult_def vec_eq_iff
  using finite[of UNIV]
  by(induct rule: finite_induct)
    (auto simp add: left_diff_distrib)

lemma matrix_sum_mult:
  fixes A :: "('a::comm_ring_1)^'n\<Colon>finite^'n\<Colon>finite"
      and f :: "nat \<Rightarrow> ('a::comm_ring_1)^'n\<Colon>finite^'n\<Colon>finite" and n :: nat
  shows "A ** (\<Sum> k \<le> n. (f k)) = (\<Sum> k \<le> n. A ** (f k))"
  by (induct n) (simp_all add: matrix_add_ldistrib)

(* ------------------------------------------------------------------------- *)
subsection {* Powers *}
(* ------------------------------------------------------------------------- *)

primrec matpow :: "'a\<Colon>semiring_1^'n^'n \<Rightarrow> nat \<Rightarrow> 'a^'n^'n" where
  matpow_0:   "matpow A 0 = mat 1" |
  matpow_Suc: "matpow A (Suc n) = A ** (matpow A n)"

lemma matrix_mult_one_comm: "A ** mat 1 = mat 1 ** A"
  by (simp add: matrix_mul_lid matrix_mul_rid) 

lemma matpow_one: "matpow A 1 = A"
  by(simp add: matrix_mul_rid)

lemma matpow_comm: "A ** matpow A n = matpow A n ** A"
  by(induct n) (simp_all add: matrix_mult_one_comm matrix_mul_assoc)

lemma matpow_suc: "matpow A n ** A = matpow A (Suc n)"
  by(simp add: matpow_comm)

end
