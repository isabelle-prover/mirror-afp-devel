(*  
    Author:      René Thiemann 
                 Akihisa Yamada
    License:     BSD
*)
section \<open>Characteristic Polynomial\<close>

text \<open>We define eigenvalues, eigenvectors, and the characteristic polynomial. We further prove
  that the eigenvalues are exactly the roots of the characteristic polynomial.
  Finally, we apply the fundamental theorem of algebra to show that the characteristic polynomial
  of a complex matrix can always be represented as product of linear factors $x - a$.\<close>
 
theory Char_Poly
imports 
  "~~/src/HOL/Library/Fundamental_Theorem_Algebra"
  "../Polynomial_Interpolation/Missing_Polynomial"
  Determinant
  Complex_Main
begin

definition eigenvector :: "'a :: comm_ring_1 mat \<Rightarrow> 'a vec \<Rightarrow> 'a \<Rightarrow> bool" where
  "eigenvector A v k = (v \<in> carrier\<^sub>v (dim\<^sub>r A) \<and> v \<noteq> \<zero>\<^sub>v (dim\<^sub>r A) \<and> A \<otimes>\<^sub>m\<^sub>v v = k \<odot>\<^sub>v v)"
  
lemma eigenvector_pow: assumes A: "A \<in> carrier\<^sub>m n n"
  and ev: "eigenvector A v (k :: 'a :: comm_ring_1)"
  shows "A ^\<^sub>m i \<otimes>\<^sub>m\<^sub>v v = k^i \<odot>\<^sub>v v" 
proof -
  let ?G = "monoid\<^sub>v TYPE ('a) n"
  from A have dim: "dim\<^sub>r A = n" by auto
  from ev[unfolded eigenvector_def dim]
  have v: "v \<in> carrier\<^sub>v n" and Av: "A \<otimes>\<^sub>m\<^sub>v v = k \<odot>\<^sub>v v" by auto
  interpret v: comm_group ?G by (rule vec_group)
  show ?thesis
  proof (induct i)
    case 0
    show ?case using v dim by simp
  next
    case (Suc i)
    def P \<equiv> "A ^\<^sub>m i"
    have P: "P \<in> carrier\<^sub>m n n" using A unfolding P_def by simp
    have "A ^\<^sub>m Suc i = P \<otimes>\<^sub>m A" unfolding P_def by simp
    also have "\<dots> \<otimes>\<^sub>m\<^sub>v v = P \<otimes>\<^sub>m\<^sub>v (A \<otimes>\<^sub>m\<^sub>v v)" using P A v by simp
    also have "A \<otimes>\<^sub>m\<^sub>v v = k \<odot>\<^sub>v v" by (rule Av)
    also have "P \<otimes>\<^sub>m\<^sub>v (k \<odot>\<^sub>v v) = k \<odot>\<^sub>v (P \<otimes>\<^sub>m\<^sub>v v)" 
      by (rule vec_eqI, insert v P, auto)
    also have "(P \<otimes>\<^sub>m\<^sub>v v) = (k ^ i) \<odot>\<^sub>v v" unfolding P_def by (rule Suc)
    also have "k \<odot>\<^sub>v ((k ^ i) \<odot>\<^sub>v v) = (k * k ^ i) \<odot>\<^sub>v v"
      by (rule vec_eqI, insert v, auto)
    also have "k * k ^ i = k ^ (Suc i)" by auto
    finally show ?case .
  qed
qed
    


definition eigenvalue :: "'a :: comm_ring_1 mat \<Rightarrow> 'a \<Rightarrow> bool" where
  "eigenvalue A k = (\<exists> v. eigenvector A v k)"


definition char_matrix :: "'a :: field mat \<Rightarrow> 'a \<Rightarrow> 'a mat" where
  "char_matrix A e = A \<oplus>\<^sub>m ((-e) \<odot>\<^sub>m (\<one>\<^sub>m (dim\<^sub>r A)))"

lemma char_matrix_closed[simp]: "A \<in> carrier\<^sub>m n n \<Longrightarrow> char_matrix A e \<in> carrier\<^sub>m n n"
  unfolding char_matrix_def by auto

lemma eigenvector_char_matrix: assumes A: "(A :: 'a :: field mat) \<in> carrier\<^sub>m n n" 
  shows "eigenvector A v e = (v \<in> carrier\<^sub>v n \<and> v \<noteq> \<zero>\<^sub>v n \<and> char_matrix A e \<otimes>\<^sub>m\<^sub>v v = \<zero>\<^sub>v n)"
proof -
  from A have dim: "dim\<^sub>r A = n" "dim\<^sub>c A = n" by auto
  {
    assume v: "v \<in> carrier\<^sub>v n"
    hence dimv: "dim\<^sub>v v = n" by auto
    have "(A \<otimes>\<^sub>m\<^sub>v v = e \<odot>\<^sub>v v) = (A \<otimes>\<^sub>m\<^sub>v v \<oplus>\<^sub>v (-e) \<odot>\<^sub>v v = \<zero>\<^sub>v n)" (is "?id1 = ?id2")
    proof
      assume ?id1
      from arg_cong[OF this, of "\<lambda> w. w \<oplus>\<^sub>v (-e) \<odot>\<^sub>v v"]
      show ?id2 using A v by auto
    next
      assume ?id2
      have "A \<otimes>\<^sub>m\<^sub>v v \<oplus>\<^sub>v - e \<odot>\<^sub>v v \<oplus>\<^sub>v e \<odot>\<^sub>v v = A \<otimes>\<^sub>m\<^sub>v v" using A v by auto
      from arg_cong[OF `?id2`, of "\<lambda> w. w \<oplus>\<^sub>v e \<odot>\<^sub>v v", unfolded this]
      show ?id1 using A v by simp
    qed
    also have "(A \<otimes>\<^sub>m\<^sub>v v \<oplus>\<^sub>v (-e) \<odot>\<^sub>v v) = char_matrix A e \<otimes>\<^sub>m\<^sub>v v" unfolding char_matrix_def
      by (rule vec_eqI, insert v A dim, auto simp: scalar_prod_left_distrib[of _ n])
    finally have "(A \<otimes>\<^sub>m\<^sub>v v = e \<odot>\<^sub>v v) = (char_matrix A e \<otimes>\<^sub>m\<^sub>v v = \<zero>\<^sub>v n)" .
  }
  thus ?thesis unfolding eigenvector_def dim by blast
qed

lemma eigenvalue_char_matrix: assumes A: "(A :: 'a :: field mat) \<in> carrier\<^sub>m n n" 
  shows "eigenvalue A e = (\<exists> v. v \<in> carrier\<^sub>v n \<and> v \<noteq> \<zero>\<^sub>v n \<and> char_matrix A e \<otimes>\<^sub>m\<^sub>v v = \<zero>\<^sub>v n)"
  unfolding eigenvalue_def eigenvector_char_matrix[OF A] .. 

definition find_eigenvector :: "'a::field mat \<Rightarrow> 'a \<Rightarrow> 'a vec" where
  "find_eigenvector A e = 
    find_base_vector (fst (gauss_jordan (char_matrix A e) (\<zero>\<^sub>m (dim\<^sub>r A) 0)))"

lemma find_eigenvector: assumes A: "A \<in> carrier\<^sub>m n n"
  and ev: "eigenvalue A e"
  shows "eigenvector A (find_eigenvector A e) e"
proof -
  def B \<equiv> "char_matrix A e"
  from ev[unfolded eigenvalue_char_matrix[OF A]]  obtain v where
    v: "v \<in> carrier\<^sub>v n" "v \<noteq> \<zero>\<^sub>v n" and Bv: "B \<otimes>\<^sub>m\<^sub>v v = \<zero>\<^sub>v n" unfolding B_def by auto
  have B: "B \<in> carrier\<^sub>m n n" using A unfolding B_def by simp
  let ?z = "\<zero>\<^sub>m (dim\<^sub>r A) 0"
  obtain C D where gauss: "gauss_jordan B ?z = (C,D)" by force
  def w \<equiv> "find_base_vector C"
  have res: "find_eigenvector A e = w" unfolding w_def find_eigenvector_def Let_def gauss B_def[symmetric]
    by simp
  have "?z \<in> carrier\<^sub>m n 0" using A by auto
  note gauss_0 = gauss_jordan[OF B this gauss] 
  hence C: "C \<in> carrier\<^sub>m n n" by auto
  from gauss_0(1)[OF v(1)] Bv have Cv: "C \<otimes>\<^sub>m\<^sub>v v = \<zero>\<^sub>v n" by auto
  {
    assume C: "C = \<one>\<^sub>m n"
    have False using id Cv v unfolding C by auto
  }
  hence C1: "C \<noteq> \<one>\<^sub>m n" by auto
  from find_base_vector_not_1[OF gauss_jordan_row_echelon[OF B gauss] C C1]
  have w: "w \<in> carrier\<^sub>v n" "w \<noteq> \<zero>\<^sub>v n" and id: "C \<otimes>\<^sub>m\<^sub>v w = \<zero>\<^sub>v n" unfolding w_def by auto
  from gauss_0(1)[OF w(1)] id have Bw: "B \<otimes>\<^sub>m\<^sub>v w = \<zero>\<^sub>v n" by simp
  from w Bw have "eigenvector A w e" 
    unfolding eigenvector_char_matrix[OF A] B_def by auto
  thus ?thesis unfolding res .
qed

lemma eigenvalue_imp_nonzero_dim: assumes "A \<in> carrier\<^sub>m n n"
  and "eigenvalue A ev"
  shows "n > 0"
proof (cases n)
  case 0
  from assms obtain v where "eigenvector A v ev" unfolding eigenvalue_def by auto
  from this[unfolded eigenvector_def] assms 0 
  have "v \<in> carrier\<^sub>v 0" "v \<noteq> \<zero>\<^sub>v 0" by auto
  hence False by auto
  thus ?thesis by auto
qed simp
  
lemma eigenvalue_det: assumes A: "(A :: 'a :: field mat) \<in> carrier\<^sub>m n n" shows
  "eigenvalue A e = (det (char_matrix A e) = 0)"
proof -
  from A have cA: "char_matrix A e \<in> carrier\<^sub>m n n" by auto
  show ?thesis
    unfolding eigenvalue_char_matrix[OF A]
    unfolding id det_0_negate[OF cA] det_0_iff_vec_prod_zero[OF cA]
      eigenvalue_def by auto
qed

definition char_poly_matrix :: "'a :: comm_ring_1 mat \<Rightarrow> 'a poly mat" where
  "char_poly_matrix A = (([:0,1:] \<odot>\<^sub>m \<one>\<^sub>m (dim\<^sub>r A)) \<oplus>\<^sub>m map\<^sub>m (\<lambda> a. [: - a :]) A)"    

lemma char_poly_matrix_closed[simp]: "A \<in> carrier\<^sub>m n n \<Longrightarrow> char_poly_matrix A \<in> carrier\<^sub>m n n"
  unfolding char_poly_matrix_def by auto    

definition char_poly :: "'a :: comm_ring_1 mat \<Rightarrow> 'a poly" where
  "char_poly A = (det (char_poly_matrix A))"    

lemmas char_poly_defs = char_poly_def char_poly_matrix_def

lemma poly_det_cong: assumes A: "A \<in> carrier\<^sub>m n n"
  and B: "B \<in> carrier\<^sub>m n n"
  and poly: "\<And> i j. i < n \<Longrightarrow> j < n \<Longrightarrow> poly (B $$ (i,j)) k = A $$ (i,j)"
  shows "poly (det B) k = det A" 
proof -
  show ?thesis
  unfolding det_def'[OF A] det_def'[OF B] poly_setsum poly_mult poly_setprod
  proof (rule setsum.cong[OF refl])
    fix x
    assume x: "x \<in> {p. p permutes {0..<n}}"
    let ?l = "\<Prod>ka = 0..<n. poly (B $$ (ka, x ka)) k"
    let ?r = "\<Prod>i = 0..<n. A $$ (i, x i)"
    have id: "?l = ?r"
      by (rule setprod.cong[OF refl poly], insert x, auto)
    show "poly (signof x) k * ?l = signof x * ?r" unfolding id signof_def by auto
  qed
qed

lemma char_poly_matrix: assumes A: "(A :: 'a :: field mat) \<in> carrier\<^sub>m n n"
  shows "poly (char_poly A) k = det (\<ominus>\<^sub>m (char_matrix A k))"  unfolding char_poly_def
  by (rule poly_det_cong[of _ n], insert A, auto simp: char_poly_matrix_def char_matrix_def)

lemma eigenvalue_root_char_poly: assumes A: "(A :: 'a :: field mat) \<in> carrier\<^sub>m n n"
  shows "eigenvalue A k \<longleftrightarrow> poly (char_poly A) k = 0" 
  unfolding eigenvalue_det[OF A] char_poly_matrix[OF A] 
  by (subst det_0_negate[of _ n], insert A, auto)

context
  fixes A :: "'a :: comm_ring_1 mat" and n :: nat
  assumes A: "A \<in> carrier\<^sub>m n n"
  and ut: "upper_triangular A"
begin
lemma char_poly_matrix_upper_triangular: "upper_triangular (char_poly_matrix A)"
  using A ut unfolding upper_triangular_def char_poly_matrix_def by auto 

lemma char_poly_upper_triangular: 
  "char_poly A = (\<Prod> a \<leftarrow> mat_diag A. [:- a, 1:])"
proof -
  from A have cA: "char_poly_matrix A \<in> carrier\<^sub>m n n" by simp
  show ?thesis
    unfolding char_poly_def det_upper_triangular [OF char_poly_matrix_upper_triangular cA]
    by (rule arg_cong[where f = listprod], unfold list_eq_iff_nth_eq, insert cA A, auto simp: mat_diag_def
      char_poly_matrix_def)
qed
end

lemma map_poly_mult: assumes A: "A \<in> carrier\<^sub>m nr n"
  and B: "B \<in> carrier\<^sub>m n nc"
  shows 
    "map\<^sub>m (\<lambda> a. [: a :]) (A \<otimes>\<^sub>m B) = map\<^sub>m (\<lambda> a. [: a :]) A \<otimes>\<^sub>m map\<^sub>m (\<lambda> a. [: a :]) B" (is "?id")
    "map\<^sub>m (\<lambda> a. [: a :] * p) (A \<otimes>\<^sub>m B) = map\<^sub>m (\<lambda> a. [: a :] * p) A \<otimes>\<^sub>m map\<^sub>m (\<lambda> a. [: a :]) B" (is "?left")
    "map\<^sub>m (\<lambda> a. [: a :] * p) (A \<otimes>\<^sub>m B) = map\<^sub>m (\<lambda> a. [: a :]) A \<otimes>\<^sub>m map\<^sub>m (\<lambda> a. [: a :] * p) B" (is "?right")
proof -
  from A B have dim: "dim\<^sub>r A = nr" "dim\<^sub>c A = n" "dim\<^sub>r B = n" "dim\<^sub>c B = nc" by auto
  {
    fix i j
    have "i < nr \<Longrightarrow> j < nc \<Longrightarrow> 
      row (map\<^sub>m (\<lambda>a. [:a:]) A) i \<bullet> col (map\<^sub>m (\<lambda>a. [:a:]) B) j = [:(row A i \<bullet> col B j):]"
      unfolding scalar_prod_def
      by (auto simp: dim ac_simps, induct n, auto)  
  } note id = this 
  {
    fix i j
    have "i < nr \<Longrightarrow> j < nc \<Longrightarrow> 
      [:(row A i \<bullet> col B j):] * p = row (map\<^sub>m (\<lambda> a. [: a :] * p) A) i \<bullet> col (map\<^sub>m (\<lambda>a. [:a:]) B) j"
      unfolding scalar_prod_def
      by (auto simp: dim ac_simps smult_setsum) 
  } note left = this 
  {
    fix i j
    have "i < nr \<Longrightarrow> j < nc \<Longrightarrow> 
      [:(row A i \<bullet> col B j):] * p = row (map\<^sub>m (\<lambda> a. [: a :]) A) i \<bullet> col (map\<^sub>m (\<lambda>a. [:a:] * p) B) j"
      unfolding scalar_prod_def
      by (auto simp: dim ac_simps smult_setsum) 
  } note right = this 
  show ?id
    by (rule mat_eqI, insert id, auto simp: dim)
  show ?left
    by (rule mat_eqI, insert left, auto simp: dim)
  show ?right
    by (rule mat_eqI, insert right, auto simp: dim)
qed

lemma char_poly_similar: assumes "mat_similar A (B :: 'a :: comm_ring_1 mat)"
  shows "char_poly A = char_poly B"
proof -
  from mat_similarD[OF assms] obtain n P Q where
  carr: "{A, B, P, Q} \<subseteq> carrier\<^sub>m n n" (is "_ \<subseteq> ?C")
  and PQ: "P \<otimes>\<^sub>m Q = \<one>\<^sub>m n" 
  and AB: "A = P \<otimes>\<^sub>m B \<otimes>\<^sub>m Q" by auto
  hence A: "A \<in> ?C" and B: "B \<in> ?C" and P: "P \<in> ?C" and Q: "Q \<in> ?C" by auto
  let ?m = "\<lambda> a. [: -a :]"
  let ?P = "map\<^sub>m (\<lambda> a. [: a :]) P"
  let ?Q = "map\<^sub>m (\<lambda> a. [: a :]) Q"
  let ?B = "map\<^sub>m ?m B"
  let ?I = "map\<^sub>m (\<lambda> a. [: a :]) (\<one>\<^sub>m n)"
  let ?XI = "[:0, 1:] \<odot>\<^sub>m \<one>\<^sub>m n"
  from A B have dim: "dim\<^sub>r A = n" "dim\<^sub>r B = n" by auto
  have cong: "\<And> x y z. x = y \<Longrightarrow> x * z = y * z" by auto
  have id: "?m = (\<lambda> a :: 'a. [: a :] * [: -1 :])" by (intro ext, auto)
  have "char_poly A = det (?XI \<oplus>\<^sub>m map\<^sub>m (\<lambda>a. [:- a:]) (P \<otimes>\<^sub>m B \<otimes>\<^sub>m Q))" unfolding 
    char_poly_defs dim 
    by (simp add: AB)
  also have "?XI = ?P \<otimes>\<^sub>m ?XI \<otimes>\<^sub>m ?Q" (is "_ = ?left")
  proof -
    have "?P \<otimes>\<^sub>m ?XI = [:0, 1:] \<odot>\<^sub>m (?P \<otimes>\<^sub>m \<one>\<^sub>m n)" 
      by (rule mat_mult_scalar_comm[of _ n n _ n], insert P, auto)
    also have "?P \<otimes>\<^sub>m \<one>\<^sub>m n = ?P" using P by simp
    also have "([: 0, 1:] \<odot>\<^sub>m ?P) \<otimes>\<^sub>m ?Q = [: 0, 1:] \<odot>\<^sub>m (?P \<otimes>\<^sub>m ?Q)"
      by (rule mat_mult_scalar_assoc, insert P Q, auto)
    also have "?P \<otimes>\<^sub>m ?Q = ?I" unfolding PQ[symmetric]
      by (rule map_poly_mult[symmetric, OF P Q])
    also have "[: 0, 1:] \<odot>\<^sub>m ?I = ?XI"
      by (rule, auto simp: one_poly_def)
    finally show ?thesis ..
  qed
  also have "map\<^sub>m ?m (P \<otimes>\<^sub>m B \<otimes>\<^sub>m Q) = ?P \<otimes>\<^sub>m ?B \<otimes>\<^sub>m ?Q" (is "_ = ?right")
    unfolding id
    by (subst map_poly_mult[OF mat_mult_mat_closed[OF P B] Q],
      subst map_poly_mult(3)[OF P B], simp)
  also have "?left \<oplus>\<^sub>m ?right = (?P \<otimes>\<^sub>m ?XI \<oplus>\<^sub>m ?P \<otimes>\<^sub>m ?B) \<otimes>\<^sub>m ?Q"
    by (rule mat_mult_left_distrib[symmetric, of _ n n], insert B P Q, auto)
  also have "?P \<otimes>\<^sub>m ?XI \<oplus>\<^sub>m ?P \<otimes>\<^sub>m ?B = ?P \<otimes>\<^sub>m (?XI \<oplus>\<^sub>m ?B)"
    by (rule mat_mult_right_distrib[symmetric, of _ n n], insert B P Q, auto)
  also have "det (?P \<otimes>\<^sub>m (?XI \<oplus>\<^sub>m ?B) \<otimes>\<^sub>m ?Q) = det ?P * det (?XI \<oplus>\<^sub>m ?B) * det ?Q"
    by (rule trans[OF det_mult[of _ n] cong[OF det_mult]], insert P Q B, auto)
  also have "\<dots> = (det ?P * det ?Q) * det (?XI \<oplus>\<^sub>m ?B)" by (simp add: ac_simps)
  also have "det (?XI \<oplus>\<^sub>m ?B) = char_poly B" unfolding char_poly_defs dim by simp
  also have "det ?P * det ?Q = det (?P \<otimes>\<^sub>m ?Q)"
    by (rule det_mult[symmetric], insert P Q, auto)
  also have "?P \<otimes>\<^sub>m ?Q = ?I" unfolding PQ[symmetric]
    by (rule map_poly_mult[symmetric, OF P Q])
  also have "det \<dots> = listprod (mat_diag ?I)"
    by (rule det_upper_triangular[of _ n], auto)
  also have "\<dots> = 1" unfolding listprod_diag_setprod
    by (rule setprod.neutral, auto simp: one_poly_def)
  finally show ?thesis by simp
qed

lemma degree_signof_mult[simp]: "degree (signof p * q) = degree q"
  by (cases "sign p = 1", auto simp: signof_def)

lemma degree_monic_char_poly: assumes A: "A \<in> carrier\<^sub>m n n"
  shows "degree (char_poly A) = n \<and> coeff (char_poly A) n = 1"
proof -
  from A have A': "[:0, 1:] \<odot>\<^sub>m \<one>\<^sub>m (dim\<^sub>r A) \<oplus>\<^sub>m map\<^sub>m (\<lambda>a. [:- a:]) A \<in> carrier\<^sub>m n n" by auto
  from A have dA: "dim\<^sub>r A = n" by simp
  show ?thesis
    unfolding char_poly_defs det_def'[OF A']
  proof (rule degree_lcoeff_setsum[of _ id], auto simp: finite_permutations signof_id permutes_id dA)
    have both: "degree (\<Prod>i = 0..<n. ([:0, 1:] \<odot>\<^sub>m \<one>\<^sub>m n \<oplus>\<^sub>m map\<^sub>m (\<lambda>a. [:- a:]) A) $$ (i, i)) = n \<and>
      coeff (\<Prod>i = 0..<n. ([:0, 1:] \<odot>\<^sub>m \<one>\<^sub>m n \<oplus>\<^sub>m map\<^sub>m (\<lambda>a. [:- a:]) A) $$ (i, i)) n = 1"
      by (rule degree_setprod_monic, insert A, auto)
    from both show "degree (\<Prod>i = 0..<n. ([:0, 1:] \<odot>\<^sub>m \<one>\<^sub>m n \<oplus>\<^sub>m map\<^sub>m (\<lambda>a. [:- a:]) A) $$ (i, i)) = n" ..
    from both show "coeff (\<Prod>i = 0..<n. ([:0, 1:] \<odot>\<^sub>m \<one>\<^sub>m n \<oplus>\<^sub>m map\<^sub>m (\<lambda>a. [:- a:]) A) $$ (i, i)) n = 1" ..
  next
    fix p
    assume p: "p permutes {0..<n}"
      and "p \<noteq> id"
    then obtain i where i: "i < n" and pi: "p i \<noteq> i"
      by (metis atLeastLessThan_iff order_refl permutes_natset_le)
    show "degree (\<Prod>i = 0..<n. ([:0, 1:] \<odot>\<^sub>m \<one>\<^sub>m n \<oplus>\<^sub>m map\<^sub>m (\<lambda>a. [:- a:]) A) $$ (i, p i)) < n"
      by (rule degree_setprod_setsum_lt_n[OF _ i], insert p i pi A, auto)
  qed
qed

lemma fundamental_theorem_algebra_factorized: fixes p :: "complex poly"
  shows "\<exists> as. [:coeff p (degree p):] * (\<Prod> a \<leftarrow> as. [:- a, 1:]) = p"
proof -
  def n \<equiv> "degree p"
  have "degree p = n" unfolding n_def by simp
  thus ?thesis
  proof (induct n arbitrary: p)
    case (0 p)
    hence "\<exists> c. p = [: c :]" by (cases p, auto split: if_splits)
    thus ?case by (intro exI[of _ Nil], auto)
  next
    case (Suc n p)
    have dp: "degree p = Suc n" by fact
    hence "\<not> constant (poly p)" by (simp add: constant_degree)
    from fundamental_theorem_of_algebra[OF this] obtain c where rt: "poly p c = 0" by auto
    hence "[:-c,1 :] dvd p" by (simp add: dvd_iff_poly_eq_0)
    then obtain q where p: "p = q * [: -c,1 :]" by (metis dvd_def mult.commute)
    from `degree p = Suc n` have dq: "degree q = n" using p
      by (metis One_nat_def Suc_eq_plus1 `\<not> constant (poly p)` add_right_cancel constant_degree 
        degree_0 degree_1 degree_mult_eq degree_pCons_eq mult_eq_0_iff one_neq_zero one_poly_def)
    from Suc(1)[OF this] obtain as where q: "[:coeff q (degree q):] * (\<Prod>a\<leftarrow>as. [:- a, 1:]) = q" by auto
    have dc: "degree p = degree q + degree [: -c, 1 :]" unfolding dq dp by simp
    have cq: "coeff q (degree q) = coeff p (degree p)" unfolding dc unfolding p coeff_mult_degree_sum unfolding dq by simp
    show ?case using p[unfolded q[unfolded cq, symmetric]] 
      by (intro exI[of _ "c # as"], auto simp: ac_simps)
  qed
qed

lemma char_poly_factorized: fixes A :: "complex mat"
  assumes A: "A \<in> carrier\<^sub>m n n"
  shows "\<exists> as. char_poly A = (\<Prod> a \<leftarrow> as. [:- a, 1:]) \<and> length as = n"
proof -
  let ?p = "char_poly A"
  from fundamental_theorem_algebra_factorized[of ?p] obtain as
  where "[:coeff ?p (degree ?p):] * (\<Prod>a\<leftarrow>as. [:- a, 1:]) = ?p" by blast
  also have "coeff ?p (degree ?p) = 1" using degree_monic_char_poly[OF A] by simp
  finally have cA: "?p = (\<Prod>a\<leftarrow>as. [:- a, 1:])" by simp
  from degree_monic_char_poly[OF A] have "degree ?p = n" ..
  with degree_linear_factors[of uminus as, folded cA] have "length as = n" by auto
  with cA show ?thesis by blast
qed

lemma char_poly_four_block_zeros_col: assumes A1: "A1 \<in> carrier\<^sub>m 1 1"
  and A2: "A2 \<in> carrier\<^sub>m 1 n" and A3: "A3 \<in> carrier\<^sub>m n n"
  shows "char_poly (four_block_mat A1 A2 (\<zero>\<^sub>m n 1) A3) = char_poly A1 * char_poly A3" 
    (is "char_poly ?A = ?cp1 * ?cp3")
proof -
  let ?cm = "\<lambda> A. [:0, 1:] \<odot>\<^sub>m \<one>\<^sub>m (dim\<^sub>r A) \<oplus>\<^sub>m
         map\<^sub>m (\<lambda>a. [:- a:]) A"
  let ?B2 = "map\<^sub>m (\<lambda>a. [:- a:]) A2"
  have "char_poly ?A = det (?cm ?A)"
    unfolding char_poly_defs using A1 A3 by simp
  also have "?cm ?A = four_block_mat (?cm A1) ?B2 (\<zero>\<^sub>m n 1) (?cm A3)"
    by (rule mat_eqI, insert A1 A2 A3, auto simp: one_poly_def)
  also have "det \<dots> = det (?cm A1) * det (?cm A3)"
    by (rule det_four_block_mat_lower_left_zero_col[OF _ _ refl], insert A1 A2 A3, auto)
  also have "\<dots> = ?cp1 * ?cp3" unfolding char_poly_defs ..
  finally show ?thesis .
qed

lemma char_poly_mat_transpose[simp]: assumes A: "A \<in> carrier\<^sub>m n n"
  shows "char_poly (mat_transpose A) = char_poly A"
proof -
  let ?A = "[:0, 1:] \<odot>\<^sub>m \<one>\<^sub>m (dim\<^sub>r A) \<oplus>\<^sub>m map\<^sub>m (\<lambda>a. [:- a:]) A"
  have A': "?A \<in> carrier\<^sub>m n n" using A by auto
  show ?thesis unfolding char_poly_defs
    by (subst det_transpose[symmetric, OF A'], rule arg_cong[of _ _ det],
    insert A, auto)
qed

    
end