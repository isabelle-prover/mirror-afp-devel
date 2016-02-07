(*  
    Author:      René Thiemann 
                 Akihisa Yamada
    License:     BSD
*)
section \<open>Resultant\<close>

text \<open>This theory defines the Sylvester matrix and the resultant and contains 
  facts about these notions which are required for addition and multiplication
  of algebraic numbers.

  The results are taken from the textbook \cite[pages 227ff and 235ff]{AlgNumbers}.
\<close> 

theory Resultant
imports
  "../Jordan_Normal_Form/Matrix_IArray_Impl"
  "../Jordan_Normal_Form/Determinant_Impl"
  "../Polynomial_Factorization/Rational_Factorization"
  Unique_Factorization_Poly
  Bivariate_Polynomials
  Algebraic_Numbers_Prelim
  Binary_Exponentiation
begin


subsection\<open>Sylvester Matrix\<close>

definition sylvester_mat_sub :: "nat \<Rightarrow> nat \<Rightarrow> 'a poly \<Rightarrow> 'a poly \<Rightarrow> 'a :: zero mat" where
  "sylvester_mat_sub m n p q \<equiv>
   mat (m+n) (m+n) (\<lambda> (i,j).
     if i < n then
       if i \<le> j \<and> j - i \<le> m then coeff p (m + i - j) else 0
     else if i - n \<le> j \<and> j \<le> i then coeff q (i-j) else 0)"

definition sylvester_mat :: "'a poly \<Rightarrow> 'a poly \<Rightarrow> 'a :: zero mat" where
  "sylvester_mat p q \<equiv> sylvester_mat_sub (degree p) (degree q) p q"

lemma sylvester_mat_sub_dim[simp]:
  fixes m n p q
  defines "S \<equiv> sylvester_mat_sub m n p q"
  shows "dim\<^sub>r S = m+n" and "dim\<^sub>c S = m+n"
  unfolding S_def sylvester_mat_sub_def by auto

lemma sylvester_mat_sub_carrier:
  shows "sylvester_mat_sub m n p q \<in> carrier\<^sub>m (m+n) (m+n)" by auto

lemma sylvester_mat_dim[simp]:
  fixes p q
  defines "d \<equiv> degree p + degree q"
  shows "dim\<^sub>r (sylvester_mat p q) = d" "dim\<^sub>c (sylvester_mat p q) = d"
  unfolding sylvester_mat_def d_def by auto

lemma sylvester_mat_carrier:
  fixes p q
  defines "d \<equiv> degree p + degree q"
  shows "sylvester_mat p q \<in> carrier\<^sub>m d d" unfolding d_def by auto

lemma sylvester_mat_sub_index:
  fixes p q
  assumes i: "i < m+n" and j: "j < m+n"
  shows "sylvester_mat_sub m n p q $$ (i,j) =
    (if i < n then
       if i \<le> j \<and> j - i \<le> m then coeff p (m + i - j) else 0
     else if i - n \<le> j \<and> j \<le> i then coeff q (i-j) else 0)"
  unfolding sylvester_mat_sub_def
  unfolding mat_index_mat(1)[OF i j] by auto

lemma sylvester_mat_index:
  fixes p q
  defines "m \<equiv> degree p" and "n \<equiv> degree q"
  assumes i: "i < m+n" and j: "j < m+n"
  shows "sylvester_mat p q $$ (i,j) =
    (if i < n then
       if i \<le> j \<and> j - i \<le> m then coeff p (m + i - j) else 0
     else if i - n \<le> j \<and> j \<le> i then coeff q (i - j) else 0)"
  unfolding sylvester_mat_def
  using sylvester_mat_sub_index[OF i j] unfolding m_def n_def.

lemma sylvester_mat_index2:
  fixes p q :: "'a :: comm_semiring_1 poly"
  defines "m \<equiv> degree p" and "n \<equiv> degree q"
  assumes i: "i < m+n" and j: "j < m+n"
  shows "sylvester_mat p q $$ (i,j) =
    (if i < n then coeff (monom 1 (n - i) * p) (m+n-j)
     else coeff (monom 1 (m + n - i) * q) (m+n-j))"
  apply(subst sylvester_mat_index)
  unfolding m_def[symmetric] n_def[symmetric]
  using i j apply (simp,simp)
  unfolding coeff_monom_mult
  apply(cases "i < n")
  apply (cases "i \<le> j \<and> j - i \<le> m")
  using j m_def apply (force, force simp: coeff_eq_0)
  apply (cases "i - n \<le> j \<and> j \<le> i")
  using i j coeff_eq_0[of q] n_def by auto

lemma sylvester_mat_sub_0[simp]: "sylvester_mat_sub 0 n 0 q = \<zero>\<^sub>m n n"
  unfolding sylvester_mat_sub_def by auto

lemma sylvester_mat_0[simp]: "sylvester_mat 0 q = \<zero>\<^sub>m (degree q) (degree q)"
  unfolding sylvester_mat_def by simp

lemma sylvester_mat_const[simp]:
  fixes a :: "'a :: semiring_1"
  shows "sylvester_mat [:a:] q = a \<odot>\<^sub>m \<one>\<^sub>m (degree q)"
    and "sylvester_mat p [:a:] = a \<odot>\<^sub>m \<one>\<^sub>m (degree p)"
  by(auto simp: sylvester_mat_index)

lemma sylvester_mat_sub_map:
  assumes f0: "f 0 = 0"
  shows "map\<^sub>m f (sylvester_mat_sub m n p q) = sylvester_mat_sub m n (map_poly f p) (map_poly f q)"
    (is "?l = ?r")
proof(rule mat_eqI)
  note [simp] = coeff_map_poly[of f, OF f0]
  show dim: "dim\<^sub>r ?l = dim\<^sub>r ?r" "dim\<^sub>c ?l = dim\<^sub>c ?r" by auto
  fix i j
  assume ij: "i < dim\<^sub>r ?r" "j < dim\<^sub>c ?r"
  note ij' = this[unfolded sylvester_mat_sub_dim]
  note ij'' = ij[unfolded dim[symmetric] mat_index_map]
  show "?l $$ (i, j) = ?r $$ (i,j)"
    unfolding mat_index_map(1)[OF ij''] 
    unfolding sylvester_mat_sub_index[OF ij']
    unfolding Let_def
    using f0 by auto
qed

subsubsection {* Sylvester matrices and vector representation of polynomials *}

definition vec_of_poly_rev_shifted where
  "vec_of_poly_rev_shifted p n j \<equiv>
   vec n (\<lambda>i. if i \<le> j \<and> j \<le> degree p + i then coeff p (degree p + i - j) else 0)"

lemma vec_of_poly_rev_shifted_dim[simp]: "dim\<^sub>v (vec_of_poly_rev_shifted p n j) = n"
  unfolding vec_of_poly_rev_shifted_def by auto

lemma col_sylvester:
  fixes p q
  defines "m \<equiv> degree p" and "n \<equiv> degree q"
  assumes j: "j < m+n"
  shows "col (sylvester_mat p q) j =
    vec_of_poly_rev_shifted p n j @\<^sub>v vec_of_poly_rev_shifted q m j" (is "?l = ?r")
proof
  note [simp] = m_def[symmetric] n_def[symmetric]
  show "dim\<^sub>v ?l = dim\<^sub>v ?r" by simp
  fix i assume "i < dim\<^sub>v ?r" hence i: "i < m+n" by auto
  show "?l $ i = ?r $ i"
    unfolding vec_of_poly_rev_shifted_def
    apply (subst col_index) using i apply simp using j apply simp
    apply (subst sylvester_mat_index) using i apply simp using j apply simp
    apply (cases "i < n") apply force using i by simp
qed

lemma inj_on_diff_nat2: "inj_on (\<lambda>i. (n::nat) - i) {..n}" by (rule inj_onI, auto)
lemma inj_on_diff_nat3: "inj_on (\<lambda>i. i - n::nat) {n..m}" by (rule inj_onI, auto)

lemma image_diff_atMost: "(\<lambda>i. (n::nat) - i) ` {..n} = {..n}" (is "?l = ?r")
  unfolding set_eq_iff
proof (intro allI iffI)
  fix x assume x: "x \<in> ?r"
    thus "x \<in> ?l" unfolding image_def mem_Collect_eq
    by(intro bexI[of _ "n-x"],auto)
qed auto

lemma atLeastAtMost_shift:
  assumes nm: "n \<le> m"
  shows "(\<lambda>i. i - (n::nat)) ` {n..m} = {..m-n}" (is "?l = ?r")
  unfolding set_eq_iff
proof (intro allI iffI)
  fix x assume x: "x \<in> ?r"
  thus "x \<in> ?l" unfolding image_def mem_Collect_eq
    using nm by(intro bexI[of _ "x+n"],auto)
qed auto

lemma sylvester_mat_sum_upper:
  fixes p q :: "'a :: comm_semiring_1 poly"
  defines "m \<equiv> degree p" and "n \<equiv> degree q"
  assumes i: "i < n"
  shows "(\<Sum>j<m+n. monom (sylvester_mat p q $$ (i,j)) (m + n - Suc j)) =
    monom 1 (n - Suc i) * p" (is "setsum ?f _ = ?r")
proof -
  have n1: "n \<ge> 1" using i by auto
  def ni1 \<equiv> "n-Suc i"
  hence ni1: "n-i = Suc ni1" using i by auto
  def l \<equiv> "m+n-1"
  hence l: "Suc l = m+n" using n1 by auto
  let ?g = "\<lambda>j. monom (coeff (monom 1 (n-Suc i) * p) j) j"
  let ?p = "\<lambda>j. l-j"
  have "setsum ?f {..<m+n} = setsum ?f {..l}"
    unfolding l[symmetric] unfolding lessThan_Suc_atMost..
  also {
    fix j assume j: "j\<le>l"
    have "?f j = ((\<lambda>j. monom (coeff (monom 1 (n-i) * p) (Suc j)) j) \<circ> ?p) j"
      apply(subst sylvester_mat_index2)
      using i j unfolding l_def m_def[symmetric] n_def[symmetric]
      by (auto simp add: Suc_diff_Suc)
    also have "... = (?g \<circ> ?p) j"
      unfolding ni1
      unfolding coeff_monom_Suc
      unfolding ni1_def
      using i by auto
    finally have "?f j = (?g \<circ> ?p) j".
  }
  hence "(\<Sum>j\<le>l. ?f j) = (\<Sum>j\<le>l. (?g\<circ>?p) j)" using l by auto
  also have "... = (\<Sum>j\<le>l. ?g j)"
    unfolding l_def
    using setsum.reindex[OF inj_on_diff_nat2,symmetric,unfolded image_diff_atMost].
  also have "degree ?r \<le> l"
      using degree_mult_le[of "monom 1 (n-Suc i)" p]
      unfolding l_def m_def
      unfolding degree_monom_eq[OF one_neq_zero] using i by auto
    from poly_as_sum_of_monoms'[OF this]
    have "(\<Sum>j\<le>l. ?g j) = ?r".
  finally show ?thesis.
qed

lemma sylvester_mat_sum_lower:
  fixes p q :: "'a :: comm_semiring_1 poly"
  defines "m \<equiv> degree p" and "n \<equiv> degree q"
  assumes ni: "n \<le> i" and imn: "i < m+n"
  shows "(\<Sum>j<m+n. monom (sylvester_mat p q $$ (i,j)) (m + n - Suc j)) =
    monom 1 (m + n - Suc i) * q" (is "setsum ?f _ = ?r")
proof -
  def l \<equiv> "m+n-1"
  hence l: "Suc l = m+n" using imn by auto
  def mni1 \<equiv> "m + n - Suc i"
  hence mni1: "m+n-i = Suc mni1" using imn by auto
  let ?g = "\<lambda>j. monom (coeff (monom 1 (m + n - Suc i) * q) j) j"
  let ?p = "\<lambda>j. l-j"
  have "setsum ?f {..<m+n} = setsum ?f {..l}"
    unfolding l[symmetric] unfolding lessThan_Suc_atMost..
  also {
    fix j assume j: "j\<le>l"
    have "?f j = ((\<lambda>j. monom (coeff (monom 1 (m+n-i) * q) (Suc j)) j) \<circ> ?p) j"
      apply(subst sylvester_mat_index2)
      using ni imn j unfolding l_def m_def[symmetric] n_def[symmetric]
      by (auto simp add: Suc_diff_Suc)
    also have "... = (?g \<circ> ?p) j"
      unfolding mni1
      unfolding coeff_monom_Suc
      unfolding mni1_def..
    finally have "?f j = ...".
  }
  hence "(\<Sum>j\<le>l. ?f j) = (\<Sum>j\<le>l. (?g\<circ>?p) j)" by auto
  also have "... = (\<Sum>j\<le>l. ?g j)"
    using setsum.reindex[OF inj_on_diff_nat2,symmetric,unfolded image_diff_atMost].
  also have "degree ?r \<le> l"
      using degree_mult_le[of "monom 1 (m+n-1-i)" q]
      unfolding l_def n_def[symmetric]
      unfolding degree_monom_eq[OF one_neq_zero] using ni imn by auto
    from poly_as_sum_of_monoms'[OF this]
    have "(\<Sum>j\<le>l. ?g j) = ?r".
  finally show ?thesis.
qed

definition "vec_of_poly p \<equiv> let m = degree p in vec (Suc m) (\<lambda>i. coeff p (m-i))"

definition "poly_of_vec v \<equiv> let d = dim\<^sub>v v in \<Sum>i<d. monom (v $ (d - Suc i)) i"

lemma dim_vec_of_poly[simp]: "dim\<^sub>v (vec_of_poly p) = Suc (degree p)"
  unfolding vec_of_poly_def Let_def by auto

lemma vec_of_poly_index[simp]:
  assumes "i \<le> degree p" shows "vec_of_poly p $ i = coeff p (degree p - i)"
  unfolding vec_of_poly_def Let_def
  using assms by auto

lemma poly_of_vec_of_poly[simp]:
  fixes p :: "'a :: comm_monoid_add poly"
  shows "poly_of_vec (vec_of_poly p) = p"
  unfolding poly_of_vec_def vec_of_poly_def Let_def
  unfolding vec_dim_vec
  unfolding lessThan_Suc_atMost
  using poly_as_sum_of_monoms[of p] by auto

lemma vec_of_poly_eq_iff[simp]:
  fixes p q :: "'a :: comm_monoid_add poly"
  shows "vec_of_poly p = vec_of_poly q \<longleftrightarrow> p = q" (is "?p = ?q \<longleftrightarrow> _")
proof (rule iffI)
  assume "?p = ?q"
  hence "poly_of_vec ?p = poly_of_vec ?q" by auto
  thus "p = q" by auto
qed auto 

lemma vec_of_poly_0[simp]:
  fixes p :: "'a :: comm_monoid_add poly"
  shows "vec_of_poly p = \<zero>\<^sub>v (Suc (degree p)) \<longleftrightarrow> p = 0" (is "?p = ?q \<longleftrightarrow> _")
proof
  assume l: "?p = ?q"
  show "p = 0"
  proof (rule poly_eqI, unfold coeff_0)
    fix i
    show "coeff p i = 0"
    proof (cases "i \<le> degree p")
      case True hence "?p $ (degree p - i) = 0" using l by auto
        thus ?thesis unfolding vec_of_poly_def Let_def using True by auto
      next case False thus ?thesis using coeff_eq_0[of p i] by auto
    qed
  qed
  next show "p = 0 \<Longrightarrow> ?p = ?q" unfolding vec_of_poly_def Let_def by auto
qed

lemma poly_of_vec_0[simp]: "poly_of_vec (\<zero>\<^sub>v n) = 0" unfolding poly_of_vec_def Let_def by auto

lemma poly_of_vec_0_iff[simp]:
  fixes v  :: "'a :: comm_monoid_add vec"
  shows "poly_of_vec v = 0 \<longleftrightarrow> v = \<zero>\<^sub>v (dim\<^sub>v v)" (is "?v = _ \<longleftrightarrow> _ = ?z")
proof
  assume "?v = 0"
  hence "\<forall>i\<in>{..<dim\<^sub>v v}. v $ (dim\<^sub>v v - Suc i) = 0"
    unfolding poly_of_vec_def Let_def
    by (subst setsum_monom_0_iff[symmetric],auto)
  hence a: "\<And>i. i < dim\<^sub>v v \<Longrightarrow> v $ (dim\<^sub>v v - Suc i) = 0" by auto
  { fix i assume "i < dim\<^sub>v v"
    hence "v $ i = 0" using a[of "dim\<^sub>v v - Suc i"] by auto
  }
  thus "v = ?z" by auto
  next assume r: "v = ?z"
  show "?v = 0" apply (subst r) by auto
qed

(* TODO: move, copied from no longer existing Cayley-Hamilton/Polynomial_extension *)
lemma degree_setsum_smaller:
  assumes "n > 0" "finite A"
  shows "(\<And> x. x \<in>A \<Longrightarrow> degree (f x) < n) \<Longrightarrow> degree (\<Sum>x\<in>A. f x) < n"
  using `finite A`
  by(induct rule: finite_induct)
    (simp_all add: degree_add_less assms)

lemma degree_poly_of_vec_less:
  fixes v :: "'a :: comm_monoid_add vec"
  assumes dim: "dim\<^sub>v v > 0"
  shows "degree (poly_of_vec v) < dim\<^sub>v v"
  unfolding poly_of_vec_def Let_def
  apply(rule degree_setsum_smaller)
    using dim apply force
    apply force
  unfolding lessThan_iff
  by (metis degree_0 degree_monom_eq dim monom_eq_0_iff)

lemma coeff_poly_of_vec:
  "coeff (poly_of_vec v) i = (if i < dim\<^sub>v v then v $ (dim\<^sub>v v - Suc i) else 0)"
  (is "?l = ?r")
proof -
  have "?l = (\<Sum>x<dim\<^sub>v v. if x = i then v $ (dim\<^sub>v v - Suc x) else 0)" (is "_ = ?m")
    unfolding poly_of_vec_def Let_def coeff_setsum coeff_monom ..
  also have "\<dots> = ?r"
  proof (cases "i < dim\<^sub>v v")
    case False
    show ?thesis
      by (subst setsum.neutral, insert False, auto)
  next
    case True
    show ?thesis
      by (subst setsum.remove[of _ i], force, force simp: True, subst setsum.neutral, insert True, auto)
  qed
  finally show ?thesis .
qed

lemma coeff_poly_of_vec_in:
  assumes i: "i < dim\<^sub>v v"
  shows "coeff (poly_of_vec v) i = v $ (dim\<^sub>v v - Suc i)"
  unfolding coeff_poly_of_vec using i by simp

lemma vec_of_poly_rev_shifted_scalar_prod:
  fixes p v
  defines "q \<equiv> poly_of_vec v"
  assumes m[simp]: "degree p = m" and n: "dim\<^sub>v v = n"
  assumes j: "j < m+n"
  shows "vec_of_poly_rev_shifted p n (n+m-Suc j) \<bullet> v = coeff (p * q) j" (is "?l = ?r")
proof -
  have id1: "\<And> i. m + i - (n + m - Suc j) = i + Suc j - n"
    using j by auto
  let ?g = "\<lambda> i. if i \<le> n + m - Suc j \<and> n - Suc j \<le> i then coeff p (i + Suc j - n) *  v $ i else 0"
  have "?thesis = ((\<Sum>i = 0..<n. ?g i) =          
        (\<Sum>i\<le>j. coeff p i * (if j - i < n then v $ (n - Suc (j - i)) else 0)))" (is "_ = (?l = ?r)")
    unfolding vec_of_poly_rev_shifted_def coeff_mult m scalar_prod_def n q_def
      coeff_poly_of_vec 
    by (subst setsum.cong, insert id1, auto)
  also have "..." 
  proof -
    have "?r = (\<Sum>i\<le>j. (if j - i < n then coeff p i * v $ (n - Suc (j - i)) else 0))" (is "_ = setsum ?f _")
      by (rule setsum.cong, auto)
    also have "setsum ?f {..j} = setsum ?f ({i. i \<le> j \<and> j - i < n} \<union> {i. i \<le> j \<and> \<not> j - i < n})" 
      (is "_ = setsum _ (?R1 \<union> ?R2)")
      by (rule setsum.cong, auto)
    also have "\<dots> = setsum ?f ?R1 + setsum ?f ?R2"
      by (subst setsum.union_disjoint, auto)
    also have "setsum ?f ?R2 = 0"
      by (rule setsum.neutral, auto)
    also have "setsum ?f ?R1 + 0 = setsum (\<lambda> i. coeff p i * v $ (i + n - Suc j)) ?R1"
      (is "_ = setsum ?F _")
      by (subst setsum.cong, auto simp: ac_simps)
    also have "\<dots> = setsum ?F ((?R1 \<inter> {..m}) \<union> (?R1 - {..m}))"
      (is "_ = setsum _ (?R \<union> ?R')")
      by (rule setsum.cong, auto)
    also have "\<dots> = setsum ?F ?R + setsum ?F ?R'"
      by (subst setsum.union_disjoint, auto)
    also have "setsum ?F ?R' = 0"
    proof -
      { 
        fix x
        assume "x > m" 
        from coeff_eq_0[OF this[folded m]]
        have "?F x = 0" by simp
      }
      thus ?thesis
        by (subst setsum.neutral, auto)
    qed
    finally have r: "?r = setsum ?F ?R" by simp

    have "?l = setsum ?g ({i. i < n \<and> i \<le> n + m - Suc j \<and> n - Suc j \<le> i} 
      \<union> {i. i < n \<and> \<not> (i \<le> n + m - Suc j \<and> n - Suc j \<le> i)})" 
      (is "_ = setsum _ (?L1 \<union> ?L2)")
      by (rule setsum.cong, auto)
    also have "\<dots> = setsum ?g ?L1 + setsum ?g ?L2"
      by (subst setsum.union_disjoint, auto)
    also have "setsum ?g ?L2 = 0"
      by (rule setsum.neutral, auto)
    also have "setsum ?g ?L1 + 0 = setsum (\<lambda> i. coeff p (i + Suc j - n) * v $ i) ?L1"
      (is "_ = setsum ?G _")
      by (subst setsum.cong, auto)
    also have "\<dots> = setsum ?G (?L1 \<inter> {i. i + Suc j - n \<le> m} \<union> (?L1 - {i. i + Suc j - n \<le> m}))"
      (is "_ = setsum _ (?L \<union> ?L')")
      by (subst setsum.cong, auto)
    also have "\<dots> = setsum ?G ?L + setsum ?G ?L'"      
      by (subst setsum.union_disjoint, auto)
    also have "setsum ?G ?L' = 0"
    proof -
      {
        fix x
        assume "x + Suc j - n > m" 
        from coeff_eq_0[OF this[folded m]]
        have "?G x = 0" by simp
      }
      thus ?thesis
        by (subst setsum.neutral, auto)
    qed
    finally have l: "?l = setsum ?G ?L" by simp

    let ?bij = "\<lambda> i. i + n - Suc j"
    {
      fix x
      assume x: "j < m + n" "Suc (x + j) - n \<le> m" "x < n" "n - Suc j \<le> x" 
      def y \<equiv> "x + Suc j - n"
      from x have "x + Suc j \<ge> n" by auto
      with x have xy: "x = ?bij y" unfolding y_def by auto
      from x have y: "y \<in> ?R" unfolding y_def by auto
      have "x \<in> ?bij ` ?R" unfolding xy using y by blast
    } note tedious = this
    show ?thesis unfolding l r
      by (rule setsum.reindex_cong[of ?bij], insert j, auto simp: inj_on_def tedious)
  qed
  finally show ?thesis by simp
qed

lemma sylvester_vec_poly:
  fixes p q :: "'a :: comm_semiring_0 poly"
  defines "m \<equiv> degree p"
      and "n \<equiv> degree q"
  assumes v: "v \<in> carrier\<^sub>v (m+n)"
  shows "poly_of_vec (transpose\<^sub>m (sylvester_mat p q) \<otimes>\<^sub>m\<^sub>v v) =
    poly_of_vec (vec_first v n) * p + poly_of_vec (vec_last v m) * q" (is "?l = ?r")
proof (rule poly_eqI)
  fix i
  note mn[simp] = m_def[symmetric] n_def[symmetric]
  let ?Tv = "transpose\<^sub>m (sylvester_mat p q) \<otimes>\<^sub>m\<^sub>v v"
  have dim: "dim\<^sub>v (vec_first v n) = n" "dim\<^sub>v (vec_last v m) = m" "dim\<^sub>v ?Tv = n + m" 
    using v by auto
  have if_distrib: "\<And> x y z. (if x then y else (0 :: 'a)) * z = (if x then y * z else 0)" 
    by auto
  show "coeff ?l i = coeff ?r i"
  proof (cases "i < m+n")
    case False
      hence i_mn: "i \<ge> m+n"
        and i_n: "\<And>x. x \<le> i \<and> x < n \<longleftrightarrow> x < n"
        and i_m: "\<And>x. x \<le> i \<and> x < m \<longleftrightarrow> x < m" by auto
      have "coeff ?r i =
            (\<Sum> x < n. vec_first v n $ (n - Suc x) * coeff p (i - x)) +
            (\<Sum> x < m. vec_last v m $ (m - Suc x) * coeff q (i - x))"
        (is "_ = setsum ?f _ + setsum ?g _")
        unfolding coeff_add coeff_mult Let_def 
        unfolding coeff_poly_of_vec dim if_distrib
        unfolding atMost_def
        apply(subst setsum.inter_filter[symmetric],simp)
        apply(subst setsum.inter_filter[symmetric],simp)
        unfolding mem_Collect_eq
        unfolding i_n i_m
        unfolding lessThan_def by simp
      also { fix x assume x: "x < n"
        have "coeff p (i-x) = 0"
          apply(rule coeff_eq_0) using i_mn x unfolding m_def by auto
        hence "?f x = 0" by auto
      } hence "setsum ?f {..<n} = 0" by auto
      also { fix x assume x: "x < m"
        have "coeff q (i-x) = 0"
          apply(rule coeff_eq_0) using i_mn x unfolding n_def by auto
        hence "?g x = 0" by auto
      } hence "setsum ?g {..<m} = 0" by auto
      finally have "coeff ?r i = 0" by auto
      also from False have "0 = coeff ?l i"
        unfolding coeff_poly_of_vec dim setsum.distrib[symmetric] by auto
      finally show ?thesis by auto
    next case True
      hence "coeff ?l i = (transpose\<^sub>m (sylvester_mat p q) \<otimes>\<^sub>m\<^sub>v v) $ (n + m - Suc i)"
        unfolding coeff_poly_of_vec dim setsum.distrib[symmetric] by auto
      also have "... = coeff (p * poly_of_vec (vec_first v n) + q * poly_of_vec (vec_last v m)) i"
        apply(subst index_mat_mult_vec) using True apply simp
        apply(subst row_transpose) using True apply simp
        apply(subst col_sylvester)
        unfolding mn using True apply simp
        apply(subst vec_first_last_append[of v n m,symmetric]) using v apply(simp add: add.commute)
        apply(subst scalar_prod_append)
        apply (rule vec_elemsI,simp)+
        apply (subst vec_of_poly_rev_shifted_scalar_prod,simp,simp) using True apply simp
        apply (subst add.commute[of n m])
        apply (subst vec_of_poly_rev_shifted_scalar_prod,simp,simp) using True apply simp
        by simp
      also have "... =
        (\<Sum>x\<le>i. (if x < n then vec_first v n $ (n - Suc x) else 0) * coeff p (i - x)) +
        (\<Sum>x\<le>i. (if x < m then vec_last v m $ (m - Suc x) else 0) * coeff q (i - x))"
        unfolding coeff_poly_of_vec[of "vec_first v n",unfolded dim_vec_first,symmetric]
        unfolding coeff_poly_of_vec[of "vec_last v m",unfolded dim_vec_last,symmetric]
        unfolding coeff_mult[symmetric] by (simp add: mult.commute)
      also have "... = coeff ?r i"
        unfolding coeff_add coeff_mult Let_def
        unfolding coeff_poly_of_vec dim..
      finally show ?thesis.
  qed
qed

subsection \<open>Resultant\<close>

definition resultant :: "'a poly \<Rightarrow> 'a poly \<Rightarrow> 'a :: comm_ring_1" where
  "resultant p q = det (sylvester_mat p q)"

text {* Resultant, but the size of the base Sylvester matrix is given. *}

definition "resultant_sub m n p q = det (sylvester_mat_sub m n p q)"

lemma resultant_sub: "resultant p q = resultant_sub (degree p) (degree q) p q"
  unfolding resultant_def sylvester_mat_def resultant_sub_def by auto

lemma resultant_const[simp]:
  fixes a :: "'a :: comm_ring_1"
  shows "resultant [:a:] q = a ^ (degree q)"
    and "resultant p [:a:] = a ^ (degree p)"
  unfolding resultant_def unfolding sylvester_mat_const by simp_all

lemma resultant_1[simp]:
  fixes p :: "'a :: comm_ring_1 poly"
  shows "resultant 1 p = 1" "resultant p 1 = 1"
  unfolding one_poly_def by auto

lemma resultant_0[simp]:
  fixes p :: "'a :: comm_ring_1 poly"
  assumes "degree p > 0"
  shows "resultant 0 p = 0" "resultant p 0 = 0"
  using resultant_const(1)[of 0 p] resultant_const(2)[of p 0]
  using zero_power assms by auto

lemma resultant_swap: "resultant f g = 
  (if even (degree f) \<or> even (degree g) then resultant g f else - resultant g f)"
proof -
  def sw \<equiv> "\<lambda> (A :: 'a mat) xs. fold (\<lambda> (i,j). swaprows i j) xs A"
  {
    fix xs and A
    have "dim\<^sub>r (sw A xs) = dim\<^sub>r A" "dim\<^sub>c (sw A xs) = dim\<^sub>c A"
      unfolding sw_def by (induct xs arbitrary: A, auto)
  } note dim_sw[simp] = this
  {
    fix xs and A :: "'a mat"
    assume "dim\<^sub>r A = dim\<^sub>c A" "\<And> i j. (i,j) \<in> set xs \<Longrightarrow> i < dim\<^sub>c A \<and> j < dim\<^sub>c A \<and> i \<noteq> j"
    hence "det (sw A xs) = (if even (length xs) then det A else - det A)"
      unfolding sw_def
    proof (induct xs arbitrary: A)
      case (Cons xy xs A)
      obtain x y where xy: "xy = (x,y)" by force
      from Cons(3)[unfolded xy, of x y] Cons(2)
      have [simp]: "det (swaprows x y A) = - det A"
        by (intro det_swaprows, auto)
      show ?case unfolding xy by (simp, insert Cons(2-), (subst Cons(1), auto)+)
    qed simp
  } note sw = this
  def swb \<equiv> "\<lambda> A i n. sw A (map (\<lambda> j. (j,Suc j)) [i ..< i + n])"
  {
    fix k n and A :: "'a mat"
    assume k_n: "k + n < dim\<^sub>r A"
    hence "swb A k n = mat (dim\<^sub>r A) (dim\<^sub>c A) (\<lambda> (i,j). let r = 
      (if i < k \<or> i > k + n then i else if i = k + n then k else Suc i)
      in A $$ (r,j))"
    proof (induct n)
      case 0
      show ?case unfolding swb_def sw_def by (rule mat_eqI, auto)
    next
      case (Suc n)
      hence dim: "k + n < dim\<^sub>r A" by auto
      have id: "swb A k (Suc n) = swaprows (k + n) (Suc k + n) (swb A k n)" unfolding swb_def sw_def by simp
      show ?case unfolding id Suc(1)[OF dim]
        by (rule mat_eqI, insert Suc(2), auto)
    qed
  } note swb = this
  def swbl \<equiv> "\<lambda> A k n. fold (\<lambda> i A. swb A i n) (rev [0 ..< k]) A"
  {
    fix k n and A :: "'a mat"
    assume k_n: "k + n \<le> dim\<^sub>r A"
    hence "swbl A k n = mat (dim\<^sub>r A) (dim\<^sub>c A) (\<lambda> (i,j). let r = 
      (if i < n then i + k else if i < k + n then i - n else i)
      in A $$ (r,j))"
    proof (induct k arbitrary: A)
      case 0
      thus ?case unfolding swbl_def by (intro mat_eqI, auto simp: swb)
    next
      case (Suc k)
      hence dim: "k + n < dim\<^sub>r A" by auto
      have id: "swbl A (Suc k) n = swbl (swb A k n) k n" unfolding swbl_def by simp
      show ?case unfolding id swb[OF dim]
        by (subst Suc(1), insert dim, force, intro mat_eqI, auto simp: less_Suc_eq_le) 
    qed
  } note swbl = this
  {
    fix k n and A :: "'a mat"
    assume k_n: "k + n \<le> dim\<^sub>c A" "dim\<^sub>r A = dim\<^sub>c A" 
    hence "det (swbl A k n) = (if even (k * n) then det A else - det A)"
    proof (induct k arbitrary: A)
      case 0
      thus ?case unfolding swbl_def by auto
    next
      case (Suc k)
      hence dim: "k + n < dim\<^sub>r A" by auto
      have id: "swbl A (Suc k) n = swbl (swb A k n) k n" unfolding swbl_def by simp
      have det: "det (swb A k n) = (if even n then det A else - det A)" unfolding swb_def
        by (subst sw, insert Suc(2-), auto)
      show ?case unfolding id 
        by (subst Suc(1), insert Suc(2-), auto simp: det, auto simp: swb)
    qed
  } note det_swbl = this
  let ?dg = "degree g" let ?df = "degree f"
  have le: "?dg + ?df \<le> dim\<^sub>r (sylvester_mat f g)" by simp
  have gf: "sylvester_mat g f = swbl (sylvester_mat f g) ?dg ?df"
    unfolding swbl[OF le]
    by (rule mat_eqI, auto simp: sylvester_mat_def sylvester_mat_sub_def ac_simps)
  have gf: "resultant g f = (if even (?dg * ?df) then resultant f g else - resultant f g)"
    unfolding resultant_def gf
    by (subst det_swbl, auto)
  show ?thesis unfolding gf by auto
qed

lemma resultant_smult_left: assumes "(c :: 'a :: idom) \<noteq> 0" 
  shows "resultant (smult c f) g = c ^ degree g * resultant f g"
proof -
  let ?df = "degree f"
  let ?dg = "degree g"
  let ?d = "?df + ?dg"
  from `c \<noteq> 0` have deg: "degree (smult c f) = ?df" by simp
  def list \<equiv> "[0..< ?dg]"
  let ?S = "sylvester_mat f g"
  let ?cS = "sylvester_mat (smult c f) g"
  let ?fS' = "\<lambda> xs. fold (\<lambda> i A. mat_multrow i c A) xs ?S"
  let ?fS = "?fS' [0..< ?dg]"
  def dg \<equiv> ?dg  
  def S \<equiv> ?S
  have dim: "dim\<^sub>r ?S = ?d" "dim\<^sub>c ?S = ?d"  "dim\<^sub>r ?cS = ?d" "dim\<^sub>c ?cS = ?d" using deg by auto
  {
    fix list
    have "dim\<^sub>r (?fS' list) = degree f + degree g"
      "dim\<^sub>c (?fS' list) = degree f + degree g"
      using dim(1-2) unfolding S_def[symmetric]
      by (induct list arbitrary: S, auto)
  } note dim_f = this
  have dim': "dim\<^sub>r ?fS = ?d" "dim\<^sub>c ?fS = ?d" by (auto simp: dim_f)
  have id: "?cS = ?fS"
  proof (rule mat_eqI, unfold dim dim')
    fix i j
    assume ij: "i < ?d" "j < ?d"
    {
      fix A :: "'a mat" and xs
      assume "A \<in> carrier\<^sub>m ?d ?d" "i \<notin> set xs"
      hence "(fold (\<lambda> i A. mat_multrow i c A) xs A) $$ (i,j) = A $$ (i,j)"
        by (induct xs arbitrary: A, insert ij, auto)
    } note nmem = this
    have cS: "?cS $$ (i,j) = (if i < ?dg then c * ?S $$ (i,j) else ?S $$ (i,j))" 
      by (subst sylvester_mat_index, unfold deg, rule ij(1), rule ij(2), unfold sylvester_mat_index[OF ij]) auto
    also have "\<dots> = ?fS $$ (i,j)"
    proof (cases "i < ?dg")
      case False
      show ?thesis
        by (subst nmem, insert False, auto)
    next
      case True
      hence list: "list = [0..<i] @ [i] @ [Suc i ..< ?dg]" unfolding list_def
        by (metis append_Cons append_self_conv2 le0 less_imp_add_positive upt_add_eq_append upt_rec)
      have "?fS $$ (i,j) = (mat_multrow i c (?fS' [0 ..<i])) $$ (i,j)"
        unfolding list_def[symmetric] list fold_append o_def
        by (subst nmem, auto simp: dim_f)
      also have "\<dots> = c * ?fS' [0 ..< i] $$ (i,j)"
        by (subst mat_index_multrow, insert ij, auto simp: dim_f)
      also have "?fS' [0 ..< i] $$ (i,j) = ?S $$ (i,j)"
        by (subst nmem, auto)
      finally show ?thesis using True by simp
    qed
    finally show "?cS $$ (i,j) = ?fS $$ (i,j)" by simp
  qed auto
  have dg: "dg = length list" and sq: "dim\<^sub>r S = dim\<^sub>c S" and list: "set list \<subseteq> {0 ..< dim\<^sub>c S}" 
    unfolding dg_def list_def S_def by auto
  from list sq show ?thesis 
    unfolding resultant_def id list_def[symmetric] S_def[symmetric] unfolding dg_def[symmetric] dg
  proof (induct list arbitrary: S)
    case (Cons i list)
    show ?case
      by (simp, subst Cons(1), insert Cons(2-) `c \<noteq> 0`, auto intro!: det_multrow)
  qed simp
qed

lemma resultant_smult_right: assumes c: "(c :: 'a :: idom) \<noteq> 0" 
  shows "resultant f (smult c g) = c ^ degree f * resultant f g"
  unfolding resultant_swap[of f] unfolding resultant_smult_left[OF c] using c
  by simp

subsubsection{* Results for Over-Sized Sylvester Matrices *}

lemma sylvester_mat_sub_too_big_lower:
  assumes deg: "n \<ge> degree q"
  shows "mat_delete (sylvester_mat_sub m (Suc n) p q) 0 0 = sylvester_mat_sub m n p q"
    (is "?L = ?R")
  apply (rule mat_eqI)
  unfolding four_block_mat_index dim_mat_of sylvester_mat_sub_dim
proof -
  note [simp] = sylvester_mat_sub_index
  fix i j assume imn: "i < m + n" and jmn: "j < m + n"
  hence SimSn: "Suc i < m + Suc n"
    and SjmSn: "Suc j < m + Suc n" by auto
  show "?L $$ (i,j) = ?R $$ (i,j)"
    apply(subst mat_delete_index[symmetric])
  proof-
    show "sylvester_mat_sub m (Suc n) p q $$ (insert_index 0 i, insert_index 0 j) =
      sylvester_mat_sub m n p q $$ (i, j)"
      proof(cases "i < Suc n")
        case True thus ?thesis
          unfolding sylvester_mat_sub_index[OF imn jmn]
          using coeff_eq_0[of q] deg
          by (auto simp: sylvester_mat_sub_index[OF SimSn SjmSn])
        next case False thus ?thesis
          unfolding sylvester_mat_sub_index[OF imn jmn]
          using coeff_eq_0[of q] deg imn
          by (auto simp: sylvester_mat_sub_index[OF SimSn SjmSn])
      qed
  qed (auto simp: imn jmn)
qed auto

lemma sylvester_mat_sub_too_big_upper:
  assumes deg: "m \<ge> degree p"
  shows "mat_delete (sylvester_mat_sub (Suc m) n p q) n 0 = sylvester_mat_sub m n p q"
    (is "?L = ?R")
  apply (rule mat_eqI)
  unfolding four_block_mat_index dim_mat_of sylvester_mat_sub_dim
proof -
  note [simp] = sylvester_mat_sub_index
  fix i j assume imn: "i < m + n" and jmn: "j < m + n"
  hence iSmn: "i < Suc m + n"
    and SiSmn: "Suc i < Suc m + n"
    and SjSmn: "Suc j < Suc m + n" by auto
  show "?L $$ (i,j) = ?R $$ (i,j)"
    apply(subst mat_delete_index[symmetric])
  proof-
    show "sylvester_mat_sub (Suc m) n p q $$ (insert_index n i, insert_index 0 j) =
      sylvester_mat_sub m n p q $$ (i, j)"
      proof(cases "i < n")
        case True thus ?thesis
          unfolding sylvester_mat_sub_index[OF imn jmn]
          using coeff_eq_0[of p] deg
          by (auto simp: sylvester_mat_sub_index[OF iSmn SjSmn])
        next case False thus ?thesis
          unfolding sylvester_mat_sub_index[OF imn jmn]
          using coeff_eq_0[of p] deg imn
          by (auto simp: sylvester_mat_sub_index[OF SiSmn SjSmn])
      qed
  qed (auto simp: imn jmn)
qed auto

lemma sylvester_mat_sub_index_most_0:
  assumes m: "m \<ge> degree p" and n: "n \<ge> degree q" and i: "i < m+n"
  shows "sylvester_mat_sub m n p q $$ (i,0) =
    (if i = 0 \<and> n \<noteq> 0 then coeff p m else if i = n then coeff q n else 0)"
  using assms by(subst sylvester_mat_sub_index, auto)

lemma det_sylvester_mat_sub_too_big_lower:
  assumes m: "m \<ge> degree p" and n: "n \<ge> degree q"
  shows "det (sylvester_mat_sub m (Suc n) p q) = coeff p m * det (sylvester_mat_sub m n p q)"
    (is "det ?l = ?r")
proof -
  have "det ?l = (\<Sum>i < m + Suc n. ?l $$ (i, 0) * cofactor ?l i 0)"
    (is "_ = setsum ?f _")
    apply(subst laplace_expansion_column[OF sylvester_mat_sub_carrier,of 0])
    unfolding sylvester_mat_sub_dim by auto
  also have "{..< m + Suc n} = {..m+n}" by auto
  also have "... = insert 0 (insert n ({..m+n}-{0,n}))" (is "_ = insert _ (insert _ ?r')") by auto
  also have "setsum ?f ... = ?f 0 + setsum ?f ?r'" (is "setsum _ ?l' = _")
    proof(cases "n = 0")
      case True
        hence "?r' = {..m+n}-{0}" by simp
        also have "insert n ... = {..m+n}" unfolding True by auto
        also have "insert 0 ... = {..m+n}" by auto
        finally have "?l' = insert 0 ?r'" by auto
        thus ?thesis by auto
      next case False
        have "setsum ?f ?l' = ?f 0 + ?f n + setsum ?f ?r'" using False by auto
        also have "?f n = 0" using False n by(subst sylvester_mat_sub_index;simp)
        finally show ?thesis by auto
    qed
  also {
    fix i assume i: "i \<in> {..m+n}-{0,n}"
    have "?l $$ (i,0) = 0"
      apply(subst sylvester_mat_sub_index_most_0)
      using m i n coeff_eq_0[of q] by auto
    hence "?f i = 0" by auto
  } hence "setsum ?f ({..m+n}-{0,n}) = 0" by auto
  also have "?f 0 = ?r"
    unfolding cofactor_def
    unfolding sylvester_mat_sub_too_big_lower[OF n]
    by(subst(1) sylvester_mat_sub_index;simp)
  finally show ?thesis by simp
qed

lemma det_sylvester_mat_sub_too_big_upper:
  assumes m: "m \<ge> degree p" and n: "n \<ge> degree q"
  shows "det (sylvester_mat_sub (Suc m) n p q) = (-1)^n * coeff q n * det (sylvester_mat_sub m n p q)"
    (is "det ?l = ?r")
proof -
  have "det ?l = (\<Sum>i < Suc m + n. ?l $$ (i, 0) * cofactor ?l i 0)"
    (is "_ = setsum ?f _")
    apply(subst laplace_expansion_column[OF sylvester_mat_sub_carrier,of 0])
    unfolding sylvester_mat_sub_dim by auto
  also have "{..< Suc m + n} = {..m+n}" by auto
  also have "... = insert 0 (insert n ({..m+n}-{0,n}))" (is "_ = insert _ (insert _ ?r')") by auto
  also have "setsum ?f ... = ?f n + setsum ?f ?r'" (is "setsum _ ?l' = _")
    proof(cases "n = 0")
      case True
        hence "?r' = {..m+n}-{n}" by simp
        also have "insert n ... = {..m+n}" unfolding True by auto
        also have "insert 0 ... = {..m+n}" by auto
        finally have "?l' = insert n ?r'" by auto
        thus ?thesis by auto
      next case False
        have "setsum ?f ?l' = ?f 0 + ?f n + setsum ?f ?r'" using False by auto
        also have "?f 0 = 0"
          using coeff_eq_0[of p] False m n by(subst sylvester_mat_sub_index,auto)
        finally show ?thesis by auto
    qed
  also {
    fix i assume i: "i \<in> {..m+n}-{0,n}"
    have "?l $$ (i,0) = 0"
      apply(subst sylvester_mat_sub_index_most_0)
      using m i n coeff_eq_0[of q] by auto
    hence "?f i = 0" by auto
  } hence "setsum ?f ({..m+n}-{0,n}) = 0" by auto
  also have "?f n = ?r"
    unfolding cofactor_def
    unfolding sylvester_mat_sub_too_big_upper[OF m]
    by(subst(1) sylvester_mat_sub_index;simp)
  finally show ?thesis by simp
qed

lemma cofactor_sylvester_too_big_upper:
  assumes m: "m \<ge> degree p"
  shows "cofactor (sylvester_mat_sub (Suc m) n p q) n 0 = (- 1) ^ n * resultant_sub m n p q"
  unfolding cofactor_def
  using sylvester_mat_sub_too_big_upper[OF m]
  unfolding resultant_sub_def by auto

lemma resultant_sub_too_big_upper:
  assumes m: "m \<ge> degree p"
  shows "resultant_sub (Suc m) n p q = (- 1) ^ n * coeff q n * resultant_sub m n p q" (is "?l = ?r")
proof -
  have hint: "coeff p (Suc m) = 0" using m using le_degree less_le_trans not_le by blast
  let ?S = "sylvester_mat_sub (Suc m) n p q"
  have "?l = det ?S" unfolding resultant_sub_def by auto
  also have "... =  (\<Sum>i<Suc m + n. ?S $$ (i,0) * cofactor ?S i 0)"
        (is "_ = setsum ?f ?I")
    apply(subst laplace_expansion_column[OF sylvester_mat_sub_carrier,of 0],simp)
    unfolding sylvester_mat_sub_dim..
  also have "?I = insert n (?I - {n})" by auto
  also have "setsum ?f ... = ?f n + setsum ?f (?I-{n})" by (simp add: setsum.insert_remove)
  also have "?f n = ?r"
    unfolding cofactor_sylvester_too_big_upper[OF m]
    by(subst sylvester_mat_sub_index,auto)
  also have "setsum ?f (?I-{n}) = 0"
    apply (rule setsum.neutral) using hint by (auto simp: sylvester_mat_sub_index)
  finally show ?thesis by auto
qed

lemma resultant_sub_trim_upper:
  shows "resultant_sub (degree p + m) n p q = ((-1)^n * coeff q n)^m * resultant_sub (degree p) n p q"
  by (induct "m"; simp add: resultant_sub_too_big_upper)

lemma cofactor_sylvester_too_big_lower:
  assumes n: "n \<ge> degree q"
  shows "cofactor (sylvester_mat_sub m (Suc n) p q) 0 0 = resultant_sub m n p q"
  unfolding cofactor_def
  using sylvester_mat_sub_too_big_lower[OF n]
  unfolding resultant_sub_def by auto

lemma resultant_sub_too_big_lower:
  assumes n: "n \<ge> degree q"
  shows "resultant_sub m (Suc n) p q = coeff p m * resultant_sub m n p q" (is "?l = ?r")
proof -
  have hint: "coeff q (Suc n) = 0" using n using le_degree less_le_trans not_le by blast
  let ?S = "sylvester_mat_sub m (Suc n) p q"
  have "?l = det ?S" unfolding resultant_sub_def by auto
  also have "... =  (\<Sum>i<Suc m + n. ?S $$ (i,0) * cofactor ?S i 0)"
        (is "_ = setsum ?f ?I")
    apply(subst laplace_expansion_column[OF sylvester_mat_sub_carrier,of 0],simp)
    unfolding sylvester_mat_sub_dim by auto
  also have "?I = insert 0 (?I - {0})" by auto
  also have "setsum ?f ... = ?f 0 + setsum ?f (?I-{0})" by (simp add: setsum.insert_remove)
  also have "?f 0 = ?r"
    unfolding cofactor_sylvester_too_big_lower[OF n]
    by(subst sylvester_mat_sub_index,auto)
  also have "setsum ?f (?I-{0}) = 0"
    apply (rule setsum.neutral) using hint by (auto simp: sylvester_mat_sub_index)
  finally show ?thesis by auto
qed

lemma resultant_sub_trim_lower:
  shows "resultant_sub m (degree q + n) p q = coeff p m ^ n * resultant_sub m (degree q) p q"
  by (induct "n"; simp add: resultant_sub_too_big_lower)

subsubsection \<open>Homomorphism and Resultant\<close>

text \<open>Here we prove Lemma~7.3.1 of the textbook.\<close>

lemma(in ring_hom) resultant_sub_map_poly:
  fixes p q :: "'a poly"
  shows "hom (resultant_sub m n p q) = resultant_sub m n (map_poly hom p) (map_poly hom q)"
    (is "?l = ?r'")
proof -
  let ?mh = "map_poly hom"
  have "?l = det (sylvester_mat_sub m n (?mh p) (?mh q))"
    unfolding resultant_sub_def
    apply(subst sylvester_mat_sub_map[symmetric]) by auto
  thus ?thesis unfolding resultant_sub_def.
qed

lemma (in ring_hom) resultant_map_poly:
  fixes p q :: "'a poly"
    defines "p' \<equiv> map_poly hom p"
    defines "q' \<equiv> map_poly hom q"
    defines "m \<equiv> degree p"
    defines "n \<equiv> degree q"
    defines "m' \<equiv> degree p'"
    defines "n' \<equiv> degree q'"
    defines "r \<equiv> resultant p q"
    defines "r' \<equiv> resultant p' q'"
  shows "m' = m \<Longrightarrow> n' = n \<Longrightarrow> hom r = r'"
    and "m' = m \<Longrightarrow> hom r = hom (coeff p m')^(n-n') * r'"
    and "m' \<noteq> m \<Longrightarrow> n' = n \<Longrightarrow>
      hom r = (if even n then 1 else (-1)^(m-m')) * hom (coeff q n)^(m-m') * r'"
      (is "_ \<Longrightarrow> _ \<Longrightarrow> ?goal")
    and "m' \<noteq> m \<Longrightarrow> n' \<noteq> n \<Longrightarrow> hom r = 0"
proof -
  have m'm: "m' \<le> m" unfolding m_def m'_def p'_def using degree_map_poly_le by auto
  have n'n: "n' \<le> n" unfolding n_def n'_def q'_def using degree_map_poly_le by auto

  have coeffp'[simp]: "\<And>i. coeff p' i = hom (coeff p i)" unfolding p'_def by auto
  have coeffq'[simp]: "\<And>i. coeff q' i = hom (coeff q i)" unfolding q'_def by auto

  let ?f = "\<lambda>i. (if even n then 1 else (-1)^i) * hom (coeff q n)^i"

  have "hom r = resultant_sub m n p' q'"
    unfolding r_def resultant_sub
    unfolding m_def n_def p'_def q'_def
    by(rule resultant_sub_map_poly)
  also have "... = ?f (m-m') * resultant_sub m' n p' q'"
    using resultant_sub_trim_upper[of p' "m-m'" n q',folded m'_def] m'm
    by (auto simp: power_minus[symmetric])
  also have "... = ?f (m-m') * hom (coeff p m')^(n-n') * r'"
    using resultant_sub_trim_lower[of m' q' "n-n'" p'] n'n
    unfolding r'_def resultant_sub m'_def n'_def by auto
  finally have main: "hom r = ?f (m-m') * hom (coeff p m')^(n-n') * r'" by auto

  { assume "m' = m"
    thus "hom r = hom (coeff p m')^(n-n') * r'" using main by auto
    thus "n' = n \<Longrightarrow> hom r = r'" by auto
  }
  assume "m' \<noteq> m"
  hence m'm: "m' < m" using m'm by auto
  thus "n' = n \<Longrightarrow> ?goal" using main by simp
  assume "n' \<noteq> n"
  hence "n' < n" using n'n by auto
  hence "hom (coeff q n) = 0"
    unfolding coeffq'[symmetric] unfolding n'_def by(rule coeff_eq_0)
  hence "hom (coeff q n) ^ (m-m') = 0" using m'm by (simp add: power_0_left)
  from main[unfolded this]
  show "hom r = 0" using power_0_Suc by auto
qed

lemma (in inj_ring_hom) resultant_hom: "resultant (map_poly hom p) (map_poly hom q) = hom (resultant p q)"
  by (subst resultant_map_poly(1), auto)
  
subsubsection\<open>Resultant as Polynomial Expression\<close>
context begin
text {* This context provides notions for proving Lemma 7.2.1 of the textbook. *}

private fun mk_poly_sub where
  "mk_poly_sub A l 0 = A"
| "mk_poly_sub A l (Suc j) = mat_addcol (monom 1 (Suc j)) l (l-Suc j) (mk_poly_sub A l j)"

definition  "mk_poly A = mk_poly_sub (mat_map coeff_lift A) (dim\<^sub>c A - 1) (dim\<^sub>c A - 1)"

private lemma mk_poly_sub_dim[simp]:
  "dim\<^sub>r (mk_poly_sub A l j) = dim\<^sub>r A"
  "dim\<^sub>c (mk_poly_sub A l j) = dim\<^sub>c A"
  by (induct j,auto)

private lemma mk_poly_sub_carrier:
  assumes "A \<in> carrier\<^sub>m nr nc" shows "mk_poly_sub A l j \<in> carrier\<^sub>m nr nc"
  apply (rule mat_carrierI) using assms by auto

private lemma mk_poly_dim[simp]:
  "dim\<^sub>c (mk_poly A) = dim\<^sub>c A"
  "dim\<^sub>r (mk_poly A) = dim\<^sub>r A"
  unfolding mk_poly_def by auto

private lemma mk_poly_sub_others[simp]:
  assumes "l \<noteq> j'" and "i < dim\<^sub>r A" and "j' < dim\<^sub>c A"
  shows "mk_poly_sub A l j $$ (i,j') = A $$ (i,j')"
  using assms by (induct j; simp)

private lemma mk_poly_others[simp]:
  assumes i: "i < dim\<^sub>r A" and j: "j < dim\<^sub>c A - 1"
  shows "mk_poly A $$ (i,j) = [: A $$ (i,j) :]"
  unfolding mk_poly_def
  apply(subst mk_poly_sub_others)
  using i j by auto

private lemma mk_poly_delete[simp]:
  assumes i: "i < dim\<^sub>r A"
  shows "mat_delete (mk_poly A) i (dim\<^sub>c A - 1) = map\<^sub>m coeff_lift (mat_delete A i (dim\<^sub>c A - 1))"
  apply(rule mat_eqI) unfolding mat_delete_def by auto

private lemma col_mk_poly_sub[simp]:
  assumes "l \<noteq> j'" and "j' < dim\<^sub>c A"
  shows "col (mk_poly_sub A l j) j' = col A j'"
  by(rule vec_eqI; insert assms; simp)

private lemma det_mk_poly_sub:
  assumes A: "(A :: 'a :: comm_ring_1 poly mat) \<in> carrier\<^sub>m n n" and i: "i < n"
  shows "det (mk_poly_sub A (n-1) i) = det A"
  using i
proof (induct i)
  case (Suc i)
    show ?case unfolding mk_poly_sub.simps
    apply(subst det_addcol[of _ n])
      using Suc apply simp
      using Suc apply simp
      apply (rule mk_poly_sub_carrier[OF A])
      using Suc by auto
qed simp

private lemma det_mk_poly:
  fixes A :: "'a :: comm_ring_1 mat"
  shows "det (mk_poly A) = [: det A :]"
proof (cases "dim\<^sub>r A = dim\<^sub>c A")
  interpret ring_hom_coeff_lift.
  case True
    def n == "dim\<^sub>c A"
    have "map\<^sub>m coeff_lift A \<in> carrier\<^sub>m (dim\<^sub>r A) (dim\<^sub>c A)" by simp
    hence sq: "map\<^sub>m coeff_lift A \<in> carrier\<^sub>m (dim\<^sub>c A) (dim\<^sub>c A)" unfolding True.
    show ?thesis
    proof(cases "dim\<^sub>c A = 0")
      case True thus ?thesis unfolding det_def by simp
      next case False thus ?thesis
      unfolding mk_poly_def
      by (subst det_mk_poly_sub[OF sq];simp)
    qed
  next case False
    hence f2: "dim\<^sub>r A = dim\<^sub>c A \<longleftrightarrow> False" by simp
    hence f3: "dim\<^sub>r (mk_poly A) = dim\<^sub>c (mk_poly A) \<longleftrightarrow> False"
      unfolding mk_poly_dim by auto
    show ?thesis unfolding det_def unfolding f2 f3 if_False by simp
qed

private fun mk_poly2_row where
  "mk_poly2_row A d j pv 0 = pv"
| "mk_poly2_row A d j pv (Suc n) =
   mk_poly2_row A d j pv n |\<^sub>v n \<mapsto> pv $ n + monom (A$$(n,j)) d"

private fun mk_poly2_col where
  "mk_poly2_col A pv 0 = pv"
| "mk_poly2_col A pv (Suc m) =
   mk_poly2_row A m (dim\<^sub>c A - Suc m) (mk_poly2_col A pv m) (dim\<^sub>r A)"

private definition "mk_poly2 A \<equiv> mk_poly2_col A (\<zero>\<^sub>v (dim\<^sub>r A)) (dim\<^sub>c A)"

private lemma mk_poly2_row_dim[simp]: "dim\<^sub>v (mk_poly2_row A d j pv i) = dim\<^sub>v pv"
  by(induct i arbitrary: pv, auto)

private lemma mk_poly2_col_dim[simp]: "dim\<^sub>v (mk_poly2_col A pv j) = dim\<^sub>v pv"
  by (induct j arbitrary: pv, auto)

private lemma mk_poly2_dim[simp]: "dim\<^sub>v (mk_poly2 A) = dim\<^sub>r A"
  unfolding mk_poly2_def by simp

private lemma mk_poly2_row:
  assumes n: "n \<le> dim\<^sub>v pv"
  shows "mk_poly2_row A d j pv n $ i =
    (if i < n then pv $ i + monom (A $$ (i,j)) d else pv $ i)"
  using n
proof (induct n arbitrary: pv)
  case (Suc n) thus ?case
    unfolding mk_poly2_row.simps by (cases rule: linorder_cases[of "i" "n"],auto)
qed simp

private lemma mk_poly2_row_col:
  assumes dim[simp]: "dim\<^sub>v pv = n" "dim\<^sub>r A = n" and j: "j < dim\<^sub>c A"
  shows "mk_poly2_row A d j pv n = pv \<oplus>\<^sub>v map\<^sub>v (\<lambda>a. monom a d) (col A j)"
  apply rule using mk_poly2_row[of _ pv] j by auto

private lemma mk_poly2_col:
  fixes pv :: "'a :: comm_semiring_1 poly vec" and A :: "'a mat"
  assumes i: "i < dim\<^sub>r A" and dim: "dim\<^sub>r A = dim\<^sub>v pv"
  shows "mk_poly2_col A pv j $ i = pv $ i + (\<Sum>j'<j. monom (A $$ (i, dim\<^sub>c A - Suc j')) j')"
  using dim
proof (induct j arbitrary: pv)
  case (Suc j) show ?case
    unfolding mk_poly2_col.simps
    apply (subst mk_poly2_row)
      using Suc apply simp
    unfolding Suc(1)[OF Suc(2)]
    using i by (simp add: add.assoc)
qed simp

private lemma mk_poly2_pre:
  fixes A :: "'a :: comm_semiring_1 mat"
  assumes i: "i < dim\<^sub>r A"
  shows "mk_poly2 A $ i = (\<Sum>j'<dim\<^sub>c A. monom (A $$ (i, dim\<^sub>c A - Suc j')) j')"
  unfolding mk_poly2_def
  apply(subst mk_poly2_col) using i by auto

private lemma mk_poly2:
  fixes A :: "'a :: comm_semiring_1 mat"
  assumes i: "i < dim\<^sub>r A"
      and c: "dim\<^sub>c A > 0"
  shows "mk_poly2 A $ i = (\<Sum>j'<dim\<^sub>c A. monom (A $$ (i,j')) (dim\<^sub>c A - Suc  j'))"
    (is "?l = setsum ?f ?S")
proof -
  def l \<equiv> "dim\<^sub>c A - 1"
  have dim: "dim\<^sub>c A = Suc l" unfolding l_def using i c by auto
  let ?g = "\<lambda>j. l - j"
  have "?l = setsum (?f \<circ> ?g) ?S" unfolding l_def mk_poly2_pre[OF i] by auto
  also have "... = setsum ?f ?S"
    unfolding dim
    unfolding lessThan_Suc_atMost
    using setsum.reindex[OF inj_on_diff_nat2,symmetric,unfolded image_diff_atMost].
  finally show ?thesis.
qed

private lemma mk_poly2_sylvester_upper:
  fixes p q :: "'a :: comm_semiring_1 poly"
  assumes i: "i < degree q"
  shows "mk_poly2 (sylvester_mat p q) $ i = monom 1 (degree q - Suc i) * p"
  apply (subst mk_poly2)
    using i apply simp using i apply simp
  apply (subst sylvester_mat_sum_upper[OF i,symmetric])
  apply (rule setsum.cong)
    unfolding sylvester_mat_dim lessThan_Suc_atMost apply simp
  by auto

private lemma mk_poly2_sylvester_lower:
  fixes p q :: "'a :: comm_semiring_1 poly"
  assumes mi: "i \<ge> degree q" and imn: "i < degree p + degree q"
  shows "mk_poly2 (sylvester_mat p q) $ i = monom 1 (degree p + degree q - Suc i) * q"
  apply (subst mk_poly2)
    using imn apply simp using mi imn apply simp
  unfolding sylvester_mat_dim
  using sylvester_mat_sum_lower[OF mi imn]
  apply (subst sylvester_mat_sum_lower) using mi imn by auto

private lemma foo:
  fixes v :: "'a :: comm_semiring_1 vec"
  shows "monom 1 d \<odot>\<^sub>v map\<^sub>v coeff_lift v = map\<^sub>v (\<lambda>a. monom a d) v"
  apply (rule vec_eqI)
  unfolding vec_index_map col_index
  by (auto simp add: Polynomial.smult_monom)

private lemma mk_poly_sub_corresp:
  assumes dimA[simp]: "dim\<^sub>c A = Suc l" and dimpv[simp]: "dim\<^sub>v pv = dim\<^sub>r A"
      and j: "j < dim\<^sub>c A"
  shows "pv \<oplus>\<^sub>v col (mk_poly_sub (mat_map coeff_lift A) l j) l =
    mk_poly2_col A pv (Suc j)"
proof(insert j, induct j)
  have le: "dim\<^sub>r A \<le> dim\<^sub>v pv" using dimpv by simp
  have l: "l < dim\<^sub>c A" using dimA by simp
  { case 0 show ?case
      apply (rule vec_eqI)
      using mk_poly2_row[OF le]
      by (auto simp add: monom_0)
  }
  { case (Suc j)
      hence j: "j < dim\<^sub>c A" by simp
      show ?case
        unfolding mk_poly_sub.simps
        apply(subst col_addcol)
          apply simp
          apply simp
        apply(subst(2) vec_add_comm)
          apply(rule vec_elemsI, simp)
          apply(rule vec_elemsI, simp)
        apply(subst vec_add_assoc[symmetric])
          apply(rule vec_elemsI, rule refl)
          apply(rule vec_elemsI, simp)
          apply(rule vec_elemsI, simp)
        unfolding Suc(1)[OF j]
        apply(subst(2) mk_poly2_col.simps)
        apply(subst mk_poly2_row_col)
          apply simp
          apply simp
          using Suc apply simp
        apply(subst col_mk_poly_sub)
          using Suc apply simp
          using Suc apply simp
        apply(subst col_mat_map)
          using dimA apply simp
        unfolding foo dimA by simp
  }
qed

private lemma col_mk_poly_mk_poly2:
  fixes A :: "'a :: comm_semiring_1 mat"
  assumes dim: "dim\<^sub>c A > 0"
  shows "col (mk_poly A) (dim\<^sub>c A - 1) = mk_poly2 A"
proof -
  def l \<equiv> "dim\<^sub>c A - 1"
  have dim: "dim\<^sub>c A = Suc l" unfolding l_def using dim by auto
  show ?thesis
    unfolding mk_poly_def mk_poly2_def dim
    apply(subst mk_poly_sub_corresp[symmetric])
      apply(rule dim)
      apply simp
      using dim apply simp
    apply(subst vec_left_zero)
      apply(rule vec_elemsI) using dim apply simp
    apply simp
    done
qed

private lemma mk_poly_mk_poly2:
  fixes A :: "'a :: comm_semiring_1 mat"
  assumes dim: "dim\<^sub>c A > 0" and i: "i < dim\<^sub>r A"
  shows "mk_poly A $$ (i,dim\<^sub>c A - 1) = mk_poly2 A $ i"
proof -
  have "mk_poly A $$ (i,dim\<^sub>c A - 1) = col (mk_poly A) (dim\<^sub>c A - 1) $ i"
    apply (subst col_index(1)) using dim i by auto
  also note col_mk_poly_mk_poly2[OF dim] 
  finally show ?thesis.
qed

lemma mk_poly_sylvester_upper:
  fixes p q :: "'a :: comm_ring_1 poly"
  defines "m \<equiv> degree p" and "n \<equiv> degree q"
  assumes i: "i < n"
  shows "mk_poly (sylvester_mat p q) $$ (i, m + n - 1) = monom 1 (n - Suc i) * p" (is "?l = ?r")
proof -
  let ?S = "sylvester_mat p q"
  have c: "m+n = dim\<^sub>c ?S" and r: "m+n = dim\<^sub>r ?S" unfolding m_def n_def by auto
  hence "dim\<^sub>c ?S > 0" "i < dim\<^sub>r ?S" using i by auto
  from mk_poly_mk_poly2[OF this]
  have "?l = mk_poly2 (sylvester_mat p q) $ i" unfolding m_def n_def by auto
  also have "... = ?r"
    apply(subst mk_poly2_sylvester_upper)
      using i unfolding n_def m_def by auto
  finally show ?thesis.
qed

lemma mk_poly_sylvester_lower:
  fixes p q :: "'a :: comm_ring_1 poly"
  defines "m \<equiv> degree p" and "n \<equiv> degree q"
  assumes ni: "n \<le> i" and imn: "i < m+n"
  shows "mk_poly (sylvester_mat p q) $$ (i, m + n - 1) = monom 1 (m + n - Suc i) * q" (is "?l = ?r")
proof -
  let ?S = "sylvester_mat p q"
  have c: "m+n = dim\<^sub>c ?S" and r: "m+n = dim\<^sub>r ?S" unfolding m_def n_def by auto
  hence "dim\<^sub>c ?S > 0" "i < dim\<^sub>r ?S" using imn by auto
  from mk_poly_mk_poly2[OF this]
  have "?l = mk_poly2 (sylvester_mat p q) $ i" unfolding m_def n_def by auto
  also have "... = ?r"
    apply(subst mk_poly2_sylvester_lower)
      using ni imn unfolding n_def m_def by auto
  finally show ?thesis.
qed

text {* The next lemma corresponds to Lemma 7.2.1. *}
lemma resultant_as_poly:
  fixes p q :: "'a :: comm_ring_1 poly"
  assumes degp: "degree p > 0" and degq: "degree q > 0"
  shows "\<exists>p' q'. degree p' < degree q \<and> degree q' < degree p \<and>
         [: resultant p q :] = p' * p + q' * q"
proof (intro exI conjI)
  interpret ring_hom_coeff_lift.
  def m \<equiv> "degree p"
  def n \<equiv> "degree q"
  def d \<equiv> "dim\<^sub>r (mk_poly (sylvester_mat p q))"
  def c \<equiv> "\<lambda>i. coeff_lift (cofactor (sylvester_mat p q) i (m+n-1))"
  def p' \<equiv> "\<Sum>i<n. monom 1 (n - Suc i) * c i"
  def q' \<equiv> "\<Sum>i<m. monom 1 (m - Suc i) * c (n+i)"

  have degc: "\<And>i. degree (c i) = 0" unfolding c_def by auto

  have dmn: "d = m+n" and mnd: "m + n = d" unfolding d_def m_def n_def by auto
  have "[: resultant p q :] =
    (\<Sum>i<d. mk_poly (sylvester_mat p q) $$ (i,m+n-1) *
        cofactor (mk_poly (sylvester_mat p q)) i (m+n-1))"
    unfolding resultant_def
    unfolding det_mk_poly[symmetric]
    unfolding m_def n_def d_def
    apply(rule laplace_expansion_column[of _ _ "degree p + degree q - 1"])
    apply(rule mat_carrierI) using degp by auto
  also { fix i assume i: "i<d"
    have d2: "d = dim\<^sub>r (sylvester_mat p q)" unfolding d_def by auto
    have "cofactor (mk_poly (sylvester_mat p q)) i (m+n-1) =
      (- 1) ^ (i + (m+n-1)) * det (mat_delete (mk_poly (sylvester_mat p q)) i (m+n-1))"
      using cofactor_def.
    also have "... =
      (- 1) ^ (i+m+n-1) * coeff_lift (det (mat_delete (sylvester_mat p q) i (m+n-1)))"
      using mk_poly_delete[OF i[unfolded d2]] degp degq
      unfolding m_def n_def by (auto simp add: add.assoc)
    also have "i+m+n-1 = i+(m+n-1)" using i[folded mnd] by auto
    finally have "cofactor (mk_poly (sylvester_mat p q)) i (m+n-1) = c i"
      unfolding c_def cofactor_def by auto
  }
  hence "... = (\<Sum>i<d. mk_poly (sylvester_mat p q) $$ (i, m+n-1) * c i)"
    (is "_ = setsum ?f _") by auto
  also have "... = setsum ?f ({..<n} \<union> {n ..<d})" unfolding dmn apply(subst ivl_disj_un(8)) by auto
  also have "... = setsum ?f {..<n} + setsum ?f {n..<d}" apply(subst setsum.union_disjoint) by auto
  also { fix i assume i: "i < n"
    have "?f i = monom 1 (n - Suc i) * c i * p"
      unfolding m_def n_def
      apply(subst mk_poly_sylvester_upper)
      using i unfolding n_def by auto
  }
  hence "setsum ?f {..<n} = p' * p" unfolding p'_def setsum_left_distrib by auto 
  also { fix i assume i: "i \<in> {n..<d}"
    have "?f i = monom 1 (m + n - Suc i) * c i * q"
      unfolding m_def n_def
      apply(subst mk_poly_sylvester_lower)
      using i unfolding dmn n_def m_def by auto
  }
  hence "setsum ?f {n..<d} = (\<Sum>i=n..<d. monom 1 (m + n - Suc i) * c i) * q"
    (is "_ = setsum ?h _ * _") unfolding setsum_left_distrib by auto
  also have "{n..<d} = (\<lambda>i. i+n) ` {0..<m}"
    unfolding dmn
    by (metis add_0_left image_add_atLeastLessThan)
  also have "setsum ?h ... = setsum (?h \<circ> (\<lambda>i. i+n)) {0..<m}"
    apply(subst setsum.reindex[symmetric])
    apply (rule inj_onI) by auto
  also have "... = q'" unfolding q'_def apply(rule setsum.cong) by (auto simp add: add.commute)
  finally show main: "[:resultant p q:] = p' * p + q' * q".
  show "degree p' < n"
    unfolding p'_def
    apply(rule degree_setsum_smaller)
    using degq[folded n_def] apply force+
  proof -
    fix i assume i: "i \<in> {..<n}"
    show "degree (monom 1 (n - Suc i) * c i) < n"
      apply (rule order.strict_trans1)
      apply (rule degree_mult_le)
      unfolding add.right_neutral degc
      apply (rule order.strict_trans1)
      apply (rule degree_monom_le) using i by auto
  qed
  show "degree q' < m"
    unfolding q'_def
    apply (rule degree_setsum_smaller)
    using degp[folded m_def] apply force+
  proof -
    fix i assume i: "i \<in> {..<m}"
    show "degree (monom 1 (m-Suc i) * c (n+i)) < m"
    apply (rule order.strict_trans1)
    apply (rule degree_mult_le)
    unfolding add.right_neutral degc
    apply (rule order.strict_trans1)
    apply (rule degree_monom_le) using i by auto
  qed
qed

end

subsubsection \<open>Resultant as Nonzero Polynomial Expression\<close>

lemma resultant_zero:
  fixes p q :: "'a :: idom poly"
  assumes deg: "degree p > 0 \<or> degree q > 0"
      and xp: "poly p x = 0" and xq: "poly q x = 0"
  shows "resultant p q = 0"
proof -
  { assume degp: "degree p > 0" and degq: "degree q > 0"
    obtain p' q' where "[: resultant p q :] = p' * p + q' * q"
      using resultant_as_poly[OF degp degq] by force
    hence "resultant p q = poly (p' * p + q' * q) x"
      using mpoly_base_conv(2)[of "resultant p q"] by auto
    also have "... = poly p x * poly p' x + poly q x * poly q' x"
      unfolding poly2_def by simp
    finally have ?thesis using xp xq by simp
  } moreover
  { assume degp: "degree p = 0"
    have p: "p = [:0:]" using xp degree_0_id[OF degp,symmetric] by (metis mpoly_base_conv(2))
    have ?thesis unfolding p using degp deg by simp
  } moreover
  { assume degq: "degree q = 0"
    have q: "q = [:0:]" using xq degree_0_id[OF degq,symmetric] by (metis mpoly_base_conv(2))
    have ?thesis unfolding q using degq deg by simp
  }
  ultimately show ?thesis by auto
qed

lemma poly_resultant_zero:
  fixes p q :: "'a :: idom poly poly"
  assumes degp: "degree p > 0" and degq: "degree q > 0"
      and y: "poly2 p x y = 0 \<and> poly2 q x y = 0"
  shows "poly (resultant p q) x = 0"
proof -
  obtain y where p0: "poly2 p x y = 0" and q0: "poly2 q x y = 0" using y by auto
  obtain p' q' where "[: resultant p q :] = p' * p + q' * q"
    using resultant_as_poly[OF degp degq] by force
  hence "resultant p q = poly (p' * p + q' * q) [:y:]"
    using mpoly_base_conv(2)[of "resultant p q"] by auto
  also have "poly ... x = poly2 p x y * poly2 p' x y + poly2 q x y * poly2 q' x y"
    unfolding poly2_def by simp
  finally show ?thesis unfolding p0 q0 by simp
qed

lemma resultant_as_nonzero_poly_weak:
  fixes p q :: "'a :: idom poly"
  assumes degp: "degree p > 0" and degq: "degree q > 0"
      and r0: "resultant p q \<noteq> 0"
  shows "\<exists>p' q'. degree p' < degree q \<and> degree q' < degree p \<and>
         [: resultant p q :] = p' * p + q' * q \<and> p' \<noteq> 0 \<and> q' \<noteq> 0"
proof -
  obtain p' q'
    where deg: "degree p' < degree q" "degree q' < degree p"
      and main: "[: resultant p q :] = p' * p + q' * q"
      using resultant_as_poly[OF degp degq] by auto
  have p0: "p \<noteq> 0" using degp by auto
  have q0: "q \<noteq> 0" using degq by auto
  show ?thesis
  proof (intro exI conjI notI)
    assume "p' = 0"
    hence "[: resultant p q :] = q' * q" using main by auto
    also hence d0: "0 = degree (q' * q)" by (metis degree_pCons_0)
      { assume "q' \<noteq> 0"
        hence "degree (q' * q) = degree q' + degree q"
          apply(rule degree_mult_eq) using q0 by auto
        hence False using d0 degq by auto
      } hence "q' = 0" by auto
    finally show False using r0 by auto
  next
    assume "q' = 0"
    hence "[: resultant p q :] = p' * p" using main by auto
    also
      hence d0: "0 = degree (p' * p)" by (metis degree_pCons_0)
      { assume "p' \<noteq> 0"
        hence "degree (p' * p) = degree p' + degree p"
          apply(rule degree_mult_eq) using p0 by auto
        hence False using d0 degp by auto
      } hence "p' = 0" by auto
    finally show False using r0 by auto
  qed fact+
qed

text \<open> Next lemma corresponds to Lemma 7.2.2 of the textbook \<close>

lemma resultant_as_nonzero_poly:
  fixes p q :: "'a :: idom poly"
  defines "m \<equiv> degree p" and "n \<equiv> degree q"
  assumes degp: "m > 0" and degq: "n > 0"
  shows "\<exists>p' q'. degree p' < n \<and> degree q' < m \<and>
         [: resultant p q :] = p' * p + q' * q \<and> p' \<noteq> 0 \<and> q' \<noteq> 0"
proof (cases "resultant p q = 0")
  case False
    thus ?thesis
      using resultant_as_nonzero_poly_weak degp degq
      unfolding m_def n_def by auto
  next case True
    def S \<equiv> "transpose\<^sub>m (sylvester_mat p q)"
    have S: "S \<in> carrier\<^sub>m (m+n) (m+n)" unfolding S_def m_def n_def by auto
    have "det S = 0" using True
      unfolding resultant_def S_def apply (subst det_transpose) by auto
    then obtain v
      where v: "v \<in> carrier\<^sub>v (m+n)" and v0: "v \<noteq> \<zero>\<^sub>v (m+n)" and "S \<otimes>\<^sub>m\<^sub>v v = \<zero>\<^sub>v (m+n)"
      using det_0_iff_vec_prod_zero[OF S] by auto
    hence "poly_of_vec (S \<otimes>\<^sub>m\<^sub>v v) = 0" by auto
    hence main: "poly_of_vec (vec_first v n) * p + poly_of_vec (vec_last v m) * q = 0"
      (is "?p * _ + ?q * _ = _")
      using sylvester_vec_poly[OF v[unfolded m_def n_def], folded m_def n_def S_def]
      by auto
    have split: "vec_first v n @\<^sub>v vec_last v m = v"
      using vec_first_last_append[unfolded add.commute] v by auto
    show ?thesis
    proof(intro exI conjI)
      show "[: resultant p q :] = ?p * p + ?q * q" unfolding True using main by auto
      show "?p \<noteq> 0"
      proof
        assume p'0: "?p = 0"
        hence "?q * q = 0" using main by auto
        hence "?q = 0" using degq n_def by auto
        hence "vec_last v m = \<zero>\<^sub>v m" unfolding poly_of_vec_0_iff by auto
        also have "vec_first v n @\<^sub>v ... = \<zero>\<^sub>v (m+n)" using p'0 unfolding poly_of_vec_0_iff by auto
        finally have "v = \<zero>\<^sub>v (m+n)" using split by auto
        thus False using v0 by auto
      qed
      show "?q \<noteq> 0"
      proof
        assume q'0: "?q = 0"
        hence "?p * p = 0" using main by auto
        hence "?p = 0" using degp m_def by auto
        hence "vec_first v n = \<zero>\<^sub>v n" unfolding poly_of_vec_0_iff by auto
        also have "... @\<^sub>v vec_last v m = \<zero>\<^sub>v (m+n)" using q'0 unfolding poly_of_vec_0_iff by auto
        finally have "v = \<zero>\<^sub>v (m+n)" using split by auto
        thus False using v0 by auto
      qed
      show "degree ?p < n" using degree_poly_of_vec_less[of "vec_first v n"] using degq by auto
      show "degree ?q < m" using degree_poly_of_vec_less[of "vec_last v m"] using degp by auto
    qed
qed

text\<open>Corresponds to Lemma 7.2.3 of the textbook\<close>

lemma resultant_zero_imp_common_factor:
  fixes p q :: "'a :: ufd poly"
  assumes deg: "degree p > 0 \<or> degree q > 0" and r0: "resultant p q = 0"
  shows "\<not> coprime\<^sub>I p q"
  unfolding neq0_conv[symmetric]
proof -
  { assume degp: "degree p > 0" and degq: "degree q > 0"
    have p0: "p \<noteq> 0" using degp by auto
    have q0: "q \<noteq> 0" using degq by auto
    assume cop: "coprime\<^sub>I p q"
    obtain p' q' where "p' * p + q' * q = 0"
      and p': "degree p' < degree q" and q': "degree q' < degree p"
      and p'0: "p' \<noteq> 0" and q'0: "q' \<noteq> 0"
      using resultant_as_nonzero_poly[OF degp degq] r0 by auto
    hence "p' * p = - q' * q" by (simp add: eq_neg_iff_add_eq_0)
    from coprime_mult_cross_dvd[OF cop this p0 q0]
    have "p dvd q'" by auto
    from dvd_imp_degree_le[OF this q'0]
    have "degree p \<le> degree q'" by auto
    hence False using q' by auto
  }
  moreover
  { assume degp: "degree p = 0"
    then obtain x where "p = [:x:]" by (elim degree_eq_zeroE)
    moreover hence "resultant p q = x ^ degree q" using resultant_const by auto
      hence "x = 0" using r0 by auto
    ultimately have "p = 0" by auto
    hence ?thesis unfolding not_coprime_iff_common_factor
      by (metis deg degp dvd_0_right dvd_refl less_numeral_extra(3) poly_dvd_1)
  }
  moreover
  { assume degq: "degree q = 0"
    then obtain x where "q = [:x:]" by (elim degree_eq_zeroE)
    moreover hence "resultant p q = x ^ degree p" using resultant_const by auto
      hence "x = 0" using r0 by auto
    ultimately have "q = 0" by auto
    hence ?thesis unfolding not_coprime_iff_common_factor
      by (metis deg degq dvd_0_right dvd_refl less_numeral_extra(3) poly_dvd_1)
  }
  ultimately show ?thesis by auto
qed

subsubsection \<open>Computation of Resultants\<close>

definition deletion_mat :: "nat \<Rightarrow> nat \<Rightarrow> 'a :: idom poly \<Rightarrow> 'a mat" where
    "deletion_mat n m q = (let dq = degree q in mat (n+m) (n+m) (\<lambda> (i,j). if i = j then 1 else 
      if i \<ge> m then 0 else if j \<ge> m + i then (let sub = j - m - i in if sub \<le> n - m then coeff q (n - m - sub) else 0)
        else 0))"
        
lemma dim_deletion_mat[simp]: "dim\<^sub>r (deletion_mat n m q) = n + m"
  "dim\<^sub>c (deletion_mat n m q) = n + m"
  "deletion_mat n m q \<in> carrier\<^sub>m (n + m) (n + m)"
  unfolding deletion_mat_def Let_def by auto

lemma upper_triangular_deletion_mat: "upper_triangular (deletion_mat n m q)"
  by (standard, auto simp: deletion_mat_def Let_def)
  
lemma det_deletion_mat: "det (deletion_mat n m q) = 1" 
  by (subst det_upper_triangular[OF upper_triangular_deletion_mat dim_deletion_mat(3)], 
  rule listprod_neutral, auto simp: deletion_mat_def Let_def mat_diag_def)
  
lemma deletion_mat_sylvester_mat_sub: assumes m: "m \<ge> degree (g * q + r)" 
  and n: "n \<ge> degree g"
  and nm: "degree q + n \<le> m"
  shows "sylvester_mat_sub m n (g * q + r) g = 
  deletion_mat m n q \<otimes>\<^sub>m sylvester_mat_sub m n r g" (is "?A = ?r")
proof -
  let ?mn = "m + n"
  let ?f = "g * q + r"
  have dim: "dim\<^sub>r ?A = ?mn" "dim\<^sub>c ?A = ?mn" "dim\<^sub>r ?r = ?mn" "dim\<^sub>c ?r = ?mn" by auto
  show ?thesis
  proof (rule mat_eqI; unfold dim)
    fix i j
    let ?D = "deletion_mat m n q"
    let ?B = "sylvester_mat_sub m n r g"
    assume i: "i < ?mn" and j: "j < ?mn"
    hence r: "?r $$ (i,j) = row ?D i \<bullet> col ?B j"
      by simp
    show "?A $$ (i,j) = ?r $$ (i,j)" 
    proof (cases "i < n")
      case False
      have id: "row ?D i = unit\<^sub>v ?mn i"
        by (rule vec_eqI, insert i j False, auto simp: deletion_mat_def Let_def)
      have "?r $$ (i,j) = ?B $$ (i,j)" unfolding r id
        by (subst scalar_prod_left_unit, insert i j, auto simp: col_def)
      also have "\<dots> = ?A $$ (i,j)" using i j False
        by (auto simp: sylvester_mat_sub_def)
      finally show ?thesis ..
    next
      case True note i_n = this
      let ?dq = "degree q"
      def r_ij \<equiv> "(if i \<le> j \<and> j - i \<le> m then coeff r (m + i - j) else 0)"
      def gq_ij \<equiv> "(if i \<le> j \<and> j - i \<le> m then coeff (g * q) (m + i - j) else 0)"
      have A: "?A $$ (i,j) = r_ij + gq_ij"
        by (subst sylvester_mat_sub_index[OF i j], insert True, auto simp: r_ij_def gq_ij_def)
      let ?d = "\<lambda> j. if i = j then 1 else if n + i \<le> j \<and> j - n - i \<le> m - n
        then coeff q (m - (j - i)) else 0"
      let ?b = "\<lambda> i. if i < n then if i \<le> j \<and> j - i \<le> m  then coeff r (m + i - j) else 0
                   else if i - n \<le> j \<and> j \<le> i then coeff g (i - j) else 0"
      have row: "row ?D i = vec ?mn ?d" unfolding deletion_mat_def Let_def using i True
        by (intro vec_eqI, auto)
      have col: "col ?B j = vec ?mn ?b"
        by (rule vec_eqI, unfold sylvester_mat_sub_def, insert i j True, auto)
      let ?prod = "\<lambda> i. ?d i * ?b i"
      def prod \<equiv> ?prod
      let ?sum = "setsum prod {0..<?mn}"
      have "?r $$ (i,j) = ?sum" unfolding r row col scalar_prod_def prod_def by auto
      also have "{0 ..< ?mn} = {0 ..< i} \<union> {i} \<union> {Suc i ..< ?mn}" using i by auto
      also have "setsum prod \<dots> = setsum prod {0 ..< i} + prod i + setsum prod {Suc i ..< ?mn}"      
        by (subst setsum.union_disjoint, (auto)[3], subst setsum.union_disjoint, auto)
      also have "prod i = ?b i" unfolding prod_def by simp
      also have "\<dots> = r_ij" using True by (simp add: r_ij_def)
      also have "setsum prod {0 ..< i} = 0" unfolding prod_def
        by (rule setsum.neutral, auto)
      also have "setsum prod {Suc i ..< ?mn} = gq_ij" 
      proof -
        let ?Diff = "{n + i .. m + i} \<inter> {j .. j+n}"
        let ?I = "({Suc i ..< ?mn} \<inter> ?Diff)"
        let ?D = "({Suc i ..< ?mn} - ?Diff)"
        def prod' \<equiv> "\<lambda> k. coeff q (m + i - k) * coeff g (k - j)"
        have "setsum prod {Suc i ..< ?mn} = setsum prod (?I \<union> ?D)"
          by (rule arg_cong[of _ _ "setsum prod"], auto)
        also have "\<dots> = setsum prod ?I + setsum prod ?D"
          by (subst setsum.union_disjoint, auto)
        also have "setsum prod ?D = 0"
          by (rule setsum.neutral, insert nm, auto simp: prod_def)
        also have "setsum prod ?I = setsum prod' ?I" 
          unfolding prod_def prod'_def by (rule setsum.cong, auto simp: ac_simps)
        also have "\<dots> = gq_ij" 
        proof (cases "i \<le> j \<and> j - i \<le> m")
          case False
          hence "gq_ij = 0" unfolding gq_ij_def by auto
          moreover have "setsum prod' ?I = 0" unfolding prod'_def
            by (rule setsum.neutral, insert False n m nm, auto simp: prod'_def intro!: coeff_eq_0)
          ultimately show ?thesis by simp
        next
          case True note ij = this
          have eq: "{0..m + i - j} = (\<lambda>k. k - j) ` {j..m + i}" (is "?l = ?r")
          proof -
            {
              fix k
              assume "k \<in> ?l"
              hence "k + j \<in> {j..m+i}" using True by auto
              hence "(k + j) - j \<in> ?r" by blast
            }          
            thus ?thesis by auto
          qed
          from True have "gq_ij = coeff (g * q) (m + i - j)" unfolding gq_ij_def by auto
          also have "\<dots> = setsum (\<lambda> k. coeff q (m + i - j - k) * coeff g k) {0 .. m + i - j}" 
            unfolding coeff_mult by (rule setsum.cong, auto simp add: ac_simps)
          also have "\<dots> = setsum prod' {j .. m + i}" unfolding prod'_def
            by (rule setsum.reindex_cong[of "\<lambda> k. k - j"], insert eq True, auto simp: inj_on_def)
          also have "\<dots> = setsum prod' (?I \<union> ({j .. m + i} - ?I))" 
            by (rule setsum.cong, auto)
          also have "\<dots> = setsum prod' ?I + setsum prod' ({j .. m + i} - ?I)"
            by (subst setsum.union_disjoint, auto)
          also have "setsum prod' ({j .. m + i} - ?I) = 0"
          proof (rule setsum.neutral, clarify, goal_cases)
            case (1 k)
            hence k1: "k \<ge> j" "k \<le> m + i" by auto
            show ?case
            proof (cases "k > j + degree g \<or> n = 0")
              case True
              thus ?thesis using 1 ij i_n unfolding prod'_def by (auto simp: coeff_eq_0)
            next
              case False
              hence k2: "k \<le> j + degree g" "k < i + n" "k < j + n" "j \<le> m + i" "i \<le> j" "n > 0"
                using 1 True i_n n ij i_n j k1 by auto
              note * = k1 k2 i_n
              def kk \<equiv> "k - j"
              from * i_n nm
              have id: "m + i - k = m + i - j - kk" "k - j = kk"
                and k12: "kk \<le> m + i - j" "kk \<le> degree g" "kk < i - j + n" "kk < n" "j \<le> m + i" "i \<le> j"
                unfolding kk_def by auto
              note ** = n m nm
              have "m + i \<ge> j + kk" using k12 ** by auto
              from k12(3,6) have "n + i - j > kk"
                by (simp add: add.commute diff_less_mono k1 k2 kk_def)
              thus ?thesis unfolding prod'_def id using k12 ** by (auto intro: coeff_eq_0)                
            qed
          qed
          finally show ?thesis by simp
        qed
        finally show ?thesis by simp
      qed
      finally show ?thesis unfolding A r by simp
    qed
  qed auto
qed

hide_const deletion_mat

lemma resultant_sub_mod: assumes m: "m \<ge> degree (g * q + r)" 
  and n: "n \<ge> degree (g :: 'a :: idom poly)"
  and nm: "degree q + n \<le> m"
  shows "resultant_sub m n (g * q + r) g = resultant_sub m n r g"
proof -
  show ?thesis unfolding resultant_def sylvester_mat_def resultant_sub_def
    by (subst deletion_mat_sylvester_mat_sub[OF m n nm],
    subst det_mult[OF dim_deletion_mat(3)], auto simp: det_deletion_mat assms)
qed
  
lemma resultant_mod: assumes f: "f = g * q + (r :: 'a :: idom poly)"
  and deg: "degree f \<ge> degree g" "degree g > degree r"
  and ex: "ex = degree g * (degree f - degree r)"
  shows "resultant f g = (-1)^ex * coeff g (degree g)^(degree f - degree r) * resultant r g" 
proof -
  def diff \<equiv> "degree f - degree r"
  have df: "degree f = degree r + diff" using deg unfolding diff_def by auto
  show ?thesis unfolding resultant_def sylvester_mat_def resultant_sub_def[symmetric] f
  proof (subst resultant_sub_mod[OF le_refl le_refl]; unfold f[symmetric])
    show "resultant_sub (degree f) (degree g) r g =
      (-1)^ex * coeff g (degree g) ^ (degree f - degree r) * resultant_sub (degree r) (degree g) r g"
      unfolding df resultant_sub_trim_upper power_mult_distrib power_mult[symmetric]
      by (auto simp: ex diff_def)
    show "degree q + degree g \<le> degree f" using deg unfolding f
      by (metis (no_types, lifting) add.commute add.right_neutral 
        deg(1) degree_0 degree_add_eq_left degree_mult_eq f 
        leD le_less_trans less_or_eq_imp_le not_le_imp_less)
  qed
qed
  
lemma resultant_computation_pseudo_divmod: assumes 
    res: "pseudo_divmod f g = (q,r)"
  and c: "c = coeff g (degree (g :: 'a :: idom_div poly))"
  and e1: "e1 = pseudo_exponent f g * degree g"
  and e2: "e2 = degree f - degree r"
  and e3: "e3 = degree g * (degree f - degree r)"
  and degg: "degree g > degree r" "degree f \<ge> degree g"
  shows "resultant f g = exact_div ((- 1) ^ e3 * resultant r g) (c ^ (e1 - e2))"
proof -
  from degg have g: "g \<noteq> 0" by auto
  let ?c = "coeff g (degree g)"
  let ?m = "(-1)^e3"
  let ?e = "pseudo_exponent f g"
  let ?e1 = "?e * degree g"
  let ?e2 = "if q = 0 then 0 else degree g + degree q - degree r"
  from g have "?c \<noteq> 0" by auto
  hence ce: "?c ^ ?e \<noteq> 0" and c0: "\<And> m. c ^ m \<noteq> 0" by (auto simp: c)
  from pseudo_divmod[OF g res] have id: "smult (?c ^ ?e) f = g * q + r" and rg: "r = 0 \<or> degree r < degree g" by auto
  have deg_f: "degree f = degree (g * q + r)" 
    using arg_cong[OF id, of degree] unfolding degree_smult_eq using ce by (simp split: if_splits)
  from arg_cong[OF id, of "\<lambda> x. resultant x g", unfolded resultant_smult_left[OF ce]]
  have "c ^ e1 * resultant f g = resultant (g * q + r) g" 
    by (simp add: power_mult e1 c)
  also have "\<dots> = ?m * ?c ^ (degree (g * q + r) - degree r) * resultant r g" 
    by (rule resultant_mod[OF refl degg(2,1)[unfolded deg_f] e3[unfolded deg_f]])
  also have deg: "degree (g * q + r) - degree r = e2" unfolding deg_f[symmetric] e2 by simp
  finally have id: "c ^ e1 * resultant f g = c ^ e2 * ?m * resultant r g" unfolding c by simp

  have deg': "degree (g * q + r) = (if q = 0 then degree r else degree g + degree q)"
  proof (cases "q = 0")
    case False
    with g(1) have add: "degree (g * q) = degree g + degree q" by (simp add: degree_mult_eq)
    also have "\<dots> > degree r \<or> r = 0" using rg by auto
    finally show ?thesis using False
      by (metis add add_0_iff degree_add_eq_left)
  qed auto
  hence e2': "e2 = (if q = 0 then 0 else degree g + degree q - degree r)"
    unfolding e2 deg_f by auto
  from degg have e21: "e2 \<le> e1" using deg' e1 e2 deg_f deg unfolding pseudo_exponent_def by (cases "degree g", auto)
  hence e1: "c ^ e1 = c ^ (e2 + (e1 - e2))" by simp
  from e21 arg_cong[OF id, of "\<lambda> x. exact_div (exact_div x (c ^ e2)) (c ^ (e1 - e2))", 
    unfolded this power_add mult.assoc exact_div_left[OF c0]]
  show ?thesis by simp
qed
  
text \<open>For the implementation function, we require @{class semiring_gcd} for computing GCDs
  in the @{const content},
  which rules out integer polynomials as carrier at the moment. This should be changed in the 
  future. Note that even the current proof does not require optimality of the GCD, any divisor
  would do.\<close>

definition exact_div_poly :: "'a :: idom_div poly \<Rightarrow> 'a \<Rightarrow> 'a poly" where
  "exact_div_poly p a = (map_poly (\<lambda> c. exact_div c a) p)"  
  
lemma smult_exact_div_poly: assumes "\<And> c. c \<in> set (coeffs p) \<Longrightarrow> a dvd c"
  shows "smult a (exact_div_poly p a) = p" 
  unfolding smult_map_poly exact_div_poly_def 
  by (subst map_poly_compose, force+, subst map_poly_eqI, insert assms, auto)

typedef (overloaded) 'a common_divisor = "{f. \<forall> x y :: 'a :: idom_div. f x y dvd x \<and> f x y dvd y}"
  by (rule exI[of _ "\<lambda> _ _. 1"], auto)
  
setup_lifting type_definition_common_divisor

lift_definition common_divisor :: "'a common_divisor \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a :: idom_div" is "\<lambda> x. x" .

lemma common_divisor: "common_divisor f x y dvd x" "common_divisor f x y dvd y"
  by (transfer, auto)+
  
definition common_divisor_list :: "'a common_divisor \<Rightarrow> 'a list \<Rightarrow> 'a :: idom_div" where
  "common_divisor_list f xs = (let cd = common_divisor f in foldr cd xs 0)"

lemma common_divisor_list_simps: "common_divisor_list cd [] = 0" 
  "common_divisor_list cd (x # xs) = common_divisor cd x (common_divisor_list cd xs)"
  by (auto simp: common_divisor_list_def Let_def)
    
lemma common_divisor_list: "x \<in> set xs \<Longrightarrow> common_divisor_list f xs dvd x" 
proof (induct xs)
  case (Cons y ys)
  show ?case
  proof (cases "x = y")
    case False
    with Cons have "common_divisor_list f ys dvd x" by auto
    thus ?thesis unfolding common_divisor_list_simps using dvd_trans common_divisor(2) by metis
  next
    case True
    thus ?thesis unfolding common_divisor_list_simps using common_divisor(1) by metis
  qed
qed simp

lemma common_divisor_list_non0: assumes mem: "x \<in> set xs" and x: "x \<noteq> 0"
  shows "common_divisor_list cd xs \<noteq> 0"
  using common_divisor_list[OF mem, of cd] x by auto
  
lemma common_divisor_list_poly_non0: assumes "p \<noteq> 0"
  shows "common_divisor_list cd (coeffs p) \<noteq> 0"
  by (rule common_divisor_list_non0[OF _ leading_coeff_neq_0[of p]], insert assms) 
   (metis last_coeffs_eq_coeff_degree last_in_set not_0_coeffs_not_Nil)

  
context fixes
  cdf :: "'a :: idom_div common_divisor"
begin
function resultant_impl_main :: "'a poly \<Rightarrow> 'a poly \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a" where
  "resultant_impl_main f g df dg = (
    if dg = 0 then coeff g 0 ^ df 
    else let 
       cd = common_divisor_list cdf (coeffs g);
       pg = exact_div_poly g cd;
       (q,r) = pseudo_divmod f pg;
       dr = degree r;
       c = coeff pg dg;
       e1 = (Suc df - dg) * dg;
       e2 = df - dr;
       rgr = resultant_impl_main pg r dg dr;
       rrg = (if even dg \<or> (even dr = even e2) then rgr else - rgr)
     in  
       cd ^ df * (exact_div rrg (c ^ (e1 - e2))))" 
  by pat_completeness auto

termination 
proof (relation "measures [(\<lambda> (f,g,df,dg). if dg = degree g then 0 else 1), 
  (\<lambda> (f,g,df,dg). degree g)]", goal_cases)
  case (2 f g df dg cg pg qr q r dr)
  let ?cd = "common_divisor_list cdf (coeffs g)"
  let ?pg = "exact_div_poly g  ?cd"
  from 2 have pd: "pseudo_divmod f ?pg = (q,r)" and dg: "dg \<noteq> 0" by auto
  from 2 have dr: "dr = degree r" by auto
  show ?case
  proof (cases "dg = degree g")
    case True
    with dg have g: "g \<noteq> 0" "degree g \<noteq> 0" by auto    
    have cg0: "?cd \<noteq> 0" by (rule common_divisor_list_poly_non0[OF g(1)])
    have "g = smult ?cd ?pg" 
      by (rule sym, rule smult_exact_div_poly, rule common_divisor_list)
    from arg_cong[OF this, of degree]
    have deg: "degree ?pg = degree g" using cg0 degree_smult_eq[of ?cd g]  
      by simp
    with g have pg: "?pg \<noteq> 0" by auto
    from pseudo_divmod[OF pg pd, unfolded deg] g
    show ?thesis by (auto simp: dr)
  qed (auto simp: dr)
qed simp

lemma resultant_impl_main: "df = degree f \<Longrightarrow> dg = degree g \<Longrightarrow> df \<ge> dg 
  \<Longrightarrow> resultant_impl_main f g df dg = resultant f g"
proof (induct f g df dg rule: resultant_impl_main.induct)
  case (1 f g df dg)
  note dfg = 1(2-3)
  let ?df = "degree f"
  let ?dg = "degree g"
  show ?case
  proof (cases "?dg = 0")
    case True note dg = this
    from degree0_coeffs[OF dg] obtain a where g: "g = [:a:]" by auto
    from g dfg have r: "resultant_impl_main f g df dg = a ^ ?df" by auto
    also have "\<dots> = resultant f g" unfolding g by simp
    finally show ?thesis by simp
  next
    case False
    obtain cg where cg: "cg = common_divisor_list cdf (coeffs g)" by blast
    obtain pg where pg: "pg = exact_div_poly g cg" by blast
    obtain q r where div: "pseudo_divmod f pg = (q,r)" by force
    let ?dr = "degree r"
    obtain c where c: "c = coeff pg dg" by blast
    obtain e1 where e1: "e1 = pseudo_exponent f g * dg" by blast
    obtain e2 where e2: "e2 = degree f - degree r" by blast
    obtain rgr where rgr: "rgr = resultant_impl_main pg r dg ?dr" by blast
    obtain rrg where rrg: "rrg = (if even ?dg \<or> even ?dr then rgr else - rgr)" by blast
    obtain vrrg where vrrg: "vrrg = (if even ?dg \<or> even e2 then rrg else -rrg)" by blast
    have cg0: "cg \<noteq> 0" unfolding cg by (rule common_divisor_list_poly_non0, insert False, auto)
    have id: "g = smult cg pg" unfolding pg cg
      by (rule sym, rule smult_exact_div_poly, rule common_divisor_list)
    have deg[simp]: "degree pg = degree g" unfolding id using cg0 by auto
    hence dpg: "dg = degree pg" unfolding dfg ..
    from False have g: "pg \<noteq> 0" using deg cg0 id by fastforce
    from False have dpg0: "degree pg \<noteq> 0" by simp
    with pseudo_divmod[OF g div] have dr: "degree r < degree pg" "degree r \<le> dg" unfolding dpg by auto
    note IH = 1(1)[OF False[folded dfg] cg pg refl div[symmetric] refl c refl refl dpg refl dr(2)]
    have e1': "e1 = pseudo_exponent f pg * dg" by (auto simp: e1 dpg pseudo_exponent_def)
    have r: "resultant_impl_main f g df dg = cg ^ ?df * exact_div vrrg (c ^ (e1 - e2))" 
      unfolding Let_def e1 e2 c rgr rrg div[unfolded pg cg] vrrg split pseudo_exponent_def 
        cg pg resultant_impl_main.simps[of f g] dfg
      using False by auto
    also have "vrrg = (if even dg \<or> even e2 then rrg else -rrg)" unfolding vrrg 
      by (simp add: dfg)
    also have "\<dots> = (-1)^(dg * e2) * rrg" by simp
    also have "\<dots> = (-1)^(dg * e2) * resultant r pg" unfolding rrg rgr IH
      by (subst resultant_swap[of r pg], simp)
    also have "exact_div \<dots> (c ^ (e1 - e2)) = resultant f pg"
      by (subst resultant_computation_pseudo_divmod[OF div, folded dpg, OF c e1' e2  _ dr(1)[folded dpg] 
          1(4)[unfolded dfg(1)]], auto simp: e2)
    also have "cg ^ ?df * \<dots> = resultant f g" unfolding id resultant_smult_right[OF cg0] by simp
    finally show ?thesis .
  qed
qed

definition resultant_impl :: "'a poly \<Rightarrow> 'a poly \<Rightarrow> 'a" where
  "resultant_impl f g = (let df = degree f; dg = degree g
  in if df \<ge> dg then resultant_impl_main f g df dg else let gf = resultant_impl_main g f dg df in
   if even df \<or> even dg then gf else - gf)"

lemma resultant_impl[simp]: "resultant_impl f g = resultant f g"
   using resultant_impl_main[OF refl refl, of f g] resultant_impl_main[OF refl refl, of g f] 
   unfolding Let_def resultant_impl_def using resultant_swap[of f g] by auto
end
  

lift_definition common_divisor_int_poly :: "int poly common_divisor" is gcd_int_poly
  using gcd_int_poly[OF refl] by auto       
  
lift_definition gcd_divisor :: "'a :: {idom_div,semiring_gcd} common_divisor" is gcd
  by auto

definition resultant_int_poly :: "int poly poly \<Rightarrow> int poly poly \<Rightarrow> int poly" where
  [simp]: "resultant_int_poly x y = resultant x y"

lemma resultant_int_poly_code[code]: "resultant_int_poly = resultant_impl common_divisor_int_poly"
  by (intro ext, auto)
  
lemma resultant_code[code]: "resultant x y = resultant_impl gcd_divisor x y"
  by simp

instantiation rat :: ring_gcd
begin
definition gcd_rat :: "rat \<Rightarrow> rat \<Rightarrow> rat" where
  "gcd_rat x y = (if x = 0 \<and> y = 0 then 0 else 1)"
definition lcm_rat :: "rat \<Rightarrow> rat \<Rightarrow> rat" where
  "lcm_rat x y = (if x = 0 \<or> y = 0 then 0 else 1)"
definition unit_factor_rat :: "rat \<Rightarrow> rat" where
  "unit_factor_rat x = x"
definition normalize_rat :: "rat \<Rightarrow> rat" where 
  "normalize_rat x = (if x = 0 then 0 else 1)"
instance 
by (standard, insert const_poly_dvd_1 is_unit_pCons_iff, 
  (force simp: dvd_unit_imp_unit unit_factor_rat_def normalize_rat_def gcd_rat_def lcm_rat_def)+)
end

end
