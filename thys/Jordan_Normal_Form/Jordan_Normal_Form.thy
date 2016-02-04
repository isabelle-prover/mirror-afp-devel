(*  
    Author:      René Thiemann 
                 Akihisa Yamada
    License:     BSD
*)
section \<open>Jordan Normal Form\<close>

text \<open>This theory defines Jordan normal forms (JNFs) in a sparse representation, i.e., 
  as block-diagonal matrices. We also provide a closed formula for powers of JNFs, 
  which allows to estimate the growth rates of JNFs.\<close>

theory Jordan_Normal_Form
imports 
  Matrix
  Char_Poly
  Binomial
  "../Polynomial_Interpolation/Missing_Unsorted"
begin

definition jordan_block :: "nat \<Rightarrow> 'a :: {zero,one} \<Rightarrow> 'a mat" where 
  "jordan_block n a = mat n n (\<lambda> (i,j). if i = j then a else if Suc i = j then 1 else 0)"

lemma jordan_block_index[simp]: "i < n \<Longrightarrow> j < n \<Longrightarrow> 
  jordan_block n a $$ (i,j) = (if i = j then a else if Suc i = j then 1 else 0)"
  "dim\<^sub>r (jordan_block n k) = n"
  "dim\<^sub>c (jordan_block n k) = n"
  unfolding jordan_block_def by auto

lemma jordan_block_carrier[simp]: "jordan_block n k \<in> carrier\<^sub>m n n" 
  unfolding mat_carrier_def by auto

lemma jordan_block_char_poly: "char_poly (jordan_block n a) = [: -a, 1:]^n"
  unfolding char_poly_defs by (subst det_upper_triangular[of _ n], auto simp: listprod_diag_setprod)

lemma jordan_block_pow_carrier[simp]:
  "jordan_block n a ^\<^sub>m r \<in> carrier\<^sub>m n n" by auto
lemma jordan_block_pow_dim[simp]:
  "dim\<^sub>r (jordan_block n a ^\<^sub>m r) = n" "dim\<^sub>c (jordan_block n a ^\<^sub>m r) = n" by auto

lemma jordan_block_pow: "(jordan_block n (a :: 'a :: comm_ring_1)) ^\<^sub>m r = 
  mat n n (\<lambda> (i,j). if i \<le> j then of_nat (r choose (j - i)) * a ^ (r + i - j) else 0)"
proof (induct r)
  case 0
  {
    fix i j :: nat
    assume "i \<noteq> j" "i \<le> j"
    hence "j - i > 0" by auto
    hence "0 choose (j - i) = 0" by simp
  } note [simp] = this
  show ?case
    by (simp, rule mat_eqI, auto)
next
  case (Suc r)
  let ?jb = "jordan_block n a"
  let ?rij = "\<lambda> r i j. of_nat (r choose (j - i)) * a ^ (r + i - j)"
  let ?v = "\<lambda> i j. if i \<le> j then of_nat (r choose (j - i)) * a ^ (r + i - j) else 0"
  have "?jb ^\<^sub>m Suc r = mat n n (\<lambda> (i,j). if i \<le> j then ?rij r i j else 0) \<otimes>\<^sub>m ?jb" by (simp add: Suc)
  also have "\<dots> = mat n n (\<lambda> (i,j). if i \<le> j then ?rij (Suc r) i j else 0)"
  proof -
    {
      fix j
      assume j: "j < n"
      hence col: "col (jordan_block n a) j = vec n (\<lambda>i. if i = j then a else if Suc i = j then 1 else 0)"
        unfolding jordan_block_def col_mat[OF j] by simp
      fix f
      have "vec n f \<bullet> col (jordan_block n a) j = (f j * a + (if j = 0 then 0 else f (j - 1)))"
      proof -
        def p \<equiv> "\<lambda> i. vec n f $ i * col (jordan_block n a) j $ i"
        have "vec n f \<bullet> col (jordan_block n a) j = (\<Sum>i = 0 ..< n. p i)"
          unfolding scalar_prod_def p_def by simp
        also have "\<dots> = p j + setsum p ({0 ..< n} - {j})" using j
          by (subst setsum.remove[of _ j], auto)
        also have "p j = f j * a" unfolding p_def col using j by auto
        also have "setsum p ({0 ..< n} - {j}) = (if j = 0 then 0 else f (j - 1))"
        proof (cases j)
          case 0
          have "setsum p ({0 ..< n} - {j}) = 0"
            by (rule setsum.neutral, auto simp: p_def col 0)
          thus ?thesis using 0 by simp
        next
          case (Suc jj)
          with j have jj: "jj \<in> {0 ..< n} - {j}" by auto
          have "setsum p ({0 ..< n} - {j}) = p jj + setsum p ({0 ..< n} - {j} - {jj})"
            by (subst setsum.remove[OF _ jj], auto)
          also have "p jj = f (j - 1)" unfolding p_def col using jj
            by (auto simp: Suc)
          also have "setsum p ({0 ..< n} - {j} - {jj}) = 0"
            by (rule setsum.neutral, auto simp: p_def col, auto simp: Suc)
          finally show ?thesis unfolding Suc by simp
        qed
        finally show ?thesis .
      qed
    } note scalar_to_sum = this
    {
      fix i j
      assume i: "i < n" and ij: "i > j"
      hence j: "j < n" by auto
      have "vec n (?v i) \<bullet> col (jordan_block n a) j = 0"
        unfolding scalar_to_sum[OF j] using ij i j by auto
    } note easy_case = this
    {
      fix i j
      assume j: "j < n" and ij: "i \<le> j"
      hence i: "i < n" and id: "\<And> p q. (if i \<le> j then p else q) = p" by auto
      have "vec n (?v i) \<bullet> col (jordan_block n a) j =
        (of_nat (r choose (j - i)) * (a ^ (Suc (r + i - j)))) +
          (if j = 0 then 0
         else if i \<le> j - 1 then of_nat (r choose (j - 1 - i)) * a ^ (r + i - (j - 1)) else 0)"
      unfolding scalar_to_sum[OF j]
      using ij by simp
      also have "\<dots> = of_nat (Suc r choose (j - i)) * a ^ (Suc (r + i) - j)"
      proof (cases j)
        case (Suc jj)
        {
          assume "i \<le> Suc jj" and "\<not> i \<le> jj"
          hence "i = Suc jj" by auto 
          hence "a * a ^ (r + i - Suc jj) = a ^ (r + i - jj)" by simp
        } 
        moreover
        {
          assume ijj: "i \<le> jj"
          have "of_nat (r choose (Suc jj - i)) * (a * a ^ (r + i - Suc jj)) 
          + of_nat (r choose (jj - i)) * a ^ (r + i - jj) =
            of_nat (Suc r choose (Suc jj - i)) * a ^ (r + i - jj)"
          proof (cases "r + i < jj")
            case True
            hence gt: "jj - i > r" "Suc jj - i > r" "Suc jj - i > Suc r" by auto
            show ?thesis 
              unfolding binomial_eq_0[OF gt(1)] binomial_eq_0[OF gt(2)] binomial_eq_0[OF gt(3)]
              by simp
          next
            case False 
            hence ge: "r + i \<ge> jj" by simp
            show ?thesis
            proof (cases "jj = r + i")
              case True
              have gt: "r < Suc r" by simp
              show ?thesis unfolding True by (simp add: binomial_eq_0[OF gt])
            next
              case False
              with ge have lt: "jj < r + i" by auto
              hence "r + i - jj = Suc (r + i - Suc jj)" by simp 
              hence prod: "a * a ^ (r + i - Suc jj) = a ^ (r + i - jj)" by simp
              from ijj have id: "Suc jj - i = Suc (jj - i)" by simp
              have binom: "Suc r choose (Suc jj - i) = 
                r choose (Suc jj - i) + (r choose (jj - i))"
                unfolding id
                by (subst binomial_Suc_Suc, simp)
              show ?thesis unfolding prod binom  
                by (simp add: field_simps)
            qed
          qed
        }
        ultimately show ?thesis using ij unfolding Suc by auto
      qed auto
      finally have "vec n (?v i) \<bullet> col (jordan_block n a) j 
        = of_nat (Suc r choose (j - i)) * a ^ (Suc (r + i) - j)" .
    } note main_case = this
    show ?thesis
      by (rule mat_eqI, insert easy_case main_case, auto)
  qed
  finally show ?case by simp
qed

definition jordan_matrix :: "(nat \<times> 'a :: {zero,one})list \<Rightarrow> 'a mat" where
  "jordan_matrix n_as = diag_block_mat (map (\<lambda> (n,a). jordan_block n a) n_as)"

lemma jordan_matrix_dim[simp]: 
  "dim\<^sub>r (jordan_matrix n_as) = listsum (map fst n_as)"
  "dim\<^sub>c (jordan_matrix n_as) = listsum (map fst n_as)"
  unfolding jordan_matrix_def
  by (subst diag_block_mat_dim, auto, (induct n_as, auto simp: Let_def)+)

lemma jordan_matrix_carrier[simp]: 
  "jordan_matrix n_as \<in> carrier\<^sub>m (listsum (map fst n_as)) (listsum (map fst n_as))"
  unfolding mat_carrier_def by auto

lemma jordan_matrix_upper_triangular: "i < listsum (map fst n_as)
  \<Longrightarrow> j < i \<Longrightarrow> jordan_matrix n_as $$ (i,j) = 0"
  unfolding jordan_matrix_def
  by (rule diag_block_upper_triangular, auto simp: jordan_matrix_def[symmetric])

lemma jordan_matrix_pow: "(jordan_matrix n_as) ^\<^sub>m r = 
  diag_block_mat (map (\<lambda> (n,a). (jordan_block n a) ^\<^sub>m r) n_as)"
  unfolding jordan_matrix_def
  by (subst diag_block_mat_pow, force, rule arg_cong[of _ _ diag_block_mat], auto)

lemma jordan_matrix_char_poly: 
  "char_poly (jordan_matrix n_as) = (\<Prod>(n, a)\<leftarrow>n_as. [:- a, 1:] ^ n)"
proof -
  let ?n = "listsum (map fst n_as)"
  have "mat_diag
     ([:0, 1:] \<odot>\<^sub>m \<one>\<^sub>m (listsum (map fst n_as)) \<oplus>\<^sub>m map\<^sub>m (\<lambda>a. [:- a:]) (jordan_matrix n_as)) =
    concat (map (\<lambda>(n, a). replicate n [:- a, 1:]) n_as)" unfolding jordan_matrix_def
  proof (induct n_as)
    case (Cons na n_as)
    obtain n a where na: "na = (n,a)" by force
    let ?n2 = "listsum (map fst n_as)"
    note fbo = four_block_one_mat
    note mz = mat_zero_closed
    note mo = mat_one_closed
    have mA: "\<And> A. A \<in> carrier\<^sub>m (dim\<^sub>r A) (dim\<^sub>c A)" unfolding mat_carrier_def by auto
    let ?Bs = "map (\<lambda>(x, y). jordan_block x y) n_as"
    let ?B = "diag_block_mat ?Bs"
    from jordan_matrix_dim[of n_as, unfolded jordan_matrix_def]
    have dimB: "dim\<^sub>r ?B = ?n2" "dim\<^sub>c ?B = ?n2" by auto
    hence B: "?B \<in> carrier\<^sub>m ?n2 ?n2" unfolding mat_carrier_def by simp
    show ?case unfolding na fbo
    apply (simp add: Let_def fbo[symmetric] del: fbo)
    apply (subst four_block_scalar[OF mo mz mz mo])
    apply (subst four_block_map[OF jordan_block_carrier mz mz mA])
    apply (subst four_block_mat_add[of _ n n _ ?n2 _ ?n2], auto simp: dimB B)
    apply (subst four_block_diag[of _ n _ ?n2], auto simp: dimB B)
    apply (subst Cons, auto simp: jordan_block_def mat_diag_def, 
      intro nth_equalityI, auto)
    done
  qed (force simp: mat_diag_def)
  also have "listprod ... = (\<Prod>(n, a)\<leftarrow>n_as. [:- a, 1:] ^ n)"
    by (induct n_as, auto)
  finally
  show ?thesis unfolding char_poly_defs
    by (subst det_upper_triangular[of _ ?n], auto simp: jordan_matrix_upper_triangular)
qed

definition jordan_nf :: "'a :: semiring_1 mat \<Rightarrow> (nat \<times> 'a)list \<Rightarrow> bool" where
  "jordan_nf A n_as \<equiv> mat_similar A (jordan_matrix n_as)"

lemma jordan_nf_powE: assumes A: "A \<in> carrier\<^sub>m n n" and jnf: "jordan_nf A n_as" 
  obtains P Q where "P \<in> carrier\<^sub>m n n" "Q \<in> carrier\<^sub>m n n" and 
  "char_poly A = (\<Prod>(na, a)\<leftarrow>n_as. [:- a, 1:] ^ na)"
  "\<And> k. A ^\<^sub>m k = P \<otimes>\<^sub>m (jordan_matrix n_as)^\<^sub>m k \<otimes>\<^sub>m Q"
proof -
  from A have dim: "dim\<^sub>r A = n" by auto
  assume obt: "\<And>P Q. P \<in> carrier\<^sub>m n n \<Longrightarrow> Q \<in> carrier\<^sub>m n n \<Longrightarrow> 
    char_poly A = (\<Prod>(na, a)\<leftarrow>n_as. [:- a, 1:] ^ na) \<Longrightarrow> 
    (\<And>k. A ^\<^sub>m k = P \<otimes>\<^sub>m jordan_matrix n_as ^\<^sub>m k \<otimes>\<^sub>m Q) \<Longrightarrow> thesis"
  from jnf[unfolded jordan_nf_def] obtain P Q where
    simw: "mat_similar_wit A (jordan_matrix n_as) P Q"
    and sim: "mat_similar A (jordan_matrix n_as)" unfolding mat_similar_def by blast
  show thesis
  proof (rule obt)
    show "\<And> k. A ^\<^sub>m k = P \<otimes>\<^sub>m jordan_matrix n_as ^\<^sub>m k \<otimes>\<^sub>m Q"
      by (rule mat_similar_wit_pow_id[OF simw])
    show "char_poly A = (\<Prod>(na, a)\<leftarrow>n_as. [:- a, 1:] ^ na)"
      unfolding char_poly_similar[OF sim] jordan_matrix_char_poly ..    
  qed (insert simw[unfolded mat_similar_wit_def Let_def dim], auto)
qed

lemma choose_poly_bound: assumes "i \<le> d"
  shows "r choose i \<le> max 1 (r^d)"
proof (cases "i \<le> r")
  case False
  hence "r choose i = 0" by simp
  thus ?thesis by arith
next
  case True
  show ?thesis
  proof (cases r)
    case (Suc rr)
    from binomial_le_pow[OF True] have "r choose i \<le> r ^ i" by simp
    also have "\<dots> \<le> r^d" using power_increasing[OF \<open>i \<le> d\<close>, of r] Suc by auto
    finally show ?thesis by simp
  qed (insert True, simp)
qed  

context
  fixes b :: "'a :: archimedean_field"
  assumes b: "0 < b" "b < 1"
begin
      
lemma poly_exp_constant_bound: "\<exists> p. \<forall> x. c * b ^ x * of_nat x ^ deg \<le> p" 
proof (cases "c \<le> 0")
  case True
  show ?thesis
    by (rule exI[of _ 0], intro allI, 
    rule mult_nonpos_nonneg[OF mult_nonpos_nonneg[OF True]], insert b, auto)
next
  case False
  hence c: "c \<ge> 0" by simp
  from poly_exp_bound[OF b, of deg] obtain p where "\<And> x. b ^ x * of_nat x ^ deg \<le> p" by auto
  from mult_left_mono[OF this c]
  show ?thesis by (intro exI[of _ "c * p"], auto simp: ac_simps)
qed

lemma poly_exp_max_constant_bound: "\<exists> p. \<forall> x. c * b ^ x * max 1 (of_nat x ^ deg) \<le> p" 
proof -
  from poly_exp_constant_bound[of c deg] obtain p where
    p: "\<And> x. c * b ^ x * of_nat x ^ deg \<le> p" by auto
  show ?thesis
  proof (rule exI[of _ "max p c"], intro allI)
    fix x
    let ?exp = "of_nat x ^ deg :: 'a"
    show "c * b ^ x * max 1 ?exp \<le> max p c"
    proof (cases "x = 0")
      case False
      hence "?exp \<noteq> of_nat 0" by simp
      hence "?exp \<ge> 1" by (metis less_one not_less of_nat_1 of_nat_less_iff of_nat_power)
      hence "max 1 ?exp = ?exp" by simp
      thus ?thesis using p[of x] by simp
    qed (cases deg, auto)
  qed
qed
end

context
  fixes a :: "'a :: real_normed_field"
begin
lemma jordan_block_bound: 
  assumes i: "i < n" and j: "j < n"
  shows "norm ((jordan_block n a ^\<^sub>m k) $$ (i,j)) 
    \<le> norm a ^ (k + i - j) * max 1 (of_nat k ^ (n - 1))"
    (is "?lhs \<le> ?rhs")
proof -
  have id: "(jordan_block n a ^\<^sub>m k) $$ (i,j) = (if i \<le> j then of_nat (k choose (j - i)) * a ^ (k + i - j) else 0)"
    unfolding jordan_block_pow using i j by auto
  from i j have diff: "j - i \<le> n - 1" by auto
  show ?thesis
  proof (cases "i \<le> j")
    case False
    thus ?thesis unfolding id by simp
  next
    case True
    hence "?lhs = norm (of_nat (k choose (j - i)) * a ^ (k + i - j))" unfolding id by simp
    also have "\<dots> \<le> norm (of_nat (k choose (j - i)) :: 'a) * norm (a ^ (k + i - j))"
      by (rule norm_mult_ineq)
    also have "\<dots> \<le> (max 1 (of_nat k ^ (n - 1))) * norm a ^ (k + i - j)"
    proof (rule mult_mono[OF _ norm_power_ineq _ norm_ge_zero])
      have "k choose (j - i) \<le> max 1 (k ^ (n - 1))" 
        by (rule choose_poly_bound[OF diff])
      hence "norm (of_nat (k choose (j - i)) :: 'a) \<le> of_nat (max 1 (k ^ (n - 1)))"
        unfolding norm_of_nat of_nat_le_iff .
      also have "\<dots> = max 1 (of_nat k ^ (n - 1))" by (metis max_def of_nat_1 of_nat_le_iff of_nat_power)
      finally show "norm (of_nat (k choose (j - i)) :: 'a) \<le> max 1 (real_of_nat k ^ (n - 1))" .
    qed simp
    also have "\<dots> = ?rhs" by simp
    finally show ?thesis .
  qed
qed

lemma jordan_block_poly_bound: 
  assumes i: "i < n" and j: "j < n" and a: "norm a = 1"
  shows "norm ((jordan_block n a ^\<^sub>m k) $$ (i,j)) \<le> max 1 (of_nat k ^ (n - 1))"
    (is "?lhs \<le> ?rhs")
proof -
  from jordan_block_bound[OF i j, of k, unfolded a]
  show ?thesis by simp
qed


theorem jordan_block_constant_bound: assumes a: "norm a < 1" 
  shows "\<exists> p. \<forall> i j k. i < n \<longrightarrow> j < n \<longrightarrow> norm ((jordan_block n a ^\<^sub>m k) $$ (i,j)) \<le> p"
proof (cases "a = 0") 
  case True
  show ?thesis
  proof (rule exI[of _ 1], intro allI impI)
    fix i j k
    assume *: "i < n" "j < n"
    {
      assume ij: "i \<le> j"
      have "norm ((of_nat (k choose (j - i)) :: 'a) * 0 ^ (k + i - j)) \<le> 1" (is "norm ?lhs \<le> 1")
      proof (cases "k + i > j")
        case True
        hence "?lhs = 0" by simp
        also have "norm (\<dots>) \<le> 1" by simp
        finally show ?thesis .
      next
        case False
        hence id: "?lhs = (of_nat (k choose (j - i)) :: 'a)" and j: "j - i \<ge> k" by auto
        from j have "k choose (j - i) = 0 \<or> k choose (j - i) = 1" by (simp add: nat_less_le)
        thus "norm ?lhs \<le> 1"
        proof
          assume k: "k choose (j - i) = 0"
          show ?thesis unfolding id k by simp
        next
          assume k: "k choose (j - i) = 1"
          show ?thesis unfolding id unfolding k by simp
        qed
      qed
    }    
    thus "norm ((jordan_block n a ^\<^sub>m k) $$ (i,j)) \<le> 1" unfolding True
      unfolding jordan_block_pow using * by auto
  qed
next
  case False
  hence na: "norm a > 0" by auto
  def c \<equiv> "inverse (norm a ^ n)"
  def deg \<equiv> "n - 1"
  have c: "c > 0" unfolding c_def using na by auto
  def b \<equiv> "norm a"
  from a na have "0 < b" "b < 1" unfolding b_def by auto
  from poly_exp_max_constant_bound[OF this, of c deg]
  obtain p where "\<And> k. c * b ^ k * max 1 (of_nat k ^ deg) \<le> p" by auto
  show ?thesis
  proof (intro exI[of _ p], intro allI impI)
    fix i j k
    assume ij: "i < n" "j < n"
    from jordan_block_bound[OF this]
    have "norm ((jordan_block n a ^\<^sub>m k) $$ (i, j))
      \<le> norm a ^ (k + i - j) * max 1 (real_of_nat k ^ (n - 1))" .
    also have "\<dots> \<le> c * norm a ^ k * max 1 (real_of_nat k ^ (n - 1))"
    proof (rule mult_right_mono)
      from ij have "i - j \<le> n" by auto
      show "norm a ^ (k + i - j) \<le> c * norm a ^ k"
      proof (rule mult_left_le_imp_le)
        show "0 < norm a ^ n" using na by auto
        let ?lhs = "norm a ^ n * norm a ^ (k + i - j)"
        let ?rhs = "norm a ^ n * (c * norm a ^ k)"
        from ij have ge: "n + (k + i - j) \<ge> k" by arith
        have "?lhs = norm a ^ (n + (k + i - j))" by (simp add: power_add)
        also have "\<dots> \<le> norm a ^ k" using ge a na using less_imp_le power_decreasing by blast
        also have "\<dots> = ?rhs" unfolding c_def using na by simp
        finally show "?lhs \<le> ?rhs" .
      qed
    qed simp
    also have "\<dots> = c * b ^ k * max 1 (real_of_nat k ^ deg)" unfolding b_def deg_def ..
    also have "\<dots> \<le> p" by fact
    finally show "norm ((jordan_block n a ^\<^sub>m k) $$ (i, j)) \<le> p" .
  qed
qed

definition norm_bound :: "'a mat \<Rightarrow> real \<Rightarrow> bool" where
  "norm_bound A b \<equiv> \<forall> i j. i < dim\<^sub>r A \<longrightarrow> j < dim\<^sub>c A \<longrightarrow> norm (A $$ (i,j)) \<le> b"

lemma norm_boundI[intro]:
  assumes "\<And> i j. i < dim\<^sub>r A \<Longrightarrow> j < dim\<^sub>c A \<Longrightarrow> norm (A $$ (i,j)) \<le> b"
  shows "norm_bound A b"
  unfolding norm_bound_def using assms by blast

lemma  jordan_block_constant_bound2:
"\<exists>p. norm (a :: 'a :: real_normed_field) < 1 \<longrightarrow>
    (\<forall>i j k. i < n \<longrightarrow> j < n \<longrightarrow> norm ((jordan_block n a ^\<^sub>m k) $$ (i, j)) \<le> p)"
using jordan_block_constant_bound by auto

lemma jordan_matrix_poly_bound2:
  fixes n_as :: "(nat \<times> 'a) list"
  assumes n_as: "\<And> n a. (n,a) \<in> set n_as \<Longrightarrow> n > 0 \<Longrightarrow> norm a \<le> 1"
  and N: "\<And> n a. (n,a) \<in> set n_as \<Longrightarrow> norm a = 1 \<Longrightarrow> n \<le> N"
  shows "\<exists>c1. \<forall>k. \<forall>e \<in> mat_elements (jordan_matrix n_as ^\<^sub>m k).
    norm e \<le> c1 + of_nat k ^ (N - 1)"
proof -
  from jordan_matrix_carrier[of n_as] obtain d where
    jm: "jordan_matrix n_as \<in> carrier\<^sub>m d d" by blast
  def f \<equiv> "\<lambda>n (a::'a) i j k. norm ((jordan_block n a ^\<^sub>m k) $$ (i,j))"
  let ?g = "\<lambda>k c1. c1 + of_nat k ^ (N-1)"
  let ?P = "\<lambda>n (a::'a) i j k c1. f n a i j k \<le> ?g k c1"
  def Q \<equiv> "\<lambda>n (a::'a) k c1. \<forall>i j. i<n \<longrightarrow> j<n \<longrightarrow> ?P n a i j k c1"
  have "\<And> c c' k n a i j. c \<le> c' \<Longrightarrow> ?P n a i j k c \<Longrightarrow> ?P n a i j k c'" by auto  
  hence Q_mono: "\<And>n a c c'. c \<le> c' \<Longrightarrow> \<forall>k. Q n a k c \<Longrightarrow> \<forall>k. Q n a k c'"
    unfolding Q_def by arith
  { fix n a assume na: "(n,a) \<in> set n_as"
    obtain c where c: "norm a < 1 \<longrightarrow> (\<forall>i j k. i < n \<longrightarrow> j < n \<longrightarrow> f n a i j k \<le> c)"
      apply (rule exE[OF jordan_block_constant_bound2])
      unfolding f_def using Jordan_Normal_Form.jordan_block_constant_bound2
      by metis
    def c1 \<equiv> "max 1 c"
    then have "c1 \<ge> 1" "c1 \<ge> c" by auto
    have "\<exists>c1. \<forall>k i j. i < n \<longrightarrow> j < n \<longrightarrow> ?P n a i j k c1"
    proof rule+
      fix i j k assume "i < n" "j < n"
      then have "0<n" by auto
      let ?jbs = "map (\<lambda>(n,a). jordan_block n a) n_as"
      have sq_jbs: "Ball (set ?jbs) square_mat" by auto
      have "jordan_matrix n_as ^\<^sub>m k = diag_block_mat (map (\<lambda>A. A ^\<^sub>m k) ?jbs)"
        unfolding jordan_matrix_def using diag_block_mat_pow[OF sq_jbs] by auto
      show "?P n a i j k c1"
      proof (cases "norm a = 1")
        case True {
          have nN:"n-1 \<le> N-1" using N[OF na] True by auto
          have "f n a i j k \<le> max 1 (of_nat k ^ (n-1))"
            using Jordan_Normal_Form.jordan_block_poly_bound True \<open>i<n\<close> \<open>j<n\<close>
            unfolding f_def by auto
          also have "... \<le> max 1 (of_nat k ^ (N-1))"
            proof (cases "k=0")
              case False then show ?thesis
                by (subst max.mono[OF _ power_increasing[OF nN]], auto)
            qed (simp add: realpow_num_eq_if)
          also have "... \<le> max c1 (of_nat k ^ (N-1))" using \<open>c1\<ge>1\<close> by auto
          also have "... \<le> c1 + (of_nat k ^ (N-1))" using \<open>c1\<ge>1\<close> by auto
          finally show ?thesis by simp
        } next
        case False {
          then have na1: "norm a < 1" using n_as[OF na] \<open>0<n\<close> by auto
          hence "f n a i j k \<le> c" using c \<open>i<n\<close> \<open>j<n\<close> by auto
          also have "... \<le> c1" using \<open>c\<le>c1\<close>.
          also have "... \<le> c1 + of_nat k ^ (N-1)" by auto
          finally show ?thesis by auto
        }
      qed
    qed
  }
  hence "\<forall>na. \<exists>c1. na \<in> set n_as \<longrightarrow> (\<forall>k. Q (fst na) (snd na) k c1)"
    unfolding Q_def by auto
  from choice[OF this] obtain c'
    where c': "\<And> na k. na \<in> set n_as \<Longrightarrow> Q (fst na) (snd na) k (c' na)" by blast
  def c \<equiv> "max 0 (Max (set (map c' n_as)))"
  { fix n a assume na: "(n,a) \<in> set n_as"
    then have Q: "\<forall> k. Q n a k (c' (n,a))" using c'[OF na] by auto
    from na have "c' (n,a) \<in> set (map c' n_as)" by auto
    from Max_ge[OF _ this] have "c' (n,a) \<le> c" unfolding c_def by auto
    from Q_mono[OF this Q] have "\<And> k. Q n a k c" by blast
  }
  hence Q: "\<And>k n a. (n,a) \<in> set n_as \<Longrightarrow> Q n a k c" by auto
  have c0: "c \<ge> 0" unfolding c_def by simp
  { fix k n a e
    assume na:"(n,a) \<in> set n_as"
    let ?jbk = "jordan_block n a ^\<^sub>m k"
    assume "e \<in> mat_elements ?jbk"
    from mat_elementsD[OF this] obtain i j
      where "i < n" "j < n" and [simp]: "e = ?jbk $$ (i,j)"
      by (simp only:mat_pow_dim_square[OF jordan_block_carrier],auto)
    hence "norm e \<le> ?g k c" using Q[OF na] unfolding Q_def f_def by simp
  }
  hence norm_jordan:
    "\<And>k. \<forall>(n,a) \<in> set n_as. \<forall>e \<in> mat_elements (jordan_block n a ^\<^sub>m k).
     norm e \<le> ?g k c" by auto
  { fix k
    let ?jmk = "jordan_matrix n_as ^\<^sub>m k"
    have "dim\<^sub>r ?jmk = d" "dim\<^sub>c ?jmk = d"
      using jm by (simp only:mat_pow_dim_square[OF jm])+
    let ?As = "(map (\<lambda>(n,a). jordan_block n a ^\<^sub>m k) n_as)"
    have "\<And>e. e \<in> mat_elements ?jmk \<Longrightarrow> norm e \<le> ?g k c"
    proof -
      fix e assume e:"e \<in> mat_elements ?jmk"
      obtain i j where ij: "i < d" "j < d" and "e = ?jmk $$ (i,j)"
        using mat_elementsD[OF e] by (simp only:mat_pow_dim_square[OF jm],auto)
      have "?jmk = diag_block_mat ?As"
        using jordan_matrix_pow[of n_as k] by auto
      hence "mat_elements ?jmk \<subseteq> {0} \<union> \<Union> set (map mat_elements ?As)"
        using diag_block_mat_elements[of ?As] by auto
      hence e_mem: "e \<in> {0} \<union> \<Union> set (map mat_elements ?As)" using e by auto
      show "norm e \<le> ?g k c"
      proof (cases "e = 0")
        case False
          then have "e \<in> \<Union> set (map mat_elements ?As)" using e_mem by auto
          then obtain n a
            where "e \<in> mat_elements (jordan_block n a ^\<^sub>m k)"
            and na: "(n,a) \<in> set n_as" by force
          thus ?thesis using norm_jordan na by force
      qed (insert c0, auto)
    qed
  }
  thus ?thesis by auto
qed

lemma norm_bound_bridge:
  "\<forall>e \<in> mat_elements A. norm e \<le> b \<Longrightarrow> norm_bound A b"
  unfolding norm_bound_def by force

lemma norm_bound_mult: assumes A1: "A1 \<in> carrier\<^sub>m nr n"
  and A2: "A2 \<in> carrier\<^sub>m n nc"
  and b1: "norm_bound A1 b1"
  and b2: "norm_bound A2 b2"
  shows "norm_bound (A1 \<otimes>\<^sub>m A2) (b1 * b2 * of_nat n)"
proof 
  let ?A = "A1 \<otimes>\<^sub>m A2"
  let ?n = "of_nat n"
  fix i j
  assume i: "i < dim\<^sub>r ?A" and j: "j < dim\<^sub>c ?A"
  def v1 \<equiv> "\<lambda> k. row A1 i $ k"
  def v2 \<equiv> "\<lambda> k. col A2 j $ k"
  from assms(1-2) have dim: "dim\<^sub>r A1 = nr" "dim\<^sub>c A2 = nc" "dim\<^sub>c A1 = n" "dim\<^sub>r A2 = n" by auto
  {
    fix k
    assume k: "k < n"
    have n: "norm (v1 k) \<le> b1" "norm (v2 k) \<le> b2" 
      using i j k dim v1_def v2_def
      b1[unfolded norm_bound_def, rule_format, of i k] 
      b2[unfolded norm_bound_def, rule_format, of k j] by auto
    have "norm (v1 k * v2 k) \<le> norm (v1 k) * norm (v2 k)" by (rule norm_mult_ineq)
    also have "\<dots> \<le> b1 * b2" by (rule mult_mono'[OF n], auto)
    finally have "norm (v1 k * v2 k) \<le> b1 * b2" .
  } note bound = this
  have "?A $$ (i,j) = row A1 i \<bullet> col A2 j" using dim i j by simp
  also have "\<dots> = (\<Sum> k = 0 ..< n. v1 k * v2 k)" unfolding scalar_prod_def 
    using dim i j v1_def v2_def by simp
  also have "norm (\<dots>) \<le> (\<Sum> k = 0 ..< n. b1 * b2)" 
    by (rule setsum_norm_le, insert bound, simp)
  also have "\<dots> = b1 * b2 * ?n" by simp
  finally show "norm (?A $$ (i,j)) \<le> b1 * b2 * ?n" .
qed

lemma norm_bound_max: "norm_bound A (Max {norm (A $$ (i,j)) | i j. i < dim\<^sub>r A \<and> j < dim\<^sub>c A})" 
  (is "norm_bound A (Max ?norms)")
proof 
  fix i j
  have fin: "finite ?norms" by (simp add: finite_image_set2)
  assume "i < dim\<^sub>r A" and "j < dim\<^sub>c A"     
  hence "norm (A $$ (i,j)) \<in> ?norms" by auto
  from Max_ge[OF fin this] show "norm (A $$ (i,j)) \<le> Max ?norms" .
qed

lemma jordan_matrix_poly_bound: fixes n_as :: "(nat \<times> 'a)list"
  assumes n_as: "\<And> n a. (n,a) \<in> set n_as \<Longrightarrow> n > 0 \<Longrightarrow> norm a \<le> 1"
  and N: "\<And> n a. (n,a) \<in> set n_as \<Longrightarrow> norm a = 1 \<Longrightarrow> n \<le> N"
  shows "\<exists> c1. \<forall> k. norm_bound (jordan_matrix n_as ^\<^sub>m k) (c1 + of_nat k ^ (N - 1))" 
  using jordan_matrix_poly_bound2 norm_bound_bridge N n_as
  by metis

lemma jordan_nf_matrix_poly_bound: fixes n_as :: "(nat \<times> 'a)list"
  assumes A: "A \<in> carrier\<^sub>m n n"
  and n_as: "\<And> n a. (n,a) \<in> set n_as \<Longrightarrow> n > 0 \<Longrightarrow> norm a \<le> 1"
  and N: "\<And> n a. (n,a) \<in> set n_as \<Longrightarrow> norm a = 1 \<Longrightarrow> n \<le> N"
  and jnf: "jordan_nf A n_as"
  shows "\<exists> c1 c2. \<forall> k. norm_bound (A ^\<^sub>m k) (c1 + c2 * of_nat k ^ (N - 1))"
proof -
  let ?cp2 = "\<Prod>(n, a)\<leftarrow>n_as. [:- a, 1:] ^ n"
  let ?J = "jordan_matrix n_as"
  from jnf[unfolded jordan_nf_def]
  have sim: "mat_similar A ?J" .
  then obtain P Q where sim_wit: "mat_similar_wit A ?J P Q" unfolding mat_similar_def by auto
  from mat_similar_wit_pow_id[OF this] have pow: "\<And> k. A ^\<^sub>m k = P \<otimes>\<^sub>m ?J ^\<^sub>m k \<otimes>\<^sub>m Q" .
  from sim_wit[unfolded mat_similar_wit_def Let_def] A 
  have J: "?J \<in> carrier\<^sub>m n n" and P: "P \<in> carrier\<^sub>m n n" and Q: "Q \<in> carrier\<^sub>m n n"
    unfolding mat_carrier_def by force+
  have "\<exists>c1. \<forall> k. norm_bound (?J ^\<^sub>m k) (c1 + of_nat k ^ (N - 1))"
    by (rule jordan_matrix_poly_bound[OF n_as N])
  then obtain c1 where 
    bound_pow: "\<And> k. norm_bound ((?J ^\<^sub>m k)) (c1 + of_nat k ^ (N - 1))" by blast
  obtain bP where bP: "norm_bound P bP" using norm_bound_max[of P] by auto
  obtain bQ where bQ: "norm_bound Q bQ" using norm_bound_max[of Q] by auto
  let ?n = "of_nat n :: real"
  let ?c2 = "bP * ?n * bQ * ?n"
  let ?c1 = "?c2 * c1"
  {
    fix k
    have Jk: "?J ^\<^sub>m k \<in> carrier\<^sub>m n n" using J by simp
    from norm_bound_mult[OF mat_mult_mat_closed[OF P Jk] Q 
      norm_bound_mult[OF P Jk bP bound_pow] bQ, folded pow] 
    have "norm_bound (A ^\<^sub>m k) (?c1 + ?c2 * of_nat k ^ (N - 1))"  (is "norm_bound _ ?exp") 
      by (simp add: field_simps)
  } note main = this
  show ?thesis 
    by (intro exI allI, rule main)
qed
end

context 
  fixes f_ty :: "'a :: field itself"
begin
lemma char_matrix_jordan_block: "char_matrix (jordan_block n a) b = (jordan_block n (a - b))"
  unfolding char_matrix_def jordan_block_def by auto

lemma diag_jordan_block_pow: "mat_diag (jordan_block n (a :: 'a) ^\<^sub>m k) = replicate n (a ^ k)"
  unfolding mat_diag_def jordan_block_pow
  by (intro nth_equalityI, auto)

lemma jordan_block_zero_pow: "(jordan_block n (0 :: 'a)) ^\<^sub>m k = 
  (mat n n (\<lambda> (i,j). if j \<ge> i \<and> j - i = k then 1 else 0))"
proof -
  {
    fix i j
    assume  *: "j - i \<noteq> k"
    have "of_nat (k choose (j - i)) * 0 ^ (k + i - j) = (0 :: 'a)"
    proof (cases "k + i - j > 0")
      case True thus ?thesis by (cases "k + i - j", auto)
    next
      case False
      with * have "j - i > k" by auto
      thus ?thesis by (simp add: binomial_eq_0)
    qed
  }
  thus ?thesis unfolding jordan_block_pow by (intro mat_eqI, auto)
qed
end

lemma jordan_matrix_concat_diag_block_mat: "jordan_matrix (concat jbs) = diag_block_mat (map jordan_matrix jbs)"
  unfolding jordan_matrix_def[abs_def]
  by (induct jbs, auto simp: diag_block_mat_append Let_def)

lemma jordan_nf_diag_block_mat: assumes Ms: "\<And> A jbs. (A,jbs) \<in> set Ms \<Longrightarrow> jordan_nf A jbs"
  shows "jordan_nf (diag_block_mat (map fst Ms)) (concat (map snd Ms))"
proof -
  let ?Ms = "map (\<lambda> (A, jbs). (A, jordan_matrix jbs)) Ms"
  have id: "map fst ?Ms = map fst Ms" by auto
  have id2: "map snd ?Ms = map jordan_matrix (map snd Ms)" by auto
  {
    fix A B
    assume "(A,B) \<in> set ?Ms"
    then obtain jbs where mem: "(A,jbs) \<in> set Ms" and B: "B = jordan_matrix jbs" by auto
    from Ms[OF mem] have "mat_similar A B" unfolding B jordan_nf_def .
  }
  from mat_similar_diag_block_mat[of ?Ms, OF this, unfolded id id2]
  show ?thesis
    unfolding jordan_nf_def jordan_matrix_concat_diag_block_mat by auto
qed  


lemma jordan_nf_char_poly: assumes "jordan_nf A n_as"
  shows "char_poly A = (\<Prod> (n,a) \<leftarrow> n_as. [:- a, 1:] ^ n)"
  unfolding jordan_matrix_char_poly[symmetric]
  by (rule char_poly_similar, insert assms[unfolded jordan_nf_def])

lemma jordan_nf_block_size_order_bound: assumes jnf: "jordan_nf A n_as"
  and mem: "(n,a) \<in> set n_as"
  shows "n \<le> order a (char_poly A)"
proof -
  from jnf[unfolded jordan_nf_def]
  have "mat_similar A (jordan_matrix n_as)" .
  from mat_similarD[OF this] obtain m where "A \<in> carrier\<^sub>m m m" by auto
  from degree_monic_char_poly[OF this] have A: "char_poly A \<noteq> 0" by auto
  from mem obtain as bs where nas: "n_as = as @ (n,a) # bs" 
    by (meson split_list)
  from jordan_nf_char_poly[OF jnf] 
  have cA: "char_poly A = (\<Prod>(n, a)\<leftarrow>n_as. [:- a, 1:] ^ n)" .
  also have "\<dots> = [: -a, 1:] ^ n * (\<Prod>(n, a)\<leftarrow> as @ bs. [:- a, 1:] ^ n)" unfolding nas by auto
  also have "[: -a,1 :] ^ n dvd \<dots>" unfolding dvd_def by blast
  finally have "[: -a,1 :] ^ n dvd char_poly A" by auto
  from order_max[OF this A] show ?thesis .
qed


subsection \<open>Application for Complexity\<close>

lemma factored_char_poly_norm_bound: assumes A: "A \<in> carrier\<^sub>m n n"
  and linear_factors: "char_poly A = (\<Prod> (a :: 'a :: real_normed_field) \<leftarrow> as. [:- a, 1:])"
  and jnf_exists: "\<exists> n_as. jordan_nf A n_as" 
  and le_1: "\<And> a. a \<in> set as \<Longrightarrow> norm a \<le> 1"
  and le_N: "\<And> a. a \<in> set as \<Longrightarrow> norm a = 1 \<Longrightarrow> length (filter (op = a) as) \<le> N"
  shows "\<exists> c1 c2. \<forall> k. norm_bound (A ^\<^sub>m k) (c1 + c2 * of_nat k ^ (N - 1))"
proof -
  from jnf_exists obtain n_as 
    where jnf: "jordan_nf A n_as" by auto
  let ?cp1 = "(\<Prod> a \<leftarrow> as. [:- a, 1:])"
  let ?cp2 = "\<Prod>(n, a)\<leftarrow>n_as. [:- a, 1:] ^ n"
  let ?J = "jordan_matrix n_as"
  from jnf[unfolded jordan_nf_def]
  have sim: "mat_similar A ?J" .
  from char_poly_similar[OF sim, unfolded linear_factors jordan_matrix_char_poly]
  have cp: "?cp1 = ?cp2" .
  show ?thesis
  proof (rule jordan_nf_matrix_poly_bound[OF A _ _ jnf])
    fix n a
    assume na: "(n,a) \<in> set n_as"
    then obtain na1 na2 where n_as: "n_as = na1 @ (n,a) # na2"
      unfolding in_set_conv_decomp by auto
    then obtain p where "?cp2 = [: -a, 1 :]^n * p" unfolding n_as by auto
    from cp[unfolded this] have dvd: "[: -a, 1 :] ^ n dvd ?cp1" by auto
    let ?as = "filter (op = a) as"
    let ?pn = "\<lambda> as. \<Prod>a\<leftarrow>as. [:- a, 1:]"
    let ?p = "\<lambda> as. \<Prod>a\<leftarrow>as. [: a, 1:]"
    have "?pn as = ?p (map uminus as)" by (induct as, auto)
    from poly_linear_exp_linear_factors[OF dvd[unfolded this]] 
    have "n \<le> length (filter (op = (- a)) (map uminus as))" .
    also have "\<dots> = length (filter (op = a) as)" 
      by (induct as, auto)
    finally have filt: "n \<le> length (filter (op = a) as)" .
    {
      assume "0 < n"
      with filt obtain b bs where "?as = b # bs" by (cases ?as, auto)
      from arg_cong[OF this, of set]
      have "a \<in> set as" by auto 
      from le_1[rule_format, OF this]
      show "norm a \<le> 1" .
      note `a \<in> set as`
    } note mem = this
    {
      assume "norm a = 1" 
      from le_N[OF mem this] filt show "n \<le> N" by (cases n, auto)
    }
  qed
qed

end
