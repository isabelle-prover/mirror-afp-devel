section \<open>Integral and Bounded Matrices and Vectors\<close>

text \<open>We define notions of integral vectors and matrices and bounded vectors and matrices
  and prove some preservation lemmas. Moreover, we prove two bounds on determinants.\<close>
theory Integral_Bounded_Vectors
  imports
    Missing_VS_Connect
    Sum_Vec_Set
    LLL_Basis_Reduction.Gram_Schmidt_2 (* for some simp-rules *)
begin

(* TODO: move into theory Norms *)
lemma sq_norm_unit_vec[simp]: assumes i: "i < n"
  shows "\<parallel>unit_vec n i\<parallel>\<^sup>2 = (1 :: 'a :: {comm_ring_1,conjugatable_ring})"
proof -
  from i have id: "[0..<n] = [0..<i] @ [i] @ [Suc i ..< n]"
    by (metis append_Cons append_Nil diff_zero length_upt list_trisect)
  show ?thesis unfolding sq_norm_vec_def unit_vec_def
    by (auto simp: o_def id, subst (1 2) sum_list_0, auto)
qed

definition Ints_vec ("\<int>\<^sub>v") where
  "\<int>\<^sub>v = {x. \<forall> i < dim_vec x. x $ i \<in> \<int>}"

definition indexed_Ints_vec  where
  "indexed_Ints_vec I = {x. \<forall> i < dim_vec x. i \<in> I \<longrightarrow> x $ i \<in> \<int>}"

lemma indexed_Ints_vec_UNIV: "\<int>\<^sub>v = indexed_Ints_vec UNIV"
  unfolding Ints_vec_def indexed_Ints_vec_def by auto

lemma indexed_Ints_vec_subset: "\<int>\<^sub>v \<subseteq> indexed_Ints_vec I"
  unfolding Ints_vec_def indexed_Ints_vec_def by auto

lemma Ints_vec_vec_set: "v \<in> \<int>\<^sub>v = (vec_set v \<subseteq> \<int>)"
  unfolding Ints_vec_def vec_set_def by auto

definition Ints_mat ("\<int>\<^sub>m") where
  "\<int>\<^sub>m = {A. \<forall> i < dim_row A. \<forall> j < dim_col A. A $$ (i,j) \<in> \<int>}"

lemma Ints_mat_elements_mat: "A \<in> \<int>\<^sub>m = (elements_mat A \<subseteq> \<int>)"
  unfolding Ints_mat_def elements_mat_def by force

lemma minus_in_Ints_vec_iff[simp]: "(-x) \<in> \<int>\<^sub>v \<longleftrightarrow> (x :: 'a :: ring_1 vec) \<in> \<int>\<^sub>v"
  unfolding Ints_vec_vec_set by (auto simp: minus_in_Ints_iff)

lemma minus_in_Ints_mat_iff[simp]: "(-A) \<in> \<int>\<^sub>m \<longleftrightarrow> (A :: 'a :: ring_1 mat) \<in> \<int>\<^sub>m"
  unfolding Ints_mat_elements_mat by (auto simp: minus_in_Ints_iff)

lemma Ints_vec_rows_Ints_mat[simp]: "set (rows A) \<subseteq> \<int>\<^sub>v \<longleftrightarrow> A \<in> \<int>\<^sub>m"
  unfolding rows_def Ints_vec_def Ints_mat_def by force

lemma unit_vec_integral[simp,intro]: "unit_vec n i \<in> \<int>\<^sub>v"
  unfolding Ints_vec_def by (auto simp: unit_vec_def)

lemma diff_indexed_Ints_vec:
  "x \<in> carrier_vec n \<Longrightarrow> y \<in> carrier_vec n \<Longrightarrow> x \<in> indexed_Ints_vec I \<Longrightarrow> y \<in> indexed_Ints_vec I
  \<Longrightarrow> x - y \<in> indexed_Ints_vec I"
  unfolding indexed_Ints_vec_def by auto

lemma smult_indexed_Ints_vec: "x \<in> \<int> \<Longrightarrow> v \<in> indexed_Ints_vec I \<Longrightarrow> x \<cdot>\<^sub>v v \<in> indexed_Ints_vec I" 
  unfolding indexed_Ints_vec_def smult_vec_def by simp

lemma add_indexed_Ints_vec:
  "x \<in> carrier_vec n \<Longrightarrow> y \<in> carrier_vec n \<Longrightarrow> x \<in> indexed_Ints_vec I \<Longrightarrow> y \<in> indexed_Ints_vec I
  \<Longrightarrow> x + y \<in> indexed_Ints_vec I"
  unfolding indexed_Ints_vec_def by auto

lemma (in vec_space) lincomb_indexed_Ints_vec: assumes cI: "\<And> x. x \<in> C \<Longrightarrow> c x \<in> \<int>"
  and C: "C \<subseteq> carrier_vec n"
  and CI: "C \<subseteq> indexed_Ints_vec I"
shows "lincomb c C \<in> indexed_Ints_vec I"
proof -
  from C have id: "dim_vec (lincomb c C) = n" by auto
  show ?thesis unfolding indexed_Ints_vec_def mem_Collect_eq id
  proof (intro allI impI)
    fix i
    assume i: "i < n" and iI: "i \<in> I"
    have "lincomb c C $ i = (\<Sum>x\<in>C. c x * x $ i)"
      by (rule lincomb_index[OF i C])
    also have "\<dots> \<in> \<int>"
      by (intro Ints_sum Ints_mult cI, insert i iI CI[unfolded indexed_Ints_vec_def] C, force+)
    finally show "lincomb c C $ i \<in> \<int>" .
  qed
qed

definition "Bounded_vec (b :: 'a :: linordered_idom) = {x . \<forall> i < dim_vec x . abs (x $ i) \<le> b}"

lemma Bounded_vec_vec_set: "v \<in> Bounded_vec b \<longleftrightarrow> (\<forall> x \<in> vec_set v. abs x \<le> b)"
  unfolding Bounded_vec_def vec_set_def by auto

definition "Bounded_mat (b :: 'a :: linordered_idom) =
  {A . (\<forall> i < dim_row A . \<forall> j < dim_col A. abs (A $$ (i,j)) \<le> b)}"

lemma Bounded_mat_elements_mat: "A \<in> Bounded_mat b \<longleftrightarrow> (\<forall> x \<in> elements_mat A. abs x \<le> b)"
  unfolding Bounded_mat_def elements_mat_def by auto

lemma Bounded_vec_rows_Bounded_mat[simp]: "set (rows A) \<subseteq> Bounded_vec B \<longleftrightarrow> A \<in> Bounded_mat B"
  unfolding rows_def Bounded_vec_def Bounded_mat_def by force

lemma unit_vec_Bounded_vec[simp,intro]: "unit_vec n i \<in> Bounded_vec (max 1 Bnd)"
  unfolding Bounded_vec_def unit_vec_def by auto

lemma unit_vec_int_bounds: "set (unit_vecs n) \<subseteq> \<int>\<^sub>v \<inter> Bounded_vec (of_int (max 1 Bnd))" 
  unfolding unit_vecs_def by (auto simp: Bounded_vec_def)

lemma Bounded_matD: assumes "A \<in> Bounded_mat b"
  "A \<in> carrier_mat nr nc"
shows "i < nr \<Longrightarrow> j < nc \<Longrightarrow> abs (A $$ (i,j)) \<le> b"
  using assms unfolding Bounded_mat_def by auto

lemma Bounded_vec_mono: "b \<le> B \<Longrightarrow> Bounded_vec b \<subseteq> Bounded_vec B"
  unfolding Bounded_vec_def by auto

lemma Bounded_mat_mono: "b \<le> B \<Longrightarrow> Bounded_mat b \<subseteq> Bounded_mat B"
  unfolding Bounded_mat_def by force

lemma finite_Bounded_vec_Max:
  assumes A: "A \<subseteq> carrier_vec n"
    and fin: "finite A"
  shows "A \<subseteq> Bounded_vec (Max { abs (a $ i) | a i. a \<in> A \<and> i < n})"
proof
  let ?B = "{ abs (a $ i) | a i. a \<in> A \<and> i < n}"
  have fin: "finite ?B"
    by (rule finite_subset[of _ "(\<lambda> (a,i). abs (a $ i)) ` (A \<times> {0 ..< n})"], insert fin, auto)
  fix a
  assume a: "a \<in> A"
  show "a \<in> Bounded_vec (Max ?B)"
    unfolding Bounded_vec_def
    by (standard, intro allI impI Max_ge[OF fin], insert a A, force)
qed

definition is_det_bound :: "(nat \<Rightarrow> 'a :: linordered_idom \<Rightarrow> 'a) \<Rightarrow> bool" where
  "is_det_bound f = (\<forall> A n x. A \<in> carrier_mat n n \<longrightarrow> A \<in> Bounded_mat x \<longrightarrow> abs (det A) \<le> f n x)" 

lemma is_det_bound_ge_zero: assumes "is_det_bound f"
  and "x \<ge> 0" 
  shows "f n x \<ge> 0" 
  using assms(1)[unfolded is_det_bound_def, rule_format, of "0\<^sub>m n n" n x]
  using assms(2) unfolding Bounded_mat_def by auto

definition det_bound_fact :: "nat \<Rightarrow> 'a :: linordered_idom \<Rightarrow> 'a" where
  "det_bound_fact n x = fact n * (x^n)"

lemma det_bound_fact: "is_det_bound det_bound_fact" 
  unfolding is_det_bound_def
proof (intro allI impI)
  fix A :: "'a :: linordered_idom mat" and n x
  assume A: "A \<in> carrier_mat n n"
    and x: "A \<in> Bounded_mat x"
  show "abs (det A) \<le> det_bound_fact n x"
  proof -
    have "abs (det A) = abs (\<Sum>p | p permutes {0..<n}. signof p * (\<Prod>i = 0..<n. A $$ (i, p i)))"
      unfolding det_def'[OF A] ..
    also have "\<dots> \<le> (\<Sum>p | p permutes {0..<n}. abs (signof p * (\<Prod>i = 0..<n. A $$ (i, p i))))"
      by (rule sum_abs)
    also have "\<dots> = (\<Sum>p | p permutes {0..<n}. (\<Prod>i = 0..<n. abs (A $$ (i, p i))))"
      by (rule sum.cong[OF refl], auto simp: abs_mult abs_prod sign_def simp flip: of_int_abs)
    also have "\<dots> \<le> (\<Sum>p | p permutes {0..<n}. (\<Prod>i = 0..<n. x))"
      by (intro sum_mono prod_mono conjI Bounded_matD[OF x A], auto)
    also have "\<dots> = fact n * x^n" by (auto simp add: card_permutations)
    finally show "abs (det A) \<le> det_bound_fact n x" unfolding det_bound_fact_def by auto
  qed
qed


lemma (in gram_schmidt_fs) Gramian_determinant_det: assumes A: "A \<in> carrier_mat n n"
  shows "Gramian_determinant (rows A) n = det A * det A" 
proof -
  have [simp]: "mat_of_rows n (rows A) = A" using A
    by (intro eq_matI, auto)
  show ?thesis using A
  unfolding Gramian_determinant_def
  by (subst Gramian_matrix_alt_def, force, simp add: Let_def, subst det_mult[of _ n], 
    auto simp: det_transpose)
qed

lemma (in gram_schmidt_fs_lin_indpt) det_bound_main: assumes rows: "rows A = fs"
  and A: "A \<in> carrier_mat n n" 
  and n0: "n > 0" 
  and Bnd: "A \<in> Bounded_mat c"  
shows 
  "(abs (det A))^2 \<le> of_nat n ^ n * c ^ (2 * n)" 
proof -
  from n0 A Bnd have "abs (A $$ (0,0)) \<le> c" by (auto simp: Bounded_mat_def)
  hence c0: "c \<ge> 0" by auto
  from n0 A rows have fs: "set fs \<noteq> {}" by (auto simp: rows_def)
  from rows A have len: "length fs = n" by auto
  have "(abs (det A))^2 = det A * det A" unfolding power2_eq_square by simp
  also have "\<dots> = d n" using Gramian_determinant_det[OF A] unfolding rows by simp 
  also have "\<dots> = (\<Prod>j<n. \<parallel>gso j\<parallel>\<^sup>2)" 
    by (rule Gramian_determinant(1), auto simp: len)
  also have "\<dots> \<le> (\<Prod>j<n. N)" 
    by (rule prod_mono, insert N_gso, auto simp: len)
  also have "\<dots> = N^n" by simp
  also have "\<dots> \<le> (of_nat n * c^2)^n" 
  proof (rule power_mono)
    show "0 \<le> N" using N_ge_0 len n0 by auto
    show "N \<le> of_nat n * c^2" unfolding N_def
    proof (intro Max.boundedI, force, use fs in force, clarify)
      fix f
      assume "f \<in> set fs" 
      from this[folded rows] obtain i where i: "i < n" and f: "f = row A i" 
        using A unfolding rows_def by auto
      have "\<parallel>f\<parallel>\<^sup>2 = (\<Sum>x\<leftarrow>list_of_vec (row A i). x^2)" 
        unfolding f sq_norm_vec_def power2_eq_square by simp
      also have "list_of_vec (row A i) = map (\<lambda> j. A $$ (i,j)) [0..<n]" 
        using i A by (intro nth_equalityI, auto)
      also have "sum_list (map power2 (map (\<lambda>j. A $$ (i, j)) [0..<n])) \<le>
          sum_list (map (\<lambda> j. c^2) [0..<n])" unfolding map_map o_def
      proof (intro sum_list_mono)
        fix j
        assume "j \<in> set [0 ..< n]" 
        hence j: "j < n" by auto
        from Bnd i j A have "\<bar>A $$ (i, j)\<bar> \<le> c" by (auto simp: Bounded_mat_def)
        thus "(A $$ (i, j))\<^sup>2 \<le> c\<^sup>2"
          by (meson abs_ge_zero order_trans power2_le_iff_abs_le)
      qed
      also have "\<dots> = (\<Sum>j <n. c\<^sup>2)"
        unfolding interv_sum_list_conv_sum_set_nat by auto
      also have "\<dots> = of_nat n * c\<^sup>2" by auto
      finally show "\<parallel>f\<parallel>\<^sup>2 \<le> of_nat n * c\<^sup>2" .
    qed
  qed
  also have "\<dots> = (of_nat n)^n * (c\<^sup>2 ^ n)" by (auto simp: algebra_simps)
  also have "\<dots> =  of_nat n ^n * c^(2 * n)" unfolding power_mult[symmetric] 
    by (simp add: ac_simps)
  finally show ?thesis .
qed


lemma det_bound_hadamard_squared: fixes A::"'a :: trivial_conjugatable_linordered_field mat"
  assumes A: "A \<in> carrier_mat n n" 
    and Bnd: "A \<in> Bounded_mat c"  
  shows "(abs (det A))^2 \<le> of_nat n ^ n * c ^ (2 * n)"
proof (cases "n > 0")
  case n: True
  from n A Bnd have "abs (A $$ (0,0)) \<le> c" by (auto simp: Bounded_mat_def)
  hence c0: "c \<ge> 0" by auto
  let ?us = "map (row A) [0 ..< n]"
  interpret gso: gram_schmidt_fs n ?us .
  have len: "length ?us = n" by simp
  have us: "set ?us \<subseteq> carrier_vec n" using A by auto
  let ?vs = "map gso.gso [0..<n]" 
  show ?thesis
  proof (cases "carrier_vec n \<subseteq> gso.span (set ?us)")
    case False
    from mat_of_rows_rows[unfolded rows_def,of A] A gram_schmidt.non_span_det_zero[OF len False us]
    have zero: "det A = 0" by auto
    show ?thesis unfolding zero using c0 by simp
  next
    case True
    with us len have basis: "gso.basis_list ?us" unfolding gso.basis_list_def by auto
    note in_dep = gso.basis_list_imp_lin_indpt_list[OF basis]
    interpret gso: gram_schmidt_fs_lin_indpt n ?us
      by (standard) (use in_dep gso.lin_indpt_list_def in auto)
    from gso.det_bound_main[OF _ A n Bnd]
    show ?thesis using A by (auto simp: rows_def)
  qed
next
  case False
  with A show ?thesis by auto 
qed

definition det_bound_hadamard :: "nat \<Rightarrow> int \<Rightarrow> int" where
  "det_bound_hadamard n c = (sqrt_int_floor ((int n * c^2)^n))" 

lemma det_bound_hadamard_altdef[code]: 
  "det_bound_hadamard n c = (if n = 1 \<or> even n then int n ^ (n div 2) * (abs c)^n else sqrt_int_floor ((int n * c^2)^n))" 
proof (cases "n = 1 \<or> even n")
  case False
  thus ?thesis unfolding det_bound_hadamard_def by auto
next
  case True
  define thesis where "thesis = ?thesis" 
  have "thesis \<longleftrightarrow> sqrt_int_floor ((int n * c^2)^n) = int n ^ (n div 2) * abs c^n" 
    using True unfolding thesis_def det_bound_hadamard_def by auto
  also have "(int n * c^2)^n = int n^n * c^(2 * n)" 
    unfolding power_mult[symmetric] power_mult_distrib by (simp add: ac_simps)
  also have "int n^n = int n ^ (2 * (n div 2))" using True by auto
  also have "\<dots> * c^(2 * n) = (int n ^ (n div 2) * c^n)^2" 
    unfolding power_mult_distrib power_mult[symmetric] by (simp add: ac_simps)
  also have "sqrt_int_floor \<dots> = int n ^ (n div 2) * \<bar>c\<bar> ^ n" 
    unfolding sqrt_int_floor of_int_power real_sqrt_abs of_int_abs[symmetric] floor_of_int
     abs_mult power_abs by simp
  finally have thesis by auto
  thus ?thesis unfolding thesis_def by auto
qed
  
lemma det_bound_hadamard: "is_det_bound det_bound_hadamard" 
  unfolding is_det_bound_def
proof (intro allI impI)
  fix A :: "int mat" and n c
  assume A: "A \<in> carrier_mat n n" and BndA: "A \<in> Bounded_mat c"  
  let ?h = rat_of_int
  let ?hA = "map_mat ?h A"
  let ?hc = "?h c" 
  from A have hA: "?hA \<in> carrier_mat n n" by auto
  from BndA have Bnd: "?hA \<in> Bounded_mat ?hc" 
    unfolding Bounded_mat_def 
    by (auto, unfold of_int_abs[symmetric] of_int_le_iff, auto)
  have sqrt: "sqrt ((real n * (real_of_int c)\<^sup>2) ^ n) \<ge> 0" 
    by simp
  from det_bound_hadamard_squared[OF hA Bnd, unfolded of_int_hom.hom_det of_int_abs[symmetric]]
  have "?h ( \<bar>det A\<bar>^2) \<le> ?h (int n ^ n * c ^ (2 * n))" by simp
  from this[unfolded of_int_le_iff]
  have "\<bar>det A\<bar>^2 \<le> int n ^ n * c ^ (2 * n)" .
  also have "\<dots> = (int n * c^2)^n" unfolding power_mult power_mult_distrib by simp
  finally have "\<bar>det A\<bar>\<^sup>2 \<le> (int n * c\<^sup>2) ^ n" by simp
  hence "sqrt_int_floor (\<bar>det A\<bar>\<^sup>2) \<le> sqrt_int_floor ((int n * c\<^sup>2) ^ n)" 
    unfolding sqrt_int_floor by (intro floor_mono real_sqrt_le_mono, linarith)
  also have "sqrt_int_floor (\<bar>det A\<bar>\<^sup>2) = \<bar>det A\<bar>" by (simp del: of_int_abs add: of_int_abs[symmetric])
  finally show "\<bar>det A\<bar> \<le> det_bound_hadamard n c" unfolding det_bound_hadamard_def by simp
qed

lemma n_pow_n_le_fact_square: "n ^ n \<le> (fact n)^2" 
proof -
  define ii where "ii (i :: nat) = (n + 1 - i)" for i
  have id: "ii ` {1..n} = {1..n}" unfolding ii_def 
  proof (auto, goal_cases)
    case (1 i)
    hence i: "i = (-) (Suc n) (ii i)" unfolding ii_def by auto
    show ?case by (subst i, rule imageI, insert 1, auto simp: ii_def)
  qed
  have "(fact n) = (\<Prod>{1..n})" 
    by (simp add: fact_prod)
  hence "(fact n)^2 = ((\<Prod>{1..n}) * (\<Prod>{1..n}))" by (auto simp: power2_eq_square)
  also have "\<dots> = ((\<Prod>{1..n}) * prod (\<lambda> i. i) (ii ` {1..n}))" 
    by (rule arg_cong[of _ _ "\<lambda> x. (_ * x)"], rule prod.cong[OF id[symmetric]], auto) 
  also have "\<dots> = ((\<Prod>{1..n}) * prod ii {1..n})" 
    by (subst prod.reindex, auto simp: ii_def inj_on_def)
  also have "\<dots> = (prod (\<lambda> i. i * ii i) {1..n})" 
    by (subst prod.distrib, auto)
  also have "\<dots> \<ge> (prod (\<lambda> i. n) {1..n})" 
  proof (intro prod_mono conjI, simp)
    fix i
    assume i: "i \<in> {1 .. n}" 
    let ?j = "ii i" 
    show "n \<le> i * ?j" 
    proof (cases "i = 1 \<or> i = n")
      case True
      thus ?thesis unfolding ii_def by auto
    next
      case False
      hence min: "min i ?j \<ge> 2" using i by (auto simp: ii_def)
      have max: "n \<le> 2 * max i ?j" using i by (auto simp: ii_def)
      also have "\<dots> \<le> min i ?j * max i ?j" using min
        by (intro mult_mono, auto)
      also have "\<dots> = i * ?j" by (cases "i < ?j", auto simp: ac_simps)
      finally show ?thesis .
    qed
  qed
  finally show ?thesis by simp
qed

lemma sqrt_int_floor_bound: "0 \<le> x \<Longrightarrow> (sqrt_int_floor x)^2 \<le> x"
  unfolding sqrt_int_floor_def
  using root_int_floor_def root_int_floor_pos_lower by auto

lemma det_bound_hadamard_improves_det_bound_fact: assumes c: "c \<ge> 0" 
  shows "det_bound_hadamard n c \<le> det_bound_fact n c" 
proof -
  have "(det_bound_hadamard n c)^2 \<le> (int n * c\<^sup>2) ^ n" unfolding det_bound_hadamard_def
    by (rule sqrt_int_floor_bound, auto)
  also have "\<dots> = int (n ^ n) * c^(2 * n)" by (simp add: power_mult power_mult_distrib)
  also have "\<dots> \<le> int ((fact n)^2) * c^(2 * n)"
    by (intro mult_right_mono, unfold of_nat_le_iff, rule n_pow_n_le_fact_square, auto)
  also have "\<dots> = (det_bound_fact n c)^2" unfolding det_bound_fact_def
    by (simp add: power_mult_distrib power_mult[symmetric] ac_simps)
  finally have "abs (det_bound_hadamard n c) \<le> abs (det_bound_fact n c)" 
    unfolding abs_le_square_iff .
  hence "det_bound_hadamard n c \<le> abs (det_bound_fact n c)" by simp
  also have "\<dots> = det_bound_fact n c" unfolding det_bound_fact_def using c by auto
  finally show ?thesis .
qed  

context
begin
private fun syl :: "int \<Rightarrow> nat \<Rightarrow> int mat" where
  "syl c 0 = mat 1 1 (\<lambda> _. c)" 
| "syl c (Suc n) = (let A = syl c n in
     four_block_mat A A (-A) A)" 

private lemma syl: assumes c: "c \<ge> 0" 
  shows "syl c n \<in> Bounded_mat c \<and> syl c n \<in> carrier_mat (2^n) (2^n)
    \<and> det (syl c n) = det_bound_hadamard (2^n) c"
proof (cases "n = 0")
  case True
  thus ?thesis using c 
    unfolding det_bound_hadamard_altdef 
    by (auto simp: Bounded_mat_def det_single)
next
  case False
  then obtain m where n: "n = Suc m" by (cases n, auto)
  show ?thesis unfolding n
  proof (induct m)
    case 0
    show ?case unfolding syl.simps Let_def using c
      apply (subst det_four_block_mat[of _ 1]; force?)
      apply (subst det_single, 
        auto simp: Bounded_mat_def scalar_prod_def det_bound_hadamard_altdef power2_eq_square)
      done
  next
    case (Suc m)
    define A where "A = syl c (Suc m)" 
    let ?FB = "four_block_mat A A (- A) A" 
    define n :: nat where "n = 2 ^ Suc m" 
    from Suc[folded A_def n_def]
    have Bnd: "A \<in> Bounded_mat c" 
      and A: "A \<in> carrier_mat n n" 
      and detA: "det A = det_bound_hadamard n c" 
      by auto
    have n2: "2 ^ Suc (Suc m) = 2 * n" unfolding n_def by auto
    show ?case unfolding syl.simps(2)[of _ "Suc m"] A_def[symmetric] Let_def n2
    proof (intro conjI)
      show "?FB \<in> carrier_mat (2 * n) (2 * n)" using A by auto
      show "?FB \<in> Bounded_mat c" using Bnd A unfolding Bounded_mat_elements_mat
        by (subst elements_four_block_mat_id, auto)
      have ev: "even n" and sum: "n div 2 + n div 2 = n" unfolding n_def by auto
      have n2: "n * 2 = n + n" by simp
      have "det ?FB = det (A * A - A * - A)"
        by (rule det_four_block_mat[OF A A _ A], insert A, auto)
      also have "A * A - A * - A = A * A + A * A" using A by auto
      also have "\<dots> = 2 \<cdot>\<^sub>m (A * A)" using A by auto
      also have "det \<dots> = 2^n * det (A * A)"
        by (subst det_smult, insert A, auto)
      also have "det (A * A) = det A * det A" by (rule det_mult[OF A A])
      also have "2^n * \<dots> = det_bound_hadamard (2 * n) c" unfolding detA
        unfolding det_bound_hadamard_altdef by (simp add: ev ac_simps power_add[symmetric] sum n2)
      finally show "det ?FB = det_bound_hadamard (2 * n) c" .
    qed
  qed
qed

lemma det_bound_hadamard_tight: 
    assumes c: "c \<ge> 0" 
      and "n = 2^m" 
    shows "\<exists> A. A \<in> carrier_mat n n \<and> A \<in> Bounded_mat c \<and> det A = det_bound_hadamard n c" 
  by (rule exI[of _ "syl c m"], insert syl[OF c, of m, folded assms(2)], auto)
end

lemma Ints_matE: assumes "A \<in> \<int>\<^sub>m" 
  shows "\<exists> B. A = map_mat of_int B" 
proof -
  have "\<forall> ij. \<exists> x. fst ij < dim_row A \<longrightarrow> snd ij < dim_col A \<longrightarrow> A $$ ij = of_int x" 
    using assms unfolding Ints_mat_def Ints_def by auto
  from choice[OF this] obtain f where 
    f: "\<forall> i j. i < dim_row A \<longrightarrow> j < dim_col A \<longrightarrow> A $$ (i,j) = of_int (f (i,j))" 
    by auto
  show ?thesis
    by (intro exI[of _ "mat (dim_row A) (dim_col A) f"] eq_matI, insert f, auto)
qed
  
lemma is_det_bound_of_int: fixes A :: "'a :: linordered_idom mat" 
  assumes db: "is_det_bound db" 
  and A: "A \<in> carrier_mat n n" 
  and "A \<in> \<int>\<^sub>m \<inter> Bounded_mat (of_int bnd)" 
shows "abs (det A) \<le> of_int (db n bnd)" 
proof -
  from assms have "A \<in> \<int>\<^sub>m" by auto
  from Ints_matE[OF this] obtain B where
    AB: "A = map_mat of_int B" by auto
  from assms have "A \<in> Bounded_mat (of_int bnd)" by auto
  hence "B \<in> Bounded_mat bnd" unfolding AB Bounded_mat_elements_mat 
    by (auto simp flip: of_int_abs)
  from db[unfolded is_det_bound_def, rule_format, OF _ this, of n] AB A
  have "\<bar>det B\<bar> \<le> db n bnd" by auto
  thus ?thesis unfolding AB of_int_hom.hom_det 
    by (simp flip: of_int_abs)
qed
  


lemma minus_in_Bounded_vec[simp]:
  "(-x) \<in> Bounded_vec b \<longleftrightarrow> x \<in> Bounded_vec b"
  unfolding Bounded_vec_def by auto

lemma sum_in_Bounded_vecI[intro]: assumes
  xB: "x \<in> Bounded_vec B1" and
  yB: "y \<in> Bounded_vec B2" and
  x: "x \<in> carrier_vec n" and
  y: "y \<in> carrier_vec n"
shows "x + y \<in> Bounded_vec (B1 + B2)"
proof -
  from x y have id: "dim_vec (x + y) = n" by auto
  show ?thesis unfolding Bounded_vec_def mem_Collect_eq id
  proof (intro allI impI)
    fix i
    assume i: "i < n"
    with x y xB yB have *: "abs (x $ i) \<le> B1" "abs (y $ i) \<le> B2"
      unfolding Bounded_vec_def by auto
    thus "\<bar>(x + y) $ i\<bar> \<le> B1 + B2" using i x y by simp
  qed
qed

lemma (in gram_schmidt) lincomb_card_bound: assumes XBnd: "X \<subseteq> Bounded_vec Bnd"
  and X: "X \<subseteq> carrier_vec n"
  and Bnd: "Bnd \<ge> 0"
  and c: "\<And> x. x \<in> X \<Longrightarrow> abs (c x) \<le> 1"
  and card: "card X \<le> k"
shows "lincomb c X \<in> Bounded_vec (of_nat k * Bnd)"
proof -
  from X have dim: "dim_vec (lincomb c X) = n" by auto
  show ?thesis unfolding Bounded_vec_def mem_Collect_eq dim
  proof (intro allI impI)
    fix i
    assume i: "i < n"
    have "abs (lincomb c X $ i) = abs (\<Sum>x\<in>X. c x * x $ i)"
      by (subst lincomb_index[OF i X], auto)
    also have "\<dots> \<le> (\<Sum>x\<in>X. abs (c x * x $ i))" by auto
    also have "\<dots> = (\<Sum>x\<in>X. abs (c x) * abs (x $ i))" by (auto simp: abs_mult)
    also have "\<dots> \<le> (\<Sum>x\<in>X. 1 * abs (x $ i))"
      by (rule sum_mono[OF mult_right_mono], insert c, auto)
    also have "\<dots> = (\<Sum>x\<in>X. abs (x $ i))" by simp
    also have "\<dots> \<le> (\<Sum>x\<in>X. Bnd)"
      by (rule sum_mono, insert i XBnd[unfolded Bounded_vec_def] X, force)
    also have "\<dots> = of_nat (card X) * Bnd" by simp
    also have "\<dots> \<le> of_nat k * Bnd"
      by (rule mult_right_mono[OF _ Bnd], insert card, auto)
    finally show "abs (lincomb c X $ i) \<le> of_nat k * Bnd" by auto
  qed
qed

lemma bounded_vecset_sum:
  assumes Acarr: "A \<subseteq> carrier_vec n"
    and Bcarr: "B \<subseteq> carrier_vec n"
    and sum: "C = A + B"
    and Cbnd: "\<exists> bndC. C \<subseteq> Bounded_vec bndC"
  shows "A \<noteq> {} \<Longrightarrow> (\<exists> bndB. B \<subseteq> Bounded_vec bndB)"
    and "B \<noteq> {} \<Longrightarrow> (\<exists> bndA. A \<subseteq> Bounded_vec bndA)"
proof -
  {
    fix A B :: "'a vec set"
    assume Acarr: "A \<subseteq> carrier_vec n"
    assume Bcarr: "B \<subseteq> carrier_vec n"
    assume sum: "C = A + B"
    assume Ane: "A \<noteq> {}"
    have "\<exists> bndB. B \<subseteq> Bounded_vec bndB"
    proof(cases "B = {}")
      case Bne: False
      from Cbnd obtain bndC where bndC: "C \<subseteq> Bounded_vec bndC" by auto
      from Ane obtain a where aA: "a \<in> A" and acarr: "a \<in> carrier_vec n" using Acarr by auto
      let ?M = "{abs (a $ i) | i. i < n}"
      have finM: "finite ?M" by simp
      define nb where "nb = abs bndC + Max ?M"
      {
        fix b
        assume bB: "b \<in> B" and bcarr: "b \<in> carrier_vec n"
        have ab: "a + b \<in> Bounded_vec bndC" using aA bB bndC sum by auto
        {
          fix i
          assume i_lt_n: "i < n"
          hence ai_le_max: "abs(a $ i) \<le> Max ?M" using acarr finM Max_ge by blast
          hence "abs(a $ i + b $ i) \<le> abs bndC"
            using ab bcarr acarr index_add_vec(1) i_lt_n unfolding Bounded_vec_def by auto
          hence "abs(b $ i) \<le> abs bndC + abs(a $ i)" by simp
          hence "abs(b $ i) \<le> nb" using i_lt_n bcarr ai_le_max unfolding nb_def by simp
        }
        hence "b \<in> Bounded_vec nb" unfolding Bounded_vec_def using bcarr carrier_vecD by blast
      }
      hence "B \<subseteq> Bounded_vec nb" unfolding Bounded_vec_def using Bcarr by auto
      thus ?thesis by auto
    qed auto
  } note theor = this
  show "A \<noteq> {} \<Longrightarrow> (\<exists> bndB. B \<subseteq> Bounded_vec bndB)" using theor[OF Acarr Bcarr sum] by simp
  have CBA: "C = B + A" unfolding sum by (rule comm_add_vecset[OF Acarr Bcarr])
  show "B \<noteq> {} \<Longrightarrow> \<exists> bndA. A \<subseteq> Bounded_vec bndA" using theor[OF Bcarr Acarr CBA] by simp
qed

end