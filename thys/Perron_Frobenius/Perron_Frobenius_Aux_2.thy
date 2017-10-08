section \<open>Perron-Frobenius Theorem, Irreducible Matrices\<close>

subsection \<open>More Auxiliary Notions\<close>

theory Perron_Frobenius_Aux_2
imports 
  Roots_Unity
  Perron_Frobenius
  Graph_Theory.Shortest_Path
begin

lemma trancl_image: 
  "(i,j) \<in> R\<^sup>+ \<Longrightarrow> (f i, f j) \<in> (map_prod f f ` R)\<^sup>+" 
proof (induct rule: trancl_induct)
  case (step j k)
  from step(2) have "(f j, f k) \<in> map_prod f f ` R" by auto
  from step(3) this show ?case by auto
qed auto

lemma inj_trancl_image: assumes inj: "inj f" 
  shows "(f i, f j) \<in> (map_prod f f ` R)\<^sup>+ = ((i,j) \<in> R\<^sup>+)" (is "?l = ?r")
proof
  assume ?r from trancl_image[OF this] show ?l .
next
  assume ?l from trancl_image[OF this, of "the_inv f"]
  show ?r unfolding image_image prod.map_comp o_def the_inv_f_f[OF inj] by auto
qed

lemma cmod_plus_eqD: assumes "cmod (x + y) = cmod x + cmod y"
  shows "x = 0 \<or> y = 0 \<or> sgn x = sgn y"
proof (cases "x = 0 \<or> y = 0")
  case True
  thus ?thesis by auto
next
  case False
  from False have 0: "cmod x \<noteq> 0" "cmod y \<noteq> 0" by auto
  {
    assume min: "cmod y * x = - cmod x * y" 
    hence "sgn y = - sgn x" unfolding sgn_eq using 0 by (auto simp: field_simps)
    hence False
      by (smt "0"(1) False assms min mult_cancel_right norm_triangle_eq of_real_eq_iff scaleR_conv_of_real)
  } note sgn = this
  obtain rx ix where x: "x = Complex rx ix" by (cases x, auto)
  obtain ry iy where y: "y = Complex ry iy" by (cases y, auto)
  from arg_cong[OF assms, of "\<lambda> x. x^2", unfolded cmod_power2]
  have "(rx + ry)^2 + (ix + iy)^2 = (cmod x + cmod y)^2" 
    by (simp add: x y)
  also have "\<dots> = (cmod x)^2 + (cmod y)^2 + 2 * cmod (x * y)"
    by (simp add: field_simps power2_eq_square norm_mult)
  also have "\<dots> = rx^2 + ix^2 + ry^2 + iy^2 + 2 * cmod (x * y)" 
    unfolding cmod_power2 x y by (simp add: cmod_power2)
  also have "(rx + ry)^2 + (ix + iy)^2 = rx^2 + ry^2 + 2 * rx * ry + ix^2 + iy^2 + 2 * ix * iy" 
    by (simp add: field_simps power2_eq_square norm_mult)
  finally have 1: "rx * ry + ix * iy = cmod (x * y)" by simp
  hence pos: "rx * ry + ix * iy \<ge> 0" by auto
  from arg_cong[OF 1, of "\<lambda> x. x^2", unfolded cmod_power2, unfolded x y]
  have "(ix * ry - iy * rx)^2 = 0" 
    by (simp add: field_simps power2_eq_square)
  hence 2: "ix * ry = iy * rx" by simp
  have 3: "sgn x = sgn y \<longleftrightarrow> cmod y * x = cmod x * y" using 0 by (auto simp: field_simps sgn_eq)
  also have "\<dots> \<longleftrightarrow> (cmod y * x)^2 = (cmod x * y)^2" using sgn unfolding power2_eq_iff by auto
  also have "\<dots> \<longleftrightarrow> (cmod y)^2 * x^2 = (cmod x)^2 * y^2" 
    by (simp add: field_simps power2_eq_square)
  also have "\<dots> \<longleftrightarrow> (ry^2 + iy^2) * x^2 = (rx^2 + ix^2) * y^2" 
    unfolding cmod_power2 x y by simp
  also have "\<dots> \<longleftrightarrow> (iy * rx)^2 = (ix * ry)^2 \<and>
     ix * iy^2 * rx + ix * rx * ry^2 =  ix^2 * iy * ry + iy * rx^2 * ry" 
    unfolding x y by (auto simp: field_simps power2_eq_square complex_mult 
      complex_add complex_of_real_mult_Complex)
  also have "\<dots> \<longleftrightarrow> ix * iy^2 * rx + ix * rx * ry^2 = ix^2 * iy * ry + iy * rx^2 * ry" 
    unfolding 2 by simp
  also have "ix * iy^2 * rx + ix * rx * ry^2 = ix * iy^2 * rx + iy * rx^2 * ry" 
    using 2 by (auto simp: field_simps power2_eq_square)
  also have "ix^2 * iy * ry + iy * rx^2 * ry = ix * iy^2 * rx + iy * rx^2 * ry" 
    using 2 by (auto simp: field_simps power2_eq_square)
  finally show ?thesis by simp
qed

lemma cmod_plus_eq_exD: assumes "cmod (x + y) = cmod x + cmod y"
  shows "\<exists> n. \<forall> z \<in> {x,y}. z = n * of_real (cmod z)"
proof -
  have z: "z = sgn z * cmod z" for z unfolding sgn_eq by (cases "z = 0", auto)
  from cmod_plus_eqD[OF assms]
  have *: "x = 0 \<or> y = 0 \<or> sgn x = sgn y" .
  {
    assume "x = 0" 
    hence ?thesis by (intro exI[of _ "sgn y"], insert z, auto)
  }
  moreover
  {
    assume "y = 0" 
    hence ?thesis by (intro exI[of _ "sgn x"], insert z, auto)
  }
  moreover
  {
    assume "sgn x = sgn y"  
    hence ?thesis by (intro exI[of _ "sgn y"], insert z[of x] z[of y], auto)
  }
  ultimately show ?thesis using * by blast
qed

lemma cmod_sum_eq_exD: assumes "finite I" 
  and "cmod (sum f I) = sum (\<lambda> i. cmod (f i)) I" 
shows "\<exists> n. \<forall> z \<in> f ` I. z = n * of_real (cmod z)" 
  using assms
proof (induct I rule: finite_induct)
  case (insert i I)
  have id0: "sum f (insert i I) = f i + sum f I" for f
    by (rule sum.insert, insert insert, auto)
  from insert(4)[unfolded id0] 
  have id1: "cmod (f i + sum f I) = cmod (f i) + (\<Sum>i\<in>I. cmod (f i))" by auto
  note this[symmetric]
  also have "cmod (f i + sum f I) \<le> cmod (f i) + cmod (sum f I)" by (rule norm_triangle_ineq)
  finally have "(\<Sum>i\<in>I. cmod (f i)) \<le> cmod (sum f I)" by simp
  with norm_sum[of f I] have id2: "cmod (sum f I) = (\<Sum>i\<in>I. cmod (f i))" by simp
  from insert(3)[OF id2] obtain n where n: "\<And> x. x \<in> f ` I \<Longrightarrow> x = n * of_real (cmod x)" by auto
  from cmod_plus_eq_exD[OF id1[folded id2]] obtain m where 
    m1: "f i = m * of_real (cmod (f i))" and
    m2: "sum f I = m * of_real (cmod (sum f I))" 
    by auto
  have *: "sum f I = m * (\<Sum>i\<in>I. of_real (cmod (f i)))" 
    unfolding m2[unfolded id2] by simp
  have **: "sum f I = n * (\<Sum>i\<in>I. of_real (cmod (f i)))" 
    unfolding sum_distrib_left
    by (rule sum.cong, insert n, auto)
  have "m * cmod (sum f I) = n * cmod (sum f I)" 
    using * ** unfolding id2 by auto
  hence "m = n \<or> sum f I = 0" by auto
  thus ?case
  proof
    assume "m = n" 
    with n m1 m2 show ?case by (intro exI[of _ n], auto)
  next
    assume "sum f I = 0" 
    hence "cmod (sum f I) = 0" by simp
    from this[unfolded id2] insert(1) have I: "x \<in> f ` I \<Longrightarrow> x = m * of_real (cmod x)" for x
      by (subst (asm) sum_nonneg_eq_0_iff, auto)
    show ?case by (intro exI[of _ m], insert m1 I, auto)
  qed
qed auto
  

lemma matrix_add_rdistrib: "((B + C) ** A) = (B ** A) + (C ** A)"
  by (vector matrix_matrix_mult_def sum.distrib[symmetric] field_simps)

lemma norm_smult: "norm ((a :: real) *s x) = abs a * norm x" 
  unfolding norm_vec_def 
  by (metis norm_scaleR norm_vec_def scalar_mult_eq_scaleR)

lemma (in linorder_topology) tendsto_Min: assumes I: "I \<noteq> {}" and fin: "finite I"
  shows "(\<And>i. i \<in> I \<Longrightarrow> (f i \<longlongrightarrow> a i) F) \<Longrightarrow> ((\<lambda>x. Min ((\<lambda> i. f i x) ` I)) \<longlongrightarrow> 
    (Min (a ` I) :: 'a)) F" 
  using fin I
proof (induct rule: finite_induct)
  case (insert i I)
  hence i: "(f i \<longlongrightarrow> a i) F" by auto
  show ?case
  proof (cases "I = {}")
    case True
    show ?thesis unfolding True using i by auto
  next
    case False
    have *: "Min (a ` insert i I) = min (a i) (Min (a ` I))" using False insert(1) by auto
    have **: "(\<lambda>x. Min ((\<lambda>i. f i x) ` insert i I)) = (\<lambda>x. min (f i x) (Min ((\<lambda>i. f i x) ` I)))" 
      using False insert(1) by auto
    have IH: "((\<lambda>x. Min ((\<lambda>i. f i x) ` I)) \<longlongrightarrow> Min (a ` I)) F" 
      using insert(3)[OF insert(4) False] by auto
    show ?thesis unfolding * **
      by (auto intro!: tendsto_min i IH)
  qed
qed simp

lemma tendsto_mat_mult [tendsto_intros]: 
  "(f \<longlongrightarrow> a) F \<Longrightarrow> (g \<longlongrightarrow> b) F \<Longrightarrow> ((\<lambda>x. f x ** g x) \<longlongrightarrow> a ** b) F" 
  for f :: "'a \<Rightarrow> 'b :: {semiring_1, real_normed_algebra} ^ 'n1 ^ 'n2" 
  unfolding matrix_matrix_mult_def[abs_def] by (auto intro!: tendsto_intros)

lemma tendsto_matpower [tendsto_intros]: "(f \<longlongrightarrow> a) F \<Longrightarrow> ((\<lambda>x. matpow (f x) n) \<longlongrightarrow> matpow a n) F"
  for f :: "'a \<Rightarrow> 'b :: {semiring_1, real_normed_algebra} ^ 'n ^ 'n"
  by (induct n, simp_all add: tendsto_mat_mult)

lemma continuous_matpow: "continuous_on R (\<lambda> A :: 'a :: {semiring_1, real_normed_algebra_1} ^ 'n ^ 'n. matpow A n)"
  unfolding continuous_on_def by (auto intro!: tendsto_intros)

lemma vector_smult_distrib: "(A *v ((a :: 'a :: comm_ring_1) *s x)) = a *s ((A *v x))" 
  unfolding matrix_vector_mult_def vector_scalar_mult_def
  by (simp add: ac_simps sum_distrib_left)  


lemma (in fin_digraph) length_apath_less:
  assumes "apath u p v"
  shows "length p < card (verts G)"
proof -
  have "length p < length (awalk_verts u p)" unfolding awalk_verts_conv
    by (auto simp: awalk_verts_conv)
  also have "length (awalk_verts u p) = card (set (awalk_verts u p))"
    using `apath u p v` by (auto simp: apath_def distinct_card)
  also have "\<dots> \<le> card (verts G)"
    using `apath u p v` unfolding apath_def awalk_conv
    by (auto intro: card_mono)
  finally show ?thesis .
qed

instance real :: ordered_semiring_strict
  by (intro_classes, auto)

lemma (in inj_comm_ring_hom) eigen_vector_hom: 
  "eigen_vector (map_matrix hom A) (map_vector hom v) (hom x) = eigen_vector A v x"
  unfolding eigen_vector_def matrix_vector_mult_hom vector_smult_hom map_vector_0 map_vector_inj 
  by auto

lemma pderiv_sum: "pderiv (sum f I) = sum (\<lambda> i. (pderiv (f i))) I" 
  by (induct I rule: infinite_finite_induct, auto simp: pderiv_add)

lemma degree_det_le: assumes "\<And> i j. i < n \<Longrightarrow> j < n \<Longrightarrow> degree (A $$ (i,j)) \<le> k"
  and A: "A \<in> carrier_mat n n" 
shows "degree (Determinant.det A) \<le> k * n" 
proof -
  {
    fix p
    assume p: "p permutes {0..<n}"
    have "(\<Sum>x = 0..<n. degree (A $$ (x, p x))) \<le> (\<Sum>x = 0..<n. k)"     
      by (rule sum_mono[OF assms(1)], insert p, auto)
    also have "\<dots> = k * n" unfolding sum_constant by simp
    also note calculation 
  } note * = this
  show ?thesis unfolding det_def'[OF A]
    by (rule degree_sum_le, insert *, auto simp: finite_permutations intro!: order.trans[OF degree_prod_sum_le]) try
qed

lemma pderiv_char_poly: fixes A :: "'a :: idom mat" 
  assumes A: "A \<in> carrier_mat n n" 
  shows "pderiv (char_poly A) = (\<Sum>i < n. char_poly (mat_delete A i i))"
proof -
  let ?det = Determinant.det
  let ?m = "map_mat (\<lambda>a. [:- a:])" 
  let ?lam = "[:0, 1:] \<cdot>\<^sub>m 1\<^sub>m n :: 'a poly mat" 
  from A have id: "dim_row A = n" by auto  

  define mA where "mA = ?m A"
  define lam where "lam = ?lam" 
  let ?sum = "lam + mA" 
  define Sum where "Sum = ?sum" 
  have mA: "mA \<in> carrier_mat n n" and 
    lam: "lam \<in> carrier_mat n n" and
    Sum: "Sum \<in> carrier_mat n n" 
    using A unfolding mA_def Sum_def lam_def by auto
  let ?P = "{p. p permutes {0..<n}}" 
  let ?e = "\<lambda> p. (\<Prod>i = 0..<n. Sum $$ (i, p i))" 
  let ?f = "\<lambda> p a. signof p * (\<Prod>i\<in>{0..<n} - {a}. Sum $$ (i, p i)) * pderiv (Sum $$ (a, p a))" 
  let ?g = "\<lambda> p a. signof p * (\<Prod>i\<in>{0..<n} - {a}. Sum $$ (i, p i))" 
  define f where "f = ?f" 
  define g where "g = ?g" 
  {
    fix p
    assume p: "p permutes {0 ..< n}" 
    have "pderiv (signof p :: 'a poly) = 0" unfolding signof_def by (simp add: pderiv_minus) 
    hence "pderiv (signof p * ?e p) = signof p * pderiv (\<Prod>i = 0..<n. Sum $$ (i, p i))" 
      unfolding pderiv_mult by auto
    also have "signof p * pderiv (\<Prod>i = 0..<n. Sum $$ (i, p i)) = 
       (\<Sum>a = 0..<n. f p a)" 
      unfolding pderiv_prod sum_distrib_left f_def by (simp add: ac_simps)
    also note calculation
  } note to_f = this
  {
    fix a
    assume a: "a < n" 
    have Psplit: "?P = {p. p permutes {0..<n} \<and> p a = a} \<union> (?P - {p. p a = a})" (is "_ = ?Pa \<union> ?Pz") by auto 
    {
      fix p
      assume p: "p permutes {0 ..< n}" "p a \<noteq> a"
      hence "pderiv (Sum $$ (a, p a)) = 0" unfolding Sum_def lam_def mA_def using a p A by auto
      hence "f p a = 0" unfolding f_def by auto
    } note 0 = this
    {
      fix p
      assume p: "p permutes {0 ..< n}" "p a = a"
      hence "pderiv (Sum $$ (a, p a)) = 1" unfolding Sum_def lam_def mA_def using a p A
        by (auto simp: pderiv_pCons)
      hence "f p a = g p a" unfolding f_def g_def by auto
    } note fg = this
    let ?n = "n - 1" 
    from a have n: "Suc ?n = n" by simp
    let ?B = "[:0, 1:] \<cdot>\<^sub>m 1\<^sub>m ?n + ?m (mat_delete A a a)" 
    have B: "?B \<in> carrier_mat ?n ?n" using A by auto
    have "sum (\<lambda> p. f p a) ?P = sum (\<lambda> p. f p a) ?Pa + sum (\<lambda> p. f p a) ?Pz" 
      by (subst sum_union_disjoint'[OF _ _ _ Psplit[symmetric]], auto simp: finite_permutations)
    also have "\<dots> = sum (\<lambda> p. f p a) ?Pa" 
      by (subst (2) sum.neutral, insert 0, auto)
    also have "\<dots> = sum (\<lambda> p. g p a) ?Pa" 
      by (rule sum.cong, auto simp: fg)
    also have "\<dots> = ?det ?B"
      unfolding det_def'[OF B] 
      unfolding permutation_fix[of a ?n a, unfolded n, OF a a]
      unfolding sum.reindex[OF permutation_insert_inj_on[of a ?n a, unfolded n, OF a a]] o_def
    proof (rule sum.cong[OF refl])
      fix p
      let ?Q = "{p. p permutes {0..<?n}}" 
      assume "p \<in> ?Q"      
      hence p: "p permutes {0 ..< ?n}" by auto
      let ?p = "permutation_insert a a p"
      let ?i = "insert_index a" 
      have sign: "signof ?p = signof p" 
        unfolding signof_permutation_insert[OF p, unfolded n, OF a a] by simp
      show "g (permutation_insert a a p) a = signof p * (\<Prod>i = 0..<?n. ?B $$ (i, p i))" 
        unfolding g_def sign
      proof (rule arg_cong[of _ _ "op * (signof p)"])
        have "(\<Prod>i\<in>{0..<n} - {a}. Sum $$ (i, ?p i)) = 
           prod (op $$ Sum) ((\<lambda>x. (x, ?p x)) ` ({0..<n} - {a}))"
          unfolding prod.reindex[OF inj_on_convol_ident, of _ ?p] o_def ..
        also have "\<dots> = (\<Prod> ii \<in> {(i', ?p i') |i'. i' \<in> {0..<n} - {a}}. Sum $$ ii)" 
          by (rule prod.cong, auto)
        also have "\<dots> = prod (op $$ Sum) ((\<lambda> i. (?i i, ?i (p i))) ` {0 ..< ?n})" 
          unfolding Determinant.foo[of a ?n a, unfolded n, OF a a p]
          by (rule arg_cong[of _ _ "prod _"], auto) 
        also have "\<dots> = prod (\<lambda> i. Sum $$ (?i i, ?i (p i))) {0 ..< ?n}"
        proof (subst prod.reindex, unfold o_def)
          show "inj_on (\<lambda>i. (?i i, ?i (p i))) {0..<?n}" using insert_index_inj_on[of a]
            by (auto simp: inj_on_def)
        qed simp
        also have "\<dots> = (\<Prod>i = 0..<?n. ?B $$ (i, p i))" 
        proof (rule prod.cong[OF refl], rename_tac i)
          fix j
          assume "j \<in> {0 ..< ?n}"
          hence j: "j < ?n" by auto
          with p have pj: "p j < ?n" by auto
          from j pj have jj: "?i j < n" "?i (p j) < n" by (auto simp: insert_index_def)
          let ?jj = "(?i j, ?i (p j))" 
          note index_adj = mat_delete_index[of _ ?n, unfolded n, OF _ a a j pj]
          have "Sum $$ ?jj = lam $$ ?jj + mA $$ ?jj" unfolding Sum_def using jj A lam mA by auto
          also have "\<dots> = ?B $$ (j, p j)" 
            unfolding index_adj[OF mA] index_adj[OF lam] using j pj A
            by (simp add: mA_def lam_def mat_delete_def)
          finally show "Sum $$ ?jj = ?B $$ (j, p j)" .
        qed
        finally 
        show "(\<Prod>i\<in>{0..<n} - {a}. Sum $$ (i, ?p i)) = (\<Prod>i = 0..<?n. ?B $$ (i, p i))" .
      qed
    qed
    also have "\<dots> = char_poly (mat_delete A a a)" unfolding char_poly_def char_poly_matrix_def
      using A by simp
    also note calculation
  } note to_char_poly = this
  have "pderiv (char_poly A) = pderiv (?det Sum)" 
    unfolding char_poly_def char_poly_matrix_def id lam_def mA_def Sum_def by auto
  also have "\<dots> = sum (\<lambda> p. pderiv (signof p * ?e p)) ?P" unfolding det_def'[OF Sum]
    pderiv_sum by (rule sum.cong, auto)
  also have "\<dots> = sum (\<lambda> p. (\<Sum>a = 0..<n. f p a)) ?P" 
    by (rule sum.cong[OF refl], subst to_f, auto)
  also have "\<dots> = (\<Sum>a = 0..<n. sum (\<lambda> p. f p a) ?P)" 
    by (rule sum.swap) 
  also have "\<dots> = (\<Sum>a <n. char_poly (mat_delete A a a))" 
    by (rule sum.cong, auto simp: to_char_poly)
  finally show ?thesis .
qed    

lemma char_poly_0_column: fixes A :: "'a :: idom mat" 
  assumes 0: "\<And> j. j < n \<Longrightarrow> A $$ (j,i) = 0" 
  and A: "A \<in> carrier_mat n n" 
  and i: "i < n"
shows "char_poly A = monom 1 1 * char_poly (mat_delete A i i)" 
proof -
  let ?det = Determinant.det
  let ?n = "n - 1" 
  let ?A = "mat_delete A i i" 
  let ?sum = "[:0, 1:] \<cdot>\<^sub>m 1\<^sub>m n + map_mat (\<lambda>a. [:- a:]) A" 
  define Sum where "Sum = ?sum" 
  let ?f = "\<lambda> j. Sum $$ (j, i) * cofactor Sum j i" 
  have Sum: "Sum \<in> carrier_mat n n" using A unfolding Sum_def by auto
  from A have id: "dim_row A = n" by auto  
  have "char_poly A = (\<Sum>j<n. ?f j)" 
    unfolding char_poly_def[of A] char_poly_matrix_def 
    using laplace_expansion_column[OF Sum i] unfolding Sum_def using A by simp
  also have "\<dots> = ?f i + sum ?f ({..<n} - {i})" 
    by (rule sum.remove[of _ i], insert i, auto)
  also have "\<dots> = ?f i" 
  proof (subst sum.neutral, intro ballI)
    fix j
    assume "j \<in> {..<n} - {i}" 
    hence j: "j < n" and ji: "j \<noteq> i" by auto
    show "?f j = 0" unfolding Sum_def using ji j i A 0[OF j] by simp
  qed simp
  also have "?f i = [:0, 1:] * (cofactor Sum i i)" 
    unfolding Sum_def using i A 0[OF i] by simp
  also have "cofactor Sum i i = ?det (mat_delete Sum i i)" 
    unfolding cofactor_def by simp
  also have "\<dots> = char_poly ?A" 
    unfolding char_poly_def char_poly_matrix_def Sum_def
  proof (rule arg_cong[of _ _ ?det])
    show "mat_delete ?sum i i = [:0, 1:] \<cdot>\<^sub>m 1\<^sub>m (dim_row ?A) + map_mat (\<lambda>a. [:- a:]) ?A"
      using i A by (auto simp: mat_delete_def)
  qed
  also have "[:0, 1:] = (monom 1 1 :: 'a poly)" by (rule x_as_monom)
  finally show ?thesis .
qed

definition mat_erase :: "'a :: zero mat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a mat" where
  "mat_erase A i j = Matrix.mat (dim_row A) (dim_col A) 
     (\<lambda> (i',j'). if i' = i \<or> j' = j then 0 else A $$ (i',j'))"  

lemma mat_erase_carrier[simp]: "(mat_erase A i j) \<in> carrier_mat nr nc \<longleftrightarrow> A \<in> carrier_mat nr nc" 
  unfolding mat_erase_def carrier_mat_def by simp

lemma pderiv_char_poly_mat_erase: fixes A :: "'a :: idom mat" 
  assumes A: "A \<in> carrier_mat n n" 
  shows "monom 1 1 * pderiv (char_poly A) = (\<Sum>i < n. char_poly (mat_erase A i i))"
proof -
  show ?thesis unfolding pderiv_char_poly[OF A] sum_distrib_left
  proof (rule sum.cong[OF refl])
    fix i
    assume "i \<in> {..<n}" 
    hence i: "i < n" by simp
    have mA: "mat_erase A i i \<in> carrier_mat n n" using A by simp
    show "monom 1 1 * char_poly (mat_delete A i i) = char_poly (mat_erase A i i)"
      by (subst char_poly_0_column[OF _ mA i], (insert i A, force simp: mat_erase_def),
      rule arg_cong[of _ _ "\<lambda> x. f * char_poly x" for f],
      auto simp: mat_delete_def mat_erase_def)
  qed
qed

definition erase_mat :: "'a :: zero ^ 'nc ^ 'nr \<Rightarrow> 'nr \<Rightarrow> 'nc \<Rightarrow> 'a ^ 'nc ^ 'nr" 
  where "erase_mat A i j = (\<chi> i'. \<chi>  j'. if i' = i \<or> j' = j then 0 else A $ i' $ j')" 

definition sum_UNIV_type :: "('n :: finite \<Rightarrow> 'a :: comm_monoid_add) \<Rightarrow> 'n itself \<Rightarrow> 'a" where
  "sum_UNIV_type f _ = sum f UNIV" 

definition sum_UNIV_set :: "(nat \<Rightarrow> 'a :: comm_monoid_add) \<Rightarrow> nat \<Rightarrow> 'a" where
  "sum_UNIV_set f n = sum f {..<n}" 

definition HMA_T :: "nat \<Rightarrow> 'n :: finite itself \<Rightarrow> bool" where
  "HMA_T n _ = (n = CARD('n))" 

context
  includes lifting_syntax
begin
lemma HMA_M_erase_mat[transfer_rule]: "(HMA_M ===> HMA_I ===> HMA_I ===> HMA_M) mat_erase erase_mat" 
  unfolding mat_erase_def[abs_def] erase_mat_def[abs_def]
  by (auto simp: HMA_M_def HMA_I_def from_hma\<^sub>m_def to_nat_from_nat_id intro!: eq_matI)

lemma HMA_M_sum_UNIV[transfer_rule]: 
  "((HMA_I ===> op =) ===> HMA_T ===> op =) sum_UNIV_set sum_UNIV_type"
  unfolding rel_fun_def 
proof (clarify, rename_tac f fT n nT)
  fix f and fT :: "'b \<Rightarrow> 'a" and n and nT :: "'b itself" 
  assume f: "\<forall>x y. HMA_I x y \<longrightarrow> f x = fT y"
    and n: "HMA_T n nT" 
  let ?f = "from_nat :: nat \<Rightarrow> 'b" 
  let ?t = "to_nat :: 'b \<Rightarrow> nat" 
  from n[unfolded HMA_T_def] have n: "n = CARD('b)" .
  from to_nat_from_nat_id[where 'a = 'b, folded n]
  have tf: "i < n \<Longrightarrow> ?t (?f i) = i" for i by auto
  have "sum_UNIV_set f n = sum f (?t ` ?f ` {..<n})" 
    unfolding sum_UNIV_set_def
    by (rule arg_cong[of _ _ "sum f"], insert tf, force)
  also have "\<dots> = sum (f \<circ> ?t) (?f ` {..<n})" 
    by (rule sum.reindex, insert tf n, auto simp: inj_on_def)
  also have "?f ` {..<n} = UNIV" 
    using range_to_nat[where 'a = 'b, folded n] by force
  also have "sum (f \<circ> ?t) UNIV = sum fT UNIV" 
  proof (rule sum.cong[OF refl])
    fix i :: 'b
    show "(f \<circ> ?t) i = fT i" unfolding o_def 
      by (rule f[rule_format], auto simp: HMA_I_def)
  qed
  also have "\<dots> = sum_UNIV_type fT nT" 
    unfolding sum_UNIV_type_def ..
  finally show "sum_UNIV_set f n = sum_UNIV_type fT nT" .
qed
end

lemma pderiv_char_poly_erase_mat: fixes A :: "'a :: idom ^ 'n ^ 'n" 
  shows "monom 1 1 * pderiv (charpoly A) = sum (\<lambda> i. charpoly (erase_mat A i i)) UNIV" 
proof -
  let ?A = "from_hma\<^sub>m A" 
  let ?n = "CARD('n)" 
  have tA[transfer_rule]: "HMA_M ?A A" unfolding HMA_M_def by simp
  have tN[transfer_rule]: "HMA_T ?n TYPE('n)" unfolding HMA_T_def by simp
  have A: "?A \<in> carrier_mat ?n ?n" unfolding from_hma\<^sub>m_def by auto
  have id: "sum (\<lambda> i. charpoly (erase_mat A i i)) UNIV = 
    sum_UNIV_type (\<lambda> i. charpoly (erase_mat A i i)) TYPE('n)"
    unfolding sum_UNIV_type_def ..
  show ?thesis unfolding id
    by (transfer, insert pderiv_char_poly_mat_erase[OF A], simp add: sum_UNIV_set_def)
qed

lemma degree_monic_charpoly: fixes A :: "'a :: comm_ring_1 ^ 'n ^ 'n" 
  shows "degree (charpoly A) = CARD('n) \<and> monic (charpoly A)" 
proof (transfer, goal_cases)
  case 1
  from degree_monic_char_poly[OF 1] show ?case by auto
qed

lemma poly_pinfty_ge:
  fixes p :: "real poly"
  assumes "lead_coeff p > 0" "degree p \<noteq> 0" 
  shows "\<exists>n. \<forall> x \<ge> n. poly p x \<ge> b"
proof -
  let ?p = "p - [:b - lead_coeff p :]" 
  have id: "lead_coeff ?p = lead_coeff p" using assms(2)
    by (cases p, auto)
  with assms(1) have "lead_coeff ?p > 0" by auto
  from poly_pinfty_gt_lc[OF this, unfolded id] obtain n
    where "\<And> x. x \<ge> n \<Longrightarrow> 0 \<le> poly p x - b" by auto
  thus ?thesis by auto
qed

lemma poly_tendsto_pinfty:  fixes p :: "real poly"
  assumes "lead_coeff p > 0" "degree p \<noteq> 0" 
  shows "poly p \<longlonglongrightarrow> \<infinity>" 
  unfolding Lim_PInfty
proof 
  fix b
  show "\<exists>N. \<forall>n\<ge>N. ereal b \<le> ereal (poly p (real n))" 
    unfolding ereal_less_eq using poly_pinfty_ge[OF assms, of b]
    by (meson Extended_Nonnegative_Real.of_nat_le_iff order_trans real_arch_simple)
qed

definition diagvector :: "('n \<Rightarrow> 'a :: semiring_0) \<Rightarrow> 'a ^ 'n ^ 'n" where
  "diagvector x = (\<chi> i. \<chi> j. if i = j then x i else 0)" 

lemma diagvector_mult_vector[simp]: "diagvector x *v y = (\<chi> i. x i * y $ i)" 
  unfolding diagvector_def matrix_vector_mult_def vec_eq_iff vec_lambda_beta
proof (rule, goal_cases)
  case (1 i)
  show ?case by (subst sum.remove[of _ i], auto)
qed

lemma diagvector_mult_left: "diagvector x ** A = (\<chi> i j. x i * A $ i $ j)" (is "?A = ?B") 
  unfolding vec_eq_iff
proof (intro allI)
  fix i j
  show "?A $ i $ j = ?B $ i $ j" 
    unfolding map_vector_def diagvector_def matrix_matrix_mult_def vec_lambda_beta
    by (subst sum.remove[of _ i], auto)
qed

lemma diagvector_mult_right: "A ** diagvector x = (\<chi> i j. A $ i $ j * x j)" (is "?A = ?B") 
  unfolding vec_eq_iff
proof (intro allI)
  fix i j
  show "?A $ i $ j = ?B $ i $ j" 
    unfolding map_vector_def diagvector_def matrix_matrix_mult_def vec_lambda_beta
    by (subst sum.remove[of _ j], auto)
qed

lemma diagvector_mult[simp]: "diagvector x ** diagvector y = diagvector (\<lambda> i. x i * y i)" 
  unfolding diagvector_mult_left unfolding diagvector_def by (auto simp: vec_eq_iff)

lemma diagvector_const[simp]: "diagvector (\<lambda> x. k) = mat k" 
  unfolding diagvector_def mat_def by auto

lemma diagvector_eq_mat: "diagvector x = mat a \<longleftrightarrow> x = (\<lambda> x. a)" 
  unfolding diagvector_def mat_def by (auto simp: vec_eq_iff)

lemma cmod_eq_Re: assumes "cmod x = Re x"
  shows "of_real (Re x) = x" 
proof (cases "Im x = 0")
  case False
  hence "(cmod x)^2 \<noteq> (Re x)^2" unfolding norm_complex_def by simp
  from this[unfolded assms] show ?thesis by auto
qed (cases x, auto simp: norm_complex_def complex_of_real_def)

hide_const(open) Coset.order

lemma order_linear_power: "order a ([: b, 1:]^n) = (if b = -a then n else 0)" 
proof (cases n)
  case (Suc m)
  show ?thesis unfolding Suc order_linear_power' by simp
qed simp
  
lemma jordan_nf_order: assumes "jordan_nf A n_as" 
  shows "order a (char_poly A)  = sum_list (map fst (filter (\<lambda> na. snd na = a) n_as))" 
proof - 
  let ?p = "\<lambda> n_as. (\<Prod>(n, a)\<leftarrow>n_as. [:- a, 1:] ^ n)" 
  let ?s = "\<lambda> n_as. sum_list (map fst (filter (\<lambda> na. snd na = a) n_as))" 
  from jordan_nf_char_poly[OF assms]
  have "order a (char_poly A) = order a (?p n_as)" by simp
  also have "\<dots> = ?s n_as" 
  proof (induct n_as)
    case (Cons nb n_as)
    obtain n b where nb: "nb = (n,b)" by force
    have "order a (?p (nb # n_as)) = order a ([: -b, 1:] ^ n * ?p n_as)" unfolding nb by simp
    also have "\<dots> = order a ([: -b, 1:] ^ n) + order a (?p n_as)" 
      by (rule order_mult, auto simp: prod_list_zero_iff)
    also have "\<dots> = (if a = b then n else 0) + ?s n_as" unfolding Cons order_linear_power by simp
    also have "\<dots> = ?s (nb # n_as)" unfolding nb by auto
    finally show ?case .
  qed simp
  finally show ?thesis .
qed

definition mat_diag :: "nat \<Rightarrow> (nat \<Rightarrow> 'a :: zero) \<Rightarrow> 'a mat" where
  "mat_diag n f = Matrix.mat n n (\<lambda> (i,j). if i = j then f j else 0)" 

lemma mat_diag_dim[simp]: "mat_diag n f \<in> carrier_mat n n" 
  unfolding mat_diag_def by auto

lemma mat_diag_mult_left: assumes A: "A \<in> carrier_mat n nr" 
  shows "mat_diag n f * A = Matrix.mat n nr (\<lambda> (i,j). f i * A $$ (i,j))" 
proof (rule eq_matI, insert A, auto simp: mat_diag_def scalar_prod_def, goal_cases)
  case (1 i j)
  thus ?case by (subst sum.remove[of _ i], auto)
qed

lemma mat_diag_mult_right: assumes A: "A \<in> carrier_mat nr n" 
  shows "A * mat_diag n f = Matrix.mat nr n (\<lambda> (i,j). A $$ (i,j) * f j)" 
proof (rule eq_matI, insert A, auto simp: mat_diag_def scalar_prod_def, goal_cases)
  case (1 i j)
  thus ?case by (subst sum.remove[of _ j], auto)
qed

lemma mat_diag_diag[simp]: "mat_diag n f * mat_diag n g = mat_diag n (\<lambda> i. f i * g i)" 
  by (subst mat_diag_mult_left[of _ n n], auto simp: mat_diag_def)

lemma mat_diag_one[simp]: "mat_diag n (\<lambda> x. 1) = 1\<^sub>m n" unfolding mat_diag_def by auto

lemma similar_mat_wit_smult: fixes A :: "'a :: comm_ring_1 mat" 
  assumes "similar_mat_wit A B P Q" 
  shows "similar_mat_wit (k \<cdot>\<^sub>m A) (k \<cdot>\<^sub>m B) P Q" 
proof -
  define n where "n = dim_row A" 
  note main = similar_mat_witD[OF n_def assms]
  show ?thesis
    by (rule similar_mat_witI[OF main(1-2) _ _ _ main(6-7)], insert main(3-), auto
      simp: mult_smult_distrib mult_smult_assoc_mat[of _ n n _ n]) 
qed

lemma similar_mat_smult: fixes A :: "'a :: comm_ring_1 mat" 
  assumes "similar_mat A B" 
  shows "similar_mat (k \<cdot>\<^sub>m A) (k \<cdot>\<^sub>m B)" 
  using similar_mat_wit_smult assms unfolding similar_mat_def by blast


lemma similar_mat_jordan_block_smult: fixes A :: "'a :: field mat" 
  assumes "similar_mat A (jordan_block n a)" 
   and k: "k \<noteq> 0" 
  shows "similar_mat (k \<cdot>\<^sub>m A) (jordan_block n (k * a))" 
proof -
  let ?J = "jordan_block n a" 
  let ?Jk = "jordan_block n (k * a)" 
  let ?kJ = "k \<cdot>\<^sub>m jordan_block n a" 
  from k have inv: "k ^ i \<noteq> 0" for i by auto
  let ?A = "mat_diag n (\<lambda> i. k^i)" 
  let ?B = "mat_diag n (\<lambda> i. inverse (k^i))"
  have "similar_mat_wit ?Jk ?kJ ?A ?B" 
  proof (rule similar_mat_witI)
    show "jordan_block n (k * a) = ?A * ?kJ * ?B"
      by (subst mat_diag_mult_left[of _ _ n], force, subst mat_diag_mult_right[of _ n],
       insert k inv, auto simp: jordan_block_def field_simps intro!: eq_matI)
  qed (auto simp: inv field_simps k)
  hence kJ: "similar_mat ?Jk ?kJ" 
    unfolding similar_mat_def by auto
  have "similar_mat A ?J" by fact
  hence "similar_mat (k \<cdot>\<^sub>m A) (k \<cdot>\<^sub>m ?J)" by (rule similar_mat_smult)
  with kJ show ?thesis
    using similar_mat_sym similar_mat_trans by blast
qed

lemma jordan_matrix_Cons:  "jordan_matrix (Cons (n,a) n_as) = four_block_mat 
  (jordan_block n a)                 (0\<^sub>m n (sum_list (map fst n_as))) 
  (0\<^sub>m (sum_list (map fst n_as)) n)   (jordan_matrix n_as)" 
  unfolding jordan_matrix_def by (simp, simp add: jordan_matrix_def[symmetric])

lemma smult_zero_mat[simp]: "(k :: 'a :: mult_zero) \<cdot>\<^sub>m 0\<^sub>m nr nc = 0\<^sub>m nr nc" 
  by (intro eq_matI, auto)

lemma similar_mat_jordan_matrix_smult:  fixes n_as :: "(nat \<times> 'a :: field) list"
  assumes k: "k \<noteq> 0" 
  shows "similar_mat (k \<cdot>\<^sub>m jordan_matrix n_as) (jordan_matrix (map (\<lambda> (n,a). (n, k * a)) n_as))" 
proof (induct n_as)
  case Nil
  show ?case by (auto simp: jordan_matrix_def intro!: similar_mat_refl)
next
  case (Cons na n_as)
  obtain n a where na: "na = (n,a)" by force
  let ?l = "map (\<lambda> (n,a). (n, k * a))" 
  let ?n = "sum_list (map fst n_as)" 
  have "k \<cdot>\<^sub>m jordan_matrix (Cons na n_as) = k \<cdot>\<^sub>m four_block_mat 
     (jordan_block n a) (0\<^sub>m n ?n)
     (0\<^sub>m ?n n) (jordan_matrix n_as)" (is "?M = _ \<cdot>\<^sub>m four_block_mat ?A ?B ?C ?D")
    by (simp add: na jordan_matrix_Cons)
  also have "\<dots> = four_block_mat (k \<cdot>\<^sub>m ?A) ?B ?C (k \<cdot>\<^sub>m ?D)" 
    by (subst smult_four_block_mat, auto)
  finally have jm: "?M = four_block_mat (k \<cdot>\<^sub>m ?A) ?B ?C (k \<cdot>\<^sub>m ?D)" .
  have [simp]: "fst (case x of (n :: nat, a) \<Rightarrow> (n, k * a)) = fst x" for x by (cases x, auto)
  have jmk: "jordan_matrix (?l (Cons na n_as)) = four_block_mat
     (jordan_block n (k * a)) ?B
     ?C (jordan_matrix (?l n_as))" (is "?kM = four_block_mat ?kA _ _ ?kD")
    by (simp add: na jordan_matrix_Cons o_def)
  show ?case unfolding jmk jm
    by (rule similar_mat_four_block_0_0[OF similar_mat_jordan_block_smult[OF _ k] Cons],
      auto intro!: similar_mat_refl)
qed

lemma jordan_nf_smult: fixes k :: "'a :: field" 
  assumes jn: "jordan_nf A n_as" 
  and k: "k \<noteq> 0" 
  shows "jordan_nf (k \<cdot>\<^sub>m A) (map (\<lambda> (n,a). (n, k * a)) n_as)" 
proof -
  let ?l = "map (\<lambda> (n,a). (n, k * a))" 
  from jn[unfolded jordan_nf_def] have sim: "similar_mat A (jordan_matrix n_as)" .
  from similar_mat_smult[OF this, of k] similar_mat_jordan_matrix_smult[OF k, of n_as]
  show ?thesis using jordan_nf_def similar_mat_trans by blast
qed

lemma similar_iff_same_jordan_nf: fixes A :: "complex mat" 
  assumes A: "A \<in> carrier_mat n n" and B: "B \<in> carrier_mat n n"
  shows "similar_mat A B = (jordan_nf A = jordan_nf B)" 
proof 
  show "similar_mat A B \<Longrightarrow> jordan_nf A = jordan_nf B" 
    by (intro ext, auto simp: jordan_nf_def, insert similar_mat_trans similar_mat_sym, blast+)
  assume id: "jordan_nf A = jordan_nf B" 
  from char_poly_factorized[OF A] obtain as where "char_poly A = (\<Prod>a\<leftarrow>as. [:- a, 1:])" by auto
  from jordan_nf_exists[OF A this] obtain n_as where jnfA: "jordan_nf A n_as" ..
  with id have jnfB: "jordan_nf B n_as" by simp
  from jnfA jnfB show "similar_mat A B" 
    unfolding jordan_nf_def using similar_mat_trans similar_mat_sym by blast
qed

lemma order_char_poly_smult: fixes A :: "complex mat" 
  assumes A: "A \<in> carrier_mat n n" 
  and k: "k \<noteq> 0" 
shows "order x (char_poly (k \<cdot>\<^sub>m A)) = order (x / k) (char_poly A)" 
proof -
  from char_poly_factorized[OF A] obtain as where "char_poly A = (\<Prod>a\<leftarrow>as. [:- a, 1:])" by auto
  from jordan_nf_exists[OF A this] obtain n_as where jnf: "jordan_nf A n_as" ..
  show ?thesis unfolding jordan_nf_order[OF jnf] jordan_nf_order[OF jordan_nf_smult[OF jnf k]]
    by (induct n_as, auto simp: k)
qed

locale inj_idom_divide_hom = idom_divide_hom hom + inj_idom_hom hom
  for hom :: "'a :: idom_divide \<Rightarrow> 'b :: idom_divide" 
begin
lemma hom_dvd_iff[simp]: "(hom p dvd hom q) = (p dvd q)"
proof (cases "p = 0")
  case False
  show ?thesis
  proof
    assume "hom p dvd hom q" from this[unfolded dvd_def] obtain k where 
      id: "hom q = hom p * k" by auto
    hence "(hom q div hom p) = (hom p * k) div hom p" by simp
    also have "\<dots> = k" by (rule nonzero_mult_div_cancel_left, insert False, simp)
    also have "hom q div hom p = hom (q div p)" by (simp add: hom_div)
    finally have "k = hom (q div p)" by auto
    from id[unfolded this] have "hom q = hom (p * (q div p))" by (simp add: hom_mult)
    hence "q = p * (q div p)" by simp
    thus "p dvd q" unfolding dvd_def ..
  qed simp
qed simp
end

locale map_poly_inj_idom_divide_hom = base: inj_idom_divide_hom
begin
sublocale map_poly_idom_hom ..
sublocale map_poly_inj_zero_hom .. 
sublocale inj_idom_hom "map_poly hom" ..
lemma divide_poly_main_hom: defines "hh \<equiv> map_poly hom" 
  shows "hh (divide_poly_main lc f g h i j) = divide_poly_main (hom lc) (hh f) (hh g) (hh h) i j"  
  unfolding hh_def
proof (induct j arbitrary: lc f g h i)
  case (Suc j lc f g h i)
  let ?h = "map_poly hom" 
  show ?case unfolding divide_poly_main.simps Let_def
    unfolding base.coeff_map_poly_hom base.hom_div[symmetric] base.hom_mult[symmetric] base.eq_iff
      if_distrib[of ?h] hom_zero
    by (rule if_cong[OF refl _ refl], subst Suc, simp add: hom_minus hom_add hom_mult)
qed simp

sublocale inj_idom_divide_hom "map_poly hom" 
proof
  fix f g :: "'a poly" 
  let ?h = "map_poly hom" 
  show "?h (f div g) = (?h f) div (?h g)" unfolding divide_poly_def if_distrib[of ?h]
    divide_poly_main_hom by simp
qed

lemma order_hom: "order (hom x) (map_poly hom f) = order x f"
  unfolding Polynomial.order_def unfolding hom_dvd_iff[symmetric]
  unfolding hom_power by (simp add: base.hom_uminus)
end


context field_hom
begin
sublocale inj_idom_divide_hom ..
end

lemma (in comm_ring_hom) hom_root_unity: "map_poly hom (root_unity n) = root_unity n" 
proof -
  interpret p: map_poly_comm_ring_hom hom ..
  show ?thesis unfolding root_unity_def 
    by (simp add: hom_distribs)
qed

lemma (in idom_hom) hom_prod_root_unity: "map_poly hom (prod_root_unity n) = prod_root_unity n" 
proof -
  interpret p: map_poly_comm_ring_hom hom ..  
  show ?thesis unfolding prod_root_unity_def p.hom_prod_list map_map o_def hom_root_unity ..
qed

lemma (in field_hom) hom_decompose_prod_root_unity_main: 
  "decompose_prod_root_unity_main (map_poly hom p) k = map_prod id (map_poly hom)
    (decompose_prod_root_unity_main p k)"
proof (induct p k rule: decompose_prod_root_unity_main.induct)
  case (1 p k)
  let ?h = "map_poly hom" 
  let ?p = "?h p" 
  let ?u = "root_unity k :: 'a poly" 
  let ?u' = "root_unity k :: 'b poly" 
  interpret p: map_poly_inj_idom_divide_hom hom ..
  have u': "?u' = ?h ?u" unfolding hom_root_unity ..
  note simp = decompose_prod_root_unity_main.simps
  let ?rec1 = "decompose_prod_root_unity_main (p div ?u) k" 
  have 0: "?p = 0 \<longleftrightarrow> p = 0" by simp
  show ?case 
    unfolding simp[of ?p k] simp[of p k] if_distrib[of "map_prod id ?h"] Let_def u'
    unfolding 0 p.hom_div[symmetric] p.hom_dvd_iff
    by (rule if_cong[OF refl], force, rule if_cong[OF refl if_cong[OF refl]], force,
     (subst 1(1), auto, cases ?rec1, auto)[1],
     (subst 1(2), auto))
qed

lemma (in field_hom) hom_decompose_prod_root_unity: 
  "decompose_prod_root_unity (map_poly hom p) = map_prod id (map_poly hom)
    (decompose_prod_root_unity p)" 
  unfolding decompose_prod_root_unity_def
  by (subst hom_decompose_prod_root_unity_main, simp)

end