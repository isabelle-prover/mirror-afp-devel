section \<open>Perron-Frobenius Theorem, Irreducible Matrices\<close>

subsection \<open>More Auxiliary Notions\<close>

theory Perron_Frobenius_Aux_2
imports 
  Perron_Frobenius
  Graph_Theory.Shortest_Path
begin

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
    by (rule sum.commute) 
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

lemma cis_mult_cmod_id: "cis (arg x) * of_real (cmod x) = x"
  using rcis_cmod_arg[unfolded rcis_def] by (simp add: ac_simps)

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

lemma rcis_mult_cis[simp]: "rcis n a * cis b = rcis n (a + b)" unfolding cis_rcis_eq rcis_mult by simp
lemma rcis_div_cis[simp]: "rcis n a / cis b = rcis n (a - b)" unfolding cis_rcis_eq rcis_divide by simp

lemma cis_plus_2pi[simp]: "cis (x + 2 * pi) = cis x" by (auto simp: complex_eq_iff)
lemma cis_plus_2pi_neq_1: assumes x: "0 < x" "x < 2 * pi" 
  shows "cis x \<noteq> 1" 
proof -
  from x have "cos x \<noteq> 1" by (smt cos_2pi_minus cos_monotone_0_pi cos_zero)
  thus ?thesis by (auto simp: complex_eq_iff)
qed

lemma cis_times_2pi[simp]: "cis (of_nat n * 2 * pi) = 1" 
proof (induct n)
  case (Suc n)
  have "of_nat (Suc n) * 2 * pi = of_nat n * 2 * pi + 2 * pi" by (simp add: distrib_right)
  also have "cis \<dots> = 1" unfolding cis_plus_2pi Suc ..
  finally show ?case .
qed simp

lemma rcis_plus_2pi[simp]: "rcis y (x + 2 * pi) = rcis y x" unfolding rcis_def by simp
lemma rcis_times_2pi[simp]: "rcis r (of_nat n * 2 * pi) = of_real r" 
  unfolding rcis_def cis_times_2pi by simp

lemma arg_rcis_cis: assumes n: "n > 0" shows "arg (rcis n x) = arg (cis x)"
  using arg_bounded arg_unique cis_arg complex_mod_rcis n rcis_def sgn_eq by auto

lemma arg_eqD: assumes "arg (cis x) = arg (cis y)" "-pi < x" "x \<le> pi" "-pi < y" "y \<le> pi" 
  shows "x = y" 
  using assms(1) unfolding arg_unique[OF sgn_cis assms(2-3)] arg_unique[OF sgn_cis assms(4-5)] .

lemma rcis_inj_on: assumes r: "r \<noteq> 0" shows "inj_on (rcis r) {0 ..< 2 * pi}" 
proof (rule inj_onI, goal_cases)
  case (1 x y)
  from arg_cong[OF 1(3), of "\<lambda> x. x / r"] have "cis x = cis y" using r by (simp add: rcis_def) 
  from arg_cong[OF this, of "\<lambda> x. inverse x"] have "cis (-x) = cis (-y)" by simp
  from arg_cong[OF this, of uminus] have *: "cis (-x + pi) = cis (-y + pi)"
    by (auto simp: complex_eq_iff)
  have "- x + pi = - y + pi" 
    by (rule arg_eqD[OF arg_cong[OF *, of arg]], insert 1(1-2), auto)
  thus ?case by simp
qed

lemma cis_inj_on: "inj_on cis {0 ..< 2 * pi}"
  using rcis_inj_on[of 1] unfolding rcis_def by auto

definition root_unity :: "nat \<Rightarrow> 'a :: comm_ring_1 poly" where
  "root_unity n = monom 1 n - 1"  

lemma poly_root_unity: "poly (root_unity n) x = 0 \<longleftrightarrow> x^n = 1" 
  unfolding root_unity_def by (simp add: poly_monom)

lemma degree_root_unity[simp]: "degree (root_unity n) = n" (is "degree ?p = _")
proof -
  have p: "?p = monom 1 n + (-1)" unfolding root_unity_def by auto
  show ?thesis
  proof (cases n)
    case 0
    thus ?thesis unfolding p by simp
  next
    case (Suc m)
    show ?thesis unfolding p unfolding Suc
      by (subst degree_add_eq_left, auto simp: degree_monom_eq)
  qed
qed

lemma zero_root_unit[simp]: "root_unity n = 0 \<longleftrightarrow> n = 0" (is "?p = 0 \<longleftrightarrow> _")
proof (cases "n = 0")
  case True
  thus ?thesis unfolding root_unity_def by simp
next
  case False
  from degree_root_unity[of n] False 
  have "degree ?p \<noteq> 0" by auto 
  hence "?p \<noteq> 0" by fastforce
  thus ?thesis using False by auto 
qed

lemma (in comm_ring_hom) hom_root_unity: "map_poly hom (root_unity n) = root_unity n" 
proof -
  interpret p: map_poly_comm_ring_hom hom ..
  show ?thesis unfolding root_unity_def 
    by (simp add: hom_distribs)
qed

definition prod_root_unity :: "nat list \<Rightarrow> 'a :: idom poly" where
  "prod_root_unity ns = prod_list (map root_unity ns)" 

lemma poly_prod_root_unity: "poly (prod_root_unity ns) x = 0 \<longleftrightarrow> (\<exists>k\<in>set ns. x ^ k = 1)" 
  unfolding prod_root_unity_def 
  by (simp add: poly_prod_list prod_list_zero_iff o_def image_def poly_root_unity)

lemma degree_prod_root_unity[simp]: "0 \<notin> set ns \<Longrightarrow> degree (prod_root_unity ns) = sum_list ns" 
  unfolding prod_root_unity_def 
  by (subst degree_prod_list_eq, auto simp: o_def)

lemma zero_prod_root_unit[simp]: "prod_root_unity ns = 0 \<longleftrightarrow> 0 \<in> set ns" 
  unfolding prod_root_unity_def prod_list_zero_iff by auto

lemma (in idom_hom) hom_prod_root_unity: "map_poly hom (prod_root_unity n) = prod_root_unity n" 
proof -
  interpret p: map_poly_comm_ring_hom hom ..  
  show ?thesis unfolding prod_root_unity_def p.hom_prod_list map_map o_def hom_root_unity ..
qed

function decompose_prod_root_unity_main :: 
  "'a :: field poly \<Rightarrow> nat \<Rightarrow> nat list \<times> 'a poly" where
  "decompose_prod_root_unity_main p k = ( 
    if k = 0 then ([], p) else 
   let q = root_unity k in if q dvd p then if p = 0 then ([],0) else
     map_prod (Cons k) id (decompose_prod_root_unity_main (p div q) k) else
     decompose_prod_root_unity_main p (k - 1))" 
  by pat_completeness auto

termination by (relation "measure (\<lambda> (p,k). degree p + k)", auto simp: degree_div_less)

declare decompose_prod_root_unity_main.simps[simp del]

lemma decompose_prod_root_unity_main: fixes p :: "complex poly" 
  assumes p: "p = prod_root_unity ks * f"
  and d: "decompose_prod_root_unity_main p k = (ks',g)" 
  and f: "\<And> x. cmod x = 1 \<Longrightarrow> poly f x \<noteq> 0" 
  and k: "\<And> k'. k' > k \<Longrightarrow> \<not> root_unity k' dvd p" 
shows "p = prod_root_unity ks' * f \<and> f = g \<and> set ks = set ks'"
  using d p k
proof (induct p k arbitrary: ks ks' rule: decompose_prod_root_unity_main.induct)
  case (1 p k ks ks')
  note p = 1(4)
  note k = 1(5)
  from k[of "Suc k"] have p0: "p \<noteq> 0" by auto
  hence "p = 0 \<longleftrightarrow> False" by auto
  note d = 1(3)[unfolded decompose_prod_root_unity_main.simps[of p k] this if_False Let_def]
  from p0[unfolded p] have ks0: "0 \<notin> set ks" by simp
  from f[of 1] have f0: "f \<noteq> 0" by auto
  note IH = 1(1)[OF _ refl _ p0] 1(2)[OF _ refl]
  show ?case 
  proof (cases "k = 0")
    case True
    with p k[unfolded this, of "hd ks"] p0 have "ks = []" 
      by (cases ks, auto simp: prod_root_unity_def)
    with d p True show ?thesis by (auto simp: prod_root_unity_def)
  next
    case k0: False
    note IH = IH[OF k0]
    from k0 have "k = 0 \<longleftrightarrow> False" by auto
    note d = d[unfolded this if_False]
    let ?u = "root_unity k :: complex poly" 
    show ?thesis
    proof (cases "?u dvd p")
      case True
      note IH = IH(1)[OF True]
      let ?call = "decompose_prod_root_unity_main (p div ?u) k" 
      from True d obtain Ks where rec: "?call = (Ks,g)" and ks': "ks' = (k # Ks)" 
        by (cases ?call, auto)
      from True have "?u dvd p \<longleftrightarrow> True" by simp
      note d = d[unfolded this if_True rec]
      let ?x = "cis (2 * pi / k)"
      have rt: "poly ?u ?x = 0" unfolding poly_root_unity using cis_times_2pi[of 1] 
        by (simp add: DeMoivre)
      with True have "poly p ?x = 0" unfolding dvd_def by auto
      from this[unfolded p] f[of ?x] rt have "poly (prod_root_unity ks) ?x = 0" 
        unfolding poly_root_unity by auto
      from this[unfolded poly_prod_root_unity] ks0 obtain k' where k': "k' \<in> set ks" 
        and rt: "?x ^ k' = 1" and k'0: "k' \<noteq> 0" by auto
      let ?u' = "root_unity k' :: complex poly" 
      from k' rt k'0 have rtk': "poly ?u' ?x = 0" unfolding poly_root_unity by auto
      {
        let ?phi = " k' * (2 * pi / k)" 
        assume "k' < k" 
        hence "0 < ?phi" "?phi < 2 * pi" using k0 k'0 by (auto simp: field_simps)
        from cis_plus_2pi_neq_1[OF this] rtk'
        have False unfolding poly_root_unity DeMoivre ..
      }
      hence kk': "k \<le> k'" by presburger
      {
        assume "k' > k" 
        from k[OF this, unfolded p] 
        have "\<not> ?u' dvd prod_root_unity ks" using dvd_mult2 by auto
        with k' have False unfolding prod_root_unity_def 
          using prod_list_dvd[of ?u' "map root_unity ks"] by auto
      }
      with kk' have kk': "k' = k" by presburger
      with k' have "k \<in> set ks" by auto
      from split_list[OF this] obtain ks1 ks2 where ks: "ks = ks1 @ k # ks2" by auto
      hence "p div ?u = (?u * (prod_root_unity (ks1 @ ks2) * f)) div ?u"
        unfolding p prod_root_unity_def by auto
      also have "\<dots> = prod_root_unity (ks1 @ ks2) * f" 
        by (rule nonzero_mult_div_cancel_left, insert k0, auto)
      finally have id: "p div ?u = prod_root_unity (ks1 @ ks2) * f" .
      from d have ks': "ks' = k # Ks" by auto
      have "k < k' \<Longrightarrow> \<not> root_unity k' dvd p div ?u" for k' 
        using k[of k'] True by (metis dvd_div_mult_self dvd_mult2)
      from IH[OF rec id this]
      have id: "p div root_unity k = prod_root_unity Ks * f" and
        *: "f = g \<and> set (ks1 @ ks2) = set Ks" by auto
      from arg_cong[OF id, of "\<lambda> x. x * ?u"] True 
      have "p = prod_root_unity Ks * f * root_unity k" by auto
      thus ?thesis using * unfolding ks ks' by (auto simp: prod_root_unity_def)
    next
      case False
      from d False have "decompose_prod_root_unity_main p (k - 1) = (ks',g)" by auto
      note IH = IH(2)[OF False this p]
      have k: "k - 1 < k' \<Longrightarrow> \<not> root_unity k' dvd p" for k' using False k[of k'] k0
        by (cases "k' = k", auto)
      show ?thesis by (rule IH, insert False k, auto)
    qed
  qed
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

definition "decompose_prod_root_unity p = decompose_prod_root_unity_main p (degree p)" 

lemma decompose_prod_root_unity: fixes p :: "complex poly" 
  assumes p: "p = prod_root_unity ks * f"
  and d: "decompose_prod_root_unity p = (ks',g)" 
  and f: "\<And> x. cmod x = 1 \<Longrightarrow> poly f x \<noteq> 0" 
  and p0: "p \<noteq> 0" 
shows "p = prod_root_unity ks' * f \<and> f = g \<and> set ks = set ks'"
proof (rule decompose_prod_root_unity_main[OF p d[unfolded decompose_prod_root_unity_def] f])
  fix k
  assume deg: "degree p < k" 
  hence "degree p < degree (root_unity k)" by simp
  with p0 show "\<not> root_unity k dvd p"
    by (simp add: poly_divides_conv0)
qed

lemma (in field_hom) hom_decompose_prod_root_unity: 
  "decompose_prod_root_unity (map_poly hom p) = map_prod id (map_poly hom)
    (decompose_prod_root_unity p)" 
  unfolding decompose_prod_root_unity_def
  by (subst hom_decompose_prod_root_unity_main, simp)


lemma roots_of_unity: assumes n: "n \<noteq> 0" 
  shows "(\<lambda> i. (cis (of_nat i * 2 * pi / n))) ` {0 ..< n} = { x :: complex. x ^ n = 1}" (is "?prod = ?Roots")
     "{x. poly (root_unity n) x = 0} = { x :: complex. x ^ n = 1}" 
     "card { x :: complex. x ^ n = 1} = n" 
proof (atomize(full), goal_cases)
  case 1
  let ?one = "1 :: complex"
  let ?p = "monom ?one n - 1" 
  have degM: "degree (monom ?one n) = n" by (rule degree_monom_eq, simp)
  have "degree ?p = degree (monom ?one n + (-1))" by simp
  also have "\<dots> = degree (monom ?one n)" 
    by (rule degree_add_eq_left, insert n, simp add: degM) 
  finally have degp: "degree ?p = n" unfolding degM .
  with n have p: "?p \<noteq> 0" by auto
  have roots: "?Roots = {x. poly ?p x = 0}"
    unfolding poly_diff poly_monom by simp
  also have "finite \<dots>" by (rule poly_roots_finite[OF p])
  finally have fin: "finite ?Roots" .
  have sub: "?prod \<subseteq> ?Roots" 
  proof
    fix x
    assume "x \<in> ?prod" 
    then obtain i where x: "x = cis (real i * 2 * pi / n)" by auto
    have "x ^ n = cis (real i * 2 * pi)" unfolding x DeMoivre using n by simp
    also have "\<dots> = 1" by simp
    finally show "x \<in> ?Roots" by auto
  qed
  have Rn: "card ?Roots \<le> n" unfolding roots
    by (rule poly_roots_degree[of ?p, unfolded degp, OF p])
  have "\<dots> = card {0 ..< n}" by simp
  also have "\<dots> = card ?prod" 
  proof (rule card_image[symmetric], rule inj_onI, goal_cases)
    case (1 x y)
    {
      fix m
      assume "m < n" 
      hence "real m < real n" by simp
      from mult_strict_right_mono[OF this, of "2 * pi / real n"] n
      have "real m * 2 * pi / real n < real n * 2 * pi / real n" by simp
      hence "real m * 2 * pi / real n < 2 * pi" using n by simp
    } note [simp] = this      
    have 0: "(1 :: real) \<noteq> 0" using n by auto
    have "real x * 2 * pi / real n = real y * 2 * pi / real n" 
      by (rule inj_onD[OF rcis_inj_on 1(3)[unfolded cis_rcis_eq]], insert 1(1-2), auto)
    with n show "x = y" by auto
  qed
  finally have cn:  "card ?prod = n" ..
  with Rn have "card ?prod \<ge> card ?Roots" by auto
  with card_mono[OF fin sub] have card: "card ?prod = card ?Roots" by auto
  have "?prod = ?Roots"
    by (rule card_subset_eq[OF fin sub card])
  from this roots[symmetric] cn[unfolded this]
  show ?case unfolding root_unity_def by blast
qed

lemma poly_roots_dvd: fixes p :: "'a :: field poly" 
  assumes "p \<noteq> 0" and "degree p = n" 
  and "card {x. poly p x = 0} \<ge> n" and "{x. poly p x = 0} \<subseteq> {x. poly q x = 0}" 
shows "p dvd q" 
proof -
  from poly_roots_degree[OF assms(1)] assms(2-3) have "card {x. poly p x = 0} = n" by auto
  from assms(1-2) this assms(4)
  show ?thesis
  proof (induct n arbitrary: p q)
    case (0 p q)
    from is_unit_iff_degree[OF 0(1)] 0(2) show ?case by auto
  next
    case (Suc n p q)
    let ?P = "{x. poly p x = 0}" 
    let ?Q = "{x. poly q x = 0}" 
    from Suc(4-5) card_gt_0_iff[of ?P] obtain x where 
      x: "poly p x = 0" "poly q x = 0" and fin: "finite ?P" by auto
    define r where "r = [:-x, 1:]" 
    from x[unfolded poly_eq_0_iff_dvd r_def[symmetric]] obtain p' q' where
      p: "p = r * p'" and q: "q = r * q'" unfolding dvd_def by auto
    from Suc(2) have "degree p = degree r + degree p'" unfolding p
      by (subst degree_mult_eq, auto)
    with Suc(3) have deg: "degree p' = n" unfolding r_def by auto
    from Suc(2) p have p'0: "p' \<noteq> 0" by auto
    let ?P' = "{x. poly p' x = 0}"
    let ?Q' = "{x. poly q' x = 0}"
    have P: "?P = insert x ?P'" unfolding p poly_mult unfolding r_def by auto
    have Q: "?Q = insert x ?Q'" unfolding q poly_mult unfolding r_def by auto
    {
      assume "x \<in> ?P'"  
      hence "?P = ?P'" unfolding P by auto
      from arg_cong[OF this, of card, unfolded Suc(4)] deg have False 
        using poly_roots_degree[OF p'0] by auto
    } note xp' = this
    hence xP': "x \<notin> ?P'" by auto
    have "card ?P = Suc (card ?P')" unfolding P 
      by (rule card_insert_disjoint[OF _ xP'], insert fin[unfolded P], auto) 
    with Suc(4) have card: "card ?P' = n" by auto
    from Suc(5)[unfolded P Q] xP' have "?P' \<subseteq> ?Q'" by auto
    from Suc(1)[OF p'0 deg card this] 
    have IH: "p' dvd q'" .
    show ?case unfolding p q using IH by simp
  qed
qed

lemma root_unity_decomp: assumes n: "n \<noteq> 0" 
  shows "root_unity n = 
    prod_list (map (\<lambda> i. [:-cis (of_nat i * 2 * pi / n), 1:]) [0 ..< n])" (is "?u = ?p")
proof - 
  have deg: "degree ?u = n" by simp
  note main = roots_of_unity[OF n]
  have dvd: "?u dvd ?p" 
  proof (rule poly_roots_dvd[OF _ deg])
    show "n \<le> card {x. poly ?u x = 0}" using main by auto
    show "?u \<noteq> 0" using n by auto
    show "{x. poly ?u x = 0} \<subseteq> {x. poly ?p x = 0}" 
      unfolding main(2) main(1)[symmetric] poly_prod_list prod_list_zero_iff by auto
  qed
  have deg': "degree ?p = n"
    by (subst degree_prod_list_eq, auto simp: o_def sum_list_triv)   
  have mon: "monic ?u" using deg unfolding root_unity_def using n by auto
  have mon': "monic ?p" by (rule monic_prod_list, auto)
  from dvd[unfolded dvd_def] obtain f where puf: "?p = ?u * f" by auto
  have "degree ?p = degree ?u + degree f" using mon' n unfolding puf
    by (subst degree_mult_eq, auto)
  with deg deg' have "degree f = 0" by auto
  from degree0_coeffs[OF this] obtain a where f: "f = [:a:]" by blast
  from arg_cong[OF puf, of lead_coeff] mon mon'
  have "a = 1" unfolding puf f by (cases "a = 0", auto)
  with f have f: "f = 1" by auto
  with puf show ?thesis by auto
qed

lemma order_monic_linear: "order x [:y,1:] = (if y + x = 0 then 1 else 0)" 
proof (cases "y + x = 0")
  case True
  hence "poly [:y,1:] x = 0" by simp  
  from this[unfolded order_root] have "order x [:y,1:] \<noteq> 0" by auto
  moreover from order_degree[of "[:y,1:]" x] have "order x [:y,1:] \<le> 1" by auto
  ultimately show ?thesis unfolding True by auto
next
  case False
  hence "poly [:y,1:] x \<noteq> 0" by auto
  from order_0I[OF this] False show ?thesis by auto
qed
  
lemma order_root_unity: fixes x :: complex assumes n: "n \<noteq> 0" 
  shows "order x (root_unity n) = (if x^n = 1 then 1 else 0)" 
  (is "order _ ?u = _")
proof (cases "x^n = 1")
  case False
  with roots_of_unity(2)[OF n] have "poly ?u x \<noteq> 0" by auto
  from False order_0I[OF this] show ?thesis by auto
next
  case True
  let ?phi = "\<lambda> i :: nat. i * 2 * pi / n" 
  from True roots_of_unity(1)[OF n] obtain i where i: "i < n" 
    and x: "x = cis (?phi i)" by force
  from i have n_split: "[0 ..< n] = [0 ..< i] @ i # [Suc i ..< n]"
    by (metis le_Suc_ex less_imp_le_nat not_le_imp_less not_less0 upt_add_eq_append upt_conv_Cons)
  {
    fix j
    assume j: "j < n \<or> j < i" and eq: "cis (?phi i) = cis (?phi j)"      
    from inj_onD[OF cis_inj_on eq] i j n have "i = j" by (auto simp: field_simps)
  } note inj = this
  have "order x ?u = 1" unfolding root_unity_decomp[OF n]
    unfolding x n_split using inj
    by (subst order_prod_list, force, fastforce simp: order_monic_linear)
  with True show ?thesis by auto
qed

lemma order_prod_root_unity: assumes 0: "0 \<notin> set ks" 
  shows "order (x :: complex) (prod_root_unity ks) = length (filter (\<lambda> k. x^k = 1) ks)" 
proof -
  have "order x (prod_root_unity ks) = (\<Sum>k\<leftarrow>ks. order x (root_unity k))" 
    unfolding prod_root_unity_def
    by (subst order_prod_list, insert 0, auto simp: o_def)
  also have "\<dots> = (\<Sum>k\<leftarrow>ks. (if x^k = 1 then 1 else 0))" 
    by (rule sum_list_cong, insert 0, force, intro order_root_unity, metis)
  also have "\<dots> = length (filter (\<lambda> k. x^k = 1) ks)" 
    by (subst sum_list_map_filter'[symmetric], simp add: sum_list_triv)
  finally show ?thesis .
qed

end