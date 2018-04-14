theory LLL_Number_Bounds
  imports LLL_Complexity
    Perron_Frobenius.HMA_Connect
begin

definition "replace_col_hma A b k = (\<chi> i j. if j = k then b $h i else A $h i $h j)"
hide_const (open) Determinants.det
hide_const (open) Cartesian_Euclidean_Space.mat
hide_const (open) Cartesian_Euclidean_Space.row
hide_const (open) Cartesian_Euclidean_Space.vec

no_notation Inner_Product.real_inner_class.inner (infix "\<bullet>" 70)
no_notation Finite_Cartesian_Product.vec.vec_nth (infixl "$" 90)

definition "replace_col A b k = mat (dim_row A) (dim_col A) (\<lambda> (i,j). if j = k then b $ i else A $$ (i,j))" 

lemma HMA_M_replace_col[transfer_rule]: 
  "(HMA_M ===> HMA_V ===> HMA_I ===> HMA_M) replace_col replace_col_hma" 
  unfolding rel_fun_def replace_col_def replace_col_hma_def HMA_M_def HMA_V_def HMA_I_def
  by (auto simp: from_hma\<^sub>m_def from_hma\<^sub>v_def to_nat_from_nat_id intro!: eq_matI)

lemma cramer_lemma_real: fixes A :: "real mat" 
  assumes A: "A \<in> carrier_mat n n" 
  and x: "x \<in> carrier_vec n" 
  and k: "k < n" 
shows "det (replace_col A (A *\<^sub>v x) k) = x $v k * det A" 
  using cramer_lemma[folded replace_col_hma_def, untransferred, cancel_card_constraint] assms
  by auto

lemma cramer_lemma_rat: fixes A :: "rat mat" 
  assumes A: "A \<in> carrier_mat n n" 
  and x: "x \<in> carrier_vec n" 
  and k: "k < n" 
shows "det (replace_col A (A *\<^sub>v x) k) = x $v k * det A"
proof -
  let ?r = real_of_rat
  let ?hM = "map_mat ?r"
  let ?hV = "map_vec ?r" 
  let ?A = "?hM A" 
  let ?x = "?hV x" 
  have AA: "?A \<in> carrier_mat n n" using A by auto
  have xx: "?x \<in> carrier_vec n" using x by auto
  from cramer_lemma_real[OF AA xx k]
  have "det (replace_col ?A (?A *\<^sub>v ?x) k) = ?x $v k * det ?A" .
  also have "\<dots> = ?r (x $v k * det A)" using x k by (simp add: of_rat_mult)
  also have "?A *\<^sub>v ?x = ?hV (A *\<^sub>v x)" using A x
    by (metis of_rat_hom.mult_mat_vec_hom)
  also have "replace_col ?A \<dots> k = ?hM (replace_col A (A *\<^sub>v x) k)" 
    using A x k unfolding replace_col_def
    by (intro eq_matI, auto)
  also have "det \<dots> = ?r (det (replace_col A (A *\<^sub>v x) k))" by simp
  finally show ?thesis by simp
qed

lemma vec_cong:
  assumes "\<And>k. k < n \<Longrightarrow> f k = g k"
  shows "vec n f = vec n g"
  using assms by auto

lemma mat_cong:
  assumes "\<And>m' n'. m' < m \<Longrightarrow> n' < n \<Longrightarrow> f (m', n') = g (m',n')"
  shows "mat m n f = mat m n g"
  using assms by auto

lemma rat_of_int_dvd:
  assumes "b \<noteq> 0" "rat_of_int a / rat_of_int b \<in> \<int>"
  shows "b dvd a"
  using assms apply(elim Ints_cases)
  unfolding dvd_def
  by (metis nonzero_mult_div_cancel_left of_int_0_eq_iff of_int_eq_iff of_int_simps(4) times_divide_eq_right)

lemma times_mat_sum:
  fixes A::"'a::semiring_0 mat"
  assumes "dim_col A = dim_row B"
  shows "A * B = mat (dim_row A) (dim_col B) (\<lambda>(i, j). \<Sum>ia = 0..<dim_row B. A $$ (i, ia) * B $$ (ia, j))"
  using assms by (auto simp add: times_mat_def scalar_prod_def)

lemma denom_dvd_ints:
  fixes i::int
  assumes "quotient_of r = (z, n)" "rat_of_int i * r \<in> \<int>"
  shows "n dvd i"
proof -
  have "rat_of_int i * (rat_of_int z / rat_of_int n) \<in> \<int>"
    using assms quotient_of_div by blast
  then have "n dvd i * z"
    using quotient_of_denom_pos assms by (auto intro!: rat_of_int_dvd)
  then show "n dvd i"
    using assms algebraic_semidom_class.coprime_commute 
      quotient_of_coprime coprime_dvd_mult_left_iff by blast
qed

lemma quotient_of_bounds: 
  assumes "quotient_of r = (z, n)" "rat_of_int i * r \<in> \<int>" "0 < i" "\<bar>r\<bar> \<le> b"
  shows "rat_of_int \<bar>z\<bar> \<le> rat_of_int i * b" "n \<le> i" 
proof -
  show ni: "n \<le> i"
    using assms denom_dvd_ints  by (intro zdvd_imp_le) blast+
  have "\<bar>r\<bar> = \<bar>rat_of_int z / rat_of_int n\<bar>"
    using assms quotient_of_div by blast
  also have "\<dots> = rat_of_int \<bar>z\<bar> / rat_of_int n"
    using assms using quotient_of_denom_pos by force
  finally have "rat_of_int \<bar>z\<bar> = rat_of_int n * \<bar>r\<bar>"
    using assms by auto
  also have "\<dots> \<le> rat_of_int n * b"
    using assms quotient_of_denom_pos by auto
  also have "\<dots> \<le> rat_of_int i * b"
    using ni assms of_int_le_iff by (auto intro!: mult_right_mono)
  finally show "rat_of_int \<bar>z\<bar> \<le> rat_of_int i * b" 
    by simp
qed

lemma scalar_prod_Cauchy:
  fixes u v::"'a :: {trivial_conjugatable_ordered_field, linordered_field} Matrix.vec"
  assumes "u \<in> carrier_vec n" "v \<in> carrier_vec n"
  shows "(u \<bullet> v)\<^sup>2 \<le> \<parallel>u\<parallel>\<^sup>2 * \<parallel>v\<parallel>\<^sup>2 "
proof -
  { assume v_0: "v \<noteq> 0\<^sub>v n"
    have "0 \<le> (u - r \<cdot>\<^sub>v v) \<bullet> (u - r \<cdot>\<^sub>v v)" for r
      by (simp add: scalar_prod_ge_0)
    also have "(u - r \<cdot>\<^sub>v v) \<bullet> (u - r \<cdot>\<^sub>v v) = u \<bullet> u - r * (u \<bullet> v) - r * (u \<bullet> v) + r * r * (v \<bullet> v)" for r::'a
    proof -
      have "(u - r \<cdot>\<^sub>v v) \<bullet> (u - r \<cdot>\<^sub>v v) = (u - r \<cdot>\<^sub>v v) \<bullet> u - (u - r \<cdot>\<^sub>v v) \<bullet> (r \<cdot>\<^sub>v v)"
        using assms by (subst scalar_prod_minus_distrib) auto
      also have "\<dots> = u \<bullet> u - (r \<cdot>\<^sub>v v) \<bullet> u - r * ((u - r \<cdot>\<^sub>v v) \<bullet> v)"
        using assms by (subst minus_scalar_prod_distrib) auto
      also have "\<dots> = u \<bullet> u - r * (v \<bullet> u) - r * (u \<bullet> v - r * (v \<bullet> v))"
        using assms by (subst minus_scalar_prod_distrib) auto
      also have "\<dots> = u \<bullet> u - r * (u \<bullet> v) - r * (u \<bullet> v) + r * r * (v \<bullet> v)"
        using assms comm_scalar_prod by (auto simp add: field_simps)
      finally show ?thesis
        by simp
    qed
    also have "u \<bullet> u - r * (u \<bullet> v) - r * (u \<bullet> v) + r * r * (v \<bullet> v) = sq_norm u - (u \<bullet> v)\<^sup>2 / sq_norm v"
      if "r = (u \<bullet> v) / (v \<bullet> v)" for r
      unfolding that by (auto simp add: sq_norm_vec_as_cscalar_prod power2_eq_square)
    finally have "0 \<le> \<parallel>u\<parallel>\<^sup>2 - (u \<bullet> v)\<^sup>2 / \<parallel>v\<parallel>\<^sup>2"
      by auto
    then have "(u \<bullet> v)\<^sup>2 / \<parallel>v\<parallel>\<^sup>2 \<le> \<parallel>u\<parallel>\<^sup>2"
      by auto
    then have "(u \<bullet> v)\<^sup>2 \<le> \<parallel>u\<parallel>\<^sup>2 * \<parallel>v\<parallel>\<^sup>2"
      using pos_divide_le_eq[of "\<parallel>v\<parallel>\<^sup>2"] v_0 assms by (auto)
  }
  then show ?thesis
    by (fastforce simp add: assms)
qed
    
context gram_schmidt
begin

lemma sumlist_mult:
  assumes "set ws \<subseteq> carrier_vec n"
  shows "r \<cdot>\<^sub>v sumlist ws = sumlist (map (\<lambda>w. r \<cdot>\<^sub>v w) ws)"
proof -
  have [simp]: "dim_vec (M.sumlist (map ((\<cdot>\<^sub>v) r) ws)) = n" "\<forall>x\<in>set (map ((\<cdot>\<^sub>v) r) ws). dim_vec x = n"
               "\<forall>x\<in>set ws. dim_vec x = n" "dim_vec (M.sumlist ws) = n"
    using assms by (fastforce intro!: dim_sumlist)+
  have "(r \<cdot>\<^sub>v sumlist ws) $ i = sumlist (map ((\<cdot>\<^sub>v) r) ws) $ i" if "i < n" for i
  proof -
    have "(r \<cdot>\<^sub>v sumlist ws) $ i = r * M.sumlist ws $ i"
      using that by (auto)
    also have "\<dots> = r * (\<Sum>j = 0..<length ws. ws ! j $ i)"
      using that by (auto simp add: sumlist_nth)
    also have "\<dots> = (\<Sum>j = 0..<length ws. r * ws ! j $ i)"
      by (auto simp add: mult_hom.hom_sum)
    also have "\<dots> = (\<Sum>j = 0..<length ws. (r \<cdot>\<^sub>v ws ! j) $ i)"
      using that by (auto)
    also have "\<dots> = sumlist (map ((\<cdot>\<^sub>v) r) ws) $ i"
      using that by (subst sumlist_nth) auto
    finally show ?thesis
      by simp
  qed
  then show ?thesis
    by (auto)
qed

context
  fixes m::nat
begin

context
  fixes vs fs
  assumes indep: "lin_indpt_list fs"
   and len_fs: "length fs = m" 
   and snd_main: "snd (main fs) = vs" 
begin

(* Lemma 16.17 *) 

lemma ex_\<rho>:
  assumes "k < m"
  shows "\<exists>\<rho>. gso fs k = fs ! k + sumlist (map (\<lambda>j. \<rho> j \<cdot>\<^sub>v fs ! j) [0 ..< k])" (is "\<exists> \<rho>. ?Prop k \<rho>")
  using assms proof (induction k rule: less_induct)
  case (less k)
  then have "\<exists>\<rho>. ?Prop i \<rho>" if "i < k" for i
    using that by (intro less) auto
  hence "\<forall>i. \<exists>\<rho>. i < k \<longrightarrow> ?Prop i \<rho>"
    by blast
  from choice[OF this] obtain \<rho> where \<rho>_def: "?Prop i (\<rho> i)" if "i < k" for i
    by auto
  have "gso fs k = fs ! k + M.sumlist (map (\<lambda>i. - \<mu> fs k i \<cdot>\<^sub>v gso fs i) [0..<k])"
    by (subst gso.simps) simp
  also have "map (\<lambda>i. - \<mu> fs k i \<cdot>\<^sub>v gso fs i) [0..<k] = 
   map (\<lambda>i. - \<mu> fs k i \<cdot>\<^sub>v (fs ! i + M.sumlist (map (\<lambda>j. \<rho> i j \<cdot>\<^sub>v fs ! j) [0..<i]))) [0..<k]"
    by (auto intro: map_cong simp add: \<rho>_def)
  finally have *: "gso fs k = fs ! k + 
    M.sumlist (map (\<lambda>i. (- \<mu> fs k i) \<cdot>\<^sub>v (fs ! i + M.sumlist (map (\<lambda>j. \<rho> i j \<cdot>\<^sub>v fs ! j) [0..<i])))
              [0..<k])"
    by simp
  define \<gamma> where "\<gamma> = (\<lambda>x j. (if j < x then \<rho> x j else 0))"
  define \<rho>'::"nat \<Rightarrow> 'a" where "\<rho>' = (\<lambda>x. - \<mu> fs k x - (\<Sum>xa = 0..<k. \<mu> fs k xa * \<gamma> xa x))"
  have "gso fs k $ i = (fs ! k + M.sumlist (map (\<lambda>j. \<rho>' j \<cdot>\<^sub>v fs ! j) [0..<k])) $ i" if "i < n" for i
  proof -
    (* get rid of sumlist *)
    have 1: "gso fs k $ i = fs ! k $ i +
      (\<Sum>x = 0..<k. - (\<mu> fs k x * (fs ! x $v i + (\<Sum>j = 0..<x. (\<rho> x j * fs ! j $v i)))))"
    proof -
      have "gso fs k $ i =  fs ! k $ i + 
    M.sumlist (map (\<lambda>i. (- \<mu> fs k i) \<cdot>\<^sub>v (fs ! i + M.sumlist (map (\<lambda>j. \<rho> i j \<cdot>\<^sub>v fs ! j) [0..<i])))
              [0..<k]) $ i"
        using that gso_dim indep len_fs less by (fastforce simp add: *)
      also have "\<dots> = fs ! k $ i + (\<Sum>j = 0..<k. (- \<mu> fs k j \<cdot>\<^sub>v (fs ! j + M.sumlist (map (\<lambda>ja. \<rho> j ja \<cdot>\<^sub>v fs ! ja) [0..<j]))) $v i)"
        using assms less indep len_fs that by (subst sumlist_nth) (auto intro!: dim_sumlist) 
      also have "(\<Sum>j = 0..<k. (- \<mu> fs k j \<cdot>\<^sub>v (fs ! j + M.sumlist (map (\<lambda>ja. \<rho> j ja \<cdot>\<^sub>v fs ! ja) [0..<j]))) $v i) =
      (\<Sum>x = 0..<k. - (\<mu> fs k x * (fs ! x $v i + M.sumlist (map (\<lambda>ja. \<rho> x ja \<cdot>\<^sub>v fs ! ja) [0..<x]) $v i)))"
        using assms less indep len_fs that by (intro sum.cong) (auto simp add: dim_sumlist)
      also have "\<dots> = (\<Sum>x = 0..<k. - (\<mu> fs k x * (fs ! x $v i + (\<Sum>j = 0..<x. (\<rho> x j \<cdot>\<^sub>v fs ! j) $v i))))"
        using assms less indep len_fs that by (intro sum.cong) (auto simp add: dim_sumlist sumlist_nth)
      finally show ?thesis
        using assms less indep len_fs that by (auto simp add: dim_sumlist sumlist_nth)
    qed
    also have "(\<Sum>x = 0..<k. - (\<mu> fs k x * (fs ! x $v i + (\<Sum>j = 0..<x. \<rho> x j * fs ! j $v i)))) =
(\<Sum>x = 0..<k. - \<mu> fs k x * fs ! x $v i - \<mu> fs k x * (\<Sum>j = 0..<x. \<rho> x j * fs ! j $v i))"
      by (auto simp add: field_simps)
    also have "\<dots> = (\<Sum>x = 0..<k. - \<mu> fs k x * fs ! x $v i) - (\<Sum>x = 0..<k. \<mu> fs k x * (\<Sum>j = 0..<x. \<rho> x j * fs ! j $v i))"
      using sum_subtractf by fast
    also have "(\<Sum>x = 0..<k. \<mu> fs k x * (\<Sum>j = 0..<x. \<rho> x j * fs ! j $v i)) = (\<Sum>x = 0..<k. \<mu> fs k x * (\<Sum>j = 0..<k. \<gamma> x j * fs ! j $v i))"
    proof -
      have "(\<Sum>j = 0..<x. \<rho> x j * fs ! j $v i) = (\<Sum>j = 0..<k. \<gamma> x j * fs ! j $v i)" if "x < k" for x
      proof -
        let ?f = "(\<lambda>j. \<gamma> x j * fs ! j $v i)"
        have "{0..<x} \<union> {x..<k} = {0..<k}"
          using that by auto
        then show ?thesis
          using that sum.union_disjoint[of "{0..<x}" "{x..<k}" ?f] by (auto simp add: \<gamma>_def)
      qed
      then show ?thesis
        by (auto intro: sum.cong)
    qed
    also have "(\<Sum>x = 0..<k. \<mu> fs k x * (\<Sum>j = 0..<k. \<gamma> x j * fs ! j $v i)) = (\<Sum>x = 0..<k. (\<Sum>j = 0..<k. \<mu> fs k x * \<gamma> x j * fs ! j $v i))"
      by (auto simp add: sum_distrib_left field_simps)
    also have "\<dots> = (\<Sum>j = 0..<k. (\<Sum>x = 0..<k. \<mu> fs k x * \<gamma> x j) * fs ! j $v i)"
      using sum.swap by (subst sum_distrib_right) fast
    also have "((\<Sum>x = 0..<k. - \<mu> fs k x * fs ! x $v i) - (\<Sum>j = 0..<k. (\<Sum>x = 0..<k. \<mu> fs k x * \<gamma> x j) * fs ! j $v i))
    = (\<Sum>x = 0..<k. \<rho>' x * fs ! x $v i)" 
      by (auto simp add: sum_subtractf field_simps \<rho>'_def)
    finally show ?thesis
      using assms less indep len_fs that by (auto simp add: dim_sumlist sumlist_nth)
  qed
  then show ?case
    using less indep len_fs by (intro exI[of _ \<rho>'] eq_vecI) (auto simp add: dim_sumlist) 
qed

definition \<rho>_SOME_def:
  "\<rho> = (SOME \<rho>. \<forall>k<m. gso fs k = fs ! k + M.sumlist (map (\<lambda>l. \<rho> k l \<cdot>\<^sub>v fs ! l) [0..<k]))"

lemma \<rho>_def:
  assumes "k < m"
  shows "gso fs k = fs ! k + M.sumlist (map (\<lambda>j. \<rho> k j \<cdot>\<^sub>v fs ! j) [0..<k])"
proof -
  from ex_\<rho> have "\<forall>k. \<exists>\<rho>. k < m \<longrightarrow> gso fs k = fs ! k + M.sumlist (map (\<lambda>l. \<rho> l \<cdot>\<^sub>v fs ! l) [0..<k])"
    by blast
  from choice[OF this] have "\<exists>\<rho>. \<forall>k<m. gso fs k = fs ! k + M.sumlist (map (\<lambda>l. \<rho> k l \<cdot>\<^sub>v fs ! l) [0..<k])"
    by blast
  from someI_ex[OF this] show ?thesis
    unfolding \<rho>_SOME_def using assms by blast
qed

lemma gso_is_oc_projection:
  assumes "i < m"
  shows "is_oc_projection (gso fs i) (set (take i fs)) (fs ! i)"
proof -
  have "span (gso fs ` {0..<i}) = span (set (take i fs))"
    by (rule partial_span) (auto simp add: assms len_fs less_or_eq_imp_le indep)
  moreover have "is_oc_projection (gso fs i) (span (gso fs ` {0..<i})) (fs ! i)"
    by (rule gso_oc_projection_span) (auto simp add: assms len_fs less_or_eq_imp_le indep)
  ultimately have "is_oc_projection (gso fs i) (span (set (take i fs))) (fs ! i)"
    by auto
  then show ?thesis
    unfolding is_oc_projection_def apply(auto)
     apply(subst (asm) span_span)
    subgoal by (meson in_set_takeD indep lin_indpt_list_def subsetCE subsetI)
     apply(blast)
    subgoal for u
      apply(subgoal_tac " u \<in> span (set (take i fs))")
       apply(auto)
      apply(rule span_mem)
       apply(auto)
      subgoal for x
        apply(subgoal_tac "x \<in> set fs")
        using cof_vec_space.lin_indpt_list_def indep apply blast
        by (meson in_set_takeD)
      done
    done
qed

lemma gso_scalar_zero:
  assumes "k < m" "i < k"
  shows "(gso fs k) \<bullet> (fs ! i) = 0"
proof -
  have "fs ! i \<in> set (take k fs)"
    apply(subst nth_take[symmetric, of _ k])
    using assms apply(simp)
    apply(rule nth_mem)
    apply(simp)
    using assms
    using dual_order.strict_trans len_fs by blast
  moreover have "gso fs k \<bullet> u = 0" if "u \<in> set (take k fs)" for u
    using that gso_is_oc_projection[of k] unfolding is_oc_projection_def using assms by blast
  ultimately show ?thesis
    by blast
qed


end

end

end

lemma Ints_sum:
  assumes "\<And>a. a \<in> A \<Longrightarrow> f a \<in> \<int>"
  shows "sum f A \<in> \<int>"
  using assms by (induction A rule: infinite_finite_induct) auto

lemma Ints_prod:
  assumes "\<And>a. a \<in> A \<Longrightarrow> f a \<in> \<int>"
  shows "prod f A \<in> \<int>"
using assms by (induction A rule: infinite_finite_induct) auto

hide_const (open) Inner_Product.real_inner_class.inner

locale gram_schmidt_rat = gram_schmidt n "TYPE(rat)"
  for n :: nat 
begin

context
  fixes fs vs and m::nat
  assumes con_assms: "lin_indpt_list fs" "length fs = m" "snd (main fs) = vs"
begin

context
  assumes fs_int: "\<And>i j. i < n \<Longrightarrow> j < m \<Longrightarrow> fs ! j $v i \<in> \<int>"
begin

lemma fs_scalar_Ints:
  assumes "i < m" "j < m"
  shows "fs ! i \<bullet> fs ! j \<in> \<int>"
proof -
  have "dim_vec (fs ! j) = n"
    using assms con_assms by auto
  moreover have "(\<Sum>x = 0..<n'. fs ! i $v x * fs ! j $v x) \<in> \<int>" if "n' \<le> n" for n'
    using that assms apply (induction n') by (auto intro!: fs_int Ints_mult Ints_add)
  ultimately show ?thesis
    unfolding scalar_prod_def by auto
qed

lemma Gramian_matrix_alt_alt_def:
  assumes "k < m"
  shows "Gramian_matrix fs k = mat k k (\<lambda>(i,j). fs ! i \<bullet> fs ! j)"
proof -
  have *: "vec n (($v) (fs ! i)) = fs ! i" if "i < m" for i
    using that con_assms by auto
  then show ?thesis
    unfolding Gramian_matrix_def using con_assms assms
    by (intro eq_matI) (auto simp add: Let_def)
qed

lemma Gramian_determinant_Ints:
  assumes "k < m"
  shows "Gramian_determinant fs k \<in> \<int>"
proof -
  have "\<sigma> x < m" if "\<sigma> permutes {0..<k}" "x < k" for x \<sigma>
    using that permutes_less assms nat_SN.gt_trans by blast
  then have "signof \<sigma> * (\<Prod>j<k. Gramian_matrix fs k $$ (\<sigma> j, j)) \<in> \<int>" if "\<sigma> permutes {0..<k}" for \<sigma>
    unfolding Gramian_matrix_alt_alt_def using assms that
    by (intro Ints_mult)
      (auto simp add: Gramian_matrix_alt_alt_def signof_def intro!: fs_scalar_Ints Ints_prod)
  then show ?thesis
    unfolding Gramian_determinant_def using finite_permutations
    by (auto simp add: det_col[of _ k] Gramian_matrix_alt_alt_def assms intro!: Ints_sum)
qed


lemma inti_inti:
  assumes "i < n" "k < m"
  shows "(Gramian_determinant fs k \<cdot>\<^sub>v (gso fs k)) $ i \<in> \<int>"
proof -
  define \<rho>' where "\<rho>' = \<rho> m fs"
  have 1: "sum_list (map ((\<lambda>v. v \<bullet> fs ! j) \<circ> (\<lambda>j. \<rho>' k j \<cdot>\<^sub>v fs ! j)) [0..<k]) = 
           (\<Sum>i = 0..<k. \<rho>' k i * (fs ! i \<bullet> fs ! j))" if "j < k" for j
    using that assms con_assms
    by (subst interv_sum_list_conv_sum_set_nat) (auto intro!: sum.cong)
  have 1: "vec (dim_row (Gramian_matrix fs k)) (\<lambda>i. row (Gramian_matrix fs k) i \<bullet> vec k (\<rho>' k)) $ i = row (Gramian_matrix fs k) i \<bullet> vec k (\<rho>' k)" if "i < k" for i
    using that 
    apply(subst index_vec)
    using Gramian_matrix_def dim_row_mat(1) index_mult_mat(2) index_vec by metis+
  have 2: "row (Gramian_matrix fs k) i \<bullet> vec k (\<rho>' k) = - (fs ! k \<bullet> fs ! i)" if "i < k" for i
  proof -
    have "(\<Sum>j = 0..<k. fs ! i \<bullet> fs ! j * \<rho>' k j) = - (fs ! k \<bullet> fs ! i)"
    proof -
      have "(\<Sum>j = 0..<k. fs ! i \<bullet> fs ! j * \<rho>' k j) = (\<Sum>j = 0..<k. (\<rho>' k j \<cdot>\<^sub>v fs ! j) \<bullet> fs ! i)"
        apply(rule sum.cong)
         apply(auto)
        apply(subst scalar_prod_smult_left)
         apply(auto)
        using assms(2) con_assms(1) con_assms(2) that apply auto[1]
        apply(subst (asm) comm_scalar_prod[of _ n])
        using assms(2) con_assms(1) con_assms(2) that by auto
      also have "\<dots> = sum_list (map (\<lambda>j. (\<rho>' k j \<cdot>\<^sub>v fs ! j) \<bullet> fs ! i) [0..<k])"
        by (subst interv_sum_list_conv_sum_set_nat) auto
      also have "\<dots> = (\<Sum>j\<leftarrow>(map (\<lambda>j. (\<rho>' k j \<cdot>\<^sub>v fs ! j)) [0..<k]). j \<bullet> fs ! i)"
        by (subst map_map) (metis comp_apply)
      also have "\<dots> = M.sumlist (map (\<lambda>j. \<rho>' k j \<cdot>\<^sub>v fs ! j) [0..<k]) \<bullet> fs ! i"
        apply(subst  scalar_prod_left_sum_distrib[symmetric])
          apply(auto)
        using assms(2) con_assms(1) con_assms(2) gram_schmidt.f_carrier nat_SN.gt_trans apply blast
        using assms(2) con_assms(1) con_assms(2) gram_schmidt.f_carrier nat_SN.gt_trans that by blast
      also have "M.sumlist (map (\<lambda>j. \<rho>' k j \<cdot>\<^sub>v fs ! j) [0..<k]) = gso fs k - fs ! k"
      proof -
        have "M.sumlist (map (\<lambda>j. \<rho> (length fs) fs k j \<cdot>\<^sub>v fs ! j) [0..<k]) \<in> carrier_vec n"
          apply(intro sumlist_carrier)
          apply(auto) using con_assms assms by simp
        then show ?thesis
          unfolding \<rho>'_def apply(subst \<rho>_def) using con_assms assms by (auto)
      qed
      also have "(gso fs k - fs ! k) \<bullet> fs ! i = gso fs k \<bullet> fs ! i - fs ! k \<bullet> fs ! i"
        apply(rule minus_scalar_prod_distrib)
        using con_assms assms that by auto
      also have "\<dots> = - (fs ! k \<bullet> fs ! i)"
        apply(subst gso_scalar_zero) using con_assms assms that by (auto)
      finally show ?thesis
        by simp
    qed
    then show ?thesis
      apply(subst Gramian_matrix_alt_alt_def)
      using assms apply(simp)
      apply(subst row_mat)
      using that apply(simp)
      apply(auto)
      apply(subst (2) scalar_prod_def)
      by (auto)
  qed
  then have 1: "Gramian_matrix fs k *\<^sub>v (vec k (\<lambda>i. \<rho>' k i)) = (vec k (\<lambda>i. - (fs ! k \<bullet> fs ! i)))"
    unfolding mult_mat_vec_def
    apply(intro eq_vecI)
    apply(auto)
     apply(subst 1)
      apply(simp)
    using 2 apply(simp)
    by (metis dim_row_mat(1) gram_schmidt.Gramian_matrix_def index_mult_mat(2))
  have " det (replace_col (Gramian_matrix fs k) (vec k (\<lambda>i. - (fs ! k \<bullet> fs ! i))) i) \<in> \<int>" if "i < k" for i
    apply(subst det_col[of _ k])
    subgoal
      by (simp add: Gramian_matrix_alt_alt_def assms(2) replace_col_def)
    apply(subst Gramian_matrix_alt_alt_def)
    unfolding replace_col_def
     apply(auto)
    using assms apply simp
    apply(rule Ints_sum)
    apply(rule Ints_mult)
    unfolding signof_def apply(simp)
    apply(rule Ints_prod)
     apply(simp)
    apply(auto)
    apply (meson Ints_minus assms(2) fs_scalar_Ints nat_SN.gt_trans permutes_less(1))
    by (meson assms(2) fs_scalar_Ints nat_SN.gt_trans permutes_less(1))
  then have "vec k (\<rho>' k) $v i * Gramian_determinant fs k \<in> \<int>" if "i < k" for i
    using that unfolding Gramian_determinant_def
    apply(subst cramer_lemma_rat[where A="Gramian_matrix fs k" and x="vec k (\<rho>' k)", of k, symmetric])
       apply(auto simp add: Gramian_matrix_def Let_def)[3]
    apply(subst 1)
    by blast
  then have 1: "(\<rho>' k i) * Gramian_determinant fs k \<in> \<int>" if "i < k" for i
    by (simp add: that)
  show ?thesis
    apply(subst \<rho>_def)
    using con_assms assms apply(auto)[4]
    apply(subst index_smult_vec)
     apply(auto)
     apply(subst sumlist_dim)
    using assms con_assms apply(auto)
    apply(subst index_add_vec)
     apply(subst sumlist_dim)
    using assms con_assms apply(fastforce)+
    apply(subst distrib_left)
    apply(rule Ints_add)
     apply(rule Ints_mult)
      apply (simp add: Gramian_determinant_Ints)
         apply (simp add: fs_int)
    apply(subst sumlist_nth)
      apply(auto)
    apply(subst sum_distrib_left)
    apply(rule Ints_sum)
     apply(simp)
    apply(subst mult.assoc[symmetric])
    apply(rule Ints_mult)
    using 1 unfolding \<rho>'_def
    by (auto simp add: field_simps fs_int)
qed

lemma Gramian_determinant_div:
  assumes "l < m"
  shows "Gramian_determinant fs (Suc l) / Gramian_determinant fs l = \<parallel>vs ! l\<parallel>\<^sup>2"
proof -
  have "(\<Prod>j<Suc l. \<parallel>vs ! j\<parallel>\<^sup>2) = (\<Prod>j \<in> {0..<l} \<union> {l}. \<parallel>vs ! j\<parallel>\<^sup>2)"
    using assms by (intro prod.cong) (auto)
  also have "\<dots> = (\<Prod>j<l. \<parallel>vs ! j\<parallel>\<^sup>2) * \<parallel>vs ! l\<parallel>\<^sup>2"
    using assms by (subst prod_Un) (auto simp add: atLeast0LessThan)
  finally show ?thesis
    apply(subst Gramian_determinant)
    using con_assms assms apply(auto)
    apply(subst Gramian_determinant)
    using con_assms assms apply(fastforce)
       apply(blast) apply(blast) apply simp
    by (metis (no_types, lifting) cring_simprules(14) finite_lessThan lessThan_iff nonzero_mult_div_cancel_right order.strict_trans order_less_irrefl prod_zero_iff sq_norm_pos)
qed

lemma Gramian_determinant_mu_ints:
  assumes "l < k" "k < m"
  shows "Gramian_determinant fs (Suc l) * \<mu> fs k l \<in> \<int>"
proof -
  have 2: "vs ! l = gso fs l"
    by (metis assms(1) assms(2) atLeast0LessThan con_assms(1) con_assms(2) con_assms(3) gram_schmidt(4) gram_schmidt.main_connect(2) lessThan_iff map_eq_conv map_nth nat_SN.gt_trans set_upt)
  have 3: "(Gramian_determinant fs l \<cdot>\<^sub>v gso fs l) $v i = Gramian_determinant fs l * gso fs l $v i" if "i < n" for i
    using that
    using assms(1) assms(2) con_assms(1) con_assms(2) by auto
  show ?thesis
    unfolding \<mu>.simps using assms apply(simp)
    apply(subst (2) 2[symmetric])
    apply(subst (1) Gramian_determinant_div[symmetric])
    apply(auto)
    apply(subst mult_ac)
    apply(subst scalar_prod_smult_right[symmetric])
    subgoal using con_assms by auto
    unfolding scalar_prod_def
    apply(auto)
    apply(rule Ints_sum)
     apply(simp)
    apply(rule Ints_mult)
     apply (simp add: con_assms(1) con_assms(2) fs_int)
    apply(subst 3[symmetric])
    apply (simp add: con_assms(1) con_assms(2))
    apply(rule inti_inti)
    using assms con_assms by (auto)
qed

lemma Gramian_determinant_ge1:
  assumes "k < m"
  shows "1 \<le> Gramian_determinant fs k"
proof -
  have "0 < Gramian_determinant fs k"
    by (simp add: assms con_assms Gramian_determinant(2) less_or_eq_imp_le)
  moreover have "Gramian_determinant fs k \<in> \<int>"
    by (simp add: Gramian_determinant_Ints assms)
  ultimately show ?thesis
    using Ints_nonzero_abs_ge1 by fastforce
qed

lemma mu_bound_Gramian_determinant:
  assumes "l < k" "k < m"
  shows "(\<mu> fs k l)\<^sup>2 \<le> Gramian_determinant fs l * \<parallel>fs ! k\<parallel>\<^sup>2"
proof -
  have "(\<mu> fs k l)\<^sup>2  = (fs ! k \<bullet> gso fs l)\<^sup>2 / (\<parallel>gso fs l\<parallel>\<^sup>2)\<^sup>2"
    using assms by (simp add: power_divide \<mu>.simps)
  also have "\<dots> \<le> (\<parallel>fs ! k\<parallel>\<^sup>2 * \<parallel>gso fs l\<parallel>\<^sup>2) / (\<parallel>gso fs l\<parallel>\<^sup>2)\<^sup>2"
    using assms con_assms by (auto intro!: scalar_prod_Cauchy divide_right_mono)
  also have "\<dots> = \<parallel>fs ! k\<parallel>\<^sup>2 / \<parallel>gso fs l\<parallel>\<^sup>2"
    by (auto simp add: field_simps power2_eq_square)
  also have "\<dots> = \<parallel>fs ! k\<parallel>\<^sup>2 / \<parallel>vs ! l\<parallel>\<^sup>2"
    by (metis assms(1) assms(2) atLeast0LessThan con_assms(1) con_assms(2) con_assms(3) 
       gram_schmidt(4) gram_schmidt.main_connect(2) lessThan_iff map_eq_conv map_nth nat_SN.gt_trans set_upt)
  also have "\<dots> =  \<parallel>fs ! k\<parallel>\<^sup>2 / (Gramian_determinant fs (Suc l) / Gramian_determinant fs l)"
    apply(subst Gramian_determinant_div[symmetric])
    using assms by auto
  also have "\<dots> =  Gramian_determinant fs l * \<parallel>fs ! k\<parallel>\<^sup>2 / Gramian_determinant fs (Suc l)"
    by (auto simp add: field_simps)
  also have "\<dots> \<le> Gramian_determinant fs l * \<parallel>fs ! k\<parallel>\<^sup>2 / 1"
    apply(rule divide_left_mono)
      apply(auto)
    prefer 2
      apply (metis assms(1) assms(2) con_assms(1) con_assms(2) cring_simprules(27) gram_schmidt.Gramian_determinant(2) mult_le_cancel_left_pos nat_SN.gt_trans nat_less_le sq_norm_vec_ge_0)
    using Gramian_determinant_ge1 assms apply fastforce
    using Gramian_determinant_ge1 assms
    using con_assms(1) con_assms(2) gram_schmidt.Gramian_determinant(2) by fastforce
  finally show ?thesis
    by simp
qed

end

end

end

lemma vec_le_sq_norm:
  fixes v :: "'a :: {conjugatable_ring_1_abs_real_line} Matrix.vec"
  assumes "v \<in> carrier_vec n" "i < n"
  shows "\<bar>v $ i\<bar>\<^sup>2 \<le> \<parallel>v\<parallel>\<^sup>2"
using assms proof (induction v arbitrary: i)
  case (Suc n a v i)
  note IH = Suc
  show ?case 
  proof (cases i)
    case (Suc ii)
    then show ?thesis
      using IH IH(2)[of ii] le_add_same_cancel2 order_trans by fastforce
  qed (auto)
qed (auto)






context LLL
begin

lemma vec_hom_ints:
  assumes "i < n" "xs \<in> carrier_vec n"
  shows "of_int_hom.vec_hom xs $v i \<in> \<int>"
  using assms by auto

context 
  assumes alpha: "4 / 3 \<le> \<alpha>" 
begin

lemma LLL_partial_invariant_g_num_denom_bound:
  assumes inv: "LLL_partial_invariant A (k, Fs, Gs) fs gs" 
  and j: "j < n" and i: "i < m" 
  and quot: "quotient_of (gs ! i $ j) = (num, denom)" 
shows "\<bar>num\<bar> \<le> A ^ m" "\<bar>denom\<bar> \<le> A ^ m"
proof -
  note * = LLL_pinvD[OF inv]
  interpret gs: gram_schmidt_rat n .
  note dk_approx[OF alpha inv i, unfolded dk_def]  
  note *(12)[unfolded g_bound_def, rule_format, OF i]
  let ?r = "rat_of_int" 
  let ?fs = "map of_int_hom.vec_hom fs" 
  note gs.inti_inti[OF *(10)]
  have 1: "gs.gso ?fs i = gs ! i" using LLL_connect[OF inv] i by auto
  from gs.inti_inti[OF *(10)] have int: "(gs.Gramian_determinant ?fs i \<cdot>\<^sub>v (gs ! i)) $v j \<in> \<int>"
    apply(subst 1[symmetric])
    apply(rule gs.inti_inti[OF *(10), of m gs])
    using * assms apply(auto)[1]
    using "*"(2) gs.gso_connect snd_gram_schmidt_int apply auto[1]
    subgoal for j i 
      by (metis "*"(3) "*"(4) nth_map nth_mem subset_code(1) vec_hom_ints)
    using assms by auto
  have gsi: "gs ! i \<in> Rn"
    apply(subst 1[symmetric])
    apply(rule)
    using "*"(10) "*"(4) gram_schmidt.f_carrier i by fastforce
  have gs_sq: "\<bar>(gs ! i $ j)\<bar>\<^sup>2 \<le> rat_of_nat A"
    apply(rule order_trans)
     apply(rule vec_le_sq_norm[of _ n])
    apply (rule gsi)
    using assms by (auto simp add: \<open>\<parallel>gs ! i\<parallel>\<^sup>2 \<le> rat_of_nat A\<close>)
  from i have "m * m \<noteq> 0" by auto
  with D_approx[OF alpha inv] LLL_D_pos[OF inv] have A0: "A \<noteq> 0"
    by (meson nat_SN.compat nat_zero_less_power_iff order_less_irrefl)
  have "\<bar>(gs ! i $ j)\<bar> \<le> max 1 \<bar>(gs ! i $ j)\<bar>" by simp
  also have "\<dots> \<le> (max 1 \<bar>gs ! i $ j\<bar>)\<^sup>2"
    by (rule self_le_power, auto) 
  also have "\<dots> \<le> of_nat A" using gs_sq A0 unfolding max_def by auto
  finally have gs_bound: "\<bar>(gs ! i $ j)\<bar> \<le> of_nat A" .
  have "gs.Gramian_determinant (map of_int_hom.vec_hom fs) i = rat_of_int (gs.Gramian_determinant fs i)"
     using  assms *(3,4) carrier_vecD nth_mem by (intro of_int_Gramian_determinant) (simp, blast)
  with int have "(of_int (dk fs i) \<cdot>\<^sub>v gs ! i) $v j \<in> \<int>" unfolding dk_def by simp
  also have "(of_int (dk fs i) \<cdot>\<^sub>v gs ! i) $v j = of_int (dk fs i) * (gs ! i $ j)" using gsi i j by auto
  finally have "of_int (dk fs i) * gs ! i $v j \<in> \<int>" by auto
  from quotient_of_bounds[OF quot this LLL_dk_pos[OF inv] gs_bound] i
  have num: "rat_of_int \<bar>num\<bar> \<le> of_int (dk fs i * int A)" 
    and denom: "denom \<le> dk fs i" by auto
  from num have num: "\<bar>num\<bar> \<le> dk fs i * int A" by linarith
  from dk_approx[OF alpha inv i] have dk: "dk fs i \<le> int (A ^ i)" by linarith
  from denom dk have denom: "denom \<le> int (A ^ i)" by auto
  note num also have "dk fs i * int A \<le> int (A ^ i) * int A" 
    by (rule mult_right_mono[OF dk], auto)
  also have "\<dots> = int (A ^ (Suc i))" by simp
  finally have num: "\<bar>num\<bar> \<le> int (A ^ (i + 1))" by auto
  {
    fix jj
    assume "jj \<le> i + 1" 
    with i have "jj \<le> m" by auto
    from pow_mono_exp[OF _ this, of A] A0
    have "A^jj \<le> A^m" by auto
    hence "int (A^jj) \<le> int (A^m)" by linarith
  } note j_m = this
  have "\<bar>denom\<bar> = denom" using quotient_of_denom_pos[OF quot] by auto
  also have "\<dots> \<le> int (A ^ i)" by fact 
  also have "\<dots> \<le> int (A ^ m)" by (rule j_m, auto)
  finally show "\<bar>denom\<bar> \<le> int (A ^ m)" by auto
  show "\<bar>num\<bar> \<le> int (A ^ m)" using j_m[of "i+1"] num by auto
qed

lemma LLL_invariant_mu_num_denom_bound: 
  assumes inv: "LLL_invariant A (k, Fs, Gs) fs gs" 
  and i: "i < m" and j: "j < i"                
  and quot: "quotient_of (gs.\<mu> (RAT fs) i j) = (num, denom)" 
shows "\<bar>num\<bar> \<le> int (A ^ (2 * m) * m)" 
  and "\<bar>denom\<bar> \<le> int (A ^ m)" 
proof -
  have inv': "LLL_partial_invariant A (k, Fs, Gs) fs gs"
    using inv unfolding LLL_invariant_def by auto
  from LLL_invariant_A_pos[OF alpha inv'] i have A: "A > 0" by auto 
  note * = LLL_invD[OF inv]
  let ?mu = "gs.\<mu> (RAT fs) i j" 
  interpret gs: gram_schmidt_rat n .
  note dk_approx[OF alpha inv' i, unfolded dk_def]  
  note *(13)[unfolded g_bound_def, rule_format, OF i]
  note vec_le_sq_norm
  note *(2)  
  from j i have jm: "j < m" by auto
  from quotient_of_square[OF quot] 
  have quot_sq: "quotient_of (?mu^2) = (num * num, denom * denom)" 
    unfolding power2_eq_square by auto
  from dk_approx[OF alpha inv' jm]
  have dkj: "dk fs j \<le> int (A ^ j)" by linarith
  from LLL_dk_pos[OF inv', of "Suc j"] i j have dksj: "0 < dk fs (Suc j)" by auto
  hence dk_pos: "0 < (dk fs (Suc j))^2" by auto
  from dk_approx[OF alpha inv', of "Suc j"] j i 
  have "rat_of_int (dk fs (Suc j)) \<le> of_nat (A ^ Suc j)" 
    by auto
  hence dk_j_bound: "dk fs (Suc j) \<le> int (A^Suc j)" by linarith
  have "?mu^2 \<le> (gs.Gramian_determinant (RAT fs) j) * sq_norm (RAT fs ! i)"
    by (rule gs.mu_bound_Gramian_determinant[OF *(10) _ _ _ j i],
    insert *(2-), auto simp: gram_schmidt_int_def gram_schmidt_wit_def set_conv_nth)
  also have "sq_norm (RAT fs ! i) = of_int (sq_norm (fs ! i))" 
    unfolding sq_norm_of_int[symmetric] using *(4) i by auto
  also have "(gs.Gramian_determinant (RAT fs) j) = of_int (dk fs j)" 
    unfolding dk_def apply(rule of_int_Gramian_determinant)
    using j assms
    using *(4) dual_order.strict_trans apply simp
    using *(3) carrier_vecD nth_mem by blast
  also have "\<dots> * of_int (sq_norm (fs ! i)) = of_int (dk fs j * sq_norm (fs ! i))" by simp 
  also have "\<dots> \<le> of_int (int (A^j) * int (A * m))" unfolding of_int_le_iff 
    by (rule mult_mono[OF dkj \<open>f_bound A fs\<close>[unfolded f_bound_def, rule_format, OF i]], auto)
  also have "\<dots> = of_nat (A^(Suc j) * m)" by simp
  also have "\<dots> \<le> of_nat (A^m * m)" unfolding of_nat_le_iff
    by (rule mult_right_mono[OF pow_mono_exp], insert A jm, auto)
  finally have mu_bound: "abs (?mu^2) \<le> of_nat (A ^ m * m)" by auto
  have "gs.Gramian_determinant (RAT fs) (Suc j) * ?mu \<in> \<int>" 
    by (rule gs.Gramian_determinant_mu_ints[OF *(10) _ _ _ j i],
    insert *(2-), auto simp: gram_schmidt_int_def gram_schmidt_wit_def set_conv_nth)
  also have "(gs.Gramian_determinant (RAT fs) (Suc j)) = of_int (dk fs (Suc j))" 
    unfolding dk_def apply(rule of_int_Gramian_determinant)
    using j assms
    using *(4) dual_order.strict_trans apply simp
    using *(3) carrier_vecD nth_mem by blast
  finally have ints: "of_int (dk fs (Suc j)) * ?mu \<in> \<int>" .
  have "dk fs (Suc j) \<le> A ^ (Suc j)" by fact
  also have "\<dots> \<le> A ^ m" unfolding of_nat_le_iff
    by (rule pow_mono_exp, insert A jm, auto)
  finally have dk_j: "dk fs (Suc j) \<le> A ^ m" .
  from ints have "(of_int (dk fs (Suc j)) * ?mu)^2 \<in> \<int>" by auto
  also have "(of_int (dk fs (Suc j)) * ?mu)^2 = of_int ((dk fs (Suc j))^2) * ?mu^2" 
    unfolding power2_eq_square of_int_mult by simp
  finally have "of_int ((dk fs (Suc j))^2) * ?mu^2 \<in> \<int>" .
  note quot_bounds = quotient_of_bounds[OF quot_sq this dk_pos mu_bound]
  have "(abs denom)^2 = denom * denom" unfolding power2_eq_square by auto
  also have "\<dots> \<le> (dk fs (Suc j))^2" by fact
  finally have "abs denom \<le> dk fs (Suc j)" unfolding abs_le_square_iff[symmetric] using dksj by auto 
  also have "\<dots> \<le> A ^ m" by fact
  finally show "\<bar>denom\<bar> \<le> int (A ^ m)" .
  from quot_bounds(1)
  have "\<bar>num\<bar>^2 \<le> ((dk fs (Suc j))\<^sup>2 * int (A ^ m * m)) * 1" 
    unfolding power2_eq_square
    by (subst of_int_le_iff[symmetric, where ?'a = rat], auto)
  also have "\<dots> \<le> ((dk fs (Suc j))\<^sup>2 * int (A ^ m * m)) * int (A ^ m * m)" 
    by (rule mult_left_mono, insert A i, auto)
  also have "\<dots> = (dk fs (Suc j)* int (A ^ m * m))\<^sup>2" unfolding power2_eq_square by auto
  finally have "\<bar>num\<bar> \<le> dk fs (Suc j)* int (A ^ m * m)" unfolding abs_le_square_iff[symmetric] using dksj by auto 
  also have "\<dots> \<le> A^m * int (A^m * m)" 
    by (rule mult_right_mono[OF dk_j], auto)
  also have "\<dots> = int ((A^m * A ^ m) * m)" by simp
  also have "A^m * A ^ m = A^(2 * m)" unfolding power_add[symmetric] 
    by (rule arg_cong[of _ _ "\<lambda> x. A^x"], simp)
  finally show "\<bar>num\<bar> \<le> int (A ^ (2 * m) * m)" .
qed


end


end