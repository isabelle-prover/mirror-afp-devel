(*
    Authors:    Maximilian Haslbeck
                René Thiemann
    License:    BSD
*)
subsection \<open>Explicit Bounds for Size of Numbers that Occur During LLL Algorithm\<close>

text \<open>The LLL invariant does not contain bounds on the number that occur during the execution. 
  We here strengthen the invariant so that it enforces bounds on the norms of the $f_i$ and $g_i$
  and we prove that the stronger invariant is maintained throughout the execution of the LLL algorithm.

  Based on the stronger invariant we prove bounds on the absolute values of the $\mu_{i,j}$,
  and on the absolute values of the numbers in the vectors $f_i$ and $g_i$. 
  Moreover, we further show that also the denominators in all of these numbers doesn't grow to much.
  Finally, we prove that each number (i.e., numerator or denominator) during the execution 
  can be represented with at most ${\cal OO}(m \cdot \log(M \cdot n))$ bits, where
  $m$ is the number of input vectors, $n$ is the dimension of the input vectors,
  and $M$ is the maximum absolute value of all numbers in the input vectors.
  Hence, each arithmetic operation in the LLL algorithm can be performed in polynomial time.\<close>
theory LLL_Number_Bounds
  imports LLL
    Perron_Frobenius.HMA_Connect
begin

(* TODO: Documentation and add references to computer algebra book *)

hide_const (open) Determinants.det
hide_const (open) Finite_Cartesian_Product.mat
hide_const (open) Finite_Cartesian_Product.row
hide_const (open) Finite_Cartesian_Product.vec
hide_const (open) Path_Connected.outside
hide_const (open) Linear_Algebra.orthogonal
hide_type (open) Finite_Cartesian_Product.vec

no_notation Inner_Product.real_inner_class.inner (infix "\<bullet>" 70)
no_notation Finite_Cartesian_Product.vec.vec_nth (infixl "$" 90)

definition "replace_col_hma A b k = (\<chi> i j. if j = k then b $h i else A $h i $h j)"


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

lemma rat_of_int_dvd:
  assumes "b \<noteq> 0" "rat_of_int a / rat_of_int b \<in> \<int>"
  shows "b dvd a"
  using assms apply(elim Ints_cases)
  unfolding dvd_def
  by (metis nonzero_mult_div_cancel_left of_int_0_eq_iff of_int_eq_iff of_int_simps(4) times_divide_eq_right)

lemma denom_dvd_ints:
  fixes i::int
  assumes "quotient_of r = (z, n)" "of_int i * r \<in> \<int>"
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
  assumes "quotient_of r = (n, d)" "rat_of_int i * r \<in> \<int>" "0 < i" "\<bar>r\<bar> \<le> b"
  shows "of_int \<bar>n\<bar> \<le> of_int i * b" "d \<le> i" 
proof -
  show ni: "d \<le> i"
    using assms denom_dvd_ints  by (intro zdvd_imp_le) blast+
  have "\<bar>r\<bar> = \<bar>rat_of_int n / rat_of_int d\<bar>"
    using assms quotient_of_div by blast
  also have "\<dots> = rat_of_int \<bar>n\<bar> / rat_of_int d"
    using assms using quotient_of_denom_pos by force
  finally have "of_int \<bar>n\<bar> = rat_of_int d * \<bar>r\<bar>"
    using assms by auto
  also have "\<dots> \<le> rat_of_int d * b"
    using assms quotient_of_denom_pos by auto
  also have "\<dots> \<le> rat_of_int i * b"
    using ni assms of_int_le_iff by (auto intro!: mult_right_mono)
  finally show "rat_of_int \<bar>n\<bar> \<le> rat_of_int i * b" 
    by simp
qed
    
context gram_schmidt
begin

context
  fixes m::nat
begin

context
  fixes fs
  assumes indep: "lin_indpt_list fs"
   and len_fs: "length fs = m" 
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
end (* fs *)

end (* m *)

end (* gram_schmidt *)

lemma Ints_sum:
  assumes "\<And>a. a \<in> A \<Longrightarrow> f a \<in> \<int>"
  shows "sum f A \<in> \<int>"
  using assms by (induction A rule: infinite_finite_induct) auto

lemma Ints_prod:
  assumes "\<And>a. a \<in> A \<Longrightarrow> f a \<in> \<int>"
  shows "prod f A \<in> \<int>"
using assms by (induction A rule: infinite_finite_induct) auto

lemma Ints_scalar_prod: 
  "v \<in> carrier_vec n \<Longrightarrow> w \<in> carrier_vec n
   \<Longrightarrow> (\<And> i. i < n \<Longrightarrow> v $ i \<in> \<int>) \<Longrightarrow> (\<And> i. i < n \<Longrightarrow> w $ i \<in> \<int>) \<Longrightarrow> v \<bullet> w \<in> \<int>" 
  unfolding scalar_prod_def  by (intro Ints_sum Ints_mult, auto)

locale gram_schmidt_rat = gram_schmidt n "TYPE(rat)"
  for n :: nat 
begin

context
  fixes fs and m::nat
  assumes con_assms: "lin_indpt_list fs" "length fs = m"
begin

context
  assumes fs_int: "\<And>i j. i < n \<Longrightarrow> j < m \<Longrightarrow> fs ! j $v i \<in> \<int>"
begin

lemma fs_scalar_Ints:
  assumes "i < m" "j < m"
  shows "fs ! i \<bullet> fs ! j \<in> \<int>"
  by (rule Ints_scalar_prod[of _ n], insert fs_int assms con_assms, auto)

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

lemma Gramian_determinant_times_gso_Ints:
  assumes "i < n" "k < m"
  shows "(Gramian_determinant fs k \<cdot>\<^sub>v (gso fs k)) $ i \<in> \<int>"
proof -
  let ?\<rho> = "\<rho> m fs" 
  have [intro!]: "(?\<rho> k i) * Gramian_determinant fs k \<in> \<int>" if "i < k" for i
  proof -
    have "- (fs ! k \<bullet> fs ! i) = (\<Sum>j = 0..<k. fs ! i \<bullet> fs ! j * ?\<rho>  k j)" if "i < k" for i
    proof -
      have "0 = gso fs k \<bullet> fs ! i"
        using gso_scalar_zero assms con_assms that by (auto simp add: gso_scalar_zero)
      also have "gso fs k = fs ! k + M.sumlist (map (\<lambda>j. ?\<rho>  k j \<cdot>\<^sub>v fs ! j) [0..<k])"
        using con_assms assms \<rho>_def by auto
      also have "\<dots> \<bullet> fs ! i = fs ! k \<bullet> fs ! i + M.sumlist (map (\<lambda>j. ?\<rho>  k j \<cdot>\<^sub>v fs ! j) [0..<k]) \<bullet> fs ! i"
        using assms con_assms that by (auto intro!: sumlist_carrier add_scalar_prod_distrib[of _ n])
      also have "M.sumlist (map (\<lambda>j. ?\<rho>  k j \<cdot>\<^sub>v fs ! j) [0..<k]) \<bullet> fs ! i = 
                 sum_list (map ((\<lambda>v. v \<bullet> fs ! i) \<circ> (\<lambda>j. ?\<rho>  k j \<cdot>\<^sub>v fs ! j)) [0..<k])"
        using con_assms assms that
        by (subst scalar_prod_left_sum_distrib) (auto intro!: sumlist_carrier)
      also have "\<dots> = (\<Sum>j\<leftarrow>[0..<k]. (?\<rho>  k j \<cdot>\<^sub>v fs ! j) \<bullet> fs ! i)"
        by (auto intro: arg_cong[where f=sum_list])
      also have "\<dots> = (\<Sum>j = 0..<k. fs ! i \<bullet> fs ! j * ?\<rho>  k j)"
        using con_assms assms that f_carrier 
        by(subst sum_set_upt_conv_sum_list_nat[symmetric], intro sum.cong)
          (auto simp add: comm_scalar_prod[of _ n])
      finally show ?thesis
        by simp
    qed
    then have a: "Gramian_matrix fs k *\<^sub>v (vec k (\<lambda>i. ?\<rho> k i)) = (vec k (\<lambda>i. - (fs ! k \<bullet> fs ! i)))"
      using con_assms assms by (auto simp add: Gramian_matrix_alt_alt_def scalar_prod_def)
    moreover have "det (replace_col (Gramian_matrix fs k) (vec k (\<lambda>i. - (fs ! k \<bullet> fs ! i))) i) \<in> \<int>" if "i < k" for i
    proof -
      have "\<sigma> i < length fs" if "\<sigma> permutes {0..<k}" "i < k" for \<sigma> i
        using that assms con_assms order.strict_trans permutes_less by blast
      then show ?thesis
        using con_assms assms permutes_less(1) 
        by(subst det_col[of _ k])
          (auto simp add: Gramian_matrix_alt_alt_def replace_col_def signof_def
            intro!: Ints_sum Ints_mult Ints_prod Ints_minus fs_scalar_Ints)
    qed
    then have "det (replace_col (Gramian_matrix fs k) (Gramian_matrix fs k *\<^sub>v vec k (\<rho> m fs k)) i) \<in> \<int>" if "i < k" for i
      using that by (subst a) auto
    then have "vec k (?\<rho>  k) $v i * Gramian_determinant fs k \<in> \<int>" if "i < k" for i
      using that unfolding Gramian_determinant_def
      by (subst cramer_lemma_rat[of _ k,symmetric]) (auto simp add: Gramian_matrix_def Let_def)
    then show ?thesis
      using that by simp
  qed
  then have "( ?\<rho> k j * Gramian_determinant fs k) * fs ! j $v i \<in> \<int>" if "j < k" for j
    using that fs_int assms by (auto intro!: Ints_mult)
  moreover have "( ?\<rho> k j * Gramian_determinant fs k) * fs ! j $v i =
                 Gramian_determinant fs k *  ?\<rho> k j * fs ! j $v i" for j
    by (auto simp add: field_simps)
  ultimately have "Gramian_determinant fs k * (\<Sum>j = 0..<k. \<rho> (length fs) fs k j * fs ! j $v i) \<in> \<int>"
    using con_assms by (subst sum_distrib_left) (auto simp add: field_simps intro!: Ints_sum)
  moreover have "(gso fs k) $v i = fs ! k $v i + sum (\<lambda>j. (?\<rho> k j \<cdot>\<^sub>v fs ! j) $v i) {0..<k}"
  proof -
    have " i < dim_vec (M.sumlist (map (\<lambda>j. \<rho> (length fs) fs k j \<cdot>\<^sub>v fs ! j) [0..<k]))"
      using con_assms assms by (subst sumlist_dim) auto
    then show ?thesis
      using assms con_assms by (auto simp add: sumlist_nth sumlist_dim \<rho>_def)
  qed
  ultimately show ?thesis
    using con_assms assms
    by (auto simp add: distrib_left Gramian_determinant_Ints fs_int intro!: Ints_mult Ints_add)
qed

lemma Gramian_determinant_div:
  assumes "l < m"
  shows "Gramian_determinant fs (Suc l) / Gramian_determinant fs l = \<parallel>gso fs l\<parallel>\<^sup>2"
proof -
  have "Gramian_determinant fs (Suc l) / Gramian_determinant fs l = 
             (\<Prod>j<Suc l. \<parallel>gso fs j\<parallel>\<^sup>2) / (\<Prod>j<l. \<parallel>gso fs j\<parallel>\<^sup>2)"
    using con_assms assms by (auto simp add: Gramian_determinant)
  also have "(\<Prod>j<Suc l. \<parallel>gso fs j\<parallel>\<^sup>2) = (\<Prod>j \<in> {0..<l} \<union> {l}. \<parallel>gso fs j\<parallel>\<^sup>2)"
    using assms by (intro prod.cong) (auto)
  also have "\<dots> = (\<Prod>j<l. \<parallel>gso fs j\<parallel>\<^sup>2) * \<parallel>gso fs l\<parallel>\<^sup>2"
    using assms by (subst prod_Un) (auto simp add: atLeast0LessThan)
  also have "(\<Prod>j<l. \<parallel>gso fs j\<parallel>\<^sup>2) * \<parallel>gso fs l\<parallel>\<^sup>2 / (\<Prod>j<l. \<parallel>gso fs j\<parallel>\<^sup>2) = \<parallel>gso fs l\<parallel>\<^sup>2"
  proof -
    have "0 < \<parallel>gso fs j\<parallel>\<^sup>2" if "j < l" for j
      using assms con_assms that by (intro sq_norm_pos[of _ m]) (auto)
    then show ?thesis
      using assms by (fastforce simp add: field_simps)
  qed
  finally show ?thesis
    by simp
qed

lemma Gramian_determinant_mu_ints:
  assumes "l \<le> k" "k < m"
  shows "Gramian_determinant fs (Suc l) * \<mu> fs k l \<in> \<int>"
proof (cases "l < k")
  case True
  have ll: "Gramian_determinant fs l * gso fs l $v i = (Gramian_determinant fs l \<cdot>\<^sub>v gso fs l) $v i" if "i < n" for i
    using that assms con_assms by auto
  have "Gramian_determinant fs (Suc l) * \<mu> fs k l = Gramian_determinant fs (Suc l) * (fs ! k \<bullet> gso fs l) / \<parallel>gso fs l\<parallel>\<^sup>2 "
    using assms True unfolding \<mu>.simps by simp
  also have "\<dots> = fs ! k \<bullet> (Gramian_determinant fs l \<cdot>\<^sub>v gso fs l)"
    using assms con_assms Gramian_determinant(2)[of fs m "Suc l"]
    by (subst Gramian_determinant_div[symmetric]) (auto)
  also have "\<dots> \<in> \<int>"
  proof -
    have "Gramian_determinant fs l * gso fs l $v i \<in> \<int>" if "i < n" for i
      using assms Gramian_determinant_times_gso_Ints that ll by (simp)
    then show ?thesis
     using con_assms assms by (auto intro!: Ints_sum simp add: con_assms fs_int scalar_prod_def)
 qed
 finally show ?thesis
   by simp
next
  case False
  with assms have l: "l = k" by auto
  show ?thesis unfolding l \<mu>.simps using Gramian_determinant_Ints[OF con_assms fs_int] assms by simp
qed

end (* fs_int *)

end (* fixes fs *)

end (* gram_schmidt_rat *)


lemma vec_hom_Ints:
  assumes "i < n" "xs \<in> carrier_vec n"
  shows "of_int_hom.vec_hom xs $v i \<in> \<int>"
  using assms by auto

context LLL
begin

lemma LLL_mu_d_Z: assumes inv: "LLL_invariant upw i fs" 
  and j: "j \<le> ii" and ii: "ii < m" 
shows "of_int (d fs (Suc j)) * \<mu> fs ii j \<in> \<int>"
proof -
  interpret gram_schmidt_rat n .
  note * = LLL_invD[OF inv]
  have id: "gs.Gramian_determinant (RAT fs) (Suc j) = of_int (d fs (Suc j))" 
    unfolding d_def
    by (rule of_int_Gramian_determinant, insert j ii *(4,6), auto)
  show ?thesis
    by (rule Gramian_determinant_mu_ints[OF *(1-2) _ j ii, unfolded id], insert *(4,6), force)
qed

text \<open>maximum absolute value in initial basis\<close>
definition "M = Max ({abs (fs_init ! i $ j) | i j. i < m \<and> j < n} \<union> {0})" 

text \<open>The bounds for the $f_i$ distinguishes whether we are inside or outside the inner for-loop.\<close>

definition f_bound :: "bool \<Rightarrow> nat \<Rightarrow> int vec list \<Rightarrow> bool" where 
  "f_bound outside ii fs = (\<forall> i < m. sq_norm (fs ! i) \<le> (if i \<noteq> ii \<or> outside then int (A * m) else 
     int (4 ^ (m - 1) * A ^ m * m * m)))" 

definition "\<mu>_bound_row fs bnd i = (\<forall> j \<le> i. (\<mu> fs i j)^2 \<le> bnd)" 
abbreviation "\<mu>_bound_row_inner fs i j \<equiv> \<mu>_bound_row fs (4 ^ (m - 1 - j) * of_nat (A ^ (m - 1) * m)) i"  

definition "LLL_bound_invariant outside upw i fs =
  (LLL_invariant upw i fs \<and> f_bound outside i fs \<and> g_bound fs)" 

lemma bound_invD: assumes "LLL_bound_invariant outside upw i fs" 
  shows "LLL_invariant upw i fs" "f_bound outside i fs" "g_bound fs"
  using assms unfolding LLL_bound_invariant_def by auto

lemma bound_invI: assumes "LLL_invariant upw i fs" "f_bound outside i fs" "g_bound fs" 
  shows "LLL_bound_invariant outside upw i fs"
  using assms unfolding LLL_bound_invariant_def by auto

lemma \<mu>_bound_rowI: assumes "\<And> j. j \<le> i \<Longrightarrow> (\<mu> fs i j)^2 \<le> bnd"
  shows "\<mu>_bound_row fs bnd i" 
  using assms unfolding \<mu>_bound_row_def by auto

lemma \<mu>_bound_rowD: assumes "\<mu>_bound_row fs bnd i" "j \<le> i"
  shows "(\<mu> fs i j)^2 \<le> bnd"
  using assms unfolding \<mu>_bound_row_def by auto

lemma \<mu>_bound_row_1: assumes "\<mu>_bound_row fs bnd i" 
  shows "bnd \<ge> 1" using \<mu>_bound_rowD[OF assms, of i]
  by (auto simp: gs.\<mu>.simps)

lemma reduced_\<mu>_bound_row: assumes red: "reduced fs i"  
  and ii: "ii < i" 
shows "\<mu>_bound_row fs 1 ii"
proof (intro \<mu>_bound_rowI)
  fix j
  assume "j \<le> ii"
  show "(\<mu> fs ii j)^2 \<le> 1"
  proof (cases "j < ii")
    case True
    from red[unfolded gs.reduced_def, THEN conjunct2, rule_format, OF ii True]
    have "abs (\<mu> fs ii j) \<le> 1/2" by auto
    from mult_mono[OF this this]
    show ?thesis by (auto simp: power2_eq_square)
  qed (auto simp: gs.\<mu>.simps)
qed

lemma f_bound_True_arbitrary: assumes "f_bound True ii fs"
  shows "f_bound outside j fs" 
  unfolding f_bound_def 
proof (intro allI impI, rule ccontr, goal_cases)
  case (1 i)
  from 1 have nz: "\<parallel>fs ! i\<parallel>\<^sup>2 \<noteq> 0" by (auto split: if_splits)
  hence gt: "\<parallel>fs ! i\<parallel>\<^sup>2 > 0" using sq_norm_vec_ge_0[of "fs ! i"] by auto
  from assms(1)[unfolded f_bound_def, rule_format, OF 1(1)]
  have one: "\<parallel>fs ! i\<parallel>\<^sup>2 \<le> int (A * m) * 1" by auto
  from less_le_trans[OF gt one] have A0: "A \<noteq> 0" by (cases "A = 0", auto)
  note one
  also have "int (A * m) * 1 \<le> int (A * m) * int (4 ^ (m - 1) * A ^ (m - 1) * m)"
    by (rule mult_left_mono, unfold of_nat_mult, intro mult_ge_one, insert 1 A0, auto)  
  also have "\<dots> = int (4 ^ (m - 1) * A ^ (Suc (m - 1)) * m * m)" unfolding of_nat_mult by simp
  also have "Suc (m - 1) = m" using 1 by simp
  finally show ?case using one 1 by (auto split: if_splits)
qed


context fixes fs :: "int vec list" 
  assumes lin_indep: "lin_indep fs" 
  and len: "length fs = m" 
begin

lemma sq_norm_fs_via_sum_mu_gso: assumes i: "i < m" 
  shows "of_int \<parallel>fs ! i\<parallel>\<^sup>2 = (\<Sum>j\<leftarrow>[0..<Suc i]. (\<mu> fs i j)\<^sup>2 * \<parallel>gso fs j\<parallel>\<^sup>2)" 
proof -
  let ?G = "map (gso fs) [0 ..< m]" 
  let ?gso = "\<lambda> fs j. ?G ! j"
  have "of_int \<parallel>fs ! i\<parallel>\<^sup>2 = \<parallel>RAT fs ! i\<parallel>\<^sup>2" unfolding sq_norm_of_int[symmetric] using insert i len by auto
  also have "RAT fs ! i = gs.sumlist (map (\<lambda>j. \<mu> fs i j \<cdot>\<^sub>v gso fs j) [0..<Suc i])" 
    using gs.fi_is_sum_of_mu_gso[OF lin_indep _ i] len by auto
  also have id: "map (\<lambda>j. \<mu> fs i j \<cdot>\<^sub>v gso fs j) [0..<Suc i] = map (\<lambda>j. \<mu> fs i j \<cdot>\<^sub>v ?gso fs j) [0..<Suc i]" 
    by (rule nth_equalityI, insert i, auto simp: nth_append)
  also have "sq_norm (gs.sumlist \<dots>) = sum_list (map sq_norm (map (\<lambda>j. \<mu> fs i j \<cdot>\<^sub>v gso fs j) [0..<Suc i]))" 
    unfolding map_map o_def sq_norm_smult_vec
    unfolding sq_norm_vec_as_cscalar_prod cscalar_prod_is_scalar_prod conjugate_id
  proof (subst gs.scalar_prod_lincomb_orthogonal)
    show "Suc i \<le> length ?G" using i by auto
    show "set ?G \<subseteq> Rn" using gs.gso_carrier[OF lin_indep, of m] len by auto
    show "orthogonal ?G" using gs.orthogonal_gso[OF lin_indep, of m] len by auto
  qed (rule arg_cong[of _ _ sum_list], intro nth_equalityI, insert i, auto simp: nth_append)
  also have "map sq_norm (map (\<lambda>j. \<mu> fs i j \<cdot>\<^sub>v gso fs j) [0..<Suc i]) = map (\<lambda>j. (\<mu> fs i j)^2 * sq_norm (gso fs j)) [0..<Suc i]" 
    unfolding map_map o_def sq_norm_smult_vec by (rule map_cong, auto simp: power2_eq_square)
  finally show ?thesis . 
qed

lemma sq_norm_fs_mu_g_bound: assumes i: "i < m" 
  and mu_bound: "\<mu>_bound_row fs bnd i" 
  and g_bound: "g_bound fs" 
shows "of_int \<parallel>fs ! i\<parallel>\<^sup>2 \<le> of_nat (Suc i * A) * bnd" 
proof -
  have "of_int \<parallel>fs ! i\<parallel>\<^sup>2 = (\<Sum>j\<leftarrow>[0..<Suc i]. (\<mu> fs i j)\<^sup>2 * \<parallel>gso fs j\<parallel>\<^sup>2)" 
    by (rule sq_norm_fs_via_sum_mu_gso[OF i])
  also have "\<dots> \<le> (\<Sum>j\<leftarrow>[0..<Suc i]. bnd * of_nat A)" 
  proof (rule sum_list_ge_mono, force, unfold length_map length_upt,
    subst (1 2) nth_map_upt, force, goal_cases)
    case (1 j)
    hence ji: "j \<le> i" by auto
    from g_bound[unfolded g_bound_def] i ji 
    have GB: "sq_norm (gso fs j) \<le> of_nat A" by auto
    show ?case 
      by (rule mult_mono, insert \<mu>_bound_rowD[OF mu_bound ji]
          GB order.trans[OF zero_le_power2], auto)
  qed
  also have "\<dots> = of_nat (Suc i) * (bnd * of_nat A)" unfolding sum_list_triv length_upt by simp
  also have "\<dots> = of_nat (Suc i * A) * bnd" unfolding of_nat_mult by simp
  finally show ?thesis .
qed
end

lemma increase_i_bound: assumes LLL: "LLL_bound_invariant True upw i fs" 
  and i: "i < m" 
  and upw: "upw \<Longrightarrow> i = 0" 
  and red_i: "i \<noteq> 0 \<Longrightarrow> sq_norm (gso fs (i - 1)) \<le> \<alpha> * sq_norm (gso fs i)"
shows "LLL_bound_invariant True True (Suc i) fs" 
proof -
  from bound_invD[OF LLL] have LLL: "LLL_invariant upw i fs" 
    and "f_bound True i fs" and gbnd: "g_bound fs" by auto
  hence fbnd: "f_bound True (Suc i) fs" by (auto simp: f_bound_def)
  from increase_i[OF LLL i upw red_i]
  have inv: "LLL_invariant True (Suc i) fs" and "LLL_measure (Suc i) fs < LLL_measure i fs" (is ?g2) 
    by auto
  show "LLL_bound_invariant True True (Suc i) fs" 
    by (rule bound_invI[OF inv fbnd gbnd])
qed

text \<open>Addition step preserves @{term "LLL_bound_invariant False"}\<close>

lemma basis_reduction_add_row_main_bound: assumes Linv: "LLL_bound_invariant False True i fs"
  and i: "i < m"  and j: "j < i" 
  and c: "c = floor_ceil (\<mu> fs i j)" 
  and fs': "fs' = fs[ i := fs ! i - c \<cdot>\<^sub>v fs ! j]" 
  and mu_small: "\<mu>_small_row i fs (Suc j)" 
  and mu_bnd: "\<mu>_bound_row_inner fs i (Suc j)" 
shows "LLL_bound_invariant False True i fs'"
  "\<mu>_bound_row_inner fs' i j"
proof (rule bound_invI)
  from bound_invD[OF Linv]
  have Linv: "LLL_invariant True i fs" and fbnd: "f_bound False i fs" and gbnd: "g_bound fs"
    by auto
  note main = basis_reduction_add_row_main[OF Linv i j c fs' mu_small]
  show Linv': "LLL_invariant True i fs'" by fact
  define bnd :: rat where bnd: "bnd = 4 ^ (m - 1 - Suc j) * of_nat (A ^ (m - 1) * m)" 
  note mu_bnd = mu_bnd[folded bnd]
  note inv = LLL_invD[OF Linv]
  let ?mu = "\<mu> fs"
  let ?mu' = "\<mu> fs'"
  from j have "j \<le> i" by simp
  let ?R = rat_of_int

  (* (squared) mu bound will increase at most by factor 4 *)
  have mu_bound_factor: "\<mu>_bound_row fs' (4 * bnd) i" 
  proof (intro \<mu>_bound_rowI)
    fix k
    assume ki: "k \<le> i" 
    from \<mu>_bound_rowD[OF mu_bnd] have bnd_i: "\<And> j. j \<le> i \<Longrightarrow> (?mu i j)^2 \<le> bnd" by auto
    have bnd_ik: "(?mu i k)\<^sup>2 \<le> bnd" using bnd_i[OF ki] by auto
    have bnd_ij: "(?mu i j)\<^sup>2 \<le> bnd" using bnd_i[OF \<open>j \<le> i\<close>] by auto
    from \<mu>_bound_row_1[OF mu_bnd] have bnd1: "bnd \<ge> 1" "bnd \<ge> 0" by auto
    show "(?mu' i k)\<^sup>2 \<le> 4 * bnd"
    proof (cases "k > j")
      case True
      show ?thesis
        by (subst main(5), (insert True ki i bnd1, auto)[3], intro order.trans[OF bnd_ik], auto)
    next
      case False
      hence kj: "k \<le> j" by auto
      show ?thesis
      proof (cases "k = j")
        case True 
        have small: "abs (?mu' i k) \<le> 1/2" using main(2) j unfolding True \<mu>_small_row_def by auto
        show ?thesis using mult_mono[OF small small] using bnd1 
          by (auto simp: power2_eq_square)
      next
        case False
        with kj have k_j: "k < j" by auto
        define M where "M = max (abs (?mu i k)) (max (abs (?mu i j)) (1/2))" 
        have M0: "M \<ge> 0" unfolding M_def by auto
        let ?new_mu = "?mu i k - ?R c * ?mu j k" 
        have "abs ?new_mu \<le> abs (?mu i k) + abs (?R c * ?mu j k)" by simp
        also have "\<dots> = abs (?mu i k) + abs (?R c) * abs (?mu j k)" unfolding abs_mult ..
        also have "\<dots> \<le> abs (?mu i k) + (abs (?mu i j) + 1/2) * (1/2)" 
        proof (rule add_left_mono[OF mult_mono], unfold c)
          show "\<bar>?R (floor_ceil (?mu i j))\<bar> \<le> \<bar>?mu i j\<bar> + 1 / 2" unfolding floor_ceil_def by linarith
          from inv(10)[unfolded gs.reduced_def, THEN conjunct2, rule_format, OF \<open>j < i\<close> k_j]
          show "\<bar>?mu j k\<bar> \<le> 1/2" .
        qed auto
        also have "\<dots> \<le> M + (M + M) * (1/2)" 
          by (rule add_mono[OF _ mult_right_mono[OF add_mono]], auto simp: M_def)
        also have "\<dots> = 2 * M" by auto
        finally have le: "abs ?new_mu \<le> 2 * M" .
        have "(?mu' i k)\<^sup>2 = ?new_mu\<^sup>2" 
          by (subst main(5), insert kj False i j, auto)
        also have "\<dots> \<le> (2 * M)^2" unfolding abs_le_square_iff[symmetric] using le M0 by auto
        also have "\<dots> = 4 * M^2" by simp
        also have "\<dots> \<le> 4 * bnd" 
        proof (rule mult_left_mono)            
          show "M^2 \<le> bnd" using bnd_ij bnd_ik bnd1 unfolding M_def
            by (auto simp: max_def power2_eq_square)
        qed auto
        finally show ?thesis .
      qed
    qed
  qed
  also have "4 * bnd = (4 ^ (1 + (m - 1 - Suc j)) * of_nat (A ^ (m - 1) * m))" unfolding bnd 
    by simp
  also have "1 + (m - 1 - Suc j) = m - 1 - j" using i j by auto
  finally show bnd: "\<mu>_bound_row_inner fs' i j" by auto

  show gbnd: "g_bound fs'" using gbnd unfolding g_bound_def
    using main(4) by auto

  note inv' = LLL_invD[OF Linv']
  show "f_bound False i fs'"
    unfolding f_bound_def
  proof (intro allI impI, goal_cases)
    case (1 jj)
    show ?case
    proof (cases "jj = i")
      case False
      with 1 fbnd[unfolded f_bound_def] have "\<parallel>fs ! jj\<parallel>\<^sup>2 \<le> int (A * m)" by auto
      thus ?thesis unfolding fs' using False 1 inv(2-) by auto
    next
      case True        
      have "of_int \<parallel>fs' ! i\<parallel>\<^sup>2 = \<parallel>RAT fs' ! i\<parallel>\<^sup>2" using i inv' by (auto simp: sq_norm_of_int)
      also have "... \<le> rat_of_nat (Suc i * A) * (4 ^ (m - 1 - j) * rat_of_nat (A ^ (m - 1) * m))" 
        using sq_norm_fs_mu_g_bound[OF inv'(1,6) i bnd gbnd] i inv'
        unfolding sq_norm_of_int[symmetric]
        by (auto simp: ac_simps)
      also have "\<dots> = rat_of_int ( int (Suc i * A) * (4 ^ (m - 1 - j) * (A ^ (m - 1) * m)))"
        by simp
      finally have "\<parallel>fs' ! i\<parallel>\<^sup>2 \<le> int (Suc i * A) * (4 ^ (m - 1 - j) * (A ^ (m - 1) * m))" by linarith
      also have "\<dots> = int (Suc i) * 4 ^ (m - 1 - j) * (int A ^ (Suc (m - 1))) * int m" 
        unfolding of_nat_mult by (simp add: ac_simps)
      also have "\<dots> = int (Suc i) * 4 ^ (m - 1 - j) * int A ^ m * int m" using i j by simp
      also have "\<dots> \<le> int m * 4 ^ (m - 1) * int A ^ m * int m" 
        by (rule mult_right_mono[OF mult_right_mono[OF mult_mono[OF _ pow_mono_exp]]], insert i, auto)
      finally have "\<parallel>fs' ! i\<parallel>\<^sup>2 \<le> int (4 ^ (m - 1) * A ^ m * m * m)" unfolding of_nat_mult by (simp add: ac_simps)
      thus ?thesis unfolding True by auto
    qed
  qed
qed
end

context LLL_with_assms
begin

subsubsection \<open>@{const LLL_bound_invariant} is maintained during execution of @{const basic_basis_reduction}\<close>

lemma basis_reduction_add_rows_enter_bound: assumes binv: "LLL_bound_invariant True True i fs"
  and i: "i < m"   
shows "LLL_bound_invariant False True i fs"
  "\<mu>_bound_row_inner fs i i" 
proof (rule bound_invI)
  from bound_invD[OF binv]
  have Linv: "LLL_invariant True i fs" (is ?g1) and fbnd: "f_bound True i fs" 
    and gbnd: "g_bound fs" by auto
  note inv = LLL_invD[OF Linv]
  show "LLL_invariant True i fs" by fact
  show fbndF: "f_bound False i fs" using f_bound_True_arbitrary[OF fbnd] .
  have A0: "A > 0" using LLL_inv_A_pos[OF Linv gbnd] i by auto
  {
    fix j
    assume ji: "j < i" 
    have "(\<mu> fs i j)\<^sup>2 \<le> gs.Gramian_determinant (RAT fs) j * \<parallel>RAT fs ! i\<parallel>\<^sup>2"
    proof (rule gs.mu_bound_Gramian_determinant[OF inv(1-2) _ ji i], goal_cases)
      case (1 j i)
      thus ?case using inv(4)[OF 1(2)] inv(6) by auto
    qed
    also have "gs.Gramian_determinant (RAT fs) j = of_int (d fs j)" unfolding d_def 
      by (subst of_int_Gramian_determinant, insert ji i inv(2-), auto simp: set_conv_nth)
    also have "\<parallel>RAT fs ! i\<parallel>\<^sup>2 = of_int \<parallel>fs ! i\<parallel>\<^sup>2" using i inv(2-) by (auto simp: sq_norm_of_int)
    also have "of_int (d fs j) * \<dots> \<le> rat_of_nat (A^j) * of_int \<parallel>fs ! i\<parallel>\<^sup>2"
      by (rule mult_right_mono, insert ji i d_approx[OF Linv gbnd, of j], auto)
    also have "\<dots> \<le> rat_of_nat (A^(m-2)) * of_int (int (A * m))" 
      by (intro mult_mono, unfold of_nat_le_iff of_int_le_iff, rule pow_mono_exp,
      insert fbnd[unfolded f_bound_def, rule_format, of i] A0 ji i, auto)
    also have "\<dots> = rat_of_nat (A^(m-2) * A * m)" by simp
    also have "A^(m-2) * A = A^(Suc (m - 2))" by simp
    also have "Suc (m - 2) = m - 1" using ji i by auto
    finally have "(\<mu> fs i j)\<^sup>2 \<le> of_nat (A ^ (m - 1) * m)" .
  } note mu_bound = this
  show mu_bnd: "\<mu>_bound_row_inner fs i i"
  proof (rule \<mu>_bound_rowI)
    fix j
    assume j: "j \<le> i" 
    have "(\<mu> fs i j)\<^sup>2 \<le> 1 * of_nat (A ^ (m - 1) * m)" 
    proof (cases "j = i")
      case False
      with mu_bound[of j] j show ?thesis by auto
    next
      case True
      show ?thesis unfolding True gs.\<mu>.simps using i A0 by auto
    qed
    also have "\<dots> \<le> 4 ^ (m - 1 - i) * of_nat (A ^ (m - 1) * m)" 
      by (rule mult_right_mono, auto)
    finally show "(\<mu> fs i j)\<^sup>2 \<le> 4 ^ (m - 1 - i) * rat_of_nat (A ^ (m - 1) * m)" . 
  qed
  show "g_bound fs" by fact 
qed

lemma basis_basis_reduction_add_rows_loop_leave:
  assumes binv: "LLL_bound_invariant False True i fs" 
  and mu_small: "\<mu>_small_row i fs 0"
  and mu_bnd: "\<mu>_bound_row_inner fs i 0" 
  and i: "i < m" 
shows "LLL_bound_invariant True False i fs" 
proof -
  note Linv = bound_invD(1)[OF binv]
  from mu_small have mu_small: "\<mu>_small fs i" unfolding \<mu>_small_row_def \<mu>_small_def by auto
  note inv = LLL_invD[OF Linv]
  note fbnd = bound_invD(2)[OF binv]
  note gbnd = bound_invD(3)[OF binv]
  {
    fix ii
    assume ii: "ii < m" 
    have "\<parallel>fs ! ii\<parallel>\<^sup>2 \<le> int (A * m)" 
    proof (cases "ii = i")
      case False
      thus ?thesis using ii fbnd[unfolded f_bound_def] by auto
    next
      case True
      have row: "\<mu>_bound_row fs 1 i" 
      proof (intro \<mu>_bound_rowI)
        fix j
        assume j: "j \<le> i" 
        from mu_small[unfolded \<mu>_small_def, rule_format, of j]
        have "abs (\<mu> fs i j) \<le> 1" using j unfolding \<mu>_small_def by (cases "j = i", force simp: gs.\<mu>.simps, auto)
        from mult_mono[OF this this] show "(\<mu> fs i j)\<^sup>2 \<le> 1" by (auto simp: power2_eq_square)
      qed
      have "rat_of_int \<parallel>fs ! i\<parallel>\<^sup>2 \<le> rat_of_int (int (Suc i * A))" 
        using sq_norm_fs_mu_g_bound[OF inv(1,6) i row gbnd] by auto
      hence "\<parallel>fs ! i\<parallel>\<^sup>2 \<le> int (Suc i * A)" by linarith
      also have "\<dots> = int A * int (Suc i)" unfolding of_nat_mult by simp
      also have "\<dots> \<le> int A * int m" 
        by (rule mult_left_mono, insert i, auto)
      also have "\<dots> = int (A * m)" by simp
      finally show ?thesis unfolding True .
    qed
  }
  hence f_bound: "f_bound True i fs" unfolding f_bound_def by auto
  with binv show ?thesis using basis_reduction_add_row_done[OF Linv i assms(2)] 
    by (auto simp: LLL_bound_invariant_def)
qed


lemma basic_basis_reduction_add_rows_loop_bound: assumes
  binv: "LLL_bound_invariant False True i fs" 
  and mu_small: "\<mu>_small_row i fs j"
  and mu_bnd: "\<mu>_bound_row_inner fs i j" 
  and res: "basic_basis_reduction_add_rows_loop i fs j = fs'" 
  and i: "i < m" 
  and j: "j \<le> i" 
shows "LLL_bound_invariant True False i fs'" 
  using assms
proof (induct j arbitrary: fs)
  case (0 fs)
  note binv = 0(1)
  from basis_basis_reduction_add_rows_loop_leave[OF 0(1-3) i] 0(4)
  show ?case by auto
next
  case (Suc j fs)
  note binv = Suc(2)
  note Linv = bound_invD(1)[OF binv]
  from Suc have j: "j < i" by auto
  let ?c = "floor_ceil (\<mu> fs i j)" 
  note step = basis_reduction_add_row_main_bound[OF Suc(2) i j refl refl Suc(3-4)]
  note step' = basis_reduction_add_row_main(1,2,3)[OF Linv i j refl refl Suc(3)]
  show ?case
  proof (cases "?c = 0")
    case True
    note inv = LLL_invD[OF Linv]
    from inv(5)[OF i] inv(5)[of j] i j
    have id: "fs[i := fs ! i - 0 \<cdot>\<^sub>v fs ! j] = fs" 
      by (intro nth_equalityI, insert inv i, auto)
    show ?thesis 
      by (rule Suc(1), insert step step' id True Suc(2-), auto)
  next
    case False
    show ?thesis using Suc(1)[OF step(1) step'(2) step(2)] Suc(2-) False step'(3) by auto
  qed
qed

lemma basic_basis_reduction_add_rows_bound: assumes 
  binv: "LLL_bound_invariant True upw i fs" 
  and res: "basic_basis_reduction_add_rows upw i fs = fs'" 
  and i: "i < m" 
shows "LLL_bound_invariant True False i fs'"  
proof -
  note def = basic_basis_reduction_add_rows_def
  show ?thesis
  proof (cases upw)
    case False
    with res binv show ?thesis by (simp add: def)
  next
    case True
    with binv have binv: "LLL_bound_invariant True True i fs" by auto
    note start = basis_reduction_add_rows_enter_bound[OF this i]
    from res[unfolded def] True 
    have "basic_basis_reduction_add_rows_loop i fs i = fs'" by auto
    from basic_basis_reduction_add_rows_loop_bound[OF start(1) \<mu>_small_row_refl start(2) this i le_refl]      
    show ?thesis by auto
  qed
qed


lemma basic_basis_reduction_swap_bound: assumes 
  binv: "LLL_bound_invariant True False i fs" 
  and res: "basic_basis_reduction_swap i fs = (upw',i',fs')" 
  and cond: "sq_norm (gso fs (i - 1)) > \<alpha> * sq_norm (gso fs i)" 
  and i: "i < m" "i \<noteq> 0" 
shows "LLL_bound_invariant True upw' i' fs'" 
proof (rule bound_invI)
  note Linv = bound_invD(1)[OF binv]
  from basic_basis_reduction_swap[OF Linv res cond i]
  show Linv': "LLL_invariant upw' i' fs'" by auto
  from res[unfolded basic_basis_reduction_swap_def]
  have id: "i' = i - 1" "fs' = fs[i := fs ! (i - 1), i - 1 := fs ! i]" by auto
  from LLL_invD(6)[OF Linv] i
  have choice: "fs' ! k = fs ! k \<or> fs' ! k = fs ! i \<or> fs' ! k = fs ! (i - 1)" for k 
    unfolding id by (cases "k = i"; cases "k = i - 1", auto) 
  from bound_invD(2)[OF binv] i 
  show "f_bound True i' fs'" unfolding id(1) f_bound_def
  proof (intro allI impI, goal_cases)
    case (1 k)
    thus ?case using choice[of k] by auto
  qed

  let ?g1 = "\<lambda> i. gso fs i"
  let ?g2 = "\<lambda> i. gso fs' i" 
  let ?n1 = "\<lambda> i. sq_norm (?g1 i)"
  let ?n2 = "\<lambda> i. sq_norm (?g2 i)" 
  from bound_invD(3)[OF binv, unfolded g_bound_def]
  have short: "\<And> k. k < m \<Longrightarrow> ?n1 k \<le> of_nat A" by auto
  from short[of "i - 1"] i 
  have short_im1: "?n1 (i - 1) \<le> of_nat A" by auto
  note swap = basis_reduction_swap[OF Linv i cond id(2)]
  note updates = swap(3,4)
  note Linv' = swap(1)
  note inv' = LLL_invD[OF Linv']
  note inv = LLL_invD[OF Linv]
  let ?mu1 = "\<mu> fs" 
  let ?mu2 = "\<mu> fs'" 
  let ?mu = "?mu1 i (i - 1)" 
  from LLL_invD[OF Linv] have "\<mu>_small fs i" by blast
  from this[unfolded \<mu>_small_def] i have mu: "abs ?mu \<le> 1/2" by auto
  have "?n2 (i - 1) = ?n1 i + ?mu * ?mu * ?n1 (i - 1)" 
   by (subst updates(2), insert i, auto)
  also have "\<dots> = inverse \<alpha> * (\<alpha> * ?n1 i) + (?mu * ?mu) * ?n1 (i - 1)" 
    using \<alpha> by auto
  also have "\<dots> \<le> inverse \<alpha> * ?n1 (i - 1) + (abs ?mu * abs ?mu) * ?n1 (i - 1)"
    by (rule add_mono[OF mult_left_mono], insert cond \<alpha>, auto)
  also have "\<dots> = (inverse \<alpha> + abs ?mu * abs ?mu) * ?n1 (i - 1)" by (auto simp: field_simps)
  also have "\<dots> \<le> (inverse \<alpha> + (1/2) * (1/2)) * ?n1 (i - 1)" 
    by (rule mult_right_mono[OF add_left_mono[OF mult_mono]], insert mu, auto)  
  also have "inverse \<alpha> + (1/2) * (1/2) = reduction" unfolding reduction_def using \<alpha>0 
    by (auto simp: field_simps)
  also have "\<dots> * ?n1 (i - 1) \<le> 1 * ?n1 (i - 1)" 
    by (rule mult_right_mono, auto simp: reduction)
  finally have n2im1: "?n2 (i - 1) \<le> ?n1 (i - 1)" by simp
  show "g_bound fs'" unfolding g_bound_def
  proof (intro allI impI)
    fix k 
    assume km: "k < m" 
    consider (ki) "k = i" | (im1) "k = i - 1" | (other) "k \<noteq> i" "k \<noteq> i-1" by blast
    thus "?n2 k \<le> of_nat A"
    proof cases
      case other
      from short[OF km] have "?n1 k \<le> of_nat A" by auto
      also have "?n1 k = ?n2 k" using km other
        by (subst updates(2), auto)
      finally show ?thesis by simp
    next
      case im1
      have "?n2 k = ?n2 (i - 1)" unfolding im1 ..
      also have "\<dots> \<le> ?n1 (i - 1)" by fact
      also have "\<dots> \<le> of_nat A" using short_im1 by auto
      finally show ?thesis by simp
    next
      case ki
      have "?n2 k = ?n2 i" unfolding ki using i by auto
      also have "\<dots> \<le> ?n1 (i - 1)" 
      proof -
        let ?f1 = "\<lambda> i. RAT fs ! i"
        let ?f2 = "\<lambda> i. RAT fs' ! i" 
        define u where "u = gs.sumlist (map (\<lambda>j. ?mu1 (i - 1) j \<cdot>\<^sub>v ?g1 j) [0..<i - 1])" 
        define U where "U = ?f1 ` {0 ..< i - 1} \<union> {?f1 i}" 
        have g2i: "?g2 i \<in> Rn" using i inv' by simp
        have U: "U \<subseteq> Rn" unfolding U_def using inv i by auto
        have uU: "u \<in> gs.span U"
        proof -
          have im1: "i - 1 \<le> m" using i by auto
          have G1: "?g1 ` {0..< i - 1} \<subseteq> Rn" using inv(5) i by auto
          have "u \<in> gs.span (?g1 ` {0 ..< i - 1})" unfolding u_def 
            by (rule gs.sumlist_in_span[OF G1], unfold set_map, insert G1,
              auto intro!: gs.smult_in_span intro: gs.span_mem)
          also have "gs.span (?g1 ` {0 ..< i - 1}) = gs.span (?f1 ` {0 ..< i - 1})" 
            unfolding gs.partial_span[OF inv(1-2) im1]
            by (rule arg_cong[of _ _ gs.span], subst nth_image[symmetric], insert i inv(6), auto)
          also have "\<dots> \<subseteq> gs.span U" unfolding U_def 
            by (rule gs.span_is_monotone, auto)
          finally show ?thesis .
        qed
        from i have im1: "i - 1 < m" by auto
        have u: "u \<in> Rn" using uU U by simp
        have id_u: "u + (?g1 (i - 1) - ?g2 i) = u + ?g1 (i - 1) - ?g2 i" 
          using u g2i inv(5)[OF im1] by auto
        have list_id: "[0..<Suc (i - 1)] = [0..< i - 1] @ [i - 1]" 
          "map f [x] = [f x]" for f x by auto
        from gs.gso_oc_projection_span(2)[OF inv'(1-2) i(1)]
        have "gs.is_oc_projection (?g2 i) (gs.span (gs.gso (RAT fs') ` {0 ..< i}))  (?f1 (i - 1))" 
          unfolding id(2) using inv(6) i by simp
        also have "?f1 (i - 1) = u + ?g1 (i - 1) " 
          unfolding gs.fi_is_sum_of_mu_gso[OF inv(1-2) im1] list_id map_append u_def 
          by (subst gs.M.sumlist_snoc, insert i, auto simp: gs.\<mu>.simps intro!: inv(5))
        also have "gs.span (gs.gso (RAT fs') ` {0 ..< i}) = gs.span (set (take i (RAT fs')))" 
          unfolding gs.partial_span[OF inv'(1-2) \<open>i \<le> m\<close>] ..
        also have "set (take i (RAT fs')) = ?f2 ` {0 ..< i}" using inv'(6) i 
          by (subst nth_image[symmetric], auto)
        also have "{0 ..< i} = {0 ..< i - 1} \<union> {(i - 1)}" using i by auto
        also have "?f2 ` \<dots> = ?f2 ` {0 ..< i - 1} \<union> {?f2 (i - 1)}" by auto
        also have "\<dots> = U" unfolding U_def id(2) 
          by (rule arg_cong2[of _ _ _ _ "(\<union>)"], insert i inv(6), force+)
        finally have "gs.is_oc_projection (?g2 i) (gs.span U) (u + ?g1 (i - 1))" .        
        hence proj: "gs.is_oc_projection (?g2 i) (gs.span U) (?g1 (i - 1))"
          unfolding gs.is_oc_projection_def using gs.span_add[OF U uU, of "?g1 (i - 1) - ?g2 i"] 
          inv(5)[OF im1] g2i u id_u by (auto simp: U)
        from gs.is_oc_projection_sq_norm[OF this gs.span_is_subset2[OF U]  inv(5)[OF im1]]
        show "?n2 i \<le> ?n1 (i - 1)" .
      qed
      also have "\<dots> \<le> of_nat A" by fact
      finally show ?thesis .
    qed
  qed
qed

lemma basic_basis_reduction_step_bound: assumes 
  binv: "LLL_bound_invariant True upw i fs" 
  and res: "basic_basis_reduction_step upw i fs = (upw',i',fs')" 
  and i: "i < m" 
shows "LLL_bound_invariant True upw' i' fs'" 
proof -
  note def = basic_basis_reduction_step_def
  obtain fs'' where fs'': "basic_basis_reduction_add_rows upw i fs = fs''" by auto
  show ?thesis
  proof (cases "i = 0")
    case True
    from increase_i_bound[OF binv i True] res True
    show ?thesis by (auto simp: def)
  next
    case False
    hence id: "(i = 0) = False" by auto
    note res = res[unfolded def id if_False fs'' Let_def]
    let ?x = "sq_norm (gso fs'' (i - 1))" 
    let ?y = "\<alpha> * sq_norm (gso fs'' i)" 
    from basic_basis_reduction_add_rows_bound[OF binv fs'' i]
    have binv: "LLL_bound_invariant True False i fs''" by auto
    show ?thesis
    proof (cases "?x \<le> ?y")
      case True
      from increase_i_bound[OF binv i _ True] True res
      show ?thesis by auto
    next
      case gt: False
      hence "?x > ?y" by auto
      from basic_basis_reduction_swap_bound[OF binv _ this i False] gt res
      show ?thesis by auto
    qed
  qed
qed

lemma basic_basis_reduction_main_bound: assumes "LLL_bound_invariant True upw i fs" 
  and res: "basic_basis_reduction_main (upw,i,fs) = fs'" 
shows "LLL_bound_invariant True True m fs'" 
  using assms
proof (induct "LLL_measure i fs" arbitrary: i fs upw rule: less_induct)
  case (less i fs upw)
  have id: "LLL_bound_invariant True upw i fs = True" using less by auto
  note res = less(3)[unfolded basic_basis_reduction_main.simps[of upw i fs] id]
  note inv = less(2)
  note IH = less(1)
  note Linv = bound_invD(1)[OF inv]
  show ?case
  proof (cases "i < m")
    case i: True
    obtain i' fs' upw' where step: "basic_basis_reduction_step upw i fs = (upw',i',fs')" 
      (is "?step = _") by (cases ?step, auto)
    note decrease = basic_basis_reduction_step(2)[OF Linv step i]
    from IH[OF decrease basic_basis_reduction_step_bound(1)[OF inv step i]] res[unfolded step] i Linv
    show ?thesis by auto
  next
    case False
    with LLL_invD[OF Linv] have i: "i = m" upw by auto
    with False res inv show ?thesis by auto
  qed
qed

lemma LLL_inv_initial_state_bound: "LLL_bound_invariant True True 0 fs_init" 
proof (intro bound_invI[OF LLL_inv_initial_state _ g_bound_fs_init])
  {
    fix i
    assume i: "i < m" 
    let ?N = "map (nat o sq_norm) fs_init"
    let ?r = rat_of_int
    from i have mem: "nat (sq_norm (fs_init ! i)) \<in> set ?N" using fs_init len unfolding set_conv_nth by force
    from mem_set_imp_le_max_list[OF _ mem]
    have FA: "nat (sq_norm (fs_init ! i)) \<le> A" unfolding A_def by force
    hence "\<parallel>fs_init ! i\<parallel>\<^sup>2 \<le> int A" using i by auto
    also have "\<dots> \<le> int (A * m)" using i by fastforce
    finally have f_bnd:  "\<parallel>fs_init ! i\<parallel>\<^sup>2 \<le> int (A * m)" .
  }
  thus "f_bound True 0 fs_init" unfolding f_bound_def by auto
qed

lemma basic_basis_reduction: assumes res: "basic_basis_reduction = fs" 
  shows "LLL_bound_invariant True True m fs" 
  using basic_basis_reduction_main_bound[OF LLL_inv_initial_state_bound res[unfolded basic_basis_reduction_def]] .


subsubsection \<open>Bound extracted from @{term LLL_bound_invariant}.\<close>

lemma A_le_MMn: assumes m0: "m \<noteq> 0" 
  shows "A \<le> nat M * nat M * n" 
  unfolding A_def
proof (rule max_list_le, unfold set_map o_def)
  fix ni
  assume "ni \<in> (\<lambda>x. nat \<parallel>x\<parallel>\<^sup>2) ` set fs_init" 
  then obtain fi where ni: "ni = nat (\<parallel>fi\<parallel>\<^sup>2)" and fi: "fi \<in> set fs_init" by auto
  from fi len obtain i where fii: "fi = fs_init ! i" and i: "i < m" unfolding set_conv_nth by auto
  from fi fs_init have fi: "fi \<in> carrier_vec n" by auto
  let ?set = "{\<bar>fs_init ! i $v j\<bar> |i j. i < m \<and> j < n} \<union> {0}" 
  have id: "?set = (\<lambda> (i,j). abs (fs_init ! i $ j)) ` ({0..<m} \<times> {0..<n}) \<union> {0}" 
    by force
  have fin: "finite ?set" unfolding id by auto
  { 
    fix j assume "j < n" 
    hence "M \<ge> \<bar>fs_init ! i $ j\<bar>" unfolding M_def using i
      by (intro Max_ge[of _ "abs (fs_init ! i $ j)"], intro fin, auto)
  } note M = this
  from Max_ge[OF fin, of 0] have M0: "M \<ge> 0" unfolding M_def by auto
  have "ni = nat (\<parallel>fi\<parallel>\<^sup>2)" unfolding ni by auto
  also have "\<dots> \<le> nat (int n * \<parallel>fi\<parallel>\<^sub>\<infinity>\<^sup>2)" using sq_norm_vec_le_linf_norm[OF fi]
    by (intro nat_mono, auto)
  also have "\<dots> = n * nat (\<parallel>fi\<parallel>\<^sub>\<infinity>\<^sup>2)"
    by (simp add: nat_mult_distrib)
  also have "\<dots> \<le> n * nat (M^2)" 
  proof (rule mult_left_mono[OF nat_mono])
    have fi: "\<parallel>fi\<parallel>\<^sub>\<infinity> \<le> M" unfolding linf_norm_vec_def    
    proof (rule max_list_le, unfold set_append set_map, rule ccontr)
      fix x
      assume "x \<in> abs ` set (list_of_vec fi) \<union> set [0]" and xM: "\<not> x \<le> M"  
      with M0 obtain fij where fij: "fij \<in> set (list_of_vec fi)" and x: "x = abs fij" by auto
      from fij fi obtain j where j: "j < n" and fij: "fij = fi $ j" 
        unfolding set_list_of_vec vec_set_def by auto
      from M[OF j] xM[unfolded x fij fii] show False by auto
    qed auto                
    show "\<parallel>fi\<parallel>\<^sub>\<infinity>\<^sup>2 \<le> M^2" unfolding abs_le_square_iff[symmetric] using fi 
      using linf_norm_vec_ge_0[of fi] by auto
  qed auto
  finally show "ni \<le> nat M * nat M * n" using M0 
    by (subst nat_mult_distrib[symmetric], auto simp: power2_eq_square ac_simps)
qed (insert m0 len, auto)

fun f_bnd :: "bool \<Rightarrow> nat" where
  "f_bnd False = 2 ^ (m - 1) * A ^ m * m" 
| "f_bnd True = A * m" 

lemma f_bnd_mono: "f_bnd outside \<le> f_bnd False" 
proof (cases outside)
  case out: True
  show ?thesis
  proof (cases "A = 0 \<or> m = 0")
    case True
    thus ?thesis using out by auto
  next
    case False
    hence 0: "A > 0" "m > 0" by auto
    let ?num = "(2 ^ (m - 1) * A ^ m)" 
    have "(A * m) * 1 \<le> (A * m) * (2 ^ (m - 1) * A ^ (m - 1))" 
      by (rule mult_left_mono, insert 0, auto)
    also have "\<dots> = 2 ^ (m - 1) * A ^ (Suc (m - 1)) * m " by simp
    also have "Suc (m - 1) = m" using 0 by simp
    finally show ?thesis using out by auto
  qed
qed auto 

lemma aux_bnd_mono: "A * m \<le> (4 ^ (m - 1) * A ^ m * m * m)" 
proof (cases "A = 0 \<or> m = 0")
  case False
  hence 0: "A > 0" "m > 0" by auto
  let ?num = "(4 ^ (m - 1) * A ^ m * m * m)" 
  have "(A * m) * 1 \<le> (A * m) * (4 ^ (m - 1) * A ^ (m - 1) * m)" 
    by (rule mult_left_mono, insert 0, auto)
  also have "\<dots> = 4 ^ (m - 1) * A ^ (Suc (m - 1)) * m * m" by simp
  also have "Suc (m - 1) = m" using 0 by simp
  finally show "A * m \<le> ?num" by simp
qed auto

lemma LLL_invariant_f_bound: 
  assumes binv: "LLL_bound_invariant outside upw k fs" 
  and i: "i < m" and j: "j < n" 
shows "\<bar>fs ! i $ j\<bar> \<le> f_bnd outside" 
proof -
  from bound_invD[OF binv]
  have inv: "LLL_invariant upw k fs" 
    and fbnd: "f_bound outside k fs" 
    and gbnd: "g_bound fs" by auto
  from LLL_inv_A_pos[OF inv gbnd] i have A0: "A > 0" by auto
  note inv = LLL_invD[OF inv] 
  from inv i have fsi: "fs ! i \<in> carrier_vec n" by auto
  have one: "\<bar>fs ! i $ j\<bar>^1 \<le> \<bar>fs ! i $ j\<bar>^2" 
    by (cases "fs ! i $ j \<noteq> 0", intro pow_mono_exp, auto)
  let ?num = "(4 ^ (m - 1) * A ^ m * m * m)" 
  let ?sq_bnd = "if i \<noteq> k \<or> outside then int (A * m) else int ?num" 
  have "\<bar>fs ! i $ j\<bar>^2 \<le> \<parallel>fs ! i\<parallel>\<^sup>2" using fsi j by (metis vec_le_sq_norm)
  also have "\<dots> \<le> ?sq_bnd" 
    using fbnd[unfolded f_bound_def, rule_format, OF i] by auto
  finally have two: "(fs ! i $ j)^2 \<le> ?sq_bnd" by simp
  show ?thesis
  proof (cases outside)
    case True
    with one two show ?thesis by auto
  next
    case False
    let ?num2 = "(2 ^ (m - 1) * A ^ m * m)" 
    have four: "(4 :: nat) = 2^2" by auto
    have "(fs ! i $ j)^2 \<le> int (max (A * m) ?num)" 
      by (rule order.trans[OF two], auto simp: of_nat_mult[symmetric] simp del: of_nat_mult)
    also have "max (A * m) ?num = ?num" using aux_bnd_mono by presburger 
    also have "int ?num = int ?num * 1" by simp
    also have "\<dots> \<le> int ?num * A ^ m" 
      by (rule mult_left_mono, insert A0, auto)
    also have "\<dots> = int (?num * A ^ m)" by simp
    also have "?num * A ^ m = ?num2^2" unfolding power2_eq_square four power_mult_distrib
      by simp
    also have "int \<dots> = (int ?num2)^2" by simp
    finally have "(fs ! i $v j)\<^sup>2 \<le> (int (f_bnd outside))\<^sup>2" using False by simp
    thus ?thesis unfolding abs_le_square_iff[symmetric] by simp 
  qed
qed

lemma LLL_invariant_gso_bound:
  assumes binv: "LLL_bound_invariant outside upw k fs" 
  and i: "i < m" and j: "j < n" 
  and quot: "quotient_of (gso fs i $ j) = (num, denom)" 
shows "\<bar>num\<bar>   \<le> A ^ m" 
  and "\<bar>denom\<bar> \<le> A ^ m"
proof -
  from bound_invD[OF binv]
  have inv: "LLL_invariant upw k fs" 
    and gbnd: "g_bound fs" by auto
  note * = LLL_invD[OF inv]
  interpret gs: gram_schmidt_rat n .
  note d_approx[OF inv gbnd i, unfolded d_def]  
  let ?r = "rat_of_int"
  have int: "(gs.Gramian_determinant (RAT fs) i \<cdot>\<^sub>v (gso fs i)) $v j \<in> \<int>"
  proof -
    have "of_int_hom.vec_hom (fs ! j) $v i \<in> \<int>" if "i < n" "j < m" for i j
      using that assms * by (intro vec_hom_Ints) (auto)
    then show ?thesis
      using * gs.gso_connect snd_gram_schmidt_int assms
      by (intro gs.Gramian_determinant_times_gso_Ints) (auto)
  qed
  have gsi: "gso fs i \<in> Rn" using *(5)[OF i] .
  have gs_sq: "\<bar>(gso fs i $ j)\<bar>\<^sup>2 \<le> rat_of_nat A"
    by(rule order_trans, rule vec_le_sq_norm[of _ n])
      (use gsi assms gbnd * LLL.g_bound_def in auto)
  from i have "m * m \<noteq> 0"
    by auto
  then have A0: "A \<noteq> 0"
    using less_le_trans[OF LLL_D_pos[OF inv] D_approx[OF inv gbnd]] by auto
  have "\<bar>(gso fs i $ j)\<bar> \<le> max 1 \<bar>(gso fs i $ j)\<bar>"
    by simp
  also have "\<dots> \<le> (max 1 \<bar>gso fs i $ j\<bar>)\<^sup>2"
    by (rule self_le_power, auto) 
  also have "\<dots> \<le> of_nat A"
    using gs_sq A0 unfolding max_def by auto
  finally have gs_bound: "\<bar>(gso fs i $ j)\<bar> \<le> of_nat A" .
  have "gs.Gramian_determinant (RAT fs) i = rat_of_int (gs.Gramian_determinant fs i)"
    using  assms *(4-6) carrier_vecD nth_mem by (intro of_int_Gramian_determinant) (simp, blast)
  with int have "(of_int (d fs i) \<cdot>\<^sub>v gso fs i) $v j \<in> \<int>"
    unfolding d_def by simp
  also have "(of_int (d fs i) \<cdot>\<^sub>v gso fs i) $v j = of_int (d fs i) * (gso fs i $ j)"
    using gsi i j by auto
  finally have l: "of_int (d fs i) * gso fs i $v j \<in> \<int>"
    by auto
  have num: "rat_of_int \<bar>num\<bar> \<le> of_int (d fs i * int A)" and denom: "denom \<le> d fs i"
    using quotient_of_bounds[OF quot l LLL_d_pos[OF inv] gs_bound] i by auto
  from num have num: "\<bar>num\<bar> \<le> d fs i * int A"
    by linarith
  from d_approx[OF inv gbnd i] have d: "d fs i \<le> int (A ^ i)"
    by linarith
  from denom d have denom: "denom \<le> int (A ^ i)"
    by auto
  note num also have "d fs i * int A \<le> int (A ^ i) * int A" 
    by (rule mult_right_mono[OF d], auto)
  also have "\<dots> = int (A ^ (Suc i))"
    by simp
  finally have num: "\<bar>num\<bar> \<le> int (A ^ (i + 1))"
    by auto
  {
    fix jj
    assume "jj \<le> i + 1" 
    with i have "jj \<le> m" by auto
    from pow_mono_exp[OF _ this, of A] A0
    have "A^jj \<le> A^m" by auto
    hence "int (A^jj) \<le> int (A^m)" by linarith
  } note j_m = this
  have "\<bar>denom\<bar> = denom"
    using quotient_of_denom_pos[OF quot] by auto
  also have "\<dots> \<le> int (A ^ i)"
    by fact 
  also have "\<dots> \<le> int (A ^ m)"
    by (rule j_m, auto)
  finally show "\<bar>denom\<bar> \<le> int (A ^ m)"
    by auto
  show "\<bar>num\<bar> \<le> int (A ^ m)"
    using j_m[of "i+1"] num by auto
qed

lemma LLL_invariant_mu_bound: 
  assumes binv: "LLL_bound_invariant outside upw k fs" 
  and i: "i < m"                 
  and quot: "quotient_of (\<mu> fs i j) = (num, denom)" 
shows "\<bar>num\<bar>   \<le> A ^ (2 * m) * 2 ^ m * m" 
  and "\<bar>denom\<bar> \<le> A ^ m" 
proof (atomize(full))
  from bound_invD[OF binv]
  have inv: "LLL_invariant upw k fs"
     and fbnd: "f_bound outside k fs"
     and gbnd: "g_bound fs" by auto
  from LLL_inv_A_pos[OF inv gbnd] i have A: "A > 0" by auto 
  note * = LLL_invD[OF inv]
  let ?mu = "\<mu> fs i j" 
  interpret gs: gram_schmidt_rat n .
  show "\<bar>num\<bar> \<le> A ^ (2 * m) * 2 ^ m * m \<and> \<bar>denom\<bar> \<le> A ^ m" 
  proof (cases "j < i")
    case j: True
    from j i have jm: "j < m" by auto
    from quotient_of_square[OF quot] 
    have quot_sq: "quotient_of (?mu^2) = (num * num, denom * denom)" 
      unfolding power2_eq_square by auto
    from d_approx[OF inv gbnd jm]
    have dj: "d fs j \<le> int (A ^ j)" by linarith
    from LLL_d_pos[OF inv, of "Suc j"] i j have dsj: "0 < d fs (Suc j)" by auto
    hence d_pos: "0 < (d fs (Suc j))^2" by auto
    from d_approx[OF inv gbnd, of "Suc j"] j i 
    have "rat_of_int (d fs (Suc j)) \<le> of_nat (A ^ Suc j)" 
      by auto
    hence d_j_bound: "d fs (Suc j) \<le> int (A^Suc j)" by linarith
    let ?num = "4 ^ (m - 1) * A ^ m * m * m" 
    let ?bnd = "A^(m - 1) * 2 ^ (m - 1) * m" 
    from fbnd[unfolded f_bound_def, rule_format, OF i]
      aux_bnd_mono[folded of_nat_le_iff[where ?'a = int]]
    have sq_f_bnd: "sq_norm (fs ! i) \<le> int ?num" by (auto split: if_splits)
    have four: "(4 :: nat) = 2^2" by auto
    have "?mu^2 \<le> (gs.Gramian_determinant (RAT fs) j) * sq_norm (RAT fs ! i)"
      by (rule gs.mu_bound_Gramian_determinant[OF *(1-2) _ j i], insert *(3,6) j i, auto simp: set_conv_nth)
    also have "sq_norm (RAT fs ! i) = of_int (sq_norm (fs ! i))" 
      unfolding sq_norm_of_int[symmetric] using *(6) i by auto
    also have "(gs.Gramian_determinant (RAT fs) j) = of_int (d fs j)" 
      unfolding d_def by (rule of_int_Gramian_determinant, insert i j *(3,6), auto simp: set_conv_nth)
    also have "\<dots> * of_int (sq_norm (fs ! i)) = of_int (d fs j * sq_norm (fs ! i))" by simp 
    also have "\<dots> \<le> of_int (int (A^j) * int ?num)" unfolding of_int_le_iff 
      by (rule mult_mono[OF dj sq_f_bnd], auto)
    also have "\<dots> = of_nat (A^(j + m) * (4 ^ (m - 1) * m * m))" by (simp add: power_add)
    also have "\<dots> \<le> of_nat (A^( (m - 1) + (m-1)) * (4 ^ (m - 1) * m * m))" unfolding of_nat_le_iff
      by (rule mult_right_mono[OF pow_mono_exp], insert A j i jm, auto)
    also have "\<dots> = of_nat (?bnd^2)" 
      unfolding four power_mult_distrib power2_eq_square of_nat_mult by (simp add: power_add)
    finally have "?mu^2 \<le> (of_nat ?bnd)^2" by auto
    from this[folded abs_le_square_iff] 
    have mu_bound: "abs ?mu \<le> of_nat ?bnd" by auto
    have "gs.Gramian_determinant (RAT fs) (Suc j) * ?mu \<in> \<int>" 
      by (rule gs.Gramian_determinant_mu_ints[OF *(1-2) _ _ i],
      insert j *(3,6), auto simp: set_conv_nth)
    also have "(gs.Gramian_determinant (RAT fs) (Suc j)) = of_int (d fs (Suc j))" 
      unfolding d_def by (rule of_int_Gramian_determinant, insert i j *(3,6), auto simp: set_conv_nth)
    finally have ints: "of_int (d fs (Suc j)) * ?mu \<in> \<int>" .
    have "d fs (Suc j) \<le> A ^ (Suc j)" by fact
    also have "\<dots> \<le> A ^ m" unfolding of_nat_le_iff
      by (rule pow_mono_exp, insert A jm, auto)
    finally have d_j: "d fs (Suc j) \<le> A ^ m" .
    note quot_bounds = quotient_of_bounds[OF quot ints dsj mu_bound]
    have "abs denom \<le> denom" using quotient_of_denom_pos[OF quot] by auto
    also have "\<dots> \<le> d fs (Suc j)" by fact
    also have "\<dots> \<le> A ^ m" by fact
    finally have denom: "abs denom \<le> A ^ m" by auto
    from quot_bounds(1) have "\<bar>num\<bar> \<le> d fs (Suc j) * int ?bnd" 
      unfolding of_int_le_iff[symmetric, where ?'a = rat] by simp
    also have "\<dots> \<le> A ^ m * int ?bnd" by (rule mult_right_mono[OF d_j], auto)
    also have "\<dots> = (int A ^ (m + (m - 1))) * (2 ^ (m - 1)) * int m" unfolding power_add of_nat_mult by simp
    also have "\<dots> \<le> (int A ^ (2 * m)) * (2 ^ m) * int m" unfolding of_nat_mult
      by (intro mult_mono pow_mono_exp, insert A, auto)
    also have "\<dots> = int (A ^ (2 * m) * 2 ^ m * m)" by simp
    finally have num: "\<bar>num\<bar> \<le> A ^ (2 * m) * 2 ^ m * m" .
    from denom num show ?thesis by blast
  next
    case False
    hence "?mu = 0 \<or> ?mu = 1" unfolding gs.\<mu>.simps by auto
    hence "quotient_of ?mu = (1,1) \<or> quotient_of ?mu = (0,1)" by auto
    from this[unfolded quot] show ?thesis using A i by (auto intro!: mult_ge_one)
  qed
qed

text \<open>Now we have bounds on each number $(f_i)_j$, $(g_i)_j$, and $\mu_{i,j}$, i.e.,
  for rational numbers bounds on the numerators and denominators.\<close>

text \<open>We now prove a combined size-bound for all of these numbers. The bounds clearly indicate
  that the size of the numbers grows at most polynomial, namely the sizes are roughly 
  bounded by ${\cal O}(m \cdot \log(M \cdot n))$ where $m$ is the number of vectors, $n$ is the dimension
  of the vectors, and $M$ is the maximum absolute value that occurs in the input to the LLL algorithm.\<close>

lemma combined_size_bound: fixes number :: int 
  assumes binv: "LLL_bound_invariant outside upw k fs" 
  and i: "i < m" and j: "j < n"
  and x: "x \<in> {of_int (fs ! i $ j), gso fs i $ j, \<mu> fs i j}" 
  and quot: "quotient_of x = (num, denom)" 
  and number: "number \<in> {num, denom}" 
  and number0: "number \<noteq> 0" 
shows "log 2 \<bar>number\<bar> \<le> 2 * m * log 2 A       + m + log 2 m" 
      "log 2 \<bar>number\<bar> \<le> 4 * m * log 2 (M * n) + m + log 2 m"
proof -
  from bound_invD[OF binv]
  have inv: "LLL_invariant upw k fs"
     and fbnd: "f_bound outside k fs" 
     and gbnd: "g_bound fs" 
    by auto
  from LLL_inv_A_pos[OF inv gbnd] i have A: "A > 0" by auto
  let ?bnd = "A ^ (2 * m) * 2 ^ m * m" 
  have "A ^ m * int 1 \<le> A ^ (2 * m) * (2^m * int m)" 
    by (rule mult_mono, unfold of_nat_le_iff, rule pow_mono_exp, insert A i, auto)
  hence le: "int (A ^ m) \<le> A ^ (2 * m) * 2^m * m" by auto
  from x consider (xfs) "x = of_int (fs ! i $ j)" | (xgs) "x = gso fs i $ j" | (xmu) "x = \<mu> fs i j" 
    by auto
  hence num_denom_bound: "\<bar>num\<bar> \<le> ?bnd \<and> \<bar>denom\<bar> \<le> A ^ m" 
  proof (cases)
    case xgs
    from LLL_invariant_gso_bound[OF binv i j quot[unfolded xgs]] le
    show ?thesis by auto
  next
    case xmu
    from LLL_invariant_mu_bound[OF binv i, of j, OF quot[unfolded xmu]]
    show ?thesis by auto
  next
    case xfs
    have "\<bar>denom\<bar> = 1" using quot[unfolded xfs] by auto
    also have "\<dots> \<le> A ^ m" using A by auto
    finally have denom: "\<bar>denom\<bar> \<le> A ^ m" .
    have "\<bar>num\<bar> = \<bar>fs ! i $ j\<bar>" using quot[unfolded xfs] by auto
    also have "\<dots> \<le> int (f_bnd outside)" using LLL_invariant_f_bound[OF binv i j] by auto
    also have "\<dots> \<le> int (f_bnd False)" using f_bnd_mono[of outside] by presburger
    also have "\<dots> = int (A ^ m * 2 ^ (m - 1) * m)" by simp
    also have "\<dots> \<le> ?bnd" unfolding of_nat_mult of_nat_power
      by (intro mult_mono pow_mono_exp, insert A, auto)
    finally show ?thesis using denom by auto
  qed
  from number consider (num) "number = num" | (denom) "number = denom" by auto
  hence number_bound: "\<bar>number\<bar> \<le> ?bnd" 
  proof (cases)
    case num
    with num_denom_bound show ?thesis by auto
  next
    case denom
    with num_denom_bound have "\<bar>number\<bar> \<le> A ^ m" by auto
    with le show ?thesis by auto
  qed
  from number_bound have bnd: "of_int \<bar>number\<bar> \<le> real ?bnd" by linarith
  have "log 2 \<bar>number\<bar> \<le> log 2 ?bnd" 
    by (subst log_le_cancel_iff, insert number0 bnd, auto)
  also have "\<dots> = log 2 (A^(2 * m) * 2^m) + log 2 m" 
    by (subst log_mult[symmetric], insert i A, auto)
  also have "\<dots> = log 2 (A^(2 * m)) + log 2 (2^m) + log 2 m" 
    by (subst log_mult[symmetric], insert i A, auto)
  also have "log 2 (A^(2 * m)) = log 2 (A powr (2 * m))" 
    by (rule arg_cong[of _ _ "log 2"], subst powr_realpow, insert A, auto) 
  also have "\<dots> = (2 * m) * log 2 A" 
    by (subst log_powr, insert A, auto)
  also have "log 2 (2^m) = m" by simp
  finally show boundA: "log 2 \<bar>number\<bar> \<le> 2 * m * log 2 A + m + log 2 m" .
  have "A \<le> nat M * nat M * n * 1" using A_le_MMn i by auto
  also have "\<dots> \<le> nat M * nat M * n * n" by (intro mult_mono, insert j, auto)
  finally have AM: "A \<le> nat M * nat M * n * n" by simp
  with A have "nat M \<noteq> 0" by auto
  hence M: "M > 0" by simp
  note boundA
  also have "2 * m * log 2 A + m + log 2 m \<le> 2 * m * (2 * log 2 (M * n)) + m + log 2 m" 
  proof (intro add_right_mono mult_left_mono)
    have "log 2 A \<le> log 2 (M * M * n * n)" 
    proof (subst log_le_cancel_iff)      
      show "real A \<le> (M * M * int n * int n)" using AM[folded of_nat_le_iff[where ?'a = real]] M
        by simp
    qed (insert A M j, auto)
    also have "\<dots> = log 2 (of_int (M * n) * of_int (M * n))" 
      unfolding of_int_mult by (simp  add: ac_simps)
    also have "\<dots> = 2 * log 2 (M * n)" 
      by (subst log_mult, insert j M, auto)
    finally show "log 2 A \<le> 2 * log 2 (M * n)" .
  qed auto
  finally show "log 2 \<bar>number\<bar> \<le> 4 * m * log 2 (M * n) + m + log 2 m" by simp    
qed

end (* LLL locale *)
end