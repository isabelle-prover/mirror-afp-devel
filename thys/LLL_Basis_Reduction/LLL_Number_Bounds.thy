(*
    Authors:    Maximilian Haslbeck
                René Thiemann
    License:    BSD
*)
subsection \<open>Explicit Bounds for Size of Numbers that Occur During LLL Algorithm\<close>

text \<open>The LLL invariant already contains bounds on the norms of the vectors $f_i$ and $g_i$. 
  Based on these bounds we also prove bounds on the absolute values of the $\mu_{i,j}$,
  and on the absolute values of the numbers in the vectors $f_i$ and $g_i$. 
  Moreover, we further show that also the denominators in all of these numbers doesn't grow to much.
  Finally, we prove that each number (i.e., numerator or denominator) during the execution 
  can be represented with at most ${\cal OO}(m \cdot \log(M \cdot n))$ bits, where
  $m$ is the number of input vectors, $n$ is the dimension of the input vectors,
  and $M$ is the maximum absolute value of all numbers in the input vectors.\<close>
theory LLL_Number_Bounds
  imports LLL
    Perron_Frobenius.HMA_Connect
begin

(* TODO: Documentation and add references to computer algebra book *)

hide_const (open) Determinants.det
hide_const (open) Cartesian_Euclidean_Space.mat
hide_const (open) Cartesian_Euclidean_Space.row
hide_const (open) Cartesian_Euclidean_Space.vec
hide_const (open) Path_Connected.outside

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
end (* vs fs *)

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
    using that assms by (induction n') (auto intro!: fs_int Ints_mult Ints_add)
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
  shows "Gramian_determinant fs (Suc l) / Gramian_determinant fs l = \<parallel>vs ! l\<parallel>\<^sup>2"
proof -
  have "Gramian_determinant fs (Suc l) / Gramian_determinant fs l = 
             (\<Prod>j<Suc l. \<parallel>vs ! j\<parallel>\<^sup>2) / (\<Prod>j<l. \<parallel>vs ! j\<parallel>\<^sup>2)"
    using con_assms assms by (auto simp add: Gramian_determinant)
  also have "(\<Prod>j<Suc l. \<parallel>vs ! j\<parallel>\<^sup>2) = (\<Prod>j \<in> {0..<l} \<union> {l}. \<parallel>vs ! j\<parallel>\<^sup>2)"
    using assms by (intro prod.cong) (auto)
  also have "\<dots> = (\<Prod>j<l. \<parallel>vs ! j\<parallel>\<^sup>2) * \<parallel>vs ! l\<parallel>\<^sup>2"
    using assms by (subst prod_Un) (auto simp add: atLeast0LessThan)
  also have "(\<Prod>j<l. \<parallel>vs ! j\<parallel>\<^sup>2) * \<parallel>vs ! l\<parallel>\<^sup>2 / (\<Prod>j<l. \<parallel>vs ! j\<parallel>\<^sup>2) = \<parallel>vs ! l\<parallel>\<^sup>2"
  proof -
    have "0 < \<parallel>vs ! j\<parallel>\<^sup>2" if "j < l" for j
      using assms con_assms that by (intro sq_norm_pos[of _ m]) (auto)
    then show ?thesis
      using assms by (fastforce simp add: field_simps)
  qed
  finally show ?thesis
    by simp
qed

lemma Gramian_determinant_mu_ints:
  assumes "l < k" "k < m"
  shows "Gramian_determinant fs (Suc l) * \<mu> fs k l \<in> \<int>"
proof -
  have l: "gso fs l = vs ! l "
    using gram_schmidt.main_connect(2)
    by (metis assms atLeast0LessThan con_assms gram_schmidt(4)  lessThan_iff map_eq_conv map_nth nat_SN.gt_trans set_upt)
  have ll: "Gramian_determinant fs l * gso fs l $v i = (Gramian_determinant fs l \<cdot>\<^sub>v gso fs l) $v i" if "i < n" for i
    using that assms con_assms by auto
  have "Gramian_determinant fs (Suc l) * \<mu> fs k l = Gramian_determinant fs (Suc l) * (fs ! k \<bullet> gso fs l) / \<parallel>vs ! l\<parallel>\<^sup>2 "
    using assms unfolding \<mu>.simps by (simp add: l)
  also have "\<dots> = fs ! k \<bullet> (Gramian_determinant fs l \<cdot>\<^sub>v gso fs l)"
    using assms con_assms Gramian_determinant(2)[of fs m vs "Suc l"]
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
qed

end (* fs_int *)

end (* fixes fs vs *)

end (* gram_schmidt_rat *)


lemma vec_hom_Ints:
  assumes "i < n" "xs \<in> carrier_vec n"
  shows "of_int_hom.vec_hom xs $v i \<in> \<int>"
  using assms by auto

context LLL_with_assms
begin

lemma fs_init: "set fs_init \<subseteq> carrier_vec n" 
  using lin_dep[unfolded gs.lin_indpt_list_def] by auto

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
  assumes inv: "LLL_invariant outside (upw,k, Fs, Gs) fs gs" 
  and i: "i < m" and j: "j < n" 
shows "\<bar>fs ! i $ j\<bar> \<le> f_bnd outside" 
proof -
  from LLL_inv_A_pos[OF inv] i have A0: "A > 0" by auto
  note inv = LLL_invD[OF inv] 
  from inv(4,3) i have fsi: "fs ! i \<in> carrier_vec n" by auto
  have one: "\<bar>fs ! i $ j\<bar>^1 \<le> \<bar>fs ! i $ j\<bar>^2" 
    by (cases "fs ! i $ j \<noteq> 0", intro pow_mono_exp, auto)
  let ?num = "(4 ^ (m - 1) * A ^ m * m * m)" 
  let ?sq_bnd = "if i \<noteq> k \<or> outside then int (A * m) else int ?num" 
  have "\<bar>fs ! i $ j\<bar>^2 \<le> \<parallel>fs ! i\<parallel>\<^sup>2" using fsi j by (metis vec_le_sq_norm)
  also have "\<dots> \<le> ?sq_bnd" 
    using \<open>f_bound outside k fs\<close>[unfolded f_bound_def, rule_format, OF i] by auto
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


lemma LLL_invariant_g_bound:
  assumes inv: "LLL_invariant outside (upw,k, Fs, Gs) fs gs" 
  and i: "i < m" and j: "j < n" 
  and quot: "quotient_of (gs ! i $ j) = (num, denom)" 
shows "\<bar>num\<bar>   \<le> A ^ m" 
  and "\<bar>denom\<bar> \<le> A ^ m"
proof -
  note * = LLL_invD[OF inv]
  interpret gs: gram_schmidt_rat n .
  note d_approx[OF inv i, unfolded d_def]  
  let ?r = "rat_of_int"
  have gso_gs: "gs ! i = gs.gso (RAT fs) i"
    using LLL_connect[OF inv] i by auto
  then have int: "(gs.Gramian_determinant (RAT fs) i \<cdot>\<^sub>v (gs ! i)) $v j \<in> \<int>"
  proof -
    have "of_int_hom.vec_hom (fs ! j) $v i \<in> \<int>" if "i < n" "j < m" for i j
      using that assms * by (intro vec_hom_Ints) (auto)
    then show ?thesis
      using * gs.gso_connect snd_gram_schmidt_int assms
      by (subst gso_gs, intro gs.Gramian_determinant_times_gso_Ints) (auto)
  qed
  have gsi: "gs ! i \<in> Rn"
    using * gram_schmidt.f_carrier assms by (subst gso_gs) (fastforce)
  have gs_sq: "\<bar>(gs ! i $ j)\<bar>\<^sup>2 \<le> rat_of_nat A"
    by(rule order_trans, rule vec_le_sq_norm[of _ n])
      (use gsi assms * LLL.g_bound_def in auto)
  from i have "m * m \<noteq> 0"
    by auto
  then have A0: "A \<noteq> 0"
    using less_le_trans[OF LLL_D_pos[OF inv] D_approx[OF inv]] by auto
  have "\<bar>(gs ! i $ j)\<bar> \<le> max 1 \<bar>(gs ! i $ j)\<bar>"
    by simp
  also have "\<dots> \<le> (max 1 \<bar>gs ! i $ j\<bar>)\<^sup>2"
    by (rule self_le_power, auto) 
  also have "\<dots> \<le> of_nat A"
    using gs_sq A0 unfolding max_def by auto
  finally have gs_bound: "\<bar>(gs ! i $ j)\<bar> \<le> of_nat A"
    .
  have "gs.Gramian_determinant (map of_int_hom.vec_hom fs) i = rat_of_int (gs.Gramian_determinant fs i)"
    using  assms *(3,4) carrier_vecD nth_mem by (intro of_int_Gramian_determinant) (simp, blast)
  with int have "(of_int (d fs i) \<cdot>\<^sub>v gs ! i) $v j \<in> \<int>"
    unfolding d_def by simp
  also have "(of_int (d fs i) \<cdot>\<^sub>v gs ! i) $v j = of_int (d fs i) * (gs ! i $ j)"
    using gsi i j by auto
  finally have l: "of_int (d fs i) * gs ! i $v j \<in> \<int>"
    by auto
  have num: "rat_of_int \<bar>num\<bar> \<le> of_int (d fs i * int A)" and denom: "denom \<le> d fs i"
    using quotient_of_bounds[OF quot l LLL_d_pos[OF inv] gs_bound] i by auto
  from num have num: "\<bar>num\<bar> \<le> d fs i * int A"
    by linarith
  from d_approx[OF inv i] have d: "d fs i \<le> int (A ^ i)"
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
  assumes inv: "LLL_invariant outside (upw,k, Fs, Gs) fs gs" 
  and i: "i < m"                 
  and quot: "quotient_of (gs.\<mu> (RAT fs) i j) = (num, denom)" 
shows "\<bar>num\<bar>   \<le> A ^ (2 * m) * 2 ^ m * m" 
  and "\<bar>denom\<bar> \<le> A ^ m" 
proof (atomize(full))
  from LLL_inv_A_pos[OF inv] i have A: "A > 0" by auto 
  note * = LLL_invD[OF inv]
  let ?mu = "gs.\<mu> (RAT fs) i j" 
  interpret gs: gram_schmidt_rat n .
  note d_approx[OF inv i, unfolded d_def]  
  note *(13)[unfolded g_bound_def, rule_format, OF i]
  note vec_le_sq_norm
  note *(2)  
  show "\<bar>num\<bar> \<le> A ^ (2 * m) * 2 ^ m * m \<and> \<bar>denom\<bar> \<le> A ^ m" 
  proof (cases "j < i")
    case j: True
    from j i have jm: "j < m" by auto
    from quotient_of_square[OF quot] 
    have quot_sq: "quotient_of (?mu^2) = (num * num, denom * denom)" 
      unfolding power2_eq_square by auto
    from d_approx[OF inv jm]
    have dj: "d fs j \<le> int (A ^ j)" by linarith
    from LLL_d_pos[OF inv, of "Suc j"] i j have dsj: "0 < d fs (Suc j)" by auto
    hence d_pos: "0 < (d fs (Suc j))^2" by auto
    from d_approx[OF inv, of "Suc j"] j i 
    have "rat_of_int (d fs (Suc j)) \<le> of_nat (A ^ Suc j)" 
      by auto
    hence d_j_bound: "d fs (Suc j) \<le> int (A^Suc j)" by linarith
    let ?num = "4 ^ (m - 1) * A ^ m * m * m" 
    let ?bnd = "A^(m - 1) * 2 ^ (m - 1) * m" 
    from *(12)[unfolded f_bound_def, rule_format, OF i]
      aux_bnd_mono[folded of_nat_le_iff[where ?'a = int]]
    have sq_f_bnd: "sq_norm (fs ! i) \<le> int ?num" by (auto split: if_splits)
    have four: "(4 :: nat) = 2^2" by auto
    have "?mu^2 \<le> (gs.Gramian_determinant (RAT fs) j) * sq_norm (RAT fs ! i)"
      by (rule gs.mu_bound_Gramian_determinant[OF *(10) _ _ _ j i],
      insert *(2-), auto simp: gram_schmidt_int_def gram_schmidt_wit_def set_conv_nth)
    also have "sq_norm (RAT fs ! i) = of_int (sq_norm (fs ! i))" 
      unfolding sq_norm_of_int[symmetric] using *(4) i by auto
    also have "(gs.Gramian_determinant (RAT fs) j) = of_int (d fs j)" 
      unfolding d_def apply(rule of_int_Gramian_determinant)
      using j assms
      using *(4) dual_order.strict_trans apply simp
      using *(3) carrier_vecD nth_mem by blast
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
      by (rule gs.Gramian_determinant_mu_ints[OF *(10) _ _ _ j i],
      insert *(2-), auto simp: gram_schmidt_int_def gram_schmidt_wit_def set_conv_nth)
    also have "(gs.Gramian_determinant (RAT fs) (Suc j)) = of_int (d fs (Suc j))" 
      unfolding d_def apply(rule of_int_Gramian_determinant)
      using j assms
      using *(4) dual_order.strict_trans apply simp
      using *(3) carrier_vecD nth_mem by blast
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
  assumes inv: "LLL_invariant outside (upw, k, Fs, Gs) fs gs" 
  and i: "i < m" and j: "j < n"
  and x: "x \<in> {of_int (fs ! i $ j), gs ! i $ j, gs.\<mu> (RAT fs) i j}" 
  and quot: "quotient_of x = (num, denom)" 
  and number: "number \<in> {num, denom}" 
  and number0: "number \<noteq> 0" 
shows "log 2 \<bar>number\<bar> \<le> 2 * m * log 2 A       + m + log 2 m" 
      "log 2 \<bar>number\<bar> \<le> 4 * m * log 2 (M * n) + m + log 2 m"
proof -
  from LLL_inv_A_pos[OF inv] i have A: "A > 0" by auto
  let ?bnd = "A ^ (2 * m) * 2 ^ m * m" 
  have "A ^ m * int 1 \<le> A ^ (2 * m) * (2^m * int m)" 
    by (rule mult_mono, unfold of_nat_le_iff, rule pow_mono_exp, insert A i, auto)
  hence le: "int (A ^ m) \<le> A ^ (2 * m) * 2^m * m" by auto
  from x consider (xfs) "x = of_int (fs ! i $ j)" | (xgs) "x = gs ! i $ j" | (xmu) "x = gs.\<mu> (RAT fs) i j" 
    by auto
  hence num_denom_bound: "\<bar>num\<bar> \<le> ?bnd \<and> \<bar>denom\<bar> \<le> A ^ m" 
  proof (cases)
    case xgs
    from LLL_invariant_g_bound[OF inv i j quot[unfolded xgs]] le
    show ?thesis by auto
  next
    case xmu
    from LLL_invariant_mu_bound[OF inv i, of j, OF quot[unfolded xmu]]
    show ?thesis by auto
  next
    case xfs
    have "\<bar>denom\<bar> = 1" using quot[unfolded xfs] by auto
    also have "\<dots> \<le> A ^ m" using A by auto
    finally have denom: "\<bar>denom\<bar> \<le> A ^ m" .
    have "\<bar>num\<bar> = \<bar>fs ! i $ j\<bar>" using quot[unfolded xfs] by auto
    also have "\<dots> \<le> int (f_bnd outside)" using LLL_invariant_f_bound[OF inv i j] by auto
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