(*
    Authors:    Ralph Bottesch
                Maximilian Haslbeck
                René Thiemann
    License:    BSD
*)
subsection \<open>Gram Schmidt Implementation for Integer Vectors\<close>

text \<open>This theory implements the Gram-Schmidt algorithm on integer vectors
  using purely integer arithmetic. The formalization is based on \cite{GS_EKM}.\<close>

theory Gram_Schmidt_Int
  imports 
    Gram_Schmidt_2
    More_IArray
begin

context fixes
  fs :: "int vec iarray" and m :: nat
begin 
fun sigma_array where
  "sigma_array dmus dmusi dmusj dll l = (if l = 0 then dmusi !! l * dmusj !! l
      else let l1 = l - 1; dll1 = dmus !! l1 !! l1 in
      (dll * sigma_array dmus dmusi dmusj dll1 l1 + dmusi !! l * dmusj !! l) div 
          dll1)"

declare sigma_array.simps[simp del]

partial_function(tailrec) dmu_array_row_main where
  [code]: "dmu_array_row_main fi i dmus j = (if j = i then dmus
     else let sj = Suc j; 
       dmus_i = dmus !! i;
       djj = dmus !! j !! j;
       dmu_ij = djj * (fi \<bullet> fs !! sj) - sigma_array dmus dmus_i (dmus !! sj) djj j;
       dmus' = iarray_update dmus i (iarray_append dmus_i dmu_ij)
      in dmu_array_row_main fi i dmus' sj)" 

definition dmu_array_row where
  "dmu_array_row dmus i = (let fi = fs !! i in 
      dmu_array_row_main fi i (iarray_append dmus (IArray [fi \<bullet> fs !! 0])) 0)" 

partial_function (tailrec) dmu_array where 
  [code]: "dmu_array dmus i = (if i = m then dmus else 
    let dmus' = dmu_array_row dmus i 
      in dmu_array dmus' (Suc i))"
end

definition d\<mu>_impl :: "int vec list \<Rightarrow> int iarray iarray" where
  "d\<mu>_impl fs = dmu_array (IArray fs) (length fs) (IArray []) 0" 


definition (in gram_schmidt) \<beta> where "\<beta> fs l = Gramian_determinant fs (Suc l) / Gramian_determinant fs l"

context gram_schmidt_fs_lin_indpt
begin

lemma Gramian_beta:
  assumes "i < m"
  shows "\<beta> fs i = \<parallel>fs ! i\<parallel>\<^sup>2 - (\<Sum>j = 0..<i. (\<mu> i j)\<^sup>2 * \<beta> fs j)"
proof -
  let ?S = "M.sumlist (map (\<lambda>j. - \<mu> i j \<cdot>\<^sub>v gso j) [0..<i])"
  have S: "?S \<in> carrier_vec n"
    using assms by (auto intro!: M.sumlist_carrier gso_carrier)
  have fi: "fs ! i \<in> carrier_vec n" using assms by auto
  have "\<beta> fs i = gso i \<bullet> gso i"
    unfolding \<beta>_def
    using assms dist by (auto simp add: Gramian_determinant_div sq_norm_vec_as_cscalar_prod)
  also have "\<dots> = (fs ! i + ?S) \<bullet> (fs ! i + ?S)"
    by (subst gso.simps, subst (2) gso.simps) auto
  also have "\<dots> = fs ! i \<bullet> fs ! i + ?S \<bullet> fs ! i + fs ! i \<bullet> ?S + ?S \<bullet> ?S"
    using assms S by (auto simp add: add_scalar_prod_distrib[of _ n] scalar_prod_add_distrib[of _ n])
  also have "fs ! i \<bullet> ?S = ?S \<bullet> fs ! i" 
    by (rule comm_scalar_prod[OF fi S])
  also have "?S \<bullet> fs ! i = ?S \<bullet> gso i - ?S \<bullet> ?S"
  proof -
    have "fs ! i = gso i - M.sumlist (map (\<lambda>j. - \<mu> i j \<cdot>\<^sub>v gso j) [0..<i])"
       using assms S by (subst gso.simps) auto
    then show ?thesis
      using assms S by (auto simp add: minus_scalar_prod_distrib[of _ n] scalar_prod_minus_distrib[of _ n])
  qed
  also have "?S \<bullet> gso i = 0"
    using assms orthogonal
    by(subst scalar_prod_left_sum_distrib)
      (auto intro!: sum_list_neutral M.sumlist_carrier gso_carrier)
  also have "?S \<bullet> ?S = (\<Sum>j = 0..<i. (\<mu> i j)\<^sup>2 * (gso j \<bullet> gso j))"
    using assms dist by (subst scalar_prod_lincomb_gso)
       (auto simp add: power2_eq_square interv_sum_list_conv_sum_set_nat)
  also have "\<dots> =  (\<Sum>j = 0..<i. (\<mu> i j)\<^sup>2 * \<beta> fs j)"
    using assms dist
    by (auto simp add: \<beta>_def Gramian_determinant_div sq_norm_vec_as_cscalar_prod
        intro!: sum.cong)
  finally show ?thesis
    by (auto simp add: sq_norm_vec_as_cscalar_prod)
qed

lemma gso_norm_beta:
  assumes "j < m"
  shows "\<beta> fs j = sq_norm (gso j)"
  unfolding \<beta>_def
  using assms dist by (auto simp add: Gramian_determinant_div sq_norm_vec_as_cscalar_prod)

lemma mu_Gramian_beta_def:
  assumes "j < i" "i < m"
  shows "\<mu> i j = (fs ! i \<bullet> fs ! j - (\<Sum>k = 0..<j. \<mu> j k * \<mu> i k * \<beta> fs k)) / \<beta> fs j"
proof -
  let ?list = "map (\<lambda>ja. \<mu> i ja \<cdot>\<^sub>v gso ja) [0..<i]" 
  let ?neg_sum = "M.sumlist (map (\<lambda>ja. - \<mu> j ja \<cdot>\<^sub>v gso ja) [0..<j])"
  have list: "set ?list \<subseteq> carrier_vec n" using gso_carrier assms by auto
  define fi where "fi = fs ! i"
  have list_id: "[0..<i] = [0..<j] @ [j..<i]" 
    using assms by (metis append.simps(1) neq0_conv upt.simps(1) upt_append)

  have "\<mu> i j = (fs ! i) \<bullet> (gso j) / sq_norm (gso j) "
    unfolding \<mu>.simps using assms by auto
  also have " ... = fs ! i \<bullet> (fs ! j + ?neg_sum) / sq_norm (gso j)" 
    by (subst gso.simps, simp)
  also have " ... = (fi \<bullet> fs ! j + fs ! i \<bullet> ?neg_sum) / sq_norm (gso j)"
    using assms unfolding fi_def
    by (subst scalar_prod_add_distrib [of _ n]) (auto intro!: M.sumlist_carrier gso_carrier)
  also have "fs ! i = gso i + M.sumlist ?list "
    by (rule fs_by_gso_def[OF assms(2)])
  also have "... \<bullet> ?neg_sum = gso i \<bullet> ?neg_sum + M.sumlist ?list \<bullet> ?neg_sum"
    using assms by (subst add_scalar_prod_distrib [of _ n]) (auto intro!: M.sumlist_carrier gso_carrier)
  also have " M.sumlist ?list = M.sumlist (map (\<lambda>ja. \<mu> i ja \<cdot>\<^sub>v gso ja) [0..<j]) 
     + M.sumlist (map (\<lambda>ja. \<mu> i ja \<cdot>\<^sub>v gso ja) [j..<i]) " (is "_ = ?sumj + ?sumi")
    unfolding list_id
    by (subst M.sumlist_append[symmetric], insert gso_carrier assms, auto)
  also have "gso i \<bullet> ?neg_sum = 0"
    by (rule orthogonal_sumlist, insert gso_carrier dist assms orthogonal, auto)
  also have " (?sumj + ?sumi) \<bullet> ?neg_sum = ?sumj \<bullet> ?neg_sum + ?sumi \<bullet> ?neg_sum"
    using assms
    by (subst add_scalar_prod_distrib [of _ n], auto intro!: M.sumlist_carrier gso_carrier)
  also have " ?sumj \<bullet> ?neg_sum = (\<Sum>l = 0..<j. (\<mu> i l) * (-\<mu> j l) * (gso l \<bullet> gso l)) "
    using assms
    by (subst scalar_prod_lincomb_gso) (auto simp add: interv_sum_list_conv_sum_set_nat)
  also have "\<dots> = - (\<Sum>l = 0..<j. (\<mu> i l) * (\<mu> j l) * (gso l \<bullet> gso l)) " (is "_ = - ?sum")
    by (auto simp add: sum_negf)
  also have "?sum = (\<Sum>l = 0..<j. (\<mu> j l) * (\<mu> i l) * \<beta> fs l)" 
    using assms
    by (intro sum.cong, auto simp: gso_norm_beta sq_norm_vec_as_cscalar_prod)
  also have "?sumi \<bullet> ?neg_sum = 0"
    apply (rule orthogonal_sumlist, insert gso_carrier assms orthogonal, auto intro!: M.sumlist_carrier gso_carrier)
    apply (subst comm_scalar_prod[of _ n], auto intro!: M.sumlist_carrier)
    by (rule orthogonal_sumlist, use dist in auto)
  also have "sq_norm (gso j) = \<beta> fs j"
    using assms
    by (subst gso_norm_beta, auto)
  finally show ?thesis unfolding fi_def by simp
qed

end

lemma (in gram_schmidt) Gramian_matrix_alt_alt_alt_def:
  assumes "k \<le> length fs" "set fs \<subseteq> carrier_vec n"
  shows "Gramian_matrix fs k = mat k k (\<lambda>(i,j). fs ! i \<bullet> fs ! j)"
proof -
  have *: "vec n (($) (fs ! i)) = fs ! i" if "i < length fs" for i
    using that assms
    by (metis carrier_vecD dim_vec eq_vecI index_vec nth_mem subsetCE)
  then show ?thesis
    unfolding Gramian_matrix_def using  assms
    by (intro eq_matI) (auto simp add: Let_def)
qed

lemma (in gram_schmidt_fs_Rn) Gramian_determinant_1 [simp]:
  assumes "0 < length fs"
  shows "Gramian_determinant fs (Suc 0) = \<parallel>fs ! 0\<parallel>\<^sup>2"
proof -
  have "Gramian_determinant fs (Suc 0) = fs ! 0 \<bullet> fs ! 0"
    using assms unfolding Gramian_determinant_def 
    by (subst det_def') (auto simp add: Gramian_matrix_def Let_def scalar_prod_def)
  then show ?thesis
    by (subst sq_norm_vec_as_cscalar_prod) simp
qed


context gram_schmidt_fs_lin_indpt
begin

abbreviation d where "d \<equiv> Gramian_determinant fs" 
definition \<mu>' where "\<mu>' i j \<equiv> d (Suc j) * \<mu> i j" 

fun \<sigma> where 
  "\<sigma> 0 i j = 0" 
| "\<sigma> (Suc l) i j = (d (Suc l) * \<sigma> l i j + \<mu>' i l * \<mu>' j l) / d l" 

lemma d_Suc: "d (Suc i) = \<mu>' i i" unfolding \<mu>'_def by (simp add: \<mu>.simps)
lemma d_0: "d 0 = 1" by (rule Gramian_determinant_0)

lemma \<sigma>: assumes lj: "l \<le> m" 
  shows "\<sigma> l i j = d l * (\<Sum>k < l. \<mu> i k * \<mu> j k * \<beta> fs k)"
  using lj
proof (induct l)
  case (Suc l)
  from Suc(2-) have lj: "l \<le> m" by auto
  note IH = Suc(1)[OF lj]
  let ?f = "\<lambda> k. \<mu> i k * \<mu> j k * \<beta> fs k" 
  have dl0: "d l > 0" using lj Gramian_determinant dist unfolding lin_indpt_list_def by auto
  have "\<sigma> (Suc l) i j = (d (Suc l) * \<sigma> l i j + \<mu>' i l * \<mu>' j l) / d l" by simp
  also have "\<dots> = (d (Suc l) * \<sigma> l i j) / d l + (\<mu>' i l * \<mu>' j l) / d l" using dl0 
    by (simp add: field_simps)
  also have "(\<mu>' i l * \<mu>' j l) / d l = d (Suc l) * ?f l" (is "_ = ?one")
    unfolding \<beta>_def \<mu>'_def by auto
  also have "(d (Suc l) * \<sigma> l i j) / d l = d (Suc l) * (\<Sum>k < l. ?f k)" (is "_ = ?sum")
    using dl0 unfolding IH by simp
  also have "?sum + ?one = d (Suc l) * (?f l + (\<Sum>k < l. ?f k))" by (simp add: field_simps)
  also have "?f l + (\<Sum>k < l. ?f k) = (\<Sum>k < Suc l. ?f k)" by simp
  finally show ?case .
qed auto

lemma \<mu>': assumes j: "j \<le> i" and i: "i < m" 
  shows "\<mu>' i j = d j * (fs ! i \<bullet> fs ! j) - \<sigma> j i j" 
proof (cases "j < i")
  case j: True
  have dsj: "d (Suc j) > 0"
    using j i Gramian_determinant dist unfolding lin_indpt_list_def
    by (meson less_trans_Suc nat_less_le)
  let ?sum = " (\<Sum>k = 0..<j. \<mu> j k * \<mu> i k * \<beta> fs k)" 
  have "\<mu>' i j = (fs ! i \<bullet> fs ! j - ?sum) * (d (Suc j) / \<beta> fs j)"     
    unfolding mu_Gramian_beta_def[OF j i] \<mu>'_def by simp
  also have "d (Suc j) / \<beta> fs j = d j" unfolding \<beta>_def using dsj by auto
  also have "(fs ! i \<bullet> fs ! j - ?sum) * d j = (fs ! i \<bullet> fs ! j) * d j - d j * ?sum" 
    by (simp add: ring_distribs)
  also have "d j * ?sum = \<sigma> j i j" 
    by (subst \<sigma>, (insert j i, force), intro arg_cong[of _ _ "\<lambda> x. _ * x"] sum.cong, auto)
  finally show ?thesis by simp
next
  case False
  with j have j: "j = i" by auto
  have dsi: "d (Suc i) > 0" "d i > 0"
    using i Suc_leI dist  unfolding lin_indpt_list_def
    by (simp_all add: Suc_leI Gramian_determinant(2))
  let ?sum = " (\<Sum>k = 0..<i. \<mu> i k * \<mu> i k * \<beta> fs k)" 
  have bzero: "\<beta> fs i \<noteq> 0" unfolding \<beta>_def using dsi by auto
  have "\<mu>' i i = d (Suc i)" by (simp add: \<mu>.simps \<mu>'_def)
  also have "\<dots> = \<beta> fs i * (d (Suc i)  / \<beta> fs i)" using bzero by simp 
  also have "d (Suc i) / \<beta> fs i = d i" unfolding \<beta>_def using dsi by auto
  also have "\<beta> fs i = (fs ! i \<bullet> fs ! i - ?sum)" 
    unfolding Gramian_beta[OF i]
    by (rule arg_cong2[of _ _ _ _ "(-)", OF _ sum.cong], 
        auto simp: power2_eq_square sq_norm_vec_as_cscalar_prod)
  also have "(fs ! i \<bullet> fs ! i - ?sum) * d i = (fs ! i \<bullet> fs ! i) * d i - d i * ?sum" 
    by (simp add: ring_distribs)
  also have "d i * ?sum = \<sigma> i i i" 
    by (subst \<sigma>, (insert i i, force), intro arg_cong[of _ _ "\<lambda> x. _ * x"] sum.cong, auto)
  finally show ?thesis using j by simp
qed

lemma \<sigma>_via_\<mu>': "\<sigma> (Suc l) i j = 
  (if l = 0 then \<mu>' i 0 * \<mu>' j 0 else (\<mu>' l l * \<sigma> l i j + \<mu>' i l * \<mu>' j l) / \<mu>' (l - 1) (l - 1))"
  by (cases l, auto simp: d_Suc)

lemma \<mu>'_via_\<sigma>: assumes j: "j \<le> i" and i: "i < m" 
  shows "\<mu>' i j = 
    (if j = 0 then fs ! i \<bullet> fs ! j else \<mu>' (j - 1) (j - 1) * (fs ! i \<bullet> fs ! j) - \<sigma> j i j)"
  unfolding \<mu>'[OF assms] by (cases j, auto simp: d_Suc)

lemma fs_i_sumlist_\<kappa>:
  assumes "i < m" "l \<le> i" "j < l"
  shows "(fs ! i + sumlist (map (\<lambda>j. \<kappa> i l j \<cdot>\<^sub>v fs ! j) [0..<l])) \<bullet> fs ! j = 0"
proof -
  have "fs ! i + sumlist (map (\<lambda>j. \<kappa> i l j \<cdot>\<^sub>v fs ! j) [0..<l])
        = fs ! i - M.sumlist (map (\<lambda>j. \<mu> i j \<cdot>\<^sub>v gso j) [0..<l])"
    using assms gso_carrier assms 
    by (subst \<kappa>_def[symmetric]) (auto simp add: dim_sumlist sumlist_nth sum_negf)
  also have "\<dots> = M.sumlist (map (\<lambda>j. \<mu> i j \<cdot>\<^sub>v gso j) [l..<Suc i])"
  proof -
    have "fs ! i = M.sumlist (map (\<lambda>j. \<mu> i j \<cdot>\<^sub>v gso j) [0..<Suc i])"
      using assms by (intro fi_is_sum_of_mu_gso) auto
    also have "\<dots> = M.sumlist (map (\<lambda>j. \<mu> i j \<cdot>\<^sub>v gso j) [0..<l]) +
                  M.sumlist (map (\<lambda>j. \<mu> i j \<cdot>\<^sub>v gso j) [l..<Suc i])"
    proof -
      have *: "[0..<Suc i] = [0..<l] @ [l..<Suc i]"
        using assms by (metis diff_zero le_imp_less_Suc length_upt list_trisect upt_conv_Cons)
      show ?thesis
        by (subst *, subst map_append, subst sumlist_append) (use gso_carrier assms in auto)
    qed
    finally show ?thesis
      using assms gso_carrier assms by (auto simp add: algebra_simps dim_sumlist)
  qed
  finally have "fs ! i + M.sumlist (map (\<lambda>j. \<kappa> i l j \<cdot>\<^sub>v fs ! j) [0..<l]) =
                M.sumlist (map (\<lambda>j. \<mu> i j \<cdot>\<^sub>v gso j) [l..<Suc i])"
    by simp
  moreover have "\<dots> \<bullet> (fs ! j) = 0"
    using assms gso_carrier assms unfolding lin_indpt_list_def
    by (subst scalar_prod_left_sum_distrib)
       (auto simp add: algebra_simps dim_sumlist gso_scalar_zero intro!: sum_list_zero)
  ultimately show ?thesis using assms by auto
qed

lemma fs_i_fs_j_sum_\<kappa>:
  assumes "i < m" "l \<le> i" "j < l"
  shows "- (fs ! i \<bullet> fs ! j) = (\<Sum>t = 0..<l. fs ! t \<bullet> fs ! j * \<kappa> i l t)"
proof -
  have [simp]: "M.sumlist (map (\<lambda>j. \<kappa> i l j \<cdot>\<^sub>v fs ! j) [0..<l]) \<in> carrier_vec n"
    using assms by (auto intro!: sumlist_carrier simp add: dim_sumlist)
  have "0  = (fs ! i + M.sumlist (map (\<lambda>j. \<kappa> i l j \<cdot>\<^sub>v fs ! j) [0..<l])) \<bullet> fs ! j"
    using fs_i_sumlist_\<kappa> assms by simp
  also have "\<dots> = fs ! i \<bullet> fs ! j + M.sumlist (map (\<lambda>j. \<kappa> i l j \<cdot>\<^sub>v fs ! j) [0..<l]) \<bullet> fs ! j"
    using assms by (subst add_scalar_prod_distrib[of _ n]) (auto)
  also have "M.sumlist (map (\<lambda>j. \<kappa> i l j \<cdot>\<^sub>v fs ! j) [0..<l]) \<bullet> fs ! j =
             (\<Sum>v\<leftarrow>map (\<lambda>j. \<kappa> i l j \<cdot>\<^sub>v fs ! j) [0..<l]. v \<bullet> fs ! j)"
    using assms by (intro scalar_prod_left_sum_distrib) (auto)
  also have "\<dots> = (\<Sum>t\<leftarrow>[0..<l]. (\<kappa> i l t \<cdot>\<^sub>v fs ! t) \<bullet> fs ! j)"
    by (rule arg_cong[where f=sum_list]) (auto)
  also have "\<dots> =  (\<Sum>t = 0..<l. (\<kappa> i l t \<cdot>\<^sub>v fs ! t) \<bullet> fs ! j) "
    by (subst interv_sum_list_conv_sum_set_nat) (auto)
  also have "\<dots> = (\<Sum>t = 0..<l. fs ! t \<bullet> fs ! j * \<kappa> i l t)"
    using assms by (intro sum.cong) auto
  finally show ?thesis by (simp add: field_simps)
qed


lemma Gramian_matrix_times_\<kappa>:
  assumes "i < m" "l \<le> i"
  shows "Gramian_matrix fs l *\<^sub>v (vec l (\<lambda>t. \<kappa> i l t)) = (vec l (\<lambda>j. - (fs ! i \<bullet> fs ! j)))"
proof -
  have "- (fs ! i \<bullet> fs ! j) = (\<Sum>t = 0..<l. fs ! t \<bullet> fs ! j * \<kappa> i l t)" if "j < l" for j
    using fs_i_fs_j_sum_\<kappa> assms that by simp
  then show ?thesis using assms
    by (subst Gramian_matrix_alt_alt_def) (auto simp add: scalar_prod_def algebra_simps)
qed

end (* gram_schmidt_fs_lin_indpt *)

context gram_schmidt_fs_int
begin

lemma d_\<kappa>_int :
  assumes "i < m" "l \<le> i" "t < l"
  shows "d l * \<kappa> i l t \<in> \<int>"
proof -
  let ?A = "Gramian_matrix fs l"
  let ?B = "replace_col ?A (Gramian_matrix fs l *\<^sub>v vec l (\<kappa> i l)) t" 
  have deteq: "d l = det ?A"
    unfolding Gramian_determinant_def
    using Gramian_determinant_Ints
    by auto

  have **: "Gramian_matrix fs l \<in> carrier_mat l l" unfolding Gramian_matrix_def Let_def  using fs_carrier by auto
      
  then have " \<kappa> i l t * det ?A = det ?B"
    using assms fs_carrier cramer_lemma_mat[of ?A l " (vec l (\<lambda>t. \<kappa> i l t))" t]
    by auto

  also have " ... \<in> \<int> "
  proof -
    have *: "t<l \<Longrightarrow> (?A *\<^sub>v vec l (\<kappa> i l)) $ t \<in> \<int>" for t
      using assms
      apply(subst Gramian_matrix_times_\<kappa>, force, force)
      using fs_int fs_carrier
      by (auto intro!: fs_scalar_Ints Ints_minus)

    define B where "B = ?B"

    have Bint: "t1<l \<longrightarrow> s1 < l \<longrightarrow> B $$ (t1,s1) \<in> \<int>" for t1 s1
    proof (cases "s1 = t")
      case True
      from * ** this show ?thesis 
        unfolding replace_col_def B_def
        by auto
    next
      case False
      from * ** Gramian_matrix_def this fs_carrier assms show ?thesis
        unfolding replace_col_def B_def
        by (auto simp: Gramian_matrix_def Let_def scalar_prod_def intro!: Ints_sum Ints_mult fs_int)
    qed
    have B: "B \<in> carrier_mat l l"
      using ** replace_col_def unfolding B_def
      by (auto simp: replace_col_def)
    have "det B \<in> \<int>"
      using B Bint assms  det_col[of B l]
      by (auto intro!: Ints_sum Ints_mult Ints_prod simp: signof_def)
    thus ?thesis unfolding B_def.
  qed
  finally show ?thesis using deteq by (auto simp add: algebra_simps)
qed

lemma \<beta>_pos : "i < m \<Longrightarrow> \<beta> fs i > 0" 
  using Gramian_determinant(2) unfolding lin_indpt_list_def \<beta>_def by auto

lemma \<beta>_zero : "i < m \<Longrightarrow> \<beta> fs i \<noteq> 0" 
  using \<beta>_pos[of i] by simp

lemma \<sigma>_integer:  
  assumes l: "l \<le> j" and j: "j \<le> i" and i: "i < m"
  shows "\<sigma> l i j \<in> \<int>" 
proof -
  from assms have ll: "l \<le> m" by auto
  have fs_carr: "j < m \<Longrightarrow> fs ! j \<in> carrier_vec n" for j using assms fs_carrier unfolding set_conv_nth by force
  with assms have fs_carr_j: "fs ! j \<in> carrier_vec n" by auto
  have dim_gso: "i < m \<Longrightarrow> dim_vec (gso i) = n" for i using gso_carrier by auto
  have dim_fs: "k < m \<Longrightarrow> dim_vec (fs ! k) = n" for k using smult_carrier_vec fs_carr by auto
  have i_l_m: "i < l \<Longrightarrow> i < m" for i using assms by auto
  have smult: "\<And> i j . j < n \<Longrightarrow> i < l \<Longrightarrow> (c \<cdot>\<^sub>v fs ! i) $ j = c * (fs ! i $ j)" for c
    using i_l_m dim_fs by auto
  have "\<sigma> l i j = d l * (\<Sum>k < l. \<mu> i k * \<mu> j k * \<beta> fs k)"
    unfolding \<sigma>[OF ll] by simp
  also have " ... = d l * (\<Sum>k < l. \<mu> i k * ((fs ! j) \<bullet> (gso k) /  sq_norm (gso k)) * \<beta> fs k)" (is "_ = _ * ?sum")
    unfolding \<mu>.simps using assms by auto
  also have "?sum =  (\<Sum>k < l. \<mu> i k * ((fs ! j) \<bullet> (gso k) /  \<beta> fs k) * \<beta> fs k)"
    apply (rule sum.cong [OF refl])
    apply (subst gso_norm_beta[symmetric])
    using assms
    by auto

  also have "... = (\<Sum>k < l. \<mu> i k * ((fs ! j) \<bullet> (gso k) ))"
    apply (rule sum.cong[OF refl])
    using \<beta>_zero assms by auto

  also have " ... = (fs ! j) \<bullet> M.sumlist (map (\<lambda>k. (\<mu> i k) \<cdot>\<^sub>v (gso k)) [0..<l] )"
    apply (subst scalar_prod_right_sum_distrib, unfold map_map o_def)
    using assms fs_carr[of j] gso_carrier
    by (auto intro!: gso_carrier fs_carr sum.cong simp: sum_list_sum_nth)

  also have "d l * \<dots> = (fs ! j) \<bullet> (d l \<cdot>\<^sub>v M.sumlist (map (\<lambda>k. (\<mu> i k) \<cdot>\<^sub>v (gso k)) [0..<l]))" (is "_ = _ \<bullet> (_ \<cdot>\<^sub>v ?sum2)")
    apply (rule scalar_prod_smult_distrib[symmetric])
     apply (rule fs_carr)
    using assms gso_carrier
    by (auto intro!: sumlist_carrier)

	  also have "?sum2 = - sumlist (map (\<lambda>k. (- \<mu> i k) \<cdot>\<^sub>v (gso k)) [0..<l])"
	    apply(rule eq_vecI)
	    using fs_carr gso_carrier assms i_l_m
	    by(auto simp: sum_negf[symmetric] dim_sumlist sumlist_nth dim_gso intro!: sum.cong)

	  also have "\<dots> = - sumlist (map (\<lambda>k. \<kappa> i l k \<cdot>\<^sub>v fs ! k) [0..<l])"
	    using assms gso_carrier assms 
	    apply (subst \<kappa>_def)
	    by (auto)

	  also have "(d l \<cdot>\<^sub>v - sumlist (map (\<lambda>k. \<kappa> i l k \<cdot>\<^sub>v fs ! k) [0..<l])) =
		     (- sumlist (map (\<lambda>k. (d l * \<kappa> i l k) \<cdot>\<^sub>v fs ! k) [0..<l]))"
	    apply(rule eq_vecI)
	    using fs_carr smult_carrier_vec dim_fs
	    using dim_fs i_l_m 
	    by (auto simp: smult dim_sumlist sumlist_nth sum_distrib_left intro!: sum.cong)

	  finally have id: " \<sigma> l i j = fs ! j \<bullet> - M.sumlist (map (\<lambda>k. d l * \<kappa> i l k \<cdot>\<^sub>v fs ! k) [0..<l]) " .
	  (* now we are able to apply d_\<kappa>_int *)
	  show "\<sigma> l i j \<in> \<int>" unfolding id
	    using i_l_m fs_carr assms fs_int d_\<kappa>_int
	    by (auto simp: dim_sumlist sumlist_nth smult 
	        intro!: sumlist_carrier Ints_minus Ints_sum Ints_mult[of _ "fs ! _ $ _"]  Ints_scalar_prod[OF fs_carr])
	qed

end (* gram_schmidt_fs_int *)


context fs_int (* TODO: think of locale structure: Gram_Schmidt should not depend on LLL,
	  but currently d\<mu> is defined in locale LLL *)
begin

context
  fixes fs :: "int vec list"
  assumes indep: "lin_indep fs" 
	  and len: "length fs = m" 
begin

fun \<sigma>s and \<mu>' where 
  "\<sigma>s 0 i j = \<mu>' i 0 * \<mu>' j 0" 
| "\<sigma>s (Suc l) i j = (\<mu>' (Suc l) (Suc l) * \<sigma>s l i j + \<mu>' i (Suc l) * \<mu>' j (Suc l)) div \<mu>' l l" 
| "\<mu>' i j = (if j = 0 then fs ! i \<bullet> fs ! j else \<mu>' (j - 1) (j - 1) * (fs ! i \<bullet> fs ! j) - \<sigma>s (j - 1) i j)"

declare \<mu>'.simps[simp del]

interpretation gs1: gram_schmidt_fs_int "RAT fs" n "TYPE(rat)"
  by (standard)
    (use indep len gs.lin_indpt_list_def fs_intD(4) fs_int_def indep in
      \<open>auto intro!: vec_hom_Ints simp add: gs.lin_indpt_list_def \<close>)

lemma lenR: "length (RAT fs) = m" using len by auto
lemma fs_carrier: "set fs \<subseteq> carrier_vec n" using indep unfolding gs.lin_indpt_list_def by auto

lemmas gs_\<sigma>_simps = gs1.\<sigma>_via_\<mu>'
lemmas gs_\<mu>'_simps = gs1.\<mu>'_via_\<sigma>

lemma \<sigma>s_\<mu>': "l < j \<Longrightarrow> j \<le> i \<Longrightarrow> i < m \<Longrightarrow> of_int (\<sigma>s l i j) = gs1.\<sigma> (Suc l) i j" 
  "i < m \<Longrightarrow> j \<le> i \<Longrightarrow> of_int (\<mu>' i j) = gs1.\<mu>' i j" 
proof (induct l i j and i j rule: \<sigma>s_\<mu>'.induct)
  case (1 i j)
  thus ?case by (simp add: gs_\<sigma>_simps)
next
  case (2 l i j)
  have l: "Suc l < j" by fact
  have j: "j \<le> i" by fact
  have i: "i < m" by fact
  from l j i have jm: "j < m" and lm: "Suc l < m" and lj: "l < j" and li: "Suc l \<le> i" 
    and lj': "Suc l \<le> j" and lm': "l < m" and sslm: "Suc (Suc l) \<le> m" by auto
  note IH1 = 2(1)[OF lm le_refl]
  note IH2 = 2(2)[OF lj j i]
  note IH3 = 2(3)[OF i li]
  note IH4 = 2(4)[OF jm lj']
  note IH5 = 2(5)[OF lm' le_refl]
  note IHs = IH1 IH2 IH3 IH4 IH5
  have id: "(Suc l = 0) = False" "(Suc l - 1) = l" by auto
  have "gs1.\<sigma>(Suc (Suc l)) i j \<in> \<int>" 
    by (rule gs1.\<sigma>_integer, insert l j i fs_carrier len, auto)
  thus ?case unfolding gs_\<sigma>_simps[of "Suc l"] id if_False \<sigma>s.simps
	    IHs[symmetric] of_int_mult[symmetric] of_int_add[symmetric]
	  by (rule exact_division)
next
  case (3 i j)
  note i = 3(3)
  note j = 3(4)
  show ?case
  proof (cases "j = 0")
    case True
    then have "x < dim_vec (fs ! 0) \<Longrightarrow> rat_of_int (fs ! i $v x) = of_int_hom.vec_hom (fs ! i) $v x" for x
      using 3 gs1.f_dim lenR by auto
    then show ?thesis
      by (subst gs_\<mu>'_simps, insert i j True fs_carrier len, auto simp: scalar_prod_def \<mu>'.simps)
  next
    case False
    with i j have jm: "j - 1 < m" and jj: "j - 1 < j" by auto
    from i have im: "i < length (RAT fs)"
      using len by auto
    note IH1 = 3(1)[OF False jm le_refl]
    note IH2 = 3(2)[OF False jj j i]
    from False have id: "(j = 0) = False" "Suc (j - 1) = j" by auto
    have "x < dim_vec (fs ! j) \<Longrightarrow> rat_of_int (fs ! i $v x) = of_int_hom.vec_hom (fs ! i) $v x" for x
      using 3 gs1.f_dim lenR by auto
	  then show ?thesis 
	    unfolding gs_\<mu>'_simps[OF j im] 
	    unfolding \<mu>'.simps[of i j] of_int_mult of_int_diff id if_False
	    unfolding IH1 IH2 id
	    using i j len fs_carrier
	    by (auto simp: scalar_prod_def)
	qed
qed  

lemma \<mu>': assumes "i < m" "j \<le> i"
  shows "\<mu>' i j = d\<mu> fs i j"
    "j = i \<Longrightarrow> \<mu>' i j = d fs (Suc i)"  
proof -
  let ?r = rat_of_int
  have "fs_int fs"
    unfolding fs_int_def using indep len by simp
  note d\<mu> = d\<mu>[OF this assms(2,1)]
  have "?r (\<mu>' i j) = gs1.\<mu>'  i j" by (rule \<sigma>s_\<mu>'(2)[OF assms])
  also have "\<dots> = ?r (d\<mu> fs i j)" unfolding gs1.\<mu>'_def d\<mu>
    by (subst of_int_Gramian_determinant, insert assms len lenR fs_carrier, auto simp: d_def subset_eq)
  finally show 1: "\<mu>' i j = d\<mu> fs i j" by simp
  assume j: "j = i" 
  have "?r (\<mu>' i j) = ?r (d\<mu> fs i j)" unfolding 1 ..
  also have "\<dots> = ?r (d fs (Suc i))" unfolding d\<mu> unfolding j by (simp add: gs1.\<mu>.simps)
  finally show "\<mu>' i j = d fs (Suc i)" by simp
qed

lemma sigma_array: assumes mm: "mm \<le> m" and j: "j < mm" 
  shows "l \<le> j \<Longrightarrow> sigma_array (IArray.of_fun (\<lambda>i. IArray.of_fun (\<mu>' i) (if i = mm then Suc j else Suc i)) (Suc mm))
	     (IArray.of_fun (\<mu>' mm) (Suc j)) (IArray.of_fun (\<mu>' (Suc j)) (if Suc j = mm then Suc j else Suc (Suc j))) (\<mu>' l l) l =
	    \<sigma>s l mm (Suc j)"
proof (induct l)
  case 0
  show ?case unfolding \<sigma>s.simps sigma_array.simps[of _ _ _ _ 0]
    using mm j by (auto simp: nth_append)
next
  case (Suc l)
  hence l: "l < j" "l \<le> j" by auto
  have id: "(Suc l = 0) = False" "Suc l - 1 = l" by auto
  have ineq: "Suc l < Suc mm" "l < Suc mm" 
    "Suc l < (if Suc l = mm then Suc j else Suc (Suc l))" 
    "Suc l < (if Suc j = mm then Suc j else Suc (Suc j))" 
    "l < (if l = mm then Suc j else Suc l)" 
    "Suc l < Suc j" 
    using mm l j by auto
  note IH = Suc(1)[OF l(2)]
  show ?case unfolding sigma_array.simps[of _ _ _ _ "Suc l"] id if_False Let_def IH
	    of_fun_nth[OF ineq(1)] of_fun_nth[OF ineq(2)] of_fun_nth[OF ineq(3)] 
	    of_fun_nth[OF ineq(4)] of_fun_nth[OF ineq(5)] of_fun_nth[OF ineq(6)]
	  unfolding \<sigma>s.simps by simp
qed

lemma dmu_array_row_main: assumes mm: "mm \<le> m" shows
  "j \<le> mm \<Longrightarrow> dmu_array_row_main (IArray fs) (IArray fs !!  mm) mm
	    (IArray.of_fun (\<lambda>i. IArray.of_fun (\<mu>' i) (if i = mm then Suc j else Suc i)) (Suc mm))    
	     j = IArray.of_fun (\<lambda>i. IArray.of_fun (\<mu>' i) (Suc i)) (Suc mm)" 
proof (induct "mm - j" arbitrary: j)
  case 0
  thus ?case unfolding dmu_array_row_main.simps[of _ _ _ _ j] by simp
next
  case (Suc x j)
  hence prems: "x = mm - Suc j" "Suc j \<le> mm" and j: "j < mm" by auto
  note IH = Suc(1)[OF prems]
  have id: "(j = mm) = False" "(mm = mm) = True" using Suc(2-) by auto
  have id2: "IArray.of_fun (\<mu>' mm) (Suc j) = IArray (map (\<mu>' mm) [0..<Suc j])" 
    by simp
  have id3: "IArray fs !! mm = fs ! mm" "IArray fs !! Suc j = fs ! Suc j" by auto
  have le: "j < Suc j" "Suc j < Suc mm" "mm < Suc mm" "j < Suc mm" 
    "j < (if j = mm then Suc j else Suc j)" using j by auto
  show ?case unfolding dmu_array_row_main.simps[of _ _ _ _ j] 
      IH[symmetric] Let_def id if_True if_False id3
      of_fun_nth[OF le(1)] of_fun_nth[OF le(2)]
      of_fun_nth[OF le(3)] of_fun_nth[OF le(4)]
      of_fun_nth[OF le(5)]  
      sigma_array[OF mm j le_refl, folded id2]
      iarray_length_of_fun iarray_update_of_fun iarray_append_of_fun
  proof (rule arg_cong[of _ _ "\<lambda> x. dmu_array_row_main _ _ _ x _"], rule iarray_cong', goal_cases)
    case (1 i)
    show ?case unfolding of_fun_nth[OF 1] using j 1
      by (cases "i = mm", auto simp: \<mu>'.simps[of _ "Suc j"])
  qed
qed

lemma dmu_array_row: assumes mm: "mm \<le> m" shows
  "dmu_array_row (IArray fs) (IArray.of_fun (\<lambda>i. IArray.of_fun (\<mu>' i) (Suc i)) mm) mm =
	    IArray.of_fun (\<lambda>i. IArray.of_fun (\<mu>' i) (Suc i)) (Suc mm)" 
proof -
  have 0: "0 \<le> mm" by auto
  show ?thesis unfolding dmu_array_row_def Let_def dmu_array_row_main[OF assms 0, symmetric]
    unfolding iarray_append.simps IArray.of_fun_def id map_append list.simps
    by (rule arg_cong[of _ _ "\<lambda> x. dmu_array_row_main _ _ _ (IArray x) _"], rule nth_equalityI, 
	      auto simp: nth_append \<mu>'.simps[of _ 0])
qed

lemma dmu_array: assumes "mm \<le> m" 
  shows "dmu_array (IArray fs) m (IArray.of_fun (\<lambda> i. IArray.of_fun (\<lambda> j. \<mu>' i j) (Suc i)) mm) mm 
	  = IArray.of_fun (\<lambda> i. IArray.of_fun (\<lambda> j. \<mu>' i j) (Suc i)) m" 
	using assms
proof (induct mm rule: wf_induct[OF wf_measure[of "\<lambda> mm. m - mm"]])
  case (1 mm)
  show ?case
  proof (cases "mm = m")
    case True
    thus ?thesis unfolding dmu_array.simps[of _ _ _ mm] by simp
  next
    case False
    with 1(2-)
    have mm: "mm \<le> m" and id: "(Suc mm = 0) = False" "Suc mm - 1 = mm" "(mm = m) = False"
      and prems: "(Suc mm, mm) \<in> measure ((-) m)" "Suc mm \<le> m" by auto
    have list: "[0..<Suc mm] = [0..< mm] @ [mm]" by auto
    note IH = 1(1)[rule_format, OF prems]
    show ?thesis unfolding dmu_array.simps[of _ _ _ mm] id if_False Let_def 
      unfolding dmu_array_row[OF mm] IH[symmetric]
      by (rule arg_cong[of _ _ "\<lambda> x. dmu_array _ _ x _"], rule iarray_cong, auto)
  qed
qed

lemma d\<mu>_impl: "d\<mu>_impl fs = IArray.of_fun (\<lambda> i. IArray.of_fun (\<lambda> j. d\<mu> fs i j) (Suc i)) m" 
  unfolding d\<mu>_impl_def len using dmu_array[of 0]
  by (auto simp: \<mu>')
end
end


end
