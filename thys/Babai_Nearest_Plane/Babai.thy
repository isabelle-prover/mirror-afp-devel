theory Babai
  imports Babai_Algorithm
          
begin

text \<open>This theory contains the proof of correctness of the algorithm. The main theorem is
 "theorem Babai-Correct", under the locale "Babai-with-assms".
To use the theorem, one needs to show that lattice, the vectors in the lattice basis, and the target
vector all have the same dimension, that the lattice basis vectors are linearly independent and form an invertible 
matrix, and that the lattice basis is LLL-weakly-reduced.

\<close>

section \<open> Locale setup for Babai \<close>

locale Babai = 
  fixes M :: "int vec list"
  fixes t :: "rat vec"
  assumes length_M: "length M = dim_vec t" (*Clean up by turning these into lemmas*)
begin

abbreviation n where  "n \<equiv> length M"
definition \<alpha> where "(\<alpha>::rat) = 4/3"
sublocale LLL n n M \<alpha>.



abbreviation coset::"rat vec set" where "coset\<equiv>{(map_vec rat_of_int  x)-t|x. x\<in>L}" 
abbreviation Mt where "Mt \<equiv> gram_schmidt n (RAT M)"

definition s :: "nat \<Rightarrow> rat vec" where
  "s i = Babai_Help (uminus t) (RAT M) Mt i"

definition closest_distance_sq:: "real" where
  "closest_distance_sq = Inf {real_of_rat (sq_norm x::rat) |x. x \<in> coset}"
end

  
text \<open>Locale setup with additional assumptions required for main theorem\<close>

locale Babai_with_assms = Babai+
  fixes mat_M mat_M_inv:: "rat mat"
  assumes basis: "lin_indep M"
  defines "mat_M \<equiv> mat_of_cols n (RAT M)"
  defines "mat_M_inv \<equiv> 
    (if (invertible_mat mat_M) then SOME B. (inverts_mat B mat_M) \<and> (inverts_mat mat_M B) else (0\<^sub>m n n))"
  assumes inv:"invertible_mat mat_M"
  assumes reduced:"weakly_reduced M n" 
  assumes non_trivial:"0<n"
begin



lemma dim_vecs_in_M:
  shows "\<forall>v \<in> set M. dim_vec v = length M"
  using basis unfolding gs.lin_indpt_list_def by force


lemma inv1:"mat_M * mat_M_inv = 1\<^sub>m n"
proof-
  have dim_m:"dim_row mat_M = n" using dim_vecs_in_M unfolding mat_M_def by fastforce
  then have "inverts_mat mat_M mat_M_inv" using inv
  unfolding mat_M_inv_def
  by (smt (verit, ccfv_SIG) invertible_mat_def some_eq_imp)
  then show ?thesis using dim_m unfolding inverts_mat_def by argo
qed

lemma inv2:"mat_M_inv * mat_M = 1\<^sub>m n"
proof-
  have dim_m:"dim_col mat_M = n" unfolding mat_M_def by fastforce
  have "inverts_mat mat_M_inv mat_M" using inv
  unfolding mat_M_inv_def
  by (smt (verit, ccfv_SIG) invertible_mat_def some_eq_imp)
  then have inv:"mat_M_inv * mat_M = 1\<^sub>m (dim_row mat_M_inv)"
    unfolding inverts_mat_def by blast
  then have dim_n:"dim_col (1\<^sub>m (dim_row mat_M_inv)) = n"
    using dim_m index_mult_mat(3)[of mat_M_inv mat_M] by fastforce
  have "(dim_row mat_M_inv)= n"
  proof(rule ccontr)
    assume "(dim_row mat_M_inv)\<noteq> n"
    then have "dim_col (1\<^sub>m (dim_row mat_M_inv)) \<noteq> n"
      by auto
    then show False using dim_n by blast
  qed
  then show ?thesis using inv by argo
qed


sublocale rats: vec_module "TYPE(rat)" n.



lemma M_dim: "dim_row mat_M = n" "dim_col mat_M = n"
   apply (metis index_mult_mat(2) index_one_mat(2) inv1)
  by (metis index_mult_mat(3) index_one_mat(3) inv2)

lemma M_inv_dim: "dim_row mat_M_inv = n" "dim_col mat_M_inv = n"
   apply (metis M_dim(1) index_mult_mat(2) inv1 inv2)
  by (metis index_mult_mat(3) index_one_mat(3) inv1)


lemma Babai_to_Help:                          
  shows "s n = Babai_Algorithm.Babai (uminus t) (RAT M)" 
  using Babai.Babai_def Babai.s_def Babai_Algorithm.Babai_def Babai_axioms by force

section \<open>Coordinates\<close>

text \<open> This section sets up the use of the lattice basis and its GS orthogonalization
as coordinate systems and some properties of that coordinate system. The important lemma here
is coord-invariance, which shows that after step i of the algorithm, all coordinates (in both
systems) after n-i are invariant. \<close>

definition lattice_coord :: "rat vec \<Rightarrow> rat vec"
  where "lattice_coord a = mat_M_inv *\<^sub>v a"

lemma dim_preserve_lattice_coord:
  fixes v::"rat vec"
  assumes "dim_vec v=n"
  shows "dim_vec (lattice_coord v) = n" unfolding lattice_coord_def mat_M_inv_def using M_inv_dim 
  by (simp add: mat_M_inv_def)
lemma vec_to_col:
  assumes "i < n"
  shows "(RAT M)!i = col mat_M i"
  unfolding mat_M_def
  by (metis Babai_with_assms_axioms Babai_with_assms_axioms_def Babai_with_assms_def M_dim(2) 
      assms cols_mat_of_cols cols_nth gs.lin_indpt_list_def mat_M_def)

lemma unit:
  assumes "i < n"
  shows "lattice_coord ((RAT M)!i) = unit_vec n i"
  using assms inv2 unfolding lattice_coord_def
  by (metis M_dim(1) M_dim(2) M_inv_dim(2) carrier_matI col_mult2 col_one vec_to_col)

lemma linear:
  fixes i::nat
  fixes v1::"rat vec"
  and v2:: "rat vec"
  and q:: rat
  assumes "dim_vec v1 = n"
  assumes dim_2:"dim_vec v2 = n"
  assumes "0\<le>i"
  assumes dim_i:"i<n"
  shows "(lattice_coord (v1+(q\<cdot>\<^sub>vv2)))$i = (lattice_coord v1)$i + q*((lattice_coord v2)$i)"
  using assms
proof(-)
  have linear_vec:"(lattice_coord (v1+(q\<cdot>\<^sub>vv2))) = (lattice_coord v1) + q\<cdot>\<^sub>v((lattice_coord v2))"
  unfolding lattice_coord_def
  by (metis (mono_tags, opaque_lifting) M_inv_dim(2) assms(1) assms(2) carrier_mat_triv 
      carrier_vec_dim_vec mult_add_distrib_mat_vec mult_mat_vec smult_carrier_vec)
  then have 2: "(lattice_coord (v1+(q\<cdot>\<^sub>vv2)))$i= ((lattice_coord v1) + q\<cdot>\<^sub>v((lattice_coord v2)))$i" by auto
  also have dim_v2: "dim_vec (lattice_coord v2) = n" using dim_preserve_lattice_coord dim_2 by blast
  then have i_in_range: "i<dim_vec (q\<cdot>\<^sub>v(lattice_coord v2))" using dim_v2 dim_i by simp
  also have 3:"((lattice_coord v1) + q\<cdot>\<^sub>v((lattice_coord v2)))$i=(lattice_coord v1)$i+ 
              (q\<cdot>\<^sub>v(lattice_coord v2))$i" using i_in_range by simp
  also have 4: "(q\<cdot>\<^sub>v(lattice_coord v2))$i=q*(lattice_coord v2)$i" using i_in_range by simp
  thus ?thesis unfolding vec_def using linear_vec 2 3 4 by simp
qed

lemma sub_s:
  fixes i::nat
  assumes "0\<le>i"
  assumes "i<n"
  shows "s (Suc i) = (s i) -
( (rat_of_int (calculate_c (s i) Mt (Suc i) ) ) \<cdot>\<^sub>v (RAT M)!( (dim_vec (s i)) -(Suc i))) "
  using assms Babai_Help.simps[of "-t" "RAT M" Mt] unfolding s_def
  by (metis update_s.simps)

lemma M_locale_1:
  shows "gram_schmidt_fs_Rn n (RAT M)"
  by (smt (verit) M_dim(1) M_dim(2) carrier_dim_vec dim_col gram_schmidt_fs_Rn.intro in_set_conv_nth 
      mat_M_def mat_of_cols_carrier(3) subset_code(1) vec_to_col)

lemma M_locale_2:
  shows "gram_schmidt_fs_lin_indpt n (RAT M)"
  using basis M_locale_1 gram_schmidt_fs_lin_indpt.intro[of n "(RAT M)"]  unfolding gs.lin_indpt_list_def 
  using gram_schmidt_fs_lin_indpt_axioms.intro by blast


lemma more_dim: "length (RAT M) = n"
  by simp

lemma Mt_gso_connect:
  fixes j::nat
  assumes "j<n"
  shows "Mt!j = gs.gso j"
proof(-)
 have "Mt = map gs.gso[0..<n]"
    using M_locale_1 gram_schmidt_fs_Rn.main_connect[of n "(RAT M)"]
    by fastforce
  then show ?thesis 
    using assms
    by simp
qed

lemma access_index_M_dim: 
  assumes "0 \<le> i"
  assumes "i < n"
  shows "dim_vec (map of_int_hom.vec_hom M ! i) =  n"
  using assms dim_vecs_in_M 
  by auto

lemma s_dim:
  fixes i::nat
  assumes "i\<le> n"
  shows "dim_vec (s i) = n \<and> (s i) \<in>carrier_vec n"
  using assms
  proof(induct i)
  case 0
  have unfold1:"s 0 = Babai_Help (uminus t) (RAT M) Mt 0" unfolding s_def by simp
  also have unfold2:"Babai_Help (uminus t) (RAT M) Mt 0 = uminus t" unfolding Babai_Help.simps by simp
  also have unfold3:"s 0 = uminus t" using unfold1 unfold2 by simp
  also have dim_eq:"dim_vec (s 0) = dim_vec (uminus t)" using unfold3 by simp
  moreover have dim_minus:"dim_vec (uminus t) = n" by (metis index_uminus_vec(2) length_M)
  then have "dim_vec (s 0) = n"
    using dim_eq dim_minus
    by simp
  then have "(s 0) \<in> carrier_vec n"
    using carrier_vecI[of "(s 0)" n]
    by simp
  then show ?case
    by simp
 next
  case (Suc i)
  then have leq: "i\<le>n" by linarith
  have sub:"s (Suc i) = (s i) - ( (rat_of_int (calculate_c (s i) Mt (Suc i) ) ) \<cdot>\<^sub>v (RAT M)!( (dim_vec (s i)) -(Suc i))) "
    using sub_s Suc 
    by auto
  moreover have prev_s_dim:"(s i)\<in>carrier_vec n"
    using Suc
    by simp
  moreover have "dim_vec (s i)=n"
    using Suc
    by simp
  then have "0\<le>(dim_vec (s i)) -(Suc i)\<and> (dim_vec (s i)) -(Suc i)<n"
    using Suc
    by linarith
  then have dim_m:"(dim_vec  ((RAT M)!( (dim_vec (s i)) -(Suc i)))) = n"
    using access_index_M_dim[of "(dim_vec (s i)) -(Suc i)"]
    by simp
  then have dim_qm:"dim_vec ( (rat_of_int (calculate_c (s i) Mt (Suc i) ) ) \<cdot>\<^sub>v 
            (RAT M)!( (dim_vec (s i)) -(Suc i))) = n"
    by simp
  then have final_dim:"dim_vec ((s i) -
( (rat_of_int (calculate_c (s i) Mt (Suc i) ) ) \<cdot>\<^sub>v (RAT M)!( (dim_vec (s i)) -(Suc i)))) = n"
    using index_minus_vec(2) prev_s_dim dim_qm
    by metis
   show ?case 
    using final_dim sub carrier_vecI[of "s i" n]
    by (metis carrier_vec_dim_vec)
 qed 

lemma dim_vecs_in_Mt:
  fixes i::nat
  assumes "i<n"
  shows "dim_vec (Mt!i) = n"
  using Mt_gso_connect[of "i"] M_locale_1 assms gram_schmidt_fs_Rn.gso_dim
  by fastforce
lemma upper_tri:
  fixes i::nat
    and j::nat
  assumes "j>i"
  assumes "j<n"
  shows "((RAT M)!i)\<bullet> (Mt!j) =0"
proof(-)
   have "(gs.gso j)\<bullet> (RAT M)!i= 0"
    using gram_schmidt_fs_lin_indpt.gso_scalar_zero[of n "(RAT M)" j i]
        Mt_gso_connect[of "j"]
        assms
        M_locale_2  
        more_dim
    by presburger
  then have "(Mt!j)\<bullet> ((RAT M)!i)= 0"
    using Mt_gso_connect[of "j"] assms
    by simp
  then show ?thesis
    using comm_scalar_prod[of "(Mt!j)" n  "((RAT M)!i)"]
          carrier_vecI[of "(Mt!j)" n]
          carrier_vecI[of "((RAT M)!i)" n]
          access_index_M_dim[of i]
          dim_vecs_in_Mt[of j]
          assms
    by auto
qed
lemma one_diag:
  fixes i::nat
  assumes "0\<le>i"
  assumes "i<n"
  shows "((RAT M)!i)\<bullet> (Mt!i)=sq_norm (Mt!i)"
proof(-)
   have mu:"((RAT M)!i)\<bullet>(Mt!i) = (gs.\<mu> i i)*sq_norm (Mt!i) "
    using gram_schmidt_fs_lin_indpt.fi_scalar_prod_gso[of "n" "(RAT M)" i i]
          M_locale_2
          assms
          more_dim
          Mt_gso_connect
    by presburger
  moreover have "gs.\<mu> i i=1"
    by (meson gs.\<mu>.elims order_less_imp_not_eq2) 
  then show ?thesis
    using mu
    by fastforce
qed


lemma coord_invariance:
  fixes j::nat
  fixes k::nat
  fixes i::nat
  assumes "k\<le>j"
  assumes "j+i\<le>n"
  assumes "k>0"
  shows "(lattice_coord (s (j+i)))$(n-k) = (lattice_coord (s j))$(n-k)
    \<and> (s (j+i)) \<bullet> Mt!(n-k)=(s j) \<bullet> Mt!(n-k)"
  using assms
proof(induct i)
  case 0
  show ?case by simp
next 
  case (Suc i)
  have "j+ (Suc i) = Suc (j+i)" by simp
  then have 1:"s (Suc (j+i)) =s (j + (Suc i))" by simp
  then have sub:"s (Suc (j+i) ) = 
    (s (j+i)) -( (rat_of_int (calculate_c (s (j+i)) Mt (Suc (j+i)) ) )
       \<cdot>\<^sub>v (RAT M)!( (dim_vec (s (j+i))) -(Suc (j+i)) ) )" 
    using sub_s[of "j+i "] Suc(3) by linarith
  then have dim1: "dim_vec (s (j + i)) = n"
    using s_dim[of "j+i"] using Suc(3) by auto
  then have dim2: "dim_vec
     (map of_int_hom.vec_hom M !
      (dim_vec (s (j + i)) - Suc (j + i))) = n"
    using access_index_M_dim[of "n - Suc (j + i)"] Suc(3)
    by auto
  have k_in_range:"0\<le>(n-k) \<and>(n-k)<n" using Suc(2) Suc(3) Suc(4)
    by simp 
  have index_in_range:"0\<le>(dim_vec (s (j+i))) -(Suc (j+i))\<and>(dim_vec (s (j+i))) -(Suc (j+i))<n"
    using Suc(3) s_dim[of "j+i"]
    by simp
  moreover have carriers: "s (j+i) \<in> carrier_vec n\<and>
                    map of_int_hom.vec_hom M ! (dim_vec (s (j + i)) - Suc (j + i))\<in>carrier_vec n"
    using dim1 dim2
          carrier_vecI[of "s (j + i)" n]
          carrier_vecI[of "map of_int_hom.vec_hom M ! (dim_vec (s (j + i)) - Suc (j + i))" n]
    by fast

  let ?sSuc = "(s (Suc (j+i)))"
  let ?si = "(s (j+i))"
  let ?c = "(rat_of_int (calculate_c (s (j+i)) Mt (Suc (j+i)) ) )"
  let ?ind = "(dim_vec (s (j+i))) -(Suc (j+i))"

  have "?si - ?c\<cdot>\<^sub>v (RAT M)!?ind = ?si + (-?c)\<cdot>\<^sub>v (RAT M)!?ind"
    using minus_add_uminus_vec[of ?si n "?c\<cdot>\<^sub>v (RAT M)!?ind"] 
          carriers
    by fastforce
  then have "(lattice_coord (?si - ?c\<cdot>\<^sub>v (RAT M)!?ind))$(n-k) = 
    (lattice_coord(?si))$(n-k) + (-?c)* (lattice_coord((RAT M)!?ind))$(n-k)"
    using linear[of ?si "(RAT M)!?ind" "n-k" "-?c"] dim1 dim2 k_in_range
    by metis
  then have lin_lattice_coord:"(lattice_coord (?sSuc))$(n-k) = 
    (lattice_coord(?si))$(n-k) - ?c* (lattice_coord((RAT M)!?ind))$(n-k)"
    using sub
    by algebra
  have neq:"Suc (j+i)\<noteq>k" using Suc(3) Suc(2) by auto
  moreover have "((dim_vec (s (j+i))) -(Suc (j+i)))\<noteq> (n-k)" 
    using s_dim[of "j+i"] neq Suc(3)
    by (metis Suc(2) \<open>j + Suc i = Suc (j + i)\<close> diff_0_eq_0 diff_cancel2 
          diff_commute diff_diff_cancel diff_diff_eq diff_is_0_eq dim1)
  moreover have "(lattice_coord ((RAT M)!( (dim_vec (s (j+i))) -(Suc (j+i))) ) )$(n-k)= 
                  (unit_vec n ( (dim_vec (s (j+i))) -(Suc (j+i))))$(n-k)"
    using unit[of "dim_vec (s (j+i)) -(Suc (j+i))"] index_in_range by presburger 
  then have zero:"(lattice_coord ((RAT M)!( (dim_vec (s (j+i))) -(Suc (j+i))) ) )$(n-k) = 0"
    unfolding unit_vec_def
    using neq calculation(3) k_in_range by fastforce
  then have "(lattice_coord (s (Suc (j+i))) )$(n-k) = ( (lattice_coord (s (j+i)))$(n-k)) - 
(rat_of_int (calculate_c (s (j+i)) Mt (Suc (j+i)) ) )
*0"
    using zero lin_lattice_coord by presburger
  then have conclusion1:"(lattice_coord (s (Suc (j+i))) )$(n-k) = ( (lattice_coord (s (j+i)))$(n-k))"
    by simp
  have init_sub:"(s (Suc (j+i)))\<bullet> Mt!(n-k) =  ((s (j+i)) -
( (rat_of_int (calculate_c (s (j+i)) Mt (Suc (j+i)) ) ) \<cdot>\<^sub>v (RAT M)!( (dim_vec (s (j+i))) -(Suc (j+i)) ) ))
  \<bullet> (Mt!(n-k))"
    using sub
    by simp
  moreover have carrier_prod:"( (rat_of_int (calculate_c (s (j+i)) Mt (Suc (j+i)) ) ) 
\<cdot>\<^sub>v (RAT M)!( (dim_vec (s (j+i))) -(Suc (j+i)) ) )\<in>carrier_vec n"
    using smult_carrier_vec[of "(rat_of_int (calculate_c (s (j+i)) Mt (Suc (j+i)) ) )" 
          "(RAT M)!( (dim_vec (s (j+i))) -(Suc (j+i)) )" n]  carrier_vecI dim2 by blast    
  moreover have l:"((s (j+i)) -
( (rat_of_int (calculate_c (s (j+i)) Mt (Suc (j+i)) ) ) \<cdot>\<^sub>v (RAT M)!( (dim_vec (s (j+i))) -(Suc (j+i)) ) ))
  \<bullet> (Mt!(n-k)) = (s (j+i))\<bullet> (Mt!(n-k)) - ( (rat_of_int (calculate_c (s (j+i)) Mt (Suc (j+i)) ) ) 
          \<cdot>\<^sub>v (RAT M)!( (dim_vec (s (j+i))) -(Suc (j+i)) ) )\<bullet> (Mt!(n-k))"
    using s_dim[of "j+i"]
        assms(2)
        access_index_M_dim
        dim_vecs_in_Mt
        carrier_vecI[of "Mt!(n-k)" n]
        carrier_vecI[of "(RAT M)!((dim_vec (s (j+i))) -(Suc (j+i)))" n]
        add_scalar_prod_distrib[of
        "(s (j+i))"
        n
        "(rat_of_int (calculate_c (s (j+i)) Mt (Suc (j+i)) ) ) \<cdot>\<^sub>v (RAT M)!( (dim_vec (s (j+i))) -(Suc (j+i)) )"
        " (Mt!(n-k))"]
    using calculation(5) carriers k_in_range minus_scalar_prod_distrib by blast
     (*Potential TODO: split apart later *)
  moreover then have lin_scalar_prod:"((s (j+i)) -
( (rat_of_int (calculate_c (s (j+i)) Mt (Suc (j+i)) ) ) \<cdot>\<^sub>v (RAT M)!( (dim_vec (s (j+i))) -(Suc (j+i)) ) ))
  \<bullet> (Mt!(n-k)) = (s (j+i))\<bullet> (Mt!(n-k)) -  (rat_of_int (calculate_c (s (j+i)) Mt (Suc (j+i)) ) ) 
                                        * ((RAT M)!( (dim_vec (s (j+i))) -(Suc (j+i)) ) \<bullet> (Mt!(n-k)))"
    by (metis dim2 dim_vecs_in_Mt k_in_range scalar_prod_smult_left)
  moreover have step_past_index:"(dim_vec (s (j+i))) -(Suc (j+i))<n-k"
     using s_dim[of "j+i"] Suc(3) Suc(2)
     by (simp add: calculation(3) diff_le_mono2 dim1 le_SucI nat_less_le trans_le_add1)
  moreover have "( (RAT M)!( (dim_vec (s (j+i))) -(Suc (j+i)) ) \<bullet> (Mt!(n-k)  ) ) = 0"
    using step_past_index upper_tri[of "(dim_vec (s (j+i))) -(Suc (j+i))" "n-k"] Suc(4)
    by simp
  then have "(s (Suc (j+i)))\<bullet> Mt!(n-k) =  (s (j+i))\<bullet> Mt!(n-k) -
( (rat_of_int (calculate_c (s (j+i)) Mt (Suc (j+i)) ) ) *0)"
    using lin_scalar_prod init_sub
    by algebra
  then have conclusion2:"(s (Suc (j+i)))\<bullet> Mt!(n-k) =  (s (j+i))\<bullet> Mt!(n-k)" by auto
  show ?case
    by (metis Suc(2) Suc(3) Suc(4) Suc.hyps Suc_leD \<open>j + Suc i = Suc (j + i)\<close> conclusion1 conclusion2)
qed

lemma small_orth_coord:
  fixes i::nat
  assumes "1\<le>i"
  assumes "i\<le>n"
  shows "abs ( (s i) \<bullet> Mt!(n-i)) \<le>  (sq_norm (Mt!(n-i)))*(1/2) "
proof(-)
  have minus_plus:"Suc (i-1) = i" using assms(1) by auto
  then have init_sub:"s i = (s (i-1))-( (rat_of_int (calculate_c (s (i-1)) Mt i ) ) \<cdot>\<^sub>v (RAT M)!( (dim_vec (s (i-1))) -i))"
    using sub_s[of "i-1"] 
    by (metis (full_types) Suc_le_eq assms(2) less_eq_nat.simps(1))
  then have scalar_distrib:"(s i) \<bullet> Mt!(n-i) = (s (i-1)) \<bullet> Mt!(n-i)-(( (rat_of_int (calculate_c (s (i-1)) Mt i ) ) 
                            \<cdot>\<^sub>v (RAT M)!( (dim_vec (s (i-1))) -i))\<bullet>Mt!(n-i))"
    using add_scalar_prod_distrib[of "(s (i-1))" n "( (rat_of_int (calculate_c (s (i-1)) Mt i ) ) 
                                      \<cdot>\<^sub>v (RAT M)!( (dim_vec (s (i-1))) -i))" "Mt!(n-i)"]
          s_dim[of "i-1"]
          carrier_vecI[of "Mt!(n-i)"]
          carrier_vecI[of "(RAT M)!( (dim_vec (s (i-1))) -i)"]
          access_index_M_dim[of "( (dim_vec (s (i-1))) -i)"]
          dim_vecs_in_Mt[of "n-i"]
          init_sub
          minus_scalar_prod_distrib[of "(s (i-1))" n "( (rat_of_int (calculate_c (s (i-1)) Mt i ) ) 
                                      \<cdot>\<^sub>v (RAT M)!( (dim_vec (s (i-1))) -i))" "Mt!(n-i)"]
    by (metis Suc_leD assms(2) diff_Suc_less gs.smult_closed le0 minus_plus non_trivial)
  also have scalar_commute:"(s (i-1)) \<bullet> Mt!(n-i)-(( (rat_of_int (calculate_c (s (i-1)) Mt i ) ) 
                                                \<cdot>\<^sub>v (RAT M)!( (dim_vec (s (i-1))) -i))\<bullet>Mt!(n-i)) =
             (s (i-1)) \<bullet> Mt!(n-i)-( (rat_of_int (calculate_c (s (i-1)) Mt i ) ) 
                                    *  (((RAT M)!( (dim_vec (s (i-1))) -i)) \<bullet>Mt!(n-i) ))"
    using scalar_prod_smult_left 
          carrier_vecI[of "Mt!(n-i)"]
          carrier_vecI[of "(RAT M)!( (dim_vec (s (i-1))) -i)"]
          access_index_M_dim
          dim_vecs_in_Mt
    (* Takes a second to load *)
    by (smt (verit) Suc_le_D assms(2) diff_less index_minus_vec(2) index_smult_vec(2) 
          init_sub minus_plus s_dim zero_less_Suc)
  moreover have index_in_range: "0\<le>n-i \<and> n-i<n"
    using assms(1) assms(2)
    by simp
  moreover have sq_norm_eq:"((RAT M)!( (dim_vec (s (i-1))) -i)) \<bullet>Mt!(n-i) = sq_norm (Mt!(n-i))"
    using one_diag[of "n-i"]
          s_dim[of "i-1"]
          index_in_range
          assms(1)
          assms(2)
          less_imp_diff_less
    by simp
  then have "(s i) \<bullet> Mt!(n-i) = (s (i-1)) \<bullet> Mt!(n-i)-
            ( (rat_of_int (calculate_c (s (i-1)) Mt i ) ) * sq_norm (Mt!(n-i)))"
    using scalar_distrib scalar_commute sq_norm_eq by argo
  then have final_sub:"abs((s i) \<bullet> Mt!(n-i)) = abs(( (rat_of_int (calculate_c (s (i-1)) Mt i ) ) 
                                                * sq_norm (Mt!(n-i))) -  (s (i-1)) \<bullet> Mt!(n-i)) "
    using abs_minus_commute by simp
  then have round_small:"abs(rat_of_int (calculate_c (s (i-1)) Mt i )-
                        (((s (i-1)) \<bullet> (Mt!( (dim_vec (s (i-1))) - i ) ) ) 
                        / (sq_norm_vec (Mt!( (dim_vec (s (i-1))) - i ) ) ) ))\<le>1/2"
    by (metis calculate_c.simps of_int_round_abs_le)
  moreover have pos:"0\<le> sq_norm (Mt!(n-i))"
    by (simp add: sq_norm_vec_ge_0) 
  then have "(sq_norm (Mt!(n-i)))*abs((rat_of_int (calculate_c (s (i-1)) Mt i )-
              (((s (i-1)) \<bullet> (Mt!( (dim_vec (s (i-1))) - i ) ) ) / 
              (sq_norm_vec (Mt!( (dim_vec (s (i-1))) - i ) ) ) )))
              \<le>(sq_norm (Mt!(n-i)))*(1/2)"
    using pos round_small mult_left_mono by blast
  then have 2:"abs((sq_norm (Mt!(n-i)))*(rat_of_int (calculate_c (s (i-1)) Mt i )-
                (((s (i-1)) \<bullet> (Mt!( (dim_vec (s (i-1))) - i ) ) ) / 
                (sq_norm_vec (Mt!( (dim_vec (s (i-1))) - i ) ) ) )) )\<le>(sq_norm (Mt!(n-i)))*(1/2)"
    using pos by (smt (verit) abs_mult abs_of_nonneg)
  have "i\<le>n"
    using assms(2) by simp
  then have "abs(
              (sq_norm (Mt!(n-i)))*(rat_of_int (calculate_c (s (i-1)) Mt i ))-
            (sq_norm (Mt!(n-i)))*( ((s (i-1)) \<bullet> (Mt!( (dim_vec (s (i-1))) - i ) ) )/
            (sq_norm (Mt!(n-i))) )
            )\<le>(sq_norm (Mt!(n-i)))*(1/2) "
    using 2
          s_dim[of i]
    by (smt (verit) Rings.ring_distribs(4) Suc_leD minus_plus s_dim)
  then have 1:"abs(
              (sq_norm (Mt!(n-i)))*(rat_of_int (calculate_c (s (i-1)) Mt i ))-
              ((s (i-1)) \<bullet> (Mt!( (dim_vec (s (i-1))) - i ) ) )*
            ( (sq_norm (Mt!(n-i)))/(sq_norm (Mt!(n-i))) )
            )\<le>(sq_norm (Mt!(n-i)))*(1/2) "
    using assms(2) s_dim
    by (smt (z3) gs.cring_simprules(14) times_divide_eq_right)
  moreover have nonzero:"sq_norm (Mt!(n-i))\<noteq>0"
    using Mt_gso_connect[of "n-i"] assms
    by (metis M_locale_2 gram_schmidt_fs_lin_indpt.sq_norm_pos index_in_range length_map rel_simps(70))
  moreover have cancel:"(sq_norm (Mt!(n-i)))/(sq_norm (Mt!(n-i)))=1" 
    using nonzero 
    by auto
  moreover have dim_match:"dim_vec (s (i-1)) = n"
    using s_dim[of "i-1"] assms(2)
    by linarith
  then have final_ineq:"abs(
              (sq_norm (Mt!(n-i)))*(rat_of_int (calculate_c (s (i-1)) Mt i ))-
              ((s (i-1)) \<bullet> (Mt!( (dim_vec (s (i-1))) - i ) ) )
            )\<le>(sq_norm (Mt!(n-i)))*(1/2) "
    using 1 cancel
    by (smt (verit) gs.r_one) 
  then have rearrange_final_ineq: "abs( (rat_of_int (calculate_c (s (i-1)) Mt i ))
            * (sq_norm (Mt!(n-i))) -  ((s (i-1)) \<bullet> (Mt!( n - i ) )  ))\<le>(sq_norm (Mt!(n-i)))*(1/2)"
    using dim_match
    by algebra
  show ?thesis
    using final_sub rearrange_final_ineq
    by argo
qed
lemma lattice_carrier: "L\<subseteq> carrier_vec n"
proof-
  have "x\<in>carrier_vec n" if x_def:"x\<in>L" for x
  proof-
    obtain f where f_def:"x = sumlist (map (\<lambda>i. (f i)\<cdot>\<^sub>v M!i ) [0..<n])"
      using x_def unfolding L_def lattice_of_def by fast
    have "(f i)\<cdot>\<^sub>v M!i\<in>carrier_vec n" if "0\<le>i\<and>i<n" for i
      using access_index_M_dim[of i]
      by (metis carrier_vec_dim_vec map_carrier_vec nth_map smult_closed that)
    then have "set (map (\<lambda>i. (f i)\<cdot>\<^sub>v M!i ) [0..<n]) \<subseteq> carrier_vec n" by auto
    then have "sumlist (map (\<lambda>i. (f i)\<cdot>\<^sub>v M!i ) [0..<n]) \<in> carrier_vec n" by simp
    then show "x\<in>carrier_vec n" using f_def by fast
  qed
  then show ?thesis by fast
qed

section \<open>Lattice Lemmas\<close>

lemma lattice_sum_close:
  fixes u::"int vec" and v::"int vec"
  assumes "u\<in>L" "v\<in>L"
  shows "u+v\<in>L"
proof - 
  let ?mM = "mat_of_cols n M"
  have 1:"?mM \<in>carrier_mat n n" using dim_vecs_in_M by fastforce
  have set_M: "set M \<subseteq> carrier_vec n"
    using dim_vecs_in_M carrier_vecI by blast
  have as_mat_mult:"lattice_of M = {y\<in>carrier_vec n. \<exists>x\<in>carrier_vec n. ?mM *\<^sub>v x = y}"
     using lattice_of_as_mat_mult[OF set_M] by blast (*using lattice_of_as_mat_mult*)
  then obtain u1 where u1_def:"u = ?mM *\<^sub>v u1 \<and> u1\<in>carrier_vec n" using assms unfolding L_def by auto
  obtain v1 where v1_def:"v = ?mM *\<^sub>v v1 \<and> v1\<in>carrier_vec n" 
    using assms as_mat_mult unfolding L_def by auto
  have "u1+v1\<in>carrier_vec n" using u1_def v1_def by blast
  moreover have "?mM*\<^sub>v (u1+v1) = u+v" 
    using u1_def v1_def 1 mult_add_distrib_mat_vec[of ?mM n n u1 v1]
    by metis
  moreover have "u+v\<in>carrier_vec n" using assms lattice_carrier by blast
  ultimately show "u+v\<in>L"
    using as_mat_mult unfolding L_def
    by blast
qed


lemma lattice_smult_close:
  fixes u::"int vec" and q::int
  assumes "u\<in>L"
  shows "q\<cdot>\<^sub>v u\<in>L"

proof-
  let ?mM = "mat_of_cols n M"
  have 1:"?mM \<in>carrier_mat n n" using dim_vecs_in_M by fastforce
  have set_M: "set M \<subseteq> carrier_vec n"
    using dim_vecs_in_M carrier_vecI by blast
  have as_mat_mult:"lattice_of M = {y\<in>carrier_vec n. \<exists>x\<in>carrier_vec n. ?mM *\<^sub>v x = y}"
    using lattice_of_as_mat_mult[OF set_M] by blast
  then obtain v::"int vec" where v_def:"u = ?mM *\<^sub>v v\<and>v\<in>carrier_vec n" 
    using assms unfolding L_def by auto
  then have "q\<cdot>\<^sub>v v \<in>carrier_vec n" by blast
  moreover then have "q\<cdot>\<^sub>v u= ?mM *\<^sub>v (q\<cdot>\<^sub>v v)" using 1 v_def by fastforce
  ultimately show "q\<cdot>\<^sub>v u \<in> L"
    by (metis (mono_tags, lifting) L_def as_mat_mult assms mem_Collect_eq smult_closed)
qed 

lemma smult_vec_zero:
  fixes v ::"'a::ring vec"
  shows "0 \<cdot>\<^sub>v v = 0\<^sub>v (dim_vec v)"
  unfolding smult_vec_def vec_eq_iff
  by (auto)

lemma coset_s:
  fixes i::nat
  assumes "i\<le>n"
  shows "s i \<in>coset"
  using assms
proof(induct i)
  case 0
  have "s 0 = -t" unfolding s_def by simp
  moreover have carrier_mt:"-t\<in>carrier_vec n" using length_M carrier_vecI[of t n] by fastforce
  ultimately have pzero:"s 0 = of_int_hom.vec_hom (0\<^sub>v n) -t" by fastforce
  let ?zero = "\<lambda> j. 0"
  have "0<length M" using non_trivial by fast
  then have "M!0 \<in> set M" by force
  then have "M!0\<in>L" using basis_in_latticeI[of M "M!0"] dim_vecs_in_M carrier_vecI L_def
    by blast
  then have "0\<^sub>v n \<in>L" 
    using lattice_smult_close[of "M!0" 0] smult_vec_zero[of "M!0"] access_index_M_dim[of 0] non_trivial
    unfolding L_def
    by fastforce
  then show ?case  using pzero by blast
next
  case (Suc i)
  let ?q = "(rat_of_int (calculate_c (s i) Mt (Suc i) ) )"
  let ?ind = "( (dim_vec (s i)) -(Suc i))"
  have sub:"s (Suc i) = (s i) -
( ?q \<cdot>\<^sub>v (RAT M)!?ind)"
    using sub_s[of i] Suc.prems by linarith
  have "s i \<in>coset" using Suc by auto
  then obtain x where x_def:"x\<in>L \<and> (s i) = of_int_hom.vec_hom x-t" by blast
  have "( ?q \<cdot>\<^sub>v (RAT M)!?ind)\<in> of_int_hom.vec_hom` L"
  proof-
    have "dim_vec (s i) = n" using s_dim[of i] Suc.prems by fastforce
    then have in_range:"?ind<n\<and> 0\<le>?ind" using Suc.prems by simp
    then have com_hom:"(RAT M)!(?ind) = of_int_hom.vec_hom (M!?ind)" by auto
    have "M!?ind\<in>set M" using in_range by simp
    then have mil:"M!?ind \<in> L" using basis_in_latticeI[of M "M!?ind"] dim_vecs_in_M carrier_vecI L_def
      by blast
    moreover have "?q\<cdot>\<^sub>v(of_int_hom.vec_hom (M!?ind)) =
                   of_int_hom.vec_hom ((calculate_c (s i) Mt (Suc i) ) \<cdot>\<^sub>v M!?ind)"
      by fastforce
    moreover have "(calculate_c (s i) Mt (Suc i) ) \<cdot>\<^sub>v M!?ind\<in>L"
      using lattice_smult_close[of "M!?ind" "(calculate_c (s i) Mt (Suc i) )"] mil by simp
    ultimately show "( ?q \<cdot>\<^sub>v (RAT M)!?ind) \<in> of_int_hom.vec_hom` L"
      using com_hom
      by force
  qed
  then obtain y where y_def:"( ?q \<cdot>\<^sub>v (RAT M)!?ind) = of_int_hom.vec_hom y\<and> y\<in>L" by blast
  have carrier_x: "x\<in>carrier_vec n" using lattice_carrier x_def by blast
  have carrier_y: "y\<in>carrier_vec n" using lattice_carrier y_def by blast
  then have carrier_my: "-y\<in>carrier_vec n" by simp
  then have 1:"-( ?q \<cdot>\<^sub>v (RAT M)!?ind) = of_int_hom.vec_hom (-y)" using y_def by fastforce
  then have "s (Suc i) = of_int_hom.vec_hom x-t+ of_int_hom.vec_hom (-y)"
    using sub x_def y_def 1 by fastforce
  then have "s (Suc i) = of_int_hom.vec_hom x + of_int_hom.vec_hom (-y) - t"
    using lattice_carrier x_def y_def length_M
    by fastforce
  moreover have "of_int_hom.vec_hom x + of_int_hom.vec_hom (-y) = of_int_hom.vec_hom (x+ -y)"
    using carrier_my carrier_x by fastforce
  ultimately have 2:"s (Suc i) = of_int_hom.vec_hom (x+ -y) -t "
    by metis
  have "-y = -1 \<cdot>\<^sub>v y" by auto
  then have "-y\<in>L" using lattice_smult_close y_def by simp
  then have "x+-y\<in>L" using lattice_sum_close x_def by simp
  then show ?case using 2 by fast
qed

lemma subtract_coset_into_lattice:
  fixes v::"rat vec"
  fixes w::"rat vec"
  assumes "v\<in>coset"
  assumes "w\<in>coset"
  shows " (v-w)\<in>of_int_hom.vec_hom` L"
proof-
  obtain l1 where l1_def:"v=l1-t\<and> l1\<in>of_int_hom.vec_hom` L" using assms(1) by blast
  obtain l2 where l2_def:"w = l2-t\<and> l2\<in>of_int_hom.vec_hom` L" using assms(2) by blast
  have carrier_l1:"l1 \<in> carrier_vec n" using lattice_carrier l1_def by force
  have carrier_l2:"l2 \<in> carrier_vec n" using lattice_carrier l2_def by force
  obtain l1p where l1p_def:"l1 = of_int_hom.vec_hom l1p \<and> l1p\<in>L" using l1_def by fast
  obtain l2p where l2p_def:"l2 = of_int_hom.vec_hom l2p \<and> l2p\<in>L" using l2_def by fast
  have "-l2p = -1\<cdot>\<^sub>v l2p" using carrier_l2 by fastforce
  then have ml2p:"-l2p\<in>  L" using lattice_smult_close[of l2p "-1"] l2p_def by presburger
  then have "of_int_hom.vec_hom (-l2p)\<in> of_int_hom.vec_hom` L" by simp
  moreover have "of_int_hom.vec_hom (-l2p) = -l2" using l2p_def by fastforce
  then have "l1-l2 = of_int_hom.vec_hom (l1p - l2p)" using l1p_def l2p_def carrier_l1 carrier_l2 by auto
  moreover have "l1p-l2p\<in>L" using lattice_sum_close[of l1p "-l2p"]
     l1p_def l2p_def ml2p carrier_l1 carrier_l2
    by (simp add: minus_add_uminus_vec)
  ultimately have "l1-l2\<in> of_int_hom.vec_hom` L" by fast
  moreover have "v-w = l1-l2" using l1_def l2_def length_M carrier_vecI carrier_l1 carrier_l2 by force
  ultimately show ?thesis by simp
qed
lemma t_in_coset:
  shows "uminus t \<in> coset"
  using coset_s[of 0] Babai_Help.simps unfolding s_def by simp

section "Lemmas on closest distance"

lemma closest_distance_sq_pos: "closest_distance_sq\<ge>0"
proof-
  have  "\<forall>N\<in> {real_of_rat (sq_norm x::rat) |x. x \<in> coset}. 0\<le>N"
    using sq_norm_vec_ge_0 by auto
  moreover have "{real_of_rat (sq_norm x::rat) |x. x \<in> coset}\<noteq>{}" using t_in_coset by blast
  ultimately have "0\<le>Inf {real_of_rat (sq_norm x::rat) |x. x \<in> coset}"
    by (meson cInf_greatest)
  then show ?thesis unfolding closest_distance_sq_def by blast
qed

definition witness:: "rat vec\<Rightarrow>rat \<Rightarrow> bool" 
  where "witness v eps_closest = (sq_norm v \<le> eps_closest \<and> v\<in>coset\<and>dim_vec v = n)"

definition epsilon::real where "epsilon = 11/10"

definition close_condition::"rat \<Rightarrow> bool"
  where "close_condition eps_closest \<equiv> 
(if closest_distance_sq = 0 then 0\<le> real_of_rat eps_closest 
else real_of_rat (eps_closest)>closest_distance_sq)
\<and> (real_of_rat (eps_closest)\<le>epsilon*closest_distance_sq)"

lemma close_rat:
  obtains eps_closest::rat 
  where "close_condition eps_closest"
proof(cases "closest_distance_sq = 0")
  case t:True
  then have "epsilon*closest_distance_sq = real_of_rat (0::rat)" by simp
  then have "real_of_rat (0::rat)\<le> epsilon*closest_distance_sq\<and>closest_distance_sq
            \<le>(real_of_rat (0::rat))"
    using t by force
  then show ?thesis
    using that t unfolding close_condition_def by metis
  next
    case f:False
    then have "0<closest_distance_sq"
      using closest_distance_sq_pos by linarith
    moreover have "(1::real)<epsilon" unfolding epsilon_def by simp
    ultimately have "closest_distance_sq<epsilon*closest_distance_sq" by simp
    then show ?thesis
      using Rats_dense_in_real[of closest_distance_sq "epsilon*closest_distance_sq"] that
      unfolding close_condition_def
      by (metis Rats_cases less_eq_real_def)
qed

definition eps_closest::rat
  where "eps_closest = (if \<exists>r. close_condition r then SOME r. close_condition r else 0)"

lemma eps_closest_lemma: "close_condition eps_closest"
  using close_rat  unfolding eps_closest_def by (metis (full_types))

lemma rational_tri_ineq:
  fixes v::"rat vec"
  fixes w::"rat vec"
  assumes "dim_vec v = dim_vec w"
  shows "(sq_norm (v+w))\<le> 4*(Max {(sq_norm v), (sq_norm w)})"
proof-
  let ?d = "dim_vec w"
  let ?M = "Max {(sq_norm v), (sq_norm w)}"
  have carr_v:"v\<in>carrier_vec ?d" using assms carrier_vecI[of v ?d] by fastforce
  have carr_w:"w\<in>carrier_vec ?d" using carrier_vecI[of w ?d] by fastforce
  have carr_vw:"v+w\<in>carrier_vec ?d" using carr_v carr_w add_carrier_vec by blast
  have "sq_norm (v+w) = (v+w)\<bullet>(v+w)"
    by (simp add: sq_norm_vec_as_cscalar_prod)
  also have "(v+w)\<bullet>(v+w) = v\<bullet>(v+w)+w\<bullet>(v+w)" 
    using add_scalar_prod_distrib[of v ?d w "v+w"]
          carr_v carr_w carr_vw by blast
  also have "v\<bullet>(v+w)+w\<bullet>(v+w) = v\<bullet>v+v\<bullet>w+w\<bullet>v+w\<bullet>w"
    using scalar_prod_add_distrib[of v ?d v w]
          scalar_prod_add_distrib[of w ?d v w]
          carr_v carr_w carr_vw by algebra
  also have "v\<bullet>w=w\<bullet>v"
    using carr_v carr_w comm_scalar_prod by blast
  also have "v\<bullet>v = sq_norm v"
    using sq_norm_vec_as_cscalar_prod[of v] by force
  also have "w\<bullet>w = sq_norm w"
    using sq_norm_vec_as_cscalar_prod[of w] by force
  finally have "sq_norm (v+w) = sq_norm v + sq_norm w + 2*(w\<bullet>v)" by force
  also have b1:"sq_norm v\<le>?M" by force
  also have b2:"sq_norm w\<le>?M" by force
  also have "2*(w\<bullet>v)\<le>2*(Max {(sq_norm v), (sq_norm w)})"
  proof-
    have "(w\<bullet>v)^2\<le> (sq_norm v) * (sq_norm w)"
      using scalar_prod_Cauchy[of w ?d v] carr_w carr_v by algebra
    also have "(sq_norm v) * (sq_norm w)\<le>?M*?M"
      using b1 b2 sq_norm_vec_ge_0[of w] sq_norm_vec_ge_0[of v]
            mult_mono[of "sq_norm v" ?M "sq_norm w" ?M] by linarith
    also have "?M*?M = ?M^2"
      using power2_eq_square[of ?M] by presburger
    finally have "(w\<bullet>v)^2\<le>?M^2" by blast
    also have "(w\<bullet>v)^2=abs(w\<bullet>v)^2" by force
    finally have "abs(w\<bullet>v)^2\<le>?M^2" by presburger
    moreover have "0\<le>abs(w\<bullet>v)" by fastforce
    moreover have "0\<le>?M"
      using sq_norm_vec_ge_0[of w] sq_norm_vec_ge_0[of v] by fastforce
    ultimately have "abs(w\<bullet>v)\<le>?M"
      using  power2_le_imp_le by blast
    also have "(w\<bullet>v)\<le>abs(w\<bullet>v)" by force
    finally show ?thesis by linarith
  qed
  finally show ?thesis by auto
qed

lemma witness_exists:
  shows "\<exists>v. witness v eps_closest"
proof(cases "closest_distance_sq = 0")
  case t:True
  have "eps_closest = 0"
    using eps_closest_lemma t
    unfolding witness_def unfolding close_condition_def
    by auto
  then have equiv:"?thesis = (\<exists>v. v\<in>coset\<and> (dim_vec v = n) \<and> (sq_norm v) \<le> 0)" 
    unfolding witness_def eps_closest_def by auto
  show ?thesis
  proof(rule ccontr)
    assume contra:"\<not>?thesis"
    have "{real_of_rat (sq_norm x::rat) |x. x \<in> coset}\<noteq>{}" using t_in_coset by fast
    then have limit_point:"\<exists>v::rat vec. real_of_rat (sq_norm v) < (eps::real) \<and> v\<in>coset" if "0<eps" for eps
      using t cInf_lessD[of "{real_of_rat (sq_norm x::rat) |x. x \<in> coset}" eps] that
      unfolding closest_distance_sq_def by auto
    moreover have "0<real_of_rat ((sq_norm ((RAT M)!0) )/ (4*\<alpha>^(n-1)))"
    proof-
      have "0<1/(4*\<alpha>^(n-1))" using non_trivial unfolding \<alpha>_def by force
      moreover have "0< (sq_norm ((RAT M)!0))" 
        using gram_schmidt_fs_lin_indpt.sq_norm_pos[of n "RAT M" 0] 
              gram_schmidt_fs_lin_indpt.sq_norm_gso_le_f[of n "RAT M" 0]
              M_locale_2 non_trivial
        by fastforce
      ultimately show ?thesis by auto
    qed
    ultimately obtain v::"rat vec" where v_def:"real_of_rat (sq_norm v) 
                          < real_of_rat ((sq_norm ((RAT M)!0) )/ (4*\<alpha>^(n-1)))\<and> v\<in>coset"
      by presburger
    then have "dim_vec v = n"
      using length_M by force
    then have "0< real_of_rat (sq_norm v)"
      using equiv contra v_def by auto
    then obtain w::"rat vec" where w_def:"real_of_rat (sq_norm w) < real_of_rat (sq_norm v)\<and>w\<in>coset"
      using limit_point by fast
    then have small_w:"real_of_rat (sq_norm w)<real_of_rat ((sq_norm ((RAT M)!0) )/ (4*\<alpha>^(n-1)))"
      using v_def by argo
    have lat:"w-v\<in> of_int_hom.vec_hom` L" using subtract_coset_into_lattice[of w v]
      using v_def w_def by force
    then obtain l where l_def:"l\<in>L\<and>w-v=of_int_hom.vec_hom l" by blast
    then have "of_int_hom.vec_hom l \<in> gs.lattice_of (RAT M)"
      using lattice_of_of_int[of M n l] dim_vecs_in_M carrier_vecI L_def by blast
    then have lat_hom:"w-v \<in> gs.lattice_of (RAT M)" using l_def by simp
    have "sq_norm v \<noteq> sq_norm w" using w_def by auto
    then have neq:"w\<noteq>v" by meson
    have c1:"w\<in>carrier_vec n" using length_M w_def lattice_carrier carrier_dim_vec by fastforce
    moreover have  c2:"v\<in>carrier_vec n" using length_M v_def lattice_carrier carrier_dim_vec by fastforce
    ultimately have c3:"w-v\<in>carrier_vec n" by simp
    have neqzero:"w-v\<noteq>0\<^sub>v n"
    proof(rule ccontr)
      assume c:"\<not>?thesis"
      have "w-v=0\<^sub>v n" using c by blast
      then have "w=v+ 0\<^sub>v n" using c1 c2 c3
        by (smt (verit, ccfv_SIG) gs.M.add.r_inv_ex minus_add_minus_vec minus_cancel_vec minus_zero_vec right_zero_vec)
      then show False using c2 neq by simp
    qed
    then have "w-v \<in> gs.lattice_of (RAT M) - {0\<^sub>v n}" using lat_hom by blast
    moreover have "\<alpha>^(n-1) * (sq_norm (w-v)) < (sq_norm ((RAT M)!0) )"
    proof-
      have "w-v = w+ (-v)" by fastforce
      then have "sq_norm (w-v) = sq_norm (w+(-v))" by simp
      also have "sq_norm (w+(-v)) \<le> 4*Max({sq_norm w, sq_norm (-v)})"
        using rational_tri_ineq[of w "-v"] c1 c2 by fastforce
      also have "sq_norm (-v) = sq_norm v"
      proof-
        have "-v = (-1)\<cdot>\<^sub>v v" by fastforce
        then have "sq_norm (-v) = ((-1)\<cdot>\<^sub>v v)\<bullet>((-1)\<cdot>\<^sub>v v)" using sq_norm_vec_as_cscalar_prod[of "-v"] by force
        then have "sq_norm (-v) = (-1)*(-1)*(v\<bullet>v)" using c1 c2 by simp
        then show ?thesis using sq_norm_vec_as_cscalar_prod[of "v"] by simp
      qed
      also have "Max({sq_norm w, sq_norm (v)})<((sq_norm ((RAT M)!0) )/ (4*\<alpha>^(n-1)))"
        using v_def small_w of_rat_less by auto
      finally have "sq_norm (w-v)<4*((sq_norm ((RAT M)!0) )/ (4*\<alpha>^(n-1)))" by linarith
      then have "sq_norm (w-v)<(sq_norm ((RAT M)!0) )/ (\<alpha>^(n-1))" by linarith
      moreover have p:"0<\<alpha>^(n-1)" unfolding \<alpha>_def by fastforce
      ultimately show ?thesis using p
        by (metis gs.cring_simprules(14) pos_less_divide_eq)
    qed
    ultimately show False
      using gram_schmidt_fs_lin_indpt.weakly_reduced_imp_short_vector[of n "(RAT M)" \<alpha> "w-v"]
            M_locale_2 reduced
      unfolding \<alpha>_def gs.reduced_def L_def by force
  qed
next
  case False
  then have "closest_distance_sq < real_of_rat eps_closest"
    using eps_closest_lemma unfolding eps_closest_def close_condition_def
    by presburger
  moreover have "{real_of_rat (sq_norm x::rat) |x. x \<in> coset}\<noteq>{}" using t_in_coset by fast
  ultimately obtain l where "l\<in>{real_of_rat (sq_norm x::rat) |x. x \<in> coset}\<and> l< real_of_rat eps_closest"
    using closest_distance_sq_pos
    unfolding closest_distance_sq_def
    by (meson cInf_lessD)
  moreover then obtain v::"rat vec" where "l = real_of_rat (sq_norm v) \<and> v\<in>coset" by blast
  ultimately show ?thesis unfolding witness_def lattice_carrier 
    by (smt (verit) length_M index_minus_vec(2) mem_Collect_eq of_rat_less_eq)
qed

section \<open>More linear algebra lemmas\<close>

lemma carrier_Ms:
  shows "mat_M \<in>carrier_mat n n" "mat_M_inv \<in>carrier_mat n n"
    using M_dim M_inv_dim
     apply blast
    by (simp add: M_inv_dim(1) M_inv_dim(2) carrier_matI)

lemma carrier_L:
  fixes v::"rat vec"
  assumes "dim_vec v = n"
  shows "lattice_coord v\<in>carrier_vec n"
  unfolding lattice_coord_def
  using mult_mat_vec_carrier[of "mat_M_inv" n n v]
            carrier_Ms
            carrier_vecI[of "v"]
            assms(1)
  by fast

lemma sumlist_index_commute:
  fixes Lst::"rat vec list" (*Want to make this more general*)
  fixes i::nat
  assumes "set Lst\<subseteq>carrier_vec n"
  assumes "i<n"
  shows "(gs.sumlist Lst)$i = sum_list (map (\<lambda>j. (Lst!j)$i) [0..<(length Lst)])"
  using assms
proof(induct Lst)
  case Nil
  have "gs.sumlist Nil =  0\<^sub>v n" using assms unfolding gs.sumlist_def by auto  
  then have lhs:"(gs.sumlist Nil)$i = 0" using assms(2) by auto
  have "[0..<(length Nil)] = Nil" by simp
  then  have "(map (\<lambda>j. (Nil!j)$i) [0..<(length Nil)]) = Nil" by blast
  then have "sum_list (map (\<lambda>j. (Nil!j)$i) [0..<(length Nil)]) = 0" by simp
  then show ?case using lhs by simp
next
  case (Cons a Lst)
  let ?CaLst = "Cons a Lst"
  have "set Lst \<subseteq> carrier_vec n" using Cons.prems by auto 
  then have carr:"gs.sumlist Lst \<in>carrier_vec n" using assms gs.sumlist_carrier[of Lst ]
    by blast
  have "gs.sumlist (Cons a Lst) = a + gs.sumlist Lst" by simp
  then have lhs:"(gs.sumlist ?CaLst)$i = a$i + (gs.sumlist Lst)$i" using assms carr by simp
  have "sum_list (map (\<lambda>j. (?CaLst!j)$i) [0..<(length ?CaLst)]) = sum_list (map (\<lambda>l. l$i) ?CaLst)"
    by (smt (verit) length_map map_eq_conv' map_nth nth_map)
  moreover have "sum_list (map (\<lambda>l. l$i) ?CaLst) = a$i + sum_list (map (\<lambda>l. l$i) Lst)" by simp
  moreover have "sum_list (map (\<lambda>l. l$i) Lst) = sum_list (map (\<lambda>j. (Lst!j)$i) [0..<(length Lst)])"
    by (smt (verit) length_map map_eq_conv' map_nth nth_map)
  moreover have "sum_list (map (\<lambda>j. (Lst!j)$i) [0..<(length Lst)]) = (gs.sumlist Lst)$i"
    using Cons.prems Cons.hyps by simp
  ultimately show ?case using lhs
    by argo
qed


lemma mat_mul_to_sum_list:
  fixes A::"rat mat"
  fixes v::"rat vec"
  assumes "dim_vec v = dim_col A"
  assumes "dim_row A = n"
  shows "A*\<^sub>vv = gs.sumlist (map (\<lambda>j. v$j  \<cdot>\<^sub>v (col A j)) [0 ..< dim_col A])"
proof-
  have carrier:"set (map (\<lambda>j. v $ j \<cdot>\<^sub>v col A j) [0..<dim_col A]) \<subseteq> Rn"
      by (smt (verit) assms(2) carrier_dim_vec dim_col ex_map_conv index_smult_vec(2) subset_code(1))
  have "(A*\<^sub>vv)$i = gs.sumlist (map (\<lambda>j. v$j  \<cdot>\<^sub>v (col A j)) [0 ..< dim_col A])$i" if small:"i<dim_row A" for i
  proof-
    let ?rAi = "row A i"

    have 1:"(A*\<^sub>vv)$i = ?rAi \<bullet> v" using small by simp
    have 2:"?rAi \<bullet> v = sum_list (map (\<lambda>j. (?rAi$j)*(v$j)) [0..<dim_col A])"
      using assms sum_set_upt_conv_sum_list_nat unfolding scalar_prod_def by auto
    have "?rAi$j*(v$j) = (v$j  \<cdot>\<^sub>v (col A j))$i" if jsmall:"j<dim_col A" for j 
      unfolding row_def col_def using small jsmall
      by force
    then have "(map (\<lambda>j. (?rAi$j)*(v$j)) [0..<dim_col A]) = (map (\<lambda>j. (v$j  \<cdot>\<^sub>v (col A j))$i) [0..<dim_col A])"
      by fastforce
    then have "(A*\<^sub>vv)$i = sum_list (map (\<lambda>j. (v$j  \<cdot>\<^sub>v (col A j))$i) [0..<dim_col A])"
      using 1 2 by algebra
    then show ?thesis using sumlist_index_commute[of "map (\<lambda>j. v$j  \<cdot>\<^sub>v (col A j)) [0 ..< dim_col A]" i] 
                            small assms(2) carrier
      by (smt (verit) gs.sumlist_vec_index length_map map_equality_iff nth_map subset_code(1))
  qed
  moreover have "dim_vec (A*\<^sub>vv) = dim_row A" by fastforce
  moreover have "dim_vec (gs.sumlist (map (\<lambda>j. v$j  \<cdot>\<^sub>v (col A j)) [0 ..< dim_col A])) = n" 
    using carrier by auto
  ultimately show ?thesis using assms
    by auto
qed

lemma recover_from_lattice_coord:
  fixes v::"rat vec"
  assumes "dim_vec v = n"
  shows "v = gs.sumlist (map (\<lambda>i. (lattice_coord  v)$i  \<cdot>\<^sub>v (RAT M)!i) [0 ..< n]) "
proof -
  have "(mat_M * mat_M_inv)*\<^sub>v  v= mat_M*\<^sub>v(lattice_coord v)"
    unfolding lattice_coord_def
    using assms(1) carrier_Ms carrier_vecI[of v]
          assoc_mult_mat_vec[of "mat_M" n n mat_M_inv n v]
    by presburger
  then have "(1\<^sub>m n)*\<^sub>vv=mat_M*\<^sub>v(lattice_coord v)"
    using inv1
    by simp
  then have "v = mat_M*\<^sub>v(lattice_coord v)"
    by (metis assms carrier_vec_dim_vec one_mult_mat_vec)
  then have pre:"v = gs.sumlist (map (\<lambda>i. (lattice_coord  v)$i  \<cdot>\<^sub>v col mat_M i) [0 ..< dim_col mat_M]) "
    using mat_mul_to_sum_list[of "lattice_coord v" "mat_M"]
          M_dim
          assms
          dim_preserve_lattice_coord
    by simp
  moreover have "col mat_M i = (RAT M)!i" if "i<n" for i
    using vec_to_col
    by (simp add: that)
  ultimately have "(map (\<lambda>i. (lattice_coord  v)$i  \<cdot>\<^sub>v col mat_M i) [0 ..< dim_col mat_M]) = 
                   (map (\<lambda>i. (lattice_coord  v)$i  \<cdot>\<^sub>v (RAT M)!i) [0 ..< n])" using M_dim
    by simp
  then show "v = gs.sumlist (map (\<lambda>i. (lattice_coord  v)$i  \<cdot>\<^sub>v (RAT M)!i) [0 ..< n])"
    using pre by presburger
qed

lemma sumlist_linear_coord:
  fixes Lst::"int vec list"
  assumes "\<And>i. i<length Lst \<Longrightarrow>dim_vec (Lst!i) = n"
  shows "lattice_coord (map_vec rat_of_int (sumlist Lst)) = gs.sumlist (map lattice_coord (RAT Lst))"
using assms 
proof(induct Lst)
  case Nil
  have rhs:"gs.sumlist(map lattice_coord (RAT Nil)) = 0\<^sub>v n" by fastforce
  have "map_vec rat_of_int (sumlist Nil) = 0\<^sub>v n" by auto
  then have "lattice_coord (map_vec rat_of_int (sumlist Nil)) = 0\<^sub>v n"
    unfolding lattice_coord_def using M_inv_dim
    by (metis carrier_Ms(2) gs.M.add.r_cancel_one' gs.M.zero_closed mult_add_distrib_mat_vec mult_mat_vec_carrier)
  then show ?case using rhs by simp
next
  case (Cons a Lst)
  let ?CaLst = "Cons a Lst"
  let ?ra = "of_int_hom.vec_hom a"
  have dim:"i\<in>set ?CaLst \<Longrightarrow> dim_vec i = n" for i using Cons.prems
    by (metis in_set_conv_nth)
  then have i_lt: "(i < length Lst \<Longrightarrow> dim_vec (Lst ! i) = n)" for i
    using Cons.prems carrier_dim_vec by auto
  have carrier:"set ?CaLst\<subseteq> carrier_vec n" using Cons.prems
    using carrier_vecI dim by fast
  then have carrier_sumCaLst: "(sumlist ?CaLst)\<in>carrier_vec n" by force
  have carrier_a: "a \<in> carrier_vec n" using carrier by force
  have carrier_Lst:"set Lst \<subseteq> carrier_vec n" using carrier by simp
  have lhs:"lattice_coord (map_vec rat_of_int (sumlist ?CaLst)) = (lattice_coord ?ra) + gs.sumlist (map lattice_coord (RAT Lst))"
  proof-
    have carrier_sumLst: "sumlist Lst\<in>carrier_vec n" using carrier_Lst by force
    have "sumlist ?CaLst = a + sumlist Lst" by force
    then have "(map_vec rat_of_int (sumlist ?CaLst)) = ?ra + (map_vec rat_of_int (sumlist Lst))"
      using carrier_a carrier_sumLst carrier_sumCaLst by auto
    then have "lattice_coord (map_vec rat_of_int (sumlist ?CaLst))
              = lattice_coord(?ra) + lattice_coord(map_vec rat_of_int (sumlist Lst))"
      unfolding lattice_coord_def
      using carrier_sumCaLst carrier_a carrier_sumLst
      by (metis carrier_Ms(2) map_carrier_vec mult_add_distrib_mat_vec)
    then show ?thesis using i_lt Cons.hyps 
      by algebra
  qed
  moreover have rhs:"gs.sumlist (map lattice_coord (RAT ?CaLst)) = 
                     (lattice_coord ?ra) + gs.sumlist (map lattice_coord (RAT Lst))"
    by fastforce
  ultimately show ?case by argo
qed


lemma integral_sum:
  fixes l::nat
  assumes "\<And>j1. j1 < l \<Longrightarrow>
    map f [0..<l] ! j1  \<in> \<int>"
  shows "sum_list
     (map f [0..<l]) \<in> \<int>"
  using assms 
proof(induct l)
  case 0
  have "(map f [0..<0]) = Nil" by auto
  then have "sum_list (map f [0..<0]) = 0" by simp
  then show ?case by simp
next
  case (Suc l)  
  have nontriv:"Suc l>0" by simp
  have break:"sum_list (map f [0..<(Suc l)]) = sum_list (map f [0..<l]) + (f l)" by fastforce
  have "l<Suc l" by simp
  then have "[0..<(Suc l)]!l = l"
    by (metis nth_upt plus_nat.add_0)
  moreover then have "f ([0..<(Suc l)] ! l) = (map f [0..<(Suc l)]) ! l"
    by (metis One_nat_def Suc_diff_Suc diff_Suc_1 local.nontriv nat_SN.default_gt_zero 
          nth_map_upt nth_upt plus_1_eq_Suc real_add_less_cancel_right_pos)
  ultimately have z:"f l \<in>\<int>" using Suc.prems by fastforce
  have "\<And>j1. j1 < l \<Longrightarrow>
    map f [0..<l] ! j1  \<in> \<int>"
    by (metis Suc.prems diff_Suc_1' diff_Suc_Suc less_SucI nth_map_upt)
  then have "sum_list (map f [0..<l])\<in>\<int>" using Suc by blast
  then show ?case using z break by force
qed
(*honestly surprised that this doesn't work, given that I use similar arguments in the previous lemma
  have "set (map f [0..<l])\<subseteq> \<int>" using assms by auto
  then show ?thesis sledgehammer *)

lemma int_coord:
  fixes i::nat
  assumes "0\<le>i"
  assumes "i<n"
  fixes v::"int vec"
  assumes "v\<in>L"
  assumes "dim_vec v = n"
  shows "(lattice_coord (map_vec rat_of_int v))$i\<in>\<int>"
proof -
  obtain w where w_def:"v = sumlist (map (\<lambda> i. of_int (w i) \<cdot>\<^sub>v M ! i) [0 ..< length M])"
    using L_def assms(3) vec_module.lattice_of_def 
    by blast
  let ?Lst = "(map (\<lambda> i. of_int (w i) \<cdot>\<^sub>v M ! i) [0 ..< length M])"
  have dims_j:"dim_vec (?Lst!j) = n" if j_lt:"j<length ?Lst" for j 
    using access_index_M_dim carrier_vecI j_lt by force
  let ?recover = "(map lattice_coord (RAT ?Lst))"
  have 1:"lattice_coord (map_vec rat_of_int v) = gs.sumlist ?recover"
    using sumlist_linear_coord[of ?Lst]
          w_def
          dims_j
    by blast
  have int_recover:"\<And>j. j<n\<Longrightarrow>(?recover!j)$i \<in>\<int>\<and> (dim_vec (?recover!j)) = n"
  proof -
    fix j::nat
    assume small:"j<n"
    have "?recover!j = lattice_coord ((RAT ?Lst)!j) "
      using List.nth_map[of j "(RAT ?Lst)" lattice_coord]
            small
      by simp
    then have "?recover!j = lattice_coord (of_int_hom.vec_hom (?Lst!j))"
      using List.nth_map[of j ?Lst of_int_hom.vec_hom]
            small
      by simp
    then have "?recover!j = lattice_coord (of_int_hom.vec_hom (of_int (w j) \<cdot>\<^sub>v M ! j))"
      using List.nth_map[of j "[0 ..< length M]" "(\<lambda> i. of_int (w i) \<cdot>\<^sub>v M ! i)"]
            small
      by simp
    then have commuted_maps:"?recover!j = mat_M_inv *\<^sub>v (of_int_hom.vec_hom (of_int (w j) \<cdot>\<^sub>v M ! j)) "
      unfolding lattice_coord_def
      by simp
    then have "?recover!j = mat_M_inv *\<^sub>v((of_int (of_int (w j))) \<cdot>\<^sub>v of_int_hom.vec_hom  (M ! j)) "
      using of_int_hom.vec_hom_smult[of "of_int (w j)" "M ! j"]
      by metis
    then have "?recover!j = (of_int (of_int (w j))) \<cdot>\<^sub>v (mat_M_inv *\<^sub>v of_int_hom.vec_hom  (M ! j))"
      using mult_mat_vec[of "mat_M_inv" n n "of_int_hom.vec_hom (M ! j)" "(of_int (of_int (w j)))"]
            carrier_Ms
            access_index_M_dim[of j]
            carrier_vecI[of "of_int_hom.vec_hom  (M ! j)" n]
      by (simp add: small)
    then have "?recover!j = (of_int (of_int (w j))) \<cdot>\<^sub>v (lattice_coord (of_int_hom.vec_hom (M ! j)))"
      unfolding lattice_coord_def
      by simp
    then have recover_unit:"?recover!j = (of_int (of_int (w j))) \<cdot>\<^sub>v (unit_vec n j)"
      using unit[of j]
            small
      by simp
    then have "(?recover!j)$i=((of_int (of_int (w j))) \<cdot>\<^sub>v (unit_vec n j))$i"
      by simp
    then have "(?recover!j)$i = (of_int (of_int (w j))) * (unit_vec n j)$i"
      by (simp add: assms(2))
    then have "(?recover!j)$i = (of_int (of_int (w j))) * (if i=j then 1 else 0)"
      using small assms(2)
      by simp
    moreover have "(if i=j then 1 else 0) \<in>\<int>"
      by simp
    moreover have "(of_int (of_int (w j)))\<in>\<int>"
      by simp
    moreover have "dim_vec (?recover!j) = n"
    using recover_unit
          smult_closed[of "(unit_vec n j)" "(of_int (of_int (w j)))"]
          unit_vec_carrier[of n j]
    by force
    ultimately show "(?recover!j)$i \<in>\<int> \<and> dim_vec (?recover!j) = n"
      by simp
  qed
  then have "\<forall>v\<in>set ?recover. dim_vec v = n"
    by auto
  then have "set ?recover\<subseteq>carrier_vec n"
    using carrier_vecI
    by blast
  then have "(gs.sumlist ?recover)$i = sum_list (map (\<lambda>j. (?recover!j)$i) [0..<(length ?recover)])"
    using sumlist_index_commute[of ?recover i] assms
    by blast
  moreover have "length ?recover = n"
    by auto
  ultimately have "(gs.sumlist ?recover)$i = sum_list (map (\<lambda>j. (?recover!j)$i) [0..<n])"
    by simp
  moreover have "\<And>j. j<n \<Longrightarrow> (map (\<lambda>j. (?recover!j)$i) [0..<n])!j \<in>\<int>"
  proof-
    fix j::nat
    assume jsmall:"j<n"
    have "(map (\<lambda>j. (?recover!j)$i) [0..<n])!j =  (\<lambda>j. (?recover!j)$i) j"
      using List.nth_map[of j "[0..<n]" "(\<lambda>j. (?recover!j)$i)"]
            jsmall
      by simp
    then have "(map (\<lambda>j. (?recover!j)$i) [0..<n])!j =(?recover!j)$i"
      by simp
    then show "(map (\<lambda>j. (?recover!j)$i) [0..<n])!j\<in>\<int>"
      using int_recover[of j] jsmall
      by simp
  qed
  ultimately have "(gs.sumlist ?recover)$i\<in>\<int>"
     using integral_sum[of n "(\<lambda>j. map lattice_coord
              (map of_int_hom.vec_hom (map (\<lambda>i. of_int (w i) \<cdot>\<^sub>v M ! i) [0..<n])) !
             j $
             i)"]
     by argo
  then show ?thesis
    using 1
    by simp
qed

lemma int_coord_for_rat:
  fixes i::nat
  assumes "0\<le>i"
  assumes "i<n"
  fixes v::"rat vec"
  assumes "v\<in>of_int_hom.vec_hom` L"
  assumes "dim_vec v = n"
  shows "(lattice_coord  v)$i\<in>\<int>"
proof-
  let ?hom = "of_int_hom.vec_hom"
  obtain vint where "v = ?hom vint\<and> vint\<in>L" using assms(3) by blast
  moreover then have "(lattice_coord (?hom vint))$i\<in>\<int>" using int_coord assms by simp
  ultimately show ?thesis by simp
qed

section \<open>Coord-Invariance\<close>

text \<open> This section shows that the algorithm output matches true closest (or near-closest) vector
in some trailing coordinates. \<close>

definition I where 
  "I =  (if ({i\<in>{0..<n}. ((sq_norm (Mt!i)::rat))\<le>4*eps_closest}::nat set) \<noteq> {} 
   then Max ({i\<in>{0..<n}. ((sq_norm (Mt!i)::rat))\<le>4*eps_closest}::nat set) else -1)"

lemma I_geq:
  shows "I\<ge>-1"
  unfolding I_def
  by simp
lemma I_leq:
  shows "I<n"
  unfolding I_def
  by force


lemma index_geq_I_big:
  fixes i::nat
  assumes "i>I"
  assumes "i<n"
  shows "((sq_norm (Mt!i)::rat))>4*eps_closest"
proof(rule ccontr)
  assume "\<not>?thesis"
  then have "((sq_norm (Mt!i)::rat))\<le>4*eps_closest" by linarith
  then have i_def:"i\<in>({i\<in>{0..<n}. ((sq_norm (Mt!i)::rat))\<le>4*eps_closest}::nat set)" using assms by fastforce
  then have "({i\<in>{0..<n}. ((sq_norm (Mt!i)::rat))\<le>4*eps_closest}::nat set)\<noteq>{}" by fast
  moreover then have "I= Max ({i\<in>{0..<n}. ((sq_norm (Mt!i)::rat))\<le>4*eps_closest}::nat set)" unfolding I_def by presburger
  moreover have "finite ({i\<in>{0..<n}. ((sq_norm (Mt!i)::rat))\<le>4*eps_closest}::nat set)"
    by simp
  ultimately show False using assms i_def eq_Max_iff by auto
qed

lemma scalar_prod_gs_from_lattice_coord:
  fixes i::nat
  fixes v::"rat vec"
  assumes "dim_vec v = n"
  assumes "i<n"
  shows "v\<bullet>Mt!i=sum_list (map (\<lambda>k. (lattice_coord v)$k * (((RAT M)!k)\<bullet>Mt!i)) [i..<n])"
proof(-)
  let ?lc = "lattice_coord v"
  let ?recover = "((map (\<lambda>j. ?lc$j  \<cdot>\<^sub>v (RAT M)!j) [0 ..< n]))"
  let ?gsv = "Mt!i"
  have "v = gs.sumlist ?recover"
    using recover_from_lattice_coord[of v] assms
    by blast
  then have split_ip:" v  \<bullet> ?gsv =  (gs.sumlist (map (\<lambda>j. ?lc$j  \<cdot>\<^sub>v (RAT M)!j) [0 ..< n]))\<bullet> ?gsv"
    by simp
  have "\<And>u. u\<in>set ?recover\<Longrightarrow>u\<in>carrier_vec n"
  proof(-)
    fix u::"rat vec"
    assume u_init:"u\<in> set ?recover"
    then have index_small:"find_index ?recover u < length ?recover"
      by (meson find_index_leq_length)
    then have carrier_v_ind_M:"(RAT M)!(find_index ?recover u)\<in>carrier_vec n"
      using carrier_vecI[of "(RAT M)!(find_index ?recover u)" n]
            access_index_M_dim
      by (smt (z3) M_locale_1 gram_schmidt_fs_Rn.f_carrier length_map map_nth)
    then have "u=?recover!(find_index ?recover u)"
      using u_init
      by (simp add: find_index_in_set)
    then have "u=(\<lambda>j. ?lc$j  \<cdot>\<^sub>v (RAT M)!j) (find_index ?recover u) "
      using u_init
            List.nth_map[of "find_index ?recover u" "[0..<n]" "(\<lambda>j. ?lc$j  \<cdot>\<^sub>v (RAT M)!j)"]
            index_small
      by auto
    then have "u = ?lc$(find_index ?recover u)\<cdot>\<^sub>v (RAT M)!(find_index ?recover u)"
      by simp
    then show "u\<in>carrier_vec n"
      using carrier_v_ind_M
            smult_carrier_vec[of "?lc$(find_index ?recover u)" "(RAT M)!(find_index ?recover u)" n]
      by presburger
  qed
  then have result_sumlist_L:"v \<bullet> ?gsv =  sum_list (map (\<lambda>w. w \<bullet> ?gsv) ?recover)"
    using split_ip 
          gs.scalar_prod_left_sum_distrib[of ?recover ?gsv] 
    by (metis (no_types, lifting) assms(2) carrier_dim_vec dim_vecs_in_Mt)
  let ?L="(map (\<lambda>w. w \<bullet> ?gsv) ?recover)"
  have 2:"\<And>k. k<n\<Longrightarrow>?L!k = ?lc$k * ((RAT M)!k\<bullet> ?gsv)"
  proof(-)
    fix k::nat
    assume k_bound:"k<n"
    then have "?L!k= (\<lambda>w. w \<bullet> ?gsv) (?recover!k)"
      by force
    then have "?L!k = ?recover!k \<bullet> ?gsv"
      by simp
    then have "?L!k = ((\<lambda>j. (?lc$j  \<cdot>\<^sub>v (RAT M)!j)) k)  \<bullet> ?gsv"
      using List.nth_map[of k "[0..<n]" "(\<lambda>j. (?lc$j  \<cdot>\<^sub>v (RAT M)!j))"] k_bound
      by simp
    then have "?L!k = (?lc$k \<cdot>\<^sub>v(RAT M)!k)\<bullet> ?gsv"
      by simp
    then show "?L!k =?lc$k * ((RAT M)!k\<bullet> ?gsv)"
      using smult_scalar_prod_distrib[of "(RAT M)!k" n ?gsv "?L!k"]
            access_index_M_dim
            dim_vecs_in_Mt[of i]
            carrier_vecI[of ?gsv n]
            k_bound
            assms
      by force
  qed
  moreover have "length ?L = n"
    by fastforce
  ultimately have 1:"?L = (map (\<lambda>k. ?lc$k * ((RAT M)!k\<bullet> ?gsv)) [0..<n])"
    by auto 
  moreover then have filt:"\<And>k. k<i\<Longrightarrow> (\<lambda>k. ?lc$k * ((RAT M)!k\<bullet> ?gsv)) k =0"
  proof(-)
  fix k::nat
  assume tri:"k<i"
  then have "(?gsv \<bullet>(RAT M)!k) = 0"
    using gram_schmidt_fs_lin_indpt.gso_scalar_zero[of n "(RAT M)" i k]
          M_locale_2
          Mt_gso_connect[of i]
          assms(2)
          more_dim
    by presburger
  then have "((RAT M)!k)\<bullet>?gsv = 0"
    using comm_scalar_prod[of "((RAT M)!k)" n ?gsv ]
          access_index_M_dim[of "k"]
          tri
          assms(2)
          dim_vecs_in_Mt[of i]
          carrier_vecI[of "?gsv"] carrier_vecI[of "((RAT M)!k)"]
    by fastforce
  then have "?lc$k * ((RAT M)!k\<bullet> ?gsv) = 0"
    by simp
  then show "(\<lambda>k. ?lc$k * ((RAT M)!k\<bullet> ?gsv)) k =0"
    by blast
qed
  moreover have "k\<in> set [0..<n]\<and> \<not>i\<le>k\<Longrightarrow>k<i"
    by linarith
  ultimately have "sum_list ?L = sum_list (map (\<lambda>k. ?lc$k * ((RAT M)!k\<bullet> ?gsv)) (filter (\<lambda>k. i\<le>k) [0..<n] ) )"
    using sum_list_map_filter[of "[0..<n]" "(\<lambda>k. i\<le>k)" "(\<lambda>k. ?lc$k * ((RAT M)!k\<bullet> ?gsv))" ]
    by (metis (no_types, lifting) le_eq_less_or_eq nat_neq_iff)
  moreover have "(filter (\<lambda>k. i\<le>k) [0..<n] ) = [i..<n]"
    using assms(2) bot_nat_0.extremum filter_upt 
    by presburger
  ultimately have "sum_list ?L = sum_list (map (\<lambda>k. ?lc$k * ((RAT M)!k\<bullet> ?gsv)) [i..<n])"
    by presburger
  then show ?thesis 
    using result_sumlist_L
    by simp
qed

lemma correct_coord_help:
  fixes i::"nat"
  assumes "i<(int n)-I"
  assumes "witness v (eps_closest)"
  assumes "0<i"
  shows "(lattice_coord (s i))$(n-i)=(lattice_coord v)$(n-i)
          \<and> ( (s i)  \<bullet> Mt!(n-i) = v \<bullet> Mt!(n-i) )"
  using assms
proof(induct i rule: less_induct)
  case (less i)
  let ?lcs = "(lattice_coord  (s i))"
  let ?lcIs = "\<lambda>i. lattice_coord (s i)$(n-i)"
  let ?lcv = "lattice_coord v"
  let ?gsv = "Mt!(n-(i))"
  have leq:"(int n)-I\<le>n+1"
    using I_geq
    by simp
  moreover have nonbase:"0<i"
    using less by blast
  then have 1:"i\<le>n"
    using leq less 
    by linarith
  moreover have nms:"n-(i)<n"
    using 1 nonbase by linarith
  ultimately have s_ip:"(s (i))  \<bullet> ?gsv = sum_list (map (\<lambda>j. ?lcs$j *((RAT M)!j\<bullet> ?gsv)) [n-(i)..<n])"
    using scalar_prod_gs_from_lattice_coord[of "s (i)" "n-(i)"]
          s_dim[of "i"] by force
  have dim_v:"dim_vec v = n"
    using assms(2)
    unfolding witness_def
    by blast
  then have v_ip:"v \<bullet> ?gsv = sum_list (map (\<lambda>j. ?lcv$j *((RAT M)!j\<bullet> ?gsv)) [n-(i)..<n])"
    unfolding witness_def
    using scalar_prod_gs_from_lattice_coord[of v "n-i"]
          nms assms(2)
          carrier_vecI[of v n]
    by satx
  have "[n-i..<n]\<noteq>[]" using nms by auto
  then have split_indices:"[n-(i)..<n] = (n-i) # [n-(i)+1..<n]"
    by (simp add: upt_eq_Cons_conv) 
  then have split_s_list:"(map (\<lambda>j. ?lcs$j *((RAT M)!j\<bullet> ?gsv)) [n-(i)..<n]) =
         ((\<lambda>j. ?lcs$j *((RAT M)!j\<bullet> ?gsv)) (n-(i)))#(map (\<lambda>j. ?lcs$j *((RAT M)!j\<bullet> ?gsv)) [n-(i)+1..<n])"
    by simp
  then have split_s_ip_pre:"(s (i))  \<bullet> ?gsv = ((\<lambda>j. ?lcs$j *((RAT M)!j\<bullet> ?gsv)) (n-(i)))
                                             + sum_list (map (\<lambda>j. ?lcs$j *((RAT M)!j\<bullet> ?gsv)) [n-(i)+1..<n])"
    using s_ip
    by force
  then have split_s_ip: "(s (i))  \<bullet> ?gsv = ((\<lambda>j. ?lcs$j *((RAT M)!j\<bullet> ?gsv)) (n-(i)))
                                             + sum_list (map (\<lambda>j. ?lcs$j *((RAT M)!j\<bullet> ?gsv)) [n-i+1..<n])"
    by presburger
  have split_v_list:"(map (\<lambda>j. ?lcv$j *((RAT M)!j\<bullet> ?gsv)) [n-(i)..<n]) =
         ((\<lambda>j. ?lcv$j *((RAT M)!j\<bullet> ?gsv)) (n-(i)))#(map (\<lambda>j. ?lcv$j *((RAT M)!j\<bullet> ?gsv)) [n-(i)+1..<n])"
    using split_indices by simp
  then have split_v_ip_pre:"v \<bullet> ?gsv = ((\<lambda>j. ?lcv$j *((RAT M)!j\<bullet> ?gsv)) (n-(i)))
                        + sum_list (map (\<lambda>j. ?lcv$j *((RAT M)!j\<bullet> ?gsv)) [n-(i)+1..<n])"
    using v_ip
    by force
  then have split_v_ip:"v \<bullet> ?gsv = ((\<lambda>j. ?lcv$j *((RAT M)!j\<bullet> ?gsv)) (n-(i)))
                        + sum_list (map (\<lambda>j. ?lcv$j *((RAT M)!j\<bullet> ?gsv)) [n-i+1..<n])"
    by presburger
  have use_coord_inv: "(\<lambda>j. ?lcs$j *((RAT M)!j\<bullet> ?gsv)) k = (\<lambda>j. ?lcv$j *((RAT M)!j\<bullet> ?gsv)) k" if k_bound: "k<n \<and> k\<ge>n-i+1" for k
  proof -
    have nmssmall:"n-k<i"
      using k_bound by linarith
   then have arith:"(n-k)+(i - (n-k)) = i"
      using k_bound 1 by linarith
   have 2:"0<n-k"
      using k_bound by linarith
    moreover have 3:"(n-k)+(i - (n-k))\<le>n"
      using 1 arith by linarith
    moreover have 4:"n-k\<le>n-k" by auto
    ultimately have 5:"lattice_coord (s (n-k + (i - (n-k)))) $ (n-(n-k)) = lattice_coord (s (n-k)) $ (n-(n-k)) "
      using coord_invariance[of "n-k" "n-k" "(i)-(n-k)"] by blast
    also have cancel:"n-(n-k) =k"
      using k_bound 2 by auto
    then have "?lcs$k = ?lcIs (n-k)"
      using arith 5 by presburger
    moreover have "int (n-k)<int n -I"
      using assms nmssmall less by linarith
    ultimately have "?lcs$k = ?lcv$(n-(n-k))"
      using less(1)[of "n-k"] nmssmall assms(2) 2 by argo
    then have "?lcs$k = ?lcv$k"
      using cancel by presburger
    then have "?lcs$k *((RAT M)!k\<bullet> ?gsv) = ?lcv$k *((RAT M)!k\<bullet> ?gsv)"
      by simp
    then show "(\<lambda>j. ?lcs$j *((RAT M)!j\<bullet> ?gsv)) k = (\<lambda>j. ?lcv$j *((RAT M)!j\<bullet> ?gsv)) k"
      by simp
  qed
  then have "(map (\<lambda>j. ?lcs$j *((RAT M)!j\<bullet> ?gsv)) [n-i+1..<n]) 
              = (map (\<lambda>j. ?lcv$j *((RAT M)!j\<bullet> ?gsv)) [n-i+1..<n])"
    by simp
  then have "sum_list (map (\<lambda>j. ?lcs$j *((RAT M)!j\<bullet> ?gsv)) [n-i+1..<n]) 
              = sum_list (map (\<lambda>j. ?lcv$j *((RAT M)!j\<bullet> ?gsv)) [n-i+1..<n])"
    by presburger
  then have "(s i)  \<bullet> ?gsv = 
            ((\<lambda>j. ?lcs$j *((RAT M)!j\<bullet> ?gsv)) (n-i)) + 
            sum_list (map (\<lambda>j. ?lcv$j *((RAT M)!j\<bullet> ?gsv)) [n-i+1..<n])"
    using split_s_ip by argo
  then have "(s i)  \<bullet> ?gsv - v \<bullet> ?gsv = 
              ((\<lambda>j. ?lcs$j *((RAT M)!j\<bullet> ?gsv)) (n-i))- 
              ((\<lambda>j. ?lcv$j *((RAT M)!j\<bullet> ?gsv)) (n-i))"
    using split_v_ip by linarith
  then have "(s i)  \<bullet> ?gsv - v \<bullet> ?gsv = ((?lcs$(n-i) - ?lcv$(n-i)) * ((RAT M)!(n-i)\<bullet> ?gsv))"
    by algebra
  then have case_2_from_case_1:"(s i)  \<bullet> ?gsv - v \<bullet> ?gsv =  ((?lcs$(n-i) - ?lcv$(n-i)) * (sq_norm ?gsv))"
    using one_diag[of "n- i"] 1 nms
    by fastforce
  then have "abs ((s i)  \<bullet> ?gsv - v \<bullet> ?gsv) = abs(?lcs$(n-i) - ?lcv$(n-i)) * abs(sq_norm ?gsv)"
    using abs_mult by auto
  then have a:"abs ((s i)  \<bullet> ?gsv - v \<bullet> ?gsv) = abs(?lcs$(n-i) - ?lcv$(n-i)) * (sq_norm ?gsv)"
    by (metis abs_of_nonneg sq_norm_vec_ge_0)
  have lattice_coord_equal:"?lcs$(n-i) - ?lcv$(n-i)= 0"
  proof(rule ccontr)
    assume "\<not>(?lcs$(n-i) - ?lcv$(n-i)= 0)"
    then have contra:"?lcs$(n-i) - ?lcv$(n-i) \<noteq> 0 " by simp
    have "?lcs$(n-i) - ?lcv$(n-i) = (?lcs-?lcv)$(n-i)"
      using index_minus_vec(1)[of "n-i" ?lcv ?lcs]
            dim_preserve_lattice_coord[of v]
            assms(2) nms
      unfolding witness_def by argo
    moreover have "?lcs-?lcv = lattice_coord((s i)-v)"
      using mult_minus_distrib_mat_vec
      unfolding lattice_coord_def
      by (metis "1" carrier_Ms(2) carrier_vecI dim_v s_dim)
    ultimately have use_linear:"?lcs$(n-i) - ?lcv$(n-i) = (lattice_coord((s i)-v))$(n-i)"
      by presburger
    have "(s i)-v\<in> of_int_hom.vec_hom` L"
      using subtract_coset_into_lattice[of "s i" v]
            coset_s[of i]
            1 assms(2)
      unfolding witness_def
      by linarith
    then have use_int_coord:"(lattice_coord(  ((s i)-v))  )$(n-i)\<in>\<int>"
      using int_coord_for_rat[of "n-i" "((s i)-v)"] 1 nms
      by (simp add: dim_v)
    then have " abs((lattice_coord(  ((s i)-v))  )$(n-i))>0"
      using contra use_linear
      by linarith
    then have " abs((lattice_coord(  ((s i)-v))  )$(n-i))\<ge>1"
      using use_int_coord
      by (simp add: Ints_nonzero_abs_ge1 contra use_linear)
    then have "abs(?lcs$(n-i) - ?lcv$(n-i))\<ge>1"
      using use_linear by presburger
    then have "abs(?lcs$(n-i) - ?lcv$(n-i))*(sq_norm ?gsv)\<ge>sq_norm ?gsv"
      using sq_norm_vec_ge_0[of "?gsv"] mult_left_mono[of 1 "abs(?lcs$(n-i) - ?lcv$(n-i))" "sq_norm ?gsv"] by algebra
    then have big1:"abs ((s i)  \<bullet> ?gsv - v \<bullet> ?gsv)\<ge>sq_norm ?gsv"
      using a by argo
    then have tri_ineq:"abs(v \<bullet> ?gsv)\<ge> abs(abs ((s i)  \<bullet> ?gsv - v \<bullet> ?gsv) -abs((s i)  \<bullet> ?gsv))"
      using cancel_ab_semigroup_add_class.diff_right_commute 
            cancel_comm_monoid_add_class.diff_cancel diff_zero by linarith
    then have smallhalf:"abs((s i)  \<bullet> ?gsv)\<le>(1/2)*(sq_norm ?gsv)"
      using small_orth_coord[of i] nonbase 1
      by fastforce
    then have "abs((s i)  \<bullet> ?gsv - v \<bullet> ?gsv) -abs((s i)  \<bullet> ?gsv)\<ge> sq_norm ?gsv - (1/2)*(sq_norm ?gsv)"
      using big1 by linarith
    then have big2:"abs((s i)  \<bullet> ?gsv - v \<bullet> ?gsv) -abs((s i)  \<bullet> ?gsv)\<ge> (1/2)*(sq_norm ?gsv)"
      by linarith
    then have "abs((s i)  \<bullet> ?gsv - v \<bullet> ?gsv) -abs((s i)  \<bullet> ?gsv)\<ge>0"
      using sq_norm_vec_ge_0[of "?gsv"] by linarith
    then have "abs(abs ((s i)  \<bullet> ?gsv - v \<bullet> ?gsv) -abs((s i)  \<bullet> ?gsv)) 
                = abs((s i)  \<bullet> ?gsv - v \<bullet> ?gsv) -abs((s i)  \<bullet> ?gsv)"
      by fastforce
    then have "abs(v \<bullet> ?gsv)\<ge>(1/2)*(sq_norm ?gsv)"
      using big2
      by linarith
    moreover have "(1/2)*(sq_norm ?gsv)\<ge>0"
      using sq_norm_vec_ge_0[of ?gsv] by simp
    moreover have "abs(v \<bullet> ?gsv)\<ge>0" by simp
    ultimately have "abs(v \<bullet> ?gsv)^2\<ge>((1/2)*(sq_norm ?gsv))^2"
      using nonneg_power_le by blast
    moreover have "(sq_norm v) * (sq_norm ?gsv)\<ge>abs(v \<bullet> ?gsv)^2"
      using scalar_prod_Cauchy[of v n ?gsv]
            carrier_vecI[of v n] assms(2)
            carrier_vecI[of ?gsv] dim_vecs_in_Mt[of "n-i"] nms
      unfolding witness_def
      by fastforce
    ultimately have "sq_norm v * sq_norm ?gsv \<ge> ((1/2)*(sq_norm ?gsv))^2"
      by order
    then have "sq_norm v * sq_norm ?gsv \<ge> (1/2)^2 * (sq_norm ?gsv)^2"
      by (metis gs.nat_pow_distrib)
    then have "sq_norm v * sq_norm ?gsv \<ge> 1/4 * (sq_norm ?gsv)^2"
      by (smt (z3) numeral_Bit0_eq_double one_power2 power2_eq_square times_divide_times_eq)
    moreover have "sq_norm ?gsv > 0"
      using gram_schmidt_fs_lin_indpt.sq_norm_pos[of n "RAT M" "n-i"]
            M_locale_2 M_locale_1 gram_schmidt_fs_Rn.main_connect[of n "(RAT M)"]
            nms by force
    ultimately have big:"sq_norm v \<ge> 1/4 * sq_norm ?gsv"
      by (simp add: power2_eq_square)
    have "n-i>I"
      using less by linarith
    then have big_again:"sq_norm ?gsv > 4*eps_closest"
      using index_geq_I_big[of "n-i"] nms by simp
    then have "sq_norm v> 1/4 *4*eps_closest"
      using big by fastforce
    then have "sq_norm v > eps_closest" by auto
    then show False
      using assms(2)
      unfolding witness_def
      by linarith
  qed 
  then have piece1: "lattice_coord (s i) $ (n - i) = lattice_coord v $ (n - i)" 
    using lattice_coord_equal by simp
  have "(s i)  \<bullet> ?gsv - v \<bullet> ?gsv = 0"
    using lattice_coord_equal case_2_from_case_1
    by algebra
  then show ?case using piece1 by simp
qed
 
lemma correct_coord:
  fixes v::"rat vec"
  fixes k::nat
  assumes "witness v eps_closest"
  assumes "I<k"
  assumes "k<n"
  shows "(s n) \<bullet> Mt!(k) = v \<bullet> Mt!(k)"
proof -
  have "(s n) \<bullet> Mt!(k) = (s (n-k)) \<bullet> Mt!(k)"
    using coord_invariance[of "n-k" "n-k" k] assms
    by force
  moreover have "(s (n-k)) \<bullet> Mt!(k) = v \<bullet> Mt!(k)"
    using correct_coord_help[of "n-k" v] assms
    by simp
  ultimately show ?thesis by simp
qed

section \<open>Main Theorem\<close>
text \<open> This section culminates in the main theorem.\<close>
lemma sq_norm_from_Mt:
  fixes v::"rat vec"
  assumes v_carr:"v\<in>carrier_vec n"
  shows "sq_norm v = sum_list (map (\<lambda>i. (v\<bullet>Mt!i)^2/(sq_norm (Mt!i))) [0..<n])"
proof-
  let ?Mt_inv_list = "map (\<lambda>i. (1/sq_norm(Mt!i))\<cdot>\<^sub>v (Mt!i)) [0..<n]"
  have nonsing:"?Mt_inv_list!i \<in> carrier_vec n" if i:"0\<le>i\<and>i<n" for i
  proof-
    have "0< sq_norm(Mt!i)"
    using gram_schmidt_fs_lin_indpt.sq_norm_pos[of n "RAT M" "i"]
      M_locale_1 gram_schmidt_fs_Rn.main_connect[of n "(RAT M)"] i
    by (simp add: M_locale_2)
  then have "0<1/sq_norm(Mt!i)" by fastforce
  then have "(1/sq_norm(Mt!i))\<cdot>\<^sub>v (Mt!i)\<in>carrier_vec n" 
    using carrier_vecI[of "(Mt!i)"] dim_vecs_in_Mt[of i] i by blast
  moreover have "?Mt_inv_list!i = (1/sq_norm(Mt!i))\<cdot>\<^sub>v (Mt!i)"
    using i by simp
  ultimately show ?thesis by argo
qed 
  let ?Mt_inv_mat = "mat_of_rows n ?Mt_inv_list"
  have carrier_mat_inv:"?Mt_inv_mat\<in>carrier_mat  n n" by fastforce 
  let ?vMt = "?Mt_inv_mat *\<^sub>v v"
  have "?vMt$i = ((1/sq_norm(Mt!i))\<cdot>\<^sub>v (Mt!i))\<bullet>v" if i:"0\<le>i\<and>i<n" for i
    using i nonsing[of i] by auto
  have dim_vMt:"dim_vec ?vMt = n"
    using carrier_mat_inv v_carr by auto
  let ?Mt_mat = "mat_of_cols n Mt"
  have l:"length Mt = n" 
    using gs.gram_schmidt_result[of "RAT M" Mt] basis dim_vecs_in_M
    unfolding gs.lin_indpt_list_def
    by fastforce
  then have carrier_mat_Mt:"?Mt_mat\<in>carrier_mat  n n"
    using dim_vecs_in_Mt carrier_vecI by auto
  then have to_sumlist:"?Mt_mat*\<^sub>v?vMt = gs.sumlist (map (\<lambda>j. ?vMt$j  \<cdot>\<^sub>v (col ?Mt_mat j)) [0 ..< n])"
    using mat_mul_to_sum_list[of ?vMt ?Mt_mat] dim_vMt
    by fastforce
  have "?vMt$i  \<cdot>\<^sub>v (col ?Mt_mat i) = (1/sq_norm(Mt!i))* ((Mt!i)\<bullet>v)  \<cdot>\<^sub>v Mt!i" if i:"0\<le>i\<and>i<n" for i
    using i l dim_vecs_in_Mt v_carr  carrier_vecI by fastforce
  then have "(map (\<lambda>j. ?vMt$j  \<cdot>\<^sub>v (col ?Mt_mat j)) [0 ..< n]) 
            = (map (\<lambda>j. (1/sq_norm(Mt!j))* ((Mt!j)\<bullet>v)  \<cdot>\<^sub>v Mt!j) [0 ..< n])"
    by simp
  then have 1:"gs.sumlist (map (\<lambda>j. ?vMt$j  \<cdot>\<^sub>v (col ?Mt_mat j)) [0 ..< n]) 
              =gs.sumlist (map (\<lambda>j. (1/sq_norm(Mt!j))* ((Mt!j)\<bullet>v)  \<cdot>\<^sub>v Mt!j) [0 ..< n])"
    by presburger
  then have 2:"?Mt_mat*\<^sub>v?vMt = gs.sumlist (map (\<lambda>j. (1/sq_norm(Mt!j))* ((Mt!j)\<bullet>v)  \<cdot>\<^sub>v Mt!j) [0 ..< n])"
    using to_sumlist by argo
  have "?Mt_mat *\<^sub>v ?vMt = (?Mt_mat * ?Mt_inv_mat)*\<^sub>v v"
    using carrier_mat_Mt carrier_mat_inv v_carr by auto
  have "(?Mt_inv_mat*?Mt_mat)$$(i,j) = (1\<^sub>m n)$$(i,j)" 
    if sensible_indices:"0\<le>i \<and> i<n \<and> 0\<le>j \<and> j<n" for i j
  proof-
    have "(?Mt_inv_mat*?Mt_mat)$$(i,j) = (row ?Mt_inv_mat i)\<bullet>(col ?Mt_mat j)"
      using sensible_indices carrier_mat_Mt carrier_mat_inv by auto
    then have "(?Mt_inv_mat*?Mt_mat)$$(i,j) = ?Mt_inv_list!i\<bullet>Mt!j"
      using sensible_indices carrier_mat_Mt carrier_mat_inv nonsing
      by auto
    then have "(?Mt_inv_mat*?Mt_mat)$$(i,j) = ((1/sq_norm(Mt!i))\<cdot>\<^sub>v (Mt!i))\<bullet>Mt!j"
      using sensible_indices by simp
    then have "(?Mt_inv_mat*?Mt_mat)$$(i,j) = (1/sq_norm(Mt!i)) *((Mt!i)\<bullet>(Mt!j))"
      using dim_vecs_in_Mt[of i] dim_vecs_in_Mt[of j] sensible_indices by auto
    moreover have "(1/sq_norm(Mt!i)) *((Mt!i)\<bullet>(Mt!j)) = (if i=j then 1 else 0)"
    proof(cases "i=j")
      case diag:True
      have nonzero:"0< sq_norm(Mt!i)"
        using gram_schmidt_fs_lin_indpt.sq_norm_pos[of n "RAT M" "i"]
          M_locale_1 gram_schmidt_fs_Rn.main_connect[of n "(RAT M)"] sensible_indices
          by (simp add: M_locale_2)
      have "(1/sq_norm(Mt!i)) *((Mt!i)\<bullet>(Mt!j)) = (1/sq_norm(Mt!i)) * sq_norm(Mt!i)"
        using sensible_indices diag sq_norm_vec_as_cscalar_prod[of "Mt!i"] by auto
      then have "(1/sq_norm(Mt!i)) *((Mt!i)\<bullet>(Mt!j)) = 1"
        using nonzero by auto
      then show ?thesis using diag by argo
    next
      case off:False
      have nonzero:"0< sq_norm(Mt!i)"
        using gram_schmidt_fs_lin_indpt.sq_norm_pos[of n "RAT M" "i"]
          M_locale_1 gram_schmidt_fs_Rn.main_connect[of n "(RAT M)"] sensible_indices
        by (simp add: M_locale_2)
      then have "0<1/sq_norm(Mt!i)" by simp
      moreover have "((Mt!i)\<bullet>(Mt!j)) = 0"
        using gram_schmidt_fs_lin_indpt.orthogonal[of n "(RAT) M" i j] off sensible_indices
              M_locale_1 M_locale_2 gram_schmidt_fs_Rn.main_connect
        by force
      ultimately show ?thesis using off by algebra
    qed
    moreover then have "(1/sq_norm(Mt!i)) *((Mt!i)\<bullet>(Mt!j)) = (1\<^sub>m n)$$(i,j)" 
      using sensible_indices unfolding one_mat_def by simp
    ultimately show ?thesis by presburger
  qed
  then have inv_Mt:"(?Mt_inv_mat*?Mt_mat) = 1\<^sub>m n" 
    using carrier_mat_inv carrier_mat_Mt
    by fastforce
  then have "?Mt_mat * ?Mt_inv_mat = 1\<^sub>m n" 
    using mat_mult_left_right_inverse[of ?Mt_inv_mat n ?Mt_mat] carrier_mat_inv carrier_mat_Mt
    by argo
  then have 3:"(?Mt_mat * ?Mt_inv_mat)*\<^sub>v v = v" 
    using v_carr by simp
  then have 4:"v = gs.sumlist (map (\<lambda>j. (1/sq_norm(Mt!j))* ((Mt!j)\<bullet>v)  \<cdot>\<^sub>v Mt!j) [0 ..< n])"
    using v_carr carrier_mat_inv carrier_mat_Mt 1 2 by auto
  have "(map (\<lambda>j. (1/sq_norm(Mt!j))* ((Mt!j)\<bullet>v)  \<cdot>\<^sub>v Mt!j) [0 ..< n])
         = (map (\<lambda>j. (1/sq_norm(Mt!j))* ((Mt!j)\<bullet>v)  \<cdot>\<^sub>v gs.gso j) [0 ..< n])"
    using M_locale_1 gram_schmidt_fs_Rn.main_connect[of n "RAT M"]
    by auto
  then have "gs.sumlist (map (\<lambda>j. (1/sq_norm(Mt!j))* ((Mt!j)\<bullet>v)  \<cdot>\<^sub>v Mt!j) [0 ..< n])
         = gs.sumlist (map (\<lambda>j. (1/sq_norm(Mt!j))* ((Mt!j)\<bullet>v)  \<cdot>\<^sub>v gs.gso j) [0 ..< n])"
    by argo
  then have "v = gs.sumlist (map (\<lambda>j. (1/sq_norm(Mt!j))* ((Mt!j)\<bullet>v)  \<cdot>\<^sub>v gs.gso j) [0 ..< n])"
    using 4 by argo
  then have "v\<bullet>v = gs.sumlist (map (\<lambda>j. (1/sq_norm(Mt!j))* ((Mt!j)\<bullet>v)  \<cdot>\<^sub>v gs.gso j) [0 ..< n])\<bullet>
                   gs.sumlist (map (\<lambda>j. (1/sq_norm(Mt!j))* ((Mt!j)\<bullet>v)  \<cdot>\<^sub>v gs.gso j) [0 ..< n])"
    by simp
  then have a:"v\<bullet>v = 
    sum_list(map (\<lambda>j. (1/sq_norm(Mt!j))* ((Mt!j)\<bullet>v)*(1/sq_norm(Mt!j))* ((Mt!j)\<bullet>v)*(gs.gso j \<bullet> gs.gso j)) [0..<n])"
    using gram_schmidt_fs_lin_indpt.scalar_prod_lincomb_gso[
          of n "RAT M" n "(\<lambda>j. (1/sq_norm(Mt!j))* ((Mt!j)\<bullet>v))" "(\<lambda>j. (1/sq_norm(Mt!j))* ((Mt!j)\<bullet>v))"]
          M_locale_2
          M_locale_1 gram_schmidt_fs_Rn.main_connect[of n "RAT M"] by force
  have "(map (\<lambda>j. (1/sq_norm(Mt!j))* ((Mt!j)\<bullet>v)*(1/sq_norm(Mt!j))* ((Mt!j)\<bullet>v)*(gs.gso j \<bullet> gs.gso j)) [0..<n])
                = (map (\<lambda>j. (1/sq_norm(Mt!j))* ((Mt!j)\<bullet>v)*(1/sq_norm(Mt!j))* ((Mt!j)\<bullet>v)*(Mt!j \<bullet> Mt!j)) [0..<n])"
    using M_locale_1 gram_schmidt_fs_Rn.main_connect[of n "RAT M"]
    by auto
  then have b:"sum_list (map (\<lambda>j. (1/sq_norm(Mt!j))* ((Mt!j)\<bullet>v)*(1/sq_norm(Mt!j))* ((Mt!j)\<bullet>v)*(gs.gso j \<bullet> gs.gso j)) [0..<n])
            =sum_list (map (\<lambda>j. (1/sq_norm(Mt!j))* ((Mt!j)\<bullet>v)*(1/sq_norm(Mt!j))* ((Mt!j)\<bullet>v)*(Mt!j \<bullet> Mt!j)) [0..<n])"
    by argo
  have  " (1/sq_norm(Mt!j))* ((Mt!j)\<bullet>v)*(1/sq_norm(Mt!j))* ((Mt!j)\<bullet>v)*(Mt!j \<bullet> Mt!j) = 
           (v\<bullet>(Mt!j))^2/(sq_norm (Mt!j)) " if sensible_indices:"0\<le>j\<and>j<n" for j
  proof-
    have nonzero:"0< sq_norm(Mt!j)"
      using gram_schmidt_fs_lin_indpt.sq_norm_pos[of n "RAT M" "j"]
            M_locale_1 gram_schmidt_fs_Rn.main_connect[of n "(RAT M)"] sensible_indices
      by (simp add: M_locale_2)
    moreover have "(1/sq_norm(Mt!j))* ((Mt!j)\<bullet>v)*(1/sq_norm(Mt!j))* ((Mt!j)\<bullet>v)*(Mt!j \<bullet> Mt!j)
                     = (1/sq_norm(Mt!j))* ((Mt!j)\<bullet>v)*(1/sq_norm(Mt!j))* ((Mt!j)\<bullet>v)*sq_norm (Mt!j)"
      using sq_norm_vec_as_cscalar_prod[of "Mt!j"] by force
    moreover have "(1/sq_norm(Mt!j))* ((Mt!j)\<bullet>v)*(1/sq_norm(Mt!j))* ((Mt!j)\<bullet>v)* sq_norm (Mt!j)
                  = ((Mt!j)\<bullet>v)^2 * (1/sq_norm(Mt!j))^2 *sq_norm (Mt!j) "
      by (simp add: power2_eq_square)
    moreover have "((Mt!j)\<bullet>v)^2 * (1/sq_norm(Mt!j))^2 *sq_norm (Mt!j) = ((Mt!j)\<bullet>v)^2/(sq_norm(Mt!j))"
      using nonzero
      by (simp add:  divide_divide_eq_left' power2_eq_square)
    moreover have "(Mt!j)\<bullet>v = v\<bullet>(Mt!j)" using v_carr dim_vecs_in_Mt sensible_indices
      by (metis carrier_vecI comm_scalar_prod)
    ultimately show ?thesis by argo
  qed
  then have "(map (\<lambda>j. (1/sq_norm(Mt!j))* ((Mt!j)\<bullet>v)*(1/sq_norm(Mt!j))* ((Mt!j)\<bullet>v)*(Mt!j \<bullet> Mt!j)) [0..<n])
            = (map (\<lambda>j. (v\<bullet>(Mt!j))^2/(sq_norm(Mt!j))) [0..<n])" by force
  then have c:"sum_list (map (\<lambda>j. (1/sq_norm(Mt!j))* ((Mt!j)\<bullet>v)*(1/sq_norm(Mt!j))* ((Mt!j)\<bullet>v)*(Mt!j \<bullet> Mt!j)) [0..<n])
            = sum_list (map (\<lambda>j. (v\<bullet>(Mt!j))^2/(sq_norm(Mt!j))) [0..<n])" by argo
  then have "v\<bullet>v = sum_list (map (\<lambda>j. (v\<bullet>(Mt!j))^2/(sq_norm(Mt!j))) [0..<n])" using a b c by argo
  moreover have "v\<bullet>v = v\<bullet>cv" by force
  ultimately show ?thesis using sq_norm_vec_as_cscalar_prod[of v] v_carr by argo
  qed

lemma bound_help:
  fixes N::nat
  shows "real_of_rat ((rat_of_int N)*\<alpha>^N) * epsilon\<le>2^N"
proof(induct N)
  case 0
  then show ?case by simp
next
  case (Suc N)
  let ?SN = "Suc N"
  have "?SN=1\<or>?SN=2\<or>2<?SN" by fastforce
  then show ?case
  proof(elim disjE)
    {assume 1:"?SN = 1"
      then have "real_of_rat ((rat_of_int ?SN)*\<alpha>^?SN)*epsilon = real_of_rat ((rat_of_int 1)*4/3)*11/10"
        unfolding \<alpha>_def epsilon_def by auto
      also have "real_of_rat ((rat_of_int 1)*4/3)*11/10 = real_of_rat (4/3)*11/10" by force
      also have "real_of_rat (4/3)*11/10 =real_of_rat ((4/3)* 11/10)"
        by (simp add: of_rat_hom.hom_div)
      also have "real_of_rat ((4/3)* 11/10) = real_of_rat (44/30)" by auto
      also have "real_of_rat (44/30)\<le>(2::real)"
        by (simp add: of_rat_hom.hom_div)
      finally show ?thesis using 1 by simp}
  next
    {assume 2:"?SN=2" 
      then have "real_of_rat ((rat_of_int ?SN)*\<alpha>^?SN)*epsilon = real_of_rat ((rat_of_int 2)*(4/3)^2)*11/10"
        unfolding \<alpha>_def epsilon_def
        by (metis int_ops(3) times_divide_eq_right)
      also have "((4::rat)/3)^2 = (4*4)/(3*3)"
        using power2_eq_square[of "4/3"] times_divide_times_eq[of 4 3 4 3] by metis 
      also have "(4*(4::rat))/(3*3) = 16/9" by auto
      finally have "real_of_rat ((rat_of_int ?SN)*\<alpha>^?SN)*epsilon= real_of_rat ((rat_of_int 2)*(16/9))*11/10"
        by blast
      also have "(rat_of_int 2)*(16/9) = 32/9" by force
      finally have "real_of_rat ((rat_of_int ?SN)*\<alpha>^?SN)*epsilon = real_of_rat (32 / 9) * 11 / 10"
        by simp
      also have "real_of_rat (32 / 9) * 11 / 10 = real_of_rat (32 / 9 *( 11 / 10))"
        using of_rat_hom.hom_mult[of "32/9" "11/10"]
        by (simp add:  of_rat_hom.hom_div)
      also have "real_of_rat (32 / 9 *( 11 / 10)) = real_of_rat (352/90)"
        using times_divide_times_eq[of 32 9 11 10] by force
      also have "352/90\<le>(4::rat)" by linarith
      also have "(4::rat) = 2^?SN" using 2 by auto
      finally show ?thesis
        by (simp add: "2" gs.cring_simprules(14) int_ops(3) of_rat_hom.hom_power of_rat_less_eq)}
  next
    {assume ind:"?SN>2" 
      then have "N>0" by simp
      then have "?SN = N*(?SN/N)" by auto
      moreover have "\<alpha>^?SN = \<alpha>^N*\<alpha>" by auto
      ultimately have "real_of_rat ((rat_of_int ?SN)*\<alpha>^?SN) =  (N*(?SN/N)) * (real_of_rat (\<alpha>^N*\<alpha>))"
        by (metis of_int_of_nat_eq of_rat_mult of_rat_of_nat_eq)
      also have "(N*(?SN/N)) * real_of_rat (\<alpha>^N*\<alpha>) = real_of_rat ((rat_of_int N) * \<alpha>^N) * ((?SN/N) *(real_of_rat \<alpha>))"
        by (simp add: \<open>real (Suc N) = real N * (real (Suc N) / real N)\<close> gs.cring_simprules(11) mult_of_int_commute of_rat_divide of_rat_mult)
      finally have "real_of_rat ((rat_of_int ?SN)*\<alpha>^?SN) * epsilon = real_of_rat ((rat_of_int N) * \<alpha>^N) * ((?SN/N) *(real_of_rat \<alpha>)) * epsilon"
        by presburger
      then have "real_of_rat ((rat_of_int ?SN)*\<alpha>^?SN) * epsilon = real_of_rat ((rat_of_int N) * \<alpha>^N) * epsilon * ((?SN/N) *(real_of_rat \<alpha>))"
        by argo
      moreover have "((?SN/N) *(real_of_rat \<alpha>))\<le>2"
      proof-
        have N_big:"2\<le>N" using ind
          by force 
        then have "4\<le>2*N" by fastforce
        then have "4*N+4\<le>6*N" by fastforce
        then have "4/3*(Suc N)\<le>2*N" by auto
        moreover have "0<1/N" using N_big by simp
        ultimately have " (4/3*?SN)* (1/N)\<le> 2*N*(1/N)" 
          using N_big mult_right_mono[of "(4/3*?SN)" "2*N" "(1/N)"] by linarith
        then have "(4/3*?SN)/N\<le> 2*N/N" by argo 
        then have "4/3*(?SN / N)\<le> 2*(N/N)" by linarith
        then have "4/3*(?SN/N)\<le> 2" using N_big by auto
        moreover have "4/3 = real_of_rat \<alpha>" using of_rat_divide unfolding \<alpha>_def
          by (metis of_rat_numeral_eq)
        ultimately have "(real_of_rat \<alpha>)*(?SN/N)\<le> 2" by algebra
        then show ?thesis by argo
      qed
      moreover have 
        "0\<le>real_of_rat (rat_of_int (int N) * \<alpha> ^ N) * epsilon" unfolding \<alpha>_def epsilon_def by force
      moreover have "0\<le>(real_of_rat \<alpha>)*(?SN/N)" unfolding \<alpha>_def by simp
      ultimately have "real_of_rat ((rat_of_int ?SN)*\<alpha>^?SN) * epsilon\<le>2^N * 2"
        using Suc mult_mono[of 
                              "real_of_rat (rat_of_int (int N) * \<alpha> ^ N) * epsilon"
                              "2^N"
                              "((?SN/N) *(real_of_rat \<alpha>))"
                              2] by argo
      then show ?thesis by simp}
  qed
qed


lemma present_bound_nicely:
  fixes N::nat
  shows "real_of_rat ((rat_of_int N)*\<alpha>^N* eps_closest)\<le>2^N*closest_distance_sq"
proof-
  have "real_of_rat eps_closest\<le> epsilon*closest_distance_sq"
    using eps_closest_lemma unfolding close_condition_def by fastforce
  moreover have "0\<le>(rat_of_int N)*\<alpha>^N" unfolding \<alpha>_def by simp
  ultimately have "real_of_rat ((rat_of_int N)*\<alpha>^N *  eps_closest)\<le> real_of_rat ((rat_of_int N)*\<alpha>^N) * epsilon*closest_distance_sq"
    by (metis ab_semigroup_mult_class.mult_ac(1) mult_left_mono of_rat_hom.hom_mult zero_le_of_rat_iff)
  also have "real_of_rat ((rat_of_int N)*\<alpha>^N) * epsilon*closest_distance_sq\<le>2^N*closest_distance_sq"
    using bound_help[of N] closest_distance_sq_pos mult_right_mono by fast
  finally show ?thesis by force
qed

lemma basis_decay:
  fixes i::nat
  fixes j::nat
  assumes "i<n"
  assumes "i+j<n"
  shows "sq_norm (Mt!i)\<le> \<alpha>^j*sq_norm(Mt!(i+j))"
  using assms
proof(induct j)
  case 0
  have "\<alpha>^0 = 1" by simp
  moreover have "sq_norm (Mt!i) = sq_norm(Mt!(i+0))" by simp
  moreover have "0\<le> sq_norm(Mt!i)"
    using gram_schmidt_fs_lin_indpt.sq_norm_pos[of n "RAT M" i]
          M_locale_2 M_locale_1 gram_schmidt_fs_Rn.main_connect[of n "(RAT M)"]
          assms by force
  moreover have "(0::rat)\<le>(1::rat)" by force
  ultimately show ?case by simp
next
  case (Suc j)
  have "(1::rat) \<le>\<alpha>" unfolding \<alpha>_def by fastforce 
  moreover have "n\<ge>0" by simp
  ultimately have "(1::rat)\<le>\<alpha>^j" by simp
  moreover have "sq_norm (Mt!(i+j))\<le>\<alpha>*(sq_norm (Mt!(i+Suc j)))"
    using reduced M_locale_1 gram_schmidt_fs_Rn.main_connect[of n "(RAT M)"] Suc.prems
    unfolding gs.reduced_def gs.weakly_reduced_def
    by force
  moreover have "0\<le> sq_norm (Mt!(i+j))"
    using gram_schmidt_fs_lin_indpt.sq_norm_pos[of n "RAT M" "i+j"]
      M_locale_2 M_locale_1 gram_schmidt_fs_Rn.main_connect[of n "(RAT M)"]
      Suc.prems by force
  ultimately have "\<alpha>^j*sq_norm (Mt!(i+j))\<le>\<alpha>^j*\<alpha>*(sq_norm (Mt!(i+Suc j)))"
    by simp
  moreover have "sq_norm(Mt!i)\<le> \<alpha>^j * sq_norm (Mt!(i+j))"
    using Suc by linarith
  ultimately have "sq_norm(Mt!i)\<le>\<alpha>^j*\<alpha>*(sq_norm (Mt!(i+Suc j)))" by order
  moreover have "\<alpha>^j*\<alpha> = \<alpha>^(Suc j)" by simp
  ultimately show ?case by argo
qed

lemma basis_decay_cor:
  fixes i::nat
  fixes j::nat
  assumes "i<n"
  assumes "j<n"
  assumes "i\<le>j"
  shows "sq_norm (Mt!i)\<le> \<alpha>^n*sq_norm(Mt!j)"
proof-
  have 1:"sq_norm (Mt!i)\<le> \<alpha>^(j-i)*sq_norm(Mt!j)"
    using basis_decay[of i "j-i"] assms
    by simp
  have "\<alpha>^(j-i)\<le>\<alpha>^n" using assms unfolding \<alpha>_def by force
  then have "\<alpha>^(j-i)*sq_norm(Mt!j)\<le>\<alpha>^n*sq_norm(Mt!j)"
    using mult_right_mono by blast
  then show ?thesis using 1 by order
qed



theorem Babai_Correct:
  shows "real_of_rat ((sq_norm (s n))::rat) \<le> 2^n * closest_distance_sq\<and> s n \<in> coset"
proof-
  let ?s = "s n"
  let ?component = "(\<lambda>i. (?s\<bullet>Mt!i)^2/(sq_norm (Mt!i)))"
  obtain v where wit_v:"witness v (eps_closest)"
    using witness_exists by force
  have split_norm:"sq_norm ?s = sum_list (map ?component [0..<n])"
    using s_dim[of n] sq_norm_from_Mt[of ?s] by fast
  have "I+1\<in>\<nat>" using I_geq
    using Nats_0 Nats_1 Nats_add R.add.l_inv_ex R.add.r_inv_ex add_diff_cancel_right' 
      cring_simprules(21) rangeI range_abs_Nats verit_la_disequality verit_minus_simplify(3) 
      zabs_def zle_add1_eq_le by auto
  then obtain Inat where Inat_def:"int Inat = I+1"
    using Nats_cases by metis
  then have Inat_small:"Inat\<le>n" using I_leq by fastforce
  then have "[0..<n] = [0..<Inat] @ [Inat..<n]"
    by (metis bot_nat_0.extremum_uniqueI le_Suc_ex nat_le_linear upt_add_eq_append)
  then have split_norm_sum:"sq_norm ?s = sum_list (map ?component [0..<Inat]) + sum_list (map ?component [Inat..<n])"
    using split_norm by force


  have "?component i \<le> eps_closest " if i:"Inat\<le>i\<and>i<n" for i
  proof-
    have ge0:"sq_norm (Mt!i) > 0"
      using gram_schmidt_fs_lin_indpt.sq_norm_pos[of n "RAT M" i]
            M_locale_2 M_locale_1 gram_schmidt_fs_Rn.main_connect[of n "(RAT M)"]
            i by force
    then have "?component i = (v\<bullet> Mt!i)^2 / (sq_norm (Mt!i))"
      using ge0 correct_coord[of v i] wit_v Inat_def i 
      by auto
    also have "(v\<bullet>Mt!i)^2\<le> (sq_norm v)*sq_norm (Mt!i)"
      using scalar_prod_Cauchy[of v n "Mt!i"]
            dim_vecs_in_Mt[of i] carrier_vecI[of v] carrier_vecI[of "Mt!i"] wit_v
            i
      unfolding witness_def
      by algebra
    also have "sq_norm v \<le> eps_closest"
      using wit_v unfolding witness_def by fast
    finally show ?thesis using ge0
      by (simp add: divide_right_mono)
  qed
  then have "\<And>x. x\<in>set [Inat..<n] \<Longrightarrow> ?component x \<le> (\<lambda>i. eps_closest) x" by simp
  then have "sum_list (map ?component [Inat..<n])\<le> sum_list (map (\<lambda>i. eps_closest) [Inat..<n])"
    using sum_list_mono[of "[Inat..<n]" ?component "(\<lambda>i. eps_closest)"] by argo
  then have right_sum:"sum_list (map ?component [Inat..<n])\<le>(rat_of_nat (n-Inat))*eps_closest"
    using sum_list_triv[of "eps_closest" "[Inat..<n]" ] by force
  have "(1::rat) \<le>\<alpha>" unfolding \<alpha>_def by fastforce 
  moreover have "n\<ge>0" by simp
  ultimately have "(1::rat)\<le>\<alpha>^n" by simp
  moreover have "(0::rat)\<le>1" by simp
  moreover have "0\<le>(rat_of_nat (n-Inat))*eps_closest"
  proof-
    have "0\<le>(rat_of_nat (n-Inat))" using Inat_small by fast
    moreover have "0\<le>eps_closest" 
    proof(cases "closest_distance_sq = 0")
      case t:True
      then show ?thesis using eps_closest_lemma closest_distance_sq_pos unfolding close_condition_def
        by auto
    next
      case f:False
      then show ?thesis using eps_closest_lemma closest_distance_sq_pos unfolding close_condition_def
        by (smt (verit, del_insts) zero_le_of_rat_iff)
    qed
    ultimately show ?thesis by blast
  qed
  ultimately have "(rat_of_nat (n-Inat))*eps_closest \<le> (rat_of_nat (n-Inat))*eps_closest * \<alpha>^n"
    using mult_left_mono[of 1 "\<alpha>^n" "(rat_of_nat (n-Inat))*eps_closest"] by linarith
  then have "sum_list (map ?component [Inat..<n])\<le>(rat_of_nat (n-Inat))*eps_closest*\<alpha>^n" using right_sum by order
  then have right_sum_alpha:"sum_list (map ?component [Inat..<n])\<le>(rat_of_nat (n-Inat))*\<alpha>^n*eps_closest"
    by algebra
  have "sum_list (map ?component [0..<Inat]) + sum_list (map ?component [Inat..<n])\<le> (rat_of_int n)*\<alpha>^n*eps_closest"
  proof(cases "Inat = 0")
    case Inat:True
    then have "sum_list (map ?component [0..<Inat]) = 0" by auto
    then have "sum_list (map ?component [0..<Inat]) + sum_list (map ?component [Inat..<n])\<le>(rat_of_int (n-Inat))*\<alpha>^n * eps_closest"
      using right_sum_alpha by simp
    also have "n-Inat = n" using Inat by simp
    finally show ?thesis by linarith
  next
    case False
    then have non_zero:"Inat>0" by blast
    then have I_not_min:"I\<ge>0" using Inat_def by simp
    then have non_empty:"I = Max ({i\<in>{0..<n}. ((sq_norm (Mt!i)::rat))\<le>4*eps_closest}::nat set)"
      unfolding I_def by presburger
    then have max:"Inat-1= Max({i\<in>{0..<n}. ((sq_norm (Mt!i)::rat))\<le>4*eps_closest}::nat set)"
      using Inat_def by linarith
    then have "Inat -1 \<in> ({i\<in>{0..<n}. ((sq_norm (Mt!i)::rat))\<le>4*eps_closest}::nat set)"
    proof-
      have "finite ({i\<in>{0..<n}. ((sq_norm (Mt!i)::rat))\<le>4*eps_closest}::nat set)"
        by simp
      moreover have "({i\<in>{0..<n}. ((sq_norm (Mt!i)::rat))\<le>4*eps_closest}::nat set)\<noteq>{}"
        using I_not_min unfolding I_def by presburger
      ultimately show "Inat -1 \<in> ({i\<in>{0..<n}. ((sq_norm (Mt!i)::rat))\<le>4*eps_closest}::nat set)"
        using max eq_Max_iff by blast
    qed 
    then have 2:"(sq_norm (Mt!(Inat-1))::rat)\<le>4*eps_closest" by blast
    have "(1::rat) \<le>\<alpha>" unfolding \<alpha>_def by fastforce 
    moreover have "n\<ge>0" by simp
    ultimately have "(1::rat)\<le>\<alpha>^n" by simp 
    then have "((1/4)::rat)\<le>1/4 * \<alpha>^n" by auto
    then have "(0::rat)<1/4*\<alpha>^n" by linarith
    moreover have "0<(sq_norm (Mt!(Inat-1))::rat)"
      using gram_schmidt_fs_lin_indpt.sq_norm_pos[of n "RAT M" "Inat-1"]
            M_locale_2 M_locale_1 gram_schmidt_fs_Rn.main_connect[of n "(RAT M)"]
            non_zero Inat_small by force
    ultimately have bound:"1/4 *\<alpha>^n* (sq_norm (Mt!(Inat-1)))\<le> ((1/4 * \<alpha>^n)* 4*eps_closest)"
       using 2 by auto
    have "?component i \<le> \<alpha>^n *eps_closest" if list1:"i<Inat" for i
    proof-
      have 1:"0<n-i" using list1 Inat_small by simp
      then have "?s\<bullet>Mt!i = (s (n-i))\<bullet>Mt!i"
        using coord_invariance[of "n-i" "n-i" i] by fastforce
      then have "abs(?s\<bullet>Mt!i)\<le> (1/2)*(sq_norm (Mt!i))"
        using small_orth_coord[of "n-i"] 1 by force
      then have "(?s\<bullet>Mt!i)^2 \<le> ((1/2)*(sq_norm (Mt!i)))^2"
        by (meson abs_ge_self abs_le_square_iff ge_trans)
      moreover have ge0:"sq_norm (Mt!i) > 0"
        using gram_schmidt_fs_lin_indpt.sq_norm_pos[of n "RAT M" i]
              M_locale_2 M_locale_1 gram_schmidt_fs_Rn.main_connect[of n "(RAT M)"]
              list1 Inat_small by force
      ultimately have "?component i \<le>((1/2)*(sq_norm (Mt!i)))^2 / (sq_norm (Mt!i))"
        using divide_right_mono by auto
      also have "((1/2)*(sq_norm (Mt!i)))^2/ (sq_norm (Mt!i)) = 1/4 * (sq_norm (Mt!i))^2/ (sq_norm (Mt!i))"
        by (metis (no_types, lifting) gs.cring_simprules(12) numeral_Bit0_eq_double power2_eq_square times_divide_eq_left times_divide_times_eq)
      also have "1/4 * (sq_norm (Mt!i))^2/ (sq_norm (Mt!i)) = 1/4 * (sq_norm (Mt!i))"
        using ge0 by (simp add: power2_eq_square)
      also have "1/4*sq_norm (Mt!i) \<le> 1/4*\<alpha>^n * (sq_norm (Mt!(Inat-1)))"
        using basis_decay_cor[of i "Inat-1"] list1 Inat_small mult_left_mono[
            of "sq_norm (Mt!i)" "\<alpha>^n * (sq_norm (Mt!(Inat-1)))" "1/4"]
          by linarith
      finally have "?component i \<le> 1/4 * \<alpha>^n * 4 *eps_closest"
        using bound by linarith
      also have "1/4 * \<alpha>^n * 4 * eps_closest=\<alpha>^n * eps_closest" by force
      finally show ?thesis by blast
    qed
    then have "sum_list (map ?component [0..<Inat])\<le> sum_list (map (\<lambda>i. \<alpha>^n * eps_closest)[0..<Inat])"
      using sum_list_mono[of "[0..<Inat]" ?component "(\<lambda>i. \<alpha>^n * eps_closest)"] by fastforce
    then have "sum_list (map ?component [0..<Inat])\<le> (rat_of_int Inat)*\<alpha>^n * eps_closest"
      using sum_list_triv[of "\<alpha>^n * eps_closest" "[0..<Inat]"] by auto
    then have "(sum_list (map ?component [0..<Inat])) + sum_list (map ?component [Inat..<n])
                \<le> (rat_of_int Inat)*\<alpha>^n * eps_closest+(rat_of_int (n-Inat))*\<alpha>^n * eps_closest"
      using right_sum_alpha by linarith
    then have "(sum_list (map ?component [0..<Inat])) + sum_list (map ?component [Inat..<n])
                \<le> ((rat_of_int Inat)+(rat_of_int (n-Inat)))*\<alpha>^n * eps_closest"
      using gs.cring_simprules(13) by auto
    then show ?thesis
      by (metis (no_types, lifting) Inat_small add_diff_inverse_nat diff_is_0_eq' less_nat_zero_code 
          of_int_of_nat_eq of_nat_add zero_less_diff)
  qed
  then have "sq_norm ?s \<le> (rat_of_int n)*\<alpha>^n * eps_closest"
    using split_norm_sum by argo
  then have "real_of_rat (sq_norm ?s) \<le> real_of_rat ((rat_of_int n)*\<alpha>^n * eps_closest)"
    by (simp add: of_rat_less_eq)
  also have "real_of_rat ((rat_of_int n)*\<alpha>^n * eps_closest)\<le>2^n*closest_distance_sq"
    using present_bound_nicely[of n]
    by blast
  finally show ?thesis
    using coset_s[of n]
    by fast
qed



end
end
