section \<open>Cheeger Inequality\label{sec:cheeger_ineq}\<close>

text \<open>The Cheeger inequality relates edge expansion (a combinatorial property) with the second
largest eigenvalue.\<close>

theory Expander_Graphs_Cheeger_Inequality
  imports 
    Expander_Graphs_Eigenvalues
begin

unbundle intro_cong_syntax
hide_const Quantum.T

context regular_graph
begin

lemma edge_expansionD2:
  assumes "m = card (S \<inter> verts G)" "2*m \<le> n"
  shows "\<Lambda>\<^sub>e * m \<le> real (card (edges_betw S (-S)))"
proof -
  define S' where "S' = S \<inter> verts G"
  have "\<Lambda>\<^sub>e * m = \<Lambda>\<^sub>e * card S'"
    using assms(1) S'_def by simp
  also have "... \<le> real (card (edges_betw S' (-S')))"
    using assms unfolding S'_def by (intro edge_expansionD) auto
  also have "... = real (card (edges_betw S (-S)))"
    unfolding S'_def edges_betw_def
    by (intro arg_cong[where f="real"] arg_cong[where f="card"]) auto
  finally show ?thesis by simp
qed

lemma edges_betw_sym:
  "card (edges_betw S T) = card (edges_betw T S)" (is "?L = ?R")
proof -
  have "?L =  (\<Sum>a \<in> arcs G. of_bool (tail G a \<in> S \<and> head G a \<in> T))"
    unfolding edges_betw_def of_bool_def by (simp add:sum.If_cases Int_def)
  also have "... = (\<Sum>e \<in># edges G. of_bool (fst e \<in> S \<and> snd e \<in> T))"
    unfolding sum_unfold_sum_mset edges_def arc_to_ends_def
    by (simp add:image_mset.compositionality comp_def)
  also have "... =  (\<Sum>e \<in># edges G. of_bool (snd e \<in> S \<and> fst e \<in> T))"
    by (subst edges_sym[OF sym, symmetric]) 
        (simp add:image_mset.compositionality comp_def case_prod_beta)
  also have "... = (\<Sum>a \<in> arcs G. of_bool (tail G a \<in> T \<and> head G a \<in> S))"
    unfolding sum_unfold_sum_mset edges_def arc_to_ends_def
    by (simp add:image_mset.compositionality comp_def conj.commute)
  also have "... = ?R"
    unfolding edges_betw_def of_bool_def by (simp add:sum.If_cases Int_def)
  finally show ?thesis by simp
qed

lemma edges_betw_reg:
  assumes "S \<subseteq> verts G"
  shows "card (edges_betw S UNIV) = card S * d" (is "?L = ?R")
proof -
  have "?L = card (\<Union>(out_arcs G ` S))"
    unfolding edges_betw_def out_arcs_def by (intro arg_cong[where f="card"]) auto
  also have "... = (\<Sum>i\<in>S. card (out_arcs G i))"
    using finite_subset[OF assms] unfolding out_arcs_def
    by (intro card_UN_disjoint) auto
  also have "... = (\<Sum>i\<in>S. out_degree G i)"
    unfolding out_degree_def by simp
  also have "... = (\<Sum>i\<in>S. d)"
    using assms by (intro sum.cong reg) auto
  also have "... = ?R"
    by simp
  finally show ?thesis by simp
qed

text \<open>The following proof follows Hoory et al.~@{cite \<open>\S 4.5.1\<close> "hoory2006"}.\<close>

lemma cheeger_aux_2:
  assumes "n > 1"
  shows "\<Lambda>\<^sub>e \<ge> d*(1-\<Lambda>\<^sub>2)/2"
proof -
  have "real (card (edges_betw S (-S))) \<ge> (d * (1 - \<Lambda>\<^sub>2) / 2) * real (card S)" 
    if "S \<subseteq> verts G" "2 * card S \<le> n" for S
  proof -
    let ?ct = "real (card (verts G - S))" 
    let ?cs = "real (card S)" 

    have "card (edges_betw S S)+card (edges_betw S (-S))=card(edges_betw S S\<union>edges_betw S (-S))"
      unfolding edges_betw_def by (intro card_Un_disjoint[symmetric]) auto
    also have "... = card (edges_betw S UNIV)"
      unfolding edges_betw_def by (intro arg_cong[where f="card"]) auto
    also have "... = d * ?cs"
      using edges_betw_reg[OF that(1)] by simp
    finally have "card (edges_betw S S) + card (edges_betw S (-S)) = d * ?cs" by simp 
    hence 4: "card (edges_betw S S) = d * ?cs - card (edges_betw S (-S))"
      by simp

    have "card(edges_betw S(-S))+card(edges_betw(-S)(-S))=card(edges_betw S(-S)\<union>edges_betw(-S)(-S))"
      unfolding edges_betw_def by (intro card_Un_disjoint[symmetric]) auto
    also have "... = card (edges_betw UNIV (verts G - S))"
      unfolding edges_betw_def by (intro arg_cong[where f="card"]) auto
    also have "... = card (edges_betw (verts G - S) UNIV)"
      by (intro edges_betw_sym)
    also have "... = d * ?ct"
      using edges_betw_reg by auto
    finally have "card (edges_betw S (-S)) + card (edges_betw (-S) (-S)) = d * ?ct" by simp
    hence 5: "card (edges_betw (-S) (-S)) = d * ?ct - card (edges_betw S (-S))"
      by simp
    have 6: "card (edges_betw (-S) S) = card (edges_betw S (-S))" 
      by (intro edges_betw_sym)

    have "?cs + ?ct =real (card (S \<union> (verts G- S)))"
      unfolding of_nat_add[symmetric] using finite_subset[OF that(1)]
      by (intro_cong "[\<sigma>\<^sub>1 of_nat, \<sigma>\<^sub>1 card]" more:card_Un_disjoint[symmetric]) auto
    also have "... = real n"
      unfolding n_def  using that(1) by (intro_cong "[\<sigma>\<^sub>1 of_nat, \<sigma>\<^sub>1 card]") auto 
    finally have 7: "?cs + ?ct = n"  by simp

    define f  where 
      "f x = real (card (verts G - S)) * of_bool (x \<in> S) - card S * of_bool (x \<notin> S)" for x

    have "g_inner f (\<lambda>_. 1) = ?cs * ?ct - real (card (verts G \<inter> {x. x \<notin> S})) * ?cs"
      unfolding g_inner_def f_def using Int_absorb1[OF that(1)] by (simp add:sum_subtractf)
    also have "... = ?cs * ?ct - ?ct * ?cs"
      by (intro_cong "[\<sigma>\<^sub>2 (-), \<sigma>\<^sub>2 (*), \<sigma>\<^sub>1 of_nat, \<sigma>\<^sub>1 card]") auto
    also have "... = 0" by simp
    finally have 11:" g_inner f (\<lambda>_. 1) = 0" by simp

    have "g_norm f^2 = (\<Sum>v\<in>verts G. f v^2)"
      unfolding g_norm_sq g_inner_def conjugate_real_def by (simp add:power2_eq_square)
    also have "...=(\<Sum>v\<in>verts G. ?ct^2*(of_bool (v \<in> S))\<^sup>2)+(\<Sum>v\<in>verts G. ?cs^2*(of_bool (v \<notin> S))\<^sup>2)"
      unfolding f_def power2_diff by (simp add:sum.distrib sum_subtractf power_mult_distrib)
    also have "... = real (card (verts G \<inter> S))*?ct^2 + real (card (verts G \<inter> {v. v \<notin> S})) * ?cs^2"
      unfolding of_bool_def by (simp add:if_distrib if_distribR sum.If_cases)
    also have "... = real(card S)*(real(card(verts G-S)))\<^sup>2 + real(card(verts G-S))*(real(card S))\<^sup>2"
      using that(1) by (intro_cong "[\<sigma>\<^sub>2(+), \<sigma>\<^sub>2 (*), \<sigma>\<^sub>2 power, \<sigma>\<^sub>1 of_nat, \<sigma>\<^sub>1 card]") auto
    also have "...  = real(card S)*real (card (verts G -S))*(?cs + ?ct)"
      by (simp add:power2_eq_square algebra_simps)
    also have "...  = real(card S)*real (card (verts G -S))*n"
      unfolding 7 by simp
    finally have 9:" g_norm f^2 = real(card S)*real (card (verts G -S))*real n" by simp

    have "(\<Sum>a \<in> arcs G. f (head G a) * f (tail G a)) = 
      (card (edges_betw S S) * ?ct*?ct) + (card (edges_betw (-S) (-S)) * ?cs*?cs) - 
      (card (edges_betw S (-S)) * ?ct*?cs) - (card (edges_betw (-S) S) * ?cs*?ct)"
      unfolding f_def by (simp add:of_bool_def algebra_simps Int_def if_distrib if_distribR 
          edges_betw_def sum.If_cases)
    also have "... = d*?cs*?ct*(?cs+?ct) - card (edges_betw S (-S))*(?ct*?ct+2*?ct*?cs+?cs*?cs)"
      unfolding 4 5 6 by (simp add:algebra_simps)
    also have "... = d*?cs*?ct*n - (?ct+?cs)^2 * card (edges_betw S (-S))"
      unfolding power2_diff 7 power2_sum by (simp add:ac_simps power2_eq_square)
    also have "... = d *?cs*?ct*n - n^2 * card (edges_betw S (-S))"
      using 7 by (simp add:algebra_simps)
    finally have 8:"(\<Sum>a \<in> arcs G. f(head G a)*f(tail G a))=d*?cs*?ct*n-n^2*card(edges_betw S (-S))" 
      by simp

    have "d*?cs*?ct*n-n^2*card(edges_betw S (-S)) = (\<Sum>a \<in> arcs G. f (head G a) * f (tail G a))"
      unfolding 8 by simp
    also have "... \<le> d * (g_inner f (g_step f))"
      unfolding g_inner_step_eq using d_gt_0
      by simp
    also have "... \<le> d * (\<Lambda>\<^sub>2 * g_norm f^2)"
      by (intro mult_left_mono os_expanderD 11) auto
    also have "... = d * \<Lambda>\<^sub>2 * ?cs*?ct*n"
      unfolding 9 by simp
    finally have "d*?cs*?ct*n-n^2*card(edges_betw S (-S)) \<le> d * \<Lambda>\<^sub>2 * ?cs*?ct*n" 
      by simp
    hence "n * n * card (edges_betw S (-S)) \<ge> n * (d * ?cs * ?ct * (1-\<Lambda>\<^sub>2))"
      by (simp add:power2_eq_square algebra_simps)
    hence 10:"n * card (edges_betw S (-S)) \<ge> d * ?cs * ?ct * ( 1-\<Lambda>\<^sub>2)"
      using n_gt_0 by simp 

    have "(d * (1 - \<Lambda>\<^sub>2) / 2) * ?cs = (d * (1-\<Lambda>\<^sub>2) * (1 - 1 / 2)) * ?cs"
      by simp
    also have "... \<le> d * (1-\<Lambda>\<^sub>2) * ((n - ?cs) / n) * ?cs"
      using that n_gt_0 \<Lambda>\<^sub>2_le_1 
      by (intro mult_left_mono mult_right_mono mult_nonneg_nonneg) auto
    also have "... = (d * (1-\<Lambda>\<^sub>2) * ?ct / n) * ?cs"
      using 7 by simp
    also have "... = d * ?cs * ?ct * (1-\<Lambda>\<^sub>2) / n"
      by simp
    also have "... \<le> n * card (edges_betw S (-S)) / n"
      by (intro divide_right_mono 10) auto
    also have "... = card (edges_betw S (-S))"
      using n_gt_0 by simp
    finally show ?thesis by simp
  qed
  thus ?thesis
    by (intro edge_expansionI assms) auto
qed

end

lemma surj_onI:
  assumes "\<And>x. x \<in> B \<Longrightarrow> g x \<in> A \<and> f (g x) = x"
  shows "B \<subseteq> f ` A"
  using assms by force

lemma find_sorted_bij_1:
  fixes g :: "'a \<Rightarrow> ('b :: linorder)"
  assumes "finite S"
  shows "\<exists>f. bij_betw f {..<card S} S \<and> mono_on {..<card S} (g\<circ> f)"
proof -
  define h where "h x = from_nat_into S x" for x

  have h_bij:"bij_betw h {..<card S} S"
    unfolding h_def using bij_betw_from_nat_into_finite[OF assms] by simp

  define xs where "xs = sort_key (g \<circ> h) [0..<card S]"
  define f where "f i = h (xs ! i)" for i

  have l_xs: "length xs = card S" 
    unfolding xs_def by auto 
  have set_xs: "set xs = {..<card S}" 
    unfolding xs_def by auto 
  have dist_xs: "distinct xs" 
    using l_xs set_xs by (intro card_distinct) simp
  have sorted_xs: "sorted (map (g \<circ> h) xs)"
    unfolding xs_def using sorted_sort_key by simp

  have "(\<lambda>i. xs ! i) ` {..<card S} = set xs"
    using l_xs by (auto simp:in_set_conv_nth)
  also have "... = {..<card S}"
    unfolding set_xs by simp
  finally have set_xs': 
    "(\<lambda>i. xs ! i) ` {..<card S} = {..<card S}" by simp

  have "f ` {..<card S} = h ` ((\<lambda>i. xs ! i) ` {..<card S})"
    unfolding f_def image_image by simp
  also have "... = h ` {..<card S}"
    unfolding set_xs' by simp
  also have "... = S"
    using bij_betw_imp_surj_on[OF h_bij] by simp
  finally have 0: "f ` {..<card S} = S" by simp

  have "inj_on ((!) xs) {..<card S}" 
    using dist_xs l_xs unfolding distinct_conv_nth 
    by (intro inj_onI) auto  
  hence "inj_on (h \<circ> (\<lambda>i. xs ! i)) {..<card S}"
    using set_xs' bij_betw_imp_inj_on[OF h_bij]
    by (intro comp_inj_on) auto
  hence 1: "inj_on f {..<card S}"
    unfolding f_def comp_def by simp
  have 2: "mono_on {..<card S} (g \<circ> f)" 
    using sorted_nth_mono[OF sorted_xs] l_xs unfolding f_def 
    by (intro mono_onI)  simp
  thus ?thesis 
    using 0 1 2 unfolding bij_betw_def by auto
qed

lemma find_sorted_bij_2:
  fixes g :: "'a \<Rightarrow> ('b :: linorder)"
  assumes "finite S"
  shows "\<exists>f. bij_betw f S {..<card S} \<and> (\<forall>x y. x \<in> S \<and> y \<in> S \<and> f x < f y \<longrightarrow> g x \<le> g y)"
proof -
  obtain f where f_def: "bij_betw f {..<card S} S" "mono_on {..<card S} (g \<circ> f)"
    using find_sorted_bij_1 [OF assms] by auto

  define h where "h = the_inv_into {..<card S} f"
  have bij_h: "bij_betw h S {..<card S}"
    unfolding h_def by (intro bij_betw_the_inv_into f_def)

  moreover have "g x \<le> g y" if "h x < h y" "x \<in> S" "y \<in> S" for x y
  proof -
    have "h y < card S" "h x < card S" "h x \<le> h y"
      using bij_betw_apply[OF bij_h] that by auto
    hence "g (f (h x)) \<le> g (f (h y))"
      using f_def(2) unfolding mono_on_def by simp
    moreover have "f ` {..<card S} = S"
      using bij_betw_imp_surj_on[OF f_def(1)] by simp 
    ultimately show "g x \<le> g y"
      unfolding h_def using that f_the_inv_into_f[OF bij_betw_imp_inj_on[OF f_def(1)]]
      by auto
  qed
  ultimately show ?thesis by auto
qed

context regular_graph_tts
begin

text \<open>Normalized Laplacian of the graph\<close>
definition L where "L = mat 1 - A"

lemma L_pos_semidefinite:
  fixes v :: "real ^'n"
  shows  "v \<bullet> (L *v v)  \<ge> 0"
proof -
  have "0 = v \<bullet> v - norm v^2" unfolding power2_norm_eq_inner by simp
  also have "... \<le> v \<bullet> v - abs (v \<bullet> (A *v v))"
    by (intro diff_mono rayleigh_bound) auto
  also have "... \<le> v \<bullet> v - v \<bullet> (A *v v)"
    by (intro diff_mono) auto
  also have "... = v \<bullet> (L *v v)"
    unfolding L_def by (simp add:algebra_simps)
  finally show ?thesis by simp
qed

text \<open>The following proof follows Hoory et al.~@{cite \<open>\S 4.5.2\<close> "hoory2006"}.\<close>

lemma cheeger_aux_1:
  assumes "n > 1"
  shows "\<Lambda>\<^sub>e \<le> d * sqrt (2 * (1-\<Lambda>\<^sub>2))"
proof -
  obtain v where v_def: "v \<bullet> 1 = 0" "v \<noteq> 0" "A *v v = \<Lambda>\<^sub>2 *s v"
    using \<Lambda>\<^sub>2_eq_\<gamma>\<^sub>2 \<gamma>\<^sub>2_ev[OF assms] by auto

  have "False" if "2*card {i. (1 *s v) $h i > 0} > n" "2*card {i. ((-1) *s v) $h i > 0} > n"
  proof -
    have "2 * n = n + n" by simp
    also have "... <2 * card {i.  (1 *s v) $h i > 0} + 2 * card {i. ((-1) *s v) $h i > 0}"
      by (intro add_strict_mono that)
    also have "... = 2 * (card {i.  (1 *s v) $h i > 0} + card {i.  ((-1) *s v) $h i > 0})"
      by simp
    also have "... = 2 * (card ({i.  (1 *s v) $h i > 0} \<union> {i.  ((-1) *s v) $h i > 0}))"
      by (intro arg_cong2[where f="(*)"] card_Un_disjoint[symmetric]) auto
    also have "... \<le> 2 * (card (UNIV :: 'n set))"
      by (intro mult_left_mono card_mono) auto
    finally have "2 * n < 2 * n" 
      unfolding n_def card_n by auto
    thus ?thesis by simp
  qed
  then obtain \<beta>  :: real where \<beta>_def: "\<beta> = 1 \<or> \<beta>=(-1)" "2* card {i. (\<beta> *s v) $h i > 0 } \<le> n"
    unfolding not_le[symmetric] by blast

  define g where "g = \<beta> *s v"

  have g_orth: "g \<bullet> 1 = 0" unfolding g_def using v_def(1) 
    by (simp add: scalar_mult_eq_scaleR)
  have g_nz: "g \<noteq> 0" 
    unfolding g_def using \<beta>_def(1) v_def(2) by auto
  have g_ev: "A *v g = \<Lambda>\<^sub>2 *s g"
    unfolding g_def scalar_mult_eq_scaleR matrix_vector_mult_scaleR v_def(3) by auto
  have g_supp: "2 * card { i. g $h i > 0 } \<le> n"
    unfolding g_def using \<beta>_def(2) by auto

  define f where "f = (\<chi> i. max (g $h i) 0)"

  have "(L *v f) $h i \<le> (1-\<Lambda>\<^sub>2) * g $h i" (is "?L \<le> ?R") if "g $h i > 0" for i
  proof -
    have "?L = f $h i - (A *v f) $h i"
      unfolding L_def by (simp add:algebra_simps)
    also have "... = g $h i - (\<Sum>j \<in> UNIV. A $h i $h j * f $h j)"
      unfolding matrix_vector_mult_def f_def using that by auto
    also have "... \<le> g $h i - (\<Sum>j \<in> UNIV. A $h i $h j * g $h j)"
      unfolding f_def A_def by (intro diff_mono sum_mono mult_left_mono) auto
    also have "... = g $h i - (A *v g) $h i" 
      unfolding matrix_vector_mult_def by simp
    also have "... = (1-\<Lambda>\<^sub>2) * g $h i"
      unfolding g_ev by (simp add:algebra_simps)
    finally show ?thesis by simp
  qed
  moreover have "f $h i \<noteq> 0 \<Longrightarrow> g $h i > 0 "for i 
    unfolding f_def by simp
  ultimately have  0:"(L *v f) $h i \<le> (1-\<Lambda>\<^sub>2) * g $h i \<or> f $h i = 0" for i
    by auto

  text \<open>Part (i) in Hoory et al. (\S 4.5.2) but the operator L here is normalized.\<close>
  have "f \<bullet> (L *v f) = (\<Sum>i\<in>UNIV. (L *v f) $h i * f $h i)"
    unfolding inner_vec_def by (simp add:ac_simps)
  also have "... \<le> (\<Sum>i\<in>UNIV. ((1-\<Lambda>\<^sub>2) * g $h i) * f $h i)"
    by (intro sum_mono mult_right_mono' 0) (simp add:f_def)
  also have "... = (\<Sum>i\<in>UNIV. (1-\<Lambda>\<^sub>2) * f $h i * f $h i)"
    unfolding f_def by (intro sum.cong refl) auto
  also have "... = (1-\<Lambda>\<^sub>2) * (f \<bullet> f)"
    unfolding inner_vec_def by (simp add:sum_distrib_left ac_simps)
  also have "... = (1 - \<Lambda>\<^sub>2) * norm f^2"
    by (simp add: power2_norm_eq_inner)
  finally have h_part_i: "f \<bullet> (L *v f) \<le> (1 - \<Lambda>\<^sub>2) * norm f^2" by simp

  define f' where "f' x = f $h (enum_verts_inv x)" for x
  have f'_alt: "f = (\<chi> i. f' (enum_verts i))"
    unfolding f'_def Rep_inverse by simp

  define B\<^sub>f where "B\<^sub>f  = (\<Sum>a\<in>arcs G. \<bar>f' (tail G a)^2-f' (head G a)^2\<bar>)"

  have "(x + y)^2 \<le> 2 * (x^2  + y^2)" for x y :: real
  proof -
    have "(x + y)^2 = (x^2 + y^2) + 2 * x * y"
      unfolding power2_sum by simp
    also have "... \<le> (x^2 + y^2) + (x^2 + y^2)"
      by (intro add_mono sum_squares_bound) auto
    finally show ?thesis by simp
  qed
  hence "(\<Sum>a\<in>arcs G.(f'(tail G a)+ f'(head G a))\<^sup>2)\<le>(\<Sum>a\<in>arcs G. 2*(f'(tail G a)^2+f'(head G a)^2))"
    by (intro sum_mono) auto
  also have "... = 2*((\<Sum>a\<in>arcs G. f'(tail G a)^2) +  (\<Sum>a\<in>arcs G. f'(head G a)^2))"
    by (simp add:sum_distrib_left)
  also have "... = 4 * d * g_norm f'^2"
    unfolding sum_arcs_tail[where f="\<lambda>x. f' x^2"] sum_arcs_head[where f="\<lambda>x. f' x^2"]
      g_norm_sq g_inner_def by (simp add:power2_eq_square)
  also have "... = 4 * d * norm f^2"
    unfolding g_norm_conv f'_alt by simp
  finally have 1: "(\<Sum>i\<in>arcs G. (f' (tail G i) + f' (head G i))\<^sup>2) \<le> 4*d* norm f^2"
    by simp

  have "(\<Sum>a\<in>arcs G. (f' (tail G a) - f' (head G a))\<^sup>2) = (\<Sum>a\<in>arcs G. (f' (tail G a))\<^sup>2) + 
    (\<Sum>a\<in>arcs G. (f' (head G a))\<^sup>2) - 2* (\<Sum>a\<in>arcs G. f' (tail G a) * f' (head G a))"
    unfolding power2_diff by (simp add:sum_subtractf sum_distrib_left ac_simps)
  also have "... =  2 * (d * (\<Sum>v\<in>verts G. (f' v)\<^sup>2) - (\<Sum>a\<in>arcs G. f' (tail G a) * f' (head G a)))"
    unfolding sum_arcs_tail[where f="\<lambda>x. f' x^2"] sum_arcs_head[where f="\<lambda>x. f' x^2"] by simp
  also have "... =  2 * (d * g_inner f' f' - d * g_inner f' (g_step f'))"
    unfolding g_inner_step_eq using d_gt_0
    by (intro_cong "[\<sigma>\<^sub>2 (*), \<sigma>\<^sub>2 (-)]") (auto simp:power2_eq_square g_inner_def ac_simps)
  also have "... = 2 * d * (g_inner f' f' -g_inner f' (g_step f'))"
    by (simp add:algebra_simps) 
  also have "... = 2 * d * (f \<bullet> f - f \<bullet> (A *v f))"
    unfolding g_inner_conv g_step_conv f'_alt by simp
  also have "... = 2 * d * (f \<bullet> (L *v f))"
    unfolding L_def by (simp add:algebra_simps)
  finally have 2:"(\<Sum>a\<in>arcs G. (f' (tail G a) - f' (head G a))\<^sup>2) = 2 * d * (f \<bullet> (L *v f))" by simp

  have "B\<^sub>f = (\<Sum>a\<in>arcs G. \<bar>f' (tail G a)+f' (head G a)\<bar>*\<bar>f' (tail G a)-f' (head G a)\<bar>)"
    unfolding B\<^sub>f_def abs_mult[symmetric] by (simp add:algebra_simps power2_eq_square)
  also have "...\<le> L2_set (\<lambda>a. f'(tail G a) + f'(head G a)) (arcs G) * 
    L2_set (\<lambda>a. f' (tail G a) - f'(head G a)) (arcs G)"
    by (intro L2_set_mult_ineq)
  also have "... \<le> sqrt (4*d* norm f^2) * sqrt (2 * d * (f \<bullet> (L *v f)))"
    unfolding L2_set_def 2
    by (intro mult_right_mono iffD2[OF real_sqrt_le_iff] 1 real_sqrt_ge_zero 
        mult_nonneg_nonneg L_pos_semidefinite) auto
  also have "... = 2 * sqrt 2 * d * norm f * sqrt (f \<bullet> (L *v f))"
    by (simp add:real_sqrt_mult)
  finally have hoory_4_12: "B\<^sub>f \<le> 2 * sqrt 2 * d * norm f * sqrt (f \<bullet> (L *v f))" 
    by simp
  text \<open>The last statement corresponds to Lemma 4.12 in Hoory et al.\<close>


  obtain \<rho> :: "'a \<Rightarrow> nat" where \<rho>_bij: "bij_betw \<rho> (verts G) {..<n}" and 
    \<rho>_dec: "\<And>x y. x \<in> verts G \<Longrightarrow> y \<in> verts G \<Longrightarrow> \<rho> x < \<rho> y \<Longrightarrow> f' x \<ge> f' y"
    unfolding n_def
    using find_sorted_bij_2[where S="verts G" and g="(\<lambda>x. - f' x)"] by auto

  define \<phi> where "\<phi> = the_inv_into (verts G) \<rho>"
  have \<phi>_bij: "bij_betw \<phi> {..<n} (verts G)"
    unfolding \<phi>_def by (intro bij_betw_the_inv_into \<rho>_bij)

  have "edges G = {# e \<in># edges G . \<rho>(fst e) \<noteq> \<rho>(snd e) \<or> \<rho>(fst e) = \<rho>(snd e) #}"
    by simp
  also have "... = {# e \<in># edges G . \<rho>(fst e) \<noteq> \<rho>(snd e) #} + {#e\<in>#edges G. \<rho>(fst e)=\<rho>(snd e)#}"
    by (simp add:filter_mset_ex_predicates)
  also have "...={# e\<in>#edges G. \<rho>(fst e)<\<rho>(snd e)\<or>\<rho>(fst e)>\<rho>(snd e)#}+{#e\<in>#edges G. fst e=snd e#}"
    using bij_betw_imp_inj_on[OF \<rho>_bij] edge_set
    by (intro arg_cong2[where f="(+)"] filter_mset_cong refl inj_on_eq_iff[where A="verts G"])
     auto
  also have "... = {#e \<in># edges G. \<rho>(fst e) < \<rho> (snd e) #} + 
    {#e \<in># edges G. \<rho>(fst e) > \<rho> (snd e) #} + 
    {#e \<in># edges G. fst e = snd e #}"
    by (intro arg_cong2[where f="(+)"] filter_mset_ex_predicates[symmetric]) auto
  finally have edges_split: "edges G = {#e \<in># edges G. \<rho>(fst e) < \<rho> (snd e) #} + 
    {#e \<in># edges G. \<rho>(fst e) > \<rho> (snd e) #} + {#e \<in># edges G. fst e = snd e #}" 
    by simp

  have \<rho>_lt_n: "\<rho> x < n" if "x \<in> verts G" for x
    using bij_betw_apply[OF \<rho>_bij] that by auto

  have \<phi>_\<rho>_inv: "\<phi> (\<rho> x) = x" if "x \<in> verts G" for x
    unfolding \<phi>_def using bij_betw_imp_inj_on[OF \<rho>_bij]
    by (intro the_inv_into_f_f that) auto

  have \<rho>_\<phi>_inv: "\<rho> (\<phi> x) = x" if "x < n" for x
    unfolding \<phi>_def using bij_betw_imp_inj_on[OF \<rho>_bij] bij_betw_imp_surj_on[OF \<rho>_bij] that
    by (intro f_the_inv_into_f) auto

  define \<tau> where "\<tau> x = (if x < n then f' (\<phi> x) else 0)" for x

  have \<tau>_nonneg: "\<tau> k \<ge> 0" for k 
    unfolding \<tau>_def f'_def f_def by auto

  have \<tau>_antimono: "\<tau> k \<ge> \<tau> l" if " k < l" for k l
  proof (cases "l \<ge> n")
    case True
    hence "\<tau> l = 0" unfolding \<tau>_def by simp
    then show ?thesis using \<tau>_nonneg by simp 
  next
    case False
    hence "\<tau> l = f' (\<phi> l)" 
      unfolding \<tau>_def by simp
    also have "... \<le> f' (\<phi> k)"
      using \<rho>_\<phi>_inv False that 
      by (intro \<rho>_dec bij_betw_apply[OF \<phi>_bij]) auto  
    also have "... = \<tau> k"
      unfolding \<tau>_def using False that by simp
    finally show ?thesis by simp
  qed

  define m :: nat where "m = Min {i. \<tau> i = 0 \<and> i \<le> n}"

  have "\<tau> n = 0" 
    unfolding \<tau>_def by simp
  hence "m \<in> {i. \<tau> i = 0 \<and> i \<le> n}"
    unfolding m_def by (intro Min_in) auto

  hence m_rel_1: "\<tau> m = 0" and m_le_n: "m \<le> n" by auto

  have "\<tau> k > 0" if "k < m" for k
  proof (rule ccontr)
    assume "\<not>(\<tau> k > 0)" 
    hence "\<tau> k = 0"
      by (intro order_antisym \<tau>_nonneg) simp
    hence "k \<in> {i. \<tau> i = 0 \<and> i \<le> n}"
      using that m_le_n by simp
    hence "m \<le> k" 
      unfolding m_def by (intro Min_le) auto
    thus "False" using that by simp
  qed
  hence m_rel_2: "f' x > 0" if "x \<in> \<phi> ` {..<m}" for x
    unfolding \<tau>_def using m_le_n that by auto

  have "2 * m = 2 * card {..<m}" by simp
  also have "... = 2 * card (\<phi> ` {..<m})" 
    using m_le_n inj_on_subset[OF bij_betw_imp_inj_on[OF \<phi>_bij]]
    by (intro_cong "[\<sigma>\<^sub>2 (*)]" more:card_image[symmetric]) auto
  also have "... \<le> 2 * card {x \<in> verts G. f' x > 0}"
    using m_rel_2 bij_betw_apply[OF \<phi>_bij] m_le_n
    by (intro mult_left_mono card_mono subsetI) auto 
  also have "... = 2 * card (enum_verts_inv ` {x \<in> verts G. f $h (enum_verts_inv x) > 0})"
    unfolding f'_def using Abs_inject
    by (intro arg_cong2[where f="(*)"] card_image[symmetric] inj_onI) auto 
  also have "... = 2 * card {x. f $h x > 0}"
    using Rep_inverse Rep_range unfolding f'_def by (intro_cong "[\<sigma>\<^sub>2 (*), \<sigma>\<^sub>1 card]" 
        more:subset_antisym image_subsetI surj_onI[where g="enum_verts"]) auto 
  also have "... = 2 * card {x. g $h x > 0}"
    unfolding f_def by (intro_cong "[\<sigma>\<^sub>2 (*), \<sigma>\<^sub>1 card]") auto
  also have "... \<le> n" 
    by (intro g_supp)
  finally have m2_le_n: "2*m \<le> n" by simp

  have "\<tau> k \<le> 0" if "k > m" for k
    using m_rel_1 \<tau>_antimono that by metis
  hence "\<tau> k \<le> 0" if "k \<ge> m" for k
    using m_rel_1 that by (cases "k > m") auto
  hence \<tau>_supp: "\<tau> k = 0" if "k \<ge> m" for k
    using that  by (intro order_antisym \<tau>_nonneg) auto

  have 4: "\<rho> v \<le> x \<longleftrightarrow> v \<in> \<phi> ` {..x}" if "v \<in> verts G" "x < n" for v x
  proof -
    have "\<rho> v \<le> x \<longleftrightarrow> \<rho> v \<in> {..x}" 
      by simp
    also have "... \<longleftrightarrow> \<phi> (\<rho> v) \<in> \<phi> ` {..x}"
      using bij_betw_imp_inj_on[OF \<phi>_bij] bij_betw_apply[OF \<rho>_bij] that
      by (intro inj_on_image_mem_iff[where B="{..<n}", symmetric]) auto
    also have "... \<longleftrightarrow> v \<in> \<phi> ` {..x}"
      unfolding \<phi>_\<rho>_inv[OF that(1)] by simp
    finally show ?thesis by simp
  qed

  have "B\<^sub>f = (\<Sum>a\<in>arcs G. \<bar>f' (tail G a)^2 - f' (head G a)^2\<bar>)"
    unfolding B\<^sub>f_def by simp
  also have "... = (\<Sum>e \<in># edges G. \<bar>f' (fst e)^2 - f' (snd e)^2\<bar>)"
    unfolding edges_def arc_to_ends_def sum_unfold_sum_mset 
    by (simp add:image_mset.compositionality comp_def)
  also have "... = 
    (\<Sum>e\<in>#{#e \<in># edges G. \<rho> (fst e) < \<rho> (snd e)#}. \<bar>(f' (fst e))\<^sup>2 - (f' (snd e))\<^sup>2\<bar>) +
    (\<Sum>e\<in>#{#e \<in># edges G. \<rho> (snd e) < \<rho> (fst e)#}. \<bar>(f' (fst e))\<^sup>2 - (f' (snd e))\<^sup>2\<bar>) +
    (\<Sum>e\<in>#{#e \<in># edges G. fst e = snd e#}. \<bar>(f' (fst e))\<^sup>2 - (f' (snd e))\<^sup>2\<bar>)"
    by (subst edges_split) simp
  also have "... =
    (\<Sum>e\<in>#{#e \<in># edges G. \<rho> (snd e) < \<rho> (fst e)#}. \<bar>(f' (fst e))\<^sup>2 - (f' (snd e))\<^sup>2\<bar>) +
    (\<Sum>e\<in>#{#e \<in># edges G. \<rho> (snd e) < \<rho> (fst e)#}. \<bar>(f' (snd e))\<^sup>2 - (f' (fst e))\<^sup>2\<bar>) +
    (\<Sum>e\<in>#{#e \<in># edges G. fst e = snd e#}. \<bar>(f' (fst e))\<^sup>2 - (f' (snd e))\<^sup>2\<bar>)"
    by (subst edges_sym[OF sym, symmetric]) (simp add:image_mset.compositionality 
        comp_def image_mset_filter_mset_swap[symmetric] case_prod_beta)
  also have "... = 
    (\<Sum>e\<in>#{#e \<in># edges G. \<rho> (snd e) < \<rho> (fst e)#}. \<bar>(f' (snd e))\<^sup>2 - (f' (fst e))\<^sup>2\<bar>) +
    (\<Sum>e\<in>#{#e \<in># edges G. \<rho> (snd e) < \<rho> (fst e)#}. \<bar>(f' (snd e))\<^sup>2 - (f' (fst e))\<^sup>2\<bar>) +
    (\<Sum>e\<in>#{#e \<in># edges G. fst e = snd e#}. 0)"
    by (intro_cong "[\<sigma>\<^sub>2 (+), \<sigma>\<^sub>1 sum_mset]" more:image_mset_cong) auto
  also have "... = 2 * (\<Sum>e\<in>#{#e\<in>#edges G. \<rho>(snd e)<\<rho>(fst e)#}. \<bar>(f' (snd e))\<^sup>2 - (f' (fst e))\<^sup>2\<bar>)"
    by simp
  also have "... = 2 *(\<Sum>a|a\<in>arcs G\<and>\<rho>(tail G a)>\<rho>(head G a). \<bar>f'(head G a)^2 - f'(tail G a)^2\<bar>)"
    unfolding edges_def arc_to_ends_def sum_unfold_sum_mset 
    by (simp add:image_mset.compositionality comp_def image_mset_filter_mset_swap[symmetric])
  also have "... = 2 *
    (\<Sum>a|a\<in>arcs G\<and>\<rho>(tail G a)>\<rho>(head G a). \<bar>\<tau>(\<rho>(head G a))^2 - \<tau>(\<rho>(tail G a))^2\<bar>)"
    unfolding \<tau>_def using \<phi>_\<rho>_inv \<rho>_lt_n
    by (intro arg_cong2[where f="(*)"] sum.cong refl) auto
  also have "... = 2 * (\<Sum>a|a\<in>arcs G\<and>\<rho>(tail G a)>\<rho>(head G a). \<tau>(\<rho>(head G a))^2 - \<tau>(\<rho>(tail G a))^2)"
    using \<tau>_antimono power_mono \<tau>_nonneg
    by (intro arg_cong2[where f="(*)"] sum.cong refl abs_of_nonneg)(auto)
  also have "... = 2 *
    (\<Sum>a|a\<in>arcs G\<and>\<rho>(tail G a)>\<rho>(head G a). (-(\<tau>(\<rho>(tail G a))^2)) - (-(\<tau>(\<rho>(head G a))^2)))"
    by (simp add:algebra_simps)
  also have "... = 2 *(\<Sum>a|a\<in>arcs G\<and>\<rho>(tail G a)>\<rho>(head G a). 
    (\<Sum>i=\<rho>(head G a)..<\<rho>(tail G a). (-(\<tau> (Suc i)^2)) - (-(\<tau> i^2))))"
    by (intro arg_cong2[where f="(*)"] sum.cong refl sum_Suc_diff'[symmetric]) auto
  also have "...=2*(\<Sum>(a, i)\<in>(SIGMA x:{a \<in> arcs G. \<rho> (head G a) < \<rho> (tail G a)}. 
    {\<rho> (head G x)..<\<rho> (tail G x)}).  \<tau> i^2 - \<tau> (Suc i)^2)" 
    by (subst sum.Sigma) auto
  also have "...=2*(\<Sum>p\<in>{(a,i).a \<in> arcs G\<and>\<rho>(head G a)\<le>i\<and>i<\<rho>(tail G a)}. \<tau>(snd p)^2-\<tau> (snd p+1)^2)" 
    by (intro arg_cong2[where f="(*)"] sum.cong refl) (auto simp add:Sigma_def)
  also have "...=2*(\<Sum>p\<in>{(i,a).a \<in> arcs G\<and>\<rho>(head G a) \<le> i\<and>i < \<rho>(tail G a)}. \<tau>(fst p)^2-\<tau>(fst p+1)^2)" 
    by (intro sum.reindex_cong[where l="prod.swap"] arg_cong2[where f="(*)"]) auto
  also have "...=2*
    (\<Sum>(i, a)\<in>(SIGMA x:{..<n}. {a \<in> arcs G. \<rho> (head G a)\<le>x \<and> x<\<rho>(tail G a)}). \<tau> i^2-\<tau> (i+1)^2)" 
    using less_trans[OF _ \<rho>_lt_n] by (intro sum.cong arg_cong2[where f="(*)"]) auto 
  also have "...=2*(\<Sum>i<n. (\<Sum>a|a\<in>arcs G \<and>\<rho>(head G a) \<le> i\<and>i < \<rho>(tail G a). \<tau> i^2 - \<tau> (i+1)^2))" 
    by (subst sum.Sigma) auto
  also have "...=2*(\<Sum>i<n. card {a\<in>arcs G. \<rho>(head G a)\<le>i\<and>i<\<rho>(tail G a)} * (\<tau> i^2 - \<tau> (i+1)^2))"
    by simp
  also have "...=2*(\<Sum>i<n. card {a\<in>arcs G. \<rho>(head G a)\<le>i\<and>\<not>(\<rho>(tail G a)\<le>i)} * (\<tau> i^2 - \<tau> (i+1)^2))"
    by (intro_cong "[\<sigma>\<^sub>2 (*), \<sigma>\<^sub>1 card, \<sigma>\<^sub>1 of_nat]" more:sum.cong Collect_cong) auto
  also have "...=2*(\<Sum>i<n. card {a\<in>arcs G. head G a\<in>\<phi>`{..i}\<and>tail G a\<notin>\<phi>`{..i}} * (\<tau> i^2-\<tau> (i+1)^2))"
    using 4 
    by (intro_cong "[\<sigma>\<^sub>2 (*), \<sigma>\<^sub>1 card, \<sigma>\<^sub>1 of_nat, \<sigma>\<^sub>2 (\<and>)]" more:sum.cong restr_Collect_cong) auto
  also have "... = 2 * (\<Sum>i<n. real (card (edges_betw (-\<phi>`{..i}) (\<phi>`{..i}))) * (\<tau> i^2-\<tau> (i+1)^2))"
    unfolding edges_betw_def by (auto simp:conj.commute)
  also have "... = 2 * (\<Sum>i<n. real (card (edges_betw (\<phi>`{..i}) (-\<phi>`{..i}))) * (\<tau> i^2-\<tau> (i+1)^2))"
    using edges_betw_sym by simp
  also have "... = 2 * (\<Sum>i<m. real (card (edges_betw (\<phi>`{..i}) (-\<phi>`{..i}))) * (\<tau> i^2-\<tau> (i+1)^2))"
    using \<tau>_supp m_le_n by (intro sum.mono_neutral_right arg_cong2[where f="(*)"]) auto
  finally have Bf_eq: 
    "B\<^sub>f = 2 * (\<Sum>i<m. real (card (edges_betw (\<phi>`{..i}) (-\<phi>`{..i}))) * (\<tau> i^2-\<tau> (i+1)^2))"
    by simp

  have 3:"card (\<phi> ` {..i} \<inter> verts G) = i + 1" if "i < m" for i 
  proof -
    have "card (\<phi> ` {..i} \<inter> verts G) = card (\<phi> ` {..i})"
      using m_le_n that by (intro arg_cong[where f="card"] Int_absorb2 
          image_subsetI bij_betw_apply[OF \<phi>_bij]) auto
    also have "... = card {..i}"
      using m_le_n that by (intro card_image 
          inj_on_subset[OF bij_betw_imp_inj_on[OF \<phi>_bij]]) auto
    also have "... = i+1" by simp
    finally show ?thesis
      by simp
  qed

  have "2 * \<Lambda>\<^sub>e * norm f^2 =  2 * \<Lambda>\<^sub>e * (g_norm f'^2)"
    unfolding g_norm_conv f'_alt by simp
  also have "... \<le> 2 * \<Lambda>\<^sub>e * (\<Sum>v\<in> verts G. f' v^2)"
    unfolding g_norm_sq g_inner_def by (simp add:power2_eq_square)
  also have "... = 2 * \<Lambda>\<^sub>e * (\<Sum>i<n. f' (\<phi> i)^2)"
    by (intro arg_cong2[where f="(*)"] refl sum.reindex_bij_betw[symmetric] \<phi>_bij)
  also have "... = 2 * \<Lambda>\<^sub>e * (\<Sum>i<n. \<tau> i^2)"
    unfolding \<tau>_def by (intro arg_cong2[where f="(*)"] refl sum.cong) auto
  also have "... = 2 * \<Lambda>\<^sub>e * (\<Sum>i<m. \<tau> i^2)"
    using \<tau>_supp m_le_n by (intro sum.mono_neutral_cong_right arg_cong2[where f="(*)"] refl) auto
  also have "... \<le> 2 * \<Lambda>\<^sub>e * ((\<Sum>i<m. \<tau> i^2) + (real 0 * \<tau> 0^2 - m * \<tau> m^2))"
    using \<tau>_supp[of "m"] by simp
  also have "... \<le> 2 * \<Lambda>\<^sub>e * ((\<Sum>i<m. \<tau> i^2) + (\<Sum>i<m. i*\<tau> i^2-(Suc i)*\<tau> (Suc i)^2))"
    by (subst sum_lessThan_telescope'[symmetric]) simp
  also have "... \<le> 2 * (\<Sum>i<m. (\<Lambda>\<^sub>e * (i+1)) * (\<tau> i^2-\<tau> (i+1)^2))"
    by (simp add:sum_distrib_left algebra_simps sum.distrib[symmetric])
  also have "... \<le> 2 * (\<Sum>i<m. real (card (edges_betw (\<phi>`{..i}) (-\<phi>`{..i}))) * (\<tau> i^2-\<tau> (i+1)^2))"
    using \<tau>_nonneg \<tau>_antimono power_mono 3 m2_le_n
    by (intro mult_left_mono sum_mono mult_right_mono edge_expansionD2) auto
  also have "... = B\<^sub>f"
    unfolding Bf_eq by simp
  finally have hoory_4_13: "2 * \<Lambda>\<^sub>e * norm f^2 \<le> B\<^sub>f"
    by simp
  text \<open>Corresponds to Lemma 4.13 in Hoory et al.\<close>

  have f_nz: "f \<noteq> 0" 
  proof (rule ccontr)
    assume f_nz_assms: "\<not> (f \<noteq> 0)" 
    have "g $h i \<le> 0" for i
    proof -
      have "g $h i \<le> max (g $h i) 0" 
        by simp
      also have "... = 0"
        using f_nz_assms unfolding f_def vec_eq_iff by auto
      finally show ?thesis by simp
    qed
    moreover have "(\<Sum>i \<in> UNIV. 0-g $h i) = 0"
      using g_orth unfolding sum_subtractf inner_vec_def by auto
    ultimately have "\<forall>x\<in>UNIV. -(g $h x) = 0"
      by (intro iffD1[OF sum_nonneg_eq_0_iff]) auto
    thus "False"
      using g_nz unfolding vec_eq_iff by simp
  qed
  hence norm_f_gt_0: "norm f> 0"
    by simp

  have "\<Lambda>\<^sub>e * norm f * norm f \<le> sqrt 2 * real d * norm f * sqrt (f \<bullet> (L *v f))"
    using order_trans[OF hoory_4_13 hoory_4_12] by (simp add:power2_eq_square)
  hence "\<Lambda>\<^sub>e \<le> real d * sqrt 2 * sqrt (f \<bullet> (L *v f)) / norm f"
    using norm_f_gt_0 by (simp add:ac_simps divide_simps)
  also have "... \<le> real d * sqrt 2 * sqrt ((1 - \<Lambda>\<^sub>2) * (norm f)\<^sup>2) / norm f"
    by (intro mult_left_mono divide_right_mono real_sqrt_le_mono h_part_i) auto
  also have "... = real d * sqrt 2 * sqrt (1- \<Lambda>\<^sub>2)"
    using f_nz by (simp add:real_sqrt_mult)
  also have "... = d * sqrt (2 * (1-\<Lambda>\<^sub>2))"
    by (simp add:real_sqrt_mult[symmetric])
  finally show ?thesis
    by simp
qed

end

context regular_graph
begin 

lemmas (in regular_graph) cheeger_aux_1 =  
  regular_graph_tts.cheeger_aux_1[OF eg_tts_1,
    internalize_sort "'n :: finite", OF _ regular_graph_axioms, 
    unfolded remove_finite_premise, cancel_type_definition, OF verts_non_empty]

theorem cheeger_inequality:
  assumes "n > 1"
  shows "\<Lambda>\<^sub>e \<in> {d * (1 - \<Lambda>\<^sub>2) / 2.. d * sqrt (2 * (1 - \<Lambda>\<^sub>2))}"
  using cheeger_aux_1 cheeger_aux_2 assms by auto

unbundle no_intro_cong_syntax

end

end