section \<open>Random Walks\label{sec:random_walks}\<close>

theory Expander_Graphs_Walks
  imports
    Expander_Graphs_Algebra
    Expander_Graphs_Eigenvalues
    Expander_Graphs_TTS
    Constructive_Chernoff_Bound
begin                           

unbundle intro_cong_syntax

no_notation Matrix.vec_index (infixl "$" 100)
hide_const Matrix.vec_index
hide_const Matrix.vec
no_notation Matrix.scalar_prod  (infix "\<bullet>" 70)

fun walks' :: "('a,'b) pre_digraph \<Rightarrow> nat \<Rightarrow> ('a list) multiset"
  where 
    "walks' G 0 = image_mset (\<lambda>x. [x]) (mset_set (verts G))" |
    "walks' G (Suc n) = 
      concat_mset {#{#w @[z].z\<in># vertices_from G (last w)#}. w \<in># walks' G n#}" 

definition "walks G l = (case l of 0 \<Rightarrow> {#[]#} | Suc pl \<Rightarrow> walks' G pl)"

lemma Union_image_mono: "(\<And>x. x \<in> A \<Longrightarrow> f x \<subseteq> g x) \<Longrightarrow> \<Union> (f ` A) \<subseteq> \<Union> (g ` A)"
  by auto

context fin_digraph
begin

lemma count_walks':
  assumes "set xs \<subseteq> verts G"
  assumes "length xs = l+1"
  shows "count (walks' G l) xs = (\<Prod>i \<in> {..<l}. count (edges G) (xs ! i, xs ! (i+1)))"
proof -
  have a:"xs \<noteq> []" using assms(2) by auto

  have "count (walks' G (length xs-1)) xs = (\<Prod>i<length xs -1. count (edges G) (xs ! i, xs ! (i + 1)))"
    using a assms(1)
  proof (induction xs rule:rev_nonempty_induct)
    case (single x)
    hence "x \<in> verts G" by simp
    hence "count {#[x]. x \<in># mset_set (verts G)#} [x] = 1" 
      by (subst count_image_mset_inj, auto simp add:inj_def) 
    then show ?case by simp 
  next
    case (snoc x xs)
    have set_xs: "set xs \<subseteq> verts G" using snoc by simp

    define l where "l = length xs - 1" 
    have l_xs: "length xs = l + 1" unfolding l_def using snoc by simp
    have "count (walks' G (length (xs @ [x]) - 1)) (xs @ [x]) =
      (\<Sum>ys\<in>#walks' G l. count {#ys @ [z]. z \<in># vertices_from G (last ys)#} (xs @ [x]))"
      by (simp add:l_xs count_concat_mset image_mset.compositionality comp_def)
    also have "... = (\<Sum>ys\<in>#walks' G l. 
      (if ys = xs then count {#xs @ [z]. z \<in># vertices_from G (last xs)#} (xs @ [x]) else 0))"
      by (intro arg_cong[where f="sum_mset"] image_mset_cong) (auto intro!: count_image_mset_0_triv) 
    also have "... = (\<Sum>ys\<in>#walks' G l.(if ys=xs then count (vertices_from G (last xs)) x else 0))"
      by (subst count_image_mset_inj, auto simp add:inj_def)
    also have "... = count (walks' G l) xs * count (vertices_from G (last xs)) x"
      by (subst sum_mset_delta, simp)
    also have "... = count (walks' G l) xs * count (edges G) (last xs, x)"
      unfolding vertices_from_def count_mset_exp image_mset_filter_mset_swap[symmetric] 
        filter_filter_mset by (simp add:prod_eq_iff)
    also have "... = count (walks' G l) xs * count (edges G) ((xs@[x])!l, (xs@[x])!(l+1))"
      using snoc(1) unfolding l_def nth_append last_conv_nth[OF snoc(1)] by simp 
    also have "... = (\<Prod>i<l+1. count (edges G) ((xs@[x])!i, (xs@[x])!(i+1)))"
      unfolding l_def snoc(2)[OF set_xs] by (simp add:nth_append)
    finally have "count (walks' G (length (xs @ [x]) - 1)) (xs @ [x]) =
       (\<Prod>i<length (xs@[x]) - 1. count (edges G) ((xs@[x])!i, (xs@[x])!(i+1)))"
      unfolding l_def using snoc(1) by simp
    then show ?case by simp 
  qed
  moreover have "l = length xs - 1" using a assms by simp
  ultimately show ?thesis by simp
qed

lemma count_walks:
  assumes "set xs \<subseteq> verts G"
  assumes "length xs = l" "l > 0"
  shows "count (walks G l) xs = (\<Prod>i \<in> {..<l-1}. count (edges G)  (xs ! i, xs ! (i+1)))"
  using assms unfolding walks_def by (cases l, auto simp add:count_walks')

lemma set_walks':
  "set_mset (walks' G l) \<subseteq> {xs. set xs \<subseteq> verts G \<and> length xs = (l+1)}"
proof (induction l)
  case 0
  then show ?case by auto 
next
  case (Suc l)

  have "set_mset (walks' G (Suc l)) =
    (\<Union>x\<in>set_mset (walks' G l). (\<lambda>z. x @ [z]) ` set_mset (vertices_from G (last x)))"
    by (simp add:set_mset_concat_mset)
  also have "... \<subseteq> (\<Union>x\<in>{xs. set xs \<subseteq> verts G \<and> length xs = l + 1}. 
    (\<lambda>z. x @ [z]) ` set_mset (vertices_from G (last x)))"
    by (intro Union_mono image_mono Suc)
  also have "... \<subseteq> (\<Union>x\<in>{xs. set xs \<subseteq> verts G \<and> length xs = l + 1}. (\<lambda>z. x @ [z]) ` verts G)"
    by (intro Union_image_mono image_mono set_mset_vertices_from)
  also have "... \<subseteq> {xs. set xs \<subseteq> verts G \<and> length xs = (Suc l + 1)}"
    by (intro subsetI) auto
  finally show ?case by simp
qed

lemma set_walks:
  "set_mset (walks G l) \<subseteq> {xs. set xs \<subseteq> verts G \<and> length xs = l}"
  unfolding walks_def using set_walks' by (cases l, auto)

lemma set_walks_2:
  assumes  "xs \<in># walks' G l"
  shows "set xs \<subseteq> verts G" "xs \<noteq> []"
proof -
  have a:"xs \<in> set_mset (walks' G l)"
    using assms by simp
  thus "set xs \<subseteq> verts G"
    using set_walks' by auto
  have "length xs \<noteq> 0"
    using set_walks' a by fastforce
  thus "xs \<noteq> []" by simp
qed

lemma set_walks_3:
  assumes "xs \<in># walks G l"
  shows  "set xs \<subseteq> verts G" "length xs = l"
  using set_walks assms by auto
end

lemma measure_pmf_of_multiset:
  assumes "A \<noteq> {#}"
  shows "measure (pmf_of_multiset A) S = real (size (filter_mset (\<lambda>x. x \<in> S) A)) / size A" 
    (is "?L = ?R")
proof -
  have "sum (count A) (S \<inter> set_mset A) = size (filter_mset (\<lambda>x. x \<in> S \<inter> set_mset A) A)"
    by (intro sum_count_2) simp
  also have "... = size (filter_mset (\<lambda>x. x \<in> S) A)"
    by (intro arg_cong[where f="size"] filter_mset_cong) auto
  finally have a: "sum (count A) (S \<inter> set_mset A) = size (filter_mset (\<lambda>x. x \<in> S) A)" 
    by simp

  have "?L = measure (pmf_of_multiset A) (S \<inter> set_mset A)"
    using assms by (intro measure_eq_AE AE_pmfI) auto
  also have "... = sum (pmf (pmf_of_multiset A)) (S \<inter> set_mset A)"
    by (intro measure_measure_pmf_finite) simp
  also have "... = (\<Sum>x \<in> S \<inter> set_mset A. count A x / size A)"
    using assms by (intro sum.cong, auto)
  also have "... = (\<Sum>x \<in> S \<inter> set_mset A. count A x) / size A"
    by (simp add:sum_divide_distrib)
  also have "... = ?R" 
    using a by simp
  finally show ?thesis
    by simp
qed

lemma pmf_of_multiset_image_mset:
  assumes "A \<noteq> {#}"
  shows "pmf_of_multiset (image_mset f A) = map_pmf f (pmf_of_multiset A)"
  using assms by (intro pmf_eqI) (simp add:pmf_map measure_pmf_of_multiset count_mset_exp 
      image_mset_filter_mset_swap[symmetric])


context regular_graph 
begin

lemma size_walks':
  "size (walks' G l) = card (verts G) * d^l"
proof (induction l)
  case 0
  then show ?case by simp
next
  case (Suc l)
  have a:"out_degree G (last x) = d" if "x \<in># walks' G l" for x
  proof -
    have "last x \<in> verts G" 
      using set_walks_2 that by fastforce
    thus ?thesis
      using reg by simp
  qed

  have "size (walks' G (Suc l)) = (\<Sum>x\<in>#walks' G l. out_degree G (last x))"
    by (simp add:size_concat_mset image_mset.compositionality comp_def verts_from_alt out_degree_def)
  also have "... = (\<Sum>x\<in>#walks' G l. d)"
    by (intro arg_cong[where f="sum_mset"] image_mset_cong a) simp
  also have "... = size (walks' G l) * d" by simp
  also have "... = card (verts G) * d^(Suc l)" using Suc by simp
  finally show ?case by simp
qed

lemma size_walks:
  "size (walks G l) = (if l > 0 then n * d^(l-1) else 1)"
  using size_walks' unfolding walks_def n_def by (cases l, auto)

lemma walks_nonempty: 
  "walks G l \<noteq> {#}"
proof -
  have "size (walks G l) > 0"
    unfolding size_walks using d_gt_0 n_gt_0 by auto 
  thus "walks G l \<noteq> {#}"
    by auto
qed

end

context regular_graph_tts
begin

lemma g_step_remains_orth:
  assumes "g_inner f (\<lambda>_. 1) = 0"
  shows "g_inner (g_step f) (\<lambda>_. 1) = 0" (is "?L = ?R")
proof -
  have "?L = (A *v (\<chi> i. f (enum_verts i))) \<bullet> 1"
    unfolding g_inner_conv g_step_conv one_vec_def by simp
  also have "... = (\<chi> i. f (enum_verts i)) \<bullet> 1"
    by (intro markov_orth_inv markov)
  also have "... = g_inner f (\<lambda>_. 1)"
    unfolding g_inner_conv one_vec_def by simp
  also have "... = 0" using assms by simp
  finally show ?thesis by simp
qed

lemma spec_bound:
  "spec_bound A \<Lambda>\<^sub>a"
proof -
  have "norm (A *v v) \<le> \<Lambda>\<^sub>a * norm v" if "v \<bullet> 1 = (0::real)" for v::"real^'n"
    unfolding \<Lambda>\<^sub>e_eq_\<Lambda>
    by (intro \<gamma>\<^sub>a_real_bound that)
  thus ?thesis
    unfolding spec_bound_def using \<Lambda>_ge_0 by auto
qed

text \<open>A spectral expansion rule that does not require orthogonality of the vector for the stationary 
distribution:\<close>

lemma expansionD3:
  "\<bar>g_inner f (g_step f)\<bar> \<le> \<Lambda>\<^sub>a * g_norm f^2 + (1-\<Lambda>\<^sub>a) * g_inner f (\<lambda>_. 1)^2 / n" (is "?L \<le> ?R")
proof -
  define v where "v = (\<chi> i. f (enum_verts i))"
  define v1 :: "real^ 'n" where "v1 = ((v \<bullet> 1) / n) *\<^sub>R 1"
  define v2 :: "real^ 'n" where "v2 = v - v1"
  have v_eq: "v = v1 + v2"
    unfolding v2_def by simp

  have 0: "A *v v1 = v1" 
    unfolding v1_def using markov_apply[OF markov] 
    by (simp add:algebra_simps)
  have 1: "v1 v* A = v1" 
    unfolding v1_def using markov_apply[OF markov] 
    by (simp add:algebra_simps scaleR_vector_matrix_assoc)

  have "v2 \<bullet> 1 = v \<bullet> 1 - v1 \<bullet> 1"
    unfolding v2_def by (simp add:algebra_simps)
  also have "... = v \<bullet> 1  - v \<bullet> 1 * real CARD('n) / real n"
    unfolding v1_def by (simp add:inner_1_1)
  also have "... = 0 "
    using verts_non_empty unfolding card n_def by simp
  finally have 4:"v2 \<bullet> 1 = 0" by simp
  hence 2: "v1 \<bullet> v2 = 0"
    unfolding v1_def by (simp add:inner_commute)

  define f2 where "f2 i = v2 $ (enum_verts_inv i)" for i
  have f2_def: "v2 = (\<chi> i. f2 (enum_verts i))"
    unfolding f2_def Rep_inverse by simp

  have 6: "g_inner f2 (\<lambda>_. 1) = 0"
    unfolding g_inner_conv f2_def[symmetric] one_vec_def[symmetric] 4 by simp

  have "\<bar>v2 \<bullet> (A *v v2)\<bar> = \<bar>g_inner f2 (g_step f2)\<bar>"
    unfolding f2_def g_inner_conv g_step_conv by simp
  also have "... \<le> \<Lambda>\<^sub>a * (g_norm f2)\<^sup>2"
    by (intro expansionD1 6) 
  also have "... = \<Lambda>\<^sub>a * (norm v2)^2"
    unfolding g_norm_conv f2_def by simp
  finally have 5:"\<bar>v2 \<bullet> (A *v v2)\<bar> \<le> \<Lambda>\<^sub>a * (norm v2)\<^sup>2" by simp

  have 3: "norm (1 :: real^'n)^2 = n"
    unfolding power2_norm_eq_inner inner_1_1 card n_def by presburger 

  have "?L = \<bar>v \<bullet> (A *v v)\<bar>"
    unfolding g_inner_conv g_step_conv v_def by simp
  also have "... = \<bar>v1 \<bullet> (A *v v1) + v2 \<bullet> (A *v v1) + v1 \<bullet> (A *v v2) + v2 \<bullet> (A *v v2)\<bar>"
    unfolding v_eq by (simp add:algebra_simps)
  also have "... = \<bar>v1 \<bullet> v1 + v2 \<bullet> v1 + v1 \<bullet> v2 + v2 \<bullet> (A *v v2)\<bar>"
    unfolding dot_lmul_matrix[where x="v1",symmetric] 0 1 by simp
  also have "... = \<bar>v1 \<bullet> v1 + v2 \<bullet> (A *v v2)\<bar>"
    using 2 by (simp add:inner_commute)
  also have "... \<le> \<bar>norm v1^2\<bar> + \<bar>v2 \<bullet> (A *v v2)\<bar>"
    unfolding power2_norm_eq_inner by (intro abs_triangle_ineq)
  also have "... \<le> norm v1^2 + \<Lambda>\<^sub>a * norm v2^2"
    by (intro add_mono 5) auto
  also have "... = \<Lambda>\<^sub>a * (norm v1^2 + norm v2^2) + (1 - \<Lambda>\<^sub>a) * norm v1^2"
    by (simp add:algebra_simps)
  also have "... = \<Lambda>\<^sub>a * norm v^2 + (1 - \<Lambda>\<^sub>a) * norm v1^2"
    unfolding v_eq pythagoras[OF 2] by simp
  also have "... = \<Lambda>\<^sub>a * norm v^2 + ((1 - \<Lambda>\<^sub>a)) * ((v \<bullet> 1)^2*n)/n^2"
    unfolding v1_def by (simp add:power_divide power_mult_distrib 3)
  also have "... = \<Lambda>\<^sub>a * norm v^2 + ((1 - \<Lambda>\<^sub>a)/n) * (v \<bullet> 1)^2"
    by (simp add:power2_eq_square)
  also have "... = ?R"
    unfolding g_norm_conv g_inner_conv v_def one_vec_def by (simp add:field_simps)
  finally show ?thesis by simp
qed

definition ind_mat where "ind_mat S = diag (ind_vec (enum_verts -` S))"

lemma walk_distr:
  "measure (pmf_of_multiset (walks G l)) {\<omega>. (\<forall>i<l. \<omega> ! i \<in> S i)} =
  foldl (\<lambda>x M. M *v x) stat (intersperse A (map (\<lambda>i. ind_mat (S i)) [0..<l]))\<bullet>1" 
  (is "?L = ?R")
proof (cases "l > 0")
  case True
  let ?n = "real n"
  let ?d = "real d"
  let ?W = "{(w::'a list). set w \<subseteq> verts G \<and> length w = l}"
  let ?V = "{(w::'n list). length w = l}"

  have a: "set_mset (walks G l) \<subseteq> ?W"
    using set_walks by auto
  have b: "finite ?W"
    by (intro finite_lists_length_eq) auto

  define lp where "lp = l - 1"

  define xs where "xs = map (\<lambda>i. ind_mat (S i)) [0..<l]"
  have "xs \<noteq> []" unfolding xs_def using True by simp
  then obtain xh xt where xh_xt: "xh#xt=xs" by (cases xs, auto)

  have "length xs = l"
    unfolding xs_def by simp
  hence len_xt: "length xt = lp" 
    using True unfolding xh_xt[symmetric] lp_def by simp

  have "xh = xs ! 0" 
    unfolding xh_xt[symmetric] by simp
  also have "... = ind_mat (S 0)"
    using True unfolding xs_def by simp
  finally have xh_eq: "xh = ind_mat (S 0)" 
    by simp

  have inj_map_enum_verts: "inj_on (map enum_verts) ?V"
    using bij_betw_imp_inj_on[OF enum_verts] inj_on_subset
    by (intro inj_on_mapI) auto

  have "card ?W = card (verts G)^l"
    by (intro card_lists_length_eq) simp
  also have "... = card {w. set w \<subseteq> (UNIV :: 'n set) \<and> length w  = l}"
    unfolding card[symmetric] by (intro card_lists_length_eq[symmetric]) simp
  also have "... = card ?V"
    by (intro arg_cong[where f="card"]) auto
  also have "... = card (map enum_verts ` ?V)"
    by (intro card_image[symmetric] inj_map_enum_verts)
  finally have "card ?W = card (map enum_verts ` ?V)"
    by simp
  hence "map enum_verts ` ?V = ?W"
    using bij_betw_apply[OF enum_verts]
    by (intro card_subset_eq b image_subsetI) auto

  hence bij_map_enum_verts: "bij_betw (map enum_verts) ?V ?W"
    using inj_map_enum_verts unfolding bij_betw_def by auto

  have "?L = size {# w \<in># walks G l. \<forall>i<l. w ! i \<in> S i #} / (?n * ?d^(l-1))"
    using True unfolding size_walks measure_pmf_of_multiset[OF walks_nonempty] by simp
  also have "... = (\<Sum>w\<in>?W. real (count (walks G l) w) * of_bool (\<forall>i<l. w!i \<in> S i))/(?n*?d^(l-1))"
    unfolding size_filter_mset_conv sum_mset_conv_2[OF a b] by simp
  also have "... = (\<Sum>w\<in>?W. (\<Prod>i<l-1. real (count (edges G) (w!i,w!(i+1)))) * 
                            (\<Prod>i<l. of_bool (w!i \<in> S i)))/(?n*?d^(l-1))"
    using True by (intro sum.cong arg_cong2[where f="(/)"]) (auto simp add: count_walks)
  also have "... = 
    (\<Sum>w\<in>?W. (\<Prod>i<l-1. real (count (edges G) (w!i,w!(i+1)))/?d)*(\<Prod>i<l. of_bool (w!i \<in> S i)))/?n"
    using True unfolding prod_dividef by (simp add:sum_divide_distrib algebra_simps)
  also have "... = 
    (\<Sum>w\<in>?V. (\<Prod>i<l-1. count (edges G) (map enum_verts w!i,map enum_verts w!(i+1)) / ?d) * 
    (\<Prod>i<l. of_bool (map enum_verts w!i \<in> S i)))/?n"
    by (intro sum.reindex_bij_betw[symmetric] arg_cong2[where f="(/)"] refl bij_map_enum_verts)
  also have "... = 
    (\<Sum>w\<in>?V. (\<Prod>i<lp. A $ w!(i+1) $ w!i) * (\<Prod>i<Suc lp. of_bool(enum_verts (w!i) \<in> S i)))/?n"
    unfolding A_def lp_def using True by simp
  also have "... = (\<Sum>w\<in>?V. (\<Prod>i<lp. A $ w!(i+1) $ w!i) * 
    (\<Prod>i\<in>insert 0 (Suc ` {..<lp}). of_bool(enum_verts (w!i) \<in> S i)))/?n"
    using lessThan_Suc_eq_insert_0
    by (intro sum.cong arg_cong2[where f="(/)"] arg_cong2[where f="(*)"] prod.cong) auto
  also have "... = (\<Sum>w\<in>?V. (\<Prod>i<lp. of_bool(enum_verts (w!(i+1))\<in>S(i+1))* A$ w!(i+1) $ w!i) 
    * of_bool(enum_verts(w!0)\<in>S 0))/?n"
    by (simp add:prod.reindex algebra_simps prod.distrib)
  also have "... = 
    (\<Sum>w\<in>?V. (\<Prod>i<lp. (ind_mat (S (i+1))**A) $ w!(i+1) $ w!i) * of_bool(enum_verts (w!0)\<in>S 0))/?n"
    unfolding diag_def ind_vec_def matrix_matrix_mult_def ind_mat_def
    by (intro sum.cong arg_cong2[where f="(/)"] arg_cong2[where f="(*)"] prod.cong refl) 
      (simp add:if_distrib if_distribR sum.If_cases)
  also have "... = 
    (\<Sum>w\<in>?V. (\<Prod>i<lp. (xs!(i+1)**A) $ w!(i+1) $ w!i) * of_bool(enum_verts (w!0)\<in>S 0))/?n"
    unfolding xs_def lp_def True
    by (intro sum.cong arg_cong2[where f="(/)"] arg_cong2[where f="(*)"] prod.cong refl) auto 
  also have "... = 
    (\<Sum>w\<in>?V. (\<Prod>i<lp. (xt ! i ** A) $ w!(i+1) $ w!i) * of_bool(enum_verts (w!0)\<in>S 0))/?n"
    unfolding xh_xt[symmetric] by auto
  also have "... = (\<Sum>w\<in>?V. (\<Prod>i<lp. (xt!i**A)$ w!(i+1) $ w!i)*(ind_mat(S 0)*v stat) $w!0)"
    using n_def unfolding matrix_vector_mult_def diag_def stat_def ind_vec_def ind_mat_def card
    by (simp add:sum.If_cases if_distrib if_distribR sum_divide_distrib)
  also have "... = (\<Sum>w\<in>?V. (\<Prod>i<lp. (xt ! i ** A) $ w!(i+1) $ w!i) * (xh *v stat) $ w ! 0)"
    unfolding xh_eq by simp
  also have "... = foldl (\<lambda>x M. M *v x) (xh *v stat) (map (\<lambda>x. x ** A) xt) \<bullet> 1" 
    using True unfolding foldl_matrix_mult_expand_2 by (simp add:len_xt lp_def)
  also have "... = foldl (\<lambda>x M. M *v (A *v x)) (xh *v stat) xt \<bullet> 1" 
    by (simp add: matrix_vector_mul_assoc foldl_map)
  also have "... = foldl (\<lambda>x M. M *v x) stat (intersperse A (xh#xt)) \<bullet> 1" 
    by (subst foldl_intersperse_2, simp)
  also have "... = ?R"  unfolding xh_xt xs_def by simp
  finally show ?thesis by simp
next
  case False
  hence "l = 0" by simp
  thus ?thesis unfolding stat_def by (simp add: inner_1_1)
qed

lemma hitting_property:
  assumes "S \<subseteq> verts G" 
  assumes "I \<subseteq> {..<l}"
  defines "\<mu> \<equiv> real (card S) / card (verts G)"
  shows "measure (pmf_of_multiset (walks G l)) {w. set (nths w I) \<subseteq> S} \<le> (\<mu>+\<Lambda>\<^sub>a*(1-\<mu>))^card I" 
    (is "?L \<le> ?R")
proof -
  define T where "T = (\<lambda>i. if i \<in> I then S else UNIV)" 

  have 0: "ind_mat UNIV = mat 1"
    unfolding ind_mat_def diag_def ind_vec_def Finite_Cartesian_Product.mat_def by vector

  have \<Lambda>_range: "\<Lambda>\<^sub>a \<in> {0..1}"
    using \<Lambda>_ge_0 \<Lambda>_le_1 by simp

  have "S \<subseteq> range enum_verts" 
    using assms(1) enum_verts unfolding bij_betw_def by simp
  moreover have "inj enum_verts" 
    using bij_betw_imp_inj_on[OF enum_verts] by simp
  ultimately have \<mu>_alt: "\<mu> = real (card (enum_verts -` S)) / CARD ('n)"
    unfolding \<mu>_def card by (subst card_vimage_inj) auto

  have "?L = measure (pmf_of_multiset (walks G l)) {w. \<forall>i<l. w ! i \<in> T i}"
    using walks_nonempty set_walks_3 unfolding T_def set_nths
    by (intro measure_eq_AE AE_pmfI) auto
  also have "... = foldl (\<lambda>x M. M *v x) stat 
    (intersperse A (map (\<lambda>i. (if i \<in> I then ind_mat S else mat 1)) [0..<l])) \<bullet> 1"
    unfolding walk_distr T_def by (simp add:if_distrib if_distribR 0 cong:if_cong)
  also have "... \<le> ?R"
    unfolding \<mu>_alt ind_mat_def
    by (intro hitting_property_alg_2[OF \<Lambda>_range assms(2) spec_bound markov])
  finally show ?thesis by simp
qed

lemma uniform_property:
  assumes  "i < l" "x \<in> verts G"
  shows "measure (pmf_of_multiset (walks G l)) {w. w ! i = x} = 1/real (card (verts G))" 
    (is "?L = ?R")
proof -
  obtain xi where xi_def: "enum_verts xi = x" 
    using assms(2) bij_betw_imp_surj_on[OF enum_verts] by force

  define T where "T = (\<lambda>j. if j = i then {x} else UNIV)"

  have "diag (ind_vec UNIV) = mat 1"
    unfolding diag_def ind_vec_def Finite_Cartesian_Product.mat_def by vector
  moreover have "enum_verts -` {x} = {xi}"
    using bij_betw_imp_inj_on[OF enum_verts]
    unfolding vimage_def xi_def[symmetric] by (auto simp add:inj_on_def)
  ultimately have 0: "ind_mat (T j) = (if j = i then diag (ind_vec {xi}) else mat 1)" for j
    unfolding T_def ind_mat_def by (cases "j = i", auto)

  have "?L = measure (pmf_of_multiset (walks G l)) {w. \<forall>j < l. w ! j \<in> T j}"
    unfolding T_def using assms(1) by simp
  also have "... = foldl (\<lambda>x M. M *v x) stat (intersperse A (map (\<lambda>j. ind_mat (T j)) [0..<l])) \<bullet> 1"
    unfolding walk_distr by simp
  also have "... = 1/CARD('n)"
    unfolding 0 uniform_property_alg[OF assms(1) markov] by simp
  also have "... = ?R" 
    unfolding card by simp
  finally show ?thesis  by simp
qed

end

context regular_graph
begin

lemmas expansionD3 =  
  regular_graph_tts.expansionD3[OF eg_tts_1,
    internalize_sort "'n :: finite", OF _ regular_graph_axioms, 
    unfolded remove_finite_premise, cancel_type_definition, OF verts_non_empty]

lemmas g_step_remains_orth =  
  regular_graph_tts.g_step_remains_orth[OF eg_tts_1,
    internalize_sort "'n :: finite", OF _ regular_graph_axioms, 
    unfolded remove_finite_premise, cancel_type_definition, OF verts_non_empty]

lemmas hitting_property =  
  regular_graph_tts.hitting_property[OF eg_tts_1,
    internalize_sort "'n :: finite", OF _ regular_graph_axioms, 
    unfolded remove_finite_premise, cancel_type_definition, OF verts_non_empty]

lemmas uniform_property_2 =  
  regular_graph_tts.uniform_property[OF eg_tts_1,
    internalize_sort "'n :: finite", OF _ regular_graph_axioms, 
    unfolded remove_finite_premise, cancel_type_definition, OF verts_non_empty]

theorem uniform_property:
  assumes "i < l"
  shows "map_pmf (\<lambda>w. w ! i) (pmf_of_multiset (walks G l)) = pmf_of_set (verts G)" (is "?L = ?R")
proof (rule pmf_eqI)
  fix x :: "'a"
  have a:"measure (pmf_of_multiset (walks G l)) {w. w ! i = x} = 0" (is "?L1 = ?R1")
    if "x \<notin> verts G"
  proof -
    have "?L1 \<le> measure (pmf_of_multiset (walks G l)) {w. set w \<subseteq> verts G \<and> x \<in> set w}"
      using walks_nonempty set_walks_3 assms(1)
      by (intro measure_pmf.pmf_mono[OF refl]) auto
    also have "... \<le> measure (pmf_of_multiset (walks G l)) {}"
      using that by (intro measure_pmf.pmf_mono[OF refl]) auto
    also have "... = 0" by simp
    finally have "?L1 \<le> 0" by simp
    thus ?thesis using measure_le_0_iff by blast
  qed

  have "pmf ?L x = measure (pmf_of_multiset (walks G l)) {w. w ! i = x}"
    unfolding pmf_map by (simp add:vimage_def)
  also have "... = indicator (verts G) x/real (card (verts G))"
    using uniform_property_2[OF assms(1)] a
    by (cases "x \<in> verts G", auto)
  also have "... = pmf ?R x"
    using verts_non_empty by (intro pmf_of_set[symmetric]) auto 
  finally show "pmf ?L x = pmf ?R x" by simp
qed

lemma uniform_property_gen:
  fixes S :: "'a set"
  assumes "S \<subseteq> verts G" "i < l"
  defines "\<mu> \<equiv> real (card S) / card (verts G)"
  shows "measure (pmf_of_multiset (walks G l)) {w. w ! i \<in> S} = \<mu>" (is "?L = ?R")
proof -

  have "?L = measure (map_pmf (\<lambda>w. w ! i) (pmf_of_multiset (walks G l))) S"
    unfolding measure_map_pmf by (simp add:vimage_def)
  also have "... = measure (pmf_of_set (verts G)) S"
    unfolding uniform_property[OF assms(2)] by simp
  also have "... = ?R"
    using verts_non_empty Int_absorb1[OF assms(1)] 
    unfolding \<mu>_def by (subst measure_pmf_of_set) auto 
  finally show ?thesis by simp
qed

theorem kl_chernoff_property:
  assumes "l > 0"
  assumes "S \<subseteq> verts G"
  defines "\<mu> \<equiv> real (card S) / card (verts G)"
  assumes "\<gamma> \<le> 1" "\<mu> + \<Lambda>\<^sub>a * (1-\<mu>) \<in> {0<..\<gamma>}"
  shows "measure (pmf_of_multiset (walks G l)) {w. real (card {i \<in> {..<l}. w ! i \<in> S}) \<ge> \<gamma>*l} 
    \<le> exp (- real l * KL_div \<gamma> (\<mu>+\<Lambda>\<^sub>a*(1-\<mu>)))" (is "?L \<le> ?R")
proof -
  let ?\<delta> = "(\<Sum>i<l. \<mu>+\<Lambda>\<^sub>a*(1-\<mu>))/l"

  have a: "measure (pmf_of_multiset (walks G l)) {w. \<forall>i\<in>T. w ! i \<in> S} \<le> (\<mu> + \<Lambda>\<^sub>a*(1-\<mu>)) ^ card T"
    (is "?L1 \<le> ?R1") if "T \<subseteq> {..<l}" for T 
  proof -
    have "?L1 = measure (pmf_of_multiset (walks G l)) {w. set (nths w T) \<subseteq> S}"
      unfolding set_nths setcompr_eq_image using that set_walks_3 walks_nonempty
      by (intro measure_eq_AE AE_pmfI) (auto simp add:image_subset_iff)
    also have "... \<le> ?R1"
      unfolding \<mu>_def by (intro hitting_property[OF assms(2) that])
    finally show ?thesis by simp
  qed
 
  have "?L \<le> exp ( - real l * KL_div \<gamma> ?\<delta>)"
    using assms(1,4,5) a by (intro impagliazzo_kabanets_pmf) simp_all
  also have "... = ?R" by simp
  finally show ?thesis by simp
qed

end

unbundle no_intro_cong_syntax

end

