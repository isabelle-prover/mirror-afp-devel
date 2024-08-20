section\<open>Towards the proof of the Balog--Szemer\'{e}di--Gowers Theorem\<close>

(*
  Session: Balog_Szemeredi_Gowers
  Title:   Balog_Szemeredi_Gowers_Main_Proof.thy
  Authors: Angeliki Koutsoukou-Argyraki, Mantas Bakšys, and Chelsea Edmonds 
  Affiliation: University of Cambridge
  Date: August 2022.
*)

theory Balog_Szemeredi_Gowers_Main_Proof
  imports 
    Prob_Space_Lemmas
    Graph_Theory_Preliminaries
    Sumset_Triangle_Inequality
    Additive_Combinatorics_Preliminaries
begin

context additive_abelian_group

begin

text\<open>After having introduced all the necessary preliminaries in the imported files, we are now 
 ready to follow the chain of the arguments for the main proof as in Gowers's notes \cite{Gowersnotes}.\<close>

text\<open>The following lemma corresponds to Lemma 2.13 in Gowers's notes \cite{Gowersnotes}.\<close>

lemma (in fin_bipartite_graph) proportion_bad_pairs_subset_bipartite: 
  fixes c::real
  assumes "c > 0"
  obtains X' where "X' \<subseteq> X" and "card X' \<ge> density * card X / sqrt 2" and
  "card (bad_pair_set X' Y c) / (card X')^2 \<le> 2 * c / density^2"
proof (cases "density = 0") (* Edge case *)
  case True
  then show ?thesis using that[of "{}"] bad_pair_set_def by auto
next
  case False
  then have dgt0: "density > 0" using density_simp by auto
  let ?M = "uniform_count_measure Y"
  interpret P: prob_space ?M
    by (simp add: Y_not_empty partitions_finite prob_space_uniform_count_measure)
  have sp: "space ?M = Y"
    by (simp add: space_uniform_count_measure)
  (* First show that the expectation of the size of X' is the average degree of a vertex *)
  have avg_degree: "P.expectation (\<lambda> y . card (neighborhood y)) = density * (card X)"
  proof -
    have "density = (\<Sum>y \<in> Y . degree y)/(card X * card Y)"
      using edge_size_degree_sumY density_simp by simp
    then have d: "density * (card X) = (\<Sum>y \<in> Y . degree y)/(card Y)"
      using card_edges_between_set edge_size_degree_sumY partitions_finite(1) partitions_finite(2) by auto 
    have "P.expectation (\<lambda> y . card (neighborhood y)) = P.expectation (\<lambda> y . degree y)"
      using alt_deg_neighborhood by simp
    also have "... =(\<Sum> y \<in> Y. degree y)/(card Y)" using P.expectation_uniform_count
      by (simp add: partitions_finite(2)) 
    finally show ?thesis using d by simp
  qed
(* Conclude an inequality by Cauchy-Schwarz variation *)
  then have card_exp_gt: "P.expectation (\<lambda> y. (card (neighborhood y))^2) \<ge> density^2 * (card X)^2"
  proof - 
    have "P.expectation (\<lambda> y. (card (neighborhood y))^2) \<ge> (P.expectation (\<lambda> y . card (neighborhood y)))^2" 
      using P.cauchy_schwarz_ineq_var_uniform partitions_finite(2) by auto 
    thus ?thesis using avg_degree
      by (metis of_nat_power power_mult_distrib) 
  qed
(* Define our bad pair sets in this context *)
  define B where "B \<equiv> bad_pair_set X Y c"
  define B' where "B' \<equiv> \<lambda> y. bad_pair_set (neighborhood y) Y c"
  have finB: "finite B" using bad_pair_set_finite partitions_finite B_def by auto
  have "\<And> x. x \<in> X \<Longrightarrow> x \<in> V" using partitions_ss(1) by auto 
  have "card B \<le> (card (X \<times> X))" using B_def bad_pair_set_ss partitions_finite 
    card_mono finite_cartesian_product_iff by metis 
  then have card_B: "card B \<le> (card X)^2"
    by (metis card_cartesian_prod_square partitions_finite(1)) 
  (* Find a bound on the probability of both x and x' belonging to X' *)
  have "\<And> x x' . (x, x') \<in> B \<Longrightarrow> P.prob {y \<in> Y . {x, x'} \<subseteq> neighborhood y} < c"
  proof -
    fix x x' assume assm: "(x, x') \<in> B"
    then have "x \<in> X" "x' \<in> X" unfolding B_def bad_pair_set_def bad_pair_def by auto
    then have card_eq: "card {v \<in> V . vert_adj v x \<and> vert_adj v x'} = card {y \<in> Y. vert_adj y x \<and> vert_adj y x'}"
      by (metis (no_types, lifting) X_vert_adj_Y vert_adj_edge_iff2 vert_adj_imp_inV) 
    have ltc: "card {v \<in> V . vert_adj v x \<and> vert_adj v x'}/(card Y) < c" 
      using assm by (auto simp add: B_def bad_pair_set_def bad_pair_def codegree_normalized_def codegree_def vert_adj_sym)
    have "{y \<in> Y . {x, x'} \<subseteq> neighborhood y} = {y \<in> Y . vert_adj y x \<and> vert_adj y x'}"
      using bad_pair_set_def bad_pair_def neighborhood_def vert_adj_imp_inV vert_adj_imp_inV by auto
    then have "P.prob {y \<in> Y . {x, x'} \<subseteq> neighborhood y} = card {y \<in> Y. vert_adj y x \<and> vert_adj y x'}/ card Y"
      using measure_uniform_count_measure partitions_finite(2) by fastforce 
    thus "P.prob {y \<in> Y . {x, x'} \<subseteq> neighborhood y} < c" using card_eq ltc by simp
  qed
  then have "\<And> x x' . (x, x') \<in> B \<Longrightarrow> P.prob {y \<in> Y . (x, x') \<in> B' y} < c"
    by (simp add: B_def B'_def bad_pair_set_def)
  then have prob: "\<And> p .p \<in> B \<Longrightarrow> P.prob {y \<in> Y . indicator (B' y) p = 1} \<le> c"
    unfolding indicator_def by fastforce   
(* Conclude a bound on the expected number of bad pairs in X' *)
  have dsimp: "(density^2 - (density^2/(2 * c)) * c) * (card X)^2 =(density^2/2) * (card X)^2" 
    using assms by (simp add: algebra_simps)
  then have gt0: "(density^2/2) * (card X)^2 > 0"
    using dgt0 by (metis density_simp division_ring_divide_zero half_gt_zero linorder_neqE_linordered_idom
          of_nat_less_0_iff of_nat_mult power2_eq_square zero_less_mult_iff)
  have Cgt0: "(density^2/(2 * c)) > 0" using dgt0 assms by auto
  have "\<And> y . y \<in> Y \<Longrightarrow> card (B' y) = (\<Sum> p \<in> B. indicator (B' y) p)"
  proof -
    fix y assume "y \<in> Y"
    then have "neighborhood y \<subseteq> X" by (simp add: neighborhood_subset_oppY) 
    then have ss: "B' y \<subseteq> B" unfolding B_def B'_def bad_pair_set_def 
      using set_pairs_filter_subset by blast   
    then show "card (B' y) = (\<Sum> p \<in> B. indicator (B' y) p)" 
      using card_set_ss_indicator[of "B' y" "B"] finB by auto
  qed
  then have "P.expectation (\<lambda> y. card (B' y)) = P.expectation (\<lambda> y. (\<Sum> p \<in> B. indicator (B' y) p))"
    by (metis (mono_tags, lifting) P.prob_space_axioms of_nat_sum partitions_finite(2) 
        prob_space.expectation_uniform_count real_of_nat_indicator sum.cong)
  also have "... = (\<Sum> p \<in> B . P.expectation (\<lambda> y. indicator (B' y) p))"
    by (rule Bochner_Integration.integral_sum[of "B" ?M "\<lambda> p y . indicator (B' y) p"]) 
      (auto simp add:  P.integrable_uniform_count_measure_finite partitions_finite(2))
  finally have "P.expectation (\<lambda> y. card (B' y)) = (\<Sum> p \<in> B . P.prob {y \<in> Y. indicator (B' y) p = 1})"
    using P.expectation_finite_uniform_indicator[of "Y" "B'"] using partitions_finite(2)
    by (smt (verit, best) sum.cong)
  then have "P.expectation (\<lambda> y. card (B' y)) \<le> (\<Sum> p \<in> B . c)" 
    using prob sum_mono[of B "\<lambda> p. P.prob {y \<in> Y. indicator (B' y) p = 1}" "\<lambda> p. c"]
    by (simp add: indicator_eq_1_iff) 
  then have lt1: "P.expectation (\<lambda> y. card (B' y)) \<le> c * (card B)" using finB
    by (simp add: mult_of_nat_commute)  
(* State the inequality for any positive constant C *)
  have "c * (card B) \<le> c * (card X)^2" using assms card_B by auto
  then have "P.expectation (\<lambda> y. card (B' y)) \<le> c * (card X)^2"
    using lt1 by linarith
  then have "\<And> C. C> 0 \<Longrightarrow>  C * P.expectation (\<lambda> y. card (B' y)) \<le> C * c * (card X)^2"
    by auto
  then have "\<And> C . C> 0 \<Longrightarrow>(P.expectation (\<lambda> y. (card (neighborhood y))^2) - C * (P.expectation (\<lambda> y. card (B' y))) 
      \<ge> (density^2 *(card X)^2) - (C*c*(card X)^2))" 
    using card_exp_gt diff_strict1_mono by (smt (verit)) 
  then have "\<And> C .C> 0 \<Longrightarrow> (P.expectation (\<lambda> y. (card (neighborhood y))^2) - C * (P.expectation (\<lambda> y. card (B' y))) 
      \<ge> (density^2 - C * c) * (card X)^2)"
    by (simp add: field_simps)
(* Choose a value for C *)
  then have "(P.expectation (\<lambda> y. (card (neighborhood y))^2) - (density^2/(2 * c)) * (P.expectation (\<lambda> y. card (B' y))) 
      \<ge> (density^2 - (density^2/(2 * c)) * c) * (card X)^2)"
    using Cgt0 assms by blast
  then have "P.expectation (\<lambda> y. (card (neighborhood y))^2) - (density^2/(2 * c)) * (P.expectation (\<lambda> y. card (B' y)))
       \<ge> (density^2/2) * (card X)^2" using dsimp by linarith
  then have "P.expectation (\<lambda> y. (card (neighborhood y))^2) - (P.expectation (\<lambda> y. (density^2/(2 * c)) * card (B' y)))
       \<ge> (density^2/2) * (card X)^2" by auto
  then have "P.expectation (\<lambda> y. (card (neighborhood y))^2 - ((density^2/(2*c)) * card (B' y)))
       \<ge> (density^2/2) * (card X)^2" 
    using Bochner_Integration.integral_diff[of ?M "(\<lambda> y. (card (neighborhood y))^2)" "(\<lambda> y. (density^2/(2 * c)) * card (B' y))"]
    P.integrable_uniform_count_measure_finite partitions_finite(2) by fastforce     
      (* Obtain an X' with the required inequalities *)
  then obtain y where yin: "y \<in> Y" and ineq: "(card (neighborhood y))^2 - ((density^2/(2 * c)) * card (B' y)) \<ge> (density^2/2) * (card X)^2"
    using P.expectation_obtains_ge partitions_finite(2) by blast
(* Show the result follows *)
  let ?X' = "neighborhood y"
  have ss: "?X' \<subseteq> X" 
    using yin by (simp add: neighborhood_subset_oppY) 
  have "local.density\<^sup>2 / (2 * c) * real (card (B' y)) \<ge> 0" 
    using assms density_simp by simp 
  then have d1: "(card ?X')^2 \<ge> (density^2/2) * (card X)^2" 
    using ineq by linarith
  then have "(card ?X') \<ge> sqrt(((density) * (card X))^2/2)"
    by (simp add: field_simps real_le_lsqrt) 
  then have den: "((card ?X') \<ge> (density * (card X)/(sqrt 2)))"
    by (smt (verit, del_insts) divide_nonneg_nonneg divide_nonpos_nonneg real_sqrt_divide 
        real_sqrt_ge_0_iff real_sqrt_unique zero_le_power2)
  have xgt0: "(card ?X') > 0" using dgt0 gt0
    using d1 gr0I by force (* long *)
  then have "(card ?X')^2 \<ge> (density^2/(2 * c)) * card (B' y)"
    using gt0 ineq by simp 
  then have "(card ?X')^2/(density^2/(2 * c)) \<ge> card (B' y)" 
    using Cgt0 by (metis mult.commute pos_le_divide_eq)
  then have "((2 * c)/(density^2)) \<ge> card (B' y)/(card ?X')^2"  
    using pos_le_divide_eq xgt0 by (simp add: field_simps)
  thus ?thesis using that[of "?X'"] den ss B'_def by auto
qed

text\<open>The following technical probability lemma corresponds to Lemma 2.14 in Gowers's notes \cite{Gowersnotes}. \<close>

lemma (in prob_space) expectation_condition_card_1: 
  fixes X::"'a set"  and f::"'a \<Rightarrow> real" and \<delta>::real
  assumes "finite X" and "\<forall> x \<in> X. f x \<le> 1" and "M = uniform_count_measure X" and "expectation f \<ge> \<delta>"
  shows "card {x \<in> X. (f x \<ge> \<delta> / 2)} \<ge> \<delta> * card X / 2"
proof (cases "\<delta> \<ge> 0")
  assume h\<delta>: "\<delta> \<ge> 0"
  have ineq1: "real (card (X - {x \<in> X. \<delta> \<le> f x * 2})) * \<delta> \<le> real (card X) * \<delta>" 
    using card_mono assms Diff_subset h\<delta> mult_le_cancel_right nat_le_linear of_nat_le_iff 
    by (smt (verit, best))
  have ineq2: "\<forall> x \<in> X - {x. x \<in> X \<and> (f x \<ge> \<delta>/2)}. f x \<le> \<delta> / 2" by auto
  have "expectation f * card X = (\<Sum>x \<in> X. f x)"
    using assms(1) expectation_uniform_count assms(3) by force
  also have "... = (\<Sum> x \<in>{x. x \<in> X \<and> (f x \<ge> \<delta>/2)}. f x) 
    +(\<Sum> x \<in> X - {x. x \<in> X \<and> (f x \<ge> \<delta>/2)}. f x)"
    using assms 
    by (metis (no_types, lifting) add.commute mem_Collect_eq subsetI sum.subset_diff)
  also have "... \<le> (\<Sum> x \<in>  {x. x \<in> X \<and> (f x \<ge> \<delta>/2)}. 1) + 
    (\<Sum> x \<in> X - {x. x \<in> X \<and> (f x \<ge> \<delta>/2)} . \<delta> / 2)"
    using assms sum_mono ineq2 by (smt (verit, ccfv_SIG) mem_Collect_eq)
  also have "... \<le> card ({x. x \<in> X \<and> (f x \<ge> \<delta>/2)}) + (card X) * \<delta> / 2 "
    using ineq1 by auto
  finally have "\<delta> * card X \<le> card  {x. x \<in> X \<and> (f x \<ge> \<delta>/2)}+ (\<delta>/2)*(card X)"
    using ineq1 mult_of_nat_commute assms(4) mult_right_mono le_trans
    by (smt (verit, del_insts) of_nat_0_le_iff times_divide_eq_left)
  then show ?thesis by auto
next
  assume "\<not> \<delta> \<ge> 0"
  thus ?thesis by (smt (verit, del_insts) divide_nonpos_nonneg mult_nonpos_nonneg of_nat_0_le_iff)
qed

text\<open>The following technical probability lemma corresponds to Lemma 2.15 in Gowers's notes. \<close>

lemma (in prob_space) expectation_condition_card_2:
  fixes X::"'a set" and \<beta>::real and \<alpha>::real and f:: "'a \<Rightarrow> real"
  assumes "finite X"  and "\<And> x. x \<in> X \<Longrightarrow> f x \<le> 1" and "\<beta> > 0" and "\<alpha> > 0"
  and "expectation f \<ge> 1 - \<alpha>" and "M = uniform_count_measure X"
  shows "card {x \<in> X. f x \<ge> 1 - \<beta>} \<ge> (1- \<alpha> / \<beta>) * card X"

proof-
  have hcard: "card {x \<in> X. 1 - \<beta> \<le> f x} \<le> card X" using card_mono assms(1) by fastforce
  have h\<beta>: "\<forall> x \<in> X- {x. x \<in> X \<and> (f x \<ge> 1 - \<beta>)}. f x \<le> 1 - \<beta>" by auto
  have "expectation f * card X = (\<Sum> x \<in> X. f x)"
    using assms(1) expectation_uniform_count assms(6) by force
  then have "(1 - \<alpha>) * card X \<le> (\<Sum> x \<in> X. f x)" using assms
    by (metis mult.commute sum_bounded_below sum_constant)
  also have "... = (\<Sum> x \<in> {x. x \<in> X \<and> (f x \<ge> 1 - \<beta>)}. f x) + 
 (\<Sum> x \<in> X - {x. x \<in> X \<and> (f x \<ge> 1 - \<beta>)}. f x)" using assms 
    by (metis (no_types, lifting) add.commute mem_Collect_eq subsetI sum.subset_diff)
  also have "... \<le>  (\<Sum> x \<in> {x. x \<in> X \<and> (f x \<ge> 1 - \<beta>)}. 1) + 
 (\<Sum> x \<in> X - {x. x \<in> X \<and> (f x \<ge> 1 - \<beta>)}. (1 - \<beta>))"
    using assms h\<beta> sum_mono by (smt (verit, ccfv_SIG) mem_Collect_eq)
  also have "...  = card {x. x \<in> X \<and> (f x \<ge> 1 - \<beta>)} + (1-\<beta>) * card ( X- {x. x \<in> X \<and> (f x \<ge> 1 - \<beta>)})"
    by auto
  also have "... = (card {x. x \<in> X \<and> (f x \<ge> 1 - \<beta>)} + 
    card (X- {x. x \<in> X \<and> (f x \<ge> 1 - \<beta>)})) - \<beta> * card (X -{x. x \<in> X \<and> (f x \<ge> 1 - \<beta>)})"
    using left_diff_distrib
    by (smt (verit, ccfv_threshold) mult.commute mult.right_neutral of_nat_1 of_nat_add of_nat_mult)
  also have heq: "... = card X - \<beta> * card (X -{x. x \<in> X \<and> (f x \<ge> 1 - \<beta>)})" 
    using assms(1) card_Diff_subset[of "{x. x \<in> X \<and> (f x \<ge> 1 - \<beta>)}" "X"] hcard by auto
  finally have "(1- \<alpha>) * card X \<le> card X - \<beta> * card ( X -{x. x \<in> X \<and> (f x \<ge> 1 - \<beta>)})" by blast
  then have "- (1- \<alpha>) * card X + card X \<ge> \<beta> * card ( X -{x. x \<in> X \<and> (f x \<ge> 1 - \<beta>)})" by linarith
  then have "- card X + \<alpha> * card X + card X \<ge> \<beta> * card(X - {x. x \<in> X \<and> (f x \<ge> 1 - \<beta>)})"
    using add.assoc add.commute
    add.right_neutral add_0 add_diff_cancel_right' add_diff_eq add_uminus_conv_diff diff_add_cancel 
    distrib_right minus_diff_eq mult.commute mult_1 of_int_minus of_int_of_nat_eq uminus_add_conv_diff
    cancel_comm_monoid_add_class.diff_cancel by (smt (verit, del_insts) mult_cancel_right2)
  then have "\<alpha> * card X \<ge> \<beta> * card(X - {x. x \<in> X \<and> (f x \<ge> 1 - \<beta>)})" by auto
  then have "\<alpha> * card X / \<beta> \<ge> card(X - {x. x \<in> X \<and> (f x \<ge> 1 - \<beta>)})" using assms
    by (smt (verit, ccfv_SIG) mult.commute pos_divide_less_eq)
  then show ?thesis by (smt (verit) heq combine_common_factor left_diff_distrib' mult_of_nat_commute
    nat_mult_1_right of_nat_1 of_nat_add of_nat_mult times_divide_eq_left scale_minus_left)
qed

text\<open>The following lemma corresponds to Lemma 2.16 in Gowers's notes \cite{Gowersnotes}. For the proof, we will apply 
Lemma 2.13 (@{term proportion_bad_pairs_subset_bipartite}, the technical probability Lemmas 2.14 
(@{term expectation_condition_card_1}) and 2.15 (@{term expectation_condition_card_2}) as well 
as background material on graphs with loops and bipartite graphs that was previously presented.  \<close>

lemma (in fin_bipartite_graph) walks_of_length_3_subsets_bipartite: 
  obtains X' and Y' where "X' \<subseteq> X" and "Y' \<subseteq> Y" and
  "card X' \<ge> (edge_density X Y)^2 * card X / 16" and
  "card Y' \<ge> edge_density X Y * card Y / 4" and
  "\<forall> x \<in> X'. \<forall> y \<in> Y'. card {p. connecting_walk x y p \<and> walk_length p = 3} \<ge> 
  (edge_density X Y)^6 * card X * card Y / 2^13"

proof (cases "edge_density X Y > 0")
  let ?\<delta> = "edge_density X Y"
  assume h\<delta>: "?\<delta> > 0" 
  interpret P1: prob_space "uniform_count_measure X"
    by (simp add: X_not_empty partitions_finite(1) prob_space_uniform_count_measure)
  have hP1exp: "P1.expectation (\<lambda> x. degree_normalized x Y) \<ge> ?\<delta>"
    using P1.expectation_uniform_count partitions_finite sum_degree_normalized_X_density by auto
  let ?X1 = "{x \<in> X. (degree_normalized x Y \<ge> ?\<delta>/2)}"
  have hX1X: "?X1 \<subseteq> X" and hX1card: "card ?X1 \<ge> ?\<delta> * (card X)/2"
    and hX1degree: "\<forall> x \<in> ?X1. degree_normalized x Y \<ge> ?\<delta> /2" using 
      P1.expectation_condition_card_1 partitions_finite degree_normalized_le_1 hP1exp by auto
  have hX1cardpos: "card ?X1 > 0" using hX1card h\<delta> X_not_empty
    by (smt (verit, del_insts) divide_divide_eq_right divide_le_0_iff density_simp gr0I 
        less_eq_real_def mult_is_0 not_numeral_le_zero of_nat_le_0_iff of_nat_less_0_iff)
  interpret H: fin_bipartite_graph "(?X1 \<union> Y)" "{e \<in> E. e \<subseteq> (?X1 \<union> Y)}" "?X1" "Y"
  proof (unfold_locales, simp add: partitions_finite)
    have "disjoint {?X1, Y}" using hX1X partition_on_def partition
      by (metis (no_types, lifting) disjnt_subset2 disjnt_sym ne pairwise_insert singletonD)
    moreover have "{} \<notin> {?X1, Y}" using hX1cardpos Y_not_empty
      by (metis (no_types, lifting) card.empty insert_iff neq0_conv singleton_iff)
    ultimately show "partition_on (?X1 \<union> Y) {?X1, Y}" using partition_on_def by auto
  next
    show "?X1 \<noteq> Y" using ne partition by (metis Int_absorb1 Y_not_empty hX1X part_intersect_empty)
  next
    show "\<And>e. e \<in> {e \<in> E. e \<subseteq> ?X1 \<union> Y} \<Longrightarrow> e \<in> all_bi_edges {x \<in> X. edge_density X Y / 2 \<le> 
      degree_normalized x Y} Y"
      using Un_iff Y_verts_not_adj edge_betw_indiv in_mono insert_subset mem_Collect_eq 
       subset_refl that vert_adj_def all_bi_edges_def[of "?X1" "Y"] in_mk_uedge_img_iff
       by (smt (verit, ccfv_threshold) all_edges_betw_I all_edges_between_bi_subset)
  next
    show "finite (?X1 \<union> Y)" using hX1X by (simp add: partitions_finite(1) partitions_finite(2))
  qed
  have neighborhood_unchanged: "\<forall> x \<in> ?X1. neighbors_ss x Y = H.neighbors_ss x Y" 
    using neighbors_ss_def H.neighbors_ss_def vert_adj_def H.vert_adj_def by auto
  then have degree_unchanged: "\<forall> x \<in> ?X1. degree x = H.degree x" 
    using H.degree_neighbors_ssX degree_neighbors_ssX by auto
  have hHdensity: "(H.edge_density ?X1 Y) \<ge> ?\<delta> / 2" 
  proof-
    have "?\<delta> / 2 = (\<Sum> x \<in> ?X1. (?\<delta> / 2)) / card ?X1" using hX1cardpos by auto
    also have "... \<le> (\<Sum> x \<in> ?X1. degree_normalized x Y) / card ?X1"
      using sum_mono hX1degree  hX1cardpos divide_le_cancel
      by (smt (z3) H.X_not_empty H.partitions_finite(1) 
        calculation divide_pos_pos h\<delta> sum_pos zero_less_divide_iff)
    also have "... = (H.edge_density ?X1 Y)" 
      using H.degree_normalized_def degree_normalized_def degree_unchanged sum.cong
        H.degree_neighbors_ssX degree_neighbors_ssX H.sum_degree_normalized_X_density by auto
    finally show ?thesis by simp
  qed
  have h\<delta>3pos: "?\<delta>^3 / 128 > 0" using h\<delta> by auto
  then obtain X2 where hX2subX1: "X2 \<subseteq> ?X1" and hX2card: "card X2 \<ge> (H.edge_density ?X1 Y) * 
    (card ?X1)/ (sqrt 2)" and hX2badtemp: "(card (H.bad_pair_set X2 Y (?\<delta>^3 / 128))) / real ((card X2)^2)
           \<le> 2 * (?\<delta>^3 / 128) / (H.edge_density ?X1 Y)^2" using H.proportion_bad_pairs_subset_bipartite
    by blast
  have "(H.edge_density ?X1 Y) * (card ?X1)/ (sqrt 2) > 0" using hHdensity hX1cardpos h\<delta> hX2card 
    by auto
  then have hX2cardpos: "card X2 > 0" using hX2card by auto
  then have hX2finite: "finite X2" using card_ge_0_finite by auto
  have hX2bad: "(card (H.bad_pair_set X2 Y (?\<delta>^3 / 128))) \<le> (?\<delta> / 16) * (card X2)^2"
  proof-
    have hpos: "real ((card X2)^2) > 0" using hX2cardpos by auto
    have trivial: "(3:: nat) - 2 = 1" by simp
    then have h\<delta>pow: "?\<delta> ^ 3 / ?\<delta> ^ 2 = ?\<delta>^1" using power_diff h\<delta>
      by (metis div_greater_zero_iff less_numeral_extra(3) numeral_Bit1_div_2 zero_less_numeral) 
    have "card (H.bad_pair_set X2 Y (?\<delta>^3 / 128)) \<le> (2 * (?\<delta>^3 / 128) / (H.edge_density ?X1 Y)^2) *
      (card X2)^2" using hX2badtemp hX2cardpos by (simp add: field_simps)
    also have "... \<le> (2 * (?\<delta>^3 / 128) / (?\<delta> / 2)^2) * (card X2)^2" 
      using h\<delta> hHdensity divide_left_mono frac_le hpos by (smt (verit) divide_pos_pos 
          edge_density_ge0 le_divide_eq power_mono zero_le_divide_iff zero_less_power)
    also have "... = (?\<delta>^3 / ?\<delta>^2) * (1/16) * (card X2)^2" by (simp add: field_simps)
    also have "... = (?\<delta> / 16) * (card X2) ^ 2" using h\<delta>pow by auto
    finally show ?thesis by simp
  qed
  let ?E_loops = "mk_edge ` {(x, x') | x x'. x \<in> X2 \<and> x' \<in> X2 \<and> 
    (H.codegree_normalized x x' Y) \<ge> ?\<delta> ^ 3 / 128}"
  interpret \<Gamma>: ulgraph "X2" "?E_loops"
  proof(unfold_locales)
    show "\<And>e. e \<in> ?E_loops \<Longrightarrow> e \<subseteq> X2" by auto
  next
    have "\<And>a b. a \<in> X2 \<Longrightarrow> b \<in> X2 \<Longrightarrow> 0 < card {a, b}"
      by (meson card_0_eq finite.emptyI finite_insert insert_not_empty neq0_conv)
    moreover have "\<And> a b. a \<in> X2 \<Longrightarrow> b \<in> X2 \<Longrightarrow> card {a, b} \<le> 2"
      by (metis card_2_iff dual_order.refl insert_absorb2 is_singletonI 
          is_singleton_altdef one_le_numeral)
    ultimately show "\<And>e. e \<in> ?E_loops \<Longrightarrow> 0 < card e \<and> card e \<le> 2" by auto
  qed
  have h\<Gamma>_edges: "\<And> a b. a \<in> X2 \<Longrightarrow> b \<in> X2 \<Longrightarrow> 
      {a, b} \<in> ?E_loops \<longleftrightarrow> H.codegree_normalized a b Y \<ge> ?\<delta>^3/128"
    proof
      fix a b assume "{a, b} \<in> ?E_loops"
      then show "H.codegree_normalized a b Y \<ge> ?\<delta>^3/128"
        using in_mk_uedge_img_iff[of "a" "b" "{(x, x') | x x'. x \<in> X2 \<and> x' \<in> X2 \<and> 
        (H.codegree_normalized x x' Y) \<ge> ?\<delta> ^ 3 / 128}"] doubleton_eq_iff H.codegree_normalized_sym 
        by auto
    next
      fix a b assume "a \<in> X2" and "b \<in> X2" and "H.codegree_normalized a b Y \<ge> ?\<delta>^3/128"
      then show "{a, b} \<in> ?E_loops" using in_mk_uedge_img_iff[of "a" "b" "{(x, x') | x x'. x \<in> X2 \<and> 
        x' \<in> X2 \<and> (H.codegree_normalized x x' Y) \<ge> ?\<delta> ^ 3 / 128}"] H.codegree_normalized_sym by auto
  qed
  interpret P2: prob_space "uniform_count_measure X2"
    using hX2finite hX2cardpos prob_space_uniform_count_measure by fastforce
  have hP2exp: "P2.expectation (\<lambda> x. \<Gamma>.degree_normalized x X2) \<ge> 1 - ?\<delta> / 16"
  proof-
    have h\<Gamma>all: "\<Gamma>.all_edges_between X2 X2 = (X2 \<times> X2) - H.bad_pair_set X2 Y (?\<delta>^3 / 128)"
    proof
      show "\<Gamma>.all_edges_between X2 X2 \<subseteq> X2 \<times> X2 - H.bad_pair_set X2 Y (?\<delta> ^ 3 / 128)"
      proof
        fix x assume "x \<in> \<Gamma>.all_edges_between X2 X2"
        then obtain a b where "a \<in> X2" and "b \<in> X2" and "x = (a, b)" and 
          "H.codegree_normalized a b Y \<ge> ?\<delta>^3 / 128" 
          using \<Gamma>.all_edges_between_def in_mk_uedge_img_iff h\<Gamma>_edges
          by (smt (verit, del_insts) \<Gamma>.all_edges_betw_D3 \<Gamma>.wellformed_alt_snd edge_density_commute 
              mk_edge.cases mk_edge.simps that)
        then show "x \<in> X2 \<times> X2 - H.bad_pair_set X2 Y (?\<delta> ^ 3 / 128)" 
          using H.bad_pair_set_def H.bad_pair_def by auto
      qed
    next
      show "X2 \<times> X2 - H.bad_pair_set X2 Y (?\<delta> ^ 3 / 128) \<subseteq> \<Gamma>.all_edges_between X2 X2"
        using H.bad_pair_set_def H.bad_pair_def \<Gamma>.all_edges_between_def h\<Gamma>_edges by auto
    qed
    then have h\<Gamma>all_le: "card (\<Gamma>.all_edges_between X2 X2) \<ge> (1 - ?\<delta> / 16) * (card X2 * card X2)" 
    proof-
      have hbadsub: "H.bad_pair_set X2 Y (?\<delta> ^3 / 128) \<subseteq> X2 \<times> X2" using H.bad_pair_set_def by auto
      have "(1 - ?\<delta> / 16) * (card X2 * card X2) = card (X2 \<times> X2) - ?\<delta> / 16 * (card X2) ^2"
        using card_cartesian_product power2_eq_square 
        by (metis Rings.ring_distribs(4) more_arith_simps(6) mult_of_nat_commute)
      also have "... \<le> card (X2 \<times> X2) - card (H.bad_pair_set X2 Y (?\<delta> ^ 3 / 128))" 
        using hX2bad by auto
      also have "... = card (X2 \<times> X2 - H.bad_pair_set X2 Y (?\<delta> ^ 3 / 128))" using card_Diff_subset 
        finite_cartesian_product[of "X2" "X2"] hX2finite hbadsub 
        by (metis (mono_tags, lifting) finite_subset)
      finally show "card(\<Gamma>.all_edges_between X2 X2) \<ge> (1 - ?\<delta>/16) * (card X2 * card X2)"
        using h\<Gamma>all by simp
    qed
    have "1 - ?\<delta> / 16 = ((1 - ?\<delta> / 16) * (card X2 * card X2)) / (card X2 * card X2)" 
      using hX2cardpos by auto
    also have "... \<le> card (\<Gamma>.all_edges_between X2 X2) / (card X2 * card X2)" 
      using h\<Gamma>all_le hX2cardpos divide_le_cancel of_nat_less_0_iff by fast
    also have "... = (\<Sum> x \<in> X2. real (card (\<Gamma>.neighbors_ss x X2))) / card X2 / card X2"
      using \<Gamma>.card_all_edges_betw_neighbor[of "X2" "X2"] hX2finite by (auto simp add: field_simps)
    also have "... = (\<Sum> x \<in> X2. \<Gamma>.degree_normalized x X2) / card X2"
      unfolding \<Gamma>.degree_normalized_def 
      using sum_divide_distrib[of "\<lambda> x. real (card (\<Gamma>.neighbors_ss x X2))" "X2" "card X2"] by auto
    also have "... = P2.expectation (\<lambda> x. \<Gamma>.degree_normalized x X2)"
      using P2.expectation_uniform_count hX2finite by auto
    finally show ?thesis by simp
  qed
  let ?X' = "{x \<in> X2. \<Gamma>.degree_normalized x X2 \<ge> 1 - ?\<delta> / 8}"
  have hX'subX2: "?X' \<subseteq> X2" by blast
  have hX'cardX2: "card ?X' \<ge> card X2 / 2" using hX2finite divide_self h\<delta>
    P2.expectation_condition_card_2 [of "X2" "(\<lambda> x. \<Gamma>.degree_normalized x X2)" "?\<delta> /8" "?\<delta> / 16"] 
    hP2exp \<Gamma>.degree_normalized_le_1 by auto
  interpret P3: prob_space "uniform_count_measure Y"
    by (simp add: Y_not_empty partitions_finite(2) prob_space_uniform_count_measure)
  have hP3exp: "P3.expectation (\<lambda> y. H.degree_normalized y X2) \<ge> ?\<delta> / 2"
  proof-
    have hHdegree_normalized: "\<And> x. x \<in> X2 \<Longrightarrow> (?\<delta> / 2) \<le> H.degree_normalized x Y"
      using hX1degree degree_normalized_def  H.degree_normalized_def neighborhood_unchanged 
        hX2subX1 subsetD by (metis (no_types, lifting))
    have "?\<delta> / 2 = (\<Sum> x \<in> X2. (?\<delta> / 2)) / card X2" using hX2cardpos by auto
    also have "... \<le> (\<Sum> x \<in> X2. real (card (H.neighbors_ss x Y))) / card Y / card X2" 
      using hHdegree_normalized sum_mono divide_le_cancel hX2cardpos of_nat_0_le_iff
        H.degree_normalized_def sum.cong sum_divide_distrib by (smt (verit, best))
    also have "... = (card (H.all_edges_between Y X2)) / card X2 / card Y"
      using H.card_all_edges_between_commute  H.card_all_edges_betw_neighbor hX2finite 
        H.partitions_finite(2) by auto
    also have "... = (\<Sum> y \<in> Y. real (card(H.neighbors_ss y X2))) / card X2 / card Y" using
        H.card_all_edges_betw_neighbor hX2finite H.partitions_finite(2) by auto
    also have "... = (\<Sum> y \<in> Y. H.degree_normalized y X2) / card Y" using H.degree_normalized_def 
      sum.cong sum_divide_distrib by (smt (verit, best))
    also have "... = P3.expectation (\<lambda> y. H.degree_normalized y X2)" 
      using P3.expectation_uniform_count H.partitions_finite(2) by auto
    finally show ?thesis by linarith
  qed
  let ?Y' = "{x \<in> Y. H.degree_normalized x X2 \<ge> ?\<delta> / 4}"
  have hY'subY: "?Y' \<subseteq> Y" by blast
  then have hY'card: "card ?Y' \<ge> ?\<delta>  * card Y / 4"
    using P3.expectation_condition_card_1[of "Y" "(\<lambda> y. H.degree_normalized y X2)" "?\<delta> / 2"] H.partitions_finite(2) 
      hP3exp H.degree_normalized_le_1 by auto

  have hX2adjcard: "\<And> x y. x \<in> ?X' \<Longrightarrow> y \<in> ?Y' \<Longrightarrow> 
    card {x' \<in> X2. \<Gamma>.vert_adj x x' \<and> vert_adj y x'} \<ge> ?\<delta> / 8 * card X2"
  proof-
    fix x y assume hx: "x \<in> ?X'" and hy: "y \<in> ?Y'"
    have hinter: "{x' \<in> X2. \<Gamma>.vert_adj x x' \<and> vert_adj y x'} = 
      {x' \<in> X2. \<Gamma>.vert_adj x x'} \<inter> {x' \<in> X2. vert_adj y x'}" by auto
    have huncardX2: "card ({x' \<in> X2. \<Gamma>.vert_adj x x'} \<union> {x' \<in> X2. vert_adj y x'}) \<le> card X2" 
      using card_mono hX2finite by fastforce
    have fin1: "finite {x' \<in> X2. \<Gamma>.vert_adj x x'}" and fin2: "finite {x' \<in> X2. vert_adj y x'}"
      using hX2finite by auto 
    have "{x' \<in> X2. \<Gamma>.vert_adj x x'} = \<Gamma>.neighbors_ss x X2"
    using \<Gamma>.vert_adj_def vert_adj_def \<Gamma>.neighbors_ss_def hX2subX1 \<Gamma>.neighbors_ss_def by auto
    then have hcard1: "card {x' \<in> X2. \<Gamma>.vert_adj x x'} \<ge> (1 - ?\<delta>/8) * card X2" using hx 
        \<Gamma>.degree_normalized_def divide_le_eq hX2cardpos by (simp add: hX2card le_divide_eq)
    have "{x' \<in> X2. vert_adj y x'} = H.neighbors_ss y X2" using H.vert_adj_def vert_adj_def 
      H.neighbors_ss_def hy hY'subY hX2subX1 H.neighbors_ss_def by auto
    then have hcard2: "card {x' \<in> X2. vert_adj y x'} \<ge> (?\<delta> / 4) * card X2" 
      using hy H.degree_normalized_def divide_le_eq hX2cardpos by (simp add: hX2card le_divide_eq)
    have "?\<delta> / 8 * card X2 = (1 - ?\<delta> / 8) * card X2 + ?\<delta>/4 * card X2 - card X2" 
      by (simp add: algebra_simps)
    also have "... \<le> card {x' \<in> X2. \<Gamma>.vert_adj x x'} + card {x' \<in> X2. vert_adj y x'} -
      card ({x' \<in> X2. \<Gamma>.vert_adj x x'} \<union> {x' \<in> X2. vert_adj y x'})" 
      using huncardX2 hcard1 hcard2 by linarith
    also have "... = card {x' \<in> X2. \<Gamma>.vert_adj x x' \<and> vert_adj y x'}"
      using card_Un_Int fin1 fin2 hinter by fastforce
    finally show "card {x' \<in> X2. \<Gamma>.vert_adj x x' \<and> vert_adj y x'} \<ge> ?\<delta> / 8 * card X2" 
      by linarith
  qed
  have hYpos: "real (card Y) > 0" using Y_not_empty partitions_finite(2) by auto
  have "\<And> x y. x \<in> ?X' \<Longrightarrow> y \<in> ?Y' \<Longrightarrow> card {p. connecting_walk x y p \<and> walk_length p = 3} \<ge> 
    (?\<delta> ^ 3 / 128 * (card Y)) * ((?\<delta> / 8) * (card X2))"
  proof-
    fix x y assume hx: "x \<in> ?X'" and hy: "y \<in> ?Y'"
    then have hxV: "x \<in> V" and hyV: "y \<in> V" using hY'subY hX'subX2 hX2subX1 hX1X partitions_ss(1)
     partitions_ss(2) subsetD by auto
    define f:: "'a \<Rightarrow> 'a list set" where "f \<equiv> (\<lambda> a. ((\<lambda> z. z @ [y]) ` {p. connecting_path x a p \<and> walk_length p = 2}))"
    have h_norm: "\<And> a. a \<in> {x' \<in> X2. \<Gamma>.vert_adj x x' \<and> vert_adj y x'} \<Longrightarrow> codegree_normalized x a Y \<ge> ?\<delta>^3 / 128"
      using \<Gamma>.vert_adj_def codegree_normalized_sym hx hX'subX2 subsetD 
        codegree_normalized_altX H.codegree_normalized_altX neighborhood_unchanged 
        h\<Gamma>_edges hX2subX1 hX1X by (smt (verit, del_insts) mem_Collect_eq)
    have inj_concat: "inj (\<lambda> z. z @ [y])" using inj_def by blast                                       
    then have card_f_eq: "\<And> a. card (f a) = card {p. connecting_path x a p \<and> walk_length p = 2}" 
      using f_def card_image inj_eq by (smt (verit) inj_onI)
    then have card_f_ge: "\<And> a. a \<in> {x' \<in> X2. \<Gamma>.vert_adj x x' \<and> vert_adj y x'} \<Longrightarrow> 
      card (f a) \<ge> ?\<delta>^3 / 128 * card Y" 
      using codegree_is_path_length_two codegree_normalized_def hYpos f_def h_norm by (simp add: field_simps)
    have f_disjoint: "pairwise (\<lambda> s t. disjnt (f s) (f t)) {x' \<in> X2. \<Gamma>.vert_adj x x' \<and> vert_adj y x'}"
    proof (intro pairwiseI)
      fix s t assume "s \<in> {x' \<in> X2. \<Gamma>.vert_adj x x' \<and> vert_adj y x'}" and 
        "t \<in> {x' \<in> X2. \<Gamma>.vert_adj x x' \<and> vert_adj y x'}" and "s \<noteq> t" 
      moreover have "\<And> a l. l \<in> f a \<Longrightarrow> l ! 2 = a" 
      proof-
        fix a l assume "l \<in> f a"
        then obtain z where hz: "z \<in> {p. connecting_path x a p \<and> walk_length p = 2}" and hlz: "l = z @ [y]" 
          using f_def by blast
        then have "z ! 2 = a" using walk_length_conv connecting_path_def last_conv_nth
          by (metis (mono_tags, lifting) diff_add_inverse length_tl list.sel(2) mem_Collect_eq 
            nat_1_add_1 one_eq_numeral_iff rel_simps(18))
        then show "l ! 2 = a" using hlz nth_append hz walk_length_conv less_diff_conv mem_Collect_eq
          by (metis (mono_tags, lifting) nat_1_add_1 one_less_numeral_iff rel_simps(9))
      qed
      ultimately show "disjnt (f s) (f t)" by (metis disjnt_iff)
    qed
    have hwalk_subset: "{p. connecting_walk x k p \<and> walk_length p = n} \<subseteq> {p. set p \<subseteq> V \<and> length p = n + 1}" for n k
      using connecting_walk_def is_walk_def walk_length_conv by auto
    have finite_walk: "finite {p. connecting_walk x k p \<and> walk_length p = n}" for n k
      using finV finite_lists_length_eq finite_subset hwalk_subset[of "k" "n"] rev_finite_subset by blast
    have f_finite: "\<And> A. A \<in> (f ` {x' \<in> X2. \<Gamma>.vert_adj x x' \<and> vert_adj y x'}) \<Longrightarrow> finite A"
    proof-
      fix A assume "A \<in> (f ` {x' \<in> X2. \<Gamma>.vert_adj x x' \<and> vert_adj y x'})"
      then obtain a where "a \<in> {x' \<in> X2. \<Gamma>.vert_adj x x' \<and> vert_adj y x'}" and hA: "A = f a" by blast
      have "{p. connecting_path x a p \<and> walk_length p = 2} \<subseteq> {p. connecting_walk x a p \<and> walk_length p = 2}" 
        using connecting_path_walk by blast
      then have "finite {p. connecting_path x a p \<and> walk_length p = 2}" 
        using finite_walk finite_subset connecting_path_walk by blast
      then show "finite A" using f_def hA by auto
    qed
    moreover have f_image_sub: 
      "(\<Union> x \<in> {x' \<in> X2. \<Gamma>.vert_adj x x' \<and> vert_adj y x'}. f x) \<subseteq> {p. connecting_walk x y p \<and> walk_length p = 3}"
    proof(intro Union_least)
      fix X assume "X \<in> f ` {x' \<in> X2. \<Gamma>.vert_adj x x' \<and> vert_adj y x'}"
      then obtain a where ha: "a \<in> {x' \<in> X2. \<Gamma>.vert_adj x x' \<and> vert_adj y x'}" and haX: "f a = X" by blast
      have "\<And>z. connecting_path x a z \<Longrightarrow> walk_length z = 2 \<Longrightarrow> connecting_walk x y (z @ [y])"
      proof-
        fix z assume hpath: "connecting_path x a z" and hlen: "walk_length z = 2" 
        then obtain y' where "z ! 1 = y'" by blast
        then have hz: "z = [x, y', a]" using list2_middle_singleton walk_length_conv 
          connecting_path_def hpath hlen add_diff_cancel_left' append_butlast_last_id
          butlast.simps connecting_path_walk connecting_walk_def diff_diff_add diff_le_self 
          is_walk_not_empty is_walk_tl last_ConsL last_tl list.expand list.sel list.simps(3) 
          nat_1_add_1 le_imp_diff_is_add 
          by (metis (no_types, lifting) arith_simps(45) arithmetic_simps(2) numerals(1))
        moreover have hwalk: "connecting_walk x a z" using connecting_path_walk hpath by blast
        then show "connecting_walk x y (z @ [y])" using connecting_walk_def is_walk_def 
          connecting_path_def is_gen_path_def is_walk_def ha hz hwalk hyV vert_adj_sym vert_adj_def by auto
      qed
      then show "X \<subseteq> {p. connecting_walk x y p \<and> walk_length p = 3}"
        using haX f_def walk_length_conv by auto
    qed
    ultimately have hUn_le: "card (\<Union> x \<in> {x' \<in> X2. \<Gamma>.vert_adj x x' \<and> vert_adj y x'}. f x) \<le> card {p. connecting_walk x y p \<and> walk_length p = 3}"
      using card_mono finite_walk[of "y" "3"] by blast
    have "disjoint (f ` {x' \<in> X2. \<Gamma>.vert_adj x x' \<and> vert_adj y x'})" using f_disjoint pairwise_def
        pairwise_image[of "disjnt" "f" "{x' \<in> X2. \<Gamma>.vert_adj x x' \<and> vert_adj y x'}"] by (metis (mono_tags, lifting))
    then have "card (\<Union> (f ` {x' \<in> X2. \<Gamma>.vert_adj x x' \<and> vert_adj y x'})) = sum card (f ` {x' \<in> X2. \<Gamma>.vert_adj x x' \<and> vert_adj y x'})" 
      using card_Union_disjoint[of "f ` {x' \<in> X2. \<Gamma>.vert_adj x x' \<and> vert_adj y x'}"] f_finite by blast
    also have "... = (\<Sum> a \<in> {x' \<in> X2. \<Gamma>.vert_adj x x' \<and> vert_adj y x'}. card (f a))" 
      using sum_card_image[OF _ f_disjoint] hX2finite finite_subset by fastforce
    also have "... \<ge> card {x' \<in> X2. \<Gamma>.vert_adj x x' \<and> vert_adj y x'} * ?\<delta>^3 / 128 * card Y" 
      using sum_mono[of "{x' \<in> X2. \<Gamma>.vert_adj x x' \<and> vert_adj y x'}" "(\<lambda> a. ?\<delta>^3 / 128 * card Y)" "(\<lambda> a. card (f a))"] 
        card_f_ge by auto
    finally have "card {x' \<in> X2. \<Gamma>.vert_adj x x' \<and> vert_adj y x'} * ?\<delta>^3 / 128 * card Y \<le> card {p. connecting_walk x y p \<and> walk_length p = 3}"
      using hUn_le by linarith
    then have "(?\<delta> ^ 3 / 128 * (card Y)) * card {x' \<in> X2. \<Gamma>.vert_adj x x' \<and> vert_adj y x'} \<le> card {p. connecting_walk x y p \<and> walk_length p = 3}"
      by argo
    then show "(?\<delta> ^ 3 / 128 * (card Y)) * ((?\<delta> / 8) * (card X2)) \<le> card {p. connecting_walk x y p \<and> walk_length p = 3}" 
      using hX2adjcard[OF hx hy] hYpos mult_left_mono h\<delta>3pos mult_pos_pos
      by (smt (verit, del_insts))
  qed
  moreover have hX2cardX: "card X2 \<ge> (?\<delta> ^2 / 8) *(card X)" 
  proof-
    have "card X2 \<ge> (H.edge_density ?X1 Y / sqrt 2) * (card ?X1)" 
      using hX2card by (simp add: algebra_simps)
    moreover have "(H.edge_density ?X1 Y / sqrt 2) * (card ?X1) \<ge> (?\<delta> / (2 * sqrt 2)) * card ?X1" 
      using hHdensity hX1cardpos by (simp add: field_simps)
    moreover have "(?\<delta> / (2 * sqrt 2)) * card ?X1 \<ge> (?\<delta> / 4) * card ?X1" 
      using sqrt2_less_2 hX1cardpos h\<delta> by (simp add: field_simps)
    moreover have "(?\<delta> / 4) * card ?X1 \<ge> (?\<delta> / 4) * (?\<delta> / 2 * card X)" 
      using hX1card h\<delta> by (simp add: field_simps)
    moreover have "(?\<delta> / 4) * (?\<delta> / 2 * card X) = (?\<delta> ^2 / 8) *(card X)" using power2_eq_square
      by (metis (no_types, opaque_lifting) Groups.mult_ac(2) Groups.mult_ac(3) divide_divide_eq_left
      num_double numeral_times_numeral times_divide_eq_left times_divide_eq_right)
    ultimately show ?thesis by linarith
  qed
  moreover have "(?\<delta> ^ 3 / 128 * (card Y)) * ((?\<delta> / 8) * (card X2)) \<ge> 
    ?\<delta> ^ 6 * card X * card Y / 2 ^ 13" 
  proof-
    have hinter: "(?\<delta> / 8) * (?\<delta> ^2 / 8 * card X) \<le> (?\<delta> / 8) * (card X2)" 
      using hX2cardX h\<delta> by (simp add: algebra_simps)
    have "?\<delta> ^ 6 * real (card X * card Y) / 2 ^ 13  = 
      ?\<delta> ^ 3 * ?\<delta> * ?\<delta> ^ 2 * real (card X * card Y) / (128 * 8 * 8)" by algebra
    also have "... = (?\<delta> ^ 3 / 128 * (card Y)) * ((?\<delta> / 8) * (?\<delta> ^2 / 8 * card X))" by auto
    also have "... \<le> (?\<delta> ^ 3 / 128 * (card Y)) * ((?\<delta> / 8) * (card X2))" 
      using hinter hYpos h\<delta> power3_eq_cube
      by (smt (verit) \<open>0 < edge_density X Y ^ 3 / 128\<close> mult_left_mono zero_compare_simps(6))
    finally show ?thesis by simp
  qed
  moreover have hX'card: "card ?X' \<ge> ?\<delta> ^ 2 * card X / 16" using hX'cardX2 hX2cardX by auto
  moreover have hX'subX: "?X' \<subseteq> X" using hX'subX2 hX2subX1 hX1X by auto
  ultimately show ?thesis using hY'card hX'card hY'subY hX'subX that
    by (smt (verit, best))
next
  assume "\<not> 0 < edge_density X Y"
  then have "edge_density X Y = 0" by (smt (verit, ccfv_threshold) edge_density_ge0)
  then show "?thesis" using that by auto
qed


text\<open>The following lemma corresponds to Lemma 2.17 in Gowers's notes \cite{Gowersnotes}. \<close>

text\<open> Note that here we have set(@{term "additive_energy A = 2 * c"} (instead of 
(@{term "additive_energy A = c"} as in the notes) and we are accordingly considering c-popular 
differences (instead of c/2-popular differences as in the notes) so that we will still have 
(@{term "\<theta> = additive_energy A / 2"}.\<close>

lemma popular_differences_card:  fixes A::"'a set" and c::real
  assumes "finite A" and "A \<subseteq> G" and "additive_energy A = 2 * c"
  shows "card (popular_diff_set c A) \<ge> c * card A"  
  (* typo in the notes, square must not be there *)

proof(cases "card A \<noteq> 0")
  assume hA: "card A \<noteq> 0"
  have hc: "c \<ge> 0" using assms additive_energy_def of_nat_0_le_iff 
    by (smt (verit, best) assms(3) divide_nonneg_nonneg of_nat_0_le_iff)
  have "(2 * c) * (card A)^3 = (\<Sum>d \<in> (differenceset A A). (f_diff d A)^2)" 
    using assms f_diff_card_quadruple_set_additive_energy by auto
  also have "...= ((\<Sum>d \<in> (popular_diff_set c A). (f_diff d A)^2))
    +((\<Sum> d \<in> ((differenceset A A) - (popular_diff_set c A)). (f_diff d A)^2))" 
    using popular_diff_set_def assms finite_minusset finite_sumset by (metis (no_types, lifting) 
      add.commute mem_Collect_eq subsetI sum.subset_diff)
  also have "... \<le> ((card (popular_diff_set c A)) * (card A)^2)
    + c * card A * ((\<Sum>d \<in> (differenceset A A - (popular_diff_set c A)) . (f_diff d A)))" 
  proof-
    have "\<forall> d \<in> ((differenceset A A) - (popular_diff_set c A)) . (f_diff d A)^2 \<le> 
      (c * (card A)) * (f_diff d A)"
    proof
     fix d assume hd1: "d \<in> differenceset A A - popular_diff_set c A"
     have hnonneg: "f_diff d A \<ge> 0" by auto
     have "\<not> popular_diff d c A" using hd1 popular_diff_set_def by blast
     from this have "f_diff d A \<le> c * card A" using popular_diff_def by auto
     thus "real ((f_diff d A)\<^sup>2) \<le> c * real (card A) * real (f_diff d A)" 
       using power2_eq_square hnonneg mult_right_mono of_nat_0 of_nat_le_iff of_nat_mult by metis
   qed
   moreover have "\<forall> d \<in> (differenceset A A) . f_diff d A \<le> (card A)^2" 
     using f_diff_def finite_minusset finite_sumset assms
     by (metis f_diff_le_card le_antisym nat_le_linear power2_nat_le_imp_le)
   ultimately have "((\<Sum>d \<in> ((differenceset A A) - popular_diff_set c A) . (f_diff d A)^2)) \<le> 
     ((\<Sum>d \<in> ((differenceset A A) - popular_diff_set c A). (c * card A) * (f_diff d A)))"
     using assms finite_minusset finite_sumset sum_distrib_left sum_mono by fastforce
   then have "((\<Sum>d \<in> ((differenceset A A) - popular_diff_set c A) . (f_diff d A)^2)) \<le>  
     (c * card A) * ((\<Sum>d \<in> ((differenceset A A) - popular_diff_set c A) . (f_diff d A)))"
     by (metis (no_types) of_nat_sum sum_distrib_left)
   moreover have "(\<Sum>d \<in> popular_diff_set c A. (f_diff d A)^2) \<le> 
    (\<Sum>d \<in> popular_diff_set c A. (card A)^2)" using f_diff_le_card assms sum_mono assms popular_diff_set_def
     by (metis (no_types, lifting) power2_nat_le_eq_le)
   moreover then have ddd: "(\<Sum>d \<in> popular_diff_set c A . (f_diff d A)^2) \<le> 
    (card (popular_diff_set c A)) * (card A)^2" 
    using sum_distrib_right by simp
    ultimately show ?thesis by linarith
  qed
  also have "...  \<le> ((card (popular_diff_set c A)) * (card A)^2) + (c * card A) * (card A)^2" 
  proof-
    have "(\<Sum>d \<in> (differenceset A A - popular_diff_set c A) . (f_diff d A)) \<le>
      (\<Sum>d \<in> differenceset A A . (f_diff d A))" using DiffD1 subsetI assms sum_mono2 
      finite_minusset finite_sumset zero_le by metis
    then have "(c * card A) * ((\<Sum>d \<in> (differenceset A A - popular_diff_set c A). (f_diff d A))) 
      \<le> (c * card A) * (card A)^2" 
      using f_diff_card hc le0 mult_left_mono of_nat_0 of_nat_mono zero_le_mult_iff assms by metis
    then show ?thesis by linarith 
  qed
  finally have "(2 * c) * (card A)^3  \<le> ((card (popular_diff_set c A)) * (card A)^2) + 
    (c * card A) * (card A)^2" by linarith
  then have "(card (popular_diff_set c A)) \<ge>
    ((2 * c) * (card A)^3 - (c * card A) * (card A)^2)/((card A)^2)"
    using hA by (simp add: field_simps)
  moreover have "((2 * c)* (card A)^3 - (c * card A) * (card A)^2)/((card A)^2) = 2 * c * card A - c * card A" 
    using hA by (simp add: power2_eq_square power3_eq_cube)
  ultimately show ?thesis by linarith
next
  assume "\<not> card A \<noteq> 0"
  thus ?thesis by auto
qed


text\<open>The following lemma corresponds to Lemma 2.18 in Gowers's notes \cite{Gowersnotes}. It includes the key argument
of the main proof and its proof applies Lemmas 2.16 (@{term walks_of_length_3_subsets_bipartite})
and 2.17 (@{term popular_differences_card}). In the proof we will use an appropriately defined
bipartite graph as an intermediate/auxiliary construct so as to apply lemma 
@{term walks_of_length_3_subsets_bipartite}. As each vertex set of the bipartite graph is constructed
to be a copy of a finite subset of an Abelian group, we need flexibility regarding types, which is 
what prompted the introduction and use of the new graph theory library \cite{Undirected_Graph_Theory-AFP} (that does not impose any type 
restrictions e.g. by representing vertices as natural numbers). \<close>

lemma obtains_subsets_differenceset_card_bound:  
  fixes A::"'a set" and c::real 
  assumes "finite A"  and "c>0"  and "A \<noteq> {}" and "A \<subseteq> G" and "additive_energy A = 2 * c"
  obtains B and A' where "B \<subseteq> A" and "B \<noteq> {}" and "card B \<ge> c^4 * card A / 16"
  and "A' \<subseteq> A" and "A' \<noteq> {}" and "card A' \<ge> c^2 * card A / 4"
  and "card (differenceset A' B) \<le> 2^13 * card A / c^15"

proof-
  let ?X = "A \<times> {0:: nat}" (* Is this the best way to tag? *)
  let ?Y = "A \<times> {1:: nat}"
  let ?E = "mk_edge ` {(x, y)| x y. x \<in> ?X \<and> y \<in> ?Y \<and> (popular_diff (fst y \<ominus> fst x) c A)}"
  interpret H: fin_bipartite_graph "?X \<union> ?Y" ?E ?X ?Y
  proof (unfold_locales, auto simp add: partition_on_def assms(3) assms(1) disjoint_def)
    show "{} = A \<times> {0} \<Longrightarrow> False" using assms(3) by auto
  next
    show "{} = A \<times> {Suc 0} \<Longrightarrow> False" using assms(3) by auto
  next
    show "A \<times> {0} = A \<times> {Suc 0} \<Longrightarrow> False" using assms(3) by fastforce
  next
    fix x y assume "x \<in> A" and "y \<in> A" and "popular_diff (y \<ominus> x) c A"
    thus "{(x, 0), (y, Suc 0)} \<in> all_bi_edges (A \<times> {0}) (A \<times> {Suc 0})" 
      using all_bi_edges_def[of "A \<times> {0}" "A \<times> {Suc 0}"]
      by (simp add: in_mk_edge_img)
  qed
  have edges1: "\<forall> a \<in> A. \<forall> b \<in> A. ({(a, 0), (b, 1)} \<in> ?E \<longleftrightarrow> popular_diff (b \<ominus> a) c A)"
    by (auto simp add: in_mk_uedge_img_iff)
  have hXA: "card A = card ?X" by (simp add: card_cartesian_product)
  have hYA: "card A = card ?Y" by (simp add: card_cartesian_product) 
  have hA: "card A \<noteq> 0" using assms card_0_eq by blast
  have edge_density: "H.edge_density ?X ?Y \<ge> c^2"
  proof-
    define f:: "'a \<Rightarrow> ('a \<times> nat) edge set" where "f \<equiv> (\<lambda> x. {{(a, 0), (b, 1)} | a b. 
      a \<in> A \<and> b \<in> A \<and> b \<ominus> a = x})"
    have f_disj: "pairwise (\<lambda> s t. disjnt (f s) (f t)) (popular_diff_set c A)" 
    proof (intro pairwiseI)
      fix x y assume hx: "x \<in> popular_diff_set c A" and hy: "y \<in> popular_diff_set c A" 
        and hxy: "x \<noteq> y" 
      show "disjnt (f x) (f y)"
      proof-
        have "\<forall>a. \<not> (a \<in> f x \<and> a \<in> f y)"
        proof (intro allI notI)
          fix a assume "a \<in> f x \<and> a \<in> f y"
          then obtain z w where hazw: "a = {(z, 0), (w, 1)}" and hx: "{(z,0), (w, 1)} \<in> f x"
            and hy: "{(z, 0), (w, 1)} \<in> f y" using f_def by blast
          have "w \<ominus> z = x" using f_def hx by (simp add: doubleton_eq_iff)
          moreover have "w \<ominus> z = y" using f_def hy by (simp add: doubleton_eq_iff)
          ultimately show "False" using hxy by auto
        qed
        thus ?thesis using disjnt_iff by auto
      qed
    qed
    have f_sub_edges: "\<forall> d \<in> popular_diff_set c A. (f d) \<subseteq> ?E"
      using popular_diff_set_def f_def edges1 by auto
    have f_union_sub: "(\<Union> d \<in> popular_diff_set c A. (f d)) \<subseteq> ?E" using popular_diff_set_def 
      f_def edges1 by auto
    have f_disj2: "disjoint (f ` (popular_diff_set c A))" using f_disj 
      pairwise_image[of "disjnt" "f" "popular_diff_set c A"] by (simp add: pairwise_def) 
    have f_finite: "\<And>B. B \<in> f ` popular_diff_set c A \<Longrightarrow> finite B"
      using finite_subset f_sub_edges H.fin_edges by auto
    have card_eq_f_diff: "\<forall> d \<in> popular_diff_set c A. card (f d) = f_diff d A"
    proof
      fix d assume "d \<in> popular_diff_set c A"
      define g:: "('a \<times> 'a) \<Rightarrow> ('a \<times> nat) edge" where "g = (\<lambda> (a, b). {(b, 0), (a, 1)})"
      have g_inj: "inj_on g {(a, b) | a b. a \<in> A \<and> b \<in> A \<and> a \<ominus> b = d}"
      proof (intro inj_onI)
        fix x y assume "x \<in> {(a, b) |a b. a \<in> A \<and> b \<in> A \<and> a \<ominus> b = d}" and 
          "y \<in> {(a, b) |a b. a \<in> A \<and> b \<in> A \<and> a \<ominus> b = d}" and hg: "g x = g y"
        then obtain a1 a2 b1 b2  where hx: "x = (a1, a2)" and hy: "y = (b1, b2)"  by blast
        thus "x = y" using g_def hg hx hy by (simp add: doubleton_eq_iff)
      qed
      have g_image: "g ` {(a, b) |a b. a \<in> A \<and> b \<in> A \<and> a \<ominus> b = d} = f d" using f_def g_def by auto
      show "card (f d) = f_diff d A" using card_image g_inj g_image f_diff_def by fastforce
    qed
    have "c ^ 2 * (card A) ^ 2 = c * (card A) * (c * (card A))" using power2_eq_square
      by (metis of_nat_power power_mult_distrib)
    also have "... \<le> (card (popular_diff_set c A)) * (c * (card A))" 
      using assms popular_differences_card hA by force  
    also have "... \<le> (\<Sum> d \<in> popular_diff_set c A. f_diff d A)" using sum_mono popular_diff_set_def
      popular_diff_def by (smt (verit, ccfv_SIG) mem_Collect_eq of_nat_sum of_real_of_nat_eq 
      sum_constant)  
    also have "... = (\<Sum> d \<in> popular_diff_set c A. card (f d))"
      using card_eq_f_diff sum.cong by auto
    also have "... = sum card (f ` (popular_diff_set c A))"
      using f_disj sum_card_image[of "popular_diff_set c A" "f"] popular_diff_set_def 
        finite_minusset finite_sumset assms(1) finite_subset by auto
    also have "... = card (\<Union> d \<in> popular_diff_set c A. (f d))"
      using card_Union_disjoint[of "f ` (popular_diff_set c A)"] f_disj2 f_finite by auto
    also have "... \<le> card ?E" using card_mono f_union_sub H.fin_edges by auto
    finally have "c ^ 2 * (card A) ^ 2 \<le> card ?E" by linarith
    then have "c ^ 2 * (card A) ^ 2 \<le> card (H.all_edges_between ?X ?Y)"
      using H.card_edges_between_set by auto
    moreover have "H.edge_density ?X ?Y = card (H.all_edges_between ?X ?Y) / (card A) ^ 2" 
      using  H.edge_density_def power2_eq_square hXA hYA
      by (smt (verit, best))
    ultimately have "(c ^ 2 * (card A) ^ 2) / (card A) ^ 2 \<le> H.edge_density ?X ?Y" using hA 
      divide_le_cancel by (smt (verit, del_insts) H.edge_density_ge0 \<open>c\<^sup>2 * real ((card A)\<^sup>2) = 
        c * real (card A) * (c * real (card A))\<close> divide_divide_eq_right zero_le_divide_iff)
    thus ?thesis using hA assms(2) by auto
  qed
  obtain X' and Y' where X'sub: "X' \<subseteq> ?X" and Y'sub: "Y' \<subseteq> ?Y" and
    hX': "card X' \<ge> (H.edge_density ?X ?Y)^2 * (card ?X)/16" and
    hY': "card Y' \<ge> (H.edge_density ?X ?Y) * (card ?Y)/4" and
    hwalks: "\<forall> x \<in> X'. \<forall> y \<in> Y'. card ({p. H.connecting_walk x y p \<and> H.walk_length p = 3}) 
    \<ge> (H.edge_density ?X ?Y)^6 * card ?X * card ?Y / 2^13"
    using H.walks_of_length_3_subsets_bipartite \<open>c>0\<close> by auto
  have "((c^2)^2) * (card A) \<le> (H.edge_density ?X ?Y)^2 * (card A)"
    using edge_density assms(2) hA power_mono zero_le_power2 mult_le_cancel_right
    by (smt (verit) of_nat_less_of_nat_power_cancel_iff of_nat_zero_less_power_iff 
      power2_less_eq_zero_iff power_0_left)
  then have cardX': "card X' \<ge> (c^4) * (card A)/16" using hX' divide_le_cancel hXA by fastforce
  have "c^2 * (card A) / 4 \<le> (H.edge_density ?X ?Y) * card ?Y / 4" using hYA hA edge_density 
      mult_le_cancel_right by simp
  then have cardY': "card Y' \<ge> c^2 * (card A)/4" using hY' by linarith
  have "(H.edge_density ?X ?Y)^6 * (card ?X * card ?Y)/ 2^13 \<ge> (c^2)^6 * ((card A)^2) / 2^13" using
  hXA hYA power2_eq_square edge_density divide_le_cancel mult_le_cancel_right hA
    by (smt (verit, ccfv_SIG) of_nat_power power2_less_0 power_less_imp_less_base zero_le_power)
  then have card_walks: "\<forall> x \<in> X'. \<forall> y \<in> Y'. 
    card ({p. H.connecting_walk x y p \<and> H.walk_length p = 3}) \<ge> (c^12) * ((card A)^2) / 2^13" 
    using hwalks by fastforce 
  (* ?X and ?Y are subsets of the vertex set, now project down to G, giving subsets ?B and ?C of A,
  respectively*)
  let ?B = "(\<lambda> (a, b). a) ` X'"
  let ?C = "(\<lambda> (a, b). a) ` Y'"
  have hBA: "?B \<subseteq> A" and hCA: "?C \<subseteq> A" using Y'sub X'sub by auto
  have inj_on_X': "inj_on (\<lambda> (a, b). a) X'" using X'sub by (intro inj_onI) (auto)
  have inj_on_Y': "inj_on (\<lambda> (a, b). a) Y'" using Y'sub by (intro inj_onI) (auto)
  have hBX': "card ?B = card X'" and hCY': "card ?C = card Y'"
    using card_image inj_on_X' inj_on_Y' by auto 
  then have cardB: "card ?B \<ge> (c^4) * (card A)/16" and cardC: "card ?C \<ge> c^2 * (card A)/4" 
    using cardX' cardY' by auto
  have card_ineq1: "\<And> x y. x \<in> ?B \<Longrightarrow> y \<in> ?C \<Longrightarrow> card ({(z, w) | z w. z \<in> A \<and> w \<in> A \<and> 
  popular_diff (z \<ominus> x) c A \<and> popular_diff (z \<ominus> w) c A \<and> popular_diff (y \<ominus> w) c A}) \<ge> 
  (c^12) * ((card A)^2) / 2^13"
  proof-
    fix x y assume hx: "x \<in> ?B" and hy: "y \<in> ?C"
    have hxA: "x \<in> A" and hyA: "y \<in> A" using hx hy hBA hCA by auto
    define f:: "'a \<times> 'a \<Rightarrow> ('a \<times> nat) list" 
      where "f \<equiv> (\<lambda> (z, w). [(x, 0), (z, 1), (w, 0), (y, 1)])"
    have f_inj_on: "inj_on f {(z, w) |z w. z \<in> A \<and> w \<in> A \<and> popular_diff (z \<ominus> x) c A \<and>
      popular_diff (z \<ominus> w) c A \<and> popular_diff (y \<ominus> w) c A}" using f_def by (intro inj_onI) (auto)
    have f_image: "f ` {(z, w) |z w. z \<in> A \<and> w \<in> A \<and> popular_diff (z \<ominus> x) c A \<and>
      popular_diff (z \<ominus> w) c A \<and> popular_diff (y \<ominus> w) c A} = 
      {p. H.connecting_walk (x, 0) (y, 1) p \<and> H.walk_length p = 3}"
    proof
      show "f ` {(z, w) |z w. z \<in> A \<and> w \<in> A \<and> popular_diff (z \<ominus> x) c A \<and> 
        popular_diff (z \<ominus> w) c A \<and> popular_diff (y \<ominus> w) c A} \<subseteq> 
        {p. H.connecting_walk (x, 0) (y, 1) p \<and> H.walk_length p = 3}"
      proof
        fix p assume hp: "p \<in> f ` {(z, w) |z w. z \<in> A \<and> w \<in> A \<and> popular_diff (z \<ominus> x) c A \<and>
          popular_diff (z \<ominus> w) c A \<and> popular_diff (y \<ominus> w) c A}"
        then obtain z w where hz: "z \<in> A" and hw: "w \<in> A" and hzx: "popular_diff (z \<ominus> x) c A" and 
          hzw: "popular_diff (z \<ominus> w) c A" and hyw: "popular_diff (y \<ominus> w) c A" and 
          hp: "p = [(x, 0), (z, 1), (w, 0), (y, 1)]" using f_def hp by fast
        then have hcon: "H.connecting_walk (x, 0) (y, 1) p"
          unfolding H.connecting_walk_def H.is_walk_def 
          using hxA hyA H.vert_adj_def H.vert_adj_sym edges1 by simp
        thus "p \<in> {p. H.connecting_walk (x, 0) (y, 1) p \<and> H.walk_length p = 3}" 
            using hp H.walk_length_conv by auto
        qed
      next
        show "{p. H.connecting_walk (x, 0) (y, 1) p \<and> H.walk_length p = 3} \<subseteq> f ` {(z, w) |z w.
          z \<in> A \<and> w \<in> A \<and> popular_diff (z \<ominus> x) c A \<and> popular_diff (z \<ominus> w) c A \<and> 
          popular_diff (y \<ominus> w) c A}"
        proof(intro subsetI)
          fix p assume hp: "p \<in> {p. H.connecting_walk (x, 0) (y, 1) p \<and> H.walk_length p = 3}"
          then have len: "length p = 4" using H.walk_length_conv by auto
          have hpsub: "set p \<subseteq> A \<times> {0} \<union> A \<times> {1}" using hp H.connecting_walk_def H.is_walk_def 
            by auto
          then have fst_sub: "fst ` set p \<subseteq> A" by auto
          have h1A: "fst (p!1) \<in> A" and h2A: "fst (p!2) \<in> A" using fst_sub len by auto
          have hpnum: "p = [p!0, p!1, p!2, p!3]"
          proof (auto simp add:  list_eq_iff_nth_eq len) 
            fix k assume "k < (4:: nat)"
            then have "k = 0 \<or> k = 1 \<or> k = 2 \<or> k = 3" by auto
            thus "p ! k = [p ! 0, p ! Suc 0, p ! 2, p ! 3] ! k" by fastforce
          qed
          then have "set (H.walk_edges p) = {{p!0, p!1} , {p!1, p!2}, {p!2, p!3}}" using
            comp_sgraph.walk_edges.simps(2) comp_sgraph.walk_edges.simps(3) 
            by (metis empty_set list.simps(15))
          then have h1: "{p!0, p!1} \<in> ?E" and h2: "{p!2, p!1} \<in> ?E" and h3: "{p!2, p!3} \<in> ?E"
            using hp H.connecting_walk_def H.is_walk_def len by auto
          have hxp: "p!0 = (x, 0)" using hp len hd_conv_nth H.connecting_walk_def H.is_walk_def 
            by fastforce 
          have hyp: "p!3 = (y,1)" using hp len last_conv_nth H.connecting_walk_def H.is_walk_def 
            by fastforce
          have h1p: "p!1 = (fst (p!1), 1)"
          proof-
            have "p!1 \<in> A \<times> {0} \<union> A \<times> {1}" using hpnum hpsub 
              by (metis (no_types, lifting) insertCI list.simps(15) subsetD)
            then have hsplit: "snd (p!1) = 0 \<or> snd (p!1) = 1" by auto
            then have "snd (p!1) = 1"
            proof(cases "snd (p!1) = 0")
              case True
              then have 1: "{(x, 0), (fst (p!1), 0)} \<in> ?E" using h1 hxp doubleton_eq_iff
                by (smt (verit, del_insts) surjective_pairing)
              have hY: "(fst (p!1), 0) \<notin> ?Y" and  hX: "(x, 0) \<in> ?X" using hxA by auto
              then have 2: "{(x, 0), (fst (p!1), 0)} \<notin> ?E" using H.X_vert_adj_Y H.vert_adj_def by meson
              then show ?thesis using 1 2 by blast
            next
              case False
              then show ?thesis using hsplit by auto
            qed
            thus "(p ! 1) = (fst (p ! 1), 1)" 
              by (metis (full_types) split_pairs)
          qed
          have h2p: "p!2 = (fst (p!2), 0)"
          proof-
            have "p!2 \<in> A \<times> {0} \<union> A \<times> {1}" using hpnum hpsub
              by (metis (no_types, lifting) insertCI list.simps(15) subsetD)
            then have hsplit: "snd (p!2) = 0 \<or> snd (p!2) = 1" by auto
            then have "snd (p!2) = 0" 
            proof(cases "snd (p!2) = 1")
              case True
              then have 1: "{(fst (p!2), 1), (y, 1)} \<in> ?E" using h3 hyp doubleton_eq_iff
                by (smt (verit, del_insts) surjective_pairing)
              have hY: "(y, 1) \<notin> ?X" and hX: "(fst (p!2), 1) \<in> ?Y" using hyA h2A by auto
              then have 2: "{(fst (p!2), 1), (y, 1)} \<notin> ?E" using H.Y_vert_adj_X H.vert_adj_def
                by meson
              then show ?thesis using 1 2 by blast
            next
              case False
              then show ?thesis using hsplit by auto
            qed
            thus "(p ! 2) = (fst (p ! 2), 0)" 
              by (metis (full_types) split_pairs)
          qed
          have hpop1: "popular_diff ((fst (p!1)) \<ominus> x) c A" using edges1 h1 hxp h1p hxA h1A
            by (smt (z3))
          have hpop2: "popular_diff((fst (p!1)) \<ominus> (fst (p!2))) c A" using edges1 h2 h1p h2p h1A h2A
            by (smt (z3))
          have hpop3: "popular_diff (y \<ominus> (fst (p!2))) c A" using edges1 h3 h2p hyp hyA h2A 
            by (smt (z3))
          thus "p \<in> f ` {(z, w) |z w. z \<in> A \<and> w \<in> A \<and> popular_diff (z \<ominus> x) c A \<and>
            popular_diff (z \<ominus> w) c A \<and> popular_diff (y \<ominus> w) c A}" using f_def hpnum hxp h1p h2p hyp
            h1A h2A hpop1 hpop2 hpop3 by force
        qed
      qed
      have hx1: "(x, 0) \<in> X'" and hy2: "(y, 1) \<in> Y'"  using hx X'sub hy Y'sub by auto
      have "card {(z, w) |z w. z \<in> A \<and> w \<in> A \<and> popular_diff (z \<ominus> x) c A \<and> 
        popular_diff (z \<ominus> w) c A \<and> popular_diff (y \<ominus> w) c A} = 
        card {p. H.connecting_walk (x, 0) (y, 1) p \<and> H.walk_length p = 3}"
        using card_image f_inj_on f_image by fastforce
      thus "card {(z, w) |z w. z \<in> A \<and> w \<in> A \<and>  popular_diff (z \<ominus> x) c A \<and> 
        popular_diff (z \<ominus> w) c A \<and> popular_diff (y \<ominus> w) c A} \<ge> c ^ 12 * ((card A)^2) / 2 ^ 13"
        using hx1 hy2 card_walks by auto
  qed
  have card_ineq2: "\<And> x y z w. x \<in> ?B \<Longrightarrow> y \<in> ?C \<Longrightarrow> (z, w) \<in> {(z, w) | z w. z \<in> A \<and> w \<in> A \<and> 
    popular_diff (z \<ominus> x) c A \<and> popular_diff (z \<ominus> w) c A \<and> popular_diff (y \<ominus> w) c A} \<Longrightarrow>
    card {(p, q, r, s, t, u)| p q r s t u. p \<in> A \<and> q \<in> A \<and> r \<in> A \<and> s \<in> A \<and> t \<in> A \<and> u \<in> A \<and> 
    p \<ominus> q = z \<ominus> x \<and> r \<ominus> s = z \<ominus> w \<and> t \<ominus> u = y \<ominus> w} \<ge> c^3 * card A^3"
  proof (auto)
    fix x x2 y y2 z w assume "(x, x2) \<in> X'" and "(y, y2) \<in> Y'" and "z \<in> A" and "w \<in> A" and
      1: "popular_diff (z \<ominus> x) c A" and 2: "popular_diff (z \<ominus> w) c A" and 
      3: "popular_diff (y \<ominus> w) c A"
    define f:: "'a \<times> 'a \<times> 'a \<times> 'a \<times> 'a \<times> 'a \<Rightarrow> ('a \<times> 'a) \<times> ('a \<times> 'a) \<times> ('a \<times> 'a)" where
      "f \<equiv> (\<lambda> (p, q, r, s, t, u). ((p, q), (r, s), (t, u)))"
    (* Types ('a \<times> 'a \<times> 'a \<times> 'a \<times> 'a \<times> 'a) and  ('a \<times> 'a) \<times> ('a \<times> 'a) \<times> ('a \<times> 'a) are not
    definitionally equal, so we need to define a bijection between them *)
    have f_inj: "inj_on f {(p, q, r, s, t, u)| p q r s t u. p \<in> A \<and> q \<in> A \<and> r \<in> A \<and> s \<in> A \<and> 
      t \<in> A \<and> u \<in> A \<and> p \<ominus> q = z \<ominus> x \<and> r \<ominus> s = z \<ominus> w \<and> t \<ominus> u = y \<ominus> w}" using f_def 
      by (intro inj_onI) (auto) 
    have f_image: "f ` {(p, q, r, s, t, u)| p q r s t u. p \<in> A \<and> q \<in> A \<and> r \<in> A \<and> s \<in> A \<and> 
      t \<in> A \<and> u \<in> A \<and> p \<ominus> q = z \<ominus> x \<and> r \<ominus> s = z \<ominus> w \<and> t \<ominus> u = y \<ominus> w} = 
      {(p, q) | p q. p \<in> A \<and> q \<in> A \<and> p \<ominus> q = z \<ominus> x} \<times> 
      {(p, q) | p q. p \<in> A \<and> q \<in> A \<and> p \<ominus> q = z \<ominus> w} \<times> 
      {(p, q) | p q. p \<in> A \<and> q \<in> A \<and> p \<ominus> q = y \<ominus> w}" using f_def by force  (*slow *)
    have "card {(p, q, r, s, t, u)| p q r s t u. p \<in> A \<and> q \<in> A \<and> r \<in> A \<and> s \<in> A \<and> 
      t \<in> A \<and> u \<in> A \<and> p \<ominus> q = z \<ominus> x \<and> r \<ominus> s = z \<ominus> w \<and> t \<ominus> u = y \<ominus> w} = card ({(p, q). p \<in> A \<and> q \<in> A \<and> p \<ominus> q = z \<ominus> x} \<times>
      {(p, q). p \<in> A \<and> q \<in> A \<and> p \<ominus> q = z \<ominus> w} \<times> {(p, q). p \<in> A \<and> q \<in> A \<and> p \<ominus> q = y \<ominus> w})" 
      using card_image f_inj f_image by fastforce
    moreover have "card ({(p, q). p \<in> A \<and> q \<in> A \<and> p \<ominus> q = z \<ominus> x} \<times>
      {(p, q). p \<in> A \<and> q \<in> A \<and> p \<ominus> q = z \<ominus> w} \<times> {(p, q). p \<in> A \<and> q \<in> A \<and> p \<ominus> q = y \<ominus> w}) =
      card {(p, q) | p q. p \<in> A \<and> q \<in> A \<and> p \<ominus> q = z \<ominus> x} *
      card {(p, q) | p q. p \<in> A \<and> q \<in> A \<and> p \<ominus> q = z \<ominus> w} * 
      card {(p, q) | p q. p \<in> A \<and> q \<in> A \<and> p \<ominus> q = y \<ominus> w}"
      using card_cartesian_product3 by auto
    moreover have "c * card A \<le> card {(p, q) | p q. p \<in> A \<and> q \<in> A \<and> p \<ominus> q = z \<ominus> x}" 
      using 1 popular_diff_def f_diff_def by auto
    moreover then have "(c * card A) * (c * card A) \<le> card {(p, q) | p q. p \<in> A \<and> q \<in> A \<and> p \<ominus> q = z \<ominus> x}
      * card {(p, q) | p q. p \<in> A \<and> q \<in> A \<and> p \<ominus> q = z \<ominus> w}" 
      using 2 popular_diff_def f_diff_def mult_mono assms(2) mult_nonneg_nonneg 
        of_nat_0_le_iff of_nat_mult by fastforce
    moreover then have "(c * card A) * (c * card A) * (c * card A) \<le> card {(p, q) | p q. p \<in> A \<and> q \<in> A \<and> p \<ominus> q = z \<ominus> x}
      * card {(p, q) | p q. p \<in> A \<and> q \<in> A \<and> p \<ominus> q = z \<ominus> w} * 
      card {(p, q) | p q. p \<in> A \<and> q \<in> A \<and> p \<ominus> q = y \<ominus> w}"
      using 3 popular_diff_def f_diff_def mult_mono assms(2) mult_nonneg_nonneg of_nat_0_le_iff 
      of_nat_mult by fastforce
    moreover have "c ^ 3 * card A ^ 3 = (c * card A) * ((c * card A) * (c * card A))" 
      by (simp add: power3_eq_cube algebra_simps)
    ultimately show "c ^ 3 * real (card A) ^ 3 \<le>
      (card {(p, q, r, s, t, u) |p q r s t u. p \<in> A \<and> q \<in> A \<and> r \<in> A \<and> s \<in> A \<and> t \<in> A \<and> u \<in> A \<and> 
      p \<ominus> q = z \<ominus> x \<and> r \<ominus> s = z \<ominus> w \<and> t \<ominus> u = y \<ominus> w})" by auto
  qed
  have card_ineq3: "\<And> x y.  x \<in> ?B \<Longrightarrow> y \<in> ?C \<Longrightarrow> card (\<Union> (z, w) \<in> {(z, w) | z w. z \<in> A \<and> w \<in> A \<and> 
    popular_diff (z \<ominus> x) c A \<and> popular_diff (z \<ominus> w) c A \<and> popular_diff (y \<ominus> w) c A}. 
    {(p, q, r, s, t, u)| p q r s t u. p \<in> A \<and> q \<in> A \<and> r \<in> A \<and> s \<in> A \<and> 
    t \<in> A \<and> u \<in> A \<and> p \<ominus> q = z \<ominus> x \<and> r \<ominus> s = z \<ominus> w \<and> t \<ominus> u = y \<ominus> w}) \<ge> 
    c ^ 15 * ((card A)^5) / 2 ^ 13"
  proof-
    fix x y assume hx: "x \<in> ?B" and hy: "y \<in> ?C"
    have hxG: "x \<in> G" and hyG: "y \<in> G" using hx hy hBA hCA assms(4) by auto
    let ?f = "(\<lambda> (z, w). {(p, q, r, s, t, u) |p q r s t u. p \<in> A \<and> q \<in> A \<and>
      r \<in> A \<and> s \<in> A \<and> t \<in> A \<and> u \<in> A \<and> p \<ominus> q = z \<ominus> x \<and> r \<ominus> s = z \<ominus> w \<and> t \<ominus> u = y \<ominus> w})"
    have h_pairwise_disjnt: "pairwise (\<lambda> a b. disjnt (?f a) (?f b)) 
      {(z, w) |z w. z \<in> A \<and> w \<in> A \<and> popular_diff (z \<ominus> x) c A \<and> popular_diff (z \<ominus> w) c A \<and>
      popular_diff (y \<ominus> w) c A}" 
      proof (intro pairwiseI)
      fix a b assume "a \<in> {(z, w) |z w. z \<in> A \<and> w \<in> A \<and> popular_diff (z \<ominus> x) c A \<and> 
       popular_diff (z \<ominus> w) c A \<and> popular_diff (y \<ominus> w) c A}" "b \<in> {(z, w) |z w. z \<in> A \<and> w \<in> A \<and>
       popular_diff (z \<ominus> x) c A \<and> popular_diff (z \<ominus> w) c A \<and> popular_diff (y \<ominus> w) c A}" and 
       "a \<noteq> b" 
      then obtain a1 a2 b1 b2 where ha: "a = (a1, a2)" and hb: "b = (b1, b2)" and ha1: "a1 \<in> G" and 
        ha2: "a2 \<in> G" and hb1: "b1 \<in> G" and hb2: "b2 \<in> G" and hne: "(a1, a2) \<noteq> (b1, b2)" 
        using assms(4) by blast
      have "(\<forall>x. \<not> (x \<in> (?f a) \<and> x \<in> (?f b)))"
      proof(intro allI notI)
        fix d assume "d \<in> (?f a) \<and> d \<in> (?f b)"
        then obtain p q r s t u where "d = (p, q, r, s, t, u)" and hpq1: "p \<ominus> q = a1 \<ominus> x" and 
          htu1: "t \<ominus> u = y \<ominus> a2" and hpq2: "p \<ominus> q = b1 \<ominus> x" and htu2: "t \<ominus> u = y \<ominus> b2" 
          using ha hb by auto
        then have "y \<ominus> a2 = y \<ominus> b2" using htu1 htu2 by auto
        then have 2: "a2 = b2" using ha2 hb2 hyG 
          by (metis additive_abelian_group.inverse_closed additive_abelian_group_axioms 
            invertible invertible_inverse_inverse invertible_left_cancel)
        have 1: "a1 = b1" using hpq1 hpq2 ha1 hb1 hxG by simp
        show "False" using 1 2 hne by auto
      qed
      thus "disjnt (?f a) (?f b)" using disjnt_iff[of "(?f a)" "(?f b)"] by auto
    qed
    have hfinite_walks: "\<And> B. B \<in> ((\<lambda> (z, w). {(p, q, r, s, t, u) |p q r s t u. p \<in> A \<and>  q \<in> A \<and>
      r \<in> A \<and> s \<in> A \<and> t \<in> A \<and> u \<in> A \<and> p \<ominus> q = z \<ominus> x \<and> r \<ominus> s = z \<ominus> w \<and> t \<ominus> u = y \<ominus> w}) ` 
      {(z, w) |z w. z \<in> A \<and> w \<in> A \<and> popular_diff (z \<ominus> x) c A \<and> popular_diff (z \<ominus> w) c A \<and>
      popular_diff (y \<ominus> w) c A}) \<Longrightarrow> finite B"
    proof-
      fix B assume "B \<in> ((\<lambda> (z, w). {(p, q, r, s, t, u) |p q r s t u. p \<in> A \<and>  q \<in> A \<and>
        r \<in> A \<and> s \<in> A \<and> t \<in> A \<and> u \<in> A \<and> p \<ominus> q = z \<ominus> x \<and> r \<ominus> s = z \<ominus> w \<and> t \<ominus> u = y \<ominus> w}) ` 
        {(z, w) |z w. z \<in> A \<and> w \<in> A \<and> popular_diff (z \<ominus> x) c A \<and> popular_diff (z \<ominus> w) c A \<and>
        popular_diff (y \<ominus> w) c A})"
      then have "B \<subseteq> A \<times> A \<times> A \<times> A \<times> A \<times> A" by auto
      thus "finite B" using assms(1)
        by (auto simp add: finite_subset)
    qed
    have hdisj: "disjoint ((\<lambda> (z, w). {(p, q, r, s, t, u) |p q r s t u. p \<in> A \<and>  q \<in> A \<and>
      r \<in> A \<and> s \<in> A \<and> t \<in> A \<and> u \<in> A \<and> p \<ominus> q = z \<ominus> x \<and> r \<ominus> s = z \<ominus> w \<and> t \<ominus> u = y \<ominus> w}) ` 
      {(z, w) |z w. z \<in> A \<and> w \<in> A \<and> popular_diff (z \<ominus> x) c A \<and> popular_diff (z \<ominus> w) c A \<and>
      popular_diff (y \<ominus> w) c A})" using h_pairwise_disjnt pairwise_image[of "disjnt" "(\<lambda> (z, w). {(p, q, r, s, t, u) |p q r s t u. p \<in> A \<and>  q \<in> A \<and>
      r \<in> A \<and> s \<in> A \<and> t \<in> A \<and> u \<in> A \<and> p \<ominus> q = z \<ominus> x \<and> r \<ominus> s = z \<ominus> w \<and> t \<ominus> u = y \<ominus> w})" 
      "{(z, w) |z w. z \<in> A \<and> w \<in> A \<and> popular_diff (z \<ominus> x) c A \<and> popular_diff (z \<ominus> w) c A \<and>
      popular_diff (y \<ominus> w) c A}"] by (simp add: pairwise_def)
    have "{(z, w) |z w. z \<in> A \<and> w \<in> A \<and> popular_diff (z \<ominus> x) c A \<and> 
      popular_diff (z \<ominus> w) c A \<and> popular_diff (y \<ominus> w) c A} \<subseteq> A \<times> A" by auto
    then have hwalks_finite: "finite {(z, w) |z w. z \<in> A \<and> w \<in> A \<and> popular_diff (z \<ominus> x) c A \<and> 
      popular_diff (z \<ominus> w) c A \<and> popular_diff (y \<ominus> w) c A}" using finite_subset assms(1) 
      by fastforce
    have f_ineq: "\<forall> a \<in> {(z, w) |z w. z \<in> A \<and> w \<in> A \<and> popular_diff (z \<ominus> x) c A \<and> 
      popular_diff (z \<ominus> w) c A \<and> popular_diff (y \<ominus> w) c A}. c ^ 3 * (card A) ^ 3 \<le>
      card (?f a)" using card_ineq2 hx hy by auto
    have "c ^ 15 * ((card A)^5) / 2 ^ 13 = (c ^ 12 * (card A) ^ 2 / 2 ^ 13) *  (c ^ 3 * card A ^ 3)"
      by (simp add: algebra_simps)
      also have "... \<le> card {(z, w) |z w. z \<in> A \<and> w \<in> A \<and> popular_diff (z \<ominus> x) c A \<and> 
      popular_diff (z \<ominus> w) c A \<and> popular_diff (y \<ominus> w) c A} * (c ^ 3 * (card A) ^ 3)" 
        using card_ineq1[of "x" "y"] hx hy mult_le_cancel_right hA by (smt (verit, best) assms(2) 
        mult_pos_pos of_nat_0_less_iff of_nat_le_0_iff zero_less_power)
    also have "...  = (\<Sum> a \<in> {(z, w) |z w. z \<in> A \<and> w \<in> A \<and> popular_diff (z \<ominus> x) c A \<and> 
      popular_diff (z \<ominus> w) c A \<and> popular_diff (y \<ominus> w) c A}. (c ^ 3 * (card A) ^ 3))" by auto
    also have "... \<le> (\<Sum>a\<in>{(z, w) |z w. z \<in> A \<and> w \<in> A \<and> popular_diff (z \<ominus> x) c A \<and> 
      popular_diff (z \<ominus> w) c A \<and> popular_diff (y \<ominus> w) c A}. card (?f a))"
      using sum_mono f_ineq by (smt (verit, del_insts) of_nat_sum) 
    also have "... = sum card (?f ` {(z, w) |z w. z \<in> A \<and> w \<in> A \<and> popular_diff (z \<ominus> x) c A \<and>
      popular_diff (z \<ominus> w) c A \<and> popular_diff (y \<ominus> w) c A})"
      using sum_card_image[of "{(z, w) |z w. z \<in> A \<and> w \<in> A \<and> popular_diff (z \<ominus> x) c A \<and> 
      popular_diff (z \<ominus> w) c A \<and> popular_diff (y \<ominus> w) c A}" "?f"] h_pairwise_disjnt hwalks_finite by auto
    also have "... = card (\<Union> (z, w)\<in>{(z, w) |z w. z \<in> A \<and> w \<in> A \<and> popular_diff (z \<ominus> x) c A \<and>
      popular_diff (z \<ominus> w) c A \<and> popular_diff (y \<ominus> w) c A}. {(p, q, r, s, t, u) |p q r s t u.
      p \<in> A \<and> q \<in> A \<and> r \<in> A \<and> s \<in> A \<and> t \<in> A \<and> u \<in> A \<and> p \<ominus> q = z \<ominus> x \<and> r \<ominus> s = z \<ominus> w \<and> 
      t \<ominus> u = y \<ominus> w})" using card_Union_disjoint hfinite_walks hdisj by (metis (no_types, lifting))
    finally show "c ^ 15 * real (card A ^ 5) / 2 ^ 13 \<le> real (card (\<Union>(z, w)\<in>{(z, w) |z w.
     z \<in> A \<and> w \<in> A \<and> popular_diff (z \<ominus> x) c A \<and> popular_diff (z \<ominus> w) c A \<and> 
     popular_diff (y \<ominus> w) c A}. {(p, q, r, s, t, u) |p q r s t u. p \<in> A \<and> q \<in> A \<and> r \<in> A \<and>
     s \<in> A \<and> t \<in> A \<and> u \<in> A \<and> p \<ominus> q = z \<ominus> x \<and> r \<ominus> s = z \<ominus> w \<and> t \<ominus> u = y \<ominus> w}))" by simp
  qed
  have hdsub: "\<forall> d \<in> differenceset ?C ?B. \<exists> y \<in> ?C. \<exists> x \<in> ?B.
    (\<Union> (z, w) \<in> {(z, w) | z w. z \<in> A \<and> w \<in> A \<and> popular_diff (z \<ominus> x) c A \<and> 
    popular_diff (z \<ominus> w) c A \<and> popular_diff (y \<ominus> w) c A}. 
    {(p, q, r, s, t, u)| p q r s t u. p \<in> A \<and> q \<in> A \<and> r \<in> A \<and> s \<in> A \<and> 
    t \<in> A \<and> u \<in> A \<and> p \<ominus> q = z \<ominus> x \<and> r \<ominus> s = z \<ominus> w \<and> t \<ominus> u = y \<ominus> w}) 
    \<subseteq> {(p, q, r, s, t, u) | p q r s t u. p \<in> A \<and> q \<in> A \<and> r \<in> A \<and>
    s \<in> A \<and> t \<in> A \<and> u \<in> A \<and> d = p \<ominus> q \<ominus> r \<oplus> s \<oplus> t \<ominus> u}"
  proof
    fix d assume "d \<in> differenceset ?C ?B"
    then obtain y x where hy: "y \<in> ?C" and hx: "x \<in> ?B" and hxy: "d = y \<ominus> x" 
      using sumset_def minusset_def hBA hCA assms(4) subset_trans
      by (smt (verit, best) minusset.simps sumset.cases)
    have hxG: "x \<in> G" and hyG: "y \<in> G" using hx hy hBA hCA assms(4) by auto
    have "(\<Union>(z, w)\<in>{(z, w) |z w. z \<in> A \<and> w \<in> A \<and> popular_diff (z \<ominus> x) c A \<and> 
      popular_diff (z \<ominus> w) c A \<and> popular_diff (y \<ominus> w) c A}. {(p, q, r, s, t, u) |p q r s t u.
      p \<in> A \<and> q \<in> A \<and> r \<in> A \<and> s \<in> A \<and> t \<in> A \<and> u \<in> A \<and> p \<ominus> q = z \<ominus> x \<and> r \<ominus> s = z \<ominus> w \<and> t \<ominus> u = y \<ominus> w})
      \<subseteq> {(p, q, r, s, t, u) |p q r s t u. p \<in> A \<and> q \<in> A \<and> r \<in> A \<and> s \<in> A \<and> t \<in> A \<and> u \<in> A \<and> 
      d = p \<ominus> q \<ominus> r \<oplus> s \<oplus> t \<ominus> u}"
    proof (rule Union_least)
      fix X assume "X \<in> (\<lambda>(z, w). {(p, q, r, s, t, u) |p q r s t u.
      p \<in> A \<and> q \<in> A \<and> r \<in> A \<and> s \<in> A \<and> t \<in> A \<and> u \<in> A \<and> p \<ominus> q = z \<ominus> x \<and> r \<ominus> s = z \<ominus> w \<and> 
      t \<ominus> u = y \<ominus> w}) ` {(z, w) |z w. z \<in> A \<and> w \<in> A \<and> popular_diff (z \<ominus> x) c A \<and> 
      popular_diff (z \<ominus> w) c A \<and> popular_diff (y \<ominus> w) c A}"
      then obtain z w where hX: "X = {(p, q, r, s, t, u) |p q r s t u. p \<in> A \<and> q \<in> A \<and> r \<in> A \<and> 
        s \<in> A \<and> t \<in> A \<and> u \<in> A \<and> p \<ominus> q = z \<ominus> x \<and> r \<ominus> s = z \<ominus> w \<and> t \<ominus> u = y \<ominus> w}"
        and hz: "z \<in> A" and hw: "w \<in> A" by auto
      have hzG: "z \<in> G" and hwG: "w \<in> G" using hz hw assms(4) by auto
      have "{(p, q, r, s, t, u) |p q r s t u. p \<in> A \<and> q \<in> A \<and> r \<in> A \<and> 
        s \<in> A \<and> t \<in> A \<and> u \<in> A \<and> p \<ominus> q = z \<ominus> x \<and> r \<ominus> s = z \<ominus> w \<and> t \<ominus> u = y \<ominus> w} \<subseteq> 
        {(p, q, r, s, t, u) |p q r s t u. p \<in> A \<and> q \<in> A \<and> r \<in> A \<and> s \<in> A \<and> t \<in> A \<and> u \<in> A \<and> 
        d = p \<ominus> q \<ominus> r \<oplus> s \<oplus> t \<ominus> u}" 
      proof
        fix e assume "e \<in> {(p, q, r, s, t, u) |p q r s t u. p \<in> A \<and> q \<in> A \<and> r \<in> A \<and> s \<in> A \<and> 
          t \<in> A \<and> u \<in> A \<and> p \<ominus> q = z \<ominus> x \<and> r \<ominus> s = z \<ominus> w \<and> t \<ominus> u = y \<ominus> w}"
        then obtain p q r s t u where "p \<ominus> q = z \<ominus> x" and "r \<ominus> s = z \<ominus> w" and "t \<ominus> u = y \<ominus> w"
          and hp: "p \<in> A" and hq: "q \<in> A" and hr: "r \<in> A" and hs: "s \<in> A" and ht: "t \<in> A" 
          and hu: "u \<in> A" and he: "e = (p, q, r, s, t, u)" by blast
        then have "p \<ominus> q \<ominus> r \<oplus> s \<oplus> t \<ominus> u = (z \<ominus> x) \<ominus> (z \<ominus> w) \<oplus> (y \<ominus> w)"
          by (smt (z3) additive_abelian_group.inverse_closed additive_abelian_group_axioms assms(4)
          associative commutative_monoid.commutative commutative_monoid_axioms composition_closed
          invertible invertible_inverse_inverse monoid.inverse_composition_commute monoid_axioms subsetD)
        also have "... = (w \<ominus> x) \<oplus> (y \<ominus> w)" using hxG hyG hzG hwG associative commutative 
          inverse_composition_commute invertible_right_inverse2 by auto
        also have "... = y \<ominus> x" using hxG hwG hyG associative commutative
          by (simp add: monoid.invertible_right_inverse2 monoid_axioms)
        finally have "p \<ominus> q \<ominus> r \<oplus> s \<oplus> t \<ominus> u = d" using hxy by simp
        thus "e \<in> {(p, q, r, s, t, u) |p q r s t u. p \<in> A \<and> q \<in> A \<and> r \<in> A \<and> s \<in> A \<and> t \<in> A \<and> 
          u \<in> A \<and> d = p \<ominus> q \<ominus> r \<oplus> s \<oplus> t \<ominus> u}" using he hp hq hr hs ht hu by auto
      qed
      thus "X \<subseteq> {(p, q, r, s, t, u) |p q r s t u.
               p \<in> A \<and> q \<in> A \<and> r \<in> A \<and> s \<in> A \<and> t \<in> A \<and> u \<in> A \<and> d = p \<ominus> q \<ominus> r \<oplus> s \<oplus> t \<ominus> u}" 
        using hX by auto
    qed
    thus "\<exists>y\<in>(\<lambda>(a, b). a) ` Y'. \<exists>x\<in>(\<lambda>(a, b). a) ` X'. (\<Union>(z, w)\<in>{(z, w) |z w. z \<in> A \<and> w \<in> A \<and> 
      popular_diff (z \<ominus> x) c A \<and> popular_diff (z \<ominus> w) c A \<and> popular_diff (y \<ominus> w) c A}.
      {(p, q, r, s, t, u) |p q r s t u. p \<in> A \<and> q \<in> A \<and> r \<in> A \<and> s \<in> A \<and> t \<in> A \<and> u \<in> A \<and> 
      p \<ominus> q = z \<ominus> x \<and> r \<ominus> s = z \<ominus> w \<and> t \<ominus> u = y \<ominus> w}) \<subseteq> {(p, q, r, s, t, u) |p q r s t u.
      p \<in> A \<and> q \<in> A \<and> r \<in> A \<and> s \<in> A \<and> t \<in> A \<and> u \<in> A \<and> d = p \<ominus> q \<ominus> r \<oplus> s \<oplus> t \<ominus> u}" 
      using hx hy by meson
  qed
  have pos: "0 < c ^ 15 * real (card A ^ 5) / 2 ^ 13" using hA \<open>c>0\<close> by auto
  have "(5:: nat) \<le> 6" by auto
  then have "(card A ^ 6 / card A ^ 5) = (card A) ^ (6 - 5)" 
    using hA power_diff by (metis of_nat_eq_0_iff of_nat_power)
  then have cardApow: "(card A ^ 6 / card A ^ 5) = card A" using power_one_right by simp
  moreover have "\<forall> d \<in> differenceset ?C ?B. card {(p, q, r, s, t, u) | p q r s t u. p \<in> A \<and> q \<in> A \<and>
    r \<in> A \<and> s \<in> A \<and> t \<in> A \<and> u \<in> A \<and> (d = p \<ominus> q \<ominus> r \<oplus>  s \<oplus>  t \<ominus> u)} \<ge> c ^ 15 * (card A) ^ 5 / 2 ^13"
  proof
    fix d assume "d \<in> differenceset ?C ?B"
    then obtain x y where hy: "y \<in> ?C" and hx: "x \<in> ?B" and hsub: 
    "(\<Union> (z, w) \<in> {(z, w) | z w. z \<in> A \<and> w \<in> A \<and> popular_diff (z \<ominus> x) c A \<and> 
    popular_diff (z \<ominus> w) c A \<and> popular_diff (y \<ominus> w) c A}. 
    {(p, q, r, s, t, u)| p q r s t u. p \<in> A \<and> q \<in> A \<and> r \<in> A \<and> s \<in> A \<and> 
    t \<in> A \<and> u \<in> A \<and> p \<ominus> q = z \<ominus> x \<and> r \<ominus> s = z \<ominus> w \<and> t \<ominus> u = y \<ominus> w}) 
    \<subseteq> {(p, q, r, s, t, u) | p q r s t u. p \<in> A \<and> q \<in> A \<and> r \<in> A \<and>
    s \<in> A \<and> t \<in> A \<and> u \<in> A \<and> d = p \<ominus> q \<ominus> r \<oplus> s \<oplus> t \<ominus> u}" using hdsub by meson
    have "{(p, q, r, s, t, u) | p q r s t u. p \<in> A \<and> q \<in> A \<and> r \<in> A \<and>
    s \<in> A \<and> t \<in> A \<and> u \<in> A \<and> d = p \<ominus> q \<ominus> r \<oplus> s \<oplus> t \<ominus> u} \<subseteq> A \<times> A \<times> A \<times> A \<times> A \<times> A" by auto
    then have fin: "finite {(p, q, r, s, t, u) | p q r s t u. p \<in> A \<and> q \<in> A \<and> r \<in> A \<and>
      s \<in> A \<and> t \<in> A \<and> u \<in> A \<and> d = p \<ominus> q \<ominus> r \<oplus> s \<oplus> t \<ominus> u}" 
      using finite_subset assms(1) finite_cartesian_product by fastforce
    have "c ^ 15 * (card A) ^ 5 / 2 ^13 \<le> card (\<Union> (z, w) \<in> {(z, w) | z w. z \<in> A \<and> w \<in> A \<and> popular_diff (z \<ominus> x) c A \<and> 
    popular_diff (z \<ominus> w) c A \<and> popular_diff (y \<ominus> w) c A}. 
    {(p, q, r, s, t, u)| p q r s t u. p \<in> A \<and> q \<in> A \<and> r \<in> A \<and> s \<in> A \<and> 
    t \<in> A \<and> u \<in> A \<and> p \<ominus> q = z \<ominus> x \<and> r \<ominus> s = z \<ominus> w \<and> t \<ominus> u = y \<ominus> w})" 
      using card_ineq3 hx hy by auto
    also have "... \<le> card {(p, q, r, s, t, u) | p q r s t u. p \<in> A \<and> q \<in> A \<and> r \<in> A \<and>
    s \<in> A \<and> t \<in> A \<and> u \<in> A \<and> d = p \<ominus> q \<ominus> r \<oplus> s \<oplus> t \<ominus> u}" 
      using hsub card_mono fin by auto 
    finally show "c ^ 15 * (card A) ^ 5 / 2 ^13 \<le> card {(p, q, r, s, t, u) | p q r s t u. p \<in> A \<and> q \<in> A \<and> r \<in> A \<and>
    s \<in> A \<and> t \<in> A \<and> u \<in> A \<and> d = p \<ominus> q \<ominus> r \<oplus> s \<oplus> t \<ominus> u}" by linarith
  qed
  moreover have "pairwise (\<lambda> s t. disjnt ((\<lambda> d. {(p, q, r, s, t, u)| p q r s t u. p \<in> A \<and> q \<in> A \<and> 
    r \<in> A \<and>  s \<in> A \<and>  t \<in> A \<and>  u \<in> A \<and> (d = p \<ominus> q \<ominus> r \<oplus>  s \<oplus>  t \<ominus> u)}) s) 
    ((\<lambda> d. {(p, q, r, s, t, u)| p q r s t u. p \<in> A \<and> q \<in> A \<and> 
    r \<in> A \<and>  s \<in> A \<and>  t \<in> A \<and>  u \<in> A \<and> (d = p \<ominus> q \<ominus> r \<oplus>  s \<oplus>  t \<ominus> u)}) t)) (differenceset ?C ?B)" 
    unfolding disjnt_def by (intro pairwiseI) (auto)
  moreover have "\<forall> d \<in> differenceset ?C ?B. ((\<lambda> d. {(p, q, r, s, t, u)| p q r s t u. p \<in> A \<and> q \<in> A \<and> 
    r \<in> A \<and>  s \<in> A \<and>  t \<in> A \<and>  u \<in> A \<and> (d = p \<ominus> q \<ominus> r \<oplus>  s \<oplus>  t \<ominus> u)}) d) \<subseteq> A \<times> A \<times> A \<times> A \<times> A \<times> A"
    by blast
  ultimately have "card (differenceset ?C ?B) \<le> ((card A) ^ 6) / (c^15 * (card A)^5 /2^13)" 
    using assms(1) hA finite_cartesian_product card_cartesian_product_6[of "A"]
    pos card_le_image_div[of "A \<times> A \<times> A \<times> A \<times> A \<times> A" "(\<lambda> d. {(p, q, r, s, t, u)| p q r s t u. p \<in> A \<and> q \<in> A \<and> 
    r \<in> A \<and> s \<in> A \<and> t \<in> A \<and> u \<in> A \<and> (d = p \<ominus> q \<ominus> r \<oplus> s \<oplus> t \<ominus> u)})" "differenceset ?C ?B" 
    "(c^15 * (card A)^5 /2^13)"] by auto
  also have "... = (card A ^ 6 / card A ^ 5) / (c^15 / 2^13)" 
    using hA assms(3) field_simps by simp
  also have "... = (card A) / (c ^ 15 / 2 ^ 13)"
    using cardApow by metis
  finally have final: "card (differenceset ?C ?B) \<le> 2 ^ 13 * (1 / c ^ 15) * real (card A)"
    by argo
  have "0 < c ^ 4 * real (card A) / 16" and "0 < c ^ 2 * real (card A) / 4" using assms(2) hA by auto
  then have "?B \<noteq> {}" and "?C \<noteq> {}" using cardB cardC by auto
  then show ?thesis using hCA hBA cardC cardB final that by auto
qed


text\<open>We now show the main theorem, which is a direct application of lemma  
@{term obtains_subsets_differenceset_card_bound} and the Ruzsa triangle inequality.
(The main theorem corresponds to Corollary 2.19 in Gowers's notes \cite{Gowersnotes}.) \<close>

theorem Balog_Szemeredi_Gowers: fixes A::"'a set" and c::real
  assumes afin: "finite A" and "A \<noteq> {}" and "c>0" and "additive_energy A = 2 * c" and ass: "A \<subseteq> G"
  obtains A' where "A' \<subseteq> A" and "card A' \<ge> c^2 * card A / 4" and
    "card (differenceset A' A') \<le>  2^30 * card A / c^34"
proof-
  obtain B and A' where bss: "B \<subseteq> A" and bne: "B \<noteq> {}" and bge: "card B \<ge> (c^4) * (card A)/16"
    and a2ss: "A' \<subseteq> A"  and a2ge: "card A' \<ge> (c^2) * (card (A))/4"
    and hcardle: "card (differenceset A' B) \<le> 2^13 * card A / c^15" 
    using assms obtains_subsets_differenceset_card_bound by metis
  have Bg0: "(card B :: real) > 0" using bne afin bss infinite_super by fastforce
  have "(card  B) * card (differenceset A' A') \<le> 
    card (differenceset A' B) * card (differenceset A' B)"
    using afin a2ss bss infinite_super ass Ruzsa_triangle_ineq1 card_minusset' differenceset_commute
      sumset_subset_carrier subset_trans sumset_commute by (smt (verit, best))
  then have "card B * card (differenceset A' A') \<le> (card (differenceset A' B))^2"
    using bss bss power2_eq_square by metis
  then have "(card (differenceset A' A')) \<le> (card (differenceset A' B))^2/card B"  
    using Bg0 nonzero_mult_div_cancel_left[of "card B" "card(differenceset A' A')"]
      divide_right_mono by (smt (verit) of_nat_0 of_nat_mono real_of_nat_div4)
  moreover have "(card (differenceset A' B))^2  \<le> ((2^13) * (1/c^15)*(card A))^2"  
    using hcardle  by simp
  ultimately have "(card (differenceset A' A')) \<le> ((2^13) * (1/c^15)*(card A))^2/(card B)" 
    using pos_le_divide_eq[OF Bg0] by simp
  moreover have "(c^4) * (card A)/16 >0" 
    using assms card_0_eq by fastforce
  moreover have "((2^13) * (1/c^15) * (card A))^2/(card B) = 
    ((2^13)* (1/c^15)*(card A))^2 * (1/(card B))" by simp
  moreover have "((2^13)* (1/c^15) * (card A))^2 * (1/(card B)) \<le> 
    ((2^13) * (1/c^15) * (card A))^2/ ((c^4) * (card A)/16)" 
    using bge calculation(2, 3) frac_le less_eq_real_def zero_le_power2 by metis 
  ultimately have "(card (differenceset A' A')) \<le> ((2^13) * (1/c^15) * (card A))^2/ ((c^4) * (card A)/16)" 
    by linarith
  then have "(card (differenceset A' A')) \<le> (2^30) * (card A)/(c^34)" 
    using card_0_eq assms by (simp add: power2_eq_square)
  then show ?thesis using a2ss a2ge that by blast
qed 

text\<open>The following is an analogous version of the Balog--Szemer\'{e}di--Gowers 
Theorem for a sumset instead of a difference set. The proof is similar to that of the original
version, again using @{term obtains_subsets_differenceset_card_bound}, however, instead
of the Ruzsa triangle inequality we will use the alternative triangle inequality for sumsets  
@{term triangle_ineq_sumsets}. \<close>

theorem Balog_Szemeredi_Gowers_sumset: fixes A::"'a set" and c::real
  assumes afin: "finite A" and "A \<noteq> {}" and "c>0" and "additive_energy A = 2 * c" and ass: "A \<subseteq> G"
  obtains A' where "A' \<subseteq> A" and "card A' \<ge> c^2 * card A / 4" and 
    "card (sumset A' A') \<le> 2^30 * card A / c^34"

proof-
  obtain B and A' where bss: "B \<subseteq> A" and bne: "B \<noteq> {}" and bge: "card B \<ge> (c^4) * (card A)/16"
    and a2ss: "A' \<subseteq> A"  and a2ne: "A' \<noteq> {}" and a2ge: "card A' \<ge> (c^2) * (card (A))/4"
    and hcardle: "card (differenceset A' B) \<le> 2^13 * card A / c^15" 
    using assms obtains_subsets_differenceset_card_bound by metis
  have finA': "finite A'" and finB: "finite B" using afin a2ss bss using infinite_super by auto
  have bg0: "(card B :: real) > 0" using bne afin bss infinite_super by fastforce
  have "card (minusset B) * card (sumset A' A') \<le> 
    card (sumset (minusset B) A') * card (sumset (minusset B) A')"
    using finA' finB ass a2ss bss triangle_ineq_sumsets 
    finite_minusset minusset_subset_carrier subset_trans by metis
  then have "card B * card (sumset A' A') \<le> (card (differenceset A' B))^2"
    using card_minusset bss ass power2_eq_square
    by (metis card_minusset' subset_trans sumset_commute)
  then have "(card (sumset A' A')) \<le> (card (differenceset A' B))^2/card B"  
    using bg0 nonzero_mult_div_cancel_left[of "card B" "card(sumset A' A')"]
      divide_right_mono by (smt (verit) of_nat_0 of_nat_mono real_of_nat_div4)
  moreover have "(card (differenceset A' B))^2  \<le> ((2^13) * (1/c^15) * (card A))^2"  
    using hcardle  by simp
  ultimately have "(card (sumset A' A')) \<le> ((2^13) * (1/c^15) * (card A))^2/(card B)" 
    using pos_le_divide_eq[OF bg0] by simp
  moreover have "(c^4) * (card A)/16 >0" 
    using assms card_0_eq by fastforce
  moreover have "((2^13) * (1/c^15) * (card A))^2/(card B) = 
    ((2^13)* (1/c^15) * (card A))^2 * (1/(card B))" by simp
  moreover have "((2^13) * (1/c^15)*(card A))^2 * (1/(card B)) \<le> 
    ((2^13) * (1/c^15) * (card A))^2/ ((c^4) * (card A)/16)" using bge frac_le less_eq_real_def 
    zero_le_power2 calculation(2, 3) by metis
  ultimately have "(card (sumset A' A')) \<le> ((2^13) * (1/c^15)*(card A))^2/ ((c^4) * (card A)/16)" 
    by linarith
  then have "(card (sumset A' A')) \<le> (2^30) * (card A)/(c^34)"
    using card_0_eq assms by (simp add: power2_eq_square)
  then show ?thesis using a2ss a2ne a2ge that by blast
qed 

end
end