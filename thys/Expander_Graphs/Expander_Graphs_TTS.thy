section \<open>Setup for Types to Sets\label{sec:tts}\<close>

theory Expander_Graphs_TTS
  imports 
    Expander_Graphs_Definition     
    "HOL-Analysis.Cartesian_Space"
    "HOL-Types_To_Sets.Types_To_Sets"
begin

text \<open>This section sets up a sublocale with the assumption that there is a finite type with the same
cardinality as the vertex set of a regular graph. This allows defining the adjacency matrix for 
the graph using type-based linear algebra.

Theorems shown in the sublocale that do not refer to the local type are then lifted to the
@{locale regular_graph} locale using the Types-To-Sets mechanism.\<close>

locale regular_graph_tts = regular_graph +
  fixes n_itself :: "('n :: finite) itself"
  assumes td: "\<exists>(f :: ('n \<Rightarrow> 'a)) g. type_definition f g (verts G)"
begin

definition td_components :: "('n \<Rightarrow> 'a) \<times> ('a \<Rightarrow> 'n)" 
  where "td_components = (SOME q. type_definition (fst q) (snd q) (verts G))"

definition enum_verts where "enum_verts = fst td_components"
definition enum_verts_inv where "enum_verts_inv = snd td_components"

sublocale type_definition "enum_verts" "enum_verts_inv" "verts G"
proof -
  have 0:"\<exists>q. type_definition ((fst q)::('n \<Rightarrow> 'a)) (snd q) (verts G)"
    using td by simp
  show "type_definition enum_verts enum_verts_inv (verts G)"
    unfolding td_components_def enum_verts_def enum_verts_inv_def using someI_ex[OF 0] by simp
qed

lemma enum_verts: "bij_betw enum_verts UNIV (verts G)"
  unfolding bij_betw_def by (simp add: Rep_inject Rep_range inj_on_def)

text \<open>The stochastic matrix associated to the graph.\<close>

definition A :: "('c::field)^'n^'n" where
  "A = (\<chi> i j. of_nat (count (edges G) (enum_verts j,enum_verts i))/of_nat d)"

lemma card_n: "CARD('n) = n"
  unfolding n_def card by simp

lemma symmetric_A: "transpose A = A"
proof -
  have "A $ i $ j = A $ j $ i" for i j
    unfolding A_def count_edges arcs_betw_def using symmetric_multi_graphD[OF sym]
    by auto
  thus ?thesis
    unfolding transpose_def
    by (intro iffD2[OF vec_eq_iff] allI) auto
qed

lemma g_step_conv: 
  "(\<chi> i. g_step f (enum_verts i)) = A *v (\<chi> i. f (enum_verts i))"
proof -
  have "g_step f (enum_verts i) = (\<Sum>j\<in>UNIV. A $ i $ j * f (enum_verts j))" (is "?L = ?R") for i
  proof -
    have "?L = (\<Sum>x\<in>in_arcs G (enum_verts i). f (tail G x) / d)"
      unfolding g_step_def by simp
    also have "... = (\<Sum>x\<in>#vertices_to G (enum_verts i). f x/d)"
      unfolding verts_to_alt sum_unfold_sum_mset by (simp add:image_mset.compositionality comp_def)
    also have "... = (\<Sum>j\<in>verts G. (count (vertices_to G (enum_verts i)) j) * (f j / real d))"
      by (intro sum_mset_conv_2 set_mset_vertices_to) auto
    also have "... = (\<Sum>j\<in>verts G. (count (edges G) (j,enum_verts i)) * (f j / real d))"
      unfolding vertices_to_def count_mset_exp 
      by (intro sum.cong arg_cong[where f="real"] arg_cong2[where f="(*)"])
       (auto simp add:filter_filter_mset image_mset_filter_mset_swap[symmetric] prod_eq_iff ac_simps)
    also have "...=(\<Sum>j\<in>UNIV.(count(edges G)(enum_verts j,enum_verts i))*(f(enum_verts j)/real d))"
      by (intro sum.reindex_bij_betw[symmetric] enum_verts)
    also have "... = ?R"
      unfolding A_def by simp
    finally show ?thesis by simp
  qed
  thus ?thesis
    unfolding matrix_vector_mult_def by (intro iffD2[OF vec_eq_iff] allI) simp
qed

lemma g_inner_conv: 
  "g_inner f g = (\<chi> i. f (enum_verts i)) \<bullet> (\<chi> i. g (enum_verts i))"
  unfolding inner_vec_def g_inner_def vec_lambda_beta inner_real_def conjugate_real_def
  by (intro sum.reindex_bij_betw[symmetric] enum_verts)

lemma g_norm_conv: 
  "g_norm f = norm (\<chi> i. f (enum_verts i))"
proof -
  have "g_norm f^2 = norm (\<chi> i. f (enum_verts i))^2"
    unfolding g_norm_sq power2_norm_eq_inner g_inner_conv by simp
  thus ?thesis
    using g_norm_nonneg norm_ge_zero by simp
qed

end

lemma eg_tts_1:
  assumes "regular_graph G"
  assumes "\<exists>(f::('n::finite) \<Rightarrow> 'a) g. type_definition f g (verts G)"
  shows "regular_graph_tts TYPE('n) G"
  using assms  
  unfolding regular_graph_tts_def  regular_graph_tts_axioms_def by auto

context regular_graph 
begin

lemma remove_finite_premise_aux:
  assumes "\<exists>(Rep :: 'n  \<Rightarrow> 'a) Abs. type_definition Rep Abs (verts G)"
  shows "class.finite TYPE('n)"
proof -
  obtain Rep :: "'n \<Rightarrow> 'a" and Abs where d:"type_definition Rep Abs (verts G)"
    using assms by auto
  interpret type_definition Rep Abs "verts G"
    using d by simp
                              
  have "finite (verts G)" by simp 
  thus ?thesis
    unfolding class.finite_def univ by auto
qed

lemma remove_finite_premise: 
  "(class.finite TYPE('n) \<Longrightarrow> \<exists>(Rep :: 'n  \<Rightarrow> 'a) Abs. type_definition Rep Abs (verts G) \<Longrightarrow> PROP Q) 
  \<equiv> (\<exists>(Rep :: 'n  \<Rightarrow> 'a) Abs. type_definition Rep Abs (verts G) \<Longrightarrow> PROP Q)" 
  (is "?L \<equiv> ?R")
proof (intro Pure.equal_intr_rule)
  assume e:"\<exists>(Rep :: 'n  \<Rightarrow> 'a) Abs. type_definition Rep Abs (verts G)" and l:"PROP ?L"
  hence f: "class.finite TYPE('n)" 
    using remove_finite_premise_aux[OF e] by simp

  show "PROP ?R"
    using l[OF f] by auto
next
  assume "\<exists>(Rep :: 'n  \<Rightarrow> 'a) Abs. type_definition Rep Abs (verts G)" and l:"PROP ?R"
  show "PROP ?L"
    using l by auto
qed

end

end