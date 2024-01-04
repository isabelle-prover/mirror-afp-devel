(* Theory: Hypergraph_Colourings.thy
   Author: Chelsea Edmonds *)

section \<open>Hypergraph Colourings \<close>

theory Hypergraph_Colourings imports  "Card_Partitions.Card_Partitions"
"Hypergraph_Basics.Hypergraph_Variations" "HOL-Library.Extended_Real" 
"Girth_Chromatic.Girth_Chromatic_Misc" 
begin

subsection \<open>Function and Number extras \<close>
lemma surj_PiE: 
  assumes "f \<in> A \<rightarrow>\<^sub>E B"
  assumes "f ` A = B"
  assumes "b \<in> B"
  obtains a where "a \<in> A" and "f a = b"
  using assms(2) assms(3) by blast

lemma Stirling_gt_0: "n \<ge> k \<Longrightarrow> k \<noteq> 0 \<Longrightarrow> Stirling n k > 0"
  apply (induct n k rule: Stirling.induct, simp_all) 
  using  Stirling_same Suc_lessI gr0I zero_neq_one by (metis Suc_leI) 

lemma card_partition_on_ne: 
  assumes "card A \<ge> n"  "n\<noteq> 0" 
  shows "{P. partition_on A P \<and> card P = n} \<noteq> {}"
proof -
  have "finite A" using assms
    using card_eq_0_iff by force 
  then have "card {P. partition_on A P \<and> card P = n} > 0" 
    using card_partition_on Stirling_gt_0 assms by fastforce 
  thus ?thesis using card.empty
    by fastforce
qed

lemma enat_lt_INF:
  fixes f :: "'a \<Rightarrow> enat"
  assumes "(INF x\<in> S. f x) < t"
  obtains x where "x \<in> S" and "f x < t"
proof -
  from assms have "(INF x\<in> S. f x) \<noteq> top"
    by fastforce
  then obtain y where " y \<in> S" and "f y = (INF x \<in> S . f x)" using enat_in_INF
    by metis
  thus ?thesis using assms
    by (simp add: that) 
qed

subsection \<open>Basic Definitions \<close>

context hypergraph
begin

text \<open>Edge colourings - using older partition approach \<close>
definition edge_colouring :: "('a hyp_edge \<Rightarrow> colour) \<Rightarrow> colour set \<Rightarrow> bool" where
"edge_colouring f C \<equiv> partition_on_mset E {# {#h \<in># E . f h = c#} . c \<in># (mset_set C)#}"

(* An edge colouring where any two edges of the same colour must not share a vertex *)
definition proper_edge_colouring :: "('a hyp_edge \<Rightarrow> colour) \<Rightarrow> colour set \<Rightarrow> bool" where
"proper_edge_colouring f C \<equiv> edge_colouring f C \<and> 
  (\<forall> e1 e2 c. e1 \<in># E \<and> e2 \<in># E - {#e1#} \<and> c \<in> C \<and> f e1 = c \<and> f e2 = c \<longrightarrow> e1 \<inter> e2 = {})"

text \<open>A vertex colouring function with no edge monochromatic requirements \<close>
abbreviation vertex_colouring :: "('a \<Rightarrow> colour) \<Rightarrow> nat \<Rightarrow> bool" where
"vertex_colouring f n \<equiv> f \<in> \<V> \<rightarrow>\<^sub>E {0..<n}"

lemma vertex_colouring_union: 
  assumes "vertex_colouring f n"
  shows "\<Union> {{v \<in> \<V>. f v = c} |c. c \<in> {0..<n}} = \<V>"
  using assms by (intro subset_antisym subsetI) blast+

lemma vertex_colouring_disj: 
  assumes "vertex_colouring f n"
  assumes "p \<in> {{v \<in> \<V>. f v = c} |c. c \<in> {0..<n}}"
  assumes "p' \<in> {{v \<in> \<V>. f v = c} |c. c \<in> {0..<n}}"
  assumes "p \<noteq> p'"
  shows "p \<inter> p' = {}"
proof (rule ccontr)
  assume a: "p \<inter> p' \<noteq> {} "
  obtain c c' where "c \<in> {0..<n}" and "c' \<in> {0..<n}" "p = {v \<in> \<V>. f v = c}" and 
      "p' = {v \<in> \<V>. f v = c}" and "c \<noteq> c'" 
    using assms(4) assms(2) assms(3) a by blast 
  then obtain v where "v \<in> \<V>" and "v \<in> p" and "v \<in> p'" using a by blast
  then show False using Fun.apply_inverse
    using \<open>p = {v \<in> \<V>. f v = c}\<close> \<open>p' = {v \<in> \<V>. f v = c}\<close> assms(4) by blast 
qed

lemma vertex_colouring_n0: "\<V> \<noteq> {} \<Longrightarrow> \<not> vertex_colouring f 0"
  by auto 

lemma vertex_colouring_image:  "vertex_colouring f n \<Longrightarrow> v \<in> \<V> \<Longrightarrow> f v \<in> {0..<n}"
  using funcset_mem by blast 

lemma vertex_colouring_image_edge_ss:  "vertex_colouring f n \<Longrightarrow> e \<in># E \<Longrightarrow> f ` e \<subseteq> {0..<n}"
  using wellformed vertex_colouring_image by blast

lemma vertex_colour_edge_map_ne: "vertex_colouring f n \<Longrightarrow> e \<in># E \<Longrightarrow> f ` e \<noteq> {}"
  using blocks_nempty by simp

lemma vertex_colouring_ne: "vertex_colouring f n \<Longrightarrow> f u \<noteq> f v \<Longrightarrow> u \<noteq> v"
  by auto 

lemma vertex_colour_one: "\<V> \<noteq> {} \<Longrightarrow> vertex_colouring f 1 \<Longrightarrow> v \<in> \<V> \<Longrightarrow> f v = (0::nat)"
  using atLeastLessThan_iff less_one vertex_colouring_image by simp 

lemma vertex_colour_one_alt: 
  assumes "\<V> \<noteq> {}"
  shows "vertex_colouring f (1::nat) \<longleftrightarrow> f = (\<lambda> v \<in> \<V> . 0::nat)"
proof (intro iffI)
  assume a: "vertex_colouring f 1"
  show "f = (\<lambda>v\<in>\<V>. 0::nat) "
  proof (rule ccontr)
    assume "f \<noteq> (\<lambda>v\<in>\<V>. 0)"
    then have "\<exists> v\<in> \<V> . f v \<noteq> 0"
      using a by auto  
    thus False using vertex_colour_one assms a
      by meson 
  qed
next
  show "f = (\<lambda>v\<in>\<V>. 0) \<Longrightarrow> f \<in> \<V> \<rightarrow>\<^sub>E {0..<1}" using PiE_eq_singleton by auto
qed

lemma vertex_colouring_partition:
  assumes "vertex_colouring f n"
  assumes "f ` \<V> = {0..<n}" (* uses n colours *)
  shows "partition_on \<V> { {v \<in> \<V> . f v = c} | c. c\<in> {0..<n}}"
proof (intro partition_onI)
  fix p assume "p \<in> {{v \<in> \<V>. f v = c} |c. c \<in> {0..<n}}"
  then obtain c where peq: "p = {v \<in> \<V> . f v = c}" and cin: "c \<in> {0..<n}" by blast
  have "f \<in> \<V> \<rightarrow>\<^sub>E {0..<n}" using assms(1) by presburger 
  then obtain v where "v \<in> \<V>" and "f v = c"
    using surj_PiE[of f \<V> "{0..<n}" c] cin assms(2) by auto
  then show "p \<noteq> {}" using peq by auto
next 
  show " \<Union> {{v \<in> \<V>. f v = c} |c. c \<in> {0..<n}} = \<V>" using vertex_colouring_union assms by auto
next
  show "\<And>p p'. p \<in> {{v \<in> \<V>. f v = c} |c. c \<in> {0..<n}} \<Longrightarrow> 
    p' \<in> {{v \<in> \<V>. f v = c} |c. c \<in> {0..<n}} \<Longrightarrow> p \<noteq> p' \<Longrightarrow> p \<inter> p' = {}"
    by auto
qed

subsection \<open> Monochromatic Edges \<close>
definition mono_edge :: "('a \<Rightarrow> colour) \<Rightarrow> 'a hyp_edge \<Rightarrow> bool" where
"mono_edge f e \<equiv> \<exists> c. \<forall> v \<in> e.  f v = c" 

lemma mono_edge_single: 
  assumes "e \<in># E"
  shows "mono_edge f e \<longleftrightarrow> is_singleton (f ` e)"
  unfolding mono_edge_def 
proof (intro iffI)
  assume "\<exists>c. \<forall>v\<in>e.  f v = c"
  then obtain c where ceq: "\<And> v . v \<in> e \<Longrightarrow> f v = c" by blast
  then have "f ` e = {c}" using image_singleton assms blocks_nempty by metis 
  then show "is_singleton (f ` e)" by simp
next 
  assume "is_singleton (f ` e)"
  then obtain c where "f ` e = {c}" by (meson is_singletonE)    
  then show "\<exists>c. \<forall>v\<in>e.  f v = c" by auto
qed

definition mono_edge_col :: "('a \<Rightarrow> colour) \<Rightarrow> 'a hyp_edge \<Rightarrow> colour \<Rightarrow> bool" where
"mono_edge_col f e c \<equiv> \<forall> v \<in> e. f v = c"

lemma mono_edge_colI: "(\<And> v. v \<in> e \<Longrightarrow> f v = c) \<Longrightarrow> mono_edge_col f e c"
  unfolding mono_edge_col_def by simp

lemma mono_edge_colD: "mono_edge_col f e c \<Longrightarrow> (\<And> v. v \<in> e \<Longrightarrow> f v = c)"
  unfolding mono_edge_col_def by simp

lemma mono_edge_alt_col: "mono_edge f e \<equiv> \<exists> c. mono_edge_col f e c" 
  unfolding mono_edge_def mono_edge_col_def by auto

subsection \<open>Proper colourings \<close>
text \<open>A proper vertex colouring brings in the monochromatic edge decision. Note that
this allows for a colouring of up to $n$ colours, not precisely $n$ colours\<close>

definition is_proper_colouring :: "('a \<Rightarrow> colour) \<Rightarrow> nat \<Rightarrow> bool" where
"is_proper_colouring f n \<equiv> vertex_colouring f n \<and> (\<forall> e \<in># E. \<forall> c \<in> {0..<n}. f ` e \<noteq> {c})"

lemma is_proper_colouring_alt: "is_proper_colouring f n \<longleftrightarrow> vertex_colouring f n \<and>(\<forall> e \<in># E. \<not> is_singleton (f ` e))"
  unfolding is_proper_colouring_def using vertex_colouring_image_edge_ss 
  by (auto) (metis insert_subset is_singleton_def) 

lemma is_proper_colouring_alt2: "is_proper_colouring f n \<longleftrightarrow> vertex_colouring f n \<and>(\<forall> e \<in># E. \<not> mono_edge f e)"
  unfolding is_proper_colouring_def using vertex_colouring_image_edge_ss mono_edge_single 
    is_proper_colouring_alt is_proper_colouring_def by force 

lemma is_proper_colouringI[intro]: "vertex_colouring f n \<Longrightarrow> (\<And> e .e \<in># E \<Longrightarrow> 
    \<not> is_singleton (f ` e)) \<Longrightarrow> is_proper_colouring f n"
  using is_proper_colouring_alt by simp

lemma is_proper_colouringI2[intro]: "vertex_colouring f n \<Longrightarrow> (\<And> e .e \<in># E \<Longrightarrow> \<not> mono_edge f e) 
    \<Longrightarrow> is_proper_colouring f n"
  using is_proper_colouring_alt2 by simp

lemma is_proper_colouring_n0: "\<V> \<noteq> {} \<Longrightarrow> \<not> is_proper_colouring f 0"
  unfolding is_proper_colouring_def using vertex_colouring_n0 by auto

lemma is_proper_colouring_empty: 
  assumes "\<V> = {}"
  shows "is_proper_colouring f n \<longleftrightarrow> f = (\<lambda> x . undefined)"
  unfolding is_proper_colouring_def using PiE_empty_domain assms
  using vertex_colouring_image_edge_ss by fastforce

lemma is_proper_colouring_n1: 
  assumes "\<V> \<noteq> {}" "E \<noteq> {#}" 
  shows "\<not> is_proper_colouring f 1"
proof (rule ccontr)
  assume "\<not> \<not> is_proper_colouring f 1"
  then have vc: "vertex_colouring f 1" and em: "(\<forall> e \<in># E. \<not> mono_edge f e)"
    using is_proper_colouring_alt2 by auto
  then obtain e where ein: "e \<in># E" using assms by blast
  have "f \<in> \<V> \<rightarrow>\<^sub>E {0}" using vc by auto
  then have "\<forall> v\<in> \<V>. f v = 0"
    by simp
  then have "\<forall> v \<in> e. f v = 0"  using wellformed\<open>e \<in># E\<close> by blast
  then have "mono_edge f e" using ein mono_edge_def by auto
  then show False using em ein by simp
qed

lemma (in fin_hypergraph) is_proper_colouring_image_card: 
  assumes "\<V> \<noteq> {}" "E \<noteq> {#}" 
  assumes "n > 1"
  assumes "is_proper_colouring f n"
  shows "card (f ` \<V>) > 1"
proof (rule ccontr)
  assume "\<not> 1 < card (f ` \<V>)"
  then have a: "card (f ` \<V>) = 1"
    using assms by (meson card_0_eq finite_imageI finite_sets image_is_empty less_one linorder_neqE_nat)
  then obtain c where ceq: "f ` \<V> = {c}"
    using card_1_singletonE by blast 
  then obtain e where ein: "e \<in># E" using assms(2) by blast
  then have ss: "e \<subseteq> \<V>" using wellformed by auto
  then have "\<forall> v \<in> e. f v = c"  using ceq
    by blast 
  then have "mono_edge f e" using ein mono_edge_def by auto
  then show False using is_proper_colouring_alt2 ein
    using assms(4) by blast 
qed

text \<open> More monochromatic edges \<close>

lemma no_monochomatic_is_colouring:
  assumes "\<forall> e \<in># E . \<not> mono_edge f e"
  assumes "vertex_colouring f n"
  shows "is_proper_colouring f n"
  using assms mono_edge_single is_proper_colouringI by (auto) 

lemma ex_monochomatic_not_colouring:
  assumes "\<exists> e \<in># E . mono_edge f e"
  assumes "vertex_colouring f n"
  shows "\<not> is_proper_colouring f n"
  using assms(1) by (simp add: mono_edge_single is_proper_colouring_alt) 

lemma mono_edge_colour_obtain:
  assumes "mono_edge f e"
  assumes "vertex_colouring f n"
  assumes "e \<in># E"
  obtains c where "c \<in> {0..<n}" and "mono_edge_col f e c"
proof -
  have ss: "f ` e \<subseteq> {0..<n}" using vertex_colouring_image_edge_ss assms by simp
  obtain c where all: "\<forall> v \<in> e. f v = c" using mono_edge_def
    using assms(1) by fastforce 
  have "f ` e \<noteq> {}" using blocks_nempty by (simp add: assms(3)) 
  then have "c \<in> f ` e" using all
    by fastforce
  thus ?thesis using ss that all mono_edge_col_def by blast 
qed

text \<open> Complete proper colourings - i.e. when n colours are required \<close>

definition is_complete_proper_colouring:: "('a \<Rightarrow> colour) \<Rightarrow> nat \<Rightarrow> bool" where
"is_complete_proper_colouring f n \<equiv> is_proper_colouring f n \<and> f ` \<V> = {0..<n}"

lemma is_complete_proper_colouring_part: 
  assumes "is_complete_proper_colouring f n"
  shows "partition_on \<V> { {v \<in> \<V> . f v = c} | c. c\<in> {0..<n}}"
  using vertex_colouring_partition assms is_complete_proper_colouring_def is_proper_colouring_def 
  by auto

lemma is_complete_proper_colouring_n0: "\<V> \<noteq> {} \<Longrightarrow> \<not> is_complete_proper_colouring f 0"
  unfolding is_complete_proper_colouring_def using is_proper_colouring_n0 by simp

lemma is_complete_proper_colouring_n1: 
  assumes "\<V> \<noteq> {}" "E \<noteq> {#}" 
  shows "\<not> is_complete_proper_colouring f 1"
  unfolding is_complete_proper_colouring_def using is_proper_colouring_n1 assms by simp

lemma (in fin_hypergraph) is_proper_colouring_reduce: 
  assumes "is_proper_colouring f n"
  obtains f' where "is_complete_proper_colouring f' (card (f ` \<V>))"
proof (cases "f ` \<V> = {0..<(n::nat)}")
  case True
  then have "card (f ` \<V>) = n" by simp
  then show ?thesis using is_complete_proper_colouring_def assms
    using True that by auto 
next
  case False
  obtain g :: "nat \<Rightarrow> nat" where bij: "bij_betw g (f ` \<V>) {0..<(card (f ` \<V>))}"
    using ex_bij_betw_finite_nat finite_sets by blast
  let ?f' = "\<lambda> x . if x \<in> \<V> then (g \<circ> f) x else undefined" 
  have img: "?f' ` \<V> = {0..<card (f ` \<V>)}" using bij bij_betw_imp_surj_on image_comp
    by (smt (verit) image_cong) 
  have "is_proper_colouring ?f' (card (f ` \<V>))"
  proof (intro is_proper_colouringI)
    show "vertex_colouring ?f' (card (f ` \<V>))"
      using img by auto
  next
    fix e assume ein: "e \<in># E"
    then have ns: "\<not> is_singleton (f ` e)" using assms is_proper_colouring_alt by blast
    have ss: "(f ` e) \<subseteq> (f ` \<V>)" using wellformed
      by (simp add: ein image_mono) 
    have "e \<subseteq> \<V>" using wellformed ein by simp
    then have "?f' ` e = g ` (f ` e)" by auto
    then show "\<not> is_singleton (?f' ` e)" using bij ns ss bij_betw_singleton_image by metis 
  qed
  then show ?thesis using is_complete_proper_colouring_def img
    by (meson that) 
qed

lemma (in fin_hypergraph) two_colouring_is_complete: 
  assumes "\<V> \<noteq> {}"
  assumes "E \<noteq> {#}"
  assumes "is_proper_colouring f 2"
  shows "is_complete_proper_colouring f 2"
proof -
  have gt: "card (f ` \<V>) > 1" using is_proper_colouring_image_card assms
    using one_less_numeral_iff semiring_norm(76) by blast 
  have "f \<in> \<V> \<rightarrow>\<^sub>E {0..<2}" using is_proper_colouring_def assms(3) by auto
  then have "f ` \<V> \<subseteq> {0..<2}" by blast 
  then have "card (f ` \<V>) = 2"
    by (metis Nat.le_diff_conv2 gt leI less_one less_zeroE nat_1_add_1 order_antisym_conv 
        subset_eq_atLeast0_lessThan_card zero_less_diff)
  thus ?thesis using is_complete_proper_colouring_def assms
    by (metis \<open>f ` \<V> \<subseteq> {0..<2}\<close> plus_nat.add_0 subset_card_intvl_is_intvl) 
qed

subsection \<open>n vertex colourings \<close>

definition is_n_colourable :: "nat \<Rightarrow> bool" where
"is_n_colourable n \<equiv> \<exists> f . is_proper_colouring f n"

definition is_n_edge_colourable :: "nat \<Rightarrow> bool" where
"is_n_edge_colourable n \<equiv> \<exists> f C . card C = n \<longrightarrow> proper_edge_colouring f C"

definition all_n_vertex_colourings :: "nat \<Rightarrow> ('a \<Rightarrow> colour) set" where
"all_n_vertex_colourings n \<equiv> {f . vertex_colouring f n}"

notation all_n_vertex_colourings ("(\<C>\<^sup>_)" [502] 500)

lemma all_n_vertex_colourings_alt: "\<C>\<^sup>n = \<V> \<rightarrow>\<^sub>E {0..<n}"
  unfolding all_n_vertex_colourings_def by auto

lemma vertex_colourings_empty: "\<V> \<noteq> {} \<Longrightarrow> all_n_vertex_colourings 0 = {}"
  unfolding all_n_vertex_colourings_def using vertex_colouring_n0
  by simp 

lemma (in fin_hypergraph) vertex_colourings_fin : "finite (\<C>\<^sup>n) "
  using all_n_vertex_colourings_alt finite_PiE finite_sets by (metis finite_atLeastLessThan) 

lemma (in fin_hypergraph) count_vertex_colourings: "card (\<C>\<^sup>n) = n ^ horder"
  using all_n_vertex_colourings_alt card_funcsetE
  by (metis card_atLeastLessThan finite_sets minus_nat.diff_0) 

lemma vertex_colourings_nempty: 
  assumes "card \<V> \<ge> n"
  assumes "n \<noteq> 0"
  shows "\<C>\<^sup>n \<noteq> {}"
  using all_n_vertex_colourings_alt assms
  by (simp add: PiE_eq_empty_iff) 

lemma vertex_colourings_one: 
  assumes "\<V> \<noteq> {}"
  shows "\<C>\<^sup>1 = {\<lambda> v\<in> \<V> . 0}"
  using vertex_colour_one_alt assms
  by (simp add: all_n_vertex_colourings_def) 

lemma mono_edge_set_union:
  assumes "e \<in># E"
  shows "{f \<in> \<C>\<^sup>n . mono_edge f e} = (\<Union>c \<in> {0..<n}. {f \<in> \<C>\<^sup>n . mono_edge_col f e c})" 
proof (intro subset_antisym subsetI)
  fix g assume a1: "g \<in> {f \<in> \<C>\<^sup>n. mono_edge f e}"
  then have "vertex_colouring g n" using all_n_vertex_colourings_def by blast
  then obtain c where "c \<in> {0..<n}" and "mono_edge_col g e c" using a1 assms mono_edge_colour_obtain
    by blast 
  then show "g \<in> (\<Union>c\<in>{0..<n}. {f \<in> \<C>\<^sup>n. mono_edge_col f e c})"
    using \<open>vertex_colouring g n\<close> all_n_vertex_colourings_def by auto
next
  fix h assume "h \<in> (\<Union>c\<in>{0..<n}. {f \<in> \<C>\<^sup>n. mono_edge_col f e c})"
  then obtain c where "c \<in> {0..<n}" and "h \<in> {f \<in> \<C>\<^sup>n. mono_edge_col f e c}"
    by blast
  then show "h \<in> {f \<in> \<C>\<^sup>n. mono_edge f e}"
    using mono_edge_alt_col by blast
qed

end

text \<open> Property B set up \<close>

abbreviation (in hypergraph) has_property_B :: "bool" where
"has_property_B \<equiv> is_n_colourable 2"

abbreviation hyp_graph_order:: "'a hyp_graph \<Rightarrow> nat" where
"hyp_graph_order h \<equiv> card (hyp_verts h)"

definition not_col_n_uni_hyps:: "nat \<Rightarrow> 'a hyp_graph set"
  where "not_col_n_uni_hyps n \<equiv> { h . fin_kuniform_hypergraph_nt (hyp_verts h) (hyp_edges h) n  \<and> 
    \<not> (hypergraph.has_property_B (hyp_verts h) (hyp_edges h)) }"

definition min_edges_colouring :: "nat \<Rightarrow> 'a itself \<Rightarrow>  enat" where (* m(n)*) 
"min_edges_colouring n _ \<equiv> INF h \<in> ((not_col_n_uni_hyps n) :: 'a hyp_graph set) . enat (size (hyp_edges h))"

lemma obtains_min_edge_colouring: 
  fixes z :: "'a itself"
  assumes "min_edges_colouring n z < x"
  obtains h :: "'a hyp_graph" where "h \<in> not_col_n_uni_hyps n" and "enat (size (hyp_edges h)) < x"
proof -
  have "(INF h \<in> ((not_col_n_uni_hyps n) :: 'a hyp_graph set) . enat (size (hyp_edges h))) < x" 
    using min_edges_colouring_def[of "n" z] assms by auto
  thus ?thesis using enat_lt_INF[of "\<lambda> h. enat (size (hyp_edges h))" "not_col_n_uni_hyps n" "x"]
    using that by blast 
qed

subsection \<open>Alternate Partition Definition.\<close>
text \<open>Note that the indexed definition should be used most of the time instead \<close>
context hypergraph
begin

definition is_proper_colouring_part :: "'a set set \<Rightarrow> bool" where
"is_proper_colouring_part C \<equiv> partition_on \<V> C \<and> (\<forall> c \<in> C. \<forall> e \<in># E. \<not> e \<subseteq> c)"

definition is_n_colourable_part :: "nat \<Rightarrow> bool" where
"is_n_colourable_part n \<equiv> \<exists> C . card C = n \<longrightarrow> is_proper_colouring_part C"

abbreviation has_property_B_part :: "bool" where
"has_property_B_part \<equiv> is_n_colourable_part 2"

definition mono_edge_ss :: "'a set set \<Rightarrow> 'a hyp_edge \<Rightarrow> bool" where
"mono_edge_ss C e \<equiv> \<exists> c \<in> C. e \<subseteq> c"

lemma is_proper_colouring_partI: "partition_on \<V> C \<Longrightarrow> (\<forall> c \<in> C. \<forall> e \<in># E. \<not> e \<subseteq> c) \<Longrightarrow> 
    is_proper_colouring_part C"
  by (simp add: is_proper_colouring_part_def)

lemma no_monochomatic_is_colouring_part:
  assumes "\<forall> e \<in># E . \<not> mono_edge_ss C e"
  assumes "partition_on \<V> C"
  shows "is_proper_colouring_part C"
  using assms(1) mono_edge_ss_def by(intro is_proper_colouring_partI) (simp_all add: assms)

lemma ex_monochomatic_not_colouring_part:
  assumes "\<exists> e \<in># E . mono_edge_ss C e"
  assumes "partition_on \<V> C"
  shows "\<not> is_proper_colouring_part C"
  using assms(1) mono_edge_ss_def is_proper_colouring_part_def by auto 

definition all_n_vertex_colourings_part :: "nat \<Rightarrow> 'a set set set" where
"all_n_vertex_colourings_part n \<equiv> {C . partition_on \<V> C \<and> card C = n}"

lemma (in fin_hypergraph) all_vertex_colourings_part_fin: "finite (all_n_vertex_colourings_part n)"
  unfolding all_n_vertex_colourings_part_def is_proper_colouring_part_def 
  using finitely_many_partition_on finite_sets by fastforce 

lemma all_vertex_colourings_part_nempty: "card \<V> \<ge> n \<Longrightarrow> n \<noteq> 0 \<Longrightarrow> all_n_vertex_colourings_part n \<noteq> {}"
  unfolding all_n_vertex_colourings_part_def using card_partition_on_ne  by blast

lemma disjoint_family_on_colourings: 
  assumes "e \<in># E"
  shows "disjoint_family_on (\<lambda> c. {f \<in> \<C>\<^sup>n . mono_edge_col f e c}) {0..<n}"
    using blocks_nempty mono_edge_col_def assms by (auto intro: disjoint_family_onI)

end 

end