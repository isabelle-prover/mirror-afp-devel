(* Graph Theory Library Base 
Theory: Undirected_Graph_Basics 
Author: Chelsea Edmonds

*)

text \<open> This library aims to present a general theory for undirected graphs. The formalisation 
approach models edges as sets with two elements, and is inspired in part by the graph theory 
basics defined by Lars Noschinski in \<^cite>\<open>"noschinski_2012"\<close> which are used in \<^cite>\<open>"edmonds_szemeredis" and "edmonds_roths"\<close>. 
Crucially this library makes the definition more flexible by removing the type synonym from vertices 
to natural numbers. This is limiting in more advanced mathematical applications, where it is common 
for vertices to represent elements of some other set. It additionally extends significantly on basic
graph definitions.

The approach taken in this formalisation is the "locale-centric" approach for modelling different
graph properties, which has been successfully used in other combinatorial structure formalisations. \<close>

section \<open> Undirected Graph Theory Basics \<close>

text \<open>This first theory focuses on the basics of graph theory (vertices, edges, degree, incidence, 
neighbours etc), as well as defining a number of different types of basic graphs.
This theory draws inspiration from \<^cite>\<open>"noschinski_2012" and "edmonds_szemeredis" and "edmonds_roths"\<close> \<close>

theory Undirected_Graph_Basics imports Main "HOL-Library.Multiset" "HOL-Library.Disjoint_Sets" 
"HOL-Library.Extended_Real" "Girth_Chromatic.Girth_Chromatic_Misc"
begin

subsection \<open> Miscellaneous Extras \<close>

text \<open> Useful concepts on lists and sets \<close>
lemma distinct_tl_rev: 
  assumes "hd xs = last xs"
  shows "distinct (tl xs) \<longleftrightarrow> distinct (tl (rev xs))"
  using assms 
proof (induct xs)
  case Nil
  then show ?case by simp
next
  case (Cons a xs)
  then show ?case proof (cases "xs = []")
    case True
    then show ?thesis by simp 
  next
    case False
    then have "a = last xs"
      using Cons.prems by auto 
    then obtain xs' where "xs = xs' @ [last xs]"
      by (metis False append_butlast_last_id)
    then have tleq: "tl (rev xs) = rev (xs')"
      by (metis butlast_rev butlast_snoc rev_rev_ident) 
    have "distinct (tl (a # xs)) \<longleftrightarrow> distinct xs"  by simp
    also have "... \<longleftrightarrow> distinct (rev xs') \<and> a \<notin> set (rev xs')"
      by (metis False Nil_is_rev_conv \<open>a = last xs\<close> distinct.simps(2) distinct_rev hd_rev list.exhaust_sel tleq)    
    finally show "distinct (tl (a # xs)) \<longleftrightarrow> distinct (tl (rev (a # xs)))"
      using tleq by (simp add: False)
  qed
qed

lemma last_in_list_set:  "length xs \<ge> 1 \<Longrightarrow> last xs \<in> set (xs)"
  using dual_order.strict_trans1 last_in_set by blast

lemma last_in_list_tl_set: 
  assumes "length xs \<ge> 2"
  shows "last xs \<in> set (tl xs)"
  using assms by (induct xs) auto

lemma length_list_decomp_lt: "ys \<noteq> [] \<Longrightarrow> length (xs @zs) < length (xs@ys@zs)"
  using length_append by simp 

lemma obtains_Max:
  assumes "finite A" and "A \<noteq> {}"
  obtains x where "x \<in> A" and "Max A = x"
  using assms Max_in by blast

lemma obtains_MAX:
  assumes "finite A" and "A \<noteq> {}"
  obtains x where "x \<in> A" and "Max (f ` A) = f x"
  using obtains_Max
  by (metis (mono_tags, opaque_lifting) assms(1) assms(2) empty_is_image finite_imageI image_iff) 

lemma obtains_Min:
  assumes "finite A" and "A \<noteq> {}"
  obtains x where "x \<in> A" and "Min A = x"
  using assms Min_in by blast

lemma obtains_MIN:
  assumes "finite A" and "A \<noteq> {}"
  obtains x where "x \<in> A" and "Min (f ` A) = f x"
  using obtains_Min assms empty_is_image finite_imageI image_iff
  by (metis (mono_tags, opaque_lifting)) 

subsection \<open> Initial Set up \<close>
text \<open>For convenience and readability, some functions and type synonyms are defined outside locale context \<close>

fun mk_triangle_set :: "('a \<times> 'a \<times> 'a) \<Rightarrow> 'a set"
  where "mk_triangle_set (x, y, z) = {x,y,z}"

type_synonym 'a edge = "'a set"

(* This is preferably not needed, but may be a helpful abbreviation when working outside a locale context *)
type_synonym 'a pregraph = "('a set) \<times> ('a edge set)" 

abbreviation gverts :: "'a pregraph \<Rightarrow> 'a set" where
  "gverts H \<equiv> fst H"

abbreviation gedges :: "'a pregraph \<Rightarrow> 'a edge set" where
  "gedges H \<equiv> snd H"


fun mk_edge :: "'a \<times> 'a \<Rightarrow> 'a edge" where
   "mk_edge (u,v) = {u,v}"

text \<open>All edges is simply the set of subsets of a set S of size 2\<close>
definition "all_edges S \<equiv> {e . e \<subseteq> S \<and> card e = 2}" 
text \<open> Note, this is a different definition to Noschinski's \<^cite>\<open>"noschinski_2012"\<close> ugraph which uses 
the @{term "mk_edge"} function unnecessarily \<close>

text \<open> Basic properties of these functions \<close>
lemma all_edges_mono:
  "vs \<subseteq> ws \<Longrightarrow> all_edges vs \<subseteq> all_edges ws"
  unfolding all_edges_def by auto

lemma all_edges_alt: "all_edges S = {{x, y} | x y . x \<in> S \<and> y \<in> S \<and> x \<noteq> y}"
  unfolding all_edges_def
proof (intro subset_antisym subsetI)
  fix x assume "x \<in> {e. e \<subseteq> S \<and> card e = 2}"
  then obtain u v where "x = {u, v}" and "card {u, v} = 2" and "{u, v} \<subseteq> S"
    by (metis (mono_tags, lifting) card_2_iff mem_Collect_eq)
  then show "x \<in> {{x, y} |x y. x \<in> S \<and> y \<in> S \<and> x \<noteq> y}"
    by fastforce 
next
  show "\<And>x. x \<in> {{x, y} |x y. x \<in> S \<and> y \<in> S \<and> x \<noteq> y} \<Longrightarrow> x \<in> {e. e \<subseteq> S \<and> card e = 2}"
    by auto
qed

lemma all_edges_alt_pairs: "all_edges S = mk_edge ` {uv \<in> S \<times> S. fst uv \<noteq> snd uv}"
  unfolding all_edges_alt
proof (intro subset_antisym)
  have img: "mk_edge ` {uv \<in> S \<times> S. fst uv \<noteq> snd uv} = {mk_edge (u, v) | u v. (u, v) \<in> S \<times> S \<and> u \<noteq>v}"
    by (smt (z3) Collect_cong fst_conv prod.collapse setcompr_eq_image snd_conv)
  then show " mk_edge ` {uv \<in> S \<times> S. fst uv \<noteq> snd uv} \<subseteq> {{x, y} |x y. x \<in> S \<and> y \<in> S \<and> x \<noteq> y}"
    by auto
  show  "{{x, y} |x y. x \<in> S \<and> y \<in> S \<and> x \<noteq> y} \<subseteq> mk_edge ` {uv \<in> S \<times> S. fst uv \<noteq> snd uv}" 
    using img by simp
qed

lemma all_edges_subset_Pow: "all_edges A \<subseteq> Pow A"
  by (auto simp: all_edges_def)

lemma all_edges_disjoint:  "S \<inter> T = {} \<Longrightarrow> all_edges S \<inter> all_edges T = {}"
  by (auto simp add: all_edges_def disjoint_iff subset_eq)

lemma card_all_edges: "finite A \<Longrightarrow> card (all_edges A) = card A choose 2"
  using all_edges_def by (metis (full_types) n_subsets) 

lemma finite_all_edges: "finite S \<Longrightarrow> finite (all_edges S)"
  by (meson all_edges_subset_Pow finite_Pow_iff finite_subset)

lemma in_mk_edge_img: "(a,b) \<in> A \<or> (b,a) \<in> A \<Longrightarrow> {a,b} \<in> mk_edge ` A"
  by (auto intro: rev_image_eqI)

thm in_mk_edge_img
lemma in_mk_uedge_img_iff: "{a,b} \<in> mk_edge ` A \<longleftrightarrow> (a,b) \<in> A \<or> (b,a) \<in> A"
  by (auto simp: doubleton_eq_iff intro: rev_image_eqI)

lemma inj_on_mk_edge: "X \<inter> Y = {} \<Longrightarrow> inj_on mk_edge (X \<times> Y)"
  by (auto simp: inj_on_def doubleton_eq_iff)

definition complete_graph :: "'a set \<Rightarrow> 'a pregraph" where
"complete_graph S \<equiv> (S, all_edges S)"

definition all_edges_loops:: "'a set \<Rightarrow> 'a edge set"where
"all_edges_loops S \<equiv> all_edges S \<union> {{v} | v. v \<in> S}"

lemma all_edges_loops_alt: "all_edges_loops S = {e . e \<subseteq> S \<and> (card e = 2 \<or> card e = 1)}"
proof -
  have 1: " {{v} | v. v \<in> S} = {e . e \<subseteq> S \<and> card e = 1}"
    by (metis One_nat_def card.empty card_Suc_eq empty_iff empty_subsetI insert_subset is_singleton_altdef is_singleton_the_elem )
  have "{e . e \<subseteq> S \<and> (card e = 2 \<or> card e = 1)} = {e . e \<subseteq> S \<and> card e = 2} \<union> {e . e \<subseteq> S \<and> card e = 1}"
    by auto
  then have "{e . e \<subseteq> S \<and> (card e = 2 \<or> card e = 1)} = all_edges S \<union> {{v} | v. v \<in> S}"
    by (simp add: all_edges_def 1)
  then show ?thesis unfolding all_edges_loops_def by simp
qed

lemma loops_disjoint: "all_edges S \<inter> {{v} | v. v \<in> S} = {}"
  unfolding all_edges_def using card_2_iff 
  by fastforce

lemma all_edges_loops_ss: "all_edges S \<subseteq> all_edges_loops S" "{{v} | v. v \<in> S} \<subseteq> all_edges_loops S"
  by (simp_all add: all_edges_loops_def)

lemma finite_singletons: "finite S \<Longrightarrow> finite ({{v} | v. v \<in> S})"
  by (auto)

lemma card_singletons: 
  assumes "finite S" shows "card {{v} | v. v \<in> S} = card S" 
  using assms
proof (induct S rule: finite_induct)
  case empty
  then show ?case by simp
next
  case (insert x F)
  then have disj: "{{x}} \<inter> {{v} |v. v \<in> F} = {}" by auto
  have "{{v} |v. v \<in> insert x F} = ({{x}} \<union> {{v} |v. v \<in> F})" by auto
  then have "card {{v} |v. v \<in> insert x F} = card ({{x}} \<union> {{v} |v. v \<in> F})" by simp
  also have "... = card {{x}} + card {{v} |v. v \<in> F}" using card_Un_disjoint disj assms finite_subset
    using insert.hyps(1) by force 
  also have "... = 1 + card {{v} |v. v \<in> F}" using is_singleton_altdef by simp 
  also have "... = 1 + card F" using insert.hyps by auto
  finally show ?case using insert.hyps(1) insert.hyps(2) by force 
qed

lemma finite_all_edges_loops: "finite S \<Longrightarrow> finite (all_edges_loops S)"
  unfolding all_edges_loops_def using finite_all_edges finite_singletons by auto

lemma card_all_edges_loops: 
  assumes "finite S"
  shows "card (all_edges_loops S) = (card S) choose 2 + card S"
proof -
  have "card (all_edges_loops S) = card (all_edges S \<union> {{v} | v. v \<in> S})" 
    by (simp add: all_edges_loops_def)
  also have "... = card (all_edges S) + card {{v} | v. v \<in> S}"
    using loops_disjoint assms card_Un_disjoint[of "all_edges S" "{{v} | v. v \<in> S}"] 
      all_edges_loops_ss finite_all_edges_loops finite_subset by fastforce 
  also have "... = (card S) choose 2 + card {{v} | v. v \<in> S}" by(simp add: card_all_edges assms)
  finally show ?thesis using assms card_singletons by auto
qed

subsection \<open> Graph System Locale \<close>
text \<open> A generic incidence set system re-labeled to graph notation, where repeated edges are not allowed. 
All the definitions here do not need the "edge" size to be constrained to make sense. \<close>

locale graph_system = 
  fixes vertices :: "'a set" ("V")
  fixes edges :: "'a edge set" ("E")
  assumes wellformed: "e \<in> E \<Longrightarrow> e \<subseteq> V"
begin

(* Basic incidence and adjacency definitions *)
abbreviation gorder :: "nat" where
"gorder \<equiv> card (V)"

abbreviation graph_size :: "nat" where
"graph_size \<equiv> card E"

definition vincident :: "'a \<Rightarrow> 'a edge \<Rightarrow> bool" where
"vincident v e \<equiv> v \<in> e"

lemma incident_edge_in_wf: "e \<in> E \<Longrightarrow> vincident v e \<Longrightarrow> v \<in> V"
  using wellformed vincident_def by auto

definition incident_edges :: "'a \<Rightarrow> 'a edge set" where
"incident_edges v \<equiv>{e . e \<in> E \<and> vincident v e}"

lemma incident_edges_empty: "\<not> (v \<in> V) \<Longrightarrow> incident_edges v = {}"
  using incident_edges_def incident_edge_in_wf by auto 

lemma finite_incident_edges: "finite E \<Longrightarrow> finite (incident_edges v)"
  by (simp add: incident_edges_def)

definition edge_adj :: "'a edge \<Rightarrow> 'a edge \<Rightarrow> bool" where
"edge_adj e1 e2 \<equiv> e1 \<inter> e2 \<noteq> {} \<and> e1 \<in> E \<and> e2 \<in> E"

lemma edge_adj_inE: "edge_adj e1 e2 \<Longrightarrow> e1 \<in> E \<and> e2 \<in> E" 
  using edge_adj_def by auto

lemma edge_adjacent_alt_def: "e1 \<in> E \<Longrightarrow> e2 \<in> E \<Longrightarrow> \<exists> x . x \<in> V \<and> x \<in> e1 \<and> x \<in> e2 \<Longrightarrow> edge_adj e1 e2"
  unfolding edge_adj_def by auto

lemma wellformed_alt_fst:  "{x, y} \<in> E \<Longrightarrow> x \<in> V"
  using wellformed by auto

lemma wellformed_alt_snd:  "{x, y} \<in> E \<Longrightarrow> y \<in> V"
  using wellformed  by auto
end

text \<open>Simple constraints on a graph system may include finite and non-empty constraints \<close>
locale fin_graph_system = graph_system + 
  assumes finV: "finite V"
begin

lemma fin_edges: "finite E"
  using wellformed finV
  by (meson PowI finite_Pow_iff finite_subset subsetI) 

end

locale ne_graph_system = graph_system +
  assumes not_empty: "V \<noteq> {}"

subsection \<open> Undirected Graph with Loops \<close>
text \<open> This formalisation models a loop by a singleton set. In this case a graph has the edge
size criteria if it has edges of size 1 or 2. Notably this removes the option for an edge to be empty \<close>
locale ulgraph = graph_system +
  assumes edge_size: "e \<in> E \<Longrightarrow> card e > 0 \<and> card e \<le> 2"

begin

lemma alt_edge_size: "e \<in> E \<Longrightarrow> card e = 1 \<or> card e = 2"
  using edge_size by fastforce 

definition is_loop:: "'a edge \<Rightarrow> bool" where
"is_loop e \<equiv> card e = 1"

definition is_sedge :: "'a edge \<Rightarrow> bool" where
"is_sedge e \<equiv> card e = 2"

lemma is_edge_or_loop: "e \<in> E \<Longrightarrow> is_loop e \<or> is_sedge e"
  using alt_edge_size is_loop_def is_sedge_def by simp

lemma edges_split_loop: "E = {e \<in> E . is_loop e } \<union> {e \<in> E . is_sedge e}"
  using is_edge_or_loop by auto

lemma edges_split_loop_inter_empty: "{} = {e \<in> E . is_loop e } \<inter> {e \<in> E . is_sedge e}"
  unfolding is_loop_def is_sedge_def by auto

definition vert_adj :: "'a \<Rightarrow> 'a \<Rightarrow> bool" where \<comment> \<open> Neighbor in graph from Roth \cite{edmonds_roths}\<close>
"vert_adj v1 v2 \<equiv> {v1, v2} \<in> E"

lemma vert_adj_sym: "vert_adj v1 v2 \<longleftrightarrow> vert_adj v2 v1"
  unfolding vert_adj_def by (simp_all add: insert_commute)

lemma vert_adj_imp_inV: "vert_adj v1 v2 \<Longrightarrow> v1 \<in> V \<and> v2 \<in> V"
  using vert_adj_def wellformed by auto

lemma vert_adj_inc_edge_iff: "vert_adj v1 v2 \<longleftrightarrow> vincident v1 {v1, v2} \<and> vincident v2 {v1, v2} \<and> {v1, v2} \<in> E"
  unfolding vert_adj_def vincident_def by auto

lemma not_vert_adj[simp]: "\<not> vert_adj v u \<Longrightarrow> {v, u} \<notin> E"
  by (simp add: vert_adj_def)

definition neighborhood :: "'a \<Rightarrow> 'a set" where \<comment> \<open> Neighbors in Roth Development \cite{edmonds_roths}\<close>
"neighborhood x \<equiv> {v \<in> V . vert_adj x v}"

lemma neighborhood_incident: "u \<in> neighborhood v \<longleftrightarrow> {u, v} \<in> incident_edges v"
  unfolding neighborhood_def incident_edges_def
  by (smt (verit) vincident_def insert_commute insert_subset mem_Collect_eq subset_insertI vert_adj_def wellformed) 

definition neighbors_ss :: "'a \<Rightarrow> 'a set \<Rightarrow> 'a set" where
"neighbors_ss x Y \<equiv> {y \<in> Y . vert_adj x y}"

lemma vert_adj_edge_iff2: 
  assumes "v1 \<noteq> v2"
  shows "vert_adj v1 v2 \<longleftrightarrow> (\<exists> e \<in> E . vincident v1 e \<and> vincident v2 e)"
proof (intro iffI)
  show "vert_adj v1 v2 \<Longrightarrow> \<exists>e\<in>E. vincident v1 e \<and> vincident v2 e" using vert_adj_inc_edge_iff by blast
  assume "\<exists>e\<in>E. vincident v1 e \<and> vincident v2 e"
  then obtain e where ein: "e \<in> E" and "vincident v1 e" and "vincident v2 e"
  using vert_adj_inc_edge_iff assms alt_edge_size by auto 
  then have "e = {v1, v2}" using alt_edge_size assms
    by (smt (verit) card_1_singletonE card_2_iff vincident_def insertE insert_commute singletonD) 
  then show "vert_adj v1 v2" using ein vert_adj_def
    by simp 
qed

text \<open>Incident simple edges, i.e. excluding loops \<close>
definition incident_sedges :: "'a \<Rightarrow> 'a edge set" where
"incident_sedges v \<equiv> {e \<in> E . vincident v e \<and> card e = 2}"

lemma finite_inc_sedges: "finite E \<Longrightarrow> finite (incident_sedges v)"
  by (simp add: incident_sedges_def)

lemma incident_sedges_empty[simp]: "v \<notin> V \<Longrightarrow> incident_sedges v = {}"
  unfolding incident_sedges_def using vincident_def wellformed by fastforce 

definition has_loop :: "'a \<Rightarrow> bool" where
"has_loop v \<equiv> {v} \<in> E"

lemma has_loop_in_verts: "has_loop v \<Longrightarrow> v \<in> V"
  using has_loop_def wellformed by auto

lemma is_loop_set_alt: "{{v} | v . has_loop v} = {e \<in> E . is_loop e}"
proof (intro subset_antisym subsetI)
  fix x assume "x \<in> {{v} |v. has_loop v}"
  then obtain v where "x = {v}" and "has_loop v"
    by blast
  then show "x \<in> {e \<in> E. is_loop e}" using has_loop_def is_loop_def by auto
next
  fix x assume a: "x \<in>{e \<in> E. is_loop e}"
  then have "is_loop x" by blast
  then obtain v where "x = {v}" and "{v} \<in> E" using is_loop_def a
    by (metis card_1_singletonE mem_Collect_eq)
  thus "x \<in> {{v} |v. has_loop v}" using has_loop_def by simp
qed

definition incident_loops :: "'a \<Rightarrow> 'a edge set" where
"incident_loops v \<equiv> {e \<in> E. e = {v}}"

lemma card1_incident_imp_vert: "vincident v e \<and> card e = 1 \<Longrightarrow> e = {v}"
  by (metis card_1_singletonE vincident_def singleton_iff)

lemma incident_loops_alt: "incident_loops v = {e \<in> E. vincident v e \<and> card e = 1}"
  unfolding incident_loops_def using card1_incident_imp_vert vincident_def by auto 

lemma incident_loops_simp: "has_loop v \<Longrightarrow> incident_loops v = {{v}}" "\<not> has_loop v \<Longrightarrow> incident_loops v = {}"
  unfolding incident_loops_def has_loop_def by auto

lemma incident_loops_union: "\<Union> (incident_loops ` V) = {e \<in> E . is_loop e}"
proof -
  have "V = {v \<in> V. has_loop v} \<union> {v \<in> V . \<not> has_loop v}"
    by auto
  then have "\<Union> (incident_loops ` V) = \<Union> (incident_loops ` {v \<in> V. has_loop v}) \<union> 
      \<Union> (incident_loops ` {v \<in> V. \<not> has_loop v})" by auto
  also have "... = \<Union> (incident_loops ` {v \<in> V. has_loop v})" using incident_loops_simp(2) by simp
  also have "... = \<Union> ({{{v}} | v . has_loop v})" using has_loop_in_verts incident_loops_simp(1) by auto
  also have "... = ({{v} | v . has_loop v})" by auto
  finally show ?thesis using is_loop_set_alt by simp
qed

lemma finite_incident_loops: "finite (incident_loops v)"
   using incident_loops_simp by (cases "has_loop v") auto

lemma incident_loops_card: "card (incident_loops v) \<le> 1"
  by (cases "has_loop v") (simp_all add: incident_loops_simp)

lemma incident_edges_union: "incident_edges v = incident_sedges v \<union> incident_loops v"
  unfolding incident_edges_def incident_sedges_def incident_loops_alt using alt_edge_size
  by auto 

lemma incident_edges_sedges[simp]: "\<not> has_loop v \<Longrightarrow> incident_edges v = incident_sedges v"
  using incident_edges_union incident_loops_simp by auto

lemma incident_sedges_union: "\<Union> (incident_sedges ` V) = {e \<in> E . is_sedge e}"
proof (intro subset_antisym subsetI)
  fix x assume "x \<in> \<Union> (incident_sedges ` V)"
  then obtain v where "x \<in> incident_sedges v" by blast
  then show "x \<in> {e \<in> E. is_sedge e}" using incident_sedges_def is_sedge_def by auto
next
  fix x assume "x \<in> {e \<in> E. is_sedge e}"
  then have xin: "x \<in> E" and c2: "card x = 2" using is_sedge_def by auto
  then obtain v where "v \<in> x" and vin: "v \<in> V" using wellformed
    by (meson card_2_iff' subsetD) 
  then have "x \<in> incident_sedges v" unfolding incident_sedges_def vincident_def using xin c2 by auto
  then show "x \<in> \<Union> (incident_sedges ` V)" using vin by auto
qed

lemma empty_not_edge: "{} \<notin> E"
  using edge_size by fastforce

text \<open> The degree definition is complicated by loops - each loop contributes two to degree. 
This is required for basic counting properties on the degree to hold\<close>
definition degree :: "'a \<Rightarrow> nat" where
"degree v \<equiv> card (incident_sedges v) + 2 * (card (incident_loops v))"

lemma degree_no_loops[simp]: "\<not> has_loop v \<Longrightarrow> degree v = card (incident_edges v)"
  using incident_edges_sedges degree_def incident_loops_simp(2) by auto

lemma degree_none[simp]: "\<not> v  \<in> V \<Longrightarrow> degree v = 0"
  using degree_def degree_no_loops has_loop_in_verts incident_edges_sedges incident_sedges_empty by auto

lemma degree0_inc_edges_empt_iff: 
  assumes "finite E"
  shows "degree v = 0 \<longleftrightarrow> incident_edges v = {}"
proof (intro iffI)
  assume "degree v = 0"
  then have "card (incident_sedges v) + 2 * (card (incident_loops v)) = 0" using degree_def by simp
  then have "incident_sedges v = {}" and "incident_loops v = {}" 
    using degree_def incident_edges_union assms finite_incident_edges finite_incident_loops by auto 
  thus "incident_edges v = {}" using incident_edges_union by auto
next
  show "incident_edges v = {} \<Longrightarrow> degree v = 0" using incident_edges_union degree_def
    by simp 
qed

lemma incident_edges_neighbors_img: "incident_edges v = (\<lambda> u . {v, u}) ` (neighborhood v)"
proof (intro subset_antisym subsetI)
  fix x assume a: "x \<in> incident_edges v"
  then have xE: "x \<in> E" and vx: "v \<in> x" using incident_edges_def vincident_def by auto
  then obtain u where "x = {u, v}" using alt_edge_size
    by (smt (verit, best) card_1_singletonE card_2_iff insertE insert_absorb2 insert_commute singletonD) 
  then have "u \<in> neighborhood v"
    using a neighborhood_incident by blast 
  then show "x \<in> (\<lambda>u. {v, u}) ` neighborhood v" using \<open>x = {u, v}\<close> by blast 
next
  fix x assume "x \<in> (\<lambda>u. {v, u}) ` neighborhood v"
  then obtain u' where "x = {v, u'}" and "u' \<in> neighborhood v"
    by blast
  then show "x \<in> incident_edges v"
    by (simp add: insert_commute neighborhood_incident) 
qed

lemma card_incident_sedges_neighborhood: "card (incident_edges v) = card (neighborhood v)"
proof -
  have "bij_betw (\<lambda> u . {v, u}) (neighborhood v) (incident_edges v)" 
    by(intro bij_betw_imageI inj_onI, simp_all add:incident_edges_neighbors_img)(metis doubleton_eq_iff)
  thus ?thesis
    by (metis bij_betw_same_card) 
qed

lemma degree0_neighborhood_empt_iff: 
  assumes "finite E"
  shows "degree v = 0 \<longleftrightarrow> neighborhood v = {}"
  using degree0_inc_edges_empt_iff incident_edges_neighbors_img
  by (simp add: assms) 

definition is_isolated_vertex:: "'a \<Rightarrow> bool" where
"is_isolated_vertex v \<equiv> v \<in> V \<and> (\<forall> u \<in> V . \<not> vert_adj u v)"

lemma is_isolated_vertex_edge: "is_isolated_vertex v \<Longrightarrow> (\<And> e. e \<in> E \<Longrightarrow> \<not> (vincident v e))"
  unfolding is_isolated_vertex_def
  by (metis (full_types) all_not_in_conv vincident_def insert_absorb insert_iff mk_disjoint_insert 
      vert_adj_def vert_adj_edge_iff2 vert_adj_imp_inV) 

lemma is_isolated_vertex_no_loop: "is_isolated_vertex v \<Longrightarrow> \<not> has_loop v"
  unfolding has_loop_def is_isolated_vertex_def vert_adj_def by auto

lemma is_isolated_vertex_degree0: "is_isolated_vertex v \<Longrightarrow> degree v = 0"
proof -
  assume assm: "is_isolated_vertex v"
  then have "\<not> has_loop v" using is_isolated_vertex_no_loop by simp
  then have "degree v = card (incident_edges v)" using degree_no_loops by auto
  moreover have "\<And> e. e \<in> E \<Longrightarrow> \<not> (vincident v e)"
    using is_isolated_vertex_edge assm by auto
  then have "(incident_edges v) = {}" unfolding incident_edges_def by auto
  ultimately show "degree v = 0" by simp
qed

lemma iso_vertex_empty_neighborhood: "is_isolated_vertex v \<Longrightarrow> neighborhood v = {}"
  using is_isolated_vertex_def neighborhood_def
  by (metis (mono_tags, lifting) Collect_empty_eq is_isolated_vertex_edge vert_adj_inc_edge_iff) 

definition max_degree :: "nat" where
"max_degree \<equiv> Max {degree v | v. v \<in> V}"

definition min_degree :: "nat" where
"min_degree \<equiv> Min {degree v | v . v \<in> V}"

definition is_edge_between :: "'a set \<Rightarrow> 'a set \<Rightarrow> 'a edge \<Rightarrow> bool" where
"is_edge_between X Y e \<equiv> \<exists> x y. e = {x, y} \<and> x \<in> X \<and> y \<in> Y"

text \<open>All edges between two sets of vertices, @{term X} and @{term Y}, in a graph, @{term G}. 
Inspired by Szemeredi development \<^cite>\<open>"edmonds_szemeredis"\<close> and generalised here \<close>

definition all_edges_between :: "'a set \<Rightarrow> 'a set \<Rightarrow> ('a \<times> 'a) set" where
"all_edges_between X Y \<equiv> {(x, y) . x \<in> X \<and> y \<in> Y \<and> {x, y} \<in> E}"

lemma all_edges_betw_D3: "(x, y) \<in> all_edges_between X Y \<Longrightarrow> {x, y} \<in> E"
  by (simp add: all_edges_between_def)

lemma all_edges_betw_I: "x \<in> X \<Longrightarrow> y \<in> Y \<Longrightarrow> {x, y} \<in> E \<Longrightarrow> (x, y) \<in> all_edges_between X Y"
  by (simp add: all_edges_between_def)

lemma all_edges_between_subset: "all_edges_between X Y \<subseteq> X\<times>Y"
  by (auto simp: all_edges_between_def)

lemma all_edges_between_E_ss: "mk_edge ` all_edges_between X Y \<subseteq> E"
  by (auto simp add: all_edges_between_def)

lemma all_edges_between_rem_wf: "all_edges_between X Y = all_edges_between (X \<inter> V) (Y \<inter> V)"
  using wellformed by (simp add: all_edges_between_def) blast 

lemma all_edges_between_empty [simp]:
  "all_edges_between {} Z = {}" "all_edges_between Z {} = {}"
  by (auto simp: all_edges_between_def)

lemma all_edges_between_disjnt1: "disjnt X Y \<Longrightarrow> disjnt (all_edges_between X Z) (all_edges_between Y Z)"
  by (auto simp: all_edges_between_def disjnt_iff)

lemma all_edges_between_disjnt2: "disjnt Y Z \<Longrightarrow> disjnt (all_edges_between X Y) (all_edges_between X Z)"
  by (auto simp: all_edges_between_def disjnt_iff)

lemma max_all_edges_between: 
  assumes "finite X" "finite Y"
  shows "card (all_edges_between X Y) \<le> card X * card Y"
  by (metis assms card_mono finite_SigmaI all_edges_between_subset card_cartesian_product)

lemma all_edges_between_Un1:
  "all_edges_between (X \<union> Y) Z = all_edges_between X Z \<union> all_edges_between Y Z"
  by (auto simp: all_edges_between_def)

lemma all_edges_between_Un2:
  "all_edges_between X (Y \<union> Z) = all_edges_between X Y \<union> all_edges_between X Z"
  by (auto simp: all_edges_between_def)

lemma finite_all_edges_between:
  assumes "finite X" "finite Y"
  shows "finite (all_edges_between X Y)"
  by (meson all_edges_between_subset assms finite_cartesian_product finite_subset)

lemma all_edges_between_Union1:
  "all_edges_between (Union \<X>) Y = (\<Union>X\<in>\<X>. all_edges_between X Y)"
  by (auto simp: all_edges_between_def)

lemma all_edges_between_Union2:
  "all_edges_between X (Union \<Y>) = (\<Union>Y\<in>\<Y>. all_edges_between X Y)"
  by (auto simp: all_edges_between_def)

lemma all_edges_between_disjoint1:
  assumes "disjoint R"
  shows "disjoint ((\<lambda>X. all_edges_between X Y) ` R)"
  using assms by (auto simp: all_edges_between_def disjoint_def)

lemma all_edges_between_disjoint2:
  assumes "disjoint R"
  shows "disjoint ((\<lambda>Y. all_edges_between X Y) ` R)"
  using assms by (auto simp: all_edges_between_def disjoint_def)

lemma all_edges_between_disjoint_family_on1:
  assumes "disjoint R"
  shows "disjoint_family_on (\<lambda>X. all_edges_between X Y) R"
  by (metis (no_types, lifting) all_edges_between_disjnt1 assms disjnt_def disjoint_family_on_def pairwiseD)

lemma all_edges_between_disjoint_family_on2:
  assumes "disjoint R"
  shows "disjoint_family_on (\<lambda>Y. all_edges_between X Y) R"
  by (metis (no_types, lifting) all_edges_between_disjnt2 assms disjnt_def disjoint_family_on_def pairwiseD)

lemma all_edges_between_mono1:
  "Y \<subseteq> Z \<Longrightarrow> all_edges_between Y X \<subseteq> all_edges_between Z X"
  by (auto simp: all_edges_between_def)

lemma all_edges_between_mono2:
  "Y \<subseteq> Z \<Longrightarrow> all_edges_between X Y \<subseteq> all_edges_between X Z"
  by (auto simp: all_edges_between_def)

lemma inj_on_mk_edge: "X \<inter> Y = {} \<Longrightarrow> inj_on mk_edge (all_edges_between X Y)"
  by (auto simp: inj_on_def doubleton_eq_iff all_edges_between_def)

lemma all_edges_between_subset_times: "all_edges_between X Y \<subseteq> (X \<inter> \<Union>E) \<times> (Y \<inter> \<Union>E)"
  by (auto simp: all_edges_between_def)

lemma all_edges_betw_prod_def_neighbors: "all_edges_between X Y = {(x, y) \<in> X \<times> Y . vert_adj x y }"
  by (auto simp: vert_adj_def all_edges_between_def)

lemma all_edges_betw_sigma_neighbor: 
"all_edges_between X Y = (SIGMA x:X. neighbors_ss x Y)"
  by (auto simp add: all_edges_between_def neighbors_ss_def vert_adj_def)

lemma card_all_edges_betw_neighbor: 
  assumes "finite X" "finite Y"
  shows "card (all_edges_between X Y) = (\<Sum>x\<in>X. card (neighbors_ss x Y))"
  using all_edges_betw_sigma_neighbor assms by (simp add: neighbors_ss_def)

lemma all_edges_between_swap:
  "all_edges_between X Y = (\<lambda>(x,y). (y,x)) ` (all_edges_between Y X)"
  unfolding all_edges_between_def
  by (auto simp add: insert_commute image_iff split: prod.split)

lemma card_all_edges_between_commute:
  "card (all_edges_between X Y) = card (all_edges_between Y X)"
proof -
  have "inj_on (\<lambda>(x, y). (y, x)) A" for A :: "(nat*nat)set"
    by (auto simp: inj_on_def)
  then show ?thesis using all_edges_between_swap [of X Y] card_image
    by (metis swap_inj_on) 
qed

lemma all_edges_between_set: "mk_edge ` all_edges_between X Y = {{x, y}| x y. x \<in> X \<and> y \<in> Y \<and> {x, y} \<in> E}"
  unfolding all_edges_between_def 
proof (intro subset_antisym subsetI)
  fix e assume "e \<in> mk_edge ` {(x, y). x \<in> X \<and> y \<in> Y \<and> {x, y} \<in> E}"
  then obtain x y where "e = mk_edge (x, y)" and "x \<in> X" and "y \<in> Y" and "{x, y} \<in> E"
    by blast
  then show "e \<in> {{x, y} |x y. x \<in> X \<and> y \<in> Y \<and> {x, y} \<in> E}"
    by auto
next
  fix e assume "e \<in> {{x, y} |x y. x \<in> X \<and> y \<in> Y \<and> {x, y} \<in> E}"
  then obtain x y where "e ={x, y}" and "x \<in> X" and "y \<in> Y" and "{x, y} \<in> E"
    by blast
  then have "e = mk_edge (x, y)"
    by auto
  then show "e \<in> mk_edge ` {(x, y). x \<in> X \<and> y \<in> Y \<and> {x, y} \<in> E}"
    using \<open>x \<in> X\<close> \<open>y \<in> Y\<close> \<open>{x, y} \<in> E\<close> by blast
qed

subsection \<open>Edge Density\<close>

text \<open>The edge density between two sets of vertices, @{term X} and @{term Y}, in @{term G}.
      This is the same definition as taken in the Szemeredi development, generalised here \<^cite>\<open>"edmonds_szemeredis"\<close>\<close>

definition "edge_density X Y \<equiv> card (all_edges_between X Y)/(card X * card Y)"
lemma edge_density_ge0: "edge_density X Y \<ge> 0"
  by (auto simp: edge_density_def)

lemma edge_density_le1: "edge_density X Y \<le> 1"
proof (cases "finite X \<and> finite Y")
  case True
  then show ?thesis 
    using of_nat_mono [OF max_all_edges_between, of X Y]
    by (fastforce simp add: edge_density_def divide_simps)
qed (auto simp: edge_density_def)

lemma edge_density_zero:  "Y = {} \<Longrightarrow> edge_density X Y = 0" 
  by (simp add: edge_density_def)

lemma edge_density_commute: "edge_density X Y = edge_density Y X"
  by (simp add: edge_density_def card_all_edges_between_commute mult.commute)

lemma edge_density_Un:
  assumes "disjnt X1 X2" "finite X1" "finite X2" "finite Y"
  shows "edge_density (X1 \<union> X2) Y = (edge_density X1 Y * card X1 + edge_density X2 Y * card X2) / (card X1 + card X2)"
  using assms unfolding edge_density_def
  by (simp add: all_edges_between_disjnt1 all_edges_between_Un1 finite_all_edges_between card_Un_disjnt divide_simps)

lemma edge_density_eq0:
  assumes "all_edges_between A B = {}" and "X \<subseteq> A" "Y \<subseteq> B"
  shows "edge_density X Y  = 0"
proof -
  have "all_edges_between X Y = {}"
    by (metis all_edges_between_mono1 all_edges_between_mono2 assms subset_empty)
  then show ?thesis
    by (auto simp: edge_density_def)
qed

end


text \<open>A number of lemmas are limited to a finite graph \<close>
locale fin_ulgraph = ulgraph + fin_graph_system
begin

lemma card_is_has_loop_eq: "card {e \<in> E . is_loop e} = card {v \<in> V . has_loop v}"
proof -
  have "\<And> e . e \<in> E \<Longrightarrow> is_loop e \<longleftrightarrow> (\<exists> v. e = {v})" using is_loop_def
    using is_singleton_altdef is_singleton_def by blast
  define f :: "'a \<Rightarrow> 'a set"  where "f = (\<lambda> v . {v})"
  have feq: "f ` {v \<in> V . has_loop v} = {{v} | v . has_loop v}" using has_loop_in_verts f_def by auto
  have "inj_on f {v \<in> V . has_loop v}" by (simp add: f_def) 
  then have "card {v \<in> V . has_loop v} = card (f ` {v \<in> V . has_loop v})" 
    using card_image by fastforce 
  also have "... = card {{v} | v . has_loop v}" using feq by simp
  finally have "card {v \<in> V . has_loop v} = card {e \<in> E . is_loop e}" using is_loop_set_alt by simp
  thus "card {e \<in> E . is_loop e} = card {v \<in> V . has_loop v}" by simp
qed

lemma finite_all_edges_between': "finite (all_edges_between X Y)"
  using finV wellformed
  by (metis all_edges_between_rem_wf finite_Int finite_all_edges_between) 

lemma card_all_edges_between:
  assumes "finite Y"
  shows "card (all_edges_between X Y) = (\<Sum>y\<in>Y. card (all_edges_between X {y}))"
proof -
  have "all_edges_between X Y = (\<Union>y\<in>Y. all_edges_between X {y})"
    by (auto simp: all_edges_between_def)
  moreover have "disjoint_family_on (\<lambda>y. all_edges_between X {y}) Y"
    unfolding disjoint_family_on_def
    by (auto simp: disjoint_family_on_def all_edges_between_def)
  ultimately show ?thesis 
    by (simp add: card_UN_disjoint' assms finite_all_edges_between')
qed

end

subsection \<open>Simple Graphs \<close>

text \<open> A simple graph (or sgraph) constrains edges to size of two. This is the classic definition 
of an undirected graph \<close>

locale sgraph = graph_system + 
  assumes two_edges: "e \<in> E \<Longrightarrow> card e = 2"
begin

lemma wellformed_all_edges: "E \<subseteq> all_edges V" 
  unfolding all_edges_def using wellformed two_edges by auto

lemma e_in_all_edges: "e \<in> E \<Longrightarrow> e \<in> all_edges V"
  using wellformed_all_edges by auto 

lemma e_in_all_edges_ss: "e \<in> E \<Longrightarrow> e \<subseteq> V' \<Longrightarrow> V' \<subseteq> V \<Longrightarrow> e \<in> all_edges V'"
  unfolding all_edges_def using wellformed two_edges by auto

lemma singleton_not_edge: "{x} \<notin> E" \<comment> \<open> Suggested by Mantas Baksys \<close>
  using two_edges by fastforce 

end

text \<open> It is easy to proof that @{term "sgraph"} is a sublocale of @{term "ulgraph"}. By using indirect inheritance, 
we avoid two unneeded cardinality conditions \<close>
sublocale sgraph \<subseteq> ulgraph V E 
  by (unfold_locales)(simp add: two_edges)

locale fin_sgraph = sgraph + fin_graph_system
begin

lemma fin_neighbourhood: "finite (neighborhood x)"
  unfolding neighborhood_def using finV by simp 

lemma fin_all_edges: "finite (all_edges V)" 
  unfolding all_edges_def by (simp add: finV) 

lemma max_edges_graph:  "card E \<le> (card V)^2"
proof -
  have "card E \<le> card V choose 2" 
    by (metis fin_all_edges finV card_all_edges card_mono wellformed_all_edges)
  thus ?thesis
    by (metis binomial_le_pow le0 neq0_conv order.trans zero_less_binomial_iff) 
qed

end

sublocale fin_sgraph \<subseteq> fin_ulgraph 
  by (unfold_locales)

context sgraph
begin

lemma no_loops: "v \<in> V \<Longrightarrow> \<not> has_loop v"
  using has_loop_def two_edges by fastforce 

text \<open>Ideally, we'd redefine degree in the context of a simple graph. However, this requires 
a named loop locale, which complicates notation unnecessarily. This is the lemma that should always
be used when unfolding the degree definition in a simple graph context \<close>
lemma alt_degree_def[simp]: "degree v = card (incident_edges v)"
  using no_loops degree_no_loops  degree_none incident_edges_empty by (cases "v \<in> V") simp_all

lemma alt_deg_neighborhood: "degree v = card (neighborhood v)"
using card_incident_sedges_neighborhood by simp

definition degree_set :: "'a set \<Rightarrow> nat" where
"degree_set vs \<equiv> card {e \<in> E. vs \<subseteq> e}"

definition is_complete_n_graph:: "nat \<Rightarrow> bool" where 
"is_complete_n_graph n \<equiv> gorder = n \<and> E = all_edges V"

text \<open> The complement of a graph is a basic concept \<close>

definition is_complement :: "'a pregraph \<Rightarrow> bool" where
"is_complement G \<equiv> V = gverts G \<and> gedges G = all_edges V - E"

definition complement_edges :: "'a edge set" where
"complement_edges \<equiv> all_edges V - E"

lemma is_complement_edges: "is_complement (V', E')  \<longleftrightarrow> V = V' \<and> complement_edges = E'"
  unfolding is_complement_def complement_edges_def by auto

interpretation G_comp: sgraph V "complement_edges"
  by (unfold_locales)(auto simp add: complement_edges_def all_edges_def)

lemma is_complement_edge_iff: "e \<subseteq> V \<Longrightarrow> e \<in> complement_edges \<longleftrightarrow> e \<notin> E \<and> card e = 2"
  unfolding complement_edges_def all_edges_def by auto

end

text \<open>A complete graph is a simple graph \<close>

lemma complete_sgraph: "sgraph S (all_edges S)"
  unfolding all_edges_def by (unfold_locales) (simp_all)

interpretation comp_sgraph: sgraph S "(all_edges S)"
  using complete_sgraph by auto

lemma complete_fin_sgraph: "finite S \<Longrightarrow> fin_sgraph S (all_edges S)"
  using complete_sgraph 
  by (intro_locales) (auto simp add: sgraph.axioms(1) sgraph_def fin_graph_system_axioms_def)

subsection \<open> Subgraph Basics \<close>

text \<open> A subgraph is defined as a graph where the vertex and edge sets are subsets of the original graph. 
 Note that using the locale approach, we require each graph to be wellformed. This is interestingly
omitted in a number of other formal definitions.  \<close>
locale subgraph = H: graph_system "V\<^sub>H :: 'a set" E\<^sub>H + G: graph_system "V\<^sub>G :: 'a set" E\<^sub>G for "V\<^sub>H" "E\<^sub>H" "V\<^sub>G" "E\<^sub>G" +
  assumes verts_ss: "V\<^sub>H \<subseteq> V\<^sub>G"
  assumes edges_ss: "E\<^sub>H \<subseteq> E\<^sub>G"

(* An intro rule *)
lemma is_subgraphI[intro]: "V' \<subseteq> V \<Longrightarrow> E' \<subseteq> E \<Longrightarrow> graph_system V' E' \<Longrightarrow> graph_system V E \<Longrightarrow> subgraph V' E' V E"
  using graph_system_def by (unfold_locales) 
    (auto simp add: graph_system.vincident_def graph_system.incident_edge_in_wf)

context subgraph
begin

text \<open> Note: it could also be useful to have similar rules in @{term "ulgraph"} locale etc with 
subgraph assumption \<close>
lemma is_subgraph_ulgraph: 
  assumes "ulgraph V\<^sub>G E\<^sub>G"
  shows "ulgraph V\<^sub>H E\<^sub>H"
  using assms ulgraph.edge_size[ of V\<^sub>G E\<^sub>G] edges_ss by (unfold_locales) auto

lemma is_simp_subgraph:
  assumes "sgraph V\<^sub>G E\<^sub>G"
  shows "sgraph V\<^sub>H E\<^sub>H"
  using assms sgraph.two_edges edges_ss by (unfold_locales) auto

lemma is_finite_subgraph:
  assumes "fin_graph_system V\<^sub>G E\<^sub>G"
  shows "fin_graph_system V\<^sub>H E\<^sub>H"
  using assms verts_ss 
  by (unfold_locales) (simp add: fin_graph_system.finV finite_subset) 

lemma (in graph_system) subgraph_refl: "subgraph V E V E"
  by (simp add: graph_system_axioms is_subgraphI) 

lemma subgraph_trans: 
  assumes "graph_system V E"
  assumes "graph_system V' E'"
  assumes "graph_system V'' E''"
  shows "subgraph V'' E'' V' E' \<Longrightarrow> subgraph V' E' V E \<Longrightarrow> subgraph V'' E'' V E"
  by (meson assms(1) assms(3) is_subgraphI subgraph.edges_ss subgraph.verts_ss subset_trans)

lemma subgraph_antisym: "subgraph V' E' V E \<Longrightarrow> subgraph V E V' E' \<Longrightarrow> V = V' \<and> E = E'"
  by (simp add: dual_order.eq_iff subgraph.edges_ss subgraph.verts_ss)

end

lemma (in sgraph) subgraph_complete: "subgraph V E V (all_edges V)"
proof -
  interpret comp: sgraph V "(all_edges V)"
    using complete_sgraph by auto
  show ?thesis by (unfold_locales) (simp_all add: wellformed_all_edges)
qed

text \<open> We are often interested in the set of subgraphs. This is still very possible using locale definitions.
Interesting Note - random graphs \<^cite>\<open>"Hupel_Random"\<close> has a different definition for the well formed 
constraint to be added in here instead of in the main subgraph definition\<close>

definition (in graph_system) subgraphs:: "'a pregraph set" where
"subgraphs \<equiv> {G . subgraph (gverts G) (gedges G) V E}" 


text \<open> Induced subgraph - really only affects edges \<close>
definition (in graph_system) induced_edges:: "'a set \<Rightarrow> 'a edge set" where
"induced_edges V' \<equiv> {e \<in> E. e \<subseteq> V'}"

lemma (in sgraph) induced_edges_alt: "induced_edges V' = E \<inter> all_edges V'"
  unfolding induced_edges_def all_edges_def using two_edges by blast

lemma (in sgraph) induced_edges_self: "induced_edges V = E"
  unfolding induced_edges_def
  by (simp add: subsetI subset_antisym wellformed) 


context graph_system
begin

lemma induced_edges_ss: "V' \<subseteq> V \<Longrightarrow> induced_edges V' \<subseteq> E"
  unfolding induced_edges_def by auto

lemma induced_is_graph_sys: "graph_system V' (induced_edges V')"
  by (unfold_locales) (simp add: induced_edges_def)

interpretation induced_graph: graph_system V' "(induced_edges V')"
  using induced_is_graph_sys by simp

lemma induced_is_subgraph: "V' \<subseteq> V \<Longrightarrow> subgraph V' (induced_edges V') V E"
  using induced_edges_ss by (unfold_locales) auto

lemma induced_edges_union: 
  assumes "VH1 \<subseteq> S" "VH2 \<subseteq> T"
  assumes "graph_system VH1 EH1" "graph_system VH2 EH2"
  assumes "EH1 \<union> EH2 \<subseteq> (induced_edges (S \<union> T))"
  shows "EH1 \<subseteq> (induced_edges S)"
proof (intro subsetI, simp add: induced_edges_def, intro conjI)
  show "\<And>x. x \<in> EH1 \<Longrightarrow> x \<in> E" using assms(5)
    by (simp add: induced_edges_def subset_iff)
  show "\<And>x. x \<in> EH1 \<Longrightarrow> x \<subseteq> S"
    using assms(1) assms(3) graph_system.wellformed by blast
qed

lemma induced_edges_union_subgraph_single: 
  assumes "VH1 \<subseteq> S" "VH2 \<subseteq> T"
  assumes "graph_system VH1 EH1" "graph_system VH2 EH2"
  assumes "subgraph (VH1 \<union> VH2) (EH1 \<union> EH2) (S \<union> T) (induced_edges (S \<union> T))"
  shows "subgraph VH1 EH1 S (induced_edges S)"
proof -
  interpret ug: subgraph "(VH1 \<union> VH2)" "(EH1 \<union> EH2)" "(S \<union> T)" "(induced_edges (S \<union> T))"
    using assms(5) by simp
  show "subgraph VH1 EH1 S (induced_edges S)"
    using assms(3) graph_system_def 
    by (unfold_locales) (blast, simp add: assms(1), meson assms induced_edges_union ug.edges_ss)
qed

lemma induced_union_subgraph: 
  assumes "VH1 \<subseteq> S" and "VH2 \<subseteq> T"
  assumes "graph_system VH1 EH1" "graph_system VH2 EH2"
  shows "subgraph VH1 EH1 S (induced_edges S) \<and> subgraph VH2 EH2 T (induced_edges T) \<longleftrightarrow>
    subgraph (VH1 \<union> VH2) (EH1 \<union> EH2) (S \<union> T) (induced_edges (S \<union> T))"
proof (intro iffI conjI, elim conjE)
  show "subgraph (VH1 \<union> VH2) (EH1 \<union> EH2) (S \<union> T) (induced_edges (S \<union> T)) 
      \<Longrightarrow> subgraph VH1 EH1 S (induced_edges S)"
    using induced_edges_union_subgraph_single assms by simp
  show "subgraph (VH1 \<union> VH2) (EH1 \<union> EH2) (S \<union> T) (induced_edges (S \<union> T)) 
      \<Longrightarrow> subgraph VH2 EH2 T (induced_edges T)"
    using induced_edges_union_subgraph_single assms by (simp add: Un_commute) 
  assume a1: "subgraph VH1 EH1 S (induced_edges S)" and a2: "subgraph VH2 EH2 T (induced_edges T)"
  then interpret h1: subgraph VH1 EH1 S "(induced_edges S)"
    by simp
  interpret h2: subgraph VH2 EH2 T "(induced_edges T)" using a2 by simp
  show "subgraph (VH1 \<union> VH2) (EH1 \<union> EH2) (S \<union> T) (induced_edges (S \<union> T))"
    using h1.H.wellformed h2.H.wellformed h1.verts_ss h2.verts_ss h1.edges_ss h2.edges_ss 
    by (unfold_locales) (auto simp add: induced_edges_def)
qed

end
end