section \<open>Szemerédi's Regularity Lemma\<close>

theory Szemeredi
  imports Roth_Library "Girth_Chromatic.Ugraphs"

begin

text\<open>We formalise Szemerédi's Regularity Lemma, which is a major result in the study of large graphs
(extremal graph theory).
We follow Yufei Zhao's notes ``Graph Theory and Additive Combinatorics'' (MIT)
\<^url>\<open>https://ocw.mit.edu/courses/mathematics/18-217-graph-theory-and-additive-combinatorics-fall-2019/lecture-notes/MIT18_217F19_ch3.pdf\<close>
and W.T. Gowers's notes ``Topics in Combinatorics'' (University of Cambridge, Lent 2004, Chapter 3)
\<^url>\<open>https://www.dpmms.cam.ac.uk/~par31/notes/tic.pdf\<close>.
We also refer to a third source, also by Zhao and also entitled 
``Graph Theory and Additive Combinatorics'': \<^url>\<open>https://yufeizhao.com/gtac/gtac17.pdf\<close>.\<close>


subsection \<open>Miscellaneous\<close>

text \<open>A technical lemma used below in @{text \<open>energy_graph_partition_half\<close>}\<close>
lemma sum_products_le:
  fixes a :: "'a \<Rightarrow> 'b::linordered_idom"
  assumes "\<And>i. i \<in> I \<Longrightarrow> a i \<ge> 0"
  shows "(\<Sum>i\<in>I. a i * b i)\<^sup>2 \<le> (\<Sum>i\<in>I. a i) * (\<Sum>i\<in>I. a i * (b i)\<^sup>2)"
  using assms
proof (induction I rule: infinite_finite_induct)
  case (insert j I)
  then have "(\<Sum>i\<in>insert j I. a i * b i)\<^sup>2
          \<le> (a j * b j)\<^sup>2 + 2 * a j * b j * (\<Sum>i\<in>I. a i * b i) + (\<Sum>i\<in>I. a i) * (\<Sum>i\<in>I. a i * (b i)\<^sup>2)"
    using insert by (simp add: algebra_simps power2_eq_square)
  also have "\<dots> \<le> a j * (a j * (b j)\<^sup>2) + (a j * (sum a I * (b j)\<^sup>2 + (\<Sum>i\<in>I. a i * (b i)\<^sup>2)) 
                 + sum a I * (\<Sum>i\<in>I. a i * (b i)\<^sup>2))"
  proof -
    have "0 \<le> (\<Sum>i\<in>I. a i * (b i - b j)\<^sup>2)"
      by (simp add: insert.prems sum_nonneg)
    then have "2 * b j * (\<Sum>i\<in>I. a i * b i) \<le> (sum a I * (b j)\<^sup>2) + (\<Sum>i\<in>I. a i * (b i)\<^sup>2)"
      by (simp add: power2_eq_square algebra_simps sum_subtractf sum.distrib sum_distrib_left)
    then show ?thesis
      by (simp add: insert.prems power2_eq_square mult.commute mult.left_commute mult_left_mono)
  qed
  finally show ?case 
    by (simp add: insert algebra_simps)
qed auto

subsubsection \<open>Partitions indexed by integers\<close>

definition finite_graph_partition :: "[uvert set, nat \<Rightarrow> uvert set, nat] \<Rightarrow> bool"
  where "finite_graph_partition V P n \<equiv> partition_on V (P ` {..<n}) \<and> disjoint_family_on P {..<n}"

text \<open>Equivalent, simpler characterisation\<close>
lemma finite_graph_partition_eq: "finite_graph_partition V P n \<longleftrightarrow> partition_on V (P ` {..<n}) \<and> inj_on P {..<n}"
  unfolding finite_graph_partition_def 
proof (rule conj_cong)
  show "partition_on V (P ` {..<n}) \<Longrightarrow> disjoint_family_on P {..<n} = inj_on P {..<n}"
  unfolding finite_graph_partition_def partition_on_def disjoint_family_on_def inj_on_def
  by (metis disjointD inf.idem image_eqI)
qed auto

lemma finite_graph_partition_0 [iff]:
  "finite_graph_partition V P 0 \<longleftrightarrow> V={}"
  by (auto simp: finite_graph_partition_eq partition_on_def)

lemma finite_graph_partition_equals:
  "finite_graph_partition V P n \<Longrightarrow> (\<Union>i<n. P i) = V"
  by (meson finite_graph_partition_def partition_on_def)

lemma finite_graph_partition_subset:
  "\<lbrakk>finite_graph_partition V P n; i<n\<rbrakk> \<Longrightarrow> P i \<subseteq> V"
  using finite_graph_partition_equals by blast

lemma finite_graph_partition_nonempty: 
  "\<lbrakk>finite_graph_partition V P n; i<n\<rbrakk> \<Longrightarrow> P i \<noteq> {}"
  by (metis finite_graph_partition_def image_eqI lessThan_iff partition_on_def)

lemma trivial_graph_partition:
  assumes "finite_graph_partition V P 1" shows "P 0 = V"
  using finite_graph_partition_equals [OF assms] by auto

lemma trivial_graph_partition_exists:
  assumes "V \<noteq> {}"
  shows "finite_graph_partition V (\<lambda>i. V) (Suc 0)"
  using assms by (simp add: lessThan_Suc finite_graph_partition_eq partition_on_def)

lemma finite_graph_partition_finite:
  assumes "finite_graph_partition V P k" "finite V" "i<k"
  shows "finite (P i)"
  by (metis assms finite_UN finite_graph_partition_equals finite_lessThan lessThan_iff)

lemma finite_graph_partition_le:
  assumes "finite_graph_partition V P k" "finite V" "i<k"
  shows "card (P i) \<le> card V"
  by (metis (mono_tags, lifting) UN_I assms card_mono finite_graph_partition_equals lessThan_iff subsetI)

lemma finite_graph_partition_gt0:
  assumes "finite_graph_partition V P k" "finite V" "i<k"
  shows "card (P i) > 0"
  by (metis assms card_gt_0_iff finite_graph_partition_def finite_graph_partition_finite imageI lessThan_iff partition_on_def)

lemma card_finite_graph_partition:
  assumes "finite_graph_partition V P k" "finite V"
  shows "(\<Sum>i<k. card (P i)) = card V"
proof -
  have "(\<Sum>i<k. card (P i)) = sum card (P ` {..<k})"
    by (metis assms(1) finite_graph_partition_eq sum.reindex_cong)
  also have "\<dots> = card (\<Union> (P ` {..<k}))"
    using assms card_Union_disjoint finite_graph_partition_def partition_on_def by fastforce
  also have "\<dots> = card V"
    using assms finite_graph_partition_equals by blast
  finally show ?thesis .
qed

lemma finite_graph_partition_obtain:
  assumes "finite_graph_partition V P k" "x \<in> V"
  obtains i where "i < k" and "x \<in> P i"
  using assms finite_graph_partition_equals by force

text \<open>Partitions into two parts\<close>
fun binary_partition :: "['a set, 'a set, nat] \<Rightarrow> 'a set"
  where "binary_partition A B 0 = A"
      | "binary_partition A B (Suc 0) = B-A"

lemma binary_partition2_eq [simp]: "binary_partition A B ` {..<2} = {A,B-A}"
   by (auto simp add: numeral_2_eq_2 lessThan_Suc)

lemma inj_binary_partition:
   "B \<noteq> {} \<Longrightarrow> inj_on (binary_partition A B) {..<2}"
  by (auto simp: numeral_2_eq_2 lessThan_Suc)

lemma disjoint_family_binary_partition: "disjoint_family_on (binary_partition A B) {..<2}"
  by (auto simp: numeral_2_eq_2 lessThan_Suc disjoint_family_on_def)

lemma finite_graph_partition_binary_partition:
  assumes "A \<subset> B" "A \<noteq> {}"
  shows "finite_graph_partition B (binary_partition A B) 2"
  unfolding finite_graph_partition_def partition_on_def binary_partition2_eq
    using assms 
  by (force simp add: disjnt_iff pairwise_insert disjoint_family_binary_partition)

subsubsection \<open>Tools to combine the refinements of the partition @{term "P i"} for each @{term i}\<close>

text \<open>These are needed to retain the ``intuitive'' idea of partitions as indexed by integers.\<close>

lemma less_sum_nat_iff:
  fixes b::nat and k::nat
  shows "b < (\<Sum>i<k. a i) \<longleftrightarrow> (\<exists>j<k. (\<Sum>i<j. a i) \<le> b \<and> b < (\<Sum>i<j. a i) + a j)"
proof (induction k arbitrary: b)
  case (Suc k)
  then show ?case
    by (simp add: less_Suc_eq) (metis not_less trans_less_add1)
qed auto

lemma less_sum_nat_iff_uniq:
  fixes b::nat and k::nat
  shows "b < (\<Sum>i<k. a i) \<longleftrightarrow> (\<exists>!j. j<k \<and> (\<Sum>i<j. a i) \<le> b \<and> b < (\<Sum>i<j. a i) + a j)"
  unfolding less_sum_nat_iff by (meson leD less_sum_nat_iff nat_neq_iff)

definition part :: "(nat \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat"
  where "part a k b \<equiv> (THE j. j<k \<and> (\<Sum>i<j. a i) \<le> b \<and> b < (\<Sum>i<j. a i) + a j)"

lemma part: 
  "b < (\<Sum>i<k. a i) \<longleftrightarrow> (let j = part a k b in j < k \<and> (\<Sum>i < j. a i) \<le> b \<and> b < (\<Sum>i < j. a i) + a j)"
  (is "?lhs = ?rhs")
proof
  assume ?lhs
  then show ?rhs
    unfolding less_sum_nat_iff_uniq part_def by (metis (no_types, lifting) theI')
qed (auto simp: less_sum_nat_iff Let_def)

lemma part_Suc: "part a (Suc k) b = (if sum a {..<k} \<le> b \<and> b < sum a {..<k} + a k then k else part a k b)"
  using leD 
  by (fastforce simp: part_def less_Suc_eq less_sum_nat_iff conj_disj_distribR cong: conj_cong)

lemma part_eq:
  assumes "i < k" "d < a i"
  shows "part a k (sum a {..<i} + d) = i"
proof -
  have \<section>: "\<And>j. \<lbrakk>sum a {..<j} \<le> sum a {..<i} + d;
              sum a {..<i} + d < sum a {..<j} + a j\<rbrakk> \<Longrightarrow> j = i"
    by (meson \<open>d < a i\<close> leD le_add1 less_sum_nat_iff nat_add_left_cancel_less not_less_iff_gr_or_eq)
  show ?thesis
    unfolding part_def
    using assms
    by (intro the_equality) (auto simp: \<section>)
qed

lemma sum_layers_less:
  fixes d::nat and k::nat
  shows "\<lbrakk>i < k; d < a i\<rbrakk> \<Longrightarrow> sum a {..<i} + d < sum a {..<k}"
  by (meson le_add1 less_sum_nat_iff nat_add_left_cancel_less)


subsection \<open>Edges\<close>

text \<open>All edges between two sets of vertices, @{term X} and @{term Y}, in a graph, @{term G}\<close>

definition all_edges_between :: "nat set \<Rightarrow> nat set \<Rightarrow> nat set \<times> nat set set \<Rightarrow> (nat \<times> nat) set"
  where "all_edges_between X Y G \<equiv> {(x,y). x\<in>X \<and> y\<in>Y \<and> {x,y} \<in> uedges G}"

lemma all_edges_between_subset: "all_edges_between X Y G \<subseteq> X\<times>Y"
  by (auto simp: all_edges_between_def)

lemma max_all_edges_between: 
  assumes "finite X" "finite Y"
  shows "card (all_edges_between X Y G) \<le> card X * card Y"
  by (metis assms card_mono finite_SigmaI all_edges_between_subset card_cartesian_product)

lemma all_edges_between_empty [simp]:
  "all_edges_between {} Z G = {}" "all_edges_between Z {} G = {}"
  by (auto simp: all_edges_between_def)

lemma all_edges_between_disjnt1:
  assumes "disjnt X Y"
  shows "disjnt (all_edges_between X Z G) (all_edges_between Y Z G)"
  using assms by (auto simp: all_edges_between_def disjnt_iff)

lemma all_edges_between_disjnt2:
  assumes "disjnt Y Z"
  shows "disjnt (all_edges_between X Y G) (all_edges_between X Z G)"
  using assms by (auto simp: all_edges_between_def disjnt_iff)

lemma all_edges_between_Un1:
  "all_edges_between (X \<union> Y) Z G = all_edges_between X Z G \<union> all_edges_between Y Z G"
  by (auto simp: all_edges_between_def)

lemma all_edges_between_Un2:
  "all_edges_between X (Y \<union> Z) G = all_edges_between X Y G \<union> all_edges_between X Z G"
  by (auto simp: all_edges_between_def)

lemma finite_all_edges_between:
  assumes "finite X" "finite Y"
  shows "finite (all_edges_between X Y G)"
  by (meson all_edges_between_subset assms finite_cartesian_product finite_subset)

subsection \<open>Edge Density and Regular Pairs\<close>

text \<open>The edge density between two sets of vertices, @{term X} and @{term Y}, in @{term G}.
      Authors disagree on whether the sets are assumed to be disjoint!.
      Quite a few authors assume disjointness, e.g. Malliaris and Shelah \<^url>\<open>https://www.jstor.org/stable/23813167\<close>
      For the following definitions, see pages 49--50 in Zhao's notes.\<close>
definition "edge_density X Y G \<equiv> card(all_edges_between X Y G) / (card X * card Y)"

lemma edge_density_ge0: "edge_density X Y G \<ge> 0"
  by (auto simp: edge_density_def)

lemma edge_density_le1:
  assumes "finite X" "finite Y"
  shows "edge_density X Y G \<le> 1"
  using of_nat_mono [OF max_all_edges_between [OF assms]]
  by (fastforce simp add: edge_density_def divide_simps)

lemma all_edges_between_swap:
  "all_edges_between X Y G = (\<lambda>(x,y). (y,x)) ` (all_edges_between Y X G)"
  unfolding all_edges_between_def
  by (auto simp add: insert_commute image_iff split: prod.split)

lemma card_all_edges_between_commute:
  "card (all_edges_between X Y G) = card (all_edges_between Y X G)"
proof -
  have "inj_on (\<lambda>(x, y). (y, x)) A" for A :: "(nat*nat)set"
    by (auto simp: inj_on_def)
  then show ?thesis
    by (simp add: all_edges_between_swap [of X Y] card_image)
qed

lemma edge_density_commute: "edge_density X Y G = edge_density Y X G"
  by (simp add: edge_density_def card_all_edges_between_commute mult.commute)


text \<open>$\epsilon$-regular pairs, for two sets of vertices. Again, authors disagree on whether the
sets need to be disjoint, though it seems that overlapping sets cause double-counting. Authors also
disagree about whether or not to use the strict subset relation here. The proofs below are easier if
it is strict but later proofs require the non-strict version. The two definitions can be proved to
be equivalent under fairly mild conditions.\<close>

definition regular_pair::  "uvert set  \<Rightarrow> uvert set \<Rightarrow> ugraph \<Rightarrow> real \<Rightarrow> bool"
  where "regular_pair X Y G \<epsilon> \<equiv> 
    \<forall>A B. A \<subset> X \<and> B \<subset> Y \<and> (card A \<ge> \<epsilon> * card X) \<and> (card B \<ge> \<epsilon> * card Y) \<longrightarrow>
              \<bar>edge_density A B G - edge_density X Y G\<bar> \<le> \<epsilon>" for \<epsilon>::real

lemma regular_pair_commute: "regular_pair X Y G \<epsilon> \<longleftrightarrow> regular_pair Y X G \<epsilon>"
  by (metis edge_density_commute regular_pair_def)

abbreviation "irregular_pair X Y G \<epsilon> \<equiv> \<not> regular_pair X Y G \<epsilon>"

lemma irregular_pair_E:
  fixes \<epsilon>::real
  assumes "irregular_pair X Y G \<epsilon>" 
  obtains A B where "A \<subset> X \<and> B \<subset> Y \<and> (card A \<ge> \<epsilon> * card X) \<and> (card B \<ge> \<epsilon> * card Y)"
              "\<bar>edge_density A B G - edge_density X Y G\<bar> > \<epsilon>"
  using assms by (auto simp: not_le regular_pair_def)

lemma irregular_pair_I: 
  fixes \<epsilon>::real
  assumes "A \<subset> X" "B \<subset> Y" "(card A \<ge> \<epsilon> * card X)" "(card B \<ge> \<epsilon> * card Y)"
              "\<bar>edge_density A B G - edge_density X Y G\<bar> > \<epsilon>"
  shows "irregular_pair X Y G \<epsilon>"
  using assms  by (auto simp: not_le regular_pair_def)

lemma edge_density_Un:
  assumes "disjnt X1 X2" "finite X1" "finite X2" "finite Y"
  shows "edge_density (X1 \<union> X2) Y G = (edge_density X1 Y G * card X1 + edge_density X2 Y G * card X2) / (card X1 + card X2)"
  using assms unfolding edge_density_def
  by (simp add: all_edges_between_disjnt1 all_edges_between_Un1 finite_all_edges_between card_Un_disjnt divide_simps)

lemma edge_density_partition:
  assumes U: "finite_graph_partition U P n" "finite U" and "finite W"
  shows "edge_density U W G = (\<Sum>i<n. edge_density (P i) W G * card (P i)) / (\<Sum>i<n. card (P i))"
  using U
proof (induction n arbitrary: U)
  case 0
  then show ?case
    by (simp add: edge_density_def)
next
  case (Suc n)
  then have fin_n: "finite_graph_partition (\<Union> (P ` {..<n})) P n"
    unfolding partition_on_def finite_graph_partition_def
    by (simp add: disjoint_family_on_disjoint_image disjoint_family_on_insert lessThan_Suc)
  moreover have finU: "finite (\<Union> (P ` {..<Suc n}))"
    by (metis Suc.prems finite_graph_partition_def partition_on_def)
  ultimately have card_UP: "card (\<Union> (P ` {..<n})) = (\<Sum>i<n. card (P i))"
    by (metis card_finite_graph_partition finite_UN finite_lessThan lessI lessThan_iff less_trans)
  have eq0_iff: "(\<Sum>i<n. card (P i)) = 0 \<longleftrightarrow> (\<forall>i<n. card (P i) = 0)"
    by (meson finite_lessThan lessThan_iff sum_eq_0_iff)
  have fin_P: "finite (P i)" if "i < Suc n" for i
    using Suc.prems finite_graph_partition_finite that by presburger
  have "edge_density U W G = edge_density (P n \<union> \<Union> (P ` {..<n})) W G"
    by (simp add: lessThan_Suc flip: finite_graph_partition_equals [OF Suc.prems(1)])
  also have "\<dots> = (edge_density (P n) W G * card (P n) 
                + edge_density (\<Union> (P ` {..<n})) W G * card (\<Union> (P ` {..<n}))) / (card (P n) + card (\<Union> (P ` {..<n})))"
  proof (rule edge_density_Un)
    show "disjnt (P n) (\<Union> (P ` {..<n}))"
      by (metis Suc.prems(1) disjnt_def disjoint_family_on_insert finite_graph_partition_def lessThan_Suc lessThan_iff less_irrefl_nat)
    show "finite (P n)"
      using Suc.prems finite_graph_partition_finite lessI by presburger
  qed (use \<open>finite W\<close> finU in auto)
  also have "\<dots> = (edge_density (P n) W G * card (P n) 
                + edge_density (\<Union> (P ` {..<n})) W G * (\<Sum>i<n. card (P i))) / (\<Sum>i<Suc n. card (P i))"
    by (simp add: card_UP)
  also have "\<dots> = (\<Sum>i<Suc n. edge_density (P i) W G * card (P i)) / (\<Sum>i<Suc n. card (P i))"
    using Suc.prems 
    by (simp add: Suc.IH [OF fin_n] fin_P eq0_iff flip: of_nat_sum)
  finally show ?case .
qed


text\<open>Let @{term P}, @{term Q} be partitions of a set of vertices @{term V}. 
  Then @{term P} refines @{term Q} if for all @{term \<open>A \<in> P\<close>} there is @{term \<open>B \<in> Q\<close>} 
  such that @{term \<open>A \<subseteq> B\<close>}.\<close>

definition finite_graph_refines :: "[uvert set, nat \<Rightarrow> uvert set, nat, nat \<Rightarrow> uvert set, nat] \<Rightarrow> bool" 
  where "finite_graph_refines V P n Q m \<equiv>
        finite_graph_partition V P n \<and> finite_graph_partition V Q m \<and> (\<forall>i<n. \<exists>j<m. P i \<subseteq> Q j)" 

text \<open>For the sake of generality, and following Zhao's Online Lecture 
\<^url>\<open>https://www.youtube.com/watch?v=vcsxCFSLyP8&t=16s\<close>
we do not impose disjointness: we do not include @{term "i\<noteq>j"} below.\<close>

definition irregular_set:: "[real, ugraph, nat \<Rightarrow> uvert set, nat] \<Rightarrow> (nat\<times>nat) set"
  where "irregular_set \<equiv> \<lambda>\<epsilon>::real. \<lambda>G P k. {(i,j)|i j. i<k \<and> j<k \<and> irregular_pair (P i) (P j) G \<epsilon>}"

text\<open>A regular partition may contain a few irregular pairs as long as their total size is bounded as follows.\<close>
definition regular_partition:: "[real, ugraph, nat \<Rightarrow> uvert set, nat] \<Rightarrow> bool"
  where
  "regular_partition \<equiv> \<lambda>\<epsilon>::real. \<lambda>G P k. 
     finite_graph_partition (uverts G) P k \<and>
     (\<Sum>(i,j) \<in> irregular_set \<epsilon> G P k. card (P i) * card (P j)) \<le> \<epsilon> * (card (uverts G))\<^sup>2"

lemma irregular_set_subset: "irregular_set \<epsilon> G P k \<subseteq> {..<k} \<times> {..<k}"
  by (auto simp: irregular_set_def)

lemma irregular_set_swap: "(i,j) \<in> irregular_set \<epsilon> G P k \<longleftrightarrow> (j,i) \<in> irregular_set \<epsilon> G P k"
  by (auto simp add: irregular_set_def regular_pair_commute)

lemma finite_graph_refines_refines:
  assumes "finite_graph_refines V Y n X m"
  shows "refines V (Y ` {..<n}) (X ` {..<m})"
  using assms by (auto simp: finite_graph_refines_def refines_def finite_graph_partition_def)

lemma finite_irregular_set [simp]: "finite (irregular_set \<epsilon> G P k)"
proof -
  have "irregular_set \<epsilon> G P k \<subseteq> {0..<k} \<times> {0..<k}"
    by (auto simp: irregular_set_def)
  then show ?thesis
    by (simp add: finite_subset)
qed

subsection \<open>Energy of a Graph\<close>

text \<open>Definition 3.7 (Energy), written @{term "q(\<U>,\<W>)"}\<close>
definition energy_graph_subsets:: "[uvert set, uvert set, ugraph] \<Rightarrow> real" where
  "energy_graph_subsets \<U> \<W> G \<equiv>
     card \<U> * card \<W> * (edge_density \<U> \<W> G)\<^sup>2 / (card (uverts G))\<^sup>2"

text \<open>Definition for partitions\<close>
definition energy_graph_partitions_subsets
  :: "[ugraph, nat \<Rightarrow> uvert set, nat, nat \<Rightarrow> uvert set, nat] \<Rightarrow> real"
  where "energy_graph_partitions_subsets G U k W l \<equiv> 
           \<Sum>i<k.\<Sum>j<l. energy_graph_subsets (U i) (W j) G"

lemma energy_graph_subsets_ge0 [simp]:
  "energy_graph_subsets \<U> \<W> G \<ge> 0"
  by (auto simp: energy_graph_subsets_def)

lemma energy_graph_partitions_subsets_ge0 [simp]:
  "energy_graph_partitions_subsets G U k W l \<ge> 0"
  by (auto simp: sum_nonneg energy_graph_partitions_subsets_def)

lemma energy_graph_subsets_commute: 
  "energy_graph_subsets \<U> \<W> G = energy_graph_subsets \<W> \<U> G"
  by (simp add: energy_graph_subsets_def edge_density_commute)

lemma energy_graph_partitions_subsets_commute:
  "energy_graph_partitions_subsets G W l U k = energy_graph_partitions_subsets G U k W l"
  by (simp add: energy_graph_partitions_subsets_def energy_graph_subsets_commute sum.swap [where A="{..<l}"])

text\<open>Definition 3.7 (Energy of a Partition), or following Gowers, mean square density:
 a version of energy for a single partition of the vertex set. \<close> 

abbreviation mean_square_density :: "[ugraph, nat \<Rightarrow> uvert set, nat] \<Rightarrow> real"
  where "mean_square_density G U k \<equiv> energy_graph_partitions_subsets G U k U k"

lemma mean_square_density: 
  "mean_square_density G U k \<equiv> 
          (\<Sum>i<k. \<Sum>j<k. card (U i) * card (U j) * (edge_density (U i) (U j) G)\<^sup>2)
        / (card (uverts G))\<^sup>2"
  by (simp add: energy_graph_partitions_subsets_def energy_graph_subsets_def sum_divide_distrib)

text\<open>Observation: the energy is between 0 and 1 because the edge density is bounded above by 1.\<close>

lemma sum_partition_le:
  assumes "finite_graph_partition V P k" "finite V"
    shows "(\<Sum>i<k. \<Sum>j<k. real (card (P i) * card (P j))) \<le> (real(card V))\<^sup>2"
  using assms
proof (induction k arbitrary: V)
  case (Suc k)
  then have [simp]: "V \<inter> P k = P k"
    using finite_graph_partition_equals by fastforce
  have [simp]: "finite (P i)" if "i\<le>k" for i
    using Suc.prems finite_graph_partition_finite that by force
  have C: "card (P i) \<le> card V" if "i\<le>k" for i
    using Suc.prems finite_graph_partition_le le_imp_less_Suc that by presburger
  have D [simp]: "(\<Sum>j<k. real (card (P j))) = real (card V) - real (card (P k))"
    by (simp flip: card_finite_graph_partition [OF Suc.prems])
  have "disjnt (P k) (\<Union> (P ` {..<k}))"
    using Suc
    by (metis disjnt_def disjoint_family_on_insert finite_graph_partition_def lessThan_Suc lessThan_iff less_irrefl_nat)
  with Suc have *: "(\<Sum>i<k. \<Sum>j<k. real (card (P i) * card (P j)))
     \<le> (real (card (V - P k)))\<^sup>2"
    by (simp add: finite_graph_partition_def lessThan_Suc partition_on_insert disjoint_family_on_insert comm_monoid_add_class.sum.distrib)
  have "(\<Sum>i<Suc k. \<Sum>j<Suc k. real (card (P i) * card (P j))) 
      = real (card (P k) * card (P k)) + 2 * (card V - card (P k)) * card (P k)
        + (\<Sum>i<k. \<Sum>j<k. real (card (P i) * card (P j)))"
    by (simp add: C of_nat_diff sum.distrib algebra_simps flip: sum_distrib_right)
  also have "\<dots> \<le> real (card (P k) * card (P k)) +
        2 * (card V - card (P k)) * card (P k) + (real (card (V - P k)))\<^sup>2"
    using * by linarith
  also have "\<dots> \<le> (real (card V))\<^sup>2"
    by (simp add: of_nat_diff C card_Diff_subset_Int algebra_simps power2_eq_square)
  finally show ?case .
qed auto

lemma mean_square_density_bounded: 
  assumes "finite_graph_partition (uverts G) P k" "finite (uverts G)" 
  shows "mean_square_density G P k \<le> 1"
proof-
  have \<section>: "edge_density (P i) (P j) G \<le> 1" for i j
    using assms of_nat_mono [OF max_all_edges_between]
    by (smt (verit, best) card.infinite divide_eq_0_iff edge_density_def edge_density_le1 mult_eq_0_iff of_nat_0)
  have "(\<Sum>i<k. \<Sum>j<k. real (card (P i) * card (P j)) * (edge_density (P i) (P j) G)\<^sup>2) 
     \<le> (\<Sum>i<k. \<Sum>j<k. real (card (P i) * card (P j)))"
    by (intro sum_mono mult_right_le_one_le) (auto simp: abs_square_le_1 edge_density_ge0 \<section>)
  also have "\<dots> \<le> (real(card (uverts G)))\<^sup>2"
    using sum_partition_le using assms by presburger
  finally show ?thesis 
    by (simp add: mean_square_density divide_simps)
qed

subsection \<open>Partitioning and Energy\<close>

text\<open>Zhao's Lemma 3.8 and Gowers's remark after Lemma 11. 
 Further partitioning of subsets of the vertex set cannot make the energy decrease. 
 We follow Gowers's proof, which avoids the use of probability.\<close>

lemma energy_graph_partition_half:
  assumes fin: "finite \<U>" "finite \<W>" and U: "finite_graph_partition \<U> U n"
  shows "card \<U> * (edge_density \<U> \<W> G)\<^sup>2 \<le> (\<Sum>i<n. card (U i) * (edge_density (U i) \<W> G)\<^sup>2)"
proof -
  have "card \<U> * (edge_density \<U> \<W> G)\<^sup>2 = (\<Sum>i<n. card (U i) * (edge_density \<U> \<W> G)\<^sup>2)"
    by (metis \<open>finite \<U>\<close> U sum_distrib_right card_finite_graph_partition of_nat_sum)
  also have "\<dots> = edge_density \<U> \<W> G * (\<Sum>i<n. edge_density \<U> \<W> G * card (U i))"
    by (simp add: sum_distrib_left power2_eq_square mult_ac)
  also have "\<dots> = (\<Sum>i<n. edge_density (U i) \<W> G * real (card (U i))) * edge_density \<U> \<W> G"
  proof -
    have "edge_density \<U> \<W> G * (\<Sum>n<n. edge_density (U n) \<W> G * card (U n)) 
        = edge_density \<U> \<W> G * (edge_density \<U> \<W> G * (\<Sum>n<n. card (U n)))"
      by (simp add: edge_density_partition [OF U fin])
    then show ?thesis
      by (simp add: mult.commute sum_distrib_left)
  qed
  also have "\<dots> = (\<Sum>i<n. card (U i) * edge_density (U i) \<W> G) * edge_density \<U> \<W> G"
    by (simp add: sum_distrib_left mult_ac)
  also have "\<dots> = (\<Sum>i<n. card (U i) * edge_density (U i) \<W> G)\<^sup>2 / (\<Sum>i<n. card (U i))"
    unfolding edge_density_partition [OF U fin]
    by (simp add: mult_ac flip: power2_eq_square)
  also have "\<dots> \<le> (\<Sum>i<n. card (U i) * (edge_density (U i) \<W> G)\<^sup>2)"
    apply (clarsimp simp add: mult_ac divide_simps simp flip: of_nat_sum)
    by (simp add: sum_products_le)
  finally show ?thesis .
qed

proposition energy_graph_partition_increase:
  assumes fin: "finite \<U>" "finite \<W>" 
    and U: "finite_graph_partition \<U> U k" 
    and V: "finite_graph_partition \<W> W l"
  shows "energy_graph_partitions_subsets G U k W l \<ge> energy_graph_subsets \<U> \<W> G" 
proof -
  have "(card \<U> * card \<W>) * (edge_density \<U> \<W> G)\<^sup>2 = card \<W> * (card \<U> * (edge_density \<U> \<W> G)\<^sup>2)"
    using fin by (simp add: mult_ac)
  also have "\<dots> \<le> card \<W> * (\<Sum>i<k. card (U i) * (edge_density (U i) \<W> G)\<^sup>2)"
    by (intro mult_left_mono energy_graph_partition_half fin) (use assms in auto)
  also have "\<dots> = (\<Sum>i<k. card (U i) * (card \<W> * (edge_density \<W> (U i) G)\<^sup>2))"
    by (simp add: sum_distrib_left edge_density_commute mult_ac)
  also have "\<dots> \<le> (\<Sum>i<k. card (U i) * (\<Sum>j<l. card (W j) * (edge_density (W j) (U i) G)\<^sup>2))"
  proof (intro mult_left_mono energy_graph_partition_half sum_mono fin)
    show "finite (U i)" if "i \<in> {..<k}" for i
      using that U fin finite_graph_partition_finite by blast
  qed (use assms in auto)
  also have "\<dots> \<le> (\<Sum>i<k. \<Sum>j<l. (card (U i) * card (W j)) * (edge_density (U i) (W j) G)\<^sup>2)"
    by (simp add: sum_distrib_left edge_density_commute mult_ac)
  finally
  have "(card \<U> * card \<W>) * (edge_density \<U> \<W> G)\<^sup>2 
    \<le> (\<Sum>i<k. \<Sum>j<l. (card (U i) * card (W j)) * (edge_density (U i) (W j) G)\<^sup>2)" .
  then show ?thesis
    unfolding energy_graph_partitions_subsets_def energy_graph_subsets_def
    by (simp add: divide_simps flip: sum_divide_distrib)
qed

lemma partition_imp_finite_graph_partition:
  "\<lbrakk>partition_on A P; finite P\<rbrakk> \<Longrightarrow> finite_graph_partition A (from_nat_into P) (card P)"
  by (metis bij_betw_def bij_betw_from_nat_into_finite finite_graph_partition_eq)

text \<open>The following is the fully general version of Gowers's Lemma 11 and Zhao's Lemma 3.9. 
Further partitioning of subsets of the vertex set cannot make the energy decrease.
Note that @{term V} should be @{term "uverts G"} even though this more general version holds.\<close>

lemma energy_graph_partitions_subsets_increase_half:
  assumes ref: "finite_graph_refines V Y n X m" and "finite V" 
    and finU: "\<And>i. i < k \<Longrightarrow> card (U i) > 0"
  shows "energy_graph_partitions_subsets G X m U k \<le> energy_graph_partitions_subsets G Y n U k" 
        (is "?lhs \<le> ?rhs")
proof -
  have "\<exists>F. partition_on (X i) F \<and> F = Y ` {j. j<n \<and> Y j \<subseteq> X i}" if "i<m" for i
    using that refines_obtains_subset [OF finite_graph_refines_refines [OF assms(1)]] by blast
  then obtain F where F: "\<And>i. i<m \<Longrightarrow> partition_on (X i) (F i) \<and> F i = Y ` {j. j<n \<and> Y j \<subseteq> X i}"
    by fastforce
  have finite_X: "finite (X i)" if "i<m" for i
    using \<open>finite V\<close> finite_graph_partition_finite finite_graph_refines_def ref that by auto
  have finite_F: "finite (F i)" if "i<m" for i
    using that by (simp add: F)
  have Fi_eq: "F i = from_nat_into (F i) ` {..<card (F i)}" if "i<m" for i
    by (metis bij_betw_def bij_betw_from_nat_into_finite finite_F that)
  have F_disjoint: "disjoint_family_on F {..<m}"
    using ref unfolding finite_graph_refines_def finite_graph_partition_def disjoint_family_on_def
    by (smt (verit) F Int_subset_iff Union_upper disjoint_iff lessThan_iff partition_on_def subset_empty)
  have F_ne: "F i \<noteq> {}" if "i<m" for i
    using that ref F unfolding finite_graph_refines_def partition_on_def
    by (metis Sup_empty finite_graph_partition_nonempty)
  have injF: "inj_on F {..<m}"
    by (metis disjoint_family_on_iff_disjoint_image F_disjoint F_ne lessThan_iff)
  have injY: "inj_on Y {..<n}"
    using finite_graph_partition_eq finite_graph_refines_def ref(1) by presburger
  have F_sums_Y: "(\<Sum>i<m. \<Sum>U\<in>F i. f U) = (\<Sum>i<n. f (Y i))" for f :: "nat set \<Rightarrow> real"
  proof -
    have Yn_eq: "Y ` {..<n} = (\<Union>i<m. F i)"
      using ref by (force simp add: finite_graph_refines_def dest: F)
    have "inj_on (\<lambda>i. {Y i}) {..<n}"
      using injY by (force simp add: inj_on_def)
    then have "(\<Sum>i<n. f (Y i)) = sum f (\<Union>i<m. F i)"
      by (metis Yn_eq injY sum.reindex_cong)
    also have "\<dots> = (sum \<circ> sum) f (F ` {..<m})"
      using F_disjoint finite_F 
      by (simp add: disjoint_family_on_disjoint_image sum.Union_disjoint_sets)
    also have "\<dots> = (\<Sum>i<m. \<Sum>U\<in>F i. f U)"
      unfolding comp_apply by (metis injF sum.reindex_cong)
    finally show ?thesis
      by simp
  qed
  have "?lhs = (\<Sum>i<m. \<Sum>j<k. energy_graph_subsets (X i) (U j) G)"
    by (simp add: energy_graph_partitions_subsets_def)
  also have "\<dots> \<le> (\<Sum>i<m. \<Sum>j<k. energy_graph_partitions_subsets G (from_nat_into (F i)) (card (F i)) (\<lambda>x. U j) 1)"
  proof -
    have "finite_graph_partition (X i) (from_nat_into (F i)) (card (F i))"
      if "i < m" "j < k" for i j
      using partition_imp_finite_graph_partition that F by fastforce
    moreover have "finite_graph_partition (U j) (\<lambda>x. U j) (Suc 0)"
      if "i < m" "j < k" for i j
      using that by (metis card.empty finU less_not_refl trivial_graph_partition_exists)
    ultimately show ?thesis
      by (intro sum_mono energy_graph_partition_increase; simp add: finU card_ge_0_finite finite_X)
  qed
  also have "\<dots> = (\<Sum>i<m. \<Sum>r<card (F i). \<Sum>j<k. energy_graph_subsets (from_nat_into (F i) r) (U j) G)"
    by (simp add: energy_graph_partitions_subsets_def sum.swap [where B = "{..<k}"])
  also have "\<dots> = (\<Sum>i<m. \<Sum>v\<in>F i. \<Sum>j<k. energy_graph_subsets v (U j) G)"
    by (intro sum.cong sum.card_from_nat_into refl)
  also have "\<dots> = ?rhs"
    by (simp add: energy_graph_partitions_subsets_def F_sums_Y)
  finally show ?thesis .
qed

proposition energy_graph_partitions_subsets_increase:
  assumes refX: "finite_graph_refines V Y n X m" and refU: "finite_graph_refines V' W l U k" 
    and "finite V" "finite V'"
  shows "energy_graph_partitions_subsets G X m U k \<le> energy_graph_partitions_subsets G Y n W l"
        (is "?lhs \<le> ?rhs")
proof -
  have finU: "\<And>i. i < k \<Longrightarrow> card (U i) > 0" and finY: "\<And>i. i < n \<Longrightarrow> card (Y i) > 0"
    using finite_graph_partition_gt0 finite_graph_refines_def assms by auto
  have "?lhs \<le> energy_graph_partitions_subsets G Y n U k"
    using assms energy_graph_partitions_subsets_increase_half finU refX by blast
  also have "\<dots> = energy_graph_partitions_subsets G U k Y n"
    by (meson energy_graph_partitions_subsets_commute)
  also have "\<dots> \<le> energy_graph_partitions_subsets G W l Y n"
    using assms energy_graph_partitions_subsets_increase_half finY refU by blast
  also have "\<dots> = ?rhs"
    by (simp add: energy_graph_partitions_subsets_commute)
  finally show ?thesis .
qed

text \<open>The original version of Gowers's Lemma 11 and Zhao's Lemma 3.9 
      is not general enough to be used for anything.\<close>
corollary mean_square_density_increase:
  assumes "finite_graph_refines V Y n X m" "finite V"
  shows "mean_square_density G X m \<le> mean_square_density G Y n"
  using assms energy_graph_partitions_subsets_increase by presburger 


text\<open>The Energy Boost Lemma (Lemma 3.10 in Zhao's notes) says that an 
irregular partition increases the energy substantially. We assume that @{term "\<U> \<subseteq> uverts G"} 
and @{term "\<W> \<subseteq> uverts G"} are not irregular, as witnessed by their subsets @{term"U1 \<subseteq> \<U>"} and @{term"W1 \<subseteq> \<W>"}.
The proof follows Lemma 12 of Gowers. \<close>

proposition energy_boost:
  fixes \<epsilon>::real and \<U> \<W> G
  defines "alpha \<equiv> edge_density \<U> \<W> G"
  defines "u \<equiv> \<lambda>X Y. edge_density X Y G - alpha"
  assumes "finite \<U>" "finite \<W>"
    and "U1 \<subset> \<U>" "W1 \<subset> \<W>" "\<epsilon> > 0"
    and U1: "card U1 \<ge> \<epsilon> * card \<U>" and W1: "card W1 \<ge> \<epsilon> * card \<W>"
    and gt: "\<bar>u U1 W1\<bar> > \<epsilon>"
  shows "(\<Sum>A \<in> {U1, \<U> - U1}. \<Sum>B \<in> {W1, \<W> - W1}. energy_graph_subsets A B G)
         \<ge> energy_graph_subsets \<U> \<W> G + \<epsilon>^4 * (card \<U> * card \<W>) / (card (uverts G))\<^sup>2"
          (is "?lhs \<ge> ?rhs")
proof -
  define UF where "UF \<equiv> {U1, \<U> - U1}"
  define WF where "WF \<equiv> {W1, \<W> - W1}"
  obtain [simp]: "finite \<U>" "finite \<W>"
    using assms by (meson finite_subset)
  then obtain 0: "card \<U> > 0" "card \<W> > 0"
    using assms by fastforce
  then obtain 1: "card U1 > 0" "card W1 > 0"
    by (smt (verit) U1 W1 \<open>\<epsilon> > 0\<close> of_nat_0_less_iff zero_less_mult_iff)
  then obtain [simp]: "finite U1" "finite W1"
    by (meson card_ge_0_finite)
  have 2 [simp]: "card x > 0" if "x \<in> UF" for x
    using "1"(1) UF_def assms that by fastforce
  have 3 [simp]: "card x > 0" if "x \<in> WF" for x
    using "1"(2) WF_def assms that by force
  have cardUW: "card \<U> = card U1 + card(\<U> - U1)" "card \<W> = card W1 + card(\<W> - W1)"
    using 0 1 \<open>U1 \<subset> \<U>\<close> \<open>W1 \<subset> \<W>\<close>
    by (metis card_eq_0_iff card_Diff_subset card_mono le_add_diff_inverse less_le)+

  have CU: "card (all_edges_between \<U> Z G) 
          = card (all_edges_between (\<U> - U1) Z G) + card (all_edges_between U1 Z G)" 
      if "finite Z" for Z
    using card_Un_disjnt all_edges_between_Un1 all_edges_between_disjnt1 \<open>U1 \<subset> \<U>\<close> that
    by (metis DiffD2 Un_Diff_cancel2 \<open>finite U1\<close> \<open>finite \<U>\<close> disjnt_iff finite_Diff 
        finite_all_edges_between sup.strict_order_iff)

  have CW: "card (all_edges_between Z \<W> G) 
          = card (all_edges_between Z (\<W> - W1) G) + card (all_edges_between Z W1 G)"
    if "finite Z" for Z
    using card_Un_disjnt all_edges_between_Un2 all_edges_between_disjnt2 \<open>W1 \<subset> \<W>\<close> that
    by (metis DiffD2 Un_Diff_cancel2 \<open>finite W1\<close> \<open>finite \<W>\<close> disjnt_iff finite_Diff 
        finite_all_edges_between sup.strict_order_iff)
  have [simp]: "U1 \<noteq> \<U> - U1" "W1 \<noteq> \<W> - W1"
    using assms by blast+
  have *: "(\<Sum>i\<in>UF. \<Sum>j\<in>WF. real (card (all_edges_between i j G))) 
         = card (all_edges_between \<U> \<W> G)"
    by (simp add: UF_def WF_def cardUW CU CW)
  have **: "real (card \<U>) * real (card \<W>) = (\<Sum>i\<in>UF. \<Sum>j\<in>WF. card i * card j)"
    by (simp add: UF_def WF_def cardUW algebra_simps)

  let ?S = "\<Sum>i\<in>UF. \<Sum>j\<in>WF. (card i * card j) / (card \<U> * card \<W>) * (edge_density i j G)\<^sup>2"
  have \<section>: "2 * (\<Sum>i\<in>UF. \<Sum>j\<in>WF.
                 (card i * card j) / (card \<U> * card \<W>) * (edge_density i j G)) 
         = alpha + alpha * (\<Sum>i\<in>UF. \<Sum>j\<in>WF. (card i * card j) / (card \<U> * card \<W>))"
    unfolding alpha_def
    by (simp add: * ** edge_density_def divide_simps flip: sum_divide_distrib)

  have "\<epsilon> * \<epsilon> \<le> u U1 W1 * u U1 W1"
    by (metis abs_ge_zero abs_mult_self_eq \<open>\<epsilon> > 0\<close> gt less_le mult_mono)
  then have "(\<epsilon>*\<epsilon>)*(\<epsilon>*\<epsilon>) \<le> (card U1 * card W1) / (card \<U> * card \<W>) * (u U1 W1)\<^sup>2"
    using 0 mult_mono [OF U1 W1]  \<open>\<epsilon> > 0\<close>
    apply (simp add: divide_simps eval_nat_numeral)
    by (smt (verit, del_insts) mult.assoc mult.commute mult_mono' of_nat_0_le_iff zero_le_mult_iff)
  also have "\<dots> \<le> (\<Sum>i\<in>UF. \<Sum>j\<in>WF.  (card i * card j) / (card \<U> * card \<W>) * (u i j)\<^sup>2)"
    by (simp add: UF_def WF_def)
  also have "\<dots> = ?S - 2 * alpha * (\<Sum>i\<in>UF. \<Sum>j\<in>WF. 
                         (card i * card j) / (card \<U> * card \<W>) * edge_density i j G)
                 + alpha\<^sup>2 * (\<Sum>i\<in>UF. \<Sum>j\<in>WF. (card i * card j) / (card \<U> * card \<W>))"
    by (simp add: u_def power2_diff mult_ac ring_distribs divide_simps 
          sum_distrib_left sum_distrib_right sum_subtractf sum.distrib flip: sum_divide_distrib)
  also have "\<dots> = ?S - alpha\<^sup>2"
    using \<section> by (simp add: power2_eq_square algebra_simps)
  finally have 12: "alpha\<^sup>2 + \<epsilon>^4 \<le> ?S"
    by (simp add: eval_nat_numeral)
  have "?rhs = (alpha\<^sup>2 + \<epsilon>^4) * (card \<U> * card \<W> / (card (uverts G))\<^sup>2)"
    unfolding alpha_def energy_graph_subsets_def
    by (simp add: ring_distribs divide_simps power2_eq_square)
  also have "\<dots> \<le> ?S * (card \<U> * card \<W> / (card (uverts G))\<^sup>2)"
    by (rule mult_right_mono [OF 12]) auto
  also have "\<dots> = ?lhs"
    using 0 unfolding energy_graph_subsets_def UF_def WF_def
    by (auto simp add: algebra_simps)
  finally show ?thesis .
qed

subsection \<open>Towards Zhao's Lemma 3.11\<close>

text\<open>Lemma 3.11 says that we can always find a refinement
that increases the energy by a certain amount.\<close>

text \<open>A necessary lemma for the tower of exponentials in the result. Angeliki's proof\<close>
lemma le_tower_2: "k * (2 ^ Suc k) \<le> 2^(2^k)"
proof (induction k rule: less_induct)
  case (less k)
  show ?case 
  proof (cases "k \<le> Suc (Suc 0)")
    case False
    define j where "j = k - Suc 0"
    have kj: "k = Suc j"
      using False j_def by force
    have "(3::nat) \<le> 2 ^ j"
      by (metis kj False Suc_leI less_trans_Suc less_exp not_less numeral_3_eq_3)
    then have \<section>: "(2^j + 3) \<le> (2::nat) ^ k"
      by (simp add: kj)
    have "k * (2 ^ Suc k) \<le> 6 * j * 2^j"
      using False by (simp add: kj)
    also have "\<dots> \<le> 6 * 2^(2^j)"
      using kj less.IH by force
    also have "\<dots> < 8 * 2^(2^j)" by simp
    also have "\<dots> = 2^(2^j + 3)"
      by (simp add: power_add) 
    also have "\<dots> \<le> 2^2^k"
      using \<section> by (metis One_nat_def less_2_cases_iff power_increasing_iff)
    finally show ?thesis
      by simp      
  qed (auto simp: le_Suc_eq)
qed


text \<open>Zhao's actual Lemma 3.11. However, the bound $m \le k 2 ^{k+1}$  
comes from a different source by Zhao: ``Graph Theory and Additive Combinatorics'', \<^url>\<open>https://yufeizhao.com/gtac/gtac17.pdf\<close>.
Zhao's original version, and Gowers', both have incorrect bounds.\<close>
proposition exists_refinement:
  assumes "finite_graph_partition (uverts G) P k" and "finite (uverts G)" 
    and irreg: "\<not> regular_partition \<epsilon> G P k" and "\<epsilon> > 0"
  obtains Q m where "finite_graph_refines (uverts G) Q m P k"                     
                    "mean_square_density G Q m \<ge> mean_square_density G P k + \<epsilon>^5" 
                    "\<And>i. i<k \<Longrightarrow> card {j. j<m \<and> Q j \<subseteq> P i} \<le> 2 ^ Suc k"
                    "m \<le> k * 2 ^ Suc k"
proof -
  define sum_pp where "sum_pp \<equiv> (\<Sum>(i,j) \<in> irregular_set \<epsilon> G P k. card (P i) * card (P j))"
  have "k \<noteq> 0"
    using assms unfolding regular_partition_def irregular_set_def
    by (intro notI) auto
  then have G_nonempty: "0 < card (uverts G)"
    by (metis assms(1) assms(2) finite_graph_partition_gt0 finite_graph_partition_le gr_zeroI leD)
  have part_GP: "partition_on (uverts G) (P ` {..<k})" and "inj_on P {..<k}"
    using assms by (auto simp: finite_graph_partition_eq)
  have disjfam_P: "disjoint_family_on P {..<k}"
    using assms by (auto simp: finite_graph_partition_def)
  have finP: "finite (P i)" "P i \<noteq> {}" if "i<k" for i
    using assms that finite_graph_partition_finite finite_graph_partition_nonempty by presburger+
  have spp: "sum_pp > \<epsilon> * (card (uverts G))\<^sup>2"
    using assms by (metis not_le regular_partition_def sum_pp_def)
  then have sum_irreg_pos: "sum_pp > 0"
    using \<open>\<epsilon> > 0\<close> G_nonempty less_asym by fastforce
  have "\<exists>X\<subset>P i.
         \<exists>Y\<subset>P j.
            \<epsilon> * card (P i) \<le> card X \<and>
            \<epsilon> * card (P j) \<le> card Y \<and>
            \<bar>edge_density X Y G - edge_density (P i) (P j) G\<bar> > \<epsilon>"
    if "(i,j) \<in> irregular_set \<epsilon> G P k" for i j
    using that assms(1) finite_graph_partition_subset by (simp add: irregular_set_def regular_pair_def not_le) 
  then obtain X0 Y0 
    where XY0_psub_P: "\<And>i j. \<lbrakk>(i,j) \<in> irregular_set \<epsilon> G P k\<rbrakk> \<Longrightarrow> X0 i j \<subset> P i \<and> Y0 i j \<subset> P j"
    and XY0_eps:
    "\<And>i j. \<lbrakk>(i,j) \<in> irregular_set \<epsilon> G P k\<rbrakk> 
        \<Longrightarrow> \<epsilon> * card (P i) \<le> card (X0 i j) \<and>
            \<epsilon> * card (P j) \<le> card (Y0 i j) \<and>
            \<bar>edge_density (X0 i j) (Y0 i j) G - edge_density (P i) (P j) G\<bar> > \<epsilon>"
    by metis

  define X where "X \<equiv> \<lambda>i j. if j>i then Y0 j i else X0 i j"
  define Y where "Y \<equiv> \<lambda>i j. if j>i then X0 j i else Y0 i j"

  have XY_psub_P: "\<And>i j. \<lbrakk>(i,j) \<in> irregular_set \<epsilon> G P k\<rbrakk> \<Longrightarrow> X i j \<subset> P i \<and> Y i j \<subset> P j"
    using XY0_psub_P by (force simp: X_def Y_def irregular_set_swap)
  have XY_eps:
    "\<And>i j. \<lbrakk>(i,j) \<in> irregular_set \<epsilon> G P k\<rbrakk> 
        \<Longrightarrow> \<epsilon> * card (P i) \<le> card (X i j) \<and>
            \<epsilon> * card (P j) \<le> card (Y i j) \<and>
            \<bar>edge_density (X i j) (Y i j) G - edge_density (P i) (P j) G\<bar> > \<epsilon>"
    using XY0_eps by (force simp: X_def Y_def edge_density_commute irregular_set_swap)

  have cardP: "card (P i) > 0" if "i<k" for i
    using assms finite_graph_partition_gt0 that by presburger

  have XY_nonempty: "X i j \<noteq> {}" "Y i j \<noteq> {}" if "(i,j) \<in> irregular_set \<epsilon> G P k" for i j
    using XY_eps [OF that] that \<open>\<epsilon> > 0\<close> cardP [of i] cardP [of j]
    by (auto simp: irregular_set_def mult_le_0_iff)

  text\<open>By the assumption that our partition is irregular, there are many irregular pairs.
       For each irregular pair, find pairs of subsets that witness irregularity.\<close>
  define XP where "XP i \<equiv> ((\<lambda>j. {X i j, P i - X i j}) ` {j. (i,j) \<in> irregular_set \<epsilon> G P k})" for i
  define YP where "YP j \<equiv> ((\<lambda>i. {Y i j, P j - Y i j}) ` {i. (i,j) \<in> irregular_set \<epsilon> G P k})" for j

  text \<open>include degenerate partition to ensure it works whether or not there's an irregular pair\<close>
  define PP where "PP \<equiv> \<lambda>i. insert {P i} (XP i \<union> YP i)"
  have finPP: "finite (PP i)" for i
    unfolding PP_def XP_def YP_def
    by (auto simp: inj_def intro!: finite_inverse_image finite_irregular_set)
  have inPP_fin: "P \<in> PP i \<Longrightarrow> finite P" for P i
    by (auto simp: PP_def XP_def YP_def)
  have fin_cf: "finite (common_refinement (PP i))" for i
    by (simp add: finPP finite_common_refinement inPP_fin)

  have part_cr: "partition_on (P i) (common_refinement (PP i))" if "i < k" for i
  proof (intro partition_on_common_refinement partition_onI)
    show "\<And>\<A>. \<A> \<in> PP i \<Longrightarrow> {} \<notin> \<A>"
      using that XY_nonempty XY_psub_P finP(2) by (fastforce simp add: PP_def XP_def YP_def)
  qed (auto simp: disjnt_iff PP_def XP_def YP_def dest: XY_psub_P)

  define QS where "QS i \<equiv> from_nat_into (common_refinement (PP i))" for i
  define r where "r i \<equiv> card (common_refinement (PP i))" for i
  have to_nat_on_cr: 
    "\<And>x i. \<lbrakk>x \<in> common_refinement (PP i); i < k\<rbrakk>
           \<Longrightarrow> to_nat_on (common_refinement (PP i)) x < r i"
    by (metis bij_betw_apply fin_cf lessThan_iff r_def to_nat_on_finite)
  have QSr_eq: "QS i ` {..<r i} = common_refinement (PP i)" for i
    by (simp add: QS_def r_def fin_cf bij_betw_from_nat_into_finite bij_betw_imp_surj_on)
  have inj_QS: "inj_on (QS i) {..<r i}" for i
    by (metis QSr_eq card_lessThan eq_card_imp_inj_on finite_lessThan r_def)
  have part_P_QS: "finite_graph_partition (P i) (QS i) (r i)" if "i<k" for i
    by (simp add: QSr_eq that finite_graph_partition_eq inj_QS part_cr)
  have QS_ne: "QS i q \<noteq> {}" if "i<k" "q < r i" for i q 
    by (metis QSr_eq imageI lessThan_iff part_cr partition_on_def that)
  have QS_subset_P: "QS i q \<subseteq> P i" if "i < k" "q < r i" for i q
    using part_cr [of i] QSr_eq that
    unfolding partition_on_def by blast
  then have QS_inject: "i = i'" if "QS i q = QS i' q'" "i<k" "i'<k" "q < r i" "q' < r i'" for i i' q q'
    by (metis QS_ne disjfam_P disjnt_def disjnt_iff disjnt_subset2 disjoint_family_on_def equals0I lessThan_iff that)

  define sumr where "sumr \<equiv> \<lambda>j. (\<Sum>i<j. r i)"
  define m where "m \<equiv> sumr k"
  define Q where "Q \<equiv> \<lambda>d. QS (part r k d) (d - sumr (part r k d))"
  have QS_Q: "QS j q = Q (sumr j + q)" if "j<k" "q < r j" for j q
    using that by (simp add: Q_def part_eq sumr_def)
  have Qm_eq_QS: "Q ` {..<m} = (\<Union>i<k.  (QS i) ` {..<r i})" (is "?lhs = ?rhs")
  proof
    show "?lhs \<subseteq> ?rhs"
      using QSr_eq r_def
      apply (simp add: image_subset_iff Ball_def Bex_def QS_def Q_def m_def)
      by (metis sumr_def add.right_neutral card.empty from_nat_into leD part)
    show "?rhs \<subseteq> ?lhs"
      using QS_Q m_def sum_layers_less sumr_def by fastforce
  qed
  have Qm_eq: "Q ` {..<m} = (\<Union>i<k. common_refinement (PP i))"
    using QSr_eq Qm_eq_QS by presburger

  show thesis
  proof
    show ref_QP: "finite_graph_refines (uverts G) Q m P k"
      unfolding finite_graph_refines_def
    proof (intro conjI strip)
      show "finite_graph_partition (uverts G) Q m"
        unfolding finite_graph_partition_eq
      proof (intro conjI partition_onI)
        have "\<Union> (Q ` {..<m}) = (\<Union>i<k. \<Union> (common_refinement (PP i)))"
          by (auto simp add: Qm_eq)
        also have "\<dots> = uverts G"
          using part_cr finite_graph_partition_equals assms(1) 
          by (force simp: partition_on_def)
        finally show "\<Union> (Q ` {..<m}) = uverts G" .
        show "disjnt p q"
          if "p \<in> Q ` {..<m}" and "q \<in> Q ` {..<m}" and "p \<noteq> q" for p q
        proof -
          from that 
          obtain i j where "i<k" "j<k" 
            and i: "p \<in> common_refinement (PP i)" and j: "q \<in> common_refinement (PP j)"
            by (auto simp add: Qm_eq)
          show ?thesis
          proof (cases "i=j")
            case True
            then show ?thesis
              using part_cr [of i]
              by (metis \<open>j < k\<close> i j pairwise_def partition_on_def \<open>p \<noteq> q\<close>)
          next
            case False
            have "p \<subseteq> P i \<and> q \<subseteq> P j"
              by (metis Union_upper \<open>i < k\<close> \<open>j < k\<close> i j part_cr partition_onD1)
            then show ?thesis
              using False \<open>i < k\<close> \<open>j < k\<close> part_GP disjfam_P
              by (metis disjnt_Union1 disjnt_Union2 disjnt_def disjoint_family_on_def i j lessThan_iff part_cr partition_onD1) 
          qed
        qed
        show "{} \<notin> Q ` {..<m}"
          by (simp add: Qm_eq common_refinement_def)
        show "inj_on Q {..<m}"
          using inj_QS QS_inject unfolding Q_def inj_on_def m_def sumr_def
          by (metis le_add_diff_inverse lessThan_iff nat_add_left_cancel_less part)
      qed
      fix i
      assume "i < m"
      have "part r k i < k" "(\<Sum>i < part r k i. r i) \<le> i \<and> i < (\<Sum>i < part r k i. r i) + r (part r k i)"
        by (metis \<open>i < m\<close> m_def part sumr_def)+
      then have "QS (part r k i) (i - sum r {..<part r k i}) \<subseteq> P (part r k i)"
        by (simp add: QS_subset_P less_diff_conv2)
      then show "\<exists>j<k. Q i \<subseteq> P j"
        unfolding Q_def sumr_def using \<open>part r k i < k\<close> by blast
    qed (use assms in auto)

    have inj_Q: "inj_on Q {..<m}"
      using finite_graph_partition_eq finite_graph_refines_def ref_QP by presburger
    let ?KK = "{..<k} \<times> {..<k}"
    let ?REG = "?KK - irregular_set \<epsilon> G P k"
    define sum_eps where "sum_eps \<equiv> (\<Sum>(i,j) \<in> irregular_set \<epsilon> G P k. \<epsilon>^4 * (card (P i) * card (P j)) / (card (uverts G))\<^sup>2)"
    { fix i j
      assume ij: "(i,j) \<in> irregular_set \<epsilon> G P k"
      then have "i<k" "j<k"
        by (auto simp: irregular_set_def)
      have "energy_graph_subsets (P i) (P j) G + \<epsilon>^4 * (card (P i) * card (P j)) / (card (uverts G))\<^sup>2
         \<le> (\<Sum>A \<in> {X i j, P i - X i j}. \<Sum>B \<in> {Y i j, P j - Y i j}. energy_graph_subsets A B G)"
        using XY_psub_P [OF ij] XY_eps [OF ij] assms
        by (intro energy_boost \<open>i < k\<close> \<open>j < k\<close> finP \<open>\<epsilon>>0\<close>) auto
      also have "\<dots> = (\<Sum>a<2. \<Sum>b<2. energy_graph_subsets (binary_partition (X i j) (P i) a) (binary_partition (Y i j) (P j) b) G)"
        using \<open>i < k\<close> \<open>j < k\<close>
        by (simp add: sum.reindex inj_binary_partition finP flip: binary_partition2_eq)
      also have "\<dots> = energy_graph_partitions_subsets G (binary_partition (X i j) (P i)) 2 (binary_partition (Y i j) (P j)) 2"
        by (simp add: energy_graph_partitions_subsets_def)
      finally have "energy_graph_subsets (P i) (P j) G + \<epsilon>^4 * (card (P i) * card (P j)) / (card (uverts G))\<^sup>2
                  \<le> energy_graph_partitions_subsets G (binary_partition (X i j) (P i)) 2 (binary_partition (Y i j) (P j)) 2" .
    } note A = this
    { fix i j
      assume ij: "(i,j) \<in> irregular_set \<epsilon> G P k"
      then have "i<k" "j<k" by (auto simp: irregular_set_def)
      have XPX: "{X i j, P i - X i j} \<in> PP i"
        using ij by (simp add: PP_def XP_def)
      have I: "finite_graph_partition (P i) (QS i) (r i)"
        by (simp add: QSr_eq \<open>i < k\<close> finite_graph_partition_eq inj_QS part_cr)
      moreover have "\<forall>q<r i. \<exists>b<2. QS i q \<subseteq> binary_partition (X i j) (P i) b"
        using common_refinement_exists [OF _ XPX]
        by (fastforce simp add: QS_def r_def numeral_2_eq_2 intro: from_nat_into)
      ultimately have ref_XP: "finite_graph_refines (P i) (QS i) (r i) (binary_partition (X i j) (P i)) 2"
        unfolding finite_graph_refines_def
        using XY_nonempty(1) XY_psub_P finite_graph_partition_binary_partition ij by presburger
      have YPY: "{Y i j, P j - Y i j} \<in> PP j"
        using ij by (simp add: PP_def YP_def)
      have J: "finite_graph_partition (P j) (QS j) (r j)"
        by (simp add: QSr_eq \<open>j < k\<close> finite_graph_partition_eq inj_QS part_cr)
      moreover have "\<forall>q<r j. \<exists>b<2. QS j q \<subseteq> binary_partition (Y i j) (P j) b"
        using common_refinement_exists [OF _ YPY]
        by (fastforce simp add: QS_def r_def numeral_2_eq_2 intro: from_nat_into)
      ultimately have ref_YP: "finite_graph_refines (P j) (QS j) (r j) (binary_partition (Y i j) (P j)) 2"
        unfolding finite_graph_refines_def
        using XY_nonempty(2) XY_psub_P finite_graph_partition_binary_partition ij by presburger
      have "energy_graph_partitions_subsets G (binary_partition (X i j) (P i)) 2 (binary_partition (Y i j) (P j)) 2
          \<le> energy_graph_partitions_subsets G (QS i) (r i) (QS j) (r j)"
        using \<open>i < k\<close> \<open>j < k\<close>
        by (simp add: finP energy_graph_partitions_subsets_increase [OF ref_XP ref_YP])
    } note B = this 
    have df_QS: "disjoint_family_on (\<lambda>i. QS i ` {..<r i}) {..<k}" 
      unfolding disjoint_family_on_def using QS_inject by force
    have "mean_square_density G P k + \<epsilon>^5 \<le> mean_square_density G P k + sum_eps"
    proof -
      have "\<epsilon>^5 = (\<epsilon> * (card (uverts G))\<^sup>2) * (\<epsilon>^4 / (card (uverts G))\<^sup>2)"
        using G_nonempty by (simp add: field_simps eval_nat_numeral)
      also have "\<dots> \<le> sum_pp * (sum_eps / sum_pp)"
      proof (rule mult_mono)
        show "\<epsilon>^4 / real ((card (uverts G))\<^sup>2) \<le> sum_eps / sum_pp"
          using sum_irreg_pos sum_eps_def sum_pp_def
          by (auto simp add: case_prod_unfold sum.neutral simp flip: sum_distrib_left sum_divide_distrib of_nat_sum of_nat_mult)
      qed (use spp sum_nonneg in auto)
      also have "\<dots> \<le> sum_eps"
        by (simp add: sum_irreg_pos)
      finally show ?thesis by simp
    qed
    also have "\<dots> = (\<Sum>(i,j)\<in>?REG. energy_graph_subsets (P i) (P j) G) 
                   + (\<Sum>(i,j)\<in>irregular_set \<epsilon> G P k. energy_graph_subsets (P i) (P j) G) + sum_eps"
      by (simp add: energy_graph_partitions_subsets_def sum.cartesian_product irregular_set_subset sum.subset_diff)
  also have "\<dots> \<le> (\<Sum>(i,j) \<in> ?REG. energy_graph_subsets (P i) (P j) G)
                   + (\<Sum>(i,j) \<in> irregular_set \<epsilon> G P k. energy_graph_partitions_subsets G (binary_partition (X i j) (P i)) 2 (binary_partition (Y i j) (P j)) 2)"
    using A unfolding sum_eps_def case_prod_unfold
    by (force intro: sum_mono simp flip: energy_graph_partitions_subsets_def sum.distrib)
    also have "\<dots> \<le> (\<Sum>(i,j) \<in> ?REG. energy_graph_partitions_subsets G (QS i) (r i) (QS j) (r j))
                   + (\<Sum>(i,j) \<in> irregular_set \<epsilon> G P k. energy_graph_partitions_subsets G (binary_partition (X i j) (P i)) 2 (binary_partition (Y i j) (P j)) 2)"
      by(auto simp: part_P_QS finP intro!: sum_mono energy_graph_partition_increase)
    also have "\<dots> \<le> (\<Sum>(i,j) \<in> ?REG. energy_graph_partitions_subsets G (QS i) (r i) (QS j) (r j)) 
                  + (\<Sum>(i,j) \<in> irregular_set \<epsilon> G P k. energy_graph_partitions_subsets G (QS i) (r i) (QS j) (r j))"
      using B
    proof (intro sum_mono add_mono ordered_comm_monoid_add_class.sum_mono2)
    qed (auto split: prod.split)
    also have "\<dots> = (\<Sum>(i,j) \<in> ?KK. energy_graph_partitions_subsets G (QS i) (r i) (QS j) (r j))"
      by (metis (no_types, lifting) finite_SigmaI finite_lessThan irregular_set_subset sum.subset_diff)
    also have "\<dots> = (\<Sum>i<k. \<Sum>j<k. energy_graph_partitions_subsets G (QS i) (r i) (QS j) (r j))"
      by (simp flip: sum.cartesian_product)
    also have "\<dots> = (\<Sum>A \<in> Q ` {..<m}. \<Sum>B \<in> Q ` {..<m}. energy_graph_subsets A B G)"
      by (simp add: Qm_eq_QS sum.UNION_disjoint_family df_QS energy_graph_partitions_subsets_def 
          inj_QS sum.reindex  sum.swap [of _ "{..<k}" "{..<r _}"])
    also have "\<dots> = (\<Sum>i<m. \<Sum>j<m. energy_graph_subsets (Q i) (Q j) G)"
      by (simp add: inj_Q sum.reindex)
    also have "\<dots> = mean_square_density G Q m"
      by (simp add: mean_square_density energy_graph_subsets_def sum_divide_distrib)
    finally show "mean_square_density G P k + \<epsilon> ^ 5 \<le> mean_square_density G Q m" .

    let ?QinP = "\<lambda>i. {j. j < m \<and> Q j \<subseteq> P i}"
    show card_QP: "card (?QinP i) \<le> 2 ^ Suc k"
      if "i < k" for i 
    proof -
      have card_cr: "card (common_refinement (PP i)) \<le> 2 ^ Suc k"
      proof -
        have "card (common_refinement (PP i)) \<le> prod card (PP i)" 
          by (intro card_common_refinement finPP inPP_fin)
        also have "\<dots> = prod card (XP i \<union> YP i)"
          unfolding PP_def
        proof (subst prod.insert)
          have XYP_2: "\<And>i \<A>. \<A> \<in> XP i \<union> YP i \<Longrightarrow> card \<A> = 2" 
            by (auto simp: XP_def YP_def; metis Diff_iff XY_psub_P card_2_iff psubset_imp_ex_mem)
          then show "{P i} \<notin> XP i \<union> YP i"
            by fastforce
        qed (use PP_def finPP in auto)
        also have "\<dots> \<le> 2 ^ Suc k" 
        proof (rule prod_le_power)
          define XS where "XS \<equiv> (\<lambda>l. {X0 i l, P i - X0 i l}) ` {..i}"
          define YS where "YS \<equiv> (\<lambda>l. {Y0 l i, P i - Y0 l i}) ` {i..<k}"
          have "card XS \<le> Suc i" "card YS \<le> k-i"
            unfolding XS_def YS_def using card_image_le by force+
          with that have k': "card XS + card YS \<le> Suc k"
            by linarith
          have finXYS: "finite (XS \<union> YS)"
            by (simp add: XS_def YS_def)
          have "XP i \<union> YP i \<subseteq> XS \<union> YS"
            by (auto simp: XP_def YP_def X_def Y_def XS_def YS_def irregular_set_def)
          then have "card (XP i \<union> YP i) \<le> card XS + card YS"
            by (meson card_Un_le card_mono finXYS order_trans)
          then show "card (XP i \<union> YP i) \<le> Suc k"
            using k' le_trans by blast
          fix x
          assume "x \<in> XP i \<union> YP i"
          then show "0 \<le> card x \<and> card x \<le> 2"
            by (auto simp: XP_def YP_def card_insert_le_m1)
        qed auto
        finally show ?thesis .
      qed
      have "i' = i" if "QS i' q \<subseteq> P i" "i'<k" "q < r i'" for i' q
        using disjfam_P unfolding disjoint_family_on_def
        by (metis QS_ne QS_subset_P \<open>i < k\<close> inf.bounded_iff lessThan_iff subset_empty that)
      then have "?QinP i \<subseteq> {sumr i..< sumr (Suc i)}"
        by (clarsimp simp: Q_def sumr_def m_def) (metis add_less_cancel_left le_add_diff_inverse part)
      then have "card (?QinP i) \<le> card {sumr i..< sumr (Suc i)}"
        by (meson card_mono finite_atLeastLessThan)
      also have "\<dots> \<le> 2 ^ Suc k"
        using card_cr by (simp add: sumr_def r_def)
      finally show ?thesis .
    qed
    have "m = card {j. j < m}"
      by simp
    also have "\<dots> \<le> card (\<Union>i<k. ?QinP i)"
    proof (rule card_mono)
      show "{j. j < m} \<subseteq> (\<Union>i<k. ?QinP i)"
        using ref_QP by (auto simp: finite_graph_refines_def)
    qed auto
    also have "\<dots> \<le> (\<Sum>i<k. card (?QinP i))"
      using card_UN_le by blast
    also have "\<dots> \<le> (\<Sum>i<k. 2 ^ Suc k)"
      using card_QP by (metis (no_types, lifting) lessThan_iff sum_mono)
    finally show "m \<le> k * 2 ^ Suc k" 
      by simp
  qed
qed

subsection \<open>The Regularity Proof Itself\<close>

text\<open>Szemerédi's Regularity Lemma is Theorem 3.5 in Zhao's notes.\<close>

text\<open>We start with a trivial partition (one part). If it is already $\epsilon$-regular, we are done. If
not, we refine it by applying lemma @{thm[source]"exists_refinement"} above, which increases the
energy. We can repeat this step, but it cannot increase forever: by @{thm [source]
mean_square_density_bounded} it cannot exceed~1. This defines an algorithm that must stop
after at most $\epsilon^{-5}$ steps, resulting in an $\epsilon$-regular partition.\<close>
theorem Szemeredi_Regularity_Lemma:
  assumes "\<epsilon> > 0"
  obtains M where "\<And>G. card (uverts G) > 0 \<Longrightarrow> \<exists>P k. regular_partition \<epsilon> G P k \<and> k \<le> M"
proof 
  fix G
  assume "card (uverts G) > 0"
  then obtain finG: "finite (uverts G)" and nonempty: "uverts G \<noteq> {}"
    by (simp add: card_gt_0_iff) 
  define \<Phi> where "\<Phi> \<equiv> \<lambda>Q m P k. finite_graph_refines (uverts G) Q m P k \<and> 
                                 mean_square_density G Q m \<ge> mean_square_density G P k + \<epsilon>^5 \<and> 
                                 m \<le> k * 2 ^ Suc k"
  define nxt where "nxt \<equiv> \<lambda>(P,k). if regular_partition \<epsilon> G P k then (P,k) else SOME (Q,m). \<Phi> Q m P k"
  define iter where "iter \<equiv> \<lambda>i. (nxt ^^ i) ((\<lambda>u. uverts G, Suc 0))"
  define last where "last \<equiv> Suc (nat\<lceil>1 / \<epsilon> ^ 5\<rceil>)"
  have iter_Suc [simp]: "iter (Suc i) = nxt (iter i)" for i
    by (simp add: iter_def)
  have \<Phi>: "\<Phi> Q m P k"
    if Pk: "finite_graph_partition (uverts G) P k" and irreg: "\<not> regular_partition \<epsilon> G P k" 
       and "(Q,m) = nxt (P,k)" for P k Q m
    using that exists_refinement [OF Pk finG irreg assms] irreg
    apply (simp add: nxt_def \<Phi>_def)
    by (metis (mono_tags, lifting) case_prod_conv someI)
  have iter_finite_graph_partition: "case iter i of (P,k) \<Rightarrow> finite_graph_partition (uverts G) P k" for i
  proof (induction i)
    case 0
    then show ?case
      by (simp add: iter_def nonempty trivial_graph_partition_exists)
  next
    case (Suc i)
    with \<Phi> show ?case
      apply (simp add: nxt_def \<Phi>_def split: prod.split)
      by (metis (no_types, lifting) case_prodD finite_graph_refines_def)
  qed
  have False if irreg: "\<And>i. i\<le>last \<Longrightarrow> (case iter i of (P,k) \<Rightarrow> \<not> regular_partition \<epsilon> G P k)"
  proof -
    have \<Phi>_loop: "\<Phi> Q m P k" if "nxt (P,k) = (Q,m)" "iter i = (P,k)" "i\<le>last" for i Q m P k
      by (metis \<Phi> case_prod_conv irreg iter_finite_graph_partition that)
    have iter_grow: "(case iter i of (Q,m) \<Rightarrow> mean_square_density G Q m) \<ge> i * \<epsilon>^5" if "i\<le>last" for i
      using that
    proof (induction i)
      case (Suc i)
      then show ?case
        by (auto simp add: algebra_simps \<Phi>_def split: prod.split prod.split_asm dest: \<Phi>_loop)
    qed (auto simp: iter_def)
    have "last * \<epsilon>^5 \<le> (case iter last of (Q,m) \<Rightarrow> mean_square_density G Q m)"
      by (simp add: iter_grow)
    also have "\<dots> \<le> 1"
      by (metis (no_types, lifting) finG case_prod_beta iter_finite_graph_partition mean_square_density_bounded)
    finally have "real last * \<epsilon> ^ 5 \<le> 1" .
    with assms show False
      unfolding last_def by (meson lessI natceiling_lessD not_less pos_divide_less_eq zero_less_power)
  qed
  then obtain i where "i \<le> last" and "case iter i of (P,k) \<Rightarrow> regular_partition \<epsilon> G P k"
    by force
  then have reglar: "case iter (i + d) of (P,k) \<Rightarrow> regular_partition \<epsilon> G P k" for d
    by (induction d) (auto simp add: nxt_def split: prod.split prod.split_asm)
  define tower where "tower \<equiv> \<lambda>k. (power(2::nat) ^^ k) 2"
  have [simp]: "tower (Suc k) = 2 ^ tower k" for k
    by (simp add: tower_def)
  have iter_tower: "(case iter i of (Q,m) \<Rightarrow> m) \<le> tower (2*i)" for i
  proof (induction i)
    case 0
    then show ?case
      by (auto simp: iter_def tower_def)
  next
    case (Suc i)
    then obtain Q m P k where Qm: "nxt (P,k) = (Q,m)" "iter i = (P,k)" and kle: "k \<le> tower (2 * i)"
      by (metis case_prod_conv surj_pair)
    then have *: "m \<le> k * 2 ^ Suc k" 
      using iter_finite_graph_partition [of i] \<Phi> 
      by (smt (verit, ccfv_SIG) Suc_leD \<Phi>_def case_prod_conv le_eq_less_or_eq mult_le_mono2 nxt_def 
                    power2_eq_square power2_nat_le_imp_le prod.simps(1) self_le_ge2_pow)
    also have "\<dots> \<le> 2 ^ 2 ^ tower (2 * i)"
      by (metis (full_types) One_nat_def le_tower_2 lessI numeral_2_eq_2 order.trans power_increasing_iff kle)
    finally show ?case
      by (simp add: Qm)
  qed
  then show "\<exists>P k. regular_partition \<epsilon> G P k \<and> k \<le> tower(2 * last)"
    using reglar \<open>i \<le> last\<close> by (metis case_prod_beta nat_le_iff_add)
qed 

text \<open>The actual value of the bound is visible above: a tower of exponentials of height $2(1 + \epsilon^{-5})$.\<close>

end
