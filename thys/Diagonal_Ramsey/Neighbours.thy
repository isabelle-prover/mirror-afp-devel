section \<open>Background material: the neighbours of vertices\<close>

text \<open>Preliminaries for the Book Algorithm\<close>

theory Neighbours imports "Ramsey_Bounds.Ramsey_Bounds"

begin

abbreviation set_difference :: "['a set,'a set] \<Rightarrow> 'a set" (infixl \<open>\<setminus>\<close> 65)
  where "A \<setminus> B \<equiv> A-B"

subsection \<open>Preliminaries on graphs\<close>

context ulgraph
begin

text \<open>The set of \emph{undirected} edges between two sets\<close>
definition all_edges_betw_un :: "'a set \<Rightarrow> 'a set \<Rightarrow> 'a set set" where
  "all_edges_betw_un X Y \<equiv> {{x, y}| x y. x \<in> X \<and> y \<in> Y \<and> {x, y} \<in> E}"

lemma all_edges_betw_un_commute1: "all_edges_betw_un X Y \<subseteq> all_edges_betw_un Y X"
  by (smt (verit, del_insts) Collect_mono all_edges_betw_un_def insert_commute)

lemma all_edges_betw_un_commute: "all_edges_betw_un X Y = all_edges_betw_un Y X"
  by (simp add: all_edges_betw_un_commute1 subset_antisym)

lemma all_edges_betw_un_iff_mk_edge: "all_edges_betw_un X Y = mk_edge ` all_edges_between X Y"
  using all_edges_between_set all_edges_betw_un_def by presburger

lemma all_uedges_betw_subset: "all_edges_betw_un X Y \<subseteq> E"
  by (auto simp: all_edges_betw_un_def)

lemma all_uedges_betw_I: "x \<in> X \<Longrightarrow> y \<in> Y \<Longrightarrow> {x, y} \<in> E \<Longrightarrow> {x, y} \<in> all_edges_betw_un X Y"
  by (auto simp: all_edges_betw_un_def)

lemma all_edges_betw_un_subset: "all_edges_betw_un X Y \<subseteq> Pow (X\<union>Y)"
  by (auto simp: all_edges_betw_un_def)

lemma all_edges_betw_un_empty [simp]:
  "all_edges_betw_un {} Z = {}" "all_edges_betw_un Z {} = {}"
  by (auto simp: all_edges_betw_un_def)

lemma card_all_uedges_betw_le: 
  assumes "finite X" "finite Y"
  shows "card (all_edges_betw_un X Y) \<le> card (all_edges_between X Y)"
  by (simp add: all_edges_betw_un_iff_mk_edge assms card_image_le finite_all_edges_between)

lemma all_edges_betw_un_le: 
  assumes "finite X" "finite Y"
  shows "card (all_edges_betw_un X Y) \<le> card X * card Y"
  by (meson assms card_all_uedges_betw_le max_all_edges_between order_trans)

lemma all_edges_betw_un_insert1:
  "all_edges_betw_un (insert v X) Y = ({{v, y}| y. y \<in> Y} \<inter> E) \<union> all_edges_betw_un X Y"
  by (auto simp: all_edges_betw_un_def)

lemma all_edges_betw_un_insert2:
  "all_edges_betw_un X (insert v Y) = ({{x, v}| x. x \<in> X} \<inter> E) \<union> all_edges_betw_un X Y"
  by (auto simp: all_edges_betw_un_def)

lemma all_edges_betw_un_Un1:
  "all_edges_betw_un (X \<union> Y) Z = all_edges_betw_un X Z \<union> all_edges_betw_un Y Z"
  by (auto simp: all_edges_betw_un_def)

lemma all_edges_betw_un_Un2:
  "all_edges_betw_un X (Y \<union> Z) = all_edges_betw_un X Y \<union> all_edges_betw_un X Z"
  by (auto simp: all_edges_betw_un_def)

lemma finite_all_edges_betw_un:
  assumes "finite X" "finite Y"
  shows "finite (all_edges_betw_un X Y)"
  by (simp add: all_edges_betw_un_iff_mk_edge assms finite_all_edges_between)

lemma all_edges_betw_un_Union1:
  "all_edges_betw_un (Union \<X>) Y = (\<Union>X\<in>\<X>. all_edges_betw_un X Y)"
  by (auto simp: all_edges_betw_un_def)

lemma all_edges_betw_un_Union2:
  "all_edges_betw_un X (Union \<Y>) = (\<Union>Y\<in>\<Y>. all_edges_betw_un X Y)"
  by (auto simp: all_edges_betw_un_def)

lemma all_edges_betw_un_mono1:
  "Y \<subseteq> Z \<Longrightarrow> all_edges_betw_un Y X \<subseteq> all_edges_betw_un Z X"
  by (auto simp: all_edges_betw_un_def)

lemma all_edges_betw_un_mono2:
  "Y \<subseteq> Z \<Longrightarrow> all_edges_betw_un X Y \<subseteq> all_edges_betw_un X Z"
  by (auto simp: all_edges_betw_un_def)

lemma disjnt_all_edges_betw_un:
  assumes "disjnt X Y" "disjnt X Z"
  shows "disjnt (all_edges_betw_un X Z) (all_edges_betw_un Y Z)"
  using assms by (auto simp: all_edges_betw_un_def disjnt_iff doubleton_eq_iff)

end

subsection \<open>Neighbours of a vertex\<close>

definition Neighbours :: "'a set set \<Rightarrow> 'a \<Rightarrow> 'a set" where
  "Neighbours \<equiv> \<lambda>E x. {y. {x,y} \<in> E}"

lemma in_Neighbours_iff: "y \<in> Neighbours E x \<longleftrightarrow> {x,y} \<in> E"
  by (simp add: Neighbours_def)

lemma finite_Neighbours:
  assumes "finite E"
  shows "finite (Neighbours E x)"
proof -
  have "Neighbours E x \<subseteq> Neighbours {X\<in>E. finite X} x"
    by (auto simp: Neighbours_def)
  also have "\<dots> \<subseteq> (\<Union>{X\<in>E. finite X})"
    by (meson Union_iff in_Neighbours_iff insert_iff subset_iff)
  finally show ?thesis
    using assms finite_subset by fastforce
qed

lemma (in fin_sgraph) not_own_Neighbour: "E' \<subseteq> E \<Longrightarrow> x \<notin> Neighbours E' x"
  by (force simp: Neighbours_def singleton_not_edge)

context fin_sgraph
begin

declare singleton_not_edge [simp]

text \<open>"A graph on vertex set @{term"S \<union> T"}  that contains all edges incident to @{term"S"}"
  (page 3). In fact, @{term S} is a clique and every vertex in @{term T} 
  has an edge into @{term S}.\<close>
definition book :: "'a set \<Rightarrow> 'a set \<Rightarrow> 'a set set \<Rightarrow> bool" where
  "book \<equiv> \<lambda>S T F. disjnt S T \<and> all_edges_betw_un S (S\<union>T) \<subseteq> F"

text \<open>Cliques of a given number of vertices; the definition of clique from Ramsey is used\<close>

definition size_clique :: "nat \<Rightarrow> 'a set \<Rightarrow> 'a set set \<Rightarrow> bool" where
  "size_clique p K F \<equiv> card K = p \<and> clique K F \<and> K \<subseteq> V"

lemma size_clique_smaller: "\<lbrakk>size_clique p K F; p' < p\<rbrakk> \<Longrightarrow> \<exists>K'. size_clique p' K' F"
  unfolding size_clique_def
  by (meson card_Ex_subset order.trans less_imp_le_nat smaller_clique)

subsection \<open>Density: for calculating the parameter p\<close>

definition "edge_card \<equiv> \<lambda>C X Y. card (C \<inter> all_edges_betw_un X Y)"

definition "gen_density \<equiv> \<lambda>C X Y. edge_card C X Y / (card X * card Y)"

lemma edge_card_empty [simp]: "edge_card C {} X = 0" "edge_card C X {} = 0"
  by (auto simp: edge_card_def)

lemma edge_card_commute: "edge_card C X Y = edge_card C Y X"
  using all_edges_betw_un_commute edge_card_def by presburger

lemma edge_card_le: 
  assumes "finite X" "finite Y"
  shows "edge_card C X Y \<le> card X * card Y"
proof -
  have "edge_card C X Y \<le> card (all_edges_betw_un X Y)"
    by (simp add: assms card_mono edge_card_def finite_all_edges_betw_un)
  then show ?thesis
    by (meson all_edges_betw_un_le assms le_trans)
qed

text \<open>the assumption that @{term Z} is disjoint from @{term X} (or @{term Y}) is necessary\<close>
lemma edge_card_Un:
  assumes "disjnt X Y" "disjnt X Z" "finite X" "finite Y"
  shows "edge_card C (X \<union> Y) Z = edge_card C X Z + edge_card C Y Z"
proof -
  have [simp]: "finite (all_edges_betw_un U Z)" for U
    by (meson all_uedges_betw_subset fin_edges finite_subset)
  have "disjnt (C \<inter> all_edges_betw_un X Z) (C \<inter> all_edges_betw_un Y Z)"
    using assms by (meson Int_iff disjnt_all_edges_betw_un disjnt_iff)
  then show ?thesis
    by (simp add: edge_card_def card_Un_disjnt all_edges_betw_un_Un1 Int_Un_distrib)
qed

lemma edge_card_diff:
  assumes "Y\<subseteq>X" "disjnt X Z" "finite X" 
  shows "edge_card C (X-Y) Z = edge_card C X Z - edge_card C Y Z"
proof -
  have "(X\<setminus>Y) \<union> Y = X" "disjnt (X\<setminus>Y) Y"
    by (auto simp: Un_absorb2 assms disjnt_iff)
  then show ?thesis
    by (metis add_diff_cancel_right' assms disjnt_Un1 edge_card_Un finite_Diff finite_subset)
qed

lemma edge_card_mono:
  assumes "Y\<subseteq>X" shows "edge_card C Y Z \<le> edge_card C X Z"
  unfolding edge_card_def
proof (intro card_mono)
  show "finite (C \<inter> all_edges_betw_un X Z)"
    by (meson all_uedges_betw_subset fin_edges finite_Int finite_subset)
  show "C \<inter> all_edges_betw_un Y Z \<subseteq> C \<inter> all_edges_betw_un X Z"
    by (meson Int_mono all_edges_betw_un_mono1 assms subset_refl)
qed

lemma edge_card_eq_sum_Neighbours:
  assumes "C\<subseteq>E" and B: "finite B" "disjnt A B"
  shows "edge_card C A B = (\<Sum>i\<in>B. card (Neighbours C i \<inter> A))"
  using B
proof (induction B)
  case empty
  then show ?case
    by (auto simp: edge_card_def)
next
  case (insert b B)
  have "finite C"
    using assms(1) fin_edges finite_subset by blast
  have bij: "bij_betw (\<lambda>e. the_elem(e-{b})) (C \<inter> {{x, b} |x. x \<in> A}) (Neighbours C b \<inter> A)"
    unfolding bij_betw_def
  proof
    have [simp]: "the_elem ({x, b} - {b}) = x" if "x \<in> A" for x
      using insert.prems by (simp add: disjnt_iff insert_Diff_if that)
    show "inj_on (\<lambda>e. the_elem (e - {b})) (C \<inter> {{x, b} |x. x \<in> A})"
      by (auto simp: inj_on_def)
    show "(\<lambda>e. the_elem (e - {b})) ` (C \<inter> {{x, b} |x. x \<in> A}) = Neighbours C b \<inter> A"
      by (fastforce simp: Neighbours_def insert_commute image_iff Bex_def)
  qed
  have "(C \<inter> all_edges_betw_un A (insert b B)) = (C \<inter> ({{x, b} |x. x \<in> A} \<union> all_edges_betw_un A B))"
    using \<open>C \<subseteq> E\<close> by (auto simp: all_edges_betw_un_insert2)
  then have "edge_card C A (insert b B) = card ((C \<inter> ({{x,b} |x. x \<in> A}) \<union> (C \<inter> all_edges_betw_un A B)))"
    by (simp add: edge_card_def Int_Un_distrib)
  also have "\<dots> = card (C \<inter> {{x,b} |x. x \<in> A}) + card (C \<inter> all_edges_betw_un A B)"
  proof (rule card_Un_disjnt)
    show "disjnt (C \<inter> {{x, b} |x. x \<in> A}) (C \<inter> all_edges_betw_un A B)"
      using insert by (auto simp: disjnt_iff all_edges_betw_un_def doubleton_eq_iff)
  qed (use \<open>finite C\<close> in auto)
  also have "\<dots> = card (Neighbours C b \<inter> A) + card (C \<inter> all_edges_betw_un A B)"
    using bij_betw_same_card [OF bij] by simp
  also have "\<dots> = (\<Sum>i\<in>insert b B. card (Neighbours C i \<inter> A))"
    using insert by (simp add: edge_card_def)
  finally show ?case .
qed

lemma sum_eq_card: "finite A \<Longrightarrow> (\<Sum>x \<in> A. if x \<in> B then 1 else 0) = card (A\<inter>B)"
  by (metis (no_types, lifting) card_eq_sum sum.cong sum.inter_restrict)

lemma sum_eq_card_Neighbours:
  assumes "x \<in> V" "C \<subseteq> E"
  shows "(\<Sum>y \<in> V\<setminus>{x}. if {x,y} \<in> C then 1 else 0) = card (Neighbours C x)"
proof -
  have "Neighbours C x = (V \<setminus> {x}) \<inter> {y. {x, y} \<in> C}"
    using assms wellformed by (auto simp: Neighbours_def)
  with finV sum_eq_card [of _ "{y. {x,y}\<in>C}"] show ?thesis by simp
qed

lemma Neighbours_insert_NO_MATCH: "NO_MATCH {} C \<Longrightarrow> Neighbours (insert e C) x = Neighbours {e} x \<union> Neighbours C x"
  by (auto simp: Neighbours_def)

lemma Neighbours_sing_2:
  assumes "e \<in> E"
  shows "(\<Sum>x\<in>V. card (Neighbours {e} x)) = 2"
proof -
  obtain u v where uv: "e = {u,v}" "u\<noteq>v"
    by (meson assms card_2_iff two_edges)
  then have "u \<in> V" "v \<in> V"
    using assms wellformed uv by blast+
  have *: "Neighbours {e} x = (if x=u then {v} else if x=v then {u} else {})" for x
    by (auto simp: Neighbours_def uv doubleton_eq_iff)
  show ?thesis
    using \<open>u\<noteq>v\<close>
    by (simp add: * if_distrib [of card] finV sum.delta_remove \<open>u \<in> V\<close> \<open>v \<in> V\<close> cong: if_cong)
qed

lemma sum_Neighbours_eq_card:
  assumes "finite C" "C\<subseteq>E" 
  shows "(\<Sum>i\<in>V. card (Neighbours C i)) = card C * 2"
  using assms
proof (induction C)
  case empty
  then show ?case
    by (auto simp: Neighbours_def)
next
  case (insert e C)
  then have [simp]: "Neighbours {e} x \<inter> Neighbours C x = {}" for x
    by (auto simp: Neighbours_def)
  with insert show ?case
    by (auto simp: card_Un_disjoint finite_Neighbours Neighbours_insert_NO_MATCH sum.distrib Neighbours_sing_2)
qed

lemma gen_density_empty [simp]: "gen_density C {} X = 0" "gen_density C X {} = 0"
  by (auto simp: gen_density_def)

lemma gen_density_commute: "gen_density C X Y = gen_density C Y X"
  by (simp add: edge_card_commute gen_density_def)

lemma gen_density_ge0: "gen_density C X Y \<ge> 0"
  by (auto simp: gen_density_def)

lemma gen_density_gt0: 
  assumes "finite X" "finite Y" "{x,y} \<in> C" "x \<in> X" "y \<in> Y" "C \<subseteq> E"
  shows "gen_density C X Y > 0"
proof -
  have xy: "{x,y} \<in> all_edges_betw_un X Y"
    using assms by (force simp: all_edges_betw_un_def)
  moreover have "finite (all_edges_betw_un X Y)"
    by (simp add: assms finite_all_edges_betw_un)
  ultimately have "edge_card C X Y > 0"
    by (metis IntI assms(3) card_0_eq edge_card_def emptyE finite_Int gr0I)
  with xy show ?thesis
    using assms gen_density_def less_eq_real_def by fastforce
qed

lemma gen_density_le1: "gen_density C X Y \<le> 1"
  unfolding gen_density_def
  by (smt (verit) card.infinite divide_le_eq_1 edge_card_le mult_eq_0_iff of_nat_le_0_iff of_nat_mono)

lemma gen_density_le_1_minus: 
  shows "gen_density C X Y \<le> 1 - gen_density (E-C) X Y"
proof (cases "finite X \<and> finite Y")
  case True
  have "C \<inter> all_edges_betw_un X Y \<union> (E - C) \<inter> all_edges_betw_un X Y = all_edges_betw_un X Y"
    by (auto simp: all_edges_betw_un_def)
  with True have "(edge_card C X Y) + (edge_card (E - C) X Y) \<le> card (all_edges_betw_un X Y)"
    unfolding edge_card_def
    by (metis Diff_Int_distrib2 Diff_disjoint card_Un_disjoint card_Un_le finite_Int finite_all_edges_betw_un)
  with True show ?thesis
    apply (simp add: gen_density_def divide_simps)
    by (smt (verit) all_edges_betw_un_le of_nat_add of_nat_mono of_nat_mult)
qed (auto simp: gen_density_def)

lemma gen_density_lt1: 
  assumes "{x,y} \<in> E-C" "x \<in> X" "y \<in> Y" "C \<subseteq> E"
  shows "gen_density C X Y < 1"
proof (cases "finite X \<and> finite Y")
  case True
  then have "0 < gen_density (E - C) X Y"
    using assms gen_density_gt0 by auto
  have "gen_density C X Y \<le> 1 - gen_density (E - C) X Y"
    by (intro gen_density_le_1_minus)
  then show ?thesis
    using \<open>0 < gen_density (E - C) X Y\<close> by linarith
qed (auto simp: gen_density_def)

lemma gen_density_le_iff:
  assumes "disjnt X Z" "finite X" "Y\<subseteq>X" "Y \<noteq> {}" "finite Z"
  shows "gen_density C X Z \<le> gen_density C Y Z \<longleftrightarrow> 
        edge_card C X Z / card X \<le> edge_card C Y Z / card Y"
  using assms by (simp add: gen_density_def divide_simps mult_less_0_iff zero_less_mult_iff)

text \<open>"Removing vertices whose degree is less than the average can only increase the density 
from the remaining set" (page 17) \<close>
lemma gen_density_below_avg_ge:
  assumes "disjnt X Z" "finite X" "Y\<subset>X" "finite Z" 
    and genY: "gen_density C Y Z \<le> gen_density C X Z"
  shows "gen_density C (X-Y) Z \<ge> gen_density C X Z"
proof -
  have "real (edge_card C Y Z) / card Y \<le> real (edge_card C X Z) / card X"
    using assms
    by (force simp: gen_density_def divide_simps zero_less_mult_iff split: if_split_asm)
  have "card Y < card X"
    by (simp add: assms psubset_card_mono)
  have *: "finite Y" "Y \<subseteq> X" "X\<noteq>{}"
    using assms finite_subset by blast+
  then
  have "card X * edge_card C Y Z \<le> card Y * edge_card C X Z"
    using genY assms
    by (simp add: gen_density_def field_split_simps card_eq_0_iff flip: of_nat_mult split: if_split_asm)
  with assms * \<open>card Y < card X\<close> show ?thesis
    by (simp add: gen_density_le_iff field_split_simps edge_card_diff card_Diff_subset 
        edge_card_mono flip: of_nat_mult)
qed

lemma edge_card_insert:
  assumes "NO_MATCH {} F" and "e \<notin> F"
    shows  "edge_card (insert e F) X Y = edge_card {e} X Y + edge_card F X Y"
proof -
  have fin: "finite (all_edges_betw_un X Y)"
    by (meson all_uedges_betw_subset fin_edges finite_subset)
  have "insert e F \<inter> all_edges_betw_un X Y 
      = {e} \<inter> all_edges_betw_un X Y \<union> F \<inter> all_edges_betw_un X Y"
    by auto
  with \<open>e\<notin>F\<close> show ?thesis
    by (auto simp: edge_card_def card_Un_disjoint disjoint_iff fin)
qed

lemma edge_card_sing:
  assumes "e \<in> E"
  shows "edge_card {e} U U = (if e \<subseteq> U then 1 else 0)"
proof (cases "e \<subseteq> U")
  case True
  obtain x y where xy: "e = {x,y}" "x\<noteq>y"
    using assms by (metis card_2_iff two_edges)
  with True assms have "{e} \<inter> all_edges_betw_un U U = {e}"
    by (auto simp: all_edges_betw_un_def)
  with True show ?thesis
    by (simp add: edge_card_def)
qed (auto simp: edge_card_def all_edges_betw_un_def)

lemma sum_edge_card_choose: 
  assumes "2\<le>k" "C \<subseteq> E"
  shows "(\<Sum>U\<in>[V]\<^bsup>k\<^esup>. edge_card C U U) = (card V - 2 choose (k-2)) * card C"
proof -
  have *: "card {A \<in> [V]\<^bsup>k\<^esup>. e \<subseteq> A} = card V - 2 choose (k-2)" if e: "e \<in> C" for e
  proof -
    have "e \<subseteq> V"
      using \<open>C\<subseteq>E\<close> e wellformed by force
    obtain x y where xy: "e = {x,y}" "x\<noteq>y"
      using \<open>C\<subseteq>E\<close> e by (metis in_mono card_2_iff two_edges)
    define \<A> where "\<A> \<equiv> {A \<in> [V]\<^bsup>k\<^esup>. e \<subseteq> A}"
    have "\<And>A. A \<in> \<A> \<Longrightarrow> A = e \<union> (A\<setminus>e) \<and> A\<setminus>e \<in> [V\<setminus>e]\<^bsup>(k - 2)\<^esup>"
      by (auto simp: \<A>_def nsets_def xy)
    moreover have "\<And>xa. \<lbrakk>xa \<in> [V \<setminus> e]\<^bsup>(k - 2)\<^esup>\<rbrakk> \<Longrightarrow> e \<union> xa \<in> \<A>"
      using \<open>e \<subseteq> V\<close> assms
      by (auto simp: \<A>_def nsets_def xy card_insert_if)
    ultimately have "\<A> = (\<union>)e ` [V\<setminus>e]\<^bsup>(k-2)\<^esup>"
      by auto
    moreover have "inj_on ((\<union>) e) ([V\<setminus>e]\<^bsup>(k - 2)\<^esup>)"
      by (auto simp: inj_on_def nsets_def)
    moreover have "card (V\<setminus>e) = card V - 2"
      by (metis \<open>C\<subseteq>E\<close> \<open>e \<in> C\<close> subsetD card_Diff_subset finV finite_subset two_edges wellformed)
    ultimately show ?thesis
      using assms by (simp add: card_image \<A>_def)
  qed
  have "(\<Sum>U\<in>[V]\<^bsup>k\<^esup>. edge_card R U U) = ((card V - 2) choose (k-2)) * card R"
    if "finite R" "R \<subseteq> C" for R
    using that
  proof (induction R)
    case empty
    then show ?case
      by (simp add: edge_card_def)
  next
    case (insert e R)
    with assms have "e\<in>E" by blast
    with insert show ?case
      by (simp add: edge_card_insert * sum.distrib edge_card_sing Ramsey.finite_imp_finite_nsets 
           finV flip: sum.inter_filter)
  qed
  then show ?thesis
    by (meson \<open>C\<subseteq>E\<close> fin_edges finite_subset set_eq_subset)
qed

lemma sum_nsets_Compl:
  assumes "finite A" "k \<le> card A"
  shows "(\<Sum>U\<in>[A]\<^bsup>k\<^esup>. f (A\<setminus>U)) = (\<Sum>U\<in>[A]\<^bsup>(card A - k)\<^esup>. f U)"
proof -
  have "B \<in> (\<setminus>) A ` [A]\<^bsup>k\<^esup>" if "B \<in> [A]\<^bsup>(card A - k)\<^esup>" for B
  proof -
    have "card (A\<setminus>B) = k"
      using assms that by (simp add: nsets_def card_Diff_subset)
    moreover have "B = A\<setminus>(A\<setminus>B)"
      using that by (auto simp: nsets_def)
    ultimately show ?thesis
      using assms unfolding nsets_def image_iff by blast
  qed
  then have "bij_betw (\<lambda>U. A\<setminus>U) ([A]\<^bsup>k\<^esup>) ([A]\<^bsup>(card A - k)\<^esup>)"
    using assms by (auto simp: nsets_def bij_betw_def inj_on_def card_Diff_subset)
  then show ?thesis
    using sum.reindex_bij_betw by blast
qed

subsection \<open>Lemma 9.2 preliminaries\<close>

text \<open>Equation (45) in the text, page 30, is seemingly a huge gap.
   The development below relies on binomial coefficient identities.\<close>

definition "graph_density \<equiv> \<lambda>C. card C / card E"

lemma graph_density_Un:
  assumes "disjnt C D" "C \<subseteq> E" "D \<subseteq> E" 
  shows "graph_density (C \<union> D) = graph_density C + graph_density D"
proof (cases "card E > 0")
  case True
  with assms obtain "finite C" "finite D"
    by (metis card_ge_0_finite finite_subset)
  with assms show ?thesis
    by (auto simp: graph_density_def card_Un_disjnt divide_simps)
qed (auto simp: graph_density_def)

text \<open>Could be generalised to any complete graph\<close>
lemma density_eq_average:
  assumes "C \<subseteq> E" and complete: "E = all_edges V"
  shows "graph_density C =
    real (\<Sum>x \<in> V. \<Sum>y \<in> V\<setminus>{x}. if {x,y} \<in> C then 1 else 0) / (card V * (card V - 1))"
proof -
  have cardE: "card E = card V choose 2"
    using card_all_edges complete finV by blast
  have "finite C"
    using assms fin_edges finite_subset by blast
  then have *: "(\<Sum>x\<in>V. \<Sum>y\<in>V\<setminus>{x}. if {x, y} \<in> C then 1 else 0) = card C * 2"
    using assms by (simp add: sum_eq_card_Neighbours sum_Neighbours_eq_card)
  show ?thesis
    by (auto simp: graph_density_def divide_simps cardE choose_two_real *)
qed

lemma edge_card_V_V: 
  assumes "C \<subseteq> E" and complete: "E = all_edges V"
  shows "edge_card C V V = card C"
proof -
  have "C \<subseteq> all_edges_betw_un V V"
    using assms clique_iff complete subset_refl
    by (metis all_uedges_betw_I all_uedges_betw_subset clique_def)
  then show ?thesis
    by (metis Int_absorb2 edge_card_def)
qed

text \<open>Bhavik's statement; own proof\<close>
proposition density_eq_average_partition:
  assumes k: "0 < k" "k < card V" and "C \<subseteq> E" and complete: "E = all_edges V"
  shows "graph_density C = (\<Sum>U\<in>[V]\<^bsup>k\<^esup>. gen_density C U (V\<setminus>U)) / (card V choose k)"
proof (cases "k=1 \<or> gorder = Suc k")
  case True
  then have [simp]: "gorder choose k = gorder" by auto
  have eq: "(C \<inter> {{x, y} |y. y \<in> V \<and> y \<noteq> x \<and> {x, y} \<in> E}) 
           = (\<lambda>y. {x,y}) ` {y. {x,y} \<in> C}" for x
    using \<open>C\<subseteq>E\<close> wellformed by fastforce
  have "V \<noteq> {}"
    using assms by force
  then have nontriv: "E \<noteq> {}"
    using assms card_all_edges finV by force
  have "(\<Sum>U\<in>[V]\<^bsup>k\<^esup>. gen_density C U (V \<setminus> U)) = (\<Sum>x\<in>V. gen_density C {x} (V \<setminus> {x}))"
    using True
  proof
    assume "k = 1"
    then show ?thesis
      by (simp add: sum_nsets_one)
  next
    assume \<section>: "gorder = Suc k"
    then have  "V-A \<noteq> {}" if "card A = k" "finite A" for A
      using that
      by (metis assms(2) card.empty card_less_sym_Diff finV less_nat_zero_code)
    then have bij: "bij_betw (\<lambda>x. V \<setminus> {x}) V ([V]\<^bsup>k\<^esup>)"
      using finV \<section> 
      by (auto simp: inj_on_def bij_betw_def nsets_def image_iff)
        (metis Diff_insert_absorb card.insert card_subset_eq insert_subset subsetI)
    moreover have "V\<setminus>(V\<setminus>{x}) = {x}" if "x\<in>V" for x
      using that by auto
    ultimately show ?thesis
      using sum.reindex_bij_betw [OF bij] gen_density_commute 
      by (metis (no_types, lifting) sum.cong) 
  qed
  also have "\<dots> = (\<Sum>x\<in>V. real (edge_card C {x} (V \<setminus> {x}))) / (gorder - 1)"
    by (simp add: \<open>C\<subseteq>E\<close> gen_density_def flip: sum_divide_distrib)
  also have "\<dots> = (\<Sum>i\<in>V. card (Neighbours C i)) / (gorder - 1)"
    unfolding edge_card_def Neighbours_def all_edges_betw_un_def
    by (simp add: eq card_image inj_on_def doubleton_eq_iff)
  also have "\<dots> = graph_density C * gorder"
    using assms density_eq_average [OF \<open>C\<subseteq>E\<close> complete]
    by (simp add: sum_eq_card_Neighbours)
  finally show ?thesis
    using k by simp
next
  case False
  then have K: "gorder > Suc k" "k\<ge>2" 
    using assms by auto
  then have "gorder - Suc (Suc (gorder - Suc (Suc k))) = k"
    using assms by auto
  then have [simp]: "gorder - 2 choose (gorder - Suc (Suc k)) = (gorder - 2 choose k)"
    using binomial_symmetric [of "(gorder - Suc (Suc k))"]
    by simp
  have cardE: "card E = card V choose 2"
    using card_all_edges complete finV by blast
  have "card E > 0"
    using k cardE by auto
  have in_E_iff [iff]: "{v,w} \<in> E \<longleftrightarrow> v\<in>V \<and> w\<in>V \<and> v\<noteq>w" for v w
    by (auto simp: complete all_edges_alt doubleton_eq_iff)

  have B: "edge_card C V V = edge_card C U U + edge_card C U (V\<setminus>U) + edge_card C (V\<setminus>U) (V\<setminus>U)"
    (is "?L = ?R")
    if "U \<subseteq> V" for U
  proof -
    have fin: "finite (all_edges_betw_un U U')" for U'
      by (meson all_uedges_betw_subset fin_edges finite_subset)
    have dis: "all_edges_betw_un U U \<inter> all_edges_betw_un U (V \<setminus> U) = {}"
      by (auto simp: all_edges_betw_un_def doubleton_eq_iff)
    have "all_edges_betw_un V V = all_edges_betw_un U U \<union> all_edges_betw_un U (V\<setminus>U) \<union> all_edges_betw_un (V\<setminus>U) (V\<setminus>U)"
      by (smt (verit) that Diff_partition Un_absorb Un_assoc all_edges_betw_un_Un2 all_edges_betw_un_commute)
    with that have "?L = card (C \<inter> all_edges_betw_un U U \<union> C \<inter> all_edges_betw_un U (V \<setminus> U)
                             \<union> C \<inter> all_edges_betw_un (V \<setminus> U) (V \<setminus> U))"
      by (simp add: edge_card_def Int_Un_distrib)
    also have "\<dots> = ?R"
      using fin dis \<open>C\<subseteq>E\<close> fin_edges finite_subset
      by ((subst card_Un_disjoint)?, fastforce simp: edge_card_def all_edges_betw_un_def doubleton_eq_iff)+
    finally show ?thesis .
  qed
  have C: "(\<Sum>U\<in>[V]\<^bsup>k\<^esup>. real (edge_card C U (V\<setminus>U)))
      = (card V choose k) * card C - real(\<Sum>U\<in>[V]\<^bsup>k\<^esup>. edge_card C U U + edge_card C (V\<setminus>U) (V\<setminus>U))"
    (is "?L = ?R")
  proof -
    have "?L = (\<Sum>U\<in>[V]\<^bsup>k\<^esup>. edge_card C V V - real (edge_card C U U + edge_card C (V\<setminus>U) (V\<setminus>U)))"
      unfolding nsets_def by (rule sum.cong) (auto simp: B)
    also have "\<dots> = ?R"
      using \<open>C\<subseteq>E\<close> complete edge_card_V_V 
      by (simp add: \<open>C\<subseteq>E\<close> sum_subtractf edge_card_V_V)
    finally show ?thesis .
  qed

  have "(gorder-2 choose k) + (gorder-2 choose (k-2)) + 2 * (gorder-2 choose (k-1)) = (gorder choose k)"
    using assms K by (auto simp: choose_reduce_nat [of "gorder"] choose_reduce_nat [of "gorder-Suc 0"] eval_nat_numeral)
  moreover
  have "(gorder - 1) * (gorder-2 choose (k-1)) = (gorder-k) * (gorder-1 choose (k-1))"
    by (metis Suc_1 Suc_diff_1 binomial_absorb_comp diff_Suc_eq_diff_pred \<open>k>0\<close>)
  ultimately have F: "(gorder - 1) * (gorder-2 choose k) + (gorder - 1) * (gorder-2 choose (k-2)) + 2 * (gorder-k) * (gorder-1 choose (k-1)) 
      = (gorder - 1) * (gorder choose k)"
    by (smt (verit) add_mult_distrib2 mult.assoc mult.left_commute)

  have "(\<Sum>U\<in>[V]\<^bsup>k\<^esup>. edge_card C U (V\<setminus>U) / (real (card U) * card (V\<setminus>U)))
     = (\<Sum>U\<in>[V]\<^bsup>k\<^esup>. edge_card C U (V\<setminus>U) / (real k * (card V - k)))"
    using card_Diff_subset by (intro sum.cong) (auto simp: nsets_def)
  also have "\<dots> = (\<Sum>U\<in>[V]\<^bsup>k\<^esup>. edge_card C U (V\<setminus>U)) / (k * (card V - k))"
    by (simp add: sum_divide_distrib)
  finally have *: "(\<Sum>U\<in>[V]\<^bsup>k\<^esup>. edge_card C U (V\<setminus>U) / (real (card U) * card (V\<setminus>U)))
              = (\<Sum>U\<in>[V]\<^bsup>k\<^esup>. edge_card C U (V\<setminus>U)) / (k * (card V - k))" .

  have choose_m1: "gorder * (gorder - 1 choose (k - 1)) = k * (gorder choose k)"
    using \<open>k>0\<close> times_binomial_minus1_eq by presburger 
  have **: "(real k * (real gorder - real k) * real (gorder choose k)) =
        (real (gorder choose k) - (real (gorder - 2 choose (k - 2)) + real (gorder - 2 choose k))) *
        real (gorder choose 2)"
    using assms K arg_cong [OF F, of "\<lambda>u. real gorder * real u"] arg_cong [OF choose_m1, of real]
    apply (simp add: choose_two_real ring_distribs)
    by (smt (verit) distrib_right mult.assoc mult_2_right mult_of_nat_commute)
  have eq: "(\<Sum>U\<in>[V]\<^bsup>k\<^esup>. real (edge_card C (V\<setminus>U) (V\<setminus>U))) 
          = (\<Sum>U\<in>[V]\<^bsup>(gorder-k)\<^esup>. real (edge_card C U U))"
    using K finV by (subst sum_nsets_Compl, simp_all)
  show ?thesis
    unfolding graph_density_def gen_density_def
    using K \<open>card E > 0\<close> \<open>C\<subseteq>E\<close>
    apply (simp add: eq divide_simps B C sum.distrib *)
    apply (simp add: ** sum_edge_card_choose cardE flip: of_nat_sum)
    by argo
qed

lemma exists_density_edge_density:
  assumes k: "0 < k" "k < card V" and "C \<subseteq> E" and complete: "E = all_edges V"
  obtains U where "card U = k" "U\<subseteq>V" "graph_density C \<le> gen_density C U (V\<setminus>U)"
proof -
  have False if "\<And>U. U \<in> [V]\<^bsup>k\<^esup> \<Longrightarrow> graph_density C > gen_density C U (V\<setminus>U)"
  proof -
    have "card([V]\<^bsup>k\<^esup>) > 0"
      using assms by auto
    then have "(\<Sum>U\<in>[V]\<^bsup>k\<^esup>. gen_density C U (V \<setminus> U)) < card([V]\<^bsup>k\<^esup>) * graph_density C"
      by (meson sum_bounded_above_strict that)
    with density_eq_average_partition assms show False by force
  qed
  with that show thesis
    unfolding nsets_def by fastforce
qed

end  (*fin_sgraph*)

end
