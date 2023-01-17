section \<open> Connectivity \<close>
text \<open>This theory defines concepts around the connectivity of a graph and its vertices, as well as
graph properties that depend on connectivity definitions, such as shortest path, radius, diameter,
and eccentricity \<close>

theory Connectivity imports Undirected_Graph_Walks
begin

context ulgraph 
begin

subsection \<open>Connecting Walks and Paths \<close>

definition connecting_walk :: "'a \<Rightarrow> 'a \<Rightarrow> 'a list \<Rightarrow> bool" where
"connecting_walk u v xs \<equiv> is_walk xs \<and> hd xs= u \<and> last xs = v"

lemma connecting_walk_rev: "connecting_walk u v xs \<longleftrightarrow> connecting_walk v u (rev xs)"
  unfolding connecting_walk_def using is_walk_rev 
  by (auto simp add: hd_rev last_rev)

lemma connecting_walk_wf: "connecting_walk u v xs \<Longrightarrow> u \<in> V \<and> v \<in> V"
  using is_walk_wf_hd is_walk_wf_last by (auto simp add: connecting_walk_def)

lemma connecting_walk_self: "u \<in> V \<Longrightarrow> connecting_walk u u [u] = True"
  unfolding connecting_walk_def by (simp add: is_walk_singleton)

text \<open> We define two definitions of connecting paths. The first uses the @{term "gen_path"} definition, which 
allows for trivial paths and cycles, the second uses the stricter definition of a path which requires
it to be an open walk \<close>
definition connecting_path :: "'a \<Rightarrow> 'a \<Rightarrow> 'a list \<Rightarrow> bool" where
"connecting_path u v xs \<equiv> is_gen_path xs \<and> hd xs = u \<and> last xs = v"

definition connecting_path_str :: "'a \<Rightarrow> 'a \<Rightarrow> 'a list \<Rightarrow> bool" where
"connecting_path_str u v xs \<equiv> is_path xs \<and> hd xs = u \<and> last xs = v"

lemma connecting_path_rev: "connecting_path u v xs \<longleftrightarrow> connecting_path v u (rev xs)"
  unfolding connecting_path_def using is_gen_path_rev
  by (auto simp add: hd_rev last_rev) 

lemma connecting_path_walk: "connecting_path u v xs \<Longrightarrow> connecting_walk u v xs"
  unfolding connecting_path_def connecting_walk_def using is_gen_path_def by auto 

lemma connecting_path_str_gen: "connecting_path_str u v xs \<Longrightarrow> connecting_path u v xs"
  unfolding connecting_path_def connecting_path_str_def is_gen_path_def is_path_def
  by (simp add: is_open_walk_def) 

lemma connecting_path_gen_str: "connecting_path u v xs \<Longrightarrow> (\<not> is_cycle xs) \<Longrightarrow> walk_length xs > 0 \<Longrightarrow> connecting_path_str u v xs"
  unfolding connecting_path_def connecting_path_str_def using is_gen_path_path by auto

lemma connecting_path_alt_def: "connecting_path u v xs \<longleftrightarrow> connecting_walk u v xs \<and> is_gen_path xs"
proof -
  have "is_gen_path xs \<Longrightarrow> is_walk xs"
    by (simp add: is_gen_path_def) 
  then have "(is_walk xs \<and> hd xs = u \<and> last xs = v) \<and> is_gen_path xs \<longleftrightarrow> (hd xs = u \<and> last xs = v) \<and> is_gen_path xs"
    by blast
  thus ?thesis
    by (auto simp add: connecting_path_def connecting_walk_def)
qed

lemma connecting_path_length_bound: "u \<noteq> v \<Longrightarrow> connecting_path u v p \<Longrightarrow> walk_length p \<ge> 1"
  using walk_length_def
  by (metis connecting_path_def is_gen_path_def is_walk_not_empty2 last_ConsL le_refl length_0_conv 
less_one list.exhaust_sel  nat_less_le nat_neq_iff neq_Nil_conv walk_edges.simps(3))

lemma connecting_path_self: "u \<in> V \<Longrightarrow> connecting_path u u [u] = True"
  unfolding connecting_path_alt_def using connecting_walk_self
  by (simp add: is_gen_path_def is_walk_singleton) 

lemma connecting_path_singleton: "connecting_path u v xs \<Longrightarrow> length xs = 1 \<Longrightarrow> u = v" 
  by (metis  cancel_comm_monoid_add_class.diff_cancel connecting_path_def fact_1 fact_nonzero 
      last_rev length_0_conv neq_Nil_conv singleton_rev_conv walk_edges.simps(3) walk_length_conv walk_length_def) 

lemma connecting_walk_path: 
  assumes "connecting_walk u v xs"
  shows "\<exists> ys . connecting_path u v ys \<and> walk_length ys \<le> walk_length xs"
proof (cases "u = v")
  case True
  then show ?thesis
    using assms connecting_path_self connecting_walk_wf
    by (metis bot_nat_0.extremum list.size(3) walk_edges.simps(2) walk_length_def) 
next
  case False
  then have "walk_length xs \<noteq> 0" using assms connecting_walk_def is_walk_def
    by (metis last_ConsL length_0_conv list.distinct(1) list.exhaust_sel walk_edges.simps(3) walk_length_def) 
  then show ?thesis using assms False proof (induct "walk_length xs" arbitrary: xs rule: less_induct)
    fix xs assume IH: "(\<And>xsa. walk_length xsa < walk_length xs \<Longrightarrow> walk_length xsa \<noteq> 0 \<Longrightarrow> 
      connecting_walk u v xsa \<Longrightarrow> u \<noteq> v \<Longrightarrow> \<exists>ys. connecting_path u v ys \<and> walk_length ys \<le> walk_length xsa)"
    assume assm: "connecting_walk u v xs" and ne: "u \<noteq> v" and n0: "walk_length xs \<noteq> 0"
    then show "\<exists>ys. connecting_path u v ys \<and> walk_length ys \<le> walk_length xs"
    proof (cases "walk_length xs \<le> 1") \<comment> \<open> Base Cases \<close>
      case True
      then have "walk_length xs = 1"
        using n0 by auto
      then show ?thesis using ne assm cancel_comm_monoid_add_class.diff_cancel connecting_path_alt_def connecting_walk_def 
            distinct_length_2_or_more distinct_singleton hd_Cons_tl is_gen_path_def is_walk_def last_ConsL 
            last_ConsR length_0_conv length_tl walk_length_conv
        by (metis True) 
    next
      case False
      then show ?thesis
      proof (cases "distinct xs")
        case True
        then show ?thesis
          using assm connecting_path_alt_def connecting_walk_def is_gen_path_def by auto 
      next
        case False
        then obtain ws ys zs y where xs_decomp: "xs = ws@[y]@ys@[y]@zs" using not_distinct_decomp
          by blast
        let ?rs = "ws@[y]@zs"
        have hd: "hd ?rs = u" using xs_decomp assm connecting_walk_def
          by (metis hd_append list.distinct(1)) 
        have lst: "last ?rs = v" using xs_decomp assm connecting_walk_def by simp 
        have wl: "walk_length ?rs \<noteq> 0" using hd lst ne walk_length_conv by auto 
        have "set ?rs \<subseteq> V" using assm connecting_walk_def is_walk_def xs_decomp by auto
        have cw: "connecting_walk u v ?rs" unfolding connecting_walk_def is_walk_decomp
          using assm connecting_walk_def hd is_walk_decomp lst xs_decomp by blast  
        have "ys@[y] \<noteq> []"by simp 
        then have "length ?rs < length xs" using xs_decomp length_list_decomp_lt by auto
        have "walk_length ?rs < walk_length xs" using walk_length_conv xs_decomp by force 
        then show ?thesis using IH[of ?rs] using cw ne wl le_trans less_or_eq_imp_le by blast 
      qed
    qed
  qed
qed

lemma connecting_walk_split: 
  assumes "connecting_walk u v xs" assumes "connecting_walk v z ys"
  shows "connecting_walk u z (xs @ (tl ys))"
  using connecting_walk_def is_walk_append
  by (metis append.right_neutral assms(1) assms(2) connecting_walk_self connecting_walk_wf hd_append2 is_walk_not_empty last_appendR last_tl list.collapse) 

lemma connecting_path_split: 
  assumes "connecting_path u v xs" "connecting_path v z ys"
  obtains p where "connecting_path u z p" and "walk_length p \<le> walk_length (xs @ (tl ys))"
  using connecting_walk_split connecting_walk_path connecting_path_walk assms(1) assms(2) by blast 

lemma connecting_path_split_length: 
  assumes "connecting_path u v xs" "connecting_path v z ys"
  obtains p where "connecting_path u z p" and "walk_length p \<le> walk_length xs + walk_length ys"
proof -
  have "connecting_walk u z (xs @ (tl ys))"
    using connecting_walk_split assms connecting_path_walk by blast
  have "walk_length (xs @ (tl ys)) \<le> walk_length xs + walk_length ys" 
    using walk_length_app_ineq
    by (simp add: le_diff_conv walk_length_conv) 
  thus ?thesis using connecting_path_split
    by (metis (full_types) assms(1) assms(2) dual_order.trans that) 
qed

subsection \<open> Vertex Connectivity \<close>
text \<open>Two vertices are defined to be connected if there exists a connecting path. Note that the more
general version of a connecting path is again used as a vertex should be considered as connected to itself \<close>
definition vert_connected :: "'a \<Rightarrow> 'a \<Rightarrow> bool" where
"vert_connected u v \<equiv> \<exists> xs . connecting_path u v xs"

lemma vert_connected_rev: "vert_connected u v \<longleftrightarrow> vert_connected v u"
  unfolding vert_connected_def using connecting_path_rev by auto

lemma vert_connected_id: "u \<in> V \<Longrightarrow> vert_connected u u = True"
  unfolding vert_connected_def using connecting_path_self by auto 

lemma vert_connected_trans: "vert_connected u v \<Longrightarrow> vert_connected v z \<Longrightarrow> vert_connected u z"
  unfolding vert_connected_def using connecting_path_split
  by meson 

lemma vert_connected_wf: "vert_connected u v \<Longrightarrow> u \<in> V \<and> v \<in> V"
  using vert_connected_def connecting_path_walk connecting_walk_wf by blast 

definition vert_connected_n :: "'a \<Rightarrow> 'a \<Rightarrow> nat \<Rightarrow> bool" where
"vert_connected_n u v n \<equiv> \<exists> p. connecting_path u v p \<and> walk_length p = n"

lemma vert_connected_n_imp: "vert_connected_n u v n \<Longrightarrow> vert_connected u v"
  by (auto simp add: vert_connected_def vert_connected_n_def)

lemma vert_connected_n_rev: "vert_connected_n u v n \<longleftrightarrow> vert_connected_n v u n"
  unfolding vert_connected_n_def using  walk_length_rev
  by (metis connecting_path_rev) 

definition connecting_paths :: "'a \<Rightarrow> 'a \<Rightarrow> 'a list set" where
"connecting_paths u v \<equiv> {xs . connecting_path u v xs}"

lemma connecting_paths_self: "u \<in> V \<Longrightarrow> [u] \<in> connecting_paths u u"
  unfolding connecting_paths_def using connecting_path_self by auto

lemma connecting_paths_empty_iff: "vert_connected u v \<longleftrightarrow> connecting_paths u v \<noteq> {}"
  unfolding connecting_paths_def vert_connected_def by auto

lemma elem_connecting_paths: "p \<in> connecting_paths u v \<Longrightarrow> connecting_path u v p"
  using connecting_paths_def by blast

lemma connecting_paths_ss_gen: "connecting_paths u v \<subseteq> gen_paths"
  unfolding connecting_paths_def gen_paths_def connecting_path_def by auto

lemma connecting_paths_sym: "xs \<in> connecting_paths u v \<longleftrightarrow> rev xs \<in> connecting_paths v u"
  unfolding connecting_paths_def using connecting_path_rev by simp

text \<open>A set is considered to be connected, if all the vertices within that set are pairwise connected \<close>
definition is_connected_set :: "'a set \<Rightarrow> bool" where
"is_connected_set V' \<equiv> (\<forall> u v . u \<in> V' \<longrightarrow> v \<in> V' \<longrightarrow> vert_connected u v)"

lemma is_connected_set_empty: "is_connected_set {}"
  unfolding is_connected_set_def by simp

lemma is_connected_set_singleton: "x \<in> V \<Longrightarrow> is_connected_set {x}"
  unfolding is_connected_set_def by (auto simp add: vert_connected_id)

lemma is_connected_set_wf: "is_connected_set V' \<Longrightarrow> V' \<subseteq> V"
  unfolding is_connected_set_def
  by (meson connecting_path_walk connecting_walk_wf subsetI vert_connected_def) 

lemma is_connected_setD: "is_connected_set V' \<Longrightarrow> u \<in> V' \<Longrightarrow> v \<in> V' \<Longrightarrow> vert_connected u v"
  by (simp add: is_connected_set_def)

lemma not_connected_set: "\<not> is_connected_set V' \<Longrightarrow> u \<in> V' \<Longrightarrow> \<exists> v \<in> V' . \<not> vert_connected u v"
  using is_connected_setD by (meson is_connected_set_def vert_connected_rev vert_connected_trans) 

subsection \<open>Graph Properties on Connectivity \<close>

text \<open>The shortest path is defined to be the infinum of the set of connecting path walk lengths. 
Drawing inspiration from \<^cite>\<open>"noschinski_2012"\<close>, we use the infinum and enats as this enables more 
natural reasoning in a non-finite setting, while also being useful for proofs of a more probabilistic
or analysis nature\<close>

definition shortest_path :: "'a \<Rightarrow> 'a \<Rightarrow> enat" where
"shortest_path u v \<equiv> INF p\<in> connecting_paths u v. enat (walk_length p)"

lemma shortest_path_walk_length: "shortest_path u v = n \<Longrightarrow> p \<in> connecting_paths u v \<Longrightarrow> walk_length p \<ge> n"
  using shortest_path_def INF_lower[of p "connecting_paths u v" "\<lambda> p . enat (walk_length p)"] 
  by auto

lemma shortest_path_lte: "\<And> p . p \<in> connecting_paths u v \<Longrightarrow> shortest_path u v \<le> walk_length p"
  unfolding shortest_path_def by (simp add: Inf_lower)

lemma shortest_path_obtains: 
  assumes "shortest_path u v = n"
  assumes "n \<noteq> top"
  obtains p where "p \<in> connecting_paths u v" and "walk_length p = n"
  using enat_in_INF shortest_path_def by (metis assms(1) assms(2) the_enat.simps) 

lemma shortest_path_intro: 
  assumes "n \<noteq> top"
  assumes "(\<exists> p \<in> connecting_paths u v . walk_length p = n)"
  assumes "(\<And> p. p \<in> connecting_paths u v \<Longrightarrow> n \<le> walk_length p)"
  shows "shortest_path u v = n"
proof (rule ccontr)
  assume a: "shortest_path u v \<noteq> enat n"
  then have "shortest_path u v < n"
    by (metis antisym_conv2 assms(2) shortest_path_lte)
  then have "\<exists> p \<in> connecting_paths u v .walk_length p < n" 
    using shortest_path_def by (simp add: INF_less_iff) 
  thus False using assms(3)
    using le_antisym less_imp_le_nat by blast 
qed

lemma shortest_path_self: 
  assumes "u \<in> V" 
  shows "shortest_path u u = 0"
proof -
  have "[u] \<in> connecting_paths u u" 
    using connecting_paths_self by (simp add: assms)
  then have "walk_length [u] = 0"
    using walk_length_def walk_edges.simps by auto
  thus ?thesis using shortest_path_def
    by (metis \<open>[u] \<in> connecting_paths u u\<close> le_zero_eq shortest_path_lte zero_enat_def) 
qed

lemma connecting_paths_sym_length: "i \<in> connecting_paths u v \<Longrightarrow> \<exists>j\<in>connecting_paths v u. (walk_length j) = (walk_length i)"
  using connecting_paths_sym by (metis walk_length_rev) 

lemma shortest_path_sym: "shortest_path u v = shortest_path v u"
  unfolding shortest_path_def 
  by (intro INF_eq)(metis add.right_neutral le_iff_add connecting_paths_sym_length)+ 

lemma shortest_path_inf:  "\<not> vert_connected u v \<Longrightarrow> shortest_path u v = \<infinity>"
  using connecting_paths_empty_iff shortest_path_def by (simp add: top_enat_def)

lemma shortest_path_not_inf: 
  assumes "vert_connected u v"
  shows "shortest_path u v \<noteq> \<infinity>"
proof -
  have "\<And> p. connecting_path u v p \<Longrightarrow> enat (walk_length p) \<noteq> \<infinity>"
    using connecting_path_def is_gen_path_def by auto
  thus ?thesis unfolding shortest_path_def connecting_paths_def
    by (metis assms connecting_paths_def infinity_ileE mem_Collect_eq shortest_path_def shortest_path_lte vert_connected_def)
qed

lemma shortest_path_obtains2:
  assumes "vert_connected u v"
  obtains p where "p \<in> connecting_paths u v" and "walk_length p = shortest_path u v"
proof -
  have "connecting_paths u v \<noteq> {}" using assms connecting_paths_empty_iff by auto
  have "shortest_path u v \<noteq> \<infinity>" using assms shortest_path_not_inf by simp
  thus ?thesis using shortest_path_def enat_in_INF
    by (metis that top_enat_def) 
qed

lemma shortest_path_split: "shortest_path x y \<le> shortest_path x z + shortest_path z y" 
proof (cases "vert_connected x y \<and> vert_connected x z")
  case True
  show ?thesis 
  proof (rule ccontr)
    assume " \<not> shortest_path x y \<le> shortest_path x z + shortest_path z y"
    then have c: "shortest_path x y > shortest_path x z + shortest_path z y" by simp
    have "vert_connected z y" using True vert_connected_trans vert_connected_rev by blast
    then obtain p1 p2 where "connecting_path x z p1" and "connecting_path z y p2" and 
      s1: "shortest_path x z = walk_length p1" and s2: "shortest_path z y = walk_length p2"
      using True shortest_path_obtains2 connecting_paths_def elem_connecting_paths by metis
    then obtain p3 where cp: "connecting_path x y p3" and "walk_length p1 + walk_length p2 \<ge> walk_length p3" 
      using connecting_path_split_length by blast
    then have "shortest_path x z + shortest_path z y \<ge> walk_length p3" using s1 s2 by simp
    then have lt: "shortest_path x y > walk_length p3" using c by auto
    have "p3 \<in> connecting_paths x y" using cp connecting_paths_def by auto
    then show False using shortest_path_def shortest_path_obtains2
      by (metis True enat_ord_simps(1) enat_ord_simps(2) le_Suc_ex lt not_add_less1 shortest_path_lte) 
  qed
next
  case False
  then show ?thesis
    by (metis enat_ord_code(3) plus_enat_simps(2) plus_enat_simps(3) shortest_path_inf vert_connected_trans)
qed

lemma shortest_path_invalid_v: "v \<notin> V \<or> u \<notin> V \<Longrightarrow> shortest_path u v = \<infinity>"
  using shortest_path_inf vert_connected_wf by blast 

lemma shortest_path_lb: 
  assumes "u \<noteq> v"
  assumes "vert_connected u v"
  shows "shortest_path u v > 0"
proof - 
  have "\<And> p. connecting_path u v p  \<Longrightarrow>  enat (walk_length p) > 0"
    using connecting_path_length_bound assms by fastforce 
  thus ?thesis unfolding shortest_path_def
    by (metis elem_connecting_paths shortest_path_def shortest_path_obtains2 assms(2))
qed

text \<open>Eccentricity of a vertex v is the furthest distance between it and a (different) vertex \<close>
definition eccentricity :: "'a \<Rightarrow> enat" where
"eccentricity v \<equiv> SUP u \<in> V - {v}. shortest_path v u" 

lemma eccentricity_empty_vertices: "V = {} \<Longrightarrow> eccentricity v = 0"
  "V = {v} \<Longrightarrow> eccentricity v = 0"
  unfolding eccentricity_def using bot_enat_def by simp_all

lemma eccentricity_bot_iff: "eccentricity v = 0 \<longleftrightarrow> V = {} \<or> V = {v}"
proof (intro iffI)
  assume a: "eccentricity v = 0"
  show "V = {} \<or> V = {v}"
  proof (rule ccontr, simp)
    assume a2: "V \<noteq> {} \<and> V \<noteq> {v}"
    have eq0: "\<forall> u \<in> V - {v} . shortest_path v u = 0"
      using SUP_bot_conv(1)[of "\<lambda> u. shortest_path v u" "V - {v}"] a eccentricity_def bot_enat_def by simp
    have nc: "\<forall> u \<in> V - {v} . \<not> vert_connected v u \<longrightarrow> shortest_path v u = \<infinity>"
      using shortest_path_inf by simp
    have "\<forall> u \<in> V - {v} . vert_connected v u \<longrightarrow> shortest_path v u > 0" 
      using shortest_path_lb by auto
    then show False using eq0 a2 nc
      by auto 
  qed
next 
  show "V = {} \<or> V = {v} \<Longrightarrow> eccentricity v = 0" using eccentricity_empty_vertices by auto
qed

lemma eccentricity_invalid_v: 
  assumes "v \<notin> V" 
  assumes "V \<noteq> {}"
  shows "eccentricity v = \<infinity>"
proof -
  have "\<And> u. shortest_path v u = \<infinity>" using assms shortest_path_invalid_v by blast
  have "V - {v} = V" using assms by simp
  then have "eccentricity v = (SUP u \<in> V . shortest_path v u)" by (simp add: eccentricity_def)
  thus ?thesis using eccentricity_def shortest_path_invalid_v assms by simp 
qed

lemma eccentricity_gt_shortest_path: 
  assumes "u \<in> V"
  shows "eccentricity v \<ge> shortest_path v u"
proof (cases "u \<in> V - {v}")
  case True
  then show ?thesis unfolding eccentricity_def by (simp add: SUP_upper) 
next
  case f1: False
  then have "u = v" using assms by auto
  then have "shortest_path u v = 0" using shortest_path_self assms by auto
  then show ?thesis by (simp add: \<open>u = v\<close>) 
qed

lemma eccentricity_disconnected_graph: 
  assumes "\<not> is_connected_set V"
  assumes "v \<in> V"
  shows "eccentricity v = \<infinity>"
proof -
  obtain u where uin: "u \<in> V" and nvc: "\<not> vert_connected v u"
    using not_connected_set assms by auto
  then have "u \<noteq> v" using vert_connected_id by auto
  then have "u \<in> V - {v}" using uin by simp
  moreover have "shortest_path v u = \<infinity>" using nvc shortest_path_inf by auto 
  thus ?thesis using eccentricity_gt_shortest_path
    by (metis enat_ord_simps(5) uin) 
qed

text \<open>The diameter is the largest distance between any two vertices \<close>
definition diameter :: "enat" where
"diameter \<equiv> SUP v \<in> V . eccentricity v"

lemma diameter_gt_eccentricity: "v \<in> V \<Longrightarrow> diameter \<ge> eccentricity v"
  using diameter_def by (simp add: SUP_upper)

lemma diameter_disconnected_graph: 
  assumes "\<not> is_connected_set V"
  shows "diameter = \<infinity>"
  unfolding diameter_def using eccentricity_disconnected_graph
  by (metis SUP_eq_const assms is_connected_set_empty)

lemma diameter_empty: "V = {} \<Longrightarrow> diameter = 0"
  unfolding diameter_def using Sup_empty bot_enat_def by simp

lemma diameter_singleton: "V = {v} \<Longrightarrow> diameter = eccentricity v"
  unfolding diameter_def by simp 

text \<open>The radius is the smallest "shortest" distance between any two vertices \<close>
definition radius :: "enat" where
"radius \<equiv> INF v \<in> V . eccentricity v"

lemma radius_lt_eccentricity: "v \<in> V \<Longrightarrow> radius \<le> eccentricity v"
  using radius_def by (simp add: INF_lower)

lemma radius_disconnected_graph: "\<not> is_connected_set V \<Longrightarrow> radius = \<infinity>"
  unfolding radius_def using eccentricity_disconnected_graph
  by (metis INF_eq_const is_connected_set_empty) 

lemma radius_empty: "V = {} \<Longrightarrow> radius = \<infinity>"
  unfolding radius_def using Inf_empty top_enat_def by simp

lemma radius_singleton: "V = {v} \<Longrightarrow> radius = eccentricity v"
  unfolding radius_def by simp

text \<open>The centre of the graph is all vertices whose eccentricity equals the radius \<close>
definition centre :: "'a set" where
"centre \<equiv> {v \<in> V. eccentricity v = radius }"

lemma centre_disconnected_graph: "\<not> is_connected_set V \<Longrightarrow> centre = V"
  unfolding centre_def using radius_disconnected_graph eccentricity_disconnected_graph by auto

end

lemma (in fin_ulgraph) fin_connecting_paths: "finite (connecting_paths u v)"
  using connecting_paths_ss_gen finite_gen_paths finite_subset by fastforce

subsection \<open>We define a connected graph as a non-empty graph (the empty set is not usually considered
connected by convention), where the vertex set is connected \<close>
locale connected_ulgraph = ulgraph + ne_graph_system + 
  assumes connected: "is_connected_set V"
begin

lemma vertices_connected: "u \<in> V \<Longrightarrow> v \<in> V \<Longrightarrow> vert_connected u v"
  using is_connected_set_def connected by auto 

lemma vertices_connected_path: "u \<in> V \<Longrightarrow> v \<in> V \<Longrightarrow> \<exists> p. connecting_path u v p"
  using vertices_connected by (simp add: vert_connected_def) 

lemma connecting_paths_not_empty: "u \<in> V \<Longrightarrow> v \<in> V \<Longrightarrow> connecting_paths u v \<noteq> {}"
  using connected not_empty connecting_paths_empty_iff is_connected_setD by blast 

lemma min_shortest_path: assumes "u \<in> V" "v \<in> V" "u \<noteq> v"
  shows "shortest_path u v > 0"
  using shortest_path_lb assms vertices_connected by auto

text \<open>The eccentricity, diameter, radius, and centre definitions tend to be only used in a connected context, 
as otherwise they are the INF/SUP value. In these contexts, we can obtain the vertex responsible \<close>
lemma eccentricity_obtains_inf: 
  assumes "V \<noteq> {v}"
  shows "eccentricity v = \<infinity> \<or> (\<exists> u \<in> (V - {v}) . shortest_path v u = eccentricity v)"
proof (cases "finite ((\<lambda> u. shortest_path v u) ` (V - {v}))")
  case True
  then have e: "eccentricity v = Max ((\<lambda> u. shortest_path v u) ` (V - {v}))" unfolding eccentricity_def using Sup_enat_def
    using assms not_empty by auto
  have "(V - {v}) \<noteq> {}" using assms not_empty by auto
  then have "((\<lambda> u. shortest_path v u) ` (V - {v})) \<noteq> {}" by simp
  then obtain n where "n \<in> ((\<lambda> u. shortest_path v u) ` (V - {v}))" and "n = eccentricity v" 
    using Max_in e True by auto
  then obtain u where "u \<in> (V - {v})" and "shortest_path v u = eccentricity v"
    by blast
  then show ?thesis by auto
next
  case False
  then have "eccentricity v = \<infinity>" unfolding eccentricity_def using Sup_enat_def
    by (metis (mono_tags, lifting) cSup_singleton empty_iff finite_insert insert_iff) 
  then show ?thesis by simp
qed

lemma diameter_obtains: "diameter = \<infinity> \<or> (\<exists> v \<in> V . eccentricity v = diameter)"
proof (cases "is_singleton V")
  case True
  then obtain v where "V = {v}"
    using is_singletonE by auto
  then show ?thesis using diameter_singleton
    by simp 
next
  case f1: False
  then show ?thesis proof (cases "finite ((\<lambda> v. eccentricity v) ` V)")
    case True
    then have "diameter = Max ((\<lambda> v. eccentricity v) ` V)" unfolding diameter_def using Sup_enat_def not_empty
      by simp
    then obtain n where "n \<in>((\<lambda> v. eccentricity v) ` V)" and "diameter = n" using Max_in True
      using not_empty by auto 
    then obtain u where "u \<in> V" and "eccentricity u = diameter"
      by fastforce 
    then show ?thesis by auto
  next
    case False
    then have "diameter = \<infinity>" unfolding diameter_def using Sup_enat_def by auto
    then show ?thesis by simp
  qed
qed

lemma radius_diameter_singleton_eq: assumes "card V = 1" shows "radius = diameter"
proof -
  obtain v where "V = {v}" using assms card_1_singletonE by auto 
  thus ?thesis unfolding radius_def diameter_def by auto
qed

end

locale fin_connected_ulgraph = connected_ulgraph + fin_ulgraph
begin 

text \<open> In a finite context the supremum/infinum are equivalent to the Max/Min of the sets respectively.
This can make reasoning easier \<close>
lemma shortest_path_Min_alt: 
  assumes "u \<in> V" "v \<in> V"
  shows "shortest_path u v = Min ((\<lambda> p. enat (walk_length p)) ` (connecting_paths u v))" (is "shortest_path u v = Min ?A")
proof -
  have ne: "?A \<noteq> {}"
    using connecting_paths_not_empty assms by auto
  have "finite (connecting_paths u v)"
    by (simp add: fin_connecting_paths) 
  then have fin: "finite ?A"
    by simp 
  have "shortest_path u v = Inf ?A" unfolding shortest_path_def by simp
  thus ?thesis using Min_Inf ne
    by (metis fin)
qed

lemma eccentricity_Max_alt:
  assumes "v \<in> V"
  assumes "V \<noteq> {v}"
  shows "eccentricity v = Max ((\<lambda> u. shortest_path v u) ` (V - {v}))"
  unfolding eccentricity_def using assms Sup_enat_def finV not_empty
  by auto

lemma diameter_Max_alt: "diameter = Max ((\<lambda> v. eccentricity v) ` V)"
  unfolding diameter_def using Sup_enat_def finV not_empty by auto

lemma radius_Min_alt: "radius = Min ((\<lambda> v. eccentricity v) ` V)"
  unfolding radius_def using Min_Inf finV not_empty
  by (metis (no_types, opaque_lifting) empty_is_image finite_imageI) 

lemma eccentricity_obtains: 
  assumes "v \<in> V"
  assumes "V \<noteq> {v}"
  obtains u where "u \<in> V" and "u \<noteq> v" and "shortest_path u v = eccentricity v"
proof -
  have ni: "\<And> u. u \<in> V - {v} \<Longrightarrow> u \<noteq> v \<and> u \<in> V" by auto
  have ne: "V - {v} \<noteq> {}" using assms not_empty by auto
  have "eccentricity v = Max ((\<lambda> u. shortest_path v u) ` (V - {v}))" using eccentricity_Max_alt assms by simp
  then obtain u where ui: "u \<in> V - {v}" and eq: "shortest_path v u = eccentricity v" 
    using obtains_MAX assms finV ne by (metis finite_Diff) 
  then have neq: "u \<noteq> v" by blast
  have uin: "u \<in> V" using ui by auto
  thus ?thesis using neq eq that[of u] shortest_path_sym by simp
qed

lemma radius_obtains: 
  obtains v where "v \<in> V" and "radius = eccentricity v"
proof -
  have "radius = Min ((\<lambda> v. eccentricity v) ` V)" using radius_Min_alt by simp
  then obtain v where "v \<in> V" and "radius = eccentricity v" 
    using obtains_MIN[of V "(\<lambda> v . eccentricity v)"] not_empty finV by auto 
  thus ?thesis
    by (simp add: that) 
qed

lemma radius_obtains_path_vertices:
  assumes "card V \<ge> 2"
  obtains u v where "u \<in> V" and "v \<in> V" and "u \<noteq> v" and "radius = shortest_path u v"
proof -
  obtain v where vin: "v \<in> V" and e: "radius = eccentricity v"
    using radius_obtains by blast
  then have "V \<noteq> {v}" using assms by auto
  then obtain u where "u \<in> V" and "u \<noteq> v" and "shortest_path u v = radius"
    using eccentricity_obtains vin e by auto
  thus ?thesis using vin
    by (simp add: that) 
qed

lemma diameter_obtains: 
  obtains v where "v \<in> V" and "diameter = eccentricity v"
proof -
  have "diameter = Max ((\<lambda> v. eccentricity v) ` V)" using diameter_Max_alt by simp
  then obtain v where "v \<in> V" and "diameter = eccentricity v" 
    using obtains_MAX[of V "(\<lambda> v . eccentricity v)"] not_empty finV by auto 
  thus ?thesis
    by (simp add: that) 
qed

lemma diameter_obtains_path_vertices:
  assumes "card V \<ge> 2"
  obtains u v where "u \<in> V" and "v \<in> V" and "u \<noteq> v" and "diameter = shortest_path u v"
proof -
  obtain v where vin: "v \<in> V" and e: "diameter = eccentricity v"
    using diameter_obtains by blast
  then have "V \<noteq> {v}" using assms by auto
  then obtain u where "u \<in> V" and "u \<noteq> v" and "shortest_path u v = diameter"
    using eccentricity_obtains vin e by auto
  thus ?thesis using vin
    by (simp add: that) 
qed

lemma radius_diameter_bounds: 
  shows "radius \<le> diameter" "diameter \<le> 2 * radius"
proof -
  show "radius \<le> diameter" unfolding radius_def diameter_def
    by (simp add: INF_le_SUP not_empty) 
next
  show "diameter \<le> 2 * radius" 
  proof (cases "card V \<ge> 2")
    case True
    then obtain x y where xin: "x \<in> V" and yin: "y \<in> V" and d: "shortest_path x y = diameter" 
      using diameter_obtains_path_vertices by metis
    obtain z where zin: "z \<in> V" and e: "eccentricity z = radius" using radius_obtains
      by metis 
    have "shortest_path x z \<le> eccentricity z" 
      using eccentricity_gt_shortest_path xin shortest_path_sym by simp
    have "shortest_path x y \<le> shortest_path x z + shortest_path z y" using shortest_path_split by simp
    also have "... \<le> eccentricity z + eccentricity z" 
      using eccentricity_gt_shortest_path shortest_path_sym zin xin yin by (simp add: add_mono) 
    also have "... \<le> radius + radius" using e by simp
    finally  show ?thesis using d by (simp add: mult_2) 
  next
    case False
    have "card V \<noteq> 0" using not_empty finV by auto 
    then have "card V = 1" using False by simp
    then show ?thesis using radius_diameter_singleton_eq by (simp add: mult_2) 
  qed
qed

end

text \<open> We define various subclasses of the general connected graph, using the functor locale pattern\<close>
locale connected_sgraph = sgraph + ne_graph_system + 
  assumes connected: "is_connected_set V"

sublocale connected_sgraph \<subseteq> connected_ulgraph
  by (unfold_locales) (simp add: connected)

locale fin_connected_sgraph = connected_sgraph + fin_sgraph

sublocale fin_connected_sgraph \<subseteq> fin_connected_ulgraph 
  by (unfold_locales)

end