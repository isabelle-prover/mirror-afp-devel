theory Shortest_Path_Tree
  imports "Graph_Theory.Graph_Theory" "Graph_Definitions" "Graph_Theory_Batteries" "Misc"
begin

text \<open>
This theory defines the notion of a partial shortest path tree in the locale @{text psp_tree}.
A partial shortest path tree contains the s nearest notes with respect to some weight function.
Since, at the time of writing, the definition of @{const forest} only guarantees acyclicity
and the definition of @{const tree} is also incorrect by extension, we develop our own definition
of a directed tree in the locale @{text directed_tree}.
\<close>

section \<open>Directed tree\<close>

text \<open>
The following locale defines the notion of a rooted directed tree. The tree property is
established by asserting a unique walk from the root to each vertex. Note that we need
@{const pre_digraph.awalk} and not @{const pre_digraph.apath} here since we want to have only one
incoming arc for each vertex. In the locale all the usual properties of trees are established, e.g.
non-existence of @{const pre_digraph.cycle}, absence of loops with @{locale loopfree_digraph} and
multi-arcs with @{locale nomulti_digraph}.
We also prove the admissibility of an induction rule for finite trees which constructs any tree
inductively by starting with a single node (the root) and consecutively adding leaves.
Finally we define the depth of a tree.
\<close>
locale directed_tree =
    wf_digraph T for T +
fixes
  root :: 'a
assumes
  root_in_T: "root \<in> verts T" and
  unique_awalk: "v \<in> verts T \<Longrightarrow> \<exists>!p. awalk root p v"
begin

subsection \<open>General properties of trees\<close>

lemma reachable_from_root: "v \<in> verts T \<Longrightarrow> root \<rightarrow>\<^sup>*\<^bsub>T\<^esub> v"
  using unique_awalk reachable_awalkI by blast

lemma non_empty: "verts T \<noteq> {}"
  using root_in_T by blast

theorem cycle_free: "\<nexists>c. cycle c"
proof
  assume "\<exists>c. cycle c"
  then obtain c where c: "cycle c" by blast
  from unique_awalk[of "awhd root c", OF awhd_in_verts[OF root_in_T, of c]]
  obtain p where p: "awalk root p (awhd root c)"
    using c[unfolded cycle_conv] unfolding awalk_conv by auto
  from c p awalk_appendI have "awalk root (p@c) (awhd root c)"
    by (metis awalkE' cycle_def awalk_verts_ne_eq)
  with unique_awalk p c show "False"
    using awalk_last_in_verts unfolding cycle_def by blast
qed

sublocale loopfree: loopfree_digraph T
proof(standard, rule ccontr)
  fix e assume arc: "e \<in> arcs T" and loop: "\<not> tail T e \<noteq> head T e"
  then have "cycle [e]"
    unfolding cycle_conv
    using arc_implies_awalk by force
  with cycle_free show "False" by blast
qed

sublocale nomulti: nomulti_digraph T
proof(standard, rule ccontr, goal_cases)
  case (1 e1 e2)
  let ?u = "tail T e1" and ?v = "head T e1"
  from unique_awalk obtain p where "awalk root p ?u"
    using 1 tail_in_verts by blast
  with 1 have "awalk root (p@[e1]) ?v" and "awalk root (p@[e2]) ?v"
    unfolding arc_to_ends_def
    using arc_implies_awalk by (fastforce)+

  with unique_awalk show "False"
    using \<open>e1 \<noteq> e2\<close> by blast
qed


lemma connected': "\<lbrakk> u \<in> verts T; v \<in> verts T \<rbrakk> \<Longrightarrow> u \<rightarrow>\<^sup>*\<^bsub>mk_symmetric T\<^esub> v"
proof -
  let ?T' = "mk_symmetric T"
  fix u v assume "u \<in> verts T" and "v \<in> verts T"
  then have "\<exists>up. awalk root up u" and "\<exists>vp. awalk root vp v"
    using unique_awalk by blast+
  then obtain up vp where up: "awalk root up u" and vp: "awalk root vp v" by blast
  then have "u \<rightarrow>\<^sup>*\<^bsub>mk_symmetric T\<^esub> root" and "root \<rightarrow>\<^sup>*\<^bsub>mk_symmetric T\<^esub> v"
    by (meson reachable_awalkI reachable_mk_symmetricI
        symmetric_mk_symmetric symmetric_reachable)+
  then show "u \<rightarrow>\<^sup>*\<^bsub>mk_symmetric T\<^esub> v"
    by (meson wellformed_mk_symmetric wf_digraph.reachable_trans wf_digraph_wp_iff)
qed

theorem connected: "connected T"
  unfolding connected_def strongly_connected_def
  using connected' root_in_T by auto

lemma unique_awalk_All: "\<exists>p. awalk u p v \<Longrightarrow> \<exists>!p. awalk u p v"
proof(rule ccontr, goal_cases)
  case 1
  then have "\<exists>p q. awalk u p v \<and> awalk u q v \<and> p \<noteq> q"
    by blast
  then obtain p q where
    p: "awalk u p v" and q: "awalk u q v" and "p \<noteq> q" by blast
  from unique_awalk obtain w where w: "awalk root w u"
    using \<open>awalk u p v\<close> by blast
  then have "awalk root (w@p) v" and "awalk root (w@q) v" and "(w@p) \<noteq> (w@q)"
    using \<open>awalk u p v\<close> \<open>awalk u q v\<close> \<open>p \<noteq> q\<close> awalk_appendI by auto
  with unique_awalk show ?case by blast
qed

lemma unique_arc:
  shows "u \<rightarrow>\<^bsub>T\<^esub> v \<Longrightarrow> \<exists>!e \<in> arcs T. tail T e = u \<and> head T e = v"
    and "(\<nexists>e. e \<in> arcs T \<and> tail T e = u \<and> head T e = v) \<Longrightarrow> \<not> u \<rightarrow>\<^bsub>T\<^esub> v"
  using unique_awalk_All nomulti.no_multi_arcs unfolding arc_to_ends_def
  by auto

lemma unique_arc_set:
  fixes u v
  defines "A \<equiv> {e \<in> arcs T. tail T e = u \<and> head T e = v}"
  shows "A = {} \<or> (\<exists>e. A = {e})"
proof(cases "u \<rightarrow>\<^bsub>T\<^esub> v")
  case True
  note unique_arc(1)[OF True]
  then show ?thesis unfolding A_def by blast
next
  case False
  then have "\<nexists>e. e \<in> arcs T \<and> tail T e = u \<and> head T e = v"
    using in_arcs_imp_in_arcs_ends arcs_ends_def by blast
  then show ?thesis unfolding A_def by auto
qed


lemma sp_eq_awalk_cost: "awalk a p b \<Longrightarrow> awalk_cost w p = \<mu> w a b"
proof -
  assume "awalk a p b"
  with unique_awalk_All have "{p. awalk a p b} = {p}"
    by blast
  then show ?thesis unfolding \<mu>_def
    by (metis cInf_singleton image_empty image_insert)
qed

lemma sp_cost_finite: "awalk a p b \<Longrightarrow> \<mu> w a b > -\<infinity> \<and> \<mu> w a b < \<infinity>"
  using sp_eq_awalk_cost[symmetric] by simp

theorem sp_append:
  "\<lbrakk> awalk a p b; awalk b q c \<rbrakk> \<Longrightarrow> \<mu> w a c = \<mu> w a b + \<mu> w b c"
proof -
  assume p: "awalk a p b" and q: "awalk b q c"
  then have p_q: "awalk a (p@q) c" by auto
  then have "awalk_cost w (p@q) = awalk_cost w p + awalk_cost w q"
    using awalk_cost_append by blast

  with p q p_q show ?thesis using sp_eq_awalk_cost
    by (metis plus_ereal.simps(1))
qed

text \<open>Convenience lemma which reformulates @{thm sp_append} to use reachability as assumptions.\<close>
lemma sp_append2: "\<lbrakk> v1 \<rightarrow>\<^sup>*\<^bsub>T\<^esub> v2; v2 \<rightarrow>\<^sup>*\<^bsub>T\<^esub> v3 \<rbrakk>
  \<Longrightarrow> \<mu> w v1 v3 = \<mu> w v1 v2 + \<mu> w v2 v3"
  using reachable_awalk sp_append by auto

theorem connected_minimal: "e \<in> arcs T \<Longrightarrow>  \<not> (tail T e) \<rightarrow>\<^sup>*\<^bsub>(del_arc e)\<^esub> (head T e)"
proof
  let ?T' = "del_arc e" and ?u = "tail T e" and ?v = "head T e"
  assume "e \<in> arcs T" and "?u \<rightarrow>\<^sup>*\<^bsub>?T'\<^esub> ?v"
  note e = this
  then have T'_wf: "wf_digraph ?T'" by blast

  from e have "awalk ?u [e] ?v"
    by (simp add: arc_implies_awalk)
  moreover
  note wf_digraph.reachable_awalk[OF T'_wf, of ?u ?v]
  with e obtain p where p: "pre_digraph.awalk ?T' ?u p ?v" by blast

  from e have "e \<notin> arcs ?T'" by simp
  with e p have "e \<notin> set p" by (meson T'_wf subsetCE wf_digraph.awalkE')
  with p have "[e] \<noteq> p" and "awalk ?u p ?v"
    by (auto simp: subgraph_awalk_imp_awalk subgraph_del_arc)

  ultimately show False using unique_awalk_All by blast
qed

lemma All_arcs_in_path: "e \<in> arcs T \<Longrightarrow> \<exists>p u v. awalk u p v \<and> e \<in> set p"
  by (meson arc_implies_awalk list.set_intros(1))

subsection \<open>An induction rule for finite trees\<close>
text \<open>
In this section we develop an induction rule for finite trees. Since this induction rule works by
inductively adding trees we first need to define the notion of a leaf and prove numerous facts
about them.
\<close>

definition (in pre_digraph) leaf :: "'a \<Rightarrow> bool" where
  "leaf v \<equiv> v \<in> verts G \<and> out_arcs G v = {}"

lemma in_degree_root_zero: "in_degree T root = 0"
proof(rule ccontr)
  assume "in_degree T root \<noteq> 0"
  then obtain e u where e: "tail T e = u" "head T e = root" "u \<in> verts T" "e \<in> arcs T"
    by (metis tail_in_verts all_not_in_conv card.empty in_degree_def in_in_arcs_conv)
  with unique_awalk obtain p where p: "awalk root p u" by blast
  with e have "awalk root (p@[e]) root"
    using awalk_appendI arc_implies_awalk by auto
  moreover
  have "awalk root [] root" by (simp add: awalk_Nil_iff root_in_T)
  ultimately show "False" using unique_awalk by blast
qed

lemma leaf_out_degree_zero: "leaf v \<Longrightarrow> out_degree T v = 0"
  unfolding leaf_def out_degree_def by auto

lemma two_in_arcs_contr:
  assumes "e1 \<in> arcs T" "e2 \<in> arcs T" and "e1 \<noteq> e2" and "head T e1 = head T e2"
  shows "False"
proof -
  from unique_awalk assms obtain p1 p2
    where "awalk root p1 (tail T e1)" and "awalk root p2 (tail T e2)"
    by (meson tail_in_verts in_in_arcs_conv)
  with assms have "awalk root (p1@[e1]) (head T e1)" and "awalk root (p2@[e2]) (head T e1)"
    unfolding in_arcs_def
    using arc_implies_awalk by force+
  with unique_awalk \<open>e1 \<noteq> e2\<close> show "False" by blast
qed

lemma in_arcs_finite: "v \<in> verts T \<Longrightarrow> finite (in_arcs T v)"
proof(rule ccontr)
  assume "\<not> finite (in_arcs T v)"
  then obtain e1 e2
    where e1_e2: "e1 \<in> in_arcs T v" "e2 \<in> in_arcs T v" "e1 \<noteq> e2"
    by (metis finite.emptyI finite_insert finite_subset insertI1 subsetI)
  with two_in_arcs_contr show "False" unfolding in_arcs_def by auto
qed

lemma not_root_imp_in_deg_one: "\<lbrakk> v \<in> verts T; v \<noteq> root \<rbrakk>  \<Longrightarrow> in_degree T v = 1"
proof(rule ccontr)
  assume "v \<noteq> root" and "v \<in> verts T" and "in_degree T v \<noteq> 1"
  then have "in_degree T v \<noteq> 0"
  proof -
    from unique_awalk \<open>v \<in> verts T\<close> obtain p where "awalk root p v" by blast
    with \<open>v \<noteq> root\<close> have "root \<rightarrow>\<^sup>+\<^bsub>T\<^esub> v" using reachable_awalkI by blast
    then have "\<exists>u. u \<rightarrow>\<^bsub>T\<^esub> v" by (meson tranclD2)
    then show ?thesis
      using in_arcs_finite[OF \<open>v \<in> verts T\<close>] unfolding in_degree_def
      using card_eq_0_iff by fastforce
  qed
  moreover
  have "\<not> in_degree T v \<ge> 2"
  proof
    assume in_deg_ge_2: "in_degree T v \<ge> 2"
    have "\<exists>e1 e2. e1 \<in> in_arcs T v \<and> e2 \<in> in_arcs T v \<and> e1 \<noteq> e2"
    proof(cases "in_arcs T v = {}")
      case True
      then show ?thesis using in_deg_ge_2[unfolded in_degree_def] by simp
    next
      case False
      then obtain e1 where "e1 \<in> in_arcs T v" by blast
      then have "card (in_arcs T v) = 1" if "\<forall>e2 \<in> in_arcs T v. e1 = e2"
        using that by(auto simp: card_Suc_eq[where ?A="(in_arcs T v)"])
      then show ?thesis
        using in_deg_ge_2[unfolded in_degree_def] \<open>e1 \<in> in_arcs T v\<close> by force
    qed
    with two_in_arcs_contr show "False" unfolding in_arcs_def by auto
  qed
  ultimately show "False" using \<open>in_degree T v \<noteq> 1\<close> by linarith
qed

lemma in_deg_one_imp_not_root: "\<lbrakk> v \<in> verts T; in_degree T v = 1 \<rbrakk>  \<Longrightarrow> v \<noteq> root"
  using in_degree_root_zero by auto

corollary in_deg_one_iff: "v \<in> verts T \<Longrightarrow> v \<noteq> root \<longleftrightarrow> in_degree T v = 1"
  using not_root_imp_in_deg_one in_deg_one_imp_not_root by blast

lemma ex_in_arc: "\<lbrakk> v \<noteq> root; v \<in> verts T \<rbrakk> \<Longrightarrow> \<exists>e. in_arcs T v = {e}"
  using not_root_imp_in_deg_one unfolding in_degree_def
  by (auto simp: card_Suc_eq)

lemma ex_leaf: "finite (verts T) \<Longrightarrow> \<exists>v \<in> verts T. leaf v"
proof(rule ccontr, simp)
  assume verts_fin: "finite (verts T)" and  no_leaves: "\<forall>x\<in>verts T. \<not> leaf x"
  then have "\<forall>x \<in> verts T. \<exists>e. e \<in> out_arcs T x"
    unfolding leaf_def by (simp add: out_arcs_def)
  then have "\<forall>x \<in> verts T. \<exists>x' e. awalk x [e] x'"
    unfolding out_arcs_def using arc_implies_awalk by force
  then have extend: "\<exists>p v'. awalk u (ps@[p]) v'" if "awalk u ps v" for u ps v
    using that by force
  have "\<exists>u p v. awalk u p v \<and> length p = n" for n
  proof(induction n)
    case 0
    from root_in_T have "awalk root [] root"
      by (simp add: awalk_Nil_iff)
    then show ?case by blast
  next
    case (Suc n)
    then obtain u p v where "awalk u p v" and "length p = n" by blast
    from extend[OF this(1)] obtain e v' where "awalk u (p@[e]) v'" and "length (p@[e]) = Suc n"
      using length_append_singleton \<open>length p = n\<close> by auto
    then show ?case by blast
  qed
  with awalk_not_distinct[OF verts_fin] have "\<exists>p. cycle p"
    using awalk_cyc_decompE' closed_w_imp_cycle by (metis order_refl)
  with cycle_free show False by blast
qed

lemma verts_finite_imp_arcs_finite: "finite (verts T) \<Longrightarrow> finite (arcs T)"
proof -
  assume "finite (verts T)"
  then have "finite (verts T \<times> verts T)" by simp
  let ?a = "\<lambda>(u,v). {e \<in> arcs T.  tail T e = u \<and> head T e = v}"
  let ?A = "\<Union>{?a e |e. e \<in> verts T \<times> verts T}"
  have "arcs T \<subseteq> ?A"
  proof
    fix e assume e: "e \<in> arcs T"
    then have "tail T e \<in> verts T" and "head T e \<in> verts T"
      using wellformed by auto
    with e show "e \<in> ?A" by blast
  qed
  moreover
  have "finite (?a (u,v))" for u v
    using unique_arc_set[of u v] finite.simps by auto
  with finite_Union[OF \<open>finite (verts T \<times> verts T)\<close>] have "finite ?A"
    by blast
  ultimately show "finite (arcs T)" using finite_subset by blast
qed

lemma root_leaf_iff: "leaf root \<longleftrightarrow> verts T = {root}"
proof
  from root_in_T show "verts T = {root} \<Longrightarrow> leaf root"
    using leaf_def ex_leaf by auto
  show "leaf root \<Longrightarrow> (verts T = {root})"
  proof(rule ccontr)
    assume "leaf root" and "verts T \<noteq> {root}"
    with non_empty obtain u where u: "u \<in> verts T" "u \<noteq>root"
      by blast
    with unique_awalk obtain p where p: "awalk root p u" by blast
    with \<open>u \<noteq> root\<close> obtain e where e: "e = hd p" "tail T e = root"
      by (metis awalkE' awalk_ends pre_digraph.cas_simp)
    with u p have "e \<in> out_arcs T root" unfolding out_arcs_def
      by (simp, metis awalkE awalk_ends hd_in_set subset_iff)
    with \<open>leaf root\<close> show "False"
      unfolding leaf_def out_degree_def by auto
  qed
qed

lemma leaf_not_mem_awalk:
  "\<lbrakk> leaf x; awalk u p v; v \<noteq> x \<rbrakk> \<Longrightarrow> x \<notin> set (awalk_verts u p)"
proof(induction p arbitrary: u)
  case Nil
  then have "u = v" unfolding awalk_conv by simp
  with Nil show ?case by auto
next
  case (Cons a p)
  then have "x \<notin> set (awalk_verts (head T a) p)" by (simp add: awalk_Cons_iff)
  moreover
  from Cons.prems have "tail T a \<noteq> x"
    unfolding leaf_def out_arcs_def by auto
  ultimately show ?case by simp
qed

lemma tree_del_vert:
  assumes "v \<noteq> root" and "leaf v"
  shows "directed_tree (del_vert v) root"
proof(unfold_locales)
  from \<open>v \<noteq> root\<close> show "root \<in> verts (del_vert v)" using verts_del_vert root_in_T by auto

  have "u\<in>verts (del_vert v) \<Longrightarrow> \<exists>!p. pre_digraph.awalk (del_vert v) root p u" for u
  proof -
    assume "u \<in> verts (del_vert v)"
    then have "u \<in> verts T" "u \<noteq> v" by (simp_all add: verts_del_vert)
    then obtain p where p: "awalk root p u" "\<forall>p'. awalk root p' u \<longrightarrow> p = p'"
    using unique_awalk[OF \<open>u \<in> verts T\<close>] by auto
    then have "v \<notin> set (awalk_verts root p)"
    using leaf_not_mem_awalk[OF \<open>leaf v\<close> _ \<open>u \<noteq> v\<close>] by blast
    with p have
      "pre_digraph.awalk (del_vert v) root p u"
      "\<forall>p'. pre_digraph.awalk (del_vert v) root p' u \<longrightarrow> p = p'"
      using awalk_del_vert subgraph_awalk_imp_awalk subgraph_del_vert by blast+
    then show ?thesis by blast
  qed
  then show "\<And>va. va \<in> verts (del_vert v)
  \<Longrightarrow> \<exists>!p. pre_digraph.awalk (del_vert v) root p va" by blast
qed (meson wf_digraph_del_vert wf_digraph_def)+

lemma arcs_del_leaf:
  assumes e: "e \<in> arcs T" "head T e = v" and v: "leaf v"
  shows "arcs (del_vert v) = arcs T - {e}"
proof -
  from v have "out_arcs T v = {}"
    unfolding pre_digraph.leaf_def by simp
  moreover
  from e v have "v \<noteq> root"
    using loopfree.no_loops root_leaf_iff by fastforce
  from ex_in_arc[OF this] v have "in_arcs T v = {e}"
    unfolding pre_digraph.leaf_def using e e two_in_arcs_contr by fastforce
  ultimately show ?thesis unfolding out_arcs_def in_arcs_def
    using arcs_del_vert2 by auto
qed

lemma finite_directed_tree_induct[consumes 1, case_names single_vert add_leaf]:
  assumes "finite (verts T)"
  assumes base: "\<And>t h root. P \<lparr> verts = {root}, arcs = {}, tail = t, head = h \<rparr>"
      and add_leaf: "\<And>T' V A t h u root a v. \<lbrakk>T' = \<lparr> verts = V, arcs = A, tail = t, head = h \<rparr>; finite (verts T');
            directed_tree T' root; P T'; u \<in> V; v \<notin> V; a \<notin> A\<rbrakk>
    \<Longrightarrow> P \<lparr> verts = V \<union> {v}, arcs = A \<union> {a}, tail = t(a := u), head = h(a := v) \<rparr>"
    shows "P T"
  using assms(1) directed_tree_axioms
proof(induction "card (verts T)" arbitrary: T root)
  case 0
  then have "verts T = {}" using card_eq_0_iff by simp
  with directed_tree.non_empty[OF \<open>directed_tree T root\<close>] show ?case by blast
next
  case (Suc n)
  then interpret tree_T: directed_tree T root by simp
  show ?case
  proof(cases "n = 0")
    case True
    with \<open>Suc n = card (verts T)\<close> have "card (verts T) = 1" by simp
    from mem_card1_singleton[OF tree_T.root_in_T this] have "verts T = {root}" .
    then have "arcs T = {}"
      using tree_T.loopfree.no_loops tree_T.tail_in_verts by fastforce
    with \<open>verts T = {root}\<close> have "T = \<lparr> verts = {root}, arcs = {}, tail = tail T, head = head T \<rparr>"
      by simp
    with base[of root "tail T" "head T"] show ?thesis by simp
  next
    case False

    from Suc.prems(1) have "finite (verts T)"
      using finite_insert by simp
    from tree_T.ex_leaf[OF this]
    obtain v where v: "tree_T.leaf v" by blast
    with False have "v \<noteq> root"
      using tree_T.root_leaf_iff Suc.hyps(2) by fastforce
    note v = \<open>tree_T.leaf v\<close> \<open>v \<noteq> root\<close>

    let ?T' = "tree_T.del_vert v"
    have T': "?T' = \<lparr> verts = verts ?T', arcs = arcs ?T', tail = tail ?T', head = head ?T' \<rparr>"
      by simp
    note tree_T.tree_del_vert[OF v(2,1)]
    moreover
    have "finite (verts ?T')"
      by (simp add: tree_T.verts_del_vert \<open>finite (verts T)\<close>)
    moreover
    from \<open>finite (verts ?T')\<close> Suc.hyps(2) Suc.prems(1) have "card (verts ?T') = n"
      using tree_T.verts_del_vert v(1)[unfolded tree_T.leaf_def] by auto
    moreover
    from tree_T.ex_in_arc[OF v(2)]
    obtain e where e: "in_arcs T v = {e}" "tail T e \<in> verts T"
      using v(1)[unfolded tree_T.leaf_def] by force
    then have "tail T e \<in> verts ?T'"
      unfolding in_arcs_def using tree_T.arcs_del_vert[of v]
      using tree_T.loopfree.no_loops tree_T.verts_del_vert[of v]
      using v(1)[unfolded tree_T.leaf_def] by fastforce
    moreover
    from Suc.hyps(1) have "P ?T'" using calculation by blast
    moreover
    note tree_T.verts_del_vert[of v]
    moreover
    from e have "head T e = v" unfolding in_arcs_def by blast
    then have "e \<notin> arcs ?T'" unfolding tree_T.arcs_del_vert by simp

    ultimately have "P \<lparr> verts = verts ?T' \<union> {v}, arcs = arcs ?T' \<union> {e},
      tail = (tail ?T')(e := (tail T e)), head = (head ?T')(e := v) \<rparr>"
      using add_leaf[OF T'] by blast
    moreover
    have "T = \<lparr> verts = verts ?T' \<union> {v}, arcs = arcs ?T' \<union> {e},
      tail = (tail ?T')(e := (tail T e)), head = (head ?T')(e := v) \<rparr>"
    proof -
      have "verts T = verts ?T' \<union> {v}"
        using v(1)[unfolded tree_T.leaf_def] tree_T.verts_del_vert[of v] by fastforce
      moreover
      have "arcs ?T' = arcs T - out_arcs T v - in_arcs T v"
        using tree_T.arcs_del_vert2 by fastforce
      with e v(1)[unfolded pre_digraph.leaf_def] have "arcs T = arcs ?T' \<union> {e}" by auto
      moreover
      have "tail T = (tail ?T')(e := (tail T e))"
        by (simp add: tree_T.tail_del_vert)
      moreover
      from e[unfolded in_arcs_def] have "head T = (head ?T')(e := v)"
        using tree_T.head_del_vert \<open>head T e = v\<close> by auto
      ultimately show ?thesis by simp
    qed
    ultimately show ?thesis by simp
  qed
qed

text \<open>A simple consequence of the induction rule is that a tree with n vertices has n-1 arcs.\<close>
lemma Suc_card_arcs_eq_card_verts:
  assumes "finite (verts T)"
  shows "Suc (card (arcs T)) = card (verts T)"
using assms
proof(induction rule: finite_directed_tree_induct)
  case (single_vert)
  then show ?case by simp
next
  case (add_leaf)
  then show ?case
    using directed_tree.verts_finite_imp_arcs_finite
    by fastforce
qed

subsection \<open>Depth of a tree\<close>

definition depth where "depth w \<equiv> Sup {\<mu> w root v|v. v \<in> verts T}"

context
  fixes w :: "'b weight_fun"
  assumes "\<forall>e \<in> arcs T. w e \<ge> 0"
begin

lemma sp_from_root_le: "u \<rightarrow>\<^sup>*\<^bsub>T\<^esub> v \<Longrightarrow> \<mu> w root v \<ge> \<mu> w u v"
proof -
  assume "u \<rightarrow>\<^sup>*\<^bsub>T\<^esub> v"

  have "\<mu> w root u \<ge> 0"
    using \<open>\<forall>e\<in>arcs T. 0 \<le> w e\<close> sp_non_neg_if_w_non_neg by simp
  moreover
  have "root \<rightarrow>\<^sup>*\<^bsub>T\<^esub> u"
    using \<open>u \<rightarrow>\<^sup>*\<^bsub>T\<^esub> v\<close> reachable_from_root reachable_in_verts(1) by auto
  ultimately show ?thesis
    using \<open>u \<rightarrow>\<^sup>*\<^bsub>T\<^esub> v\<close> sp_append2 ereal_le_add_self2 by auto
qed

lemma depth_lowerB: "v \<in> verts T \<Longrightarrow> depth w \<ge> \<mu> w root v"
proof -
  assume "v \<in> verts T"
  then have "\<mu> w root v \<in> {\<mu> w root v|v. v \<in> verts T}" by auto
  then show "depth w \<ge> \<mu> w root v"
    unfolding depth_def by (simp add: Sup_upper)
qed

lemma depth_upperB: "\<forall>v \<in> verts T. \<mu> w root v \<le> d \<Longrightarrow> depth w \<le> d"
proof -
  assume "\<forall>v \<in> verts T. \<mu> w root v \<le> d"
  then have "\<forall>x \<in> {\<mu> w root v |v. v \<in> verts T}. x \<le> d"
    by auto
  then show ?thesis
    unfolding depth_def using Sup_least by fast
qed

text \<open>
This relation between depth of a tree and its diameter is later used to establish the
correctness of the diameter estimate.
\<close>
lemma depth_eq_fin_dia: "fin_digraph T \<Longrightarrow> depth w = fin_diameter w"
proof -
  assume "fin_digraph T"
  have "\<forall>v \<in> verts T. \<mu> w root v < \<infinity>"
    using \<mu>_reach_conv reachable_from_root by blast
  then have "{\<mu> w root v|v. v \<in> verts T} \<subseteq> fin_sp_costs w"
    unfolding fin_sp_costs_def using root_in_T by blast
  then have "depth w \<le> fin_diameter w"
    unfolding depth_def fin_diameter_def by (simp add: Sup_subset_mono)
  moreover
  have "\<not> depth w < fin_diameter w"
  proof
    assume "depth w < fin_diameter w"
    obtain u v where "\<mu> w u v = fin_diameter w" "u \<in> verts T" "v \<in> verts T"
      using fin_digraph.ex_sp_eq_fin_dia[OF \<open>fin_digraph T\<close> non_empty] by blast
    then have "u \<rightarrow>\<^sup>*\<^bsub>T\<^esub> v"
      by (metis \<mu>_reach_conv fin_digraph.fin_diameter_finite[OF \<open>fin_digraph T\<close>])
    then have "\<mu> w u v \<le> \<mu> w root v" using sp_from_root_le by blast
    also have "\<dots> \<le> depth w" using depth_lowerB[OF \<open>v \<in> verts T\<close>] by simp
    finally have "fin_diameter w \<le> depth w"
      using \<open>\<mu> w u v = fin_diameter w\<close> by simp
    with \<open>depth w < fin_diameter w\<close> show False by simp
  qed
  ultimately show ?thesis by simp
qed

end

end

section \<open>Subgraph locale\<close>

locale subgraph =
    G: wf_digraph G for T G +
assumes
  sub_G: "subgraph T G"
begin

sublocale wf_digraph T
  using sub_G unfolding subgraph_def by blast

lemma awalk_sub_imp_awalk:
  "awalk a p b \<Longrightarrow> G.awalk a p b"
  using G.subgraph_awalk_imp_awalk sub_G by force

end

section \<open>Partial shortest path three\<close>

locale psp_tree =
  directed_tree T source + subgraph T G for G T w source n +
  assumes
    source_in_G: "source \<in> verts G" and
    partial: "G.n_nearest_verts w source n (verts T)" and
    sp: "u \<in> verts T \<Longrightarrow> \<mu> w source u = G.\<mu> w source u"
begin

text \<open>
Here we formalize the notion of a partial shortest path tree. This is a shortest path tree where
only the @{term n} nearest nodes in the graph @{term G} are explored.
Consequently, a partial shortest path tree is a subtree of the complete shortest path tree.
We can obtain the complete shortest path tree by choosing n to be larger than the cardinality
of the graph @{term G}.
\<close>

sublocale fin_digraph T
proof(unfold_locales)
  show "finite (verts T)" using G.nnvs_finite[OF partial] .
  from verts_finite_imp_arcs_finite[OF this] show "finite (arcs T)" .
qed

lemma card_verts_le: "card (verts T) \<le> Suc n"
  using G.nnvs_card_le_n partial by auto

lemma reachable_subs: "{x. r \<rightarrow>\<^sup>*\<^bsub>T\<^esub> x} \<subseteq> {x. r \<rightarrow>\<^sup>*\<^bsub>G\<^esub> x}"
  by (simp add: Collect_mono G.reachable_mono sub_G)

text \<open>The following lemma proves that we explore all nodes if we set @{term n} large enough.\<close>
lemma sp_tree:
  assumes "fin_digraph G"
  assumes card_reachable: "Suc n \<ge> card {x. source \<rightarrow>\<^sup>*\<^bsub>G\<^esub> x}"
  shows "verts T = {x. source \<rightarrow>\<^sup>*\<^bsub>G\<^esub> x}"
  using fin_digraph.nnvs_imp_all_reachable_Suc[OF \<open>fin_digraph G\<close> partial card_reachable] .

corollary sp_tree2:
  assumes "fin_digraph G"
  assumes "Suc n \<ge> card (verts G)"
  shows "verts T = {x. source \<rightarrow>\<^sup>*\<^bsub>G\<^esub> x}"
proof -
  have "{x. source \<rightarrow>\<^sup>*\<^bsub>G\<^esub> x} \<subseteq> verts G"
    using source_in_G G.reachable_in_verts(2) by blast
  then have "Suc n \<ge> card {x. source \<rightarrow>\<^sup>*\<^bsub>G\<^esub> x}"
    using \<open>Suc n \<ge> card (verts G)\<close> fin_digraph.finite_verts[OF \<open>fin_digraph G\<close>]
    by (meson card_mono dual_order.trans)
  from sp_tree[OF \<open>fin_digraph G\<close> this] show ?thesis .
qed

lemma strongly_con_imp_card_verts_eq:
  assumes "fin_digraph G"
  assumes "strongly_connected G"
  assumes card_verts: "Suc n \<le> card (verts G)"
  shows "card (verts T) = Suc n"
proof -
  have verts_G: "verts G = {x. source \<rightarrow>\<^sup>*\<^bsub>G\<^esub> x}"
    using G.strongly_con_imp_reachable_eq_verts
      [OF source_in_G \<open>strongly_connected G\<close>, symmetric] .
  with card_verts have "Suc n \<le> card {x. source \<rightarrow>\<^sup>*\<^bsub>G\<^esub> x}" by simp

  from fin_digraph.nnvs_imp_reachable[OF \<open>fin_digraph G\<close> partial this]
  show ?thesis by blast
qed

lemma depth_fin_dia_lB:
  assumes "\<forall>e \<in> arcs G. w e \<ge> 0"
  shows "depth w \<le> G.fin_diameter w"
proof(rule ccontr)
  assume "\<not> depth w \<le> G.fin_diameter w"
  then have "depth w > G.fin_diameter w"
    by auto
  then have "\<exists>v \<in> verts T. \<mu> w source v > G.fin_diameter w"
    unfolding depth_def by (auto simp: less_Sup_iff)
  then obtain v where v: "v \<in> verts T" "v \<in> verts G" "\<mu> w source v > G.fin_diameter w"
    using sub_G by blast
  moreover
  have "\<mu> w source v < \<infinity>"
    using reachable_from_root \<mu>_reach_conv v(1) by blast
  ultimately show "False"
    using source_in_G G.fin_dia_lowerB[OF source_in_G \<open>v \<in> verts G\<close>] sp v
    by (simp add: leD)
qed

end

end