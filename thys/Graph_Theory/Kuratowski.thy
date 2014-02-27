(*  Title:  Kuratowski.thy
    Author: Lars Noschinski, TU München
*)

theory Kuratowski
imports
  Arc_Walk
  Digraph_Component
  Pair_Digraph
begin

section {* Kuratowski Subgraphs *}

text {*
  We consider the underlying undirected graphs. The underlying undirected graph is represented as a
  symmetric digraph.
*}

subsection {* Public definitions *}

definition complete_digraph :: "nat \<Rightarrow> 'a pair_pre_digraph \<Rightarrow> bool" ("K\<^bsub>_\<^esub>") where
  "complete_digraph n G \<equiv> finite (pverts G) \<and> card (pverts G) = n \<and> parcs G = {(u,v). (u,v) \<in> (pverts G \<times> pverts G) \<and> u \<noteq> v}"

definition complete_bipartite_digraph :: "nat \<Rightarrow> nat \<Rightarrow> 'a pair_pre_digraph \<Rightarrow> bool" ("K\<^bsub>_,_\<^esub>") where
  "complete_bipartite_digraph m n G \<equiv> finite (pverts G) \<and> (\<exists>U V. pverts G = U \<union> V \<and> U \<inter> V = {}
    \<and> card U = m \<and> card V = n \<and> parcs G = U \<times> V \<union> V \<times> U)"

lemma pair_graphI_complete:
  assumes "K\<^bsub>n\<^esub> G" shows "pair_graph G"
proof
  have "finite (pverts G \<times> pverts G)" "parcs G \<subseteq> pverts G \<times> pverts G"
    using assms by (auto simp: complete_digraph_def)
  then show "finite (parcs G)" by (rule rev_finite_subset)
qed (insert assms, auto simp: complete_digraph_def symmetric_def split: prod.splits intro: symI)

lemma pair_graphI_complete_bipartite:
  assumes "K\<^bsub>m,n\<^esub> G" shows "pair_graph G"
  using assms by unfold_locales (fastforce simp: complete_bipartite_digraph_def symmetric_def split: prod.splits intro: symI)+

definition planar :: "'a pair_pre_digraph \<Rightarrow> bool" where
  "planar G \<equiv> \<not>(\<exists>H. subgraph (with_proj H) G \<and> (\<exists>K. subdivision K H \<and> (K\<^bsub>3,3\<^esub> K \<or> K\<^bsub>5\<^esub> K)))"

subsection {* Inner vertices of a walk *}

context pre_digraph begin

definition (in pre_digraph) inner_verts :: "'b awalk \<Rightarrow> 'a list" where
  "inner_verts p \<equiv> tl (map (tail G) p)"

lemma inner_verts_Nil[simp]: "inner_verts [] = []" by (auto simp: inner_verts_def)

lemma inner_verts_singleton[simp]: "inner_verts [x] = []" by (auto simp: inner_verts_def)

lemma (in wf_digraph) inner_verts_Cons:
  assumes "awalk u (e # es) v"
  shows "inner_verts (e # es) = (if es \<noteq> [] then head G e # inner_verts es else [])"
  using assms by (induct es) (auto simp: inner_verts_def)

lemma (in - ) inner_verts_with_proj_def:
  "pre_digraph.inner_verts (with_proj G) p = tl (map fst p)"
  unfolding pre_digraph.inner_verts_def by simp

lemma inner_verts_conv: "inner_verts p = butlast (tl (awalk_verts u p))"
  unfolding inner_verts_def awalk_verts_conv by simp

lemma (in fin_digraph) set_inner_verts:
  assumes "apath u p v"
  shows "set (inner_verts p) = set (awalk_verts u p) - {u,v}"
proof (cases "length p < 2")
  case True with assms show ?thesis
    by (cases p) (auto simp: inner_verts_conv[of _ u] apath_def)
next
  case False
  have "awalk_verts u p = u # inner_verts p @ [v]"
    using assms False length_awalk_verts[of u p] inner_verts_conv[of p u]
    by (cases "awalk_verts u p") (auto simp: apath_def awalk_conv)
  then show ?thesis using assms by (auto simp: apath_def)
qed

lemma in_set_inner_verts_appendI_l:
  assumes "u \<in> set (inner_verts p)"
  shows "u \<in> set (inner_verts (p @ q))"
  using assms
by (induct p) (auto simp: inner_verts_def)

lemma in_set_inner_verts_appendI_r:
  assumes "u \<in> set (inner_verts q)"
  shows "u \<in> set (inner_verts (p @ q))"
  using assms
by (induct p) (auto simp: inner_verts_def dest: list_set_tl)

end


subsection {* Walks with Restricted Vertices *}

definition verts3 :: "('a, 'b) pre_digraph \<Rightarrow> 'a set" where
  "verts3 G \<equiv> {v \<in> verts G. 2 < in_degree G v}"

text {* A path were only the end nodes may be in @{term V} *}

(*
  From this definition, we at least need the following properties:
    - The end nodes must be distinct (to match graph computed by the C code)
    - If there is only one connection between u and v, p must be unique

  This means we cannot replace apath by awalk, without adding at least the following restrictions:
    - u \<noteq> v
    - progressing p
  It might be possible to drop "progressing p" if we talk about trails instead
*)
definition (in pre_digraph) gen_iapath :: "'a set \<Rightarrow> 'a \<Rightarrow> 'b awalk \<Rightarrow> 'a \<Rightarrow> bool" where
  "gen_iapath V u p v \<equiv> u \<in> V \<and> v \<in> V \<and> apath u p v \<and> set (inner_verts p) \<inter> V = {} \<and> p \<noteq> []"

abbreviation (in pre_digraph) (input) iapath :: "'a \<Rightarrow> 'b awalk \<Rightarrow> 'a \<Rightarrow> bool" where
  "iapath u p v \<equiv> gen_iapath (verts3 G) u p v"

definition gen_contr_graph :: "('a,'b) pre_digraph \<Rightarrow> 'a set \<Rightarrow> 'a pair_pre_digraph" where
  "gen_contr_graph G V \<equiv> \<lparr>
     pverts = V,
     parcs = {(u,v). \<exists>p. pre_digraph.gen_iapath G V u p v}
     \<rparr>"

abbreviation (input) contracted_graph :: "'a pair_pre_digraph \<Rightarrow> 'a pair_pre_digraph" where
  "contracted_graph G \<equiv> gen_contr_graph G (verts3 G)"



subsection {* Properties of subdivisions *}

lemma (in pair_pseudo_graph) verts3_subdivide:
  assumes "e \<in> parcs G" "w \<notin> pverts G"
  shows"verts3 (subdivide G e w) = verts3 G"
proof -
  let ?sG = "subdivide G e w" 
  obtain u v where e_conv[simp]: "e = (u,v)" by (cases e) auto

  from `w \<notin> pverts G`
  have w_arcs: "(u,w) \<notin> parcs G" "(v,w) \<notin> parcs G" "(w,u) \<notin> parcs G" "(w,v) \<notin> parcs G"
    by (auto dest: wellformed)
  have G_arcs: "(u,v) \<in> parcs G" "(v,u) \<in> parcs G"
    using `e \<in> parcs G` by (auto simp: arcs_symmetric) 

  have "{v \<in> pverts G. 2 < in_degree G v} = {v \<in> pverts G. 2 < in_degree ?sG v}"
  proof -
    { fix x assume "x \<in> pverts G"
      def card_eq \<equiv> "\<lambda>x. in_degree ?sG x = in_degree G x"

      have "in_arcs ?sG u = (in_arcs G u - {(v,u)}) \<union> {(w,u)}"
           "in_arcs ?sG v = (in_arcs G v - {(u,v)}) \<union> {(w,v)}"
        using w_arcs G_arcs by auto
      then have "card_eq u" "card_eq v"
        unfolding card_eq_def in_degree_def using w_arcs G_arcs
        by (simp_all add: card_insert_disjoint finite_in_arcs  card_Suc_Diff1
            del: card_Diff_insert)
      moreover
      have "x \<notin> {u,v} \<Longrightarrow> in_arcs ?sG x = in_arcs G x"
        using `x \<in> pverts G` `w \<notin> pverts G` by (auto simp: )
      then have "x \<notin> {u,v} \<Longrightarrow> card_eq x" by (simp add: in_degree_def card_eq_def)
      ultimately have "card_eq x" by fast
      then have "in_degree G x = in_degree ?sG x"
        unfolding card_eq_def by simp }
    then show ?thesis by auto
  qed
  also have "\<dots> = {v\<in>pverts ?sG. 2 < in_degree ?sG v}"
  proof -
    have "in_degree ?sG w \<le> 2"
    proof -
      have "in_arcs ?sG w = {(u,w), (v,w)}"
        using `w \<notin> pverts G` G_arcs(1) by (auto simp: wellformed')
      then show ?thesis
        unfolding in_degree_def by (auto simp: card_insert_if)
    qed
    then show ?thesis using G_arcs assms by auto
  qed
  finally show ?thesis by (simp add: verts3_def)
qed

lemma sd_path_Nil_iff:
  "sd_path e w p = [] \<longleftrightarrow> p = []"
  by (cases "(e,w,p)" rule: sd_path.cases) auto

lemma (in pair_pseudo_graph) gen_iapath_sd_path:
  fixes e :: "'a \<times> 'a" and w :: 'a
  assumes elems: "e \<in> parcs G" "w \<notin> pverts G"
  assumes V: "V \<subseteq> pverts G"
  assumes path: "gen_iapath V u p v"
  shows "pre_digraph.gen_iapath (subdivide G e w) V u (sd_path e w p) v"
proof -
  obtain x y where e_conv: "e = (x,y)" by (cases e) auto
  interpret S: pair_pseudo_graph "subdivide G e w"
    using elems by (auto intro: pair_pseudo_graph_subdivide)

  from path have "apath u p v" by (auto simp: gen_iapath_def)
  then have apath_sd: "S.apath u (sd_path e w p) v" and
    set_ev_sd: "set (S.awalk_verts u (sd_path e w p)) \<subseteq> set (awalk_verts u p) \<union> {w}"
    using elems by (rule apath_sd_path set_awalk_verts_sd_path)+
  have "w \<notin> {u,v}" using elems `apath u p v`
    by (auto simp: apath_def awalk_hd_in_verts awalk_last_in_verts)

  have "set (S.inner_verts (sd_path e w p)) = set (S.awalk_verts u (sd_path e w p)) - {u,v}"
    using apath_sd by (rule S.set_inner_verts)
  also have "\<dots> \<subseteq> set (awalk_verts u p) \<union> {w} - {u,v}"
    using set_ev_sd by auto
  also have "\<dots> = set (inner_verts p) \<union> {w}"
    using set_inner_verts[OF `apath u p v`] `w \<notin> {u,v}` by blast
  finally have "set (S.inner_verts (sd_path e w p)) \<inter> V \<subseteq> (set (inner_verts p) \<union> {w}) \<inter> V"
    using V by blast
  also have "\<dots> \<subseteq> {}"
    using path elems V unfolding gen_iapath_def by auto
  finally show ?thesis
    using apath_sd elems path by (auto simp: gen_iapath_def S.gen_iapath_def sd_path_Nil_iff)
qed

lemma (in pair_pseudo_graph)
  assumes elems: "e \<in> parcs G" "w \<notin> pverts G"
  assumes V: "V \<subseteq> pverts G"
  assumes path: "pre_digraph.gen_iapath (subdivide G e w) V u p v"
  shows gen_iapath_co_path: "gen_iapath V u (co_path e w p) v" (is ?thesis_path)
    and set_awalk_verts_co_path': "set (awalk_verts u (co_path e w p)) = set (awalk_verts u p) - {w}" (is ?thesis_set)
proof -
  interpret S: pair_pseudo_graph "subdivide G e w"
    using elems by (rule pair_pseudo_graph_subdivide)

  have uv: "u \<in> pverts G" "v \<in> pverts G" "S.apath u p v" using V path by (auto simp: S.gen_iapath_def)
  note co = apath_co_path[OF elems uv] set_awalk_verts_co_path[OF elems uv]

  show ?thesis_set by (fact co)
  show ?thesis_path using co path unfolding gen_iapath_def S.gen_iapath_def using elems
    by (clarsimp simp add: set_inner_verts[of u] S.set_inner_verts[of u]) blast
qed



subsection {* Pair Graphs *}

context pair_pseudo_graph begin

lemma gen_iapath_rev_path:
  "gen_iapath V v (rev_path p) u = gen_iapath V u p v" (is "?L = ?R")
proof -
  { fix u p v assume "gen_iapath V u p v"
    then have "butlast (tl (awalk_verts v (rev_path p))) = rev (butlast (tl (awalk_verts u p)))"
      by (auto simp: tl_rev butlast_rev butlast_tl awalk_verts_rev_path gen_iapath_def apath_def)
    with `gen_iapath V u p v` have "gen_iapath V v (rev_path p) u"
      by (auto simp: gen_iapath_def apath_def inner_verts_conv[symmetric] awalk_verts_rev_path) }
  note RL = this
  show ?thesis by (auto dest: RL intro: RL)
qed

lemma inner_verts_rev_path:
  assumes "awalk u p v"
  shows "inner_verts (rev_path p) = rev (inner_verts p)"
by (metis assms butlast_rev butlast_tl awalk_verts_rev_path inner_verts_conv tl_rev)

lemma awalk_Cons_deg2_unique:
  assumes "apath u p v" "p \<noteq> []"
  assumes "in_degree G u \<le> 2"
  assumes "apath u1 (e1 # p) v" "apath u2 (e2 # p) v"
  shows "e1 = e2"
proof (cases p)
  case (Cons e es)
  show ?thesis
  proof (rule ccontr)
    assume "e1 \<noteq> e2"
    def x \<equiv> "snd e"
    then have e_unf:"e = (u,x)" using `apath u p v`  Cons by (auto simp: apath_simps)
    then have ei_unf: "e1 = (u1, u)" "e2 = (u2, u)"
      using Cons assms by (auto simp: apath_simps prod_eqI)
    with assms `e = (u,x)` `e1 \<noteq> e2` have "u1 \<noteq> u2" "x \<noteq> u1" "x \<noteq> u2"
      by (auto simp: apath_simps `p = _` hd_in_awalk_verts)
    moreover have "{(u1, u), (u2, u), (x,u)} \<subseteq> parcs G"
      using e_unf ei_unf Cons assms by (auto simp: apath_simps intro: arcs_symmetric)
    then have "finite (in_arcs G u)"
      and "{(u1, u), (u2, u), (x,u)} \<subseteq> in_arcs G u" by auto
    then have "card ({(u1, u), (u2, u), (x,u)}) \<le> in_degree G u"
      unfolding in_degree_def by (rule card_mono) 
    ultimately show "False" using `in_degree G u \<le> 2` by auto
  qed
qed (simp add: `p \<noteq> []`)

lemma same_awalk_by_length:
  assumes walk: "apath u1 p v" "apath u2 q v" "last p = last q"
    and verts: "set (inner_verts p) \<inter> verts3 G = {}"
      "set (inner_verts q) \<inter> verts3 G = {}"
    and len: "length p = length q"
  shows "p = q"
using len walk verts
proof (induct p q arbitrary: u1 u2 rule: list_induct2)
  case (Cons e1 es1 e2 es2)
  show ?case
  proof (cases "length es1 = 0")
    case True then show ?thesis using Cons by simp
  next
    case False
    from Cons have "apath (snd e1) es1 v" "snd e1 \<in> pverts G"
      by (auto simp: apath_Cons_iff)
    moreover
    have "snd e1 \<in> set (inner_verts (e1 # es1))"
      using False `apath u1 (e1 # es1) v` by (auto simp: apath_def inner_verts_Cons)
    then have "in_degree G (snd e1) \<le> 2"
      using Cons(6) `snd e1 \<in> pverts G` by (auto simp: verts3_def)
    moreover
    from Cons.prems (4-5) have "set (inner_verts es1) \<inter> verts3 G = {}"
        "set (inner_verts es2) \<inter> verts3 G = {}"
      unfolding inner_verts_def by (auto dest!: list_set_tl)
    with Cons have "es1 = es2"
      by (intro Cons) (auto simp: apath_Cons_iff split: split_if_asm)
    moreover
    then have "apath u2 (e2 # es1) v" using Cons by simp
    ultimately show ?thesis
      using False Cons.prems
      by (auto simp: apath_simps intro: awalk_Cons_deg2_unique)
  qed
qed simp

lemma same_awalk_by_same_end:
  assumes V: "verts3 G \<subseteq> V" "V \<subseteq> pverts G"
    and walk: "apath u p v" "apath w q v" "last p = last q" "p \<noteq> []" "q \<noteq> []"
    and tail: "u \<in> V" "w \<in> V"
    and inner_verts: "set (inner_verts p) \<inter> V = {}"
      "set (inner_verts q) \<inter> V = {}"
  shows "p = q"
proof (cases "length p" "length q" rule: linorder_cases)
  { fix u v w p q
    assume walk: "apath u p v" "apath w q v" "last p = last q" "p \<noteq> []" "q \<noteq> []"
      and tail: "u \<in> V" "w \<in> V"
      and inner_verts: "set (inner_verts p) \<inter> V = {}"
        "set (inner_verts q) \<inter> V = {}"
      and less: "length p < length q"

    def q1 \<equiv> "take (length q - length p) q" and q2 \<equiv> "drop (length q - length p) q"
    with less have "q = q1 @ q2" "length p = length q2" "q1 \<noteq> []" by auto

    note walk(1)
    moreover
    have "apath (awlast w q1) q2 v" using `q = q1 @ q2` walk
      by (auto simp: apath_append_iff)
    moreover
    have "last p = last q2"
      using walk(3) `q = q1 @ q2` `length p = length q2` by (auto simp: last_append)
    moreover
    have "set (inner_verts p) \<inter> verts3 G = {}" "set (inner_verts q2) \<inter> verts3 G = {}"
      using inner_verts `q = q1 @ q2` V by (auto dest: in_set_inner_verts_appendI_r)
    ultimately
    have "p = q2" using `length p = length q2`
      by (rule same_awalk_by_length)
    then have "awlast w q1 = u"
      using walk unfolding `q = q1 @ q2` by (auto simp: apath_def dest: awalk_ends)
    moreover have "cas w q v" using walk by (auto simp: apath_def)
    ultimately have "u \<in> set (inner_verts q)"
      using `q1 \<noteq> []` `p \<noteq> []` `apath w q v` unfolding `q = q1 @ q2` `p = q2`
      by (auto simp: apath_def inner_verts_conv[of _ w] awalk_verts_conv' last_map butlast_append)
    with `u \<in> V` inner_verts(2) have "p = q" by auto }
  note less_rule = this
  { case less with walk tail inner_verts show ?thesis by (rule less_rule) }
  { case equal with assms show ?thesis by (intro same_awalk_by_length) auto }
  { case greater with walk tail inner_verts show ?thesis by (metis less_rule) }
qed

lemma same_awalk_by_common_arc:
  assumes V: "verts3 G \<subseteq> V" "V \<subseteq> pverts G"
  assumes walk: "apath u p v" "apath w q x"
  assumes iv_not_in_V: "set (inner_verts p) \<inter> V = {}" "set (inner_verts q) \<inter> V = {}"
  assumes ends_in_V: "{u,v,w,x} \<subseteq> V"
  assumes arcs: "e \<in> set p" "e \<in> set q"
  shows "p = q"
proof -
  from arcs obtain p1 p2 where p_decomp: "p = p1 @ e # p2" by (metis in_set_conv_decomp_first)
  from arcs obtain q1 q2 where q_decomp: "q = q1 @ e # q2" by (metis in_set_conv_decomp_first)

  { def p1' \<equiv> "p1 @ [e]" and q1' \<equiv> "q1 @ [e]"
    then have decomp: "p = p1' @ p2" "q = q1' @ q2"
      and "awlast u p1' = snd e" "awlast w q1' = snd e"
      using p_decomp q_decomp by (auto simp: awlast_append)
    then have "apath u p1' (snd e)" "apath w q1' (snd e)"
      using walk by (auto simp: apath_append_iff)
    moreover have "last p1' = last q1'" "p1' \<noteq> []" "q1' \<noteq> []" by (auto simp: p1'_def q1'_def)
    moreover
    have "u \<in> V" "w \<in> V" "set (inner_verts p1') \<inter> V = {}" "set (inner_verts q1') \<inter> V = {}"
      using ends_in_V iv_not_in_V unfolding decomp
      by (auto intro: in_set_inner_verts_appendI_l in_set_inner_verts_appendI_r)
    ultimately have "p1' = q1'" by (rule same_awalk_by_same_end[OF V]) }
  moreover
  { def p2' \<equiv> "rev_path (e # p2)" and q2' \<equiv> "rev_path (e # q2)"
    then have decomp: "p = p1 @ rev_path p2'" "q = q1 @ rev_path q2'"
      using p_decomp q_decomp by auto
    moreover
    have "awlast u p1 = fst e" "awlast w q1 = fst e"
      using p_decomp q_decomp walk by (auto simp: apath_def)
    ultimately
    have "apath v p2' (fst e)" "apath x q2' (fst e)"
      using walk by (auto simp: apath_append_iff)
    moreover have "last p2' = last q2'" "p2' \<noteq> []" "q2' \<noteq> []" by (auto simp: p2'_def q2'_def)
    moreover have "v \<in> V" "x \<in> V" using ends_in_V by auto
    moreover
    have "set (inner_verts (rev_path p2')) \<inter> V = {}" "set (inner_verts (rev_path q2')) \<inter> V = {}"
      using iv_not_in_V unfolding decomp
      by (auto intro: in_set_inner_verts_appendI_l in_set_inner_verts_appendI_r)
    then have "set (inner_verts p2') \<inter> V = {}" "set (inner_verts q2') \<inter> V = {}"
      using `apath v p2' (fst e)` `apath x q2' (fst e)`
      by (auto simp: inner_verts_rev_path apath_def)
    ultimately have "p2' = q2'" by (rule same_awalk_by_same_end[OF V]) }
  ultimately
  show "p = q" using p_decomp q_decomp by (auto simp: rev_path_eq)
qed

lemma same_gen_iapath_by_common_arc:
  assumes V: "verts3 G \<subseteq> V" "V \<subseteq> pverts G"
  assumes path: "gen_iapath V u p v" "gen_iapath V w q x"
  assumes arcs: "e \<in> set p" "e \<in> set q"
  shows "p = q"
proof -
  from path have awalk: "apath u p v" "apath w q x"
      and in_V: "set (inner_verts p) \<inter> V = {}" "set (inner_verts q) \<inter> V = {}" "{u,v,w,x} \<subseteq> V"
    by (auto simp: gen_iapath_def)
  from V awalk in_V arcs show ?thesis by (rule same_awalk_by_common_arc)
qed


end



subsection {* Slim graphs *}

text {*
  We define the notion of a slim graph. The idea is that for a slim graph @{term G}, @{term G}
  is a subdivision of @{term "contracted_graph G"}.
*}

context pair_pre_digraph begin

definition (in pair_pre_digraph) is_slim :: "'a set \<Rightarrow> bool" where
  "is_slim V \<equiv>
    (\<forall>v \<in> pverts G. v \<in> V \<or>
      in_degree G v \<le> 2 \<and> (\<exists>x p y. gen_iapath V x p y \<and> v \<in> set (awalk_verts x p))) \<and>
    (\<forall>e \<in> parcs G. \<exists>x p y. gen_iapath V x p y \<and> e \<in> set p) \<and>
    (\<forall>u v p q. (gen_iapath V u p v \<and> gen_iapath V u q v) \<longrightarrow> p = q) \<and>
    V \<subseteq> pverts G"

definition direct_arc :: "'a \<times> 'a \<Rightarrow> 'a \<times> 'a" where
  "direct_arc uv \<equiv> SOME e. {fst uv , snd uv} = {fst e, snd e}"

definition choose_iapath :: "'a \<Rightarrow> 'a \<Rightarrow> ('a \<times> 'a) awalk" where
  "choose_iapath u v \<equiv> (let
      chosen_path = (\<lambda>u v. SOME p. iapath u p v)
    in if direct_arc (u,v) = (u,v) then chosen_path u v else rev_path (chosen_path v u))"

(* XXX: Replace "parcs (contracted_graph G)" by its definition *)
definition slim_paths :: "('a \<times> ('a \<times> 'a) awalk \<times> 'a) set" where
  "slim_paths \<equiv> (\<lambda>e. (fst e, choose_iapath (fst e) (snd e), snd e)) ` parcs (contracted_graph G)"

definition slim_verts :: "'a set" where
  "slim_verts \<equiv> verts3 G \<union> (\<Union>(u,p,_) \<in> slim_paths. set (awalk_verts u p))"

definition slim_arcs :: "'a rel" where
  "slim_arcs \<equiv> \<Union>(_,p,_) \<in> slim_paths. set p"

text {* Computes a slim subgraph for an arbitrary @{term pair_digraph} *}
definition slim :: "'a pair_pre_digraph" where
  "slim \<equiv> \<lparr> pverts = slim_verts, parcs = slim_arcs \<rparr>" 

end

context pair_pseudo_graph begin

lemma choose_iapath:
  assumes "\<exists>p. iapath u p v"
  shows "iapath u (choose_iapath u v) v"
proof (cases "direct_arc (u,v) = (u,v)")
  def chosen \<equiv> "\<lambda>u v. SOME p. iapath u p v"
  { case True
    have "iapath u (chosen u v) v"
      unfolding chosen_def by (rule someI_ex) (rule assms)
    then show ?thesis using True by (simp add: choose_iapath_def chosen_def) }

  { case False
    from assms obtain p where "iapath u p v" by auto
    then have "iapath v (rev_path p) u"
      by (simp add: gen_iapath_rev_path)
    then have "iapath v (chosen v u) u"
      unfolding chosen_def by (rule someI)
    then show ?thesis using False
      by (simp add: choose_iapath_def chosen_def gen_iapath_rev_path) }
qed

lemma slim_simps: "pverts slim = slim_verts" "parcs slim = slim_arcs"
  by (auto simp: slim_def)

lemma slim_paths_in_G:
  assumes "(u,p,v) \<in> slim_paths"
  shows "iapath u p v"
using assms choose_iapath
by (fastforce simp: gen_contr_graph_def slim_paths_def)

lemma verts_slim_in_G: "pverts slim \<subseteq> pverts G"
  by (auto simp: slim_simps slim_verts_def verts3_def gen_iapath_def apath_def
    dest!: slim_paths_in_G elim!: awalkE)

lemma verts3_in_slim_G[simp]:
  assumes "x \<in> verts3 G" shows "x \<in> pverts slim"
using assms by (auto simp: slim_simps slim_verts_def)

lemma arcs_slim_in_G: "parcs slim \<subseteq> parcs G"
  by (auto simp: slim_simps slim_arcs_def gen_iapath_def apath_def
      dest!: slim_paths_in_G elim!: awalkE)

lemma slim_paths_in_slimG:
  assumes "(u,p,v) \<in> slim_paths"
  shows "pre_digraph.gen_iapath slim (verts3 G) u p v \<and> p \<noteq> []"
proof -
  from assms have arcs: "\<And>e. e \<in> set p \<Longrightarrow> e \<in> parcs slim"
    by (auto simp: slim_simps slim_arcs_def)
  moreover
  from assms have "gen_iapath (verts3 G) u p v" and "p \<noteq> []"
    using slim_paths_in_G by (auto simp: gen_iapath_def)
  ultimately show ?thesis
    by (auto simp: pre_digraph.gen_iapath_def pre_digraph.apath_def pre_digraph.awalk_def
      inner_verts_with_proj_def)
qed

lemma direct_arc_swapped:
  "direct_arc (u,v) = direct_arc (v,u)"
by (simp add: direct_arc_def insert_commute)

lemma direct_arc_chooses:
  fixes u v :: 'a shows "direct_arc (u,v) = (u,v) \<or> direct_arc (u,v) = (v,u)"
proof -
  def f \<equiv> "(\<lambda>X. SOME e. X = {fst e,snd e}) :: 'a set \<Rightarrow> 'a \<times> 'a"

  have "\<exists>p::'a \<times> 'a. {u,v} = {fst p, snd p}" by (rule exI[where x="(u,v)"]) auto
  then have "{u,v} = {fst (f {u,v}), snd (f {u,v})}"
    unfolding f_def Eps_split by (rule someI_ex)
  then have "f {u,v} = (u,v) \<or> f {u,v} = (v,u)"
    by (auto simp: doubleton_eq_iff prod_eq_iff)
  then show ?thesis by (auto simp: direct_arc_def f_def)
qed

lemma rev_path_choose_iapath:
  assumes "u \<noteq> v"
  shows "rev_path (choose_iapath u v) = choose_iapath v u"
  using assms direct_arc_chooses[of u v]
  by (auto simp: choose_iapath_def direct_arc_swapped)

lemma pair_pseudo_graph_slim: "pair_pseudo_graph slim"
proof
  show "finite (pverts slim)"
    using verts_slim_in_G finite_verts by (rule finite_subset)
  show "finite (parcs slim)"
    using arcs_slim_in_G finite_arcs by (rule finite_subset)
next
  fix e assume A: "e \<in> parcs slim"
  then obtain u p v where "(u,p,v) \<in> slim_paths" "e \<in> set p" by (auto simp: slim_simps slim_arcs_def)
  with A have "iapath u p v" by (auto simp: dest: slim_paths_in_G)
  with `e \<in> set p` have "fst e \<in> set (awalk_verts u p)" "snd e \<in> set (awalk_verts u p)"
    by (auto simp: set_awalk_verts gen_iapath_def apath_def)
  moreover  
  from `_ \<in> slim_paths` have "set (awalk_verts u p) \<subseteq> pverts slim"
    by (auto simp: slim_simps slim_verts_def)
  ultimately
  show "fst e \<in> pverts slim" "snd e \<in> pverts slim" by auto
next
  { fix e assume "e \<in> parcs slim"
    then obtain u p v where "(u,p,v) \<in> slim_paths" and "e \<in> set p"
      by (auto simp: slim_simps slim_arcs_def)
    moreover
    then have "iapath u p v" and "p \<noteq> []" by (auto dest: slim_paths_in_G)
    then have "iapath v (rev_path p) u" and "rev_path p \<noteq> []"
      by (auto simp: gen_iapath_rev_path)
    then have "(v,u) \<in> parcs (contracted_graph G)"
      by (auto simp: gen_contr_graph_def)
    moreover
    from `iapath u p v` have "u \<noteq> v"
      by (auto simp: gen_iapath_def dest: apath_nonempty_ends)
    ultimately
    have "(v, rev_path p, u) \<in> slim_paths"
      by (auto simp: slim_paths_def rev_path_choose_iapath intro: rev_image_eqI)
    moreover
    from `e \<in> set p` have "(snd e, fst e) \<in> set (rev_path p)"
      by (induct p) auto
    ultimately have "(snd e, fst e) \<in> parcs slim"
     by (auto simp: slim_simps slim_arcs_def) }
  then show "symmetric slim"
    unfolding symmetric_conv by simp (metis fst_conv snd_conv)
qed

lemma subgraph_slim: "subgraph slim G"
proof (rule subgraphI)
  interpret H: pair_pseudo_graph "slim"
    by (rule pair_pseudo_graph_slim) intro_locales

  show "verts slim \<subseteq> verts G" "arcs slim \<subseteq> arcs G"
    by (auto simp: verts_slim_in_G arcs_slim_in_G)
  show "compatible G slim" ..
  show "wf_digraph slim" "wf_digraph G"
    by unfold_locales
qed

lemma giapath_if_slim_giapath:
  assumes "pre_digraph.gen_iapath slim (verts3 G) u p v"
  shows "gen_iapath (verts3 G) u p v"
using assms verts_slim_in_G arcs_slim_in_G
by (auto simp: pre_digraph.gen_iapath_def pre_digraph.apath_def pre_digraph.awalk_def
  inner_verts_with_proj_def)

lemma slim_giapath_if_giapath:
assumes "gen_iapath (verts3 G) u p v"
  shows "\<exists>p. pre_digraph.gen_iapath slim (verts3 G) u p v" (is "\<exists>p. ?P p")
proof
  from assms have choose_arcs: "\<And>e. e \<in> set (choose_iapath u v) \<Longrightarrow> e \<in> parcs slim"
    by (fastforce simp: slim_simps slim_arcs_def slim_paths_def gen_contr_graph_def)
  moreover
  from assms have choose: "iapath u (choose_iapath u v) v"
    by (intro choose_iapath) (auto simp: gen_iapath_def)
  ultimately show "?P (choose_iapath u v)"
    by (auto simp: pre_digraph.gen_iapath_def pre_digraph.apath_def pre_digraph.awalk_def
      inner_verts_with_proj_def)
qed

lemma contr_graph_slim_eq:
   "gen_contr_graph slim (verts3 G) = contracted_graph G"
  using giapath_if_slim_giapath slim_giapath_if_giapath by (fastforce simp: gen_contr_graph_def)

lemma verts3_slim_in_verts3:
  assumes "v \<in> verts3 slim" shows "v \<in> verts3 G"
proof -
  from assms have "2 < in_degree slim v" by (auto simp: verts3_def)
  also have "\<dots> \<le> in_degree G v" using subgraph_slim by (rule subgraph_in_degree)
  finally show ?thesis using assms subgraph_slim by (fastforce simp: verts3_def)
qed

lemma slim_is_slim:
  "pair_pre_digraph.is_slim slim (verts3 G)"
proof (unfold pair_pre_digraph.is_slim_def, safe)
  interpret S: pair_pseudo_graph slim by (rule pair_pseudo_graph_slim)
  { fix v assume "v \<in> pverts slim" "v \<notin> verts3 G"
    then have "in_degree G v \<le> 2"
      using verts_slim_in_G by (auto simp: verts3_def)
    then show "in_degree slim v \<le> 2"
      using subgraph_in_degree[OF subgraph_slim, of v] by fastforce
  next
    fix w assume "w \<in> pverts slim" "w \<notin> verts3 G"
    then obtain u p v where upv: "(u, p, v) \<in> slim_paths" "w \<in> set (awalk_verts u p)"
      by (auto simp: slim_simps slim_verts_def)
    moreover
    then have "S.gen_iapath (verts3 G) u p v"
      using slim_paths_in_slimG by auto
    ultimately
    show "\<exists>x q y. S.gen_iapath (verts3 G) x q y
      \<and> w \<in> set (awalk_verts x q)"
      by auto
  next
    fix u v assume "(u,v) \<in> parcs slim"
    then obtain x p y where "(x, p, y) \<in> slim_paths" "(u,v) \<in> set p"
      by (auto simp: slim_simps slim_arcs_def)
    then have "S.gen_iapath (verts3 G) x p y \<and> (u,v) \<in> set p"
      using slim_paths_in_slimG by auto
    then show "\<exists>x p y. S.gen_iapath (verts3 G) x p y \<and> (u,v) \<in> set p"
      by blast
  next
    fix u v p q
    assume paths: "S.gen_iapath (verts3 G) u p v"
          "S.gen_iapath (verts3 G) u q v"

    have V: "verts3 slim \<subseteq> verts3 G" "verts3 G \<subseteq> pverts slim"
      by (auto simp: verts3_slim_in_verts3)
  
    have "p = [] \<or> q = [] \<Longrightarrow> p = q" using paths
      by (auto simp: S.gen_iapath_def dest: S.apath_ends)
    moreover
    { assume "p \<noteq> []" "q \<noteq> []"
      { fix u p v assume "p \<noteq> []" and path: "S.gen_iapath (verts3 G) u p v"
        then obtain e where "e \<in> set p" by (metis last_in_set)
        then have "e \<in> parcs slim" using path by (auto simp: S.gen_iapath_def S.apath_def)
        then obtain x r y where "(x,r,y) \<in> slim_paths" "e \<in> set r"
          by (auto simp: slim_simps slim_arcs_def)
        then have "S.gen_iapath (verts3 G) x r y" by (metis slim_paths_in_slimG)
        with `e \<in> set r` `e \<in> set p` path have "p = r"
          by (auto intro: S.same_gen_iapath_by_common_arc[OF V])
        then have "x = u" "y = v" using path `S.gen_iapath (verts3 G) x r y` `p = r` `p \<noteq> []`
          by (auto simp: S.gen_iapath_def S.apath_def dest: S.awalk_ends)
        then have "(u,p,v) \<in> slim_paths" using `p = r` `(x,r,y) \<in> slim_paths` by simp }
      note obt = this
      from `p \<noteq> []` `q \<noteq> []` paths have "(u,p,v) \<in> slim_paths" "(u,q,v) \<in> slim_paths"
        by (auto intro: obt)
      then have "p = q" by (auto simp: slim_paths_def)
    }
    ultimately show "p = q" by metis
  }
qed auto

lemma
  assumes p: "gen_iapath (pverts G) u p v"
  shows gen_iapath_triv_path: "p = [(u,v)]"
    and gen_iapath_triv_arc: "(u,v) \<in> parcs G"
proof -
  have "set (inner_verts p) = {}"
  proof -
    have *: "\<And>A B :: 'a set. \<lbrakk>A \<subseteq> B; A \<inter> B = {}\<rbrakk> \<Longrightarrow> A = {}" by blast
    have "set (inner_verts p) = set (awalk_verts u p) - {u, v}"
      using p by (simp add: set_inner_verts gen_iapath_def)
    also have "\<dots> \<subseteq> pverts G"
      using p unfolding gen_iapath_def apath_def awalk_conv by auto
    finally show ?thesis
      using p by (rule_tac *) (auto simp: gen_iapath_def)
  qed
  then have "inner_verts p = []" by simp
  then show "p = [(u,v)]" using p
    by (cases p) (auto simp: gen_iapath_def apath_def inner_verts_def split: split_if_asm)
  then show "(u,v) \<in> parcs G"
    using p by (auto simp: gen_iapath_def apath_def)
qed

lemma gen_contr_triv:
  assumes "is_slim V" "pverts G = V" shows "gen_contr_graph G V = G"
proof -
  let ?gcg = "gen_contr_graph G V"

  from assms have "pverts ?gcg = pverts G"
    by (auto simp: gen_contr_graph_def is_slim_def)
  moreover
  have "parcs ?gcg = parcs G"
  proof (rule set_eqI, safe)
    fix u v assume "(u,v) \<in> parcs ?gcg"
    then obtain p where "gen_iapath V u p v"
      by (auto simp: gen_contr_graph_def)
    then show "(u,v) \<in> parcs G"
      using gen_iapath_triv_arc `pverts G = V` by auto
  next
    fix u v assume "(u,v) \<in> parcs G"
    with assms obtain x p y where path: "gen_iapath V x p y" "(u,v) \<in> set p"
      by (auto simp: is_slim_def)                              
    with `pverts G = V` have "p = [(x,y)]" by (intro gen_iapath_triv_path) auto
    then show "(u,v) \<in> parcs ?gcg"
      using path by (auto simp: gen_contr_graph_def)
  qed
  ultimately
  show "?gcg = G" by auto
qed

end



subsection {* Contraction Preserves Kuratowski-Subgraph-Property *}

lemma (in pair_pseudo_graph) in_degree_contr:
  assumes "v \<in> V" and V: "verts3 G \<subseteq> V" "V \<subseteq> verts G"
  shows "in_degree (gen_contr_graph G V) v \<le> in_degree G v"
proof -
  have fin: "finite {(u, p). gen_iapath V u p v}"
  proof -
    have "{(u, p). gen_iapath V u p v} \<subseteq> (\<lambda>(u,p,_). (u,p)) ` {(u,p,v). apath u p v}"
      by (force simp: gen_iapath_def)
    with apaths_finite_triple show ?thesis by (rule finite_surj)
  qed

  have io_snd: "inj_on snd {(u,p). gen_iapath V u p v}"
    by (rule inj_onI) (auto simp: gen_iapath_def apath_def dest: awalk_ends)

  have io_last: "inj_on last {p. \<exists>u. gen_iapath V u p v}"
  proof (rule inj_onI, safe)
    fix u1 u2 p1 p2
    assume A: "last p1 = last p2" and B: "gen_iapath V u1 p1 v" "gen_iapath V u2 p2 v"
    from B have "last p1 \<in> set p1" "last p2 \<in> set p2" by (auto simp: gen_iapath_def)
    with A have "last p1 \<in> set p1" "last p1 \<in> set p2" by simp_all
    with V[simplified] B show "p1 = p2" by (rule same_gen_iapath_by_common_arc)
  qed

  have "in_degree (gen_contr_graph G V) v = card ((\<lambda>(u,_). (u,v)) ` {(u,p). gen_iapath V u p v})"
  proof -
    have "in_arcs (gen_contr_graph G V) v = (\<lambda>(u,_). (u,v)) ` {(u,p). gen_iapath V u p v}"
      by (auto simp: gen_contr_graph_def)
    then show ?thesis unfolding in_degree_def by simp
  qed
  also have "\<dots> \<le> card {(u,p). gen_iapath V u p v}"
    using fin by (rule card_image_le)
  also have "\<dots> = card (snd ` {(u,p). gen_iapath V u p v})"
    using io_snd by (rule card_image[symmetric])
  also have "snd ` {(u,p). gen_iapath V u p v} = {p. \<exists>u. gen_iapath V u p v}"
    by (auto intro: rev_image_eqI)
  also have "card \<dots> = card (last ` ...)"
    using io_last by (rule card_image[symmetric])
  also have "\<dots> \<le> in_degree G v"
    unfolding in_degree_def
  proof (rule card_mono)
    show "last ` {p. \<exists>u. gen_iapath V u p v} \<subseteq> in_arcs G v"
    proof -
      have "\<And>u p. awalk u p v \<Longrightarrow> p \<noteq> [] \<Longrightarrow> last p \<in> parcs G"
        by (auto simp: awalk_def)
      moreover 
      { fix u p assume "awalk u p v" "p \<noteq> []"
        then have "snd (last p) = v" by (induct p arbitrary: u) (auto simp: awalk_simps) }
      ultimately
      show ?thesis unfolding in_arcs_def by (auto simp: gen_iapath_def apath_def)
    qed
  qed auto
  finally show ?thesis .
qed


lemma (in pair_graph) contracted_no_degree2_simp:
  assumes subd: "subdivision G H"
  assumes two_less_deg2: "verts3 G = pverts G"
  shows "contracted_graph H = G"
using subd
proof (induct rule: subdivision.induct)
  case base

  { fix e assume "e \<in> parcs G"
    then have "gen_iapath (pverts G) (fst e) [(fst e, snd e)] (snd e)" "e \<in> set [(fst e, snd e)]"
      using no_loops[of "(fst e, snd e)"] by (auto simp: gen_iapath_def apath_simps )
    then have "\<exists>u p v. gen_iapath (pverts G) u p v \<and> e \<in> set p" by blast }
  moreover
  { fix u p v assume "gen_iapath (pverts G) u p v"
    from `gen_iapath _ u p v` have "p = [(u,v)]"
      unfolding gen_iapath_def apath_def
      by safe (cases p, case_tac [2] list, auto simp: awalk_simps inner_verts_def) }
  ultimately have "is_slim (verts3 G)" unfolding is_slim_def two_less_deg2 by blast
  then show ?case by (simp add: gen_contr_triv two_less_deg2)
next
  case (divide e w H)
  let ?sH = "subdivide H e w"
  from `subdivision G H` interpret H: pair_graph H by (auto intro: pair_graph_subdivision)
  from divide(1,2) interpret S: pair_graph ?sH
    by (rule H.pair_graph_subdivide)
  obtain u v where e_conv:"e = (u,v)" by (cases e) auto
  have "contracted_graph ?sH = contracted_graph H"
  proof -
    have V_cond: "verts3 H \<subseteq> pverts H" by (auto simp: verts3_def)
    have "verts3 H = verts3 ?sH"
      using divide by (simp add: H.verts3_subdivide)
    then have v: "pverts (contracted_graph ?sH) = pverts (contracted_graph H)"
      by (auto simp: gen_contr_graph_def)
    moreover
    then have "parcs (contracted_graph ?sH) = parcs (contracted_graph H)"
      unfolding gen_contr_graph_def
      by (auto dest: H.gen_iapath_co_path[OF divide(1,2) V_cond]
          H.gen_iapath_sd_path[OF divide(1,2) V_cond])
    ultimately show ?thesis by auto
  qed
  then show ?case using divide by simp
qed

lemma verts3_K33:
  assumes "K\<^bsub>3,3\<^esub> G"
  shows "verts3 G = verts G"
proof -
  { fix v assume "v \<in> pverts G"
    from assms obtain U V where cards: "card U = 3" "card V=3"
      and UV: "U \<inter> V = {}" "pverts G = U \<union> V" "parcs G = U \<times> V \<union> V \<times> U"
      unfolding complete_bipartite_digraph_def by blast
    have "2 < in_degree G v"
    proof (cases "v \<in> U")
      case True
      then have "in_arcs G v = V \<times> {v}" using UV by fastforce
      then show ?thesis using cards by (auto simp: card_cartesian_product in_degree_def)
    next
      case False
      then have "in_arcs G v = U \<times> {v}" using `v \<in> _` UV by fastforce
      then show ?thesis using cards by (auto simp: card_cartesian_product in_degree_def)
    qed }
  then show ?thesis by (auto simp: verts3_def)
qed

lemma verts3_K5:
  assumes "K\<^bsub>5\<^esub> G"
  shows "verts3 G = verts G"
proof -
  interpret pgG: pair_graph G using assms by (rule pair_graphI_complete)
  { fix v assume "v \<in> pverts G"
    have "2 < (4 :: nat)" by simp
    also have "4 = card (pverts G - {v})"
      using assms `v \<in> pverts G` unfolding complete_digraph_def by auto
    also have "pverts G - {v} = {u \<in> pverts G. u \<noteq> v}"
      by auto
    also have "card \<dots> = card ({u \<in> pverts G. u \<noteq> v} \<times> {v})" (is "_ = card ?A")
      by auto
    also have "?A = in_arcs G v"
      using assms `v \<in> pverts G` unfolding complete_digraph_def by safe auto
    also have "card \<dots> = in_degree G v"
      unfolding in_degree_def ..
    finally have "2 < in_degree G v" . }
  then show ?thesis unfolding verts3_def by auto
qed

lemma K33_contractedI:
  assumes subd: "subdivision G H"
  assumes k33: "K\<^bsub>3,3\<^esub> G"
  shows "K\<^bsub>3,3\<^esub> (contracted_graph H)"
proof -
  interpret pgG: pair_graph G using k33 by (rule pair_graphI_complete_bipartite)
  show ?thesis
    using assms by (auto simp add: pgG.contracted_no_degree2_simp verts3_K33)
qed

lemma K5_contractedI:
  assumes subd: "subdivision G H"
  assumes k5: "K\<^bsub>5\<^esub> G"
  shows "K\<^bsub>5\<^esub> (contracted_graph H)"
proof -
  interpret pgG: pair_graph G using k5 by (rule pair_graphI_complete)
  show ?thesis
    using assms by (auto simp add: pgG.contracted_no_degree2_simp verts3_K5)
qed



subsection {* Final proof *}

context pair_pseudo_graph begin


lemma gcg_subdivide_eq:
  assumes mem: "e \<in> parcs G" "w \<notin> pverts G"
  assumes V: "V \<subseteq> pverts G"
  shows "gen_contr_graph (subdivide G e w) V = gen_contr_graph G V"
proof -
  interpret sdG: pair_pseudo_graph "subdivide G e w"
    using mem by (rule pair_pseudo_graph_subdivide)
  { fix u p v assume "sdG.gen_iapath V u p v"
    have "gen_iapath V u (co_path e w p) v"
      using mem V `sdG.gen_iapath V u p v` by (rule gen_iapath_co_path)
    then have "\<exists>p. gen_iapath V u p v" ..
  } note A = this
  moreover
  { fix u p v assume "gen_iapath V u p v"
    have "sdG.gen_iapath V u (sd_path e w p) v"
      using mem V `gen_iapath V u p v` by (rule gen_iapath_sd_path)
    then have "\<exists>p. sdG.gen_iapath V u p v" ..
  } note B = this
  ultimately show ?thesis using assms by (auto simp: gen_contr_graph_def)
qed

lemma co_path_append:
  assumes "[last p1, hd p2] \<notin> {[(fst e,w),(w,snd e)], [(snd e,w),(w,fst e)]}"
  shows "co_path e w (p1 @ p2) = co_path e w p1 @ co_path e w p2"
using assms
proof (induct p1 rule: co_path_induct)
  case single then show ?case by (cases p2) auto
next
  case (co e1 e2 es) then show ?case by (cases es) auto
next
  case (corev e1 e2 es) then show ?case by (cases es) auto
qed auto

lemma exists_co_path_decomp1:
  assumes mem: "e \<in> parcs G" "w \<notin> pverts G"
  assumes p: "pre_digraph.apath (subdivide G e w) u p v" "(fst e, w) \<in> set p" "w \<noteq> v"
  shows "\<exists>p1 p2. p = p1 @ (fst e, w) # (w, snd e) # p2"
proof -
  let ?sdG = "subdivide G e w"
  interpret sdG: pair_pseudo_graph ?sdG
    using mem by (rule pair_pseudo_graph_subdivide)
  obtain p1 p2 z where p_decomp: "p = p1 @ (fst e, w) # (w, z) # p2" "fst e \<noteq> z" "w \<noteq> z"
    by atomize_elim (rule sdG.apath_succ_decomp[OF p])
  then have "(fst e,w) \<in> parcs ?sdG" "(w, z) \<in> parcs ?sdG"
    using p by (auto simp: sdG.apath_def)
  with `fst e \<noteq> z` have "z = snd e"
    using mem by (cases e) (auto simp: wellformed')
  with p_decomp show ?thesis by fast
qed

lemma is_slim_if_subdivide:
  assumes "pair_pre_digraph.is_slim (subdivide G e w) V"
  assumes mem1: "e \<in> parcs G" "w \<notin> pverts G" and mem2: "w \<notin> V"
  shows "is_slim V"
proof -
  let ?sdG = "subdivide G e w"
  interpret sdG: pair_pseudo_graph "subdivide G e w"
    using mem1 by (rule pair_pseudo_graph_subdivide)
  obtain u v where "e = (u,v)" by (cases e) auto
  with mem1 have "u \<in> pverts G" "v \<in> pverts G" by (auto simp: wellformed')
  with mem1  have "u \<noteq> w" "v \<noteq> w" by auto

  let ?w_parcs = "{(u,w), (v,w), (w,u), (w, v)}"
  have sdg_new_parcs: "?w_parcs \<subseteq> parcs ?sdG"
    using `e = (u,v)` by auto
  have sdg_no_parcs: "(u,v) \<notin> parcs ?sdG" "(v,u) \<notin> parcs ?sdG"
    using `e = (u,v)` `u \<noteq> w` `v \<noteq> w` by auto

  { fix z assume A: "z \<in> pverts G"
    have "in_degree ?sdG z = in_degree G z"
    proof -
      { assume "z \<noteq> u" "z \<noteq> v"
        then have "in_arcs ?sdG z = in_arcs G z"
          using `e = (u,v)` mem1 A by auto
        then have "in_degree ?sdG z = in_degree G z" by (simp add: in_degree_def) }
      moreover
      { assume "z = u"
        then have "in_arcs G z = in_arcs ?sdG z \<union> {(v,u)} - {(w,u)}"
          using `e = (u,v)` mem1 by (auto simp: intro: arcs_symmetric wellformed')
        moreover
        have "card (in_arcs ?sdG z \<union> {(v,u)} - {(w,u)}) = card (in_arcs ?sdG z)"
          using sdg_new_parcs sdg_no_parcs `z = u` by (auto simp: in_arcs_def)
        ultimately have "in_degree ?sdG z= in_degree G z" by (simp add: in_degree_def) }
      moreover
      { assume "z = v"
        then have "in_arcs G z = in_arcs ?sdG z \<union> {(u,v)} - {(w,v)}"
          using `e = (u,v)` mem1 A by (auto simp: wellformed')
        moreover
        have "card (in_arcs ?sdG z \<union> {(u,v)} - {(w,v)}) = card (in_arcs ?sdG z)"
          using sdg_new_parcs sdg_no_parcs `z = v` by (auto simp: in_arcs_def)
        ultimately have "in_degree ?sdG z= in_degree G z" by (simp add: in_degree_def) }
      ultimately show ?thesis by metis
    qed }
  note in_degree_same = this

  have V_G: "V \<subseteq> pverts G" "verts3 G \<subseteq> V"
  proof -
    have "V \<subseteq> pverts ?sdG" "pverts ?sdG = pverts G \<union> {w}" "verts3 ?sdG \<subseteq> V" "verts3 G \<subseteq> verts3 ?sdG"
      using `sdG.is_slim V` `e = (u,v)` in_degree_same mem1
      unfolding sdG.is_slim_def verts3_def
      by (fast, simp, fastforce, force)
    then show "V \<subseteq> pverts G" "verts3 G \<subseteq> V" using `w \<notin> V` by auto
  qed

  have pverts: "\<forall>v\<in>pverts G. v \<in> V \<or> in_degree G v \<le> 2 \<and> (\<exists>x p y. gen_iapath V x p y \<and> v \<in> set (awalk_verts x p))"
  proof -
    { fix z assume A: "z \<in> pverts G" "z \<notin> V"
      have "z \<in> pverts ?sdG" using `e = (u,v)` A mem1 by auto
      then have "in_degree ?sdG z \<le> 2"
        using `sdG.is_slim V` A by (auto simp: sdG.is_slim_def)
      with in_degree_same[OF `z \<in> pverts G`] have idg: "in_degree G z \<le> 2" by auto

      from A have "z \<in> pverts ?sdG" "z \<notin> V" using `e = (u,v)` mem1 by auto
      then obtain x' q y' where "sdG.gen_iapath V x' q y'" "z \<in> set (sdG.awalk_verts x' q)"
        using `sdG.is_slim V` unfolding sdG.is_slim_def by metis
      then have "gen_iapath V x' (co_path e w q) y'" "z \<in> set (awalk_verts x' (co_path e w q))"
        using A mem1 V_G by (auto simp: set_awalk_verts_co_path' intro: gen_iapath_co_path)
      with idg have "in_degree G z \<le> 2 \<and> (\<exists>x p y. gen_iapath V x p y \<and> z \<in> set (awalk_verts x p))"
        by metis }
    then show ?thesis by auto
  qed

  have parcs: "\<forall>e\<in>parcs G. \<exists>x p y. gen_iapath V x p y \<and> e \<in> set p"
  proof
    fix e' assume "e' \<in> parcs G"
    show "\<exists>x p y. gen_iapath V x p y \<and> e' \<in> set p"
    proof (cases "e' \<in> parcs ?sdG")
      case True
      then obtain x p y where "sdG.gen_iapath V x p y" "e' \<in> set p"
        using `sdG.is_slim V` by (auto simp: sdG.is_slim_def)
      with `e \<in> parcs G` `w \<notin> pverts G` V_G have "gen_iapath V x (co_path e w p) y"
        by (auto intro: gen_iapath_co_path)

      from `e' \<in> parcs G` have "e' \<notin> ?w_parcs" using mem1 by (auto simp: wellformed')
      with `e' \<in> set p` have "e' \<in> set (co_path e w p)"
        by (induct p rule: co_path_induct) (force simp: `e = (u,v)`)+
      then show "\<exists>x p y. gen_iapath V x p y \<and> e' \<in> set p "
        using `gen_iapath V x (co_path e w p) y`  by fast
    next
      assume "e' \<notin> parcs ?sdG"
      def a \<equiv> "fst e'" and b \<equiv> "snd e'"
      then have "e' = (a,b)" and ab: "(a,b) = (u,v) \<or> (a,b) = (v,u)"
        using `e' \<in> parcs G` `e' \<notin> parcs ?sdG` `e = (u,v)` mem1 by auto
      obtain x p y where "sdG.gen_iapath V x p y" "(a,w) \<in> set p"
        using `sdG.is_slim V` sdg_new_parcs ab by (auto simp: sdG.is_slim_def)
      with `e \<in> parcs G` `w \<notin> pverts G` V_G have "gen_iapath V x (co_path e w p) y"
        by (auto intro: gen_iapath_co_path)

      have "(a,b) \<in> parcs G" "subdivide G (a,b) w = subdivide G e w"
        using mem1 `e = (u,v)` `e' = (a,b)` ab
        by (auto intro: arcs_symmetric simp: subdivide.simps)
      then have "pre_digraph.apath (subdivide G (a,b) w) x p y" "w \<noteq> y"
        using mem2 `sdG.gen_iapath V x p y` by (auto simp: sdG.gen_iapath_def)
      then obtain p1 p2 where "p = p1 @ (a,w) # (w,b) # p2"
        using exists_co_path_decomp1 `(a,b) \<in> parcs G` `w \<notin> pverts G` `(a,w) \<in> set p` `w \<noteq> y`
        by atomize_elim auto
      moreover
      then have "co_path e w ((a,w) # (w,b) # p2) = (a,b) # co_path e w p2"
        unfolding `e = (u,v)` using ab by auto
      ultimately
      have "(a,b) \<in> set (co_path e w p)"
        unfolding `e = (u,v)` using ab `u \<noteq> w` `v \<noteq> w`
        by (induct p rule: co_path_induct) (auto simp: co_path_append)
      then show ?thesis
        using `gen_iapath V x (co_path e w p) y` `e' = (a,b)` by fast
    qed
  qed

  have unique: "\<forall>u v p q. (gen_iapath V u p v \<and> gen_iapath V u q v) \<longrightarrow> p = q"
  proof safe
    fix x y p q assume A: "gen_iapath V x p y" "gen_iapath V x q y"
    then have "set p \<subseteq> parcs G" "set q \<subseteq> parcs G"
      by (auto simp: gen_iapath_def apath_def)
    then have w_p: "(u,w) \<notin> set p" "(v,w) \<notin> set p" and w_q: "(u,w) \<notin> set q" "(v,w) \<notin> set q"
      using mem1 by (auto simp: wellformed')

    from A have "sdG.gen_iapath V x (sd_path e w p) y" "sdG.gen_iapath V x (sd_path e w q) y"
      using mem1 V_G by (auto intro: gen_iapath_sd_path)
    then have "sd_path e w p = sd_path e w q"
      using `sdG.is_slim V` unfolding sdG.is_slim_def by metis
    then have "co_path e w (sd_path e w p) = co_path e w (sd_path e w q)" by simp
    then show "p = q" using w_p w_q `e = (u,v)` by (simp add: co_sd_id)
  qed

  from pverts parcs V_G unique show ?thesis by (auto simp: is_slim_def)
qed


lemma subdivision_gen_contr:
  assumes "is_slim V"
  shows "subdivision (gen_contr_graph G V) G"
using assms pair_pseudo_graph
proof (induct "card (pverts G - V)" arbitrary: G)
  case 0
  interpret G: pair_pseudo_graph G by fact
  from 0 show ?case by (auto intro: subdivision.intros simp: G.gen_contr_triv G.is_slim_def)
next
  case (Suc n)
  interpret G: pair_pseudo_graph G by fact

  from `Suc n = card (pverts G - V)`
  have "pverts G - V \<noteq> {}"
    by (metis Nat.diff_le_self Suc_n_not_le_n card_Diff_subset_Int diff_Suc_Suc empty_Diff finite.emptyI inf_bot_left)
  then obtain w where "w \<in> pverts G - V" by auto
  then obtain x q y where q: "G.gen_iapath V x q y" "w \<in> set (G.awalk_verts x q)" "in_degree G w \<le> 2"
    using `G.is_slim V` by (auto simp: G.is_slim_def)
  then have "w \<noteq> x" "w \<noteq> y" "w \<notin> V" using `w \<in> pverts G - V` by (auto simp: G.gen_iapath_def)
  then obtain e where "e \<in> set q" "snd e = w"
    using `w \<in> pverts G - V` q
    unfolding G.gen_iapath_def G.apath_def G.awalk_conv
    by (auto simp: G.awalk_verts_conv')
  moreover def u \<equiv> "fst e"
  ultimately obtain q1 q2 v where q_decomp: "q = q1 @ (u, w) # (w, v) # q2" "u \<noteq> v" "w \<noteq> v"
    using q `w \<noteq> y` unfolding G.gen_iapath_def by atomize_elim (rule G.apath_succ_decomp, auto)
  with q have qi_walks: "G.awalk x q1 u" "G.awalk v q2 y"
    by (auto simp: G.gen_iapath_def G.apath_def G.awalk_Cons_iff)

  from q q_decomp have uvw_arcs1: "(u,w) \<in> parcs G" "(w,v) \<in> parcs G"
    by (auto simp: G.gen_iapath_def G.apath_def)
  then have uvw_arcs2: "(w,u) \<in> parcs G" "(v,w) \<in> parcs G"
    by (blast intro: G.arcs_symmetric)+

  have "u \<noteq> w" "v \<noteq> w" using q_decomp q
    by (auto simp: G.gen_iapath_def G.apath_append_iff G.apath_simps)

  have in_arcs: "in_arcs G w = {(u,w), (v,w)}"
  proof -
    have "{(u,w), (v,w)} \<subseteq> in_arcs G w"
      using uvw_arcs1 uvw_arcs2 by (auto simp: )
    moreover note `in_degree G w \<le> 2`
    moreover have "card {(u,w), (v,w)} = 2" using `u \<noteq> v` by auto
    ultimately
    show ?thesis by - (rule card_seteq[symmetric], auto simp: in_degree_def)
  qed
  have out_arcs: "out_arcs G w \<subseteq> {(w,u), (w,v)}" (is "?L \<subseteq> ?R")
  proof
    fix e assume "e \<in> out_arcs G w"
    then have "(snd e, fst e) \<in> in_arcs G w"
      by (auto intro: G.arcs_symmetric)
    then show "e \<in> {(w, u), (w, v)}" using in_arcs by auto
  qed

  have "(u,v) \<notin> parcs G"
  proof
    assume "(u,v) \<in> parcs G"
    have "G.gen_iapath V x (q1 @ (u,v) # q2) y"
    proof -
      have awalk': "G.awalk x (q1 @ (u,v) # q2) y"
        using qi_walks `(u,v) \<in> parcs G`
        by (auto simp: G.awalk_simps)

      have "G.awalk x q y" using `G.gen_iapath V x q y` by (auto simp: G.gen_iapath_def G.apath_def)

      have "distinct (G.awalk_verts x (q1 @ (u,v) # q2))"
        using awalk' `G.gen_iapath V x q y` unfolding q_decomp 
        by (auto simp: G.gen_iapath_def G.apath_def G.awalk_verts_append)
      moreover
      have "set (G.inner_verts (q1 @ (u,v) # q2)) \<subseteq> set (G.inner_verts q)"
        using awalk' `G.awalk x q y` unfolding q_decomp
        by (auto simp: butlast_append G.inner_verts_conv[of _ x] G.awalk_verts_append
          intro: in_set_butlast_appendI)
      then have "set (G.inner_verts (q1 @ (u,v) # q2)) \<inter> V = {}"
        using `G.gen_iapath V x q y` by (auto simp: G.gen_iapath_def)
      ultimately show ?thesis using awalk' `G.gen_iapath V x q y` by (simp add: G.gen_iapath_def G.apath_def)
    qed
    then have "(q1 @ (u,v) # q2) = q"
      using `G.gen_iapath V x q y` `G.is_slim V` unfolding G.is_slim_def by metis
    then show False unfolding q_decomp by simp
  qed
  then have "(v,u) \<notin> parcs G" by (auto intro: G.arcs_symmetric)

  def G' \<equiv> "\<lparr>pverts = pverts G - {w},
      parcs = {(u,v), (v,u)} \<union> (parcs G - {(u,w), (w,u), (v,w), (w,v)})\<rparr>"

  have mem_G': "(u,v) \<in> parcs G'" "w \<notin> pverts G'" by (auto simp: G'_def)

  interpret pd_G': pair_fin_digraph G'
  proof
    fix e assume A: "e \<in> parcs G'"
    have "e \<in> parcs G \<and> e \<noteq> (u, w) \<and> e \<noteq> (w, u) \<and> e \<noteq> (v, w) \<and> e \<noteq> (w, v) \<Longrightarrow> fst e \<noteq> w"
      "e \<in> parcs G \<and> e \<noteq> (u, w) \<and> e \<noteq> (w, u) \<and> e \<noteq> (v, w) \<and> e \<noteq> (w, v) \<Longrightarrow> snd e \<noteq> w"
      using out_arcs in_arcs by auto
    with A uvw_arcs1 show "fst e \<in> pverts G'" "snd e \<in> pverts G'"
      using `u \<noteq> w` `v \<noteq> w` by (auto simp: G'_def G.wellformed')
  next
  qed (auto simp: G'_def arc_to_ends_def)

  interpret spd_G': pair_pseudo_graph G'
  proof (unfold_locales, simp add: symmetric_def)
    have "sym {(u,v), (v,u)}" "sym (parcs G)" "sym {(u, w), (w, u), (v, w), (w, v)}"
      using `symmetric G` by (auto simp: symmetric_def sym_def) 
    then have "sym ({(u,v), (v,u)} \<union> (parcs G - {(u,w), (w,u), (v,w), (w,v)}))"
      by (intro sym_Un) (auto simp: sym_diff)
    then show "sym (parcs G')" unfolding G'_def by simp
  qed

  have card_G': "n = card (pverts G' - V)"
  proof -
    have "pverts G - V = insert w (pverts G' - V)"
      using `w \<in> pverts G - V` by (auto simp: G'_def)
    then show ?thesis using `Suc n = card (pverts G - V)` mem_G' by simp
  qed

  have G_is_sd: "G = subdivide G' (u,v) w" (is "_ = ?sdG'")
    using `w \<in> pverts G - V` `(u,v) \<notin> parcs G` `(v,u) \<notin> parcs G`  uvw_arcs1 uvw_arcs2
    by (intro pair_pre_digraph.equality) (auto simp: G'_def)
  
  have gcg_sd: "gen_contr_graph (subdivide G' (u,v) w) V = gen_contr_graph G' V"
  proof -
    have "V \<subseteq> pverts G"
      using `G.is_slim V` by (auto simp: G.is_slim_def verts3_def)
    moreover
    have "verts3 G' = verts3 G"  
      by (simp only: G_is_sd spd_G'.verts3_subdivide[OF `(u,v) \<in> parcs G'` `w \<notin> pverts G'`])
    ultimately
    have V: "V \<subseteq> pverts G'"
      using `w \<in> pverts G - V` by (auto simp: G'_def)
    with mem_G' show ?thesis by (rule spd_G'.gcg_subdivide_eq)
  qed

  have is_slim_G': "pd_G'.is_slim V" using `G.is_slim V` mem_G' `w \<notin> V`
    unfolding G_is_sd by (rule spd_G'.is_slim_if_subdivide)
  with mem_G' have "subdivision (gen_contr_graph G' V) (subdivide G' (u, v) w)"
    by (intro Suc card_G' subdivision.intros) auto
  then show ?case
    by (simp add: gcg_sd G_is_sd)
qed

lemma  contr_is_subgraph_subdivision:
  shows "\<exists>H. subgraph (with_proj H) G \<and> subdivision (contracted_graph G) H"
proof -
  interpret sG: pair_pseudo_graph slim
    by (rule pair_pseudo_graph_slim)

  have "subdivision (gen_contr_graph slim (verts3 G)) slim "
    by (rule sG.subdivision_gen_contr) (rule slim_is_slim)
  then show ?thesis unfolding contr_graph_slim_eq by (blast intro: subgraph_slim)
qed

theorem final_theorem:
  fixes K :: "'a pair_pre_digraph"
  assumes subgraph_K: "subgraph K G"
  assumes spd_K: "pair_pseudo_graph K"
  assumes kuratowski: "K\<^bsub>3,3\<^esub> (contracted_graph K) \<or> K\<^bsub>5\<^esub> (contracted_graph K)"
  shows "\<not>planar G"
proof -
  interpret spd_K: pair_pseudo_graph K by (fact spd_K)
  obtain H where subgraph_H: "subgraph (with_proj H) K"
      and subdiv_H:"subdivision (contracted_graph K) H"
    by atomize_elim (rule spd_K.contr_is_subgraph_subdivision)
  from subdiv_H and kuratowski
  have "\<exists>K. subdivision K H \<and> (K\<^bsub>3,3\<^esub> K \<or> K\<^bsub>5\<^esub> K)" by blast
  then show ?thesis using  subgraph_H subgraph_K
 unfolding planar_def by (blast intro: subgraph_trans)
qed

theorem certificate_characterization:
  defines "kuratowski \<equiv> \<lambda>G. K\<^bsub>3,3\<^esub> G \<or> K\<^bsub>5\<^esub> G"
  shows "kuratowski (contracted_graph G) \<longleftrightarrow> (\<exists>H. kuratowski H \<and> subdivision H slim \<and> verts3 G = verts3 slim)" (is "?L \<longleftrightarrow> ?R")
proof
  assume ?L
  interpret S: pair_pseudo_graph slim by (rule pair_pseudo_graph_slim)
  have "subdivision (contracted_graph G) slim"
  proof -
    have *: "S.is_slim (verts3 G)" by (rule slim_is_slim)
    show ?thesis using contr_graph_slim_eq S.subdivision_gen_contr[OF *] by auto
  qed
  moreover
  have "verts3 slim = verts3 G" (is "?l = ?r")
  proof safe
    fix v assume "v \<in> ?l" then show "v \<in> ?r"
      using verts_slim_in_G verts3_slim_in_verts3 by auto
  next
    fix v assume "v \<in> ?r"
    have "v \<in> verts3 (contracted_graph G)"
    proof -
      have "v \<in> verts (contracted_graph G)"
        using `v \<in> ?r` by (auto simp: verts3_def gen_contr_graph_def)
      then show ?thesis
        using `?L` unfolding kuratowski_def by (auto simp: verts3_K33 verts3_K5)
    qed
    then have "v \<in> verts3 (gen_contr_graph slim (verts3 G))" unfolding contr_graph_slim_eq .
    then have "2 < in_degree (gen_contr_graph slim (verts3 G)) v" 
      unfolding verts3_def by auto
    also have "\<dots> \<le> in_degree slim v"
      using `v \<in> ?r` verts3_slim_in_verts3 by (auto intro: S.in_degree_contr)
    finally show "v \<in> verts3 slim"
      using verts3_in_slim_G `v \<in> ?r` unfolding verts3_def by auto
  qed
  ultimately show ?R using `?L` by auto
next
  assume ?R
  then have "kuratowski (gen_contr_graph slim (verts3 G))"
    unfolding kuratowski_def 
    by (auto intro: K33_contractedI K5_contractedI)
  then show ?L unfolding contr_graph_slim_eq .
qed

definition certify :: "'a pair_pre_digraph \<Rightarrow> bool" where
  "certify cert \<equiv> let C = contracted_graph cert in subgraph cert G \<and> (K\<^bsub>3,3\<^esub> C \<or> K\<^bsub>5\<^esub>C)"

theorem certify_complete:
  assumes "pair_pseudo_graph cert"
  assumes "subgraph cert G"
  assumes "\<exists>H. subdivision H cert \<and> (K\<^bsub>3,3\<^esub> H \<or> K\<^bsub>5\<^esub> H)"
  shows "certify cert"
  unfolding certify_def
  using assms by (auto simp: Let_def intro: K33_contractedI K5_contractedI)

theorem certify_sound:
  assumes "pair_pseudo_graph cert"
  assumes "certify cert"
  shows" \<not>planar G" 
  using assms by (intro final_theorem) (auto simp: certify_def Let_def)

theorem certify_characterization:
  assumes "pair_pseudo_graph cert"
  shows "certify cert \<longleftrightarrow> subgraph cert G \<and> verts3 cert = verts3 (pair_pre_digraph.slim cert)
      \<and>(\<exists>H. (K\<^bsub>3,3\<^esub> H \<or> K\<^bsub>5\<^esub> H) \<and> subdivision H (pair_pre_digraph.slim cert))"
      (is "?L \<longleftrightarrow> ?R")
  by (auto simp only: simp_thms certify_def Let_def pair_pseudo_graph.certificate_characterization[OF assms])

end

end
