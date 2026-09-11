(* König-Egervary Theorem for finite Graphs version
   Fabian Fernando Serrano Suárez  UNAL Manizales
   Thaynara Arielly de Lima        Universidade Federal de Goiás 
   Mauricio Ayala-Rincón           Universidade Federal de Goiás and Universidade de Brasília
   Last modified: 16 June, 2026
*)

section\<open>König-Egervary theorem for finite graphs\<close>


theory Koenig_Egervary_finite
(*<*)
  imports
    "Main"  
    "Prop_Compactness.Hall_Theorem_Graphs"
begin

(*>*)

text\<open>This theory formalizes the fact that the Cardinality of a maximal matching equals the Cardinality 
  of a minimum Vertex Cover in finite bipartite digraphs. The formalization uses the countable graph 
  version of Hall Theorem proved in the @{session Prop_Compactness} as a consequence of the compactness theorem. 

Goal: apply the finite version of König-Egervary theorem in the proof of a countable (infinite) version of Dilworth's theorem. \<close>

text\<open>
The countable version of Dilworth's theorem follows the standard approach which applies the 
finite version of Dilworth's theorem, De Bruijn-Erdös k-colouring theorem.
\<close>
text\<open>
From the finite graph version of Hall theorem follows the finite version of  König-Egervary theorem, 
and then, the finite version of Dilworth's theorem.
\<close>

text\<open>
  Formalization following Jonathan L. Gross' textbook,  "Graph Theory and its Applications", 3rd edition, pages 477-478
                         Hall's theorem implies  König-Egervary's theorem
\<close> 

text\<open>
\begin{definition}
A vertex cover of a graph $G$ is a set $C\subseteq V(G)$ that contains at least one endpoint of every edge. 
The vertices in $C$ \emph{cover} $E(G)$.  The next definition is relative to a subset of edges. 
Then, $C$ such that \texttt{vertex\_cover G C E(G)} is a vertex cover covering all edges of $G$.
\end{definition}
\<close>

definition  vertex_cover:: "('a,'b) pre_digraph \<Rightarrow> 'b set \<Rightarrow> 'a set \<Rightarrow> bool"
  where
    "vertex_cover G E C \<equiv>  C \<subseteq> (verts G) \<and> E \<subseteq>(arcs G) \<and>
                         (\<forall> e \<in> E. (head G e) \<in> C \<or> (tail G e) \<in> C)"
text \<open>
Since no vertex can cover two edges of a matching, the size of every vertex cover is at least  the size of every matching.
\<close>

text \<open>
\begin{lemma}
Let $M$ be a matching in a graph $G$, and let $C$ be a vertex cover of $G$. Then @{prop "card M \<le> card C"}.
\end{lemma}
\<close>
(* A vertex is not adjacent two different edges in a matching *)

lemma vertex_in_matching:
  assumes "dirBD_matching G X Y E" 
  shows "\<forall>e1 \<in> E. \<forall>e2 \<in> E. e1 \<noteq> e2 \<longrightarrow>
          (((tail G e1) = v \<or> (head G e1) = v) \<longrightarrow> ((tail G e2) \<noteq> v \<and> (head G e2) \<noteq> v))"
proof(rule+) 
  show " \<And>e1 e2.
       e1 \<in> E \<Longrightarrow>
       e2 \<in> E \<Longrightarrow>
       e1 \<noteq> e2 \<Longrightarrow> tail G e1 = v \<or> head G e1 = v \<Longrightarrow> tail G e2 = v \<Longrightarrow> False"
    by (metis assms bipartite_digraph_def dirBD_matching_def 
        dir_bipartite_digraph_def disjoint_iff tail_head1) 
next 
  show "\<And>e1 e2.
       e1 \<in> E \<Longrightarrow>
       e2 \<in> E \<Longrightarrow> e1 \<noteq> e2 \<Longrightarrow> tail G e1 = v \<or> head G e1 = v \<Longrightarrow> head G e2 \<noteq> v" 
    by (metis assms bipartite_digraph_def dirBD_matching_def dir_bipartite_digraph_def
        disjoint_iff tail_head1)
qed

fun f_matching_cover :: "('a,'b) pre_digraph \<Rightarrow> 'a set \<Rightarrow> 'b set  \<Rightarrow> ('a  \<Rightarrow> 'b)"
  where 
    "f_matching_cover G V E  = (\<lambda>v. (THE e.  e \<in> E \<and> (tail G e = v \<or> head G e = v)))"

lemma function_f_matching_cover:
  assumes "dirBD_matching G X Y E"  
    and "a\<in>E" and  "(head G a) = v \<or> (tail G a) = v" 
  shows "f_matching_cover G V E v = a"
proof-
  have "(THE e. e \<in> E \<and> (tail G e = v \<or> head G e = v)) = a"
  proof(rule the_equality)
    show "a \<in> E \<and> (tail G a = v \<or> head G a = v)" using assms(2,3) by auto 
  next
    fix e
    assume hyp1: "e \<in> E \<and> (tail G e = v \<or> head G e = v)"
    show   "e = a" 
    proof(rule ccontr)
      assume hyp2: "e \<noteq> a"
      hence "(tail G e) \<noteq> v \<and> (head G e) \<noteq> v" 
        using assms hyp1 hyp2  vertex_in_matching[of G X Y E]  by auto
      thus False using hyp1 by auto
    qed
  qed
  thus ?thesis by simp 
qed

lemma surj_f_matching_cover1: 
  assumes "dirBD_matching G X Y E" and  "vertex_cover G E C"
  shows "\<forall>e\<in>E. \<exists>v\<in>C. f_matching_cover G C E v = e" 
proof
  fix e
  assume hyp: "e\<in>E" 
  show "\<exists>v\<in>C. f_matching_cover G C E v = e"
  proof-
    have *: "(head G e) \<in> C \<or> (tail G e) \<in> C"  
      using assms(2) hyp by(unfold vertex_cover_def, auto) 
    let ?v1 =  "(head G e)"
    let ?v2 =  "(tail G e)"
    have  "(?v1 = (head G e) \<or> ?v1 = (tail G e)) \<and> (?v2 = (head G e) \<or> ?v2 = (tail G e))"
      by auto
    hence "(f_matching_cover G C E ?v1 = e) \<and> (f_matching_cover G C E ?v2 = e)"
      using assms(1) hyp function_f_matching_cover[of G X Y E e _ C] by auto
    thus ?thesis using * by auto 
  qed
qed

lemma surj_f_matching_cover:
  assumes "dirBD_matching G X Y E" and "vertex_cover G E C" 
  shows "E \<subseteq> (f_matching_cover G C E) ` C"
proof
  fix e 
  assume "e \<in> E"
  hence "\<exists>v\<in>C. f_matching_cover G C E v = e"  
    using assms surj_f_matching_cover1[of G X Y E C] by auto
  thus  "e \<in> f_matching_cover G C E ` C" using image_def by auto 
qed

lemma card_matching_cover:
  assumes "dirBD_matching G X Y E" and "vertex_cover G E C" and "finite C"
  shows "card E \<le> card ((f_matching_cover G C E) ` C)"
proof-
  have "E \<subseteq> (f_matching_cover G C E) ` C"
    using assms  surj_f_matching_cover[of G X  Y E] by auto
  thus ?thesis using assms(3) by (simp add: card_mono)
qed

lemma card_matching_cover0:
  assumes  "finite C"
  shows "card ((f_matching_cover G C E) ` C) \<le> card C" using 
    card_image_le assms by auto

lemma card_matching_cover1:
  assumes "dirBD_matching G X Y E" and "vertex_cover G E C" and "finite C"
  shows "card E \<le> card C" using assms card_matching_cover[of G X Y E C]
    card_matching_cover0[of C G E] by auto

text\<open>
\begin{definition}
A minimum vertex cover is a vertex cover of minimum size among all vertex cover of the graph.
\end{definition}
\<close>
definition minimum_vertex_cover:: "('a,'b) pre_digraph \<Rightarrow> 'b set \<Rightarrow> 'a set \<Rightarrow> bool"                                    
  where "minimum_vertex_cover G E C
         \<equiv> (vertex_cover G E C) \<and> (\<forall> C1. vertex_cover G E C1 \<longrightarrow> card C \<le>  card C1)"
text\<open>
\begin{definition}
A maximum  matching is a matching of maximum size among all matchings of the graph.
\end{definition}
\<close>
definition maximum_dirBD_matching:: "('a,'b) pre_digraph \<Rightarrow> 'a set \<Rightarrow> 'a set \<Rightarrow> 'b set \<Rightarrow> bool"
  where  "maximum_dirBD_matching G X Y E  \<equiv>
          dirBD_matching G X Y E  \<and> (\<forall> E1. dirBD_matching G X Y E1 \<longrightarrow> card E1 \<le> card E)" 

text\<open>
Let M be a matching in a graph G, and let C be a vertex cover of G such that |M| = |C|.
Then M is a maximum matching and C is a minimum vertex cover.
\<close>

lemma matching_cover_sub1:
  assumes  "vertex_cover G E C" and "E1 \<subseteq> E"
  shows "vertex_cover G E1 C"  using assms by(unfold vertex_cover_def, auto)

corollary matching_cover_sub2:
  assumes  "vertex_cover G (arcs G) C" and "E1 \<subseteq> (arcs G)"
  shows "vertex_cover G E1 C" using assms matching_cover_sub1 by blast

lemma card_matching_cover2:
  assumes "dirBD_matching G X Y E" and 
    "vertex_cover G (arcs G) C" and  
    "finite (verts G)" and 
    "card E = card C"           
  shows "maximum_dirBD_matching G X Y E \<and> minimum_vertex_cover G (arcs G) C"
proof
  have "C \<subseteq> (verts G)" using assms(2) unfolding vertex_cover_def by auto
  hence * : "finite C" using assms(3) finite_subset[of "C" "verts G"] by auto
  show "maximum_dirBD_matching G X Y E" 
  proof(unfold maximum_dirBD_matching_def, rule conjI)  
    show "dirBD_matching G X Y E" using assms(1) by auto 
  next
    show "\<forall>E1. dirBD_matching G X Y E1 \<longrightarrow> card E1 \<le> card E"
    proof(rule allI, rule impI)
      fix E1
      assume hyp: "dirBD_matching G X Y E1"
      show  "card E1 \<le> card E"
      proof(rule ccontr)
        assume "\<not> card E1 \<le> card E"
        hence "card E < card E1" by auto
        hence "card C < card E1" using assms(4) by auto
        moreover       
        have  "card E1 \<le> card C" 
          using hyp dirBD_matching_def[of G X Y E1]  matching_cover_sub2  
            card_matching_cover1[of G X Y E1 C] assms(2) * by auto     
        ultimately 
        show False by auto
      qed
    qed
  qed
next
  show "minimum_vertex_cover G (arcs G) C"
  proof(unfold minimum_vertex_cover_def, rule conjI)
    show "vertex_cover G (arcs G) C" using assms(2) by auto
  next
    have 2: "E \<subseteq> arcs G" using assms(1) unfolding dirBD_matching_def by auto 
    show  "\<forall>C1. vertex_cover G (arcs G) C1 \<longrightarrow> card C \<le> card C1"
    proof(rule allI, rule impI)
      fix C1
      assume hyp:  "vertex_cover G (arcs G) C1"
      show "card C \<le> card C1"
      proof-
        have 1:  "vertex_cover G E C1" 
        proof(unfold vertex_cover_def, intro conjI ballI)
          show "C1 \<subseteq> (verts G)" using hyp by(unfold vertex_cover_def, auto)
          show  "E \<subseteq> arcs G" using 2 by auto
        next
          fix e
          assume "e\<in>E" 
          hence "e\<in>(arcs G)" using 2 by auto
          thus  "head G e \<in> C1 \<or> tail G e \<in> C1" using hyp by(unfold vertex_cover_def, auto)
        qed 
      next
        show "card C \<le> card C1"
        proof-
          have 1: "vertex_cover G E C1" 
          proof(unfold vertex_cover_def, intro ballI conjI)
            show "C1 \<subseteq> (verts G)" using hyp by(unfold vertex_cover_def, auto)
            show  "E \<subseteq> arcs G" using 2 by auto
            fix e
            assume "e\<in>E" 
            hence "e\<in>(arcs G)" using 2 by auto
            thus "head G e \<in> C1 \<or> tail G e \<in> C1" using hyp by(unfold vertex_cover_def, auto)
          qed 
          have "C1 \<subseteq> verts G" using 1 by(unfold vertex_cover_def, auto)
          hence "finite  C1"  using assms(3) by (simp add: finite_subset)  
          hence "card E \<le> card C1" using assms(1) 1 card_matching_cover1[of G X Y E C1] by auto
          thus  "card C \<le> card C1" using assms(4) by auto
        qed
      qed
    qed
  qed
qed

text\<open>
Remark: The converse of the above property does not hold in general;
however, it does hold for bipartite graphs.
\<close>

text\<open>
\begin{teorema}[König-Egervary]\label{Konig-Egervary}
If $G$ is a bipartite graph, then the maximum size of a matching in $G$ equals the minimum size of a
vertex cover $G$.
\end{teorema}
\<close>
lemma vertex_subset_BD_decomposition:
  assumes "bipartite_digraph G X Y" and "C \<subseteq> (verts G)" 
  shows  "C = (C \<inter> X) \<union> (C \<inter> Y)"
  by (metis assms(1,2) bipartite_digraph_def inf.order_iff inf_sup_distrib1)

lemma  cover_descomposition: 
  assumes "bipartite_digraph G X Y" and "vertex_cover G (arcs G) C"
  shows "C = (C \<inter> X) \<union> (C \<inter> Y)"
  using vertex_subset_BD_decomposition
  by (metis assms(1,2) vertex_cover_def) 

lemma cover_descomposition1:
  assumes  "bipartite_digraph G X Y" and "minimum_vertex_cover G (arcs G) C"
  shows "C = (C \<inter> X) \<union> (C \<inter> Y)"
  using assms(1,2) cover_descomposition minimum_vertex_cover_def by blast 

lemma card_neighbourhood:
  assumes  "finite (\<Union> (neighbourhood G`W))" and
    "card (\<Union> (neighbourhood G`(W-{w}))) = card (\<Union> (neighbourhood G ` W))"
  shows "(\<Union> (neighbourhood G`(W-{w}))) = (\<Union> (neighbourhood G ` W))" using assms 
proof- 
  have "(\<Union> (neighbourhood G`(W-{w}))) \<subseteq> (\<Union> (neighbourhood G ` W))" using assms by auto
  thus ?thesis using assms card_subset_eq[of "\<Union> (neighbourhood G ` W)" "(\<Union> (neighbourhood G`(W-{w})))"] 
    by auto
qed

lemma  neighbourhood_set:
  assumes "finite W" and "finite (\<Union> (neighbourhood G`W))" and 
    "(card W) > card (\<Union> (neighbourhood G ` W))"
  shows "\<exists>w\<in>W. (\<Union> (neighbourhood G`(W-{w}))) = (\<Union> (neighbourhood G ` W))" 
proof-
  {
    fix W
    have "finite W \<Longrightarrow> finite (\<Union> (neighbourhood G`W)) \<Longrightarrow>(card W) > card (\<Union> (neighbourhood G ` W)) \<Longrightarrow>
       \<exists>w\<in>W. (\<Union> (neighbourhood G`(W-{w}))) = (\<Union> (neighbourhood G ` W))"
    proof(induct arbitrary: G rule: finite_psubset_induct)
      case (psubset W)
      show ?case
      proof (cases)
        assume "W={}" then show ?thesis
          using psubset.prems(2) by auto
      next 
        assume "W \<noteq> {}"
        hence "\<exists>w. w \<in> W" by auto
        then obtain w where w: "w \<in> W" by auto
        have 1: "card (W-{w}) = (card W)-1" using  w  by auto
        have "(\<Union> (neighbourhood G`(W-{w}))) \<subseteq> (\<Union> (neighbourhood G ` W))" by auto
        hence 2:  "card (\<Union> (neighbourhood G`(W-{w}))) \<le> card (\<Union> (neighbourhood G ` W))" 
          using   psubset.prems(1) by (metis card_mono) 
        hence  "card (\<Union> (neighbourhood G`(W-{w}))) \<le> card (W-{w})" 
          using psubset.prems(2) using w by auto
        hence "(card (\<Union> (neighbourhood G`(W-{w}))) = card (W-{w})) \<or> 
            card (\<Union> (neighbourhood G`(W-{w}))) < card (W-{w})"  by auto
        thus ?thesis
        proof        
          assume hyp: "card (\<Union> (neighbourhood G`(W-{w}))) = card (W-{w})"           
          have  "card (W-{w}) \<le> card (\<Union> (neighbourhood G ` W))" using 2 hyp by auto
          hence "card (\<Union> (neighbourhood G ` W)) = card (W-{w})" using  psubset.prems(2) 1
            by auto
          hence "card (\<Union> (neighbourhood G`(W-{w}))) = card (\<Union> (neighbourhood G ` W))"
            using hyp by auto
          hence "(\<Union> (neighbourhood G`(W-{w}))) = (\<Union> (neighbourhood G ` W))" using card_neighbourhood
            by (metis psubset.prems(1)) 
          thus ?thesis using w by blast 
        next
          let ?B = "W-{w}"
          assume  "card (\<Union> (neighbourhood G`?B)) < card ?B"
          hence "\<exists>z\<in>?B. (\<Union> (neighbourhood G`(?B-{z}))) = (\<Union> (neighbourhood G `  ?B))" 
            using w   psubset(2)  psubset.prems(1)
            by (meson Diff_subset \<open>\<Union> (neighbourhood G ` (W - {w})) \<subseteq>
               \<Union> (neighbourhood G ` W)\<close> card_Diff1_less card_psubset finite_subset psubset.hyps(1))
          then obtain z where z1: "z\<in>?B" and z2: "(\<Union> (neighbourhood G`(?B-{z}))) = (\<Union> (neighbourhood G `  ?B))" 
            by auto
          have 1: "W-{z} = (?B-{z}) \<union> {w}"  using w z1 by auto
          have 2: "W = ?B \<union> {w}"  using w by auto
          have "(\<Union> (neighbourhood G`(W-{z}))) = (\<Union> (neighbourhood G ` W))" using z2 1 2 by auto            
          thus ?thesis using z1 w by auto
        qed
      qed
    qed 
  }
  thus ?thesis using assms by auto
qed

definition induced_subgraph:: "('a,'b) pre_digraph \<Rightarrow> 'a set \<Rightarrow> ('a,'b) pre_digraph"
  where 
    "induced_subgraph G V \<equiv>
   (| verts = V,
    arcs = {e |e. e \<in> (arcs G) \<and> (tail G e) \<in> V \<and> (head G e) \<in> V},
    tail =  (\<lambda> e. tail G e),
    head =  (\<lambda> e. head G e)
    |)"

lemma induced_Bipartite_Digraph:
  assumes "bipartite_digraph G X Y" and "X1\<subseteq>X" and  "Y1\<subseteq>Y"
  shows   "bipartite_digraph (induced_subgraph G  (X1 \<union> Y1)) X1 Y1"
proof-
  have "X1 \<union> Y1 = verts (induced_subgraph G  (X1 \<union> Y1))" 
    by (simp add: induced_subgraph_def)
  moreover
  have  "X1 \<inter> Y1 = {}" using assms  bipartite_digraph_def[of G X Y] by auto
  moreover
  have "(\<forall>e \<in> arcs (induced_subgraph G  (X1 \<union> Y1)).
        (tail (induced_subgraph G  (X1 \<union> Y1)) e \<in> X1) =
        (head (induced_subgraph G  (X1 \<union> Y1)) e \<in> Y1))"
    using assms
    by (smt (verit, del_insts)
        IntI Un_iff bipartite_digraph_def empty_iff induced_subgraph_def mem_Collect_eq select_convs(2)
        select_convs(3) select_convs(4) subset_eq) 
  ultimately 
  show ?thesis using  bipartite_digraph_def by blast
qed

lemma  perfect_matching_induced_subgraph:
  fixes  G :: "('a::countable, 'b::countable) pre_digraph" 
  assumes "dir_bipartite_digraph (induced_subgraph G V) X Y"
    and "\<forall>i\<in> X. finite (neighbourhood (induced_subgraph G V) i)"
    and "\<forall> W \<subseteq> X. card W \<le> card (\<Union> (neighbourhood (induced_subgraph G V) ` W))"
  shows "(\<exists>E. dirBD_perfect_matching (induced_subgraph G V) X Y E)"
  by (simp add: assms(1) assms(2) assms(3) marriage_sufficiency_graph) 


lemma vertex_cover_refining:
  assumes "dir_bipartite_digraph G X Y"
    and "finite (verts G)" 
    and "vertex_cover G (arcs G) C"
    and "W \<subseteq> C \<inter> X"
    and "card(W) > card( \<Union>(neighbourhood (induced_subgraph G ((C \<inter> X) \<union> (Y - (C \<inter> Y))))`W ))"
  shows "vertex_cover G  (arcs G) 
           ((C \<inter> X - W) \<union>  
            ((C \<inter> Y) \<union> \<Union>(neighbourhood (induced_subgraph G ((C \<inter> X) \<union> (Y - (C \<inter> Y))))`W)))"
proof(unfold vertex_cover_def, rule conjI)
  show "C \<inter> X - W \<union> (C \<inter> Y \<union> \<Union> (neighbourhood (induced_subgraph G (C \<inter> X \<union> (Y - C \<inter> Y))) ` W)) \<subseteq> verts G"
    by(smt (verit, del_insts) Int_Diff UN_iff Un_iff assms(1,3) bipartite_digraph_def dir_bipartite_digraph_def induced_subgraph_def le_infI1
        le_sup_iff mem_Collect_eq neighbour_def neighbourhood_def simps(2,3,4) subsetI tail_head vertex_cover_def)
next
  show  "arcs G \<subseteq> arcs G \<and>
         (\<forall>e\<in>arcs G.
        head G e \<in> C \<inter> X - W \<union> (C \<inter> Y \<union> \<Union> (neighbourhood (induced_subgraph G (C \<inter> X \<union> (Y - C \<inter> Y))) ` W)) \<or>
        tail G e \<in> C \<inter> X - W \<union> (C \<inter> Y \<union> \<Union> (neighbourhood (induced_subgraph G (C \<inter> X \<union> (Y - C \<inter> Y))) ` W)))"
  proof(intro conjI ballI)
    show "arcs G \<subseteq> arcs G" by auto
  next
    let ?Cx = "C \<inter> X"
    let ?Cy = "C \<inter> Y"
    let ?Cpx = "?Cx - W" 
    let ?G1 = "(induced_subgraph G (?Cx \<union> (Y - ?Cy)))" 
    let ?NbhGpW = "\<Union>(neighbourhood ?G1`W)"
    fix e 
    assume "e \<in> arcs G"
    show "head G e \<in> ?Cpx \<union> (?Cy \<union> ?NbhGpW) \<or> tail G e \<in> ?Cpx \<union> (?Cy \<union> ?NbhGpW)"
      by(smt (verit, del_insts) Diff_iff Int_iff UN_iff Un_iff \<open>e \<in> arcs G\<close> assms(1,3) induced_subgraph_def 
          mem_Collect_eq neighbour_def neighbourhood_def simps(2,3,4) tail_head vertex_cover_def)
  qed
qed

lemma vertex_cover_refining1:
  assumes "dir_bipartite_digraph G X Y"  and "finite (verts G)" and "vertex_cover G (arcs G) C"
    and "W \<subseteq> C \<inter> X"
    and "card(W) > card(\<Union>(neighbourhood (induced_subgraph G ((C \<inter> X) \<union> (Y - (C \<inter> Y))))`W ))"
  shows "card ((C \<inter> X)-W \<union> ((C \<inter> Y) \<union> \<Union> (neighbourhood (induced_subgraph G ((C \<inter> X) \<union> (Y - (C \<inter> Y))))`W ))) < (card C)"
proof-
  let ?Cx = "C \<inter> X"
  let ?Cy = "C \<inter> Y"
  let ?Cpx = "?Cx - W" 
  let ?G1 =  "(induced_subgraph G (?Cx \<union> (Y - ?Cy)))"    
  let ?NbhGpW = "\<Union>(neighbourhood ?G1`W)"
  let ?Cpy = "?Cy \<union> ?NbhGpW" 
  have 1: "?Cx \<inter> ?Cy = {}" 
    by (metis assms(1) bipartite_digraph_def dir_bipartite_digraph_def inf_assoc inf_bot_right inf_left_commute)
  have 2: "C = ?Cx \<union> ?Cy"
    using assms(1,3) cover_descomposition dir_bipartite_digraph_def by blast   
  have "card ?Cpx < card ?Cx - card ?NbhGpW"
    by (metis (full_types) assms(2,3,4,5) card_Diff_subset card_mono diff_less_mono2 
        finite_Int infinite_super less_le_trans vertex_cover_def) 
  hence "card ?Cpx + card ?Cy < card ?Cx + card ?Cy-card ?NbhGpW"
    by linarith
  hence "card ?Cpx + card ?Cy + card ?NbhGpW <  card ?Cx + card ?Cy" by auto
  hence "card ?Cpx + card ?Cy + card ?NbhGpW < card C"
    by (metis "1" "2" assms(2,3) card_Un_disjoint finite_Int rev_finite_subset vertex_cover_def)  
  thus "card  (?Cpx \<union> (?Cy \<union> ?NbhGpW)) < card C"
    by (smt (verit, ccfv_SIG) add_le_cancel_left card_Un_le linorder_not_less nat_arith.add1 order_trans) 
qed

corollary vc_refinable_not_minimal:
  assumes "dir_bipartite_digraph G X Y"
    and "finite (verts G)" 
    and "vertex_cover G (arcs G) C"
    and "W \<subseteq> C \<inter> X"
    and "card(W) > card( \<Union>(neighbourhood (induced_subgraph G ((C \<inter> X) \<union> (Y - (C \<inter> Y))))`W ))"
  shows "\<not> minimum_vertex_cover G (arcs G) C"
proof
  assume " minimum_vertex_cover G (arcs G) C"
  show False using vertex_cover_refining  vertex_cover_refining1
    by (metis \<open>minimum_vertex_cover G (arcs G) C\<close> assms(1,2,4,5) leD minimum_vertex_cover_def)
qed   

theorem Konig_Egervary1:
  fixes  G :: "('a::countable, 'b::countable) pre_digraph" 
  assumes "maximum_dirBD_matching G X Y E" and "minimum_vertex_cover G (arcs G) C" 
    and "finite (verts G)" and "finite C" and "dir_bipartite_digraph G X Y" 
    and "\<forall>i\<in>X. finite (neighbourhood G i)"
    and "dir_bipartite_digraph (induced_subgraph G ((C \<inter> X) \<union> (Y- (C \<inter> Y)))) (C \<inter> X) (Y-(C \<inter> Y))"
  shows "(\<exists>E. dirBD_perfect_matching(induced_subgraph G (C \<inter> X \<union> (Y - C \<inter> Y))) (C \<inter> X)  (Y - C \<inter> Y) E)"
proof-
  let ?C1 = "C \<inter> X" 
  let ?C2 = "C \<inter> Y"
  let ?G1 = "induced_subgraph G (?C1 \<union> (Y-?C2))" 
  have  1:  "?C1 \<subseteq> X" and 2: "Y-?C2 \<subseteq> Y" by auto
  have  3:  "bipartite_digraph G X Y" using assms(5) dir_bipartite_digraph_def by auto
  hence 4:  "bipartite_digraph ?G1 ?C1 (Y-?C2)"
    using 1 2 induced_Bipartite_Digraph[of G X Y  "?C1" "Y-?C2"] by auto 
  have *:  "vertex_cover G (arcs G) C" using assms(2)
    by (simp add: minimum_vertex_cover_def)
  have **: "\<forall> W. W \<subseteq> ?C1 \<longrightarrow>  (card W) \<le> card (\<Union> (neighbourhood ?G1 ` W))"
  proof(rule allI, rule impI)
    fix W::"'a set" 
    assume hyp1: "W \<subseteq> ?C1" 
    show "card W \<le> card (\<Union> (neighbourhood (induced_subgraph G (C \<inter> X \<union> (Y - C \<inter> Y))) ` W))"
    proof-
      have 6: "finite W"
        using finite_subset  hyp1 assms(4) by blast
      have 7: "(\<forall>W. \<forall>w. W \<subseteq> ?C1 \<and> w\<in>W \<longrightarrow> (neighbourhood ?G1 w) \<subseteq>  (neighbourhood G w))"
      proof((rule allI)+ , rule impI)
        fix W fix w
        assume hyp: "W \<subseteq> ?C1 \<and> w\<in>W"    
        show  "neighbourhood ?G1 w \<subseteq> neighbourhood G w"
        proof
          fix x
          assume "x \<in> (neighbourhood ?G1 w)" 
          hence  "neighbour ?G1 x w" using  neighbourhood_def by force
          hence  "neighbour G x w" using 1 2 4 hyp induced_subgraph_def
            by (smt (z3) mem_Collect_eq neighbour_def select_convs(2) select_convs(3) select_convs(4))
          thus "x \<in> (neighbourhood G w)"  using  neighbourhood_def by force 
        qed
      qed 
      have "\<forall>W. W \<subseteq> ?C1 \<longrightarrow> (\<Union> (neighbourhood ?G1 ` W)) \<subseteq>  (\<Union> (neighbourhood G ` W))" 
      proof(intro allI impI)
        fix W
        assume hyp: "W \<subseteq> ?C1" 
        show "(\<Union> (neighbourhood ?G1 ` W)) \<subseteq>  (\<Union> (neighbourhood G ` W))"
        proof
          fix x 
          assume "x \<in> (\<Union> (neighbourhood ?G1 ` W))"
          hence "\<exists>w \<in> W. x \<in> (neighbourhood ?G1 w)" by auto  
          then obtain w where w: "w \<in> W" and "x \<in> (neighbourhood ?G1 w)" by auto
          hence "x \<in> (neighbourhood G w)" using hyp 7 by auto
          thus "x \<in>  (\<Union> (neighbourhood G ` W))" using w by auto
        qed
      qed   
      have  "\<forall> W. W \<subseteq> ?C1 \<longrightarrow>
          card W \<le> (card (\<Union> (neighbourhood ?G1 ` W)))"
      proof (intro allI impI)
        fix W 
        assume hyp1: "W \<subseteq> ?C1" 
        hence hyp2: "finite W" using 7
          using assms(4) finite_subset by fastforce
        show  "card W  \<le> (card (\<Union> (neighbourhood ?G1 ` W)))"
        proof(rule ccontr)
          assume
            hyp: "\<not> card W \<le> (card (\<Union> (neighbourhood ?G1 ` W)))"
          show False using  vc_refinable_not_minimal
            by (metis "*" assms(2,3,5) hyp hyp1 linorder_le_less_linear)
        qed
      qed
      thus ?thesis
        using hyp1 by blast
    qed 
  qed
  thus "(\<exists>E. dirBD_perfect_matching  (induced_subgraph G (C \<inter> X \<union> (Y - C \<inter> Y))) (C \<inter> X)  (Y - C \<inter> Y) E)"
    using marriage_sufficiency_graph **  assms(7)
    by (smt (verit, del_insts) "4" Int_Un_eq(3) Un_Int_assoc_eq Un_Int_eq(3) assms(4) 
        bipartite_digraph_def card.empty card.infinite card_mono
        card_subset_eq empty_iff finite_UN finite_Un order_antisym)
qed

lemma bd_induced_subgraph: 
  assumes "bipartite_digraph G X Y" and "X1\<subseteq>X" and  "Y1\<subseteq>Y"
  shows "bipartite_digraph (induced_subgraph (inverse_digraph G) (X1 \<union> Y1)) Y1 X1"
  by (metis assms(1,2,3) induced_Bipartite_Digraph inverse_bipartite_digraph sup.commute)

lemma minimum_vertex_cover_inverse:
  assumes  "minimum_vertex_cover G (arcs G) C"
  shows  "minimum_vertex_cover (inverse_digraph G) (arcs G) C"
  by (smt (verit, ccfv_threshold) assms inverse_digraph_def
      minimum_vertex_cover_def select_convs(1,2,3,4)
      vertex_cover_def)

lemma vc_inv_digraph_is_vc:
  assumes  "vertex_cover G (arcs G) C"
  shows  "vertex_cover (inverse_digraph G) (arcs G) C"
  by (metis assms inverse_digraph_def select_convs(1,2,3,4) vertex_cover_def)

corollary vertex_cover_refining2a: 
  assumes "dir_bipartite_digraph (inverse_digraph G) Y X"
    and "finite (verts G)" 
    and "vertex_cover (inverse_digraph G) (arcs G) C"
    and "W \<subseteq> C \<inter> Y"
    and "card W > card (\<Union> (neighbourhood (induced_subgraph (inverse_digraph G) (C \<inter> Y \<union> (X - C \<inter> X))) ` W))"
  shows "\<not> minimum_vertex_cover (inverse_digraph G) (arcs G) C" 
proof
  assume "minimum_vertex_cover (inverse_digraph G) (arcs G) C"
  show False
    by (metis \<open>minimum_vertex_cover (inverse_digraph G) (arcs G) C\<close> assms(1,2,4,5) inverse_digraph_def minimum_vertex_cover_def
        select_convs(1) simps(2) vc_refinable_not_minimal)
qed   

theorem Konig_Egervary2:
  fixes  G :: "('a::countable, 'b::countable) pre_digraph" 
  assumes "maximum_dirBD_matching G X Y E"
    and "minimum_vertex_cover (inverse_digraph G) (arcs G) C" 
    and "finite (verts(inverse_digraph G))"
    and "finite C" 
    and "dir_bipartite_digraph G X Y" 
    and "\<forall>i\<in>Y. finite (neighbourhood (inverse_digraph G) i)"
    and "dir_bipartite_digraph (induced_subgraph (inverse_digraph G) ((C \<inter> Y) \<union> (X - (C \<inter> X)))) (C \<inter> Y) (X-(C \<inter> X))" 
    and "verts G \<subseteq> X \<union> Y"
  shows "(\<exists>E. dirBD_perfect_matching  (induced_subgraph (inverse_digraph G) (C \<inter> Y \<union> (X - C \<inter> X))) (C \<inter> Y) (X - C \<inter> X) E)"
proof-
  let ?C1 = "C \<inter> X" 
  let ?C2 = "C \<inter> Y"
  let ?G1 = "induced_subgraph (inverse_digraph G) (?C2 \<union> (X-?C1))" 
  have 1:  "?C2 \<subseteq> Y" and 2: "X-?C1 \<subseteq> X" by auto
  have 3:  "bipartite_digraph (inverse_digraph G) Y X" 
    using assms(5) dir_bipartite_digraph_def by (metis inverse_bipartite_digraph) 
  hence 4:  "bipartite_digraph ?G1 ?C2 (X-?C1)"
    using 1 2  bd_induced_subgraph[of G X Y "?C2" "X-?C1"] 
    by(meson induced_Bipartite_Digraph inverse_bipartite_digraph) 
  have *:  "vertex_cover (inverse_digraph G) (arcs (inverse_digraph G)) C" using assms(2)
    by (simp add: inverse_digraph_def minimum_vertex_cover_def)
  have **: "\<forall> W. W \<subseteq> ?C2 \<longrightarrow> (card W) \<le> card (\<Union> (neighbourhood ?G1 ` W))"
  proof(intro allI impI)
    fix W::"'a set" 
    assume hyp1: "W \<subseteq> ?C2" 
    show "card W \<le> card (\<Union> (neighbourhood (induced_subgraph (inverse_digraph G) (C \<inter> Y \<union> (X - C \<inter> X))) ` W))"
    proof-
      have 6: "finite W" using finite_subset hyp1 assms(4) by blast
      have 7: "(\<forall>W. \<forall>w. W \<subseteq> ?C2 \<and> w\<in>W \<longrightarrow> (neighbourhood ?G1 w) \<subseteq> (neighbourhood (inverse_digraph G) w))"
      proof(intro allI impI)
        fix W fix w
        assume hyp: "W \<subseteq> ?C2 \<and> w\<in>W"    
        show  "(neighbourhood ?G1 w) \<subseteq>  (neighbourhood (inverse_digraph G) w)"
        proof
          fix x
          assume "x \<in> (neighbourhood ?G1 w)" 
          hence  "neighbour ?G1 x w" using  neighbourhood_def by force
          hence  "neighbour (inverse_digraph G) x w" using 1 2 4 hyp induced_subgraph_def
            by (smt (z3) mem_Collect_eq neighbour_def select_convs(2) select_convs(3) select_convs(4))
          thus "x \<in> (neighbourhood (inverse_digraph G) w)"  using  neighbourhood_def by force
        qed
      qed 
      have "\<forall>W. W \<subseteq> ?C2 \<longrightarrow> (\<Union> (neighbourhood ?G1 ` W)) \<subseteq>  (\<Union> (neighbourhood (inverse_digraph G) ` W))" 
      proof(intro allI impI)
        fix W
        assume hyp: "W \<subseteq> ?C2" 
        show "(\<Union> (neighbourhood ?G1 ` W)) \<subseteq>  (\<Union> (neighbourhood (inverse_digraph G) ` W))"
        proof
          fix x 
          assume "x \<in> (\<Union> (neighbourhood ?G1 ` W))"
          hence "\<exists>w \<in> W. x \<in> (neighbourhood ?G1 w)" by auto  
          then obtain w where w: "w \<in> W" and "x \<in> (neighbourhood ?G1 w)" by auto
          hence "x \<in> (neighbourhood (inverse_digraph G) w)" using hyp 7 by auto
          thus "x \<in>  (\<Union> (neighbourhood (inverse_digraph G)` W))" using w by auto
        qed
      qed   
      hence 8: "\<forall>W. W \<subseteq> ?C2 \<longrightarrow> finite (\<Union> (neighbourhood ?G1 `W))"  using assms(6)
        by (smt (verit, ccfv_threshold) "1" Int_Diff_Un assms(4) finite_UN finite_Un rev_finite_subset subset_iff)    
      have  "\<forall> W. W \<subseteq> ?C2 \<longrightarrow>  card W \<le> (card (\<Union> (neighbourhood ?G1 ` W)))"
      proof(intro allI impI)
        fix W 
        assume hyp1: "W \<subseteq> ?C2" 
        hence hyp2: "finite W" using 7 using assms(4) finite_subset by fastforce
        show  "card W  \<le> (card (\<Union> (neighbourhood ?G1 ` W)))"
        proof(rule ccontr)
          assume hyp: "\<not> card W \<le> (card (\<Union> (neighbourhood ?G1 ` W)))"  show False
            by(metis (no_types, lifting) "3" assms(2,3,5,8) bipartite_digraph_def hyp hyp1 
                inf_sup_aci(5) infinite_super leI minimum_vertex_cover_def inv_dirBD_is_dirBD vertex_cover_refining2a)    
        qed
      qed
      thus ?thesis using hyp1 by blast
    qed 
  qed 
  thus "(\<exists>E. dirBD_perfect_matching  (induced_subgraph (inverse_digraph G) (C \<inter> Y \<union> (X - C \<inter> X))) 
        (C \<inter> Y) (X - C \<inter> X) E)" 
    using marriage_sufficiency_graph[of "(inverse_digraph G)" ?C2 "X-?C1" ] **  assms(7)
    by (smt (verit, del_insts) Diff_cancel Int_Diff_Un Un_Int_assoc_eq Un_Int_eq(3) assms(4) 
        card.empty card.infinite card_mono card_subset_eq
        empty_iff finite_UN inf_le2 nle_le perfect_matching_induced_subgraph rev_finite_subset)
qed  

lemma union_dirBd_matching:
  assumes "dir_bipartite_digraph G X Y" and  "C = (C \<inter> X) \<union> (C \<inter> Y)" 
    and "dirBD_perfect_matching (induced_subgraph G (C \<inter> X \<union> (Y - C \<inter> Y))) (C \<inter> X)  (Y - C \<inter> Y) E1"
    and "dirBD_perfect_matching (induced_subgraph (inverse_digraph G) (C \<inter> Y \<union> (X - C \<inter> X))) (C \<inter> Y) 
       (X - C \<inter> X) E2"
  shows "dirBD_matching G X Y (E1 \<union> E2)"
proof-
  have 1: "E1 \<union> E2 \<subseteq> arcs G"
    by(smt (verit, ccfv_threshold) Un_iff assms(3,4) dirBD_matching_def 
        dirBD_perfect_matching_def in_mono induced_subgraph_def inverse_digraph_def 
        mem_Collect_eq simps(2) subsetI)
  have 2: "(\<forall>e1\<in>E1 \<union> E2. \<forall>e2\<in>E1 \<union> E2. e1 \<noteq> e2 \<longrightarrow> head G e1 \<noteq> head G e2 \<and> tail G e1 \<noteq> tail G e2)"
  proof
    fix e1
    assume hyp1: "e1\<in>E1 \<union> E2"
    show "(\<forall>e2\<in>E1 \<union> E2. e1 \<noteq> e2 \<longrightarrow> head G e1 \<noteq> head G e2 \<and> tail G e1 \<noteq> tail G e2)"
    proof (intro ballI impI)
      fix e2
      assume hyp2: "e2\<in>E1 \<union> E2"
      assume hyp3:  "e1 \<noteq> e2"
      show  "head G e1 \<noteq> head G e2 \<and> tail G e1 \<noteq> tail G e2"
      proof-
        have "(e1 \<in> E1 \<and> e2 \<in> E1) \<or> (e1 \<in> E2 \<and> e2 \<in> E1)\<or>(e1 \<in> E1 \<and> e2 \<in> E2)\<or>(e1 \<in> E2 \<and> e2 \<in> E2)"
          using hyp1 hyp2 by auto
        thus ?thesis
          by (smt (verit, ccfv_SIG) DiffE assms(3,4) dirBD_perfect_matching_def hyp3 induced_subgraph_def
              inverse_digraph_def select_convs(3,4) tail_head1  vertex_in_matching)
      qed
    qed
  qed
  show ?thesis using assms(1) 1 2 using dirBD_matching_def by blast
qed

lemma card_prop_induced_dirBD_perfect_matching:
  assumes  "dirBD_perfect_matching (induced_subgraph G (C \<inter> X \<union> (Y - C \<inter> Y))) (C \<inter> X)  (Y - C \<inter> Y) E"
    and "finite (arcs G)"
  shows  "card (C \<inter> X) = card E"  
proof-
  have "E \<subseteq> (arcs G)"  using assms induced_subgraph_def
    by (metis (no_types, lifting) dirBD_matching_def dirBD_perfect_matching_def mem_Collect_eq select_convs(2) subset_iff) 
  hence  "finite E" using  induced_subgraph_def assms(2)
    using rev_finite_subset by blast 
  thus  "card (C \<inter> X) = card E" using  card_perfect_match_in_finitedirBD
    using assms(1) by blast
qed

lemma card_prop_induced_inv_dirBD_perfect_matching: 
  assumes "dirBD_perfect_matching  (induced_subgraph (inverse_digraph G) (C \<inter> Y \<union> (X - C \<inter> X))) (C \<inter> Y) (X - C \<inter> X) E"    
  shows "card (C \<inter> Y) = card E" using assms card_perfect_match_in_finitedirBD
  by (smt (verit) bijective_f_perfect_matching card_image dirBD_matching_tail_edge_unicity 
      dirBD_perfect_matching_def function_f_perfect_matching inj_on_def tail_head1)

lemma finite_neighbourhood_aux:
  assumes "dir_bipartite_digraph G X Y" and "finite (verts G)"
  shows  "\<forall>i\<in>(verts G). finite (neighbourhood G i)"
  by (smt (verit, del_insts) Un_iff assms(1,2) bipartite_digraph_def dir_bipartite_digraph_def
      mem_Collect_eq neighbour_def  neighbourhood_def rev_finite_subset subsetI tail_head)

lemma finite_neighbourhood:
  assumes "dir_bipartite_digraph G X Y" and "finite (verts G)"
  shows  "\<forall>i\<in> X. finite (neighbourhood G i)"
  using finite_neighbourhood_aux
  by (metis (no_types, lifting) Un_iff assms(1,2) bipartite_digraph_def dir_bipartite_digraph_def)

lemma finite_inverse_neighbourhood:
  assumes "dir_bipartite_digraph G X Y" and "finite (verts G)"
  shows  "\<forall>i\<in>Y. finite (neighbourhood (inverse_digraph G) i)" 
proof- 
  have "Y \<subseteq> (verts G)" 
    by (metis Un_iff assms(1) bipartite_digraph_def dir_bipartite_digraph_def subsetI) 
  thus ?thesis  using  inverse_bipartite_digraph[of G X Y]
      finite_neighbourhood_aux[of "inverse_digraph G" Y X] finite_neighbourhood[of "inverse_digraph G" Y X]
    by (metis assms(1,2) inv_dirBD_is_dirBD inverse_digraph_def select_convs(1))
qed  

lemma finite_vertex_cover: 
  assumes "dir_bipartite_digraph G X Y" and "finite (verts G)" and "vertex_cover G (arcs G) C" 
  shows "finite C"
  by (metis assms(2,3) rev_finite_subset vertex_cover_def) 

theorem Konig_Egervary:
  fixes  G :: "('a::countable, 'b::countable) pre_digraph" 
  assumes "dir_bipartite_digraph G X Y" and "finite (verts G)" 
    and "maximum_dirBD_matching G X Y E" and  "minimum_vertex_cover G (arcs G) C"
  shows "card E = card C"
proof-
  let ?C1 = "C \<inter> X"
  let ?C2 = "C \<inter> Y"
  let ?G0 = "induced_subgraph G (?C1 \<union> (Y- ?C2))"  
  let ?G1 = "induced_subgraph (inverse_digraph G) (?C2 \<union> (X-?C1))"  
  have 1: "C = (C \<inter> X) \<union> (C \<inter> Y)" using cover_descomposition assms(1) dir_bipartite_digraph_def assms(3)
    by (metis assms(4) minimum_vertex_cover_def)
  have 2: "(C \<inter> X) \<inter> (C \<inter> Y) = {}"  using assms(1) dir_bipartite_digraph_def
    by (metis bipartite_digraph_def induced_Bipartite_Digraph inf_le2) 
  have 3: "finite C" 
    using finite_vertex_cover assms(1,2,4) minimum_vertex_cover_def by blast
  have "dir_bipartite_digraph ?G0 ?C1 (Y-?C2)" 
  proof-
    have 1: "bipartite_digraph  ?G0 ?C1 (Y-?C2)"
      using assms(1) induced_Bipartite_Digraph dir_bipartite_digraph_def by fastforce 
    have 2: "tails ?G0 \<subseteq> ?C1"  
    proof
      fix x
      assume hyp: "x \<in> tails ?G0"
      show  "x \<in> ?C1" 
      proof-
        have "\<exists>e. e \<in> arcs ?G0 \<and> x = (tail ?G0 e)" using hyp tails_def
          by (smt (verit, best) mem_Collect_eq)
        thus ?thesis
          by (metis (lifting) "1" IntI Int_Diff_Un Un_iff assms(1) 
              bipartite_digraph_def dir_bipartite_digraph_def induced_subgraph_def
              mem_Collect_eq select_convs(2,3) tail_head)       
      qed
    qed
    have 3: "(\<forall>e1 \<in> arcs (induced_subgraph G (?C1 \<union> (Y- ?C2))).
           \<forall>e2 \<in> arcs (induced_subgraph G (?C1 \<union> (Y- ?C2))).
           (e1 = e2) =
           (head (induced_subgraph G (?C1 \<union> (Y- ?C2))) e1 = head (induced_subgraph G (?C1 \<union> (Y- ?C2))) e2 \<and>
           tail (induced_subgraph G (?C1 \<union> (Y- ?C2))) e1 = tail (induced_subgraph G (?C1 \<union> (Y- ?C2))) e2))"
      by (metis (no_types, lifting) assms(1) dir_bipartite_digraph_def induced_subgraph_def mem_Collect_eq
          select_convs(2,3,4))
    show ?thesis using 1 2 3 dir_bipartite_digraph_def by blast
  qed 
  have "(\<exists> E1. dirBD_perfect_matching (induced_subgraph G (C \<inter> X \<union> (Y - C \<inter> Y))) (C \<inter> X)  (Y - C \<inter> Y) E1)"
    by (smt (verit, ccfv_threshold) "3" Konig_Egervary1 Un_iff \<open>dir_bipartite_digraph (induced_subgraph G (C \<inter> X \<union> (Y - C \<inter> Y))) (C \<inter> X) (Y - C \<inter> Y)\<close>
        assms(1,2,3,4) bipartite_digraph_def dir_bipartite_digraph_def finite_neighbourhood_aux subset_iff)
  then obtain E1 where E1:  "dirBD_perfect_matching (induced_subgraph G (C \<inter> X \<union> (Y - C \<inter> Y))) (C \<inter> X) (Y - C \<inter> Y) E1" by auto 
  have "dir_bipartite_digraph ?G1 ?C2 (X-?C1)"
  proof-
    have 1: "bipartite_digraph ?G1 ?C2 (X-?C1)"
      by (metis Diff_subset assms(1) bd_induced_subgraph dir_bipartite_digraph_def inf.cobounded2 inf_sup_aci(5))      
    have 2: "tails ?G1  \<subseteq> ?C2" 
    proof
      fix x
      assume hyp: "x \<in> tails ?G1"
      show  "x \<in> C \<inter> Y" 
      proof-
        have "\<exists>e. e \<in> arcs ?G1 \<and> x = (tail ?G1 e)" using hyp tails_def
          by (smt (verit, best) mem_Collect_eq)
        thus ?thesis 
          by (metis (no_types, lifting) "2" Int_iff Un_Diff_Int Un_iff assms(1) bipartite_digraph_def dir_bipartite_digraph_def
              induced_subgraph_def inverse_digraph_def mem_Collect_eq select_convs(2,3) tail_head)       
      qed
    qed
    have 3: "(\<forall>e1 \<in> arcs ?G1. \<forall>e2 \<in> arcs ?G1.
           (e1 = e2) = (head ?G1 e1 = head ?G1 e2 \<and> tail ?G1 e1 = tail ?G1 e2))"
      by (metis (no_types, lifting) assms(1) dir_bipartite_digraph_def induced_subgraph_def inverse_digraph_def mem_Collect_eq
          select_convs(2,3,4)) 
    show ?thesis using 1 2 3 dir_bipartite_digraph_def by blast
  qed
  have "(\<exists>E2. dirBD_perfect_matching ?G1 (C \<inter> Y) (X - C \<inter> X) E2)"
    by (smt (verit, best) "3" Konig_Egervary2 \<open>dir_bipartite_digraph (induced_subgraph (inverse_digraph G) (C \<inter> Y \<union> (X - C \<inter> X))) (C \<inter> Y) (X - C \<inter> X)\<close>
        assms(1,2,3,4) bipartite_digraph_def dir_bipartite_digraph_def finite_neighbourhood inverse_digraph_def minimum_vertex_cover_inverse select_convs(1)
        subset_refl inv_dirBD_is_dirBD)
  then obtain E2 where E2: "dirBD_perfect_matching ?G1 (C \<inter> Y) (X - C \<inter> X) E2"
    by auto
  have 4: "dirBD_matching G X Y (E1 \<union> E2)" using union_dirBd_matching assms(1) 1 E1 E2 by blast
  have 5: "finite (E1 \<union> E2)" using E1 E2 
    by (metis "3" "4" assms(4) dirBD_matching_def finite_surj
        matching_cover_sub2 minimum_vertex_cover_def surj_f_matching_cover)  
  have 6: "card (C \<inter> X) = card E1" using E1 card_prop_induced_dirBD_perfect_matching  "5" card_perfect_match_in_finitedirBD by blast
  have 7: "card (C \<inter> Y) = card E2" using E2 card_prop_induced_inv_dirBD_perfect_matching by blast
  have 8: "card C = card E1 + card E2"
    by (metis "1" "2" "3" "6" "7" card_Un_disjoint finite_Int) 
  have  "E1 \<inter> E2 = {}" 
  proof(rule ccontr)
    assume "E1 \<inter> E2 \<noteq> {}"
    hence "\<exists>e. e \<in> E1 \<and> e \<in> E2" by auto
    then obtain e where e: "e \<in> E1 \<and> e \<in> E2" by auto
    hence "tail G e \<in> (C \<inter> X) \<and> tail G e \<in> (C \<inter> Y)" using E1 E2 using dirBD_perfect_matching_def
      by (metis (no_types, lifting) DiffE induced_subgraph_def inverse_digraph_def select_convs(3) 
          simps(4) tail_head1)
    hence 1: "tail G e \<in>  X \<inter> Y" by auto
    hence "X \<inter> Y \<noteq> {}" by auto
    have  "X \<inter> Y = {}" using assms(1) bipartite_digraph_def by (metis dir_bipartite_digraph_def) 
    thus False using 1 by auto
  qed
  hence 9: "card (E1 \<union> E2) = card C" 
    using "5" "8" card_Un_disjoint by auto 
  hence "maximum_dirBD_matching G X Y (E1 \<union> E2)"  using card_matching_cover2
    using "4" assms(2,4) minimum_vertex_cover_def by blast
  thus ?thesis
    by (metis "9" assms(3) maximum_dirBD_matching_def
        order_antisym)
qed

end
(*>*)
