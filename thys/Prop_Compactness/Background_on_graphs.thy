theory Background_on_graphs

imports Main

begin

section \<open>Special Graph Theoretical Notions\<close>

text \<open>This theory provides a background on specialized graph notions and    properties.  We follow the approach by L. Noschinski available in the AFPs.  Since not all elements of Noschinski theory are required, we prefer not to import it.

 The proof are desiccated in several steps since the focus is clarity instead proof automation. \<close>

record ('a,'b) pre_digraph =
  verts :: "'a set"
  arcs :: "'b set"
  tail :: "'b \<Rightarrow> 'a"
  head :: "'b \<Rightarrow> 'a"
  
definition tails:: "('a,'b) pre_digraph \<Rightarrow> 'a set" where
   "tails G \<equiv>  {tail G e |e. e \<in> arcs G }"

definition tails_set :: "('a,'b) pre_digraph \<Rightarrow> 'b set \<Rightarrow> 'a set" where
   "tails_set G E \<equiv>  { tail G e |e. e \<in> E \<and> E \<subseteq> arcs G }"

definition heads:: "('a,'b) pre_digraph \<Rightarrow> 'a set" where
   "heads G \<equiv>  { head G e |e.  e \<in> arcs G }"

definition heads_set:: "('a,'b) pre_digraph \<Rightarrow> 'b set \<Rightarrow> 'a set" where
   "heads_set G E \<equiv>  { head G e |e.  e \<in> E \<and> E \<subseteq> arcs G }"

(* Incident vertexes *)
definition neighbour::  "('a,'b) pre_digraph \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" where
   "neighbour G v u  \<equiv>
   \<exists>e. e\<in> (arcs G) \<and> (( head G e = v \<and> tail G e = u) \<or>
   (head G e  = u \<and> tail G e = v))"

(* Vertex neighbourhood *)
definition neighbourhood:: "('a,'b) pre_digraph \<Rightarrow> 'a  \<Rightarrow> 'a set" where
   "neighbourhood G v \<equiv> {u |u. neighbour G u v}"

definition bipartite_digraph:: "('a,'b) pre_digraph \<Rightarrow> 'a set \<Rightarrow> 'a set \<Rightarrow> bool" where
   "bipartite_digraph G X Y  \<equiv> 
       (X \<union> Y = (verts G)) \<and>  X \<inter> Y = {} \<and>
       (\<forall>e \<in> (arcs G).(tail G e) \<in> X \<longleftrightarrow> (head G e) \<in> Y)"

(* Left to right directed bipartite digraph *)
definition dir_bipartite_digraph:: "('a,'b) pre_digraph \<Rightarrow> 'a set \<Rightarrow> 'a set \<Rightarrow> bool" 
  where
  "dir_bipartite_digraph G X Y  \<equiv> (bipartite_digraph G X Y) \<and> 
   ((tails G = X) \<and>  (\<forall> e1 \<in> arcs G. \<forall> e2 \<in> arcs G. e1 = e2 \<longleftrightarrow> head G e1 = head G e2 \<and> tail G e1 = tail G e2))"  

(* Directed bipartite digraph with finite neighbourhoods of its tails *)
definition K_E_bipartite_digraph:: "('a,'b) pre_digraph \<Rightarrow> 'a set \<Rightarrow> 'a set \<Rightarrow> bool" 
  where
  "K_E_bipartite_digraph G X Y \<equiv>
  (dir_bipartite_digraph G X Y) \<and> (\<forall>x\<in>X.  finite (neighbourhood G x))"

(* Matchings in directed bipartite digraphs *)
definition dirBD_matching:: "('a,'b) pre_digraph \<Rightarrow> 'a set \<Rightarrow> 'a set \<Rightarrow> 'b set \<Rightarrow> bool"
  where
  "dirBD_matching G X Y E  \<equiv>  
           dir_bipartite_digraph G X Y \<and> (E  \<subseteq>  (arcs G)) \<and>
           (\<forall> e1\<in>E. (\<forall> e2\<in> E.  e1 \<noteq> e2 \<longrightarrow>
           ((head G e1) \<noteq> (head G e2)) \<and> 
           ((tail G e1) \<noteq> (tail G e2))))"

lemma tail_head:
  assumes "dir_bipartite_digraph G X Y" and "e \<in> arcs G" 
  shows "(tail G e) \<in> X \<and> (head G e) \<in> Y"
  using assms
     by (unfold dir_bipartite_digraph_def, unfold bipartite_digraph_def, unfold tails_def, auto)

lemma tail_head1:
  assumes "dirBD_matching G X Y E" and "e \<in> E" 
  shows "(tail G e) \<in> X \<and> (head G e) \<in> Y"
  using assms tail_head[of G X Y e] by(unfold dirBD_matching_def, auto) 

lemma dirBD_matching_tail_edge_unicity:
   "dirBD_matching G X Y E \<longrightarrow>  
    (\<forall>e1 \<in> E. (\<forall> e2\<in> E. (tail G e1 = tail G e2) \<longrightarrow> e1 = e2))"
(* Slederhammer proof: by (meson dirBD_matching_def) *)
proof
  assume "dirBD_matching G X Y E"
  thus "\<forall>e1\<in>E. \<forall>e2\<in>E. tail G e1 = tail G e2 \<longrightarrow> e1 = e2"
     by (unfold dirBD_matching_def, auto)
qed

lemma dirBD_matching_head_edge_unicity:
   "dirBD_matching G X Y E \<longrightarrow>  
    (\<forall>e1 \<in> E. (\<forall> e2\<in> E. (head G e1 = head G e2) \<longrightarrow> e1 = e2))"
(* Slederhammer proof:  by (meson dirBD_matching_def) *)
proof
  assume "dirBD_matching G X Y E"
  thus " \<forall>e1\<in>E. \<forall>e2\<in>E. head G e1 = head G e2 \<longrightarrow> e1 = e2"
     by(unfold dirBD_matching_def, auto)
qed

(* Perfect matching (covering tail vertexes) in directed bipartite digraphs *)
definition dirBD_perfect_matching::
  "('a,'b) pre_digraph \<Rightarrow> 'a set \<Rightarrow> 'a set \<Rightarrow> 'b set \<Rightarrow> bool"
  where
  "dirBD_perfect_matching G X Y E \<equiv> 
   dirBD_matching G X Y E \<and> (tails_set G E = X)"

lemma Tail_covering_edge_in_Pef_matching: 
      "\<forall>x\<in>X. dirBD_perfect_matching G X Y E \<longrightarrow> (\<exists>e \<in> E. tail G e = x)"
proof
  fix x 
  assume Hip1: "x \<in> X"
  show "dirBD_perfect_matching G X Y E \<longrightarrow> (\<exists>e\<in>E. tail G e = x)"
  proof
    assume "dirBD_perfect_matching G X Y E"
    hence "x \<in> tails_set G E" using Hip1 
           by (unfold dirBD_perfect_matching_def, auto)
    thus "\<exists>e\<in>E. tail G e = x " by (unfold tails_set_def, auto)
  qed
qed

lemma Edge_unicity_in_dirBD_P_matching: 
   "\<forall>x\<in>X. dirBD_perfect_matching G X Y E \<longrightarrow> (\<exists>!e \<in> E. tail G e = x)"
(* Shorter proof:  by (metis Tail_covering_edge_in_Pef_matching dirBD_matching_def dirBD_perfect_matching_def) *)
proof
  fix x 
  assume Hip1: "x \<in> X"
  show "dirBD_perfect_matching G X Y E \<longrightarrow> (\<exists>!e \<in> E. tail G e = x)" 
  proof
    assume Hip2: "dirBD_perfect_matching G X Y E" 
    then obtain "\<exists>e. e \<in> E \<and> tail G e = x"
    using Hip1  Tail_covering_edge_in_Pef_matching[of X G Y E] by auto
    then obtain e where e: "e \<in> E \<and>  tail G e = x" by auto
    hence a: "e \<in> E \<and>  tail G e = x" by auto
    show "\<exists>!e. e \<in> E \<and> tail G e = x"
    proof
      show  "e \<in> E \<and> tail G e = x"  using a by auto
      next      
      fix e1 
      assume Hip3: "e1 \<in> E \<and> tail G e1 = x"
      hence "tail G e = tail G e1 \<and> e \<in> E  \<and> e1 \<in> E" using a by auto
      moreover 
      have "dirBD_matching G X Y E"
        using Hip2  by(unfold dirBD_perfect_matching_def, auto)
      ultimately
      show "e1 = e" 
        using Hip2 dirBD_matching_tail_edge_unicity[of G X Y E]
        by auto 
    qed
  qed
qed

definition E_head :: "('a,'b) pre_digraph \<Rightarrow> 'b set  \<Rightarrow> ('a  \<Rightarrow> 'a)" 
  where
  "E_head G E = (\<lambda>x. (THE y. \<exists> e. e \<in> E \<and> tail G e = x \<and>  head G e = y))"

lemma unicity_E_head1:
   assumes "dirBD_matching G X Y E \<and> e \<in> E \<and> tail G e = x \<and> head G e = y"
   shows "(\<forall>z.(\<exists> e. e \<in> E \<and> tail G e = x \<and> head G e = z)\<longrightarrow> z = y)"
using assms dirBD_matching_tail_edge_unicity by blast

lemma unicity_E_head2:
   assumes "dirBD_matching G X Y E \<and> e \<in> E \<and> tail G e = x \<and> head G e = y" 
   shows  "(THE a. \<exists> e. e \<in> E \<and> tail G e = x \<and> head G e = a) = y" 
using assms dirBD_matching_tail_edge_unicity by blast

lemma  unicity_E_head:
  assumes "dirBD_matching G X Y E \<and> e \<in> E \<and> tail G e = x \<and> head G e = y" 
  shows "(E_head G E) x = y"
  using assms unicity_E_head2[of G X Y E e x y] by(unfold E_head_def, auto)

lemma E_head_image : 
  "dirBD_perfect_matching G X Y E \<longrightarrow>  
   (e \<in> E \<and> tail G e = x \<longrightarrow> (E_head G E) x = head G e)"
(* Shorter proof:  by (meson dirBD_perfect_matching_def unicity_E_head) *)
proof
  assume "dirBD_perfect_matching G X Y E" 
  thus "e \<in> E \<and> tail G e = x \<longrightarrow> (E_head G E) x = head G e"
    using dirBD_matching_tail_edge_unicity [of G X Y E] 
    by (unfold E_head_def, unfold dirBD_perfect_matching_def, blast)
qed

lemma E_head_in_neighbourhood:
  "dirBD_matching G X Y E \<longrightarrow> e \<in> E \<longrightarrow> tail G e = x \<longrightarrow> 
   (E_head G E) x \<in> neighbourhood G x"
(* Shorter proof:  by (metis dirBD_matching_def in_mono mem_Collect_eq neighbour_def neighbourhood_def unicity_E_head) *)
proof (rule impI)+
  assume 
  dir_BDm: "dirBD_matching G X Y E" and ed: "e \<in> E" and hd: "tail G e = x"
  show "E_head G E x \<in> neighbourhood G x" 
  proof- 
    have  "(\<exists>y. y = head G e)" using hd by auto
    then obtain y where y: "y = head G e" by auto
    hence "(E_head G E) x = y" 
      using dir_BDm ed hd unicity_E_head[of G X Y E e x y] 
      by auto
    moreover
    have "e \<in> (arcs G)" using dir_BDm ed by(unfold dirBD_matching_def, auto)
    hence "neighbour G y x" using ed hd y by(unfold neighbour_def, auto)
    ultimately
    show ?thesis using  hd ed by(unfold neighbourhood_def, auto)
  qed
qed

lemma dirBD_matching_inj_on:
   "dirBD_perfect_matching G X Y E \<longrightarrow> inj_on (E_head G E) X"
(* A shorter proof:  
by (smt (verit, best) E_head_image Edge_unicity_in_dirBD_P_matching dirBD_matching_head_edge_unicity dirBD_perfect_matching_def inj_onI) *)
proof(rule impI)
  assume dirBD_pm : "dirBD_perfect_matching G X Y E"
  show "inj_on (E_head G E) X" 
  proof(unfold inj_on_def)
    show "\<forall>x\<in>X. \<forall>y\<in>X. E_head G E x = E_head G E y \<longrightarrow> x = y"
    proof
      fix x
      assume 1: "x\<in> X"
      show "\<forall>y\<in>X. E_head G E x = E_head G E y \<longrightarrow> x = y"
      proof 
        fix y
        assume 2: "y\<in> X" 
        show "E_head G E x = E_head G E y \<longrightarrow> x = y"
        proof(rule impI)
          assume same_eheads: "E_head G E x = E_head G E y" 
          show "x=y"
          proof- 
            have hex: " (\<exists>!e \<in> E. tail G e = x)"
              using dirBD_pm 1 Edge_unicity_in_dirBD_P_matching[of X G Y E] 
              by auto
            then obtain ex where hex1: "ex \<in> E \<and> tail G ex = x" by auto
            have ey: " (\<exists>!e \<in> E. tail G e = y)" 
              using  dirBD_pm 2 Edge_unicity_in_dirBD_P_matching[of X G Y E] 
              by auto
            then obtain ey where hey1: "ey \<in> E \<and> tail G ey = y" by auto
            have ettx: "E_head G E x = head G ex"
              using  dirBD_pm hex1 E_head_image[of G X Y E ex x] by auto
            have etty: "E_head G E y = head G ey"
              using  dirBD_pm hey1 E_head_image[of G X Y E ey y] by auto
            have same_heads: "head G ex = head G ey" 
              using same_eheads ettx etty by auto
            hence same_edges: "ex = ey" 
              using dirBD_pm 1 2 hex1 hey1 
                    dirBD_matching_head_edge_unicity[of G X Y E]
            by(unfold dirBD_perfect_matching_def,unfold dirBD_matching_def, blast)
            thus ?thesis using  same_edges hex1 hey1 by auto
          qed
        qed
      qed
    qed
  qed
qed

   
end
