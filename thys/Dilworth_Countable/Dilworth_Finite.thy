(* Dilworth's Theorem for finite Graphs version
   Fabian Fernando Serrano Suárez  UNAL Manizales
   Thaynara Arielly de Lima        Universidade Federal de Goiás 
   Mauricio Ayala-Rincón           Universidade Federal de Goiás and Universidade de Brasília
   Last modified: 16 June, 2026
*)

section \<open>Dilworth Finite Theorem\<close>

text\<open>In a finite graph, the Cardinality of the smallest chain decomposition and the largest anti-chain are equal. \<close>

theory Dilworth_Finite

imports 
  Main
  "HOL-Library.Disjoint_Sets"
  "Koenig_Egervary_finite" 
begin

locale part_order =   (* Here we use the definition from Isabelle/HOL *)
  fixes A :: "'a set"
  fixes r :: "'a rel"
  assumes p_o_translation : "partial_order_on A r"   

locale part_order_countable = part_order A r 
  for A :: "'a::countable set" and r :: "'a rel"

definition chain:: "'a set \<Rightarrow> 'a set \<Rightarrow> 'a rel \<Rightarrow> bool"
  where "chain B A r \<equiv> B \<subseteq> A \<and> partial_order_on A r \<and> total_on B r"

definition chain_decomposition:: "'a set \<Rightarrow> 'a rel \<Rightarrow>'a set set \<Rightarrow> bool"
  where "chain_decomposition A r C \<equiv>  partition_on A C \<and> (\<forall>B\<in>C.(chain B A r))" 

lemma "chain_decomposition {} r {}"
  by (simp add: chain_decomposition_def partition_on_empty)

definition smallest_chain_decomposition:: "'a set \<Rightarrow> 'a rel \<Rightarrow>'a set set \<Rightarrow> bool"
  where  "smallest_chain_decomposition A r C \<equiv> 
          (chain_decomposition A r C) \<and> (\<forall>P. chain_decomposition A r P \<longrightarrow> card C \<le> card P)"

definition anti_total ::"'a set \<Rightarrow> 'a rel \<Rightarrow> bool"
  where "anti_total A r \<equiv> (\<forall>x\<in>A. \<forall>y\<in>A. x\<noteq>y \<longrightarrow> (x,y) \<notin> r \<and> (y, x) \<notin> r)"

definition anti_chain:: "'a set \<Rightarrow> 'a rel \<Rightarrow> 'a set \<Rightarrow> bool"
  where "anti_chain A r B \<equiv> B \<subseteq> A \<and> partial_order_on A r \<and> anti_total B r"

definition largest_antichain:: "'a set \<Rightarrow> 'a rel \<Rightarrow> 'a set  \<Rightarrow> bool"
  where "largest_antichain A r B  \<equiv> anti_chain A r B \<and> (\<forall>C. anti_chain A r C \<longrightarrow> card C \<le> card B)"

definition relation_to_digraph:: "'a set \<Rightarrow> 'a rel \<Rightarrow> (('a + 'a), ('a + 'a) \<times> ('a + 'a ))pre_digraph"
  where 
    "relation_to_digraph A r \<equiv>
   (| verts = A <+> A, 
    arcs = {(Inl x, Inr y)|x y. x \<in> A \<and> y \<in> A \<and> (x,y) \<in> r \<and> x\<noteq>y},
    tail = \<lambda> (x,y). x,
    head = \<lambda> (x,y). y
    |)"

lemma rel_to_digraph_is_dir_bipartite:
  assumes "r \<subseteq>  A \<times> A"
  shows  "dir_bipartite_digraph (relation_to_digraph A r) (Inl ` A) (Inr ` A)"
proof(unfold dir_bipartite_digraph_def, rule conjI )
  show "bipartite_digraph (relation_to_digraph A r) (Inl ` A) (Inr ` A)"
  proof(unfold bipartite_digraph_def, intro conjI)
    show "Inl ` A \<union> Inr ` A = verts (relation_to_digraph A r)"
      by (unfold relation_to_digraph_def, auto)
    show "Inl ` A \<inter> Inr ` A = {}"
      by auto
    show "(\<forall>e \<in> arcs (relation_to_digraph A r).
          (tail (relation_to_digraph A r) e \<in> Inl ` A) =
          (head (relation_to_digraph A r) e \<in>  Inr ` A))" 
    proof
      fix e
      assume Hip: "e \<in> arcs (relation_to_digraph A r)" 
      show "(tail (relation_to_digraph A r) e \<in> Inl ` A) =
            (head (relation_to_digraph A r) e \<in> Inr ` A)"
      proof-
        from Hip obtain x y where e: "e = (Inl x, Inr y) \<and> (x,y) \<in> r"
          by(unfold relation_to_digraph_def, auto) 
        hence Hip1: "e =  ((Inl x), (Inr y)) \<and> (x,y) \<in> r "  
          by auto
        hence Hip2: "(Inl x) = tail (relation_to_digraph A r) e 
                    \<and> (Inr y) = head (relation_to_digraph A r) e \<and> x\<in> A \<and> y\<in> A"                    
          using assms by(unfold relation_to_digraph_def, auto)
        hence  "x\<in> A \<and> y\<in> A" by auto
        hence  "(Inl x) \<in> Inl ` A \<and> (Inr y) \<in>  Inr ` A "       
          by auto    
        hence "(tail (relation_to_digraph A r) e \<in> Inl ` A) \<and>
                 (head (relation_to_digraph A r) e \<in>  Inr ` A)"
          using Hip1 e by(unfold relation_to_digraph_def, auto)
        thus "(tail (relation_to_digraph A r) e \<in> Inl ` A) =
              (head (relation_to_digraph A r) e \<in>  Inr ` A)"
          by auto
      qed
    qed
  qed
next
  show  "tails (relation_to_digraph A r) \<subseteq> Inl ` A \<and>
    (\<forall>e1\<in>arcs (relation_to_digraph A r).
        \<forall>e2\<in>arcs (relation_to_digraph A r).
           (e1 = e2) =
           (head (relation_to_digraph A r) e1 = head (relation_to_digraph A r) e2 \<and>
            tail (relation_to_digraph A r) e1 = tail (relation_to_digraph A r) e2))"
    by (smt (z3) image_eqI mem_Collect_eq prod.simps(2) relation_to_digraph_def 
        select_convs(2,3,4) subsetI tails_def)  
qed

lemma exists_min_vertex_cover:
  assumes "dir_bipartite_digraph G X Y" and "finite (X\<union>Y)"
  shows "\<exists>C. minimum_vertex_cover G (arcs G) C"
proof -
  let ?P = "{C. vertex_cover G (arcs G) C}" 
  have  "finite (verts G)"  
    by (metis assms(1,2) bipartite_digraph_def dir_bipartite_digraph_def)
  hence 1: "finite ?P"  using assms finite_Pow_iff by (simp add: vertex_cover_def)
  have  "vertex_cover G (arcs G) (verts G)" using assms(1) bipartite_digraph_def vertex_cover_def  
    by (smt (verit, del_insts) Un_iff dir_bipartite_digraph_def mem_Collect_eq subset_iff tails_def)
  hence 2: "?P \<noteq> {}" by auto
  have "\<exists>C \<in> ?P. (\<forall>C' \<in> ?P.  card C \<le> card C')" using 1 2
    by (metis \<open>vertex_cover G (arcs G) (verts G)\<close> ex_has_least_nat mem_Collect_eq)
  thus ?thesis using minimum_vertex_cover_def by auto
qed

definition roots :: "'a set \<Rightarrow> (('a + 'a) \<times> ('a + 'a)) set \<Rightarrow> 'a set" where
  "roots A M \<equiv> {x \<in> A. \<forall>y. (Inl y, Inr x) \<notin> M}"

lemma not_root_has_pred:
  assumes "x \<in> A" and "x \<notin> roots A M"
  shows "\<exists>y. (Inl y, Inr x) \<in> M"
proof -
  from assms(2)
  have "\<not> (\<forall>y. (Inl y, Inr x) \<notin> M)"
    unfolding roots_def using assms(1) by auto   
  then obtain y where "(Inl y, Inr x) \<in> M" by auto
  thus ?thesis by blast
qed

definition match_rel ::
  "(('a + 'a) \<times> ('a + 'a)) set \<Rightarrow> ('a \<times> 'a) set"
  where
    "match_rel M =
   {(x,y). (Inl x, Inr y) \<in> M}"

lemma matching_edges_strict:
  assumes "dirBD_matching (relation_to_digraph A r) (Inl ` A) (Inr ` A) M" and
    "(x, y) \<in> match_rel M"   
  shows "x \<in> A \<and> y \<in> A \<and> (x,y) \<in> r \<and> x \<noteq> y"
proof -
  have "(Inl x, Inr y) \<in> M" using assms(2) match_rel_def[of M] by auto
  moreover
  have "M \<subseteq> arcs (relation_to_digraph A r)" using  assms(1) dirBD_matching_def
    by metis
  ultimately 
  have "(Inl x, Inr y) \<in> arcs (relation_to_digraph A r)" using assms(1) relation_to_digraph_def by auto
  thus  ?thesis
    by (simp add: relation_to_digraph_def)
qed 

definition chain_from_root where
  "chain_from_root a A M =
   {x \<in> A. (a,x) \<in> (match_rel M)^*}"

lemma successor_unique:
  assumes "(x,y1) \<in> match_rel M" and "(x,y2) \<in> match_rel M"
    and "dirBD_matching (relation_to_digraph A r) (Inl ` A) (Inr ` A) M"
  shows "y1 = y2"
proof(rule ccontr)
  assume hip: "y1 \<noteq> y2" 
  have 1: "(Inl x, Inr y1) \<in>  M" using assms(1,2)  match_rel_def
    by (simp add: match_rel_def) 
  have 2: "(Inl x, Inr y2) \<in>  M" using assms(1,2)  match_rel_def
    by (simp add: match_rel_def)  
  have "(Inl x, Inr y1) \<noteq> (Inl x, Inr y2)" using hip by auto
  hence "x \<noteq> x" using dirBD_matching_def assms(3)
    by (metis (no_types, lifting) "1" "2" relation_to_digraph_def select_convs(3) split_conv) 
  thus False by auto
qed

lemma predecessor_unique:
  assumes "(x1,y) \<in> match_rel M" and "(x2,y) \<in> match_rel M"
    and "dirBD_matching (relation_to_digraph A r) (Inl ` A) (Inr ` A) M"
  shows "x1 = x2" 
proof(rule ccontr)
  assume hip: "x1 \<noteq> x2" 
  have 1: "(Inl x1, Inr y) \<in>  M" using assms(1,2)  match_rel_def
    by (simp add: match_rel_def) 
  have 2: "(Inl x1, Inr y) \<in>  M" using assms(1,2)  match_rel_def
    by (simp add: match_rel_def)  
  have "(Inl x1, Inr y) \<noteq> (Inl x2, Inr y)" using hip by auto
  hence "y \<noteq> y" using dirBD_matching_def assms(3)
    by (metis (no_types, lifting) "2" Product_Type.Collect_case_prodD assms(2) 
        fst_conv match_rel_def prod.simps(2) relation_to_digraph_def select_convs(4) snd_conv) 
  thus False by auto
qed

lemma root_unique:
  assumes
    ax: "(a,x) \<in> (match_rel M)^*" and
    bx: "(b,x) \<in> (match_rel M)^*" and
    ar: "a \<in> roots A M" and
    br: "b \<in> roots A M" and
    mt: "dirBD_matching (relation_to_digraph A r) (Inl ` A) (Inr ` A) M"
  shows "a = b"
  using ax bx ar br
proof (induction arbitrary: b rule: rtrancl_induct) 
  case base
  then show ?case
    by (metis (lifting) CollectD Product_Type.Collect_case_prodD match_rel_def roots_def 
        rtranclE split_pairs2)
next
  case (step y z)
  have bz: "(b,z) \<in> (match_rel M)^*"
    using step.prems by auto
  show ?case
  proof (cases "b = z")
    case True
    hence "(y,z) \<in> match_rel M"
      using step.hyps by auto
    hence "(y,b) \<in> match_rel M"
      using True by auto
    hence "\<exists>u. (u,b) \<in> match_rel M"
      by auto
    thus ?thesis
      using step.prems unfolding roots_def
      by (simp add: match_rel_def)
  next
    case False
    then obtain w where
      "(b,w) \<in> (match_rel M)^*"
      "(w,z) \<in> match_rel M"
      using bz by (metis rtranclE)
    moreover
    have "(y,z) \<in> match_rel M"  
      using step.hyps by auto
    ultimately have "y = w"
      by (meson mt predecessor_unique)
    thus ?thesis
      using step.IH step.prems
      using \<open>(b, w) \<in> (match_rel M)\<^sup>*\<close> by blast
  qed
qed

definition pred_rel:: "(('a + 'a) \<times> ('a + 'a)) set \<Rightarrow> 'a set \<Rightarrow> ('a \<times> 'a) set" where
  "pred_rel M A = {(x,y). (Inl x, Inr y) \<in> M \<and> x \<in> A \<and> y \<in> A }"

lemma pred_rel_subset_strict:
  assumes "dirBD_matching (relation_to_digraph A r) (Inl ` A) (Inr ` A) M"
  shows "pred_rel M A \<subseteq> r - Id"
proof
  fix p
  assume "p \<in> pred_rel M A"
  then obtain x y where
    p_def: "p = (x,y)"
    and edge: "(Inl x, Inr y) \<in> M"
    unfolding pred_rel_def
    by auto
  have "(x,y) \<in> r \<and> x \<noteq> y"  using  matching_edges_strict[of A r M x y]
    by (simp add: assms edge match_rel_def)
  thus "p \<in> r - Id"
    using p_def by auto
qed

lemma (in part_order)strict_order_wf:
  assumes "finite A"
  shows "wf (r - Id)"
proof-
  have fin_r : "finite r" using  p_o_translation partial_order_on_def[of A r] assms 
      finite_cartesian_product[of A A] finite_subset[of r "A \<times> A"] preorder_on_def[of A r]
    by (simp add: refl_on_def) 
  thus ?thesis using p_o_translation  partial_order_on_well_order_on[of r A] by auto
qed

lemma (in part_order)finite_pred_wf:
  assumes "finite A"  and
    "dirBD_matching (relation_to_digraph A r)(Inl ` A) (Inr ` A) M"
  shows "wf (pred_rel M A)"
proof -
  have "pred_rel M A \<subseteq> r - Id"
    using assms(2) pred_rel_subset_strict by blast
  moreover 
  have "wf (r - Id)"
    using strict_order_wf assms(1,2)
    by auto
  ultimately 
  show ?thesis
    using wf_subset
    by blast
qed

lemma (in part_order)exists_root_reaching:
  assumes "finite A"
    and "dirBD_matching (relation_to_digraph A r) (Inl ` A) (Inr ` A) M"
    and "x \<in> A"
  shows "\<exists>a\<in>roots A M. (a,x) \<in> (match_rel M)^*" 
proof -
  have wf_rel: "wf (pred_rel M A)"
    using finite_pred_wf assms
    by blast
  from assms(3)
  show ?thesis
  proof (induction x rule: wf_induct[OF wf_rel])
    case (1 x)
    have xA: "x \<in> A"
      using 1 by blast
    show ?case
    proof (cases "x \<in> roots A M")
      case True
      have "(x,x) \<in> (match_rel M)^*"
        by simp
      thus ?thesis
        using True by blast
    next
      case False
      from not_root_has_pred[OF xA False]
      obtain y where edge: "(Inl y, Inr x) \<in> M"
        by blast
      have yA: "y \<in> A"
        using match_rel_def matching_edges_strict  assms(2) edge by fastforce 
      have "(y,x) \<in> pred_rel M A"
        using pred_rel_def  edge xA yA
        by auto
      from 1
      obtain a where
        "a \<in> roots A M" and  "(a,y) \<in> (match_rel M)^*"
        using \<open>(y, x) \<in> pred_rel M A\<close> yA by blast  
      then have  "(a,x) \<in> (match_rel M)^*"
        using edge
        by (simp add: match_rel_def rtrancl.rtrancl_into_rtrancl)
      thus ?thesis
        using \<open>a \<in> roots A M\<close>
        by blast
    qed
  qed
qed

(* The reflexive-transitive closure of functional relations  *)
lemma single_valued_rfl_trnstv_closure :
  assumes "single_valued r" 
    and   "(a,x) \<in> r^*"
    and   "(a,y) \<in> r^*"
  shows   "x = y \<or> (x,y) \<in> r^* \<or> (y,x) \<in> r^*" 
  using assms single_valued_confluent[of r a x y] by auto

(* This lemma is available in the HOL/transitive closure theory
   where such functional relations are called single_valued. *)
lemma functional_rtrancl_linear:
  assumes
    func: "\<And>x y1 y2. (x,y1) \<in> r \<Longrightarrow> (x,y2) \<in> r \<Longrightarrow> y1 = y2"
    and ax: "(a,x) \<in> r^*"
    and ay: "(a,y) \<in> r^*"
  shows "x = y \<or> (x,y) \<in> r^* \<or> (y,x) \<in> r^*"
  using ay
proof (induction rule: rtrancl_induct)  
  case base
  then show ?case
    using ax by auto
next
  case (step  y z)
  then show ?case
    by (metis converse_rtranclE func rtrancl.rtrancl_into_rtrancl rtrancl.rtrancl_refl)
qed

lemma reachable_linear_from_root:
  assumes
    "(a,x) \<in> (match_rel M)^*" and
    "(a,y) \<in> (match_rel M)^*" and
    "dirBD_matching (relation_to_digraph A r) (Inl ` A) (Inr ` A) M"
  shows
    "x = y \<or> (x,y) \<in> (match_rel M)^* \<or> (y,x) \<in> (match_rel M)^*"
  by (meson assms(1,2,3) functional_rtrancl_linear successor_unique) 

lemma match_rel_subset_r:
  assumes "dirBD_matching (relation_to_digraph A r) (Inl ` A) (Inr ` A) M"
  shows "match_rel M \<subseteq> r"
proof
  fix p
  assume "p \<in> match_rel M"
  hence "\<exists>x.\<exists>y. p = (x,y) \<and>(x,y) \<in> match_rel M"
    by (metis surj_pair)
  then obtain x y where  p:  "p = (x,y)" and   "(x,y) \<in> match_rel M" by auto
  hence 1: "(Inl x, Inr y) \<in> M" unfolding match_rel_def by auto
  hence  "(Inl x, Inr y) \<in> arcs (relation_to_digraph A r)"
    using assms dirBD_matching_def by fastforce 
  hence  "(x,y) \<in> r"  unfolding relation_to_digraph_def
    by auto
  thus "p \<in> r " using p by auto
qed

definition chain_decomposition_order :: "'a set \<Rightarrow> 'a rel \<Rightarrow> (('a + 'a) \<times> ('a + 'a)) set  \<Rightarrow> 'a set set"
  where
    "chain_decomposition_order A r M =
   {chain_from_root a A M |a. a \<in> (roots A M)}"    

lemma match_rel_not_empty: "a \<in> A \<longrightarrow> (a,a) \<in> (match_rel M)^*"
  by blast 

context part_order
begin
lemma match_rel_rtrancl_in_r:
  assumes
    "dirBD_matching (relation_to_digraph A r) (Inl ` A) (Inr ` A) M"
    and "a\<in>A"  and "(a,x) \<in> (match_rel M)^*" 
  shows "(a,x) \<in> r"
  using assms(3)
proof (induction rule: rtrancl_induct)
  case base
  then show ?case using assms(1)
    by (meson assms(2) p_o_translation partial_order_onD(1) refl_onD)
next
  case (step y z)
  then have "(y,z) \<in> r"
    using step.prems
    using assms(1) match_rel_subset_r
    by blast 
  moreover have "(a,y) \<in> r"
    using step.IH by auto
  ultimately show ?case
    using assms
    by (metis p_o_translation partial_order_onD(2) transD)
qed

lemma reachable_comparable:
  assumes
    "(a,x) \<in> (match_rel M)^*" and
    "(a,y) \<in> (match_rel M)^*" and
    "dirBD_matching (relation_to_digraph A r) (Inl ` A) (Inr ` A) M" and
    "a\<in>A"
  shows
    "(x,y) \<in> r \<or> (y,x) \<in> r" 
proof -
  have sub: "match_rel M \<subseteq> r"
    using  match_rel_subset_r assms(4)
    using assms(3) by blast 
  have axr: "(a,x) \<in> r"
    by (meson assms(1,3,4) part_order.match_rel_rtrancl_in_r part_order_axioms)  
  have ayr: "(a,y) \<in> r"
    by (meson assms(2,3,4) part_order.match_rel_rtrancl_in_r part_order_axioms)
  from axr ayr
  show ?thesis 
    by (smt (verit, best) assms(1,2,3,4) match_rel_rtrancl_in_r matching_edges_strict
        reachable_linear_from_root rtrancl.simps)
qed

lemma chain_from_root_is_chain:
  assumes
    "finite A" and
    "dirBD_matching (relation_to_digraph A r) (Inl ` A) (Inr ` A) M" and  "a \<in> A"
  shows "chain (chain_from_root a A M) A r"
proof -
  have subset:
    "chain_from_root a A M \<subseteq> A"
    by (simp add: chain_from_root_def)
  moreover
  have total: "total_on (chain_from_root a A M) r"
  proof
    fix x y
    assume
      "x \<in> chain_from_root a A M" and "y \<in> chain_from_root a A M"
    hence "(a,x) \<in> (match_rel M)^*" and "(a,y) \<in> (match_rel M)^*" and "x \<in> A" and  "y \<in> A"
      unfolding chain_from_root_def by auto
    thus "(x,y) \<in> r \<or> (y,x) \<in> r"
      using reachable_comparable assms  by metis
  qed
  ultimately
  show ?thesis 
    using chain_def assms
    using p_o_translation by blast
qed

lemma chain_decomposition_cover:
  assumes
    "finite A" 
    "dirBD_matching (relation_to_digraph A r) (Inl ` A) (Inr ` A) M"
  shows
    "\<Union> (chain_decomposition_order A r M) = A"
proof
  show  "\<Union> (chain_decomposition_order A r M) \<subseteq> A"
    unfolding chain_from_root_def
    by (smt (verit, ccfv_SIG) Union_least chain_decomposition_order_def 
        chain_from_root_def mem_Collect_eq subsetI)
next
  show "A \<subseteq> \<Union> (chain_decomposition_order A r M)"
  proof
    fix x
    assume hip:"x \<in> A"
    obtain a where
      a1:  "a \<in> roots A M" and
      a2:  "(a,x) \<in> (match_rel M)^*"
      using exists_root_reaching assms `x \<in> A`
      by metis
    hence  "(a,x) \<in> (match_rel M)^*" using a1 a2
      by blast 
    thus "x \<in> \<Union> (chain_decomposition_order A r M)"
      by (smt (verit, del_insts) Union_iff \<open>x \<in> A\<close> a1 chain_decomposition_order_def
          chain_from_root_def mem_Collect_eq) 
  qed
qed

lemma chain_decomposition_disjoint:
  assumes  "finite A" and  "dirBD_matching (relation_to_digraph A r) (Inl ` A) (Inr ` A) M"
  shows "disjoint (chain_decomposition_order A r M)"
  unfolding disjoint_def
proof (intro ballI impI)
  fix c1 c2 
  assume "c1 \<in> chain_decomposition_order A r M" 
    and "c2 \<in> chain_decomposition_order A r M"
    and "c1 \<noteq> c2"
  show "c1 \<inter> c2 = {}" 
  proof(rule ccontr)
    assume hip:  "c1 \<inter> c2 \<noteq> {}"
    obtain a b where a: "c1 = chain_from_root a A M" "a \<in> roots A M"
      and b: "c2 = chain_from_root b A M" "b \<in> roots A M"
      by (smt (verit, ccfv_SIG) \<open>c1 \<in> chain_decomposition_order A r M\<close> 
          \<open>c2 \<in> chain_decomposition_order A r M\<close> chain_decomposition_order_def
          mem_Collect_eq)
    have "\<exists>x. (x \<in> chain_from_root a A M) \<and> (x \<in> chain_from_root a A M)" using hip a b by auto
    then obtain x where x: "(x \<in> chain_from_root a A M) \<and> (x \<in> chain_from_root a A M)" by auto
    hence "(x \<in> A \<and> (a,x) \<in> (match_rel M)^*) \<and> (x \<in> A \<and>(b,x) \<in> (match_rel M)^*)" 
      using  chain_from_root_def
      by (smt (verit) a(1,2) assms(2) b(1,2) disjoint_iff hip mem_Collect_eq part_order.p_o_translation part_order_axioms
          root_unique)
    hence "a=b"
      by (meson a(2) assms(2) b(2) part_order.p_o_translation part_order_axioms root_unique)
    thus False
      using \<open>c1 \<noteq> c2\<close> a(1) b(1) by blast  
  qed
qed

lemma chain_decomposition_non_empty:
  assumes "roots A M \<noteq> {}" and
    "dirBD_matching (relation_to_digraph A r) (Inl ` A) (Inr ` A) M" 
  shows "{} \<notin> chain_decomposition_order A r M"
  using chain_decomposition_order_def chain_from_root_def match_rel_not_empty
  by (smt (verit) equals0D mem_Collect_eq roots_def)

lemma chain_decomposition_partition:
  assumes "r \<subseteq> A \<times> A"  and
    "dirBD_matching (relation_to_digraph A r) (Inl ` A) (Inr ` A) M"
    and "finite A"
  shows "partition_on A (chain_decomposition_order A r M)"
  using partition_on_def[of A "chain_decomposition_order A r M"]
proof
  have 1: "\<Union> (chain_decomposition_order A r M) = A"
    using assms chain_decomposition_cover by blast
  moreover
  have 2: "disjoint (chain_decomposition_order A r M)"
    using assms chain_decomposition_disjoint by auto
  moreover
  have 3: "{} \<notin> chain_decomposition_order A r M"
    using assms chain_decomposition_non_empty
    by (smt (verit, best) chain_decomposition_order_def emptyE mem_Collect_eq) 
  ultimately
  show ?thesis using partition_on_def  by auto
qed

lemma exist_chain_decomposition: 
  assumes "r \<subseteq> A \<times> A"  and
    "dirBD_matching (relation_to_digraph A r) (Inl ` A) (Inr ` A) M"
    and "finite A"
  shows "chain_decomposition A r (chain_decomposition_order A r M)"
proof-
  have "partition_on A (chain_decomposition_order A r M)"
    using assms chain_decomposition_partition by auto
  moreover
  have "\<forall>B\<in>chain_decomposition_order A r M. chain B A r "
  proof
    fix B 
    assume "B\<in>chain_decomposition_order A r M"
    thus "chain B A r" using assms  chain_from_root_is_chain
      by (smt (verit) chain_decomposition_order_def mem_Collect_eq p_o_translation roots_def)
  qed
  ultimately  show ?thesis
    using chain_decomposition_def by blast
qed
end (* ctxt part_order *)

lemma max_card_in_set:
  fixes M :: "'a set set"
  assumes "finite M" and "M \<noteq> {}"
  shows "\<exists>m \<in> M. \<forall>m' \<in> M. card m' \<le> card m"
  by (metis Max_ge assms(1,2) finite_imageI image_eqI obtains_MAX) 

lemma maximum_matching_digraph:
  assumes "dir_bipartite_digraph G X Y" and "finite (arcs G)"
  shows "\<exists>M. maximum_dirBD_matching G X Y M" 
proof-
  let ?M = "{M. dirBD_matching G X Y M}"
  have a: "\<forall>M\<in>?M.finite M" using dirBD_matching_def
    by (metis assms(2) mem_Collect_eq rev_finite_subset)
  have 1: "finite ?M"
  proof -
    have "?M \<subseteq> Pow (arcs G)"
      using  dirBD_matching_def by fastforce 
    thus "finite ?M" by (simp add: assms(2) finite_subset) 
  qed
  have 2: "{} \<in> ?M" 
    unfolding dirBD_matching_def using assms(1) by fastforce 
  have "\<exists>M\<in>?M. (\<forall>M'\<in>?M. card M' \<le> card M)" using a 1 2
    by (metis equals0D max_card_in_set) 
  thus ?thesis
    by (simp add: maximum_dirBD_matching_def)
qed

lemma chain_from_root_inj:
  assumes
    "dirBD_matching (relation_to_digraph A r) (Inl ` A) (Inr ` A) M"
  shows
    "inj_on (\<lambda>a. chain_from_root a A M) (roots A M)"
proof -
  have "\<And>a b.
    a \<in> roots A M \<Longrightarrow>
    b \<in> roots A M \<Longrightarrow>
    chain_from_root a A M = chain_from_root b A M \<Longrightarrow>
    a = b"
  proof -
    fix a b
    assume
      "a \<in> roots A M" and
      "b \<in> roots A M" and
      "chain_from_root a A M = chain_from_root b A M"
    then have "a \<in> chain_from_root b A M"
      unfolding chain_from_root_def
      by (metis (lifting) match_rel_not_empty mem_Collect_eq roots_def)
    then have "(b,a) \<in> (match_rel M)^*"
      unfolding chain_from_root_def by auto
    moreover
    have "(a,a) \<in> (match_rel M)^*"
      by auto
    ultimately show "a = b"
      by (metis (lifting) CollectD Product_Type.Collect_case_prodD
          \<open>a \<in> roots A M\<close> match_rel_def roots_def rtrancl.cases snd_conv)
  qed
  thus ?thesis
    unfolding inj_on_def by auto
qed

lemma chain_decomposition_as_image:
  "chain_decomposition_order A r M = (\<lambda>a. chain_from_root a A M) ` roots A M"
  by (simp add: chain_decomposition_order_def setcompr_eq_image)

lemma card_chain_decomposition:
  assumes
    "dirBD_matching (relation_to_digraph A r) (Inl ` A) (Inr ` A) M" and  "finite (roots A M)"
  shows
    "card (chain_from_root ` roots A M) = card (roots A M)"
  by (metis (no_types, lifting) assms(1) card_image chain_from_root_inj inj_on_def)

fun  f_match_rel :: "('a \<times> 'a) \<Rightarrow> (('a + 'a) \<times> ('a + 'a))"
  where 
    "f_match_rel (x,y) = (Inl x, Inr y)"

lemma inj_match_rel:
  assumes  "dirBD_matching (relation_to_digraph A r) (Inl ` A) (Inr ` A) M"
  shows "inj f_match_rel"
  by (unfold inj_def, auto)

lemma surj_match_rel:
  assumes  "dirBD_matching (relation_to_digraph A r) (Inl ` A) (Inr ` A) M"
  shows "(\<forall>z.\<forall> w. (z,w) \<in> M \<longrightarrow> (\<exists>x.\<exists>y. (x,y) \<in> match_rel M \<and> (Inl x, Inr y)=(z,w)))"
proof (intro allI impI)
  fix z w 
  assume hip: "(z, w) \<in> M" 
  show "\<exists>x y. (x, y) \<in> match_rel M \<and> (Inl x, Inr y) = (z, w)"
  proof-
    have  "(\<exists>x.\<exists>y. (x,y) \<in> r \<and> x \<in> A \<and> y \<in> A \<and> x\<noteq>y \<and> (Inl x, Inr y) = (z,w))" 
      using hip
      by (smt (verit, del_insts) assms dirBD_matching_def mem_Collect_eq 
          relation_to_digraph_def select_convs(2) subset_iff)
    then obtain x y  where "(x,y) \<in> r \<and> x \<in> A \<and> y \<in> A \<and> x\<noteq>y \<and> (Inl x, Inr y) = (z,w)" by auto
    hence "(Inl x, Inr y)\<in> M  \<and> (Inl x, Inr y) = (z,w) " using hip  match_rel_def
      using hip by fastforce 
    hence "(x, y) \<in> match_rel M \<and> (Inl x, Inr y) = (z, w)" using match_rel_def by auto
    thus ?thesis by blast
  qed
qed

lemma surj_match_rel1:
  assumes  "dirBD_matching (relation_to_digraph A r) (Inl ` A) (Inr ` A) M"
  shows "f_match_rel`match_rel M = M"
proof
  show "f_match_rel ` match_rel M \<subseteq> M"
  proof
    fix X
    assume "X \<in> f_match_rel ` match_rel M"
    hence "\<exists>z.\<exists>w. X = (Inl z, Inr w)  \<and>  (Inl z, Inr w)\<in> f_match_rel ` match_rel M"
      using image_iff by fastforce 
    then  obtain z w where *: "X = (Inl z, Inr w)  \<and>  (Inl z, Inr w) \<in> f_match_rel ` match_rel M" by auto
    hence "(z,w) \<in>  match_rel M"   by fastforce
    hence  "(Inl z, Inr w)\<in> M"
      by (simp add: match_rel_def) 
    thus "X \<in> M" using * by auto
  qed
next
  show "M \<subseteq> f_match_rel ` match_rel M"
  proof
    fix X
    assume "X \<in> M" 
    hence "\<exists>z.\<exists>w. X = (Inl z, Inr w)  \<and>  (Inl z, Inr w) \<in> M" using assms
      by (metis f_match_rel.cases surj_match_rel)
    then obtain z w where  "X = (Inl z, Inr w)  \<and>  (Inl z, Inr w) \<in> M" by auto
    hence "(z,w) \<in>  match_rel M \<and> X = (Inl z, Inr w)  \<and>  (Inl z, Inr w) \<in> M"
      by (simp add: match_rel_def)
    thus "X \<in> f_match_rel ` match_rel M"
      by force
  qed
qed

lemma card_match_rel_eq:
  assumes  "dirBD_matching (relation_to_digraph A r) (Inl ` A) (Inr ` A) M" and "finite M" 
    and "finite (match_rel M)"
  shows "card (match_rel M) = card M"
proof -
  have "inj f_match_rel"
    using assms(1) inj_match_rel by blast
  moreover
  have "f_match_rel ` match_rel M = M"
    using surj_match_rel1 assms by blast
  ultimately show ?thesis
    by (metis card_image inj_on_subset subset_UNIV)
qed

definition has_pred:: "'a set \<Rightarrow>(('a + 'a) \<times> ('a + 'a)) set \<Rightarrow> 'a set" where
  "has_pred A M  =  {x\<in>A. (\<exists>y. (y,x) \<in> match_rel M )}"

lemma roots_partition:
  "roots A M = A - has_pred A M"
  unfolding roots_def has_pred_def
  by (smt (z3) Collect_cong DiffD2 DiffI Diff_subset case_prodE case_prodI f_match_rel.simps 
      match_rel_def mem_Collect_eq minus_set_def subset_eq)

lemma disjoint_roots_pred:
  "roots A M \<inter> has_pred A M = {}"
  unfolding roots_def has_pred_def
  by (simp add: disjoint_iff match_rel_def)

lemma union_roots_pred:
  "roots A M \<union> has_pred A M = A"
  using roots_partition disjoint_roots_pred
  by (simp add: Collect_conj_eq has_pred_def roots_partition)

lemma card_partition:
  assumes "finite A" 
  shows "card A = card (roots A M) + card (has_pred A M)" 
  using disjoint_roots_pred union_roots_pred 
  by (metis assms card_Un_disjoint disjoint_roots_pred finite_Un union_roots_pred)

lemma has_pred_image:
  assumes "dirBD_matching (relation_to_digraph A r) (Inl ` A) (Inr ` A) M"
  shows "has_pred A M = snd ` (match_rel M)"
  unfolding has_pred_def
  by (smt (verit, best) Collect_cong Range.RangeI RangeE assms(1) image_def matching_edges_strict mem_Collect_eq
      snd_eq_Range)

lemma inj_snd_match_rel:
  assumes
    "dirBD_matching (relation_to_digraph A r) (Inl ` A) (Inr ` A) M"
  shows "inj_on snd (match_rel M)"
  using assms
  unfolding dirBD_matching_def match_rel_def inj_on_def
  by (metis (lifting) Product_Type.Collect_case_prodD assms 
      predecessor_unique split_pairs2 sum.inject(1,2) surj_match_rel) 

lemma card_has_pred:
  assumes
    "dirBD_matching (relation_to_digraph A r) (Inl ` A) (Inr ` A) M" and "finite (match_rel M)"
  shows "card (has_pred A M) = card (match_rel M)" 
  using assms has_pred_image inj_snd_match_rel card_image by metis

lemma card_roots:
  assumes
    "dirBD_matching (relation_to_digraph A r) (Inl ` A) (Inr ` A) M" and "finite A"
    and "finite M" and "finite (match_rel M)"
  shows
    "card (roots A M) = card A - card M"
proof -
  have "card A = card (roots A M) + card (has_pred A M)"
    using card_partition assms by auto
  moreover
  have "card (has_pred A M) = card (match_rel M)"
    using card_has_pred assms by blast
  moreover
  have "card (match_rel M) = card M"
    using card_match_rel_eq assms by blast
  ultimately show ?thesis by simp
qed

lemma finite_arcs:  
  assumes  "finite A" and "r \<subseteq>  A \<times> A"
  shows "finite (arcs (relation_to_digraph A r))"
proof-
  have "finite r"
    using assms(1,2) finite_subset by blast
  thus ?thesis using relation_to_digraph_def[of A r]
    by (smt (verit, ccfv_SIG) InlI InrI SigmaI assms(1) finite_Plus_iff finite_cartesian_product
        mem_Collect_eq rev_finite_subset select_convs(2) subrelI)
qed

lemma finite_verts: 
  assumes  "finite A"
  shows "finite (verts (relation_to_digraph A r))"
  using relation_to_digraph_def assms
  by (smt (verit) finite_Plus_iff select_convs(1)) 

lemma  finite_matching:
  assumes
    "r \<subseteq> A \<times> A" and
    "dirBD_matching (relation_to_digraph A r) (Inl ` A) (Inr ` A) M" and  "finite A" 
  shows "finite M" using assms dirBD_matching_def finite_arcs
  by (metis finite_subset)

lemma (in part_order)chain_decomposition_cardinality:
  assumes
    "dirBD_matching (relation_to_digraph A r) (Inl ` A) (Inr ` A) M" and "finite A" 
  shows
    "card (chain_decomposition_order A r M) = card A - card M"
proof -
  have "chain_decomposition_order A r M =
  (\<lambda>a. chain_from_root a A M) ` roots A M"
    using chain_decomposition_as_image by blast
  moreover
  have "card (chain_from_root ` roots A M)
        = card (roots A M)"
  proof -
    have "finite (roots A M)"
      using assms
      by (simp add: roots_def)
    moreover
    have "inj_on (\<lambda>a. chain_from_root a A M) (roots A M)"
      using chain_from_root_inj assms by blast
    ultimately show ?thesis
      by (simp add: card_image inj_on_def)
  qed
  moreover
  have "card (roots A M) = card A - card M"  
    using card_roots assms finite_matching  finite_cartesian_product match_rel_subset_r p_o_translation partial_order_onD(4) rev_finite_subset
    by meson
  ultimately show ?thesis
    by (metis assms(1) card_image chain_from_root_inj)
qed

lemma cover_minimum:
  assumes "minimum_vertex_cover G E C" and "finite C"
  shows "\<forall>c\<in>C.\<exists>e\<in>E. c = (head G e) \<or> c = (tail G e)"
proof(rule ccontr)
  assume "\<not>(\<forall>c\<in>C. \<exists>e\<in>E. c = (head G e) \<or> c = (tail G e))"
  hence "\<exists>c\<in>C. \<forall>e\<in>E. c \<noteq> (head G e) \<and> c \<noteq> (tail G e)" by auto
  then obtain c where c1: "c\<in>C" and  c2: "\<forall>e\<in>E. c \<noteq> (head G e) \<and> c \<noteq> (tail G e)" by auto
  have *: "vertex_cover G E (C-{c})"
  proof-
    have "C - {c} \<subseteq> verts G" 
      using assms minimum_vertex_cover_def  vertex_cover_def
      by (metis c1 insert_Diff insert_subset)
    moreover
    have "E \<subseteq> arcs G" using assms minimum_vertex_cover_def  vertex_cover_def
      by metis 
    moreover
    have  "(\<forall>e\<in>E. head G e \<in> C - {c} \<or> tail G e \<in> C - {c})" using c1 c2
      by (metis assms(1) insert_Diff insert_iff minimum_vertex_cover_def vertex_cover_def)
    ultimately
    show ?thesis using vertex_cover_def by blast
  qed
  have  "card (C - {c}) < card C" using c1 assms(2)
    by (metis card_Diff1_less)
  thus False using * assms(1) minimum_vertex_cover_def
    using leD by blast
qed

context part_order
begin
lemma vertex_cover_reduction:
  assumes "(\<forall>e\<in>arcs (relation_to_digraph A r).
            head (relation_to_digraph A r) e \<in> C \<or>
            tail (relation_to_digraph A r) e \<in> C )"
    and "Inl x \<in> C" and "Inr x \<in> C"
  shows "(\<forall>e\<in>arcs (relation_to_digraph A r).
        head (relation_to_digraph A r) e \<in> C - {Inr x} \<or>
        tail (relation_to_digraph A r) e \<in> C - {Inr x}) \<or>
         (\<forall>e\<in>arcs (relation_to_digraph A r).
        head (relation_to_digraph A r) e \<in> C - {Inl x} \<or>
        tail (relation_to_digraph A r) e \<in> C - {Inl x})"
proof(rule ccontr)
  let ?G = "relation_to_digraph A r"
  let ?E = "arcs ?G"
  assume  
    "\<not>((\<forall>e\<in>?E.
     head ?G e \<in> C - {Inr x} \<or>
     tail ?G e \<in> C - {Inr x}) \<or>
     (\<forall>e\<in>?E.
      head ?G e \<in> C - {Inl x} \<or>
      tail ?G e \<in> C - {Inl x}))" 
  hence h: "\<not>(\<forall>e\<in>?E.
             head ?G e \<in> C - {Inr x} \<or>
             tail ?G e \<in> C - {Inr x})" and
    h0: "\<not> (\<forall>e\<in>?E.
             head ?G e \<in> C - {Inl x} \<or>
             tail ?G e \<in> C - {Inl x})" by auto
  from h have "\<exists>y.\<exists>z.\<exists>e. e = (Inl y, Inr z) \<and> (head ?G e \<notin> C - {Inr x} \<and>
            tail ?G e \<notin> C - {Inl x})" 
    by (metis (no_types, lifting) Diff_iff insertI1 old.prod.case relation_to_digraph_def select_convs(3,4))   
  then obtain y z e where e: "e\<in>?E \<and> e = (Inl y, Inr z)" and h: "head ?G e \<notin> C - {Inr x}" and 
    t:  "tail ?G e \<notin> C - {Inr x}"
    by (smt (verit, ccfv_threshold) mem_Collect_eq h relation_to_digraph_def
        select_convs(2)) 
  hence 1: "e\<in>?E \<and> e = (Inl y, Inr z) \<and> head ?G e =  Inr z \<and> tail ?G e =  Inl y \<and> 
         head ?G e \<notin> C - {Inr x} \<and> tail ?G e \<notin> C - {Inr x}"
    using e relation_to_digraph_def[of A r]  by auto
  hence *: "e = (Inl y, Inr z) \<and> (Inr z) \<notin> C - {Inr x} \<and> (Inl y) \<notin> C - {Inr x}" 
    using e h t by auto
  hence a: "(y,z)\<in>r \<and> y\<noteq>z" using relation_to_digraph_def[of A r]
    using e by auto 
  have  "(Inl y) \<noteq> (Inr x)" by auto
  hence b: "(Inl y) \<notin> C"  using  * by auto
  have "\<exists>c\<in>C. c = Inl y \<or> c =  Inr z" using e  assms(1) 1
    by auto
  then obtain c where c: "c \<in> C \<and> (c = Inl y \<or> c =  Inr z)" by auto
  hence "Inr z = Inr x " using *  by auto
  hence h1: "(y,x)\<in>r \<and> y\<noteq>x " using a by auto
  from h0 have "\<exists>y1.\<exists>z1.\<exists>e. e = (Inl y1, Inr z1) \<and> (head ?G e \<notin> C - {Inl x} \<and>
            tail ?G e \<notin> C - {Inl x})"
    by (smt (verit, best) mem_Collect_eq relation_to_digraph_def select_convs(2))   
  then obtain y1 z1 e where e: "e\<in>?E \<and> e = (Inl y1, Inr z1)" and h: "head ?G e \<notin> C - {Inl x}" and 
    t:  "tail ?G e \<notin> C - {Inl x}"
    by (smt (verit, best) CollectD h0 relation_to_digraph_def select_convs(2)) 
  hence 2: "e\<in>?E \<and> e = (Inl y1, Inr z1) \<and> head ?G e =  Inr z1 \<and> tail ?G e =  Inl y1 \<and> 
         head ?G e \<notin> C - {Inl x} \<and> tail ?G e \<notin> C - {Inl x}"
    using e relation_to_digraph_def[of A r]  by auto
  hence **: "e = (Inl y1, Inr z1) \<and> (Inr z1) \<notin> C - {Inl x} \<and> (Inl y1) \<notin> C - {Inl x}" 
    using e h t by auto
  hence a1: "(y1,z1)\<in>r \<and> y1\<noteq>z1" using relation_to_digraph_def[of A r]
    using e by auto 
  have  "(Inr z1) \<noteq> (Inl x)" by auto
  hence b1: "(Inr z1) \<notin> C"  using  ** by auto
  have "\<exists>c\<in>C. c = Inl y1 \<or> c =  Inr z1" using 2 assms(1) by auto
  then obtain c where c: "c \<in> C \<and> (c = Inl y1 \<or> c =  Inr z1)" by auto
  hence "Inl y1  = Inl x " using ** by auto
  hence h2: "(x,z1)\<in>r \<and> z1\<noteq>x " using a1 by auto
  hence "(y,z1)\<in>r \<and> y\<noteq>z1" using h0
    by (metis antisymD h1 p_o_translation partial_order_onD(2,3) transD)
  hence  "(Inl y, Inr z1)\<in>?E" 
    by (smt (verit) "1" e mem_Collect_eq prod.inject relation_to_digraph_def select_convs(2)
        sum.inject(1,2))
  thus False using b b1 assms(1)
    by (metis (no_types, lifting) prod.simps(2) relation_to_digraph_def select_convs(3,4))
qed

lemma vertex_cover_subset:
  assumes "vertex_cover (relation_to_digraph A r) (arcs (relation_to_digraph A r)) C"
    and "Inl x \<in> C \<and> Inr x \<in> C"
  shows "vertex_cover (relation_to_digraph A r) (arcs (relation_to_digraph A r)) (C-{Inl x})
       \<or> vertex_cover (relation_to_digraph A r) (arcs (relation_to_digraph A r)) (C-{Inr x})"
proof(rule disjE)
  let ?G = "relation_to_digraph A r"
  let ?E = "arcs ?G"
  show "(\<forall>e\<in>?E.
     head ?G e \<in> C - {Inr x} \<or>
     tail ?G e \<in> C - {Inr x}) \<or>
      (\<forall>e\<in>?E.
      head ?G e \<in> C - {Inl x} \<or>
      tail ?G e \<in> C - {Inl x})" using assms vertex_cover_def  vertex_cover_reduction
    by (metis (no_types, lifting)) 
next
  let ?G = "relation_to_digraph A r"
  let ?E = "arcs ?G"
  assume h: "(\<forall>e\<in>?E.head ?G e \<in> C - {Inr x} \<or> tail ?G e \<in> C - {Inr x})"
  have "vertex_cover (relation_to_digraph A r) (arcs (relation_to_digraph A r)) (C - {Inr x})"
  proof-
    have  "C - {Inr x} \<subseteq> verts (relation_to_digraph A r)" 
      using assms(1) vertex_cover_def
      by (metis assms(2) insert_Diff insert_subset)
    thus ?thesis using h vertex_cover_def
      by blast
  qed
  thus ?thesis by auto
next
  let ?G = "relation_to_digraph A r"
  let ?E = "arcs ?G"
  assume h: "(\<forall>e\<in>?E.head ?G e \<in> C - {Inl x} \<or> tail ?G e \<in> C - {Inl x})"
  have "vertex_cover (relation_to_digraph A r) (arcs (relation_to_digraph A r)) (C - {Inl x})"
  proof-
    have  "C - {Inl x} \<subseteq> verts (relation_to_digraph A r)" 
      using assms(1) vertex_cover_def
      by (metis assms(2) insert_Diff insert_subset)
    thus ?thesis using h vertex_cover_def
      by blast
  qed
  thus ?thesis by auto
qed

lemma matching_vertex_cover:
  assumes "minimum_vertex_cover (relation_to_digraph A r) (arcs (relation_to_digraph A r)) C"
    and "finite A"
  shows "Inl x\<notin>C \<or> Inr x\<notin>C"
proof(rule ccontr)
  assume h: "\<not> (Inl x \<notin> C \<or> Inr x \<notin> C)" 
  hence "vertex_cover (relation_to_digraph A r) (arcs (relation_to_digraph A r)) (C-{Inl x})
         \<or> vertex_cover (relation_to_digraph A r) (arcs (relation_to_digraph A r)) (C-{Inr x})"
    using vertex_cover_subset by (metis assms(1) minimum_vertex_cover_def) 
  thus False using assms(2) minimum_vertex_cover_def h
    by (metis assms(1) card_Diff1_less diff_shunt_var finite.emptyI finite_Diff2 
        finite_verts leD vertex_cover_def) 
qed

lemma L_R_disjoint:
  assumes "minimum_vertex_cover (relation_to_digraph A r) (arcs (relation_to_digraph A r)) C"
    and "finite A"
  shows "{x\<in>A. Inl x \<in> C} \<inter> {x\<in>A. Inr x \<in> C} = {}" using  matching_vertex_cover assms(1,2)
  using assms(2) by fastforce

lemma card_projection:
  assumes "minimum_vertex_cover (relation_to_digraph A r) (arcs (relation_to_digraph A r)) C" and
    "finite A"   
  shows
    "card {x\<in>A. Inl x \<in> C \<or> Inr x \<in> C} = card C"
proof -
  have "Inl ` A \<inter> Inr ` A = {}" by auto
  let ?L = "{x\<in>A. Inl x \<in> C}"
  let ?R = "{x\<in>A. Inr x \<in> C}"
  have d: "?L \<inter> ?R = {}" 
    using assms(1,2) matching_vertex_cover by fastforce 
  have S_def:
    "{x\<in>A. Inl x \<in> C \<or> Inr x \<in> C} = ?L \<union> ?R" by auto
  have "?L \<inter> ?R = {}" using L_R_disjoint by (simp add: d)
  moreover
  have fin1: "finite ?L" and fin2:"finite ?R"   
    using assms by auto
  ultimately
  have "card (?L \<union> ?R) = card ?L + card ?R"
    by (meson card_Un_disjoint) 
  moreover
  have "card C = card ?L + card ?R"
  proof -
    have  "C \<subseteq> Inl ` A \<union> Inr ` A" using vertex_cover_def
      by (metis (no_types, lifting) Plus_def assms(1) minimum_vertex_cover_def relation_to_digraph_def select_convs(1))
    hence "C = Inl ` ?L \<union> Inr ` ?R"  by auto
    moreover
    have "Inl ` ?L \<inter> Inr ` ?R = {}" by auto
    moreover
    have "inj_on Inl ?L" and "inj_on Inr ?R" by auto
    ultimately show ?thesis using fin1 fin2
      by (metis (no_types, lifting) card_Un_disjoint card_image finite_imageI)
  qed
  thus ?thesis
    using S_def calculation by argo
qed

lemma cover_antichain:
  assumes  "minimum_vertex_cover (relation_to_digraph A r) (arcs  (relation_to_digraph A r)) C" and 
    "finite A"
  shows "anti_chain A r {x \<in> A. Inl x \<notin> C \<and> Inr x \<notin> C} \<and>
       card {x \<in> A. Inl x \<notin> C \<and> Inr x \<notin> C} = card A - card C"
proof(rule conjI)
  show "anti_chain A r {x \<in> A. Inl x \<notin> C \<and> Inr x \<notin> C}"
  proof-
    have 1: "{x \<in> A. Inl x \<notin> C \<and> Inr x \<notin> C} \<subseteq> A \<and> partial_order_on A r"
      by (simp add: p_o_translation)
    have 2: "anti_total {x \<in> A. Inl x \<notin> C \<and> Inr x \<notin> C} r"
    proof(rule ccontr)
      assume "\<not> anti_total {x \<in> A. Inl x \<notin> C \<and> Inr x \<notin> C} r" 
      hence  "(\<exists>x\<in>A. \<exists>y\<in>A. x\<noteq>y \<and>  
            (Inl x \<in> (A <+> A) - C \<and>  Inr x \<in> (A <+> A) - C) \<and> 
            (Inl y \<in> (A <+> A) - C \<and>  Inr y \<in> (A <+> A) - C) \<and>
            ((x,y) \<in> r \<or> (y, x) \<in> r))" 
        using anti_total_def by blast
      then obtain x and y  where a:  "((x \<in> A \<and> y \<in> A \<and> x\<noteq>y) \<and>  
            (Inl x \<in> (A <+> A) - C \<and>  Inr x \<in> (A <+> A) - C) \<and> 
            (Inl y \<in> (A <+> A) - C  \<and>  Inr y \<in> (A <+> A) - C) \<and>
            ((x,y) \<in> r \<or> (y, x) \<in> r))"
        by blast
      hence "(x \<in> A \<and> y \<in> A \<and> (x,y) \<in> r \<and> x\<noteq>y) \<or> (x \<in> A \<and> y \<in> A \<and> (y,x) \<in> r \<and> x\<noteq>y )" 
        by blast
      hence b: "(Inl x, Inr y) \<in> (arcs  (relation_to_digraph A r)) \<or> 
              (Inl y, Inr x) \<in> (arcs  (relation_to_digraph A r))"
        using relation_to_digraph_def
        by (smt (verit, best) mem_Collect_eq select_convs(2)) 
      hence "(Inl x =  tail (relation_to_digraph A r) (Inl x,Inr y) \<and> 
            Inr y =  head  (relation_to_digraph A r) (Inl x,Inr y)) \<or> 
           (Inl y = tail (relation_to_digraph A r) (Inl y,Inr x) \<and> 
            Inr x =  head (relation_to_digraph A r) (Inl y,Inr x))"
        by (simp add: relation_to_digraph_def) 
      hence "(Inl x \<in> C \<or> Inr y \<in> C) \<or> (Inl y \<in> C \<or> Inr x \<in> C)" 
        using relation_to_digraph_def[of A r] vertex_cover_def[of "relation_to_digraph A r"] 
          minimum_vertex_cover_def  assms b
        by (metis (mono_tags, lifting) prod.simps(2) select_convs(3,4)) 
      thus  False using a by auto 
    qed 
    thus ?thesis
      by (simp add: "1" anti_chain_def)
  qed
next
  let ?X = "{x \<in> A. Inl x \<notin> C \<and> Inr x \<notin> C}"   
  have partition:
    "A = ?X \<union> {x\<in>A. Inl x \<in> C \<or> Inr x \<in> C}" by auto
  moreover
  have disj:
    "?X \<inter> {x\<in>A. Inl x \<in> C \<or> Inr x \<in> C} = {}"  by auto
  ultimately 
  have "card A = card ?X + card {x\<in>A. Inl x \<in> C \<or> Inr x \<in> C}"
    using assms(1)
    by (metis (lifting) assms(2) card_Un_disjoint finite_Un)
  moreover
  have  "card {x\<in>A. Inl x \<in> C \<or> Inr x \<in> C} = card C" using card_projection
      assms(1,2) p_o_translation by blast 
  ultimately 
  show "card ?X = card A - card C" by simp   
qed

lemma antichain_le_chain_decomposition:
  assumes "chain_decomposition A r C"  and  "anti_chain A r X"
    and  "finite X"  and  "finite C"
  shows "card X \<le> card C"
proof-
  have cover:
    "\<And>x. x \<in> X \<Longrightarrow> \<exists>c\<in>C. x \<in> c"
    using assms(1) anti_chain_def chain_decomposition_def
    by (metis assms(2) UnionE partition_on_def subsetD)
  then  obtain f where
    f_def: "\<And>x. x \<in> X \<Longrightarrow> f x \<in> C \<and> x \<in> f x"
    by metis
  have inj: "inj_on f X"
  proof (rule inj_onI)
    fix x y
    assume x: "x \<in> X" and y: "y \<in> X" and eq: "f x = f y"
    from f_def[OF x] have "x \<in> f x" by auto
    moreover
    from f_def[OF y] have "y \<in> f y" by auto
    ultimately
    have "x \<in> f x \<and> y \<in> f x" using eq
      by auto
    hence  both_in_chain:
      "x \<in> f x \<and> y \<in> f x" by auto
    have "chain (f x) A r" 
      using chain_decomposition_def assms(1) f_def x
      by blast
    hence total:"total_on (f x) r" using chain_def by auto
    have "(x,y) \<in> r \<or> (y,x) \<in> r"
      using total both_in_chain total_on_def 
      by (metis Dilworth_Finite.chain_def \<open>Dilworth_Finite.chain (f x) A r\<close> partial_order_onD(1) refl_onD subsetD)
    have "x \<noteq> y \<longrightarrow> \<not>((x,y) \<in> r \<or> (y,x) \<in> r)"
      using assms(2) x y anti_chain_def
      by (metis anti_total_def)
    thus "x = y"
      using \<open>(x,y) \<in> r \<or> (y,x) \<in> r\<close>
      by blast
  qed
  have "f ` X \<subseteq> C"
    using f_def by auto
  moreover 
  have "finite (f ` X)"
    using assms(3) by auto
  ultimately have "card (f ` X) \<le> card C" using assms(4) 
    by (simp add: card_mono)
  moreover have "card X = card (f ` X)"
    using inj assms(3)
    by (simp add: card_image)
  ultimately show ?thesis by simp
qed
end (* ctxt part_order *)

lemma  Konig_Egervary_relation:
  fixes A:: "'a::countable set"
  assumes   
    "maximum_dirBD_matching (relation_to_digraph A r) (Inl ` A) (Inr ` A) E" and
    "minimum_vertex_cover  (relation_to_digraph A r) (arcs  (relation_to_digraph A r)) C" and 
    "finite (verts  (relation_to_digraph A r))"      
  shows  "card E = card C" using assms Konig_Egervary
    dirBD_matching_def maximum_dirBD_matching_def by blast

lemma  (in part_order_countable)exists_max_antichain_from_matching:
  assumes "finite A" and "maximum_dirBD_matching (relation_to_digraph A r) (Inl ` A) (Inr ` A) M"
  shows "\<exists>X. largest_antichain A r X \<and> (card X = card A - card M)"
proof-
  have "\<exists>C. minimum_vertex_cover (relation_to_digraph A r) (arcs (relation_to_digraph A r)) C"
    by (meson assms(1,2) dirBD_matching_def exists_min_vertex_cover finite_Un finite_imageI 
        maximum_dirBD_matching_def)
  then  obtain C where
    Cmin: "minimum_vertex_cover (relation_to_digraph A r) (arcs (relation_to_digraph A r)) C" by auto
  have card_eq: "card M = card C"  using Konig_Egervary_relation
    using Cmin assms(1,2) finite_verts by blast
  have fin1: "finite C"
    by (meson Cmin assms(1) finite_verts minimum_vertex_cover_def rev_finite_subset vertex_cover_def) 
  let ?X = "{x \<in> A. Inl x \<notin> C \<and> Inr x \<notin> C}" 
  have anti: "anti_chain A r ?X \<and> card ?X = card A - card C" 
    using Cmin  assms(1) cover_antichain 
    by blast  
  have *:  "\<forall>X'. anti_chain A r X' \<longrightarrow> card X' \<le> card ?X"
  proof(rule allI, rule impI)
    fix X'
    assume h: "anti_chain A r X'"
    have c: "chain_decomposition A r (chain_decomposition_order A r M)" 
      using chain_decomposition_cardinality assms(1,2) maximum_dirBD_matching_def p_o_translation
        part_order.exist_chain_decomposition part_order_axioms partial_order_onD(4) by blast
    have fin3: "finite X'" using h
      by (metis anti_chain_def assms(1) finite_subset) 
    hence "card X' \<le> card (chain_decomposition_order A r M)"
      using h antichain_le_chain_decomposition[of "chain_decomposition_order A r M"]  c 
      by (metis assms(1) chain_decomposition_def finite_elements) 
    thus "card X' \<le> card ?X"
      using anti assms(1,2) card_eq maximum_dirBD_matching_def part_order.chain_decomposition_cardinality 
        part_order_axioms
      by fastforce
  qed
  from anti *
  have  "(largest_antichain A r ?X) \<and> (card ?X = card A - card M)"
    by (simp add: card_eq largest_antichain_def)
  thus ?thesis by auto
qed

lemma  (in part_order_countable)smallest_chain_decomposition_order:
  assumes "finite A" and  "maximum_dirBD_matching (relation_to_digraph A r) (Inl ` A) (Inr ` A) M" 
  shows "\<exists>DC. (smallest_chain_decomposition A r DC) \<and> (card DC = card A - card M)"  
proof-
  let ?C = "chain_decomposition_order A r M" 
  have *: "chain_decomposition A r ?C \<and> (card ?C = card A - card M)" 
    using assms chain_decomposition_cardinality  maximum_dirBD_matching_def p_o_translation 
      part_order.exist_chain_decomposition part_order_axioms partial_order_onD(4) 
    by metis
  moreover
  have "(\<forall>P. chain_decomposition A r P \<longrightarrow> card ?C \<le> card P)"  
  proof(intro allI impI)
    fix P
    assume h: "chain_decomposition A r P" 
    have  "\<exists>X. anti_chain A r X \<and> card X = card A - card M" 
      using exists_max_antichain_from_matching
      using assms(1,2) largest_antichain_def p_o_translation by blast  
    then obtain X where X: "anti_chain A r X \<and> card X = card A - card M "
      by auto
    hence "card X \<le> card P "
      using antichain_le_chain_decomposition
      by (metis antichain_le_chain_decomposition assms(1) card_eq_0_iff 
          chain_decomposition_def finite_elements h less_eq_nat.simps(1))
    thus "card ?C \<le> card P" using * X  by argo
  qed
  ultimately
  show ?thesis using smallest_chain_decomposition_def
    by blast
qed

lemma chain_unit: 
  assumes "r \<subseteq>  A \<times> A" and "r \<noteq> {}" and "\<forall>a b. (a, b) \<in> r \<longrightarrow> a = b"
  shows "(chain B A r) \<and> B \<noteq> {} \<longrightarrow> (\<exists>x\<in>A. B = {x})"
proof(rule impI)
  assume hip: "chain  B A r \<and> B \<noteq> {}"
  show  "\<exists>x\<in>A. B = {x}"
  proof(rule ccontr)
    assume "\<not> (\<exists>x\<in>A. B = {x})" 
    hence "(\<forall> x \<in> A. B \<noteq> {x})" by simp
    hence "\<exists>x.\<exists>y. x\<noteq>y \<and> x\<in>B \<and> y\<in>B" 
      by (meson Dilworth_Finite.chain_def hip is_singletonI' is_singleton_some_elem
          some_elem_nonempty subsetD)
    hence "\<exists>x.\<exists>y. x\<noteq>y \<and> (x,y)\<in>r" 
      by (metis Dilworth_Finite.chain_def hip total_on_def)
    thus False using assms(3) by auto
  qed
qed

lemma chain_descomposition_unit:
  assumes "r \<subseteq>  A \<times> A"  and "\<forall>a b. (a, b) \<in> r \<longrightarrow> a = b" and "partial_order_on A r" and "r \<noteq> {}"  
  shows "(chain_decomposition A r {{x}|x. x\<in>A} ) \<and> ((chain_decomposition A r D) \<longrightarrow> D = {{x}|x. x\<in>A})" 
proof(rule conjI)
  show "chain_decomposition A r {{x} |x. x \<in> A}"
  proof(unfold chain_decomposition_def, rule conjI) 
    show "partition_on A {{x} |x. x \<in> A}"
      by (simp add: partition_on_singletons setcompr_eq_image) 
  next
    show  "\<forall>B\<in>{{x} |x. x \<in> A}. chain B A r"
      using Dilworth_Finite.chain_def assms(3) by fastforce
  qed
next 
  show "chain_decomposition A r D \<longrightarrow> D = {{x} |x. x \<in> A}"
  proof(rule impI)
    assume *: "chain_decomposition A r D"
    show "D = {{x} |x. x \<in> A}"
    proof(rule ccontr)
      let ?D1 = "{{x} |x. x \<in> A}"
      assume hip:  "D \<noteq> ?D1"
      show False 
      proof(rule disjE)
        show "\<not>(D \<subseteq> ?D1) \<or> \<not>(?D1 \<subseteq> D)" using hip by simp
      next
        assume "\<not> D \<subseteq> ?D1"
        hence "\<exists>B. B \<in> D \<and> B \<notin> ?D1" by auto
        then obtain B where B: "B \<in> D \<and> B \<notin> ?D1" by auto
        hence "\<exists>x.\<exists>y. x\<noteq>y \<and> x\<in>B \<and> y\<in>B" using *
          by (smt (verit, del_insts) chain_decomposition_def is_singletonI' is_singleton_def 
              mem_Collect_eq mem_simps(9) partition_on_def singletonI) 
        hence "\<exists>x.\<exists>y. x\<noteq>y \<and> (x,y) \<in> r" using *
          by (metis (no_types, opaque_lifting) B Dilworth_Finite.chain_def chain_decomposition_def total_on_def) 
        thus False using assms(2) by auto
      next
        assume "\<not> ?D1 \<subseteq> D" 
        hence "\<exists>x. {x} \<in> ?D1 \<and> {x} \<notin> D" by auto
        thus False using * assms chain_unit
          by (smt (verit) UnionE chain_decomposition_def mem_Collect_eq partial_order_onD(4) partition_on_def
              singletonD)
      qed
    qed
  qed
qed

lemma antichain_on: 
  assumes "r \<subseteq>  A \<times> A"  and "\<forall>a b. (a, b) \<in> r \<longrightarrow> a = b" and "partial_order_on A r" and
    "r \<noteq> {}"
  shows "anti_chain A r A" 
  using anti_total_def anti_chain_def assms by (metis subsetI) 

lemma largest_antichain_on:
  assumes "r \<subseteq>  A \<times> A"  and "\<forall>a b. (a, b) \<in> r \<longrightarrow> a = b" and "partial_order_on A r" and
    "r \<noteq> {}" and "finite A"
  shows "largest_antichain A r A" using anti_total_def anti_chain_def largest_antichain_def 
proof-
  have "anti_chain A r A" using assms antichain_on by blast
  moreover
  have "\<forall>B. anti_chain A r B \<longrightarrow> card B \<le> card A"
  proof(rule allI, rule impI)
    fix B
    assume  "anti_chain A r B"
    hence "B \<subseteq> A" using anti_chain_def[of A r B] by simp
    thus "card B \<le> card A" using  assms(5) 
      by (simp add: card_mono) 
  qed
  ultimately
  show ?thesis using largest_antichain_def by auto
qed

lemma card_smCD_lgAC1: 
  assumes "finite A" shows " card A = card {{x} |x. x \<in> A}" 
  using assms by (metis Setcompr_eq_image inj_on_iff_eq_card inj_singleton)

lemma arcs_empty: 
  assumes "r \<subseteq>  A \<times> A" and "arcs (relation_to_digraph A r) = {}" 
  shows "\<forall>a b. (a, b) \<in> r \<longrightarrow> a = b" 
proof(rule ccontr)
  assume  "\<not> (\<forall>a b. (a, b) \<in> r \<longrightarrow> a = b)"
  thus False
    by (smt (z3) Collect_empty_eq assms(1,2) mem_Sigma_iff relation_to_digraph_def 
        select_convs(2) subset_eq) 
qed 

lemma card_smCD_lgAC:
  assumes "r \<subseteq>  A \<times> A"  and "\<forall>a b. (a, b) \<in> r \<longrightarrow> a = b" and "partial_order_on A r" and
    "r \<noteq> {}" and "finite A" and
    "smallest_chain_decomposition A r smCD "  and "largest_antichain A r lgAC"
  shows "card smCD = card lgAC" 
  using assms largest_antichain_on card_smCD_lgAC1
  by (metis (no_types, lifting) anti_chain_def card_seteq chain_descomposition_unit largest_antichain_def
      partial_order_onD(4) smallest_chain_decomposition_def)

lemma (in part_order)Dilworth_empty:
  assumes "arcs (relation_to_digraph A r) = {}" and "finite A" and
    "smallest_chain_decomposition A r smCD" and "largest_antichain  A r lgAC"
  shows "card smCD = card lgAC"
proof-
  have *: "\<forall>a b. (a, b) \<in> r \<longrightarrow> a = b" using arcs_empty
    by (metis assms(1) part_order.p_o_translation part_order_axioms partial_order_onD(4))
  show ?thesis
  proof(cases "r = {}")
    assume "r={}" 
    hence "A = {}"
      using p_o_translation partial_order_onD(1) refl_onD by fastforce 
    hence "smCD = {} \<and>  lgAC = {}"
      by (metis anti_chain_def assms(3,4) bot.extremum_uniqueI chain_decomposition_def 
          largest_antichain_def partition_on_empty
          smallest_chain_decomposition_def)
    thus ?thesis
      by simp 
  next
    assume "r\<noteq>{}"
    thus ?thesis  
      using assms * card_smCD_lgAC anti_chain_def[of A r]  largest_antichain_def[of A r lgAC]
      by (metis partial_order_onD(4))
  qed
qed

theorem (in part_order_countable) Dilworth_Finite:
  assumes "finite A" 
  shows  "\<exists>smCD.\<exists>lgAC. smallest_chain_decomposition A r smCD \<and>  largest_antichain A r lgAC
          \<and> card smCD = card lgAC"
proof(rule disjE)
  show "arcs (relation_to_digraph A r) = {} \<or> arcs (relation_to_digraph A r) \<noteq> {}" by auto
next 
  assume "arcs (relation_to_digraph A r) = {}" 
  thus ?thesis using Dilworth_empty
    using assms
    by (metis assms \<open>arcs (relation_to_digraph A r) = {}\<close> Dilworth_empty 
        smallest_chain_decomposition_order exists_max_antichain_from_matching part_order_axioms 
        partial_order_onD(4) finite_arcs rel_to_digraph_is_dir_bipartite maximum_matching_digraph 
        part_order.p_o_translation)
next
  assume hip: "arcs (relation_to_digraph A r) \<noteq> {}"  
  have "dir_bipartite_digraph (relation_to_digraph A r) (Inl ` A) (Inr ` A)"
    using assms  rel_to_digraph_is_dir_bipartite p_o_translation 
    by (metis partial_order_onD(4)) 
  moreover
  have  "finite (arcs (relation_to_digraph A r))" using finite_arcs assms
    by (metis p_o_translation partial_order_onD(4))
  ultimately
  have  "\<exists>M. maximum_dirBD_matching (relation_to_digraph A r) (Inl ` A) (Inr ` A) M"
    using maximum_matching_digraph hip by blast
  then obtain M where M: "maximum_dirBD_matching (relation_to_digraph A r) (Inl ` A) (Inr ` A)  M"
    by auto
  hence DC: "(\<exists>DC.(smallest_chain_decomposition A r DC) \<and> (card DC = card A - card M))"
    using assms(1) smallest_chain_decomposition_order by blast
  moreover
  have  "(\<exists>AC.(largest_antichain A r AC) \<and> (card AC = card A - card M))"
    using assms(1) M exists_max_antichain_from_matching
    by blast
  ultimately
  show ?thesis by metis
qed

end