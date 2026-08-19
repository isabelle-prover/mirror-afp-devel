(*Certified Infinite Descent Criteria in Isabelle/HOL *)
(*Authors: Jamie Wright, Liron Cohen, Reuben Rowe and Andrei Popescu*)
section "Incomplete Criteria for Infinite Descent"

text \<open>We next formalize some sufficient criteria for deciding Infinite Descent that are incomplete, but useful in practice.
We adapt a known Sprenger-Dam (SD) criterion ~\cite{DBLP:conf/fossacs/SprengerD03} to the general setting of sloped graphs, and then presents a novel theoretical contribution: an extension that strictly generalizes SD, which we call XSD.\<close>

subsection "Sprenger-Dam Criterion"
theory Incomplete_Criteria
imports "../Sloped_Graphs"
begin


(* 1. THE SPRENGER-DAM CRITERION *)

context Sloped_Graph
begin

(* A subgraph (Node1,edge1) satisfies the descent property with respect to a labelling of its nodes
if any edge is matched by a Main or Decrease RR-edge with the considered labels, 
and there is at least one Decr RR-edge. 
*)  

(* Descending position-change choice : *)
definition decreasingPCC :: "('node \<Rightarrow> 'node \<Rightarrow> bool) \<Rightarrow> ('node \<Rightarrow> 'pos) \<Rightarrow> bool" where 
"decreasingPCC edge1 lab \<equiv> 
  (\<forall>nd nd'. edge1 nd nd' \<longrightarrow> RR (nd,lab nd) (nd',lab nd') Main \<or> 
                             RR (nd,lab nd) (nd',lab nd') Decr) \<and> 
  (\<exists>nd nd'. edge1 nd nd' \<and> RR (nd,lab nd) (nd',lab nd') Decr)"


(* If a subgraph has the descent property w.r.t. a labeling function, 
then any ipath through it will always persist w.r.t. these labels: *)
lemma decreasingPCC_ipath_alw_holds2: 
assumes lab: "decreasingPCC edge1 lab" and nds: "Graph.ipath Node1 edge1 nds"
shows 
"alw (holds2 (\<lambda>(nd, P) (nd', P'). RR (nd, P) (nd', P') Main \<or> RR (nd, P) (nd', P') Decr))
     (szip nds (smap lab nds))"
using assms unfolding Graph.ipath_iff_snth decreasingPCC_def
unfolding alw_holds2_iff_snth by auto

(* .. and if it additionally visits all nodes infinitely often, then it 
will also always eventually decrease: *)
lemma decreasingPCC_ipath_alw_ev_holds2: 
assumes lab: "decreasingPCC edge1 lab" and nds: "Graph.ipath Node1 edge1 nds" and 
"\<forall>nd nd'. edge1 nd nd' \<longrightarrow> alw (ev (holds2 (\<lambda>ndd ndd'. ndd = nd \<and> ndd' = nd'))) nds"
shows 
"alw (ev (holds2 (\<lambda>(nd, P) (nd', P'). RR (nd, P) (nd', P') Decr))) 
   (szip nds (smap lab nds))"
using assms unfolding Graph.ipath_iff_snth decreasingPCC_def
unfolding alw_ev_holds2_iff_snth by fastforce

lemma decreasingPCC_imp_descentIpath: 
assumes nds: "ipath nds"
and lim: "decreasingPCC (limitR nds) lab"
shows "descentIpath nds (smap lab nds)"
proof-
  obtain i where 0: "Graph.ipath (limitS nds) (limitR nds) (sdrop i nds)" 
  using ipath_sdrop_limit[OF Node_finite nds] by auto
  show ?thesis 
  unfolding descentIpath_def apply(intro sdrop_evI[where m = i]) 
  unfolding sdrop_szip sdrop_smap  apply safe
    subgoal using decreasingPCC_ipath_alw_holds2[OF lim 0] .
    subgoal apply(rule decreasingPCC_ipath_alw_ev_holds2[OF lim 0])
    apply safe apply(rule alw_sdrop) unfolding limitR_def . .
  qed

(* Sprenger-Dam descent: *)
definition SDdescending :: bool where 
"SDdescending \<equiv> \<forall>Node1 edge1. scsg Node1 edge1 \<longrightarrow> (\<exists>lab. wfLabF Node1 lab \<and> decreasingPCC edge1 lab)"

proposition SDdescending_imp_InfiniteDescent: 
"SDdescending \<Longrightarrow> InfiniteDescent"
unfolding SDdescending_def InfiniteDescent_def 
using decreasingPCC_imp_descentIpath scsg_limit Node_finite by blast


subsection "Extended Sprenger-Dam Criterion"
(* 2. EXTENDED SPRENGER-DAM CRITERION  *)

(* The position-extended graph of a labeled SGSG: *)

(* The global extension graph Ext(G) of the entire sloped graph: *)
definition ExtG_Nodes :: "('node \<times> 'pos) set" where 
"ExtG_Nodes \<equiv> {(nd, P). nd \<in> Node \<and> P \<in> PosOf nd}"

definition ExtG_Edges :: "('node \<times> 'pos) \<Rightarrow> ('node \<times> 'pos) \<Rightarrow> bool" where 
"ExtG_Edges \<equiv> \<lambda>(nd, P) (nd', P'). 
   edge nd nd' \<and> (RR (nd,P) (nd',P') Main \<or> RR (nd,P) (nd',P') Decr)"


(* A Slice of a Position-change Set-choice Pi = (lab, f) w.r.t subgraph (Node1, edge1) *)
 (* It is a subgraph of the extension graph Ext(G) *)
(* Condition 1: Edges project to edge1 and respect the function f *)
(* Condition 2: Every edge in the base subgraph is covered by at least one edge in the slice *)
definition is_slice :: 
"'node set \<Rightarrow> ('node \<Rightarrow> 'node \<Rightarrow> bool) \<Rightarrow> 
 ('node \<Rightarrow> 'pos set) \<Rightarrow> ('node \<Rightarrow> 'node \<Rightarrow> 'pos \<Rightarrow> 'pos) \<Rightarrow> 
 ('node \<times> 'pos) set \<Rightarrow> (('node \<times> 'pos) \<Rightarrow> ('node \<times> 'pos) \<Rightarrow> bool) \<Rightarrow> bool" where 
"is_slice Node1 edge1 lab f NNode eedge \<equiv> 
  NNode \<subseteq> {(nd, P). nd \<in> Node1 \<and> P \<in> lab nd} \<and>
  Graph.subgr NNode eedge ExtG_Nodes ExtG_Edges \<and>
  (\<forall>nd P nd' P'. eedge (nd, P) (nd', P') \<longrightarrow> 
     {(nd, P), (nd', P')} \<subseteq> NNode \<and> edge1 nd nd' \<and> f nd nd' P = P') \<and>
  (\<forall>nd nd'. {nd,nd'} \<subseteq> Node1 \<and> edge1 nd nd' \<longrightarrow> 
     (\<exists>P P'. {(nd, P), (nd', P')} \<subseteq> NNode \<and> eedge (nd, P) (nd', P')))"


(* A slice is decreasing if it contains at least one strictly decreasing edge *)
definition decreasing_slice :: "('node \<times> 'pos) set \<Rightarrow> (('node \<times> 'pos) \<Rightarrow> ('node \<times> 'pos) \<Rightarrow> bool) \<Rightarrow> bool" where
"decreasing_slice NNode eedge \<equiv> 
  \<exists>nd P nd' P'. {(nd, P), (nd', P')} \<subseteq> NNode \<and> eedge (nd, P) (nd', P') \<and> RR (nd, P) (nd', P') Decr"


(* Descending Position-Change Set-Choice using the Sliced formulation *)
(* Every strongly connected slice of Pi is decreasing *)
definition descending_PCSC_sliced :: 
"'node set \<Rightarrow> ('node \<Rightarrow> 'node \<Rightarrow> bool) \<Rightarrow> 
 ('node \<Rightarrow> 'pos set) \<Rightarrow> ('node \<Rightarrow> 'node \<Rightarrow> 'pos \<Rightarrow> 'pos) \<Rightarrow> bool" where 
"descending_PCSC_sliced Node1 edge1 lab f \<equiv> 
  RRSetChoice Node1 edge1 lab f \<and>
  (\<forall>NNode eedge. 
     is_slice Node1 edge1 lab f NNode eedge \<and> 
     Graph.scg NNode eedge 
     \<longrightarrow> decreasing_slice NNode eedge)"


(* Sliced Extended-Sprenger-Dam (XSD) descent criterion: *)
definition XSDdescending :: bool where 
"XSDdescending \<equiv> 
  \<forall>Node1 edge1. scsg Node1 edge1 \<longrightarrow> 
    (\<exists>lab f. wfLabFS Node1 lab \<and> descending_PCSC_sliced Node1 edge1 lab f)"


lemma stake_sdrop_szip_nth:
  "k < m \<Longrightarrow> stake m (sdrop j (szip A B)) ! k = (A !! (j + k), B !! (j + k))"
  by (metis sdrop_snth snth_szip stake_nth)

lemma set_stake_sdrop_szipD:
  "(x, y) \<in> set (stake m (sdrop j (szip A B))) \<Longrightarrow> 
   \<exists>k<m. x = A !! (j + k) \<and> y = B !! (j + k)"
  by (metis in_set_conv_nth length_stake prod.inject
      stake_sdrop_szip_nth)

lemma eq_stake_sdrop_szip_tuple:
  "k < m \<Longrightarrow> (x, y) = stake m (sdrop j (szip A B)) ! k \<Longrightarrow> x = A !! (j + k) \<and> y = B !! (j + k)"
  by (metis prod.inject stake_sdrop_szip_nth)

lemma descending_PCSC_sliced_imp_descentIpath: 
assumes nds: "ipath nds" and lab: "wfLabFS (limitS nds) lab"
and lim: "descending_PCSC_sliced (limitS nds) (limitR nds) lab f"
shows "\<exists>Ps. descentIpath nds Ps"
proof-
  (* 1. ISOLATE THE LIMIT GRAPH *)
  define Node1 edge1 where Sedge1_def: "Node1 \<equiv> limitS nds" "edge1 \<equiv> limitR nds"
  obtain n where a: "alw (holdsS Node1 aand holds2 edge1) (sdrop n nds)" 
  using ipath_ev_alw[OF Node_finite nds] unfolding ev_iff_sdrop Sedge1_def by auto

  define nnds where "nnds \<equiv> sdrop n nds"
  have lndss: "limitR nds = limitR nnds" unfolding nnds_def by auto
  have nnds: "ipath nnds" by (simp add: Graph.ipath_sdrop nds nnds_def)
  
  have nnds_Sedge1: "\<forall>i. nnds!!i \<in> Node1 \<and> edge1 (nnds!!i) (nnds!!(Suc i))"
  using a unfolding nnds_def[symmetric] 
  using alw_holds2_iff_snth alw_holdsS_iff_snth alw_mono by blast

  (* 2. CONSTRUCT THE POSITION STREAM Ps *)
  obtain P0 where P0: "P0 \<in> lab (shd nnds)" 
    using lab unfolding wfLabFS_def 
    by (metis Sedge1_def(1) equals0I nnds_Sedge1 snth.simps(1))

  define Pi where "Pi \<equiv> rec_nat P0 (\<lambda>i P. f (nnds !! i) (nnds !! Suc i) P)"
  define Ps where "Ps \<equiv> fToStream Pi"

  have 00: "\<And>i. Pi i \<in> lab (nnds!!i) \<and> 
                edge1 (nnds !! i) (nnds !! Suc i) \<and> 
                Pi (Suc i) = f (nnds !! i) (nnds !! Suc i) (Pi i)"  
  subgoal for i apply(induct i) apply simp_all 
    subgoal using P0 unfolding Pi_def  
    by (metis (no_types, lifting) nnds_Sedge1 old.nat.simps(6) old.nat.simps(7) snth.simps(1))
    subgoal for i  unfolding Pi_def apply simp 
    by (smt (verit, best) Graph.limitR_S descending_PCSC_sliced_def 
      RRSetChoice_def Node_finite Sedge1_def(2) image_subset_iff ipath_sdrop_limit lim 
       limitR_sdrop_eq nds nnds_Sedge1) . .

  hence 0: "\<And>i. Ps!!i \<in> lab (nnds!!i) \<and> Ps!!(Suc i) = f (nnds !! i) (nnds !! Suc i) (Ps !! i)"  
  by (simp add: Ps_def)
    
  define \<phi> where "\<phi> \<equiv> \<lambda>i P P'. P' \<in> lab(nnds!!(Suc i)) \<and> 
            (RR (nnds!!i,P) (nnds!!(Suc i),P') Main \<or> 
             RR (nnds!!i,P) (nnds!!(Suc i),P') Decr)" 
  
  have 2: "\<forall>i. \<phi> i (Pi i) (Pi (Suc i))" 
  using 0 unfolding \<phi>_def  
  by (smt (verit, best) "00" descending_PCSC_sliced_def RRSetChoice_def 
         Sedge1_def(1) Sedge1_def(2) empty_subsetI insert_subset lim nnds_Sedge1) 

  (* Node bounding for pigeonhole principle *)
  have Node1: "finite Node1" "Node1 \<subseteq> Node" "wfLabFS Node1 lab" 
  unfolding Sedge1_def(1) using Node_finite infinite_super limitS_S 
  apply blast by (auto simp: Sedge1_def(1) limitS_S lab)  

  (* Create a local finite state space for the pigeonhole to extract an infinite cycle *)
  define StateSpace where "StateSpace \<equiv> {(nd, P). nd \<in> Node1 \<and> P \<in> lab nd}"
  have eNode1: "finite StateSpace" 
      unfolding StateSpace_def 
    proof -
      have "{(nd, P). nd \<in> Node1 \<and> P \<in> lab nd} = Sigma Node1 lab" by auto
      thus "finite {(nd, P). nd \<in> Node1 \<and> P \<in> lab nd}"
        using wfLabFS_finite[OF Node1(3) Node1(2)] Node1(1) finite_SigmaI by auto
    qed
    
    
  have ipath_states: "\<forall>i. (nnds!!i, Ps!!i) \<in> StateSpace"
    unfolding StateSpace_def using 0 nnds_Sedge1 by auto

  obtain nd P where nd_P: "(nd,P) \<in> StateSpace" "\<forall>i. \<exists>j\<ge>i. nnds!!j = nd \<and> Ps!!j = P"
  proof -
    have "range (\<lambda>i. (nnds!!i, Ps!!i)) \<subseteq> StateSpace" using ipath_states by auto
    hence fin_range: "finite (range (\<lambda>i. (nnds!!i, Ps!!i)))" 
      using eNode1 finite_subset by auto
      
    obtain nd_P where "infinite {i. (nnds!!i, Ps!!i) = nd_P}"
      using pigeonhole_infinite[OF ] fin_range by fastforce
    moreover obtain nd P where "nd_P = (nd, P)" by fastforce
    ultimately have inf: "infinite {i. (nnds!!i, Ps!!i) = (nd, P)}" by simp
    
    have "\<forall>i. \<exists>j\<ge>i. nnds!!j = nd \<and> Ps!!j = P"
      using inf unfolding infinite_nat_iff_unbounded 
      by (meson mem_Collect_eq order_less_imp_le prod.inject)
    moreover have "(nd, P) \<in> StateSpace"
      using inf ipath_states not_finite_existsD by blast
    ultimately show ?thesis using that by blast
  qed

  (* 3. PROVE DESCENT BY EXTRACTING CYCLES *)
  have d_nnds: "descentIpath nnds Ps" 
  unfolding descentIpath_iff_snth2 apply(intro conjI)
    subgoal using 2 unfolding \<phi>_def by (simp add: Ps_def)
    subgoal proof safe
      fix i    
      (* Find next visit to (nd, P) *)
      obtain j0 where j0: "j0\<ge>i" "nnds!!j0 = nd \<and> Ps!!j0 = P" using nd_P by auto

      (* Span an interval covering all edges in the limit *)
      obtain j1 j2 where j12: "j1\<ge>Suc j0" "j2\<ge>j1" 
      "\<And>nd nd'. limitR nnds nd nd' \<Longrightarrow> (\<exists>j\<ge>j1. j < j2 \<and> nnds !! j = nd \<and> nnds !! Suc j = nd')"
      using ipath_limitR_interval[OF Node_finite nnds] by blast

      (* Find the subsequent visit to (nd, P) to close the cycle *)
      obtain j3 where j3: "j3\<ge>Suc j2" "nnds!!j3 = nd \<and> Ps!!j3 = P" using nd_P by auto

      define nd_Pl where "nd_Pl \<equiv> stake (j3-j0+1) (sdrop j0 (szip nnds Ps))"
      
      have cyc: "Graph.cycleG StateSpace (\<lambda>_ _. True) nd_Pl" (* Base cycle abstraction *)
      unfolding nd_Pl_def apply(rule Graph.ipath_stake_sdrop_cycle) 
        subgoal by (simp add: Graph.ipath_iff_snth ipath_states)
        subgoal using j12(1) j12(2) j3(1) by linarith
        subgoal by simp (metis add_diff_cancel_left' add_leE j0(2) j12(1) j12(2) j3(1) j3(2) 
          nat_le_iff_add plus_1_eq_Suc) .
      
      define NNode where "NNode \<equiv> set (nd_Pl)"
      define eedge where "eedge \<equiv> \<lambda> nd_P nd_P'. 
      (\<exists>k. Suc k < length nd_Pl \<and> nd_P = nd_Pl!k \<and> nd_P' = nd_Pl!(Suc k))"

      (* 4. VERIFY IT IS A SLICE *)
      have subgr: "Graph.subgr NNode eedge ExtG_Nodes ExtG_Edges"
        unfolding Graph.subgr_def NNode_def eedge_def ExtG_Nodes_def ExtG_Edges_def
        apply safe
        subgoal for nd P 
          unfolding nd_Pl_def
          apply (drule set_stake_sdrop_szipD)
          using ipath_iff_snth nnds StateSpace_def by fastforce
        subgoal for nd P 
          unfolding nd_Pl_def
          apply (drule set_stake_sdrop_szipD)
          using ipath_states Node1(3) unfolding StateSpace_def wfLabFS_def 
          by auto
        subgoal for nd P nd' P' k
          apply(rule ssubst[of "nd" "nnds !! (j0 + k)"])
          apply (metis Suc_lessD length_stake nd_Pl_def prod.inject stake_sdrop_szip_nth)
          apply(rule ssubst[of "nd'" "nnds !! Suc (j0 + k)"])
          apply (unfold nd_Pl_def, metis prod.inject stake_sdrop_szip_nth nd_Pl_def length_stake add_Suc_right)
          using ipath_iff_snth nnds by blast
        subgoal for nd P nd' P' k
          apply(rule ssubst[of "(nd,P)" "(nnds !! (j0 + k), Ps !! (j0 + k))"])
           apply(unfold nd_Pl_def, metis Suc_lessD length_stake sdrop_snth snth_szip stake_nth)
          apply(rule ssubst[of "(nd', P')" "(nnds !! Suc (j0 + k), Ps !! Suc (j0 + k))"])
          apply( metis add_Suc_right length_stake sdrop_snth snth_szip stake_nth)
          using 2[THEN spec, of "j0 + k"] 
          unfolding nd_Pl_def \<phi>_def Ps_def 
          by (metis Suc_lessD add_Suc_right length_stake snth_fToStream
              stake_sdrop_szip_nth) .

      have proj: "\<forall>x P y P'. eedge (x, P) (y, P') \<longrightarrow> {(x, P), (y, P')} \<subseteq> NNode \<and> edge1 x y \<and> f x y P = P'"
        unfolding eedge_def apply clarify
        subgoal for x P y P' k
          using nnds_Sedge1[THEN spec, of "j0 + k"] 0[of "j0 + k"]
          unfolding nd_Pl_def 
          by (metis Suc_lessD add_Suc_right eq_stake_sdrop_szip_tuple
              length_stake NNode_def Suc_lessD empty_subsetI in_set_conv_nth insert_subset nd_Pl_def) .

      have cover: "\<forall>x y. {x, y} \<subseteq> Node1 \<and> edge1 x y \<longrightarrow> 
                   (\<exists>P P'. {(x,P),(y,P')} \<subseteq> NNode \<and> eedge (x,P) (y,P'))"
      unfolding NNode_def eedge_def Sedge1_def lndss
      proof clarify
        fix x y
        assume nodes: "{x, y} \<subseteq> limitS nds"
        assume edge: "limitR nnds x y"

        (* Extract the interval index j where the edge is traversed *)
        from j12(3)[OF edge] obtain j where j_bound: "j1 \<le> j" "j < j2"
          and x_eq: "x = nnds !! j" and y_eq: "y = nnds !! Suc j" by blast

        define k where "k \<equiv> j - j0"

        (* Prove arithmetic bounds *)
        have j0_j: "j0 \<le> j" using j12(1) j_bound(1) by linarith
        have k_len1: "k < j3 - j0 + 1" and k_len2: "Suc k < j3 - j0 + 1"
          unfolding k_def using j12(1) j_bound(2) j3(1) j0_j by linarith+
        have len_Pl: "length nd_Pl = j3 - j0 + 1" unfolding nd_Pl_def by simp

        (* Extract the k and (Suc k) elements instantly using the helper lemma *)
        have nth_k: "nd_Pl ! k = (x, Ps !! j)"
          unfolding nd_Pl_def k_def using j0_j k_len1 
          by (metis Nat.add_diff_assoc add_diff_cancel_left' k_def
              stake_sdrop_szip_nth x_eq)
        have nth_Suc_k: "nd_Pl ! Suc k = (y, Ps !! Suc j)"
          unfolding nd_Pl_def k_def using j0_j k_len2 
          by (metis Nat.add_diff_assoc add_Suc_right add_diff_cancel_left'
              k_def stake_sdrop_szip_nth y_eq)

        show "\<exists>P P'. {(x, P), (y, P')} \<subseteq> set nd_Pl \<and>
                     (\<exists>i. Suc i < length nd_Pl \<and> (x, P) = nd_Pl ! i \<and> (y, P') = nd_Pl ! Suc i)"
        proof (intro exI2[of _ "Ps !! j" "Ps !! Suc j"] conjI)
          show "{(x, Ps !! j), (y, Ps !! Suc j)} \<subseteq> set nd_Pl"
            using nth_k nth_Suc_k k_len1 k_len2 len_Pl nth_mem by (metis empty_subsetI insert_subset)
          show "\<exists>i. Suc i < length nd_Pl \<and> (x, Ps !! j) = nd_Pl ! i \<and> (y, Ps !! Suc j) = nd_Pl ! Suc i"
            using k_len2 nth_k nth_Suc_k len_Pl by (metis exI[of _ k])
        qed
      qed

      have nnode_bound: "NNode \<subseteq> {(nd, P). nd \<in> Node1 \<and> P \<in> lab nd}"
        unfolding NNode_def StateSpace_def[symmetric]
      proof
        fix x assume "x \<in> set nd_Pl"
        then obtain k where "x = nd_Pl ! k" "k < length nd_Pl" 
          by (metis \<open>x \<in> set nd_Pl\<close> in_set_conv_nth)
        thus "x \<in> StateSpace"
          unfolding nd_Pl_def using ipath_states
          by (metis length_stake sdrop_snth snth_szip stake_nth)
      qed

      have is_slice: "is_slice Node1 edge1 lab f NNode eedge"
      unfolding is_slice_def using subgr proj cover nnode_bound by blast

      (* 5. APPLY THE CRITERION *)
      have scg: "Graph.scg NNode eedge" apply(subst Graph.scg_iff_cycle)
        subgoal unfolding NNode_def by auto
        subgoal unfolding NNode_def 
        by simp (metis Graph.cycle_iff_nth cyc less_nat_zero_code list.size(3) not_path_Nil path_iff_nth)
        subgoal apply(rule exI[of _ nd_Pl], standard)
          subgoal using cyc unfolding Graph.cycleG_def NNode_def eedge_def 
             unfolding Graph.path_iff_set_nth by auto
          subgoal unfolding NNode_def .. . .

      with is_slice lim obtain nd_d P_d nd_d' P_d' where 
      decr_edge: "eedge (nd_d, P_d) (nd_d', P_d')" "RR (nd_d, P_d) (nd_d', P_d') Decr"
      unfolding descending_PCSC_sliced_def decreasing_slice_def 
      by (metis scg Sedge1_def(2) Sedge1_def(1))

      then obtain k where k: "k<length nd_Pl - 1" "RR (nd_Pl ! k) (nd_Pl ! Suc k) Decr"
      by (metis Suc_lessE diff_Suc_1 eedge_def) 

      show "\<exists>j\<ge>i. RR (nnds !! j, Ps !! j) (nnds !! Suc j, Ps !! Suc j) Decr"
      apply(rule exI[of _ "j0+k"], safe) 
        subgoal by (simp add: j0(1) trans_le_add1)
        subgoal using k unfolding nd_Pl_def sdrop_snth  
          by (metis Suc_eq_plus1 Suc_mono add_Suc_right add_diff_cancel_right' 
            length_stake less_SucI sdrop_snth snth_szip stake_nth) .
    qed .

  show ?thesis using d_nnds by (simp add: descentIpath_sdrop_any nnds_def)
qed

proposition XSDdescending_implies_InfiniteDescent: 
  "XSDdescending \<Longrightarrow> InfiniteDescent"
  unfolding XSDdescending_def InfiniteDescent_def 
  using descending_PCSC_sliced_imp_descentIpath scsg_limit Node_finite by blast

lemmas Incomplete_Criterion = SDdescending_imp_InfiniteDescent 
                              XSDdescending_implies_InfiniteDescent

(**SD implies XSD**)
theorem SDdescending_implies_XSDdescending:
  "SDdescending \<Longrightarrow> XSDdescending"
  unfolding SDdescending_def XSDdescending_def
proof clarify
  fix Node1 edge1
  assume SD: "\<forall>Node1 edge1. scsg Node1 edge1 \<longrightarrow> (\<exists>lab. wfLabF Node1 lab \<and> decreasingPCC edge1 lab)"
  assume scsg: "scsg Node1 edge1"
  
  (* 1. Sanitize the edge relation to guarantee strict node inclusion *)
  define edge1' where "edge1' \<equiv> \<lambda>x y. edge1 x y \<and> x \<in> Node1 \<and> y \<in> Node1"
  
  have scsg': "scsg Node1 edge1'"
    using scsg Graph_scg_restrict unfolding scsg_def edge1'_def Graph.subgr_def
    by auto
    
  (* 2. Apply SDdescending to the sanitized subgraph *)
  from SD scsg' obtain lab where wf: "wfLabF Node1 lab" and pcc: "decreasingPCC edge1' lab"
    by blast
    
  (* 3. Construct XSD witnesses (Singletons) *)
  define lab' where "lab' \<equiv> \<lambda>nd. {lab nd}"
  define f where "f \<equiv> \<lambda>(nd::'node) nd' (P::'pos). lab nd'"
  
  show "\<exists>lab' f. wfLabFS Node1 lab' \<and> descending_PCSC_sliced Node1 edge1 lab' f"
  proof (intro exI conjI)
    show "wfLabFS Node1 lab'"
      using wf unfolding wfLabF_def wfLabFS_def lab'_def by blast
      
    show "descending_PCSC_sliced Node1 edge1 lab' f"
      unfolding descending_PCSC_sliced_def 
    proof (intro conjI allI impI)
      (* A: RRSetChoice *)
      show "RRSetChoice Node1 edge1 lab' f"
        using pcc unfolding decreasingPCC_def RRSetChoice_def lab'_def f_def edge1'_def by auto
        
      (* B: The Slice Condition *)
      fix NNode eedge
      assume "is_slice Node1 edge1 lab' f NNode eedge \<and> Graph.scg NNode eedge" 
      hence  is_slice: "is_slice Node1 edge1 lab' f NNode eedge"
         and scg: "Graph.scg NNode eedge" by auto
                     
      (* 1. Obtain the decreasing edge, GUARANTEED to be in Node1 thanks to edge1' *)
      from pcc obtain nd_d nd_d' where decr: "edge1' nd_d nd_d'" "RR (nd_d, lab nd_d) (nd_d', lab nd_d') Decr"
        unfolding decreasingPCC_def by blast
        
      have nodes_in: "{nd_d, nd_d'} \<subseteq> Node1" and orig_edge: "edge1 nd_d nd_d'"
        using decr(1) unfolding edge1'_def by auto
        
      (* 2. Force the slice to cover this specific decreasing edge *)
      have cover: "\<forall>x y. {x, y} \<subseteq> Node1 \<and> edge1 x y \<longrightarrow> 
                   (\<exists>P P'. {(x, P), (y, P')} \<subseteq> NNode \<and> eedge (x, P) (y, P'))"
        using is_slice unfolding is_slice_def by blast
        
      obtain P P' where in_slice: "{(nd_d, P), (nd_d', P')} \<subseteq> NNode" "eedge (nd_d, P) (nd_d', P')"
        using cover nodes_in orig_edge by blast
        
      (* 3. Extract the exact positions from the singleton sets *)
      have nnode_bound: "NNode \<subseteq> {(nd, P). nd \<in> Node1 \<and> P \<in> lab' nd}"
        using is_slice unfolding is_slice_def by auto

      have "P = lab nd_d" and "P' = lab nd_d'"
        using in_slice(1) nnode_bound unfolding lab'_def by auto
        
      (* 4. Output the final existential witnesses for decreasing_slice *)
      show "decreasing_slice NNode eedge"
        unfolding decreasing_slice_def
        using in_slice decr(2) \<open>P = lab nd_d\<close> \<open>P' = lab nd_d'\<close> by blast
    qed
  qed
qed

end (* context Sloped_Graph *) 


end 
