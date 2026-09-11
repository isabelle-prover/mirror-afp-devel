(* Dilworth's Theorem for countable finite Graphs version
   Fabian Fernando Serrano Suárez  UNAL Manizales
   Thaynara Arielly de Lima        Universidade Federal de Goiás 
   Mauricio Ayala-Rincón           Universidade Federal de Goiás and Universidade de Brasília
   Last modified: 16 June, 2026
*)

section \<open>Dilworth Countable Theorem\<close>

theory DilworthCountable
  imports 
    Dilworth_Finite 
    Prop_Compactness.k_coloring
begin
text\<open>The countable infinite version of Dilworth's theorem for partially ordered sets states that, 
whenever the "width" of the partial order is finite, i.e., whenever there exists a finite upper 
bound on the size of anti-chains, there exists a finite minimal chain decomposition with size equal
to the size of the largest anti-chain.\<close> 

definition incomparability_graph :: "'a rel \<Rightarrow> 'a set \<Rightarrow>'a digraph"
  where 
    "incomparability_graph r A  \<equiv>  (A,{(x, y)|x y. x \<in> A \<and> y \<in> A \<and> (x,y) \<notin> r \<and> (y,x) \<notin> r \<and> x\<noteq>y})"

lemma chain_decomposition_colorable:
  assumes  "partition_on A P" and "finite P" and "(\<forall>B\<in>P.(total_on B r))"
  shows "(colorable (incomparability_graph r A) (card P))"  
proof-
  let ?k = "(card P)"
  have  "\<exists>f. P = f ` {i. i < ?k} \<and> inj_on f {i. i < ?k}" using assms(2)
    by (metis card_Collect_less_nat card_image finite_imp_nat_seg_image_inj_on) 
  then obtain f where f1: "P = f ` {i::nat. i < ?k}" and f2: "inj_on f {i. i < ?k}" by auto
  let ?G = "incomparability_graph r A"
  let ?c = "\<lambda>v. THE i. i < ?k \<and> (\<exists>p \<in> P. v \<in> p \<and> f i = p)"
  have *: "\<forall>u. u\<in>V[?G]\<longrightarrow> (\<exists>!i. i < ?k \<and> (\<exists>p. p \<in> P \<and> u \<in> p \<and> f i = p ) \<and> ?c(u) = i)"
  proof(intro allI impI)
    fix u
    assume hip: "u\<in>V[?G]"
    show "(\<exists>!i. i < ?k \<and> (\<exists>p. p \<in> P \<and> u \<in> p \<and> f i = p ) \<and> ?c(u) = i)"
    proof-
      have 1:"\<exists>i. i < ?k \<and> (\<exists>p. p\<in>P \<and> u \<in> p \<and> f i = p)" using hip assms f1 
        by(metis (no_types, lifting) UN_E image_eqI
            incomparability_graph_def mem_Collect_eq partition_onD1 prod.sel(1))
      then obtain p i where p: " p \<in> P \<and> u \<in> p" and i1: "f i = p"  and i2:  "i < ?k" by blast
      hence "i < ?k \<and> (\<exists>p. p\<in>P \<and> u \<in> p \<and> f i = p)" by auto 
      have 2: "\<forall>x. x < ?k \<and> (\<exists>p \<in> P. u \<in> p \<and> f x = p) \<longrightarrow> x = i"
      proof(intro allI impI)
        fix x
        assume hip: "x < ?k \<and> (\<exists>p \<in> P. u \<in> p \<and> f x = p)"
        show "x = i"
        proof-
          from hip obtain q  where q: "q \<in> P \<and> u \<in> q" and q1: "f x = q" by auto
          hence 1:  "f x \<in> f ` {i::nat. i < ?k}" using f1 by auto   
          have  2: "f i \<in> f ` {i::nat. i < ?k}" using i2 by auto
          have "p = q" using q p  assms(1) using disjointD partition_on_def by fastforce
          hence "f x = f i" using q1 i1 by auto
          hence "x = i" using hip i2  1 2 f2 by(simp add: inj_onD)
          thus ?thesis by auto
        qed
      qed
      from 1 and 2 show ?thesis by auto
      have 3: "?c(u) = i" using 1 2 p by auto
    qed
  qed
  have c1: "(\<forall>u. u\<in>V[?G]\<longrightarrow> ?c(u) < ?k)" using * by blast 
  have c2: "(\<forall>u v.(u,v)\<in>E[?G] \<longrightarrow> ?c(u)\<noteq>?c(v))" 
  proof(intro allI impI)
    fix u v 
    assume hip:  "(u,v)\<in>E[?G]"   
    hence a: "u\<in>V[?G]" and b:  "v\<in>V[?G]" by(unfold incomparability_graph_def, auto) 
    have "\<exists>i.\<exists>p. p\<in>P \<and> u \<in> p \<and> f i = p \<and> i <  ?k " using * a by auto
    then obtain p i where p: "p \<in> P \<and> u \<in> p" and i1: "f i = p"  and i2: "i < ?k"
      and i3: "?c(u) = i" using * a by auto
    have  "\<exists>j.\<exists>q. q\<in>P \<and> v \<in> q \<and> f j = q \<and> j <  ?k" using * b by auto
    then obtain q j where q: "q \<in> P \<and> v \<in> q" and j1: "f j = q"  and j2: "j < ?k"
      and j3: "?c(v) = j" using * b by auto 
    show "?c(u)\<noteq>?c(v)" 
    proof(rule notI)
      assume "?c(u) = ?c(v)"        
      hence 3:  "p = q" using i1 i3 j1 j3 by auto  
      have 4: "u\<in>A" and "v\<in>A" using hip by(unfold incomparability_graph_def, auto)
      hence "(u,v) \<in> r \<or> (v,u)\<in> r" using p q 3 assms(3)
        by (smt (verit, best) CollectD Pair_inject hip incomparability_graph_def sndI total_on_def)  
      thus False using hip by(unfold incomparability_graph_def, auto)
    qed
  qed
  hence "coloring ?c ?k (incomparability_graph r A)" 
    using c1 c2 by(unfold coloring_def,auto) 
  thus ?thesis using c1 c2 by (unfold colorable_def,auto) 
qed

lemma non_empty_set_color: assumes "coloring c k (incomparability_graph r A)" and "j\<in> c`A"
  shows "{x \<in> A. c x = j} \<noteq> {}"
proof-
  have "V[incomparability_graph r A] = A" 
    using incomparability_graph_def[of r A] by auto  
  have  "\<exists>x \<in> A. c(x) = j" 
    using assms incomparability_graph_def[of r A] by auto 
  thus ?thesis by auto
qed

lemma coloring_particion: 
  assumes  "coloring c k (incomparability_graph r A)" 
  shows  "partition_on A {{x \<in> A. c(x) = j}|j. j \<in> c`A}"
proof-
  let ?G = "incomparability_graph r A"
  have 1:  "\<Union>{{x \<in> A. c x = j} |j. j \<in>  c`(V[?G])} = A" 
  proof-
    have "\<Union> {{x \<in> A. c x = j} |j. j \<in>  c`(V[?G])} \<subseteq> A" by auto
    moreover 
    have  "A \<subseteq> \<Union> {{x \<in> A. c x = j} |j. j \<in>  c`(V[?G])}"
    proof
      fix x
      assume h: "x \<in> A"
      hence "x\<in>V[?G]" using incomparability_graph_def
        by (metis (lifting) fst_conv) 
      hence "\<exists>j. c(x) = j" using assms coloring_def
        by metis
      then obtain j where j: "c(x) = j" by auto
      hence "x\<in>{x \<in> A. c x = j |j \<in>  c`(V[?G])}" using h by auto
      thus "x\<in>\<Union> {{x \<in> A. c x = j} |j. j \<in> c`(V[?G])}" using j
        using \<open>x \<in> V[incomparability_graph r A]\<close> by blast
    qed  
    finally 
    show  "\<Union> {{x \<in> A. c x = j} |j. j \<in> c`(V[?G]) } = A" by auto
  qed
  have 2:  "disjoint {{x \<in> A. c x = j} |j. j \<in> c`(V[?G])}" 
    using assms coloring_def
    by (smt (verit, best) disjnt_iff mem_Collect_eq pairwiseI)    
  have 3: "{} \<notin> {{x \<in> A. c x = j} |j. j \<in> c`(V[?G])}"  
    using assms coloring_def non_empty_set_color
    by (smt (verit, best) Collect_empty_eq fst_conv incomparability_graph_def mem_Collect_eq)   
  show ?thesis using 1 2 3
    by (simp add: incomparability_graph_def partition_on_def)
qed

lemma (in part_order) coloring_total:
  assumes "coloring c k (incomparability_graph r A)" and "j \<in> c`A"
  shows "total_on {x \<in> A. c x = j} r"
proof-
  {
    fix x y
    assume h1: "x\<in>{x \<in> A. c x = j}" and h2: "y\<in>{x \<in> A. c x = j}" 
    have "x \<noteq> y \<longrightarrow> (x, y) \<in> r \<or> (y, x) \<in> r" 
    proof
      assume "x \<noteq> y" 
      thus  "(x, y) \<in> r \<or> (y, x) \<in> r" using h1 h2 assms incomparability_graph_def[of r A]
        by (smt (verit, best) coloring_def mem_Collect_eq snd_conv)  
    qed
  }
  thus ?thesis using total_on_def
    by blast 
qed 

lemma partition_card_le_colors:
  assumes col: "coloring c k G" 
  shows "card ({{x \<in> A. c x = j} | j. j \<in> c`(V[G])}) \<le> k"
proof(cases "k = 0")
  assume "k = 0" 
  hence "V[G] = {}" using assms coloring_def
    by (meson coloring_nonemptygraph colorable_def dual_order.irrefl)
  thus ?thesis
    by simp
next 
  assume "k \<noteq> 0" 
  hence "k > 0" by auto
  let ?P = "{{x \<in> A. c x = j} | j. j \<in> c`(V[G])}"
  have P_image: "?P = (\<lambda>j. {x \<in> A. c x = j})`(c`(V[G]))"
    by auto
  have fin_colors: "finite (c`(V[G]))"
  proof -
    have "card (c`(V[G])) \<le> k"
      using coloring_card_image[OF col] by simp 
    thus ?thesis
      by (metis (no_types, lifting) bounded_nat_set_is_finite col coloring_def imageE)
  qed
  have "card ?P \<le> card (c ` (V[G]))"
    unfolding P_image  using fin_colors 
    by (rule card_image_le)
  also have "... \<le> k"
    using coloring_card_image[OF col] by simp
  finally show ?thesis by simp
qed

lemma (in part_order) coloring_chain_decomposition1:
  assumes "coloring c k (incomparability_graph r A)"
  shows  "chain_decomposition A r {{x \<in> A. c x = j} |j. j \<in> c`A} \<and> 
          card ({{x \<in> A. c x = j} |j. j \<in> c`A})\<le> k "
proof-
  have "chain_decomposition A r {{x \<in> A. c x = j} |j. j \<in> c`A}"
    using coloring_particion[of c k r A] coloring_total[of c k] 
    by (smt (verit, best) Dilworth_Finite.chain_def Sup_upper assms(1) 
        chain_decomposition_def mem_Collect_eq  p_o_translation partition_onD1) 
  moreover
  have "card ({{x \<in> A. c x = j} |j. j \<in> c`A}) \<le> k" using assms partition_card_le_colors
      coloring_def[of c k "(incomparability_graph r A)"]  
      coloring_card_image[of c k "(incomparability_graph r A)"]
    using incomparability_graph_def[of r A] by fastforce
  ultimately show ?thesis by auto
qed

lemma coloring_chain_decomposition_finite:
  assumes "coloring c k (incomparability_graph r A)"
  shows "finite ({{x \<in> A. c x = j} | j. j \<in> c`A})"
proof -
  let ?CD = "{{x \<in> A. c x = j} | j. j \<in> c`A}"
  have "?CD = (\<lambda>j. {x \<in> A. c x = j}) ` (c`A)"
    by auto
  moreover have "finite (c`A)"
  proof -
    have "c`A \<subseteq> {0..<k}"
      using assms
      unfolding coloring_def incomparability_graph_def
      by auto
    thus ?thesis
      using finite_lessThan finite_subset
      by blast
  qed
  ultimately show ?thesis
    by simp
qed

lemma (in part_order) coloring_chain_decomposition:
  assumes "coloring c k (incomparability_graph r A)" 
  shows "(\<exists>CD. chain_decomposition A r CD \<and>  card CD \<le> k \<and> finite CD)"
  using coloring_chain_decomposition1  coloring_chain_decomposition_finite assms
  by blast 

lemma (in part_order_countable) width_coloring_finite:
  assumes "(\<forall>AC. anti_chain A r AC \<longrightarrow> card AC \<le> m)" and "finite A"
  shows "(\<exists>c. \<exists>k. coloring c k (incomparability_graph r A) \<and> k \<le> m)"
proof-
  have  "\<exists>sCD. chain_decomposition A r sCD \<and> card sCD \<le> m" 
    by (metis assms(2) assms(1) smallest_chain_decomposition_def largest_antichain_def 
        Dilworth_Finite)  
  then obtain sCD where sCD:  "chain_decomposition A r sCD \<and> card sCD \<le> m" by auto
  hence 1:"(colorable (incomparability_graph r A) (card sCD))"
    using  chain_decomposition_def chain_decomposition_colorable
    by (metis Dilworth_Finite.chain_def assms(2) finite_elements)
  have "\<exists>c. coloring c (card sCD) (incomparability_graph r A) \<and> card sCD \<le> m"
    using colorable_def 1 sCD 
    by blast 
  thus ?thesis 
    using colorable_def coloring_def sCD
    by (smt (verit, best) \<open>chain_decomposition A r sCD \<and> card sCD \<le> m\<close> coloring_def order_trans) 
qed

lemma (in part_order_countable) partial_order_restrc:
  assumes "B\<subseteq>A"
  shows "partial_order_on B (Restr r B)" 
  using partial_order_on_def[of B "(Restr r B)"]
  by (smt (verit, best) Int_iff Sigma_cong antisym_Restr assms mem_Sigma_iff p_o_translation 
      partial_order_on_def preorder_on_def refl_on_def subsetD subsetI trans_Restr)

lemma (in part_order_countable) antichain_restrc:
  assumes "anti_chain A r AC" and "B\<subseteq>A"
  shows "anti_chain B (Restr r B) (AC \<inter> B)" 
  using partial_order_restrc[of B] anti_chain_def[of B "(Restr r B)" "(AC \<inter> B)"]
  by (meson IntE anti_chain_def anti_total_def assms(1,2) inf_le2)   

lemma (in part_order_countable) width_induced_subgraph:
  assumes "\<forall>AC. anti_chain A r AC \<longrightarrow> card AC \<le> w" and "finite B"
  shows  "\<forall>ACB. anti_chain B (Restr r B) ACB \<longrightarrow> card ACB \<le> w" using assms
  by (smt (verit, del_insts) Int_iff anti_chain_def anti_total_def mem_Sigma_iff 
      p_o_translation partial_order_onD(1,4) refl_on_def subset_iff)

lemma graph_incomparability:
  "is_graph (incomparability_graph r A)" 
  using is_graph_def incomparability_graph_def
  by (smt (verit, ccfv_SIG) mem_Collect_eq split_pairs2) 

lemma induced_subgraph_incomparability:  
  assumes "is_induced_subgraph H (incomparability_graph r A) \<and> finite_graph H"
  shows "\<exists>B. (finite B) \<and> B = V[H] \<and> (E[H] = E[(incomparability_graph r A)] \<inter> (B\<times>B)) \<and> B \<subseteq> A"        
  using assms is_induced_subgraph_def incomparability_graph_def
  by (metis (mono_tags, lifting) finite_graph_def fst_conv)

lemma  incomparability_subgraph: 
  assumes "is_graph (incomparability_graph r A)"    
    and "is_subgraph H (incomparability_graph r A) \<and> finite_graph H"
  shows "\<exists>B. (finite B) \<and> B = V[H] \<and> (E[H] \<subseteq> E[(incomparability_graph r A)] \<inter> (B\<times>B)) \<and> B \<subseteq> A"
  using assms is_subgraph_def incomparability_graph_def
  by (metis (no_types, lifting) Sigma_cong finite_graph_def fst_conv)

lemma (in part_order_countable) colorable_induced_subgraph:
  assumes "\<forall>AC. anti_chain A r AC \<longrightarrow> card AC \<le> m" 
  shows "(\<forall>H. is_induced_subgraph H (incomparability_graph r A) \<and>  finite_graph H \<longrightarrow> colorable H m)" 
proof-  
  have "\<forall>H. is_induced_subgraph H (incomparability_graph r A) \<and> finite_graph H \<longrightarrow> colorable H m"
  proof (rule allI, rule impI)
    fix H  
    assume H_assms: "is_induced_subgraph H (incomparability_graph r A) \<and> finite_graph H"     
    have "\<exists>B. (finite B) \<and> B = V[H] \<and> (E[H] = E[(incomparability_graph r A)] \<inter> (B\<times>B)) \<and> B \<subseteq> A"
      using incomparability_subgraph assms(1)
      by (simp add: H_assms graph_incomparability induced_subgraph_incomparability)
    then obtain B where B: "(finite B) \<and> B = V[H] \<and> (E[H] = E[(incomparability_graph r A)] \<inter> (B\<times>B)) \<and> B \<subseteq> A" 
      by auto
    have AC_B: "\<forall>AC. anti_chain B (Restr r B) AC \<longrightarrow> card AC \<le> m"
      using B antichain_restrc
      by (smt (verit, ccfv_threshold) Int_iff anti_chain_def anti_total_def assms mem_Sigma_iff 
          p_o_translation subset_iff)
    have poB: "partial_order_on B (Restr r B)"
      using partial_order_restrc B p_o_translation  
      by auto
    have "\<exists>c.\<exists>k. coloring c k (incomparability_graph (Restr r B) B) \<and> k \<le> m"
      using AC_B B part_order_countable.width_coloring_finite part_order_countable_def part_order_def poB by blast
    then obtain  c k where c: "coloring c k (incomparability_graph (Restr r B) B) \<and> k \<le> m" by auto    
    hence "coloring c k H"
      using B induced_subgraph_incomparability 
      by (simp add: coloring_def incomparability_graph_def)
    hence "coloring c m H" using coloring_def
      by (metis c inf.absorb_iff2 inf.strict_boundedE) 
    thus "colorable H m"
      using colorable_def by blast
  qed
  thus ?thesis
    by blast
qed

lemma exists_smallest_chain_decomposition:
  assumes "\<exists>C. chain_decomposition A r C"
  shows "\<exists>C. smallest_chain_decomposition A r C"
proof-
  let ?Q = "\<lambda>n. \<exists>C. chain_decomposition A r C \<and> card C = n"
  obtain k where k1: "?Q k" and k2: "\<forall>m<k. \<not> ?Q m"
    using assms ex_least_nat_le[of ?Q ]  by blast
  obtain C where CD1: "chain_decomposition A r C" and CD2: "card C = k"
    using k1 by blast 
  have minC: "\<forall>P. chain_decomposition A r P \<longrightarrow> card C \<le> card P"
  proof(rule allI)
    fix P
    show  "chain_decomposition A r P \<longrightarrow> card C \<le> card P"
    proof
      assume PCD: "chain_decomposition A r P"
      show "card C \<le> card P"
      proof-
        have 1: "\<not> card P < k"
        proof
          assume "card P < k"
          hence "?Q (card P)"
            using PCD by blast      
          with k2 show False
            by (metis k2 \<open>\<exists>C. chain_decomposition A r C \<and> card C = card P\<close> \<open>card P < k\<close>) 
        qed 
        thus "card C \<le> card P"  using CD2 1 not_le_imp_less by blast 
      qed
    qed
  qed
  have "smallest_chain_decomposition A r C"
    unfolding smallest_chain_decomposition_def
    using CD1 minC by blast
  thus ?thesis by blast
qed

lemma (in part_order_countable) exists_largest_antichain:
  assumes "\<forall>AC. anti_chain A r AC \<longrightarrow> card AC \<le> m" 
  shows "\<exists>lgAC. largest_antichain A r lgAC"
proof-
  let ?P = "{card B | B. anti_chain A r B}"
  have 1:"?P \<subseteq> {0..m}"
    using assms(1) atLeastAtMost_iff by blast
  moreover
  have "anti_chain A r {}" 
    using anti_chain_def  anti_total_def p_o_translation 
    by blast
  hence 2: "?P \<noteq> {}"
    by blast
  ultimately 
  have "\<exists>k. k = Max ?P"
    by blast 
  then obtain k where  "k = Max ?P" by auto
  moreover 
  have finP: "finite ?P" 
    using 1 by (meson finite_atLeastAtMost finite_subset)
  hence  k_in: "k \<in> ?P" 
    using Max_in calculation 2 by auto  
  then obtain lgAC where
    lgAC_antichain: "anti_chain A r lgAC" and lgAC_card: "card lgAC = k"
    by blast
  have largest: "largest_antichain A r lgAC"
  proof(unfold largest_antichain_def, intro conjI allI impI)
    show "anti_chain A r lgAC"
      by (rule lgAC_antichain)
  next
    fix C
    assume Canti: "anti_chain A r C"
    have "card C \<in> ?P" 
      using Canti by blast
    hence "card C \<le> k"
      using finP calculation by auto
    hence "card C \<le> card lgAC"
      using lgAC_card  by simp
    thus "card C \<le> card lgAC" 
      by metis 
  qed  
  thus "\<exists>lgAC. largest_antichain A r lgAC" by auto
qed

theorem (in part_order_countable) Dilworth_countable_aux:
  assumes "largest_antichain A r lgAC" 
  shows "(\<exists>CD. (chain_decomposition A r CD \<and> finite CD) \<and> card CD \<le> card lgAC)" 
proof- 
  have 1: "is_graph (incomparability_graph r A)" 
    using  graph_incomparability by auto
  have "(colorable (incomparability_graph r A) (card lgAC))"
  proof-
    have "\<forall>H. is_induced_subgraph H (incomparability_graph r A) \<and> finite_graph H \<longrightarrow>  
          colorable H (card lgAC)" 
      using colorable_induced_subgraph assms
      by (metis largest_antichain_def)
    thus ?thesis
      using "1"  deBruijn_Erdos_coloring_for_finite_induced_subgraphs 
      by metis
  qed  
  thus ?thesis 
    using  colorable_def coloring_chain_decomposition         
    by metis
qed

definition largest_finite_antichain :: "'a set \<Rightarrow> 'a rel \<Rightarrow> 'a set \<Rightarrow> bool"
  where "largest_finite_antichain A r B \<equiv>
      anti_chain A r B \<and> finite B \<and> (\<forall>C. anti_chain A r C \<and> finite C \<longrightarrow> card C \<le> card B)"

lemma (in part_order_countable) exists_largest_finite_antichain:
  assumes H: "\<forall>AC. anti_chain A r AC \<and> finite AC \<longrightarrow> card AC \<le> m"
  shows "\<exists>lgAC. largest_finite_antichain A r lgAC"
proof -
  let ?P = "{card B | B. anti_chain A r B \<and> finite B}"
  have subsetP: "?P \<subseteq> {0..m}"
  proof
    fix n
    assume "n \<in> ?P"
    then obtain B where
      B: "anti_chain A r B \<and> finite B" and n: "n = card B"
      by blast
    have "card B \<le> m" 
      using H B by blast
    thus "n \<in> {0..m}"
      using n by auto
  qed
  have anti_empty: "anti_chain A r {}"
    unfolding anti_chain_def anti_total_def
    using p_o_translation by auto
  hence 2: "?P \<noteq> {}"
    by auto
  have finP: "finite ?P"
    using subsetP finite_atLeastAtMost
    by (rule finite_subset)
  let ?k = "Max ?P"
  have k_in: "?k \<in> ?P"
    using "2" Max_eq_iff finP by blast
  then obtain lgAC where
    lgAC1: "anti_chain A r lgAC \<and> finite lgAC" and lgAC2: "card lgAC = ?k"
    by fastforce
  have largest:
    "largest_finite_antichain A r lgAC"
  proof (unfold largest_finite_antichain_def, intro conjI allI impI)
    show "anti_chain A r lgAC"
      using lgAC1 by blast
    show "finite lgAC"
      using lgAC1 by blast
    fix C
    assume C: "anti_chain A r C \<and> finite C"
    have "card C \<in> ?P"
      using C by blast
    hence "card C \<le> ?k"
      using finP k_in by simp
    thus "card C \<le> card lgAC"
      using lgAC2 by simp
  qed
  show ?thesis
    using largest by blast
qed

(*Since the partition in singletons of any partial order is always a chain decomposition, 
  and in Isabelle the Cardinal of infinite sets is defined as zero, in the countable case, 
  it is necessary to distinguish the smallest Cardinal of finite chain decompositions to 
  have a correct notion of smallest chain decomposition *)

definition finite_smallest_chain_decomposition :: "'a set \<Rightarrow> 'a rel \<Rightarrow>'a set set \<Rightarrow> bool" where
  "finite_smallest_chain_decomposition A r CD \<equiv> 
  chain_decomposition A r CD  \<and> 
  finite CD \<and> 
  (\<forall>P. chain_decomposition A r P \<and> finite P  \<longrightarrow> card CD \<le> card P)"

lemma exists_smallest_finite_chain_decomposition:
  assumes "\<exists>CD. chain_decomposition A r CD \<and> finite CD"
  shows "\<exists>sCD. finite_smallest_chain_decomposition A r sCD"
proof-
  let ?Q = "\<lambda>n. \<exists>C. chain_decomposition A r C \<and> finite C \<and> card C = n"
  obtain k where k1: "?Q k" and k2: "\<forall>m<k. \<not> ?Q m"
    using assms ex_least_nat_le[of ?Q ]  by blast
  obtain sC where CD1: "chain_decomposition A r sC \<and> finite sC" and CD2: "card sC = k"
    using k1 by blast 
  have minC: "\<forall>P. chain_decomposition A r P \<and> finite P \<longrightarrow> card sC \<le> card P"
  proof(intro allI impI)
    fix P
    assume PCD: "chain_decomposition A r P \<and> finite P"
    show "card sC \<le> card P"
    proof-
      have 1: "\<not> card P < k"
      proof
        assume "card P < k"
        hence "?Q (card P)"
          using PCD by blast      
        with k2 show False
          by (metis \<open>\<exists>C. chain_decomposition A r C \<and> finite C \<and> card C = card P\<close> k2 \<open>card P < k\<close>)
      qed 
      thus "card sC \<le> card P"  using CD2 1 not_le_imp_less by blast 
    qed
  qed
  have "finite_smallest_chain_decomposition A r sC"
    unfolding finite_smallest_chain_decomposition_def
    using CD1 minC by blast
  thus ?thesis by blast
qed

theorem (in part_order_countable) Dilworth_countable:
  assumes "\<exists>m.\<forall>AC. anti_chain A r AC \<and> finite AC  \<longrightarrow> card AC \<le> m"
  shows "\<exists>smD. \<exists>lgAC. finite_smallest_chain_decomposition A r smD \<and> largest_finite_antichain A r lgAC \<and>
        card smD = card lgAC"
proof-
  obtain lgAC where lgAC1: "largest_finite_antichain A r lgAC" 
    using assms exists_largest_finite_antichain 
    by auto 
  hence lgAC: "largest_antichain A r lgAC \<and> finite lgAC" 
    using largest_finite_antichain_def
    by (metis bot_nat_0.extremum card_eq_0_iff largest_antichain_def) 
  then obtain sCD  where sCD: "(chain_decomposition A r sCD \<and> finite sCD) \<and> card sCD \<le> card lgAC" 
    by (meson Dilworth_countable_aux)
  then obtain C where C: "finite_smallest_chain_decomposition A r C " 
    using exists_smallest_finite_chain_decomposition  finite_smallest_chain_decomposition_def 
    by blast
  hence "card lgAC \<le> card C" 
    using lgAC sCD antichain_le_chain_decomposition[of C lgAC]
      largest_antichain_def finite_smallest_chain_decomposition_def
    by blast
  moreover
  have "card C \<le> card lgAC" using C finite_smallest_chain_decomposition_def sCD
    using le_trans by blast
  ultimately
  have "card lgAC = card C" by auto
  thus  ?thesis using C lgAC1
    by metis 
qed

end