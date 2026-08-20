(* Hall's Theorem - Graphs' version
   Fabian Fernando Serrano Suárez  UNAL Manizales
   Thaynara Arielly de Lima        Universidade Federal de Goiáis 
   Mauricio Ayala-Rincón           Universidade de Brasília
   Last modified: 3 Mar, 2026
*)
theory Hall_Theorem_Graphs
  imports
           "Background_on_graphs" 
           "HOL-Library.Countable_Set"
           "Hall_Theorem"  


begin

section \<open>Hall Theorem for countable (infinite) Graphs\<close>

text\<open>This section formalizes Hall Theorem for countable infinite Graphs (\cite{SARdL2024}). The proof applied a proof of Hall's theorem for countable infinite families of sets, obtained by the authors directly from the compactness theorem for propositional logic. The proof is based on Smullyan's approach given in the third chapter of his influential textbook on mathematical logic \cite{Smullyan}, based on Henkin's model existence theorem.  It follows the impeccable presentation in Fitting's textbook \cite{Fitting}.   \<close>

definition dirBD_to_Hall::
   "('a,'b) pre_digraph \<Rightarrow> 'a set \<Rightarrow> 'a set \<Rightarrow> 'a set \<Rightarrow> ('a  \<Rightarrow> 'a set) \<Rightarrow> bool" 
   where 
   "dirBD_to_Hall G X Y I S \<equiv>
   dir_bipartite_digraph G X Y \<and> I = X \<and> (\<forall>v\<in>I. (S v) = (neighbourhood G v))"  

theorem dir_BD_to_Hall: 
   "dirBD_perfect_matching G X Y E \<longrightarrow> 
    system_representatives (neighbourhood G) X (E_head G E)"
proof(rule impI)
  assume dirBD_pm :"dirBD_perfect_matching G X Y E"
  show "system_representatives (neighbourhood G) X (E_head G E)"
  proof-
    have wS : "dirBD_to_Hall G X Y X (neighbourhood G)" 
    using dirBD_pm
    by(unfold dirBD_to_Hall_def,unfold dirBD_perfect_matching_def,
       unfold dirBD_matching_def, auto)
    have arc: "E \<subseteq> arcs G" using dirBD_pm 
      by(unfold dirBD_perfect_matching_def, unfold dirBD_matching_def,auto)
    have a: "\<forall>i. i \<in> X \<longrightarrow> E_head G E i \<in> neighbourhood G i"
    proof(rule allI)
      fix i
      show "i \<in> X \<longrightarrow> E_head G E i \<in> neighbourhood G i"
      proof
        assume 1: "i \<in> X"
        show "E_head G E i \<in> neighbourhood G i"
        proof- 
          have 2: "\<exists>!e \<in> E. tail G e = i"
          using 1 dirBD_pm Edge_unicity_in_dirBD_P_matching [of X G Y E ]
           by auto
          then obtain e where 3: "e \<in> E \<and> tail G e = i" by auto
        thus "E_head G E i \<in> neighbourhood G i"
          using  dirBD_pm 1 3 E_head_in_neighbourhood[of G X Y E e i]
          by (unfold dirBD_perfect_matching_def, auto)
        qed
      qed
    qed
    thus "system_representatives (neighbourhood G) X (E_head G E)"
    using a dirBD_pm dirBD_matching_inj_on [of G X Y E] 
    by (unfold system_representatives_def, auto)
  qed
qed

lemma marriage_necessary_graph:
  assumes "(dirBD_perfect_matching G X Y E)" and "\<forall>i\<in>X. finite (neighbourhood G i)"
  shows "\<forall>J\<subseteq>X. finite J \<longrightarrow> (card J) \<le> card (\<Union> (neighbourhood G ` J))"
proof(rule allI, rule impI)
  fix J
  assume hip1:  "J \<subseteq> X" 
  show "finite J \<longrightarrow> card J \<le> card  (\<Union> (neighbourhood G ` J)) "
  proof  
    assume hip2: "finite J"
    show  "card J \<le> card (\<Union> (neighbourhood G ` J))"
    proof-
      have  "\<exists>R. (\<forall>i\<in>X. R i \<in> neighbourhood G i) \<and> inj_on R X"
        using assms  dir_BD_to_Hall[of G X Y E]
        by(unfold system_representatives_def, auto) 
      thus ?thesis using assms(2)  marriage_necessity[of X "neighbourhood G" ] hip1 hip2 by auto
    qed
  qed
qed

lemma neighbour3:
  fixes  G :: "('a, 'b) pre_digraph" and X:: "'a set" 
  assumes "dir_bipartite_digraph G X Y" and "x\<in>X"
  shows "neighbourhood G x = {y |y. \<exists>e. e \<in> arcs G \<and> ((x = tail G e) \<and> (y = head G e))}" 
proof
  show  "neighbourhood G x \<subseteq> {y |y. \<exists>e. e \<in> arcs G \<and> x = tail G e \<and> y = head G e}"
  proof
    fix z
    assume hip:   "z \<in> neighbourhood G x" 
    show "z \<in> {y |y. \<exists>e. e \<in> arcs G \<and> x = tail G e \<and> y = head G e}"
    proof-
      have  "neighbour G z x" using hip  by(unfold neighbourhood_def, auto)  
      hence  "\<exists>e. e \<in> arcs G \<and>((z = (head G e) \<and> x =(tail G e) \<or> 
                             ((x = (head G e) \<and> z = (tail G e)))))" 
        using assms  by (unfold neighbour_def, auto) 
      hence  "\<exists>e. e \<in> arcs G \<and> (z = (head G e) \<and> x =(tail G e))"
        using assms
        by(unfold dir_bipartite_digraph_def, unfold bipartite_digraph_def, unfold tails_def, blast)
      thus ?thesis by auto
    qed
  qed
  next
  show "{y |y. \<exists>e. e \<in> arcs G \<and> x = tail G e \<and> y = head G e} \<subseteq> neighbourhood G x"
  proof
    fix z
    assume hip1: "z \<in> {y |y. \<exists>e. e \<in> arcs G \<and> x = tail G e \<and> y = head G e}"
    thus  "z \<in> neighbourhood G x" 
      by(unfold neighbourhood_def, unfold neighbour_def, auto)
  qed
qed

lemma perfect:
  fixes  G :: "('a, 'b) pre_digraph" and X:: "'a set" 
  assumes "dir_bipartite_digraph G X Y" and "system_representatives (neighbourhood G) X R"
  shows  "tails_set G {e |e. e \<in> (arcs G) \<and> ((tail G e) \<in> X \<and> (head G e) = R(tail G e))} = X" 
proof(unfold tails_set_def)
  let ?E = "{e |e. e \<in> (arcs G) \<and> ((tail G e) \<in> X \<and> (head G e) = R (tail G e))}"
  show  "{tail G e |e. e \<in> ?E \<and> ?E \<subseteq> arcs G} = X"
  proof
    show "{tail G e |e. e \<in> ?E \<and> ?E \<subseteq> arcs G}\<subseteq> X"
    proof
      fix x
      assume hip1: "x \<in> {tail G e |e. e \<in> ?E \<and> ?E \<subseteq> arcs G}"
      show "x\<in>X"
      proof-
        have "\<exists>e. x = tail G e \<and> e \<in> ?E \<and> ?E \<subseteq> arcs G" using hip1 by auto
        then obtain e where e: "x = tail G e \<and> e \<in> ?E \<and> ?E \<subseteq> arcs G" by auto
        thus "x\<in>X"
          using assms(1) by(unfold dir_bipartite_digraph_def, unfold tails_def, auto)
      qed
    qed
    next
    show "X \<subseteq> {tail G e |e. e \<in> ?E \<and> ?E \<subseteq> arcs G}"
    proof
      fix x
      assume hip2: "x\<in>X"
      show "x\<in>{tail G e |e. e \<in> ?E \<and> ?E \<subseteq> arcs G}"
      proof-
        have "R (x) \<in> neighbourhood G x"
          using assms(2) hip2 by (unfold system_representatives_def, auto)
        hence "\<exists>e. e\<in> arcs G \<and> (x = tail G e \<and> R(x) = (head G e))" 
          using assms(1) hip2 neighbour3[of G  X Y] by auto
        moreover
        have  "?E \<subseteq> arcs G" by auto 
        ultimately show ?thesis
          using hip2 assms(1) by(unfold dir_bipartite_digraph_def, unfold tails_def, auto)
      qed
    qed
  qed
qed

lemma dirBD_matching:
  fixes  G :: "('a, 'b) pre_digraph" and X:: "'a set" 
  assumes "dir_bipartite_digraph G X Y" and R: "system_representatives (neighbourhood G) X R"
  and  "e1 \<in> arcs G \<and> tail G e1 \<in> X" and "e2 \<in> arcs G \<and> tail G e2 \<in> X" 
  and  "R(tail G e1) = head G e1" 
  and  "R(tail G e2) = head G e2"
shows "e1 \<noteq> e2 \<longrightarrow> head G e1 \<noteq> head G e2 \<and> tail G e1 \<noteq> tail G e2"
proof
  assume hip: "e1 \<noteq> e2"
  show "head G e1 \<noteq> head G e2 \<and> tail G e1 \<noteq> tail G e2"
  proof- 
    have  "(e1 = e2) = (head G e1 = head G e2 \<and> tail G e1 = tail G e2)"
      using assms(1)  assms(3-4)  by(unfold dir_bipartite_digraph_def, auto)
    hence 1:  "tail G e1 = tail G e2 \<longrightarrow> head G e1 \<noteq> head G e2" 
      using hip assms(1)  by auto
    have  2:  "tail G e1 = tail G e2 \<longrightarrow> head G e1 = head  G e2"  
      using  assms(1-2) assms(5-6)  by auto
    have 3: "tail G e1 \<noteq> tail G e2"
    proof(rule notI)
      assume *:  "tail G e1 = tail G e2"
      thus False using 1 2 by auto
    qed
    have 4:  "tail G e1 \<noteq> tail G e2 \<longrightarrow> head G e1 \<noteq> head G e2" 
      proof
        assume **: "tail G e1 \<noteq> tail G e2"
        show  "head G e1 \<noteq> head G e2"
          using ** assms(3-6) R  inj_on_def[of R X] 
          system_representatives_def[of "(neighbourhood G)" X R] by auto
      qed
    thus ?thesis using 3 by auto
  qed     
qed

lemma marriage_sufficiency_graph:
  fixes  G :: "('a::countable, 'b::countable) pre_digraph" and X:: "'a set" 
  assumes "dir_bipartite_digraph G X Y"  and "\<forall>i\<in>X. finite (neighbourhood G i)"   
  shows
  "(\<forall>J\<subseteq>X. finite J \<longrightarrow> (card J) \<le> card (\<Union> (neighbourhood G ` J))) \<longrightarrow>
   (\<exists>E. dirBD_perfect_matching G X Y E)"
proof(rule impI)
  assume hip: "\<forall>J\<subseteq>X. finite J \<longrightarrow> card J \<le> card (\<Union> (neighbourhood G ` J))" 
  show "\<exists>E. dirBD_perfect_matching G X Y E"
  proof-
    have "\<exists>R. system_representatives (neighbourhood G) X R" 
      using assms hip Hall[of X "neighbourhood G"] by auto
    then obtain R where R: "system_representatives (neighbourhood G) X R" by auto
    let ?E = "{e |e. e \<in> (arcs G) \<and> ((tail G e) \<in> X \<and> (head G e) = R (tail G e))}" 
    have "dirBD_perfect_matching G X Y ?E"
    proof(unfold dirBD_perfect_matching_def, rule conjI)
      show "dirBD_matching G X Y ?E"    
      proof(unfold dirBD_matching_def, rule conjI)
        show "dir_bipartite_digraph G X Y" using assms(1) by auto
      next
        show "?E \<subseteq> arcs G \<and> (\<forall>e1\<in>?E. \<forall>e2\<in>?E.
             e1 \<noteq> e2 \<longrightarrow> head G e1 \<noteq> head G e2 \<and> tail G e1 \<noteq> tail G e2)"
        proof(rule conjI)
          show  "?E \<subseteq> arcs G"  by auto 
        next
          show "\<forall>e1\<in>?E. \<forall>e2\<in>?E. e1 \<noteq> e2 \<longrightarrow> head G e1 \<noteq> head G e2 \<and> tail G e1 \<noteq> tail G e2"   
          proof
            fix e1
            assume H1: "e1 \<in> ?E"
            show "\<forall>e2\<in> ?E. e1 \<noteq> e2 \<longrightarrow> head G e1  \<noteq> head G e2 \<and> tail G e1 \<noteq> tail G e2"
            proof
              fix e2
              assume H2: "e2 \<in> ?E"
              show  "e1 \<noteq> e2 \<longrightarrow> head G e1 \<noteq> head G e2 \<and> tail G e1 \<noteq> tail G e2" 
              proof-
                have  "e1 \<in> (arcs G) \<and> ((tail G e1) \<in> X \<and> (head G e1) = R (tail G e1))" using H1 by auto
                hence 1:  "e1 \<in> (arcs G) \<and> (tail G e1) \<in> X" and 2:  "R (tail G e1) = (head G e1)" by auto   
                have  "e2 \<in> (arcs G) \<and> ((tail G e2) \<in> X \<and> (head G e2) = R (tail G e2))" using H2 by auto
                hence 3:  "e2 \<in> (arcs G) \<and> (tail G e2) \<in> X" and 4: "R (tail G e2) = (head G e2)" by auto
                show ?thesis using assms(1) R  1 2 3 4 assms(1) dirBD_matching[of G X Y R e1 e2] by auto
              qed
            qed
          qed
        qed
      qed
  next
    show "tails_set G {e |e. e \<in> arcs G \<and> tail G e \<in> X \<and> head G e = R (tail G e)} = X"
       using perfect[of G X Y]  assms(1) R by auto
    qed thus ?thesis by auto
  qed
qed

(* Graph version of Hall's Theorem *)

theorem Hall_digraph:
 fixes  G :: "('a::countable, 'b::countable) pre_digraph" and X:: "'a set"
  assumes "dir_bipartite_digraph G X Y"  and "\<forall>i\<in>X. finite (neighbourhood G i)"
  shows "(\<exists>E. dirBD_perfect_matching G X Y E) \<longleftrightarrow>
  (\<forall>J\<subseteq>X. finite J \<longrightarrow> (card J) \<le> card (\<Union> (neighbourhood G ` J)))"
proof
  assume hip1:  "\<exists>E. dirBD_perfect_matching G X Y E"
  show  "(\<forall>J\<subseteq>X. finite J \<longrightarrow> (card J) \<le> card (\<Union> (neighbourhood G ` J)))"
    using hip1 assms(1-2) marriage_necessary_graph[of G X Y] by auto 
next
  assume hip2: "\<forall>J\<subseteq>X. finite J \<longrightarrow> card J \<le> card (\<Union> (neighbourhood G ` J))"
  show "\<exists>E. dirBD_perfect_matching G X Y E"  using assms  marriage_sufficiency_graph[of G X Y] hip2
  proof-
    have "(\<forall>J\<subseteq>X. finite J \<longrightarrow> (card J) \<le> card (\<Union> (neighbourhood G ` J)))
                                                         \<longrightarrow> (\<exists>E. dirBD_perfect_matching G X Y E)"
      using assms marriage_sufficiency_graph[of G X Y] by auto
    thus ?thesis using hip2 by auto
  qed
qed


end
