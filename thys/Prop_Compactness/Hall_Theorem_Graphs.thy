(* Hall's Theorem - Graphs' version
   Fabian Fernando Serrano Suárez  UNAL Manizales
   Thaynara Arielly de Lima        Universidade Federal de Goiáis 
   Mauricio Ayala-Rincón           Universidade de Brasília
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

(*Feedback from and to LPAR 2023 - reviewer on "best proofs" 
Short proofs are of interest when the main objective is automating proofs. However, such an aim can be reached by applying hammers nowadays. When the central aim is generating proofs that provide meaningful feedback on the importance of proof assistants for the profession of a mathematician, short proofs are not necessarily a plus; instead, the focus is on detailed and didactic proofs. From this perspective, having an automatically generated single-step proof is neither elegant nor advantageous. Below, we include the specification provided by a reviewer and show how short proofs can be obtained through the application of the Isabelle Sledgehammer, providing, in contrast, complete proofs, those that are most convenient for our primary educational purposes. 
*)

(* Below a specification of sdr in families of indexed sets and perfect matchings
in bipartite digraphs using locales provided by the reviewer *) 


(* Family of indexed sets *) 
locale set_family =
  fixes I :: "'a set" and X :: "'a \<Rightarrow> 'b set"

(* SDR in an indexed family of sets *)
locale sdr = set_family +
  fixes repr :: "'a \<Rightarrow> 'b"
  assumes inj_repr: "inj_on repr I" and repr_X: "x \<in> I \<Longrightarrow> repr x \<in> X x"

(* Bipartite digraph *)
locale bipartite_digraph =
  fixes X :: "'a set" and Y :: "'b set" and E :: "('a \<times> 'b) set"
  assumes E_subset: "E \<subseteq> X \<times> Y"

(* Our specification in the spirit of locales following the reviewer's
suggestion of a bipartite digraph with a countable set of left-hand 
side vertexes X, whose neighborhoods are also finite sets *)
locale Count_Nbhdfin_bipartite_digraph =  
  fixes X :: "'a:: countable set" and Y :: "'b:: countable set" 
             and E :: "('a \<times> 'b) set"
  assumes E_subset: "E \<subseteq> X \<times> Y"
(*  assumes Countable_Tails: "countable X" *)
  assumes Nbhd_Tail_finite: "\<forall>x \<in> X. finite {y. (x, y) \<in> E}"

(* Matching in a bipartite digraph *)
locale matching = bipartite_digraph +
  fixes M :: "('a \<times> 'b) set"
  assumes M_subset: "M \<subseteq> E"
  assumes M_right_unique: "(x, y) \<in> M \<Longrightarrow> (x, y') \<in> M \<Longrightarrow> y = y'"
  assumes M_left_unique: "(x, y) \<in> M \<Longrightarrow> (x', y) \<in> M \<Longrightarrow> x = x'"

(* Perfect matchings in bipartite digraphs *)
locale perfect_matching = matching +
  assumes M_perfect: "fst ` M = X"

(* Regarding the above style of specification, it is clear that
some basic concepts related to Graph Theory are not visible to
the specifier: vertex, edge, whether the left- and right-hand
side sets of vertexes of a bipartite digraph may or not be 
disjunct, etc.  Questions related to types may arise, such as 
whether sets of type "a" and sets of type "b" are different classes 
only nominally, that is only because the type names "a"
and "b" are other.  
*) 

(* Formalization of a perfect matching associated to an sdr in indexed families of sets *)
lemma (in sdr) perfect_matching: 
        "perfect_matching I (\<Union>i\<in>I. X i) (Sigma I X) {(x, repr x)|x. x \<in> I}"
 by  unfold_locales (use inj_repr repr_X in \<open>force simp: inj_on_def\<close>)+

(* Formalization of an sdr associated to a perfect matching *)
lemma (in perfect_matching) sdr: "sdr X (\<lambda>x. {y. (x,y) \<in> E}) (\<lambda>x. the_elem {y. (x,y) \<in> M})"
proof unfold_locales
  define Y where "Y = (\<lambda>x. {y. (x,y) \<in> M})"
  have Y: "\<exists>y. Y x = {y}" if "x \<in> X" for x
    using that M_right_unique M_perfect unfolding Y_def by fastforce
  show "inj_on (\<lambda>x. the_elem (Y x)) X"
    unfolding Y_def inj_on_def
    by (metis (mono_tags, lifting) M_left_unique Y Y_def mem_Collect_eq singletonI the_elem_eq)
  show "the_elem (Y x) \<in> {y. (x, y) \<in> E}" if "x \<in> X" for x
    using Y M_subset Y_def \<open>x \<in> X\<close> by fastforce
qed

(* definition the_elem :: "'a set \<Rightarrow> 'a"
  where "the_elem X = (THE x. X = {x})"
*)
text \<open> From these transformations, the formalization of the countable version of Hall's Theorem for Graphs (more specifically, its sufficiency) can be stated as below; in words ``if for any finite $X_s  \subseteq  X$ the subgraph induced by $X_s$ has a perfect matching then the whole graph has a perfect matching" \<close>
theorem (in Count_Nbhdfin_bipartite_digraph) Hall_Graph:
 assumes "\<exists>g. enumeration (g:: nat \<Rightarrow>'a)" and "\<exists>h. enumeration (h:: nat \<Rightarrow>'b)" 
 shows "(\<forall> Xs \<subseteq> X. (finite Xs) \<longrightarrow>
            (\<exists> Ms.   perfect_matching Xs 
                                      {y. x \<in> Xs  \<and> (x,y) \<in> E} 
                                      {(x,y). x  \<in> Xs  \<and> (x,y) \<in> E}  
                                      Ms)) 
        \<longrightarrow> (\<exists> M.  perfect_matching X Y E M)"
proof(unfold_locales, rule impI)
  assume premisse1: "(\<forall> Xs \<subseteq> X. (finite Xs) \<longrightarrow> 
            (\<exists> Ms.  perfect_matching Xs 
                                     {y. x  \<in> Xs  \<and> (x,y) \<in> E} 
                                     {(x,y). x  \<in> Xs  \<and> (x,y) \<in> E}  
                                     Ms))" 
  show "(\<exists> M. perfect_matching X Y E M)"
  proof-
    have A: "\<forall>Xs\<subseteq>X. finite Xs \<longrightarrow>  card Xs \<le> card (\<Union> ( (\<lambda>x. {y. (x,y) \<in> E}) ` Xs))"
    proof(rule allI, rule impI)
      fix Xs
      define Ys where "Ys =  {y. x  \<in> Xs  \<and> (x,y) \<in> E}"  
      define Es where "Es = {(x,y). x  \<in> Xs  \<and> (x,y) \<in> E}"
      assume hip1:  "Xs \<subseteq> X"
      show "finite Xs \<longrightarrow>  card Xs \<le> card (\<Union> ( (\<lambda>x. {y. (x,y) \<in> E}) ` Xs))"
      proof  
        assume hip2: "finite Xs"
        show  "card Xs \<le> card (\<Union> ( (\<lambda>x. {y. (x,y) \<in> E}) ` Xs))"
        proof-
          have  "(\<exists> Ms. perfect_matching Xs Ys Es Ms)"
          using hip1 hip2 premisse1 Ys_def Es_def by auto
        then obtain Ms where Ms: "perfect_matching Xs Ys Es Ms" 
          using Ys_def Es_def by auto 
        have sdrXs : "sdr Xs (\<lambda>x. {y. (x,y) \<in> Es}) (\<lambda>x. the_elem {y. (x,y) \<in> Ms})"
          using Ms perfect_matching.sdr[of Xs Ys Es Ms]  by blast
        define Rs where "Rs =  (\<lambda>x. the_elem {y. (x,y) \<in> Ms})"
        have inj_Rs: "inj_on Rs Xs"  
          using sdrXs Rs_def sdr.inj_repr[of Xs "(\<lambda>x. {y. (x,y) \<in> Es})" Rs] by auto
        have B: "\<forall>x. x\<in>Xs  \<longrightarrow>  Rs x \<in>  (\<lambda>x. {y. (x,y) \<in> Es}) x" 
        proof(rule allI, rule impI) 
          fix x 
          assume "x\<in>Xs"
          thus "Rs x \<in>  (\<lambda>x. {y. (x,y) \<in> Es}) x" 
            using sdrXs Rs_def sdr.repr_X[of Xs " (\<lambda>x. {y. (x,y) \<in> Es}) " Rs x]
            by auto
        qed 
        have YsE : "Ys = (\<Union>x\<in>Xs. {y. (x, y) \<in> E})"  
        proof 
          show "Ys \<subseteq> (\<Union>x\<in>Xs. {y. (x, y) \<in> E})" 
          proof fix x 
            assume "x \<in> Ys" 
            thus " x \<in> (\<Union>x\<in>Xs. {y. (x, y) \<in> E}) " using Ys_def by blast
          qed
          next
          show "(\<Union>x\<in>Xs. {y. (x, y) \<in> E}) \<subseteq> Ys"
          proof fix x
            assume "x \<in> (\<Union>x\<in>Xs. {y. (x, y) \<in> E})" 
            thus "x \<in> Ys" 
              using Es_def Ms UN_iff bipartite_digraph.E_subset 
              case_prodI matching_def mem_Collect_eq mem_Sigma_iff 
              perfect_matching_def by fastforce 
            qed
          qed
          have YsFin: "finite Ys" 
            using Nbhd_Tail_finite Ys_def hip1 hip2 by fastforce 
          have "(\<forall>x\<in>Xs. Rs x \<in> (\<lambda>x. {y. (x,y) \<in> Es}) x) \<and> inj_on Rs Xs" 
            using B inj_Rs by auto 
          thus ?thesis using YsFin YsE Es_def card_inj_on_le[of Rs Xs Ys]  by blast
        qed 
      qed 
    qed
    have premisse2: "Count_Nbhdfin_bipartite_digraph X Y E"
      by (simp add: Count_Nbhdfin_bipartite_digraph_axioms) 
    have X_countable : "countable X" by simp
    have P2: "\<exists>R. system_representatives (\<lambda>x. {y. (x,y) \<in> E}) X R" 
      using premisse2 A Hall[of X "(\<lambda>x. {y. (x,y) \<in> E})"] 
            Nbhd_Tail_finite by blast  
    then obtain R where "system_representatives (\<lambda>x. {y. (x, y) \<in> E}) X R" by auto
    hence "sdr X (\<lambda>x. {y. (x,y) \<in> E}) R" unfolding system_representatives_def sdr_def by auto 
    hence "\<exists>M. perfect_matching X (\<Union>i\<in>X. (\<lambda>x. {y. (x,y) \<in> E}) i) (Sigma X (\<lambda>x. {y. (x,y) \<in> E})) M"  
      using sdr.perfect_matching[of X "(\<lambda>x. {y. (x,y) \<in> E})" R] by auto 
    then obtain M
    where PM0: "perfect_matching X (\<Union>i\<in>X. (\<lambda>x. {y. (x,y) \<in> E}) i) 
               (Sigma X (\<lambda>x. {y. (x,y) \<in> E})) M" by auto
    have Ed2: "E = (Sigma X (\<lambda>x. {y. (x,y) \<in> E}))"
    proof
      show  "  E \<subseteq> (SIGMA x:X. {y. (x, y) \<in> E})  " 
      proof fix x
        assume "x \<in> E" 
        thus "x \<in> (SIGMA x:X. {y. (x, y) \<in> E})"
          using E_subset by blast  
      qed
      next 
      show "(SIGMA x:X. {y. (x, y) \<in> E}) \<subseteq> E"
      proof fix x
        assume  "x \<in> (SIGMA x:X. {y. (x, y) \<in> E})" 
        thus "x \<in> E" by blast
      qed
    qed
    have PM1: "perfect_matching X (\<Union>i\<in>X. (\<lambda>x. {y. (x,y) \<in> E}) i) E M"
      using PM0 Ed2 by auto
    hence PM2: "perfect_matching X Y E M" 
      using Count_Nbhdfin_bipartite_digraph_axioms unfolding  matching_def perfect_matching_def
    proof -
      assume "(bipartite_digraph X (\<Union>i\<in>X. {y. (i, y) \<in> E}) E \<and> matching_axioms E M) \<and> perfect_matching_axioms X M"
      then show "(bipartite_digraph X Y E \<and> matching_axioms E M) \<and> perfect_matching_axioms X M"
        using E_subset bipartite_digraph.intro by blast
    qed 
    thus PM : "\<exists>M. perfect_matching X Y E M" using PM2 by auto
  qed
qed

end
