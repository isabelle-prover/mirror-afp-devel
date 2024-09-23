(* De Bruijn-Erdős  k-coloring theorem 
   Fabian Fernando Serrano Suárez  UNAL Manizales
   Thaynara Arielly de Lima        Universidade Federal de Goiáis 
   Mauricio Ayala-Rincón           Universidade de Brasília
*)


(*<*)
theory k_coloring
imports PropCompactness
begin
(*>*)

section \<open>de Bruijn-Erd\H{o}s k-coloring theorem for countable infinite graphs\<close>

text\<open>This section formalizes de Bruijn-Erd\H{o}s k-coloring theorem for countable infinite graphs. The construction applies the compactness theorem for propositional logic directly. \<close>


type_synonym 'v digraph =  "('v set) \<times> (('v \<times> 'v) set)"

abbreviation vert :: "'v digraph \<Rightarrow> 'v set"  (\<open>V[_]\<close> [80] 80) where
  "V[G]  \<equiv> fst G"

abbreviation edge :: "'v digraph \<Rightarrow> ('v \<times> 'v) set" (\<open>E[_]\<close> [80] 80) where
  "E[G] \<equiv> snd G"

definition is_graph :: "'v digraph \<Rightarrow> bool" where
  "is_graph G \<equiv> \<forall> u v. (u,v) \<in> E[G] \<longrightarrow> u \<in> V[G] \<and> v \<in> V[G] \<and> u \<noteq> v"


definition is_induced_subgraph :: "'v digraph \<Rightarrow>'v digraph \<Rightarrow> bool" where
  "is_induced_subgraph H G \<equiv>
  (V[H] \<subseteq> V[G]) \<and> E[H] = E[G] \<inter> ((V[H]) \<times> (V[H]))"

lemma  (* Well-definedness of the above definition *)
  assumes "is_graph G" and "is_induced_subgraph H G"
  shows "is_graph H"  
(*<*)
proof(unfold is_graph_def)
  show "\<forall>u v. (u, v) \<in> E[H] \<longrightarrow> u \<in> V[H] \<and> v \<in> V[H] \<and> u \<noteq> v"
  proof((rule allI)+, rule impI)
    fix u v
    assume "(u, v) \<in> E[H]"
    show  "u \<in> V[H] \<and> v \<in> V[H] \<and> u \<noteq> v"
    proof- 
      have  "(u, v) \<in> E[G] \<inter> (V[H]) \<times> (V[H])" using `(u, v) \<in> E[H]` assms(2)
        by(unfold is_induced_subgraph_def,auto)  
      hence 1:  "(u, v) \<in> E[G]" and 2: "u \<in> V[H] \<and> v \<in> V[H]"  by auto     
      have "u \<noteq> v" using 1  `is_graph G`  by(unfold is_graph_def,auto)
      thus  "u \<in> V[H] \<and> v \<in> V[H] \<and> u \<noteq> v" using 2 by auto
    qed
  qed
qed
(*>*)

(*<*)

definition finite_graph :: "'v digraph \<Rightarrow> bool"  where
  "finite_graph G \<equiv> finite (V[G])"
(*>*)



definition coloring :: "('v \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> 'v digraph \<Rightarrow> bool" where
 "coloring c k G  \<equiv> 
  (\<forall>u. u\<in>V[G]\<longrightarrow> c(u)\<le>k) \<and> (\<forall>u v.(u,v)\<in>E[G] \<longrightarrow> c(u)\<noteq>c(v))"

definition colorable ::  "'v digraph \<Rightarrow> nat \<Rightarrow>  bool" where
 "colorable G k \<equiv> \<exists>c. coloring c k G"


primrec atomic_disjunctions :: "'v \<Rightarrow> nat \<Rightarrow> ('v \<times> nat)formula"  where
 "atomic_disjunctions v  0 = atom (v, 0)"    
| "atomic_disjunctions v (Suc k) =
  (atom (v, Suc k)) \<or>. (atomic_disjunctions v  k)"

definition \<F> :: "'v digraph \<Rightarrow> nat \<Rightarrow> (('v \<times> nat)formula) set"  where
   "\<F> G k \<equiv> (\<Union>v\<in>V[G]. {atomic_disjunctions v  k})"

definition \<G> :: "'v digraph \<Rightarrow> nat \<Rightarrow> ('v \<times> nat)formula set"  where
   "\<G> G k \<equiv> {\<not>.(atom (v, i) \<and>. atom(v,j))
                         | v i j. (v\<in>V[G]) \<and> (0\<le>i \<and> 0\<le>j \<and> i\<le>k \<and> j\<le>k \<and> i\<noteq>j)}"

definition \<H> :: "'v digraph \<Rightarrow> nat \<Rightarrow> ('v \<times> nat)formula set"  where
   "\<H> G k \<equiv> {\<not>.(atom (u, i) \<and>. atom(v,i))
                         |u v i . (u\<in>V[G] \<and> v\<in>V[G] \<and> (u,v)\<in>E[G]) \<and> (0\<le>i \<and> i\<le>k)} "

definition \<T> :: "'v digraph \<Rightarrow> nat \<Rightarrow> ('v \<times> nat)formula set"  where
   "\<T> G k  \<equiv> (\<F> G k) \<union> (\<G> G k) \<union> (\<H> G k)" 


primrec vertices_formula :: "('v \<times> nat)formula  \<Rightarrow> 'v set" where
  "vertices_formula FF = {}"
| "vertices_formula TT = {}"
| "vertices_formula (atom P) =  {fst P}"
| "vertices_formula (\<not>. F) = vertices_formula F"
| "vertices_formula (F \<and>. G) = vertices_formula F \<union> vertices_formula G"
| "vertices_formula (F \<or>. G) = vertices_formula F \<union> vertices_formula G"
| "vertices_formula (F \<rightarrow>.G) = vertices_formula F \<union> vertices_formula G"

definition vertices_set_formulas :: "('v \<times> nat)formula set  \<Rightarrow> 'v set" where
"vertices_set_formulas S = (\<Union>F\<in> S. vertices_formula F)"

lemma finite_vertices:
  shows "finite (vertices_formula F)"
  by(induct F, auto)

lemma vertices_disjunction:
  assumes "F = atomic_disjunctions v  k" shows "vertices_formula F = {v}" 
proof-
  have  "F = atomic_disjunctions v  k \<Longrightarrow> vertices_formula F = {v}"
  proof(induct k arbitrary: F)
    case 0
    assume  "F = atomic_disjunctions v 0"
    hence "F =  atom (v, 0 )" by auto
    thus "vertices_formula F = {v}" by auto
  next
    case(Suc k)
    have "F =(atom (v, Suc k )) \<or>. (atomic_disjunctions v  k)" 
      using Suc(2) by auto
    hence "vertices_formula F = vertices_formula (atom (v, Suc k )) \<union> vertices_formula (atomic_disjunctions v  k)" by auto
    hence "vertices_formula F = {v} \<union> vertices_formula (atomic_disjunctions v  k)"
      by auto
    hence "vertices_formula F = {v} \<union> {v}" using Suc(1) by auto 
    thus "vertices_formula F = {v}" by auto
  qed
  thus  ?thesis using assms by auto
qed


lemma all_vertices_colored:
  shows "vertices_set_formulas (\<F> G k) \<subseteq> V[G]"
proof
  fix x
  assume hip: "x \<in> vertices_set_formulas (\<F> G k)" show  "x \<in> V[G]"
  proof-
    have "x \<in> (\<Union>F\<in>(\<F> G k). vertices_formula F)" using hip
      by(unfold vertices_set_formulas_def,auto)
    hence "\<exists>F\<in>(\<F> G k). x \<in> vertices_formula F" by auto
    then obtain F where "F\<in>(\<F> G k)" and x: "x \<in> vertices_formula F" by auto
    hence "\<exists> v\<in>V[G]. F\<in>{atomic_disjunctions v  k}" by (unfold \<F>_def, auto)
    then obtain v where v: "v\<in>V[G]" and "F\<in>{atomic_disjunctions v  k}" by auto
    hence "F = atomic_disjunctions v  k" by auto
    hence "vertices_formula F = {v}"
      using vertices_disjunction[OF `F = atomic_disjunctions v  k`] by auto
    hence "x = v" using x by auto
    thus ?thesis using v by auto
  qed
qed

lemma vertices_maximumC:
  shows "vertices_set_formulas(\<G> G k) \<subseteq> V[G]"
proof
  fix x
  assume hip: "x \<in> vertices_set_formulas (\<G> G k)" show  "x \<in> V[G]"
  proof-
    have "x \<in> (\<Union>F\<in>(\<G> G k). vertices_formula F)" using hip
      by(unfold vertices_set_formulas_def,auto)
    hence "\<exists>F\<in>(\<G> G k). x \<in> vertices_formula F" by auto
    then obtain F where "F\<in>(\<G> G k)" and x: "x \<in> vertices_formula F"
      by auto
    hence "\<exists>v i j. v\<in>V[G] \<and> F =  \<not>.(atom (v, i) \<and>. atom(v,j))"
      by (unfold \<G>_def, auto)
    then obtain v i j where  "v\<in>V[G]"  and "F =  \<not>.(atom (v, i) \<and>. atom(v,j))"
      by auto
    hence v: "v\<in>V[G]"  and "F =  \<not>.(atom (v, i) \<and>. atom(v,j))" by auto
    hence v: "v\<in>V[G]"  and "vertices_formula F = {v}" by auto
    thus "x \<in> V[G]" using x by auto
  qed
qed

lemma distinct_verticesC:
  shows "vertices_set_formulas(\<H> G k)\<subseteq> V[G]"
proof
  fix x
  assume hip: "x \<in> vertices_set_formulas (\<H> G k)" show "x \<in> V[G]"
  proof-
    have "x \<in> (\<Union>F\<in>(\<H> G k). vertices_formula F)" using hip
      by(unfold vertices_set_formulas_def,auto)
    hence "\<exists>F\<in>(\<H> G k) . x \<in> vertices_formula F" by auto
    then obtain F where "F\<in>(\<H> G k)" and x: "x \<in> vertices_formula F"
      by auto
    hence "\<exists>u v i . u\<in>V[G] \<and>  v\<in>V[G] \<and>  F =  \<not>.(atom (u, i) \<and>. atom(v,i))"
      by (unfold \<H>_def, auto)
    then obtain u v i
      where "u\<in>V[G]" and "v\<in>V[G]"  and "F = \<not>.(atom (u, i) \<and>. atom(v,i))"
      by auto
    hence  "u\<in>V[G]" and  "v\<in>V[G]" and "F = \<not>.(atom (u, i) \<and>. atom(v,i))"
      by auto
    hence u: "u\<in>V[G]" and v: "v\<in>V[G]" and "vertices_formula F = {u, v}"
      by auto
    hence "x=u \<or> x=v"  using x by auto
    thus "x \<in> V[G]" using u v  by auto
  qed
qed

lemma vv:
  shows "vertices_set_formulas (A \<union> B) = (vertices_set_formulas A) \<union> (vertices_set_formulas B)"
  by(unfold  vertices_set_formulas_def, auto)  

lemma vv1:
  assumes "F\<in>(\<F> G k)"
  shows "(vertices_formula F) \<subseteq> (vertices_set_formulas (\<F> G k))" 
proof
  fix x 
  assume hip: "x \<in> vertices_formula F"
  show  "x \<in> vertices_set_formulas (\<F> G k)"
  proof-
    have "\<exists>F. F\<in>(\<F> G k) \<and> x \<in> vertices_formula F" using assms hip by auto
    thus  ?thesis by(unfold vertices_set_formulas_def, auto)
  qed
qed

lemma vv2:
  assumes  "F\<in>(\<G> G k)"
  shows "(vertices_formula F) \<subseteq> (vertices_set_formulas (\<G> G k))" 
proof
  fix x 
  assume hip: "x \<in> vertices_formula F"
  show  "x \<in> vertices_set_formulas (\<G> G k)"
  proof-
    have "\<exists>F. F\<in>(\<G> G k) \<and> x \<in> vertices_formula F" using assms hip by auto
    thus ?thesis by(unfold vertices_set_formulas_def, auto)
  qed
qed

lemma vv3:
  assumes  "F\<in>(\<H> G k)"
  shows "(vertices_formula F) \<subseteq> (vertices_set_formulas (\<H> G k))" 
proof
  fix x 
  assume hip: "x \<in> vertices_formula F"
  show  "x \<in> vertices_set_formulas (\<H> G k)"
  proof-
    have "\<exists>F. F\<in>(\<H> G k) \<and> x \<in> vertices_formula F" using assms hip by auto
    thus ?thesis by(unfold vertices_set_formulas_def, auto)
  qed
qed

(*>*)

lemma vertex_set_inclusion:
  shows "vertices_set_formulas (\<T> G k) \<subseteq> V[G]" 
proof
  fix x
  assume hip: "x \<in> vertices_set_formulas (\<T> G k)" show "x \<in> V[G]"
  proof-
    have  "x \<in> vertices_set_formulas ((\<F> G k) \<union> (\<G> G k)  \<union> (\<H> G k))"
      using hip by (unfold \<T>_def,auto)
    hence "x \<in> vertices_set_formulas ((\<F> G k) \<union> (\<G> G k)) \<union>
    vertices_set_formulas(\<H> G k)"
      using vv[of "(\<F> G k) \<union> (\<G> G k)"] by auto
    hence "x \<in> vertices_set_formulas ((\<F> G k) \<union> (\<G> G k)) \<or> 
    x \<in> vertices_set_formulas(\<H> G k)"
      by auto
    thus ?thesis
    proof(rule disjE)        
      assume hip: "x \<in> vertices_set_formulas (\<F> G k \<union> \<G> G k)"       
      hence "x \<in> (\<Union>F\<in> (\<F> G k) \<union> (\<G> G k). vertices_formula F)"
        by(unfold  vertices_set_formulas_def, auto)
      then obtain F
      where F: "F\<in>(\<F> G k) \<union> (\<G> G k)" and x: "x \<in> vertices_formula F" by auto 
      from F have  "(vertices_formula F) \<subseteq> (vertices_set_formulas (\<F> G k))
      \<or> vertices_formula F \<subseteq> (vertices_set_formulas (\<G> G k))"
        using vv1 vv2 by blast
      hence "x \<in> vertices_set_formulas (\<F> G k) \<or> x \<in> vertices_set_formulas (\<G> G k)"
        using x by auto
      thus "x \<in> V[G]" 
        using all_vertices_colored[of "G" "k"] vertices_maximumC[of "G" "k"] by auto
      next
      assume "x \<in> vertices_set_formulas (\<H> G k)" 
      hence
      "x \<in> (\<Union>F\<in>(\<H> G k). vertices_formula F)" 
        by(unfold  vertices_set_formulas_def, auto)
      then obtain F where F:  "F\<in>(\<H> G k)" and x: "x \<in> vertices_formula F"
        by auto
      from F have "(vertices_formula F) \<subseteq> (vertices_set_formulas (\<H> G k))"
        using vv3 by blast
      hence "x \<in> vertices_set_formulas (\<H> G k)" using x by auto
      thus "x \<in> V[G]" using distinct_verticesC[of "G" "k"]
        by auto
    qed
  qed
qed

lemma vsf:
  assumes "G \<subseteq> H"
  shows "vertices_set_formulas G \<subseteq> vertices_set_formulas H"
  using assms by(unfold vertices_set_formulas_def, auto)

lemma vertices_subset_formulas:
  assumes "S \<subseteq> (\<T> G k)"
  shows "vertices_set_formulas S \<subseteq> V[G]" 
proof- 
  have "vertices_set_formulas S \<subseteq> vertices_set_formulas (\<T> G k)"
  using assms vsf by auto
  thus ?thesis using vertex_set_inclusion[of "G"] by auto
qed


(*>*)


definition subgraph_aux :: "'v digraph \<Rightarrow> 'v set \<Rightarrow>'v digraph" where
  "subgraph_aux G V \<equiv>  (V, E[G] \<inter> (V \<times> V))"

lemma induced_subgraph: 
 assumes "is_graph G" and "S \<subseteq>(\<T> G k)"
 shows "is_induced_subgraph (subgraph_aux G (vertices_set_formulas S)) G"
proof-
  let ?V = "vertices_set_formulas S"
  let ?H = "(?V, E[G] \<inter> (?V \<times> ?V))"
  have 1: "E[?H] =  E[G] \<inter> (?V \<times> ?V)" and 2: "V[?H]= ?V"  by auto       
  have "(V[?H] \<subseteq> V[G])" using 2 assms(2) vertices_subset_formulas[of S G ] by auto 
  moreover
  have "E[?H] = (E[G] \<inter> ((V[?H]) \<times> (V[?H])))" using 1 2 by auto 
  ultimately
  have  "is_induced_subgraph ?H G" by(unfold is_induced_subgraph_def, auto)
  thus ?thesis
    by (simp add: subgraph_aux_def)
qed

lemma finite_subgraph:
  assumes "is_graph G" and "S \<subseteq> (\<T> G k)" and "finite S"
  shows "finite_graph (subgraph_aux G (vertices_set_formulas S))" 
proof- 
  let ?V = "vertices_set_formulas S"
  let ?H = "(?V, E[G] \<inter> (?V \<times> ?V))"
  have 1: "E[?H] =  E[G] \<inter> (?V \<times> ?V)" and 2: "V[?H]= ?V"  by auto
  have 3: "finite ?V" using `finite S` finite_vertices 
    by(unfold vertices_set_formulas_def, auto)
  hence  "finite (V[?H])" using 2 by auto
  thus ?thesis
    by (simp add: finite_graph_def subgraph_aux_def) 
qed 

(*>*)


fun graph_interpretation :: "'v digraph \<Rightarrow> ('v \<Rightarrow> nat) \<Rightarrow> (('v \<times> nat) \<Rightarrow> v_truth)"  where
"graph_interpretation G f = (\<lambda>(v,i).(if v \<in> V[G] \<and> f(v) = i  then Ttrue else Ffalse))"

lemma value1:
  assumes "v \<in> V[G]" and "f(v)\<le> k"  and  "F = atomic_disjunctions v  k" 
  shows "t_v_evaluation (graph_interpretation G f) F = Ttrue" 
proof- 
  let ?i = "f(v)"
  have "0 \<le> ?i" by auto
   {have  "v \<in> V[G] \<Longrightarrow> 0 \<le> ?i \<Longrightarrow> ?i\<le>k \<Longrightarrow> F = atomic_disjunctions v  k \<Longrightarrow>
   t_v_evaluation (graph_interpretation G f) F = Ttrue"
  proof(induct k arbitrary: F)
    case 0
    have "?i = 0" using "0" (2-3)  by auto
    hence "t_v_evaluation (graph_interpretation G f) (atom (v, 0)) =  Ttrue"
      using `v \<in> V[G]`  by auto
    thus ?case using  "0" (4)  by auto 
    next
    case(Suc k)
    from Suc(1) Suc(2) Suc(3) Suc(4) Suc(5) show ?case 
    proof(cases)
      assume "(Suc  k) = ?i" 
      hence "t_v_evaluation (graph_interpretation G f) (atom (v,Suc  k )) =  Ttrue"
      using Suc(2) Suc(3) Suc(5) by auto
      hence
      "t_v_evaluation (graph_interpretation G f) (atom (v, Suc  k) 
       \<or>.atomic_disjunctions v  k) = Ttrue"
      using v_disjunction_def by auto
      thus ?case using  Suc(5) by auto
      next
      assume 1: "(Suc  k) \<noteq> ?i" 
      hence "t_v_evaluation (graph_interpretation G f) (atom (v, Suc k)) =  Ffalse"
        using Suc(5) by auto
      moreover
      have "?i < (Suc  k)" using Suc(4) 1  by auto
      hence "?i \<le> k" by auto
      hence "t_v_evaluation (graph_interpretation G f) (atomic_disjunctions v k) = Ttrue" 
      using  Suc(1) Suc(2) Suc(3)  Suc(5)  by auto
      thus ?case using  Suc(5)  v_disjunction_def by auto
    qed
  qed
 }
  thus ?thesis using assms by auto
qed

lemma t_value_vertex:
  assumes  "t_v_evaluation (graph_interpretation G f) (atom (v, i)) = Ttrue"
  shows  "f(v)=i"
proof(rule ccontr)
  assume  "f v \<noteq> i" hence "t_v_evaluation (graph_interpretation G f) (atom (v, i)) \<noteq> Ttrue" by auto
  hence "t_v_evaluation (graph_interpretation G f) (atom (v, i)) = Ffalse" 
  using non_Ttrue[of "graph_interpretation G f" "atom (v, i)"] by auto 
  thus False using assms by simp
qed

lemma value2:
  assumes  "i\<noteq>j" and "F =\<not>.(atom (v, i) \<and>. atom (v, j))" 
  shows "t_v_evaluation (graph_interpretation G f) F = Ttrue"
proof(rule ccontr)
  assume "t_v_evaluation (graph_interpretation G f) F \<noteq> Ttrue"
  hence  "t_v_evaluation (graph_interpretation G f) (\<not>.(atom (v, i) \<and>. atom (v, j))) \<noteq> Ttrue"
    using assms(2) by auto
  hence "t_v_evaluation (graph_interpretation G f) (\<not>.(atom (v, i) \<and>. atom (v, j))) = Ffalse" using
  non_Ttrue[of "graph_interpretation G f" "\<not>.(atom (v, i) \<and>. atom (v, j))" ]
    by auto     
  hence  "t_v_evaluation (graph_interpretation G f) ((atom (v, i) \<and>. atom (v, j))) = Ttrue" 
  using  NegationValues1[of "graph_interpretation G f" "(atom (v, i) \<and>. atom (v, j))"] by auto
  hence "t_v_evaluation (graph_interpretation G f) (atom (v, i)) = Ttrue" and
  "t_v_evaluation (graph_interpretation G f) (atom (v, j)) = Ttrue"
  using ConjunctionValues[of "graph_interpretation G f" "atom (v, i)" "atom (v, j)"] by auto
  hence "f(v)=i" and "f(v)=j" using t_value_vertex by auto
  hence "i=j" by auto
  thus False using assms(1) by auto
qed

lemma value3:
  assumes "f(u)\<noteq>f(v)" and  "F =\<not>.(atom (u, i) \<and>. atom (v, i))" 
  shows "t_v_evaluation (graph_interpretation G f) F = Ttrue"
proof(rule ccontr)
  assume "t_v_evaluation (graph_interpretation G f) F \<noteq> Ttrue"
  hence(*and "finite S"*)
  "t_v_evaluation (graph_interpretation G f) (\<not>.(atom (u, i) \<and>. atom (v, i))) \<noteq> Ttrue" 
    using assms(2) by auto
  hence "t_v_evaluation (graph_interpretation G f) (\<not>.(atom (u, i) \<and>. atom (v, i))) = Ffalse"
    using
  non_Ttrue[of "graph_interpretation G f" "\<not>.(atom (u, i) \<and>. atom (v, i))"]
    by auto     
  hence  "t_v_evaluation (graph_interpretation G f) ((atom (u, i) \<and>. atom (v, i))) = Ttrue" 
    using  NegationValues1[of "graph_interpretation G f" "(atom (u, i) \<and>. atom (v, i))"]
    by auto
  hence "t_v_evaluation (graph_interpretation G f) (atom (u, i)) = Ttrue" and
  "t_v_evaluation (graph_interpretation G f) (atom (v, i)) = Ttrue"
    using ConjunctionValues[of "graph_interpretation G f" "atom (u, i)" "atom (v, i)"]
    by auto
  hence "f(u)=i" and "f(v)=i" using t_value_vertex by auto
  hence "f(u)=f(v)" by auto
  thus False using assms(1) by auto
qed

theorem coloring_satisfiable:
  assumes "is_graph G" and "S \<subseteq> (\<T> G k)" and 
  "coloring f k (subgraph_aux G (vertices_set_formulas S))" 
  shows "satisfiable S"
proof- 
  let ?V = "vertices_set_formulas S"
  let ?H = "subgraph_aux G ?V"
  have "(graph_interpretation ?H f) model S"
  proof(unfold model_def) 
    show "\<forall> F \<in> S. t_v_evaluation (graph_interpretation ?H f) F  = Ttrue"
    proof 
      fix F assume "F \<in> S"
      show  "t_v_evaluation (graph_interpretation ?H f) F  = Ttrue"
      proof- 
        have 1:  "vertices_formula F \<subseteq>?V"
        proof
          fix v
          assume "v \<in> (vertices_formula F)" thus "v \<in> ?V"
          using `F \<in> S` by(unfold vertices_set_formulas_def,auto)
        qed
        have "F \<in> (\<F> G k) \<union> (\<G> G k)  \<union> (\<H> G k)" 
        using  `F \<in> S` assms(2)  by(unfold \<T>_def,auto) 
        hence  "F \<in> (\<F> G k) \<or> F \<in> (\<G> G k) \<or> F \<in> (\<H> G k)" by auto 
        thus ?thesis
        proof(rule disjE)
          assume "F \<in> (\<F> G k)"
          hence "\<exists>v\<in>V[G]. F = atomic_disjunctions v  k"  by(unfold \<F>_def,auto)
          then obtain v
          where v: "v\<in>V[G]" and F: "F = atomic_disjunctions v k"
            by auto
          have "v\<in>?V" using F vertices_disjunction[of "F"] 1 by auto  
          hence "v\<in> V[?H]" by(unfold subgraph_aux_def, auto)
          hence "f(v)\<le> k" using coloring_def[of "f" "k" "?H"] assms(3) by auto
          thus ?thesis using F  value1[OF `v\<in>V[?H]`] by auto
          next
          assume "F \<in> (\<G> G k) \<or> F \<in> (\<H> G k)"
          thus ?thesis
          proof(rule disjE)
            assume "F \<in> (\<G> G k)"
            hence "\<exists>v.\<exists>i.\<exists>j. F = \<not>.(atom (v, i) \<and>. atom(v,j)) \<and> ( i\<noteq>j)" 
            by(unfold \<G>_def, auto)
            then obtain v i j
            where "F = \<not>.(atom (v, i) \<and>. atom(v,j))" and "(i\<noteq>j)" 
            by auto
            thus "t_v_evaluation (graph_interpretation ?H f) F = Ttrue"
            using value2[OF `i\<noteq>j` `F = \<not>.(atom (v, i) \<and>. atom(v,j))`]
            by auto
            next
            assume " F \<in> (\<H> G k)" 
            hence  "\<exists>u.\<exists>v.\<exists>i.(F = \<not>.(atom (u, i) \<and>. atom(v,i)) \<and>  (u,v)\<in>E[G])"
            by(unfold \<H>_def, auto)
            then obtain u v i 
            where F:  "F = \<not>.(atom (u, i) \<and>. atom(v,i))" and uv: "(u,v)\<in>E[G]"
            by auto 
            have "vertices_formula F = {u,v}" using F by auto
            hence "{u,v} \<subseteq> ?V" using 1 by auto   
            hence "(u,v)\<in>E[?H]" using uv  by(unfold subgraph_aux_def, auto)  
            hence  "f(u) \<noteq>f(v)" using  coloring_def[of "f" "k" "?H"] assms(3)
              by auto
            show ?thesis
              using value3[OF `f(u) \<noteq>f(v)` `F = \<not>.(atom (u, i) \<and>. atom(v,i))`]
              by auto
          qed
        qed
      qed
    qed
  qed  
  thus "satisfiable S" by(unfold satisfiable_def, auto)
qed

(*>*)


fun graph_coloring ::  "(('v \<times> nat) \<Rightarrow> v_truth) \<Rightarrow> nat  \<Rightarrow> ('v \<Rightarrow> nat)"
  where
"graph_coloring I k = (\<lambda>v.(THE i. (t_v_evaluation I (atom (v,i)) = Ttrue) \<and> 0\<le>i \<and> i\<le>k))" 

lemma unicity:
  assumes "(t_v_evaluation I (atom (v, i)) = Ttrue \<and> 0\<le>i \<and> i \<le> k)" 
  and "\<forall>j. (0\<le>j \<and> j\<le>k \<and> i\<noteq>j) \<longrightarrow> (t_v_evaluation I (\<not>.(atom (v, i) \<and>. atom(v,j))) = Ttrue)"
  shows "\<forall>j. (0\<le>j \<and> j\<le>k \<and> i\<noteq>j) \<longrightarrow>  t_v_evaluation I (atom (v, j)) = Ffalse"
proof(rule allI, rule impI)
  fix j
  assume hip: "0\<le>j \<and> j\<le>k \<and> i\<noteq>j"
  show "t_v_evaluation I (atom (v, j)) = Ffalse"
  proof(rule ccontr)
    assume "t_v_evaluation I (atom (v, j)) \<noteq> Ffalse" 
    hence "t_v_evaluation I (atom (v, j)) = Ttrue" using Bivaluation by blast
    hence 1: "t_v_evaluation I (atom (v, i) \<and>. atom(v,j))  = Ttrue"
      using assms(1) v_conjunction_def by auto
    have "t_v_evaluation I (\<not>.(atom (v, i) \<and>. atom(v,j))) = Ttrue"
      using hip assms(2)  by auto
    hence "t_v_evaluation I (atom (v, i) \<and>. atom(v,j)) = Ffalse" 
      using NegationValues2  by blast
    thus False using 1  by auto
  qed      
qed

lemma existence:
  assumes "(t_v_evaluation I (atom (v, i)) = Ttrue \<and> 0\<le>i \<and> i \<le> k)" 
  and  "\<forall>j. (0\<le>j \<and> j\<le>k \<and> i\<noteq>j) \<longrightarrow>  t_v_evaluation I (atom (v, j)) = Ffalse"
shows  "(\<forall>x. (t_v_evaluation I (atom (v, x)) = Ttrue \<and> 0\<le>x \<and> x \<le> k) \<longrightarrow> x = i)"
proof(rule allI)
  fix x 
  show "t_v_evaluation I (atom (v, x)) = Ttrue \<and> 0 \<le> x \<and> x \<le> k \<longrightarrow> x = i"
  proof(rule impI)
    assume hip: "t_v_evaluation I (atom (v, x)) = Ttrue \<and> 0\<le>x \<and> x \<le> k" show "x = i" 
    proof(rule ccontr)
      assume 1:  "x \<noteq> i" 
      have  "0\<le>x \<and> x \<le> k" using hip by auto 
      hence "t_v_evaluation I (atom (v, x)) = Ffalse" using 1 assms(2) by auto
      thus False using hip by auto
    qed
  qed
qed

lemma exist_unicity1:
  assumes  "(t_v_evaluation I (atom (v, i)) = Ttrue \<and> 0\<le>i \<and> i \<le> k)"
  and "\<forall>j. (0\<le>j \<and> j\<le>k \<and> i\<noteq>j) \<longrightarrow> (t_v_evaluation I (\<not>.(atom (v, i) \<and>. atom(v,j))) = Ttrue)"
shows "(\<forall>x. (t_v_evaluation I (atom (v, x)) = Ttrue \<and> 0\<le>x \<and> x \<le> k) \<longrightarrow> x = i)"
using assms  unicity[of "I" "v" "i" "k" ] existence[of "I" "v" "i" "k"]  by blast

lemma exist_unicity2:
  assumes "(t_v_evaluation I (atom (v, i)) = Ttrue \<and> 0\<le>i \<and> i \<le> k )" and
  "(\<And>x. (t_v_evaluation I (atom (v, x)) = Ttrue \<and> 0\<le>x \<and> x \<le> k) \<Longrightarrow> x = i)"
shows "(THE a. (t_v_evaluation I (atom (v,a)) = Ttrue \<and> 0\<le>a \<and> a \<le> k )) = i" 
  using assms by (rule the_equality)

lemma exist_unicity:
  assumes "(t_v_evaluation I (atom (v, i)) = Ttrue \<and> 0\<le>i \<and> i\<le>k )" and
  "\<forall>j. (0\<le>j \<and> j\<le>k \<and> i\<noteq>j) \<longrightarrow> (t_v_evaluation I (\<not>.(atom (v, i) \<and>. atom(v,j))) = Ttrue)"
shows "(THE a. (t_v_evaluation I (atom (v,a)) = Ttrue \<and> 0\<le>a \<and> a \<le> k )) = i"  
 using assms  exist_unicity1[of "I" "v" "i" "k" ] exist_unicity2[of "I" "v" "i" "k"] by blast

lemma unique_color:
  assumes  "v \<in> V[G]" 
  shows "\<forall>i j.(0\<le>i \<and> 0\<le>j \<and> i\<le>k \<and> j\<le>k \<and> i\<noteq>j) \<longrightarrow>  (\<not>.(atom (v, i) \<and>. atom(v,j))\<in> (\<G> G k))"
proof(rule allI )+
  fix i j
  show "0 \<le> i \<and> 0 \<le> j \<and> i \<le> k \<and> j \<le> k \<and> i \<noteq> j \<longrightarrow> \<not>.(atom (v, i) \<and>. atom (v, j)) \<in> (\<G> G k)"
  proof(rule impI)
    assume "0 \<le> i \<and> 0 \<le> j \<and> i \<le> k \<and> j \<le> k \<and> i \<noteq> j"
    thus "\<not>.(atom (v, i) \<and>. atom (v, j)) \<in> (\<G> G k)" 
      using `v \<in> V[G]` by(unfold  \<G>_def, auto)
  qed
qed

lemma different_colors:
  assumes  "u \<in> V[G]" and  "v\<in>V[G]" and "(u,v)\<in>E[G]"
  shows  "\<forall>i.(0\<le>i \<and> i\<le>k) \<longrightarrow>  (\<not>.(atom (u, i) \<and>. atom(v,i))\<in> (\<H> G k))"
proof(rule allI) 
  fix i
  show "0\<le>i \<and> i\<le>k \<longrightarrow>  (\<not>.(atom (u, i) \<and>. atom(v,i))\<in> (\<H> G k))"
  proof(rule impI)
    assume "0\<le>i \<and> i\<le>k"
    thus  "\<not>.(atom (u, i) \<and>. atom(v,i))\<in> (\<H> G k)"
      using assms  by(unfold  \<H>_def, auto)
  qed
qed

lemma atom_value:
  assumes "(t_v_evaluation I (atomic_disjunctions u  k)) = Ttrue"  
  shows "\<exists>i.(t_v_evaluation I (atom (u,i)) = Ttrue) \<and> 0\<le>i \<and> i\<le>k"
proof-
  have "(t_v_evaluation I (atomic_disjunctions u  k)) = Ttrue \<Longrightarrow>
  \<exists>i.(t_v_evaluation I (atom (u,i)) = Ttrue) \<and> 0\<le>i \<and> i\<le>k"
  proof(induct k)
    case(0)
    assume "(t_v_evaluation I (atomic_disjunctions u 0)) = Ttrue"
    thus "\<exists>i. t_v_evaluation I (atom (u, i)) = Ttrue \<and> 0\<le>i \<and>  i \<le> 0" by auto
    next
    case(Suc k)
    from Suc(1) Suc(2) show ?case
    proof-
      have "t_v_evaluation I (atom (u, (Suc k)) \<or>. (atomic_disjunctions u k)) = Ttrue" 
        using Suc(2) by auto
      hence "t_v_evaluation I (atom (u, (Suc k))) = Ttrue \<or>
      (t_v_evaluation I (atomic_disjunctions u k)) = Ttrue"
        using  DisjunctionValues[of I "(atom (u, (Suc k)))"] by auto
      thus ?case
        using Suc.hyps le_SucI by blast
    qed
  qed
  thus ?thesis using assms by auto
qed

(*>*)

lemma coloring_function:
  assumes "u \<in> V[G]" and "I model (\<T> G k)"  
  shows "\<exists>!i. (t_v_evaluation I (atom (u,i)) = Ttrue \<and> 0\<le>i \<and> i\<le>k) \<and> graph_coloring I k u = i" 
proof- 
  from  `u \<in> V[G]`  
  have "atomic_disjunctions u  k \<in> \<F> G k" by(induct, unfold  \<F>_def, auto)
  hence  "atomic_disjunctions u  k \<in> \<T> G k"  by(unfold  \<T>_def, auto)
  hence "(t_v_evaluation I (atomic_disjunctions u  k)) = Ttrue"
    using assms(2) model_def[of I "\<T> G k"] by auto
  hence "\<exists>i.(t_v_evaluation I (atom (u,i)) = Ttrue \<and> 0\<le>i \<and> i\<le>k)"
    using atom_value by auto
  then obtain i where i: "(t_v_evaluation I (atom (u,i)) = Ttrue) \<and> 0\<le>i \<and>  i\<le>k"
    by auto
  moreover 
  have "\<forall>i j.(0\<le>i \<and> 0\<le>j \<and> i\<le>k \<and> j\<le>k \<and> i\<noteq>j)\<longrightarrow>
  (\<not>.(atom (u, i) \<and>.atom(u,j))\<in> (\<G> G k))"
  using `u \<in> V[G]` unique_color[of "u"] by auto
  hence "\<forall>j.(0\<le>j  \<and> j\<le>k \<and> i\<noteq>j) \<longrightarrow>  (\<not>.(atom (u, i) \<and>. atom(u,j))\<in> \<T> G k)" 
  using i  by(unfold  \<T>_def, auto)
  hence
  "\<forall>j. (0\<le>j \<and> j\<le>k \<and> i\<noteq>j) \<longrightarrow> (t_v_evaluation I (\<not>.(atom (u, i) \<and>. atom(u,j)))  = Ttrue)" 
  using assms(2)  model_def[of I "\<T> G k"] by blast
  hence "(THE a. (t_v_evaluation I (atom (u,a)) = Ttrue \<and> 0\<le>a \<and> a \<le> k ))= i"
    using i exist_unicity[of "I" "u"] by blast
  hence "graph_coloring I k u = i" by auto
  hence
  "(t_v_evaluation I (atom (u,i)) = Ttrue \<and> 0\<le>i \<and>  i\<le>k) \<and>
   graph_coloring I k u = i" 
    using i by auto
  thus ?thesis  by auto
qed

lemma \<H>1:
  assumes "(t_v_evaluation I (atom (u, a)) = Ttrue \<and> 0\<le>a \<and> a\<le>k )" and  "(t_v_evaluation I (atom (v, b)) = Ttrue \<and> 0\<le>b \<and> b\<le>k)"
  and "\<forall>i.(0\<le>i \<and> i\<le>k) \<longrightarrow> (t_v_evaluation I (\<not>.(atom (u, i) \<and>. atom(v,i))) = Ttrue)"
  shows "a\<noteq>b"  
proof(rule ccontr)
  assume  "\<not> a \<noteq> b" 
  hence "a=b" by auto
  hence "t_v_evaluation I (atom (u, a)) = Ttrue" and  "t_v_evaluation I (atom (v, a)) = Ttrue" using assms by auto
  hence "t_v_evaluation I (atom (u, a) \<and>. atom(v,a)) = Ttrue" using v_conjunction_def by auto
  hence "t_v_evaluation I (\<not>.(atom (u, a) \<and>. atom(v,a))) = Ffalse" using v_negation_def by auto
  moreover
  have "0\<le>a \<and> a\<le>k" using assms(1) by auto
  hence "t_v_evaluation I (\<not>.(atom (u, a) \<and>. atom(v,a))) = Ttrue" using assms(3) by auto
  finally show False by auto
qed

(* Include also in the document  *)
lemma distinct_colors:
  assumes "is_graph G" and "(u,v) \<in> E[G]" and I: "I model (\<T> G k)"
  shows "graph_coloring I k u \<noteq> graph_coloring I k v"
proof-
  have "u \<noteq> v" and "u \<in> V[G]" and "v \<in> V[G]"  using  `(u,v) \<in> E[G]` `is_graph G`
    by(unfold is_graph_def, auto)
  have "\<exists>!i. (t_v_evaluation I (atom (u,i)) = Ttrue \<and> 0\<le>i \<and>  i\<le>k) \<and>  graph_coloring I k u = i"
  using coloring_function[OF `u \<in> V[G]`  I]  by blast   
  then obtain i where i1: "(t_v_evaluation I (atom (u,i)) = Ttrue \<and> 0\<le>i \<and> i\<le>k)" and i2: "graph_coloring I k u = i"
    by auto
  have  "\<exists>!j. (t_v_evaluation I (atom (v,j)) = Ttrue \<and> 0\<le>j \<and>  j\<le>k) \<and> graph_coloring I k v = j"
  using coloring_function[OF `v \<in> V[G]`  I]  by blast   
  then obtain j where j1: "(t_v_evaluation I (atom (v,j)) = Ttrue \<and> 0\<le>j \<and> j\<le>k)" and
   j2: "graph_coloring I k v = j" by auto
  have  "\<forall>i.(0\<le>i \<and> i\<le>k) \<longrightarrow>  (\<not>.(atom (u, i) \<and>. atom(v,i))\<in> \<H> G k)"
  using `u \<in> V[G]` `v \<in> V[G]`  `(u,v) \<in> E[G]`  by(unfold  \<H>_def, auto)
  hence "\<forall>i. (0\<le>i \<and> i\<le>k) \<longrightarrow> \<not>.(atom (u, i) \<and>. atom(v,i)) \<in> \<T> G k"
  by(unfold  \<T>_def, auto)
  hence  "\<forall>i. (0\<le>i \<and> i\<le>k) \<longrightarrow> (t_v_evaluation I  (\<not>.(atom (u, i) \<and>. atom(v,i))) = Ttrue)" 
  using assms(2) I model_def[of I "\<T> G k"] by blast
  hence "i \<noteq> j" using i1 j1 \<H>1[of "I" "u" "i"  "k" "v" "j"] by blast
  thus ?thesis using i2 j2 by auto 
qed  

theorem satisfiable_coloring:
  assumes "is_graph G" and  "satisfiable (\<T> G k)" 
  shows  "colorable G k"  
proof(unfold colorable_def)
  show "\<exists>f. coloring f k G"
  proof-
    from assms(2) have "\<exists>I. I model (\<T> G k)"  by(unfold satisfiable_def)
    then obtain I where I: "I model (\<T> G k)" by auto 
    hence  "coloring (graph_coloring I k) k G"
    proof(unfold coloring_def)
      show
      "(\<forall>u. u \<in> V[G] \<longrightarrow> (graph_coloring I  k u) \<le> k) \<and> (\<forall>u v. (u, v) \<in> E[G]
      \<longrightarrow> graph_coloring I k u \<noteq> graph_coloring I k v)"
      proof(rule conjI)
        show "\<forall>u. u \<in> V[G] \<longrightarrow> graph_coloring I k u \<le> k"
        proof(rule allI, rule impI)
          fix u
          assume  "u \<in> V[G]"            
          show "graph_coloring I k u \<le> k"
            using coloring_function[OF `u \<in> V[G]` I] by blast
        qed
        next
          show
          "\<forall>u v. (u, v) \<in> E[G] \<longrightarrow>
          graph_coloring I k u \<noteq> graph_coloring I k v"    
          proof(rule allI,rule allI,rule impI)
          fix u v     
          assume "(u,v) \<in> E[G]" 
          thus "graph_coloring I k u \<noteq> graph_coloring I k v"
          using  distinct_colors[OF `is_graph G` `(u,v) \<in> E[G]`  I]  by blast
        qed
      qed
    qed
    thus "\<exists>f. coloring f k G" by auto
  qed
qed


theorem deBruijn_Erdos_coloring:
  assumes "is_graph (G::('vertices:: countable) set \<times> ('vertices \<times> 'vertices) set)"
  and "\<forall>H. (is_induced_subgraph H G \<and> finite_graph H \<longrightarrow> colorable H k)"
  shows "colorable G k"
proof- 
  have "\<forall> S. S \<subseteq> (\<T> G k) \<and> (finite S) \<longrightarrow> satisfiable S"
  proof(rule allI, rule impI) 
    fix S assume "S \<subseteq> (\<T> G k) \<and> (finite S)"
    hence hip1:  "S \<subseteq> (\<T> G k)" and  hip2: "finite S" by auto
    show "satisfiable S"
    proof -
      let ?V = "vertices_set_formulas S"
      let ?H = "(?V, E[G] \<inter> (?V \<times> ?V))"     
      have "is_induced_subgraph ?H G"
        using assms(1) hip1 induced_subgraph[of G S k]
        by(unfold subgraph_aux_def, auto)         
      moreover      
      have "finite_graph ?H"
        using assms(1) hip1 hip2 finite_subgraph[of G S k]
        by(unfold subgraph_aux_def, auto)
      ultimately
      have "colorable ?H k" using assms by auto
      hence  "\<exists>f. coloring f k ?H" by(unfold colorable_def, auto)
      then obtain f where "coloring f k ?H" by auto
      thus "satisfiable S" using coloring_satisfiable[OF assms(1) hip1]
        by(unfold subgraph_aux_def, auto)
    qed
  qed
  hence "satisfiable (\<T> G k)" using 
   Compactness_Theorem by auto
  thus ?thesis using assms(1) satisfiable_coloring by blast
qed

end
