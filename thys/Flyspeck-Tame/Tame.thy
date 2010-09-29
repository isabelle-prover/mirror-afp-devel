(*  Author:     Gertrud Bauer, Tobias Nipkow
*)

header{* Tameness *}

theory Tame
imports Graph ListSum
begin


subsection {* Constants \label{sec:TameConstants}*}

definition squanderTarget :: "nat" where
 "squanderTarget \<equiv> 14800" 

definition excessTCount :: "nat \<Rightarrow> nat" (*<*) ("\<a>")(*>*)where

 "\<a> t \<equiv> if t < 3 then squanderTarget
     else if t = 3 then 1400 
     else if t = 4 then 1500
     else 0"

definition squanderVertex :: "nat \<Rightarrow> nat \<Rightarrow> nat" (*<*)("\<b>")(*>*)where

 "\<b> p q \<equiv> if p = 0 \<and> q = 3 then 7135 
     else if p = 0 \<and> q = 4 then 10649 
     else if p = 1 \<and> q = 2 then  6950 
     else if p = 1 \<and> q = 3 then  7135 
     else if p = 2 \<and> q = 1 then  8500 
     else if p = 2 \<and> q = 2 then  4756 
     else if p = 2 \<and> q = 3 then 12981 
     else if p = 3 \<and> q = 1 then  3642 
     else if p = 3 \<and> q = 2 then  8334 
     else if p = 4 \<and> q = 0 then  4139 
     else if p = 4 \<and> q = 1 then  3781 
     else if p = 5 \<and> q = 0 then   550 
     else if p = 5 \<and> q = 1 then 11220 
     else if p = 6 \<and> q = 0 then  6339 
     else squanderTarget"

definition scoreFace :: "nat \<Rightarrow> int" (*<*)("\<c>")(*>*)where

 "\<c> n \<equiv> if n = 3 then 1000
     else if n = 4 then 0
     else if n = 5 then -1030
     else if n = 6 then -2060
     else if n = 7 then -3030
     else if n = 8 then -3030
     else -3030" 

definition squanderFace :: "nat \<Rightarrow> nat" (*<*)("\<d>")(*>*)where

 "\<d> n \<equiv> if n = 3 then 0
     else if n = 4 then 2378
     else if n = 5 then 4896
     else if n = 6 then 7414
     else if n = 7 then 9932
     else if n = 8 then 10916
     else squanderTarget" 

text_raw{* 
\index{@{text "\<a>"}}
\index{@{text "\<b>"}}
\index{@{text "\<c>"}}
\index{@{text "\<d>"}}
*}

subsection{* Separated sets of vertices \label{sec:TameSeparated}*}


text {* A set of vertices $V$ is {\em separated},
\index{separated}
\index{@{text "separated"}}
iff the following conditions hold:
 *}

text {*  1. For each vertex in $V$ there is an exceptional face 
containing it: *}

definition separated\<^isub>1 :: "graph \<Rightarrow> vertex set \<Rightarrow> bool" where
 "separated\<^isub>1 g V \<equiv> \<forall>v \<in> V. except g v \<noteq> 0" 

text {*  2. No two vertices in V are adjacent: *}

definition separated\<^isub>2 :: "graph \<Rightarrow> vertex set \<Rightarrow> bool" where
 "separated\<^isub>2 g V \<equiv> \<forall>v \<in> V. \<forall>f \<in> set (facesAt g v). f\<bullet>v \<notin> V"

text {*  3. No two vertices lie on a common quadrilateral: *}

definition separated\<^isub>3 :: "graph \<Rightarrow> vertex set \<Rightarrow> bool" where
 "separated\<^isub>3 g V \<equiv> 
     \<forall>v \<in> V. \<forall>f \<in> set (facesAt g v). |vertices f|\<le>4 \<longrightarrow> \<V> f \<inter> V = {v}"

text {*  A set of vertices  is  called {\em preseparated},
\index{preseparated} \index{@{text "preSeparated"}}
iff no two vertices are adjacent or lie on a common quadrilateral: *}

definition preSeparated :: "graph \<Rightarrow> vertex set \<Rightarrow> bool" where
 "preSeparated g V \<equiv> separated\<^isub>2 g V \<and> separated\<^isub>3 g V"

text {*  4. Every vertex in V has degree 5: *}

definition separated\<^isub>4 :: "graph \<Rightarrow> vertex set \<Rightarrow> bool" where
 "separated\<^isub>4 g V \<equiv> \<forall>v \<in> V. degree g v = 5"

definition separated :: "graph \<Rightarrow> vertex set \<Rightarrow> bool" where
 "separated g V \<equiv> 
     separated\<^isub>1 g V \<and> separated\<^isub>2 g V \<and> separated\<^isub>3 g V \<and> separated\<^isub>4 g V"

subsection{* Admissible weight assignments\label{sec:TameAdmissible} *}

text {*  
A weight assignment @{text "w :: face \<Rightarrow> nat"} 
assigns a natural number to every face.

\index{@{text "admissible"}}
\index{admissible weight assignment}

We formalize the admissibility requirements as follows:
 *}

text {*  1. $\isasymd(|f|) \leq w (f)$: *}

definition admissible\<^isub>1 :: "(face \<Rightarrow> nat) \<Rightarrow> graph \<Rightarrow> bool" where  
 "admissible\<^isub>1 w g \<equiv> \<forall>f \<in> \<F> g. \<d> |vertices f| \<le> w f"

text {*  2. If $v$ has type $(p, q)$, then 
   $\isasymb(p, q) \leq \sum\limits_{v\in f} w(f)$: *}

definition admissible\<^isub>2 :: "(face \<Rightarrow> nat) \<Rightarrow> graph \<Rightarrow> bool" where  
 "admissible\<^isub>2 w g \<equiv> 
  \<forall>v \<in> \<V> g. except g v = 0 \<longrightarrow> \<b> (tri g v) (quad g v) \<le> \<Sum>\<^bsub>f\<in>facesAt g v\<^esub> w f"

text {* 4. Let $V$ be any separated set  of vertices. \\ 
    Then  $\sum\limits_{v\in V} \isasyma(tri(v)) 
    \leq \sum\limits_{V \cap f \neq \emptyset} (w(f) - d (|f|))$: *}
(* fixme set (vertices f) \<inter> set V \<noteq> {} *)

definition admissible\<^isub>3 :: "(face \<Rightarrow> nat) \<Rightarrow> graph \<Rightarrow> bool" where  
 "admissible\<^isub>3 w g \<equiv> 
     \<forall>V. separated g (set V) \<and> set V \<subseteq> \<V> g \<longrightarrow>
        (\<Sum>\<^bsub>v\<in>V\<^esub> \<a> (tri g v))
     + (\<Sum>\<^bsub>f\<in>[f\<leftarrow>faces g. \<exists>v \<in> set V. f \<in> set (facesAt g v)]\<^esub> \<d> |vertices f| )
     \<le> \<Sum>\<^bsub>f\<in>[f\<leftarrow>faces g. \<exists>v \<in> set V. f \<in> set (facesAt g v)]\<^esub> w f"


text {* Finally we define admissibility of weights functions. *}


definition admissible :: "(face \<Rightarrow> nat) \<Rightarrow> graph \<Rightarrow> bool" where  
 "admissible w g \<equiv> admissible\<^isub>1 w g \<and> admissible\<^isub>2 w g \<and> admissible\<^isub>3 w g"
 
subsection{* Tameness \label{sec:TameDef} *}

text {* 1. The length of each face is (at least 3 and) at most 8: *}

definition tame\<^isub>1 :: "graph \<Rightarrow> bool" where
 "tame\<^isub>1 g \<equiv> \<forall>f \<in> \<F> g. 3 \<le> |vertices f| \<and> |vertices f| \<le> 8"

text {* 2.\  Every 3-cycle is a face or the opposite of a
 face: *}

text {* A face given by a vertex list @{text "vs"} is contained 
in a graph $g$, if it is isomorphic to one of the faces in $g$.
The notation @{text "f \<in>\<^isub>\<cong> F"} means  @{text "\<exists>f'\<in> F. f \<cong> f'"}, 
where @{text "\<cong>"} is the equivalence relation on faces
 (see Chapter~\ref{sec:Isomorphism}).
*}

text {* The notions @{text is_path} and @{text is_cycle} are defined
locally (rather than in the theory of graphs) because no lemmas need
to be proved about them because the generation of tame graphs uses
these same executable functions as the definition of tameness. Hence
there is nothing to prove. *}

primrec is_path :: "graph \<Rightarrow> vertex list \<Rightarrow> bool" where
"is_path g [] = True" |
"is_path g (u#vs) = (case vs of [] \<Rightarrow> True
                      | v#ws \<Rightarrow> v \<in> set(neighbors g u) \<and> is_path g vs)"

definition is_cycle :: "graph \<Rightarrow> vertex list \<Rightarrow> bool" where
"is_cycle g vs \<equiv> hd vs \<in> set(neighbors g (last vs)) \<and> is_path g vs"

definition tame\<^isub>2 :: "graph \<Rightarrow> bool" where
 "tame\<^isub>2 g \<equiv> 
     \<forall>a b c. is_cycle g [a,b,c] \<and> distinct [a,b,c] \<longrightarrow>
     (\<exists>f \<in> \<F> g. vertices f \<cong> [a,b,c] \<or> vertices f \<cong> [c,b,a])"

text {* 
3.\ Every 4-cycle surrounds one of the following configurations:\\  

%\begin{center}
%\includegraphics[scale=0.85]{graphics/quadcases}
%\end{center}
*}

definition tameConf\<^isub>1 :: "vertex \<Rightarrow> vertex \<Rightarrow> vertex \<Rightarrow> vertex \<Rightarrow> vertex list list" where
 "tameConf\<^isub>1 a b c d \<equiv> [[a,b,c,d]]"

definition tameConf\<^isub>2 :: "vertex \<Rightarrow> vertex \<Rightarrow> vertex \<Rightarrow> vertex \<Rightarrow> vertex list list" where
 "tameConf\<^isub>2 a b c d \<equiv> [[a,b,c], [a,c,d]]"

definition tameConf\<^isub>3 :: "vertex \<Rightarrow> vertex \<Rightarrow> vertex \<Rightarrow> vertex \<Rightarrow> vertex \<Rightarrow> vertex list list" where
 "tameConf\<^isub>3 a b c d e \<equiv>  [[a,b,e], [b,c,e], [a,e,c,d]]"

definition tameConf\<^isub>4 :: "vertex \<Rightarrow> vertex \<Rightarrow> vertex \<Rightarrow> vertex \<Rightarrow> vertex \<Rightarrow> vertex list list" where
 "tameConf\<^isub>4 a b c d e \<equiv> [[a,b,e], [b,c,e], [c,d,e], [d,a,e]]"


text {*  
Given a fixed 4-cycle and using the convention of drawing faces clockwise,
a tame configuration can occur in the `interior' 
or on the outside of the 4-cycle.
For configuration @{text "tameConf\<^isub>2"} there are two possible rotations of 
the triangles, for configuration 
@{text "tameConf\<^isub>3"} there are 4.
The notation @{text "F\<^isub>1 \<subseteq>\<^isub>\<cong> F\<^isub>2 "} means  @{text "\<forall>f \<in> F\<^isub>1. f \<in>\<^isub>\<cong> F\<^isub>2"}.

Note that our definition only ensures the existence of certain
faces in the graph, not the fact that no other  faces of the graph
may lie in the interior or on the outside. Hence it is slightly 
weaker than the definition in Hales' paper.
 
*}

definition tame_quad :: "graph \<Rightarrow> vertex \<Rightarrow> vertex \<Rightarrow> vertex \<Rightarrow> vertex \<Rightarrow> bool" where
 "tame_quad g a b c d \<equiv> 
         set(tameConf\<^isub>1 a b c d) \<subseteq>\<^isub>\<cong> vertices ` \<F> g
       \<or> set(tameConf\<^isub>2 a b c d) \<subseteq>\<^isub>\<cong> vertices ` \<F> g
       \<or> set(tameConf\<^isub>2 b c d a) \<subseteq>\<^isub>\<cong> vertices ` \<F> g
       \<or> (\<exists>e \<in> \<V> g - {a,b,c,d}.
          set(tameConf\<^isub>3 a b c d e) \<subseteq>\<^isub>\<cong> vertices ` \<F> g
        \<or> set(tameConf\<^isub>3 b c d a e) \<subseteq>\<^isub>\<cong> vertices ` \<F> g
        \<or> set(tameConf\<^isub>3 c d a b e) \<subseteq>\<^isub>\<cong> vertices ` \<F> g
        \<or> set(tameConf\<^isub>3 d a b c e) \<subseteq>\<^isub>\<cong> vertices ` \<F> g
        \<or> set(tameConf\<^isub>4 a b c d e) \<subseteq>\<^isub>\<cong> vertices ` \<F> g)"

definition tame\<^isub>3 :: "graph \<Rightarrow> bool" where
 "tame\<^isub>3 g \<equiv> \<forall>a b c d. is_cycle g [a,b,c,d] \<and> distinct[a,b,c,d] \<longrightarrow> 
    tame_quad g a b c d \<or> tame_quad g d c b a"  

text {* 4. The degree of every  vertex is at least 2 and at most 6: *}

definition tame\<^isub>4\<^isub>5 :: "graph \<Rightarrow> bool" where
 "tame\<^isub>4\<^isub>5 g \<equiv> \<forall>v \<in> \<V> g. degree g v \<le> (if except g v = 0 then 6 else 5)"
(*
text {*   5. If a vertex is contained in an exceptional face, 
 then the degree of the vertex is at most 5: *}

definition tame\<^isub>5 :: "graph \<Rightarrow> bool" where 
 "tame\<^isub>5 g \<equiv>  \<forall>f \<in> \<F> g. \<forall>v \<in> \<V> f. 5 \<le> |vertices f| \<longrightarrow> degree g v \<le> 5"
*)
text {*  6. The following inequality holds: *}

definition tame\<^isub>6 :: "graph \<Rightarrow> bool" where
 "tame\<^isub>6 g \<equiv> 8000 \<le> \<Sum>\<^bsub>f \<in> faces g\<^esub> \<c> |vertices f|"

text {* This property implies that there are at least 8 triangles in a
tame graph.  *}

text {* 7. There exists an admissible weight assignment of total
weight less than the target: *}

definition tame\<^isub>7 :: "graph \<Rightarrow> bool" where
 "tame\<^isub>7 g \<equiv> \<exists>w. admissible w g \<and> \<Sum>\<^bsub>f \<in> faces g\<^esub> w f < squanderTarget" 


text {* 8. We formalize the additional restriction (compared with the
original definition) that tame graphs do not contain two adjacent
vertices of type $(4,0)$: *}

definition type40 :: "graph \<Rightarrow> vertex \<Rightarrow> bool" where  
 "type40 g v \<equiv> tri g v = 4 \<and> quad g v = 0 \<and> except g v = 0" 

definition tame\<^isub>8 :: "graph \<Rightarrow> bool" where
 "tame\<^isub>8 g \<equiv> \<not>(\<exists>v\<in> \<V> g. type40 g v \<and> (\<exists>w\<in> set(neighbors g v). type40 g w))"


text {* Finally we define the notion of tameness. *}

definition tame :: "graph \<Rightarrow> bool" where
 "tame g \<equiv>
     tame\<^isub>1 g \<and> tame\<^isub>2 g \<and> tame\<^isub>3 g \<and> tame\<^isub>4\<^isub>5 g (*\<and> tame\<^isub>5 g*) \<and> tame\<^isub>6 g \<and> tame\<^isub>7 g 
   \<and> tame\<^isub>8 g"
(*<*)
end
(*>*)
