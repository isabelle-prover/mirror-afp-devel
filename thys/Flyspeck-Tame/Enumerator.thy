(*  ID:         $Id: Enumerator.thy,v 1.2 2007-06-06 18:15:27 nipkow Exp $
    Author:     Gertrud Bauer
*)

header {* Enumerating Patches *}

theory Enumerator
imports Graph Vector
begin

text {*
Generates an Enumeration of lists. 
(See Kepler98, PartIII, section 8, p.11).

Used to construct all possible extensions of an unfinished outer
 face $F$ with $outer$ vertices
by a new finished inner face with $inner$ vertices, such a fixed 
edge $e$ of the outer face is also contained in the inner face. 

Label the vertices  of $F$ consecutively 
$0, \ldots, outer-1$, with $0$ and $outer-1$ the endpoints of $e$.

Generate all lists $$[a0, \ldots,  a_{inner_1}]$$ of length
 $inner$, 
%such that $0 = a_0 \le a_1 \ldots a_{outer - 2} < a_{outer -1}$.
such that $0 = a_0 \le a_1 \ldots a_{inner - 2} < a_{inner -1}$.
Every list represents an inner face, with vertices
 $v_0, \ldots, v_{inner-1}$. 

Construct the vertices $v_0, \ldots, v_{inner - 1}$ inductively:
If $i = 1$ or $a_i \not = a_{i -1}$, we set $v_i$ to the vertex 
with index
$a_i$ of F. But if  $a_i = a_{i -1}$, we add a new vertex $v_i$ 
to the planar map.
The new face is to be drawn along the edge $e$ over the face $F$.

As we run over all $inner$ and all lists
 $[a0, \ldots,  a_{inner_1}]$, 
we run over all osibilites fro the finishe face along the edge
 $e$ inside $F$.
*}

text{* \paragraph{Executable enumeration of patches} *}

constdefs enumBase :: "nat \<Rightarrow> nat list list"
 "enumBase nmax \<equiv> [[i]. i \<leftarrow> [0 .. nmax]]"

constdefs enumAppend :: "nat \<Rightarrow> nat list list \<Rightarrow> nat list list"
 "enumAppend nmax iss \<equiv> \<Squnion>\<^bsub>is\<in>iss\<^esub> [is @ [n]. n \<leftarrow> [last is .. nmax]]"

constdefs enumerator :: "nat \<Rightarrow> nat \<Rightarrow> nat list list" (* precondition inner >= 3 *)
 "enumerator inner outer \<equiv>
     let nmax = outer - 2; k = inner - 3 in 
     [[0] @ is @ [outer - 1]. is \<leftarrow> ((enumAppend nmax)^k) (enumBase nmax)]"    

 enumTab :: "nat list list vector vector"
"enumTab \<equiv> \<lbrakk> enumerator inner outer. inner < 9, outer < 9 \<rbrakk>"

(* never used with > 8 but easier this way *)
 enum :: "nat \<Rightarrow> nat \<Rightarrow> nat list list"
"enum inner outer \<equiv> if inner < 9 & outer < 9 then enumTab\<lbrakk>inner,outer\<rbrakk>
                    else enumerator inner outer"

text{* \paragraph{Conversion to list of vertices} *}

consts hideDupsRec :: "'a \<Rightarrow> 'a list \<Rightarrow> 'a option list"
primrec "hideDupsRec a [] = []"
 "hideDupsRec a (b#bs) = 
     (if a = b then None # hideDupsRec b bs 
     else Some b # hideDupsRec b bs)"    

consts hideDups :: "'a list \<Rightarrow> 'a option list"
primrec "hideDups [] = []"
 "hideDups (b#bs) = Some b # hideDupsRec b bs"

constdefs indexToVertexList :: "face \<Rightarrow> vertex \<Rightarrow> nat list \<Rightarrow> vertex option list" (* precondition hd is = 0 *)
 "indexToVertexList f v is \<equiv> hideDups [f\<^bsup>k\<^esup>\<bullet>v. k \<leftarrow> is]" 


end
