(*  ID:         $Id: Generator.thy,v 1.7 2008-04-24 11:42:59 fhaftmann Exp $
    Author:     Gertrud Bauer, Tobias Nipkow
*)

header {* Enumeration of Tame Plane Graphs *}

theory Generator
imports Plane1 Tame
begin


text{* \paragraph{Lower bounds for total weight} *}


constdefs
 faceSquanderLowerBound :: "graph \<Rightarrow> nat"
"faceSquanderLowerBound g \<equiv> \<Sum>\<^bsub>f \<in> finals g\<^esub> \<d> |vertices f|"

constdefs
 d3_const :: nat
"d3_const == \<d> 3"
 d4_const :: nat
"d4_const == \<d> 4"

 excessAtType :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat"
"excessAtType t q e \<equiv>
    if e = 0 then if 6 < t + q then squanderTarget
                  else \<b> t q - t * d3_const - q * d4_const
    else if t + q + e \<noteq> 5 then 0 else \<a> t"

declare d3_const_def[simp] d4_const_def[simp]


constdefs ExcessAt :: "graph \<Rightarrow> vertex \<Rightarrow> nat"
 "ExcessAt g v \<equiv> if \<not> finalVertex g v then 0
     else excessAtType (tri g v) (quad g v) (except g v)"


constdefs ExcessTable :: "graph \<Rightarrow> vertex list \<Rightarrow> (vertex \<times> nat) list"
 "ExcessTable g vs \<equiv>
     [(v, ExcessAt g v). v \<leftarrow> [v \<leftarrow> vs. 0 < ExcessAt g v ]]"
text{* Implementation: *}
lemma [code]:
  "ExcessTable g =
   filtermap (\<lambda>v. let e = ExcessAt g v in if 0 < e then Some (v, e) else None)"
 by (rule ext) (simp add: ExcessTable_def filtermap_conv)

(* FIXME delete stupid removeKeyList *)
constdefs deleteAround ::
     "graph \<Rightarrow> vertex \<Rightarrow> (vertex \<times> nat) list \<Rightarrow> (vertex \<times> nat) list"
 "deleteAround g v ps \<equiv>
      let fs = facesAt g v;
      ws = \<Squnion>\<^bsub>f\<in>fs\<^esub> if |vertices f| = 4 then [f\<bullet>v, f\<^bsup>2\<^esup>\<bullet>v] else [f\<bullet>v] in
      removeKeyList ws ps"  (*<*)
text{* Implementation: *}
lemma [code]: "deleteAround g v ps =
      (let vs = (\<lambda>f. let n = f\<bullet>v
                     in if |vertices f| = 4 then [n, f\<bullet>n] else [n])
       in removeKeyList (concat(map vs (facesAt g v))) ps)"
   by (simp only: Let_def deleteAround_def nextV2)
lemma length_deleteAround: "length (deleteAround g v ps) \<le> length ps"
  by (auto simp only: deleteAround_def length_removeKeyList Let_def)

function ExcessNotAtRec :: "(nat, nat) table \<Rightarrow> graph \<Rightarrow> nat" where
 "ExcessNotAtRec [] = (%g. 0)"
 | "ExcessNotAtRec ((x, y)#ps) = (%g.  max (ExcessNotAtRec ps g)
         (y + ExcessNotAtRec (deleteAround g x ps) g))"
by pat_completeness auto
termination by (relation "measure size") 
  (auto simp add: length_deleteAround less_Suc_eq_le)

constdefs ExcessNotAt :: "graph \<Rightarrow> vertex option \<Rightarrow> nat"
 "ExcessNotAt g v_opt \<equiv>
     let ps = ExcessTable g (vertices g) in
     case v_opt of None \<Rightarrow>  ExcessNotAtRec ps g
      | Some v \<Rightarrow> ExcessNotAtRec (deleteAround g v ps) g" (*<*)

constdefs squanderLowerBound :: "graph \<Rightarrow> nat"
 "squanderLowerBound g \<equiv>  faceSquanderLowerBound g + ExcessNotAt g None"



text{* \paragraph{Tame graph enumeration} *}


constdefs
 makeTrianglesFinal :: "graph \<Rightarrow> graph"
"makeTrianglesFinal g \<equiv>
 foldl (%g f. makeFaceFinal f g) g [f \<leftarrow> faces g. \<not> final f \<and> triangle f]"


constdefs
 is_tame\<^isub>7 :: "graph \<Rightarrow> bool"
"is_tame\<^isub>7 g \<equiv> squanderLowerBound g < squanderTarget"

 notame :: "graph \<Rightarrow> bool"
"notame g \<equiv> \<not> (tame\<^isub>4\<^isub>5 g \<and> is_tame\<^isub>7 g)"

 generatePolygonTame :: "nat \<Rightarrow> vertex \<Rightarrow> face \<Rightarrow> graph \<Rightarrow> graph list"
"generatePolygonTame n v f g \<equiv>
     let
     enumeration = enum n |vertices f|;
     enumeration = [is \<leftarrow> enumeration. \<not> containsDuplicateEdge g f v is];
     vertexLists = [indexToVertexList f v is. is \<leftarrow> enumeration]
     in
     [g' \<leftarrow> [subdivFace g f vs. vs \<leftarrow> vertexLists] . \<not> notame g']"

constdefs
 polysizes :: "nat \<Rightarrow> graph \<Rightarrow> nat list"
"polysizes p g \<equiv>
    let lb = squanderLowerBound g in
    [n \<leftarrow> [3 ..< Suc(maxGon p)]. lb + \<d> n < squanderTarget]"

constdefs
 next_tame0 :: "nat \<Rightarrow> graph \<Rightarrow> graph list" ("next'_tame0\<^bsub>_\<^esub>")
"next_tame0\<^bsub>p\<^esub> g \<equiv>
     let fs = nonFinals g in
     if fs = [] then []
     else let f = minimalFace fs; v = minimalVertex g f
          in \<Squnion>\<^bsub>i \<in> polysizes p g\<^esub> generatePolygonTame i v f g"

 next_tame1 :: "nat \<Rightarrow> graph \<Rightarrow> graph list" ("next'_tame1\<^bsub>_\<^esub>")
"next_tame1\<^bsub>p\<^esub> \<equiv> map makeTrianglesFinal o next_tame0\<^bsub>p\<^esub>"

text{*\noindent Extensionally, @{const next_tame0} is just
@{term"filter P o next_plane p"} for some suitable @{text P}. But
efficiency suffers considerably if we first create many graphs and
then filter out the ones not in @{const polysizes}. *}

end
