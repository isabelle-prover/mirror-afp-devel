(*
   Author: Mike Stannett
   Date: August 2020
   Updated: Feb 2023
*)

section \<open> Cones \<close>

text \<open>This theory defines (light)cones, regular cones, and their properties. \<close>

theory Cones
  imports WorldLine TangentLines
begin


class Cones = WorldLine + TangentLines
begin

abbreviation tl :: "'a Point set \<Rightarrow> Body \<Rightarrow> Body \<Rightarrow> 'a Point \<Rightarrow> bool"
  where "tl l m b x  \<equiv> tangentLine l (wline m b) x"


text \<open>The cone of a body at a point comprises the set of points that lie on
tangent lines of photons emitted by the body at that point.\<close>

abbreviation cone :: "Body \<Rightarrow> 'a Point \<Rightarrow> 'a Point \<Rightarrow> bool"
  where "cone m x p 
             \<equiv> \<exists> l . (onLine p l) \<and>  (onLine x l) \<and> (\<exists> ph . Ph ph \<and> tl l m ph x)" 


abbreviation regularCone :: "'a Point \<Rightarrow> 'a Point \<Rightarrow> bool"
  where "regularCone x p \<equiv> \<exists> l . (onLine p l) \<and> (onLine x l) 
                                \<and> (\<exists> v \<in> lineVelocity l . sNorm2 v = 1)"


abbreviation coneSet :: "Body \<Rightarrow> 'a Point \<Rightarrow> 'a Point set"
  where "coneSet m x \<equiv> { p . cone m x p }"


abbreviation regularConeSet :: "'a Point \<Rightarrow> 'a Point set"
  where "regularConeSet x \<equiv> { p . regularCone x p }"




end (* of class Cones *)

end (* of theory Cones *)

