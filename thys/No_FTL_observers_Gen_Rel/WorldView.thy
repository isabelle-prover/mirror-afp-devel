(*
   Author: Edward Higgins and Mike Stannett
   Date: July 2019

   Updated August 2019 for GenRel
   Updated: (MS) Jan 2023

*)

section \<open> WorldView \<close>

text \<open>This theory defines worldview transformations. These form the ultimate
foundation for all of GenRel's axioms.\<close>

theory WorldView
  imports Points
begin

(* 
  Worldview transformation 
  haromsalzburg: w_mk(p,q) defined by  ev_m(p) = ev_k(q) \<noteq> \<emptyset>
  where
    ev_m(p) := { b : W(m,b,p) }

*)


class WorldView = Points + 
fixes
(* Worldview relation *)
  W :: "Body \<Rightarrow> Body \<Rightarrow> 'a Point \<Rightarrow> bool" ("_ sees _ at _")
begin

abbreviation ev :: "Body \<Rightarrow> 'a Point \<Rightarrow> Body set"
  where "ev h x \<equiv> { b . h sees b at x }"

fun wvt :: "Body \<Rightarrow> Body \<Rightarrow> 'a Point \<Rightarrow> 'a Point set"
  where "wvt m k p = { q. (\<exists> b . (m sees b at p)) \<and> (ev m p = ev k q) }"

abbreviation wvtFunc :: "Body \<Rightarrow> Body \<Rightarrow> ('a Point \<Rightarrow> 'a Point \<Rightarrow> bool)"
  where "wvtFunc m k \<equiv> (\<lambda> p q . q \<in> wvt m k p)"

(* image of a line under a WVT *)
abbreviation wvtLine :: "Body \<Rightarrow> Body \<Rightarrow> 'a Point set \<Rightarrow> 'a Point set \<Rightarrow> bool"
  where "wvtLine m k l l' \<equiv>   \<exists> p q p' q' . (
                                   (wvtFunc m k p p') \<and> (wvtFunc m k q q') \<and>
                                   (l = lineJoining p q) \<and> (l' = lineJoining p' q'))"

end (* of class WorldView *)

end (* of theory WorldView *)

