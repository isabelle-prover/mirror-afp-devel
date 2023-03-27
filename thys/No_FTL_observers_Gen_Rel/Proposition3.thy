(*
   Proposition3.thy
   Author: Mike Stannett
   m.stannett@sheffield.ac.uk
   Date: Aug 2020
   Updated: Feb 2023
*)

section \<open> Proposition3 \<close>

text \<open>This theory collects together earlier results to show that 
worldview transformations can be approximated by affine transformations
that have various useful properties. \<close>

theory Proposition3
  imports Proposition1 Proposition2 AxEventMinus
begin

class Proposition3 = Proposition1 + Proposition2 + AxEventMinus
begin




lemma lemProposition3:
  assumes "m sees k at x"
  shows   "\<exists> A y . (wvtFunc m k x y)
              \<and>    (affineApprox A (wvtFunc m k) x)
              \<and>    (applyToSet (asFunc A) (coneSet m x) \<subseteq> coneSet k y)
              \<and>    (coneSet k y = regularConeSet y)"
proof -
  define g1 where g1: "g1 = (\<lambda> y . wvtFunc m k x y)"
  define g2 where g2: "g2 = (\<lambda> A . affineApprox A (wvtFunc m k) x)"
  define g3 where g3: "g3 = (\<lambda> A y . applyToSet (asFunc A) (coneSet m x) \<subseteq> coneSet k y)"
  define g4 where g4: "g4 = (\<lambda> y . coneSet k y = regularConeSet y)"

  have "axEventMinus m k x" using AxEventMinus by simp
  hence "(\<exists> q . \<forall> b . ( (m sees b at x) \<longleftrightarrow> (k sees b at q)))"
    using assms by simp

  (* goal 1 *)
  then obtain y where y: "\<forall> b . ( (m sees b at x) \<longleftrightarrow> (k sees b at y))" by auto
  hence "ev m x = ev k y" by blast
  hence goal1: "g1 y" using assms g1 by auto

  (* goal 2*)
  have "axDiff m k x" using AxDiff by simp
  hence "\<exists> A . affineApprox A (wvtFunc m k) x" using g1 goal1 by blast
  then obtain A where goal2: "g2 A" using g2 by auto

  (* goal 3 *)
  have "applyToSet (asFunc A) (coneSet m x) \<subseteq> coneSet k (A x)"
    using g2 goal2 lemProposition2[of "m" "k" "A" "x"]
    by auto
  moreover have "A x = y"
    using goal1 goal2 g1 g2 lemAffineEqualAtBase[of "wvtFunc m k" "A" "x"]
    by blast
  ultimately have goal3: "g3 A y" using g3 by auto

  (* goal 4 *)
  have "k sees k at y" using assms(1) g1 goal1 by fastforce
  hence "\<forall> p . cone k y p = regularCone y p" 
    using lemProposition1[of "y" "k"] by auto
  hence goal4: "g4 y" using g4 by force

  (* and finally *)
  hence "\<exists> A  y . (g1 y) \<and> (g2 A) \<and> (g3 A y) \<and> (g4 y)"  
    using goal1 goal2 goal3 goal4 by blast

  thus ?thesis using g1 g2 g3 g4 by fastforce
qed 



end (* of class Proposition3 *)

end (* of theory Proposition3 *)
