(*
   ObserverConeLemma.thy
   Author: Mike Stannett
   m.stannett@sheffield.ac.uk
   Date: Aug 2020
   Updated: Feb 2023
*)

section \<open> ObserverConeLemma \<close>

text \<open>This theory gives sufficient conditions for an observed observer's cone
to appear upright to that observer.\<close>

theory ObserverConeLemma
  imports Proposition3
begin

class ObserverConeLemma = Proposition3
begin



lemma lemConeOfObserved:
  assumes "affineApprox A (wvtFunc m k) x"
and       "m sees k at x"
shows     "coneSet k (A x) = regularConeSet (A x)"
proof -  
  have Ax: "\<forall>y. (wvtFunc m k x y) \<longleftrightarrow> (y = A x)" 
    using assms(1) lemAffineEqualAtBase[of "(wvtFunc m k)" "A" "x"]
    by auto

  define set1 where set1: "set1 = coneSet k (A x)"
  define set2 where set2: "set2 = regularConeSet (A x)"
  define P where P: "P = (\<lambda> A' y . (wvtFunc m k x y)
                \<and>    (affineApprox A' (wvtFunc m k) x)
                \<and>    (applyToSet (asFunc A') (coneSet m x) \<subseteq> coneSet k y)
                \<and>    (coneSet k y = regularConeSet y))"
  have "m sees k at x" using assms(2) by auto
  hence "\<exists> A' y . P A' y" using P lemProposition3[of "m" "k" "x"] by fast
  then obtain A' y where A'y: "P A' y" by auto
  
  have "wvtFunc m k x y" using P A'y by auto
  hence "y = A x" using Ax by auto
  moreover have "coneSet k y = regularConeSet y" using A'y P by auto
  ultimately show ?thesis using set1 set2 by auto
qed



end (* of class ObserverConeLemma *)

end (* of theory ObserverConeLemma *)
