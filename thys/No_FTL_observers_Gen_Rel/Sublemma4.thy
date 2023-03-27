(*
   Author:  Mike Stannett
   Date: April 2020
   Updated: Jan 2023
*)

section \<open> Sublemma4 \<close>

text \<open>This theory shows that functions with affine approximations are continuous
where approximated.\<close>

theory Sublemma4
  imports Affine AxTriangleInequality
begin

text \<open>Our naming of lemmas, propositions, etc., is sometimes counterintuitive.
This is because the proof follows a hand-written proof, and we need to maintain 
the link between the paper-based and Isabelle versions. We will specifically be 
discussing how we translated from one to the other in a forthcoming paper (under 
construction). In fact, sublemmas 1 and 2 were eventually found to be 
unnecessary during construction of the Isabelle proof, and so do not appear in 
this documentation. 
\<close>

class Sublemma4 = Affine + AxTriangleInequality
begin

lemma sublemma4:
  assumes "affineApprox A f x"
  shows "(\<exists>\<delta>>0. \<forall>p. (p within \<delta> of x) \<longrightarrow> (definedAt f p)) \<and> (cts f x)"
proof -

  have diff: "(definedAt f x) \<and>
    (\<forall> \<epsilon> > 0 . (\<exists> \<delta> > 0 . (\<forall> y .
      ( (y within \<delta> of x)
        \<longrightarrow> 
        (definedAt f y) \<and> ( \<forall> u v . (f y u \<and> (asFunc A) y v) \<longrightarrow>
         ( sep2 v u ) \<le> (sqr \<epsilon>) * sep2 y x ))  )
  ))" using assms by simp

  have "0 < 1" by simp
  then obtain d where d: "(d > 0) \<and> (\<forall> y .
      ( (y within d of x) 
        \<longrightarrow> 
        ((definedAt f y) \<and> (\<forall> u v . (f y u \<and> (asFunc A) y v) \<longrightarrow>
         ( sep2 v u  \<le> (sqr 1) * sep2 y x )))))" using diff by blast
  hence "\<forall> p . (p within d of x) \<longrightarrow> (definedAt f p)" by blast
  hence rtp1: "\<exists> \<delta> > 0 . \<forall> p . (p within \<delta> of x) \<longrightarrow> (definedAt f p)"
    using d by auto

  (* CONTINUITY *)
  have funcF: "isFunction f" using assms by simp
  have affA: "affine A" using assms by simp
  have funcA: "isFunction (asFunc A)" using assms by simp
    
  { fix x'
    assume x': "f x x'"
    hence ax: "x' = A x" 
      using assms lemAffineEqualAtBase[of "f" "A" "x"] by blast

    { fix e
      assume epos: "e > 0"
      hence e2pos: "e/2 > 0" by simp

      (* continuity of A *)
      obtain d1 where d1: "(d1 > 0) \<and> (\<forall> y . 
         ((y within d1 of x) \<longrightarrow> ((A y) within (e/2) of (A x))))"
        using e2pos affA lemAffineContinuity by blast

      (* affine approximation *)
      obtain d2' where d2': "(d2' > 0) \<and> (\<forall> y .
      ( (y within d2' of x)  \<longrightarrow> ((definedAt f y) \<and>
        ( \<forall> fy Ay . (f y fy \<and> (asFunc A) y Ay) \<longrightarrow>
         ( sep2 Ay fy ) \<le> (sqr (e/2)) * sep2 y x ))))" 
        using e2pos assms by auto
      then obtain d2 
        where d2: "(d2 > 0) \<and> (d2 < d2') \<and> (sqr d2 < d2) \<and> (d2 < 1)"
        using lemReducedBound[of "d2'"] by auto

      define d where d: "d = min d1 d2"
      have dd1: "d \<le> d1" using d by auto
      have dd2: "d \<le> d2" using d by auto
      have dpos: "d > 0" using d1 d2 d by auto

      (* Main part of proof *)
      (* need to show y' within e of x' *)
      { fix y'
        assume y': "y' \<in> applyToSet f (ball x d)"
        then obtain y where y: "(y \<in> ball x d) \<and> (f y y')" by auto
        hence y_near_x: "y within d of x" using lemSep2Symmetry by auto

        have "y within d1 of x" using lemBallInBall y_near_x dpos dd1 by auto
        hence dist1: "(A y) within (e/2) of (A x)" using d1 by auto


        have yd2'x: "y within d2' of x" using lemBallInBall y_near_x dpos d2 dd2 by auto
        hence "\<forall> fy Ay . (f y fy \<and> (asFunc A) y Ay) \<longrightarrow>
         ( sep2 Ay fy  \<le> (sqr (e/2)) * sep2 y x )" 
          using d2' by auto
        hence conc2: "sep2 (A y) y'  \<le> (sqr (e/2)) * sep2 y x" using y by auto

        have "y within d2 of x" using lemBallInBall y_near_x dpos d2 dd2 by auto
        hence yx1: "y within 1 of x" using lemBallInBall d2 by auto

        have "sqr (e/2) > 0" using e2pos lemSqrMonoStrict[of "0" "e/2"] by auto
        hence "(sqr (e/2)) * sep2 y x < sqr (e/2)"
          using mult_strict_left_mono[of "sep2 y x" "1" "sqr (e/2)"] 
                lemNorm2NonNeg[of "y\<ominus>x"] yx1
          by auto
        hence dist2: "sep2 (A y) y' < sqr (e/2)" using conc2 by auto

        (* Now apply the triangle inequality *)
        define p where p: "p = (A x)"
        define q where q: "q = (A y)"
        define r where r: "r = y'"

        have tri: "axTriangleInequality (q\<ominus>p) (r\<ominus>q)"
          using AxTriangleInequality by blast
        have Dist1: "p within (e/2) of q" 
          using dist1 p q lemSep2Symmetry by auto
        have Dist2: "r within (e/2) of q" 
          using dist2 q r lemSep2Symmetry by auto

        have "r within ((e/2)+(e/2)) of p"
          using e2pos Dist1 Dist2 tri           
                lemDistancesAdd[of "q" "p" "r" "e/2" "e/2"]
          by blast
        hence "r within e of p" using lemSumOfTwoHalves by auto
        hence "y' \<in> ball x' e" using p r ax lemSep2Symmetry by auto
      }
      hence "\<exists>d>0. applyToSet f (ball x d) \<subseteq> (ball x' e)" using dpos by auto
    }
    hence "(\<forall>e>0. \<exists>d>0. applyToSet f (ball x d) \<subseteq> (ball x' e))" 
      by auto   
  }
  hence "\<forall>x'. (f x x') \<longrightarrow> (\<forall>e>0. \<exists>d>0. applyToSet f (ball x d) \<subseteq> (ball x' e))" 
    by auto   
  hence rtp2: "cts f x" by simp

  thus ?thesis using rtp1 by auto
qed


end (* of class Sublemma4 *)

end (*of theory Sublemma4 *)
