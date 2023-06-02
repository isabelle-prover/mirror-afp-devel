(*
   Author: Mike Stannett
   m.stannett@sheffield.ac.uk
   July 2020
   Updated: Feb 2023
*)

section \<open> TangentLineLemma \<close>

text \<open>This theory shows that affine approximations map tangent 
lines to tangent lines. \<close>

theory TangentLineLemma
  imports MainLemma AxDiff Cones
begin

class TangentLineLemma = MainLemma + AxDiff + Cones
begin

(* We show that worldview transformations satisfy the requirements for lemMainLemma *)

lemma lemWVTImpliesFunction: "isFunction (wvtFunc k h)"
proof -
  { fix x p q
    assume hyp: "wvtFunc k h x p \<and> wvtFunc k h x q"

    have "axDiff k h x" using AxDiff by blast
    hence axdiff: "(\<exists> r . wvtFunc k h x r) 
                         \<longrightarrow> (\<exists> A . (affineApprox A (wvtFunc k h) x ))" 
      by auto

    then obtain A where A: "affineApprox A (wvtFunc k h) x" using hyp by auto
    hence "\<forall>z. (wvtFunc k h x z) \<longleftrightarrow> (z = A x)" 
      using lemAffineEqualAtBase[of "wvtFunc k h" "A" "x"]
      by auto
    hence "p = A x \<and> q = A x" using hyp by blast
    moreover have "affine A" using A by auto
    ultimately have "p = q" by auto
  }
  thus ?thesis by force
qed


lemma lemWVTCts:
  assumes "definedAt (wvtFunc h k) p"
  shows   "cts (wvtFunc h k) p"
proof -
  have "axDiff h k p" using AxDiff by blast
  hence axdiff: "(\<exists> r . wvtFunc h k p r) \<longrightarrow> (\<exists> A . (affineApprox A (wvtFunc h k) p ))"
    by auto
  then obtain A where A: "affineApprox A (wvtFunc h k) p" using assms by auto
  thus ?thesis using sublemma4[of "wvtFunc h k" "A" "p"] by auto
qed


lemma lemWVTInverse: "invFunc (wvtFunc k h) = wvtFunc h k"
  by force


lemma lemWVTInverseCts: 
  assumes "wvtFunc k h p q"
  shows   "cts (wvtFunc h k) q"
proof -
  define whk where whk: "whk = wvtFunc h k"
  have "definedAt whk q \<longrightarrow> cts whk q" 
    using lemWVTCts[of "h" "k" "q"] whk by fast
  moreover have "definedAt whk q" using whk assms by auto
  ultimately have "cts whk q" by auto
  thus ?thesis using whk by auto
qed


lemma lemWVTInjective: "injective (wvtFunc k h)"
proof -
  define wkh where wkh: "wkh = wvtFunc k h"
  define inv where inv: "inv = invFunc wkh"
  define inv2 where inv2: "inv2 = invFunc inv"
  define whk where whk: "whk = wvtFunc h k"

  have 1:  "inv = whk" using inv whk wkh by force
  have 2:  "inv2 = wkh" using inv2 inv wkh by force

  have"isFunction whk" using lemWVTImpliesFunction whk by auto
  hence    "isFunction inv" using 1 by auto
  hence    "injective inv2" using inv2 by auto
  hence    "injective wkh" using 2 by auto
  thus ?thesis using wkh by auto
qed



lemma lemPresentation:
  assumes "x \<in> wline m b"
and       "tangentLine l (wline m b) x"
and       "affineApprox A (wvtFunc m k) x"
and       "wvtFunc m k x y"
and       "applyAffineToLine A l l'"
shows     "tangentLine l' (wline k b) y"
proof - 

  have main: "(tangentLine l (wline m b) x) \<longrightarrow>
              (injective (wvtFunc m k)) \<longrightarrow> 
              (affineApprox A  (wvtFunc m k) x) \<longrightarrow>
              ((wvtFunc m k) x y) \<longrightarrow>
              (cts (invFunc (wvtFunc m k)) y) \<longrightarrow> 
              (applyAffineToLine A l l') \<longrightarrow>
              (tangentLine l' (applyToSet (wvtFunc m k) (wline m b)) y)"
    using lemMainLemma[of "x" "wline m b" "l" "wvtFunc m k" "A" "y" "l'"]
    by blast

  have 1: "(tangentLine l (wline m b) x)" using assms(2) by auto
  have 2: "injective (wvtFunc m k)" using lemWVTInjective by auto
  have 3: "affineApprox A  (wvtFunc m k) x" using assms(3) by auto
  have 4: "(wvtFunc m k) x y" using assms(4) by auto

  have "invFunc (wvtFunc m k) = wvtFunc k m" using lemWVTInverse by auto
  moreover have "cts (wvtFunc k m) y" 
    using assms(4) lemWVTInverseCts[of "y" "m" "k" "x"] by auto
  ultimately have 5: "cts (invFunc (wvtFunc m k)) y" by force

  have 6: "applyAffineToLine A l l'" using assms(5) by auto

  hence tgt: "tangentLine l' (applyToSet (wvtFunc m k) (wline m b)) y"
    using main 1 2 3 4 5 by meson

  (* Main part done. Now finish up. *)

  (*
      "we will prove that there is an 0 < \<delta> such that
         w_mk[wl_m b] \<inter> B(w_mk(x),\<delta>)  =  wl_k(b) \<inter> B(w_mk(x),\<delta>)
      and this will imply that the tangent line A[l] of w_mk[wl_m b]
      at w_mk(x) will be the tangent line of wl_k(b) at w_mk(x)."
  *)

  have axdiff: "axDiff k m y" using AxDiff by blast
  hence "(\<exists> r . wvtFunc k m y r) 
             \<longrightarrow> (\<exists> A' . (affineApprox A' (wvtFunc k m) y ))" by blast
  then obtain A' where A': "affineApprox A' (wvtFunc k m) y" using assms(4) by auto
  hence "(\<exists>\<delta>>0. \<forall>p. (p within \<delta> of y) \<longrightarrow> (definedAt (wvtFunc k m) p))"
    using sublemma4[of "wvtFunc k m" "A'" "y"] by auto
  then obtain d where d: "(d > 0) \<and> (\<forall>p. 
                             (p within d of y) \<longrightarrow> (definedAt (wvtFunc k m) p))"
    by auto
  hence dpos: "d > 0" by auto

  define Ball where Ball: "Ball = ball y d"

  have l2r: "(applyToSet (wvtFunc m k) (wline m b)) \<inter> Ball  \<subseteq> (wline k b) \<inter> Ball" 
    using Ball by auto

  (* right \<subseteq> left *)
  { fix q
    assume q: "q \<in> (wline k b) \<inter> Ball"
    hence "q within d of y" using Ball lemSep2Symmetry by auto
    hence "definedAt (wvtFunc k m) q" using d by auto
    hence qset: "q \<in> applyToSet (wvtFunc m k) (wvt k m q)" by auto
 
    have "wvt k m q \<subseteq> applyToSet (wvtFunc k m) (wline k b)" using q by auto
    hence "wvt k m q \<subseteq> wline m b" by auto
    hence "applyToSet (wvtFunc m k) (wvt k m q) 
               \<subseteq> applyToSet (wvtFunc m k)  (wline m b)" by auto 
    hence "q \<in> applyToSet (wvtFunc m k)  (wline m b)" using qset by auto 
    hence "q \<in> (applyToSet (wvtFunc m k)  (wline m b)) \<inter> Ball" using qset q by auto 
  }
  hence r2l: "(wline k b) \<inter> Ball  \<subseteq> (applyToSet (wvtFunc m k)  (wline m b)) \<inter> Ball"
    by auto

  define lBall where lBall: "lBall = (applyToSet (wvtFunc m k)  (wline m b)) \<inter> Ball"
  define rBall where rBall: "rBall = (wline k b) \<inter> Ball"

  hence equ: "lBall = rBall" using l2r r2l lBall rBall by auto

  (* "... and this will imply ..." *)

  have yinBall: "y \<in> Ball" using Ball d by auto

  (* have   tgt: "tangentLine l' (applyToSet (wvtFunc m k) (wline m b)) y"  *)

  have tgt1: "y \<in> (applyToSet (wvtFunc m k) (wline m b))" using tgt  by auto
  hence "y \<in> lBall" using yinBall lBall by auto
  hence rtp1: "y \<in> wline k b" using equ rBall by auto

  have rtp2: "onLine y l'" using tgt by auto

  have tgt3: "accPoint y (applyToSet (wvtFunc m k) (wline m b))" using tgt by auto
  hence tgt3': "\<forall> \<epsilon> > 0. \<exists> q \<in> (applyToSet (wvtFunc m k) (wline m b)) . (y \<noteq> q) \<and> (inBall q \<epsilon> y)"
    by auto
  { fix e
    assume epos: "e > 0"
    define d1 where d': "d1 = min d e"
    have dd: "d1 \<le> d" using d' by auto
    have de: "d1 \<le> e" using d' by auto
    have d'pos: "d1 > 0" using dpos epos d' by auto

    then obtain q 
      where q: "q \<in> (applyToSet (wvtFunc m k) (wline m b)) \<and> (y \<noteq> q) \<and> (inBall q d1 y)" 
      using tgt3' by blast
    hence "q \<in> (applyToSet (wvtFunc m k) (wline m b)) \<and> (inBall q d y) \<and> (y \<noteq> q)" 
      using  lemBallInBall[of "q" "y" "d1" "d"] d'pos dd by auto
    hence "q \<in> lBall \<and> (y \<noteq> q) \<and> (inBall q d1 y)" 
      using q Ball lemSep2Symmetry lBall by auto
    hence "q \<in> rBall \<and> (y \<noteq> q) \<and> (inBall q e y)" 
      using lemBallInBall[of "q" "y" "d1" "e"] d'pos de equ by auto

    hence "\<exists> q \<in> rBall . (y \<noteq> q) \<and> (inBall q e y)" by auto
  }
  hence rtp3: "\<forall> e > 0. \<exists> q \<in> wline k b . (y \<noteq> q) \<and> (inBall q e y)" using rBall by auto


  have tgt4: "(\<exists> p . ( (onLine p l') \<and> (p \<noteq> y) \<and>
      (\<forall> \<epsilon> > 0 .  \<exists> \<delta> > 0 . \<forall> y' \<in> (applyToSet (wvtFunc m k) (wline m b)). (
        ( (y' within \<delta> of y) \<and> (y' \<noteq> y) )
        \<longrightarrow>
        ( \<exists> r . ((onLine r (lineJoining y y')) \<and> (r within \<epsilon> of p))))
      )
   ))" using tgt by auto
  then obtain p where p: "( (onLine p l') \<and> (p \<noteq> y) \<and>
      (\<forall> \<epsilon> > 0 .  \<exists> \<delta> > 0 . \<forall> y' \<in> (applyToSet (wvtFunc m k) (wline m b)). (
        ( (y' within \<delta> of y) \<and> (y' \<noteq> y) )
        \<longrightarrow>
        ( \<exists> r . ((onLine r (lineJoining y y')) \<and> (r within \<epsilon> of p))))
      ))" by auto
  have p1: "onLine p l'" using p by auto
  have p2: "p \<noteq> y" using p by auto
  { fix e
    assume epos: "e > 0"
    then obtain d2 where d2: "(d2 > 0) \<and> 
      (\<forall> y' \<in> (applyToSet (wvtFunc m k) (wline m b)). (
        ( (y' within d2 of y) \<and> (y' \<noteq> y) )
        \<longrightarrow>
        ( \<exists> r . ((onLine r (lineJoining y y')) \<and> (r within e of p))))
      )" using p by auto
    hence d2pos: "d2 > 0" by auto

    define dm where dm: "dm = min d2 d"
    have dmd2: "dm \<le> d2" using dm by auto
    have dmd:  "dm \<le> d"  using dm by auto
    have dmpos: "dm > 0" using dpos d2pos dm by auto

    { fix y'
      assume y': "(y' \<in> wline k b) \<and> (y' within dm of y) \<and> (y' \<noteq> y)"
      hence ydm: "y' within dm of y" by auto
      hence "y' within d of y" using dmpos dmd lemBallInBall[of "y'" "y" "dm" "d"] by auto
      hence "y' \<in> Ball" using Ball lemSep2Symmetry by auto
      hence "y' \<in> rBall" using y' rBall by auto
      hence yL: "y' \<in> lBall" using equ by auto
 
      have "y' within d2 of y" 
        using ydm dmpos dmd2 lemBallInBall[of "y'" "y" "dm" "d2"] by auto

      hence "y' \<in> (applyToSet (wvtFunc m k) (wline m b)) \<and> (y' within d2 of y) \<and> (y' \<noteq> y)"
        using y' yL lBall by auto
      hence "\<exists> r . ((onLine r (lineJoining y y')) \<and> (r within e of p))"
        using d2 by auto
    }
    hence "\<exists> dm > 0. \<forall> y' \<in> (wline k b) . 
              (y' within dm of y) \<and> (y' \<noteq> y)
                  \<longrightarrow> (\<exists> r . ((onLine r (lineJoining y y')) \<and> (r within e of p)))"
      using dmpos by blast
  }
  hence "\<forall> e > 0 . \<exists> dm > 0. \<forall> y' \<in> (wline k b) . 
              (y' within dm of y) \<and> (y' \<noteq> y)
                  \<longrightarrow> (\<exists> r . ((onLine r (lineJoining y y')) \<and> (r within e of p)))"
    by auto
  hence rtp4: "\<exists>p . ( (onLine p l') \<and> (p \<noteq> y) \<and> (\<forall> e > 0 . \<exists> dm > 0. \<forall> y' \<in> (wline k b) . 
              (y' within dm of y) \<and> (y' \<noteq> y)
                  \<longrightarrow> (\<exists> r . ((onLine r (lineJoining y y')) \<and> (r within e of p)))))"
    using p1 p2 by auto

  hence "tangentLine l' (wline k b) y" using rtp1 rtp2 rtp3 rtp4 by blast
  thus ?thesis by auto
qed


(* Re-expression of lemPresentation *)
lemma lemTangentLines:
  assumes "affineApprox A (wvtFunc m k) x"
and       "tl l m b x"
and       "applyAffineToLine A l l'"
and       "wvtFunc m k x y"
shows     "tl l' k b y"
proof - 
  have pres: "x \<in> wline m b
             \<longrightarrow> tangentLine l (wline m b) x
             \<longrightarrow> affineApprox A (wvtFunc m k) x
             \<longrightarrow> wvtFunc m k x y
             \<longrightarrow> applyAffineToLine A l l'
             \<longrightarrow> tangentLine l' (wline k b) y"
    using lemPresentation[of "x" "m" "b" "l" "k" "A" "y" "l'"] 
    by blast
  
  have 1: "x \<in> wline m b" using assms(2) by auto
  have 2: "tangentLine l (wline m b) x" using assms(2) by auto
  have 3: "affineApprox A (wvtFunc m k) x" using assms(1) by simp
  have 4: "wvtFunc m k x y" using assms(4) by simp
  have 5: "applyAffineToLine A l l'" using assms(3) by simp

  have "tangentLine l' (wline k b) y" using pres 1 2 3 4 5 by meson
  thus ?thesis by auto
qed



lemma lemSelfTangentIsTimeAxis: 
  assumes "tangentLine l (wline k k) x"
shows     "l = timeAxis"
proof -
  define s where s: "s = wline k k"
  hence "s \<subseteq> timeAxis" using s AxSelfMinus by blast
  hence xOnAxis: "onTimeAxis x" using assms(1) s by auto
  
  have x: "(x \<in> s) \<and> (onLine x l) \<and> (accPoint x s)
           \<and> (\<exists> p . ( (onLine p l) \<and> (p \<noteq> x) \<and>
                (\<forall> \<epsilon> > 0 .  \<exists> \<delta> > 0 . \<forall> z \<in> s. (
                  ( (z within \<delta> of x) \<and> (z \<noteq> x) )
                  \<longrightarrow>
                  ( \<exists> r . ((onLine r (lineJoining x z)) \<and> (r within \<epsilon> of p))))
      )))" using s assms(1) by auto
  then obtain p where
    p: "( (onLine p l) \<and> (p \<noteq> x) \<and>
      (\<forall> \<epsilon> > 0 .  \<exists> \<delta> > 0 . \<forall> z \<in> s. (
        ( (z within \<delta> of x) \<and> (z \<noteq> x) )
        \<longrightarrow>
        ( \<exists> r . ((onLine r (lineJoining x z)) \<and> (r within \<epsilon> of p))))
      ))" by auto

  (* Need to show that p is on tAxis *)
  have accxs: "accPoint x s" using x by auto

  define p0 where 
    p0: "p0 = \<lparr> tval = tval p, xval = 0, yval = 0, zval = 0 \<rparr>"
  hence p0OnAxis: "onTimeAxis p0" by auto

  define dp where dp: "dp = sep2 p p0"


  have pp0: "dp = sqr (tval p0 - tval p) + sqr (xval p0 - xval p) + 
                  sqr (yval p0 - yval p) + sqr (zval p0 - zval p)" 
    using dp p0 by simp
  moreover have "\<dots> = sqr (xval p) + sqr (yval p) + sqr (zval p)"
    using p0 by auto
  ultimately have dpval: "dp = sqr (xval p) + sqr (yval p) + sqr (zval p)"
    using dp by simp

  define e where e: "e = (min dp 1) / 2"
  define e2 where e2: "e2 = sqr e"
  have e2ledp: "e2 \<le> dp" 
  proof -
    have msmall: "0 \<le> (min dp 1) \<le> 1" using lemNorm2NonNeg dp by auto
    hence esmall: "0 \<le> e < 1" using e leI by force
    hence e2lte: "e2 \<le> e" using e2 mult_left_le by force

    have mrange: "0 \<le> (min dp 1) \<le> dp" using lemNorm2NonNeg dp by auto
    hence "e \<le> dp/2" using e divide_right_mono zero_le_numeral by blast
    hence "e \<le> dp" using msmall e add_increasing2 divide_nonneg_nonneg 
          le_cases lemSumOfTwoHalves min_def zero_le_numeral
      by metis
      
    thus ?thesis using e2lte by auto
  qed

        
  have offaxis: "\<forall> z . (dp > 0) \<and> onTimeAxis z \<longrightarrow> \<not> (z within e of p)"
  proof - 
    { fix z
      { assume z: "(dp > 0) \<and> onTimeAxis z"
  
        have "sep2 z p = sqr (tval z - tval p) 
                       + sqr (xval z - xval p) 
                       + sqr (yval z - yval p) 
                       + sqr (zval z - zval p)" using p0 by simp
        moreover have "\<dots> = sep2 z p0 
                       + sqr (xval p) + sqr (yval p) + sqr (zval p)" 
          using p0 z by auto
        moreover have "\<dots> = sep2 z p0 + dp" 
          using dpval add_assoc 
          by presburger
        moreover have "\<dots> \<ge> dp" using lemNorm2NonNeg by simp
        ultimately have "sep2 z p \<ge> e2" 
          using e2ledp dual_order.trans by presburger
      }
      hence "(0 < dp) \<and> onTimeAxis z \<longrightarrow> \<not> (z within e of p)" 
        using e2 by auto        
    }
    thus ?thesis by auto
  qed


  (* claim: dp = 0. Prove by contradiction *)
  { assume dpnz: "dp > 0"

    hence enz: "e > 0" using e by auto
    then obtain d where d: "(d > 0) \<and> (\<forall> z \<in> s. (
          ( (z within d of x) \<and> (z \<noteq> x) )
          \<longrightarrow>
          ( \<exists> r . ((onLine r (lineJoining x z)) \<and> (r within e of p)))))"
        using p by blast

    obtain q where q: "(q \<in> s) \<and> (x \<noteq> q) \<and> (inBall q d x)"
      using accxs dpnz enz d by blast

    hence qOnAxis: "q \<in> timeAxis" using s AxSelfMinus by blast

    have qprops: "(q within d of x) \<and> (q \<noteq> x)" using q by auto
    then obtain r where r: "(onLine r (lineJoining x q)) \<and> (r within e of p)"
      using d q by blast

    have "x \<noteq> q" using q by auto
    moreover have "onLine x timeAxis" using xOnAxis lemTimeAxisIsLine by auto
    moreover have "onLine q timeAxis" using qOnAxis lemTimeAxisIsLine by auto
    ultimately have "timeAxis = lineJoining x q"
      using lemLineAndPoints[of "x" "q" "timeAxis"]
      by auto
    hence rOnAxis: "(onTimeAxis r)" using r by auto

    hence "\<not> (r within e of p)" using offaxis dpnz by blast

    hence "False" using r by blast
  }
  hence "\<not> (dp > 0) \<and> (dp \<ge> 0)" using lemNorm2NonNeg dp by auto
  hence "dp = 0" by auto
  hence "p = p0" using dp lemNullImpliesOrigin[of "p \<ominus> p0"] by auto

  hence "onLine p timeAxis" using p0OnAxis lemTimeAxisIsLine by auto
  moreover have "onLine x timeAxis" using xOnAxis lemTimeAxisIsLine by auto
  moreover have pnotx: "p \<noteq> x" using p by blast
  ultimately have xp: "timeAxis = lineJoining x p" 
    using lemLineAndPoints[of "x" "p" "timeAxis"] 
    by auto

  have "onLine p l" using p by auto
  moreover have "onLine x l" using x by auto
  ultimately have "l = lineJoining x p"
    using lemLineAndPoints[of "x" "p" "l"]  pnotx
    by auto

  hence "timeAxis = l" using xp by auto
  thus ?thesis using s by blast
qed



lemma lemTangentLineUnique:
  assumes "tl l1 m k x"
and       "tl l2 m k x"
and       "affineApprox A (wvtFunc m k) x"
and       "wvtFunc m k x y"
and       "x \<in> wline m k"
shows     "l1 = l2"
proof -
  define L1 where L1: "L1 = applyToSet (asFunc A) l1"
  define L2 where L2: "L2 = applyToSet (asFunc A) l2"

  define p1  where p1:  "p1  = (x \<in> wline m k)"
  define p2a where p2a: "p2a = tangentLine l1 (wline m k) x"
  define p2b where p2b: "p2b = tangentLine l2 (wline m k) x"
  define p3  where p3:  "p3  = affineApprox A (wvtFunc m k) x"
  define p4  where p4:  "p4  = wvtFunc m k x y"
  define p5a where p5a: "p5a = applyAffineToLine A l1 L1"
  define p5b where p5b: "p5b = applyAffineToLine A l2 L2"

  define tgt1 where tgt1: "tgt1 = tangentLine L1 (wline k k) y"
  define tgt2 where tgt2: "tgt2 = tangentLine L2 (wline k k) y"

  have pre1:  "p1"  using p1  assms(5) by auto
  have pre2a: "p2a" using p2a assms(1) by auto
  have pre2b: "p2b" using p2b assms(2) by auto
  have pre3:  "p3"  using p3  assms(4) using assms(3) by auto
  have pre4:  "p4"  using p4  assms(4) by auto

  have "isLine l1" using assms(1) by auto
  hence pre5a: "p5a" using p5a L1 assms(3) lemAffineOfLineIsLine[of "l1" "A" "L1"] by auto

  have "isLine l2" using assms(2) by auto
  hence pre5b: "p5b" using p5b L2 assms(3) lemAffineOfLineIsLine[of "l2" "A" "L2"] by auto

  (* L1 = timeAxis = L2 *)
  have "\<lbrakk> p1; p2a; p3; p4; p5a \<rbrakk> \<Longrightarrow> tgt1"
    using p1 p2a p3 p4 p5a tgt1 lemPresentation[of "x" "m" "k" "l1" "k" "A" "y" "L1"]
    by fast
  hence "tgt1" using pre1 pre2a pre3 pre4 pre5a by auto
  hence L1axis: "L1 = timeAxis" using tgt1 lemSelfTangentIsTimeAxis by auto    
    
  have "\<lbrakk> p1; p2b; p3; p4; p5b \<rbrakk> \<Longrightarrow> tgt2"
    using p1 p2b p3 p4 p5b tgt2 lemPresentation[of "x" "m" "k" "l2" "k" "A" "y" "L2"]
    by fast
  hence "tgt2" using pre1 pre2b pre3 pre4 pre5b by auto
  hence "L2 = timeAxis" using tgt2 lemSelfTangentIsTimeAxis by auto  

  hence L1L2: "L1 = L2" using L1axis by auto

  (* now apply inverse of A to L1 and L2 *)
  obtain A' where A': "(affine A') \<and> (\<forall> p q . A p = q \<longleftrightarrow> A' q = p)"
    using assms(3) lemInverseAffine[of "A"] by auto
  { fix p
    define q where q: "q = A p"
    hence A'q: "A' q = p" using A' by auto

    { assume "p \<in> l1"
      hence "q \<in> L2" using q L1 L1L2 by auto
      then obtain p2 where p2: "q = A p2 \<and> p2 \<in> l2" using L2 by auto
      hence "A' q = p2" using A' by auto
      hence "p = p2" using A'q by auto
      hence "p \<in> l2" using p2 by auto
    } 
    hence l2r: "p \<in> l1 \<longrightarrow> p \<in> l2" by blast
      
    { assume "p \<in> l2"
      hence "q \<in> L1" using q L2 L1L2 by auto
      then obtain p1 where p1: "q = A p1 \<and> p1 \<in> l1" using L1 by auto
      hence "A' q = p1" using A' by auto
      hence "p = p1" using A'q by auto
      hence "p \<in> l1" using p1 by auto
    } 
    hence "p \<in> l2 \<longrightarrow> p \<in> l1" by blast

    hence "p \<in> l1 \<longleftrightarrow> p \<in> l2" using l2r by auto
  }

  thus ?thesis by blast
qed




end (* of class TangentLineLemma *)

end (* of theory TangentLineLemma *)
