(*
   Author: Mike Stannett
   Date: 22 October 2012
   m.stannett@sheffield.ac.uk
   Updated 28 June 2016 to run under Isabelle2016.
   Updates June & July 2020 for GenRel-NoFTL
   Refactored Feb 2023
*)

section \<open> Points \<close>

text \<open>This theory defines (1+3)-dimensional spacetime points. The first
coordinate is the time coordinate, and the remaining three coordinates
give the spatial component.\<close>

theory Points
  imports Sorts 
begin

(*
  A point has four coordinates, but can be thought of in different ways
*)
record 'a Point = 
  tval :: "'a"
  xval :: "'a"
  yval :: "'a"
  zval :: "'a"

  
record 'a Space =
  svalx :: "'a"
  svaly :: "'a"
  svalz :: "'a"


abbreviation tComponent :: "'a Point \<Rightarrow> 'a" where
  "tComponent p \<equiv> tval p"

abbreviation sComponent :: "'a Point \<Rightarrow> 'a Space" where
  "sComponent p \<equiv> \<lparr> svalx = xval p, svaly = yval p, svalz = zval p \<rparr>"

abbreviation mkPoint :: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a Point" where
  "mkPoint t x y z \<equiv> \<lparr> tval = t, xval = x, yval =y, zval = z \<rparr>"

abbreviation stPoint :: "'a \<Rightarrow> 'a Space \<Rightarrow> 'a Point" where
  "stPoint t s \<equiv> mkPoint t (svalx s) (svaly s) (svalz s)"

abbreviation mkSpace :: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a Space" where
  "mkSpace x y z \<equiv> \<lparr> svalx = x, svaly =y, svalz = z \<rparr>"



text \<open> Points have coordinates in the field of quantities, 
and can be thought of as the end-points of
vectors pinned to the origin. We can translate and scale them, 
define accumulation points, etc.\<close>

class Points = Quantities 
begin

(* Translations *)
abbreviation moveBy :: "'a Point \<Rightarrow> 'a Point \<Rightarrow> 'a Point" ("_ \<oplus> _") where
"(p \<oplus> q) \<equiv> \<lparr> tval = tval p + tval q,
           xval = xval p + xval q,
           yval = yval p + yval q,
           zval = zval p + zval q \<rparr>"


abbreviation movebackBy :: "'a Point \<Rightarrow> 'a Point \<Rightarrow> 'a Point" ("_ \<ominus> _") where
"(p \<ominus> q)  \<equiv> \<lparr> tval = tval p - tval q,
           xval = xval p - xval q,
           yval = yval p - yval q,
           zval = zval p - zval q \<rparr>"

  
abbreviation sMoveBy :: "'a Space \<Rightarrow> 'a Space \<Rightarrow> 'a Space" ("_ \<oplus>s _") where
"(p \<oplus>s q) \<equiv> \<lparr> svalx = svalx p + svalx q,
              svaly = svaly p + svaly q,
              svalz = svalz p + svalz q \<rparr>"
  

abbreviation sMovebackBy :: "'a Space \<Rightarrow> 'a Space \<Rightarrow> 'a Space" ("_ \<ominus>s _") where
"(p \<ominus>s q) \<equiv> \<lparr> svalx = svalx p - svalx q,
              svaly = svaly p - svaly q,
              svalz = svalz p - svalz q \<rparr>"
  

(* Scaling *)
abbreviation scaleBy :: "'a \<Rightarrow> 'a Point \<Rightarrow> 'a Point" ("_ \<otimes> _")  where
  "scaleBy a p \<equiv> \<lparr> tval = a*tval p, xval = a*xval p,
                   yval = a*yval p, zval = a*zval p\<rparr>"

abbreviation sScaleBy :: "'a \<Rightarrow> 'a Space \<Rightarrow> 'a Space"  (" _ \<otimes>s _") where
  "sScaleBy a p \<equiv> \<lparr> svalx = a*svalx p,
                   svaly = a*svaly p, 
                   svalz = a*svalz p\<rparr>"


(* Origins *)
abbreviation sOrigin :: "'a Space" where
  "sOrigin \<equiv> \<lparr> svalx = 0, svaly = 0, svalz = 0 \<rparr>"
  
abbreviation origin :: "'a Point" where
"origin \<equiv> \<lparr> tval = 0, xval = 0, yval = 0, zval = 0 \<rparr>"

abbreviation tUnit :: "'a Point" where
"tUnit \<equiv> \<lparr> tval = 1, xval = 0, yval = 0, zval = 0 \<rparr>"

abbreviation xUnit :: "'a Point" where
"xUnit \<equiv> \<lparr> tval = 0, xval = 1, yval = 0, zval = 0 \<rparr>"

abbreviation yUnit :: "'a Point" where
"yUnit \<equiv> \<lparr> tval = 0, xval = 0, yval = 1, zval = 0 \<rparr>"

abbreviation zUnit :: "'a Point" where
"zUnit \<equiv> \<lparr> tval = 0, xval = 0, yval = 0, zval = 1 \<rparr>"

(* Time Axis *)    

abbreviation timeAxis :: "'a Point set" where
"timeAxis \<equiv> { p . xval p = 0 \<and> yval p = 0 \<and> zval p = 0 }"

abbreviation onTimeAxis :: "'a Point \<Rightarrow> bool"
  where "onTimeAxis p \<equiv> (p \<in> timeAxis)"

(* Separation functions *)  
subsection \<open> Squared norms and separation functions \<close>

text \<open>This theory defines squared norms and separations. We do not yet
define unsquared norms because we are not assuming here that quantities
necessarily have square roots.\<close>

abbreviation norm2 :: "'a Point \<Rightarrow> 'a" where
  "norm2 p \<equiv> sqr (tval p) + sqr (xval p) + sqr (yval p) + sqr (zval p)"

abbreviation sep2 :: "'a Point \<Rightarrow> 'a Point \<Rightarrow> 'a" where
  "sep2 p q \<equiv> norm2 (p \<ominus> q)"

abbreviation sNorm2 :: "'a Space \<Rightarrow> 'a" where
  "sNorm2 s \<equiv> sqr (svalx s)
            + sqr (svaly s)
            + sqr (svalz s)"

abbreviation sSep2 :: "'a Point \<Rightarrow> 'a Point \<Rightarrow> 'a" where
  "sSep2 p q \<equiv> sqr (xval p - xval q)
             + sqr (yval p - yval q)
             + sqr (zval p - zval q)" 

abbreviation mNorm2 :: "'a Point \<Rightarrow> 'a" ("\<parallel> _ \<parallel>m")
  where "\<parallel> p \<parallel>m \<equiv> sqr (tval p) - sNorm2 (sComponent p)"

subsection \<open> Topological concepts \<close>

text \<open>We will need to define topological concepts like continuity and
affine approximation later, so here we define open balls and accumulation points.\<close>

(* Open balls in Q^4 and accumulation points *)
abbreviation inBall :: "'a Point \<Rightarrow> 'a \<Rightarrow> 'a Point \<Rightarrow> bool"
("_ within _ of _")
where "inBall q \<epsilon> p \<equiv> sep2 q p < sqr \<epsilon>"

abbreviation ball :: "'a Point \<Rightarrow> 'a \<Rightarrow> 'a Point set"
  where "ball q \<epsilon> \<equiv> { p . inBall q \<epsilon> p }"

abbreviation accPoint :: "'a Point \<Rightarrow> 'a Point set \<Rightarrow> bool"
  where "accPoint p s \<equiv> \<forall> \<epsilon> > 0. \<exists> q \<in> s. (p \<noteq> q) \<and> (inBall q \<epsilon> p)"

subsection \<open> Lines \<close>

text \<open> A line is specified by giving a point on the line, 
and a point (thought of as a vector) giving its direction. For
these purposes it doesn't matter whether the direction is "positive" 
or "negative". \<close>


abbreviation line :: "'a Point \<Rightarrow> 'a Point \<Rightarrow> 'a Point set"
  where "line base drtn \<equiv> { p . \<exists> \<alpha> . p = (base \<oplus> (\<alpha>\<otimes>drtn)) }"

abbreviation lineJoining :: "'a Point \<Rightarrow> 'a Point \<Rightarrow> 'a Point set" 
  where "lineJoining p q \<equiv> line p (q\<ominus>p)"

abbreviation isLine :: "'a Point set \<Rightarrow> bool" 
  where "isLine l \<equiv> \<exists> b d . (l = line b d)"

abbreviation sameLine :: "'a Point set \<Rightarrow> 'a Point set \<Rightarrow> bool"
  where "sameLine l1 l2 \<equiv> ((isLine l1) \<or> (isLine l2)) \<and> (l1 = l2)"

abbreviation onLine :: "'a Point \<Rightarrow> 'a Point set \<Rightarrow> bool"
  where "onLine p l \<equiv> (isLine l) \<and> (p \<in> l)"

subsection \<open> Directions \<close>

text \<open> Given any two distinct points on a line, the vector joining them 
can be used to specify the line's direction. The direction of a line is
therefore a \emph{set} of points/vectors. By lemDrtn these are all parallel \<close>

fun drtn :: "'a Point set \<Rightarrow> 'a Point set"
  where "drtn l = { d . \<exists> p q . (p \<noteq> q) \<and> (onLine p l) \<and> (onLine q l) \<and> (d = (q \<ominus> p)) }"

abbreviation parallelLines :: "'a Point set \<Rightarrow> 'a Point set  \<Rightarrow> bool"
  where "parallelLines l1 l2 \<equiv> (drtn l1) \<inter> (drtn l2) \<noteq> {}"

abbreviation parallel :: "'a Point \<Rightarrow> 'a Point \<Rightarrow> bool" (" _ \<parallel> _ ")
  where "parallel p q \<equiv> (\<exists> \<alpha> \<noteq> 0 . p = (\<alpha> \<otimes> q))"

text \<open>The "slope" of a line can be either finite or infinite. We will often
need to consider these two cases separately.\<close>

abbreviation slopeFinite :: "'a Point \<Rightarrow> 'a Point \<Rightarrow> bool" 
  where "slopeFinite p q \<equiv> (tval p \<noteq> tval q)"


abbreviation slopeInfinite :: "'a Point \<Rightarrow> 'a Point \<Rightarrow> bool" 
  where "slopeInfinite p q \<equiv> (tval p = tval q)"


abbreviation lineSlopeFinite :: "'a Point set \<Rightarrow> bool" 
  where "lineSlopeFinite l \<equiv> (\<exists> x y . (onLine x l) \<and> (onLine y l) 
                                \<and> (x \<noteq> y) \<and> (slopeFinite x y))"


(* "origin" indicates infinite slope (or else p = q) *)
subsection \<open> Slopes and slopers \<close>

text \<open>We specify the slope of a line by giving the spatial component ("sloper") 
of the point on the line at time 1. This is defined if and only if the slope is finite. 
If the slope is infinite (the line is "horizontal") we return the spatial origin. This 
avoids using "option" but means we need to consider carefully whether a sloper with
value sOrigin indicates a truly zero slope or an infinite one.\<close>

fun sloper :: "'a Point \<Rightarrow> 'a Point \<Rightarrow> 'a Point" 
  where "sloper p q = (if (slopeFinite p q) then ((1 / (tval p - tval q)) \<otimes> (p \<ominus> q))
                       else origin)"

fun velocityJoining :: "'a Point \<Rightarrow> 'a Point \<Rightarrow> 'a Space" 
  where "velocityJoining p q = sComponent (sloper p q)"  


fun lineVelocity :: "'a Point set \<Rightarrow> 'a Space set" 
  where "lineVelocity l = { v . \<exists> d \<in> drtn l . v = velocityJoining origin d }"






(* ********************************************************************** *)
(* LEMMAS *)

lemma lemNorm2Decomposition:
  shows "norm2 u = sqr (tval u) + sNorm2 (sComponent u)"
  by (simp add: add_commute local.add.left_commute)



(* Structure *)

lemma lemPointDecomposition:
  shows "p = (((tval p)\<otimes>tUnit) \<oplus> (((xval p)\<otimes>xUnit) 
                     \<oplus> (((yval p)\<otimes>yUnit) \<oplus> ((zval p)\<otimes>zUnit))))"
  by force


(* Arithmetic *)

lemma lemScaleLeftSumDistrib: "((a + b) \<otimes> p) = ((a\<otimes>p) \<oplus> (b\<otimes>p))"
  using distrib_right by auto

lemma lemScaleLeftDiffDistrib: "((a - b) \<otimes> p) = ((a\<otimes>p) \<ominus> (b\<otimes>p))"
  using left_diff_distrib by auto

lemma lemScaleAssoc: "(\<alpha> \<otimes> (\<beta> \<otimes> p)) = ((\<alpha> * \<beta>) \<otimes> p)"
  using semiring_normalization_rules(18) by auto

lemma lemScaleCommute: "(\<alpha> \<otimes> (\<beta> \<otimes> p)) = (\<beta> \<otimes> (\<alpha> \<otimes> p))"
  using mult.left_commute by auto

lemma lemScaleDistribSum: "(\<alpha> \<otimes> (p \<oplus> q)) = ((\<alpha>\<otimes>p) \<oplus> (\<alpha>\<otimes>q))"
  using distrib_left by auto

lemma lemScaleDistribDiff: "(\<alpha> \<otimes> (p \<ominus> q)) = ((\<alpha>\<otimes>p) \<ominus> (\<alpha>\<otimes>q))"
  using right_diff_distrib by auto

lemma lemScaleOrigin: "(\<alpha> \<otimes> origin) = origin"
  by auto

(* Scaling *)
lemma lemMNorm2OfScaled: "mNorm2 (scaleBy \<alpha> p) = (sqr \<alpha>) * mNorm2 p"
  using lemSqrMult distrib_left right_diff_distrib' by simp

lemma lemSNorm2OfScaled: "sNorm2 (sScaleBy \<alpha> p) = (sqr \<alpha>) * sNorm2 p"
  using lemSqrMult distrib_left by auto

lemma lemNorm2OfScaled: "norm2 (\<alpha> \<otimes> p) = (sqr \<alpha>) * norm2 p"
  using lemSqrMult distrib_left by auto

lemma lemScaleSep2: "(sqr a) * (sep2 p q) = sep2 (a\<otimes>p) (a\<otimes>q)"
  using lemNorm2OfScaled[of "a" "p\<ominus>q"] lemScaleDistribDiff by auto

lemma lemSScaleAssoc: "(\<alpha> \<otimes>s (\<beta> \<otimes>s p)) = ((\<alpha> * \<beta>) \<otimes>s p)"
  using semiring_normalization_rules(18) by auto



lemma lemScaleBall: 
  assumes "x within e of y"
and       "a \<noteq> 0"
shows     "(a\<otimes>x) within (a*e) of (a\<otimes>y)"
proof - 
  have a2pos: "sqr a > 0" using assms(2) lemSquaresPositive by auto
  have "sep2 (a\<otimes>x) (a\<otimes>y) = (sqr a) * (sep2 x y)" using lemScaleSep2 by auto
  hence "sep2 (a\<otimes>x) (a\<otimes>y) < (sqr a) * (sqr e)"
    using assms mult_strict_left_mono a2pos by auto
  thus ?thesis using mult_commute mult_assoc by auto
qed


lemma lemScaleBallAndBoundary: 
  assumes "sep2 x y \<le> sqr e"
and       "a \<noteq> 0"
shows     "sep2 (a\<otimes>x) (a\<otimes>y) \<le> sqr (a*e)"
proof - 
  have a2pos: "sqr a > 0" using assms(2) lemSquaresPositive by auto
  have "sep2 (a\<otimes>x) (a\<otimes>y) = (sqr a) * (sep2 x y)" using lemScaleSep2 by auto
  hence "sep2 (a\<otimes>x) (a\<otimes>y) \<le> (sqr a) * (sqr e)"
    using assms mult_left_mono a2pos by auto
  thus ?thesis using mult_commute mult_assoc by auto
qed



(* lines *)

lemma lemTimeAxisIsLine: "isLine timeAxis"
proof -
  { fix p
    { assume p: "p \<in> timeAxis"
      hence "p = (origin \<oplus> ((tval p) \<otimes> tUnit))" by auto
    }
    hence l2r: "onTimeAxis p \<longrightarrow> (\<exists> v . (p = (origin \<oplus> (v \<otimes> tUnit))))" by blast

    { assume v: "\<exists> v . p = (origin \<oplus> (v \<otimes> tUnit))"
      hence "onTimeAxis p" by auto
    }
    hence "(\<exists> v . (p = (origin \<oplus> (v \<otimes> tUnit)))) \<longleftrightarrow> onTimeAxis p" 
      using l2r by blast
  }
  hence "timeAxis = line origin tUnit" by blast
  thus ?thesis by blast
qed



lemma lemSameLine:
  assumes "p \<in> line b d"
shows     "sameLine (line b d) (line p d)"
proof -
  define l1 where l1: "l1 = line b d"
  define l2 where l2: "l2 = line p d"
  have lines: "isLine l1 \<and> isLine l2" using l1 l2 by blast

  obtain A where p: "p = (b \<oplus> (A \<otimes> d))" using assms by auto
  hence b: "b = (p \<ominus> (A \<otimes> d))" by auto

  { fix x
    { assume x: "x \<in> l1"
      then obtain a where a: "x = (b \<oplus> (a\<otimes>d))" using l1 by auto
      hence "x = ((p \<ominus> (A \<otimes> d)) \<oplus> (a\<otimes>d))" using b by simp
      also have "\<dots> = (p \<oplus> ((a\<otimes>d)\<ominus>(A\<otimes>d)))" 
        using add_diff_eq diff_add_eq add_commute add_assoc by simp
      finally have "x = (p \<oplus> ((a-A)\<otimes>d))" 
        using lemScaleLeftDiffDistrib by presburger
      hence "x \<in> l2" using l2 by auto
    }
    hence l2r: "(x \<in> l1) \<longrightarrow> (x \<in> l2)" using l2 by simp

    { assume x: "x \<in> l2"
      then obtain a where a: "x = (p \<oplus> (a \<otimes> d))" using l2 by auto
      hence "x = (b \<oplus> ((A+ a)\<otimes>d))"
        using p add_assoc lemScaleAssoc distrib by auto
      hence "x \<in> l1" using l1 by auto
    }
    hence "(x \<in> l1) \<longleftrightarrow> (x \<in> l2)" using l2r by auto
  }
  thus ?thesis using lines l1 l2 by auto
qed


(* Separation symmetry lemmas *)


lemma lemSSep2Symmetry: "sSep2 p q = sSep2 q p"
  using lemSqrDiffSymmetrical by simp

lemma lemSep2Symmetry: "sep2 p q = sep2 q p"
  using lemSqrDiffSymmetrical by simp


(* Only origin has zero size *)
lemma lemSpatialNullImpliesSpatialOrigin:
assumes "sNorm2 s = 0"
shows "s = sOrigin" 
  using assms local.add_nonneg_eq_0_iff by auto


lemma lemNorm2NonNeg: "norm2 p \<ge> 0"
  by simp


lemma lemNullImpliesOrigin:
assumes "norm2 p = 0"
shows "p = origin"
proof -
  have "norm2 p = sqr (tval p) + sNorm2 (sComponent p)" using add_assoc by simp
  hence a: "sqr (tval p) + sNorm2 (sComponent p) = 0" using assms by auto
  { assume b: "sNorm2 (sComponent p) > 0"
    have "sqr (tval p) + sNorm2 (sComponent p) > 0"
      using b lemSumOfNonNegAndPos by auto
    hence "False" using a by auto
  }
  hence c: "\<not>(sNorm2 (sComponent p) > 0)" by auto
  have d: "sNorm2 (sComponent p) \<ge> 0" by auto
  
  have "\<forall> x . (\<not>(x > 0))  \<and>  (x \<ge> 0)  \<longrightarrow>  x = 0" by auto
  hence e: "sNorm2 (sComponent p) = 0" using c d by force
  hence f: "sComponent p = sOrigin" 
    using lemSpatialNullImpliesSpatialOrigin by blast
  
  have     "norm2 p = sqr (tval p)" using e add_assoc by auto
  hence    "sqr (tval p) = 0" using assms  by simp
  hence    "(tval p) = 0" using lemZeroRoot by simp
  
  thus ?thesis using f by auto
qed


lemma lemNotOriginImpliesPosNorm2:
assumes "p \<noteq> origin"
shows "norm2 p > 0"
proof -
have 1: "norm2 p \<ge> 0" by simp
have 2: "norm2 p \<noteq> 0" using assms(1) lemNullImpliesOrigin by force
thus ?thesis using 1 2 dual_order.not_eq_order_implies_strict by fast
qed


lemma lemNotEqualImpliesSep2Pos:
  assumes "y \<noteq> x"
  shows "sep2 y x > 0"
proof -
  have "(y\<ominus>x) \<noteq> origin" using assms by auto
  hence 1: "norm2 (y\<ominus>x) > 0" using lemNotOriginImpliesPosNorm2 by fast
  have "sep2 y x = norm2 (y\<ominus>x)" by auto
  thus ?thesis using 1 by auto
qed


lemma lemBallContainsCentre:
  assumes "\<epsilon> > 0"
  shows "x within \<epsilon> of x"
proof -
  have "sep2 x x = 0" by auto
  thus ?thesis using assms by auto
qed


lemma lemPointLimit:
  assumes "\<forall> \<epsilon> > 0 . (v within \<epsilon> of u)"
  shows "v = u"
proof -
  define d where d: "d = sep2 v u"
  { assume "v \<noteq> u"
    hence "d > 0" using lemNotEqualImpliesSep2Pos d by auto
    then obtain s where s: "(0 < s) \<and> (sqr s < d)" using lemSmallSquares by auto
    hence "v within s of u" using d assms(1) by auto
    hence "sep2 v u < sep2 v u" using s d by auto
    hence "False" by auto
  }
  thus ?thesis by auto
qed


lemma lemBallPopulated:
  assumes "e > 0"
  shows "\<exists> y . (y within e of x) \<and> (y \<noteq> x)"
proof -
  obtain e1 where e1: "(0 < e1) \<and> (e1 < e) \<and> (sqr e1 < e1)" 
    using assms lemReducedBound by auto
  hence e2: "sqr e1 < sqr e" using lemSqrMonoStrict[of "e1" "e"] by auto

  define y where y: "y = (x \<oplus> \<lparr> tval = e1, xval=0, yval=0, zval=0 \<rparr>)"
  hence "(y \<ominus> x) = \<lparr> tval = e1, xval=0, yval=0, zval=0 \<rparr>" by auto
  hence "sep2 y x = sqr e1" by auto
  hence 1: "y within e of x" using e2  by auto

  have "tval y = tval x + e1" using y by simp
  hence "y \<noteq> x" using e1 by auto
  thus ?thesis using 1 by auto
qed

lemma lemBallInBall:
  assumes "p within x of q"
and       "0 < x \<le> y"
shows     "p within y of q"
proof -
  have "sqr x \<le> sqr y" using assms(2) lemSqrMono by auto
  thus ?thesis using le_less_trans using assms(1) by auto
qed



lemma lemSmallPoints:
  assumes "e > 0"
  shows "\<exists> a > 0 . norm2 (a\<otimes>p) < sqr e"
proof -

  { assume po: "p = origin"
    define a where a: "a = 1"
    hence apos: "a > 0" by auto
    have "norm2 (a\<otimes>p) < sqr e" using a po assms by auto
    hence ?thesis using apos by auto
  }
  hence case1: "p = origin \<longrightarrow> ?thesis" by auto

  { assume pnoto: "p \<noteq> origin"

    obtain e1 where e1: "(e1 > 0) \<and> (e1 < e) \<and> (sqr e1 < e1)" 
      using lemReducedBound assms by auto
    hence e1sqr: "0 < (sqr e1) < (sqr e)" using lemSqrMonoStrict by auto

    define n2 where n2: "n2 = norm2 p"
    hence n2pos: "n2 > 0" using pnoto lemNotOriginImpliesPosNorm2 by auto
    then obtain s where s: "(s > 0) \<and> (sqr s > n2)" 
      using lemSquareExistsAbove by auto
    hence "0 < (n2/(sqr s)) < 1" using n2pos by auto
    hence "(sqr e1)*(n2/(sqr s)) < sqr e1" 
      using lemMultPosLT1[of "sqr e1" "(n2/(sqr s))"] e1sqr by auto
    hence ineq: "(sqr e1)*(n2/(sqr s)) < sqr e" using e1sqr by auto

    define a where a: "a = e1/s"
    have "e1 > 0 \<and> s > 0" using e1 s by auto
    hence apos: "a > 0" using a by auto
    have "norm2 (a\<otimes>p) = (sqr e1)*(n2/(sqr s))" 
      using lemNorm2OfScaled[of "a"] a n2 by auto
    hence "norm2 (a\<otimes>p) < sqr e" using ineq by auto
    hence ?thesis using apos by auto
  }
  hence "p \<noteq> origin \<longrightarrow> ?thesis" by auto

  thus ?thesis using case1 by auto
qed


lemma lemLineJoiningContainsEndPoints:
  assumes "l = lineJoining x p"
  shows "onLine x l \<and> onLine p l"
proof -
  have line: "isLine l" using assms(1) by blast
  have p: "x = (x \<oplus> (0 \<otimes> (p\<ominus>x)))" by simp
  have x: "p = (x \<oplus> (1 \<otimes> (p\<ominus>x)))" using add_commute diff_add_cancel by fastforce
  thus ?thesis using p line assms(1) by blast
qed


lemma lemLineAndPoints:
  assumes "p \<noteq> q"
  shows   "(onLine p l \<and> onLine q l) \<longleftrightarrow> (l = lineJoining p q)"
proof -
  
  define lj  where lj : "lj  = lineJoining p q"
  define lhs where lhs: "lhs = (onLine p l \<and> onLine q l)"
  define rhs where rhs: "rhs = (l = lj)"

  { assume hyp: "lhs"
    then obtain b d where bd: "l = { x. \<exists> a. x = (b \<oplus> (a\<otimes>d)) }" using lhs by auto

    obtain ap where ap: "p = (b \<oplus> (ap \<otimes> d))" using hyp lhs bd by auto
    obtain aq where aq: "q = (b \<oplus> (aq \<otimes> d))" using hyp lhs bd by auto
    hence "(q\<ominus>p) = ((b \<oplus> (aq \<otimes> d)) \<ominus>  (b \<oplus> (ap \<otimes> d)))" using ap by fast
    also have "... = ((aq \<otimes> d) \<ominus> (ap \<otimes> d))" using add_diff_cancel by auto
    finally have qdiffp: "(q\<ominus>p) = ((aq - ap) \<otimes> d)" 
      using lemScaleLeftDiffDistrib[of "aq" "ap" "d"] by auto

    define R where R: "R = aq - ap"
    hence Rnz: "R \<noteq> 0" using assms(1) qdiffp by auto
    define r where r: "r = 1/R"
    hence "(r\<otimes>(R \<otimes> d)) = (r \<otimes> (q\<ominus>p))" using R qdiffp by auto
    hence d: "d = (r \<otimes> (q\<ominus>p))" using lemScaleAssoc[of "r" "R" "d"] r Rnz by force

    have "b = (p \<ominus> (ap \<otimes> d))" using ap by auto
    also have "... = (p \<ominus> (ap \<otimes> (r \<otimes> (q\<ominus>p))))" using d by auto
    finally have b: "b = (p \<ominus> ( (ap*r) \<otimes> (q\<ominus>p)))" 
      using lemScaleAssoc[of "ap" "r" "q\<ominus>p"] by auto

    { fix x
      assume "x \<in> l"
      then obtain a where "x = (b \<oplus> (a \<otimes> d))" using bd by auto
      hence "x = ((p \<ominus> ((ap*r) \<otimes> (q\<ominus>p))) \<oplus> ((a*r) \<otimes> (q\<ominus>p)))"
        using b d lemScaleAssoc[of "a" "r" "q\<ominus>p"] by fastforce
      also have "... = (p \<oplus> ( ((a*r)\<otimes>(q\<ominus>p)) \<ominus> ((ap*r)\<otimes>(q\<ominus>p)) ))"
        using add_diff_eq diff_add_eq by force
      also have "... = (p \<oplus> (((a*r)-(ap*r))\<otimes>(q\<ominus>p)))"
        using left_diff_distrib by force
      finally have "x \<in> lj" using lj by auto
    }
    hence l2r: "l \<subseteq> lj" by auto

    { fix x
      assume "x \<in> lj"
      then obtain a where a: "x = (p \<oplus> (a \<otimes>(q\<ominus>p)))" using lj by auto
      hence "x = ((b \<oplus> (ap \<otimes> d)) \<oplus> (a \<otimes>(R \<otimes> d)))" using ap qdiffp R by auto
      also have "... = (b \<oplus> ((ap + a*R)\<otimes>d))" 
        using add_assoc distrib_right lemScaleAssoc
        by auto
      finally have "onLine x l" using bd by auto
    }
    hence "lj \<subseteq> l" by auto
    hence "l = lj" using l2r by auto
  }
  hence L2R: "lhs \<longrightarrow> rhs" using rhs by auto

  { assume l: "rhs"
    hence line: "isLine l" using rhs lj by blast
    have p: "p = (p \<oplus> (0 \<otimes> (q\<ominus>p)))" by simp
    have q: "q = (p \<oplus> (1 \<otimes> (q\<ominus>p)))" using add_commute diff_add_cancel by fastforce
    hence "lhs" using p line l lhs rhs lj by blast
  }
  hence "rhs \<longrightarrow> lhs" by auto

  hence "lhs \<longleftrightarrow> rhs" using L2R by auto

  thus ?thesis using lhs rhs lj by auto
qed



lemma lemLineDefinedByPair:
  assumes "x \<noteq> p"
and       "(onLine p l1) \<and> (onLine x l1)"
and       "(onLine p l2) \<and> (onLine x l2)"
  shows "l1 = l2"
proof - 
  have "l1 = lineJoining x p" 
    using lemLineAndPoints[of "x" "p" "l1"] assms(1) assms(2) by auto
  also have "... = l2" 
    using lemLineAndPoints[of "x" "p" "l2"] assms(1) assms(3) by auto
  finally show "l1 = l2" by auto
qed


lemma lemDrtn: 
  assumes "{ d1, d2 } \<subseteq> drtn l" 
  shows "\<exists> \<alpha> \<noteq> 0 . d2 = (\<alpha> \<otimes> d1)"
proof -
  have d1d2: "{d1,d2} \<subseteq> { d . \<exists> p q . (p \<noteq> q) \<and> onLine p l \<and> onLine q l \<and> (d = (q \<ominus> p)) }"
    using assms(1) by auto
  have d1: "\<exists> p1 q1 . (p1 \<noteq> q1) \<and> (onLine p1 l) \<and> (onLine q1 l) \<and> (d1 = (q1 \<ominus> p1))"
    using d1d2 by auto
  then obtain p1 q1 
    where pq1: "(p1 \<noteq> q1) \<and> (onLine p1 l) \<and> (onLine q1 l) \<and> (d1 = (q1 \<ominus> p1))"
    by blast
  hence l1: "l = lineJoining p1 q1" using lemLineAndPoints[of "p1" "q1" "l"] by auto

  have d2: "\<exists> p2 q2 . (p2 \<noteq> q2) \<and> (onLine p2 l) \<and> (onLine q2 l) \<and> (d2 = (q2 \<ominus> p2))"
    using d1d2 by auto
  then obtain p2 q2 
    where pq2: "(p2 \<noteq> q2) \<and> (onLine p2 l) \<and> (onLine q2 l) \<and> (d2 = (q2 \<ominus> p2))"
    by blast

  hence "(p2 \<in> lineJoining p1 q1) \<and> (q2 \<in> lineJoining p1 q1)" using l1 by blast
  then obtain ap aq 
    where apaq: "(p2 = (p1 \<oplus> (ap\<otimes>(q1\<ominus>p1)))) \<and> ((q2 = (p1 \<oplus> (aq\<otimes>(q1\<ominus>p1)))))"
    by blast

  define diff where diff: "diff = aq - ap"
  hence diffnz: "diff \<noteq> 0" using apaq pq2 by auto

  have "d2 = (q2 \<ominus> p2)" using pq2 by simp
  also have "... = ((p1 \<oplus> (aq\<otimes>(q1\<ominus>p1))) \<ominus> (p1 \<oplus> (ap\<otimes>(q1\<ominus>p1))))" using apaq by force
  also have "... = ((aq\<otimes>(q1\<ominus>p1)) \<ominus> (ap\<otimes>(q1\<ominus>p1)))" by auto
  also have "... = ((aq - ap) \<otimes> d1)" 
    using pq1 lemScaleLeftDiffDistrib[ of "aq" "ap" "d1"] by auto
  finally have "(d2 = (diff \<otimes> d1)) \<and> (diff \<noteq> 0)" using diff diffnz by auto

  thus ?thesis by auto
qed


lemma lemLineDeterminedByPointAndDrtn:
  assumes "(x \<noteq> p) \<and> (p \<in> l1) \<and> (onLine x l1) \<and> (onLine x l2)"
and       "drtn l1 = drtn l2"
shows     "l1 = l2"
proof - 
  define d1 where d1: "d1 = drtn l1"
  define d2 where d2: "d2 = drtn l2"
  hence dd: "d1 = d2" using assms(2) d1 by auto

  define px where px: "px = (p \<ominus> x)"

  have l1: "(x \<noteq> p) \<and> (onLine p l1) \<and> (onLine x l1)" using assms(1) by auto
  hence "\<exists> p q . (p \<noteq> q) \<and> onLine p l1 \<and> onLine q l1 \<and> (px = (q \<ominus> p))" using px by blast
  hence "px \<in> { d . \<exists> p q . (p \<noteq> q) \<and> onLine p l1 \<and> onLine q l1 \<and> (d = (q \<ominus> p)) }" 
    by blast
  hence "px \<in> d1" using d1 subst[of "d1" "drtn l1" "\<lambda>s. px \<in> s"] by auto
  hence "px \<in> d2" using dd by simp
  hence pxonl2: "px \<in> drtn l2" using d2 by simp
  hence "\<exists> u v . (u \<noteq> v) \<and> onLine u l2 \<and> onLine v l2 \<and> (px = (v \<ominus> u))" by auto
  then obtain u v where uv: "(u \<noteq> v) \<and> onLine u l2 \<and> onLine v l2 \<and> (px = (v \<ominus> u))" by blast

  hence "(x \<noteq> u) \<or> (x \<noteq> v)" by blast
  then obtain w where w: "((w = u) \<or> (w = v)) \<and> (x \<noteq> w)" by blast
  hence xw: "(x \<noteq> w) \<and> (onLine x l2) \<and> (onLine w l2)" using uv assms(1) by blast
  hence l2: "l2 = lineJoining x w" using lemLineAndPoints[of "x" "w" "l2"] by auto
  hence "(w \<ominus> x) \<in> drtn l2 \<and> px \<in> drtn l2" using xw pxonl2 by auto
  then obtain a where a: "(a \<noteq> 0) \<and>  (p \<ominus> x) = (a \<otimes> (w \<ominus> x))" 
    using lemDrtn[of "w\<ominus>x" "p\<ominus>x" "l2"] px xw pxonl2 by blast
  hence "p = (x \<oplus> (a \<otimes> (w \<ominus> x)))" by (auto simp add: field_simps)
  hence "onLine p (lineJoining x w)" by blast

  hence l2lj: "l2 = lineJoining x p" 
    using lemLineAndPoints[of "x" "p" "l2"] assms(1) l2 xw
    by auto

  have l1lj: "l1 = lineJoining x p"
    using lemLineAndPoints[of "x" "p" "l1"] assms(1)
    by auto

  thus ?thesis using l2lj by blast
qed

end (* of class Points *)

end (* of theory Points *)
