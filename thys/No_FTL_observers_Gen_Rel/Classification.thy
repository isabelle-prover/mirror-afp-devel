(*
  Classification.thy
  Author: Mike Stannett
  Date: Jan 2023
*)

section \<open> Classification \<close>

text \<open>This theory explains how to establish whether a point lies inside,
on or outside a cone.\<close>


theory Classification
  imports Cones Quadratics CauchySchwarz
begin


text \<open> We want to establish where a point lies in relation to a cone, and will
later show that this relationship is preserved under relevant affine 
transformations. We therefore need a classification scheme that relies on purely affine
concepts. To do this we consider lines that can be drawn through the point,
and ask how many points lie in the intersection of such a line and the cone.\<close>

class Classification = Cones + Quadratics + CauchySchwarz
begin


(* A point is the vertex of the cone *)
abbreviation vertex :: "'a Point \<Rightarrow> 'a Point \<Rightarrow> bool"
  where "vertex x p \<equiv> (x = p)"

(* A point is strictly inside (regularConeSet x) *)
abbreviation insideRegularCone :: "'a Point \<Rightarrow> 'a Point \<Rightarrow> bool"
  where "insideRegularCone x p \<equiv> 
        (slopeFinite x p) \<and> (\<exists> v \<in> lineVelocity (lineJoining x p) . sNorm2 v < 1)"


(* A point is strictly outside (regularConeSet x) *)
abbreviation outsideRegularCone :: "'a Point \<Rightarrow> 'a Point \<Rightarrow> bool"
  where "outsideRegularCone x p \<equiv> 
        (x \<noteq> p) \<and> 
         ((slopeInfinite x p) \<or> (\<exists> v \<in> lineVelocity (lineJoining x p) . sNorm2 v > 1))"


(* A point is part of (regularConeSet x) *)
abbreviation onRegularCone :: "'a Point \<Rightarrow> 'a Point \<Rightarrow> bool"
  where "onRegularCone x p \<equiv> (x = p) \<or> (\<exists> v \<in> lineVelocity (lineJoining x p) . sNorm2 v = 1)"



(* CLASSIFICATION LEMMAS *)



lemma lemDrtnLineJoining:
  assumes "l = lineJoining x p"
  and     "x \<noteq> p"
  shows   "(p \<ominus> x) \<in> drtn l"
proof -
  define d where d: "d = (p \<ominus> x)"
  have lprops: "onLine x l \<and> onLine p l"
    using assms(1) lemLineJoiningContainsEndPoints by blast
  hence "\<exists> x p . (x \<noteq> p) \<and> (onLine x l) \<and> (onLine p l) \<and> (d = (p \<ominus> x))"
      using assms(2) d by blast
  thus ?thesis using d by auto
qed


lemma lemVelocityLineJoining:
  assumes "l = lineJoining x p"
    and   "v = velocityJoining origin (p \<ominus> x)"
and       "x \<noteq> p"
  shows   "v \<in> lineVelocity l"
proof -
  define d where d: "d = (p \<ominus> x)"
  hence "d \<in> drtn l" using assms lemDrtnLineJoining by auto
  hence "\<exists> d \<in> drtn l . v = velocityJoining origin d" using assms d by blast
  thus ?thesis by auto
qed


lemma lemSlopeLineJoining:
  assumes "l = lineJoining p q"
and       "p \<noteq> q"
  shows "lineSlopeFinite l \<longleftrightarrow> slopeFinite p q" 
proof -
  have pql: "onLine p l \<and> onLine q l" 
    using assms(1) lemLineJoiningContainsEndPoints by auto

  have l2r: "lineSlopeFinite l \<longrightarrow> slopeFinite p q"
  proof -
    { assume "lineSlopeFinite l"
      then obtain x y 
        where xy: "(onLine x l) \<and> (onLine y l)  \<and> (x \<noteq> y) \<and> (slopeFinite x y)" by blast
      hence lxy: "l = lineJoining x y" using lemLineAndPoints[of "x" "y" "l"] by auto
  
      define tdiff where tdiff: "tdiff = tval y - tval x"
      hence tdnot0: "tdiff \<noteq> 0" using xy by auto
  
      obtain a where a: "p = (x \<oplus> (a \<otimes> (y\<ominus>x)))" using pql lxy by auto
      hence tvalp: "tval p = tval x + a*(tval y - tval x)" by simp
  
      obtain b where b: "q = (x \<oplus> (b \<otimes> (y\<ominus>x)))" using pql lxy by auto
      hence tvalq: "tval q = tval x + b*(tval y - tval x)" by simp
  
      have anotb: "b - a \<noteq> 0" using a b assms(2) by auto
      
      have "tval q - tval p = (b - a)*tdiff" 
        using tdiff tvalp tvalq 
        by (simp add: local.left_diff_distrib')
      hence "slopeFinite p q" using anotb tdnot0 
        by (metis local.diff_self local.divisors_zero)
    }
    thus ?thesis by auto
  qed

  have r2l: "slopeFinite p q \<longrightarrow> lineSlopeFinite l" using pql assms(2) by blast
  thus ?thesis using l2r by blast
qed



lemma lemVelocityJoiningUsingPoints:
  assumes "p \<noteq> q"
  shows "velocityJoining p q = velocityJoining origin (q\<ominus>p)"
proof -
  define t1 where t1: "t1 = tval p - tval q"
  define t2 where t2: "t2 = tval origin - tval (q\<ominus>p)"
  define v1 where v1: "v1 = (p\<ominus>q)"
  define v2 where v2: "v2 = (origin\<ominus>(q\<ominus>p))"

  have ts: "t1 = t2" using t1 t2 by simp

  { assume "slopeFinite p q"
    hence "(tval origin) - (tval (q\<ominus>p)) \<noteq> 0" by simp
    hence sf2: "slopeFinite origin (q\<ominus>p)" using diff_self by metis
    hence "sloper p q = sloper origin (q\<ominus>p)" using t2 v2 sloper.simps
      by auto
    hence ?thesis by auto
  }
  hence sf: "slopeFinite p q \<longrightarrow> ?thesis" by auto
  { assume hyp: "\<not> (slopeFinite p q)"
    hence "\<not> (slopeFinite origin (q\<ominus>p))" using t1 t2 ts by simp
    hence "sloper p q = sloper origin (q\<ominus>p)" using hyp by simp
    hence ?thesis by auto
  }
  thus ?thesis using sf by blast
qed


lemma lemLineVelocityNonZeroImpliesFinite:
  assumes "u \<in> lineVelocity l"
and       "sNorm2 u \<noteq> 0"
shows "lineSlopeFinite l"
proof -
  have "u \<in> { u . \<exists> d \<in> drtn l . u = velocityJoining origin d }" using assms(1) by auto
  then obtain d where d: "d \<in> drtn l \<and> u = velocityJoining origin d" by blast
  hence "d \<in> { d . \<exists> p q . (p \<noteq> q) \<and> (onLine p l) \<and> (onLine q l) \<and> (d = (q \<ominus> p)) }"
    by auto
  then obtain p q where pq: "(p \<noteq> q) \<and> (onLine p l) \<and> (onLine q l) \<and> (d = (q \<ominus> p))"
    by blast

  hence upq: "u = velocityJoining p q" using lemVelocityJoiningUsingPoints d by auto

  { assume "slopeInfinite p q"
    hence "sloper p q = origin" by simp
    hence "u = sOrigin" using upq by simp
    hence "False" using assms(2) by auto
  }
  hence "slopeFinite p q" by auto
  thus ?thesis using pq by blast
qed


lemma lemLineVelocityUsingPoints:
  assumes "slopeFinite p q"
and       "onLine p l \<and> onLine q l"
shows     "lineVelocity l = { velocityJoining p q }"
proof -
  define v where v: "v = velocityJoining p q"
  hence v': "v = velocityJoining origin (q\<ominus>p)" 
    using lemVelocityJoiningUsingPoints[of "p" "q"] assms(1) by blast

  have pnotq: "p \<noteq> q" using assms(1) by auto
  hence l: "l = lineJoining p q" using lemLineAndPoints[of "p" "q" "l"] assms
    by auto
  hence vinlv: "v \<in> lineVelocity l" 
    using lemVelocityLineJoining[of "l" "p" "q" "v"] v' assms by blast
  hence r2l: "{v} \<subseteq> lineVelocity l" by blast
  
  { fix u assume u: "u \<in> lineVelocity l"
    hence "u = v" 
      using vinlv pnotq assms lemFiniteLineVelocityUnique[of "u" "l" "v"] by blast
  }
  hence "lineVelocity l \<subseteq> {v}" by blast

  thus ?thesis using r2l v by blast
qed


lemma lemSNorm2VelocityJoining:
  assumes "slopeFinite x p"
and       "v = velocityJoining x p"
  shows   "sqr (tval p - tval x) * sNorm2 v = sNorm2 (sComponent (p\<ominus>x))"
proof -
  have "sloper x p = ((1 / (tval x - tval p)) \<otimes> (x \<ominus> p))" using assms(1) by auto
  hence "v = ((1/(tval x - tval p))\<otimes>s (sComponent(x \<ominus> p)))" using assms(2) by simp
  hence "sNorm2 v = sqr (1/ (tval x - tval p)) * sNorm2 (sComponent (x\<ominus>p))"
    using lemSNorm2OfScaled assms(1) by blast
  also have "\<dots> =  sqr (1/ (tval p - tval x)) * sNorm2 (sComponent (p\<ominus>x))"
    using lemSSep2Symmetry assms(1) lemSqrDiffSymmetrical by simp
  finally show ?thesis using assms(1) by simp
qed
    
    

lemma lemOrthogalSpaceVectorExists:
  shows   "\<exists> w . (w \<noteq> sOrigin) \<and> (w \<odot>s v) = 0"
proof -
  obtain x y z where xyz: "v = mkSpace x y z" using Space.cases by blast
  define w where w: "w = (if x = 0 then (mkSpace 1 0 0)
                                     else (mkSpace (y/x) (-1) 0))"

  have wnot0: "(w \<noteq> sOrigin)" using w by simp

  moreover have orth: "(w \<odot>s v) = 0"
  proof -
    { assume x0: "x = 0"
      hence "w = mkSpace 1 0 0" using w by simp
      hence "(w \<odot>s v) = 0" using x0 xyz by simp
    }
    hence case0: "x = 0 \<longrightarrow> ?thesis" by blast
    { assume xnot0: "x \<noteq> 0"
      hence "w = mkSpace (y/x) (-1) 0" using w by simp
      hence "(w \<odot>s v) = 0" using xnot0 xyz by simp
    }
    hence "x \<noteq> 0 \<longrightarrow> ?thesis" by blast
    thus ?thesis using case0 by blast
  qed
  ultimately show ?thesis by force
qed


lemma lemNonParallelVectorsExist:
  shows "\<exists> w . ((w \<noteq> origin) \<and> (tval v = tval w)) \<and> (\<not> (\<exists> \<alpha> . (\<alpha> \<noteq> 0) \<and> v = (\<alpha> \<otimes> w)))"
proof -
  have cases: "xval v = 0 \<or> xval v \<noteq> 0" by auto
  { assume case1: "xval v = 0"

    define diff where diff: "diff = (if ((v \<oplus> xUnit) = origin) then (2\<otimes>xUnit) else xUnit)"
    define w where w: "w = (v \<oplus> diff)"
    hence w1: "(xval w) = 1" using case1 diff by auto 

    { assume "\<exists> \<alpha> . (\<alpha> \<noteq> 0) \<and> v = (\<alpha> \<otimes> w)"
      then obtain a where a: "(a \<noteq> 0) \<and> v = (a \<otimes> w)" by auto
      hence "xval v = a * xval w" by simp
      hence "0 = a * 1" using case1 w1 by auto
      hence "a = 0" by auto
      hence "False" using a by blast
    }
    hence "(\<not> (\<exists> \<alpha> . (\<alpha> \<noteq> 0) \<and> v = (\<alpha> \<otimes> w)))" by auto
    moreover have "tval v = tval w" using w diff by auto
    ultimately have "(w \<noteq> origin) \<and> (tval v = tval w) \<and> (\<not> (\<exists> \<alpha> . (\<alpha> \<noteq> 0) \<and> v = (\<alpha> \<otimes> w)))" 
      using w1 by auto
  }
  hence lhs: "xval v = 0 \<longrightarrow> ?thesis"  by blast

  { assume case2: "xval v \<noteq> 0"
    define w where w: "w = (v \<oplus> yUnit)"
    hence wx: "xval w = xval v" using case2 by auto
    have  wy: "yval w = yval v + 1" using w by auto

    { assume "\<exists> \<alpha> . (\<alpha> \<noteq> 0) \<and> v = (\<alpha> \<otimes> w)"
      then obtain a where a: "(a \<noteq> 0) \<and> v = (a \<otimes> w)" by auto
      hence xv: "xval v = a * xval w" by simp
      hence a1: "xval v = a * xval v" using wx by simp
      hence "a = 1" using case2 by simp
      hence "yval v = yval w" using a by auto
      hence "False" using wy by auto
    }
    hence "(\<not> (\<exists> \<alpha> . (\<alpha> \<noteq> 0) \<and> v = (\<alpha> \<otimes> w)))" by auto
    moreover have "tval v = tval w" using w by auto
    moreover have "xval w \<noteq> 0" using w case2 by auto
    ultimately have "(w \<noteq> origin) \<and>(tval v = tval w) \<and> (\<not> (\<exists> \<alpha> . (\<alpha> \<noteq> 0) \<and> v = (\<alpha> \<otimes> w)))" 
      by auto
  }
  hence rhs: "xval v \<noteq> 0 \<longrightarrow> ?thesis" by blast

  thus ?thesis using cases lhs by auto
qed


lemma lemConeContainsVertex:
  shows "regularCone x x" 
proof -
  define d where d: "d = (tUnit \<oplus> xUnit)"
  define p where p: "p = (d \<oplus> x)"
  define l where l: "l = lineJoining x p"
  define v where v: "v = velocityJoining origin d"

  have xnotp: "x \<noteq> p" 
  proof -
    { assume "x = p"
      hence "(d \<oplus> x) = x" using p by auto
      hence "d = origin" using add_cancel_left_left 
        by (metis dot.simps lemDotSumRight lemNullImpliesOrigin)
      hence "False" using d by auto
    }
    thus ?thesis by auto
  qed
  moreover have "d = (p \<ominus> x)" using p by auto
  ultimately have vel: "v \<in> lineVelocity l" 
    using l v d lemVelocityLineJoining[of "l" "x" "p" "v"] by blast

  have lprops: "onLine x l \<and> onLine p l"
    using xnotp l lemLineAndPoints[of "x" "p" "l"] by auto

  have slope: "sNorm2 v = 1"
  proof -
    define sx where sx: "sx = \<lparr> svalx = 1, svaly = 0, svalz = 0 \<rparr>"
    have "slopeFinite origin d" using d by auto
    hence "sloper origin d = ((1 / ((tval origin) - (tval d))) \<otimes> (origin \<ominus> d))" by simp
    moreover have "\<dots> = ((-1) \<otimes> (origin \<ominus> d))" using d by auto
    moreover have "\<dots> = d" by auto
    ultimately have "sloper origin d = d" by simp
    hence "velocityJoining origin d = sComponent d" by simp
    hence "v = sx" using v d sx by auto 
    thus ?thesis using sx by auto
  qed

  hence "v \<in> lineVelocity l \<and> sNorm2 v = 1" using vel by auto
  hence "\<exists> l . (onLine x l) \<and>(\<exists> v \<in> lineVelocity l . sNorm2 v = 1)"
    using lprops by blast
  thus ?thesis by blast
qed


lemma lemConesExist:
  shows "regularConeSet x \<noteq> {}"
proof -
  have "x \<in> regularConeSet x" using lemConeContainsVertex by auto
  thus ?thesis by blast
qed


lemma lemRegularCone: 
  shows   "((x = p) \<or> onRegularCone x p) \<longleftrightarrow> regularCone x p"
proof -
  define l where l: "l = lineJoining x p"
  hence lprops: "onLine p l \<and> onLine x l" 
    using lemLineJoiningContainsEndPoints by auto

  define LHS where LHS: "LHS = ((x = p) \<or> (onRegularCone x p))"
  define RHS where RHS: "RHS = (regularCone x p)"

  have "LHS \<longrightarrow> RHS" 
  proof -
    { assume "x = p"
      hence ?thesis using RHS lemConeContainsVertex by auto
    }
    hence case1: "x = p \<longrightarrow> regularCone x p" using LHS RHS by auto
    { assume "x\<noteq>p \<and> onRegularCone x p"
      then obtain v where v: "v \<in> lineVelocity l \<and> sNorm2 v = 1" using l by blast
      hence "\<exists> l . (onLine p l) \<and> (onLine x l) \<and> (\<exists> v \<in> lineVelocity l . sNorm2 v = 1)" 
        using lprops by blast
    }
    thus ?thesis using case1 LHS RHS by blast
  qed

  moreover have "RHS \<longrightarrow> LHS"
  proof -
    { assume rhs: "RHS"
      have cases: "x = p \<or> x \<noteq> p" by auto
      have case1: "x = p \<longrightarrow> (x = p \<or> onRegularCone x p)" by auto

      { assume xnotp: "x \<noteq> p"
        then obtain l1 where 
          l1: "(onLine x l1) \<and> (onLine p l1) 
                         \<and> (\<exists> v \<in> lineVelocity l1 . sNorm2 v = 1)" 
          using rhs RHS by blast
        hence "l1 = l"  using xnotp l l1 lemLineAndPoints[of "x" "p" "l1"] by auto
        hence "\<exists> v \<in> lineVelocity l . sNorm2 v = 1" using l1 by blast
        hence "onRegularCone x p" using l by blast
        hence "(x = p \<or> onRegularCone x p)" by blast
      }
      hence case2: "x \<noteq> p \<longrightarrow> LHS" 
        using l lprops LHS by blast

      hence "(x = p \<or> onRegularCone x p)" using cases case1 LHS by blast
    }
    thus ?thesis using LHS RHS by auto
  qed

  ultimately have "LHS \<longleftrightarrow> RHS" by blast
  thus ?thesis using LHS RHS by fastforce
qed


lemma lemSlopeInfiniteImpliesOutside:
  assumes "x \<noteq> p"
and       "slopeInfinite x p"
shows     "\<exists> l p' . (p' \<noteq> p) \<and> onLine p' l \<and> onLine p l
                                          \<and> (l \<inter> regularConeSet x = {})"
proof - 
  define dxp where dxp: "dxp = (x \<ominus> p)"
  hence "x = (dxp \<oplus> p)" by simp
  hence xdxp: "x = (p \<oplus> dxp)" using add_commute by blast

  have xp: "tval x = tval p" using assms(2) by blast
  hence tvaldxp: "tval dxp = 0" using dxp by simp

  obtain dnew where 
    dnew: "(dnew \<noteq> origin) \<and> (tval dnew = tval dxp) \<and> \<not>(\<exists> \<alpha>. \<alpha> \<noteq> 0 \<and> dxp = (\<alpha> \<otimes> dnew))"
    using lemNonParallelVectorsExist[of "dxp"] 
    by auto
  hence tvaldnew: "tval dnew = 0" using tvaldxp by simp

  define w where w: "w = (p \<oplus> dnew)"
  hence wmp: "(w \<ominus> p) = dnew" by simp

  have wx: "tval w = tval x"
  proof -
    have "tval dnew = tval x - tval p" using dnew dxp by auto
    hence "tval w = tval p + (tval x - tval p)" using w by auto
    thus ?thesis using add_commute diff_add_cancel by auto
  qed

  define lw where lw: "lw = lineJoining w p"

  have xNotOnLw:  "\<not> (x \<in> lw)"
  proof -
    { assume "x \<in> lw"
      then obtain a where a: "x = (w \<oplus> (a \<otimes> (p\<ominus>w)))" using lw by auto
      hence "(p \<oplus> dxp) = ((p \<oplus> dnew) \<oplus> (a \<otimes> (p\<ominus>w)))" using xdxp w by auto
      hence "dxp = (dnew \<oplus> (a \<otimes> (p\<ominus>w)))" using add_assoc by auto
      moreover have "(p\<ominus>w) = ((-1) \<otimes> (w\<ominus>p))"  by simp
      hence "(a \<otimes> (p\<ominus>w)) = ((-a) \<otimes> (w\<ominus>p))" using lemScaleAssoc[of "a" "-1" "w\<ominus>p"] by simp
      ultimately have "dxp = (dnew \<oplus> ((-a) \<otimes> (w\<ominus>p)))" by auto
      hence "dxp = ((1 \<otimes> dnew) \<oplus> ((-a) \<otimes> dnew))" using wmp by auto
      hence "dxp = ((1-a) \<otimes> dnew)" using left_diff_distrib' by fastforce
      hence "(1-a) = 0" using dnew by blast
      hence "a = 1" by simp
      hence "x = (w \<oplus> (p \<ominus> w))" using a by auto
      hence "x = p" by (simp add: local.add_diff_eq)
    }
    thus ?thesis using assms(1) by auto
  qed

  have "dnew \<noteq> origin" using dnew by auto
  hence wNotp: "w \<noteq> p" using w diff_self wmp by blast
  hence pwOnLw: "onLine p lw \<and> onLine w lw" 
    using lw lemLineAndPoints[of "w" "p" "lw"] by auto

  hence target1: "w \<noteq> p \<and> onLine w lw \<and> onLine p lw" using wNotp by auto

  define MeetW where MeetW: "MeetW = lw \<inter> regularConeSet x"
  { assume nonempty: "\<not> (MeetW = {})"
    then obtain z where z: "z \<in> MeetW" by blast

    have zx: "tval z = tval x"
    proof -
      have "z \<in> lineJoining w p" using z MeetW lw by auto
      then obtain a where a: "z = (w \<oplus> (a \<otimes> (p\<ominus>w)))" by blast
  
      have "tval (p\<ominus>w) = 0" using w tvaldnew by auto
      hence "tval z = tval w" using a by auto
      thus ?thesis using wx by auto
    qed

    have "regularCone x z" using z MeetW by auto
    then obtain l1 where l1: "(onLine z l1) \<and> (onLine x l1) 
                                     \<and> (\<exists> v \<in> lineVelocity l1 . sNorm2 v = 1)" by blast
    then obtain v where v: "v \<in> lineVelocity l1 \<and> sNorm2 v = 1" by blast
    hence "\<exists> d \<in> drtn l1 . v = velocityJoining origin d \<and> sNorm2 v = 1" by auto
    then obtain d1 where d1: "d1 \<in> drtn l1 \<and>  v = velocityJoining origin d1 \<and> sNorm2 v = 1" 
      by blast
    hence "v \<noteq> sOrigin" by fastforce
    hence "velocityJoining origin d1 \<noteq> sOrigin" using d1 by auto
    hence drtnNotZero: "tval d1 \<noteq> 0" by auto

    (* have shown drtn is nonzero, now show it must be zero *)
    define d2 where d2: "d2 = (z \<ominus> x)"
    hence tvald2: "tval d2 = 0" using zx by simp
    have zNotz: "x \<noteq> z" using xNotOnLw z MeetW by blast
    hence "(x \<noteq> z) \<and> (onLine z l1) \<and> (onLine x l1) \<and> (d2 = (z \<ominus> x))" 
      using l1 d2 by auto
    hence "\<exists> x z . (x \<noteq> z) \<and> (onLine x l1) \<and> (onLine z l1) \<and> (d2 = (z \<ominus> x))" by blast
    hence "d2 \<in> drtn l1" by auto

    then obtain b where b: "b \<noteq> 0 \<and> d1 = (b \<otimes> d2)" 
      using lemDrtn[of "d2" "d1" "l1"] d1 by blast
    hence "tval d1 = b * tval d2" by simp
    hence "tval d1 = 0" using tvald2 by simp
  
    hence "False" using drtnNotZero by auto
  }
  hence "MeetW = {}" by auto

  hence "(w \<noteq> p) \<and> onLine w lw \<and> onLine p lw \<and> (lw \<inter> regularConeSet x = {})" 
    using target1 MeetW by auto
  thus ?thesis by blast
qed




lemma lemClassification:
  shows "(insideRegularCone x p) \<or> (vertex x p \<or> outsideRegularCone x p \<or> onRegularCone x p)"
proof -
  define l where l: "l = lineJoining x p"
  define v where v: "v = velocityJoining origin (p\<ominus>x)"
  { assume xnotp: "x \<noteq> p"
    hence vel: "v \<in> lineVelocity l" 
      using l v lemVelocityLineJoining[of "l" "x" "p" "v"] by auto
    have "(sNorm2 v < 1) \<or> (sNorm2 v > 1) \<or> (sNorm2 v = 1)" by auto
    hence ?thesis using xnotp l v vel by blast
  }
  hence "x \<noteq> p \<longrightarrow> ?thesis" by auto
  moreover have "x = p \<longrightarrow> ?thesis" by auto
  ultimately show ?thesis by blast
qed

lemma lemQuadCoordinates:
  assumes "p = (B \<oplus> (\<alpha> \<otimes> D))"
and "a = mNorm2 D"
and "b = 2*(tval (B\<ominus>x))*(tval D) - 2*((sComponent D) \<odot>s (sComponent (B\<ominus>x)))"
and "c = mNorm2 (B\<ominus>x)"
shows "sqr (tval (p\<ominus>x)) - sNorm2 (sComponent (p\<ominus>x)) = a*(sqr \<alpha>) + b*\<alpha> + c"
proof -
  define X where X: "X = (B\<ominus>x)"
  have pmx: "(p \<ominus> x) = (X \<oplus> (\<alpha> \<otimes> D))" using diff_add_eq assms X by simp

  (* calculate time and space components *)
  have pmxt: "tval p - tval x = tval X + \<alpha>*tval D" using pmx by simp
  have pmxs: "sComponent (p\<ominus>x) = ((sComponent X) \<oplus>s (\<alpha> \<otimes>s (sComponent D)))"
    using pmx by simp

  (* calculate diff of squared components *)
  have tsqr: "sqr (tval (p\<ominus>x)) 
              = sqr (tval X) + \<alpha>*(2*(tval X)*(tval D)) + (sqr \<alpha>)*(sqr (tval D))" 
    using pmxt lemSqrSum[of "tval X" "\<alpha>*(tval D)"] mult_assoc mult_commute by auto

  have ssqr: "sNorm2 (sComponent (p\<ominus>x))
                 = (sNorm2 (sComponent X)) 
                       + \<alpha>*(2*((sComponent X) \<odot>s (sComponent D)))
                            + (sqr \<alpha>)*(sNorm2 (sComponent D))"
    using lemSDotScaleRight lemSNorm2OfScaled lemSNorm2OfSum mult.left_commute pmxs 
    by presburger

  hence "sqr (tval (p\<ominus>x)) - sNorm2 (sComponent (p\<ominus>x))        
      = ( sqr (tval X) + \<alpha>*(2*(tval X)*(tval D)) + (sqr \<alpha>)*(sqr (tval D)) )
      - ((sNorm2 (sComponent X)) 
                       + \<alpha>*(2*((sComponent X) \<odot>s (sComponent D)))
                            + (sqr \<alpha>)*(sNorm2 (sComponent D)) )"
    using tsqr by auto
  also have "\<dots> 
      = ( sqr (tval X) + \<alpha>*(2*(tval X)*(tval D)) )
        + ( (sqr \<alpha>)*(sqr (tval D)) - (sqr \<alpha>)*(sNorm2 (sComponent D)) )
      - ((sNorm2 (sComponent X)) 
                       + \<alpha>*(2*((sComponent X) \<odot>s (sComponent D))))"
    using diff_add_eq add_diff_eq diff_add_eq_diff_diff_swap by fastforce
  also have "\<dots>
      = sqr (tval X) + 
          ( \<alpha>*(2*(tval X)*(tval D))  - \<alpha>*(2*((sComponent X) \<odot>s (sComponent D))) )
        + ( (sqr \<alpha>)*(sqr (tval D)) - (sqr \<alpha>)*(sNorm2 (sComponent D)) )
      - (sNorm2 (sComponent X))"
    using diff_add_eq add_diff_eq diff_add_eq_diff_diff_swap add_commute by simp
  also have "\<dots>        
      = sqr (tval X) + \<alpha>*b  + (sqr \<alpha>)* a  - (sNorm2 (sComponent X))"
    using right_diff_distrib' assms(2) assms(3) X lemSDotCommute by presburger
  also have "\<dots> = c + \<alpha>*b + (sqr \<alpha>)*a"
    using right_diff_distrib' assms(4) X add_commute add_diff_eq by simp

  finally show ?thesis using add_commute mult_commute add_assoc by auto
qed


lemma lemConeCoordinates:
shows "(onRegularCone x p \<longleftrightarrow> sqr (tval p - tval x) = sNorm2 (sComponent (p\<ominus>x)))
      \<and>  (insideRegularCone x p \<longleftrightarrow> sqr (tval p - tval x) > sNorm2 (sComponent (p\<ominus>x)))
      \<and>  (outsideRegularCone x p \<longleftrightarrow> sqr (tval p - tval x) < sNorm2 (sComponent (p\<ominus>x)))"
proof -
  define tdiff where tdiff: "tdiff = tval p - tval x"
  define sdiff where sdiff: "sdiff = sComponent (p\<ominus>x)"
   
  have cases: "x = p \<or> x \<noteq> p" by simp
  have case1: "x = p \<longrightarrow> ?thesis"     
  proof - 
    { assume xisp: "x = p"
      hence on: "onRegularCone x p" by auto
      moreover have  both0: "sqr tdiff = 0 \<and> sNorm2 sdiff = 0" 
        using xisp tdiff sdiff by simp
      ultimately have "onRegularCone x p \<longleftrightarrow> sqr tdiff = sNorm2 sdiff" by simp

      moreover have "outsideRegularCone x p \<longleftrightarrow> sqr tdiff > sNorm2 sdiff" 
      proof -
        have "\<not>outsideRegularCone x p" using xisp by simp
        moreover have "\<not> (sqr tdiff > sNorm2 sdiff)" using both0 by simp
        ultimately show ?thesis by blast
      qed
         
      moreover have "insideRegularCone x p \<longleftrightarrow> sqr tdiff < sNorm2 sdiff" 
      proof -
        have "\<not>insideRegularCone x p" using xisp by simp
        moreover have "\<not> (sqr tdiff < sNorm2 sdiff)" using both0 by simp
        ultimately show ?thesis by blast
      qed

      ultimately have ?thesis using tdiff sdiff by blast
    }
    thus ?thesis by blast
  qed
         
    
  have case2: "x \<noteq> p \<longrightarrow> ?thesis"
  proof -
    define l where l: "l = lineJoining x p"
    hence onl: "onLine x l \<and> onLine p l" using lemLineJoiningContainsEndPoints by blast
    define v where v: "v = velocityJoining x p"
        
    { assume xnotp: "x \<noteq> p"

      { assume sinf: "slopeInfinite x p"

        hence t0: "sqr tdiff = 0" using tdiff by simp
        hence "sdiff \<noteq> sOrigin" using xnotp sdiff tdiff by auto
        hence "sNorm2 sdiff \<noteq> 0" using lemSpatialNullImpliesSpatialOrigin by blast
        moreover have "sNorm2 sdiff \<ge> 0" by simp
        ultimately have "sNorm2 sdiff > 0" using lemGENZGT by auto

        hence eqn: "sqr tdiff < sNorm2 sdiff" using t0 by auto
        have out: "outsideRegularCone x p" using sinf xnotp by blast

        have notin: "\<not> insideRegularCone x p" using sinf by blast
        have notgt: "\<not> (sqr tdiff > sNorm2 sdiff)" using eqn by auto

        have noton: "\<not> onRegularCone x p"
        proof -
          { assume "onRegularCone x p"
            then obtain u where u: "u \<in> lineVelocity l \<and> sNorm2 u = 1" 
              using l xnotp by blast
            hence "slopeFinite x p" 
              using xnotp lemLineVelocityNonZeroImpliesFinite[of "u" "l"]
                    zero_neq_one l
              by fastforce
            hence "False" using sinf by auto
          }
          thus ?thesis by blast
        qed
        have noteq: "\<not> (sqr tdiff = sNorm2 sdiff)" using eqn by auto

        have outs: "(outsideRegularCone x p) \<longleftrightarrow> (sqr tdiff < sNorm2 sdiff)" 
          using out eqn by blast
        have ins: "(insideRegularCone x p) \<longleftrightarrow> (sqr tdiff > sNorm2 sdiff)" 
          using notin notgt by blast
        have ons: "(onRegularCone x p) \<longleftrightarrow> (sqr tdiff = sNorm2 sdiff)" 
          using noton noteq by blast

        hence ?thesis using ins outs ons tdiff sdiff by blast
      }
      hence ifsinf: "slopeInfinite x p \<longrightarrow> ?thesis " by blast


      { assume sf: "slopeFinite x p"
        hence lv: "lineVelocity l = {v}" 
          using lemLineVelocityUsingPoints[of "x" "p" "l"] v onl xnotp by auto
        have formula: "sqr tdiff *(sNorm2 v) = sNorm2 sdiff"
          using lemSNorm2VelocityJoining[of "x" "p" "v"] sf v tdiff sdiff by auto

        { assume "onRegularCone x p"
          hence "(\<exists> v \<in> lineVelocity l . sNorm2 v = 1)" using xnotp l by auto
          then obtain u where u: "u \<in> lineVelocity l \<and> sNorm2 u = 1" by blast
          hence "u = v" using lv by blast
          hence "sNorm2 v = 1" using u by auto
          hence "sqr tdiff = sNorm2 sdiff" using formula by auto
        }
        hence on1: "(onRegularCone x p) \<longrightarrow> (sqr tdiff = sNorm2 sdiff)"  by auto

        { assume "insideRegularCone x p"
          hence "(\<exists> v \<in> lineVelocity l . sNorm2 v < 1)" using xnotp l by auto
          then obtain u where u: "u \<in> lineVelocity l \<and> sNorm2 u < 1" by blast
          hence "u = v" using lv by blast
          hence vlt1: "sNorm2 v < 1" using u by auto

          { assume "sNorm2 v = 0"
            hence v0: "v = sOrigin" using lemSpatialNullImpliesSpatialOrigin by auto
            have "sloper x p = ((1/(tval x - tval p))\<otimes>(x\<ominus>p))" using sf by auto
            hence "v = ((1/(tval x - tval p))\<otimes>s (sComponent (x\<ominus>p)))" using v by simp
            hence "sOrigin = ((1/(tval x - tval p))\<otimes>s (sComponent (x\<ominus>p)))" 
              using v0 by force
            hence "((tval x - tval p) \<otimes>s sOrigin) = sComponent (x\<ominus>p)"
              using lemSScaleAssoc[of "(tval x - tval p)" "1/(tval x - tval p)" 
                                     "(sComponent (x\<ominus>p))"] sf
                    mult_eq_0_iff right_minus_eq by auto
            hence s0: "sComponent (x\<ominus>p) = sOrigin" by auto
            hence pmxs: "sNorm2 sdiff = 0" using sdiff lemSSep2Symmetry by auto
            
            have "tdiff \<noteq> 0" using tdiff xnotp s0 by auto

            hence "sqr tdiff > sNorm2 sdiff" using pmxs lemSquaresPositive by auto
          }
          hence ifv0: "sNorm2 v = 0 \<longrightarrow> sqr tdiff > sNorm2 sdiff" by blast
  
          { assume vne0: "sNorm2 v \<noteq> 0"
            hence "sNorm2 v > 0" using lemGENZGT by auto
            moreover have tpos: "sqr tdiff > 0" 
              using sf lemSquaresPositive tdiff by auto
            ultimately have lpos: "(sqr tdiff)*(sNorm2 v) > 0" by auto
            hence rpos: "sNorm2 sdiff > 0" using formula by auto
  
            hence "(sqr tdiff)*(sNorm2 v) < (sqr tdiff)" using tpos lpos vlt1
              using lemMultPosLT1[of "sqr tdiff" "sNorm2 v"] tpos by auto
            hence "sqr tdiff > sNorm2 sdiff" using formula by auto
          }
          hence "sNorm2 v \<noteq> 0 \<longrightarrow> sqr tdiff > sNorm2 sdiff" by auto
  
          hence "sqr tdiff > sNorm2 sdiff" using ifv0 by blast
        }
        hence in1: "insideRegularCone x p \<longrightarrow> sqr tdiff > sNorm2 sdiff" by auto
  
        { assume out: "outsideRegularCone x p"
          have xnotp:  "(x \<noteq> p)" using out by simp
          have "(\<exists> v \<in> lineVelocity (lineJoining x p) . sNorm2 v > 1)"
            using sf out by blast
          then obtain u where u: "u \<in> lineVelocity (lineJoining x p) \<and> (sNorm2 u > 1)"
            by blast
          hence "u = v" using lv l by blast        
          hence "sNorm2 v > 1" using u by auto
          moreover have "sqr tdiff > 0" using sf tdiff lemSquaresPositive by auto
          ultimately have "(sqr tdiff)*(sNorm2 v) > (sqr tdiff)"
            using local.mult_strict_left_mono by fastforce
          hence "sqr tdiff < sNorm2 sdiff" using formula by auto
        }
        hence out1: "(outsideRegularCone x p) \<longrightarrow> (sqr tdiff < sNorm2 sdiff)"  by auto
  
        (* CONVERSES *)
        have in2: "(sqr tdiff > sNorm2 sdiff) \<longrightarrow> (insideRegularCone x p)"
        proof -
          { assume lhs: "sqr tdiff > sNorm2 sdiff"
            { assume "\<not> insideRegularCone x p"
              hence options: "onRegularCone x p \<or> outsideRegularCone x p" 
                using lemClassification xnotp by blast
  
              { assume "onRegularCone x p"
                hence "sqr tdiff = sNorm2 sdiff" using xnotp on1 by blast
                hence "False" using lhs by auto
              }
              hence notOn: "\<not>onRegularCone x p" by blast
  
              { assume "outsideRegularCone x p"
                hence "sqr tdiff < sNorm2 sdiff" using xnotp out1 by blast
                hence "False" using lhs by auto
              }
              hence notIn: "\<not>outsideRegularCone x p" by blast
  
              hence "False" using notOn options by blast
            }
            hence "insideRegularCone x p" by blast
          }
          thus ?thesis by blast
        qed
  
        have out2: "(sqr tdiff < sNorm2 sdiff) \<longrightarrow> (outsideRegularCone x p)"
        proof -
          { assume lhs: "sqr tdiff < sNorm2 sdiff"
            { assume "\<not> outsideRegularCone x p"
              hence options: "onRegularCone x p \<or> insideRegularCone x p" 
                using lemClassification xnotp by blast
  
              { assume "onRegularCone x p"
                hence "sqr tdiff = sNorm2 sdiff" using xnotp on1 by blast
                hence "False" using lhs by auto
              }
              hence notOn: "\<not>onRegularCone x p" by blast
  
              { assume "insideRegularCone x p"
                hence "sqr tdiff > sNorm2 sdiff" using xnotp in1 by blast
                hence "False" using lhs by auto
              }
              hence notIn: "\<not>insideRegularCone x p" by blast
  
              hence "False" using notOn options by blast
            }
            hence "outsideRegularCone x p" by blast
          }
          thus ?thesis by blast
        qed
  
  
        have on2: "(sqr tdiff = sNorm2 sdiff) \<longrightarrow> (onRegularCone x p)"
        proof -
          { assume lhs: "sqr tdiff = sNorm2 sdiff"
            { assume "\<not> onRegularCone x p"
              hence options: "outsideRegularCone x p \<or> insideRegularCone x p" 
                using lemClassification xnotp by blast
  
              { assume "outsideRegularCone x p"
                hence "sqr tdiff < sNorm2 sdiff" using xnotp out1 by blast
                hence "False" using lhs by auto
              }
              hence notOut: "\<not>outsideRegularCone x p" by blast
  
              { assume "insideRegularCone x p"
                hence "sqr tdiff > sNorm2 sdiff" using xnotp in1 by blast
                hence "False" using lhs by auto
              }
              hence notIn: "\<not>insideRegularCone x p" by blast
  
              hence "False" using notOut options by blast
            }
            hence "onRegularCone x p" by blast
          }
          thus ?thesis by blast
        qed
      
        hence ?thesis using in1 in2 out1 out2 on1 on2 tdiff sdiff by blast
      }
      hence "slopeFinite x p \<longrightarrow> ?thesis" by blast

      hence ?thesis using ifsinf by blast
    }
    thus ?thesis by blast
  qed

  thus ?thesis using cases case1 by blast
qed


lemma lemConeCoordinates1:
  shows "p \<in> regularConeSet x \<longleftrightarrow> norm2 (p\<ominus>x) = 2*sqr (tval p - tval x)" 
proof -
  define tdiff where tdiff: "tdiff = tval p - tval x"
  hence tdiff': "tdiff =  tval (p\<ominus>x)" by simp
  define sdiff where sdiff: "sdiff = (sComponent (p\<ominus>x))"

  have n: "norm2 (p\<ominus>x) = sqr tdiff + sNorm2 sdiff"
    using lemNorm2Decomposition sdiff tdiff' by blast

  have reg: "onRegularCone x p \<longleftrightarrow> sqr tdiff = sNorm2 sdiff"
    using lemConeCoordinates tdiff sdiff by blast

  { assume "p \<in> regularConeSet x"
    hence "onRegularCone x p" using lemRegularCone[of "x" "p"] by auto
    hence "sqr tdiff = sNorm2 sdiff" using reg by blast
    hence "norm2 (p\<ominus>x) = 2*sqr tdiff" using n mult_2 by force
  }
  hence l2r: "p \<in> regularConeSet x \<longrightarrow> norm2 (p\<ominus>x) = 2*sqr tdiff" by auto

  { assume "norm2 (p\<ominus>x) = 2*sqr tdiff"
    hence "sqr tdiff + sNorm2 sdiff = 2*sqr tdiff" using n by auto
    hence "sNorm2 sdiff = sqr tdiff" using mult_2 add_diff_eq by auto
    hence "onRegularCone x p" using reg by auto
    hence "p \<in> regularConeSet x" 
      using lemConeContainsVertex lemRegularCone[of "x" "p"] by blast
  }
  hence "norm2 (p\<ominus>x) = 2*sqr tdiff \<longrightarrow> p \<in> regularConeSet x" by blast
  thus ?thesis using l2r tdiff by blast
qed



lemma lemWhereLineMeetsCone:
  assumes "a = mNorm2 D"
and       "b = 2*(tval (B\<ominus>x))*(tval D) - 2*((sComponent D) \<odot>s (sComponent (B\<ominus>x)))"
and       "c = mNorm2 (B\<ominus>x)"
shows     "qroot a b c \<alpha> \<longleftrightarrow> regularCone x (B \<oplus> (\<alpha>\<otimes>D))"
proof -
  { fix \<alpha> assume \<alpha>: "qroot a b c \<alpha>"
    define p where p: "p = (B \<oplus> (\<alpha>\<otimes>D))"
    hence "mNorm2 (p\<ominus>x) = a*(sqr \<alpha>) + b*\<alpha> + c"
      using lemQuadCoordinates[of "p" "B" "\<alpha>" "D" "a" "b" "x" "c"] assms by auto
    hence "sqr (tval (p\<ominus>x)) - sNorm2 (sComponent (p\<ominus>x)) = 0" using \<alpha> by auto
    hence "onRegularCone x p" using lemConeCoordinates[of "x" "p"] by auto
    hence "regularCone x (B \<oplus> (\<alpha>\<otimes>D))" using lemRegularCone p by blast
  }
  hence l2r: "qroot a b c \<alpha> \<longrightarrow> regularCone x (B \<oplus> (\<alpha>\<otimes>D))" by blast

  { assume reg: "regularCone x (B \<oplus> (\<alpha>\<otimes>D))"
    define p where p: "p = (B \<oplus> (\<alpha>\<otimes>D))"
    hence "onRegularCone x p" using lemRegularCone reg by blast
    hence "sqr (tval (p\<ominus>x)) - sNorm2 (sComponent (p\<ominus>x)) = 0"
      using lemConeCoordinates[of "x" "p"] by auto
    hence "a*(sqr \<alpha>) + b*\<alpha> + c = 0"
      using lemQuadCoordinates[of "p" "B" "\<alpha>" "D" "a" "b" "x" "c"] p assms  
      by auto
    hence "qroot a b c \<alpha>" by auto
  }
  hence "regularCone x (B \<oplus> (\<alpha>\<otimes>D)) \<longrightarrow> qroot a b c \<alpha>" by auto

  thus ?thesis using l2r by blast
qed


lemma lemLineMeetsCone1:
  assumes "\<not> (x \<in> l)"
and       "isLine l"
and       "S = l \<inter> regularConeSet x"
and  l: "l = line B D"
and  X: "X = (B \<ominus> x)"
and  a: "a = mNorm2 D"
and  b: "b = 2*(tval X)*(tval D) - 2*((sComponent D) \<odot>s (sComponent X))"
and  c: "c = mNorm2 X"
shows "(qcase1 a b c \<longrightarrow> S = {B})"
proof -
  { assume hyp1: "qcase1 a b c"

    have impa: "norm2 D = 2*sqr (tval D)"
    proof - 
      have "a = 0" using hyp1 by simp
      hence "sqr (tval D) = sNorm2 (sComponent D)" using a by auto
      hence "onRegularCone origin D" 
        using lemConeCoordinates[of "origin" "D"] by auto
      hence "regularCone origin D" using lemRegularCone by blast
      thus ?thesis using lemConeCoordinates1 by auto
    qed

    have impb: "(D\<odot>X) = 2 * tval X * tval D"
    proof -
      have "2*(tval X)*(tval D) = 2*((sComponent D) \<odot>s (sComponent X))"
        using hyp1 b by auto
      hence "(tval X)*(tval D) = ((sComponent D) \<odot>s (sComponent X))"
        by (simp add: mult_assoc)
      thus ?thesis using mult_2 lemDotDecomposition[of "X" "D"] 
              lemSDotCommute mult_assoc lemDotCommute by metis
    qed

    have impc: "norm2 X = 2*sqr (tval X)"
    proof -
      have "sqr (tval X) = sNorm2 (sComponent X)" using hyp1 c by auto
      hence "onRegularCone x B" using X lemConeCoordinates by auto
      hence "regularCone x B" using lemRegularCone by blast
      thus ?thesis using X lemConeCoordinates1 by auto
    qed

    have allOnCone: "\<forall> \<alpha> . regularCone x (B \<oplus> (\<alpha> \<otimes> D))"
    proof -  
      { fix \<alpha>
        define y where y: "y = (B \<oplus> (\<alpha> \<otimes> D))"
        have "qroot a b c \<alpha>" using hyp1 by simp
        hence "regularCone x y" 
          using lemWhereLineMeetsCone[of "a" "D" "b" "B" "x" "c" "\<alpha>"] using y assms by auto
      }
      thus ?thesis by auto
    qed

    have "tval D = 0"
    proof -
      { assume Dnot0: "tval D \<noteq> 0"
        define \<alpha> where \<alpha>: "\<alpha> = (tval x - tval B)/(tval D)"
        define y where y: "y = (B \<oplus> (\<alpha>\<otimes>D))"
        hence yOnl: "y \<in> l" using l by blast

        hence ty0: "tval y = tval x"
        proof - 
          have "tval y = tval ((B \<oplus> (\<alpha>\<otimes>D)))" using y by auto
          also have "\<dots> = tval B + \<alpha>*(tval D)" by simp
          also have "\<dots> = tval B + (tval x - tval B)/(tval D)*(tval D)" using \<alpha> by simp
          also have "\<dots> = tval B + (tval x - tval B)" using Dnot0 by simp
          finally show ?thesis using add_commute local.diff_add_cancel by auto
        qed

        have "regularCone x y" using y allOnCone by blast
        hence "norm2 (y\<ominus>x) = 2*sqr (tval y - tval x)"
          using lemConeCoordinates1 by auto
        hence "norm2 (y\<ominus>x) = 0" using ty0 by auto
        hence "(y\<ominus>x) = origin" using lemNullImpliesOrigin by blast
        hence "y = x" by simp

        hence "False" using yOnl assms by blast
      }
      thus ?thesis by blast
    qed

    hence "norm2 D = 0" using impa by auto
    hence D0: "D = origin" using lemNullImpliesOrigin by auto

    have B0: "B = (B \<oplus> (0\<otimes>D))" by simp

    have "regularCone x (B \<oplus> (0\<otimes>D))" using allOnCone by blast
    hence BonCone: "regularCone x B" 
      using B0 by (metis (mono_tags, lifting))
    hence BinS: "B \<in> S" using assms BonCone B0 l by blast

    hence SisB: "S = {B}" 
    proof -
      { fix y assume y: "y \<in> S"
        then obtain \<alpha> where "y = (B \<oplus> (\<alpha>\<otimes>D))" using assms l by blast
        hence "y = B" using D0 by simp
        hence "y \<in> {B}" by blast
      }
      hence "S \<subseteq> {B}" by blast
      thus ?thesis using BinS by blast
    qed

  }
  thus ?thesis by auto
qed



lemma lemLineMeetsCone2:
  assumes "\<not> (x \<in> l)"
and       "isLine l"
and       "S = l \<inter> regularConeSet x"
and  l: "l = line B D"
and  X: "X = (B \<ominus> x)"
and "a = mNorm2 D"
and "b = 2*(tval (B\<ominus>x))*(tval D) - 2*((sComponent D) \<odot>s (sComponent (B\<ominus>x)))"
and "c = mNorm2 (B\<ominus>x)"
shows "qcase2 a b c \<longrightarrow> S = {}"
proof -
  { assume hyp2: "qcase2 a b c"
    { assume "S \<noteq> {}"
      then obtain y where y: "y \<in> S" by auto
      then obtain \<alpha> where \<alpha>: "y = (B \<oplus> (\<alpha>\<otimes>D))" using assms by blast
      hence "regularCone x (B \<oplus> (\<alpha>\<otimes>D))" using y assms by blast
      hence "qroot a b c \<alpha>" 
        using lemWhereLineMeetsCone[of "a" "D" "b" "B" "x" "c" "\<alpha>"] assms
        by auto
      hence "False" using lemQCase2[of "a" "b" "c"] hyp2 by auto
    }
    hence "S = {}" by auto
  }
  thus ?thesis by auto
qed
    



lemma lemLineMeetsCone3:
  assumes "\<not> (x \<in> l)"
and       "isLine l"
and       "S = l \<inter> regularConeSet x"
and  l: "l = line B D"
and  X: "X = (B \<ominus> x)"
and  a: "a = mNorm2 D"
and  b: "b = 2*(tval X)*(tval D) - 2*((sComponent D) \<odot>s (sComponent X))"
and  c: "c = sqr (tval X) - sNorm2 (sComponent X)"
and y3: "y3 = (B \<oplus> ((-c/b)\<otimes>D))"
shows "qcase3 a b c \<longrightarrow> S = {y3}"
proof -
  { assume hyp3: "qcase3 a b c"
    define T where T: "T = {y3}"

    have "S \<subseteq> T"
    proof -
      { fix y assume y: "y \<in> S"
        then obtain r where r: "y = (B \<oplus> (r\<otimes>D))" using l assms by blast  
        hence "regularCone x y" using y assms by auto
        hence abcr: "qroot a b c r"
          using a b c r X
                lemWhereLineMeetsCone[of "a" "D" "b" "B" "x" "c" "r"] 
          by auto
        hence "r = -c/b" using lemQCase3[of "a" "b" "c" "r"] abcr hyp3 by blast
        hence "y = y3" using y3 r by auto
        hence "y \<in> T" using T by blast
      }
      thus ?thesis by auto
    qed

    moreover have "T \<subseteq> S"
    proof -
      { fix y assume "y \<in> T"
        hence y: "y = (B \<oplus> ((-c/b)\<otimes>D))" using T assms by blast
        have "qroot a b c (-c/b)" using lemQCase3 hyp3 by auto

        hence rc: "regularCone x y" 
          using hyp3 assms y lemWhereLineMeetsCone[of "a" "D" "b" "B" "x" "c" "(-c/b)"] 
          by auto
        have "y \<in> l" using assms y by blast
        hence "y \<in> S" using rc assms by auto
      }
      thus ?thesis by blast
    qed

    ultimately have "S = {y3}" using T by auto
  }
  thus ?thesis by blast
qed
    


lemma lemLineMeetsCone4:
  assumes "\<not> (x \<in> l)"
and       "isLine l"
and       "S = l \<inter> regularConeSet x"
and  l: "l = line B D"
and  X: "X = (B \<ominus> x)"
and  a: "a = mNorm2 D"
and  b: "b = 2*(tval X)*(tval D) - 2*((sComponent D) \<odot>s (sComponent X))"
and  c: "c = sqr (tval X) - sNorm2 (sComponent X)"
shows "(qcase4 a b c \<longrightarrow> S = {})"
proof -
  { assume hyp4: "qcase4 a b c"
    { assume "S \<noteq> {}"
      then obtain y where y: "y \<in> S" by blast
      then obtain r where r: "y = (B \<oplus> (r\<otimes>D))" using l assms by blast  
      hence "regularCone x y" using y assms by auto
      hence abcr: "qroot a b c r"
        using a b c r X
              lemWhereLineMeetsCone[of "a" "D" "b" "B" "x" "c" "r"] 
        by auto
      hence "False" using lemQCase4 hyp4 by auto
    }
    hence "S = {}" by auto
  }
  thus ?thesis by blast
qed



lemma lemLineMeetsCone5:
  assumes "\<not> (x \<in> l)"
and       "isLine l"
and       "S = l \<inter> regularConeSet x"
and  l: "l = line B D"
and  X: "X = (B \<ominus> x)"
and  a: "a = mNorm2 D"
and  b: "b = 2*(tval X)*(tval D) - 2*((sComponent D) \<odot>s (sComponent X))"
and  c: "c = sqr (tval X) - sNorm2 (sComponent X)"
and y5: "y5 = (B \<oplus> ((-b/(2*a))\<otimes>D))"
shows "(qcase5 a b c \<longrightarrow> S = {y5})"
proof -
  { assume hyp5: "qcase5 a b c"
    define T where T: "T = {y5}"

    have "S \<subseteq> T"
    proof -
      { fix y assume y: "y \<in> S"
        then obtain r where r: "y = (B \<oplus> (r\<otimes>D))" using l assms by blast  
        hence "regularCone x y" using y assms by auto
        hence abcr: "qroot a b c r"
          using a b c r X
                lemWhereLineMeetsCone[of "a" "D" "b" "B" "x" "c" "r"] 
          by auto
        hence "r = -b/(2*a)" using lemQCase5 abcr hyp5 by blast
        hence "y = y5" using r y5 by auto
        hence "y \<in> T" using T by blast
      }
      thus ?thesis by blast
    qed

    moreover have "T \<subseteq> S"
    proof -
      { fix y assume "y \<in> T"
        hence y: "y = (B \<oplus> ( (-b/(2*a))\<otimes>D))" using T assms by blast
        have "qroot a b c (-b/(2*a))" using lemQCase5 hyp5 by blast
        hence rc: "regularCone x y" 
          using hyp5 assms y lemWhereLineMeetsCone[of "a" "D" "b" "B" "x" "c" "(-b/(2*a))"] 
          by auto
        have "y \<in> l" using assms y by blast
        hence "y \<in> S" using rc assms by auto
      }
      thus ?thesis by blast
    qed

    ultimately have "S = {y5}" using T by auto
  }
  thus ?thesis by blast
qed




lemma lemLineMeetsCone6:
  assumes "\<not> (x \<in> l)"
and       "isLine l"
and       "S = l \<inter> regularConeSet x"
and  l: "l = line B D"
and  X: "X = (B \<ominus> x)"
and  a: "a = mNorm2 D"
and  b: "b = 2*(tval X)*(tval D) - 2*((sComponent D) \<odot>s (sComponent X))"
and  c: "c = sqr (tval X) - sNorm2 (sComponent X)"
and ym: "ym = (B \<oplus> (((-b - (sqrt (discriminant a b c))) / (2*a)) \<otimes> D))"
and yp: "yp = (B \<oplus> (((-b + (sqrt (discriminant a b c))) / (2*a)) \<otimes> D))"
shows "(qcase6 a b c \<longrightarrow> (ym \<noteq> yp) \<and> S = {ym, yp})"
proof -
  { assume hyp6: "qcase6 a b c"

    define T where T: "T = {ym, yp}"
    define rm where rm: "rm = (-b - (sqrt (discriminant a b c))) / (2*a)"
    define rp where rp: "rp = (-b + (sqrt (discriminant a b c))) / (2*a)"

    have ymnotyp: "ym \<noteq> yp"
    proof -
      define d where d: "d = discriminant a b c"
      define sd where sd: "sd = sqrt d"

      have sdnot0: "sqrt d \<noteq> 0"
      proof -
        have dpos: "d > 0" using d hyp6 by simp
        hence "hasRoot d" using AxEField by auto
        thus ?thesis using lemSquareOfSqrt[of "d"] dpos by auto
      qed

      have Dnot0: "D \<noteq> origin"
      proof -
        { assume "D = origin"
          hence "a = 0" using a by simp
          hence "False" using hyp6 by simp
        }
        thus ?thesis by auto
      qed

      have rmnotrp: "rm \<noteq> rp"
      proof -
        { assume "rm = rp"
          hence "(-b - sd) / (2*a) = (-b + sd)/(2*a)" using sd d rm rp by simp
          hence "-b-sd = -b+sd" using hyp6 by simp
          hence "-sd = sd" using add_left_imp_eq diff_conv_add_uminus by metis
          hence "False" using sdnot0 sd by simp
        }
        thus ?thesis by auto
      qed

      { assume "ym = yp"
        hence "(B \<oplus> (rm \<otimes> D)) = (B \<oplus> (rp \<otimes> D))" using ym yp rm rp by auto
        hence "(rm \<otimes> D) = (rp \<otimes> D)" by simp
        hence "((rm - rp)\<otimes>D) = origin" by auto
        hence "rm - rp = 0" using Dnot0 by auto
        hence "False" using rmnotrp by auto
      }
      thus ?thesis by auto
    qed


    have "S \<subseteq> T"
    proof -
      { fix y assume y: "y \<in> S"
        then obtain r where r: "y = (B \<oplus> (r\<otimes>D))" using l assms by blast  
        hence "regularCone x y" using y assms by auto
        hence abcr: "qroot a b c r"
          using a b c r X
                lemWhereLineMeetsCone[of "a" "D" "b" "B" "x" "c" "r"] 
          by auto
        hence "qroots a b c = {rp, rm}" 
          using lemQCase6[of "a" "b" "c" "sqrt (discriminant a b c)" "rp" "rm"] 
                rp rm hyp6 by auto
        hence rchoice: "(r = rm \<or> r = rp)" using abcr by blast
        hence ychoice: "(y = ym \<or> y = yp)" using r ym yp rm rp by blast
        hence yinT: "y \<in> T" using T by blast
      }
      thus ?thesis by auto
    qed

    moreover have "T \<subseteq> S"
    proof -
      { fix y assume "y \<in> T"
        hence y: "y = ym \<or> y = yp" using T assms by blast
        
        have "qroot a b c rm" using rm lemQCase6 hyp6 by blast
        hence rcm: "regularCone x ym"
          using hyp6 assms ym rm lemWhereLineMeetsCone[of "a" "D" "b" "B" "x" "c" "rm"]
          by auto
        have "qroot a b c rp" using rp lemQCase6 hyp6 by blast
        hence rcp: "regularCone x yp"
          using hyp6 assms yp rp lemWhereLineMeetsCone[of "a" "D" "b" "B" "x" "c" "rp"]
          by auto
        hence "regularCone x y" using rcm y by blast
        moreover have "y \<in> l" using assms y by blast
        ultimately have "y \<in> S" using assms by blast
      }
      thus ?thesis by blast
    qed

    ultimately have "(ym \<noteq> yp) \<and> S = {ym, yp}" using T ymnotyp by auto
  }
  thus ?thesis by blast
qed


lemma lemConeLemma1:
  assumes "\<not> (x \<in> l)"
and       "isLine l"
and       "S = l \<inter> regularConeSet x"
shows     "finite S \<and> card S \<le> 2"
proof -
  obtain B D where BD: "l = line B D" using assms(2) by auto

  define X where X: "X = (B \<ominus> x)"
  define a where a: "a = mNorm2 D"
  define b where b: "b = 2*(tval X)*(tval D) - 2*((sComponent D) \<odot>s (sComponent X))"
  define c where c: "c = sqr (tval X) - sNorm2 (sComponent X)"

  have "qcase1 a b c \<longrightarrow> ?thesis" 
    using assms X a b c lemLineMeetsCone1[of "x" "l" "S" "B" "D" "X" "a" "b" "c"] BD
    by auto
  moreover have "qcase2 a b c \<longrightarrow> ?thesis" 
    using assms X a b c lemLineMeetsCone2[of "x" "l" "S" "B" "D" "X" "a" "b" "c"] BD
    by auto
  moreover have "qcase3 a b c \<longrightarrow> ?thesis" 
    using assms X a b c lemLineMeetsCone3[of "x" "l" "S" "B" "D" "X" "a" "b" "c"] BD
    by auto
  moreover have "qcase4 a b c \<longrightarrow> ?thesis" 
    using assms X a b c lemLineMeetsCone4[of "x" "l" "S" "B" "D" "X" "a" "b" "c"] BD
    by auto
  moreover have "qcase5 a b c \<longrightarrow> ?thesis" 
    using assms X a b c lemLineMeetsCone5[of "x" "l" "S" "B" "D" "X" "a" "b" "c"] BD
    by auto
  moreover have "qcase6 a b c \<longrightarrow> ?thesis" 
  proof -
    { assume hyp6: "qcase6 a b c"
      define ym where ym: "ym = (B \<oplus> (((-b - (sqrt (discriminant a b c))) / (2*a)) \<otimes> D))"
      define yp where yp: "yp = (B \<oplus> (((-b + (sqrt (discriminant a b c))) / (2*a)) \<otimes> D))"
  
      have "(ym \<noteq> yp) \<and> S = { ym, yp }"
        using assms X a b c ym yp hyp6
              lemLineMeetsCone6[of "x" "l" "S" "B" "D" "X" "a" "b" "c" "ym" "yp"] BD
        by auto
      hence "card S = 2" using card_2_iff by blast
      hence "finite S \<and> card S \<le> 2" using card.infinite by fastforce
    }
    thus ?thesis by auto
  qed

  ultimately show ?thesis using lemQuadraticCasesComplete by blast
qed


lemma lemConeLemma2:
  assumes "\<not> (regularCone x w)"
  shows   "\<exists> l . (onLine w l) \<and> (\<not> (x \<in> l)) \<and> (card (l \<inter> (regularConeSet x)) = 2)"
proof -
  have xnotw: "x \<noteq> w" using assms lemConeContainsVertex by blast

  have iftvalsequal: "tval x = tval w \<longrightarrow> ?thesis"
  proof -
    { assume ts: "tval x = tval w"
      define l where l: "l = line w tUnit"

      hence wonl: "onLine w l" 
      proof -
        have "w = (w \<oplus> (0\<otimes>tUnit))" by simp
        thus ?thesis using l by blast
      qed

      have xnotinl: "\<not>(x \<in> l)"
      proof -
        { assume "x \<in> l"
          then obtain a where a: "x = (w \<oplus> (a\<otimes>tUnit))" using l by blast
          hence "tval x = tval w + a" by simp
          hence "a = 0" using ts by simp
          hence "x = w" using a by simp
          hence "False" using xnotw by simp
        }
        thus ?thesis by blast
      qed

      have "card (l \<inter> (regularConeSet x)) = 2"
      proof -
        define S where S: "S = l \<inter> regularConeSet x"
        hence cardS: "finite S \<and> card S \<le> 2" 
          using xnotinl l lemConeLemma1[of "x" "l" "S"] by blast

        have "(sNorm2 (sComponent (w\<ominus>x))) \<ge> 0" by simp
        hence sExists: "hasRoot (sNorm2 (sComponent (w\<ominus>x)))" using AxEField by auto

        define s  where  s: "s = sqrt (sNorm2 (sComponent (w\<ominus>x)))"
        define yp where yp: "yp = (w \<oplus> (s\<otimes>tUnit))"
        define ym where ym: "ym = (w \<ominus> (s\<otimes>tUnit))"

        have ypnotym: "yp \<noteq> ym"
        proof -
          { assume "yp = ym"
            hence "(w \<oplus> (s\<otimes>tUnit)) = (w \<ominus> (s\<otimes>tUnit))" using yp ym by auto
            hence "tval w + s = tval w - s" by simp
            hence "s = 0" 
              by (metis local.add_cancel_right_right 
                        local.double_zero_sym local.lemDiffSumCancelMiddle)
            hence "sNorm2 (sComponent (w\<ominus>x)) = sqr 0" 
              using s lemSquareOfSqrt[of "sNorm2 (sComponent (w\<ominus>x))" "s"] sExists
              by auto
            hence "norm2 (w\<ominus>x) = 0" using lemNorm2Decomposition ts by auto
            hence "(w\<ominus>x) = origin" using lemNullImpliesOrigin by blast
            hence "w = x" by simp
            hence "False" using xnotw by simp
          }
          thus ?thesis by auto
        qed


        have ypinl: "yp \<in> l" using yp l by blast
        have yminl: "ym \<in> l" 
        proof - 
          have "ym = (w \<oplus> ((-s)\<otimes>tUnit))" using ym by simp
          thus ?thesis using l by blast
        qed

        have ypcone: "yp \<in> regularConeSet x"
        proof -
          have "(yp \<ominus> x) = ((w \<oplus> (s\<otimes>tUnit)) \<ominus> x)" using yp by auto
          hence "tval (yp \<ominus> x) = s" using ts by simp
          hence tsqr: "sqr (tval (yp\<ominus>x)) = (sNorm2 (sComponent (w\<ominus>x)))"
            using s sExists lemSquareOfSqrt AxEField by blast
          hence "sComponent (yp\<ominus>x) = sComponent ((w \<oplus> (s\<otimes>tUnit)) \<ominus> x)" using yp by auto
          also have "\<dots> = ((sComponent (w \<oplus> (s\<otimes>tUnit))) \<ominus>s (sComponent x))" by simp
          also have "\<dots> = (((sComponent w) \<oplus>s (sComponent (s\<otimes>tUnit))) \<ominus>s (sComponent x))" by simp
          also have "\<dots> = ((sComponent w) \<ominus>s (sComponent x))" by simp
          finally have "sComponent (yp\<ominus>x) = sComponent (w\<ominus>x)" by simp
          hence ssqr: "sNorm2 (sComponent (yp\<ominus>x)) = (sNorm2 (sComponent (w\<ominus>x)))"
            by auto
          hence "sqr (tval (yp\<ominus>x)) = (sNorm2 (sComponent (yp\<ominus>x)))" using tsqr by auto
          hence "onRegularCone x yp" using lemConeCoordinates[of "x" "yp"] by auto
          thus ?thesis using lemRegularCone by blast
        qed
            
        have ymcone: "ym \<in> regularConeSet x"
        proof -
          have "(ym \<ominus> x) = ((w \<ominus> (s\<otimes>tUnit)) \<ominus> x)" using ym by auto
          hence "tval (ym \<ominus> x) = tval (w \<ominus> (s\<otimes>tUnit)) - tval x" by simp
          also have "\<dots> = (tval w - tval(s\<otimes>tUnit)) - tval x" by simp
          also have "\<dots> = (tval w - s) - tval w" using ts by simp
          finally have "tval (ym\<ominus>x) = -s" using diff_right_commute 
            by (metis local.add_implies_diff local.uminus_add_conv_diff)
          hence "sqr (tval (ym\<ominus>x)) = sqr s" by simp
          hence tsqr: "sqr (tval (ym\<ominus>x)) = (sNorm2 (sComponent (w\<ominus>x)))"
            using s sExists lemSquareOfSqrt AxEField by force

          hence "sComponent (ym\<ominus>x) = sComponent ((w \<ominus> (s\<otimes>tUnit)) \<ominus> x)" using ym by auto
          also have "\<dots> = ((sComponent (w \<ominus> (s\<otimes>tUnit))) \<ominus>s (sComponent x))" by simp
          also have "\<dots> = (((sComponent w) \<ominus>s (sComponent (s\<otimes>tUnit))) \<ominus>s (sComponent x))" by simp
          also have "\<dots> = ((sComponent w) \<ominus>s (sComponent x))" by simp
          finally have "sComponent (ym\<ominus>x) = sComponent (w\<ominus>x)" by simp
          hence ssqr: "sNorm2 (sComponent (ym\<ominus>x)) = (sNorm2 (sComponent (w\<ominus>x)))"
            by auto
          hence "sqr (tval (ym\<ominus>x)) = (sNorm2 (sComponent (ym\<ominus>x)))" using tsqr by auto
          hence "onRegularCone x ym" using lemConeCoordinates[of "x" "ym"] by auto
          thus ?thesis using lemRegularCone by blast
        qed
            
        define T where T: "T = {yp, ym}"

        hence "T \<subseteq> S" using ypinl ypcone yminl ymcone S by auto
        hence TleS: "card T \<le> card S" using cardS card_mono by blast
        have cardT: "card T = 2" using T ypnotym card_2_iff by blast

        hence "(2 \<le> card S) \<and> finite S \<and> card S \<le> 2" using TleS cardS by auto
        thus ?thesis using S by simp
      qed

      hence ?thesis using xnotinl wonl by blast
    }
    thus ?thesis by auto
    (* end of proof of iftvalseq, i.e. when tval w = tval x *)
  qed

  have iftvalsne: "tval x \<noteq> tval w \<longrightarrow> ?thesis"
  proof -
    { assume ts: "tval x \<noteq> tval w"

      define x0 where x0: "x0 = mkPoint (tval w) (xval x) (yval x) (zval x)"
      have xnotx0: "x \<noteq> x0" using x0 ts by (metis Point.select_convs(1))
      have tdiff0: "tval w = tval x0" using x0 by simp

      define dir where dir: "dir = (if (w\<noteq>x0) then (w\<ominus>x0) else xUnit)"

      hence tdir0: "tval dir = 0"
      proof -
        { assume "w\<noteq>x0"
          hence "dir = (w\<ominus>x0)" using dir by simp
        }
        hence wnotx0: "(w\<noteq>x0) \<longrightarrow> ?thesis" using tdiff0 by auto
        { assume "w = x0"
          hence "dir = xUnit" using dir by simp
        }
        hence "(w=x0) \<longrightarrow> ?thesis" by simp
        thus ?thesis using wnotx0 by auto
      qed
    
      define l where l: "l = lineJoining x0 (dir\<oplus>x0)"
      hence lprops: "l = line x0 dir" using dir by auto

      hence wonl: "onLine w l"
      proof -
        { assume wnotx0: "w \<noteq> x0"
          hence "dir = (w\<ominus>x0)" using dir by simp
          hence "(dir\<oplus>x0) = ((w\<ominus>x0)\<oplus>x0)" by simp
          hence "w = (dir \<oplus> x0)" using diff_add_eq by auto
          hence ?thesis using dir lemLineJoiningContainsEndPoints l by blast
        }
        moreover have "(w=x0) \<longrightarrow> ?thesis" using lemLineJoiningContainsEndPoints l by blast
        ultimately show ?thesis by auto
      qed

      then obtain A where A: "w = (x0 \<oplus> (A \<otimes> dir ))" using l by auto
  
      have xnotinl: "\<not>(x \<in> l)"
      proof -
        { assume "x \<in> l"
          then obtain a where a: "x = (x0 \<oplus> (a\<otimes>dir))" using l by auto
          hence "tval x = tval x0" using tdir0 by simp
          hence "False" using ts tdiff0 by auto
        }
        thus ?thesis by blast
      qed
  
      have "card (l \<inter> (regularConeSet x)) = 2"
      proof -
        define S where S: "S = l \<inter> regularConeSet x"
        hence cardS: "finite S \<and> card S \<le> 2" 
          using xnotinl l lemConeLemma1[of "x" "l" "S"] by blast

        have "(sNorm2 (sComponent (w\<ominus>x0))) \<ge> 0" by simp
        hence sExists: "hasRoot (sNorm2 (sComponent (w\<ominus>x0)))" using AxEField by auto
        define s where s: "s = sqrt (sNorm2 (sComponent (w\<ominus>x0)))"

        define unit where unit: "unit = (if (w = x0) then xUnit else ((1/s)\<otimes>(w\<ominus>x0)))"

        have tunit0: "tval unit = 0"
        proof -
          { assume "w = x0"
            hence "unit = xUnit" using unit by simp
          }
          hence "w=x0 \<longrightarrow> ?thesis" by auto
          moreover have "w\<noteq>x0 \<longrightarrow> ?thesis"
          proof -
            { assume wnotx0: "w \<noteq> x0"
              hence "unit = ((1/s)\<otimes>dir)" using unit dir by simp
            }
            thus ?thesis using tdir0 by auto
          qed
          ultimately show ?thesis by auto
        qed

        have snot0: "w \<noteq> x0 \<longrightarrow> s \<noteq> 0" 
        proof -
          { assume wnotx0: "w \<noteq> x0"
            hence "norm2 (w\<ominus>x0) > 0" 
              using local.lemNotEqualImpliesSep2Pos by presburger
            also have "norm2 (w\<ominus>x0) = sNorm2 (sComponent (w\<ominus>x0))"
              using tdiff0 lemNorm2Decomposition[of "w\<ominus>x0"] by auto
            finally have s2pos: "sNorm2 (sComponent (w\<ominus>x0)) > 0" by auto
            { assume "s = 0"
              hence "False" using lemSquareOfSqrt[of "sNorm2 (sComponent (w\<ominus>x0))" "s"]
                                  s2pos s sExists by auto
            }
            hence "s \<noteq> 0" by auto
          }
          thus ?thesis by auto
        qed

        hence unit1: "sNorm2 (sComponent unit) = 1"
        proof -
          have case0: "w=x0 \<longrightarrow> ?thesis" using unit by auto
          have case1: "w\<noteq>x0 \<longrightarrow> ?thesis"
          proof -
          { assume case1: "w \<noteq> x0"
            have "unit = ((1/s)\<otimes>(w\<ominus>x0))" using unit case1 by simp
            hence "sComponent unit = ((1/s) \<otimes>s (sComponent (w\<ominus>x0)))" by simp
            hence "sNorm2 (sComponent unit) = sqr (1/s) * sNorm2 (sComponent (w\<ominus>x0))"
              using lemSNorm2OfScaled[of "(1/s)" "sComponent (w\<ominus>x0)"] 
              by auto
            also have "\<dots> = sqr (1/s) * sqr s" 
              using lemSquareOfSqrt[of "sNorm2 (sComponent (w\<ominus>x0))" "s"] sExists s 
              by auto
            finally have "sNorm2 (sComponent unit) = 1" using snot0 case1 by simp
          }
          thus ?thesis by auto
        qed
        thus ?thesis using case0 by blast
      qed

      define dt where dt: "dt = tval w - tval x"
      define mdt where mdt: "mdt = -dt"
      define yp where yp: "yp = (x0 \<oplus> (dt \<otimes> unit))"
      define ym where ym: "ym = (x0 \<ominus> (dt \<otimes> unit))"
      hence ymalt: "ym = (x0 \<oplus> (mdt \<otimes> unit))" using mdt by simp

      have ypnotym: "yp \<noteq> ym"
      proof -
        { assume "yp = ym"
          hence "(x0 \<oplus> (dt\<otimes>unit)) = (x0 \<ominus> (dt\<otimes>unit))" using yp ym by auto
          hence "((x0 \<oplus> (dt\<otimes>unit)) \<oplus> (dt\<otimes>unit)) = x0" by auto
          hence "(x0 \<oplus> (2\<otimes>(dt\<otimes>unit))) = x0" using add_assoc mult_2 by auto
          hence "((x0 \<oplus> (2\<otimes>(dt\<otimes>unit))) \<ominus> x0) = origin" by simp
          hence "(2\<otimes>(dt\<otimes>unit)) = origin" using add_diff_eq by auto
          hence "False" using unit1 ts dt by simp
        }
        thus ?thesis by auto
      qed

      have ypinl: "yp \<in> l"
      proof -
        { assume "w = x0"
          hence "yp = (w \<oplus> (dt\<otimes>dir))" using dir unit yp by simp
          hence "\<exists> a . yp = (w \<oplus> (a \<otimes> dir))" using yp by auto
        }
        hence wx0: "w=x0 \<longrightarrow> ?thesis" using l by auto

        { assume wnotx0: "w \<noteq> x0"
          hence u: "unit = ((1/s)\<otimes>dir)" using unit dir by auto
          hence "yp = (x0 \<oplus> ((dt/s)\<otimes>dir))" using lemScaleAssoc yp by auto
          hence "\<exists> a . yp = (x0 \<oplus> (a\<otimes>dir))" using snot0 by blast
        }
        hence "w\<noteq>x0 \<longrightarrow> ?thesis" using l by auto
        thus ?thesis using wx0 by blast
      qed
          
      have yminl: "ym \<in> l"
      proof -
        { assume "w = x0"
          hence "ym = (x0 \<oplus> (mdt\<otimes>dir))" using dir unit ymalt by simp
          hence "\<exists> a . ym = (x0 \<oplus> (a \<otimes> dir))" using ym by auto
        }
        hence wx0: "w=x0 \<longrightarrow> ?thesis" using l by auto

        { assume wnotx0: "w \<noteq> x0"
          hence u: "unit = ((1/s)\<otimes>dir)" using unit dir by auto
          hence "ym = (x0 \<oplus> ((mdt/s)\<otimes>dir))" using lemScaleAssoc ymalt by auto
          hence "\<exists> a . ym = (x0 \<oplus> (a\<otimes>dir))" using snot0 by blast
        }
        hence "w\<noteq>x0 \<longrightarrow> ?thesis" using l by auto
        thus ?thesis using wx0 by blast
      qed
            
      have ypcone: "yp \<in> regularConeSet x"
      proof -
        have "sNorm2 (sComponent (yp\<ominus>x0)) = sqr dt" 
        proof - 
          have "yp = (x0 \<oplus> (dt \<otimes> unit))" using yp by simp
          hence "(yp \<ominus> x0) = (dt \<otimes> unit)" using add_diff_eq diff_add_eq by auto
          hence "sComponent (yp \<ominus> x0) = (dt \<otimes>s (sComponent unit))" by auto
          thus ?thesis
            using lemSNorm2OfScaled[of "dt" "sComponent unit"] unit1 by auto
        qed       
        hence "sNorm2 (sComponent (yp\<ominus>x)) = sqr dt" using x0 by simp
        also have "\<dots> = sqr (tval (yp\<ominus>x))" using dt tunit0 yp tdiff0 by simp
        finally have "sNorm2 (sComponent (yp\<ominus>x)) =  sqr (tval (yp\<ominus>x))" by blast
        hence "onRegularCone x yp" using lemConeCoordinates[of "x" "yp"] by auto
        thus ?thesis using lemRegularCone by blast
      qed
            
      have ymcone: "ym \<in> regularConeSet x"
      proof -
        have "sNorm2 (sComponent (ym\<ominus>x0)) = sqr dt" 
        proof - 
          have "ym = (x0 \<oplus> (mdt \<otimes> unit))" using ymalt by simp
          hence "(ym \<ominus> x0) = (mdt \<otimes> unit)" using add_diff_eq diff_add_eq by auto
          hence "sComponent (ym \<ominus> x0) = (mdt \<otimes>s (sComponent unit))" by auto
          thus ?thesis
            using lemSNorm2OfScaled[of "mdt" "sComponent unit"] unit1 mdt by auto
        qed       
        hence "sNorm2 (sComponent (ym\<ominus>x)) = sqr dt" using x0 by simp
        also have "\<dots> = sqr (tval (ym\<ominus>x))" using ym mdt dt tunit0 tdiff0 by auto
        finally have "sNorm2 (sComponent (ym\<ominus>x)) =  sqr (tval (ym\<ominus>x))" by blast
        hence "onRegularCone x ym" using lemConeCoordinates[of "x" "ym"] by auto
        thus ?thesis using lemRegularCone by blast
      qed          
              
      define T where T: "T = {yp, ym}"

      hence "T \<subseteq> S" using ypinl ypcone yminl ymcone S by auto
      hence TleS: "card T \<le> card S" using cardS card_mono by blast
      have cardT: "card T = 2" using T ypnotym card_2_iff by blast

      hence "(2 \<le> card S) \<and> finite S \<and> card S \<le> 2" using TleS cardS by auto
      thus ?thesis using S by simp
    qed
    
    hence ?thesis using xnotinl wonl by blast
    }
    thus ?thesis by auto
    (* end of proof of iftvalsne, i.e. when tval w \<noteq> tval x *)
  qed
  thus ?thesis using iftvalsequal by blast
qed
  


lemma lemLineInsideRegularConeHasFiniteSlope:
  assumes "insideRegularCone x p"
and       "l = lineJoining x p"
shows     "lineSlopeFinite l"
proof -
  { assume converse: "\<not> (lineSlopeFinite l)"
    hence slope: "slopeInfinite x p" 
      using assms lemSlopeLineJoining[of "l"] by blast
    hence "False" using assms(1) assms(2) slope by simp
  }
  thus ?thesis by auto
qed



lemma lemInvertibleOnMeet:
  assumes "invertible f"
and       "S = A \<inter> B"
shows     "applyToSet (asFunc f) S = (applyToSet (asFunc f) A) \<inter> (applyToSet (asFunc f) B)"
proof -
  define S' where S': "S' = applyToSet (asFunc f) S"
  define A' where A': "A' = applyToSet (asFunc f) A"
  define B' where B': "B' = applyToSet (asFunc f) B"

  have "S' \<subseteq> A' \<inter> B'"
  proof -
    { fix s' assume "s' \<in> S'"
      then obtain s where s: "s \<in> S \<and> f s = s'" using S' by auto
      have inA: "s' \<in> A'"
      proof -
        have "s \<in> A" using assms s by auto
        thus ?thesis using s A' by auto
      qed
      have inB: "s' \<in> B'"
      proof -
        have "s \<in> B" using assms s by auto
        thus ?thesis using s B' by auto
      qed
      hence "s' \<in> A' \<inter> B'" using inA by auto
    }
    thus ?thesis by auto
  qed
  
  moreover have "A' \<inter> B' \<subseteq> S'"
  proof -
    { fix s' assume s': "s' \<in> A' \<inter> B'"
      then obtain a where a: "a \<in> A \<and> f a = s'" using A' by auto
      obtain b where b: "b \<in> B \<and> f b = s'" using s' B' by auto

      have "(\<exists> p . (f p = s') \<and> (\<forall>x. f x = s' \<longrightarrow> x = p))" using assms(1) by auto
      then obtain p where p: "(f p = s') \<and> (\<forall>x. f x = s' \<longrightarrow> x = p)" by auto
      hence "a = b" using a b by blast
      hence "a \<in> S \<and> f a = s'" using a b assms(2) by auto
      hence "s' \<in> S'" using S' by auto
    }
    thus ?thesis by auto
  qed

  ultimately show ?thesis using S' A' B' by auto
qed


lemma lemInsideCone:
  shows "insideRegularCone x p \<longleftrightarrow>
            \<not>(vertex x p \<or> outsideRegularCone x p \<or> onRegularCone x p)"
proof -
  { assume lhs: "insideRegularCone x p"
    hence "(slopeFinite x p) \<and> (\<exists> v \<in> lineVelocity (lineJoining x p) . sNorm2 v < 1)"
      by auto
    hence rtp1: "\<not>(vertex x p)" by blast

    define l where l: "l = lineJoining x p"

    obtain vin where vin: "vin \<in> lineVelocity l \<and> sNorm2 vin < 1" using l lhs by blast
    hence vs: "\<forall> v . v \<in> lineVelocity l \<longrightarrow> sNorm2 v < 1"
    proof -
      { fix v assume v: "v \<in> lineVelocity l"
        have "slopeFinite x p" using lhs by blast
        moreover have "onLine x l \<and> onLine p l" using l lemLineJoiningContainsEndPoints
          by auto
        ultimately have "v = vin" 
          using rtp1 v vin lemFiniteLineVelocityUnique[of "v" "l" "vin"] by blast
      }
      thus ?thesis using vin by blast
    qed

    { assume "outsideRegularCone x p"
      then obtain v where v: "v \<in> lineVelocity l \<and> sNorm2 v > 1" using l lhs by blast
      hence "sNorm2 v < 1" using vs by blast
      hence "False" using v by force
    }
    hence rtp2: "\<not> outsideRegularCone x p" by blast
    { assume "onRegularCone x p"
      then obtain v where v: "v \<in> lineVelocity l \<and> sNorm2 v = 1" using l lhs by blast
      hence "sNorm2 v < 1" using vs by blast
      hence "False" using v by force
    }
    hence rtp3: "\<not> onRegularCone x p" by blast
    hence "\<not>(vertex x p \<or> outsideRegularCone x p \<or> onRegularCone x p)"
      using rtp1 rtp2 by blast
  }
  hence l2r: "insideRegularCone x p \<longrightarrow>
            \<not>(vertex x p \<or> outsideRegularCone x p \<or> onRegularCone x p)"
    by blast

  { assume rhs: "\<not>(vertex x p \<or> outsideRegularCone x p \<or> onRegularCone x p)"
    define v where v: "v = (insideRegularCone x p)"
    define z where z: "z = (vertex x p \<or> outsideRegularCone x p \<or> onRegularCone x p)"
    hence "v \<or> z" using v z lemClassification[of "x" "p"] by auto
    hence "insideRegularCone x p" using rhs v z by blast
  }
  thus ?thesis using l2r by blast
qed
    

lemma lemOnRegularConeIff:
  assumes "l = lineJoining x p"
  shows "onRegularCone x p \<longleftrightarrow> (l \<inter> regularConeSet x = l)"
proof -
  { assume rc: "onRegularCone x p"
    hence reg: "regularCone x p" using lemRegularCone by blast
    define S where S: "S = l \<inter> regularConeSet x"
    
    have SinL: "S \<subseteq> l" using S by blast

    have "l \<subseteq> S"
    proof -
      { fix q assume q: "q \<in> l"
        then obtain a where a: "q = (x \<oplus> (a \<otimes> (p\<ominus>x)))" using assms by blast
        hence qmx: "(q\<ominus>x) = (a \<otimes> (p\<ominus>x))" by simp

        hence "sqr (tval (q\<ominus>x)) = sqr (tval (a \<otimes> (p\<ominus>x)))" by auto
        also have "\<dots> = (sqr a)*(sqr (tval p - tval x))" using lemSqrMult by auto
        also have "\<dots> = (sqr a)*(sNorm2 (sComponent (p\<ominus>x)))"
          using rc lemConeCoordinates[of "x" "p"] by auto
        also have "\<dots> = sNorm2 ( a \<otimes>s (sComponent (p\<ominus>x)) )"
          using lemSNorm2OfScaled[of "a" "(sComponent (p\<ominus>x))"] by auto
        also have "\<dots> = sNorm2 (sComponent ( a \<otimes> (p\<ominus>x) ))" by simp
        finally have  "sqr (tval (q\<ominus>x)) = sNorm2 (sComponent (q\<ominus>x) )" using qmx by simp
        hence "onRegularCone x q" using lemConeCoordinates[of "x" "q"] by auto
        hence "regularCone x q" using lemRegularCone by blast
        hence "q \<in> S" using S q by auto
      }
      hence "\<forall> q . q \<in> l \<longrightarrow> q \<in> S" by blast
      thus ?thesis by blast
    qed

    hence "(l \<inter> regularConeSet x = l)" using S SinL by blast
  }
  hence l2r: "onRegularCone x p \<longrightarrow> (l \<inter> regularConeSet x = l)" by blast

  { assume rhs: "(l \<inter> regularConeSet x = l)"
    have "p \<in> l" 
      using lemLineJoiningContainsEndPoints[of "l" "x" "p"] assms(1) by auto
    hence "regularCone x p" using rhs by blast
    hence "onRegularCone x p" using lemRegularCone by blast
  }
  thus ?thesis using l2r by blast
qed



lemma lemOutsideRegularConeImplies:
  shows     "outsideRegularCone x p 
                \<longrightarrow> (\<exists> l p' . (p' \<noteq> p) \<and> onLine p' l \<and> onLine p l
                                          \<and> (l \<inter> regularConeSet x = {}))"
proof -
  { assume lhs: "outsideRegularCone x p"

    hence xnotp: "(x \<noteq> p)" by auto
    hence formula: "sqr (tval p - tval x) < sNorm2 (sComponent (p\<ominus>x))"
      using lemConeCoordinates[of "x" "p"] using lhs by auto

    have  cases: "(slopeInfinite x p) \<or>
                     ((slopeFinite x p) \<and> 
                       (\<exists> v \<in> lineVelocity (lineJoining x p) . sNorm2 v > 1))"
      using lhs by blast

    have case1: "slopeInfinite x p \<longrightarrow> 
                   (\<exists> l p' . (p' \<noteq> p) \<and> onLine p' l \<and> onLine p l
                                          \<and> (l \<inter> regularConeSet x = {}))"
      using xnotp lemSlopeInfiniteImpliesOutside
      by blast


    have case2: 
      "((slopeFinite x p) \<and> (\<exists> v \<in> lineVelocity (lineJoining x p) . sNorm2 v > 1))
           \<longrightarrow> (\<exists> l p' . (p' \<noteq> p) \<and> onLine p' l \<and> onLine p l
                                          \<and> (l \<inter> regularConeSet x = {}))"
    proof -
      define l where l: "l = lineJoining x p"
      hence onl: "onLine x l \<and> onLine p l" using lemLineJoiningContainsEndPoints by blast

      { assume hyp: "(slopeFinite x p) \<and>
                           (\<exists> v \<in> lineVelocity (lineJoining x p) . sNorm2 v > 1)"
        then obtain v where v: "v \<in> lineVelocity l \<and> sNorm2 v > 1"
          using l by blast

        (* sphere at t = tval p has radius tval p. Find point of intersection
           of line from p to t-axis with sphere. Gout out twice as far.
           Then use any orthogonal line.  *)
        define x0 where x0: "x0 = mkPoint (tval p) (xval x) (yval x) (zval x)"
        define dsqr where dsqr: "dsqr = norm2 (p \<ominus> x0)"
        define d where d: "d = sqrt dsqr"

        have dExists: "hasRoot dsqr" using dsqr lemNorm2NonNeg AxEField by auto

        have xnotp: "x \<noteq> p" using hyp by auto

        have dnot0: "d \<noteq> 0"
        proof -
          { assume d0: "d = 0"
            hence "dsqr = 0" using lemSquareOfSqrt[of "dsqr" "d"] dExists d by auto
            hence "(p\<ominus>x0) = origin" using dsqr lemNullImpliesOrigin[of "(p\<ominus>x0)"] by auto
            hence "p = x0" by simp
            hence "sloper x p = ((1/(tval x - tval p))\<otimes>(x\<ominus>x0))" using x0 by auto
            moreover have "sComponent (x\<ominus>x0) = sOrigin" using x0 by simp
            ultimately have "velocityJoining x p = sOrigin" using hyp by auto
            hence "sOrigin \<in> lineVelocity l" 
              using lemLineVelocityUsingPoints[of "x" "p" "l"] l hyp xnotp onl by auto
            hence "sOrigin = v" 
              using lemFiniteLineVelocityUnique[of "sOrigin" "l" "v"] 
                    hyp v onl xnotp by blast
            hence "sNorm2 v = 0" by auto
            hence "False" using v by auto
          }
          thus ?thesis by auto
        qed

        hence dsqrnot0: "dsqr \<noteq> 0" 
          using d dExists lemSquareOfSqrt[of "dsqr" "d"] lemZeroRoot by blast

        have dpos: "d > 0" 
          using d theI'[of "isNonNegRoot dsqr"] lemSqrt dExists dnot0 by auto

        (* find spatially orthogonal line to radial line from x0 to p *)
        define T      where      T: "T      = tval p"
        define radius where radius: "radius = tval p - tval x"
        define R0     where     R0: "R0     = sComponent (p\<ominus>x)"

        have R0gtRadius: "sqr radius < sNorm2 R0" using formula radius R0 by auto

        have dsqr': "dsqr = sNorm2 R0"
        proof -
          have "sComponent x = sComponent x0" using x0 by simp
          hence "R0 = sComponent (p \<ominus> x0)" using R0 by auto
          moreover have "tval (p\<ominus>x0) = 0" using x0 by simp
          ultimately show ?thesis using lemNorm2Decomposition dsqr by auto
        qed

        hence radialnot0: "R0 \<noteq> sOrigin" using dsqrnot0 by auto

        (* Find an orthogonal direction *)
        obtain D0 where D0: "D0 \<noteq> sOrigin  \<and> ((D0 \<odot>s R0) = 0)" 
          using lemOrthogalSpaceVectorExists[of "R0"] by auto

        (* Direction and required line in 4-space *)
        define D where D: "D = stPoint 0 D0"
        define L where L: "L = line p D"

        (* CLAIM: p is on L *)
        hence pOnLine: "onLine p L" 
          using lemLineJoiningContainsEndPoints[of "L" "p" "(p\<oplus>D)"] by auto

        (* CLAIM: L doesn't meet the cone *)
        have meetEmpty: "L \<inter> regularConeSet x = {}"
        proof -
          { assume "L \<inter> regularConeSet x \<noteq> {}"
            then obtain Q where Q: "Q \<in> L \<inter> regularConeSet x" by blast
            then obtain \<alpha> where \<alpha>: "Q = (p \<oplus> (\<alpha> \<otimes> D))" using L by blast

            have "((p \<oplus> (\<alpha> \<otimes> D))\<ominus>x) = ((p\<ominus>x) \<oplus> (\<alpha>\<otimes>D))"
              using add_diff_eq diff_add_eq by auto
            hence Qmx: "(Q \<ominus> x) =  ((p\<ominus>x) \<oplus> (\<alpha>\<otimes>D))" using \<alpha> by simp

            hence Qmxt: "tval Q - tval x = tval (p\<ominus>x)" using D by simp

            have "sComponent (Q\<ominus>x) = sComponent ((p\<ominus>x) \<oplus> (\<alpha>\<otimes>D))" using Qmx by simp
            also have "\<dots> = ((sComponent (p\<ominus>x)) \<oplus>s (sComponent (\<alpha>\<otimes>D)))" by simp
            finally have "sNorm2 (sComponent (Q\<ominus>x))
               = sNorm2 ((sComponent (p\<ominus>x)) \<oplus>s (sComponent (\<alpha>\<otimes>D)))" by simp
            also have "\<dots> = sNorm2 (R0 \<oplus>s (\<alpha> \<otimes>s D0))" using R0 D by auto
            also have "\<dots> = sNorm2 R0 + 2*(R0 \<odot>s (\<alpha> \<otimes>s D0)) + sNorm2 (\<alpha> \<otimes>s D0)"
              using lemSNorm2OfSum[of "R0" "(\<alpha> \<otimes>s D0)"] by auto
            finally have
              "sNorm2 (sComponent (Q\<ominus>x)) = sNorm2 R0 + 2*(R0 \<odot>s (\<alpha> \<otimes>s D0)) + sNorm2 (\<alpha> \<otimes>s D0)"
              by auto

            moreover have "(R0 \<odot>s (\<alpha> \<otimes>s D0)) = 0"
              using D0 lemSDotCommute lemSDotScaleRight by simp
            moreover have "sNorm2 (\<alpha> \<otimes>s D0) \<ge> 0" by simp
            ultimately have "sNorm2 (sComponent (Q\<ominus>x)) \<ge> sNorm2 R0" by simp

            (* point is too far from centre of sphere *)
            hence Qmxs: "sNorm2 (sComponent (Q\<ominus>x)) > sqr radius" 
              using R0gtRadius by simp

            (* hence not on cone *)
            hence "sqr (tval Q - tval x) < sNorm2 (sComponent (Q\<ominus>x))"
              using radius Qmxt by simp
            hence "\<not> (onRegularCone x Q)" 
              using lemConeCoordinates[of "x" "Q"] by force
            hence "\<not> (regularCone x Q)" using lemRegularCone by blast
            hence "False" using Q by blast
          }
          thus ?thesis by blast
        qed

        define p' where p': "p' = (p \<oplus> D)"
        have Dnot0: "D \<noteq> origin" using D D0 by auto
        
        hence "p' \<noteq> p"
        proof -
          { assume "p' = p"
            hence "(p \<oplus> D) = p" using p' by auto
            hence "((p \<oplus> D) \<ominus> p) = origin" by simp
            hence "D = origin" using add_diff_cancel by auto
            hence "False" using Dnot0 by auto
          }
          thus ?thesis by blast
        qed
        moreover have "onLine p' L" using L p' by auto
        ultimately have target1: "p' \<noteq> p \<and> onLine p' L" by blast

        hence "(\<exists> l p' . (p' \<noteq> p) \<and> onLine p' l \<and> onLine p l
                   \<and> (l \<inter> regularConeSet x = {}))" using meetEmpty pOnLine by blast
      }
      thus ?thesis by blast
    qed

    hence "(\<exists> l p' . (p' \<noteq> p) \<and> onLine p' l \<and> onLine p l
                         \<and> (l \<inter> regularConeSet x = {}))" 
      using cases case1 by blast
  }
  hence l2r: "outsideRegularCone x p \<longrightarrow> 
                          (\<exists> l p' . (p' \<noteq> p) \<and> onLine p' l \<and> onLine p l
                                          \<and> (l \<inter> regularConeSet x = {}))"
    by blast

  thus ?thesis by blast
qed


lemma lemTimelikeInsideCone:
  assumes "insideRegularCone x p"
shows     "timelike (p \<ominus> x)"
proof -
  have "tval p - tval x \<noteq> 0" using assms by auto
  hence tdiffpos: "sqr (tval p - tval x) > 0" using lemSquaresPositive by auto

  define l where l: "l = lineJoining x p"
  hence "slopeFinite x p \<and> (\<exists> v . v \<in> lineVelocity l \<and> sNorm2 v < 1)"
    using assms by auto
  then obtain v where v: "v \<in> lineVelocity l \<and> sNorm2 v < 1" 
    using assms by blast
  have "lineVelocity l = { velocityJoining x p }" 
    using lemLineVelocityUsingPoints[of "x" "p" "l"] assms 
          lemLineJoiningContainsEndPoints l
    by blast
  hence vv: "v = velocityJoining x p \<and> sNorm2 v < 1" using v by auto
  hence formula: "sqr (tval p - tval x)*(sNorm2 v) = sNorm2 (sComponent (p\<ominus>x))" 
    using lemSNorm2VelocityJoining[of "x" "p" "v"] assms by blast

  have cases: "sNorm2 v = 0 \<or> sNorm2 v > 0"
    using local.add_less_zeroD local.not_less_iff_gr_or_eq 
          local.not_square_less_zero 
    by blast

  have case1: "sNorm2 v > 0 \<longrightarrow> timelike (p \<ominus> x)"
  proof -
    define snv where snv: "snv = sNorm2 v"
    { assume "sNorm2 v > 0"
      hence "0 < snv < 1" using vv snv by auto
      moreover have "sqr (tval p - tval x)*snv = sNorm2 (sComponent (p\<ominus>x))"
        using formula snv by simp
      ultimately have "sqr (tval p - tval x) > sNorm2 (sComponent (p\<ominus>x))"
        using lemMultPosLT[of "sqr (tval p - tval x)" "snv"]
              tdiffpos by force
      hence "timelike (p\<ominus>x)" by auto
    }
    thus ?thesis using snv by auto
  qed

  { assume "sNorm2 v = 0"
    hence "sNorm2 (sComponent (p \<ominus> x)) = 0" using formula by auto
    hence "timelike (p\<ominus>x)" using tdiffpos by auto
  }
  hence case2: "sNorm2 v = 0 \<longrightarrow> timelike (p\<ominus>x)" by auto

  thus ?thesis using case1 cases by auto
qed
    

end (* of class Classification *)
end (* of theory Classification *)
