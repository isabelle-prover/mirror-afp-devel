(*
   Author: Mike Stannett
   Date: June & July 2020
   Updated: Jan 2023
*)  

section \<open> MainLemma \<close>

text \<open>This theory establishes conditions under which a function maps
tangent lines to tangent lines.\<close>

theory MainLemma
  imports Sublemma3 Sublemma4
begin


class MainLemma = Sublemma3 + Sublemma4
begin



lemma lemMainLemmaBasic:
  assumes tgt:      "tangentLine l wl origin"
and       injf:     "injective f"
and       affapp:   "affineApprox A f origin"
and       f00:      "f origin origin"
and       ctsf'0:   "cts (invFunc f) origin"
and       affline:  "applyAffineToLine A l l'"
shows     "tangentLine l' (applyToSet f wl) origin"
proof -

  define goal1 where 
    goal1: "goal1 \<equiv> origin \<in> (applyToSet f wl)"
  define goal2 where 
    goal2: "goal2 \<equiv> onLine origin l'"
  define goal3 where 
    goal3: "goal3 \<equiv> accPoint origin (applyToSet f wl)"
  define subgoal4a where 
    subgoal4a: "subgoal4a \<equiv> (\<lambda> p' . onLine p' l')"
  define subgoal4b where 
    subgoal4b: "subgoal4b \<equiv> (\<lambda> p' . p' \<noteq> origin)"
  define subgoal4c1 where 
    subgoal4c1: "subgoal4c1 \<equiv> (\<lambda> p' d e . 
      (\<forall> y' \<in> (applyToSet f wl) . (y' within d of origin) \<and> (y' \<noteq> origin) 
     \<longrightarrow> (\<exists>r. (onLine r (lineJoining origin y')) \<and> (r within e of p'))))"
  define subgoal4c where 
    subgoal4c: "subgoal4c \<equiv> (\<lambda> p' .\<forall>e>0. \<exists>d>0 . subgoal4c1 p' d e)"
  define goal4 where 
    goal4: "goal4 \<equiv> (\<exists>p'. (subgoal4a p') \<and> (subgoal4b p') \<and> (subgoal4c p'))"

  have GOAL: "goal1 \<and> goal2 \<and> goal3 \<and> goal4 
    \<longrightarrow> tangentLine l' (applyToSet f wl) origin"
    using goal1 goal2 goal3 goal4 subgoal4a subgoal4b subgoal4c1 subgoal4c           
    by force

  (* A is affine *)
  have affA: "affine A" using affapp by auto
  then obtain T L where TL: "translation T \<and> linear L \<and> A=T\<circ>L" by auto
  then obtain t where t: "\<forall>u. T u = (u \<oplus> t)" by auto
  define Tinv where Tinv: "Tinv = mkTranslation (origin \<ominus> t)"
  hence transTinv: "translation Tinv" using lemMkTrans by blast

  (* l is a line *)
  have linel: "isLine l" using tgt by auto

  (* l' is a line *)
  hence linel': "isLine l'" 
    using affA affline lemAffineOfLineIsLine
    by auto

  (* f is a function *)
  have funcF: "isFunction f" using affapp by auto

  (* A x = f x *)
  have A00: "A origin = origin" 
      using lemAffineEqualAtBase[of "f" "A" "origin"] affapp f00 
      by auto

  have "A origin = ((L origin) \<oplus> t)" using TL t by auto
  also have "... = (origin \<oplus> t)" using TL by auto
  finally have "origin = t" using A00 by auto
  hence "\<forall>p. T p = p" using t by auto
  hence "T = id" by auto
  hence "A = L" using TL by auto

  (* A is linear *)
  hence linA: "linear A" using TL by auto


  (* (invFunc f) cts at x' *)
  have "((invFunc f) origin origin) 
           \<and> (\<forall>x . ((invFunc f) origin x) \<longrightarrow> (\<forall>\<epsilon>>0. \<exists>\<delta>>0. 
          (applyToSet (invFunc f) (ball origin \<delta>)) \<subseteq> ball x \<epsilon>))"
    using f00 ctsf'0 by auto
  hence ctsfinv: "(\<forall>\<epsilon>>0. \<exists>\<delta>>0. 
          (applyToSet (invFunc f) (ball origin \<delta>)) \<subseteq> ball origin \<epsilon>)"
    by blast
 

  (* A is continuous everywhere *)
  have ctsA: "\<forall> x. \<forall>\<epsilon>>0. \<exists>\<delta>>0 . \<forall>p. 
          (p within \<delta> of x) \<longrightarrow> ((A p) within \<epsilon> of (A x))"
    using affA lemAffineContinuity by auto

  (* assumption 1 *)
  have tgt1: "origin \<in> wl" using tgt by auto
  have tgt2: "onLine origin l" using tgt by auto
  have tgt3: "\<forall> \<epsilon> > 0. \<exists> q \<in> wl. (origin \<noteq> q) \<and> (inBall q \<epsilon> origin)" 
    using tgt by auto


  (* sublemma4 *)
  have sub4: "(\<exists>\<delta>>0. \<forall>p. (p within \<delta> of origin) 
                       \<longrightarrow> (definedAt f p)) \<and> (cts f origin)"
    using affapp sublemma4[of "f" "A" "origin"] by auto

  (* f is continuous at x *)
  hence ctsfx: "(\<forall>\<epsilon>>0. \<exists>\<delta>>0. (applyToSet f (ball origin \<delta>)) \<subseteq> ball origin \<epsilon>)"
    using f00 by auto

  (* domain of definition *)
  obtain ddef where ddef: "(ddef > 0) \<and>
                              (\<forall>p. (p within ddef of origin) \<longrightarrow> (definedAt f p))"
    using sub4 by auto


  (* rtp 1: y \<in> f[wl] *)
  have rtp1: "goal1" using tgt1 f00 goal1 by auto

  (* rtp 2: onLine y l' *)
  have l'_from_l: "l' = applyToSet (asFunc A) l" 
   using tgt affline lemAffineOfLineIsLine by auto
  have "(asFunc A) origin origin" using linA by auto
  hence rtp2: "goal2" using l'_from_l tgt2 affline goal2 by auto                                                 

  (* rtp 3: y is an accumulation point of f[wl] *)
  (* "\<forall>\<epsilon>>0. \<exists>y' \<in> (applyToSet f) wl) . (x' \<noteq> y') \<and> (y' within \<epsilon> of x')" *)
  { fix e
    assume epos: "e > 0"
    then obtain dd' 
      where dd': "(dd' > 0) \<and> ((applyToSet f (ball origin dd')) \<subseteq> ball origin e)"
      using ctsfx by auto

    define dd where dd: "dd  = min dd' ddef"
    hence ddpos: "dd > 0" using dd' ddef by simp
    then obtain q where q: "(q \<in> wl) \<and> (origin \<noteq> q) \<and> (q within dd of origin)"
      using tgt3 by auto

    have "dd \<le> ddef" using dd by auto
    hence "q within ddef of origin" 
      using ddpos q lemBallInBall[of "q" "origin" "dd" "ddef"] by auto
    then obtain q' where q': "(f q q')" using ddef by auto 

    hence fact3a: "q' \<in> (applyToSet f) wl" using q by auto

    have "q \<noteq> origin" using q by auto
    hence fact3b: "q' \<noteq> origin" using injf q' f00 by auto

    have "dd \<le> dd'" using dd by auto
    hence "q \<in> ball origin dd'" 
      using q lemBallInBall[of "q" "origin" "dd" "dd'"] ddpos by auto
    hence "q' \<in> ball origin e" using dd' q' by auto
    hence fact3c: "q' within e of origin" using lemSep2Symmetry by auto
    hence "\<exists> y' \<in> ((applyToSet f) wl) . (origin \<noteq> y') \<and> (y' within e of origin)"
      using fact3a fact3b q' by auto
  }
  hence rtp3: "goal3" using goal3 by auto


  (* rtp 4: 
    "\<exists> p'. ( ((onLine p' l') \<and> (p' \<noteq> x')) \<and>
      (\<forall> \<epsilon> > 0 .  \<exists> \<delta> > 0 . \<forall> y' . (
        ( (y' \<in> f[wl]) \<and> (y' within \<delta> of x') \<and> (x' \<noteq> y') )
        \<longrightarrow>
        ( \<exists> r' . ((onLine r' (lineJoining x' y')) \<and> (r' within \<epsilon> of p'))))
      ))"
  *)
      
  obtain P where P: "(onLine P l) \<and> (P \<noteq> origin) \<and>
      (\<forall> \<epsilon> > 0 .  \<exists> \<delta> > 0 . \<forall> y \<in> wl. (
        ( (y within \<delta> of origin) \<and> (y \<noteq> origin) )
        \<longrightarrow>
        ( \<exists> r . ((onLine r (lineJoining origin y)) \<and> (r within \<epsilon> of P)))))"
    using tgt by auto

  define nP where nP: "nP = norm P"
  have "P \<noteq> origin" using P by auto
  hence nPpos: "nP > 0" using P nP lemNotOriginImpliesPositiveNorm[of "P"]
    by auto
  define a where a: "a = 1/nP"
  hence apos: "a > 0" using nPpos by auto

  (* Construct p suitable for application of sublemma 3 *)
  define p where p: "p = (a\<otimes>P)"
  { assume "p = origin"
    hence "(a\<otimes>P) = origin" using p by auto
    hence "(nP\<otimes>(a\<otimes>P)) = (nP\<otimes>origin)" by simp
    hence "P = origin" using a apos lemScaleAssoc by auto
  }
  hence p_not_0: "p \<noteq> origin" using P by auto

  define p' where p': "p' = A p"
  obtain A' where A': "(affine A') \<and> ((affine A') \<and> (\<forall> p q . A p = q \<longleftrightarrow> A' q = p))" 
    using affapp lemInverseAffine[of "A"] by auto
  hence "A' origin = origin \<and> A' p' = p" using A00 p' by blast
  hence p'_not_0: "p' \<noteq> origin" using p_not_0 by auto


  have "(onLine origin l) \<and> (onLine P l) \<and> (origin \<noteq> P)" using P tgt2 by auto
  hence l_is_0P: "l = lineJoining origin P"
    using lemLineAndPoints[of "origin" "P" "l"] by auto

  have "p = (origin \<oplus> (a\<otimes>(P \<ominus> origin)))" using p by auto
  hence "onLine p (lineJoining origin P)" by blast

  hence p_on_l: "onLine p l" using l_is_0P by auto
  moreover have "l' = applyToSet (asFunc A) l \<and> isLine l'"
    using lemAffineOfLineIsLine [of "l" "A" "l'"]  
          affline
    by auto
  ultimately have p'_on_l': "onLine p' l'" using  p_on_l p' by auto

  have "p = (a\<otimes>P)" using p by auto
  hence "norm2 p = (sqr a)*(norm2 P)" 
    using lemNorm2OfScaled[of "a" "P"] by auto
  hence "norm2 p = (sqr a)*(sqr nP)"
    using nP lemNormSqrIsNorm2[of "P"] by auto
  hence np1: "norm2 p = 1" using a nPpos apos mult_assoc mult_commute by auto


  (* Sublemma3 applies *)
  have "(onLine p l) \<and> (norm2 p = 1) \<and> (tangentLine l wl origin)" 
    using p_on_l np1 tgt by auto
  hence sub3: "\<forall> \<epsilon> > 0 . \<exists> \<delta> > 0 . \<forall> y ny . (
       ((y within \<delta> of origin) \<and> (y \<noteq> origin) \<and> (y \<in> wl) \<and> (norm y = ny))
        \<longrightarrow>
       ( (((1/ny)\<otimes>y) within \<epsilon> of p) \<or> (((-1/ny)\<otimes>y) within \<epsilon> of p)))"
    using sublemma3[of "l" "p" "wl"]
    by auto



  { fix e
    assume epos: "e > 0"
    define e1 where e1: "e1 = nP * e"
    hence e1pos: "e1 > 0" using nPpos epos by auto
    define e2 where e2: "e2 = e/2"
    hence e2pos: "e2 > 0" using epos by auto

    (* \<odot>  By continuity of A ...  *)
    obtain dctsA0 where "(dctsA0 > 0) \<and> (\<forall>q. 
          (q within dctsA0 of origin) \<longrightarrow> ((A q) within e2 of (A origin)))"
      using ctsA e2pos A00 by blast
    hence dctsA0: "(dctsA0 > 0) \<and> (\<forall>q. 
          (q within dctsA0 of origin) \<longrightarrow> ((A q) within e2 of origin))"
      using A00 by auto

    obtain dctsAp where dctsAp: "(dctsAp > 0) \<and> (\<forall>q. 
          (q within dctsAp of p) \<longrightarrow> ((A q) within e2 of (A p)))"
      using ctsA e2pos by blast

    (* (\<star>)   By sublemma3 ...  *)
    obtain dsub where dsub: "(dsub > 0) \<and> (\<forall> y ny . 
        ((y within dsub of origin) \<and> (y \<noteq> origin) \<and> (y \<in> wl) \<and> (norm y = ny))
            \<longrightarrow>
        (((1/ny)\<otimes>y) within (dctsAp) of p) 
                      \<or> (((-1/ny)\<otimes>y) within (dctsAp) of p))"
      using apos dctsAp sub3 by blast

    (* (\<star>\<star>) By affine approximation *)
    obtain daff where daff: "(daff > 0) \<and> (\<forall> y .
      ( (y within daff of origin)
        \<longrightarrow> 
        ( (definedAt f y) \<and> (\<forall> fy Ay . (f y fy \<and> (asFunc A) y Ay) \<longrightarrow>
         ( sep2 Ay fy ) \<le> (sqr e2) * sep2 y origin )))  ) "
      using e2pos affapp by auto

    define dmin where dmin: "dmin = min dsub daff"
    hence dminsub: "dmin \<le> dsub" by auto
    have  dminaff: "dmin \<le> daff" using dmin by auto
    have  dminpos: "dmin > 0" using dmin dsub daff by auto

    obtain dfinv 
      where dfinv: "(dfinv > 0) 
              \<and> ((applyToSet (invFunc f) (ball origin dfinv)) 
                      \<subseteq> ball origin dmin)"
      using ctsfinv dminpos by auto


    { fix y'
      assume y': "(y' \<in> (applyToSet f wl)) \<and> (y' \<noteq> origin)"
      then obtain y where y: "(f y y') \<and> (y \<in> wl)" by auto

      have y_not_0: "y \<noteq> origin" using y y' f00 funcF by auto
      obtain ny where ny: "norm y = ny" by auto

      hence nypos: "ny >0" 
        using y_not_0 lemNotOriginImpliesPositiveNorm[of "y"] ny by auto

      define p1 where p1: "p1 = ((1/ny)\<otimes>y')"
      define q1 where q1: "q1 = (A ((1/ny)\<otimes>y))"
      define p2 where p2: "p2 = ((-1/ny)\<otimes>y')"
      define q2 where q2: "q2 = (A ((-1/ny)\<otimes>y))"
      define r  where r:  "r  = (A p)"

      assume y'2: "(y' within dfinv of origin)"      
      hence "y' \<in> ball origin dfinv" using lemSep2Symmetry by auto
      hence "y \<in> applyToSet (invFunc f) (ball origin dfinv)" using y by auto
      hence ydmin: "y \<in> ball origin dmin" using dfinv by auto

      (* use dsub *)
      have "dmin \<le> dsub" using dmin by auto
      hence ydsub: "y within dsub of origin"
        using lemBallInBall[of "y" "origin" "dmin" "dsub"] dminpos ydmin 
        by auto

      hence "(y within dsub of origin) \<and> (y \<noteq> origin) 
                                  \<and> (y \<in> wl) \<and> (norm y = ny)"
        using ydsub y_not_0 y ny by force
      hence cases: "(((1/ny)\<otimes>y) within dctsAp of p) 
                              \<or> (((-1/ny)\<otimes>y) within dctsAp of p)"
        using dsub by blast


      hence casesA: "(q1 within e2 of r) \<or> (q2 within e2 of r)"
        using dctsAp q1 q2 r by auto

      (* use daff *)
      have "dmin \<le> daff" using dmin by auto
      hence "y within daff of origin" 
        using lemBallInBall[of "y" "origin" "dmin" "daff"] dminpos ydmin
        by auto
      hence "(definedAt f y) \<and> (\<forall> fy Ay . (f y fy \<and> (asFunc A) y Ay) \<longrightarrow>
         ( sep2 Ay fy ) \<le> (sqr e2) * sep2 y origin)"
        using daff by auto
      hence "sep2 (A y) y' \<le> (sqr ny) * (sqr e2)"  
        using y ny lemNormSqrIsNorm2 mult_commute by auto
      hence "sep2 (A y) y' \<le> sqr (ny*e2)" 
        using lemSqrMult[of "ny" "e2"] by auto
      hence "sep2 ((1/ny)\<otimes>(A y)) ((1/ny)\<otimes>y') \<le> sqr e2"
        using nypos 
              lemScaleBallAndBoundary[of "A y" "y'" "ny*e2" "1/ny"]             
        by auto
      hence part1: "sep2 (A ((1/ny)\<otimes>y)) ((1/ny)\<otimes>y') \<le> sqr e2"
        using linA lemLinearProps[of "A" "1/ny" "y"] by auto


      { (* case 1 *)
        assume case1: "q1 within e2 of r"
  
        have   pq: "sep2 p1 q1 \<le> sqr e2"
          using part1 lemSep2Symmetry[of "p1" "q1"] p1 q1 by auto
        hence  rq: "sep2 r q1 < sqr e2" using case1 lemSep2Symmetry r q1 by auto

        { define pp where pp: "pp = (q1\<ominus>p1)"
          define qq where qq: "qq = (r\<ominus>q1)"
          have tri1: "axTriangleInequality pp qq" using AxTriangleInequality by simp
          hence "r within (e2 + e2) of p1" 
            using pp qq pq rq e2pos lemDistancesAddStrictR[of "q1" "p1" "r"]
            by blast
        }
        hence done1: "p1 within e of r" using lemSep2Symmetry lemSumOfTwoHalves e2 by auto 
  
        have "p1 = (origin \<oplus> ((1/ny)\<otimes>(y'\<ominus>origin)))" using p1 by auto
        hence "onLine p1 (lineJoining origin y')" by fastforce
        hence "onLine p1 (lineJoining origin y') \<and> (p1 within e of p')"
          using p' r done1 by blast
      }
      hence case1: "(q1 within e2 of r) 
                      \<longrightarrow> (onLine p1 (lineJoining origin y') \<and> (p1 within e of p'))"
        by blast
  
      {  (* case 2 *)
        assume case2: "q2 within e2 of r"
  
        have "p2 = (((-1)*(1/ny))\<otimes>y')" using p2 by auto
        hence p2': "p2 = ((-1)\<otimes>p1)" using lemScaleAssoc[of "-1" "1/ny" "y'"] p1 by auto
        have  "q2 = (A (((-1)*(1/ny))\<otimes>y))" using q2 by auto
        hence q2q1: "q2 = ((-1)\<otimes>q1)" 
          using linA lemLinearProps[of "A" "-1" "((1/ny)\<otimes>y)"] q1
          by auto
        hence "sep2 p2 q2 = sep2 p1 q1" using lemScaleSep2[of "-1"] p2' by auto        
        hence   pq: "sep2 p2 q2 \<le> sqr e2"
          using part1 lemSep2Symmetry[of "p1" "q1"] p1 q1 by auto
  
        hence  rq: "sep2 r q2 < sqr e2" using case2 lemSep2Symmetry r q2 by auto

        { define pp where pp: "pp = (q2\<ominus>p2)"
          define qq where qq: "qq = (r\<ominus>q2)"
          have tri2: "axTriangleInequality pp qq" using AxTriangleInequality by simp
          hence "r within (e2 + e2) of p2" 
            using pp qq pq rq e2pos lemDistancesAddStrictR[of "q2" "p2" "r"]
            by blast
        }
        hence "p2 within e of r" using lemSep2Symmetry lemSumOfTwoHalves e2 by auto 
        hence done2: "p2 within e of p'" using  r p' by simp
  
        have "p2 = (origin \<oplus> ((-1/ny)\<otimes>(y'\<ominus>origin)))" using p2 by auto
        hence "onLine p2 (lineJoining origin y')" by blast
        hence "onLine p2 (lineJoining origin y') \<and> (p2 within e of p')"
          using p' done2 by blast
      }
      hence case2: "(q2 within e2 of r) 
         \<longrightarrow> (onLine p2 (lineJoining origin y') \<and> (p2 within e of p'))"
        by blast
  
      hence "\<exists>r. (onLine r (lineJoining origin y')) \<and> (r within e of p')"
        using casesA case1 case2 by blast
    
      hence "( (y' \<in> applyToSet f wl) \<and> (y' within dfinv of origin) \<and> (y' \<noteq> origin) )
       \<longrightarrow> (\<exists>r. (onLine r (lineJoining origin y')) \<and> (r within e of p'))" 
        using dfinv by blast

    }
    hence "subgoal4c1 p' dfinv e" using dfinv subgoal4c1 by blast
    hence "\<exists>d>0 . subgoal4c1 p' d e" using dfinv by auto
  }
  hence "\<forall>e>0 . \<exists>d>0 . subgoal4c1 p' d e" by auto
  hence "subgoal4c p'" using subgoal4c subgoal4c1 by force
  
  hence "(subgoal4a p') \<and> (subgoal4b p') \<and> (subgoal4c p')"
    using p'_not_0 p'_on_l' subgoal4a subgoal4b by auto

  hence rtp4: "goal4" using goal4 subgoal4a subgoal4b subgoal4c by blast

  (* And finally ... *)
  thus ?thesis using rtp1 rtp2 rtp3 GOAL by fastforce 
qed





lemma lemMainLemmaOrigin:
  assumes tgtx:     "tangentLine l wl x"
and       injf:     "injective f"
and       affappx:  "affineApprox A f x"
and       fx0:      "f x origin"
and       ctsf'0:   "cts (invFunc f) origin"
and       affline:  "applyAffineToLine A l l'"
shows     "tangentLine l' (applyToSet f wl) origin"
proof -

  define T where T: "T = mkTranslation x"
  hence transT: "translation T" using lemMkTrans by blast
  define T' where T': "T' = mkTranslation (origin \<ominus> x)"
  hence transT': "translation T'" using lemMkTrans by blast

  have TT': "\<forall> p q . T p = q  \<longleftrightarrow>  T' q = p" using T T' by auto


  define g where g: "g = composeRel f (asFunc T)"

  define l0 where l0: "l0 = applyToSet (asFunc T') l"
  define wl0 where wl0: "wl0 = applyToSet (asFunc T') wl"
  define A0  where A0: "A0 = A \<circ> T"

  (* have 1: "tangentLine l0 wl0 origin" *)
  have "T' x = origin" using T' by auto
  hence rtp1: "tangentLine l0 wl0 origin"
    using l0 wl0 transT' tgtx lemTangentLineTranslation[of "T'" "x" "wl" "l"]
    by auto

  (* have 2: "injective g" *)
  have rtp2: "injective g" 
    using  transT lemTranslationInjective[of "T"] lemInjOfInjIsInj[of "asFunc T" "f"]  
           injf g
    by blast

  (* have 3: "affineApprox A0 g 0" *)
  have "T' x = origin" using T' by auto
  hence rtp3: "affineApprox A0 g origin" 
    using transT TT'
          lemAffineApproxDomainTranslation[of "T" "f" "A" "x" "T'"]
          affappx g A0
    by auto

  (* have 4: "g origin origin" *)
  have "(T origin = x) \<and> (f x origin)" using T fx0 by auto
  hence "\<exists>x . ((asFunc T) origin x) \<and> (f x origin)" by auto
  hence rtp4: "g origin origin" using g T fx0 by auto 


  (* have 5: "cts (invFunc g) origin" *)
  define h where h: "h = (invFunc (asFunc T))"
  hence invcomp: "composeRel h (invFunc f) = invFunc g" 
    using lemInverseComposition[of "g" "asFunc T" "f"] g by auto

  { fix p r
    have inv1: "invFunc (asFunc T) p r \<longleftrightarrow> (T'\<circ>T) r = T' p" 
      using transT' lemTranslationInjective by auto
    hence"invFunc (asFunc T) p r \<longleftrightarrow> r = T' p"     
      using T T' lemInverseTranslation[of "T" "x" "T'"] by auto
  }
  hence hT: "h = asFunc T'" using h by force
  hence "\<forall>y. cts h y"
    using transT' lemTranslationImpliesAffine[of "T'"]
          lemAffineIsCts[of "T'"] 
    by blast
  hence ctsh: "\<forall>y. (invFunc f) origin y \<longrightarrow> cts h y" by auto

  define g' where g': "g' = composeRel h (invFunc f)"
  hence invg: "g' = invFunc g" using hT invcomp by simp
  have "cts g' origin" 
    using ctsf'0 ctsh lemCtsOfCtsIsCts[of "invFunc f" "origin" "h"] g'
    by auto
  hence rtp5: "cts (invFunc g) origin" using invg by auto


  (* have 6: applyAffToLine A0 l0 l0' *)
  (* 3b: affine A0 *)
  have affA: "affine A" using assms(3) by auto
  hence rtp3b: "affine A0" 
    using lemAffOfAffIsAff[of "T" "A"] lemTranslationImpliesAffine[of "T"]
          A0 affA transT
    by auto
  define l0' where l0': "l0' = applyToSet (asFunc A0) l0"
  hence rtp6: "applyAffineToLine A0 l0 l0'"
    using rtp1 rtp3b lemAffineOfLineIsLine[of "l0" "A0" "l0'"]
    by auto

          
  (* CAN NOW APPLY THE BASIC LEMMA  *)
  (* Isabelle can't cope with this all at once, so do it in two steps *)
  have "(tangentLine l0 wl0 origin) \<longrightarrow> (
               (injective g) \<longrightarrow>
               (affineApprox A0 g origin) \<longrightarrow>
               (g origin origin) \<longrightarrow>
               ((cts (invFunc g) origin) \<longrightarrow>
               ((applyAffineToLine A0 l0 l0') \<longrightarrow>
               (tangentLine l0' (applyToSet g wl0) origin))))"
    using lemMainLemmaBasic[of "wl0" "l0" "g" "A0" "l0'"]
    by blast

  hence basic: "(tangentLine l0' (applyToSet g wl0) origin)"
    using rtp1 rtp2 rtp3 rtp4 rtp5 rtp6 by meson

(*
GOAL: "tangentLine l' (applyToSet f wl) x"
*)

 (* Rewrite l0'  *)
  obtain A' where A': "\<forall> p q . A p = q \<longleftrightarrow> A' q = p"
    using affappx by metis

  have ToT': "T \<circ> T' = id" using TT' by auto
  have "A0 \<circ> T' = (A \<circ> T) \<circ> T'" using A0 by auto
  also have "... = A \<circ> (T \<circ> T')" by auto
  finally have A0T': "A0 \<circ> T' = A" using ToT' by auto

  have "l0' = applyToSet (asFunc (A0 \<circ> T')) l" using l0 l0' by auto
  hence "l0' = applyToSet (asFunc A) l" using A0T' by auto
  hence l0'l: "l0' = l'" using tgtx affline lemAffineOfLineIsLine[of "l" "A" "l'"] by auto
  
  (* Rewrite (applyToSet g wl0) *)
  have "applyToSet g wl0 = applyToSet (composeRel f (asFunc (T\<circ>T'))) wl" using wl0 g by auto
  also have "... = applyToSet (composeRel f (asFunc id)) wl" using ToT' by auto
  also have "... = applyToSet f wl" by auto
  finally have "applyToSet g wl0 = applyToSet f wl" by auto

  hence "tangentLine l' (applyToSet f wl) origin" using basic l0'l by auto  
  thus ?thesis by auto
qed



lemma lemMainLemma:
  assumes tgtx:     "tangentLine l wl x"
and       injf:     "injective f"
and       affappx:  "affineApprox A f x"
and       fxy:      "f x y"
and       ctsf'y:   "cts (invFunc f) y"
and       affline:  "applyAffineToLine A l l'"
shows     "tangentLine l' (applyToSet f wl) y"
proof -
  define Ty where Ty: "Ty = mkTranslation y"
  hence transTy: "translation Ty" using lemMkTrans by auto
  define Ty' where Ty': "Ty' = mkTranslation (origin \<ominus> y)"
  hence transTy': "translation Ty'" using lemMkTrans by blast
  define g where g: "g = composeRel (asFunc Ty') f"
  define Ay where Ay: "Ay = Ty' \<circ> A"

  define ly' where ly': "ly' = applyToSet (asFunc Ty') l'"

  have lineL: "isLine l" using tgtx by auto
  have affA: "affine A" using affappx by auto

  have TT': "\<forall> p q . Ty p = q  \<longleftrightarrow>  Ty' q = p" using Ty Ty' by auto

  (* 1 tgtx:     "tangentLine l wl x" *)
  have rtp1: "tangentLine l wl x" by (rule tgtx)

  (* 2 injf:     "injective f" *)
  have rtp2: "injective g" 
    using  transTy' lemTranslationInjective[of "Ty'"] lemInjOfInjIsInj[of "f" "asFunc Ty'"]  
           injf g
    by blast

  (* 3 affappx:  "affineApprox A f x" *)
  have "(translation Ty') \<longrightarrow> (affineApprox A f x) 
           \<longrightarrow> (affineApprox (Ty' \<circ> A) (composeRel (asFunc Ty') f) x)"
    using lemAffineApproxRangeTranslation[of "Ty'" "f" "A" "x"]
    by blast
  hence rtp3: "affineApprox Ay g x" using Ay g transTy' affappx by meson


  (* 4 fxy:      "f x y" *)
  have rtp4: "g x origin" using g Ty' fxy by auto


  (* 5 ctsf'y:   "cts (invFunc f) y" *)
  define f' where f': "f' = invFunc f"
  define h where h: "h = (invFunc (asFunc Ty'))"
  define g' where g': "g' = invFunc g"

  hence invcomp: "g' = composeRel f' h" 
    using lemInverseComposition g f' h by auto

  { fix p r
    have inv1: "invFunc (asFunc Ty') p r \<longleftrightarrow> (Ty\<circ>Ty') r = Ty p" 
      using transTy lemTranslationInjective by auto
    hence "invFunc (asFunc Ty') p r  \<longleftrightarrow> r = Ty p" using Ty Ty' by auto
  }
  hence hT: "h = asFunc Ty" using h by force

  hence ctsh0: "cts h origin"
    using transTy lemTranslationImpliesAffine[of "Ty"]
          lemAffineIsCts[of "Ty"] 
    by blast

  { fix p
    assume "h origin p"
    hence "(asFunc Ty) origin p" using hT by auto
    hence "p = y" using Ty by auto
    hence "cts (invFunc f) p" using ctsf'y by auto
  }
  hence ctsf: "\<forall>p. h origin p \<longrightarrow> cts f' p" using f' by auto

  have "cts g' origin"
    using invcomp ctsh0 ctsf lemCtsOfCtsIsCts[of "h" "origin" "f'"]
    by blast

  hence rtp5: "cts (invFunc g) origin" using g' by auto

  (* 6 affline:  "applyAffineToLine A l l'" *)
  have affAy: "affine Ay" 
    using affA lemTranslationImpliesAffine[of "Ty'"] transTy'
          lemAffOfAffIsAff[of "A" "Ty'"] Ay
    by auto
  have "l' = applyToSet (asFunc A) l" 
    using affline lineL affA lemAffineOfLineIsLine[of "l" "A" "l'"] by auto
  hence "ly' = applyToSet (asFunc Ay) l" using ly' Ay by auto
  hence rtp6: "applyAffineToLine Ay l ly'" 
    using lineL affAy lemAffineOfLineIsLine[of "l" "Ay" "ly'"] 
    by auto

  (* GOAL:    "tangentLine l' (applyToSet f wl) y" *)
  have "(tangentLine l wl x) \<longrightarrow>
        (injective g) \<longrightarrow>
        (affineApprox Ay g x) \<longrightarrow>
        (g x origin) \<longrightarrow>
        (cts (invFunc g) origin) \<longrightarrow>
        (applyAffineToLine Ay l ly') \<longrightarrow>
        (tangentLine ly' (applyToSet g wl) origin)"
    using lemMainLemmaOrigin[of "x" "wl" "l" "g" "Ay" "ly'"]
    by fastforce

  hence tgt': "tangentLine ly' (applyToSet g wl) origin"
    using rtp1 rtp2 rtp3 rtp4 rtp5 rtp6 by meson

  define wl' where wl': "wl' = (applyToSet g wl)"
  define Term1 where Term1: "Term1 = applyToSet (asFunc Ty) ly'"
  define Term2 where Term2: "Term2 = applyToSet (asFunc Ty) wl'"
  define Term3 where Term3: "Term3 = Ty origin"

  have "tangentLine ly' wl' origin" using tgt' wl' by auto

  hence goal: "tangentLine (applyToSet (asFunc Ty) ly')
                     (applyToSet (asFunc Ty) wl')
                     (Ty origin)"
    using transTy lemTangentLineTranslation[of "Ty" "origin" "wl'" "ly'"]
    by fastforce
  hence goal: "tangentLine Term1 Term2 Term3" 
    using Term1 Term2 Term3 by auto

  have ToT': "Ty \<circ> Ty' = id" using TT' by auto
  have "Term1 = applyToSet (asFunc Ty) (applyToSet (asFunc Ty') l')"
    using ly' Term1 by auto
  also have "... = applyToSet (asFunc (Ty \<circ> Ty')) l'" by auto
  also have "... = applyToSet (asFunc id) l'" using ToT' by auto
  finally have term1: "Term1 = l'" by auto

  have "composeRel (asFunc Ty) g = composeRel (asFunc Ty) (composeRel (asFunc Ty') f)" 
    using g by auto
  also have "... = composeRel (asFunc (Ty\<circ>Ty')) f" by auto
  also have "... = composeRel (asFunc id) f" using ToT' by auto
  finally have Tog: "composeRel (asFunc Ty) g = f" by auto

  have "Term2 = applyToSet (asFunc Ty) (applyToSet g wl)"
    using wl' Term2 by auto
  also have "... = applyToSet (composeRel (asFunc Ty) g) wl" by auto
  finally have term2: "Term2 = applyToSet f wl" using Tog by auto

  have term3: "Term3 = y" using Ty Term3 by auto

  thus ?thesis using goal term1 term2 term3
    by fastforce

qed



end (* of class MainLemma *)

end (* of theory MainLemma *)
