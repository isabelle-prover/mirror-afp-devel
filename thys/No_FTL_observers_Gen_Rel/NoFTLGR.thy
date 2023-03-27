(*
   NoFTLGR.thy
   Author: Mike Stannett
   m.stannett@sheffield.ac.uk
   File created: Aug 2020
   Proof completed: Jan 2023
   Refactored: Feb 2023
*)

section \<open> NoFTLGR \<close>

text \<open>This theory completes the proof of NoFTLGR.\<close>

theory NoFTLGR
  imports ObserverConeLemma AffineConeLemma
begin

class NoFTLGR = ObserverConeLemma + AffineConeLemma
begin


(* ********************************************************************** *)
(* ********************************************************************** *)
(* *********               PROOF OF NoFTLGR                    ********** *)
(* ********************************************************************** *)
(* ********************************************************************** *)

text \<open>The theorem says: if observer m encounters observer k (so that they
are both present at the same spacetime point x), then k is moving at sub-light
speed relative to m. In other words, no observer ever encounters another 
observer who appears to be moving at or above lightspeed.\<close>


theorem lemNoFTLGR:
  assumes ass1: "x \<in> wline m m \<inter> wline m k"
and       ass2: "tl l m k x"
and       ass3: "v \<in> lineVelocity l"
and       ass4: "\<exists> p . (p \<noteq> x) \<and> (p \<in> l)"
shows     "(lineSlopeFinite l) \<and> (sNorm2 v < 1)"
proof -

  define s where s: "s = (wline k k)"

  (* statement labels refer to conditions in lemPresentation *)
  have "axEventMinus m k x" using AxEventMinus by force 
  hence "(\<exists> q . \<forall> b . ( (m sees b at x) \<longleftrightarrow> (k sees b at q)))"
    using ass1 by blast
  then obtain y where y: "\<forall> b . ( (m sees b at x) \<longleftrightarrow> (k sees b at y))" by auto
  hence mkxy: "wvtFunc m k x y" using ass1 by auto

  have "axDiff m k x" using AxDiff by simp
  hence "\<exists> A . (affineApprox A (wvtFunc m k) x )" using mkxy by fast
  then obtain A where A: "affineApprox A (wvtFunc m k) x" by auto

  hence affA: "affine A" by auto
  have lineL: "isLine l" using ass2 by auto

  define l' where l': "l' = applyToSet (asFunc A) l"

  hence lineL': "isLine l'" 
    using lineL affA lemAffineOfLineIsLine[of "l" "A" "l'"]
    by auto

  have tgtl': "tangentLine l' s y"
  proof -
    define g1 where g1: "g1 \<equiv> x \<in> wline m k"
    define g2 where g2: "g2 \<equiv> tangentLine l (wline m k) x"
    define g3 where g3: "g3 \<equiv> affineApprox A (wvtFunc m k) x"
    define g4 where g4: "g4 \<equiv> wvtFunc m k x y"
    define g5 where g5: "g5 \<equiv> applyAffineToLine A l l'" 
    define g6 where g6: "g6 \<equiv> tangentLine l' (wline k k) y"

    have "x \<in> wline m k
             \<longrightarrow> tangentLine l (wline m k) x
             \<longrightarrow> affineApprox A (wvtFunc m k) x
             \<longrightarrow> wvtFunc m k x y
             \<longrightarrow> applyAffineToLine A l l'
             \<longrightarrow> tangentLine l' (wline k k) y"
    using lemPresentation[of "x" "m" "k" "l" "k" "A" "y" "l'"] 
    by blast

    hence pres: "g1 \<longrightarrow> g2 \<longrightarrow> g3 \<longrightarrow> g4 \<longrightarrow> g5 \<longrightarrow> g6" 
      using g1 g2 g3 g4 g5 g6 by fastforce

    have 1: g1 using ass1 g1 by auto
    have 2: g2 using ass2 g2 by fast
    have 3: g3 using A g3 by fast
    have 4: g4 using mkxy g4 by fast
    have 5: g5 using 1 lineL l' affA lemAffineOfLineIsLine[of "l" "A" "l'"] g5 
      by auto
  
    hence g6   using 1 2 3 4 5 pres by meson
    thus ?thesis using s g6 by auto
  qed

  have ykk: "y \<in> wline k k" using ass1 y by auto

  (* l' = timeAxis *)
  have c2: "l' = timeAxis"
  proof -
    have "tl l' k k y" using tgtl' l' s by auto
    thus ?thesis
      using lemSelfTangentIsTimeAxis[of "y" "k" "l'"] by auto
  qed

  (* y is on the timeAxis *)
  have yOnAxis: "onLine y timeAxis"
    using lemTimeAxisIsLine ykk AxSelfMinus by blast

  (* y is on l' *)
  hence yOnl': "onLine y l'" using c2 by auto

  (* have cone k y is regular *)
  have "\<forall> p . cone k y p \<longleftrightarrow> regularCone y p" 
    using ykk lemProposition1[of "y" "k"] by auto
  hence ycone: "coneSet k y = regularConeSet y" by auto

  (* Page 34: bottom - "Also cone m x is regular" *)
  have xcone: "coneSet m x = regularConeSet x"
  proof -
    have "x \<in> wline m m" using ass1 by auto
    hence "\<forall> p . cone m x p \<longleftrightarrow> regularCone x p" 
      using lemProposition1[of "x" "m"] by auto
    thus ?thesis by auto
  qed
    
  (* Page 34: get a new affine map A~kmy *)
  have assm1': "y \<in> wline k k \<inter> wline k m"
    using ass1 y by auto
  have "axEventMinus k m y" using AxEventMinus by force 
  hence "(\<exists> q . \<forall> b . ( (k sees b at y) \<longleftrightarrow> (m sees b at q)))"
    using assm1' by blast
  then obtain z where z: "\<forall> b . ( (k sees b at y) \<longleftrightarrow> (m sees b at z))" by auto
  hence kmyz: "wvtFunc k m y z" using assm1' by auto

  have "axDiff k m y" using AxDiff by simp
  hence "\<exists> A . (affineApprox A (wvtFunc k m) y )" using kmyz by fast
  then obtain Akmy where Akmy: "affineApprox Akmy (wvtFunc k m) y" by auto

  hence affA': "affine Akmy" by auto
  have  invA': "invertible Akmy" using Akmy by auto

  then obtain Amkx where 
    Amkx: "(affine Amkx) \<and> (\<forall> p q . Akmy p = q \<longleftrightarrow> Amkx q = p)"    
    using lemInverseAffine[of "Akmy"] affA' by blast


  (* Page 35 *)
  have "wvtFunc m k x y" using mkxy by auto
  hence kmyx: "wvtFunc k m y x" by auto
  hence xisz: "x = z" using kmyz lemWVTImpliesFunction by blast

  moreover have "z = Akmy y" 
    using lemAffineEqualAtBase[of "wvtFunc k m" "Akmy" "y"] Akmy kmyz
    by blast      
  ultimately have xA'y: "x = Akmy y" by auto

  (* 35a: Akmy[cone k y] = cone m x *)
  hence p35a: "applyToSet (asFunc Akmy) (coneSet k y) \<subseteq> coneSet m x"
    using Akmy lemProposition2[of "k" "m" "Akmy" "y"]
    by simp

  (* Express using regular cones and extend to equality *)
  have p35aRegular: "applyToSet (asFunc Akmy) (regularConeSet y) = regularConeSet x"
  proof -
    have "applyToSet (asFunc Akmy) (regularConeSet y) \<subseteq> coneSet m x"
      using ycone p35a by auto
    hence l2r: "applyToSet (asFunc Akmy) (regularConeSet y) \<subseteq> regularConeSet x"
      using xcone by auto

    have r2l: "regularConeSet x \<subseteq> applyToSet (asFunc Akmy) (regularConeSet y)"
    proof -
      { assume converse: "\<not>(regularConeSet x \<subseteq> applyToSet (asFunc Akmy) (regularConeSet y))"
        then obtain z where 
          z: "z \<in> regularConeSet x \<and> \<not>(z \<in> applyToSet (asFunc Akmy) (regularConeSet y))"
          by blast
        define z' where z': "z' = Amkx z"

        have z'NotOnCone:"\<not>(z' \<in> regularConeSet y)" 
        proof -
          { assume conv: "z' \<in> regularConeSet y"
            have "Akmy z' = z" using Amkx z' by auto
            hence "(asFunc Akmy) z' z" by auto
            hence "\<exists> z' \<in> regularConeSet y . (asFunc Akmy) z' z" using conv by blast
            hence "z \<in> applyToSet (asFunc Akmy) (regularConeSet y)" by auto
            hence "False" using z by blast
          }
          thus ?thesis by blast
        qed

        hence "\<not> (regularCone y z')" by auto
        then obtain l where
          l: "(onLine z' l) \<and> (\<not> (y \<in> l)) \<and> (card (l \<inter> (regularConeSet y)) = 2)"
          using lemConeLemma2[of "z'" "y"] by blast
        then obtain p q where
          pq: "(p \<noteq> q) \<and> p \<in> (l \<inter> (regularConeSet y)) \<and> q \<in> (l \<inter> (regularConeSet y))" 
          using lemElementsOfSet2[of "l \<inter> (regularConeSet y)"] by blast

        have lineL: "isLine l" using l by auto

        define p' where p': "p' = Akmy p"
        define q' where q': "q' = Akmy q"
        have p'inv: "Amkx p' = p" using Amkx p' by auto
        have q'inv: "Amkx q' = q" using Amkx q' by auto

        have pOnCone: "p \<in> regularConeSet y" using pq by blast
        moreover have "(asFunc Akmy) p p'" using p' by auto
        ultimately have "\<exists> p \<in> regularConeSet y . (asFunc Akmy) p p'" by blast
        hence "p' \<in> applyToSet (asFunc Akmy) (regularConeSet y)" by auto
        hence Ap: "p' \<in> regularConeSet x" using l2r by blast
            
        have qOnCone: "q \<in> regularConeSet y" using pq by blast
        moreover have "(asFunc Akmy) q q'" using q' by auto
        ultimately have "\<exists> q \<in> regularConeSet y . (asFunc Akmy) q q'" by blast
        hence "q' \<in> applyToSet (asFunc Akmy) (regularConeSet y)" by auto
        hence Aq: "q' \<in> regularConeSet x" using l2r by blast

        have p'q': "p' \<noteq> q'" 
        proof -
          { assume "p' = q'"
            hence "Akmy p' = Akmy q'" by auto
            hence "p = q" by (metis p' q' Amkx)
            hence "False" using pq by simp
          }
          thus ?thesis by auto
        qed

        have p'z: "p' \<noteq> z" 
        proof -
          { assume "p' = z"
            hence "p = z'" using p'inv z' by auto
            hence "False" using pOnCone z'NotOnCone by auto
          }
          thus ?thesis by auto
        qed
        
        have q'z: "q' \<noteq> z" 
        proof -
          { assume "q' = z"
            hence "q = z'" using q'inv z' by auto
            hence "False" using qOnCone z'NotOnCone by auto
          }
          thus ?thesis by auto
        qed

        define l' where l': "l' = applyToSet (asFunc Akmy) l"
        have "affine Akmy" using Akmy by auto
        hence All': "applyAffineToLine Akmy l l'" 
          using l' lineL lemAffineOfLineIsLine[of "l" "Akmy" "l'"]
          by blast 

        have lineL': "isLine l'" using All' by auto


        define S where S: "S = l' \<inter> regularConeSet x"

        have xNotInL': "\<not> (x \<in> l')"
        proof -
          { assume "x \<in> l'" 
            hence "\<exists> y1 \<in> l . (asFunc Akmy) y1 x" using l' by auto
            then obtain y1 where y1: "(y1 \<in> l) \<and> (Akmy y1 = x)" by auto 
            hence "Akmy y1 =  Akmy y" using xA'y by auto
            hence "y1 = y" using invA' by auto
            hence "y \<in> l" using y1 by auto
            hence "False" using l by auto
          }
          thus ?thesis by auto
        qed

        have p'InMeet: "p' \<in> S"
        proof -
          have "p \<in> l \<and> (asFunc Akmy) p p'" using p' pq by auto
          hence "\<exists> p \<in> l . (asFunc Akmy) p p'" by auto
          hence "p' \<in> l'" using l' by auto
          thus ?thesis using Ap S by blast
        qed

        have q'InMeet: "q' \<in> S"
        proof -
          have "q \<in> l \<and> (asFunc Akmy) q q'" using q' pq by auto
          hence "\<exists> q \<in> l . (asFunc Akmy) q q'" by auto
          hence "q' \<in> l'" using l' by auto
          thus ?thesis using Aq S by blast
        qed

        have zInMeet: "z \<in> S"
        proof -
          have "Akmy z' = z" using z' Amkx by blast
          moreover have "z' \<in> l" using l by auto
          ultimately have "z' \<in> l \<and> (asFunc Akmy) z' z" by auto  
          hence "\<exists> z' \<in> l . (asFunc Akmy) z' z" by auto  
          hence "z \<in> l'" using l' by auto
          thus ?thesis using z S by blast
        qed

        have "finite S \<and> card S \<le> 2"          
          using xNotInL' lineL' S lemConeLemma1[of "x" "l'" "S"]
          by auto

        moreover have "S \<noteq> {}" using zInMeet by auto

        ultimately have "card S = 1 \<or> card S = 2"
          using card_0_eq by fastforce

          
        moreover have "card S \<noteq> 2"
        proof -
          { assume "card S = 2"
            hence "p' = z \<or> q' = z" 
              using p'q' p'InMeet q'InMeet zInMeet
                    lemThirdElementOfSet2[of "p'" "q'" "S" "z"] 
              by auto
            hence "False" using p'z q'z by auto
          }
          thus ?thesis by auto
        qed

        moreover have "card S \<noteq> 1" 
          using p'InMeet q'InMeet p'q' card_1_singletonE by force

              
        ultimately have "False" by blast
      }
      thus ?thesis by blast
    qed
    thus ?thesis using l2r by blast
  qed


  (* 35b: Akmy[tAxis] = l *)
  have lprops: "l = applyToSet (asFunc Akmy) timeAxis"
  proof - 
    define t' where t': "t' = applyToSet (asFunc Akmy) timeAxis"
                                                      
    define p1 where p1: "p1 = (y \<in> wline k k)"
    define p2 where p2: "p2 = tangentLine timeAxis (wline k k) y"
    define p3 where p3: "p3 = affineApprox Akmy (wvtFunc k m) y"
    define p4 where p4: "p4 = wvtFunc k m y x"
    define p5 where p5: "p5 = applyAffineToLine Akmy timeAxis t'"
  
    define tgt where tgt: "tgt = tangentLine t' (wline m k) x"
  
    have pre1: "p1" using p1 ykk by auto
    have pre2: "p2" 
    proof -
      have "tangentLine l' (wline k k) y" using tgtl' s by auto
      hence "tangentLine timeAxis (wline k k) y" using c2 by meson
      thus ?thesis using p2 by blast
    qed
    have pre3: "p3" using p3 Akmy by auto
    have pre4: "p4" using p4 kmyx by auto
    have pre5: "p5" 
      using p5 affA' lemTimeAxisIsLine t' Akmy
            lemAffineOfLineIsLine[of "timeAxis" "Akmy" "t'"]
      by blast
  
    (* t' = l *)
    have "p1 \<longrightarrow> p2 \<longrightarrow> p3 \<longrightarrow> p4 \<longrightarrow> p5 \<longrightarrow> tgt"
      using p1 p2 p3 p4 p5 tgt
           lemPresentation[of "y" "k" "k" "timeAxis" "m" "Akmy" "x" "t'"]
      by fast
    hence "tl t' m k x" using tgt pre1 pre2 pre3 pre4 pre5 by auto
    moreover have "tl l m k x" using ass2 by auto
    moreover have "affineApprox A (wvtFunc m k) x" using A by auto
    moreover have "wvtFunc m k x y" using mkxy by auto
    moreover have "x \<in> wline m k" using ass1 by auto
    ultimately have "t' = l" 
      using lemTangentLineUnique[of "x" "m" "k" "t'" "l" "A" "y"]
      by fast
    thus ?thesis using t' by blast
  qed

  (* p35c: Pick any py \<in> tAxis. Show that py is inside cone k y *)
  { fix py assume py: "onTimeAxis py \<and> py \<noteq> y"

    have pyInsideCone: "insideRegularCone y py"
    proof -
      have pyOnAxis: "onLine py timeAxis" using py lemTimeAxisIsLine by blast

      hence pyprops: "timeAxis = lineJoining y py" 
        using py yOnAxis lemLineAndPoints[of "y" "py" "timeAxis"] by auto

      define d where d: "d = (y \<ominus> py)"
      hence "\<exists> py y . (py \<noteq> y) \<and> (onLine py timeAxis) 
                                \<and> (onLine y timeAxis) \<and> (d = (y \<ominus> py))"
        using py pyOnAxis yOnAxis by blast
      hence ddrtn: "d \<in> drtn timeAxis" by simp

      have scomp0: "sComponent d = sOrigin" using d py yOnAxis by auto

      have sf: "slopeFinite py y" using py yOnAxis by force
      hence "sloper py y = ((-1) \<otimes> ((1 / (tval py - tval y)) \<otimes> d))" 
        using d by auto
      hence "velocityJoining py y = sOrigin" using scomp0 by simp
      hence "velocityJoining origin d = sOrigin" using d by auto

      hence "(d \<in> drtn timeAxis) \<and> (sOrigin = velocityJoining origin d)" 
        using ddrtn by auto
      hence "\<exists> d . (d \<in> drtn timeAxis) \<and> (sOrigin = velocityJoining origin d)" 
        by blast
      hence "(sOrigin \<in> lineVelocity timeAxis)" by auto

      hence "(sOrigin \<in> lineVelocity timeAxis) \<and> (sNorm2 sOrigin < 1)"
        by auto
      hence "\<exists> v . (v \<in> lineVelocity timeAxis) \<and> (sNorm2 v < 1)"
        by blast
      thus ?thesis using pyprops sf by auto
    qed
    
    (* Therefore: px is insideRegularCone x  *)
    define px where px: "px = Akmy py"

    have "insideRegularCone x px"
    proof - 
      have "insideRegularCone y py" using pyInsideCone by blast
      moreover have "affInvertible Akmy" using affA' invA' by blast
      moreover have "x = Akmy y" by (simp add: xA'y)
      moreover have "px = Akmy py" by (simp add: px)
      moreover have "regularConeSet x = applyToSet (asFunc Akmy) (regularConeSet y)"
        using p35aRegular by simp
      ultimately show ?thesis 
        using lemInsideRegularConeUnderAffInvertible[of "Akmy" "y" "py"]
        by auto
    qed

    moreover have "x \<noteq> px"
    proof -
      { assume xispx:"x = px"
        hence "False" using xispx invA' px xA'y py by auto
      }
      thus ?thesis by auto
    qed

    ultimately have "insideRegularCone x (Akmy py) \<and> x \<noteq> (Akmy py)" 
      using px by blast 
  }
  hence result: "\<forall>py . (onTimeAxis py \<and> py \<noteq> y) 
                         \<longrightarrow> insideRegularCone x (Akmy py) \<and> x \<noteq> (Akmy py)"
    by blast

  (* AND FINALLY: SHOW The two parts of ?thesis to end the proof *)
  {
    obtain p where p: "(p \<noteq> x) \<and> (p \<in> l)" using assms(4) by blast

    have "l = applyToSet (asFunc Akmy) timeAxis" using lprops by simp
    hence "p \<in> { p . \<exists> py \<in> timeAxis . (asFunc Akmy) py p }" using p by auto
    then obtain py where py: "py \<in> timeAxis \<and> (asFunc Akmy) py p" by blast

    hence "onTimeAxis py" by blast
    moreover have "py \<noteq> y"
    proof -
      { assume "py = y"
        hence "False" using py p by (simp add: xA'y)
      }
      thus ?thesis by auto
    qed
    ultimately have "onTimeAxis py \<and> py \<noteq> y" by blast

    hence inside: "insideRegularCone x p \<and> x \<noteq> p" using result py by auto
    have onl: "onLine x l \<and> onLine p l" using ass2 using p by blast
    have pnotx: "p \<noteq> x" using inside by auto
    hence xnotp: "x \<noteq> p" by simp

    hence lj: "l = lineJoining x p" 
      using lemLineAndPoints[of "x" "p" "l"] xnotp onl by auto

    (* TARGET: Part 1 *)
    hence "lineSlopeFinite l" using onl inside by blast

    (* TARGET: Part 2 *)
    moreover have "(sNorm2 v < 1)"
    proof -
      have "(\<exists> v \<in> lineVelocity l . sNorm2 v < 1)" using lj inside by auto
      then obtain u where u: "u \<in> lineVelocity l \<and> sNorm2 u < 1" by blast
      hence "u = v" 
        using lemFiniteLineVelocityUnique[of "u" "l" "v"] ass3 calculation 
        by presburger
      thus ?thesis using u by auto
    qed

    ultimately have "(lineSlopeFinite l) \<and> (sNorm2 v < 1)" by auto
  }
  thus ?thesis by auto
qed
    

end (* of class NoFTLGR *)

end (* of theory NoFTLGR *)
