(*
  AffineConeLemma.thy
  Author: Mike Stannett
  Date: Jan 2023
*)

section \<open> AffineConeLemma \<close>

text \<open>This theory shows that affine approximations preserve "insideness"
of points relative to cones.\<close>

theory AffineConeLemma
  imports KeyLemma TangentLineLemma Cardinalities
begin

class AffineConeLemma = KeyLemma + TangentLineLemma + Cardinalities
begin


lemma lemInverseOfAffInvertibleIsAffInvertible:
  assumes "affInvertible A"
and       "\<forall> x y . A x = y \<longleftrightarrow> A' y = x"
shows     "affInvertible A'"
proof -
  have invA': "invertible A'" using assms(2) by force
  moreover have "affine A'"
  proof - 
    obtain L T where LT: "(linear L) \<and> (translation T) \<and> (A = T \<circ> L)" 
      using assms(1) by blast
    then obtain t where t: "\<forall> x . T x = (x \<oplus> t)" using LT by auto

    have "invertible L" 
    proof -
      { fix q 
        define p where p: "p = A' (T q)"
        hence Lpq: "(L p = q)"
        proof -
          have "A p = T q" using p assms(2) by simp
          thus ?thesis using LT by auto
        qed
        moreover have "(\<forall>x. L x = q \<longrightarrow> x = p)"
        proof -
          { fix x assume "L x = q"
            hence "L x = L p" using Lpq by simp
            hence "A x = A p" using LT by auto
            hence "x = p" using assms(2) by force
          }
          thus ?thesis by auto
        qed
        ultimately have "\<exists> p . (L p = q) \<and> (\<forall>x. L x = q \<longrightarrow> x = p)" by blast
      }
      thus ?thesis by blast
    qed
    then obtain L' where L': "\<forall> x y . L x = y \<longleftrightarrow> L' y = x" by metis

    have linL: "linear L" using LT by auto
    have linL': "linear L'" 
    proof -
      have part1: "L' origin = origin" using linL L' by auto
      have part2: "\<forall> a p . L' (a\<otimes>p) = (a \<otimes> (L' p))"
      proof -
        { fix a p
          have "L (L' p) = p" using L' by auto
          hence "L (a \<otimes>  (L' p)) = (a \<otimes> p)" 
            using linL lemLinearProps[of "L" "a" "(L' p)"] by auto
          hence "(a \<otimes>  (L' p)) = (L' (a \<otimes> p))" using L' by auto
        }
        thus ?thesis by auto
      qed
      have "\<forall> p q . (L' (p \<oplus> q) = ((L' p) \<oplus> (L' q))) \<and>  (L' (p \<ominus> q) = ((L' p) \<ominus> (L' q)))"
      proof -
        { fix p q
          have "(L ((L' p) \<oplus> (L' q)) = ((L (L' p)) \<oplus> (L (L' q)))) 
                    \<and>  (L ((L' p) \<ominus> (L' q)) = ((L (L' p)) \<ominus> (L (L' q))))" 
            using linL lemLinearProps[of "L" "0" "(L' p)" "(L' q)"] by auto
          moreover have "L (L' p) = p \<and> L (L' q) = q" using L' by auto
          ultimately have "(L ((L' p) \<oplus> (L' q)) = (p \<oplus> q)) \<and>  (L ((L' p) \<ominus> (L' q)) = (p \<ominus> q))" 
            using L' by auto
          hence "((L' p) \<oplus> (L' q)) = L' (p \<oplus> q) \<and> ((L' p) \<ominus> (L' q)) = L' (p \<ominus> q)"
            using L' by force
        }
        thus ?thesis by force
      qed

      thus ?thesis using part1 part2 by blast
    qed

    define t' where t': "t' = (origin \<ominus> (L' t))"
    define T' where T': "T' = mkTranslation t'"

    have transT': "translation T'" using T' t' by fastforce

    have "A' = T' o L'"
    proof -
      { fix q define p where p: "p = A' q"
        hence "A p = q" using assms(2) by force
        hence "((L p) \<oplus> t) = q" using LT t by auto
        hence "L p = (q \<ominus> t)" using add_diff_eq by auto
        hence "p = L' (q \<ominus> t)" using L' by auto
        hence "p = ((L' q) \<ominus> (L' t))" using lemLinearProps[of "L'"] linL' by auto
        hence "p = T' (L' q)" using T' t' by auto
        hence "A' q = (T' o L') q" using p by auto
      }
      thus ?thesis by blast
    qed

    thus ?thesis using linL' transT' by blast
  qed

  ultimately show ?thesis by blast
qed

     



lemma lemInsideRegularConeUnderAffInvertible:
  assumes "affInvertible A"
and       "insideRegularCone x p"
and       "regularConeSet (A x) = applyToSet (asFunc A) (regularConeSet x)"
shows     "insideRegularCone (A x) (A p)"
proof -
  define y  where y: "y = A x"
  define q  where q: "q = A p"
  define cx where cx: "cx = regularConeSet x"
  define cy where cy: "cy = regularConeSet y"

  obtain A' where A': "\<forall> x y . A x = y \<longleftrightarrow> A' y = x" using assms(1) by metis
  hence invA': "invertible A'" by force
  have affA': "affine A'" 
    using A' assms(1) lemInverseOfAffInvertibleIsAffInvertible
    by auto

  have p': "A' q = p" using A' q by auto
  have x': "A' y = x" using A' y by auto

  have xnotp: "x \<noteq> p" using assms(2) by auto
  have ynotq: "y \<noteq> q" using p' x' xnotp by auto

  have cy': "cy = applyToSet (asFunc A) cx" using y cx cy assms(3) by auto
  have cx': "cx = applyToSet (asFunc A') cy"
  proof -
    { fix z assume "z \<in> cx"
      hence "(A z) \<in> cy" using cy' by auto
      hence "A' (A z)  \<in> applyToSet (asFunc A') cy" by auto
      hence "z \<in> applyToSet (asFunc A') cy" using A' by metis
    }
    hence l2r: "cx \<subseteq> applyToSet (asFunc A') cy" by blast
    { fix z assume rhs: "z \<in> applyToSet (asFunc A') cy"
      hence "z \<in> { z . \<exists> z' . z' \<in> cy \<and> (asFunc A') z' z }" by auto
      then obtain z1 where z1: "z1 \<in> cy \<and> (asFunc A') z1 z" by blast
      hence "z1 \<in> { z1 . \<exists> z2 . z2 \<in> cx \<and> (asFunc A) z2 z1 }" using cy' by auto
      then obtain z2 where z2: "z2 \<in> cx \<and> (asFunc A) z2 z1" by blast
      hence "z = z2" using z1 A' by auto
      hence "z \<in> cx" using z2 by auto
    }
    thus ?thesis using l2r by blast
  qed

  (* q isn't onRegularCone y *)
  have noton: "\<not> onRegularCone y q"
  proof -
    { assume on: "onRegularCone y q"

      define lx where lx: "lx = lineJoining x p"
      define ly where ly': "ly = applyToSet (asFunc A) lx"
      have onlx: "onLine x lx \<and> onLine p lx" 
        using lemLineJoiningContainsEndPoints[of "lx" "x" "p"] lx by auto
    
      have linelx: "isLine lx" using lx by blast
      have linely: "applyAffineToLine A lx ly" 
        using lemAffineOfLineIsLine[of "lx" "A" "ly"] assms(1) ly' linelx by auto
    
      have "\<exists> D . lx = line p D"
      proof -
        obtain b d where "lx = line b d" using linelx by blast
        hence "lx = line p d" using lemSameLine[of "p" "b" "d"] onlx by auto
        thus ?thesis by auto
      qed
      then obtain D where D: "lx = line p D" by auto
    
      have Dnot0: "D \<noteq> origin"
      proof -
        { assume "D = origin"
          hence "False" using D onlx xnotp by auto
        }
        thus ?thesis by auto
      qed
    
      have ly: "ly = lineJoining y q"
      proof -
        have "applyToSet (asFunc A) {x,p} \<subseteq> applyToSet (asFunc A) lx" using onlx by auto
        hence "{y,q} \<subseteq> ly" using y q ly' by auto
        moreover have "isLine ly" using linely by auto
        ultimately show ?thesis using lemLineAndPoints[of "y" "q" "ly"]
          by (simp add: ynotq)
      qed
    
      hence only: "{ y, q } \<subseteq> ly" 
        using lemLineJoiningContainsEndPoints[of "ly" "y" "q"] ly' by auto
    
      have SxSy: "applyToSet (asFunc A) (lx \<inter> cx) = (ly \<inter> cy)"
        using lemInvertibleOnMeet[of "A" "lx \<inter> cx" "lx" "cx"] assms(1) ly' cy' 
        by auto
    
      (* CARDINALITY TEST *)
      have cardx: "0 < card (lx \<inter> cx) \<le> 2" 
        using lemInsideRegularConeImplies[of "x" "p" "D" "lx"] 
              assms(2) Dnot0 lx D cx 
        by fastforce
    
      hence cardy: "card (ly \<inter> cy) = card (lx \<inter> cx)" 
        using lemSmallCardUnderInvertible[of "A" "lx \<inter> cx"] assms(1) SxSy by auto
    
      hence lycy: "ly \<inter> cy = ly" 
        using lemOnRegularConeIff[of "ly" "y" "q"] ly ynotq cy on
        by blast
      hence "\<exists> p1 p2 p3 . (p1 \<in> ly \<and> p2 \<in> ly \<and> p3 \<in> ly)
                        \<and> (p1\<noteq>p2 \<and> p2\<noteq>p3 \<and> p3\<noteq>p1)"
        using lemCardOfLineIsBig[of "y" "q" "ly"] ynotq only linely by auto
      then obtain p1 p2 p3 
        where ps: "(p1 \<in> ly \<and> p2 \<in> ly \<and> p3 \<in> ly) \<and> (p1\<noteq>p2 \<and> p2\<noteq>p3 \<and> p3\<noteq>p1)"
        by auto
      
      have not1: "card ly \<noteq> 1" using ps card_1_singleton_iff[of "ly"] by auto
      have not2: "card ly \<noteq> 2" using ps card_2_iff[of "ly"] by auto
      hence "\<not> (0 < card (ly \<inter> cy) \<le> 2)" using lycy not1 by auto
      hence "False" using cardy cardx by auto
    }
    thus ?thesis by blast
  qed

  (* q isn't outsideRegularCone y *)
  have notout: "\<not> outsideRegularCone y q"
  proof -
    { assume out: "outsideRegularCone y q"
      hence "(\<exists> l q' . (q' \<noteq> q) \<and> onLine q' l \<and> onLine q l
                                          \<and> (l \<inter> cy = {}))" 
        using lemOutsideRegularConeImplies[of "y" "q"] cy
        by auto
      then obtain l q' 
        where l: "(q' \<noteq> q) \<and> onLine q' l \<and> onLine q l \<and> (l \<inter> cy = {})" by blast

      define lx where lx: "lx = applyToSet (asFunc A') l"
      have "(lx \<inter> cx) = applyToSet (asFunc A') (l \<inter> cy)"
        using lemInvertibleOnMeet[of "A'" "l \<inter> cy" "l" "cy"]
              invA' lx cx' by auto
      hence "(lx \<inter> cx) = applyToSet (asFunc A'){}" using l by auto
      hence int0: "(lx \<inter> cx) = {}" by simp

      (* CARD = 0 *)
      hence card0: "card (lx \<inter> cx) = 0" by simp

      (* BUT: 0 < CARD \<le> 2 *)
      have linelx: "isLine lx" 
      proof -
        have "isLine l" using l by blast
        thus ?thesis using lemAffineOfLineIsLine[of "l" "A'" "lx"] lx affA' 
          by auto
      qed

      have ponlx: "onLine p lx" 
      proof -
        have "q \<in> l" using l by simp
        thus ?thesis using lx p' linelx by auto
      qed

      have "\<exists> D . lx = line p D"
      proof -
        obtain b d where "lx = line b d" using linelx by blast
        hence "lx = line p d" using lemSameLine[of "p" "b" "d"] ponlx by auto
        thus ?thesis by auto
      qed
      then obtain D where D: "lx = line p D" by auto
    
      have Dnot0: "D \<noteq> origin"
      proof -
        { assume D0: "D = origin"
          have allp: "\<forall> pt. onLine pt lx \<longrightarrow> pt = p"
          proof -
            { fix pt assume "onLine pt lx"
              then obtain a where "pt = (p \<oplus> (a \<otimes> D))" using D by auto
              hence "pt = p" using D0 by simp
            }
            thus ?thesis by blast
          qed

          define p1 where p1: "p1 = A' q'"
          have AA': "\<forall> pt . A (A' pt) = pt" by (simp add: A')

          hence "p1 \<noteq> p"
          proof -
            { assume pp: "p1 = p"
              hence  "A (A' q') = A (A' q)" using p' p1 by auto
              hence "q' = q" using AA' by simp
              hence "False" using l by auto
            }
            thus ?thesis by auto
          qed

          moreover have "onLine p1 lx" 
          proof -
            have "p1 = A' q'" using l p1 by blast
            hence "p1 \<in> applyToSet (asFunc A') l" using l by auto
            hence "p1 \<in> lx" by (simp add: lx)
            thus ?thesis using linelx by auto
          qed

          ultimately have "False" using l allp by blast
        }
        thus ?thesis by auto
      qed

      have "0 < card (lx \<inter> cx) \<le> 2" 
        using lemInsideRegularConeImplies[of "x" "p" "D" "lx"] 
              assms(2) Dnot0 D cx 
        by blast

      hence "False" using card0 by simp
    }
    thus ?thesis by blast
  qed

  hence "\<not> (vertex y q) \<and> \<not>(onRegularCone y q) \<and> \<not>(outsideRegularCone y q)"
    using ynotq noton notout by blast
  hence "insideRegularCone y q" using lemInsideCone[of "y" "q"]
    by fastforce
    
  thus ?thesis using y q by blast
qed



end (* of class AffineConeLemma *)
end (* of theory AffineConeLemma *)
