(*
  KeyLemma.thy
  Author: Mike Stannett
  Date: Jan 2023
*)

section \<open> KeyLemma \<close>

text \<open>This theory establishes a "key lemma": if you draw a line
through a point inside a cone, that line will intersect the cone in
no fewer than 1 and no more than 2 points.\<close>


theory KeyLemma
  imports Classification ReverseCauchySchwarz
begin

class KeyLemma = Classification + ReverseCauchySchwarz
begin




(* KEY THEOREM FOR PROOF *)
lemma lemInsideRegularConeImplies:
  assumes "insideRegularCone x p"
and       "D \<noteq> origin"
and       "l = line p D"
shows     "0 < card (l \<inter> regularConeSet x) \<le> 2"
proof -
  define S where S: "S = (l \<inter> regularConeSet x)"
  define X where X: "X = (p \<ominus> x)"
  define a where a: "a = mNorm2 D"
  define b where b: "b = 2*(tval X)*(tval D) - 2*((sComponent D) \<odot>s (sComponent X))"
  define c where c: "c = mNorm2 X"
  define d where d: "d = (sqr b) - (4*a*c)"

  have tlX: "timelike X" using lemTimelikeInsideCone assms(1) X by auto
  hence cpos: "c > 0" using c by auto

  have xnotp: "x \<noteq> p" using assms(1) by auto

  have aval: "a = mNorm2 D" using  a by auto
  have bval: "b = 2*(X \<odot>m D)" 
    using b local.lemSDotCommute local.right_diff_distrib' mult_assoc 
    using local.mdot.simps by presburger
  have cval: "c = mNorm2 X" using  c by auto
  have dval: "d = 4 * ( (sqr (X \<odot>m D)) - (mNorm2 X)*(mNorm2 D) )"
  proof -
    have "d = (sqr b) - (4*a*c)" using d by simp
    moreover have "(sqr b) = 4*(sqr (X \<odot>m D))"
      using lemSqrMult[of "2" "(X \<odot>m D)"] bval by auto
    moreover have "4*a*c = 4*(mNorm2 X)*(mNorm2 D)" 
      using aval cval mult_commute mult_assoc by auto
    ultimately show ?thesis using right_diff_distrib' mult_assoc by metis
  qed

  (* QCASE ANALYSIS *)
  define r2p where r2p: "r2p = (\<lambda> r . (p\<oplus>(r\<otimes>D)))"
  define p2r where p2r: "p2r = (\<lambda> q . (THE a . q = (p\<oplus>(a\<otimes>D))))"

  have bij: "\<forall> r q . r2p r = q \<longleftrightarrow> (\<exists> w . (r2p w = q)) \<and> (p2r q = r)"
  proof -
    have uniqueroots: "\<forall> a r . r2p a = r2p r \<longrightarrow> a = r"
    proof -          
      { fix a r assume "r2p a = r2p r"
        hence "(a\<otimes>D) = (r\<otimes>D)" using r2p add_diff_eq by auto
        hence "((a-r)\<otimes>D) = origin" using lemScaleDistribDiff by auto
        hence "(a-r) = 0" using assms(2) by auto
        hence "a = r" by simp
      }
      thus ?thesis by blast
    qed
    { fix q r assume lhs: "r2p r = q"
      have "(THE a . q = r2p a) = r"
      proof -
        { fix a assume "q = r2p a"
          hence "a = r" using uniqueroots lhs r2p by blast
        }
        hence "\<forall> a . q = r2p a \<longrightarrow> a = r" by auto
        thus ?thesis using lhs the_equality[of "\<lambda>a . q = r2p a" "r"]
          by force
      qed
    }
    hence l2r: "\<forall> q r . r2p r = q \<longrightarrow> (\<exists> w . (r2p w = q)) \<and> (p2r q = r)" 
      using p2r r2p by blast

    { fix r q assume ass: "(\<exists> w . (r2p w = q)) \<and> (p2r q = r)"
      then obtain w where w: "r2p w = q" by blast
      hence unique: "\<forall> a . q = r2p a \<longrightarrow> a = w" using uniqueroots by auto
      have rdef: "r = (THE a . q = r2p a)" using ass r2p p2r by simp

      have "q = r2p w" using w by simp
      hence "q = r2p r" using theI[of "\<lambda> a. q = r2p a" "w"] rdef unique
        by blast
    }
    hence "\<forall> q r . (\<exists> w . (r2p w = q)) \<and> (p2r q = r) \<longrightarrow> q = r2p r"
      by blast

    thus ?thesis using l2r by blast
  qed

  have equalr2p: "\<forall> x y . r2p x = r2p y \<longrightarrow> x = y" using bij by metis

  have SbijRoots: "S = { y . \<exists> x \<in> qroots a b c . y = r2p x }"  
  proof -
    { fix y assume y: "y \<in> S"
      then obtain r where r: "y = r2p r" using r2p S assms by blast
      hence "regularCone x (p \<oplus> (r\<otimes>D))" using r2p y S by auto
      hence "r \<in> qroots a b c" 
        using lemWhereLineMeetsCone[of "a" "D" "b" "p" "x" "c" "r"]
              a b c X by auto
      hence "\<exists> r \<in> qroots a b c . y = r2p r" using r by blast
    }
    hence l2r: "S \<subseteq> { y . \<exists> x \<in> qroots a b c . y = r2p x }" by blast
    { fix y assume y: "y \<in> { y . \<exists> x \<in> qroots a b c . y = r2p x }"
      then obtain r where r: "r \<in> qroots a b c \<and> y = r2p r" by blast
      hence "regularCone x (r2p r)"
        using lemWhereLineMeetsCone[of "a" "D" "b" "p" "x" "c" "r"]
              a b c X r2p by auto
      moreover have "r2p r \<in> l" using assms(3) r2p by auto
      ultimately have "y \<in> S" using S r by auto
    }
    thus ?thesis using l2r by blast
  qed


  have equalcard: "((card (qroots a b c) = 1) \<or> (card (qroots a b c) = 2))
                               \<longrightarrow> (card S = card (qroots a b c))"
  proof -
    { assume cases: "card (qroots a b c) = 1 \<or> card (qroots a b c) = 2"
  
      have case1: "card (qroots a b c) = 1 \<longrightarrow> (card S = card (qroots a b c))" 
      proof -
        { assume card1: "card (qroots a b c) = 1"
          hence "\<exists> r . (qroots a b c) = {r}" by (meson card_1_singletonE)
          then obtain r where r: "(qroots a b c) = {r}" by blast
          hence l2r: "{ r2p r } \<subseteq> S" using SbijRoots by auto
          { fix y assume y: "y \<in> S"
            then obtain x where x: "x \<in> qroots a b c \<and> y = r2p x"
              using SbijRoots by blast 
            hence "r2p r = y" using bij using r by auto
          }
          hence "\<forall> y . y \<in> S  \<longrightarrow> y \<in> { r2p r }" by auto
          hence "S = { r2p r }" using l2r by blast
          hence "\<exists> r . S = {r}" by blast
          hence "card S = 1" 
            using card_1_singleton_iff[of "S"] by auto
        }
        thus ?thesis by auto
      qed

      have case2: "card (qroots a b c) = 2 \<longrightarrow> (card S = card (qroots a b c))" 
      proof -
        { assume card2: "card (qroots a b c) = 2"
          hence "\<exists> r1 r2 . (qroots a b c) = {r1, r2} \<and> r1 \<noteq> r2" 
            using card_2_iff by blast
          then obtain r1 r2 where rs: "(qroots a b c) = {r1,r2} \<and> r1\<noteq>r2" by blast
          hence l2r: "{ r2p r1, r2p r2} \<subseteq> S" using SbijRoots by auto
          { fix y assume y: "y \<in> S"
            then obtain x where x: "x \<in> qroots a b c \<and> y = r2p x"
              using SbijRoots by blast 
            hence "x = r1 \<or> x = r2" using rs by auto
            hence "r2p r1 = y \<or> r2p r2 = y" using x by blast
          }
          hence "\<forall> y . y \<in> S  \<longrightarrow> y \<in> { r2p r1, r2p r2 }" by auto
          hence S2: "S = { r2p r1, r2p r2 }" using l2r by blast
          moreover have "r2p r1 \<noteq> r2p r2" using rs bij by metis
          ultimately have "\<exists> y1 y2 . S = {y1, y2} \<and> y1\<noteq>y2" by blast
          hence "card S = 2" using card_2_iff by blast
        }
        thus ?thesis by auto
      qed

      hence "(card S = card (qroots a b c))" using case1 cases by auto
    }
    thus ?thesis by auto
  qed
      


  have qc1: "\<not> qcase1 a b c" using cpos by auto

  have qc2: "\<not> qcase2 a b c" 
  proof -
    { assume "qcase2 a b c"
      hence qc2: "a = 0 \<and> b = 0 \<and> c > 0" using d cpos by auto
        
      have llD: "lightlike D" using qc2 aval assms(2) by simp

      have  "sqr (X \<odot>m D) = (mNorm2 X)*(mNorm2 D)" 
        using qc2 bval aval by simp
      hence "orthogm X D" using llD lemSqrt0 by auto
      hence parXD: "parallel X D"
          using lemCausalOrthogmToLightlikeImpliesParallel tlX llD by auto

      (* This contradicts the requirement on c *)
      then obtain \<alpha> where \<alpha>: "\<alpha> \<noteq> 0 \<and> X = (\<alpha> \<otimes> D)" by blast

      have Dnot0: "origin \<noteq> D" using assms(2) by simp
      hence "lightlike X"
      proof - 
        have tsqr: "sqr (tval X) = (sqr \<alpha>)* sqr (tval D)" 
          using lemSqrMult \<alpha> by simp
        have "sComponent X = (\<alpha> \<otimes>s (sComponent D))" using \<alpha> by simp
        hence "sNorm2 (sComponent X) = (sqr \<alpha>) * sNorm2 (sComponent D)"
          using lemSNorm2OfScaled[of "\<alpha>" "sComponent D"] by auto
        hence "mNorm2 X = (sqr \<alpha>) * mNorm2 D"
          using lemMNorm2Decomposition[of "X"] tsqr
          by (simp add: local.right_diff_distrib')
        thus ?thesis using llD qc2 xnotp X by auto
      qed

      hence "False" using tlX by auto
    }
    thus ?thesis by auto
  qed


  have qc3: "qcase3 a b c \<longrightarrow> card S = 1" 
  proof -
    { assume "qcase3 a b c"
      hence qc3: "qroots a b c = {(-c/b)}" using lemQCase3 by auto
      hence "\<exists> val . (qroots a b c = {val})" by simp
      hence "card (qroots a b c) = 1" using card_1_singleton_iff by auto
      hence "card S = 1" using equalcard by auto
    }
    thus ?thesis by auto
  qed

  have qc4: "\<not> qcase4 a b c"
  proof -
    { assume "qcase4 a b c"
      hence qc4: "a \<noteq> 0 \<and> d < 0" using d by auto
      { assume "a > 0"
        hence tlD: "timelike D" using aval by auto

        hence "sqr (X \<odot>m D) \<ge> (mNorm2 X)*(mNorm2 D)"
          using lemReverseCauchySchwarz[of "X" "D"] tlX 
          using local.dual_order.order_iff_strict by blast
        hence EQN: "4*sqr (X \<odot>m D) \<ge> 4*(mNorm2 X)*(mNorm2 D)"
          using qc4 d dval local.leD by fastforce
         
        (* This contradicts the requirement on d *)
        have "(sqr b) < 4*a*c" using d qc4 by simp
        hence "4*sqr (X \<odot>m D) < 4*(mNorm2 X)*(mNorm2 D)"
          using aval bval cval mult_assoc mult_commute 
                lemSqrMult[of "2" "(X \<odot>m D)"] by auto

        hence "False" using EQN by force
      }
      hence aneg: "a < 0" using qc4 by force
      hence "4*a*c < 0" using cpos 
        by (simp add: local.mult_pos_neg local.mult_pos_neg2)
      hence "d > sqr b" using d
        by (metis add_commute local.add_less_same_cancel2 local.diff_add_cancel)
      hence "d > 0" 
        using local.less_trans local.not_square_less_zero qc4 by blast
      hence "False" using qc4 by auto
    }
    thus ?thesis by auto
  qed
 
  have qc5: "qcase5 a b c \<longrightarrow> card S = 1" 
  proof -
    {      
      assume qc5: "qcase5 a b c"
      hence "qroots a b c = {(-b/(2*a))}" using lemQCase5 by auto
      hence "\<exists> val . qroots a b c = {val}" by simp
      hence "card (qroots a b c) = 1" using card_1_singleton_iff by auto
      hence "card S = 1" using equalcard by simp
    }
    thus ?thesis by simp
  qed

  have qc6: "qcase6 a b c \<longrightarrow> card S = 2"
  proof -
    { define rd where rd: "rd = sqrt (discriminant a b c)"
      define rp where rp: "rp = (-b + rd) / (2 * a)"
      define rm where rm: "rm = (-b - rd) / (2 * a)"

      assume qc6: "qcase6 a b c"
      hence "rp \<noteq> rm \<and> qroots a b c = {rp, rm}" 
        using lemQCase6[of "a" "b" "c" "rd" "rp" "rm"] a b c rd rm rp
        by auto
       
      hence "\<exists> v1 v2 . qroots a b c = { v1, v2 } \<and> (v1 \<noteq> v2)" by blast
      hence "card (qroots a b c) = 2" using card_2_iff[of "qroots a b c"] by blast
      hence "card S = 2" using equalcard by simp
    }
    thus ?thesis by simp
  qed

  define n where n: "n = card S"
  hence "(n = 1 \<or> n = 2)" 
    using qc1 qc2 qc3 qc4 qc5 qc6 lemQuadraticCasesComplete
    by blast
  hence "0 < n \<le> 2" by auto
  thus ?thesis using n S by auto
qed

end (* of class KeyLemma *)
end (* of theory KeyLemma *)
