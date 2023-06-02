(*
   Author: Mike Stannett
   Date: August 2020
   Updated: Feb 2023
*)

section \<open> TangentLines \<close>

text \<open>This theory defines tangent lines and establishes their key properties.\<close>

theory TangentLines
  imports Translations AxSelfMinus
begin

text \<open>At each point along the worldline of a body, we can ask what its instantaneous
direction of motion is. Unfortunately we do not know a priori that the "worldline"
actually has tangents. Dealing with tangent lines is one of the more complicated 
aspects of the main proof.\<close>

class TangentLines = Translations + AxSelfMinus
begin

abbreviation tangentLine :: "'a Point set  \<Rightarrow> 'a Point set \<Rightarrow> 'a Point \<Rightarrow> bool"
  where "tangentLine l s x \<equiv> 
   (x \<in> s) \<and> (onLine x l) \<and> (accPoint x s)
 \<and>
   (\<exists> p . ( (onLine p l) \<and> (p \<noteq> x) \<and>
      (\<forall> \<epsilon> > 0 .  \<exists> \<delta> > 0 . \<forall> y \<in> s. (
        ( (y within \<delta> of x) \<and> (y \<noteq> x) )
        \<longrightarrow>
        ( \<exists> r . ((onLine r (lineJoining x y)) \<and> (r within \<epsilon> of p))))
      )
   ))
"

abbreviation tangentLineA :: "'a Point set  \<Rightarrow> 'a Point set \<Rightarrow> 'a Point \<Rightarrow> bool"
  where "tangentLineA l s x \<equiv> 
   (x \<in> s) \<and> (onLine x l) \<and> (accPoint x s)
 \<and>
   (\<forall> p . ( ((onLine p l) \<and> (p \<noteq> x)) \<longrightarrow>
      (\<forall> \<epsilon> > 0 .  \<exists> \<delta> > 0 . \<forall> y \<in> s. (
        ( (y within \<delta> of x) \<and> (y \<noteq> x) )
        \<longrightarrow>
        ( \<exists> r . ((onLine r (lineJoining x y)) \<and> (r within \<epsilon> of p))))
      )
   ))
"

abbreviation hasTangent :: "'a Point set \<Rightarrow> 'a Point \<Rightarrow> bool" 
  where "hasTangent s p \<equiv> \<exists> l . tangentLine l s p"


text \<open>The instantaneous velocity of a body is defined to be the velocity
of a co-moving body moving along the tangent line (assuming a tangent line
exists). \<close>


fun vel :: "'a Point set \<Rightarrow> 'a Point \<Rightarrow>  'a Space \<Rightarrow> bool" 
  where "vel wl p v = ( \<exists> l . ( (tangentLine l wl p) \<and> (v \<in> lineVelocity l) ))"


(* LEMMAS *)

lemma lemTangentLineTranslation:
  assumes "translation T"
and       "tangentLine l s x"
shows     "tangentLine (applyToSet (asFunc T) l)
                       (applyToSet (asFunc T) s)  (T x)"
proof -
  define x' where x': "x' = T x"
  define l' where l': "l' = applyToSet (asFunc T) l"
  define s' where s': "s' = applyToSet (asFunc T) s"

  have tgt1: "x \<in> s" using assms(2) by simp

  have tgt2: "onLine x l" using assms(2) by simp
  hence linel: "isLine l" by auto
  
  have tgt3: "accPoint x s" using assms(2) by simp
  have tgt4: "\<exists> p . ( ((onLine p l) \<and> (p \<noteq> x)) \<and>
      (\<forall> \<epsilon> > 0 .  \<exists> \<delta> > 0 . \<forall> y \<in> s. (
        ( (y within \<delta> of x) \<and> (y \<noteq> x) )
        \<longrightarrow>
        ( \<exists> r . ((onLine r (lineJoining x y)) \<and> (r within \<epsilon> of p))))
      )
   )" using assms(2) by simp

  have rtp1: "x' \<in> s'" using x' s' tgt1 by auto
  have rtp2: "onLine x' l'" 
    using lemOnLineTranslation[of "T" "l" "x"] x' l' assms(1) linel tgt2
    by auto
  have rtp3: "accPoint x' s'"
    using assms(1) tgt3 lemAccPointTranslation x' s'
    by simp

  obtain p where p: "((onLine p l) \<and> (p \<noteq> x)) \<and>
    (\<forall> \<epsilon> > 0 .  \<exists> \<delta> > 0 . \<forall> y \<in> s. (
      ( (y within \<delta> of x) \<and> (y \<noteq> x) )
      \<longrightarrow>
      ( \<exists> r . ((onLine r (lineJoining x y)) \<and> (r within \<epsilon> of p))))
    )" using tgt4 by auto

  define p' where p': "p' = (T p)"
  hence p'_on_l': "onLine p' l'" using l' rtp2 p by auto
  have  p'_not_x': "p' \<noteq> x'" 
    using p' p assms(1) x' lemTranslationInjective[of "T"] by force

  { fix e
    assume epos: "e > 0"
    then obtain d where d: "(d > 0) \<and> (\<forall> y \<in> s. (
      ( (y within d of x) \<and> (y \<noteq> x) )
      \<longrightarrow>
      ( \<exists> r . ((onLine r (lineJoining x y)) \<and> (r within e of p))))
    )" using p  by blast

    { fix y'
      assume y': "(y' \<in> s') \<and> (y' within d of x') \<and> (y' \<noteq> x')"
      then obtain y where y: "y \<in> s \<and> y' = T y" using s' by force

      hence y1: "y \<in> s" using y by auto
      have  y2: "y within d of x"  
        using assms(1)  x' y y' lemBallTranslation by fastforce
      have  y3: "y \<noteq> x" using y' y x' assms(1) by fastforce

      then obtain r 
        where r: "(onLine r (lineJoining x y)) \<and> (r within e of p)"
        using y1 y2 d by force

      define r' where r': "r' = T r"
      hence "r' \<in> applyToSet (asFunc T) (lineJoining x y)" using r by auto
      hence r1: "onLine r' (lineJoining x' y')"
        using assms(1) lemLineJoiningTranslation[of "T" "x" "y"] x' y
        by blast
      have r2: "r' within e of p'" 
        using assms(1) r r' p' lemBallTranslation by auto

      hence "\<exists>r'. (onLine r' (lineJoining x' y')) \<and> (r' within e of p')"
        using r1 by auto
      hence "(y' within d of x') \<and> (y' \<noteq> x')
              \<longrightarrow> (\<exists>r'. (onLine r' (lineJoining x' y')) \<and> (r' within e of p'))"
        using y' by blast
    }
    hence "\<forall> y' \<in> s'.  (y' within d of x') \<and> (y' \<noteq> x')
            \<longrightarrow> (\<exists>r'. (onLine r' (lineJoining x' y')) \<and> (r' within e of p'))"
      by auto
  
    hence "\<exists>d>0. \<forall> y' \<in> s'.  (y' within d of x') \<and> (y' \<noteq> x')
            \<longrightarrow> (\<exists>r'. (onLine r' (lineJoining x' y')) \<and> (r' within e of p'))"
      using d by auto
  }
  hence "\<forall>e>0. \<exists>d>0. \<forall> y' \<in> s'.  (y' within d of x') \<and> (y' \<noteq> x')
            \<longrightarrow> (\<exists>r'. (onLine r' (lineJoining x' y')) \<and> (r' within e of p'))"
    by force
  hence "(onLine p' l') \<and> (p' \<noteq> x') 
          \<and> (\<forall>e>0. \<exists>d>0. \<forall> y' \<in> s'.  (y' within d of x') \<and> (y' \<noteq> x')
           \<longrightarrow> (\<exists>r'. (onLine r' (lineJoining x' y')) \<and> (r' within e of p')))"
    using p'_not_x' p'_on_l' by auto
  hence rtp4: "\<exists> p' . ( ((onLine p' l') \<and> (p' \<noteq> x')) 
        \<and> (\<forall>e>0. \<exists>d>0. \<forall> y' \<in> s'.  (y' within d of x') \<and> (y' \<noteq> x')
         \<longrightarrow> (\<exists>r'. (onLine r' (lineJoining x' y')) \<and> (r' within e of p'))))"
    by auto

  hence "?thesis \<longleftrightarrow> (x' \<in> s') \<and> (onLine x' l') \<and> (accPoint x' s')"
    using x' s' l' by simp
  thus ?thesis using rtp1 rtp2 rtp3 by blast
qed


lemma lemTangentLineA:
  assumes "tangentLine l s x"
  shows   "tangentLineA l s x"
proof -
  have 1: "(x \<in> s) \<and> (onLine x l) \<and> (accPoint x s)" using assms by auto

  have "\<exists> P . (onLine P l) \<and> (P \<noteq> x) \<and>
      (\<forall> \<epsilon> > 0 .  \<exists> \<delta> > 0 . \<forall> y \<in> s. (
        ( (y within \<delta> of x) \<and> (y \<noteq> x) )
        \<longrightarrow>
        ( \<exists> r . ((onLine r (lineJoining x y)) \<and> (r within \<epsilon> of P))))
      )"
    using assms by simp
  then obtain P where P: "(onLine P l) \<and> (P \<noteq> x) \<and>
      (\<forall> \<epsilon> > 0 .  \<exists> \<delta> > 0 . \<forall> y \<in> s. (
        ( (y within \<delta> of x) \<and> (y \<noteq> x) )
        \<longrightarrow>
        ( \<exists> r . ((onLine r (lineJoining x y)) \<and> (r within \<epsilon> of P))))
      )"
    by blast

(*  Need to prove   (\<forall> p . ( ((onLine p l) \<and> (p \<noteq> x)) \<longrightarrow>
      (\<forall> \<epsilon> > 0 .  \<exists> \<delta> > 0 . \<forall> y \<in> s. (
        ( (y within \<delta> of x) \<and> (y \<noteq> x) )
        \<longrightarrow>
        ( \<exists> r . ((onLine r (lineJoining x y)) \<and> (r within \<epsilon> of p))))
      )
   ))
*)
  { fix p
    assume p: "onLine p l \<and> p \<noteq> x"

    hence "onLine x l \<and> onLine p l \<and> x\<noteq>p" using 1 by auto
    hence lxp: "l = lineJoining x p"  
      using 1 lemLineAndPoints[of "x" "p" "l"] by auto

    then obtain a where a: "P = (x \<oplus> (a \<otimes> (p\<ominus>x)))" using P by auto
    hence anz: "a \<noteq> 0" using P by auto

    { fix e
      assume epos: "e > 0"
      hence aenz: "a * e \<noteq> 0" using anz by auto
      define e1 where e1: "e1 = abs (a*e)"
      hence e1pos: "e1 > 0" using aenz by auto

      then obtain d where d: "(d > 0) \<and> ( \<forall> y \<in> s. (
        ( (y within d of x) \<and> (y \<noteq> x) )
        \<longrightarrow>
        ( \<exists> r . ((onLine r (lineJoining x y)) \<and> (r within e1 of P))))
      )"
        using P by auto

      { fix y
        assume y: "(y \<in> s) \<and> (y within d of x) \<and> (y \<noteq> x)"
        then obtain R 
          where R: "(onLine R (lineJoining x y)) \<and> (R within e1 of P)"
          using d by blast

        define r where r: "r = (x \<oplus>((1/a)\<otimes>(R\<ominus>x)))"
        hence "(r\<ominus>x) = ((x \<oplus>((1/a)\<otimes>(R\<ominus>x))) \<ominus> x)" using r by auto
        also have "... = ((1/a)\<otimes>(R\<ominus>x))" 
          using add_commute add_assoc diff_add_cancel by auto
        finally have nrx: "(r\<ominus>x) = ((1/a)\<otimes>(R\<ominus>x))" by metis

        
        define T where T: "T = mkTranslation (origin \<ominus> x)"
        hence transT: "translation T" using lemMkTrans by blast
        have "R within e1 of P" using R by simp
        hence "(T R) within e1 of (T P)" 
          using transT lemBallTranslation[of "T" "R" "P" "e1"]
          by fastforce
        hence near1: "((1/a)\<otimes>(R\<ominus>x)) within (e1/a) of ((1/a)\<otimes>(P\<ominus>x))"
          using lemScaleBall[of "R\<ominus>x" "P\<ominus>x" "e1" "1/a"] anz T
          by auto

        define T' where T': "T' = mkTranslation x"
        hence transT': "translation T'" using lemMkTrans by blast
        hence near2: "(T' ((1/a)\<otimes>(R\<ominus>x))) within (e1/a) of (T' ((1/a)\<otimes>(P\<ominus>x)))"
          using near1 transT' 
                lemBallTranslation[of "T'" "(1/a)\<otimes>(R\<ominus>x)" "(1/a)\<otimes>(P\<ominus>x)" "e1/a"]
          by blast

        have term1: "(T' ((1/a)\<otimes>(R\<ominus>x))) = r" using T' add_commute r by auto

        have "(P \<ominus> x) = (a \<otimes> (p\<ominus>x))" using a by auto
        hence "(T' ((1/a)\<otimes>(P\<ominus>x))) = (x \<oplus> ((1/a)\<otimes>(a \<otimes> (p\<ominus>x))))" 
          using T' add_commute by auto
        hence "(T' ((1/a)\<otimes>(P\<ominus>x))) = (x \<oplus> (p\<ominus>x))" 
          using lemScaleAssoc[of "1/a" "a" "P\<ominus>x"] anz by auto
        hence term2: "(T' ((1/a)\<otimes>(P\<ominus>x))) = p" 
          using diff_add_cancel add_commute by auto

        have "e1/a = abs (a*e)/a" using e1 by auto
        hence "sqr (e1/a) = (sqr (abs (a*e)))/ (sqr a)" by auto
        hence "sqr (e1/a) = (sqr (a*e))/ (sqr a)" by auto
        hence "sqr (e1/a) = (sqr a)*(sqr e)/(sqr a)" using lemSqrMult by auto
        hence term3: "sqr (e1/a) = (sqr e)" using anz by simp

        hence r_near_p: "r within e of p" using near2 term1 term2 term3 by auto

        have cases: "(R = x) \<or> (R \<noteq> x)" by auto
        have x_on_xy: "onLine x (lineJoining x y)" 
          using y lemLineAndPoints[of "x" "y" "lineJoining x y"] by auto
        { assume "R = x"
          hence "r = x" using nrx anz by auto
          hence "onLine r (lineJoining x y)" using x_on_xy by blast
        }
        hence case1: "(R = x) \<longrightarrow> (onLine r (lineJoining x y))" by auto
        { assume "R \<noteq> x"
          hence "lineJoining x R = lineJoining x y"
            using R x_on_xy lemLineAndPoints[of "x" "R" "lineJoining x y"]
            by auto
          hence "onLine r (lineJoining x y)" using r by blast
        }
        hence "(R \<noteq> x) \<longrightarrow> (onLine r (lineJoining x y))" by auto
        hence "onLine r (lineJoining x y)" using cases case1 by auto

        hence "\<exists> r. (onLine r (lineJoining x y)) \<and> (r within e of p)"
          using r_near_p by auto
      }
      hence "\<forall>y \<in> s .  (y within d of x) \<and> (y \<noteq> x)
          \<longrightarrow> (\<exists> r. (onLine r (lineJoining x y)) \<and> (r within e of p))"
        by auto
      hence "\<exists>d>0. \<forall>y \<in> s .  (y within d of x) \<and> (y \<noteq> x)
          \<longrightarrow> (\<exists> r. (onLine r (lineJoining x y)) \<and> (r within e of p))"
        using d by auto
    }
    hence "\<forall>e>0. \<exists>d>0. \<forall>y \<in> s .  (y within d of x) \<and> (y \<noteq> x)
          \<longrightarrow> (\<exists> r. (onLine r (lineJoining x y)) \<and> (r within e of p))"
      by blast
  }
  hence 2: "\<forall>p . (onLine p l \<and> p \<noteq> x) \<longrightarrow> 
            (\<forall>e>0. \<exists>d>0. \<forall>y \<in> s .  (y within d of x) \<and> (y \<noteq> x)
               \<longrightarrow> (\<exists> r. (onLine r (lineJoining x y)) \<and> (r within e of p)))"
    by blast
  thus ?thesis using 1 by auto
qed


lemma lemTangentLineE:
  assumes "tangentLineA l s x"
and       "\<exists>p \<noteq> x . onLine p l"
  shows   "tangentLine l s x"
proof -
  have 1: "(x \<in> s) \<and> (onLine x l) \<and> (accPoint x s)" using assms(1) by auto

  obtain p where p: "(p \<noteq> x) \<and> (onLine p l)" using assms(2) by auto
  hence "\<forall> \<epsilon> > 0 .  \<exists> \<delta> > 0 . \<forall> y \<in> s. (
        ( (y within \<delta> of x) \<and> (y \<noteq> x) )
        \<longrightarrow>
        ( \<exists> r . ((onLine r (lineJoining x y)) \<and> (r within \<epsilon> of p))))" 
    using assms(1) by blast
  thus ?thesis using 1 p by auto
qed




end (* of class TangentLines *)

end (* of theory TangentLines *)

