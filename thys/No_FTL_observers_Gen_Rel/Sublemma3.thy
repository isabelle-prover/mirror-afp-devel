(*
   Author: Edward Higgins and Mike Stannett
   Date: July 2019

   Modified by MS June 2020
   Streamlined by MS July 2020
   Updated: (MS) Jan 2023
*)

section \<open> Sublemma3 \<close>

text \<open>This theory establishes how closely tangent lines approximate
world lines.\<close>

theory Sublemma3
  imports WorldLine AxTriangleInequality TangentLines
begin


class Sublemma3 = WorldLine + AxTriangleInequality + TangentLines
begin

(* Two of the assumptions have been removed, as they follow
   from the definition of approximation *)
   
lemma sublemma3: 
assumes "onLine p l"
and     "norm2 p = 1"
and     "tangentLine l wl origin"
shows   
"\<forall> \<epsilon> > 0 . \<exists> \<delta> > 0 . \<forall> y ny . (
       ((y within \<delta> of origin) \<and> (y \<noteq> origin) \<and> (y \<in> wl) \<and> (norm y = ny))
        \<longrightarrow>
       ( (((1/ny)\<otimes>y) within \<epsilon> of p) \<or> (((-1/ny)\<otimes>y) within \<epsilon> of p))
)"
proof -
  { fix e :: "'a"
    { assume epos: "e > 0"
  
      hence e2pos: "e/2 > 0" by simp
    
      have prop1: "origin \<in> wl"  using assms(3) by auto
      have prop2: "onLine origin l"  using assms(3) by auto
      hence prop3: "\<forall> \<epsilon> > 0. \<exists> q \<in> wl. (origin \<noteq> q) \<and> (inBall q \<epsilon> origin)"
        using assms(3) by auto


      have prop4: "\<forall> p .( ((onLine p l) \<and> (p \<noteq> origin)) \<longrightarrow>
          (\<forall> \<epsilon> > 0 .  \<exists> \<delta> > 0 . \<forall> y \<in> wl . (
            ( (y within \<delta> of origin) \<and> (y \<noteq> origin) )
            \<longrightarrow>
            ( \<exists> r . ((onLine r (lineJoining origin y)) \<and> (r within \<epsilon> of p))))
          )
       )" using assms(3) lemTangentLineA[of "origin"] 
        by auto


  
      have "p \<noteq> origin" using assms(2) lemNullImpliesOrigin by auto
    
      hence ballprops: "\<forall> \<epsilon> > 0 .  \<exists> \<delta> > 0 . \<forall> y \<in> wl . (
            ( (y within \<delta> of origin) \<and> (y \<noteq> origin) )
            \<longrightarrow>
            ( \<exists> r . ((onLine r (lineJoining origin y)) \<and> (r within \<epsilon> of p)))
        )"
        using assms(1) prop4 by auto
    
      (* Take \<epsilon> = min {1/2, e/2} and extract a corresponding \<delta> *)
      define eps where "eps = (if (e/2 < 1/2) then (e/2) else (1/2))"
    
      hence eps_le_e2: "eps \<le> e/2" by auto
    
      have epspos: "eps > 0" using e2pos eps_def by simp
    
      { assume ass1: "e/2 < 1/2"
        hence "eps = e/2" using eps_def by auto
        hence "eps < 1/2" using ass1 by simp
        hence "eps \<le> 1/2" by simp
      }
      hence case1: "(e/2 < 1/2) \<longrightarrow> eps \<le> 1/2" by auto
      have "\<not>(e/2 < 1/2) \<longrightarrow> eps = 1/2" using eps_def by simp
      hence case2: "\<not>(e/2 < 1/2) \<longrightarrow> eps \<le> 1/2" by auto
      hence "(eps \<le> (1/2))" using case1 case2 by auto
      hence eps_lt_1: "eps < 1" using le_less_trans by auto
      hence "sqr eps < eps" using epspos lemMultPosLT1 by auto
      hence epssqu: "sqr eps < 1" using eps_lt_1 le_less_trans by auto
  
      then obtain d where dprops: "(d > 0) \<and> (\<forall> y \<in> wl. (
            ( (y within d of origin) \<and> (y \<noteq> origin) )
            \<longrightarrow>
            ( \<exists> r . ((onLine r (lineJoining origin y)) \<and> (r within eps of p))))
          )" using epspos ballprops by auto
  
      { fix y ny assume ny: "ny = norm y"
        { assume y: "(y within d of origin) \<and> (y \<noteq> origin) \<and> (y \<in> wl)"      
          hence "\<exists> r . ((onLine r (lineJoining origin y)) \<and> (r within eps of p))"
            using dprops by blast      
          then obtain r 
            where r: "(onLine r (lineJoining origin y)) \<and> (r within eps of p)"
            by auto
      
          (* Claim: there exists \<alpha> \<noteq> 0 with r = \<alpha>y *)
          hence "\<exists> \<alpha> . r = (\<alpha> \<otimes> y)" by simp
          then obtain \<alpha> where alpha: "r = (\<alpha> \<otimes> y)" by auto
      
          { assume "\<alpha> = 0"
            hence rnull: "r = origin" using alpha by simp
            hence one: "sep2 r p = 1" using assms(2) by auto
            have  "sep2 r p < sqr eps" using r  by auto
            hence not_one: "sep2 r p < 1" using epssqu by auto
            hence "False" using one not_one by auto
          }
          hence anz: "\<alpha> \<noteq> 0" by auto
      
          (* Show that norm r is close to 1 *)
          define np where "np = norm p"
          hence np: "np = 1" using assms(2) lemSqrt1 by auto
      
          define npr where "npr = norm (p \<ominus> r)"
          hence "sqr npr = sep2 p r" using local.lemNormSqrIsNorm2 by presburger
          hence "sqr npr < sqr eps" using r lemSep2Symmetry by auto
          hence "sqr npr < sqr eps \<and> eps > 0" using epspos by auto
          hence npr: "npr < eps" 
            using lemSqrOrderedStrict[of "eps" "npr"] by auto
          hence npr1: "1 - npr > 1 - eps" 
            using diff_strict_left_mono by simp
      
          have npr_lt_e2: "npr < e/2" using npr eps_le_e2 le_less_trans by auto
      
          define nr where "nr = norm r" 
          hence "sqr nr = norm2 (\<alpha> \<otimes> y)" using alpha lemNormSqrIsNorm2 by presburger
          hence nr: "sqr nr = (sqr \<alpha>) * norm2 y" using lemNorm2OfScaled by auto
      
          have "axTriangleInequality (p\<ominus>r) r" using AxTriangleInequality by blast
          hence "(np \<le> npr + nr)" using np_def npr_def nr_def by simp
          hence "nr \<ge> 1 - npr" using np lemLEPlus by auto
          hence triangle1: "nr > 1 - eps" using npr1 le_less_trans by simp
          
          define nrp where "nrp = norm (r\<ominus>p)" 
          hence nrppr: "nrp = npr" using npr_def nrp_def lemSep2Symmetry[of "p" "r"] by auto
      
          have "axTriangleInequality (r\<ominus>p) p" using AxTriangleInequality by blast
          hence "(nr \<le> npr + 1)" 
            using np_def npr_def nr_def np nrp_def nrppr by auto
          hence triangle2: "nr < 1 + eps" 
            using npr add_strict_right_mono le_less_trans add_commute by simp
      
          have range: "(1 - eps) < nr < (1 + eps)" 
            using triangle1 triangle2  by simp
      
          (* Re-express in terms of y *)
          have "(ny = 0) \<longrightarrow> (y = origin)"
            using ny lemNormSqrIsNorm2[of "y"] lemNullImpliesOrigin
            by auto
          hence nynz: "ny \<noteq> 0" using y by auto
      
          have "norm ((1/ny)\<otimes>y) = ((abs (1/ny)) * ny)" using ny lemNormOfScaled[of "1/ny" "y"]  by auto
          hence nyunit: "norm ((1/ny)\<otimes>y) = 1" using y nynz ny lemNormNonNegative by auto
      
          have "norm r = ((abs \<alpha>) * ny)" using ny alpha lemNormOfScaled[of "\<alpha>" "y"] by auto
          hence nr_is_any: "nr = ((abs \<alpha>) * ny)" using nr_def lemSqrt by auto
      
          hence "(1 - eps) < ((abs \<alpha>) * ny) < (1 + eps)" using range by auto
          hence star: "abs (((abs \<alpha>) * ny) - 1) < eps" 
            using epspos lemAbsRange[of "eps" "1" "((abs \<alpha>) * ny)"] by auto
      
          have cases: "(\<alpha> > 0) \<or> (\<alpha> < 0)" using anz by auto
      
          (* Case 1 *)
          { assume apos: "\<alpha> > 0"
            hence "abs \<alpha> = \<alpha>" by auto
            hence case1range: "abs ((\<alpha> * ny) - 1) < eps" using star by auto 
      
            define w1 where "w1 = ((\<alpha> \<otimes> y) \<ominus> ((1/ny)\<otimes>y))"
            define nw1 where "nw1 = norm w1"
      
            have "(\<alpha> \<otimes> y) = ((1/ny) \<otimes> ((\<alpha> * ny) \<otimes> y))"
              using nynz lemScaleAssoc by auto
            hence "w1 = (((1/ny) \<otimes> ((\<alpha> * ny) \<otimes> y)) \<ominus> ((1/ny)\<otimes>y))"
              using w1_def by simp
            hence "w1 = ((1/ny) \<otimes>  (((\<alpha> * ny) \<otimes> y) \<ominus> y ))"
              using lemScaleDistribDiff[of "1/ny" "(\<alpha> * ny) \<otimes> y" "y"] by force
            hence "w1 = (((\<alpha> * ny) - 1) \<otimes> ((1/ny) \<otimes> y))"
              using lemScaleLeftDiffDistrib lemScaleCommute by auto
            hence 2: "norm w1 = (abs ((\<alpha> * ny) - 1))"
              using lemNormOfScaled[of "((\<alpha> * ny) - 1)" "(1/ny) \<otimes> y"] nyunit by auto
      
            (* Slow commands, so simplify *)
            {
              define pp where pp: "pp = (p\<ominus>(\<alpha>\<otimes>y))"
              define qq where qq: "qq = ((\<alpha>\<otimes>y) \<ominus> ((1/ny)\<otimes>y))"
              have "axTriangleInequality pp qq" using AxTriangleInequality by simp
              hence "norm (pp \<oplus> qq) \<le> norm pp + norm qq" by auto
              hence "norm ((p \<ominus> ((1/ny)\<otimes>y))) \<le> norm pp + norm qq" 
                using lemSumDiffCancelMiddle pp qq by simp
            hence "norm ((p \<ominus> ((1/ny)\<otimes>y))) \<le> norm (p\<ominus>r) + norm w1" 
              using alpha w1_def pp qq by auto
            }
            hence 3: "norm ((p \<ominus> ((1/ny)\<otimes>y))) \<le> npr + nw1"
              using nw1_def npr_def by force
        
            define nminus where "nminus = norm ((p \<ominus> ((1/ny)\<otimes>y)))"
        
            hence almost1:  "nminus \<le> npr + nw1" using 3 nminus_def by auto
      
            have "abs ((ny * \<alpha>) - 1) \<ge> 0" by auto
            hence "nw1 = abs ((\<alpha> * ny) - 1)" using nw1_def 2 lemSqrt by blast
            hence "nw1 < eps" using case1range le_less_trans by auto
            hence "nw1 < e/2" using eps_le_e2 le_less_trans by auto
        
            hence "nminus < (e/2 + e/2)" 
              using almost1 npr_lt_e2 add_strict_mono le_less_trans by simp
      
            hence "nminus < e" using lemSumOfTwoHalves by simp        
            hence "sqr nminus < sqr e" 
              using lemSqrMonoStrict[of "nminus" "e"] nminus_def 
                    lemNormNonNegative[of "((p \<ominus> ((1/ny)\<otimes>y)))"]
              by auto
      
            hence "norm2 ((p \<ominus> ((1/ny)\<otimes>y))) < sqr e"
              using lemNormSqrIsNorm2[of "((p \<ominus> ((1/ny)\<otimes>y)))"] nminus_def by auto
            hence "p within e of ((1/ny)\<otimes>y)" by auto 
            hence "((1/ny)\<otimes>y) within e of p" 
              using lemSep2Symmetry[of "((1/ny)\<otimes>y)"] by auto
          }
          hence case1: "(\<alpha> > 0) \<longrightarrow> (((1/ny)\<otimes>y) within e of p)" by blast
        
          (* Case 2 *)
          { assume aneg: "\<alpha> < 0"
            hence "abs \<alpha> = -\<alpha>" by auto
            hence "abs (-(\<alpha> * ny) - 1) < eps" using star by auto
            hence case2range: "abs (\<alpha>*ny + 1) < eps" 
              using lemAbsNegNeg[of "\<alpha>*ny" "1"] by auto
      
            define w2 where "w2 = ((\<alpha>\<otimes>y) \<oplus> ((1/ny)\<otimes>y))"
            define nw2 where "nw2 = norm w2"
      
            have "(\<alpha> \<otimes> y) = ((1/ny) \<otimes> ((\<alpha> * ny) \<otimes> y))"
              using nynz lemScaleAssoc by auto
            hence "w2 = (((1/ny) \<otimes> ((\<alpha>* ny) \<otimes> y)) \<oplus> ((1/ny)\<otimes>y))"
              using w2_def by simp
            also have "... = ((1/ny) \<otimes>  (((\<alpha> * ny) \<otimes> y) \<oplus> y ))"
              using lemScaleDistribSum[of "1/ny" "(\<alpha> * ny) \<otimes> y" "y"] by simp
            also have "... = (((\<alpha> * ny) + 1) \<otimes> ((1/ny) \<otimes> y))"
              using lemScaleLeftDiffDistrib[where b="-1"] lemScaleCommute by auto
            finally have 4: "norm w2 = (abs ((\<alpha> * ny) + 1))"
              using lemNormOfScaled[of "((\<alpha> * ny) + 1)" "(1/ny) \<otimes> y"] nyunit by auto
      
        (* Slow commands - simplify *)
            {
              define pp where pp: "pp = (p\<ominus>(\<alpha>\<otimes>y))"
              define qq where qq: "qq = ((\<alpha>\<otimes>y) \<oplus> ((1/ny)\<otimes>y))"
              have "axTriangleInequality pp qq" using AxTriangleInequality by simp
              hence "norm (pp \<oplus> qq) \<le> norm pp + norm qq" by auto
              hence "norm ((p \<oplus> ((1/ny)\<otimes>y))) \<le> norm pp + norm qq" 
                using lemDiffSumCancelMiddle pp qq by force
              hence "norm ((p \<oplus> ((1/ny)\<otimes>y))) \<le> norm (p\<ominus>r) + norm w2" 
                using alpha w2_def pp qq by auto
            }
            hence 5: "norm ((p \<oplus> ((1/ny)\<otimes>y))) \<le> npr + nw2" using nw2_def npr_def by auto
        
              
            define nplus where "nplus = norm ((p \<oplus> ((1/ny)\<otimes>y)))"
      
            hence almost2:  "nplus \<le> npr + nw2" using 5 nplus_def by auto
      
            have "abs ((ny * \<alpha>) - 1) \<ge> 0" by auto
            hence "nw2 = abs ((\<alpha> * ny) + 1)" using nw2_def 4 lemSqrt[of "norm2 w2"] by auto
            hence "nw2 < eps" using case2range le_less_trans by auto
            hence "nw2 < e/2" using eps_le_e2 le_less_trans by auto
        
            hence "nplus < (e/2 + e/2)" 
              using almost2 npr_lt_e2 add_strict_mono le_less_trans by simp
      
            hence "nplus < e" using lemSumOfTwoHalves by simp        
            hence "sqr nplus < sqr e" using 
                    lemSqrMonoStrict[of "nplus" "e"] nplus_def 
                    lemNormNonNegative[of "((p \<oplus> ((1/ny)\<otimes>y)))"]
              by auto
      
            hence "norm2 ((p \<oplus> ((1/ny)\<otimes>y))) < sqr e"
              using lemNormSqrIsNorm2[of "((p \<oplus> ((1/ny)\<otimes>y)))"] nplus_def by auto
      
            hence "sep2 p ((-1/ny)\<otimes>y) < sqr e" by simp
            hence "(((-1/ny)\<otimes>y) within e of p)" 
              using lemSep2Symmetry[of "((-1/ny)\<otimes>y)"] by auto
            }
            hence case2: "(\<alpha> < 0) \<longrightarrow> (((-1/ny)\<otimes>y) within e of p)" by blast
          
            hence "(((1/ny)\<otimes>y) within e of p) \<or> (((-1/ny)\<otimes>y) within e of p)"
              using cases case1 by auto
          }
        hence "((y within d of origin) \<and> (y \<noteq> origin) \<and> (y \<in> wl) \<and> (norm y = ny))
              \<longrightarrow> ((((1/ny)\<otimes>y) within e of p) \<or> (((-1/ny)\<otimes>y) within e of p))"
          by blast
      }
      hence "\<exists> \<delta> > 0 .\<forall> y ny .((y within \<delta> of origin) 
                      \<and> (y \<noteq> origin) \<and> (y \<in> wl) \<and> (norm y = ny))
              \<longrightarrow> ((((1/ny)\<otimes>y) within e of p) \<or> (((-1/ny)\<otimes>y) within e of p))"
          using dprops by blast
    }
    hence "e > 0 \<longrightarrow> 
    (\<exists> \<delta> > 0 .\<forall> y ny .((y within \<delta> of origin) \<and> (y \<noteq> origin) \<and> (y \<in> wl) \<and> (norm y = ny))
              \<longrightarrow> ((((1/ny)\<otimes>y) within e of p) \<or> (((-1/ny)\<otimes>y) within e of p)))"
        by blast
  }
  thus ?thesis by blast
qed

(* Generalised version based at x instead of origin *)
   
lemma sublemma3Translation: 
assumes "onLine p l"
and     "norm2 (p\<ominus>x) = 1"
and     "tangentLine l wl x"
shows   "\<forall> \<epsilon> > 0 . \<exists> \<delta> > 0 . \<forall> y nyx . 
                ((y within \<delta> of x) \<and> (y \<noteq> x) \<and> (y \<in> wl) \<and> (norm (y\<ominus>x) = nyx))
            \<longrightarrow>
                (((1/nyx)\<otimes>(y\<ominus>x)) within \<epsilon> of (p\<ominus>x)) 
                              \<or> (((-1/nyx)\<otimes>(y\<ominus>x)) within \<epsilon> of (p\<ominus>x))"
proof -
  define pre 
    where pre: "pre = (\<lambda> d y nyx . (y within d of x) \<and> (y \<noteq> x) \<and> (y \<in> wl) \<and> (norm (y\<ominus>x) = nyx))"
  define post 
    where post: "post = (\<lambda> e y nyx . (((1/nyx)\<otimes>(y\<ominus>x)) within e of (p\<ominus>x)) 
                              \<or> (((-1/nyx)\<otimes>(y\<ominus>x)) within e of (p\<ominus>x)))"

  define T where "T  = mkTranslation (origin \<ominus> x)"
  hence transT: "translation T" using lemMkTrans by blast
  have T: "\<forall>p. T p = (p \<oplus> (origin \<ominus> x))" using T_def by simp

  define p' where p': "p' = T p"
  define l' where l': "l' = (applyToSet (asFunc T) l)"
  define x' where x': "x' = T x"
  define wl' where wl': "wl' = (applyToSet (asFunc T) wl)"

  have 1: "onLine p' l'" 
    using assms(1) T p' l' lemOnLineTranslation[of "T" "l" "p"]
    by blast

  have x'0: "x' = origin" using T x' add_diff_eq by auto
  hence "sep2 p' origin = 1" 
    using T assms(2) p' lemTranslationPreservesSep2 by simp
  hence 2: "norm2 p' = 1" by auto

  have "tangentLine (applyToSet (asFunc T) l)
                    (applyToSet (asFunc T) wl)  (T x)"
    using transT assms(3) lemTangentLineTranslation[of "T" "x" "wl" "l"]
    by auto
  hence 3: "tangentLine l' wl' origin" using l' wl' x' x'0 by auto

  hence conc: "\<forall> \<epsilon> > 0 . \<exists> \<delta> > 0 . \<forall> y' ny' . (
       ((y' within \<delta> of origin) \<and> (y' \<noteq> origin) \<and> (y' \<in> wl') \<and> (norm y' = ny'))
        \<longrightarrow>
       ( (((1/ny')\<otimes>y') within \<epsilon> of p') \<or> (((-1/ny')\<otimes>y') within \<epsilon> of p')))"
    using 1 2 3 sublemma3[of "l'" "p'"]
    by auto

  { fix e
    assume epos: "e > 0"
    then obtain d where d: "(d > 0) \<and> (\<forall> y' ny' . (
       ((y' within d of origin) \<and> (y' \<noteq> origin) \<and> (y' \<in> wl') \<and> (norm y' = ny'))
        \<longrightarrow>
       ( (((1/ny')\<otimes>y') within e of p') \<or> (((-1/ny')\<otimes>y') within e of p'))))"
      using conc by blast

    { fix y nyx
      assume hyp: "pre d y nyx"

      define y' where y': "y' = T y"
      hence rtp1: "y' within d of origin" 
        using transT hyp x' x'0 lemBallTranslation pre by auto

      have p'px: "p' = (p \<ominus> x)" using p' T by simp
      have y'yx: "y' = (y \<ominus> x)" using y' T by simp
      hence nyx: "norm y' = nyx" using hyp pre by force

      { have "(T x = x')  \<and>  (T y = y')  \<and>  (injective (asFunc T))"
          using x' y' lemTranslationInjective[of "T"] transT by blast
        moreover have "x \<noteq> y" using hyp pre by auto
        ultimately have  "y' \<noteq> x'"by auto
      }
      hence rtp2: "y' \<noteq> origin" using x'0 by simp

      have rtp3: "y' \<in> wl'" using hyp pre y' wl' by force

      hence "(y' within d of origin) \<and> (y' \<noteq> origin) \<and> (y' \<in> wl') \<and> (norm y' = nyx)"
        using rtp1 rtp2 rtp3 nyx by blast

      hence "(((1/nyx)\<otimes>y') within e of p') \<or> (((-1/nyx)\<otimes>y') within e of p')"
        using d by auto
      hence "post e y nyx" using post y'yx p'px  by auto
    }
    hence "\<forall> y nyx . pre d y nyx \<longrightarrow> post e y nyx" by auto
    hence "\<exists>\<delta>>0. \<forall> y nyx . pre \<delta> y nyx \<longrightarrow> post e y nyx" using d by auto
  }
  hence "\<forall>\<epsilon>>0 . \<exists>\<delta>>0. \<forall> y nyx . pre \<delta> y nyx \<longrightarrow> post \<epsilon> y nyx" by auto
  thus ?thesis using post pre by blast
qed




end (* of class Sublemma3 *)

end (* of theory Sublemma3 *)

