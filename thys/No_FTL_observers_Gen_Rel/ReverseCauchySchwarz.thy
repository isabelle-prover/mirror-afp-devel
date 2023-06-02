(*
  ReverseCauchySchwarz.thy
  Author: Mike Stannett
  Date: Jan 2023
*)

section \<open> ReverseCauchySchwarz \<close>

text \<open>This theory defines and proves the "reverse" Cauchy-Schwarz inequality
for timelike vectors in the Minkowski metric.\<close>

theory ReverseCauchySchwarz
  imports CauchySchwarz
begin

text \<open>Rather than construct the proof, one could simply have asserted the
claim as an axiom. We did this during development of the main proof, and then
returned to this section later. In practice the axiom we chose to assert
contained far more information than required, because we eventually found
a proof that only required consideration of timelike vectors (our axiom
considered lightlike vectors as well).
\<close>

(*
  assumes AxReverseCauchySchwarz:
    "((causal u) \<and> (causal v)) \<longrightarrow> ((
           (parallel u v) \<longleftrightarrow> ( sqr (u \<odot>m v) = (mNorm2 u)*(mNorm2 v) ) )
        \<and> (
           (\<not> parallel u v) \<longleftrightarrow> ( sqr (u \<odot>m v) > (mNorm2 u)*(mNorm2 v) ) ))"
*)

class ReverseCauchySchwarz = CauchySchwarz

begin


lemma lemTimelikeNotZeroTime:
  assumes "timelike v"
    shows "tval v \<noteq> 0"
proof -
  { assume converse: "tval v = 0"
    have "sNorm2 (sComponent v) < sqr (tval v)" using assms by auto
    hence "sNorm2 (sComponent v) < 0" using converse by auto
    hence "False" using local.add_less_zeroD local.not_square_less_zero by blast 
  }
  thus ?thesis by auto
qed


lemma lemOrthogmToTimelike:
  assumes "timelike u"
and "orthogm u v"
and "v \<noteq> origin"
shows "spacelike v"
proof -
  have tvalu: "tval u \<noteq> 0" using assms(1) lemTimelikeNotZeroTime by auto

  define us where us: "us = sComponent u"
  define vs where vs: "vs = sComponent v"
  have "sqr ((tval u) * (tval v)) = sqr (us \<odot>s vs)" using assms(2) us vs by auto
  also have "\<dots> \<le> sNorm2 us * sNorm2 vs" using lemCauchySchwarzSqr by auto
  finally have inequ: "sqr (tval u) * sqr (tval v) \<le> sNorm2 us * sNorm2 vs" 
    using mult_assoc mult_commute by auto

  have ifvsnz: "vs \<noteq> sOrigin \<longrightarrow> sNorm2 vs > 0"
        by (meson local.add_less_zeroD local.antisym_conv3 
            local.lemSpatialNullImpliesSpatialOrigin local.not_square_less_zero)

  have iftv0: "tval v = 0 \<longrightarrow> spacelike v"
  proof -
    { assume v0: "tval v = 0"
      hence "vs \<noteq> sOrigin" using assms vs by auto
      hence "sNorm2 vs > 0" using ifvsnz by auto
      hence "spacelike v" using v0 vs
        by (metis local.less_iff_diff_less_0 local.mult_not_zero)
    }
    thus ?thesis by auto
  qed

  moreover have "(tval v \<noteq> 0 \<and> vs \<noteq> sOrigin) \<longrightarrow> spacelike v"
  proof -
    { assume vnz: "(tval v \<noteq> 0 \<and> vs \<noteq> sOrigin)"

      have utpos: "sqr (tval u) > 0" using tvalu lemSquaresPositive by simp
      have vspos: "sNorm2 vs > 0" using vnz ifvsnz by auto

      have "sqr (tval u) * sqr (tval v) \<le> sNorm2 us * sNorm2 vs" using inequ by simp
      hence "sqr (tval v) \<le> sNorm2 us * sNorm2 vs / sqr (tval u)"
        using utpos
        by (metis local.divide_right_mono local.divisors_zero local.dual_order.strict_implies_order 
                  local.nonzero_mult_div_cancel_left tvalu)
      hence "sqr (tval v) / sNorm2 vs \<le> sNorm2 us / sqr (tval u)"
        using vspos mult_commute by (simp add: local.mult_imp_div_pos_le)

      moreover have "sNorm2 us / sqr (tval u) < 1" using assms(1) us utpos by auto
      ultimately have "sqr (tval v) / sNorm2 vs < 1" by simp
      hence "spacelike v" using vs vspos by auto
    }
    thus ?thesis by auto
  qed

  moreover have "\<not> (tval v \<noteq> 0 \<and> vs = sOrigin)" 
  proof -
    { assume "(tval v \<noteq> 0 \<and> vs = sOrigin)"
      hence "(u \<odot>m v) \<noteq> 0" using tvalu vs by auto
      hence "False" using assms by auto
    }
    thus ?thesis by auto
  qed

  ultimately show ?thesis by blast
qed


lemma lemNormaliseTimelike:
  assumes "timelike v"
and       "s = sComponent ((1/tval v)\<otimes>v)"
shows     "(0 \<le> sNorm2 s < 1) \<and> (tval ((1/tval v)\<otimes>v) = 1)"
proof -
  have "sqr (tval v) > sNorm2 (sComponent v)" using assms by auto
  hence "1 > sqr (1/tval v) * sNorm2 (sComponent v)" 
    using local.divide_less_eq by force
  hence "sNorm2 s < 1" using lemSNorm2OfScaled[of "1/tval v" "sComponent v"] assms 
    by auto
  hence "(0 \<le> sNorm2 s < 1)" by simp
  moreover have "(tval ((1/tval v)\<otimes>v) = 1)" 
  proof -
    have "sqr (tval v) > sNorm2 (sComponent v)" using assms by auto
    hence "sqr (tval v) \<noteq> 0" 
      by (metis local.add_less_zeroD local.not_square_less_zero)
    hence "tval v \<noteq> 0" by auto
    thus ?thesis by auto
  qed
  ultimately show ?thesis by blast
qed


lemma lemReverseCauchySchwarz:
  assumes "timelike X \<and> timelike D"
shows     "sqr (X \<odot>m D) \<ge> (mNorm2 X)*(mNorm2 D)"
proof -
  have case1: "parallel X D \<longrightarrow> ?thesis"
  proof -
    { assume "parallel X D"
      then obtain a where a: "X = (a \<otimes> D)" by auto
      hence "(X \<odot>m D) = a * mNorm2 D" using lemMDotScaleLeft by auto
      moreover have "mNorm2 X = (sqr a) * mNorm2 D" using lemMNorm2OfScaled a by auto
      ultimately have "sqr (X \<odot>m D) = (mNorm2 X)*(mNorm2 D)" 
        using local.lemSqrMult mult_assoc by auto
    }
    thus ?thesis by simp
  qed

  have "(\<not> parallel X D) \<longrightarrow> ?thesis"
  proof -
    { assume case2: "\<not> (parallel X D)"
      define u where u: "u = ((1/tval X)\<otimes>X)"
      define v where v: "v = ((1/tval D)\<otimes>D)"
      define su where su: "su = (sComponent u)"
      define sv where sv: "sv = (sComponent v)"
    
      have sphere: "(0 \<le> sNorm2 su < 1) \<and> (0 \<le> sNorm2 sv < 1)"
        using lemNormaliseTimelike u su v sv assms by blast
      have tvals1: "tval u = 1 \<and> tval v = 1"
        using lemNormaliseTimelike u su v sv assms by blast
    
      (* the theorem works for u and v *)
      have worksuv: "sqr (u \<odot>m v) > (mNorm2 u)*(mNorm2 v)"
      proof -
    
        have uupos: "mNorm2 u > 0" using assms u lemNormaliseTimelike by auto
        have vvpos: "mNorm2 v> 0" using assms v lemNormaliseTimelike by auto
        have uvpos: "(u \<odot>m v) > 0" 
        proof - 
          have "sqr (sdot su sv) \<le> (sNorm2 su) * (sNorm2 sv)" 
            using lemCauchySchwarzSqr by auto
          also have "\<dots> < 1" 
            using mult_le_one sphere local.mult_strict_mono by fastforce
          finally have "sqr (sdot su sv) < 1" by auto
          hence "(sdot su sv) < 1"
            using local.less_1_mult local.not_less_iff_gr_or_eq by fastforce
          thus ?thesis using u v su sv tvals1 by auto
        qed
        
        define a where a: "a = (u \<odot>m v)/(mNorm2 v)"
        define up where up: "up = (a \<otimes> v)"
        define uo where uo: "uo = (u \<ominus> up)"
    
        have apos: "a > 0" using a uvpos vvpos by auto
    
        have updotup: "mNorm2 up > 0" 
        proof -
          have "mNorm2 up = (sqr a) * mNorm2 v" using up lemMNorm2OfScaled by auto
          thus ?thesis using apos lemSquaresPositive vvpos by auto
        qed
    
        have uparts: "u = (up \<oplus> uo) \<and> parallel up v \<and> orthogm uo v \<and> (up \<odot>m v) = (u \<odot>m v)"
          using lemMDecomposition a up uo vvpos uvpos by auto
    
        have updotuo: "(up \<odot>m uo) = 0"
        proof -
          have "(up \<odot>m uo) = a*(v \<odot>m uo)" using up lemMDotScaleLeft by auto
          moreover have "(v \<odot>m uo) = (uo \<odot>m v)" using mult_commute by auto
          ultimately have "(up \<odot>m uo) = 0" using uparts by force
          thus ?thesis by auto
        qed
    
        have udotu: "mNorm2 u = mNorm2 up + mNorm2 uo"
        proof -
          have "mNorm2 u = mNorm2 (up \<oplus> uo)" using uparts by auto
          also have "\<dots> = mNorm2 up + 2*(up \<odot>m uo) + mNorm2 uo" using lemMNorm2OfSum by auto
          finally show ?thesis using updotuo by auto
        qed
    
        moreover have uodotuo: "mNorm2 uo < 0"
        proof -
          have "timelike up" using updotup by auto
          moreover have "orthogm up uo" using updotuo by auto
          moreover have "uo \<noteq> origin" 
          proof -    
            define \<alpha> where \<alpha>: "\<alpha> = (tval X)*a*(1/tval D)"
            have \<alpha>pos: "\<alpha> \<noteq> 0" using apos lemTimelikeNotZeroTime assms \<alpha> by simp
    
            { assume "uo = origin"
              hence "u = (a \<otimes> v)" using uo up by auto
              moreover have "X = ((tval X)\<otimes>u)" 
                using u lemScaleAssoc assms lemTimelikeNotZeroTime by auto
              ultimately have "X = ((tval X)\<otimes>(a\<otimes>v))" by auto
              hence "X = ((tval X)\<otimes>(a\<otimes>((1/tval D)\<otimes>D)))" using v by auto
              hence "X = (\<alpha> \<otimes> D)" using \<alpha> lemScaleAssoc mult_assoc 
                by (metis Point.select_convs(3-4))
              hence "False" using case2 \<alpha>pos by blast
            }
            thus ?thesis by auto
          qed
          ultimately show ?thesis using lemOrthogmToTimelike by auto
        qed
  
        ultimately have upgeu: "mNorm2 up > mNorm2 u" by auto
      
        have "(u \<odot>m v) = (up \<odot>m v)" using uparts by auto
        also have "\<dots> = a * mNorm2 v" using up lemMDotScaleLeft by auto
        finally have final: "sqr (u \<odot>m v) = ((sqr a)*mNorm2 v) * (mNorm2 v)" 
          using lemSqrMult[of "a" "mNorm2 v"] mult_assoc by auto
    
        hence "sqr (u \<odot>m v) = (mNorm2 up)*(mNorm2 v)" using lemMNorm2OfScaled up by auto
        thus ?thesis
          using upgeu vvpos local.mult_strict_right_mono by simp
      qed
      
      (* and so it works for X and D as well *)
      have "(u \<odot>m v) = (((1/tval X)\<otimes>X) \<odot>m ((1/tval D)\<otimes>D))" using u v by auto
      hence udotv: "(u \<odot>m v) = (1/tval X)*(1/tval D) * (X \<odot>m D)" 
        using lemMDotScaleRight lemMDotScaleLeft mult_assoc mult_commute by metis
    
      have udotu: "mNorm2 u = sqr (1/tval X) * mNorm2 X" using u lemMNorm2OfScaled by blast
      moreover have vdotv: "mNorm2 v = sqr (1/tval D) * mNorm2 D" using v lemMNorm2OfScaled by blast
      ultimately have "(mNorm2 u)*(mNorm2 v) = sqr ((1/tval X)*(1/tval D)) * mNorm2 X * mNorm2 D"
        using mult_commute mult_assoc by auto
    
      hence
        "sqr ((1/tval X)*(1/tval D) * (X \<odot>m D)) > 
                         sqr ((1/tval X)*(1/tval D)) * mNorm2 X * mNorm2 D"
        using worksuv udotv by auto
      moreover have "sqr ((1/tval X)*(1/tval D)) > 0" 
        using lemTimelikeNotZeroTime 
        by (metis calculation local.lemSquaresPositive local.mult_cancel_left1)
      ultimately have ?thesis 
        using mult_less_cancel_left_pos[of "sqr ((1/tval X)*(1/tval D))"]
        by auto
    }
  
    thus ?thesis by auto
  qed

  thus ?thesis using case1 by auto
qed


end (* of class ReverseCauchySchwarz *) 

end (* of theory ReverseCauchySchwarz *)
