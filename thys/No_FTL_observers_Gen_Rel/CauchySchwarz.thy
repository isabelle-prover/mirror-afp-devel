(*
   Mike Stannett
   Date: Feb 2023
*)

section \<open> CauchySchwarz \<close>

text \<open>This theory defines and proves the Cauchy-Schwarz inequality for
both spatial and spacetime vectors.\<close>

theory CauchySchwarz
  imports Vectors
begin

(* Needs rewriting using locales implemented by 3- and 4-vectors *)

text \<open>We essentially prove the same result twice, once for 3-dimensional 
spatial points, and once for 4-dimensional spacetime points. While this
is clearly inefficient, it keeps things straightforward for non-Isabelle experts.\<close>

class CauchySchwarz = Vectors
begin

(* CAUCHY-SCHWARZ LEMMA FOR 4-VECTORS *)
lemma lemCauchySchwarz4:
  shows "abs (dot u v) \<le> (norm u)*(norm v)"
proof -
  have vorigin: "v = origin \<longrightarrow> abs (dot u v) \<le> (norm u)*(norm v)"
  proof -
    { assume "v = origin"
      hence "abs (dot u v) = 0" by simp
      also have "\<dots> \<le> (norm u)*(norm v)" using lemNormNonNegative by simp
      finally have "abs (dot u v) \<le> (norm u)*(norm v)" by auto
    }
    thus ?thesis by blast
  qed

  define a where "a = dot v v"
  define b where "b = 2 * dot u v"
  define c where "c = dot u u"

  { fix x :: "'a"
    define w where "w = (u \<oplus> (x \<otimes> v))"
    have ww: "(dot w w) \<ge> 0" by simp

    define xv where xv: "xv = (x \<otimes> v)"
    define middle2 where "middle2 = dot u xv + dot xv u"


    have "dot xv u = dot u xv" using lemDotCommute by blast
    hence "middle2 = dot u xv + dot u xv" using middle2_def by simp
    also have "... = 2 * dot u xv" using mult_2 by simp
    finally have bterm: "middle2 = b * x" 
      using lemDotScaleRight mult_assoc mult_commute b_def xv by auto

    have vxv: "(dot v xv) = (x * dot v v)"using xv lemDotScaleRight by blast
    have "dot xv xv = x * (dot v xv)" using lemDotScaleLeft xv by blast
    also have "... = (sqr x)*(dot v v)" using vxv mult_assoc by simp
    finally have aterm: "dot xv xv = a*(sqr x)" using mult_commute a_def by simp
      
    have uw: "dot u w = dot u u + dot u xv" using lemDotSumRight w_def xv by blast
    have vw: "dot xv w = dot xv u + dot xv xv" using lemDotSumRight w_def xv by blast
    have "dot w w = dot u w + dot xv w" using lemDotSumLeft w_def xv by blast
    also have "... = (dot u u + dot u xv) + (dot xv u + dot xv xv)"
      using uw vw by simp
    also have "... = (dot u u) + (dot u xv + dot xv u) + dot xv xv"
      using add_assoc by force
    also have "... = (dot u u) + middle2 + dot xv xv"
      using middle2_def by simp
    also have "... = c + b*x + a*(sqr x)" using c_def bterm aterm by force
    finally have "dot w w = a*(sqr x) + b*x + c" using add_commute add_assoc by auto

    hence "a*sqr(x) + b*x + c \<ge> 0" using ww by simp
  }
  hence quadratic: "\<forall> x. a*sqr(x) + b*x + c \<ge> 0" by auto

  { assume vnot0: "v \<noteq> origin"
    hence "a > 0" using a_def lemNullImpliesOrigin[of "v"]
      by (metis local.AxEField local.not_less local.not_less_iff_gr_or_eq 
                local.not_sum_squares_lt_zero dot.simps)
    hence "(sqr b) \<le> 4*a*c" using lemQuadraticGEZero quadratic by auto
    hence "(sqr b) \<le> 4*(dot v v)*(dot u u)" using a_def c_def by auto
    hence sqrle: "(sqr (abs b)) \<le> 4*(dot v v)*(dot u u)" by auto

    define nv where nv: "nv = norm v" 
    define nu where nu: "nu = norm u"

    have nvpos: "nv \<ge> 0" using nv lemNormNonNegative by auto
    have nupos: "nu \<ge> 0" using nu lemNormNonNegative by auto
    hence nvnu: "2*nv*nu \<ge> 0" using nvpos by auto

    have n2v: "norm2 v = sqr nv" using AxEField nv nvpos lemNormSqrIsNorm2 by presburger
    have n2u: "norm2 u = sqr nu" using AxEField nu nupos lemNormSqrIsNorm2 by presburger

    have "4*(dot v v)*(dot u u) = 4*(norm2 v)*(norm2 u)" by auto
    also have "... = (sqr 2)*(sqr nv)*(sqr nu)" using n2u n2v by auto
    also have "... = (sqr (2* nv))*(sqr nu)" using lemSqrMult[of "2" "nv"] by auto
    also have "... = sqr (2*nv*nu)" using lemSqrMult[of "2*nv" "nu"] by auto

    finally have "(sqr (abs b)) \<le> sqr (2*nv*nu)" using sqrle by auto
    hence bnvnu: "abs b \<le> 2*nv*nu" 
      using nu nv nvnu lemSqrOrdered[of "2*nv*nu"] 
      by auto

    have pos2: "0 < 2" by simp
    have "b = 2*dot u v" using b_def by auto
    hence "abs b = 2*abs(dot u v)" using abs_mult by auto
    hence "2*abs(dot u v) \<le> 2*(nv*nu)" using bnvnu mult_assoc by auto
    hence "2*abs(dot u v) \<le> 2*(nu*nv)" using mult_commute by simp
    hence "abs(dot u v) \<le> (nu*nv)" using mult_le_cancel_left[of "2"] pos2 by blast
    hence ?thesis using nu nv by auto
  }
  hence "(v \<noteq> origin) \<longrightarrow> ?thesis" by auto

  thus ?thesis using vorigin by auto
qed


lemma lemCauchySchwarzSqr4:
  shows "sqr(dot u v) \<le> (norm2 u)*(norm2 v)"
proof -
  have 1: "abs(dot u v) \<ge> 0" by simp
  have "sqr(dot u v) = sqr(abs(dot u v))" by simp
  also have "\<dots> \<le> sqr((norm u)*(norm v))" using 1 lemCauchySchwarz4 lemSqrMono by blast
  also have "\<dots> = sqr(norm u) * sqr(norm v)" using lemSqrMult by auto
  also have "\<dots> = norm2 u * norm2 v" 
    using lemSquareOfSqrt lemSqrt AxEField lemNormSqrIsNorm2
    by force
  finally show ?thesis by simp
qed



(* CAUCHY-SCHWARZ LEMMA FOR SPATIAL VECTORS *)
lemma lemCauchySchwarz:
  shows "abs (sdot u v) \<le> (sNorm u)*(sNorm v)"
proof -
  have vorigin: "v = sOrigin \<longrightarrow> abs (sdot u v) \<le> (sNorm u)*(sNorm v)"
  proof -
    { assume "v = sOrigin"
      hence "abs (sdot u v) = 0" by simp
      also have "\<dots> \<le> (sNorm u)*(sNorm v)" using lemSNormNonNeg by simp
      finally have "abs (sdot u v) \<le> (sNorm u)*(sNorm v)" by auto
    }
    thus ?thesis by blast
  qed

  define a where "a = sdot v v"
  define b where "b = 2 * sdot u v"
  define c where "c = sdot u u"

  { fix x :: "'a"
    define w where "w = (u \<oplus>s (x \<otimes>s v))"
    have ww: "(sdot w w) \<ge> 0" by simp

    define xv where xv: "xv = (x \<otimes>s v)"
    define middle2 where "middle2 = sdot u xv + sdot xv u"


    have "sdot xv u = sdot u xv" using lemSDotCommute by blast
    hence "middle2 = sdot u xv + sdot u xv" using middle2_def by simp
    also have "... = 2 * sdot u xv" using mult_2 by simp
    finally have bterm: "middle2 = b * x" 
      using lemSDotScaleRight mult_assoc mult_commute b_def xv by auto

    have vxv: "(sdot v xv) = (x * sdot v v)"using xv lemSDotScaleRight by blast
    have "sdot xv xv = x * (sdot v xv)" using lemSDotScaleLeft xv by blast
    also have "... = (sqr x)*(sdot v v)" using vxv mult_assoc by simp
    finally have aterm: "sdot xv xv = a*(sqr x)" using mult_commute a_def by simp
      
    have uw: "sdot u w = sdot u u + sdot u xv" using lemSDotSumRight w_def xv by blast
    have vw: "sdot xv w = sdot xv u + sdot xv xv" using lemSDotSumRight w_def xv by blast
    have "sdot w w = sdot u w + sdot xv w" using lemSDotSumLeft w_def xv by blast
    also have "... = (sdot u u + sdot u xv) + (sdot xv u + sdot xv xv)"
      using uw vw by simp
    also have "... = (sdot u u) + (sdot u xv + sdot xv u) + sdot xv xv"
      using add_assoc by force
    also have "... = (sdot u u) + middle2 + sdot xv xv"
      using middle2_def by simp
    also have "... = c + b*x + a*(sqr x)" using c_def bterm aterm by force
    finally have "sdot w w = a*(sqr x) + b*x + c" using add_commute add_assoc by auto

    hence "a*sqr(x) + b*x + c \<ge> 0" using ww by simp
  }
  hence quadratic: "\<forall> x. a*sqr(x) + b*x + c \<ge> 0" by auto

  { assume vnot0: "v \<noteq> sOrigin"
    hence "a > 0" using a_def lemSpatialNullImpliesSpatialOrigin[of "v"]
      by (metis local.AxEField local.not_less local.not_less_iff_gr_or_eq 
                local.not_sum_squares_lt_zero sdot.simps)
    hence "(sqr b) \<le> 4*a*c" using lemQuadraticGEZero quadratic by auto
    hence "(sqr b) \<le> 4*(sdot v v)*(sdot u u)" using a_def c_def by auto
    hence sqrle: "(sqr (abs b)) \<le> 4*(sdot v v)*(sdot u u)" by auto

    define nv where nv: "nv = sNorm v" 
    define nu where nu: "nu = sNorm u"

    have nvpos: "nv \<ge> 0" using nv lemSNormNonNeg by auto
    have nupos: "nu \<ge> 0" using nu lemSNormNonNeg by auto
    hence nvnu: "2*nv*nu \<ge> 0" using nvpos by auto

    have n2v: "sNorm2 v = sqr nv" using AxEField lemSquareOfSqrt nv nvpos by auto
    have n2u: "sNorm2 u = sqr nu" using AxEField lemSquareOfSqrt nu nvpos by auto

    have "4*(sdot v v)*(sdot u u) = 4*(sNorm2 v)*(sNorm2 u)" by auto
    also have "... = (sqr 2)*(sqr nv)*(sqr nu)" using n2u n2v by auto
    also have "... = (sqr (2* nv))*(sqr nu)" using lemSqrMult[of "2" "nv"] by auto
    also have "... = sqr (2*nv*nu)" using lemSqrMult[of "2*nv" "nu"] by auto

    finally have "(sqr (abs b)) \<le> sqr (2*nv*nu)" using sqrle by auto
    hence bnvnu: "abs b \<le> 2*nv*nu" 
      using nu nv nvnu lemSqrOrdered[of "2*nv*nu"] 
      by auto

    have pos2: "0 < 2" by simp
    have "b = 2*sdot u v" using b_def by auto
    hence "abs b = 2*abs(sdot u v)" using abs_mult by auto
    hence "2*abs(sdot u v) \<le> 2*(nv*nu)" using bnvnu mult_assoc by auto
    hence "2*abs(sdot u v) \<le> 2*(nu*nv)" using mult_commute by simp
    hence "abs(sdot u v) \<le> (nu*nv)" using mult_le_cancel_left[of "2"] pos2 by blast
    hence ?thesis using nu nv  by auto
  }
  hence "(v \<noteq> sOrigin) \<longrightarrow> ?thesis" by auto

  thus ?thesis using vorigin by auto
qed


lemma lemCauchySchwarzSqr:
  shows "sqr(sdot u v) \<le> (sNorm2 u)*(sNorm2 v)"
proof -
  have 1: "abs(sdot u v) \<ge> 0" by simp
  have "sqr(sdot u v) = sqr(abs(sdot u v))" by simp
  also have "\<dots> \<le> sqr((sNorm u)*(sNorm v))" using 1 lemCauchySchwarz lemSqrMono  by blast
  also have "\<dots> = sqr(sNorm u) * sqr(sNorm v)" using lemSqrMult by auto
  also have "\<dots> = sNorm2 u * sNorm2 v" using lemSquareOfSqrt lemSqrt AxEField by auto
  finally show ?thesis by simp
qed


  


lemma lemCauchySchwarzEquality:
  assumes "sqr (sdot u v) = (sNorm2 u)*(sNorm2 v)"
and       "u \<noteq> sOrigin \<and> v \<noteq> sOrigin"
  shows   "\<exists> a \<noteq> 0 . u = (a \<otimes>s v)"
proof -
  define a where a: "a = (sdot u v)/(sNorm2 v)"
  have uvnz: "sNorm2 u \<noteq> 0 \<and> sNorm2 v \<noteq> 0" using assms lemSpatialNullImpliesSpatialOrigin by blast
  hence "sqr (sdot u v) \<noteq> 0" using assms by auto
  hence anz: "a \<noteq> 0" using assms uvnz a by auto

  define upv where upv: "upv = (a \<otimes>s v)"
  hence sdotupv: "sdot upv v = sdot u v"
  proof -
    have "sdot upv v = a * sNorm2 v" using upv lemSDotScaleLeft by auto
    thus ?thesis using a uvnz by auto
  qed
  have sn2upv: "sNorm2 upv = (sqr a)*sNorm2 v" using upv lemSNorm2OfScaled by auto

  define uov where uov: "uov = (u \<ominus>s upv)"
  have usum: "u = (upv \<oplus>s uov)" using uov add_diff_eq by auto
  hence sdotuov: "sdot uov v = 0" using lemSDotSumLeft sdotupv by force
  hence pdoto: "sdot uov upv = 0" using upv lemSDotScaleRight local.mult_not_zero by metis

  (* lhs *)
  have "sqr (sdot u v) = sqr (sdot (a \<otimes>s v) v)" using sdotupv upv by auto
  also have "\<dots> = (sqr a) * sqr (sNorm2 v)" 
    using lemSDotScaleLeft[of "a" "v" "v"] lemSqrMult[of "a"] by auto
  finally have lhs: "sqr (sdot u v) = (sqr a) * sqr (sNorm2 v)" by auto

  (* rhs *)
  have "sNorm2 u = sNorm2 upv + 2*(upv \<odot>s uov) + sNorm2 uov" using lemSNorm2OfSum usum by auto
  also have "\<dots> = (sqr a)*sNorm2 v + sNorm2 uov" using sn2upv pdoto lemSDotCommute by auto
  finally have rhs: "(sNorm2 u)*(sNorm2 v) = (sqr a)*sqr(sNorm2 v) + (sNorm2 uov)*(sNorm2 v)"
    using distrib_right[of "(sqr a)*sNorm2 v" "sNorm2 uov" "sNorm2 v"]
          mult_assoc by auto

  hence "(sqr a) * sqr (sNorm2 v) = (sqr a)*sqr(sNorm2 v) + (sNorm2 uov)*(sNorm2 v)"
    using lhs assms(1) by auto
  hence "(sNorm2 uov)*(sNorm2 v) = 0" using add_diff_eq by auto
  hence "uov = sOrigin" using uvnz lemSpatialNullImpliesSpatialOrigin by auto

  hence "a \<noteq> 0 \<and> u = (a \<otimes>s v)" using anz usum upv by auto
  thus ?thesis by auto
qed



lemma lemCauchySchwarzEqualityInUnitSphere:
  assumes "(sNorm2 u \<le> 1) \<and> (sNorm2 v \<le> 1)"
and       "sdot u v = 1"
shows     "u = v"
proof -
  have uvnz: "u \<noteq> sOrigin \<and> v \<noteq> sOrigin" using assms(2) by auto
  { assume ass: "(sNorm2 u < 1) \<or> (sNorm2 v < 1)"
    have "(sNorm2 u > 0) \<and> (sNorm2 v > 0)" 
      using uvnz lemSpatialNullImpliesSpatialOrigin add_less_zeroD less_linear not_square_less_zero 
      by blast
    hence "(sNorm2 u)*(sNorm2 v) < 1" 
      by (metis ass assms(1) local.dual_order.not_eq_order_implies_strict local.leD 
          local.less_imp_le local.mult_le_one local.mult_less_cancel_left1 
          local.mult_less_cancel_right1)
    hence "False" using lemCauchySchwarzSqr assms(2)
      by (metis local.dual_order.strict_iff_not local.mult_cancel_right1)
  }
  hence norms1: "sNorm2 u = 1 \<and> sNorm2 v = 1" using assms(1) by force
  hence "sqr (sdot u v) = (sNorm2 u)*(sNorm2 v)" using assms(2) by auto
  hence "\<exists> a \<noteq> 0 . u = (a \<otimes>s v)" using lemCauchySchwarzEquality uvnz by blast
  then obtain a where a: "a \<noteq> 0 \<and> u = (a \<otimes>s v)" by auto
  hence "sdot u v = a * sNorm2 v" using lemSDotScaleLeft by auto
  hence "a = 1" using assms(2) norms1 by auto
  thus ?thesis using a by auto
qed


lemma lemCausalOrthogmToLightlikeImpliesParallel:
  assumes "causal p"
and       "lightlike q"
and       "orthogm p q"
shows     "parallel p q"
proof -
  have tpnz: "tval p \<noteq> 0" 
  proof -
    have "p \<noteq> origin" using assms(1) by auto
    have case1: "lightlike p \<longrightarrow> ?thesis"
      by (metis local.diff_add_cancel local.lemNorm2Decomposition 
                local.lemNullImpliesOrigin local.lemZeroRoot)
    have case2: "timelike p \<longrightarrow> ?thesis" 
      by (metis local.add_less_zeroD local.diff_gt_0_iff_gt 
                local.lemZeroRoot local.not_square_less_zero)
    thus ?thesis using assms(1) case1 by blast
  qed

  have tqnz: "tval q \<noteq> 0" using assms(2)
    by (metis local.diff_add_cancel local.lemNorm2Decomposition 
              local.lemNullImpliesOrigin local.lemZeroRoot)

  define phat where phat: "phat = ((1/tval p)\<otimes>p)"
  define qhat where qhat: "qhat = ((1/tval q)\<otimes>q)"

  have phatcausal: "causal phat"
  proof -
    have n2: "mNorm2 phat = (sqr (1/tval p))*mNorm2 p" using phat lemMNorm2OfScaled by blast
    have "lightlike p \<longrightarrow> lightlike phat" using phat n2 tpnz by auto
    moreover have "timelike p \<longrightarrow> timelike phat" using phat n2 tpnz
      by (simp add: local.lemSquaresPositive)
    ultimately show ?thesis using assms(1) by blast
  qed

  have qhatlightlike: "lightlike qhat"
  proof -
    have "mNorm2 qhat = (sqr (1/tval q))*mNorm2 q" using qhat lemMNorm2OfScaled by blast
    thus ?thesis using assms(2) tqnz qhat local.divide_eq_0_iff by force 
  qed

  have hatsorthog: "orthogm phat qhat" 
  proof -
    have "(phat \<odot>m qhat) = (1/tval p)*(p \<odot>m qhat)"
      using phat lemMDotScaleLeft[of "1/tval p" "p" "qhat"] by auto
    thus ?thesis
      using qhat lemMDotScaleRight[of "p" "1/tval q" "q"] tpnz tqnz assms(3) by auto
  qed

  define ps where ps: "ps = sComponent phat"
  define qs where qs: "qs = sComponent qhat"

  have p: "phat = stPoint 1 ps" using phat ps tpnz by auto
  have q: "qhat = stPoint 1 qs" using qhat qs tqnz by auto

  have "sNorm2 ps \<le> 1" using p phatcausal by auto
  moreover have "sNorm2 qs = 1" using q qhatlightlike by auto
  moreover have "sdot ps qs = 1" using hatsorthog p q by auto
  ultimately have "ps = qs" 
    using lemCauchySchwarzEqualityInUnitSphere by auto

  hence "phat = qhat" using p q by auto
  hence "((1/tval p)\<otimes>p) = ((1/tval q)\<otimes>q)" using phat qhat by auto
  hence "p = (((tval p)/(tval q)) \<otimes> q)" 
    using tpnz tqnz 
          lemScaleAssoc[of "tval p" "1/tval p" "p"]
          lemScaleAssoc[of "tval p" "1/tval q" "q"]
    by auto
  thus ?thesis using tpnz tqnz using local.divide_eq_0_iff 
    by blast
qed


end (* of class CauchySchwarz *)

end (* of theory CauchySchwarz *)
                     
