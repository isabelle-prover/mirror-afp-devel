(*
   Mike Stannett
   Date: June 2020
   Updated: Jan 2023
*)
section \<open> Vectors \<close>

text \<open>In this theory we define dot-products, and explain what we mean by
timelike, lightlike (null), causal and spacelike vectors. \<close>

theory Vectors
  imports Norms
begin

class Vectors = Norms
begin

fun dot :: "'a Point \<Rightarrow> 'a Point \<Rightarrow> 'a" ("_ \<odot> _")
  where "dot u v = (tval u)*(tval v) + (xval u)*(xval v) +
                     (yval u)*(yval v) + (zval u)*(zval v)"

fun sdot :: "'a Space \<Rightarrow> 'a Space \<Rightarrow> 'a" ("_ \<odot>s _")
  where "sdot u v = (svalx u)*(svalx v) + (svaly u)*(svaly v) + (svalz u)*(svalz v)"

fun mdot :: "'a Point \<Rightarrow> 'a Point \<Rightarrow> 'a" ("_ \<odot>m _ ")
  where "mdot u v = (tval u)*(tval v) - ((sComponent u) \<odot>s (sComponent v))"

abbreviation timelike :: "'a Point \<Rightarrow> bool"
  where "timelike p \<equiv> mNorm2 p > 0"

(* For simplicity, assume p isn't the origin *)
abbreviation lightlike :: "'a Point \<Rightarrow> bool"
  where "lightlike p \<equiv> (p \<noteq> origin \<and> mNorm2 p = 0)"

abbreviation spacelike :: "'a Point \<Rightarrow> bool"
  where "spacelike p \<equiv> mNorm2 p < 0"

abbreviation causal :: "'a Point \<Rightarrow> bool"
  where "causal p \<equiv> timelike p \<or> lightlike p"

abbreviation orthog :: "'a Point \<Rightarrow> 'a Point \<Rightarrow> bool"
  where "orthog p q \<equiv> (p \<odot> q) = 0"

abbreviation orthogs :: "'a Space \<Rightarrow> 'a Space \<Rightarrow> bool"
  where "orthogs p q \<equiv> (p \<odot>s q) = 0"

abbreviation orthogm :: "'a Point \<Rightarrow> 'a Point \<Rightarrow> bool"
  where "orthogm p q \<equiv> (p \<odot>m q) = 0"


(* LEMMAS *)


lemma lemDotDecomposition:
  shows "(u \<odot> v) = (tval u * tval v) + ((sComponent u) \<odot>s (sComponent v))"
  by (simp add: add_commute local.add.left_commute)


lemma lemDotCommute: "dot u v = dot v u"
  by (simp add: mult_commute)

lemma lemDotScaleLeft: "dot (a\<otimes>u) v = a * (dot u v)"
  using mult_assoc distrib_left by force

lemma lemDotScaleRight: "dot u (a\<otimes>v) = a * (dot u v)"
  using mult_assoc mult_commute distrib_left by auto 

lemma lemDotSumLeft: "dot (u\<oplus>v) w = (dot u w) + (dot v w)"
  using distrib_right add_assoc add_commute by force

lemma lemDotSumRight: "dot u (v\<oplus>w) = (dot u v) + (dot u w)"
  using distrib_left add_assoc add_commute by auto

lemma lemDotDiffLeft: "dot (u\<ominus>v) w = (dot u w) - (dot v w)"
  by (simp add: field_simps)

lemma lemDotDiffRight: "dot u (v\<ominus>w) = (dot u v) - (dot u w)"
  by (simp add: field_simps)


lemma lemNorm2OfSum: "norm2 (u \<oplus> v) = norm2 u + 2*(u \<odot> v) + norm2 v"
proof -
  have "norm2 (u \<oplus> v) = ((u \<oplus> v) \<odot> (u \<oplus> v))" by auto
  also have "\<dots> = (u \<odot> (u \<oplus> v)) + (v \<odot> (u \<oplus> v))" 
    using lemDotSumLeft[of "u" "v" "(u \<oplus> v)"] by auto
  also have "\<dots> = (u\<odot>u) + ((u\<odot>v) + (v\<odot>u)) + (v\<odot>v)"
    using lemDotSumRight[of "u" "u" "v"] lemDotSumRight[of "v" "u" "v"]
          add_assoc by auto
  finally show ?thesis using  mult_2 lemDotCommute[of "u" "v"]
    by auto
qed


lemma lemSDotCommute: "sdot u v = sdot v u"
  by (simp add: mult_commute)

lemma lemSDotScaleLeft: "sdot (a \<otimes>s u) v = a * (sdot u v)"
  using mult_assoc distrib_left by force

lemma lemSDotScaleRight: "sdot u (a \<otimes>s v) = a * (sdot u v)"
  using mult_assoc mult_commute distrib_left by auto 

lemma lemSDotSumLeft: "sdot (u \<oplus>s v) w = (sdot u w) + (sdot v w)"
  using distrib_right add_assoc add_commute by force

lemma lemSDotSumRight: "sdot u ( v\<oplus>s w) = (sdot u v) + (sdot u w)"
  using distrib_left add_assoc add_commute by auto

lemma lemSDotDiffLeft: "sdot (u \<ominus>s v) w = (sdot u w) - (sdot v w)"
  by (simp add: field_simps)

lemma lemSDotDiffRight: "sdot u ( v\<ominus>s w) = (sdot u v) - (sdot u w)"
  by (simp add: field_simps)



lemma lemMDotDiffLeft: "mdot (u\<ominus>v) w = (mdot u w) - (mdot v w)"
  by (simp add: field_simps)


lemma lemMDotSumLeft: "mdot (u \<oplus> v) w = (mdot u w) + (mdot v w)"
proof -
  have "mdot (u\<oplus>v) w = (tval (u\<oplus>v))*(tval w) - ((sComponent (u\<oplus>v))\<odot>s(sComponent w))"
    by auto
  also have "\<dots> = (tval u*tval w) + (tval v*tval w) 
                     - ( ((sComponent u)\<odot>s(sComponent w)) + ((sComponent v)\<odot>s(sComponent w)))" 
    using distrib lemSDotSumLeft[of "(sComponent u)" "(sComponent v)" "(sComponent w)"] 
    by auto
  also have "\<dots> = ((tval u*tval w) - ((sComponent u)\<odot>s(sComponent w)))
                + ((tval v*tval w) - ((sComponent v)\<odot>s(sComponent w)))"
    using add_diff_eq add_commute diff_diff_add by auto
  finally show ?thesis by simp
qed


lemma lemMDotScaleLeft: "mdot (a \<otimes> u) v = a * (mdot u v)"
proof -
  have "mdot (a \<otimes> u) v = a*(tval u*tval v) - a*((sComponent u)\<odot>s(sComponent v))"
    using lemSDotScaleLeft[of "a" "sComponent u" "sComponent v"]
    by (simp add: mult_assoc)
  thus ?thesis by (simp add: local.right_diff_distrib')
qed
  
  
lemma lemMDotScaleRight: "mdot u (a \<otimes> v) = a * (mdot u v)"
proof -
  have "mdot u (a \<otimes> v) = a*(tval u*tval v) - a*((sComponent u)\<odot>s(sComponent v))"
    using lemSDotScaleRight[of "sComponent u" "a" "sComponent v"] 
    by (simp add: local.mult.left_commute)
  thus ?thesis by (simp add: local.right_diff_distrib')
qed
  
  

lemma lemSNorm2OfSum: "sNorm2 (u \<oplus>s v) = sNorm2 u + 2*(u \<odot>s v) + sNorm2 v"
proof -
  have "sNorm2 (u \<oplus>s v) = ((u \<oplus>s v) \<odot>s (u \<oplus>s v))" by auto
  also have "\<dots> = (u \<odot>s (u \<oplus>s v)) + (v \<odot>s (u \<oplus>s v))" 
    using lemSDotSumLeft[of "u" "v" "(u \<oplus>s v)"] by auto
  also have "\<dots> = (u \<odot>s u) + ((u \<odot>s v) + (v \<odot>s u)) + (v \<odot>s v)"
    using lemSDotSumRight[of "u" "u" "v"] lemSDotSumRight[of "v" "u" "v"]
          add_assoc by auto
  finally show ?thesis using mult_2 lemSDotCommute[of "u" "v"]
    by auto
qed


lemma lemSNormNonNeg:
  shows "sNorm v \<ge> 0"
proof -
  have "hasUniqueRoot (sNorm2 v)" using AxEField lemSqrt by auto
  thus ?thesis using the1_equality[of "isNonNegRoot (sNorm2 v)"] by blast
qed


lemma lemMNorm2OfSum: "mNorm2 (u \<oplus> v) = mNorm2 u + 2*(u \<odot>m v) + mNorm2 v"
proof -
  define su where su: "su = sComponent u"
  define sv where sv: "sv = sComponent v"

  have "mNorm2 (u \<oplus> v) = ((u \<oplus> v) \<odot>m (u \<oplus> v))" by auto
  also have "\<dots> = (sqr (tval u) + 2*(tval u)*(tval v) + sqr (tval v)) - sNorm2 (su \<oplus>s sv)"
    using lemSqrSum su sv by auto
  also have "\<dots> = (sqr (tval u) + 2*(tval u)*(tval v) + sqr (tval v))
                - ( sNorm2 su + 2*(su \<odot>s sv) + sNorm2 sv)"
    using lemSNorm2OfSum by auto
  also have "\<dots> = ( sqr (tval u) - sNorm2 su )
                  + ( 2*(tval u)*(tval v) - 2*(su \<odot>s sv) )
                    + ( sqr (tval v) - sNorm2 sv )"
    using add_commute add_assoc add_diff_eq diff_add_eq diff_diff_add by simp
  finally show ?thesis using su sv right_diff_distrib' mult_assoc by auto
qed


lemma lemMNorm2OfDiff: "mNorm2 (u \<ominus> v) = mNorm2 u - 2*(u \<odot>m v) + mNorm2 v"
proof -
  define vm where vm: "vm = ((-1)\<otimes>v)"
  hence "mNorm2 (u \<ominus> v) = mNorm2 (u \<oplus> vm)" by auto
  hence "mNorm2 (u \<ominus> v) =  mNorm2 u + 2*(u \<odot>m vm) + mNorm2 vm"
    using lemMNorm2OfSum by auto
  moreover have "(u \<odot>m vm) = -(u \<odot>m v)" 
    using lemMDotScaleRight[of "u" "(-1)" "v"] vm by auto
  moreover have "mNorm2 vm = mNorm2 v" using vm lemMNorm2OfScaled by auto
  ultimately show ?thesis 
    by (metis local.diff_conv_add_uminus local.mult_minus_right)
qed
  

lemma lemMNorm2Decomposition: "mNorm2 p = (p \<odot>m p)"
  by auto



lemma lemMDecomposition: 
  assumes "(u \<odot>m v) \<noteq> 0"
and       "mNorm2 v \<noteq> 0"
and       "a = (u \<odot>m v)/(mNorm2 v)"
and       "up = (a \<otimes> v)"
and       "uo = (u \<ominus> up)"
  shows "u = (up \<oplus> uo) \<and> parallel up v \<and> orthogm uo v \<and> (up \<odot>m v) = (u \<odot>m v)"
proof -
  have anz: "a \<noteq> 0" using assms by auto

  have psum: "u = (up \<oplus> uo)" using assms  add_diff_eq by auto
  moreover have "parallel up v" using assms(4) anz by auto
  moreover have ppdot: "(up \<odot>m v) = (u \<odot>m v)"
  proof -
    have "(up \<odot>m v) = a*(v \<odot>m v)"  using assms lemMDotScaleLeft[of "a" "v" "v"] by auto
    thus ?thesis using assms by auto
  qed
  moreover have "orthogm uo v"
  proof -
    have "(uo \<odot>m v) = (u \<odot>m v) - (up \<odot>m v)" using lemMDotSumLeft psum by force
    thus ?thesis using ppdot by auto
  qed
  ultimately show ?thesis by blast
qed



end (* of class Vectors *)

end (* of theory Vectors *)
                     
