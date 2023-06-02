(*
   Mike Stannett, April 2020
   Updated: Jan 2023
*)

section \<open> WorldLine \<close>

text \<open>This theory defines worldlines.\<close>

theory WorldLine
  imports WorldView Functions
begin


class WorldLine = WorldView + Functions
begin

abbreviation wline :: "Body \<Rightarrow> Body \<Rightarrow> 'a Point set"
  where "wline m k \<equiv> { p . m sees k at p }"

(* Lemmas *)
lemma lemWorldLineUnderWVT: 
  shows "applyToSet (wvtFunc m k) (wline m b) \<subseteq>  wline k b"
  by auto

lemma lemFiniteLineVelocityUnique:
  assumes "(u \<in> lineVelocity l) \<and> (v \<in> lineVelocity l)"
and       "lineSlopeFinite l"
  shows   "u = v"
proof - 
  have "\<exists> d1 \<in> drtn l . u = velocityJoining origin d1" using assms by simp
  then obtain d1 
    where d1: "d1 \<in> drtn l \<and> u = velocityJoining origin d1" by blast

  have "\<exists> d2 \<in> drtn l . v = velocityJoining origin d2" using assms by simp
  then obtain d2 
    where d2:  "d2 \<in> drtn l \<and> v = velocityJoining origin d2" by blast

  hence "(d1 \<in> drtn l) \<and> (d2 \<in> drtn l)" using d1 d2 by auto

  then obtain a where a: "(a \<noteq> 0) \<and> (d2 = (a \<otimes> d1))" 
    using lemDrtn[of "d1" "d2" "l"] by blast

(* TODO: Show that the slopes are finite *)
  have slopes: "(tval d1 \<noteq> 0) \<and> (tval d2 \<noteq> 0) 
                  \<and> (slopeFinite origin d1) \<and> (slopeFinite origin d2)"
  proof -
    obtain x y where xy: "(x \<noteq> y) \<and> (onLine x l) \<and> (onLine y l) \<and> (slopeFinite x y)"
      using assms(2) by blast
    hence "slopeFinite x y" by blast
    hence tvalnz: "tval y - tval x \<noteq> 0" by simp

    define yx where "yx = (y\<ominus>x)"
    hence "(x \<noteq> y) \<and> (onLine x l) \<and> (onLine y l) \<and> (yx = (y \<ominus> x))" using xy by simp
    hence "\<exists> x y . (x \<noteq> y) \<and> (onLine x l) \<and> (onLine y l) \<and> (yx = (y \<ominus> x))" by blast
    hence "(y \<ominus> x) \<in> drtn l" using yx_def by auto
    then obtain b where b: "(b \<noteq> 0) \<and> (d2 = (b \<otimes> (y\<ominus>x)))" 
      using d2 lemDrtn[of "y\<ominus>x" "d2" "l"] by blast

    hence tval2: "tval d2 \<noteq> tval origin" using tvalnz b by simp
    hence tval1: "tval d1 \<noteq> tval origin" using a by auto
    hence finite: "(slopeFinite origin d1) \<and> (slopeFinite origin d2)" 
      using tval2 by auto
    have "tval origin = 0" by simp
    thus ?thesis using tval1 tval2 finite by blast
  qed

  have t1nz: "tval d1 \<noteq> 0" using slopes by auto
  have anz: "a \<noteq> 0" using a by blast
  hence equ: "1/(tval d1) = (1/(a*tval d1))*a" by simp

  hence "sloper origin d1 = (((1/(a*tval d1))*a) \<otimes> d1)" using slopes by auto
  also have "... =  ((1/(tval d2)) \<otimes> d2)" 
    using lemScaleAssoc[of "1/(a*tval d1)" "a" "d1"] a by auto
  finally have equalslopers: "sloper origin d1 = sloper origin d2" using slopes by auto

  thus ?thesis using d1 d2 by auto
qed

end (* of class WorldLine *)

end (* of theory WorldLine *)
  

