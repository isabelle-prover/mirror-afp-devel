(*
   Author: Mike Stannett
   Date: August 2020
   Updated: Feb 2023
*)

section \<open> Proposition1 \<close>

text \<open>This theory shows that observers consider their own lightcones to be upright.\<close>

theory Proposition1
  imports Cones AxLightMinus
begin


class Proposition1 = Cones + AxLightMinus
begin

lemma lemProposition1:
  assumes "x \<in> wline m m"
  shows   "cone m x p = regularCone x p"
proof -
  have mmx: "m sees m at x" using assms by simp

  have  axlight: "\<forall> l . \<forall> v \<in> lineVelocity l .
           (\<exists> ph . (Ph ph \<and> (tangentLine l (wline m ph) x)))  \<longleftrightarrow>  (sNorm2 v = 1)" 
    using AxLightMinus mmx by auto
(*
  "cone m x p \<equiv> \<exists> l . onLine p l \<and>  onLine x l  \<and> (\<exists> ph . Ph ph \<and> tl l m ph x)
  "regularCone x p \<equiv> \<exists> l . onLine p l \<and>  onLine x l \<and> (\<exists> v \<in> lineVelocity l . sNorm2 v = 1)
*)

  (* This term is too complex for isabelle to reason about quickly. Abbreviate it! *)
  define axph where axph: "axph = (\<lambda> l . \<lambda> ph . (Ph ph \<and> (tangentLine l (wline m ph) x)))"

  (* Likewise this speeds up the final steps *)
  define lhs where lhs: "lhs = cone m x p"
  define rhs where rhs: "rhs = regularCone x p"

  { assume "lhs"
    hence "\<exists> l . onLine p l \<and>  onLine x l  \<and> (\<exists> ph . axph l ph)" 
      using lhs axph by auto 
    then obtain l 
      where l: "onLine p l \<and>  onLine x l  \<and> (\<exists> ph . axph l ph)" by auto

    (* establish basic facts *)
    have xonl: "onLine x l" using l by auto
    have ponl: "onLine p l" using l by auto

    (* Can choose v \<in> lineVelocity l *)
    have exph: "\<exists> ph . axph l ph" using l by auto
    then obtain ph where ph: "axph l ph" by auto

    have axlight': "\<forall> v \<in> lineVelocity l . (\<exists> ph . axph l ph)  \<longleftrightarrow>  (sNorm2 v = 1)" 
      using axph axlight by force

    hence lv1: "\<forall> v \<in> lineVelocity l . (sNorm2 v = 1)" using exph by blast

    have  tterm1: "tl l m ph x" using ph axph by force

    hence "\<exists> p . ( (onLine p l) \<and> (p \<noteq> x) \<and> (\<forall> \<epsilon> > 0 .  \<exists> \<delta> > 0 . \<forall> y \<in> (wline m ph). (
      ( (y within \<delta> of x) \<and> (y \<noteq> x) ) \<longrightarrow>
      ( \<exists> r . ((onLine r (lineJoining x y)) \<and> (r within \<epsilon> of p))))))"
      by auto
    then obtain q where q: "onLine q l \<and> q \<noteq> x" by auto
    define qx where qx: "qx = (q \<ominus> x)"
    hence "(x \<noteq> q) \<and> onLine x l \<and> onLine q l \<and> (qx = (q \<ominus> x))" using q xonl by auto
    hence "\<exists> p q . (p \<noteq> q) \<and> onLine p l \<and> onLine q l \<and> (qx = (q \<ominus> p))" by blast
    hence qxl: "qx \<in> drtn l" by auto
    
    define v where v: "v = velocityJoining origin qx"
    hence "\<exists> d \<in> drtn l . v = velocityJoining origin d" using qxl by blast
    hence existsv: "v \<in> lineVelocity l" by auto
    hence norm2v: "sNorm2 v = 1" using lv1 by auto
    hence "\<exists> v \<in> lineVelocity l . sNorm2 v = 1" using existsv by force

    hence "onLine p l \<and>  onLine x l \<and> (\<exists> v \<in> lineVelocity l . sNorm2 v = 1)"
      using ponl xonl by auto
    hence "\<exists> l . onLine p l \<and>  onLine x l \<and> (\<exists> v \<in> lineVelocity l . sNorm2 v = 1)"
      by blast
    hence "regularCone x p" by auto
  }
  hence l2r: "lhs \<longrightarrow> rhs" using rhs by blast

  (* CONVERSE *)
  { assume "rhs"
    hence "\<exists> l . onLine p l \<and>  onLine x l \<and> (\<exists> v \<in> lineVelocity l . sNorm2 v = 1)" 
      using rhs by auto
    then obtain l 
      where l: "(onLine p l) \<and>  (onLine x l) \<and> (\<exists> v \<in> lineVelocity l . sNorm2 v = 1)" 
      by blast

    have xonl: "onLine x l" using l by auto
    have ponl: "onLine p l" using l by auto

    have "\<exists> v \<in> lineVelocity l . sNorm2 v = 1" using l  by blast
    then obtain v where v: "(v \<in> lineVelocity l) \<and> (sNorm2 v = 1)" by blast

    define final 
      where final: "final = (\<lambda> l . onLine p l \<and>  onLine x l  \<and> (\<exists> ph . axph l ph))"

    have "\<exists> ph . axph l ph" using v axlight axph by blast
    hence "final l" using ponl xonl final by auto
    hence "\<exists> l . final l" by auto
    hence "cone m x p" using final axph by auto
    hence "lhs" using lhs by auto
  }
  hence r2l: "rhs \<longrightarrow> lhs" using lhs by blast

  hence "lhs \<longleftrightarrow> rhs" using l2r by auto
  thus ?thesis using lhs rhs by auto
qed




end (* of class Proposition1 *)

end (* of theory Proposition1 *)

