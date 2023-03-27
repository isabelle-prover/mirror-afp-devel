(*
  Sorts.thy
  Mike Stannett 2012-2023
*)

section \<open>Sorts\<close>

text \<open>GenRel is a 2-sorted first-order logic. This theory introduces the two sorts and
proves a number of basic arithmetical results. The two sorts are Bodies 
(things that can move) and Quantities (used to specify coordinates, masses, etc).\<close>


theory Sorts
  imports Main
begin


subsection \<open>Bodies\<close>

text \<open>There are two types of Body: photons and observers. We do not assume
a priori that these sorts are disjoint.\<close>

record Body =
  Ph  :: "bool"
  Ob  :: "bool"


subsection \<open>Quantities\<close>
text \<open>The quantities are assumed to form a linearly ordered field. We may
  sometimes need to assume that the field is also Euclidean, i.e. that
  square roots exist, but this is not a general requirement so it
  will be added later using a separate axiom class, AxEField.
\<close>
class Quantities = linordered_field
begin


abbreviation inRangeOO :: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" ("_ < _ < _") 
  where "(a < b < c) \<equiv> (a < b) \<and> (b < c)"

abbreviation inRangeOC :: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" ("_ < _ \<le> _") 
  where "(a < b \<le> c) \<equiv> (a < b) \<and> (b \<le> c)"

abbreviation inRangeCO :: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" ("_ \<le> _ < _") 
  where "(a \<le> b < c) \<equiv> (a \<le> b) \<and> (b < c)"

abbreviation inRangeCC :: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" ("_ \<le> _ \<le> _") 
  where "(a \<le> b \<le> c) \<equiv> (a \<le> b) \<and> (b \<le> c)"


lemma lemLEPlus: "a \<le> b + c \<longrightarrow> c \<ge> a - b" 
  by (simp add: add_commute local.diff_le_eq)


lemma lemMultPosLT1: 
  assumes "(a > 0) \<and> (b \<ge> 0) \<and> (b < 1)"
  shows "(a * b) < a"
  using assms local.mult_less_cancel_left2 local.not_less by auto


lemma lemAbsRange: "e > 0 \<longrightarrow> ((a-e) < b < (a+e)) \<longleftrightarrow>  (abs (b-a) < e)"
  by (simp add: local.abs_diff_less_iff)

lemma lemAbsNeg: "abs x = abs (-x)" 
  by simp

lemma lemAbsNegNeg: "abs (-a-b) = abs (a+b)" 
  using add_commute local.abs_minus_commute by auto

lemma lemGENZGT: "(x \<ge> 0) \<and> (x \<noteq> 0) \<longrightarrow> x > 0" 
  by auto

lemma lemLENZLT: "(x \<le> 0) \<and> (x \<noteq> 0) \<longrightarrow> x < 0" 
  by force

lemma lemSumOfNonNegAndPos: "x \<ge> 0 \<and> y > 0 \<longrightarrow> x+y > 0"
  by (simp add: local.add_strict_increasing2)

lemma lemSumOfTwoHalves: "x = x/2 + x/2"
  using mult_2[of "x/2"] by force

lemma lemDiffDiffAdd: "(b-a)+(c-b) = (c-a)"
  by (auto simp add: field_simps)

lemma lemSumDiffCancelMiddle: "(a - b) + (b - c) = (a - c)"
  by (auto simp add: field_simps)

lemma lemDiffSumCancelMiddle: "(a - b) + (b + c) = (a + c)"
  by (auto simp add: field_simps)

lemma lemMultPosLT: "((0 < a) \<and> (b < c)) \<longrightarrow> (a*b < a*c)"
  using mult_strict_left_mono by auto

lemma lemMultPosLE: "((0 < a) \<and> (b \<le> c)) \<longrightarrow> (a*b \<le> a*c)"
  using mult_left_mono by auto

lemma lemNonNegLT: "((0 \<le> a) \<and> (b < c)) \<longrightarrow> (a*b \<le> a*c)"
  using mult_left_mono by auto

lemma lemMultNonNegLE: "((0 \<le> a) \<and> (b \<le> c)) \<longrightarrow> (a*b \<le> a*c)"
  using mult_left_mono by auto


abbreviation sqr :: "'a \<Rightarrow> 'a" 
  where "sqr x \<equiv>  x*x"

abbreviation hasRoot :: "'a \<Rightarrow> bool" 
  where "hasRoot x \<equiv> \<exists> r . x = sqr r"

abbreviation isNonNegRoot :: "'a \<Rightarrow> 'a \<Rightarrow> bool" 
  where "isNonNegRoot x r \<equiv> (r \<ge> 0) \<and> (x = sqr r)"

abbreviation hasUniqueRoot :: "'a \<Rightarrow> bool" 
  where "hasUniqueRoot x \<equiv> \<exists>! r . isNonNegRoot x r"

(* May not be defined for some x *)
abbreviation sqrt :: "'a \<Rightarrow> 'a"
  where "sqrt x \<equiv> THE r . isNonNegRoot x r"


lemma lemAbsIsRootOfSquare: "isNonNegRoot (sqr x) (abs x)"
  by simp

lemma lemSqrt:
  assumes "hasRoot x"
  shows   "hasUniqueRoot x" 
proof -
  obtain r where "x = sqr r" using assms(1) by auto
  define rt where "rt = (if (r \<ge> 0) then r else (-r))"
  hence rt: "rt \<ge> 0 \<and> sqr rt = x" using rt_def \<open>x = sqr r\<close> by auto
  hence rtroot: "isNonNegRoot x rt" by auto

  { fix y
    assume yprops: "isNonNegRoot x y"
    hence "y = rt"
      using local.square_eq_iff rt by auto
    hence "(( y \<ge> 0) \<and> (x = sqr  y)) \<longrightarrow> (y = rt)" by auto
  }
  hence rtunique: "\<forall> y . isNonNegRoot x y \<longrightarrow> (y = rt)" by auto
  thus ?thesis using rtroot by auto
qed


lemma lemSqrMonoStrict: assumes "(0 \<le> u) \<and> (u < v)"
shows "(sqr u) < (sqr v)"
proof -
  have 1: "(u*u) \<le> (u*v)"  using assms comm_mult_left_mono by auto
  have "(u*v) < (v*v)" 
    using assms mult_commute comm_mult_strict_left_mono by auto
  thus ?thesis using 1 le_less_trans by auto
qed

lemma lemSqrMono: "(0 \<le> u) \<and> (u \<le> v) \<longrightarrow> (sqr u) \<le> (sqr v)" 
  by (simp add: local.mult_mono')


lemma lemSqrOrderedStrict: "(v > 0) \<and> (sqr u < sqr v) \<longrightarrow> (u < v)"
  using mult_mono[of "v" "u" "v" "u"] by force


lemma lemSqrOrdered: "(v \<ge> 0) \<and> (sqr u \<le> sqr v) \<longrightarrow> (u \<le> v)"
  using mult_strict_mono[of "v" "u" "v" "u"] by force

lemma lemSquaredNegative: "sqr x = sqr (-x)" 
  by auto

lemma lemSqrDiffSymmetrical: "sqr (x - y) = sqr (y - x)"
  using lemSquaredNegative[of "y-x"] by auto

lemma lemSquaresPositive: "x \<noteq> 0 \<longrightarrow> sqr x > 0" 
  by (simp add:  lemGENZGT)

lemma lemZeroRoot: "(sqr x = 0) \<longleftrightarrow> (x = 0)"
  by simp

lemma lemSqrMult: "sqr (a * b) = (sqr a) * (sqr b)" 
  using mult_commute mult_assoc by simp

lemma lemEqualSquares: "sqr u = sqr v \<longrightarrow> abs u = abs v" 
  by (metis local.abs_mult_less local.abs_mult_self_eq local.not_less_iff_gr_or_eq)


lemma lemSqrtOfSquare: 
  assumes "b = sqr a"
shows     "sqrt b = abs a" 
proof -
  have "b \<ge> 0" using assms by auto
  hence conj1: "hasUniqueRoot b" using lemSqrt[of "b"] assms by auto
  moreover have "isNonNegRoot b (abs a)" using lemAbsIsRootOfSquare assms by auto
  ultimately have "sqrt b = abs a" 
    using theI[of "\<lambda> r . 0 \<le> r \<and> b = sqr r" "abs a"] by blast
  thus ?thesis by auto
qed


lemma lemSquareOfSqrt: 
  assumes "hasRoot b"
and       "a = sqrt b"
shows     "sqr a = b"
proof - 
  obtain r where r: "isNonNegRoot b r" using assms(1) lemSqrt[of "b"] by auto
  hence "\<forall>x. 0 \<le> x \<and> b = sqr x \<longrightarrow> x = r" using lemSqrt by blast
  hence "a = r" using r assms(2) the_equality[of "isNonNegRoot b" "r"] by blast
  thus ?thesis using r by auto
qed


lemma lemSqrt1: "sqrt 1 = 1"
proof -
  have "isNonNegRoot 1 1" by auto
  moreover have "\<forall> r . isNonNegRoot 1 r \<longrightarrow> r = 1"
  proof -
    { fix r assume "isNonNegRoot 1 r"
      hence r: "(r \<ge> 0) \<and> (1 = sqr r)" by simp
      hence "r = 1" using calculation lemSqrt by blast
    }
    thus ?thesis by blast
  qed
  ultimately show ?thesis using the_equality[of "isNonNegRoot 1" "1"] by blast
qed


lemma lemSqrt0: "sqrt 0 = 0" 
  using lemZeroRoot local.mult_cancel_right1 by blast



lemma lemSqrSum: "sqr (x + y) = (x*x) + (2*x*y) + (y*y)"
proof -
  have "x*y + y*x = x*y + x*y" using mult_commute by simp
  also have "... = (x+x)*y" using distrib_right by simp
  finally have xy: "x*y + y*x = 2*x*y" using mult_2 by auto
  
  have "sqr (x+y) = x*(x+y) + y*(x+y)" using distrib_right by auto
  also have "... = x*x + x*y + y*x + y*y" using distrib_left add_assoc by auto
  finally have "sqr (x+y) = (sqr x) + x*y + y*x + (sqr y)" 
    using distrib_left add_assoc by auto
  
  thus ?thesis using xy add_assoc by auto
qed


lemma lemQuadraticGEZero:
  assumes "\<forall> x. a*(sqr x) + b*x + c \<ge> 0"
and       "a > 0"
  shows "(sqr b) \<le> 4*a*c"
proof -
  { fix x :: "'a"
    have "a * sqr (x + (b/(2*a))) = a * ((sqr x) + 2*(b/(2*a))*x + (sqr (b/(2*a))))"
      using lemSqrSum[of "x" "(b/(2*a))"] mult_assoc 
            mult_commute[of "x" "(b/(2*a))"]
      by auto
    hence 1: "a * sqr (x + (b/(2*a))) 
             = (a * (sqr x)) + (a*(2*(b/(2*a))*x)) + (a * sqr (b/(2*a)))"
      using distrib_left by auto
    have "a*(2*(b/(2*a))*x) = b*x" using mult_assoc assms(2) by simp

    hence 2: "a * sqr (x + (b/(2*a))) = a*(sqr x) + (b*x) + (a * sqr (b/(2*a)))"
      using 1 by auto

    have "(a * sqr (b/(2*a))) = c + ((a * sqr (b/(2*a))) - c)" 
      using add_commute diff_add_cancel by auto
    hence "(a * sqr (x + (b/(2*a)))) 
      = (a*(sqr x) + (b*x) + c) + ((a * sqr (b/(2*a))) - c)" using 2 add_assoc by auto
    hence 3: "(a * sqr (x + (b/(2*a)))) \<ge> ((a * sqr (b/(2*a))) - c)"
      using assms(1) by auto
  }
  hence "\<forall> x . (a * sqr (x + (b/(2*a)))) \<ge> ((a * sqr (b/(2*a))) - c)"
    by auto

  hence "(a * sqr ((-b/(2*a)) + (b/(2*a)))) \<ge> ((a * sqr (b/(2*a))) - c)" by fast
  hence "((a * sqr (b/(2*a))) - c) \<le> 0" by simp
  hence "4*a*((a * sqr (b/(2*a))) - c) \<le> 0" 
    using  local.mult_le_0_iff assms(2) by auto
  hence "4*a*((a * sqr (b/(2*a)))) - 4*a*c \<le> 0" 
    using right_diff_distrib  mult_assoc by auto
  hence 4: "4*a*((a * sqr (b/(2*a)))) \<le> 4*a*c" by simp

  have "sqr (b/(2*a)) = (sqr b)/(4*a*a)" 
    using mult_assoc mult_commute by simp
  hence "4*a*((a * sqr (b/(2*a)))) = 4*a*((a * (sqr b)/(4*a*a)))" by auto
  hence "4*a*((a * sqr (b/(2*a)))) = (4*a*a)*(sqr b)/(4*a*a)"
    using mult_commute by auto
  hence "4*a*((a * sqr (b/(2*a)))) = (sqr b)"
    using assms(2) by simp

  thus ?thesis using 4 by auto
qed


lemma lemSquareExistsAbove:
  shows "\<exists> x > 0 . (sqr x) > y"
proof -
  have cases: "(y \<le> 0) \<or> (y > 0)" by auto
  have one: "1 \<ge> 0" by simp
  have onestrict: "0 < 1" by simp

  { assume yle0: "y \<le> 0"
    hence "y < sqr 1" using yle0 le_less_trans by simp
    hence ?thesis using onestrict by fast
  }
  hence case1: "(y \<le> 0) \<longrightarrow> ?thesis" by auto

  { assume ygt0: "y > 0"
    { assume ylt1: "y < 1"
      hence "sqr y < y" using ygt0 mult_strict_left_mono[of "y" "1"] by auto
      hence "sqr y < sqr 1" using ylt1 by simp
      hence "y < 1" using ygt0 lemSqrOrderedStrict[of "1" "y"] by auto
      hence "y < sqr 1" by simp
      hence "?thesis" using onestrict by best
    }
    hence a: "(y < 1) \<longrightarrow> ?thesis" by auto
    { assume "y = 1"
      hence b1: "y < sqr 2" by simp
      have "2 > 0" by simp
      hence "?thesis" using b1 by fast
    }
    hence b: "(y = 1) \<longrightarrow> ?thesis" by auto
    { assume ygt1: "y > 1"
      hence yge1: "y \<ge> 1" by simp 
      have yge0: "y \<ge> 0" using ygt0 by simp
      have "y \<le> y" by simp
      hence "sqr y > y*1" using lemMultPosLT ygt0 ygt1 by blast
      hence "sqr y > y" by simp
      hence "?thesis" using ygt0 by bestsimp
    }
    hence "(y > 1) \<longrightarrow> ?thesis" by simp

    hence "((y<1)\<or>(y=1)\<or>(y>1)) \<longrightarrow> ?thesis" using a b by auto
    hence ?thesis by fastforce
  }
  hence ypos: "(y > 0) \<longrightarrow> ?thesis" by auto

  thus ?thesis using cases case1 by auto
qed


lemma lemSmallSquares:
  assumes "x > 0"
  shows "\<exists> y > 0. (sqr y < x)"
proof -
  have invpos: "1/x > 0" using assms(1) by auto
  then obtain z where z: "(z > 0) \<and> ((sqr z) > (1/x))" 
    using lemSquareExistsAbove by auto
  define y where y: "y = 1/z"
  hence ypos: "y > 0" using z by auto
  have 1: "1/(sqr z) < 1/(1/x)" using z invpos
    by (meson local.divide_strict_left_mono 
              local.mult_pos_pos local.zero_less_one)
  hence "(sqr y) < x" using z y by simp
  thus ?thesis using ypos by auto
qed


lemma lemSqrLT1:
  assumes "0 < x < 1"
  shows "0 < (sqr x) < x"
using assms lemMultPosLT1[of "x" "x"] by auto



lemma lemReducedBound:
  assumes "x > 0"
  shows "\<exists> y > 0 . (y < x) \<and> (sqr y < y) \<and> (y < 1)"
proof -
  have x2: "x > x/2" 
    using assms lemSumOfTwoHalves[of "x"] add_strict_left_mono[of "0" "x/2" "x/2"]
    by auto
  have x2pos: "x/2 > 0" using assms by simp

  define y where "y = min (x/2) (1/2)"
  hence y: "(y \<le> x/2) \<and> (y \<le> 1/2) \<and> (y > 0)" using x2pos by auto

  have yltx: "y < x" using y x2 le_less_trans by auto
  have ylt1: "y < 1" using y le_less_trans by auto

  hence "sqr y < y" using lemSqrLT1 y by simp
  thus ?thesis using yltx ylt1 y by auto
qed

end (* of class Quantities *)



end (* of theory Sorts *)

