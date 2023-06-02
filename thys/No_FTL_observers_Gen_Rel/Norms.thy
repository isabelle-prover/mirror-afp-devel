(*
   Mike Stannett
   Date: June 2020

   Definitions relating to norms. Squared norms are defined in Points.
   The norms here depend on roots existing (AxEField). 

   Updated: Feb 2023
*)

section \<open> Norms \<close>

text \<open> This theory defines norms, assuming that roots exist. \<close>

theory Norms
  imports Points AxEField
begin

class Norms = Points + AxEField
begin

abbreviation norm :: "'a Point \<Rightarrow> 'a" ("\<parallel> _ \<parallel>") 
  where "norm p \<equiv> sqrt (norm2 p)"

(* spatial norms *)
abbreviation sNorm :: "'a Space \<Rightarrow> 'a"
  where "sNorm p \<equiv> sqrt (sNorm2 p)"


subsection \<open> axTriangleInequality \<close>

text \<open> Given that norms exist, we can define the triangle inequality
for specific cases. This will be asserted more generally as an axiom later. \<close>

(* TRIANGLE INEQUALITY *)
abbreviation axTriangleInequality :: "'a Point \<Rightarrow> 'a Point \<Rightarrow> bool" 
  where "axTriangleInequality p q \<equiv> (norm (p\<oplus>q) \<le> norm p + norm q)"



(* ********************************************************************** *)
(* LEMMAS *)


lemma lemNormSqrIsNorm2: "norm2 p = sqr (norm p)" 
proof - 
  have "norm2 p \<ge> 0" by simp
  moreover have "axEField (norm2 p)" using AxEField by simp
  ultimately show ?thesis using lemSquareOfSqrt[of "norm2 p" "norm p"] by force
qed


lemma lemZeroNorm:
  shows "(p = origin)  \<longleftrightarrow>  (norm p = 0)"
proof -
  { assume "p = origin"
    hence "norm2 p = 0" by auto
    hence "norm p = 0" using lemSquareOfSqrt lemZeroRoot AxEField by force
  }
  hence l2r: "(p = origin) \<longrightarrow> (norm p = 0)" by auto

  { assume "norm p = 0"
    hence "norm2 p = 0" using lemNormSqrIsNorm2[of "p"] by auto
    hence "p = origin" using lemNullImpliesOrigin by auto
  }
  hence "(norm p = 0) \<longrightarrow> (p = origin)" by auto

  thus ?thesis using l2r by blast
qed




lemma lemNormNonNegative: "norm p \<ge> 0" 
proof -
  have "norm2 p \<ge> 0" by auto
  hence unique: "\<exists>!r. 0 \<le> r \<and> norm2 p = sqr r" using AxEField lemSqrt[of "norm2 p"] by auto
  then obtain r where r: "0 \<le> r \<and> norm2 p = sqr r \<and> (\<forall> x . isNonNegRoot (norm2 p) x \<longrightarrow> x= r)"
    by auto
  hence "r = norm p" using the_equality[of "isNonNegRoot (norm2 p)" "r"] by blast
  moreover have "r \<ge> 0" using r by blast
  ultimately show ?thesis by auto
qed


lemma lemNotOriginImpliesPositiveNorm:
  assumes "p \<noteq> origin"
  shows   "(norm p > 0)"
proof -
  have  1: "norm p \<noteq> 0" using lemZeroNorm assms(1)by auto
  have     "norm p \<ge> 0" using lemNormNonNegative assms(1) by auto
  hence 2: "norm p > 0" using 1 by auto
  thus ?thesis by auto
qed



lemma lemNormSymmetry: "norm (p\<ominus>q) = norm (q\<ominus>p)"
proof -
  have "norm2 (p \<ominus> q) = norm2 (q \<ominus> p)" using lemSep2Symmetry by simp
  thus ?thesis by presburger
qed


lemma lemNormOfScaled: "norm (\<alpha>\<otimes>p) = (abs \<alpha>) * (norm p)"
proof -
  have "sqr (norm (\<alpha>\<otimes>p)) = norm2 (\<alpha>\<otimes>p)" using lemNormSqrIsNorm2 by presburger
  also have "\<dots> = (sqr \<alpha>)*(norm2 p)" using lemNorm2OfScaled by auto
  also have "\<dots> = (sqr \<alpha>)*(sqr (norm p))" using lemNormSqrIsNorm2 by force
  also have "\<dots> = sqr ( \<alpha>*(norm p) )" using lemSqrMult by auto
  finally have "abs (norm (\<alpha>\<otimes>p)) = abs ( \<alpha> *(norm p) )" using lemEqualSquares by blast
  moreover have "abs (norm (\<alpha>\<otimes>p)) = norm (\<alpha>\<otimes>p)" 
    using lemNormNonNegative[of "(\<alpha>\<otimes>p)"] abs_of_nonneg by auto
  moreover have "abs ( \<alpha> *(norm p) ) = (abs \<alpha>)*(abs (norm p))" using abs_mult by auto
  ultimately show ?thesis using lemNormNonNegative[of "p"] abs_of_nonneg by auto
qed


lemma lemDistancesAdd:
  assumes triangle:  "axTriangleInequality (q\<ominus>p) (r\<ominus>q)"
and       distances: "(x > 0) \<and> (y > 0) \<and> (sep2 p q < sqr x) \<and> (sep2 r q < sqr y)"
  shows   "r within (x+y) of p"
proof -
  define npq where npq: "npq = norm (q\<ominus>p)" 
  hence "sqr npq < sqr x" 
    using lemNormSqrIsNorm2 distances lemSep2Symmetry by presburger
  hence npqx: "npq < x" using lemSqrOrderedStrict distances by blast

  define nqr where nqr: "nqr = norm (r\<ominus>q)"
  hence "sqr nqr < sqr y" using lemNormSqrIsNorm2 distances by presburger
  hence nqry: "nqr < y" using lemSqrOrderedStrict distances by blast

  have rminusp: "(r\<ominus>p) = ((q\<ominus>p)\<oplus>(r\<ominus>q))" using lemDiffDiffAdd by fastforce
  define npr where npr: "npr = norm (r\<ominus>p)"

  have nx: "norm (q\<ominus>p) = npq" using npq lemSqrt by fast
  have ny: "norm (r\<ominus>q) = nqr" using nqr lemSqrt by fast
  have nz: "norm (r\<ominus>p) = npr" using npr lemSqrt by fast

  have "norm (r\<ominus>p) \<le> (norm (q\<ominus>p) + norm (r\<ominus>q))" using triangle rminusp by fastforce
  hence "npr \<le> (npq + nqr)" using nx ny nz lemSqrt npq nqr npr by simp
  hence "npr < x + y" using npqx nqry add_strict_mono[of "npq" "x" "nqr" "y"]
    by simp

  hence "sqr npr < sqr (x+y)" using npr lemNormNonNegative[of "(r\<ominus>p)"] lemSqrMonoStrict  by auto
  hence sep: "sep2 r p < sqr (x+y)" using npr lemSquareOfSqrt AxEField by auto

  thus ?thesis using npr lemSep2Symmetry by auto
qed


lemma lemDistancesAddStrictR:
  assumes  triangle: "axTriangleInequality (q\<ominus>p) (r\<ominus>q)"
and       distances: "(x > 0) \<and> (y > 0) \<and> (sep2 p q \<le> sqr x) \<and> (sep2 r q < sqr y)"
  shows "r within (x+y) of p"
proof -
  define npq where npq: "npq = norm (q\<ominus>p)"
  hence "sqr npq \<le> sqr x" using lemNormSqrIsNorm2 distances lemSep2Symmetry by presburger
  hence npqx: "npq \<le> x" using lemSqrOrdered[of "x" "npq"] distances npq by auto

  define nqr where nqr: "nqr = norm (r\<ominus>q)"
  hence "sqr nqr < sqr y" using lemNormSqrIsNorm2 distances by presburger
  hence nqry: "nqr < y" using lemSqrOrderedStrict distances by blast

  define npr where npr: "npr = norm (r\<ominus>p)"

  have nx: "norm (q\<ominus>p) = npq" using npq lemSqrt by blast
  have ny: "norm (r\<ominus>q) = nqr" using nqr lemSqrt by blast
  have nz: "norm (r\<ominus>p) = npr" using npr lemSqrt by blast

  have "norm (r\<ominus>p) \<le> (norm (q\<ominus>p) + norm (r\<ominus>q))" using  triangle lemDiffDiffAdd by fastforce
  hence "npr \<le> (npq + nqr)" using nx ny nz by simp
  hence "npr < x + y" using npqx nqry add_le_less_mono[of "npq" "x" "nqr" "y"]
    by auto
    
  hence "sqr npr < sqr (x+y)" using npr lemNormNonNegative[of "(r\<ominus>p)"] lemSqrMonoStrict by auto
  hence sep: "sep2 r p < sqr (x+y)" using npr lemSquareOfSqrt AxEField by auto

  thus ?thesis using npr lemSep2Symmetry[of "r" "p"] by auto
qed


end (* of class Norms *)

end (* of theory Norms *)
