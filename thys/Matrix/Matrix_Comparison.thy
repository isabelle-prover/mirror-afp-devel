(*  Title:       Executable Matrix Operations on Matrices of Arbitrary Dimensions
    Author:      Christian Sternagel <christian.sternagel@uibk.ac.at>
                 René Thiemann       <rene.thiemann@uibk.ac.at>
    Maintainer:  Christian Sternagel and René Thiemann
    License:     LGPL
*)

(*
Copyright 2010 Christian Sternagel, René Thiemann

This file is part of IsaFoR/CeTA.

IsaFoR/CeTA is free software: you can redistribute it and/or modify it under the
terms of the GNU Lesser General Public License as published by the Free Software
Foundation, either version 3 of the License, or (at your option) any later
version.

IsaFoR/CeTA is distributed in the hope that it will be useful, but WITHOUT ANY
WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS FOR A
PARTICULAR PURPOSE.  See the GNU Lesser General Public License for more details.

You should have received a copy of the GNU Lesser General Public License along
with IsaFoR/CeTA. If not, see <http://www.gnu.org/licenses/>.
*)

section {* Comparison of Matrices *}

theory Matrix_Comparison
imports 
  "../Abstract-Rewriting/SN_Orders"
  Binomial
  Matrix_Arith
begin

text {*
  This theory provides the operations of comparing matrices w.r.t. some greater or
  greater-equal relation. Moreover, monotonicity criteria of the arithmetic operations
  w.r.t. the comparison operators are provided. Eventually, there are methods to estimate
  the growth of the linear norm of a matrix $M^n$ w.r.t. $n$. 
*}

subsection {* definitions / algorithms *}

(* comparison of vectors where all components have to be in relation *)
definition vec_comp_all :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a vec \<Rightarrow> 'a vec \<Rightarrow> bool"
  where "vec_comp_all r v w \<equiv> Ball (set (zip v w)) (\<lambda> (a,b). r a b)"

(* comparison of vectors using >= componentwise *)
definition vec_ge :: "('a :: non_strict_order) vec \<Rightarrow> 'a vec \<Rightarrow> bool"
  where "vec_ge \<equiv> vec_comp_all (op \<ge>)"

(* comparison of matrices where all components have to be in relation *)
definition mat_comp_all :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a mat \<Rightarrow> 'a mat \<Rightarrow> bool"
  where "mat_comp_all r m1 m2 \<equiv> Ball (set (zip m1 m2)) (\<lambda> (v,w). vec_comp_all r v w)"

(* comparison of matrices using >= componentwise *)
definition mat_ge :: "('a :: non_strict_order) mat \<Rightarrow> 'a mat \<Rightarrow> bool"
  where "mat_ge \<equiv> mat_comp_all (op \<ge>)"

(* demanding at least one strict decrease between two vectors *)
definition vec_pre_gtI :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a vec \<Rightarrow> 'a vec \<Rightarrow> bool"
  where "vec_pre_gtI gt v w \<equiv> Bex (set (zip v w)) (\<lambda> (a,b). gt a b)"

(* demanding at least one strict decrease between two matrices *)
definition mat_pre_gtI :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a mat \<Rightarrow> 'a mat \<Rightarrow> bool"
  where "mat_pre_gtI gt m1 m2 \<equiv> Bex (set (zip m1 m2)) (\<lambda> (v,w). vec_pre_gtI gt v w)"

(* strict comparison of matrices is done by demanding that all entries are weakly
   decreasing and that there is at least one entry in the upper left sub-matrices
   which strictly decreases *)      
definition mat_gtI :: "('a :: non_strict_order \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> nat \<Rightarrow> 'a mat \<Rightarrow> 'a mat \<Rightarrow> bool"
  where "mat_gtI gt sd m1 m2 \<equiv> mat_ge m1 m2 \<and> mat_pre_gtI gt (sub_mat sd sd m1) (sub_mat sd sd m2)"

(* checking whether a matrix is monotone w.r.t. >. To this end, 
   it is ensured that all columns in the upper left sub-matrix have an entry 
   of at least 1 *)
definition mat_monoI :: "('a \<Rightarrow> bool) \<Rightarrow> nat \<Rightarrow> 'a mat \<Rightarrow> bool"
where "mat_monoI geq1 sd m = Ball (set (sub_mat sd sd m)) (\<lambda> m. Bex (set m) geq1)"

(* max on vectors and matrices *)
abbreviation vec_max where "vec_max \<equiv> vec_plusI (max :: 'a :: ord \<Rightarrow> 'a \<Rightarrow> 'a)"
abbreviation mat_max where "mat_max \<equiv> mat_plusI (max :: 'a :: ord \<Rightarrow> 'a \<Rightarrow> 'a)"

(* checking whether a matrix is arctic positive (first entry is arctic positive) *)
definition mat_arc_posI :: "('a \<Rightarrow> bool) \<Rightarrow> 'a mat \<Rightarrow> bool"
where "mat_arc_posI ap m \<equiv> ap (m ! 0 ! 0)"

(* check whether a matrix is upper triangular *)
fun upper_triangular :: "('a :: {ord,one,zero}) mat \<Rightarrow> bool"
  where "upper_triangular [] = True"
      | "upper_triangular ((a # as) # m) = (1 \<ge> a \<and> (\<forall> b \<in> set as. b = 0) \<and> upper_triangular (map tl m))"
      | "upper_triangular ([] # m) = False"


subsection {* algorithms preserve dimensions *}

lemmas mat_max = mat_plus[of _ _ _ _ max]

subsection {* properties of algorithms which do not depend on properties of type of matrix *}

lemmas mat_max_index = mat_plus_index[of _ _ _ _ _ _ max]

lemma vec_comp_all_index: assumes "vec nr v1" 
  and "vec nr v2"
  shows "vec_comp_all r v1 v2 = (\<forall> i < nr. r (v1 ! i) (v2 ! i))"
using assms
unfolding vec_def vec_comp_all_def
proof (induct nr arbitrary: v1 v2)
  case (Suc nrr)
  from Suc obtain a1 w1 where v1: "v1 = a1 # w1" and lw1: "length w1 = nrr" by (cases v1, auto)
  from Suc obtain a2 w2 where v2: "v2 = a2 # w2" and lw2: "length w2 = nrr" by (cases v2, auto)
  have rec: "(\<forall> a \<in> set (zip w1 w2). case_prod r a) = (\<forall> i < nrr. r (w1 ! i) (w2 ! i))"
    by (rule Suc, auto simp: Suc lw1 lw2)
  show ?case (is "?l = ?r")
  proof (rule iffI)
    assume ?r
    thus ?l using Suc v1 v2 by auto
  next
    assume ?l
    show ?r
    proof (intro allI impI)
      fix i
      assume i: "i < Suc nrr"
      show "r (v1 ! i) (v2 ! i)"
        using `?l` v1 v2 i
        by (cases i, auto simp: rec)
    qed
  qed
qed simp

lemma vec_ge: assumes "vec nr v1" 
  and "vec nr v2"
  shows "vec_ge v1 v2 = (\<forall> i < nr. (v1 ! i) \<ge> (v2 ! i))"
using assms
unfolding vec_ge_def by (rule vec_comp_all_index) 

lemma vec_geI: assumes wf: "vec nr v1" "vec nr v2"
  and "\<And> i. i < nr \<Longrightarrow> (v1 ! i) \<ge> (v2 ! i)"
  shows "vec_ge v1 v2"
  using assms
  unfolding vec_ge[OF wf]  by auto 

lemma vec_geE: assumes ge: "vec_ge v1 v2" and wf: "vec nr v1" "vec nr v2"
  shows "\<And> i. i < nr \<Longrightarrow> (v1 ! i) \<ge> (v2 ! i)"
  using ge unfolding vec_ge[OF wf] by auto

lemma vec_pre_gt: assumes "vec nr v1" 
  and "vec nr v2"
  shows "vec_pre_gtI gt v1 v2 = (\<exists> i < nr. gt (v1 ! i) (v2 ! i))"
using assms[simplified vec_def, symmetric]
by (simp only: Not_eq_iff[symmetric, of "vec_pre_gtI gt v1 v2"], unfold vec_pre_gtI_def, simp add: set_zip, auto) 

lemma vec_pre_gtI: assumes wf: "vec nr v1" "vec nr v2"
  and "i < nr" "gt (v1 ! i) (v2 ! i)"
  shows "vec_pre_gtI gt v1 v2" unfolding vec_pre_gt[OF wf] using assms by auto

lemma vec_pre_gtE: assumes gt: "vec_pre_gtI gt v1 v2" and wf: "vec nr v1" "vec nr v2"
  obtains i where "i < nr" "gt (v1 ! i) (v2 ! i)"
  using gt unfolding vec_pre_gt[OF wf] by auto
    
lemma mat_comp_all: assumes "mat nr nc m1" 
  and "mat nr nc m2"
  shows "mat_comp_all r m1 m2 = (\<forall> i < nc. \<forall> j < nr. r (m1 ! i ! j) (m2 ! i ! j))"
using assms
unfolding mat_def mat_comp_all_def
proof (induct nc arbitrary: m1 m2)
  case (Suc ncc)
  from Suc obtain v1 mm1 where m1: "m1 = v1 # mm1" and lm1: "length mm1 = ncc \<and> (\<forall> a \<in> set mm1. vec nr a)" by (cases m1, auto)
  from Suc obtain v2 mm2 where m2: "m2 = v2 # mm2" and lm2: "length mm2 = ncc \<and> (\<forall> a \<in> set mm2. vec nr a)" by (cases m2, auto)
  from Suc m1 have wf1: "vec nr v1" by simp
  from Suc m2 have wf2: "vec nr v2" by simp
  have rec: "(\<forall> a \<in> set (zip mm1 mm2). case_prod (vec_comp_all r) a) = (\<forall> i < ncc. \<forall> j < nr. r (mm1 ! i ! j) (mm2 ! i ! j))"
    by (rule Suc, auto simp: Suc lm1 lm2)
  show ?case (is "?l = ?r")
  proof (rule iffI)
    assume ?r
    thus ?l using m1 m2 lm1 lm2 rec vec_comp_all_index[OF wf1 wf2] by auto
  next
    assume ?l
    hence ge: "vec_comp_all r v1 v2" and "\<forall> a \<in> set (zip mm1 mm2). case_prod (vec_comp_all r) a" using m1 m2 by auto
    with rec have ge2: " (\<forall>i<ncc. \<forall>j<nr. r (mm1 ! i ! j) (mm2 ! i ! j))" by simp
    show ?r
    proof (rule allI, intro impI)
      fix i 
      assume i: "i < Suc ncc" 
      show "\<forall> j < nr. r (m1 ! i ! j) (m2 ! i ! j)"
      proof (cases i, simp add: m1 m2, simp only: vec_comp_all_index[OF wf1 wf2, symmetric], rule ge)
        case (Suc ii)   
        with i have " ii < ncc" by simp
        with Suc 
        show ?thesis by (simp add: m1 m2, simp add: ge2)
      qed
    qed
  qed
qed simp

lemma mat_comp_allI: assumes wf: "mat nr nc m1" "mat nr nc m2"
  and "\<And> i j. i < nc \<Longrightarrow> j < nr \<Longrightarrow> r (m1 ! i ! j) (m2 ! i ! j)"
  shows "mat_comp_all r m1 m2" unfolding mat_comp_all[OF wf]
  using assms by auto

lemma mat_comp_allE: assumes ge: "mat_comp_all r m1 m2"
  and wf: "mat nr nc m1" "mat nr nc m2"
  shows "\<And> i j. i < nc \<Longrightarrow> j < nr \<Longrightarrow> r (m1 ! i ! j) (m2 ! i ! j)"
  using ge unfolding mat_comp_all[OF wf] by auto

lemma mat_geI: assumes wf: "mat nr nc m1" "mat nr nc m2"
  and "\<And> i j. i < nc \<Longrightarrow> j < nr \<Longrightarrow> (m1 ! i ! j) \<ge> (m2 ! i ! j)"
  shows "mat_ge m1 m2" unfolding mat_ge_def 
  by (rule mat_comp_allI, insert assms, auto)

lemma mat_geE: assumes "mat_ge m1 m2"
  and "mat nr nc m1" "mat nr nc m2"
  shows "\<And> i j. i < nc \<Longrightarrow> j < nr \<Longrightarrow> (m1 ! i ! j) \<ge> (m2 ! i ! j)"
  by (rule mat_comp_allE, insert assms, auto simp: mat_ge_def)

lemma mat_pre_gt: assumes "mat nr nc m1"
  and "mat nr nc m2"
  shows "mat_pre_gtI gt m1 m2 = (\<exists> i < nc. \<exists> j < nr. gt (m1 ! i ! j) (m2 ! i ! j))"
proof -
  from assms have l1: "nc = length m1" and l2: "length m2 = length m1" 
    and vl1: "\<And> i. i < nc \<Longrightarrow> vec nr (m1 ! i)" and vl2: "\<And> i. i < nc \<Longrightarrow> vec nr (m2 ! i)" unfolding mat_def by auto
  let ?l = "\<lambda> i. \<not> vec_pre_gtI gt (m1 ! i) (m2 ! i)"
  let ?r = "\<lambda> i. \<forall> j < nr. \<not> gt (m1 ! i ! j) (m2 ! i ! j)"
  have lr: "\<forall> i < nc. ?l i = ?r i"
  proof (intro allI impI)
    fix i
    assume i: "i < nc"
    show "?l i = ?r i" using vec_pre_gt[OF vl1[OF i] vl2[OF i]] by auto
  qed     
  show ?thesis
  proof (simp only: Not_eq_iff[symmetric, of "mat_pre_gtI gt m1 m2"], unfold mat_pre_gtI_def set_zip l2 min.idem l1[symmetric])
    show "(\<not> (\<exists> (x,y) \<in> {(m1 ! i, m2 ! i) | i. i < nc}. vec_pre_gtI gt x y)) = (\<not> (\<exists> i<nc. \<exists> j<nr. gt (m1 ! i ! j) (m2 ! i ! j)))"
      using lr by auto
  qed
qed

lemma mat_pre_gtI: assumes wf: "mat nr nc m1" "mat nr nc m2"
  and "i < nc" "j < nr" "gt (m1 ! i ! j) (m2 ! i ! j)"
  shows "mat_pre_gtI gt m1 m2" unfolding mat_pre_gt[OF wf] using assms by auto

lemma mat_pre_gtE: assumes gt: "mat_pre_gtI gt m1 m2" and wf: "mat nr nc m1" "mat nr nc m2"
  obtains i j where "i < nc" "j < nr" "gt (m1 ! i ! j) (m2 ! i ! j)"
  using gt unfolding mat_pre_gt[OF wf] by auto

lemma mat_gt: assumes wf1: "mat n n m1"
  and wf2: "mat n n m2"
  and sd: "sd \<le> n"
  shows "mat_gtI gt sd m1 m2 = (mat_ge m1 m2 \<and> (\<exists> i < sd. \<exists> j < sd. gt (m1 ! i ! j) (m2 ! i ! j)))"
proof -
  have id: "mat_pre_gtI gt (sub_mat sd sd m1) (sub_mat sd sd m2) = (\<exists> i < sd. \<exists> j < sd. gt (m1 ! i ! j) (m2 ! i ! j))" (is "?l = ?r")
  proof -
    have "?l = (\<exists> i < sd. \<exists> j < sd. gt (sub_mat sd sd m1 ! i ! j) (sub_mat sd sd m2 ! i ! j))"
      by (simp only: mat_pre_gt[OF sub_mat[OF wf1 sd sd] sub_mat[OF wf2 sd sd]])
    also have "\<dots> = ?r" by (simp only: Not_eq_iff[symmetric, of _ ?r], auto simp: sub_mat_index[OF wf1 sd sd] sub_mat_index[OF wf2 sd sd])
    finally show "?l = ?r" .
  qed
  thus ?thesis unfolding mat_gtI_def by auto
qed

lemma mat_mono: assumes wf: "mat n n m"
  and sd: "sd \<le> n" 
  shows "mat_monoI geq1 sd m = (\<forall> i < sd. \<exists> j < sd. geq1 (m ! i ! j))"
proof -
  from wf sd have n: "n = length m" and sd: "sd \<le> length m"  and v: "\<forall> v \<in> set m. length v = n" unfolding mat_def by (auto simp: vec_def)
  have "set (take sd m) \<subseteq> set m" by (rule set_take_subset)
  with v have v: "\<forall> v \<in> set (take sd m). length v = n" by auto
  have "(\<forall> x \<in> set (take sd m). \<exists> x \<in> set (take sd x). geq1 x) = (\<forall> i < sd. \<exists> j < sd. geq1 (m ! i ! j))"
    (is "?l = ?r")
  proof
    assume ?l
    show ?r
    proof (intro allI impI)
      fix i
      assume i: "i < sd" with sd have im: "i < length m" by auto
      have mi: "m ! i \<in> set (take sd m)" by (simp add: set_conv_nth, rule exI[of _ i],
        simp add: i im)        
      with `?l` have "\<exists> x \<in> set (take sd (m ! i)). geq1 x" by auto
      then obtain x where x: "x \<in> set (take sd (m ! i))" and geq: "geq1 x" by auto
      from v mi sd n have sdmi: "sd \<le> length (m ! i)" by auto
      from x[simplified set_conv_nth] obtain j where x: "x = take sd (m ! i) ! j" and 
        j: "j < length (take sd (m ! i))" by auto
      from j sdmi have j: "j < sd" by auto
      with x sdmi have x: "x = m ! i ! j" by auto
      from j geq x show "\<exists> j < sd. geq1 (m ! i ! j)" by auto
    qed
  next
    assume ?r
    show ?l
    proof (intro ballI)
      fix v
      assume vm: "v \<in> set (take sd m)"
      then obtain i where i: "i < sd" and vmi: "v = m ! i" by (simp add: set_conv_nth, auto)        
      with `?r` obtain j where j: "j < sd" and geq: "geq1 (m ! i ! j)" by auto
      from v vm sd n have sdv: "sd \<le> length v" by auto
      with j have j2: "j < length v" by auto
      have "v ! j \<in> set (take sd v)" by (simp add: set_conv_nth, rule exI[of _ j], simp add: j sdv j2)
      hence "m ! i ! j \<in> set (take sd v)" by (simp add: vmi)
      with geq show "\<exists> x \<in> set (take sd v). geq1 x" by auto
    qed
  qed
  thus ?thesis unfolding mat_monoI_def sub_mat_def sub_vec_def 
    by auto
qed


lemma upper_triangular: assumes "mat n n m"
  shows "upper_triangular m = (\<forall> i < n. 1 \<ge> (m ! i ! i) \<and> (\<forall> j < n. j > i \<longrightarrow> m ! i ! j = 0))"
  using assms
proof (induct n arbitrary: m)
  case 0
  thus ?case unfolding mat_def by auto
next
  case (Suc n)
  note mat = Suc(2)
  note mat = mat[unfolded mat_def]
  from mat obtain r rs where m: "m = r # rs" by (cases m, auto)
  from mat m obtain a as where r: "r = a # as" by (cases r, auto simp: vec_def)
  let ?r = "map hd rs" 
  let ?m = "map tl rs"
  from mat[unfolded m r] have l: "length ?m = n" "length ?r = n" "length rs = n" and v: "Ball (set rs) (vec (Suc n))" "vec (Suc n) (a # as)" by auto
  from v have "Ball (set ?m) (vec n)" by (induct rs, auto simp: vec_def)
  with l have mat: "mat n n ?m" unfolding mat_def by simp
  from v have las: "length as = n" unfolding vec_def by simp
  note IH = Suc(1)[OF mat]
  let ?l = "\<lambda> i. 1 \<ge> (map tl rs ! i ! i) \<and>
            (\<forall>j<n. i < j \<longrightarrow> map tl rs ! i ! j = 0)"
  let ?r = "\<lambda> i. 1 \<ge> (rs ! i ! Suc i) \<and>
            (\<forall>j<n. i < j \<longrightarrow> rs ! i ! Suc j = 0)"
  {
    fix i
    assume i: "i < n"
    with l have irs:  "i < length rs" by auto
    from v have "\<forall> r \<in> set rs. vec (Suc n) r" by auto
    from this[unfolded all_set_conv_all_nth l] i have v: "vec (Suc n) (rs ! i)" by auto
    hence "length (rs ! i) = Suc n" unfolding vec_def by auto
    then obtain a as where rsi: "rs ! i = a # as" and las: "length as = n" by (cases "rs ! i", auto)
    have "?l i = ?r i" 
      unfolding nth_map[OF irs] 
      unfolding rsi by auto      
  }
  hence main: "(\<forall>i<n. ?l i) = (\<forall> i<n. ?r i)" by auto
  show ?case unfolding m r upper_triangular.simps
    unfolding IH 
    unfolding all_Suc_conv
    unfolding all_set_conv_all_nth l las
    by (auto simp: main)
qed


subsection {* lemmas requiring properties of plus, times, ge, ... *}

lemma vec_ge_refl: "vec_ge v v"
  unfolding vec_ge_def vec_comp_all_def
  by (induct v, auto simp: ge_refl)

lemma mat_ge_refl: "mat_ge m m"
  unfolding mat_ge_def mat_comp_all_def 
  by (induct m, auto simp: vec_ge_refl[unfolded vec_ge_def])

lemma vec_ge_trans: assumes ge12: "vec_ge v1 v2" and ge23: "vec_ge v2 v3" and wf: "vec nr v1" "vec nr v2" "vec nr v3"
  shows "vec_ge v1 v3"
proof (rule vec_geI)
  fix i
  assume i: "i < nr"
  show "v1 ! i \<ge> v3 ! i" using ge_trans[OF vec_geE[OF ge12 _ _ i] vec_geE[OF ge23 _ _ i]] wf by auto
qed (insert wf, auto)

lemma mat_ge_trans: assumes ge12: "mat_ge v1 v2" and ge23: "mat_ge v2 v3" and wf: "mat nr nc v1" "mat nr nc v2" "mat nr nc v3"
  shows "mat_ge v1 v3"
proof (rule mat_geI)
  fix i j
  assume ij: "i < nc" "j < nr"
  show "v1 ! i ! j \<ge> v3 ! i ! j" using ge_trans[OF mat_geE[OF ge12 _ _ ij] mat_geE[OF ge23 _ _ ij]] using wf by auto
qed (insert wf, auto)

lemma vec_plus_left_mono: assumes ge: "vec_ge v1 (v2 :: ('a :: ordered_ab_semigroup)vec)" and 
  wf: "vec nr v1" "vec nr v2" "vec nr v3"
  shows "vec_ge (vec_plus v1 v3) (vec_plus v2 v3)"
proof (rule vec_geI)
  fix i
  assume i: "i < nr"
  note [simp] = vec_plus_index[OF _ _ i] vec_geE[OF ge _ _ i]
  show "vec_plus v1 v3 ! i \<ge> vec_plus v2 v3 ! i" using wf by (auto intro: plus_left_mono)
qed (insert wf, auto)

lemma mat_plus_left_mono: assumes ge: "mat_ge m1 (m2 :: ('a :: ordered_ab_semigroup)mat)" 
  and wf: "mat nr nc m1" "mat nr nc m2" "mat nr nc m3" 
  shows "mat_ge (mat_plus m1 m3) (mat_plus m2 m3)"
proof (rule mat_geI)
  fix i j
  assume i: "i < nc" "j < nr"
  note [simp] = mat_plus_index[OF _ _ i] mat_geE[OF ge _ _ i]
  show "mat_plus m1 m3 ! i ! j \<ge> mat_plus m2 m3 ! i ! j" using wf by (auto intro: plus_left_mono)
qed (insert wf, auto)

lemma scalar_prod_mono_left: assumes wf1: "vec nr (v1 :: ('a :: ordered_semiring_1) vec)"
  and wf2: "vec nr v2"
  and wf3: "vec nr v3"
  and ge1: "vec_ge v1 v2"
  and ge2: "vec_ge v3 (vec0 nr)"
  shows "scalar_prod v1 v3 \<ge> scalar_prod v2 v3"
using assms unfolding vec_def vec_ge_def vec_comp_all_def vec0I_def
proof -
  assume "length v1 = nr" and "length v2 = nr" and " length v3 = nr" and " \<forall>(x,y)\<in>set (zip v1 v2). x \<ge> y" and " \<forall>(x,y)\<in>set (zip v3 (replicate nr 0)). x \<ge> y"
  thus "scalar_prod v1 v3 \<ge> scalar_prod v2 v3"
  proof (induct nr arbitrary: v1 v2 v3)
    case (Suc nrr)
    from Suc obtain a1 w1 where v1: "v1 = a1 # w1" and w1: "length w1 = nrr" by (cases v1, auto)
    from Suc obtain a2 w2 where v2: "v2 = a2 # w2" and w2: "length w2 = nrr" by (cases v2, auto)
    from Suc obtain a3 w3 where v3: "v3 = a3 # w3" and w3: "length w3 = nrr" by (cases v3, auto)
    from Suc have rec: "scalar_prod w1 w3 \<ge> scalar_prod w2 w3" (is "?l \<ge> ?r")
      by (auto simp: w1 w2 w3 v1 v2 v3)
    show ?case proof (simp add: v1 v2 v3 scalar_prod_cons)
      have one: "a1 * a3 \<ge> a2 * a3" using times_left_mono[of a3 a2 a1] Suc v1 v2 v3 by auto
      hence "a1 * a3 + ?l \<ge> a2 * a3 + ?l" by (rule plus_left_mono)
      also have "a2 * a3 + ?l \<ge> a2 * a3 + ?r" using rec by (rule plus_right_mono)
      finally show "a1 * a3 + ?l \<ge> a2 * a3 + ?r" .
    qed
  qed (simp add: scalar_prodI_def ge_refl)
qed

lemma scalar_prod_mono_right: assumes wf1: "vec nr (v1 :: ('a :: ordered_semiring_1) vec)"
  and wf2: "vec nr v2"
  and wf3: "vec nr v3"
  and ge1: "vec_ge v2 v3"
  and ge2: "vec_ge v1 (vec0 nr)"
  shows "scalar_prod v1 v2 \<ge> scalar_prod v1 v3"
using assms unfolding vec_def vec_ge_def vec0I_def vec_comp_all_def
proof -
  assume "length v1 = nr" and "length v2 = nr" and " length v3 = nr" 
    and " \<forall>(x,y)\<in>set (zip v2 v3). x \<ge> y" 
    and " \<forall>(x,y)\<in>set (zip v1 (replicate nr 0)). x \<ge> y"
  thus "(scalar_prod v1 v2) \<ge> (scalar_prod v1 v3)"
  proof (induct nr arbitrary: v1 v2 v3)
    case (Suc nrr)
    from Suc obtain a1 w1 where v1: "v1 = a1 # w1" and w1: "length w1 = nrr" by (cases v1, auto)
    from Suc obtain a2 w2 where v2: "v2 = a2 # w2" and w2: "length w2 = nrr" by (cases v2, auto)
    from Suc obtain a3 w3 where v3: "v3 = a3 # w3" and w3: "length w3 = nrr" by (cases v3, auto)
    from Suc have rec: "scalar_prod w1 w2 \<ge> scalar_prod w1 w3" (is "?l \<ge> ?r")
      by (auto simp: w1 w2 w3 v1 v2 v3)
    show ?case proof (simp add: v1 v2 v3 scalar_prod_cons)
      have one: "a1 * a2 \<ge> a1 * a3" using times_right_mono[of a1 a3 a2] Suc v1 v2 v3 by auto
      hence "a1 * a2 + ?l \<ge> a1 * a3 + ?l" by (rule plus_left_mono)
      also have "a1 * a3 + ?l \<ge> a1 * a3 + ?r" using rec by (rule plus_right_mono)
      finally show "a1 * a2 + ?l \<ge> a1 * a3 + ?r" .
    qed
  qed (simp add: scalar_prodI_def ge_refl)
qed


lemma mat_mult_left_mono:
  assumes wf1: "mat nr nc (m1 :: ('a :: ordered_semiring_1) mat)"
  and wf2: "mat nr nc m2"
  and wf3: "mat nc ncc m3"
  and ge1: "mat_ge m1 m2"
  and ge2: "mat_ge m3 (mat0 nc ncc)"
  shows "mat_ge (mat_mult nr m1 m3) (mat_mult nr m2 m3)"
proof -
  let ?m13 = "mat_mult nr m1 m3"
  let ?m23 = "mat_mult nr m2 m3"
  from mat_mult[OF wf1 wf3] have wf13: "mat nr ncc ?m13" .
  from mat_mult[OF wf2 wf3] have wf23: "mat nr ncc ?m23" .
  show ?thesis 
  proof (rule mat_geI)
    fix i j
    assume i: "i < ncc" and j: "j < nr"
    have ge1a: "\<forall>i<nc. \<forall> j < nr.  m1 ! i ! j \<ge> m2 ! i ! j"
      using mat_geE[OF ge1 wf1 wf2] by simp
    have ge2a: "\<forall>ia<nc. col m3 i ! ia \<ge> vec0 nc ! ia"
      using mat_geE[OF ge2 wf3 mat0] i unfolding col_def mat0I_def vec0I_def
      by auto      
    show "?m13 ! i ! j \<ge> ?m23 ! i ! j"
      by (unfold mat_mult_index[OF wf1 wf3 j i]
           mat_mult_index[OF wf2 wf3 j i], 
        rule scalar_prod_mono_left[OF row[OF wf1 j] row[OF wf2 j] col[OF wf3 i]],
        unfold vec_ge[OF row[OF wf1 j] row[OF wf2 j]],
        (auto simp: row_col[OF wf1 j] row_col[OF wf2 j] col_def ge1a j)[1],
        unfold vec_ge[OF col[OF wf3 i] vec0],
        rule ge2a)
  qed (insert wf1 wf2 wf3, auto)
qed  


lemma mat_mult_right_mono:
  assumes wf1: "mat nr nc (m1 :: ('a :: ordered_semiring_1) mat)"
  and wf2: "mat nc ncc m2"
  and wf3: "mat nc ncc m3"
  and ge1: "mat_ge m1 (mat0 nr nc)"
  and ge2: "mat_ge m2 m3"
  shows "mat_ge (mat_mult nr m1 m2) (mat_mult nr m1 m3)"
proof -
  let ?m12 = "mat_mult nr m1 m2"
  let ?m13 = "mat_mult nr m1 m3"
  from mat_mult[OF wf1 wf2] have wf12: "mat nr ncc ?m12" .
  from mat_mult[OF wf1 wf3] have wf13: "mat nr ncc ?m13" .
  show ?thesis 
  proof (rule mat_geI)
    fix i j
    assume i: "i < ncc" and j: "j < nr"
    have ge2a: " \<forall>ia<nc. col m2 i ! ia \<ge> col m3 i ! ia"
      using mat_geE[OF ge2 wf2 wf3 i] unfolding col_def by auto
    have ge1a: " \<forall>i<nc. m1 ! i ! j \<ge> 0" 
      using mat_geE[OF ge1 wf1 mat0] j unfolding mat0I_def vec0I_def
      by auto
    show "?m12 ! i ! j \<ge> ?m13 ! i ! j"
      by  (unfold mat_mult_index[OF wf1 wf2 j i]
             mat_mult_index[OF wf1 wf3 j i],
        rule scalar_prod_mono_right[OF row[OF wf1 j] col[OF wf2 i] col[OF wf3 i]], 
        unfold vec_ge[OF col[OF wf2 i] col[OF wf3 i]], rule ge2a, 
        unfold vec_ge[OF row[OF wf1 j] vec0],
        simp add: row_col[OF wf1 j] vec0I_def col_def, rule ge1a) 
  qed (insert wf1 wf2 wf3, auto)
qed

lemma mat1_ge_mat0: "mat_ge (mat1 n) ((mat0 n n) :: ('a :: ordered_semiring_1) mat)" (is "mat_ge ?m1 ?m0")
proof (rule mat_geI)
  fix i j
  assume i: "i < n" and j: "j < n"
  have zero_ij: "?m0 ! i ! j = 0" by (rule mat0_index[OF i j])
  have one_ij: "?m1 ! i ! j = (if i = j then 1 else 0)" by (rule mat1_index[OF i j])
  show "?m1 ! i ! j \<ge> ?m0 ! i ! j"
    by (simp add: zero_ij one_ij ge_refl one_ge_zero)
qed auto

lemma mat_max_comm: assumes wf: "mat nr nc m1" "mat nr nc (m2 :: ('a :: non_strict_order) mat)" shows "mat_max m1 m2 = mat_max m2 m1"
proof (rule mat_eqI)
  fix i j
  assume i: "i < nc" and j: "j < nr"
  show "mat_max m1 m2 ! i ! j = mat_max m2 m1 ! i ! j"
    by (unfold mat_max_index[OF wf i j] mat_max_index[OF wf(2,1) i j], rule max_comm)
qed (insert wf, auto)

lemma mat_max_ge_x: assumes wf: "mat nr nc m1" "mat nr nc m2" shows "mat_ge (mat_max m1 m2) m1"
proof (rule mat_geI)
  fix i j
  assume i: "i < nc" and j: "j < nr"
  show "mat_max m1 m2 ! i ! j \<ge> m1 ! i ! j"
    by (unfold mat_max_index[OF wf i j], rule max_ge_x)
qed (insert wf, auto)

lemma mat_max_ge: assumes wf1: "mat nr nc m1" and wf2: "mat nr nc m2" 
  shows "mat_ge (mat_max m1 m2) m1" "mat_ge (mat_max m1 m2) m2"
  using mat_max_ge_x[OF wf1 wf2] mat_max_ge_x[OF wf2 wf1] unfolding mat_max_comm[OF wf2 wf1]
  by auto

lemma mat_max_id: assumes ge: "mat_ge m1 m2" and wf: "mat nr nc m1" "mat nr nc m2"
  shows "mat_max m1 m2 = m1"
proof (rule mat_eqI)
  fix i j
  assume i: "i < nc" and j: "j < nr"
  from mat_geE[OF ge _ _ this]
  have "m1 ! i ! j \<ge> m2 ! i ! j" using wf by auto
  thus "mat_max m1 m2 ! i ! j = m1 ! i ! j"
    by (unfold mat_max_index[OF wf i j], rule max_id)
qed (insert wf, auto)

lemma mat_max_mono: assumes ge: "mat_ge m1 m2" and wf1: "mat nr nc m1" and wf2: "mat nr nc m2"
  and wf3: "mat nr nc m3"
  shows "mat_ge (mat_max m3 m1) (mat_max m3 m2)"
proof (rule mat_geI)
  fix i j
  assume i: "i < nc" and j: "j < nr"
  from mat_geE[OF ge _ _ this] 
  have "m1 ! i ! j \<ge> m2 ! i ! j" using wf1 wf2 by simp
  hence "max (m3 ! i ! j) (m1 ! i ! j) \<ge> max (m3 ! i ! j) (m2 ! i ! j)" by (rule max_mono)
  thus "mat_max m3 m1 ! i ! j \<ge> mat_max m3 m2 ! i ! j"
    by (unfold mat_max_index[OF wf3 wf1 i j] mat_max_index[OF wf3 wf2 i j])
qed (insert wf1 wf2 wf3, auto)

lemma mat_pow_ge_zero: assumes m: "mat n n (m :: ('a :: ordered_semiring_1) mat)" and m0: "mat_ge m (mat0 n n)"
  shows "mat_ge (mat_pow n m nn) (mat0 n n)"
proof (induct nn)
  case 0
  show ?case by (simp add: mat1_ge_mat0)
next
  case (Suc nn)
  show ?case
    unfolding mat_powI.simps
    by (rule mat_ge_trans[OF mat_mult_left_mono[OF mat_pow[OF m] mat0 m Suc m0] _ mat_mult[OF mat_pow[OF m] m] mat_mult[OF mat0 m] mat0], unfold mat0_mult_left[OF m], rule mat_ge_refl) 
qed    

lemma upper_triangular_mat_pow_main: assumes mat: "mat d d (m :: ('a :: poly_carrier) mat)"
  and tri: "upper_triangular m"
  and a: "\<And> i j. i < d \<Longrightarrow> j < d \<Longrightarrow> (m ! i ! j) \<ge> 0 \<and> a \<ge> (m ! i ! j)"
  and a1: "a \<ge> 1"
  shows "\<forall> i < d. \<forall> j < d. (i > j \<longrightarrow> mat_pow d m n ! j ! i = 0) \<and> (of_nat (fact (j - i)) * (of_nat n * a)^(j - i)) \<ge> (mat_pow d m n ! j ! i)"
proof -
  let ?n = "of_nat :: nat \<Rightarrow> 'a"
  let ?m = "mat_pow d m"
  let ?p = "\<lambda> n i j. i > j \<longrightarrow> ?m n ! j ! i = 0"
  let ?q = "\<lambda> n i j. (?n (fact (j - i)) * (?n n * a)^(j - i)) \<ge> (?m n ! j ! i)"
  show "\<forall> i < d. \<forall> j < d. ?p n i j \<and> ?q n i j"
  proof (induct n)
    case 0
    show ?case 
    proof (intro allI impI)
      fix i j
      assume i: "i < d" and j: "j < d"
      have m0: "?m 0 = mat1 d" by simp
      note id = m0 mat1_index[OF j i]
      show "?p 0 i j \<and> ?q 0 i j" unfolding id by (cases "j - i", auto intro: ge_refl one_ge_zero)
    qed
  next
    case (Suc n)
    show ?case
    proof (intro allI impI)
      fix i j
      assume i: "i < d" and j: "j < d"
      have mS: "?m (Suc n) = mat_mult d (?m n) m" by simp
      note id = mS mat_mult_index[OF mat_pow[OF mat] mat i j]
      let ?rowi = "row (?m n) i"
      let ?colj = "col m j"
      let ?prod = "scalar_prod ?rowi ?colj"
      from row[OF mat_pow[OF mat] i] have row: "vec d ?rowi" .
      from col[OF mat j] have col: "vec d ?colj" .
      have id: "?m (Suc n) ! j ! i = ?prod" unfolding id ..
      let ?z = "zip ?rowi ?colj" 
      from row col have len: "length ?rowi = length ?colj" and lenz: "length ?z = d" unfolding vec_def by auto
      let ?map = "map (\<lambda> k. (?m n ! k ! i, m ! j ! k)) [0 ..< d]"
      note tri = tri[unfolded upper_triangular[OF mat], rule_format]
      have "?z = map (\<lambda> k. (?rowi ! k, ?colj ! k)) [0 ..< d]"
        unfolding zip_nth_conv[OF len] using col[unfolded vec_def] by simp
      also have "... = ?map"
        unfolding map_eq_conv
      proof
        fix k
        assume "k \<in> set [0..<d]"
        hence k: "k < d" by auto
        show "(?rowi ! k, ?colj ! k) = (?m n ! k ! i, m ! j ! k)"
          unfolding row_col[OF mat_pow[OF mat] i k]
          unfolding col_def by simp
      qed
      finally have zip: "?z = ?map" .
      {
        fix k
        assume k: "k < d"
        hence kd: "k < length [0..<d]" and nth: "[0..<d] ! k = k" by auto
        hence "?z ! k = (?m n ! k ! i, m ! j ! k)"
          unfolding zip nth_map[OF kd] nth by simp
      } note zk = this        
      {
        assume ji: "j < i"
        obtain z where z: "?z = z" by auto        
        have "\<forall> ab \<in> set ?z. fst ab = 0 \<or> snd ab = 0"  
          unfolding all_set_conv_all_nth lenz
        proof (intro allI impI)
          fix k
          assume k: "k < d"
          show "fst (?z ! k) = 0 \<or> snd (?z ! k) = 0" 
            unfolding zk[OF k] fst_conv snd_conv
          proof (cases "k < i")
            case True
            from Suc[rule_format, THEN conjunct1, rule_format, OF i k True]
            show "?m n ! k ! i = 0 \<or> m ! j ! k = 0" by simp
          next
            case False
            with ji k i j have "j < k" by arith
            from tri[OF j, THEN conjunct2, rule_format, OF k this] 
            show "?m n ! k ! i = 0 \<or> m ! j ! k = 0" by simp
          qed
        qed
        hence "\<forall> (a,b) \<in> set z. a = 0 \<or> b = 0" unfolding z by force
        hence "?prod = 0" unfolding scalar_prod z 
          by (induct z, auto)
      } note lower_part = this
      hence p: "?p (Suc n) i j" unfolding id by simp
      from a[OF i i] have a0: "a \<ge> 0" using ge_trans[of "m ! i ! i" a 0] by auto
      have na: "\<And> n. ?n n * a \<ge> (0 :: 'a)"
        by (rule mult_ge_zero[OF of_nat_ge_zero a0])
      have "?q (Suc n) i j"
      proof (cases "j < i") 
        case True
        show ?thesis unfolding id lower_part[OF True] 
          by (rule mult_ge_zero[OF of_nat_ge_zero pow_ge_zero[OF na]])
      next
        case False
        hence ji: "j \<ge> i" by simp
        let ?fact = "\<lambda> k. ?n (fact (k - i)) * (?n n * a) ^ (k - i)" 
        let ?fac = "\<lambda> k. ?n (fact k) * (?n n * a) ^ k"
        let ?ind = "\<lambda> k. (if k < i then 0 else ?fact k)"
        let ?mind = "map ?ind [0..< d]"
        have mind: "vec d ?mind" unfolding vec_def by auto
        let ?fsn = "?n (fact (j - i)) * (?n (Suc n) * a) ^ (j - i)"
        let ?cola = "\<lambda> k. if k < j then a else if k = j then 1 else 0"
        let ?mcola = "map ?cola [0 ..< d]"
        let ?both = "\<lambda> k. (?ind k, ?cola k)"
        let ?prod = "\<lambda> k. (?ind k * ?cola k)"
        let ?mboth = "map ?both [0 ..< d]" 
        let ?mprod = "map ?prod [0 ..< d]" 
        have cola: "vec d ?mcola" unfolding vec_def by simp
        let ?z = "zip ?mind ?mcola"
        have len: "length ?mind = length ?mcola" by simp
        have z: "?z = ?mboth"
          unfolding zip_nth_conv[OF len] by auto
        let ?f = "(\<lambda> (x,y). op + (x * y))"
        let ?id = "map ?prod [i ..< d]" 
        let ?ij = "map ?prod [i ..< Suc j]" 
        let ?jd = "map ?prod [Suc j ..< d]"
        let ?zi = "map ?prod [0 ..< i]" 
        obtain i_d where i_d: "i_d = ?id" by auto
        obtain diff where diff: "j - i = diff" by auto
        have "scalar_prod ?mind ?mcola = listsum ?mprod" unfolding scalar_prod unfolding z unfolding map_map o_def by simp
        also have "... = listsum ?zi + listsum i_d"
          using upt_add_eq_append[of 0 i "d - i"] i i_d by auto
        also have "listsum ?zi = 0"
        proof (rule listsum_0)
          fix x
          assume "x \<in> set ?zi"
          then obtain k where k: "k < i" and xy: "x = ?prod k" by auto
          from k xy show "x = 0" by auto
        qed
        also have "0 + listsum i_d = listsum ?id" unfolding i_d  by simp
        also have "?id = ?ij @ ?jd"
          using upt_add_eq_append[of i "Suc j" "d - Suc j"] ji j by auto
        also have "listsum (?ij @ ?jd) = listsum ?ij + listsum ?jd" by simp
        also have "listsum ?jd = 0"
        proof (rule listsum_0)
          fix x
          assume "x \<in> set ?jd"
          then obtain k where k: "Suc j \<le> k" "k < d" and xy: "x = ?prod k" by auto
          from k xy show "x = 0" by auto
        qed
        also have "listsum ?ij + 0 = listsum ?ij" by simp
        also have "?ij = map (\<lambda> k. (?fact k * ?cola k)) [i ..< Suc j]"
          by (rule map_cong, auto)
        also have "... = map (\<lambda> k. (?fact k * ?cola k)) [i ..< j] @ [?fact j]"
          using upt_add_eq_append[of i j "Suc 0", OF ji]  by auto
        also have "... = map (\<lambda> k. (?fact k * a)) [i ..< j] @ [?fact j]" (is "_ = ?zwi @ _") by auto
        also have "?zwi = map (\<lambda> k. (?fac k * a)) [0 ..< j - i]" (is "_ = ?map")
          by (rule nth_map_conv, auto)     
        also have "listsum (?map @ [?fact j]) = listsum ?map + ?fact j" by simp
        finally have sprod: "scalar_prod ?mind ?mcola = listsum ?map + ?fact j" .
        have "?fsn \<ge> scalar_prod ?mind ?mcola" (is "_ \<ge> ?z")
          unfolding sprod
          unfolding diff
          unfolding of_nat_Suc
        proof (induct diff)
          case 0
          show ?case by (simp add: ge_refl)
        next
          case (Suc d)
          note IH = this
          show ?case
          proof (cases d)
            case 0
            show ?thesis unfolding 0 by (auto simp: ge_refl field_simps)
          next
            case (Suc dd)                        
            have ana0: "(1 + ?n n) * a \<ge> 0"
              unfolding of_nat_Suc[symmetric] by (rule na)
            have anana: "(1 + ?n n) * a \<ge> ?n n * a"
              using plus_right_mono[OF a0, of "a * ?n n"] by (auto simp: field_simps)
            have ananapow: "((1 + ?n n) * a) ^ d \<ge> (?n n * a) ^ d \<and> (?n n * a)^d \<ge> 0"
              by (rule pow_mono[OF anana na])
            have "?n (fact (Suc d)) * (a + ?n n * a) ^ Suc d = 
              ?n (fact (Suc d)) * ((a + ?n n * a) * (a + ?n n * a) ^ d)" 
              unfolding power_Suc by simp
            also have "... = ?n (fact (Suc d)) * ((?n n * a) * (a + ?n n * a) ^ d) + 
              ?n (d * fact d) * (a * (a + ?n n * a) ^ d) + 
              ?n (fact d) * (a * (a + ?n n * a) ^ d)" 
              by (simp add: field_simps)
            also have "... \<ge> ?n (fact (Suc d)) * ((?n n * a) * (a + ?n n * a) ^ d) + 
              ?n (d * fact d) * (a * (a + ?n n * a) ^ d) + 
              ?n (fact d) * (1 * (a + ?n n * a) ^ d)" 
              by (rule plus_right_mono[OF times_right_mono[OF of_nat_ge_zero times_left_mono[OF pow_ge_zero a1]]], insert na[of "Suc n"], auto simp: field_simps)
            also have "?n (fact d) * (1 * (a + ?n n * a) ^ d) = ?n (fact d) * (((1 + ?n n) * a) ^ d)" by (simp add: field_simps)
            also have "?n (fact (Suc d)) * ((?n n * a) * (a + ?n n * a) ^ d) + 
              ?n (d * fact d) * (a * (a + ?n n * a) ^ d) + 
              ?n (fact d) * (((1 + ?n n) * a) ^ d) \<ge> 
              ?n (fact (Suc d)) * ((?n n * a) * (a + ?n n * a) ^ d) + 
              ?n (d * fact d) * (a * (a + ?n n * a) ^ d) + 
              ((\<Sum>k\<leftarrow>[0..<d]. ?n (fact k) * (?n n * a) ^ k * a) +
  ?n (fact d) * (?n n * a) ^ d)" (is "_ \<ge> ?z")
              by (rule plus_right_mono[OF IH])
            also have "?z = ?n (fact (Suc d)) * ((?n n * a) * (a + ?n n * a) ^ d) + 
              ?n (d * fact d) * (a * (a + ?n n * a) ^ d) + 
              (\<Sum>k\<leftarrow>[0..<d]. ?n (fact k) * (?n n * a) ^ k * a) +
                ?n (fact d) * (?n n * a) ^ d" by (simp add: field_simps)
            also have "... \<ge> ?n (fact (Suc d)) * ((?n n * a) * (a + ?n n * a) ^ d) + 
              ?n (d * fact d) * (a * (a + ?n n * a) ^ d) + 
              (\<Sum>k\<leftarrow>[0..<d]. ?n (fact k) * (?n n * a) ^ k * a) +
                0" (is "_ \<ge> ?z")
              by (rule plus_right_mono[OF mult_ge_zero[OF of_nat_ge_zero]], insert ananapow, auto)
            also have "?z = ?n (fact (Suc d)) * ((?n n * a) * (a + ?n n * a) ^ d) + 
              (\<Sum>k\<leftarrow>[0..<d]. ?n (fact k) * (?n n * a) ^ k * a) +
              ?n (d * fact d) * (a * (a + ?n n * a) ^ d)" by (simp add: ac_simps)
            also have "... \<ge> ?n (fact (Suc d)) * ((?n n * a) * (a + ?n n * a) ^ d) + 
              (\<Sum>k\<leftarrow>[0..<d]. ?n (fact k) * (?n n * a) ^ k * a) + 
              ?n (fact d) * (?n n * a) ^ d * a" (is "_ \<ge> ?z")
            proof (rule plus_right_mono)
              have "?n (d * fact d) * (a * (a + ?n n * a) ^ d)
                = ?n (fact d) * (a * (a + ?n n * a) ^ d) + 
                ?n (dd * fact d) * (a * (a + ?n n * a) ^ d)" unfolding Suc  by (simp add: field_simps)
              also have "... \<ge> ?n (fact d) * (a * (a + ?n n * a) ^ d) + 0" (is "_ \<ge> ?z")
                by (rule plus_right_mono[OF mult_ge_zero[OF of_nat_ge_zero mult_ge_zero[OF a0]]], insert ana0, auto simp: field_simps)
              also have "?z = (?n (fact d) * (a + ?n n * a) ^ d) * a"
                by (auto simp: field_simps)
              also have "... \<ge> (?n (fact d) * (?n n * a) ^ d) * a"
                by (rule times_left_mono[OF a0 times_right_mono[OF of_nat_ge_zero]], insert ananapow, auto simp: field_simps)
              finally show "?n (d * fact d) * (a * (a + ?n n * a) ^ d) \<ge> (?n (fact d) * (?n n * a) ^ d) * a" .
            qed
            also have "?z = (\<Sum>k\<leftarrow>[0..< Suc d]. ?n (fact k) * (?n n * a) ^ k * a) 
               + ?n (fact (Suc d)) * ((?n n * a) * (a + ?n n * a) ^ d)"
              by (simp add: field_simps)
            also have "... \<ge> (\<Sum>k\<leftarrow>[0..<Suc d]. ?n (fact k) * (?n n * a) ^ k * a) +
              ?n (fact (Suc d)) * (?n n * a) ^ Suc d" unfolding power_Suc
              by (rule plus_right_mono[OF times_right_mono[OF of_nat_ge_zero times_right_mono[OF na]]], insert ananapow, auto simp: field_simps)
            finally
            show "?n (fact (Suc d)) * ((1 + ?n n) * a) ^ Suc d \<ge>
              (\<Sum>k\<leftarrow>[0..<Suc d]. ?n (fact k) * (?n n * a) ^ k * a) +
              ?n (fact (Suc d)) * (?n n * a) ^ Suc d" by (simp add: field_simps)
          qed
        qed      
        also have "?z \<ge> scalar_prod ?mind ?colj" (is "_ \<ge> ?z")
        proof (rule scalar_prod_mono_right[OF mind cola col])
          show "vec_ge ?mind (vec0 d)"
            unfolding vec_ge[OF mind vec0] using a0
            by (auto simp: vec0I_def intro: ge_refl)
        next
          show "vec_ge ?mcola ?colj"
          proof (rule vec_geI[OF cola col], unfold col_def)
            fix i
            assume i: "i < d"
            hence id: "?mcola ! i = ?cola i" by auto
            have "?cola i \<ge> m ! j ! i"
            proof (cases "i < j")
              case True
              with a[OF j i] show ?thesis by auto
            next
              case False
              hence ij: "i \<ge> j" by simp
              show ?thesis
              proof (cases "i = j")
                case True
                with tri[OF j] show ?thesis by auto
              next
                case False
                with ij have ji: "j < i" by auto
                with tri[OF j] i show ?thesis by (auto simp: ge_refl)
              qed
            qed
            thus "?mcola ! i \<ge> m ! j ! i" unfolding id .
          qed
        qed
        also have "?z \<ge> scalar_prod ?rowi ?colj"
        proof (rule scalar_prod_mono_left[OF mind row col])
          show "vec_ge ?colj (vec0 d)" 
            unfolding vec_ge[OF col vec0]
            unfolding col_def vec0I_def using a[OF j] by auto
        next
          show "vec_ge ?mind ?rowi"
          proof (rule vec_geI[OF mind row])
            fix j
            assume j: "j < d"
            have idr: "?rowi ! j = ?m n ! j ! i" unfolding row_col[OF mat_pow[OF mat] i j] col_def ..
            have idl: "?mind ! j = ?ind j" using j by auto
            note IH = Suc[rule_format, OF i j]
            have "?ind j \<ge> ?m n ! j ! i" 
              by (cases "j < i", insert IH, auto simp: ge_refl)
            thus "?mind ! j \<ge> ?rowi ! j" unfolding idl idr .
          qed
        qed
        finally
        show "?fsn \<ge> ?m (Suc n) ! j ! i" unfolding id .
      qed
      with p 
      show "?p (Suc n) i j \<and> ?q (Suc n) i j" ..
    qed
  qed
qed


definition max_mat where "max_mat m \<equiv> mat_fold max m (0 :: 'a :: ordered_ab_semigroup)"

lemma max_mat: assumes m: "mat nr nc m" 
  and i: "i < nc" and j: "j < nr"
  shows "max_mat m \<ge> m ! i ! j"
proof -
  have id: "max_mat m = foldr max (concat m) 0" 
    unfolding max_mat_def mat_fold.simps vec_fold.simps
    unfolding foldr_foldr_concat ..
  from m[unfolded mat_def] i 
  have v: "\<And> v. v \<in> set m \<Longrightarrow> vec nr v" and mi: "m ! i \<in> set m" by auto
  from v[OF mi] j have mij: "m ! i ! j \<in> set (m ! i)" unfolding vec_def by auto
  from mi mij have mij: "m ! i ! j \<in> set (concat m)" by auto
  show ?thesis unfolding id
    by (rule foldr_max[OF mij])
qed

definition mat_max_list :: "'a mat list \<Rightarrow> 'a mat \<Rightarrow> ('a :: ordered_ab_semigroup) mat"
  where "mat_max_list ms init \<equiv> foldr mat_max ms init"

lemma mat_max_list: assumes init: "mat nr nc init"
  shows "\<lbrakk> \<And> m. m \<in> set ms \<Longrightarrow> mat nr nc m\<rbrakk> \<Longrightarrow> 
  mat nr nc (mat_max_list ms init) \<and> mat_ge (mat_max_list ms init) init \<and> (\<forall> m \<in> set ms. mat_ge (mat_max_list ms init) m)"
  unfolding mat_max_list_def
proof (induct ms)
  case Nil
  thus ?case using init mat_ge_refl by simp
next
  case (Cons m ms)
  let ?m = "mat nr nc"
  from Cons(2) have m: "?m m" and ms: "\<And> m. m \<in> set ms \<Longrightarrow> ?m m" by auto
  let ?mf = "foldr mat_max ms init"
  let ?mm = "mat_max m ?mf"
  note IH = Cons(1)[OF ms]
  from IH have mf: "?m ?mf" and ge_init: "mat_ge ?mf init" and ge_ms: "\<And> m. m \<in> set ms \<Longrightarrow> mat_ge ?mf m" by auto  
  from mat_max[OF m mf] have mm: "?m ?mm" .
  from mat_max_ge[OF m mf] have mm_m: "mat_ge ?mm m" and mm_mf: "mat_ge ?mm ?mf" .
  note mm_mf = mat_ge_trans[OF mm_mf _ mm mf]
  from mm_mf[OF ge_init init] have mm_init: "mat_ge ?mm init" .
  from mm_mf[OF ge_ms ms] have mm_ms: "\<And> m. m \<in> set ms \<Longrightarrow> mat_ge ?mm m" .
  from mm mm_init mm_ms mm_m
  show ?case by simp
qed

(* upper triangular matrices grow polynomially in the degree (-1) of the matrix *)
lemma upper_triangular_mat_pow_index: assumes mat: "mat d d (m :: ('a :: poly_carrier) mat)"
  and tri: "upper_triangular m"
  and ge0: "mat_ge m (mat0 d d)"
  shows "\<exists> c. c \<ge> 0 \<and> (\<forall> n > 0. \<forall> i < d. \<forall> j < d. (c * of_nat n ^ (d - Suc 0)) \<ge> (mat_pow d m n ! i ! j))"
proof -
  let ?n = "of_nat :: nat \<Rightarrow> 'a"
  let ?d = "d - Suc 0"
  obtain a where a: "a = max 1 (max_mat m)" by auto
  note main = upper_triangular_mat_pow_main[OF mat tri]  
  {
    fix i j
    assume i: "i < d" and j: "j < d"
    from ge_trans[OF _ max_mat[OF mat i j]]
    have "a \<ge> m ! i ! j" unfolding a by auto
  } note am = this
  have a1: "a \<ge> 1" unfolding a by auto
  from ge_trans[OF this one_ge_zero] have a0: "a \<ge> 0" by simp
  from mat_geE[OF ge0 mat mat0]
  have ge0: "\<And> i j. i < d \<Longrightarrow> j < d \<Longrightarrow> m ! i ! j \<ge> 0" by auto
  note main = main[OF conjI[OF ge0 am] a1]
  obtain c where c: "c = ?n (fact ?d) * (a ^ ?d)" by auto
  have c0: "c \<ge> 0"
    unfolding c
    by (rule mult_ge_zero[OF _ pow_ge_zero[OF a0]], auto)
  show ?thesis
  proof (rule exI, rule conjI[OF c0], intro allI impI)
    fix n i j :: nat
    assume i: "i < d" and j: "j < d" and n: "n > 0"
    let ?ij = "i - j"
    from i have ijd: "?ij \<le> ?d" by auto
    from main[rule_format, OF _ _ _ _ j i]
    have ge: "?n (fact (i - j)) * ((?n n * a) ^ (i - j)) \<ge> mat_pow d m n ! i ! j" ..
    have na: "?n n * a \<ge> 0" by (rule mult_ge_zero[OF _ a0], auto)
    have nfact: "?n (fact ?d) \<ge> ?n (fact ?ij)"
      using fact_mono_nat ijd by blast 
    have "?n n ^ ?d * c = ?n n ^ ?d * (?n (fact ?d) * a ^ ?d)"
      unfolding c by auto
    also have "... = ?n (fact ?d) * ((?n n) ^ ?d * a ^ ?d)" by (auto simp: field_simps)
    also have "((?n n) ^ ?d * a ^ ?d) = (?n n * a) ^ ?d"
      by (simp add: field_simps)
    also have "?n (fact ?d) * (?n n * a) ^ ?d \<ge> ?n (fact ?ij) * (?n n* a) ^ ?d" (is "_ \<ge> ?z")
      by (rule times_left_mono[OF pow_ge_zero[OF mult_ge_zero[OF _ a0]] nfact], auto)
    also have "?z \<ge> ?n (fact ?ij) * (?n n * a) ^ ?ij" (is "_ \<ge> ?z")
    proof (rule times_right_mono[OF of_nat_ge_zero pow_mono_exp[OF mult_ge_one[OF _ a1] ijd]]) 
      from n obtain nn where n: "n = Suc nn" by (cases n, auto)
      have "?n n \<ge> 1 + 0" unfolding n of_nat_Suc
        by (rule plus_right_mono, auto)
      thus "?n n \<ge> 1" by simp
    qed
    also have "?z \<ge> mat_pow d m n ! i ! j" using ge .
    finally
    show "c * (?n n ^ ?d) \<ge> mat_pow d m n ! i ! j" by (simp add: field_simps)
  qed
qed 

(* linear norm is here taken only for positive matrices, so there is no demand for abs *)
definition linear_norm :: "('a :: monoid_add)mat \<Rightarrow> 'a"
  where "linear_norm m \<equiv> listsum (concat m)"


lemma vec_ge_listsum: fixes v1 :: "('a :: ordered_semiring_0) vec"
  assumes v1: "vec nr v1" and v2: "vec nr v2" and ge: "vec_ge v1 v2"
  shows "listsum v1 \<ge> listsum v2" 
proof -
  from v1 v2 have len: "length v1 = length v2" "length v2 = nr" unfolding vec_def by auto
  show ?thesis
    by (rule listsum_ge_mono[OF len(1), unfolded len(2)], insert vec_geE[OF ge v1 v2], auto)
qed

lemma linear_norm_ge: fixes m1 :: "('a :: ordered_semiring_0) mat"
  assumes m1: "mat nr nc m1" and m2: "mat nr nc m2"
  and ge: "mat_ge m1 m2" 
  shows "linear_norm m1 \<ge> linear_norm m2"
  using assms 
proof (induct m1 arbitrary: m2 nc)
  case Nil
  thus ?case unfolding mat_def by (cases m2, auto simp: ge_refl)
next
  case (Cons v1 m1 m2v snc)
  from Cons(2) Cons(3) obtain nc v2 m2 where m2v: "m2v = v2 # m2" and m1: "mat nr nc m1" and m2: "mat nr nc m2" and 
      v1: "vec nr v1" and v2: "vec nr v2" and snc: "snc = Suc nc" unfolding mat_def by (cases m2v, force+)
  note Cons = Cons[unfolded this]
  from Cons(4) have v12': "vec_ge v1 v2" and m12ge: "mat_ge m1 m2"
    unfolding mat_ge_def mat_comp_all_def vec_ge_def by auto
  from vec_ge_listsum[OF v1 v2 v12'] have v12: "listsum v1 \<ge> listsum v2" .
  from Cons(1)[OF  m1 m2 m12ge] have m12: "linear_norm m1 \<ge> linear_norm m2" .
  from ge_trans[OF plus_left_mono[OF v12] plus_right_mono[OF m12]]
  have vm12: "linear_norm (v1 # m1) \<ge> linear_norm (v2 # m2)" unfolding linear_norm_def by simp
  thus ?case unfolding m2v .
qed

context order_pair
begin

abbreviation mat_pre_gt :: "'a mat \<Rightarrow> 'a mat \<Rightarrow> bool"
where "mat_pre_gt \<equiv> mat_pre_gtI gt"

abbreviation mat_gt :: "nat \<Rightarrow> 'a mat \<Rightarrow> 'a mat \<Rightarrow> bool"
where "mat_gt \<equiv> mat_gtI gt"

abbreviation mat_default :: "nat \<Rightarrow> 'a mat" 
where "mat_default n \<equiv> mat1I 0 default n"

lemma mat_gt_imp_mat_ge: "mat_gt sd m1 m2 \<Longrightarrow> mat_ge m1 m2"
  unfolding mat_gtI_def by auto

lemma mat_default_ge_mat0: "mat_ge (mat_default n) (mat0 n n)"
proof (rule mat_geI)
  fix i j
  assume i: "i < n" and j: "j < n"
  have zero_ij: "mat0 n n ! i ! j = 0" by (rule mat0_index[OF i j])
  have one_ij: "mat_default n ! i ! j = (if i = j then default else 0)" by (rule mat1_index[OF i j])
  show "mat_default n ! i ! j \<ge> mat0 n n ! i ! j"
    by (simp add: zero_ij one_ij ge_refl default_ge_zero)
qed auto

lemma mat_gt_compat: assumes sd_n: "sd \<le> n" and  ge: "mat_ge m1 m2" and gt: "mat_gt sd m2 m3" and wf1: "mat n n m1" and wf2: "mat n n m2" and wf3: "mat n n m3" 
  shows "mat_gt sd m1 m3"
proof -
  from gt[unfolded mat_gt[OF wf2 wf3 sd_n]] obtain i j 
    where i: "i < sd" and j: "j < sd" and gt: "m2 ! i ! j \<succ> m3 ! i ! j" and ge23: "mat_ge m2 m3" by auto 
  from mat_geE[OF ge wf1 wf2] i j sd_n have geij: "m1 ! i ! j \<ge> m2 ! i ! j" by auto
  from mat_ge_trans[OF ge ge23 wf1 wf2 wf3] have ge: "mat_ge m1 m3" .
  with compat[OF geij gt] i j show ?thesis 
    by (auto simp: mat_gt[OF wf1 wf3 sd_n])
qed

lemma mat_gt_compat2: assumes sd_n: "sd \<le> n" and gt: "mat_gt sd m1 m2" and ge: "mat_ge m2 m3" and wf1: "mat n n m1" and wf2: "mat n n m2" and wf3: "mat n n m3" 
  shows "mat_gt sd m1 m3"
proof -
  from gt[unfolded mat_gt[OF wf1 wf2 sd_n]] obtain i j 
    where i: "i < sd" and j: "j < sd" and gt: "m1 ! i ! j \<succ> m2 ! i ! j" and ge12: "mat_ge m1 m2" by auto 
  from mat_geE[OF ge wf2 wf3] i j sd_n have geij: "m2 ! i ! j \<ge> m3 ! i ! j" by auto
  from mat_ge_trans[OF ge12 ge wf1 wf2 wf3] have ge: "mat_ge m1 m3" .
  with compat2[OF gt geij] i j show ?thesis 
    by (auto simp: mat_gt[OF wf1 wf3 sd_n])
qed

lemma mat_gt_trans: assumes sd_n: "sd \<le> n" and  gt1: "mat_gt sd m1 m2" and gt2: "mat_gt sd m2 m3" and wf1: "mat n n m1" and wf2: "mat n n m2" and wf3: "mat n n m3" 
  shows "mat_gt sd m1 m3"
  by (rule mat_gt_compat[OF sd_n _ gt2 wf1 wf2 wf3], insert gt1[unfolded mat_gtI_def], auto)
end

context one_mono_ordered_semiring_1
begin

lemma vec_gt_listsum: fixes v1 :: "'a vec"
  assumes "vec nr v1" and "vec nr v2" and "vec_ge v1 v2" and "vec_pre_gtI op \<succ> (sub_vec sd v1) (sub_vec sd v2)"
  shows "listsum v1 \<succ> listsum v2" 
proof -
  note d = vec_def
  from assms
  show ?thesis
  proof (induct v1 arbitrary: v2 nr sd)
    case Nil
    thus ?case unfolding d sub_vec_def vec_pre_gtI_def by auto
  next
    case (Cons a1 v1 av2 snr ssd)
    from Cons(2) Cons(3) obtain a2 v2 nr where av2: "av2 = a2 # v2" and snr: "snr = Suc nr" and v2: "vec nr v2" unfolding d
      by (cases snr, (cases av2, auto)+)
    note Cons = Cons[unfolded av2 snr]
    from Cons(2) have v1: "vec nr v1" unfolding d by simp
    from Cons(4) have a12: "a1 \<ge> a2" and v12: "vec_ge v1 v2"
      unfolding vec_ge_def vec_comp_all_def by auto
    from Cons(5) obtain sd where "(a1 \<succ> a2) \<or> (vec_pre_gtI op \<succ> (sub_vec sd v1) (sub_vec sd v2))" 
      unfolding vec_pre_gtI_def sub_vec_def by (cases ssd, auto)
    thus ?case unfolding av2
    proof 
      assume "a1 \<succ> a2"
      from compat[OF plus_right_mono[OF vec_ge_listsum[OF v1 v2 v12]] plus_gt_left_mono[OF this]] show "listsum (a1 # v1) \<succ> listsum (a2 # v2)" by simp
    next
      assume "vec_pre_gtI op \<succ> (sub_vec sd v1) (sub_vec sd v2)"
      from Cons(1)[OF v1 v2 v12 this] have "listsum v1 \<succ> listsum v2" .
      from compat[OF plus_right_mono[OF a12] plus_gt_left_mono[OF this]]
      show "listsum (a1 # v1) \<succ> listsum (a2 # v2)" by (simp add: ac_simps)
    qed
  qed
qed

lemma linear_norm_gt_main: assumes m1: "mat nr nc m1" and m2: "mat nr nc m2"
  and ge: "mat_ge m1 m2" 
  shows "linear_norm m1 \<ge> linear_norm m2 \<and> (mat_pre_gt (sub_mat sd sdc m1) (sub_mat sd sdc m2) \<longrightarrow> linear_norm m1 \<succ> linear_norm m2)"
proof -
  note d = vec_def
  from ge m1 m2 show "(linear_norm m1 \<ge> linear_norm m2) \<and> (mat_pre_gt (sub_mat sd sdc m1) (sub_mat sd sdc m2) \<longrightarrow> linear_norm m1 \<succ> linear_norm m2)"
  proof (induct m1 arbitrary: m2 nc sdc)
    case Nil
    thus ?case unfolding mat_pre_gtI_def sub_mat_def mat_def by (cases m2, (force simp: ge_refl)+)
  next
    case (Cons v1 m1 m2v snc ssdc)
    from Cons(3) Cons(4) obtain nc v2 m2 where m2v: "m2v = v2 # m2" and m1: "mat nr nc m1" and m2: "mat nr nc m2" and v1: "vec nr v1" and v2: "vec nr v2" unfolding mat_def by (cases m2v, auto)
    note Cons = Cons[unfolded this]
    from Cons(2) have v12': "vec_ge v1 v2" and m12ge: "mat_ge m1 m2"
      unfolding mat_ge_def mat_comp_all_def vec_ge_def by auto
    note IH = Cons(1)[OF m12ge m1 m2]
    from vec_ge_listsum[OF v1 v2 v12'] have v12: "listsum v1 \<ge> listsum v2" .
    from IH have m12: "linear_norm m1 \<ge> linear_norm m2" by simp
    from ge_trans[OF plus_left_mono[OF v12] plus_right_mono[OF m12]]
    have vm12: "linear_norm (v1 # m1) \<ge> linear_norm (v2 # m2)" unfolding linear_norm_def by simp
    show ?case unfolding m2v
    proof (rule conjI[OF vm12], rule impI)
      assume gt: "mat_pre_gt (sub_mat sd ssdc (v1 # m1)) (sub_mat sd ssdc (v2 # m2))"
      from gt[unfolded mat_pre_gtI_def sub_mat_def] obtain sdc where ssd: "ssdc = Suc sdc" by (cases ssdc, auto)
      from gt ssd have "mat_pre_gt (sub_mat sd sdc m1) (sub_mat sd sdc m2) \<or> vec_pre_gtI op \<succ> (sub_vec sd v1) (sub_vec sd v2)" unfolding mat_pre_gtI_def sub_mat_def by auto
      thus "linear_norm (v1 # m1) \<succ> linear_norm (v2 # m2)" 
      proof
        assume "mat_pre_gt (sub_mat sd sdc m1) (sub_mat sd sdc m2)"
        with IH[of sdc] have "linear_norm m1 \<succ> linear_norm m2" by auto
        from compat[OF plus_right_mono[OF v12] plus_gt_left_mono[OF this]]
        show ?thesis unfolding linear_norm_def by (simp add: ac_simps)
      next
        assume "vec_pre_gtI op \<succ> (sub_vec sd v1) (sub_vec sd v2)"
        from compat[OF plus_right_mono[OF m12] plus_gt_left_mono[OF vec_gt_listsum[OF v1 v2 v12' this]]]
        show ?thesis unfolding linear_norm_def by (simp add: ac_simps)
      qed
    qed
  qed
qed

lemma linear_norm_gt: assumes m1: "mat nr nc m1" and m2: "mat nr nc m2"
  and gt: "mat_gt sd m1 m2" 
  shows "linear_norm m1 \<succ> linear_norm m2"
proof -
  from gt[unfolded mat_gtI_def] have ge: "mat_ge m1 m2"
    and gt: "mat_pre_gt (sub_mat sd sd m1) (sub_mat sd sd m2)" by auto
  from linear_norm_gt_main[OF m1 m2 ge] gt show ?thesis by auto
qed
end

lemma linear_norm_0: "linear_norm (mat0 nr nc) = (0 :: 'a :: comm_monoid_add)"
  unfolding linear_norm_def mat_fold.simps mat0I_def
proof (induct nc)
  case 0 show ?case by simp
next
  case (Suc n)
  show ?case 
    unfolding replicate.simps foldr_Cons concat.simps listsum_append Suc
    unfolding vec0I_def by (induct nr, auto)
qed

lemma linear_norm_ge_0: fixes m :: "('a :: ordered_semiring_0) mat"
  assumes m: "mat nr nc m" 
  and ge: "mat_ge m (mat0 nr nc)" 
  shows "linear_norm m \<ge> 0"
  using linear_norm_ge[OF m mat0 ge]
  unfolding linear_norm_0 .

lemma linear_norm_plus: "mat nr nc m1 \<Longrightarrow> mat nr nc (m2 :: ('a :: comm_monoid_add)mat) \<Longrightarrow> linear_norm (mat_plus m1 m2) = linear_norm m1 + linear_norm m2" 
  unfolding linear_norm_def mat_fold.simps 
proof (induct nc arbitrary: m1 m2)
  case 0 thus ?case unfolding mat_def mat_plusI_def by simp
next
  case (Suc nc vm1 vm2)
  from Suc(2) obtain v1 m1 where vm1: "vm1 = v1 # m1" and m1: "mat nr nc m1" and v1: "vec nr v1" unfolding mat_def by (cases vm1, auto)
  from Suc(3) obtain v2 m2 where vm2: "vm2 = v2 # m2" and m2: "mat nr nc m2" and v2: "vec nr v2" unfolding mat_def by (cases vm2, auto)
  note IH = Suc(1)[OF m1 m2]
  have "listsum (concat (mat_plus vm1 vm2)) = listsum (vec_plus v1 v2) + listsum (concat (mat_plus m1 m2))" unfolding vm1 vm2 mat_plusI_def by simp
  also have "listsum (vec_plus v1 v2) = listsum v1 + listsum v2"
    using v1 v2
  proof (induct nr arbitrary: v1 v2)
    case 0
    thus ?case unfolding vec_def vec_plusI_def by auto
  next
    case (Suc nr vm1 vm2)
    from Suc(2) obtain v1 m1 where vm1: "vm1 = v1 # m1" and m1: "vec nr m1" unfolding vec_def by (cases vm1, auto)
    from Suc(3) obtain v2 m2 where vm2: "vm2 = v2 # m2" and m2: "vec nr m2" unfolding vec_def by (cases vm2, auto)
    from Suc(1)[OF m1 m2] show ?case unfolding vm1 vm2
      unfolding vec_plusI_def by (auto simp: ac_simps)
  qed
  finally show ?case unfolding IH unfolding vm1 vm2 
    by (simp add: ac_simps)
qed    

lemma linear_norm_index: fixes m :: "('a :: ordered_semiring_1) mat"   
  assumes bc: "bc \<ge> 0"
  shows "mat nr nc m \<Longrightarrow> \<lbrakk>\<And> i j. i < nc \<Longrightarrow> j < nr \<Longrightarrow> bc \<ge> m ! i ! j\<rbrakk> \<Longrightarrow> of_nat nr * of_nat nc * bc \<ge> linear_norm m"
proof (induct nc arbitrary: m)
  case 0 thus ?case using bc unfolding mat_def linear_norm_def 
    by (simp add: ge_refl)
next
  case (Suc nc vm)
  from Suc(2) obtain v m where vm: "vm = v # m" 
    and m: "mat nr nc m" and v: "vec nr v" unfolding mat_def  by (cases vm, auto)
  note Suc = Suc[unfolded vm]
  from Suc(3)[of 0] have bcv: "\<And> j. j < nr \<Longrightarrow> bc \<ge> v ! j" by simp
  {
    fix i 
    assume "i < nc" 
    with Suc(3)[of "Suc i"] have "\<And> j. j < nr \<Longrightarrow> bc \<ge> m ! i ! j" by auto
  } note bcm = this
  from Suc(1)[OF m bcm] have IH: "of_nat nr * of_nat nc * bc \<ge> linear_norm m" by auto
  from v bcv have v: "of_nat nr * bc \<ge> listsum v"
  proof (induct nr arbitrary: v)
    case 0
    thus ?case unfolding vec_def using bc by (auto simp: ge_refl)
  next
    case (Suc nr av)
    from Suc(2) obtain a v where av: "av = a # v" 
      and v: "vec nr v" unfolding vec_def  by (cases av, auto)
    note Suc = Suc[unfolded av]
    from Suc(3)[of 0] have a: "bc \<ge> a" by auto
    {
      fix i
      assume "i < nr"
      with Suc(3)[of "Suc i"] have "bc \<ge> v ! i" by auto 
    } note bcv = this
    from Suc(1)[OF v bcv] have IH: "of_nat nr * bc \<ge> listsum v" by auto
    have "of_nat (Suc nr) * bc = bc + of_nat nr * bc" by (simp add: field_simps)
    also have "... \<ge> a + listsum v"
      by (rule ge_trans[OF plus_left_mono[OF a] plus_right_mono[OF IH]])
    finally show ?case unfolding av by simp
  qed
  have "of_nat nr * of_nat (Suc nc) * bc = of_nat nr * bc + of_nat nr * of_nat nc * bc" by (simp add: field_simps)
  also have "... \<ge> listsum v + linear_norm m"
    by (rule ge_trans[OF plus_left_mono[OF v] plus_right_mono[OF IH]])
  finally show ?case unfolding vm linear_norm_def by auto
qed

lemma linear_norm_submultiplicative: fixes m1 :: "('a :: ordered_semiring_1) mat"
  shows "mat_ge m1 (mat0 nr n) \<Longrightarrow> mat_ge m2 (mat0 n nc) \<Longrightarrow> mat nr n m1 \<Longrightarrow> mat n nc m2 \<Longrightarrow>
  linear_norm m1 * linear_norm m2 \<ge> linear_norm (mat_mult nr m1 m2)" 
proof (induct n arbitrary: m1 m2)
  case 0
  have m2: "\<forall> x \<in> set m2. x = [] \<Longrightarrow> m2 = replicate (length m2) []"
    by (induct m2, auto)
  with 0(3) 0(4) have m1: "m1 = []" and m2: "m2 = replicate nc []" unfolding mat_def  
    by (auto simp: vec_def)
  have "linear_norm (mat_mult nr m1 m2) = listsum (concat (replicate nc (replicate nr (0::'a))))" unfolding m1 m2
    by (simp add: linear_norm_def mat_multI_def matT_vec_multI_def scalar_prodI_def) 
  also have "... = 0"
  proof (induct nc)
    case (Suc nc)
    show ?case by (simp add: Suc, induct nr, auto)
  qed simp
  finally have id: "linear_norm (mat_mult nr m1 m2) = 0" .
  show ?case unfolding id unfolding m1 m2 linear_norm_def by (simp add: ge_refl)
next
  case (Suc n m1 m2)
  let ?mgen = "\<lambda> nr nc m. [ m ! i ! j. i \<leftarrow> [0 ..< nc], j \<leftarrow> [0 ..< nr] ]"
  let ?mn1 = "?mgen nr n"
  let ?msn1 = "?mgen nr (Suc n)"
  let ?mn2 = "?mgen n nc"
  let ?msn2 = "?mgen (Suc n) nc"
  note m1 = Suc(4)
  note m2 = Suc(5)
  note m10 = Suc(2)
  note m20 = Suc(3)
  note IH = Suc(1)
  let ?gen = "\<lambda> (nr :: nat) nc (f :: nat \<Rightarrow> nat \<Rightarrow> 'a). map (\<lambda>i. map (f i) [0..<nr]) [0..<nc]"
  let ?v = "linear_norm"
  let ?ii = "\<lambda> m nr nc. ?gen nr nc (\<lambda> i j. m ! i ! j)"
  obtain ii1 where ii1: "ii1 = ?ii m1 nr n" by auto
  obtain ii2 where ii2: "ii2 = ?ii m2 n nc" by auto
  let ?midx = "\<lambda> m nr nc. ?gen nr nc (\<lambda> i j. m ! i ! j)" 
  obtain nn where nn: "nn = Suc n" by auto
  note nns = nn[symmetric]
  {
    fix nr :: nat and nc :: nat and f :: "nat \<Rightarrow> nat \<Rightarrow> 'a" 
    have "mat nr nc (?gen nr nc f)"
      unfolding mat_def by (auto simp: vec_def)    
  } note gen = this
  {
    fix f and g  :: "nat \<Rightarrow> 'a" and idx
    have "listsum (concat (map (\<lambda> i. f i @ [g i]) idx)) = listsum (concat (map f idx)) + listsum (map g idx)" by (induct idx, auto simp: ac_simps)
  } note listsum_concat_singleton = this
  {
    fix m :: "'a mat" and nr nc
    assume m: "mat nr nc m"
    have "m = ?midx m nr nc" 
      by (rule mat_eqI[OF m gen], auto)
  } note mat_idx = this
  let ?mni = "[ m1 ! n ! i . i \<leftarrow> [0..<nr]]"
  let ?min = "[ m2 ! i ! n . i \<leftarrow> [0..<nc]]"
  let ?lmni = "listsum ?mni"
  let ?lmin = "listsum ?min"
  {    
    from concat_mat[OF m1]
    have "concat m1 = concat (?midx m1 nr (Suc n))" by simp
    hence "?v m1 = listsum (concat (?midx m1 nr (Suc n)))" unfolding linear_norm_def by simp
    also have "... = listsum (concat (?midx m1 nr n)) + listsum ?mni"
      by simp
    also have "listsum (concat (?midx m1 nr n)) = linear_norm ii1"
      unfolding ii1 linear_norm_def ..
    finally have "linear_norm m1 = linear_norm ii1 + ?lmni" .
  } note vm1 = this
  {    
    from concat_mat[OF m2]
    have "concat m2 = concat (?midx m2 (Suc n) nc)" by simp
    hence "?v m2 = listsum (concat (?midx m2 (Suc n) nc))" unfolding linear_norm_def by simp
    also have "... = listsum (concat (map (\<lambda>i. map (op ! (m2 ! i)) [0..<n] @ [m2 ! i ! n]) [0..<nc]))" by simp
    also have "... = listsum (concat (?midx m2 n nc)) + ?lmin" unfolding listsum_concat_singleton ..
    also have "listsum (concat (?midx m2 n nc)) = linear_norm ii2"
      unfolding ii2 linear_norm_def ..
    finally have "linear_norm m2 = linear_norm ii2 + ?lmin" .
  } note vm2 = this
  have mat_ii1: "mat nr n ii1" unfolding ii1 by (rule gen)
  have mat_ii2: "mat n nc ii2" unfolding ii2 by (rule gen)
  {
    fix i j
    assume i: "i < n" and j: "j < nr"
    have "ii1 ! i ! j = m1 ! i ! j" using i j unfolding ii1 by simp
  } note ii1_idx = this
  {
    fix i j
    assume i: "i < nc" and j: "j < n"
    have "ii2 ! i ! j = m2 ! i ! j" using i j unfolding ii2 by simp
  } note ii2_idx = this
  {
    fix m :: "'a mat" and nr nc
    assume m: "mat nr nc m" and ge: "mat_ge m (mat0 nr nc)"
    from mat_geE[OF ge m]
    have ge0: "\<And> i j. i < nc \<Longrightarrow> j < nr \<Longrightarrow> m ! i ! j \<ge> 0" by auto
  } note mat_ge = this
  have ii10: "mat_ge ii1 (mat0 nr n)"
    by (rule mat_geI[OF mat_ii1], insert ii1_idx mat_ge[OF m1 m10], auto)
  have ii20: "mat_ge ii2 (mat0 n nc)"
    by (rule mat_geI[OF mat_ii2], insert ii2_idx mat_ge[OF m2 m20], auto)
  let ?mult = "mat_mult nr m1 m2"
  have m12: "mat nr nc ?mult" by (rule mat_mult[OF m1 m2])
  {
    fix i
    assume i: "i < nc"
    have "col m2 i = col ii2 i @ [m2 ! i ! n]"
      unfolding col_index[OF m2 i]
      unfolding col_index[OF mat_ii2 i]
      using ii2_idx[OF i]
      by auto
  } note col_n = this
  {
    fix i
    assume i: "i < nr"
    have "row m1 i = row ii1 i @ [m1 ! n ! i]"
      unfolding row_index[OF m1 i]
      unfolding row_index[OF mat_ii1 i]
      using ii1_idx[OF _ i]
      by auto
  } note row_n = this
  let ?scalar = "\<lambda> i j. scalar_prod (row m1 j) (col m2 i)"
  let ?scalar' = "\<lambda> i j. scalar_prod (row ii1 j) (col ii2 i) + 
    m1 ! n ! j * m2 ! i ! n" 
  obtain scalar' where scalar': "scalar' = ?scalar'" by auto
  obtain scalar where scalar: "scalar = ?scalar" by auto
  let ?mult' = "?gen nr nc scalar'"
  let ?vmii = "?v (mat_mult nr ii1 ii2)"
  let ?rii = "listsum [m1 ! n ! j * m2 ! i ! n . i \<leftarrow> [0..<nc], j \<leftarrow> [0..<nr]]"
  {
    have mult_mult': "?mult = ?mult'"
    proof (rule mat_eqI[OF m12 gen])
      fix i j
      assume i: "i < nc" and j: "j < nr"
      have "?mult ! i ! j = scalar i j"
        unfolding mat_mult_index[OF m1 m2 j i] scalar ..
      also have "... = scalar' i j"
      proof -
        from row[OF mat_ii1 j] col[OF mat_ii2 i]
        have len: "length (row (ii1) j) = length (col (ii2) i)" "length [m1 ! n ! j] = length [m2 ! i ! n]" unfolding vec_def by auto
        show "scalar i j = scalar' i j" 
          unfolding scalar scalar' row_n[OF j] col_n[OF i]
          unfolding scalar_prod
          unfolding zip_append[OF len(1)] by simp
      qed
      finally 
      show "?mult ! i ! j = ?mult' ! i ! j"
         using i j by simp
    qed
    hence "?v ?mult = ?v ?mult'" by simp
    also have "... = listsum (concat (map (\<lambda>i. map (scalar' i) [0..<nr]) [0 ..< nc]))"
      unfolding linear_norm_def ..
    also have "... =
      listsum (concat (map (\<lambda>i. map (\<lambda>j. scalar_prod (row (ii1) j) (col (ii2) i))
                  [0..<nr])
         [0..<nc])) +
    ?rii" (is "_ = ?zwi + _") unfolding scalar' unfolding listsum_double_concat  ..
    also have "?zwi = ?vmii"
      unfolding linear_norm_def
    proof (rule arg_cong[where f = "\<lambda> x. listsum (concat x)"], 
      rule mat_eqI[OF gen mat_mult[OF mat_ii1 mat_ii2]])
      fix i j
      assume i: "i < nc" and j: "j < nr"
      let ?sc = "(\<lambda> i j. scalar_prod (row (ii1) j) (col (ii2) i))"
      have "?gen nr nc ?sc ! i ! j = ?sc i j" using i j by simp
      also have "... = mat_mult nr (ii1) (ii2) ! i ! j"
        by (rule mat_mult_index[symmetric, OF mat_ii1 mat_ii2 j i])
      finally show "?gen nr nc ?sc ! i ! j = mat_mult nr (ii1) (ii2) ! i ! j" .
    qed
    finally have "?v ?mult = ?vmii + ?rii" .
  } note vmult = this
  have "?v m1 * ?v m2 = ?v (ii1) * ?v (ii2) + (?v (ii1) * ?lmin + ?lmni * ?v (ii2) + ?lmni * ?lmin)"
    unfolding vm1 vm2 by (simp add: field_simps)
  also have "... \<ge> ?vmii + (?v (ii1) * ?lmin + ?lmni * ?v (ii2) + ?lmni * ?lmin)" (is "_ \<ge> ?z")
    by (rule plus_left_mono[OF IH[OF ii10 ii20 mat_ii1 mat_ii2]])
  also have "?z \<ge> ?vmii + ?rii" (is "_ \<ge> ?z")
  proof (rule plus_right_mono)
    from linear_norm_ge_0[OF mat_ii1 ii10] have ii10: "linear_norm ii1 \<ge> 0" .
    from linear_norm_ge_0[OF mat_ii2 ii20] have ii20: "linear_norm ii2 \<ge> 0" .
    note m10 = mat_ge[OF m1 m10]
    note m20 = mat_ge[OF m2 m20]
    have lmin0: "?lmin \<ge> 0"
      by (rule listsum_ge_0_nth, insert m20, auto)
    have lmni0: "?lmni \<ge> 0"
      by (rule listsum_ge_0_nth, insert m10, auto)
    have p10: "?v (ii1) * ?lmin \<ge> 0"
      by (rule mult_ge_zero[OF ii10 lmin0])
    have p20: "?lmni * ?v (ii2) \<ge> 0"
      by (rule mult_ge_zero[OF lmni0 ii20])
    from plus_right_mono[OF ge_trans[OF plus_left_mono[OF p10] plus_right_mono[OF p20]], of "?lmni * ?lmin"]
    have ge: "?v (ii1) * ?lmin + ?lmni * ?v (ii2) + ?lmni * ?lmin \<ge> ?lmni * ?lmin"
      by (simp add: ac_simps)
    have id: "?lmni * ?lmin = ?rii" 
    proof (induct nc)
      case 0
      show ?case by simp
    next
      case (Suc nc)
      let ?nr = "listsum (map (op ! (m1 ! n)) [0..<nr])"
      let ?nrr = "listsum (concat (map (\<lambda>i. map (\<lambda>j. m1 ! n ! j * m2 ! i ! n) [0..<nr]) [0..<nc]))"
      have "?nr * (\<Sum>i\<leftarrow>[0..<Suc nc]. m2 ! i ! n)
        = ?nr * ((\<Sum>i\<leftarrow>[0..<nc]. m2 ! i ! n) + m2 ! nc ! n)"
        by simp
      also have "... = ?nr * (\<Sum>i\<leftarrow>[0..<nc]. m2 ! i ! n) + ?nr * m2 ! nc ! n" 
        by (simp add: field_simps)
      also have "... = ?nrr + ?nr * m2 ! nc ! n" unfolding Suc ..
      also have "?nr * m2 ! nc ! n = (\<Sum>j\<leftarrow>[0..<nr]. m1 ! n ! j * m2 ! nc ! n)" 
        by (induct nr, auto simp: field_simps)
      also have "?nrr + ... = listsum (concat (map (\<lambda>i. map (\<lambda>j. m1 ! n ! j * m2 ! i ! n) [0..<nr]) [0..<Suc nc]))"
        by simp
      finally
      show ?case .
    qed
    show "?v (ii1) * ?lmin + ?lmni * ?v (ii2) + ?lmni * ?lmin \<ge> ?rii" 
      using ge unfolding id .
  qed
  also have "?z = ?v ?mult" unfolding vmult ..
  finally show ?case .
qed


lemma linear_norm_mult_left_ex: assumes m: "mat n n (m :: ('a :: large_ordered_semiring_1) mat)" 
  and m0: "mat_ge m (mat0 n n)" (is "mat_ge m ?m0")
  shows "\<exists> c. (\<forall> m'. mat n n m' \<longrightarrow> mat_ge m' (mat0 n n) \<longrightarrow> linear_norm m' * (of_nat c) \<ge> linear_norm (mat_mult n m' m))"
proof -
  let ?c = "linear_norm m"
  from linear_norm_ge_0[OF m m0] have c0: "?c \<ge> 0" .
  from ex_large_of_nat[of ?c] obtain c where c: "of_nat c \<ge> ?c" by auto
  show ?thesis
  proof (rule exI[of _ c], intro allI impI)
    fix m' :: "'a mat"
    assume m': "mat n n m'" and m'0: "mat_ge m' (mat0 n n)"
    let ?m' = "linear_norm m'"
    have "?m' * of_nat c \<ge> ?m' * ?c" (is "_ \<ge> ?z")
      by (rule times_right_mono[OF linear_norm_ge_0[OF m' m'0] c])
    also have "?z \<ge> linear_norm (mat_mult n m' m)"
      by (rule linear_norm_submultiplicative[OF m'0 m0 m' m])
    finally show "linear_norm m' * of_nat c \<ge> linear_norm (mat_mult n m' m)" .
  qed
qed

lemma linear_norm_mult_right_ex: assumes m: "mat n n (m :: ('a :: large_ordered_semiring_1) mat)" 
  and m0: "mat_ge m (mat0 n n)" (is "mat_ge m ?m0")
  shows "\<exists> c. (\<forall> m'. mat n n m' \<longrightarrow> mat_ge m' (mat0 n n) \<longrightarrow> linear_norm m' * (of_nat c) \<ge> linear_norm (mat_mult n m m'))"
proof -
  let ?c = "linear_norm m"
  from linear_norm_ge_0[OF m m0] have c0: "?c \<ge> 0" .
  from ex_large_of_nat[of ?c] obtain c where c: "of_nat c \<ge> ?c" by auto
  show ?thesis
  proof (rule exI[of _ c], intro allI impI)
    fix m' :: "'a mat"
    assume m': "mat n n m'" and m'0: "mat_ge m' (mat0 n n)"
    let ?m' = "linear_norm m'"
    have "?m' * of_nat c \<ge> ?m' * ?c" (is "_ \<ge> ?z")
      by (rule times_right_mono[OF linear_norm_ge_0[OF m' m'0] c])
    also have "?z = ?c * ?m'" by (simp add: ac_simps)
    also have "... \<ge> linear_norm (mat_mult n m m')"
      by (rule linear_norm_submultiplicative[OF m0 m'0 m m'])
    finally show "linear_norm m' * of_nat c \<ge> linear_norm (mat_mult n m m')" .
  qed
qed



lemma upper_triangular_mat_pow_value: assumes mat: "mat d d (m :: ('a :: poly_carrier) mat)"
  and tri: "upper_triangular m"
  and ge0: "mat_ge m (mat0 d d)"
  shows "\<exists> c. c \<ge> 0 \<and> (\<forall> n > 0. (c * of_nat (n ^ (d - Suc 0))) \<ge> (linear_norm (mat_pow d m n)))"
proof -
  from upper_triangular_mat_pow_index[OF mat tri ge0]
  obtain c where "c \<ge> (0::'a) \<and>
         (\<forall>n>0. \<forall>i<d. \<forall>j<d. c * of_nat n ^ (d - Suc 0) \<ge>
                            mat_pow d m n ! i ! j)" ..
  hence c: "(c :: 'a) \<ge> 0" and ge: "\<And> n i j. n > 0 \<Longrightarrow> i < d \<Longrightarrow> j < d \<Longrightarrow> c * of_nat n ^ (d - Suc 0) \<ge> mat_pow d m n ! i ! j" by auto
  let ?c = "of_nat d * of_nat d * c"
  from c have c0: "?c \<ge> 0" by auto
  show ?thesis
  proof (rule exI, rule conjI[OF c0], intro allI impI)
    fix n :: nat
    assume n: "0 < n"
    hence "?c * of_nat n ^ (d - Suc 0) \<ge> linear_norm (mat_pow d m n)"
      using linear_norm_index[OF _ mat_pow[OF mat] ge[OF n]] c 
      by (auto simp: field_simps)
    thus "?c * of_nat (n ^ (d - Suc 0)) \<ge> linear_norm (mat_pow d m n)"
      unfolding of_nat_power .
  qed
qed

context one_mono_ordered_semiring_1
begin 

lemma mat_plus_gt_left_mono: assumes sd_n: "sd \<le> n" and gt: "mat_gt sd m1 m2" and ge: "mat_ge m3 m4" and wf1: "mat n n m1" and wf2: "mat n n m2" and wf3: "mat n n m3" and wf4: "mat n n m4"
  shows "mat_gt sd (mat_plus m1 m3) (mat_plus m2 m4)"
proof -
  note wf = wf1 wf2 wf3 wf4
  let ?m13 = "mat_plus m1 m3"
  let ?m23 = "mat_plus m2 m3"
  let ?m32 = "mat_plus m3 m2"
  let ?m24 = "mat_plus m2 m4"
  let ?m42 = "mat_plus m4 m2"
  have wf13: "mat n n ?m13" and wf24: "mat n n ?m24" using wf by auto
  from gt[simplified mat_gt[OF wf1 wf2 sd_n]] obtain i j where
    i: "i < sd" and j: "j < sd" and gt: "m1 ! i ! j \<succ> m2 ! i ! j" and ge12: "mat_ge m1 m2" by auto
  with sd_n have ni: "i < n" and nj: "j < n" by auto
  from mat_plus_left_mono[OF ge12 wf1 wf2 wf3] have one: "mat_ge ?m13 ?m23" .
  from mat_plus_left_mono[OF ge wf3 wf4 wf2] have "mat_ge ?m32 ?m42" .
  hence two: "mat_ge ?m23 ?m24" by (simp add: mat_plus_comm[of m2 m3] mat_plus_comm[of m2 m4])
  have matge: "mat_ge ?m13 ?m24" by (rule mat_ge_trans[OF one two], insert wf, auto)
  from i j sd_n mat_geE[OF ge] wf have ge: "m3 ! i ! j \<ge> m4 ! i ! j" by auto
  from compat2[OF plus_gt_left_mono[OF gt] plus_right_mono[OF ge]] mat_plus_index[OF wf1 wf3 ni nj] mat_plus_index[OF wf2 wf4 ni nj]      
  have gt: "?m13 ! i ! j \<succ> ?m24 ! i ! j" by simp
  from i j matge gt  show ?thesis 
    by (auto simp: mat_gt[OF wf13 wf24 sd_n] matge)
qed

lemma mat_default_gt_mat0: assumes sd_pos: "sd > 0" and sd_n: "sd \<le> n"
  shows "mat_gt sd (mat_default n) (mat0 n n)"
proof -
  from assms have n: "n > 0" by auto
  show ?thesis 
    by (simp only: mat_gt[OF mat1 mat0 sd_n] mat_default_ge_mat0, rule conjI[OF TrueI],
      (rule exI[of _ 0], simp only: sd_pos, rule conjI[OF TrueI])+, simp add: mat1_index[OF n n] mat0_index[OF n n] default_gt_zero)
qed
end

text {* three easy lemmas to go from pairs of numbers to numbers  *}

lemma mul_div_eq: assumes "c < b" shows "(a * b + c) div b = (a :: nat)" 
proof -
  from assms have b: "b \<noteq> 0" by simp
  have "(a * b + c) div b = (c + a * b) div b" by presburger
  also have "\<dots> = c div b + a" using b by simp
  also have "\<dots> = a" using assms by simp
  finally show ?thesis .
qed

lemma smaller_product: assumes i: "i < c" and j: "j < b" shows "i*b + j < c * (b :: nat)" 
proof -
  from i obtain cc where cc: "c = Suc cc" by (cases c, auto)
  with i have i: "i \<le> cc" by auto
  hence "i * b + j \<le> cc * b + j" by auto
  also have "\<dots> < cc * b + b" using j by auto
  also have "\<dots> = Suc cc * b" by auto
  also have "\<dots> = c * b" using cc by auto
  finally show ?thesis .
qed

lemma all_all_into_all: "(\<forall> i < c :: nat. \<forall> j < b. f i j) = (\<forall> ij < c * b. f (ij div b) (ij mod b))" (is "?l = ?r")
proof (cases "b = 0")
  case False
  hence b_pos: "b > 0" by simp
  show ?thesis
  proof
    assume ?l
    show ?r
    proof (intro allI impI)
      fix ij
      assume ij: "ij < c * b"
      from mod_less_divisor[OF b_pos] have mod: "ij mod b < b" .
      have div: "ij div b < c" 
      proof (rule ccontr)
        assume not: "\<not> ij div b < c" 
        have "ij div b * b + ij mod b = ij" by simp
        also have "\<dots> < c * b" by (rule ij) 
        also have "\<dots> \<le> (ij div b) * b" using not by auto
        finally show False by arith
      qed
      from mod div `?l` show "f (ij div b) (ij mod b)" by auto
    qed
  next
    assume ?r
    show ?l
    proof (intro allI impI)
      fix i j
      assume i: "i < c" and j: "j < b"
      let ?ij = "i * b + j"
      from smaller_product[OF i j] spec[OF `?r`, of ?ij] have "f (?ij div b) (?ij mod b)" by auto
      thus "f i j" using mul_div_eq[OF j] j by auto
    qed
  qed
qed simp


context SN_one_mono_ordered_semiring_1
begin

abbreviation mat_ns :: "'a mat \<Rightarrow> nat \<Rightarrow> 'a mat \<Rightarrow> bool" ("(_ \<ge>m _ _)" [51,51,51] 50) 
 where "m1 \<ge>m n m2 \<equiv> (mat n n m1 \<and> mat n n m2 \<and> mat_ge m1 m2)"

abbreviation mat_s :: "'a mat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a mat \<Rightarrow> bool" ("(_ \<succ>m _ _ _)" [51,51,51,51] 50)
 where "m1 \<succ>m n sd m2 \<equiv> (mat n n m1 \<and> mat n n m2 \<and> mat_ge m2 (mat0 n n) \<and> mat_gt sd m1 m2)"

lemma mat_sn: assumes sd_n: "sd \<le> n" shows "SN {(m1,m2) . m1 \<succ>m n sd m2}"
unfolding SN_defs
proof clarify
  fix f 
  assume "\<forall> i. (f i, f (Suc i)) \<in> {(m1,m2). m1 \<succ>m n sd m2}"
  hence ass: "\<And> i. (f i, f (Suc i)) \<in> {(m1,m2). m1 \<succ>m n sd m2}" by blast
  hence len_n: "\<And> i. length (f i) = n" by (auto simp: mat_def) 
  let ?rel = "{(x,y). y \<ge> 0 \<and> x \<succ> y}"
  let ?gt = "\<lambda> k i j. f k ! i ! j \<succ> f (Suc k) ! i ! j"
  let ?ge = "\<lambda> k i j. f k ! i ! j \<ge> f (Suc k) ! i ! j"
  let ?gez = "\<lambda> k i j. f (Suc k) ! i ! j \<ge> 0"
  let ?f = "\<lambda> k ij. f k ! (ij div sd) ! (ij mod sd)"
  let ?ij = "\<lambda> i j. (i * sd + j)"
  let ?fgt = "\<lambda> k ij. (?f k ij,?f (Suc k) ij) \<in> ?rel"
  let ?fpgt = "\<lambda> k ij. ?f k ij \<succ> ?f (Suc k) ij"
  let ?fge = "\<lambda> k ij. ?f k ij \<ge> ?f (Suc k) ij"
  let ?sd = "sd * sd"
  have all: "\<And> k. (\<exists> ij < ?sd. ?fgt k ij) \<and> (\<forall> ij < ?sd. ?fge k ij)"
  proof -
    fix k
    from ass[of k] have wf: "mat n n (f k)" and wf1: "mat n n (f (Suc k))" and gt: "mat_gt sd (f k) (f (Suc k))" and
      gez: "mat_ge (f (Suc k)) (mat0 n n)" by auto
    from gt[simplified mat_gt[OF wf wf1 sd_n]] obtain i j where i: "i < sd" and j: "j < sd" and ge: "mat_ge (f k) (f (Suc k))"
      and gt: "?gt k i j" by auto
    hence pgt: "?fpgt k (?ij i j)" by (auto simp: mul_div_eq[OF j] j)
    have ij: "?ij i j < ?sd" using i j smaller_product by auto
    from mat_geE[OF ge wf wf1] sd_n have "\<forall> i < sd. \<forall> j < sd. ?ge k i j" by auto
    hence ge: "\<forall> ij < ?sd. ?fge k ij" by (simp add: all_all_into_all)      
    from mat_geE[OF gez wf1 mat0] sd_n have "\<forall> i < sd. \<forall> j < sd. ?gez k i j" by auto
    hence "?gez k i j" using i j by simp
    hence "?f (Suc k) (?ij i j) \<ge> 0" by (auto simp: mul_div_eq[OF j] j)
    with pgt have gt: "?fgt k (?ij i j)" by auto 
    from gt ge ij show "(\<exists> ij < ?sd. ?fgt k ij) \<and> (\<forall> ij < ?sd. ?fge k ij)" by auto
  qed
  obtain f sd where f: "f = ?f" and "sd = ?sd" by auto
  with all have ex: "\<And> k. (\<exists> i < sd. (f k i, f (Suc k) i) \<in> ?rel)" and all: "\<And> k.(\<forall> i < sd. f k i \<ge> f (Suc k) i)" by auto
  let ?g = "\<lambda> k i. (f k i, f (Suc k) i) \<in> ?rel"
  from ex have g: "\<forall> k. \<exists> i < sd. ?g k i" by auto
  from inf_pigeonhole_principle[OF g] obtain i where i: "i < sd" and inf: "\<forall> k. \<exists> k' \<ge> k. ?g k' i" by auto
  let ?h = "\<lambda> k. (f k i)"
  let ?nRel = "{(x,y) | x y :: 'a. x \<ge> y}"
  from all i have all: "\<forall> k. (?h k, ?h (Suc k)) \<in> ?nRel \<union> ?rel" by auto
  from SN have SNe: "SN_on ?rel {?h 0}" unfolding SN_defs by auto
  have comp: "?nRel O ?rel \<subseteq> ?rel" using compat by auto
  from non_strict_ending[OF all comp] SNe
  obtain j where "\<forall> k \<ge> j. (?h k, ?h (Suc k)) \<in> ?nRel - ?rel" by auto
  with inf  show False by blast
qed
end


context SN_strict_mono_ordered_semiring_1
begin 

abbreviation mat_mono :: "nat \<Rightarrow> 'a mat \<Rightarrow> bool"
where "mat_mono \<equiv> mat_monoI mono"

lemma mat_mono: assumes sd_n: "sd \<le> n" and wf1: "mat n n m1" and wf2: "mat n n m2" and wf3: "mat n n m3" and gt: "mat_gt sd m2 m3" and ge: "mat_ge m1 (mat0 n n)" and mmono: "mat_mono sd m1"
  shows "mat_gt sd (mat_mult n m1 m2) (mat_mult n m1 m3)"
proof -
  let ?m12 = "mat_mult n m1 m2"
  let ?m13 = "mat_mult n m1 m3"
  from wf1 wf2 have wf12: "mat n n ?m12" by (rule mat_mult)
  from wf1 wf3 have wf13: "mat n n ?m13" by (rule mat_mult)
  from mat_mult_right_mono[OF wf1 wf2 wf3 ge] gt have gem: "mat_ge ?m12 ?m13" unfolding mat_gtI_def by auto
  from gt obtain i j where i: "i < sd" and j: "j < sd" and gt: "m2 ! i ! j \<succ> m3 ! i ! j" and geq: "mat_ge m2 m3"
    by (auto simp: mat_gt[OF wf2 wf3 sd_n])
  from mmono mat_mono[OF wf1 sd_n] j obtain k where k: "k < sd" and monojk: "mono (m1 ! j ! k)" by auto
  from i j k sd_n have ni: "i < n" and nj: "j < n" and nk: "k < n" by auto
  show ?thesis 
  proof (simp only: mat_gt[OF wf12 wf13 sd_n], simp only: gem, rule conjI[OF TrueI],
      rule exI[of _ i], simp only: i, rule conjI[OF TrueI],
      rule exI[of _ k], simp only: k, rule conjI[OF TrueI])
    let ?r = "\<lambda> n. map (\<lambda> j. m1 ! j ! k) [0 ..< n]"
    from row[OF wf1 nk] have wfr: "length (row m1 k) = n" unfolding vec_def by auto
    from col[OF wf2 ni] have wfc2: "length (col m2 i) = n" unfolding vec_def by auto
    from col[OF wf3 ni] have wfc3: "length (col m3 i) = n" unfolding vec_def by auto
    have "row m1 k = map (\<lambda> i. row m1 k ! i) [0 ..< length (row m1 k)]" by (rule map_nth[symmetric])
    also have "\<dots> = map (\<lambda> i. row m1 k !  i) [0 ..< n]" by (simp add: wfr)
    also have "\<dots> = ?r n" using row_col[OF wf1 nk, unfolded col_def]
      by auto
    finally have r: "row m1 k = ?r n" .
    let ?c2 = "\<lambda> n. map (\<lambda> j. m2 ! i ! j) [0 ..< n]"
    have c2: "col m2 i = ?c2 n" unfolding wfc2[symmetric] col_def by (simp add: map_nth)
    let ?c3 = "\<lambda> n. map (\<lambda> j. m3 ! i ! j) [0 ..< n]"
    have c3: "col m3 i = ?c3 n" unfolding wfc3[symmetric] col_def by (simp add: map_nth)
    from mat_mult_index[OF wf1 wf2 nk ni]
    have s12: "?m12 ! i ! k = scalar_prod (?r n) (?c2 n)" by (simp add: r c2)
    from mat_mult_index[OF wf1 wf3 nk ni]
    have s13: "?m13 ! i ! k = scalar_prod (?r n) (?c3 n)" by (simp add: r c3)
    have r0: "\<forall> j < n. ?r n ! j \<ge> 0" 
    proof (intro impI allI)
      fix j
      assume "j < n"
      with mat_geE[OF ge wf1 mat0] nk
      show "?r n ! j \<ge> 0" by simp
    qed
    have c2c3: "\<forall> j < n. ?c2 n ! j \<ge> ?c3 n ! j"
    proof (intro impI allI)
      fix j
      assume "j < n"
      with ni mat_geE[OF geq wf2 wf3] 
      show "?c2 n ! j \<ge> ?c3 n ! j" by simp
    qed
    from nj r0 c2c3 have "scalar_prod (?r n) (?c2 n) \<succ> scalar_prod (?r n) (?c3 n)"
    proof (induct n)
      case (Suc n)
      have "scalar_prod (?r (Suc n)) (?c2 (Suc n)) = scalar_prod (?r n @ [m1 ! n ! k]) (?c2 n @ [m2 ! i ! n])" 
        (is "?sum2 = _") by simp
      also have "\<dots> = m1 ! n ! k * m2 ! i ! n + scalar_prod (?r n) (?c2 n)" (is "_ = plus ?p2 ?s2")
        by (simp add: scalar_prod_last)
      finally have sum2: "?sum2 = ?p2 + ?s2" .
      have "scalar_prod (?r (Suc n)) (?c3 (Suc n)) = scalar_prod (?r n @ [m1 ! n ! k]) (?c3 n @ [m3 ! i ! n])" 
        (is "?sum3 = _") by simp
      also have "\<dots> = m1 ! n ! k * m3 ! i ! n + scalar_prod (?r n) (?c3 n)" (is "_ = plus ?p3 ?s3") 
        by (simp add: scalar_prod_last)
      finally have sum3: "?sum3 = ?p3 + ?s3" .
      from Suc(3) have z: "m1 ! n ! k \<ge> 0" by (simp del: upt_Suc)
      from Suc(3) have za: "\<forall> j < n. ?r n ! j \<ge> 0"  by (simp del: upt_Suc)
      from Suc(4) have ge: "\<forall> j < n. ?c2 n ! j \<ge> ?c3 n ! j"  by (simp del: upt_Suc)
      show ?case
      proof (cases "j = n")
        case False
        with Suc(2) have j: "j < n" by auto
        have rec: "?s2 \<succ> ?s3"
          by (rule Suc, rule j, rule za, rule ge)
        from Suc(4) have ge: "m2 ! i ! n \<ge> m3 ! i ! n" by (simp del: upt_Suc)
        from times_right_mono[OF z ge] have p23: "?p2 \<ge> ?p3" .
        from compat2[OF plus_gt_left_mono[OF rec] plus_right_mono[OF p23]] have "?s2 + ?p2 \<succ> ?s3 + ?p3" .
        hence "?p2 + ?s2 \<succ> ?p3 + ?s3" unfolding add.commute[of ?p2] add.commute[of ?p3] .
        with sum2 sum3 show ?thesis by simp 
      next
        case True        
        with mono[OF monojk gt] z have p23: "?p2 \<succ> ?p3" by simp
        have wf1: "vec n (?r n)" by (simp add: vec_def)
        have wf2: "vec n (?c2 n)" by (simp add: vec_def)
        have wf3: "vec n (?c3 n)" by (simp add: vec_def)
        from ge have ge: "vec_ge (?c2 n) (?c3 n)" unfolding vec_ge[OF wf2 wf3] by simp
        from za have z: "vec_ge (?r n) (vec0 n)" unfolding vec_ge[OF wf1 vec0] by (simp add: vec0I_def)
        have s23: "?s2 \<ge> ?s3"
          by (rule scalar_prod_mono_right, (simp add: vec_def)+, rule ge, rule z)
        from compat2[OF plus_gt_left_mono[OF p23] plus_right_mono[OF s23]] sum2 sum3 show ?thesis by simp
      qed
    qed simp
    with s12 s13 show "?m12 ! i ! k \<succ> ?m13 ! i ! k" by simp
  qed    
qed
end

context both_mono_ordered_semiring_1
begin 

abbreviation mat_gt_arc :: "'a mat \<Rightarrow> 'a mat \<Rightarrow> bool"
where "mat_gt_arc \<equiv> mat_comp_all gt"

abbreviation mat_arc_pos :: "'a mat \<Rightarrow> bool"
where "mat_arc_pos \<equiv> mat_arc_posI arc_pos"

lemma mat_gt_arc_imp_mat_ge: assumes gt: "mat_gt_arc m1 m2" and wf: "mat nr nc m1" "mat nr nc m2"
  shows "mat_ge m1 m2"
  by (rule mat_geI[OF wf gt_imp_ge[OF mat_comp_allE[OF gt wf]]], auto)  

lemma scalar_prod_left_mono: assumes wf1: "vec nr v1"
  and wf2: "vec nr v2"
  and wf3: "vec nr v3"
  and gt1: "vec_comp_all gt v1 v2"
  shows "scalar_prod v1 v3 \<succ> scalar_prod v2 v3"
proof -
  from vec_comp_all_index[OF wf1 wf2] gt1 have g1: "\<forall> i < nr. v1 ! i \<succ> v2 ! i" by auto
  from g1 wf1 wf2 wf3 show ?thesis unfolding vec_def
  proof (induct nr arbitrary: v1 v2 v3)
    case (Suc nrr)
    from Suc obtain a1 w1 where v1: "v1 = a1 # w1" and w1: "length w1 = nrr" by (cases v1, auto)
    from Suc obtain a2 w2 where v2: "v2 = a2 # w2" and w2: "length w2 = nrr" by (cases v2, auto)
    from Suc obtain a3 w3 where v3: "v3 = a3 # w3" and w3: "length w3 = nrr" by (cases v3, auto)
    from Suc v1 v2 have a12: "a1 \<succ> a2" and w12: "\<forall> i < nrr. w1 ! i \<succ> w2 ! i" by auto
    have rec: "scalar_prod w1 w3 \<succ> scalar_prod w2 w3" 
      by (rule Suc, auto simp: w1 w2 w3 w12)
    have a: "a1 * a3 \<succ> a2 * a3" by (rule times_gt_left_mono[OF a12])
    show ?case 
      by (simp add: v1 v2 v3 scalar_prod_cons, rule plus_gt_both_mono[OF a rec])
  qed (simp add: scalar_prodI_def zero_leastI)
qed

lemma scalar_prod_right_mono: assumes wf1: "vec nr v1"
  and wf2: "vec nr v2"
  and wf3: "vec nr v3"
  and gt1: "vec_comp_all gt v2 v3"
  shows "scalar_prod v1 v2 \<succ> scalar_prod v1 v3"
proof -
  from vec_comp_all_index[OF wf2 wf3] gt1 have g1: "\<forall> i < nr. v2 ! i \<succ> v3 ! i" by auto
  from g1 wf1 wf2 wf3 show ?thesis unfolding vec_def
  proof (induct nr arbitrary: v1 v2 v3)
    case (Suc nrr)
    from Suc obtain a1 w1 where v1: "v1 = a1 # w1" and w1: "length w1 = nrr" by (cases v1, auto)
    from Suc obtain a2 w2 where v2: "v2 = a2 # w2" and w2: "length w2 = nrr" by (cases v2, auto)
    from Suc obtain a3 w3 where v3: "v3 = a3 # w3" and w3: "length w3 = nrr" by (cases v3, auto)
    from Suc v2 v3 have a23: "a2 \<succ> a3" and w23: "\<forall> i < nrr. w2 ! i \<succ> w3 ! i" by auto
    have rec: "scalar_prod w1 w2 \<succ> scalar_prod w1 w3" 
      by (rule Suc, auto simp: w1 w2 w3 w23)
    have a: "a1 * a2 \<succ> a1 * a3" by (rule times_gt_right_mono[OF a23])
    show ?case 
      by (simp add: v1 v2 v3 scalar_prod_cons, rule plus_gt_both_mono[OF a rec])
  qed (simp add: scalar_prodI_def zero_leastI)
qed

lemma mat_arc_pos_one: assumes n_pos: "n > 0"
  shows "mat_arc_posI arc_pos (mat1 n)"
  unfolding mat_arc_posI_def 
  unfolding mat1_index[OF n_pos n_pos] using arc_pos_one by simp

lemma mat_arc_pos_zero: assumes n_pos: "n > 0"
  shows "\<not> mat_arc_posI arc_pos (mat0 n n)"
  unfolding mat_arc_posI_def 
  unfolding mat0_index[OF n_pos n_pos] using arc_pos_zero by simp



lemma mat_gt_arc_compat: assumes ge: "mat_ge m1 m2" and gt: "mat_gt_arc m2 m3" and wf1: "mat nr nc m1" and wf2: "mat nr nc m2" and wf3: "mat nr nc m3" 
  shows "mat_gt_arc m1 m3"
proof (rule mat_comp_allI[OF wf1 wf3])
  fix i j
  assume i: "i < nc" and j: "j < nr"
  from mat_geE[OF ge wf1 wf2 i j] have one: "m1 ! i ! j \<ge> m2 ! i ! j" .
  from mat_comp_allE[OF gt wf2 wf3 i j] have two: "m2 ! i ! j \<succ> m3 ! i ! j" .
  from one two show "m1 ! i ! j \<succ> m3 ! i ! j" by (rule compat)
qed 

lemma mat_gt_arc_compat2: assumes gt: "mat_gt_arc m1 m2" and ge: "mat_ge m2 m3" and wf1: "mat nr nc m1" and wf2: "mat nr nc m2" and wf3: "mat nr nc m3" 
  shows "mat_gt_arc m1 m3"
proof (rule mat_comp_allI[OF wf1 wf3])
  fix i j
  assume i: "i < nc" and j: "j < nr"
  from mat_comp_allE[OF gt wf1 wf2 i j] have one: "m1 ! i ! j \<succ> m2 ! i ! j" .
  from mat_geE[OF ge wf2 wf3 i j] have two: "m2 ! i ! j \<ge> m3 ! i ! j" .
  from one two show "m1 ! i ! j \<succ>  m3 ! i ! j" by (rule compat2)
qed

lemma mat_gt_arc_trans: assumes gt1: "mat_gt_arc m1 m2" and gt2: "mat_gt_arc m2 m3" and wf1: "mat nr nc m1" and wf2: "mat nr nc m2" and wf3: "mat nr nc m3" 
  shows "mat_gt_arc m1 m3"
proof (rule mat_comp_allI[OF wf1 wf3])
  fix i j
  assume i: "i < nc" and j: "j < nr"
  from mat_comp_allE[OF gt1 wf1 wf2 i j] have one: "m1 ! i ! j \<succ> m2 ! i ! j" .
  from mat_comp_allE[OF gt2 wf2 wf3 i j] have two: "m2 ! i ! j \<succ> m3 ! i ! j" .
  from one two show "m1 ! i ! j \<succ> m3 ! i ! j" by (rule gt_trans)
qed

lemma mat_gt_arc_plus_mono: assumes gt1: "mat_gt_arc x y"
  and gt2: "mat_gt_arc z u"
  and wfx: "mat nr nc x"
  and wfy: "mat nr nc y"
  and wfz: "mat nr nc z"
  and wfu: "mat nr nc u"
  shows "mat_gt_arc (mat_plus x z) (mat_plus y u)"
proof -
  let ?xz = "mat_plus x z"
  let ?yu = "mat_plus y u"
  show ?thesis
  proof (rule mat_comp_allI)
    fix i j
    assume i: "i < nc" and j: "j < nr"
    show "mat_plus x z ! i ! j \<succ> mat_plus y u ! i ! j"
    proof (
        simp only: mat_plus_index[OF wfx wfz i j],
        simp only: mat_plus_index[OF wfy wfu i j],
        rule plus_gt_both_mono)
      show "x ! i ! j \<succ> y ! i ! j" using mat_comp_allE[OF gt1 wfx wfy i j] .
      show "z ! i ! j \<succ> u ! i ! j" using mat_comp_allE[OF gt2 wfz wfu i j] .
    qed
  qed (insert wfx wfy wfz wfu, auto)
qed


lemma mat_gt_arc_mult_left_mono: assumes gt1: "mat_gt_arc x y"
  and wfx: "mat nr nc x"
  and wfy: "mat nr nc y"
  and wfz: "mat nc ncc z"
  shows "mat_gt_arc (mat_mult nr x z) (mat_mult nr y z)"
proof -
  let ?xz = "mat_mult nr x z"
  let ?yz = "mat_mult nr y z"
  show ?thesis 
  proof (rule mat_comp_allI)
    fix i j
    assume i: "i < ncc" and j: "j < nr"
    have wfxj: "vec nc (row x j)" using row[OF wfx j] .
    have wfyj: "vec nc (row y j)" using row[OF wfy j] .
    have wfzi: "vec nc (col z i)" using col[OF wfz i] .
    show "?xz ! i ! j \<succ> ?yz ! i ! j"
    proof (
        unfold mat_mult_index[OF wfx wfz j i] mat_mult_index[OF wfy wfz j i],
        rule scalar_prod_left_mono[OF wfxj wfyj wfzi],
        unfold vec_comp_all_index[OF wfxj wfyj],
        intro allI impI
      )
      fix k
      assume k: "k < nc"
      from gt1 mat_comp_all[OF wfx wfy, of gt] j k
      show "row x j ! k \<succ> row y j ! k"
        by (unfold row_col[OF wfx j k] row_col[OF wfy j k] col_def, auto) 
    qed
  qed (insert wfx wfy wfz, auto)
qed

lemma mat_gt_arc_mult_right_mono: fixes x :: "'a mat" 
  assumes gt1: "mat_gt_arc y z"
  and wfx: "mat nr nc x"
  and wfy: "mat nc ncc y"
  and wfz: "mat nc ncc z"
  shows "mat_gt_arc (mat_mult nr x y) (mat_mult nr x z)"
proof -
  let ?xy = "mat_mult nr x y"
  let ?xz = "mat_mult nr x z"
  show ?thesis 
  proof (rule mat_comp_allI)
    fix i j
    assume i: "i < ncc" and j: "j < nr"
    have wfxj: "vec nc (row x j)" using row[OF wfx j] .
    have wfyi: "vec nc (col y i)" using col[OF wfy i] .
    have wfzi: "vec nc (col z i)" using col[OF wfz i] .
    show "?xy ! i ! j \<succ> ?xz ! i ! j"
    proof (
        unfold mat_mult_index[OF wfx wfy j i] mat_mult_index[OF wfx wfz j i],
        rule scalar_prod_right_mono[OF wfxj wfyi wfzi],
        unfold vec_comp_all_index[OF wfyi wfzi],
        intro allI impI
      )
      fix k
      assume k: "k < nc"
      from gt1[unfolded mat_comp_all[OF wfy wfz]] i k
      show "col y i ! k \<succ> col z i ! k" unfolding col_def by auto
    qed
  qed (insert wfx wfy wfz, auto)
qed

lemma mat_not_all_ge: assumes n_pos: "n > 0"
  and m1: "mat n n m1"
  and m2: "mat n n m2"
  and a2: "mat_arc_pos m2"
  shows "\<exists> m. mat n n m \<and> mat_ge m (mat0 n n) \<and> mat_arc_pos m \<and> \<not> mat_ge m1 (mat_mult n m2 m)"
proof -
  obtain c where c: "c = m1 ! 0 ! 0" by auto
  from a2 have "arc_pos (m2 ! 0 ! 0)" unfolding mat_arc_posI_def .
  from not_all_ge[OF this, of c] obtain e where e0: "e \<ge> 0" and ae: "arc_pos e"
    and nc: "\<not> c \<ge> m2 ! 0 ! 0 * e" by auto
  let ?gen = "\<lambda> f. map (\<lambda>i. map (f i) [0..<n]) [0..<n]"
  {
    fix f :: "nat \<Rightarrow> nat \<Rightarrow> 'a" 
    have "mat n n (?gen f)"
      unfolding mat_def by (auto simp: vec_def)    
  } note gen[simp] = this
  obtain f :: "nat \<Rightarrow> nat \<Rightarrow> 'a" where f: "f = (\<lambda> i j. if i = 0 \<and> j = 0 then e else 0)" by auto
  let ?m = "?gen f"
  have m00: "?m ! 0 ! 0 = e" using n_pos unfolding f by auto
  show ?thesis
  proof (rule exI[of _ ?m], intro conjI, rule gen)
    show "mat_ge ?m (mat0 n n)"
    proof (rule mat_geI)
      fix i j
      assume i: "i < n" and j: "j < n"
      have m: "?m ! i ! j = f i j" using i j by auto
      have 0: "mat0 n n ! i ! j = (0 :: 'a)" using i j by simp 
      show "?m ! i ! j \<ge> mat0 n n ! i ! j" unfolding m 0
        unfolding f using e0 ge_refl by auto
    qed auto
  next
    show "mat_arc_pos ?m" 
      unfolding mat_arc_posI_def 
      unfolding m00 by (rule ae)
  next
    let ?mult = "mat_mult n m2 ?m"
    from n_pos obtain nn where n: "n = Suc nn" by (cases n, auto)
    have col: "col ?m 0 = map (f 0) [0 ..< n]" unfolding col_def using n_pos by simp
    also have "... = f 0 0 # map (\<lambda> i. f 0 (Suc i)) [0 ..< nn]"
      unfolding n unfolding map_upt_Suc ..
    also have "... = e # replicate nn 0" unfolding f 
      by (simp add: map_replicate_trivial)
    also have "... = e # vec0 nn" unfolding vec0I_def ..
    finally have col: "col ?m 0 = e # vec0 nn" by simp
    from row[OF m2 n_pos] have row: "length (row m2 0) = n" unfolding vec_def .
    with n_pos obtain r where row: "row m2 0 = (row m2 0 ! 0) # r"      
      by (cases "row m2 0", auto)
    also have "... = m2 ! 0 ! 0 # r" unfolding row_col[OF m2 n_pos n_pos]
      unfolding col_def ..
    finally have row: "row m2 0 = m2 ! 0 ! 0 # r" by simp
    from mat_mult_index[OF m2 gen n_pos n_pos]
    have "?mult ! 0 ! 0 = scalar_prod (row m2 0) (col ?m 0)"
      by simp
    also have "... = scalar_prod (m2 ! 0 ! 0 # r) (e # vec0 nn)"
      unfolding row col ..
    also have "... = m2 ! 0 ! 0 * e + scalar_prod r (vec0 nn)" 
      unfolding scalar_prod_cons ..
    also have "... = m2 ! 0 ! 0 * e"
      unfolding scalar_right_zero by simp
    finally have "?mult ! 0 ! 0 = m2 ! 0 ! 0 * e" .
    with nc c have "\<not> m1 ! 0 ! 0 \<ge> ?mult ! 0 ! 0" by simp
    thus "\<not> mat_ge m1 ?mult"
      unfolding mat_ge_def mat_comp_all[OF m1 mat_mult[OF m2 gen]] using n_pos
      by auto
  qed
qed

lemma mat0_leastI: assumes wf: "mat nr nc m"
  shows "mat_gt_arc m (mat0 nr nc)"
proof (rule mat_comp_allI[OF wf])
  fix i j
  assume i: "i < nc" and j: "j < nr"
  thus "m ! i ! j \<succ> mat0I 0 nr nc ! i ! j" by (auto simp: zero_leastI)
qed auto

lemma mat0_leastII: 
  assumes gt: "mat_gt_arc (mat0 nr nc) m"
  and wf: "mat nr nc m"
  shows "m = mat0 nr nc"
proof (rule mat_eqI)
  fix i j
  assume i: "i < nc" and j: "j < nr"
  show "m ! i ! j = mat0 nr nc ! i ! j"
    unfolding mat0_index[OF i j]
  proof (rule zero_leastII)
    show "0 \<succ> m ! i ! j" using i j gt mat_comp_all[OF mat0 wf] mat0_index[OF i j] by force
  qed
qed (insert wf, auto)


lemma mat0_leastIII: assumes wf: "mat nr nc m"
  shows "mat_ge m ((mat0 nr nc) :: 'a mat)"
proof (rule mat_geI[OF wf])
  fix i j
  assume i: "i < nc" and j: "j < nr"
  show "m ! i ! j \<ge> mat0 nr nc ! i ! j"
    by (simp add: mat0_index[OF i j] zero_leastIII)
qed auto

lemma mat1_gt_arc_mat0: "mat_gt_arc (mat1 n) (mat0 n n)"
proof (rule mat_comp_allI)
  fix i j
  assume i: "i < n" and j: "j < n"
  show "mat1 n ! i ! j \<succ> mat0 n n ! i ! j"
    by (simp add: mat0_index[OF i j] zero_leastI)
qed auto

lemma mat_default_gt_arc_mat0: "mat_gt_arc (mat_default n) (mat0 n n)"
proof (rule mat_comp_allI)
  fix i j
  assume i: "i < n" and j: "j < n"
  show "mat_default n ! i ! j \<succ> mat0 n n ! i ! j"
    by (simp only: mat0_index[OF i j],
      rule zero_leastI)
qed auto
end 

context SN_both_mono_ordered_semiring_1
begin

lemma mat_gt_arc_SN: assumes n_pos: "n > 0" shows
  "SN {(x, y). mat n n x \<and> mat n n y \<and> mat_arc_pos y \<and> mat_gt_arc x y}" (is "SN ?rel")
proof (rule ccontr)
  assume "\<not> SN ?rel"
  from this obtain f and x where "f (0 :: nat) = x" and steps: "\<forall> i. (f i, f (Suc i)) \<in> ?rel" unfolding SN_defs by blast
  hence pos: "\<forall> i. arc_pos (f (Suc i) ! 0 ! 0)" unfolding mat_arc_posI_def by blast
  have gt: "\<forall> i. f i ! 0 ! 0 \<succ> f (Suc i) ! 0 ! 0"
  proof
    fix i
    from steps have wf1: "mat n n (f i)" and wf2: "mat n n (f (Suc i))" and gt: "mat_gt_arc (f i) (f (Suc i))" by auto
    show "f i ! 0 ! 0 \<succ>  f (Suc i) ! 0 ! 0" using mat_comp_allE[OF gt wf1 wf2] mat0_index[OF n_pos n_pos, of 0] n_pos by force
  qed
  from pos gt SN show False unfolding SN_defs by force
qed


lemma mat_arc_pos_plus: assumes n_pos: "n > 0" 
  and wf1: "mat n n m1"
  and wf2: "mat n n m2"
  and arc_pos: "mat_arc_pos m1"
  shows "mat_arc_pos (mat_plus m1 m2)"
proof -
  from n_pos wf1 obtain v1 mm1 where m1: "m1 = v1 # mm1" unfolding mat_def by (cases m1, auto)
  from n_pos wf2 obtain v2 mm2 where m2: "m2 = v2 # mm2" unfolding mat_def by (cases m2, auto)  
  from n_pos wf1 m1 obtain a1 vv1 where v1: "v1 = a1 # vv1" unfolding mat_def by (cases v1, auto simp: vec_def)
  from n_pos wf2 m2 obtain a2 vv2 where v2: "v2 = a2 # vv2" unfolding mat_def by (cases v2, auto simp: vec_def)
  from m1 v1 arc_pos have "arc_pos a1" unfolding mat_arc_posI_def by simp
  hence "arc_pos (plus a1 a2)" by (rule arc_pos_plus)
  with m1 v1 m2 v2 show ?thesis unfolding mat_arc_posI_def mat_plusI_def vec_plusI_def by simp
qed

lemma mat_arc_pos_mult: assumes n_pos: "n > 0" 
  and wf1: "mat n n m1"
  and wf2: "mat n n m2"
  and ap1: "mat_arc_pos m1"
  and ap2: "mat_arc_pos m2"
  shows "mat_arc_pos (mat_mult n m1 m2)"
proof -
  from n_pos wf1 obtain v1 mm1 where m1: "m1 = v1 # mm1" unfolding mat_def by (cases m1, auto)
  from n_pos wf2 obtain v2 mm2 where m2: "m2 = v2 # mm2" unfolding mat_def by (cases m2, auto)  
  from n_pos wf1 m1 obtain a1 vv1 where v1: "v1 = a1 # vv1" unfolding mat_def by (cases v1, auto simp: vec_def)
  from n_pos wf2 m2 obtain a2 vv2 where v2: "v2 = a2 # vv2" unfolding mat_def by (cases v2, auto simp: vec_def)
  from m1 v1 ap1 have a1: "arc_pos a1" unfolding mat_arc_posI_def by simp
  from m2 v2 ap2 have a2: "arc_pos a2" unfolding mat_arc_posI_def by simp
  from a1 a2 have prod: "arc_pos (a1 * a2)" by (rule arc_pos_mult)
  show ?thesis unfolding mat_arc_posI_def 
    by (simp only: mat_mult_index[OF wf1 wf2 n_pos n_pos],
    simp add: m1 v1 m2 v2 col_def row_def scalar_prod_cons arc_pos_plus[OF prod])
qed

lemma mat_arc_pos_mat_default: assumes n_pos: "n > 0" shows "mat_arc_pos (mat_default n)"
  unfolding mat1I_def mat_arc_posI_def 
  using n_pos
  by (auto simp: vec1I_def arc_pos_default)
end




context weak_SN_strict_mono_ordered_semiring_1
begin

abbreviation weak_mat_gt :: "nat \<Rightarrow> 'a mat \<Rightarrow> 'a mat \<Rightarrow> bool"
where "weak_mat_gt \<equiv> mat_gtI weak_gt"

lemma weak_mat_gt_mono: assumes sd_n: "sd \<le> n" and
    orient: "\<And> m1 m2. mat n n m1 \<and> mat n n m2 \<and> (m1,m2) \<in> set m12s \<Longrightarrow> weak_mat_gt sd m1 m2"
   shows "\<exists> gt. SN_strict_mono_ordered_semiring_1 default gt mono \<and> (\<forall> m1 m2. mat n n m1 \<and> mat n n m2 \<and> (m1, m2) \<in> set m12s \<longrightarrow> mat_gtI gt sd m1 m2)"
proof -
  let ?m1x = "concat (concat (map fst m12s))"
  let ?m2y = "concat (concat (map snd m12s))"
  let ?pairs = "concat (map (\<lambda> x. map (\<lambda> y. (x,y)) ?m2y) ?m1x)"
  let ?strict = "filter (\<lambda> (x,y). weak_gt x y) ?pairs"
  have "\<forall> x y. (x,y) \<in> set ?strict \<longrightarrow> weak_gt x y" by auto
  from weak_gt_mono[OF this] obtain gt where order: "SN_strict_mono_ordered_semiring_1 default gt mono" and orient2: "\<And> x y. (x, y) \<in> set ?strict \<Longrightarrow> gt x y" by auto
  show ?thesis
  proof (intro exI allI conjI impI)
    fix m1 m2
    assume ass: "mat n n m1 \<and> mat n n m2 \<and> (m1,m2) \<in> set m12s"
    hence wf1: "mat n n m1" and wf2: "mat n n m2" and m1m2: "(m1,m2) \<in> set m12s" by auto
    from orient[OF ass, unfolded mat_gt[OF wf1 wf2 sd_n]] 
    obtain i j where ge: "mat_ge m1 m2" and i: "i < sd" and j: "j < sd" and weak_gt: "weak_gt (m1 ! i ! j) (m2 ! i ! j)" (is "weak_gt ?x ?y") by auto
    from wf1 i j sd_n have m1ij: "m1 ! i \<in> set m1 \<and> m1 ! i ! j \<in> set (m1 ! i)" unfolding mat_def  by (auto simp: vec_def)
    from wf2 i j sd_n have m2ij: "m2 ! i \<in> set m2 \<and> m2 ! i ! j \<in> set (m2 ! i)" unfolding mat_def  by (auto simp: vec_def)
    have x: "?x \<in> set ?m1x" by (auto, rule bexI[OF _ m1m2], rule bexI[of _ "m1 ! i"], auto simp: m1ij)
    have y: "?y \<in> set ?m2y" by (auto, rule bexI[OF _ m1m2], rule bexI[of _ "m2 ! i"], auto simp: m2ij)
    from x y have "(?x,?y) \<in> set ?pairs" by force
    with weak_gt have gt: "(?x,?y) \<in> set ?strict" by simp
    show "mat_gtI gt sd m1 m2" unfolding mat_gt[OF wf1 wf2 sd_n]
      by (intro exI conjI, rule ge, rule i, rule j, rule orient2[OF gt])
  qed (rule order)
qed
end



context weak_SN_both_mono_ordered_semiring_1
begin

abbreviation weak_mat_gt_arc :: "'a mat \<Rightarrow> 'a mat \<Rightarrow> bool"
where "weak_mat_gt_arc \<equiv> mat_comp_all weak_gt"

lemma weak_mat_gt_both_mono: assumes orient: "\<And> m1 m2. mat n n m1 \<and> mat n n m2 \<and> (m1,m2) \<in> set m12s \<Longrightarrow> weak_mat_gt_arc m1 m2"
   shows "\<exists> gt. SN_both_mono_ordered_semiring_1 default gt arc_pos \<and> (\<forall> m1 m2. mat n n m1 \<and> mat n n m2 \<and> (m1, m2) \<in> set m12s \<longrightarrow> mat_comp_all gt m1 m2)"
proof -
  let ?m1x = "concat (concat (map fst m12s))"
  let ?m2y = "concat (concat (map snd m12s))"
  let ?pairs = "concat (map (\<lambda> x. map (\<lambda> y. (x,y)) ?m2y) ?m1x)"
  let ?strict = "filter (\<lambda> (x,y). weak_gt x y) ?pairs"
  have "\<forall> x y. (x,y) \<in> set ?strict \<longrightarrow> weak_gt x y" by auto
  from weak_gt_both_mono[OF this] obtain gt where order: "SN_both_mono_ordered_semiring_1 default gt arc_pos" and orient2: "\<And> x y. (x, y) \<in> set ?strict \<Longrightarrow> gt x y" by auto
  show ?thesis
  proof (intro exI allI conjI impI, rule order)
    fix m1 m2
    assume ass: "mat n n m1 \<and> mat n n m2 \<and> (m1,m2) \<in> set m12s"
    hence wf1: "mat n n m1" and wf2: "mat n n m2" and m1m2: "(m1,m2) \<in> set m12s" by auto
    show "mat_comp_all gt  m1 m2" 
    proof (rule mat_comp_allI[OF wf1 wf2])
      fix i j
      assume i: "i < n" and j: "j < n"
      from mat_comp_allE[OF orient[OF ass] wf1 wf2 this]
      have weak_gt: "weak_gt (m1 ! i ! j) (m2 ! i ! j)" (is "weak_gt ?x ?y") by auto  
      from wf1 i j have m1ij: "m1 ! i \<in> set m1 \<and> m1 ! i ! j \<in> set (m1 ! i)" unfolding mat_def  by (auto simp: vec_def)
      from wf2 i j have m2ij: "m2 ! i \<in> set m2 \<and> m2 ! i ! j \<in> set (m2 ! i)" unfolding mat_def  by (auto simp: vec_def)
      have x: "?x \<in> set ?m1x" by (simp, rule bexI[OF _ m1m2], rule bexI[of _ "m1 ! i"], auto simp: m1ij)
      have y: "?y \<in> set ?m2y" by (simp, rule bexI[OF _ m1m2], rule bexI[of _ "m2 ! i"], auto simp: m2ij)
      from x y have "(?x,?y) \<in> set ?pairs" by force
      with weak_gt have gt: "(?x,?y) \<in> set ?strict" by simp
      show "gt ?x ?y" by (rule orient2[OF gt])
    qed
  qed
qed
end

subsection {* Connection to ordered semirings *}

definition mat_ordered_semiring :: "nat \<Rightarrow> nat \<Rightarrow> ('a :: ordered_semiring_1 \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'b \<Rightarrow> ('a mat,'b) ordered_semiring_scheme" where
  "mat_ordered_semiring n sd gt b \<equiv> mat_ring n \<lparr>
    ordered_semiring.geq = mat_ge,
    gt = mat_gtI gt sd,
    max = mat_max,
    \<dots> = b\<rparr>"

lemma (in one_mono_ordered_semiring_1) mat_ordered_semiring: assumes sd_n: "sd \<le> n" 
  shows "ordered_semiring 
    (mat_ordered_semiring n sd op \<succ> b :: ('a mat,'b) ordered_semiring_scheme)" 
  (is "ordered_semiring ?R")
proof -
  interpret semiring ?R unfolding mat_ordered_semiring_def by (rule mat_semiring)
  show ?thesis 
    by (unfold_locales, unfold mat_ring_def mat_ordered_semiring_def ordered_semiring_record_simps,
      auto intro: mat_max_comm mat_gt_compat[OF sd_n] mat_gt_compat2[OF sd_n] mat_ge_trans
      mat_plus_left_mono mat_mult_left_mono mat_mult_right_mono mat_ge_refl mat_gt_imp_mat_ge
      mat1_ge_mat0 mat_max_mono mat_max_ge mat_max_id)
qed

definition mat_both_ordered_semiring :: "nat \<Rightarrow> ('a :: ordered_semiring_1 \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'b \<Rightarrow> ('a mat,'b) ordered_semiring_scheme" where
  "mat_both_ordered_semiring n gt b \<equiv> mat_ring n \<lparr>
    ordered_semiring.geq = mat_ge,
    gt = mat_comp_all gt,
    max = mat_max,
    \<dots> = b\<rparr>"

lemma (in both_mono_ordered_semiring_1) mat_both_ordered_semiring: assumes n: "n > 0" 
  shows "ordered_semiring 
    (mat_both_ordered_semiring n op \<succ> b :: ('a mat,'b) ordered_semiring_scheme)" 
  (is "ordered_semiring ?R")
proof -
  interpret semiring ?R unfolding mat_both_ordered_semiring_def by (rule mat_semiring)
  show ?thesis 
    by (unfold_locales, unfold mat_ring_def mat_both_ordered_semiring_def ordered_semiring_record_simps,
      auto intro: mat_max_comm mat_ge_trans
      mat_plus_left_mono mat_mult_left_mono mat_mult_right_mono mat_ge_refl
      mat1_ge_mat0 mat_max_mono mat_max_ge mat_max_id mat_gt_arc_trans mat_gt_arc_imp_mat_ge
      mat_gt_arc_compat mat_gt_arc_compat2)
qed

end
