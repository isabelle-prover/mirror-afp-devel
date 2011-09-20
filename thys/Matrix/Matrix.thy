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

header {* Matrices *}

theory Matrix
imports "../Abstract-Rewriting/SN_Orders"
begin

text {*
  This theory shows provides the operations of matrix addition, multiplication,
  transposition, and matrix comparisons as executable functions. 
  Moreover, it is proven that strongly normalizing (monotone) orders can be lifted to
  strongly normalizing (monotone) orders over matrices. 
*}


subsection {* types and well-formedness of vectors / matrices *}

type_synonym 'a vec = "'a list"
type_synonym 'a mat = "'a vec list" (* list of column-vectors *)


(* vector of given length *)
definition vec :: "nat \<Rightarrow> 'x vec \<Rightarrow> bool"
 where "vec n x = (length x = n)"

(* matrix of given number of rows and columns *)
definition mat :: "nat \<Rightarrow> nat \<Rightarrow> 'a mat \<Rightarrow> bool" where
 "mat nr nc m = (length m = nc \<and> list_all (vec nr) m)"

subsection {* definitions / algorithms *}

text {* note that these algorithms are generic in all basic definitions / operations 
like 0 (ze) 1 (on) addition (pl) multiplication (ti) and in the dimension(s) of the matrix/vector.
Hence, many of these algorithms require these definitions/operations/sizes as arguments.
All indices start from 0.
*}

(* the 0 vector *)
definition vec0I :: "'a \<Rightarrow> nat \<Rightarrow> 'a vec" where 
 "vec0I ze n = replicate n ze"

(* the 0 matrix *)
definition mat0I :: "'a \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a mat" where
  "mat0I ze nr nc = replicate nc (vec0I ze nr)"

(* the i-th unit vector of size n *) 
definition vec1I :: "'a \<Rightarrow> 'a \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a vec"
  where "vec1I ze on n i \<equiv> replicate i ze @ on # replicate (n - 1 - i) ze"

(* the 1 matrix *)
definition mat1I :: "'a \<Rightarrow> 'a \<Rightarrow> nat \<Rightarrow> 'a mat"
  where "mat1I ze on n \<equiv> map (vec1I ze on n) [0 ..< n]"


(* vector addition *)
definition vec_plusI :: "('a \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> 'a vec \<Rightarrow> 'a vec \<Rightarrow> 'a vec" where 
 "vec_plusI pl v w = map (\<lambda> xy. pl (fst xy) (snd xy)) (zip v w)"

(* matrix addition *)
definition mat_plusI :: "('a \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> 'a mat \<Rightarrow> 'a mat \<Rightarrow> 'a mat"
 where "mat_plusI pl m1 m2 = map (\<lambda> uv. vec_plusI pl (fst uv) (snd uv)) (zip m1 m2)"

(* scalar product *)
definition scalar_prodI :: "'a \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> 'a vec \<Rightarrow> 'a vec \<Rightarrow> 'a" where
 "scalar_prodI ze pl ti v w = foldr (\<lambda> (x,y) s. pl (ti x y) s) (zip v w) ze"

(* the m-th row of a matrix *)
definition row :: "'a mat \<Rightarrow> nat \<Rightarrow> 'a vec"
where "row m i \<equiv> map (\<lambda> w. w ! i) m"

(* the m-th column of a matrix *)
definition col :: "'a mat \<Rightarrow> nat \<Rightarrow> 'a vec"
where "col m i \<equiv> m ! i"

(* transposition of a matrix (number of rows of matrix has to be given since otherwise one 
   could not compute transpose [] which might be [] or [[]] or [[], []], or ...) *)
fun transpose :: "nat \<Rightarrow> 'a mat \<Rightarrow> 'a mat"
 where "transpose nr [] = replicate nr []"
     | "transpose nr (v # m) = map (\<lambda> (vi,mi). (vi # mi)) (zip v (transpose nr m))"

(* matrix-vector multiplication, assumes the transposed matrix is given *)
definition matT_vec_multI :: "'a \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> 'a mat \<Rightarrow> 'a vec \<Rightarrow> 'a vec"
 where "matT_vec_multI ze pl ti m v = map (\<lambda> w. scalar_prodI ze pl ti w v) m"

(* matrix-matrix multiplication, number of rows of left matrix has to be given (as transpose is used) *)
definition mat_multI :: "'a \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> nat \<Rightarrow> 'a mat \<Rightarrow> 'a mat \<Rightarrow> 'a mat" 
where "mat_multI ze pl ti nr m1 m2 \<equiv> map (matT_vec_multI ze pl ti (transpose nr m1)) m2"

(* taking only the n first elements of a vector *)
definition sub_vec :: "nat \<Rightarrow> 'a vec \<Rightarrow> 'a vec"
where "sub_vec = take"

(* taking only the upper left sub matrix *)
definition sub_mat :: "nat \<Rightarrow> nat \<Rightarrow> 'a mat \<Rightarrow> 'a mat"
where "sub_mat nr nc m = map (sub_vec nr) (take nc m)"

(* comparison of vectors where all components have to be in relation *)
definition vec_comp_all :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a vec \<Rightarrow> 'a vec \<Rightarrow> bool"
  where "vec_comp_all rel v w \<equiv> list_all (\<lambda> (a,b). rel a b) (zip v w)"

(* comparison of vectors using >= componentwise *)
definition vec_ge :: "('a :: non_strict_order) vec \<Rightarrow> 'a vec \<Rightarrow> bool"
  where "vec_ge \<equiv> vec_comp_all ge"

(* comparison of matrices where all components have to be in relation *)
definition mat_comp_all :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a mat \<Rightarrow> 'a mat \<Rightarrow> bool"
  where "mat_comp_all rel m1 m2 \<equiv> list_all (\<lambda> (v,w). vec_comp_all rel v w) (zip m1 m2)"

(* comparison of matrices using >= componentwise *)
definition mat_ge :: "('a :: non_strict_order) mat \<Rightarrow> 'a mat \<Rightarrow> bool"
  where "mat_ge \<equiv> mat_comp_all ge"

(* demanding at least one strict decrease between two vectors *)
definition vec_pre_gtI :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a vec \<Rightarrow> 'a vec \<Rightarrow> bool"
  where "vec_pre_gtI gt v w \<equiv> list_ex (\<lambda> (a,b). gt a b) (zip v w)"

(* demanding at least one strict decrease between two matrices *)
definition mat_pre_gtI :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a mat \<Rightarrow> 'a mat \<Rightarrow> bool"
  where "mat_pre_gtI gt m1 m2 \<equiv> list_ex (\<lambda> (v,w). vec_pre_gtI gt v w) (zip m1 m2)"

(* strict comparison of matrices is done by demanding that all entries are weakly
   decreasing and that there is at least one entry in the upper left sub-matrices
   which strictly decreases *)      
definition mat_gtI :: "('a :: non_strict_order \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> nat \<Rightarrow> 'a mat \<Rightarrow> 'a mat \<Rightarrow> bool"
  where "mat_gtI gt sd m1 m2 \<equiv> mat_ge m1 m2 \<and> mat_pre_gtI gt (sub_mat sd sd m1) (sub_mat sd sd m2)"

(* checking whether a matrix is monotone w.r.t. >. To this end, 
   it is ensured that all columns in the upper left sub-matrix have an entry 
   of at least 1 *)
definition mat_monoI :: "('a \<Rightarrow> bool) \<Rightarrow> nat \<Rightarrow> 'a mat \<Rightarrow> bool"
where "mat_monoI geq1 sd m = list_all (list_ex geq1) (sub_mat sd sd m)"


(* map on vectors *)
definition vec_map :: "('a \<Rightarrow> 'a) \<Rightarrow> 'a vec \<Rightarrow> 'a vec"
  where "vec_map = map"

(* map on matrices *)
definition mat_map :: "('a \<Rightarrow> 'a) \<Rightarrow> 'a mat \<Rightarrow> 'a mat"
  where "mat_map f = map (vec_map f)"

(* max0 on matrices *)
definition mat_max0 :: "('a :: max_ordered_monoid_add) mat \<Rightarrow> 'a mat"
  where "mat_max0 \<equiv> mat_map max0"

(* checking whether a matrix is arctic positive (first entry is arctic positive) *)
definition mat_arc_posI :: "('a \<Rightarrow> bool) \<Rightarrow> 'a mat \<Rightarrow> bool"
where "mat_arc_posI ap m \<equiv> ap (m ! 0 ! 0)"


subsection {* algorithms preserve dimensions *}

(* locally add these lemmas to the simplifier *)
declare list_all_ex[simp]
(* and at the end throw them out of the simplifier again *)


lemma vec0[simp]: "vec nr (vec0I ze nr)"
  by (simp add: vec_def vec0I_def)

lemma mat0[simp]: "mat nr nc (mat0I ze nr nc)"
unfolding mat_def mat0I_def
using replicate_prop[of "vec nr" "vec0I ze nr" "nc"] by simp

lemma vec1: assumes "i < nr" shows "vec nr (vec1I ze on nr i)"
unfolding vec_def vec1I_def using assms by auto

lemma mat1: "mat nr nr (mat1I ze on nr)"
unfolding mat_def mat1I_def using vec1 by auto

lemma vec_plus: "\<lbrakk>vec nr u; vec nr v\<rbrakk> \<Longrightarrow> vec nr (vec_plusI pl u v)"
using assms 
unfolding vec_plusI_def vec_def
by auto

lemma mat_plus: assumes "mat nr nc m1" and "mat nr nc m2" shows "mat nr nc (mat_plusI pl m1 m2)"
using assms
unfolding mat_def mat_plusI_def
proof (simp, induct nc arbitrary: m1 m2, simp)
  case (Suc nn)
  show ?case 
  proof (cases m1)
    case Nil with Suc show ?thesis by auto
  next
    case (Cons v1 mm1) note oCons = this
    with Suc have l1: "length mm1 = nn" by auto
    show ?thesis
    proof (cases m2)
      case Nil with Suc show ?thesis by auto
    next
      case (Cons v2 mm2)
      with Suc have l2: "length mm2 = nn" by auto
      show ?thesis by (simp add: Cons oCons, intro conjI[OF vec_plus], (simp add: Cons oCons Suc)+, rule Suc, auto simp: Cons oCons Suc l1 l2)
    qed
  qed
qed

lemma vec_map: "vec nr u \<Longrightarrow> vec nr (vec_map f u)"
using assms 
unfolding vec_map_def vec_def
by auto

lemma mat_map: "mat nr nc m \<Longrightarrow> mat nr nc (mat_map f m)"
using assms vec_map
unfolding mat_map_def mat_def 
by auto

lemma row: assumes "mat nr nc m"
  and "i < nr"
  shows "vec nc (row m i)"
  using assms
  unfolding vec_def row_def mat_def
  by (auto simp: vec_def) 

lemma col: assumes "mat nr nc m"
  and "i < nc"
  shows "vec nr (col m i)"
  using assms
  unfolding vec_def col_def mat_def
  by (auto simp: vec_def) 

lemma transpose: assumes "mat nr nc m"
  shows "mat nc nr (transpose nr m)"
using assms 
proof (induct m arbitrary: nc)
  case (Cons v m)
  from `mat nr nc (v # m)` obtain ncc where nc: "nc = Suc ncc" by (cases nc, auto simp: mat_def) 
  with Cons have wfRec: "mat ncc nr (transpose nr m)" unfolding mat_def by auto
  have "min nr (length (transpose nr m)) = nr" using wfRec unfolding mat_def by auto
  moreover have "list_all (vec nc) (transpose nr (v # m))"
  proof -
    {
      fix a b
      assume mem: "(a,b) \<in> set (zip v (transpose nr m))"
      from mem have "b \<in> set (transpose nr m)" by (rule set_zip_rightD)
      with wfRec have "length b = ncc" unfolding mat_def using vec_def[of ncc] by auto
      hence "length (split op # (a,b)) = Suc ncc" by auto
    }
    thus ?thesis
      by (auto simp: vec_def nc)
  qed
  moreover from `mat nr nc (v # m)` have wfV: "length v = nr" unfolding mat_def by (simp add: vec_def)
  ultimately
  show ?case unfolding mat_def
    by (intro conjI, auto simp: wfV wfRec mat_def vec_def)
qed (simp add: mat_def vec_def set_replicate_conv_if)


lemma matT_vec_multI: assumes "mat nr nc m"
  shows "vec nc (matT_vec_multI ze pl ti m v)"
  unfolding matT_vec_multI_def
  using assms
  unfolding mat_def
  by (simp add: vec_def)

lemma mat_mult: assumes wf1: "mat nr n m1"
  and wf2: "mat n nc m2"
  shows "mat nr nc (mat_multI ze pl ti nr m1 m2)"
using assms
unfolding mat_def mat_multI_def by (auto simp: matT_vec_multI[OF transpose[OF wf1]])


lemma mat_max0: assumes "mat nr nc m" shows "mat nr nc (mat_max0 m)"
using assms unfolding mat_max0_def by (rule mat_map)

lemma sub_vec: assumes "vec nr v" and "sd \<le> nr" 
  shows "vec sd (sub_vec sd v)"
using assms unfolding vec_def sub_vec_def by auto

lemma sub_mat: assumes wf: "mat nr nc m" and sr: "sr \<le> nr" and sc: "sc \<le> nc"
  shows "mat sr sc (sub_mat sr sc m)"
using assms in_set_takeD[of _ sc m] sub_vec[OF _ sr] unfolding mat_def sub_mat_def by auto


subsection {* properties of algorithms which do not depend on properties of type of matrix *}

lemma mat0_index: assumes "i < nc" and "j < nr"
  shows "mat0I ze nr nc ! i ! j = ze"
unfolding mat0I_def vec0I_def using assms by auto

lemma mat0_row: assumes "i < nr"
  shows "row (mat0I ze nr nc) i = vec0I ze nc"
unfolding row_def mat0I_def vec0I_def
using assms by auto


lemma mat0_col: assumes "i < nc"
  shows "col (mat0I ze nr nc) i = vec0I ze nr"
unfolding mat0I_def col_def
using assms by auto

lemma vec1_index: assumes i: "i < n"
  and j: "j < n"
  shows "vec1I ze on n i ! j = (if i = j then on else ze)" (is "_ = ?r")
unfolding vec1I_def
proof -
  let ?l = "replicate i ze @ on # replicate (n - 1 - i) ze"
  have len: "length ?l > i" by auto
  have len2: "length (replicate i ze @ on # []) > i" by auto
  show "?l ! j = ?r"
  proof (cases "j = i")
    case True
    thus ?thesis by (simp add: nth_append)
  next
    case False
    show ?thesis 
    proof (cases "j < i")
      case True
      thus ?thesis by (simp add: nth_append)
    next
      case False
      with `j \<noteq> i` have gt: "j > i" by auto
      from this have "\<exists> k. j = i + Suc k" by arith
      from this obtain k where k: "j = i + Suc k" by auto
      with j i show ?thesis by (simp add: nth_append)
    qed
  qed
qed


lemma col_transpose_is_row: 
  assumes wf: "mat nr nc m"
  and i: "i < nr"
  shows "col (transpose nr m) i = row m i"
using wf 
proof (induct m arbitrary: nc)
  case (Cons v m)
  from `mat nr nc (v # m)` obtain ncc where nc: "nc = Suc ncc" and wf: "mat nr ncc m"  by (cases nc, auto simp: mat_def)
  from `mat nr nc (v # m)` nc have lengths: "(\<forall> w \<in> set m. length w = nr) \<and> length v = nr \<and> length m = ncc" unfolding mat_def by (auto simp: vec_def)
  from wf Cons have colRec: "col (transpose nr m) i = row m i" by auto
  hence simpme: "transpose nr m ! i = row m i" unfolding col_def by auto
  from wf have trans: "mat ncc nr (transpose nr m)" by (rule transpose)
  hence lengths2: "(\<forall> w \<in> set (transpose nr m). length w = ncc) \<and> length (transpose nr m) = nr" unfolding mat_def by (auto simp: vec_def)
  {
    fix j
    assume "j < length (col (transpose nr (v # m)) i)"
    hence "j < Suc ncc" by (simp add: col_def lengths2 lengths i) 
    hence "col (transpose nr (v # m)) i ! j = row (v # m) i ! j"
      by (cases j, simp add: row_def col_def i lengths lengths2, simp add: row_def col_def i lengths lengths2 simpme)
  } note simpme = this
  show ?case by (rule nth_equalityI, simp add: col_def row_def lengths lengths2 i, intro allI impI, rule simpme)
qed (simp add: col_def row_def mat_def i)

lemma mat_col_eq:
  assumes wf1: "mat nr nc m1"
  and wf2: "mat nr nc m2"
  shows "(\<forall> i < nc. col m1 i = col m2 i) = (m1 = m2)" (is "?l = ?r")
proof
  assume ?r thus ?l by auto
next
  assume ?l show ?r 
  proof (rule nth_equalityI)
    show "length m1 = length m2" using wf1 wf2 unfolding mat_def by auto
  next
    from `?l` show "\<forall> i < length m1. m1 ! i = m2 ! i" using wf1 unfolding col_def mat_def by auto
  qed
qed

lemma mat_eq_index:
  assumes wf1: "mat nr nc m1"
  and wf2: "mat nr nc m2"
  shows "(m1 = m2) = (\<forall> i < nc. \<forall> j < nr. m1 ! i ! j = m2 ! i ! j)" (is "?l = ?r")
proof 
  assume ?l thus ?r by auto
next
  assume ?r show ?l
  proof (simp only: mat_col_eq[OF wf1 wf2,symmetric], unfold col_def, intro allI impI)
    fix i
    assume i: "i < nc"
    show "m1 ! i = m2 ! i"
    proof (rule nth_equalityI)      
      show "length (m1 ! i)  = length (m2 ! i)" using wf1 wf2 i unfolding mat_def by (auto simp: vec_def)
    next
      from `?r` i show "\<forall> j < length (m1 ! i). m1 ! i ! j = m2 ! i ! j" using wf1 wf2 unfolding mat_def by (auto simp: vec_def)
    qed
  qed
qed

lemma vec_index_eq: 
  assumes wf1: "vec n v1"
  and wf2: "vec n v2"
  shows "(v1 = v2) = (\<forall> i < n. v1 ! i = v2 ! i)" (is "?l = ?r")
proof
  assume ?l thus ?r by auto
next
  assume ?r show ?l 
  proof (rule nth_equalityI)
    from wf1 wf2 show "length v1 = length v2" unfolding vec_def by simp
  next
    from `?r` wf1 show "\<forall> i < length v1. v1 ! i = v2 ! i" unfolding vec_def by simp
  qed
qed

lemma row_col: assumes "mat nr nc m"  
  and "i < nr" and "j < nc"
  shows "row m i ! j = col m j ! i"
using assms unfolding mat_def row_def col_def
  by auto

lemma mat_row_eq: 
  assumes wf1: "mat nr nc m1"
  and wf2: "mat nr nc m2"
  shows "(m1 = m2) = (\<forall> i < nr. row m1 i = row m2 i)" (is "?l = ?r")
proof 
  assume ?l thus ?r by auto
next
  assume ?r show ?l
  proof (rule nth_equalityI)
    show "length m1 = length m2" using wf1 wf2 unfolding mat_def by auto
  next
    show "\<forall> i < length m1. m1 ! i = m2 ! i"
    proof (intro allI impI)
      fix i
      assume i: "i < length m1"
      show "m1 ! i = m2 ! i"
      proof (rule nth_equalityI)
        show "length (m1 ! i) = length (m2 ! i)" using wf1 wf2 i unfolding mat_def by (auto simp: vec_def)
      next
        show "\<forall> j < length (m1 ! i). m1 ! i ! j = m2 ! i ! j" 
        proof (intro allI impI)
          fix j
          assume j: "j < length (m1 ! i)"
          from i j wf1 have i1: "i < nc" and j1: "j < nr" unfolding mat_def by (auto simp: vec_def)
          from `?r` j1 have "col m1 i ! j = col m2 i ! j"
            by (simp add: row_col[OF wf1 j1 i1, symmetric] row_col[OF wf2 j1 i1, symmetric])
          thus "m1 ! i ! j = m2 ! i ! j" unfolding col_def .
        qed
      qed
    qed
  qed
qed

lemma row_transpose_is_col:   assumes wf: "mat nr nc m"
  and i: "i < nc"
  shows "row (transpose nr m) i = col m i"
proof -
  have len: "length (row (transpose nr m) i) = length (col m i)"
    using transpose[OF wf]  wf i  unfolding row_def col_def mat_def by (auto simp: vec_def)
  show ?thesis 
  proof (rule nth_equalityI[OF len], intro allI impI)
    fix j
    assume "j < length (row (transpose nr m) i)"
    hence j: "j < nr" using transpose[OF wf] wf i unfolding row_def col_def mat_def by (auto simp: vec_def)
    show "row (transpose nr m) i ! j = col m i ! j"
      by (simp only: row_col[OF transpose[OF wf] i j],
        simp only: col_transpose_is_row[OF wf j],
        simp only: row_col[OF wf j i])
  qed
qed


lemma matT_vec_mult_to_scalar: 
  assumes "mat nr nc m"
  and "vec nr v"
  and "i < nc"
  shows "matT_vec_multI ze pl ti m v ! i = scalar_prodI ze pl ti (col m i) v"
unfolding matT_vec_multI_def using assms unfolding mat_def col_def by (auto simp: vec_def)

lemma mat_vec_mult_to_scalar: 
  assumes wf: "mat nr nc m"
  and wfV: "vec nc v"
  and i: "i < nr"
  shows "matT_vec_multI ze pl ti (transpose nr m) v ! i = scalar_prodI ze pl ti (row m i) v"
by (simp only:matT_vec_mult_to_scalar[OF transpose[OF wf] wfV i],
  simp only: col_transpose_is_row[OF wf i])

lemma mat_mult_to_scalar :
  assumes wf1: "mat nr n m1"
  and wf2: "mat n nc m2"
  and i: "i < nr"
  and j: "j < nc"
  shows "mat_multI ze pl ti nr m1 m2 ! j ! i = scalar_prodI ze pl ti (row m1 i) (col m2 j)"
proof -
  have jlen: "j < length m2" using wf2 j unfolding mat_def by auto
  have wfj: "vec n (m2 ! j)" using jlen j wf2 unfolding mat_def by auto
  show ?thesis 
    unfolding mat_multI_def
    by (simp add: jlen, simp only: mat_vec_mult_to_scalar[OF wf1 wfj i], unfold col_def, simp)
qed

lemma col_mat_mult_to_scalar :
  assumes wf1: "mat nr n m1"
  and wf2: "mat n nc m2"
  and j: "j < nc"
  shows "col (mat_multI ze pl ti nr m1 m2) j = map (\<lambda> i. scalar_prodI ze pl ti (row m1 i) (col m2 j)) [0 ..< nr]" (is "col ?l j = ?r")
proof - 
  have wf12: "mat nr nc ?l" by (rule mat_mult[OF wf1 wf2])
  have len: "length (col ?l j) = length ?r" and nr: "length (col ?l j) = nr" using wf1 wf2 wf12 j unfolding mat_def col_def by (auto simp: vec_def) 
  show ?thesis by (rule nth_equalityI[OF len], simp add: j nr, intro allI impI, unfold col_def, simp only:
    mat_mult_to_scalar[OF wf1 wf2 _ j], simp add: col_def)
qed

lemma row_mat_mult_to_scalar :
  assumes wf1: "mat nr n m1"
  and wf2: "mat n nc m2"
  and i: "i < nr"
  shows "row (mat_multI ze pl ti nr m1 m2) i = map (\<lambda> j. scalar_prodI ze pl ti (row m1 i) (col m2 j)) [0 ..< nc]" (is "row ?l i = ?r")
proof - 
  have wf12: "mat nr nc ?l" by (rule mat_mult[OF wf1 wf2])
  hence lenL: "length ?l = nc" unfolding mat_def by simp
  have len: "length (row ?l i) = length ?r" and nc: "length (row ?l i) = nc" using wf1 wf2 wf12 i unfolding mat_def row_def by (auto simp: vec_def) 
  show ?thesis by (rule nth_equalityI[OF len], simp add: i nc, intro allI impI, unfold row_def, simp add: lenL, simp only: 
    mat_mult_to_scalar[OF wf1 wf2 i], simp add: row_def)
qed

lemma scalar_prod_cons: 
  "scalar_prodI ze pl ti (a # as) (b # bs) = pl (ti a b) (scalar_prodI ze pl ti as bs)"
unfolding scalar_prodI_def by auto


lemma vec_plus_index: 
  assumes wf1: "vec nr v1"
  and wf2: "vec nr v2"
  and i: "i < nr"
  shows "vec_plusI pl v1 v2 ! i = pl (v1 ! i)  (v2 ! i)"
using wf1 wf2 i
unfolding vec_def vec_plusI_def
proof (induct v1 arbitrary: i v2 nr, simp)
  case (Cons a v11)
  from Cons obtain b v22 where v2: "v2 = b # v22" by (cases v2, auto)
  from v2 Cons obtain nrr where nr: "nr = Suc nrr" by (force)
  from Cons show ?case
    by (cases i, simp add: v2, auto simp: v2 nr)
qed

lemma mat_map_index: assumes wf: "mat nr nc m" and i: "i < nc" and j: "j < nr" 
  shows "mat_map f m ! i ! j = f (m ! i ! j)"
proof -
  from wf i have i: "i < length m" unfolding mat_def by auto
  with wf j have j: "j < length (m ! i)" unfolding mat_def by (auto simp: vec_def)
  have "mat_map f m ! i ! j = map (map f) m ! i ! j" unfolding mat_map_def vec_map_def by auto
  also have "\<dots> = map f (m ! i) ! j" using i by auto
  also have "\<dots> = f (m ! i ! j)" using j by auto
  finally show ?thesis .
qed

lemma mat_max0_index: assumes wf: "mat nr nc m" and i: "i < nc" and j: "j < nr" 
  shows "mat_max0 m ! i ! j = max0 (m ! i ! j)"
unfolding mat_max0_def using assms by (rule mat_map_index)


lemma mat_plus_index: 
  assumes wf1: "mat nr nc m1"
  and wf2: "mat nr nc m2"
  and i: "i < nc"
  and j: "j < nr"
  shows "mat_plusI pl m1 m2 ! i ! j = pl (m1 ! i ! j) (m2 ! i ! j)"
using wf1 wf2 i
unfolding mat_plusI_def mat_def 
proof (simp, induct m1 arbitrary: m2 i nc, simp)
  case (Cons v1 m11)
  from Cons obtain v2 m22 where m2: "m2 = v2 # m22" by (cases m2, auto)
  from m2 Cons obtain ncc where nc: "nc = Suc ncc" by force
  show ?case
  proof (cases i, simp add: m2, rule vec_plus_index[where nr = nr], (auto simp: Cons j m2)[3])
    case (Suc ii)
    with Cons show ?thesis using m2 nc by auto
  qed
qed

lemma col_mat_plus: assumes wf1: "mat nr nc m1"
  and wf2: "mat nr nc m2"
  and i: "i < nc"
  shows "col (mat_plusI pl m1 m2) i = vec_plusI pl (col m1 i) (col m2 i)"
using assms
unfolding mat_plusI_def col_def mat_def
proof (induct m1 arbitrary: m2 nc i, simp)
  case (Cons v m1)
  from Cons obtain v2 m22 where m2: "m2 = v2 # m22" by (cases m2, auto)
  from m2 Cons obtain ncc where nc: "nc = Suc ncc" by force
  show ?case
  proof (cases i, simp add: m2)
    case (Suc ii)
    with Cons show ?thesis using m2 nc by auto
  qed
qed

lemma transpose_index: assumes wf: "mat nr nc m"
  and i: "i < nr"
  and j: "j < nc"
  shows "transpose nr m ! i ! j = m ! j ! i"
proof -
  have "transpose nr m ! i ! j = col (transpose nr m) i ! j" unfolding col_def by simp
  also have "\<dots> = row m i ! j" using col_transpose_is_row[OF wf i] by simp
  also have "\<dots> = m ! j ! i" unfolding row_def using wf j unfolding mat_def by (auto simp: vec_def)
  finally show ?thesis . 
qed

lemma transpose_mat_plus: assumes wf1: "mat nr nc m1"
  and wf2: "mat nr nc m2"
  shows "transpose nr (mat_plusI pl m1 m2) = mat_plusI pl (transpose nr m1) (transpose nr m2)"
proof - 
  let ?m12 = "mat_plusI pl m1 m2"
  let ?t1 = "transpose nr m1"
  let ?t2 = "transpose nr m2"
  from mat_plus[OF wf1 wf2] have wf12: "mat nr nc ?m12" .
  from transpose[OF wf1] have wft1: "mat nc nr ?t1" .
  from transpose[OF wf2] have wft2: "mat nc nr ?t2" .
  show ?thesis 
  proof (simp only: mat_eq_index[OF transpose[OF wf12] mat_plus[OF wft1 wft2]], intro allI impI)
    fix i j
    assume i: "i < nr" and j: "j < nc"
    show "transpose nr ?m12 ! i ! j = mat_plusI pl ?t1 ?t2 ! i ! j"      
      by (simp only: transpose_index[OF wf12 i j],
        simp only: mat_plus_index[OF wft1 wft2 i j],
        simp only: mat_plus_index[OF wf1 wf2 j i],
        simp only: transpose_index[OF wf1 i j],
        simp only: transpose_index[OF wf2 i j])
  qed
qed
      

lemma row_mat_plus: assumes wf1: "mat nr nc m1"
  and wf2: "mat nr nc m2"
  and i: "i < nr"
  shows "row (mat_plusI pl m1 m2) i = vec_plusI pl (row m1 i) (row m2 i)"
  by (
    simp only: col_transpose_is_row[OF mat_plus[OF wf1 wf2] i, symmetric], 
    simp only: transpose_mat_plus[OF wf1 wf2],
    simp only: col_mat_plus[OF transpose[OF wf1] transpose[OF wf2] i],
    simp only: col_transpose_is_row[OF wf1 i],
    simp only: col_transpose_is_row[OF wf2 i])


lemma col_mat1: assumes "i < nr"
  shows "col (mat1I ze on nr) i = vec1I ze on nr i"
unfolding mat1I_def col_def using assms by auto


lemma mat1_index: assumes i: "i < n" and j: "j < n"
  shows "mat1I ze on n ! i ! j = (if i = j then on else ze)"
  by (simp add: col_mat1[OF i, simplified col_def] vec1_index[OF i j])

lemma transpose_mat1: "transpose nr (mat1I ze on nr) = (mat1I ze on nr)"
proof (simp only: mat_eq_index[OF transpose[OF mat1] mat1], intro impI allI)
  fix i j
  assume i: "i < nr" and j: "j < nr"
  let ?I = "mat1I ze on nr"
  show "transpose nr ?I ! i ! j = ?I ! i ! j"
    by  (simp only: col_def[symmetric], 
      simp only: col_mat1[OF i],
      simp only: row_col[OF transpose[OF mat1] j i,symmetric],
      simp only: row_transpose_is_col[OF mat1 j],
      simp only: col_mat1[OF j],
      simp only: vec1_index[OF i j],
      simp only: vec1_index[OF j i], simp)
qed

lemma row_mat1: assumes i: "i < nr"
  shows "row (mat1I ze on nr) i = vec1I ze on nr i"
by (simp only: col_transpose_is_row[OF mat1 i, symmetric],
  simp only: transpose_mat1,
  simp only: col_mat1[OF i])

lemma vec_comp_all_index: assumes "vec nr v1" 
  and "vec nr v2"
  shows "vec_comp_all rel v1 v2 = (\<forall> i < nr. rel (v1 ! i) (v2 ! i))"
using assms
unfolding vec_def vec_comp_all_def list_all_iff
proof (induct nr arbitrary: v1 v2)
  case (Suc nrr)
  from Suc obtain a1 w1 where v1: "v1 = a1 # w1" and lw1: "length w1 = nrr" by (cases v1, auto)
  from Suc obtain a2 w2 where v2: "v2 = a2 # w2" and lw2: "length w2 = nrr" by (cases v2, auto)
  have rec: "(\<forall> a \<in> set (zip w1 w2). split rel a) = (\<forall> i < nrr. rel (w1 ! i) (w2 ! i))"
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
      show "rel (v1 ! i) (v2 ! i)"
        using `?l` v1 v2 i
        by (cases i, auto simp: rec)
    qed
  qed
qed simp

lemma vec_ge_index: assumes "vec nr v1" 
  and "vec nr v2"
  shows "vec_ge v1 v2 = (\<forall> i < nr. ge (v1 ! i) (v2 ! i))"
using assms
unfolding vec_ge_def by (rule vec_comp_all_index) 

lemma vec_pre_gt_index: assumes "vec nr v1" 
  and "vec nr v2"
  shows "vec_pre_gtI gt v1 v2 = (\<exists> i < nr. gt (v1 ! i) (v2 ! i))"
using assms[simplified vec_def, symmetric]
by (simp only: Not_eq_iff[symmetric, of "vec_pre_gtI gt v1 v2"], unfold vec_pre_gtI_def, simp add: set_zip, auto) 
    
lemma mat_comp_all_index: assumes "mat nr nc m1" 
  and "mat nr nc m2"
  shows "mat_comp_all rel m1 m2 = (\<forall> i < nc. \<forall> j < nr. rel (m1 ! i ! j) (m2 ! i ! j))"
using assms
unfolding mat_def mat_comp_all_def list_all_iff
proof (induct nc arbitrary: m1 m2)
  case (Suc ncc)
  from Suc obtain v1 mm1 where m1: "m1 = v1 # mm1" and lm1: "length mm1 = ncc \<and> (\<forall> a \<in> set mm1. vec nr a)" by (cases m1, auto)
  from Suc obtain v2 mm2 where m2: "m2 = v2 # mm2" and lm2: "length mm2 = ncc \<and> (\<forall> a \<in> set mm2. vec nr a)" by (cases m2, auto)
  from Suc m1 have wf1: "vec nr v1" by simp
  from Suc m2 have wf2: "vec nr v2" by simp
  have rec: "(\<forall> a \<in> set (zip mm1 mm2). split (vec_comp_all rel) a) = (\<forall> i < ncc. \<forall> j < nr. rel (mm1 ! i ! j) (mm2 ! i ! j))"
    by (rule Suc, auto simp: Suc lm1 lm2)
  show ?case (is "?l = ?r")
  proof (rule iffI)
    assume ?r
    thus ?l using m1 m2 lm1 lm2 rec vec_comp_all_index[OF wf1 wf2] by auto
  next
    assume ?l
    hence ge: "vec_comp_all rel v1 v2" and "\<forall> a \<in> set (zip mm1 mm2). split (vec_comp_all rel) a" using m1 m2 by auto
    with rec have ge2: " (\<forall>i<ncc. \<forall>j<nr. rel (mm1 ! i ! j) (mm2 ! i ! j))" by simp
    show ?r
    proof (rule allI, intro impI)
      fix i 
      assume i: "i < Suc ncc" 
      show "\<forall> j < nr. rel (m1 ! i ! j) (m2 ! i ! j)"
      proof (cases i, simp add: m1 m2, simp only: vec_comp_all_index[OF wf1 wf2, symmetric], rule ge)
        case (Suc ii)   
        with i have " ii < ncc" by simp
        with Suc 
        show ?thesis by (simp add: m1 m2, simp add: ge2)
      qed
    qed
  qed
qed simp

lemma mat_ge_index: assumes "mat nr nc m1" 
  and "mat nr nc m2"
  shows "mat_ge m1 m2 = (\<forall> i < nc. \<forall> j < nr. ge (m1 ! i ! j) (m2 ! i ! j))"
using assms
unfolding mat_ge_def by (rule mat_comp_all_index)

lemma mat_pre_gt_index: assumes "mat nr nc m1"
  and "mat nr nc m2"
  shows "mat_pre_gtI gt m1 m2 = (\<exists> i < nc. \<exists> j < nr. gt (m1 ! i ! j) (m2 ! i ! j))"
proof -
  from assms have l1: "nc = length m1" and l2: "length m2 = length m1" 
    and vl1: "\<forall> i < nc. vec nr (m1 ! i)" and vl2: "\<forall> i < nc. vec nr (m2 ! i)" unfolding mat_def by auto
  let ?l = "\<lambda> i. \<not> vec_pre_gtI gt (m1 ! i) (m2 ! i)"
  let ?r = "\<lambda> i. \<forall> j < nr. \<not> gt (m1 ! i ! j) (m2 ! i ! j)"
  have lr: "\<forall> i < nc. ?l i = ?r i"
  proof (intro allI impI)
    fix i
    assume i: "i < nc"
    show "?l i = ?r i" using vec_pre_gt_index[OF mp[OF spec[OF vl1] i] mp[OF spec[OF vl2] i]] by auto
  qed     
  show ?thesis
  proof (simp only: Not_eq_iff[symmetric, of "mat_pre_gtI gt m1 m2"], unfold mat_pre_gtI_def list_ex_iff set_zip l2 min_max.inf_idem l1[symmetric])
    show "(\<not> (\<exists> (x,y) \<in> {(m1 ! i, m2 ! i) | i. i < nc}. vec_pre_gtI gt x y)) = (\<not> (\<exists> i<nc. \<exists> j<nr. gt (m1 ! i ! j) (m2 ! i ! j)))"
      using lr by auto
  qed
qed

lemma sub_mat_index:
  assumes wf: "mat nr nc m"
  and sr: "sr \<le> nr"
  and sc: "sc \<le> nc"
  and j: "j < sr"
  and i: "i < sc"
  shows "sub_mat sr sc m ! i ! j = m ! i ! j"
proof -
  from assms have im: "i < length m" unfolding mat_def by auto
  from assms have jm: "j < length (m ! i)" unfolding mat_def by (auto simp: vec_def)
  have "sub_mat sr sc m ! i ! j = map (take sr) (take sc m) ! i ! j"
    unfolding sub_mat_def sub_vec_def by auto
  also have "\<dots> = take sr (m ! i) ! j" using i im by auto
  also have "\<dots> = m ! i ! j" using j jm by auto
  finally show ?thesis .
qed

lemma mat_gt_index: assumes wf1: "mat n n m1"
  and wf2: "mat n n m2"
  and sd: "sd \<le> n"
  shows "mat_gtI gt sd m1 m2 = (mat_ge m1 m2 \<and> (\<exists> i < sd. \<exists> j < sd. gt (m1 ! i ! j) (m2 ! i ! j)))"
proof -
  have id: "mat_pre_gtI gt (sub_mat sd sd m1) (sub_mat sd sd m2) = (\<exists> i < sd. \<exists> j < sd. gt (m1 ! i ! j) (m2 ! i ! j))" (is "?l = ?r")
  proof -
    have "?l = (\<exists> i < sd. \<exists> j < sd. gt (sub_mat sd sd m1 ! i ! j) (sub_mat sd sd m2 ! i ! j))"
      by (simp only: mat_pre_gt_index[OF sub_mat[OF wf1 sd sd] sub_mat[OF wf2 sd sd]])
    also have "\<dots> = ?r" by (simp only: Not_eq_iff[symmetric, of _ ?r], auto simp: sub_mat_index[OF wf1 sd sd] sub_mat_index[OF wf2 sd sd])
    finally show "?l = ?r" .
  qed
  thus ?thesis unfolding mat_gtI_def by auto
qed


lemma mat_mono_index: assumes wf: "mat n n m"
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



subsection {* lemmas requiring properties of plus, times, ... *}

context plus
begin

abbreviation vec_plus :: "'a vec \<Rightarrow> 'a vec \<Rightarrow> 'a vec"
where "vec_plus \<equiv> vec_plusI plus"

abbreviation mat_plus :: "'a mat \<Rightarrow> 'a mat \<Rightarrow> 'a mat"
where "mat_plus \<equiv> mat_plusI plus"
end

context semigroup_add
begin
lemma vec_plus_assoc: assumes u: "vec nr u" and v: "vec nr v" and w: "vec nr w"
 shows "vec_plus u (vec_plus v w) = vec_plus (vec_plus u v) w" (is "?l = ?r")
proof -
  from v w have vw: "vec nr (vec_plus v w)" by (simp add: vec_plus)
  from u v have uv: "vec nr (vec_plus u v)" by (simp add: vec_plus)
  from assms have l: "vec nr ?l" by (simp add: vec_plus)
  from assms have r: "vec nr ?r" by (simp add: vec_plus)
  show ?thesis by (simp only: vec_index_eq[OF l r], intro allI impI,
    simp only: vec_plus_index[OF u vw],
    simp only: vec_plus_index[OF v w],
    simp only: vec_plus_index[OF uv w],
    simp only: vec_plus_index[OF u v],
    simp only: add_assoc)
qed

lemma mat_plus_assoc: assumes wf_1: "mat nr nc m1" and wf_2: "mat nr nc m2" and wf_3: "mat nr nc m3"
  shows "mat_plus m1 (mat_plus m2 m3) = mat_plus (mat_plus m1 m2) m3" (is "?l = ?r")
proof -
  from wf_2 wf_3 have wf_23: "mat nr nc (mat_plus m2 m3)" by (simp add: mat_plus)
  from wf_1 wf_2 have wf_12: "mat nr nc (mat_plus m1 m2)" by (simp add: mat_plus)
  from assms have wf_l: "mat nr nc ?l" by (simp add: mat_plus)
  from assms have wf_r: "mat nr nc ?r" by (simp add: mat_plus)
  show ?thesis by (simp only: mat_eq_index[OF wf_l wf_r], intro allI impI,
    simp only: mat_plus_index[OF wf_1 wf_23],
    simp only: mat_plus_index[OF wf_2 wf_3],
    simp only: mat_plus_index[OF wf_12 wf_3],
    simp only: mat_plus_index[OF wf_1 wf_2],
    simp only: add_assoc)
qed
end

context ab_semigroup_add
begin
lemma vec_plus_comm: "vec_plus x y = vec_plus y x"
unfolding vec_plusI_def
proof (induct x arbitrary: y)
  case (Cons a x)
  thus ?case 
    by (cases y, auto simp: add_commute) 
qed simp


lemma mat_plus_comm: "mat_plus m1 m2 = mat_plus m2 m1"
unfolding mat_plusI_def
proof (induct m1 arbitrary: m2)
  case (Cons v m1) note oCons = this
  thus ?case
  proof (cases m2)
    case (Cons w m2a)
    hence "mat_plus (v # m1) m2 = vec_plus v w # mat_plus m1 m2a" by (auto simp: mat_plusI_def)
    also have "\<dots> = vec_plus w v # mat_plus m1 m2a" using vec_plus_comm by auto
    finally show ?thesis using Cons oCons by (auto simp: mat_plusI_def)
  qed simp
qed simp
end

context zero
begin
abbreviation vec0 :: "nat \<Rightarrow> 'a vec"
where "vec0 \<equiv> vec0I zero"

abbreviation mat0 :: "nat \<Rightarrow> nat \<Rightarrow> 'a mat"
where "mat0 \<equiv> mat0I zero"
end

context monoid_add
begin
lemma vec0_plus[simp]: assumes "vec nr u" shows "vec_plus (vec0 nr) u = u"
using assms
unfolding vec_def vec_plusI_def vec0I_def
proof (induct nr arbitrary: u)
 case (Suc nn) thus ?case by (cases u, auto)
qed simp

lemma plus_vec0[simp]: assumes "vec nr u" shows "vec_plus u (vec0 nr) = u"
using assms
unfolding vec_def vec_plusI_def vec0I_def
proof (induct nr arbitrary: u)
 case (Suc nn) thus ?case by (cases u, auto)
qed simp

lemma plus_mat0[simp]: assumes "mat nr nc m" shows "mat_plus m (mat0 nr nc) = m"
using assms 
unfolding mat_def 
proof (induct nc arbitrary: m)
  case (Suc nn) 
  thus ?case 
  proof (cases m)
    case (Cons v mm)
    with Suc have wf: "vec nr v" by auto
    from Cons Suc have "mat_plus m (mat0 nr (Suc nn)) = vec_plus v (vec0 nr) # mat_plus mm (mat0 nr nn)" by (auto simp: mat_plusI_def mat0I_def)
    also have "\<dots> = vec_plus v (vec0 nr) # mm" using Suc Cons by auto
    also have "\<dots> = v # mm" by (simp only: plus_vec0 wf)
    finally show ?thesis using Cons by auto
  qed simp
qed (simp add: mat_plusI_def mat0I_def)
end

context semiring_0
begin
abbreviation scalar_prod :: "'a vec \<Rightarrow> 'a vec \<Rightarrow> 'a"
where "scalar_prod \<equiv> scalar_prodI zero plus times"

abbreviation mat_mult :: "nat \<Rightarrow> 'a mat \<Rightarrow> 'a mat \<Rightarrow> 'a mat"
where "mat_mult \<equiv> mat_multI zero plus times"


lemma scalar_prod_last: assumes "length v1 = length v2" 
  shows "scalar_prod (v1 @ [x1]) (v2 @ [x2]) = x1 * x2 + scalar_prod v1 v2"
using assms 
proof (induct v1 arbitrary: v2)
  case (Cons y1 w1)
  from Cons(2) obtain y2 w2 where v2: "v2 = Cons y2 w2" and len: "length w1 = length w2" by (cases v2, auto)
  from Cons(1)[OF len] have rec: "scalar_prod (w1 @ [x1]) (w2 @ [x2]) = x1 * x2 + scalar_prod w1 w2" .
  have "scalar_prod ((y1 # w1) @ [x1]) (v2 @ [x2]) = 
    (y1 * y2 + x1 * x2) + scalar_prod w1 w2" by (simp add: scalar_prod_cons v2 rec add_assoc)
  also have "\<dots> = (x1 * x2 + y1 * y2) + scalar_prod w1 w2" using add_commute[of "x1 * x2"] by simp
  also have "\<dots> = x1 * x2 + (scalar_prod (y1 # w1) v2)" by (simp add: add_assoc scalar_prod_cons v2)
  finally show ?case .
qed (simp add: scalar_prodI_def)

lemma scalar_product_assoc: 
  assumes wfm: "mat nr nc m"
  and wfr: "vec nr r"
  and wfc: "vec nc c"
  shows "scalar_prod (map (\<lambda>k. scalar_prod r (col m k)) [0..<nc]) c = scalar_prod r (map (\<lambda>k. scalar_prod (row m k) c) [0..<nr])"
using wfm wfc
unfolding col_def 
proof (induct m arbitrary: nc c)
  case Nil
  hence nc: "nc = 0" unfolding mat_def by (auto)
  from wfr have nr: "nr = length r" unfolding vec_def by auto
  let ?term = "\<lambda> r :: 'a vec. zip r (map (\<lambda> k. zero) [0..<length r])"
  let ?fun = "\<lambda> (x,y). plus (times x y)"
  have "foldr ?fun (?term r) zero = zero" 
  proof (induct r, simp)
    case (Cons d r)
    have "foldr ?fun (?term (d # r)) zero = foldr ?fun ( (d,zero) # ?term r) zero" by (simp only: map_replicate_trivial, simp)
    also have "\<dots> = zero" using Cons by simp
    finally show ?case .
  qed
  hence "zero = foldr ?fun (zip r (map (\<lambda> k. zero) [0..<nr])) zero" by (simp add: nr)
  with Nil nc show ?case 
    by (simp add: scalar_prodI_def row_def)
next
  case (Cons v m)
  from this obtain ncc where nc: "nc = Suc ncc" and wf: "mat nr ncc m" unfolding mat_def by (auto simp: vec_def)
  from nc `vec nc c` obtain a cc where c: "c = a # cc" and wfc: "vec ncc cc" unfolding vec_def by (cases c, auto)
  have rec: "scalar_prod (map (\<lambda> k. scalar_prod r (m ! k)) [0..<ncc]) cc = scalar_prod r (map (\<lambda> k. scalar_prod (row m k) cc) [0..<nr])"
    by (rule Cons, rule wf, rule wfc)
  have id: "map (\<lambda>k. scalar_prod r ((v # m) ! k)) [0..<Suc ncc] = scalar_prod r v # map (\<lambda> k. scalar_prod r (m ! k)) [0..<ncc]" by (induct ncc, auto)    
  from wfr have nr: "nr = length r" unfolding vec_def by auto
  with Cons have v: "length v = length r" unfolding mat_def by (auto simp: vec_def)
  have "\<forall> i < nr. vec ncc (row m i)" by (intro allI impI, rule row[OF wf], simp)
  obtain tm where tm: "tm = transpose nr m" by auto
  hence idk: "\<forall> k < length r. row m k = tm ! k" using col_transpose_is_row[OF wf] unfolding col_def by (auto simp: nr)
  hence idtm1: "map (\<lambda>k. scalar_prod (row m k) cc) [0..<length r] = map (\<lambda>k. scalar_prod (tm ! k) cc) [0..<length r]" 
    and idtm2: "map (\<lambda>k. plus (times (v ! k) a) (scalar_prod (row m k) cc)) [0..<length r] = map (\<lambda>k. plus (times (v ! k) a) (scalar_prod (tm ! k) cc)) [0..<length r]" by auto
  from tm transpose[OF wf] have "mat ncc nr tm" by simp
  with nr have "length tm = length r" and  "(\<forall> i < length r. length (tm ! i) = ncc)" unfolding mat_def by (auto simp: vec_def) 
  with v have main: "plus (times (scalar_prod r v) a) (scalar_prod r (map (\<lambda>k. scalar_prod (tm ! k) cc) [0..<length r])) =
    scalar_prod r (map (\<lambda>k. plus (times (v ! k) a) (scalar_prod (tm ! k) cc)) [0..<length r])" 
  proof (induct r arbitrary: v tm)
    case Nil
    thus ?case by (auto simp: scalar_prodI_def row_def)
  next
    case (Cons b r)
    from this obtain c vv where v: "v = c # vv" and vvlen: "length vv = length r" by (cases v, auto)
    from Cons obtain u mm where tm: "tm = u # mm" and mmlen: "length mm = length r"  by (cases tm, auto)
    from Cons tm have argLen: "\<forall> i < length r. length (mm ! i) = ncc" by auto
    have rec: "plus (times (scalar_prod r vv) a) (scalar_prod r (map (\<lambda>k. scalar_prod (mm ! k) cc) [0..<length r])) =
     scalar_prod r (map (\<lambda>k. plus (times (vv ! k) a) (scalar_prod (mm ! k) cc)) [0..<length r])" 
      (is "plus (times ?rv a) ?recl = ?recr")
      by (rule Cons, auto simp: vvlen mmlen argLen)
    have id: "map (\<lambda>k. scalar_prod ((u # mm) ! k) cc) [0..<length (b # r)] = scalar_prod u cc # map (\<lambda>k. scalar_prod (mm ! k) cc) [0..<length r]" 
      by (simp, induct r, auto)
    have id2: "map (\<lambda>k. plus (times ((c # vv) ! k) a) (scalar_prod ((u # mm) ! k) cc)) [0..<length (b # r)] = 
               (plus (times c a) (scalar_prod u cc)) #
               map (\<lambda>k. plus (times (vv ! k) a) (scalar_prod (mm ! k) cc)) [0..<length r]" 
      by (simp, induct r, auto)
    show ?case proof (simp only: v tm, simp only: id, simp only: id2, simp only: scalar_prod_cons)
      let ?uc = "scalar_prod u cc"
      let ?bca = "times (times b c) a"
      have "plus (times (plus (times b c) ?rv) a) (plus (times b ?uc) ?recl) = plus (plus ?bca (times ?rv a)) (plus (times b ?uc) ?recl)" 
        by (simp add: left_distrib)
      also have "\<dots> = plus (plus ?bca (times ?rv a)) (plus ?recl (times b ?uc))" by (simp add: add_commute)
      also have "\<dots> = plus ?bca (plus (plus (times ?rv a) ?recl) (times b ?uc))" by (simp add: add_assoc)
      also have "\<dots> = plus ?bca (plus ?recr (times b ?uc))" by (simp only: rec)
      also have "\<dots> = plus ?bca (plus (times b ?uc) ?recr)" by (simp add: add_commute)
      also have "\<dots> = plus (times b (plus (times c a) ?uc)) ?recr" by (simp add: right_distrib mult_assoc add_assoc)
      finally show "plus (times (plus (times b c) ?rv) a) (plus (times b ?uc) ?recl) = plus (times b (plus (times c a) ?uc)) ?recr" .
    qed
  qed
  show ?case 
    by (simp only: c scalar_prod_cons, simp only: nc, simp only: id, simp only: scalar_prod_cons, simp only: rec, simp only: nr, simp only: idtm1 idtm2, simp only: main, simp only: idtm2[symmetric], simp add: row_def scalar_prod_cons)
qed


lemma mat_mult_assoc: 
  assumes wf1: "mat nr n1 m1"
  and wf2: "mat n1 n2 m2"
  and wf3: "mat n2 nc m3"
  shows "mat_mult nr (mat_mult nr m1 m2) m3 = mat_mult nr m1 (mat_mult n1 m2 m3)" (is "?m12_3 = ?m1_23")
proof -
  let ?m12 = "mat_mult nr m1 m2"
  let ?m23 = "mat_mult n1 m2 m3"
  from wf1 wf2 have wf12: "mat nr n2 ?m12" by (rule mat_mult)
  from wf2 wf3 have wf23: "mat n1 nc ?m23" by (rule mat_mult)
  from wf1 wf23 have wf1_23: "mat nr nc ?m1_23" by (rule mat_mult)
  from wf12 wf3 have wf12_3: "mat nr nc ?m12_3" by (rule mat_mult)
  show ?thesis
  proof (simp only: mat_col_eq[OF wf12_3 wf1_23, symmetric], unfold col_def, intro allI impI)
    fix i
    assume i: "i < nc"
    with wf1_23 wf12_3 wf3 have len: "length (?m12_3 ! i) = length (?m1_23 ! i)" and ilen: "i < length m3" unfolding mat_def by (auto simp: vec_def)
    show "?m12_3 ! i = ?m1_23 ! i"
    proof (rule nth_equalityI[OF len], intro allI impI)
      fix j
      assume jlen: "j < length (?m12_3 ! i)"
      with wf12_3 i have j: "j < nr" unfolding mat_def by (auto simp: vec_def)      
      show "?m12_3 ! i ! j = ?m1_23 ! i ! j"
        by (simp only: mat_mult_to_scalar[OF wf12 wf3 j i],
             simp only: mat_mult_to_scalar[OF wf1 wf23 j i], 
             simp only: row_mat_mult_to_scalar[OF wf1 wf2 j],
             simp only: col_mat_mult_to_scalar[OF wf2 wf3 i], 
             simp only: scalar_product_assoc[OF wf2 row[OF wf1 j] col[OF wf3 i]])
    qed
  qed
qed

lemma mat_mult_assoc_n:  
  assumes wf1: "mat n n m1"
  and wf2: "mat n n m2"
  and wf3: "mat n n m3"
  shows "mat_mult n (mat_mult n m1 m2) m3 = mat_mult n m1 (mat_mult n m2 m3)"
using assms
 by (rule mat_mult_assoc)


lemma scalar_left_zero: "scalar_prod (vec0 nn) v = zero"
  unfolding vec0I_def scalar_prodI_def
proof (induct nn arbitrary: v)
  case (Suc m)
  thus ?case by (cases v, auto)
qed simp

lemma scalar_right_zero: "scalar_prod v (vec0 nn) = zero"
  unfolding vec0I_def scalar_prodI_def
proof (induct v arbitrary: nn)
  case (Cons a vv)
  thus ?case by (cases nn, auto)
qed simp

lemma mat0_mult_left: assumes wf: "mat nc ncc m"
  shows "mat_mult nr (mat0 nr nc) m = (mat0 nr ncc)"
proof (simp only: mat_eq_index[OF mat_mult[OF mat0 wf] mat0], intro allI impI)
  fix i j
  assume i: "i < ncc" and j: "j < nr"
  show "mat_mult nr (mat0 nr nc) m ! i ! j = mat0 nr ncc ! i ! j"
  by (simp only: mat_mult_to_scalar[OF mat0 wf j i], 
         simp only: mat0_index[OF i j], 
         simp only: mat0_row[OF j],
         simp only: scalar_left_zero)
qed


lemma mat0_mult_right: assumes wf: "mat nr nc m"
  shows "mat_mult nr m (mat0 nc ncc) = (mat0 nr ncc)"
proof (simp only: mat_eq_index[OF mat_mult[OF wf mat0] mat0], intro allI impI)
  fix i j
  assume i: "i < ncc" and j: "j < nr"
  show "mat_mult nr m (mat0 nc ncc) ! i ! j = mat0 nr ncc ! i ! j"
    by (simp only: mat_mult_to_scalar[OF wf mat0 j i],
         simp only: mat0_index[OF i j],
         simp only: mat0_col[OF i],
         simp only: scalar_right_zero)
qed

lemma scalar_vec_plus_distrib_right: 
  assumes wf1: "vec nr u"
  assumes wf2: "vec nr v"
  assumes wf3: "vec nr w"
  shows "scalar_prod u (vec_plus v w) = plus (scalar_prod u v) (scalar_prod u w)"
using assms
unfolding vec_def scalar_prodI_def vec_plusI_def
proof (induct nr arbitrary: u v w)
  case (Suc n)
  from Suc obtain a uu where u: "u = a # uu" by (cases u, auto)
  from Suc obtain b vv where v: "v = b # vv" by (cases v, auto)
  from Suc obtain c ww where w: "w = c # ww" by (cases w, auto)
  from Suc u v w have lu: "length uu = n" and lv: "length vv = n" and lw: "length ww = n" by auto
  show ?case by (simp only: u v w, simp, simp only: Suc(1)[OF lu lv lw], simp add: add_commute[of _ "times a c"] right_distrib add_assoc[symmetric])
qed simp

lemma scalar_vec_plus_distrib_left: 
  assumes wf1: "vec nr u"
  assumes wf2: "vec nr v"
  assumes wf3: "vec nr w"
  shows "scalar_prod (vec_plus u v) w = plus (scalar_prod u w) (scalar_prod v w)"
using assms
unfolding vec_def scalar_prodI_def vec_plusI_def
proof (induct nr arbitrary: u v w)
  case (Suc n)
  from Suc obtain a uu where u: "u = a # uu" by (cases u, auto)
  from Suc obtain b vv where v: "v = b # vv" by (cases v, auto)
  from Suc obtain c ww where w: "w = c # ww" by (cases w, auto)
  from Suc u v w have lu: "length uu = n" and lv: "length vv = n" and lw: "length ww = n" by auto
  show ?case by (simp only: u v w, simp, simp only: Suc(1)[OF lu lv lw], simp add: add_commute[of _ "times b c"] left_distrib add_assoc[symmetric])
qed simp

lemma mat_mult_plus_distrib_right: 
  assumes wf1: "mat nr nc m1"
  and wf2: "mat nc ncc m2"
  and wf3: "mat nc ncc m3"
  shows "mat_mult nr m1 (mat_plus m2 m3) = mat_plus (mat_mult nr m1 m2) (mat_mult nr m1 m3)" (is "mat_mult nr m1 ?m23 = mat_plus ?m12 ?m13")
proof -
  let ?m1_23 = "mat_mult nr m1 ?m23"
  let ?m12_13 = "mat_plus ?m12 ?m13"
  from mat_plus[OF wf2 wf3] have wf23: "mat nc ncc ?m23" .
  from mat_mult[OF wf1 wf2] have wf12: "mat nr ncc ?m12" .
  from mat_mult[OF wf1 wf3] have wf13: "mat nr ncc ?m13" .
  from mat_mult[OF wf1 wf23] have wf1_23: "mat nr ncc ?m1_23" .
  from mat_plus[OF wf12 wf13] have wf12_13: "mat nr ncc ?m12_13" .
  show ?thesis 
  proof (simp only: mat_eq_index[OF wf1_23 wf12_13], intro impI allI)
    fix i j
    assume i: "i < ncc" and j: "j < nr"
    show "?m1_23 ! i ! j = ?m12_13 ! i ! j"
      by (simp only: mat_mult_to_scalar[OF wf1 wf23 j i],
           simp only: mat_plus_index[OF wf12 wf13 i j],
           simp only: mat_mult_to_scalar[OF wf1 wf2 j i],
           simp only: mat_mult_to_scalar[OF wf1 wf3 j i],
           simp only: col_mat_plus[OF wf2 wf3 i],
        rule scalar_vec_plus_distrib_right[OF row[OF wf1 j] col[OF wf2 i] col[OF wf3 i]])
  qed
qed

lemma mat_mult_plus_distrib_left: 
  assumes wf1: "mat nr nc m1"
  and wf2: "mat nr nc m2"
  and wf3: "mat nc ncc m3"
  shows "mat_mult nr (mat_plus m1 m2) m3 = mat_plus (mat_mult nr m1 m3) (mat_mult nr m2 m3)" (is "mat_mult nr ?m12 _ = mat_plus ?m13 ?m23")
proof -
  let ?m12_3 = "mat_mult nr ?m12 m3"
  let ?m13_23 = "mat_plus ?m13 ?m23"
  from mat_plus[OF wf1 wf2] have wf12: "mat nr nc ?m12" .
  from mat_mult[OF wf1 wf3] have wf13: "mat nr ncc ?m13" .
  from mat_mult[OF wf2 wf3] have wf23: "mat nr ncc ?m23" .
  from mat_mult[OF wf12 wf3] have wf12_3: "mat nr ncc ?m12_3" .
  from mat_plus[OF wf13 wf23] have wf13_23: "mat nr ncc ?m13_23" .
  show ?thesis 
  proof (simp only: mat_eq_index[OF wf12_3 wf13_23], intro impI allI)
    fix i j
    assume i: "i < ncc" and j: "j < nr"
    show "?m12_3 ! i ! j = ?m13_23 ! i ! j"
      by (simp only: mat_mult_to_scalar[OF wf12 wf3 j i],
           simp only: mat_plus_index[OF wf13 wf23 i j],
           simp only: mat_mult_to_scalar[OF wf1 wf3 j i],
           simp only: mat_mult_to_scalar[OF wf2 wf3 j i],
           simp only: row_mat_plus[OF wf1 wf2 j],
           rule scalar_vec_plus_distrib_left[OF row[OF wf1 j] row[OF wf2 j] col[OF wf3 i]])
  qed
qed
end

context semiring_1
begin
abbreviation vec1 :: "nat \<Rightarrow> nat \<Rightarrow> 'a vec"
where "vec1 \<equiv> vec1I zero one"

abbreviation mat1 :: "nat \<Rightarrow> 'a mat"
where "mat1 \<equiv> mat1I zero one"


lemma scalar_left_one: assumes wf: "vec nn v"
  and i: "i < nn"
  shows "scalar_prod (vec1 nn i) v = v ! i"
  using assms 
  unfolding vec1I_def vec_def 
proof (induct nn arbitrary: v i)
  case (Suc n) note oSuc = this
  from this obtain a vv where v: "v = a # vv" and lvv: "length vv = n" by (cases v, auto)
  show ?case 
  proof (cases i)
    case 0
    thus ?thesis using scalar_left_zero unfolding vec0I_def by (simp add: v scalar_prod_cons add_commute)
  next
    case (Suc ii)
    thus ?thesis using oSuc lvv v by (auto simp: scalar_prod_cons)
  qed
qed blast


lemma scalar_right_one: assumes wf: "vec nn v"
  and i: "i < nn"
  shows "scalar_prod v (vec1 nn i) = v ! i"
  using assms 
  unfolding vec1I_def vec_def 
proof (induct nn arbitrary: v i)
  case (Suc n) note oSuc = this
  from this obtain a vv where v: "v = a # vv" and lvv: "length vv = n" by (cases v, auto)
  show ?case 
  proof (cases i)
    case 0
    thus ?thesis using scalar_right_zero unfolding vec0I_def by (simp add: v scalar_prod_cons add_commute)
  next
    case (Suc ii)
    thus ?thesis using oSuc lvv v by (auto simp: scalar_prod_cons)
  qed
qed blast


lemma mat1_mult_right: assumes wf: "mat nr nc m"
  shows "mat_mult nr m (mat1 nc) = m"
proof (simp only: mat_eq_index[OF mat_mult[OF wf mat1] wf], intro allI impI)
  fix i j
  assume i: "i < nc" and j: "j < nr"
  show "mat_mult nr m (mat1 nc) ! i ! j = m ! i ! j"
    by (simp only: mat_mult_to_scalar[OF wf mat1 j i],
    simp only: col_mat1[OF i],
    simp only: scalar_right_one[OF row[OF wf j] i],
    simp only: row_col[OF wf j i],
    unfold col_def, simp)
qed


lemma mat1_mult_left: assumes wf: "mat nr nc m"
  shows "mat_mult nr (mat1 nr) m = m"
proof (simp only: mat_eq_index[OF mat_mult[OF mat1 wf] wf], intro allI impI)
  fix i j
  assume i: "i < nc" and j: "j < nr"
  show "mat_mult nr (mat1 nr) m ! i ! j = m ! i ! j"
    by (simp only: mat_mult_to_scalar[OF mat1 wf j i],
      simp only: row_mat1[OF j],
      simp only: scalar_left_one[OF col[OF wf i] j], unfold col_def, simp)
qed
end

lemma vec_ge_refl: "vec_ge v v"
  unfolding vec_ge_def vec_comp_all_def
  by (induct v, auto simp: ge_refl)

lemma mat_ge_refl: "mat_ge m m"
  unfolding mat_ge_def mat_comp_all_def 
  by (induct m, auto simp: vec_ge_refl[unfolded vec_ge_def])

lemma vec_ge_trans: assumes ge12: "vec_ge v1 v2" and ge23: "vec_ge v2 v3" and wf_1: "vec nr v1" and wf_2: "vec nr v2" and wf_3: "vec nr v3"
  shows "vec_ge v1 v3"
proof (simp only: vec_ge_index[OF wf_1 wf_3], intro allI impI) 
  fix i
  assume i: "i < nr"
  show "v1 ! i \<succeq> v3 ! i"
    using 
      spec[OF ge12[simplified vec_ge_index[OF wf_1 wf_2]], of i]
      spec[OF ge23[simplified vec_ge_index[OF wf_2 wf_3]], of i]
      ge_trans[of "v1 ! i" "v2 ! i" "v3 ! i"]
      i 
    by blast
qed

lemma mat_ge_trans: assumes ge12: "mat_ge v1 v2" and ge23: "mat_ge v2 v3" and wf_1: "mat nr nc v1" and wf_2: "mat nr nc v2" and wf_3: "mat nr nc v3"
  shows "mat_ge v1 v3"
proof (simp only: mat_ge_index[OF wf_1 wf_3], intro allI impI)
  fix i j
  assume i: "i < nc" and j: "j < nr"
  show "v1 ! i ! j \<succeq> v3 ! i ! j"
    using 
      spec[OF ge12[simplified mat_ge_index[OF wf_1 wf_2]], of i]
      spec[OF ge23[simplified mat_ge_index[OF wf_2 wf_3]], of i]
      ge_trans[of "v1 ! i ! j" "v2 ! i ! j" "v3 ! i ! j"]
      i j
    by blast
qed


lemma vec_plus_left_mono: assumes ge: "vec_ge v1 (v2 :: ('a :: ordered_ab_semigroup)vec)" and wf_1: "vec nr v1" and wf_2: "vec nr v2" and wf_3: "vec nr v3"
  shows "vec_ge (vec_plus v1 v3) (vec_plus v2 v3)"
  by (simp only: vec_ge_index[OF vec_plus[OF wf_1 wf_3] vec_plus[OF wf_2 wf_3]], intro allI impI,
    simp only: vec_plus_index[OF wf_1 wf_3],
    simp only: vec_plus_index[OF wf_2 wf_3],
    rule plus_left_mono,
    auto simp: ge[simplified vec_ge_index[OF wf_1 wf_2]])

lemma mat_plus_left_mono: assumes ge: "mat_ge m1 (m2 :: ('a :: ordered_ab_semigroup)mat)" and wf_1: "mat nr nc m1" and wf_2: "mat nr nc m2" and wf_3: "mat nr nc m3" 
  shows "mat_ge (mat_plus m1 m3) (mat_plus m2 m3)"
by (simp only: mat_ge_index[OF mat_plus[OF wf_1 wf_3] mat_plus[OF wf_2 wf_3]], intro allI impI,
    simp only: mat_plus_index[OF wf_1 wf_3],
    simp only: mat_plus_index[OF wf_2 wf_3],
    rule plus_left_mono,
    auto simp: ge[simplified mat_ge_index[OF wf_1 wf_2]])


lemma scalar_prod_mono_left: assumes wf1: "vec nr (v1 :: ('a :: ordered_semiring_1) vec)"
  and wf2: "vec nr v2"
  and wf3: "vec nr v3"
  and ge1: "vec_ge v1 v2"
  and ge2: "vec_ge v3 (vec0 nr)"
  shows "scalar_prod v1 v3 \<succeq> scalar_prod v2 v3"
using assms unfolding vec_def vec_ge_def vec_comp_all_def vec0I_def list_all_iff
proof -
  assume "length v1 = nr" and "length v2 = nr" and " length v3 = nr" and " \<forall>(x,y)\<in>set (zip v1 v2). x \<succeq> y" and " \<forall>(x,y)\<in>set (zip v3 (replicate nr 0)). x \<succeq> y"
  thus "scalar_prod v1 v3 \<succeq> scalar_prod v2 v3"
  proof (induct nr arbitrary: v1 v2 v3)
    case (Suc nrr)
    from Suc obtain a1 w1 where v1: "v1 = a1 # w1" and w1: "length w1 = nrr" by (cases v1, auto)
    from Suc obtain a2 w2 where v2: "v2 = a2 # w2" and w2: "length w2 = nrr" by (cases v2, auto)
    from Suc obtain a3 w3 where v3: "v3 = a3 # w3" and w3: "length w3 = nrr" by (cases v3, auto)
    from Suc have rec: "scalar_prod w1 w3 \<succeq> scalar_prod w2 w3" (is "?l \<succeq> ?r")
      by (auto simp: w1 w2 w3 v1 v2 v3)
    show ?case proof (simp add: v1 v2 v3 scalar_prod_cons)
      have one: "a1 * a3 \<succeq> a2 * a3" using times_left_mono[of a3 a1 a2] Suc v1 v2 v3 by auto
      hence "a1 * a3 + ?l \<succeq> a2 * a3 + ?l" by (rule plus_left_mono)
      also have "\<dots> \<succeq> a2 * a3 + ?r" using rec by (rule plus_right_mono)
      finally show "a1 * a3 + ?l \<succeq> a2 * a3 + ?r" .
    qed
  qed (simp add: scalar_prodI_def ge_refl)
qed

lemma scalar_prod_mono_right: assumes wf1: "vec nr (v1 :: ('a :: ordered_semiring_1) vec)"
  and wf2: "vec nr v2"
  and wf3: "vec nr v3"
  and ge1: "vec_ge v2 v3"
  and ge2: "vec_ge v1 (vec0 nr)"
  shows "scalar_prod v1 v2 \<succeq> scalar_prod v1 v3"
using assms unfolding vec_def vec_ge_def vec0I_def vec_comp_all_def list_all_iff
proof -
  assume "length v1 = nr" and "length v2 = nr" and " length v3 = nr" and " \<forall>(x,y)\<in>set (zip v2 v3). ge x y" and " \<forall>(x,y)\<in>set (zip v1 (replicate nr 0)). ge x y"
  thus "ge (scalar_prod v1 v2) (scalar_prod v1 v3)"
  proof (induct nr arbitrary: v1 v2 v3)
    case (Suc nrr)
    from Suc obtain a1 w1 where v1: "v1 = a1 # w1" and w1: "length w1 = nrr" by (cases v1, auto)
    from Suc obtain a2 w2 where v2: "v2 = a2 # w2" and w2: "length w2 = nrr" by (cases v2, auto)
    from Suc obtain a3 w3 where v3: "v3 = a3 # w3" and w3: "length w3 = nrr" by (cases v3, auto)
    from Suc have rec: "scalar_prod w1 w2 \<succeq> scalar_prod w1 w3" (is "?l \<succeq> ?r")
      by (auto simp: w1 w2 w3 v1 v2 v3)
    show ?case proof (simp add: v1 v2 v3 scalar_prod_cons)
      have one: "a1 * a2 \<succeq> a1 * a3" using times_right_mono[of a1 a2 a3] Suc v1 v2 v3 by auto
      hence "a1 * a2 + ?l \<succeq> a1 * a3 + ?l" by (rule plus_left_mono)
      also have " \<dots> \<succeq> a1 * a3 + ?r" using rec by (rule plus_right_mono)
      finally show "a1 * a2 + ?l \<succeq> a1 * a3 + ?r" .
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
  proof (simp only: mat_ge_index[OF wf13 wf23], intro allI impI)
    fix i j
    assume i: "i < ncc" and j: "j < nr"
    from ge1 have ge1a: "\<forall>i<nc. \<forall> j < nr.  m1 ! i ! j \<succeq> m2 ! i ! j"
      using mat_ge_index[OF wf1 wf2] by simp
    from ge2 have ge2a: "\<forall>ia<nc. col m3 i ! ia \<succeq> vec0 nc ! ia"
      using mat_ge_index[OF wf3 mat0] i unfolding col_def mat0I_def vec0I_def
      by auto      
    show "?m13 ! i ! j \<succeq> ?m23 ! i ! j"
      by (simp only: mat_mult_to_scalar[OF wf1 wf3 j i],
        simp only: mat_mult_to_scalar[OF wf2 wf3 j i], 
        rule scalar_prod_mono_left[OF row[OF wf1 j] row[OF wf2 j] col[OF wf3 i]],
        simp only: vec_ge_index[OF row[OF wf1 j] row[OF wf2 j]],
        (auto simp: row_col[OF wf1 j] row_col[OF wf2 j] col_def ge1a j)[1],
        simp only: vec_ge_index[OF col[OF wf3 i] vec0],
        rule ge2a)
  qed
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
  proof (simp only: mat_ge_index[OF wf12 wf13], intro allI impI)
    fix i j
    assume i: "i < ncc" and j: "j < nr"
    from ge2 i have ge2a: " \<forall>ia<nc. col m2 i ! ia \<succeq> col m3 i ! ia"
      using mat_ge_index[OF wf2 wf3] unfolding col_def by auto
    from ge1 j have ge1a: " \<forall>i<nc. m1 ! i ! j \<succeq> 0" 
      using mat_ge_index[OF wf1 mat0] unfolding mat0I_def vec0I_def
      by auto
    show "?m12 ! i ! j \<succeq> ?m13 ! i ! j"
      by  (simp only: mat_mult_to_scalar[OF wf1 wf2 j i],
        simp only: mat_mult_to_scalar[OF wf1 wf3 j i],
        rule scalar_prod_mono_right[OF row[OF wf1 j] col[OF wf2 i] col[OF wf3 i]], 
        simp only: vec_ge_index[OF col[OF wf2 i] col[OF wf3 i]], rule ge2a, 
        simp only: vec_ge_index[OF row[OF wf1 j] vec0],
        simp add: row_col[OF wf1 j] vec0I_def col_def, rule ge1a) 
  qed
qed

lemma mat1_ge_mat0: "mat_ge (mat1 n) ((mat0 n n) :: ('a :: ordered_semiring_1) mat)" (is "mat_ge ?m1 ?m0")
unfolding mat_ge_index[OF mat1 mat0]
proof (intro allI impI)
  fix i j
  assume i: "i < n" and j: "j < n"
  have zero_ij: "?m0 ! i ! j = 0" by (rule mat0_index[OF i j])
  have one_ij: "?m1 ! i ! j = (if i = j then 1 else 0)" by (rule mat1_index[OF i j])
  show "?m1 ! i ! j \<succeq> ?m0 ! i ! j"
    by (simp add: zero_ij one_ij ge_refl one_ge_zero)
qed


lemma mat_max0_x: assumes wf: "mat nr nc m" shows "mat_ge (mat_max0 m) m"
proof (unfold mat_ge_index[OF mat_max0[OF wf] wf], intro allI impI)
  fix i j
  assume i: "i < nc" and j: "j < nr"
  show "mat_max0 m ! i ! j \<succeq> m ! i ! j"
    by (unfold mat_max0_index[OF wf i j], rule max0_x)
qed

lemma mat_max0_pos: assumes wf: "mat nr nc m"
  shows "mat_ge (mat_max0 m) (mat0 nr nc)"
proof (unfold mat_ge_index[OF mat_max0[OF wf] mat0], intro allI impI)
  fix i j
  assume i: "i < nc" and j: "j < nr"
  show "mat_max0 m ! i ! j \<succeq> mat0 nr nc ! i ! j"
    by (unfold mat_max0_index[OF wf i j] mat0_index[OF i j], rule max0_pos)
qed

lemma mat_max0_id_pos: assumes ge: "mat_ge m (mat0 nr nc)" and wf: "mat nr nc m"  
  shows "mat_max0 m = m"
proof (unfold mat_eq_index[OF mat_max0[OF wf] wf], intro allI impI)
  fix i j
  assume i: "i < nc" and j: "j < nr"
  with ge[simplified mat_ge_index[OF wf mat0]] 
  have "m ! i ! j \<succeq> mat0 nr nc ! i ! j" by simp
  hence "m ! i ! j \<succeq> 0" using mat0_index[OF i j, of "0 :: 'a"] by simp
  thus "mat_max0 m ! i ! j = m ! i ! j"
    by (unfold mat_max0_index[OF wf i j], rule max0_id_pos)
qed

lemma mat_max0_mono: assumes ge: "mat_ge m1 m2" and wf1: "mat nr nc m1" and wf2: "mat nr nc m2"
  shows "mat_ge (mat_max0 m1) (mat_max0 m2)"
proof (unfold mat_ge_index[OF mat_max0[OF wf1] mat_max0[OF wf2]], intro allI impI)
  fix i j
  assume i: "i < nc" and j: "j < nr"
  with ge[simplified mat_ge_index[OF wf1 wf2]] 
  have "m1 ! i ! j \<succeq> m2 ! i ! j" by simp
  hence "max0 (m1 ! i ! j) \<succeq> max0 (m2 ! i ! j)" by (rule max0_mono)
  thus "mat_max0 m1 ! i ! j \<succeq> mat_max0 m2 ! i ! j"
    by (unfold mat_max0_index[OF wf1 i j] mat_max0_index[OF wf2 i j])
qed


context order_pair
begin

abbreviation mat_pre_gt :: "'a mat \<Rightarrow> 'a mat \<Rightarrow> bool"
where "mat_pre_gt \<equiv> mat_pre_gtI gt"

abbreviation mat_gt :: "nat \<Rightarrow> 'a mat \<Rightarrow> 'a mat \<Rightarrow> bool"
where "mat_gt \<equiv> mat_gtI gt"

abbreviation mat_default :: "nat \<Rightarrow> 'a mat" 
where "mat_default n \<equiv> mat1I 0 default n"


lemma mat_default_ge_mat0: "mat_ge (mat_default n) (mat0 n n)"
unfolding mat_ge_index[OF mat1 mat0]
proof (intro allI impI)
  fix i j
  assume i: "i < n" and j: "j < n"
  have zero_ij: "mat0 n n ! i ! j = 0" by (rule mat0_index[OF i j])
  have one_ij: "mat_default n ! i ! j = (if i = j then default else 0)" by (rule mat1_index[OF i j])
  show "mat_default n ! i ! j \<succeq> mat0 n n ! i ! j"
    by (simp add: zero_ij one_ij ge_refl default_ge_zero)
qed

lemma mat_gt_compat: assumes sd_n: "sd \<le> n" and  ge: "mat_ge m1 m2" and gt: "mat_gt sd m2 m3" and wf1: "mat n n m1" and wf2: "mat n n m2" and wf3: "mat n n m3" 
  shows "mat_gt sd m1 m3"
proof -
  from gt[simplified mat_gt_index[OF wf2 wf3 sd_n]] obtain i j 
    where i: "i < sd" and j: "j < sd" and gt: "m2 ! i ! j \<succ> m3 ! i ! j" and ge23: "mat_ge m2 m3" by auto 
  from ge[simplified mat_ge_index[OF wf1 wf2]] i j sd_n have geij: "m1 ! i ! j \<succeq> m2 ! i ! j" by auto
  from mat_ge_trans[OF ge ge23 wf1 wf2 wf3] have ge: "mat_ge m1 m3" .
  with compat[OF geij gt] i j show ?thesis 
    by (simp only: mat_gt_index[OF wf1 wf3 sd_n], auto)
qed

lemma mat_gt_compat2: assumes sd_n: "sd \<le> n" and gt: "mat_gt sd m1 m2" and ge: "mat_ge m2 m3" and wf1: "mat n n m1" and wf2: "mat n n m2" and wf3: "mat n n m3" 
  shows "mat_gt sd m1 m3"
proof -
  from gt[simplified mat_gt_index[OF wf1 wf2 sd_n]] obtain i j 
    where i: "i < sd" and j: "j < sd" and gt: "m1 ! i ! j \<succ> m2 ! i ! j" and ge12: "mat_ge m1 m2" by auto 
  from ge[simplified mat_ge_index[OF wf2 wf3]] i j sd_n have geij: "m2 ! i ! j \<succeq> m3 ! i ! j" by auto
  from mat_ge_trans[OF ge12 ge wf1 wf2 wf3] have ge: "mat_ge m1 m3" .
  with compat2[OF gt geij] i j show ?thesis 
    by (simp only: mat_gt_index[OF wf1 wf3 sd_n], auto)
qed
end

context one_mono_ordered_semiring_1
begin 

lemma mat_plus_gt_left_mono: assumes sd_n: "sd \<le> n" and gt: "mat_gt sd m1 m2" and ge: "mat_ge m3 m4" and wf1: "mat n n m1" and wf2: "mat n n m2" and wf3: "mat n n m3" and wf4: "mat n n m4"
  shows "mat_gt sd (mat_plus m1 m3) (mat_plus m2 m4)"
proof -
  let ?m13 = "mat_plus m1 m3"
  let ?m23 = "mat_plus m2 m3"
  let ?m32 = "mat_plus m3 m2"
  let ?m24 = "mat_plus m2 m4"
  let ?m42 = "mat_plus m4 m2"
  have wf13: "mat n n ?m13" and wf24: "mat n n ?m24" by ((rule mat_plus[of n n], auto simp: wf1 wf2 wf3 wf4)+)
  from gt[simplified mat_gt_index[OF wf1 wf2 sd_n]] obtain i j where
    i: "i < sd" and j: "j < sd" and gt: "m1 ! i ! j \<succ> m2 ! i ! j" and ge12: "mat_ge m1 m2" by auto
  with sd_n have ni: "i < n" and nj: "j < n" by auto
  from mat_plus_left_mono[OF ge12 wf1 wf2 wf3] have one: "mat_ge ?m13 ?m23" .
  from mat_plus_left_mono[OF ge wf3 wf4 wf2] have "mat_ge ?m32 ?m42" .
  hence two: "mat_ge ?m23 ?m24" by (simp add: mat_plus_comm[of m2 m3] mat_plus_comm[of m2 m4])
  have matge: "mat_ge ?m13 ?m24" by (rule mat_ge_trans[OF one two, of n n], (rule mat_plus[of n n], auto simp: wf1 wf2 wf3 wf4)+)
  from i j sd_n ge[simplified mat_ge_index[OF wf3 wf4]] have ge: "m3 ! i ! j \<succeq> m4 ! i ! j" by auto
  from compat2[OF plus_gt_left_mono[OF gt] plus_right_mono[OF ge]] mat_plus_index[OF wf1 wf3 ni nj] mat_plus_index[OF wf2 wf4 ni nj]      
  have gt: "?m13 ! i ! j \<succ> ?m24 ! i ! j" by simp
  from i j matge gt  show ?thesis 
    by (auto simp: mat_gt_index[OF wf13 wf24 sd_n] matge)
qed

lemma mat_default_gt_mat0: assumes sd_pos: "sd > 0" and sd_n: "sd \<le> n"
  shows "mat_gt sd (mat_default n) (mat0 n n)"
proof -
  from assms have n: "n > 0" by auto
  show ?thesis 
    by (simp only: mat_gt_index[OF mat1 mat0 sd_n] mat_default_ge_mat0, rule conjI[OF TrueI],
      (rule exI[of _ 0], simp only: sd_pos, rule conjI[OF TrueI])+, simp add: mat1_index[OF n n] mat0_index[OF n n] default_gt_zero)
qed
end
    
text {* three easy lemmas to go from pairs of numbers to numbers  *}

lemma mul_div_eq: assumes "c < b" shows "(a * b + c) div b = (a :: nat)" 
proof -
  from assms have b: "b \<noteq> 0" by simp
  have "(a * b + c) div b = (c + a * b) div b" by arith
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

abbreviation mat_ns :: "'a mat \<Rightarrow> nat \<Rightarrow> 'a mat \<Rightarrow> bool" ("(_ \<succeq>m _ _)" [51,51,51] 50) 
 where "m1 \<succeq>m n m2 \<equiv> (mat n n m1 \<and> mat n n m2 \<and> mat_ge m1 m2)"

abbreviation mat_s :: "'a mat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a mat \<Rightarrow> bool" ("(_ \<succ>m _ _ _)" [51,51,51,51] 50)
 where "m1 \<succ>m n sd m2 \<equiv> (mat n n m1 \<and> mat n n m2 \<and> mat_ge m2 (mat0 n n) \<and> mat_gt sd m1 m2)"

lemma mat_sn: assumes sd_n: "sd \<le> n" shows "SN {(m1,m2) . m1 \<succ>m n sd m2}"
unfolding SN_defs 
proof clarify
  fix e f 
  assume ass: "\<forall> i. (f i, f (Suc i)) \<in> {(m1,m2). m1 \<succ>m n sd m2}"
  hence len_n: "\<And> i. length (f i) = n" by (auto simp: mat_def) 
  let ?rel = "{(x,y). y \<succeq> 0 \<and> x \<succ> y}"
  let ?gt = "\<lambda> k i j. f k ! i ! j \<succ> f (Suc k) ! i ! j"
  let ?ge = "\<lambda> k i j. f k ! i ! j \<succeq> f (Suc k) ! i ! j"
  let ?gez = "\<lambda> k i j. f (Suc k) ! i ! j \<succeq> 0"
  let ?f = "\<lambda> k ij. f k ! (ij div sd) ! (ij mod sd)"
  let ?ij = "\<lambda> i j. (i * sd + j)"
  let ?fgt = "\<lambda> k ij. (?f k ij,?f (Suc k) ij) \<in> ?rel"
  let ?fpgt = "\<lambda> k ij. ?f k ij \<succ> ?f (Suc k) ij"
  let ?fge = "\<lambda> k ij. ?f k ij \<succeq> ?f (Suc k) ij"
  let ?sd = "sd * sd"
  have all: "\<And> k. (\<exists> ij < ?sd. ?fgt k ij) \<and> (\<forall> ij < ?sd. ?fge k ij)"
  proof -
    fix k
    from spec[OF ass, of k] have wf: "mat n n (f k)" and wf1: "mat n n (f (Suc k))" and gt: "mat_gt sd (f k) (f (Suc k))" and
      gez: "mat_ge (f (Suc k)) (mat0 n n)" by auto
    from gt[simplified mat_gt_index[OF wf wf1 sd_n]] obtain i j where i: "i < sd" and j: "j < sd" and ge: "mat_ge (f k) (f (Suc k))"
      and gt: "?gt k i j" by auto
    hence pgt: "?fpgt k (?ij i j)" by (auto simp: mul_div_eq[OF j] j)
    have ij: "?ij i j < ?sd" using i j smaller_product by auto
    from ge[simplified mat_ge_index[OF wf wf1]] sd_n have "\<forall> i < sd. \<forall> j < sd. ?ge k i j" by auto
    hence ge: "\<forall> ij < ?sd. ?fge k ij" by (simp add: all_all_into_all)      
    from gez[simplified mat_ge_index[OF wf1 mat0]] sd_n have "\<forall> i < sd. \<forall> j < sd. ?gez k i j" by (auto simp: mat0_index)
    hence "?gez k i j" using i j by simp
    hence "?f (Suc k) (?ij i j) \<succeq> 0" by (auto simp: mul_div_eq[OF j] j)
    with pgt have gt: "?fgt k (?ij i j)" by auto 
    from gt ge ij show "(\<exists> ij < ?sd. ?fgt k ij) \<and> (\<forall> ij < ?sd. ?fge k ij)" by auto
  qed
  obtain f sd where f: "f = ?f" and "sd = ?sd" by auto
  with all have ex: "\<And> k. (\<exists> i < sd. (f k i, f (Suc k) i) \<in> ?rel)" and all: "\<And> k.(\<forall> i < sd. f k i \<succeq> f (Suc k) i)" by auto
  let ?g = "\<lambda> k i. (f k i, f (Suc k) i) \<in> ?rel"
  from ex have g: "\<forall> k. \<exists> i < sd. ?g k i" by auto
  from inf_pigeon_hole_principle[OF g] obtain i where i: "i < sd" and inf: "\<forall> k. \<exists> k' \<ge> k. ?g k' i" by auto
  let ?h = "\<lambda> k. (f k i)"
  let ?nRel = "{(x,y) | x y :: 'a. x \<succeq> y}"
  from all i have all: "\<forall> k. (?h k, ?h (Suc k)) \<in> ?nRel \<union> ?rel" by auto
  from SN have SNe: "SN_elt ?rel (?h 0)" unfolding SN_defs by auto
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
    by (auto simp: mat_gt_index[OF wf2 wf3 sd_n])
  from mmono mat_mono_index[OF wf1 sd_n] j obtain k where k: "k < sd" and monojk: "mono (m1 ! j ! k)" by auto
  from i j k sd_n have ni: "i < n" and nj: "j < n" and nk: "k < n" by auto
  show ?thesis 
  proof (simp only: mat_gt_index[OF wf12 wf13 sd_n], simp only: gem, rule conjI[OF TrueI],
      rule exI[of _ i], simp only: i, rule conjI[OF TrueI],
      rule exI[of _ k], simp only: k, rule conjI[OF TrueI])
    let ?r = "\<lambda> n. map (\<lambda> j. m1 ! j ! k) [0 ..< n]"
    from row[OF wf1 nk] have wfr: "length (row m1 k) = n" unfolding vec_def by auto
    from col[OF wf2 ni] have wfc2: "length (col m2 i) = n" unfolding vec_def by auto
    from col[OF wf3 ni] have wfc3: "length (col m3 i) = n" unfolding vec_def by auto
    have "row m1 k = map (\<lambda> i. row m1 k ! i) [0 ..< length (row m1 k)]" by (rule map_nth[symmetric])
    also have "\<dots> = map (\<lambda> i. row m1 k !  i) [0 ..< n]" by (simp add: wfr)
    also have "\<dots> = ?r n" using row_col[OF wf1 nk, simplified col_def]
      by auto
    finally have r: "row m1 k = ?r n" .
    let ?c2 = "\<lambda> n. map (\<lambda> j. m2 ! i ! j) [0 ..< n]"
    have c2: "col m2 i = ?c2 n" by (simp only: wfc2[symmetric] col_def, simp add: map_nth)
    let ?c3 = "\<lambda> n. map (\<lambda> j. m3 ! i ! j) [0 ..< n]"
    have c3: "col m3 i = ?c3 n" by (simp only: wfc3[symmetric] col_def, simp add: map_nth)
    from mat_mult_to_scalar[OF wf1 wf2 nk ni]
    have s12: "?m12 ! i ! k = scalar_prod (?r n) (?c2 n)" by (simp add: r c2)
    from mat_mult_to_scalar[OF wf1 wf3 nk ni]
    have s13: "?m13 ! i ! k = scalar_prod (?r n) (?c3 n)" by (simp add: r c3)
    have r0: "\<forall> j < n. ?r n ! j \<succeq> 0" 
    proof (intro impI allI)
      fix j
      assume "j < n"
      with ge[simplified mat_ge_index[OF wf1 mat0]] nk
      show "?r n ! j \<succeq> 0" by (simp add: mat0_index)
    qed
    have c2c3: "\<forall> j < n. ?c2 n ! j \<succeq> ?c3 n ! j"
    proof (intro impI allI)
      fix j
      assume "j < n"
      with ni geq[simplified mat_ge_index[OF wf2 wf3]] 
      show "?c2 n ! j \<succeq> ?c3 n ! j" by simp
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
      from Suc(3) have z: "m1 ! n ! k \<succeq> 0" by (simp del: upt_Suc)
      from Suc(3) have za: "\<forall> j < n. ?r n ! j \<succeq> 0"  by (simp del: upt_Suc)
      from Suc(4) have ge: "\<forall> j < n. ?c2 n ! j \<succeq> ?c3 n ! j"  by (simp del: upt_Suc)
      show ?case
      proof (cases "j = n")
        case False
        with Suc(2) have j: "j < n" by auto
        have rec: "?s2 \<succ> ?s3"
          by (rule Suc, rule j, rule za, rule ge)
        from Suc(4) have ge: "m2 ! i ! n \<succeq> m3 ! i ! n" by (simp del: upt_Suc)
        from times_right_mono[OF z ge] have p23: "?p2 \<succeq> ?p3" .
        from compat2[OF plus_gt_left_mono[OF rec] plus_right_mono[OF p23]] have "?s2 + ?p2 \<succ> ?s3 + ?p3" .
        with add_commute[of ?p2] add_commute[of ?p3] have "?p2 + ?s2 \<succ> ?p3 + ?s3" by simp
        with sum2 sum3 show ?thesis by simp 
      next
        case True        
        with mono[OF monojk gt] z have p23: "?p2 \<succ> ?p3" by simp
        have wf1: "vec n (?r n)" by (simp add: vec_def)
        have wf2: "vec n (?c2 n)" by (simp add: vec_def)
        have wf3: "vec n (?c3 n)" by (simp add: vec_def)
        from ge have ge: "vec_ge (?c2 n) (?c3 n)" 
          by (simp only: vec_ge_index[OF wf2 wf3])
        from za have z: "vec_ge (?r n) (vec0 n)" 
          by (simp only: vec_ge_index[OF wf1 vec0], auto simp: vec0I_def)
        have s23: "?s2 \<succeq> ?s3"
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


lemma mat_gt_arc_compat: assumes ge: "mat_ge m1 m2" and gt: "mat_gt_arc m2 m3" and wf1: "mat nr nc m1" and wf2: "mat nr nc m2" and wf3: "mat nr nc m3" 
  shows "mat_gt_arc m1 m3"
proof (simp only: mat_comp_all_index[OF wf1 wf3], intro allI impI)
  fix i j
  assume i: "i < nc" and j: "j < nr"
  from ge i j have one: "m1 ! i ! j \<succeq> m2 ! i ! j" using mat_ge_index[OF wf1 wf2] by auto
  from gt i j have two: "m2 ! i ! j \<succ> m3 ! i ! j" using mat_comp_all_index[OF wf2 wf3] by auto
  from one two show "m1 ! i ! j \<succ> m3 ! i ! j" by (rule compat)
qed

lemma mat_gt_arc_compat2: assumes gt: "mat_gt_arc m1 m2" and ge: "mat_ge m2 m3" and wf1: "mat nr nc m1" and wf2: "mat nr nc m2" and wf3: "mat nr nc m3" 
  shows "mat_gt_arc m1 m3"
proof (simp only: mat_comp_all_index[OF wf1 wf3], intro allI impI)
  fix i j
  assume i: "i < nc" and j: "j < nr"
  from gt i j have one: "m1 ! i ! j \<succ> m2 ! i ! j" using mat_comp_all_index[OF wf1 wf2] by auto
  from ge i j have two: "m2 ! i ! j \<succeq> m3 ! i ! j" using mat_ge_index[OF wf2 wf3] by auto
  from one two show "m1 ! i ! j \<succ>  m3 ! i ! j" by (rule compat2)
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
  from mat_plus[OF wfx wfz] have wfxz: "mat nr nc ?xz" .
  from mat_plus[OF wfy wfu] have wfyu: "mat nr nc ?yu" .
  show ?thesis 
  proof (simp only: mat_comp_all_index[OF wfxz wfyu], intro allI impI)
    fix i j
    assume i: "i < nc" and j: "j < nr"
    show "mat_plus x z ! i ! j \<succ> mat_plus y u ! i ! j"
    proof (
        simp only: mat_plus_index[OF wfx wfz i j],
        simp only: mat_plus_index[OF wfy wfu i j],
        rule plus_gt_both_mono)
      show "x ! i ! j \<succ> y ! i ! j" using gt1 i j mat_comp_all_index[OF wfx wfy] by auto
    next
      show "z ! i ! j \<succ> u ! i ! j" using gt2 i j mat_comp_all_index[OF wfz wfu] by auto
    qed
  qed
qed


lemma mat_gt_arc_mult_mono: assumes gt1: "mat_gt_arc x y"
  and wfx: "mat nr nc x"
  and wfy: "mat nr nc y"
  and wfz: "mat nc ncc z"
  shows "mat_gt_arc (mat_mult nr x z) (mat_mult nr y z)"
proof -
  let ?xz = "mat_mult nr x z"
  let ?yz = "mat_mult nr y z"
  from mat_mult[OF wfx wfz] have wfxz: "mat nr ncc ?xz" .
  from mat_mult[OF wfy wfz] have wfyz: "mat nr ncc ?yz" .
  show ?thesis 
  proof (simp only: mat_comp_all_index[OF wfxz wfyz], intro allI impI)
    fix i j
    assume i: "i < ncc" and j: "j < nr"
    have wfxj: "vec nc (row x j)" using row[OF wfx j] .
    have wfyj: "vec nc (row y j)" using row[OF wfy j] .
    have wfzi: "vec nc (col z i)" using col[OF wfz i] .
    show "?xz ! i ! j \<succ> ?yz ! i ! j"
    proof (
        simp only: mat_mult_to_scalar[OF wfx wfz j i],
        simp only: mat_mult_to_scalar[OF wfy wfz j i],
        rule scalar_prod_left_mono[OF wfxj wfyj wfzi],
        simp only: vec_comp_all_index[OF wfxj wfyj],
        intro allI impI
      )
      fix k
      assume k: "k < nc"
      from gt1 mat_comp_all_index[OF wfx wfy, of gt] j k
      show "row x j ! k \<succ> row y j ! k"
        by (
          simp only: row_col[OF wfx j k],
          simp only: row_col[OF wfy j k],
          unfold col_def, auto)
    qed
  qed
qed

lemma mat0_leastI: assumes wf: "mat nr nc m"
  shows "mat_gt_arc m (mat0 nr nc)"
proof (simp only: mat_comp_all_index[OF wf mat0], intro allI impI)
  fix i j
  assume i: "i < nc" and j: "j < nr"
  show "m ! i ! j \<succ> mat0I 0 nr nc ! i ! j"
    by (simp only: mat0_index[OF i j] zero_leastI)
qed

lemma mat0_leastII: 
  assumes gt: "mat_gt_arc (mat0 nr nc) m"
  and wf: "mat nr nc m"
  shows "m = mat0 nr nc"
proof (simp only: mat_eq_index[OF wf mat0], intro allI impI)
  fix i j
  assume i: "i < nc" and j: "j < nr"
  show "m ! i ! j = mat0 nr nc ! i ! j"
  proof (simp only: mat0_index[OF i j], rule zero_leastII)
    show "0 \<succ> m ! i ! j" using i j gt mat_comp_all_index[OF mat0 wf, of gt 0] mat0_index[OF i j, of "0 :: 'a"] by force
  qed
qed


lemma mat0_leastIII: assumes wf: "mat nr nc m"
  shows "mat_ge m ((mat0 nr nc) :: 'a mat)"
proof (simp only: mat_ge_index[OF wf mat0], intro allI impI)
  fix i j
  assume i: "i < nc" and j: "j < nr"
  show "(m ! i ! j) \<succeq> ((mat0 nr nc :: 'a mat) ! i ! j)"
    by (simp only: mat0_index[OF i j] zero_leastIII)
qed

lemma mat1_gt_arc_mat0: "mat_gt_arc (mat1 n) (mat0 n n)"
proof (simp only: mat_comp_all_index[OF mat1 mat0], intro allI impI)
  fix i j
  assume i: "i < n" and j: "j < n"
  show "mat1 n ! i ! j \<succ> mat0 n n ! i ! j"
    by (simp only: mat0_index[OF i j],
      rule zero_leastI)
qed

lemma mat_default_gt_arc_mat0: "mat_gt_arc (mat_default n) (mat0 n n)"
proof (simp only: mat_comp_all_index[OF mat1 mat0], intro allI impI)
  fix i j
  assume i: "i < n" and j: "j < n"
  show "mat_default n ! i ! j \<succ> mat0 n n ! i ! j"
    by (simp only: mat0_index[OF i j],
      rule zero_leastI)
qed
end 

context SN_both_mono_ordered_semiring_1
begin


abbreviation mat_arc_pos :: "'a mat \<Rightarrow> bool"
where "mat_arc_pos \<equiv> mat_arc_posI arc_pos"


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
    show "f i ! 0 ! 0 \<succ>  f (Suc i) ! 0 ! 0" using mat_comp_all_index[OF wf1 wf2, of gt] mat0_index[OF n_pos n_pos, of 0] gt n_pos by force
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
    by (simp only: mat_mult_to_scalar[OF wf1 wf2 n_pos n_pos],
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
    from orient[OF ass, unfolded mat_gt_index[OF wf1 wf2 sd_n]] 
    obtain i j where ge: "mat_ge m1 m2" and i: "i < sd" and j: "j < sd" and weak_gt: "weak_gt (m1 ! i ! j) (m2 ! i ! j)" (is "weak_gt ?x ?y") by auto
    from wf1 i j sd_n have m1ij: "m1 ! i \<in> set m1 \<and> m1 ! i ! j \<in> set (m1 ! i)" unfolding mat_def  by (auto simp: vec_def)
    from wf2 i j sd_n have m2ij: "m2 ! i \<in> set m2 \<and> m2 ! i ! j \<in> set (m2 ! i)" unfolding mat_def  by (auto simp: vec_def)
    have x: "?x \<in> set ?m1x" by (auto, rule bexI[OF _ m1m2], rule bexI[of _ "m1 ! i"], auto simp: m1ij)
    have y: "?y \<in> set ?m2y" by (auto, rule bexI[OF _ m1m2], rule bexI[of _ "m2 ! i"], auto simp: m2ij)
    from x y have "(?x,?y) \<in> set ?pairs" by force
    with weak_gt have gt: "(?x,?y) \<in> set ?strict" by simp
    show "mat_gtI gt sd m1 m2" unfolding mat_gt_index[OF wf1 wf2 sd_n]
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
    show "mat_comp_all gt  m1 m2" unfolding mat_comp_all_index[OF wf1 wf2]
    proof (intro allI impI)
      fix i j
      assume i: "i < n" and j: "j < n"
      with orient[OF ass, unfolded mat_comp_all_index[OF wf1 wf2]] have weak_gt: "weak_gt (m1 ! i ! j) (m2 ! i ! j)" (is "weak_gt ?x ?y") by auto  
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


declare vec0[simp del] mat0[simp del] vec0_plus[simp del] plus_vec0[simp del] plus_mat0[simp del]

(* and undo the list_all_ex[simp] *)
declare list_all_ex[simp del]



end
