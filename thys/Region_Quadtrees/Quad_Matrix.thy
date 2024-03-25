section \<open>Block Matrices via Quad Trees\<close>

theory Quad_Matrix
imports
  Complex_Main
  Quad_Base
begin

(* TODO Strassen multiplication *)

text \<open>There are two possible representations of marices as quadtrees.
In this file we use the standard quadtree with two constructors \<open>L\<close> and \<open>Q\<close>.
\<open>L x\<close> represents the \<open>x\<close>-diagonal ma of arbitrary dimension.
In particular \<open>L 0\<close> is the "empty" case.
Because \<open>L x\<close> can be of arbitrary dimension, it can be added and multiplied with \<open>Q\<close>.

In the second representation (not covered in this theory) \<open>L x\<close> is the 1x1 ma \<open>x\<close>.
The advantage is that there are fewer cases in function definitions
because one cannot add/multiply \<open>L\<close> and \<open>Q\<close>: the have different dimensions.
However, \<open>L 0\<close> is special: it still represents the 0 ma of arbitrary dimension.
This leads to a more complicated invariant wrt dimension. Or one introduces a new constructor, eg \<open>Empty\<close>.
\<close>

subsection \<open>Square Matrices\<close>

type_synonym ma = "nat \<Rightarrow> nat \<Rightarrow> real"

text \<open>Implicitly entries outside the dimensions of the ma are 0. This is
maintained by addition; multiplication and diagonal need an explicit argument \<open>n\<close> to maintain it.\<close>

definition mk_sq :: "nat \<Rightarrow> ma \<Rightarrow> ma" where
  "mk_sq n a = (\<lambda>i j. if i < 2^n \<and> j < 2^n then a i j else 0)"

abbreviation "sq_ma n (a::ma) \<equiv> (\<forall>i j. 2^n \<le> i \<or> 2^n \<le> j \<longrightarrow> a i j = 0)"

text \<open>Without \<open>mk_sq\<close> a number of lemmas like \<open>mult_ma_diag_ma_diag_ma\<close> don't hold.\<close>
definition diag_ma :: "nat \<Rightarrow> real \<Rightarrow> ma" where
  "diag_ma n x = mk_sq n (\<lambda>i j. if i=j then x else 0)"

definition add_ma :: "ma \<Rightarrow> ma  \<Rightarrow> ma" where
  "add_ma a b = (\<lambda>i j. a i j + b i j)"

definition mult_ma :: "nat \<Rightarrow> ma \<Rightarrow> ma  \<Rightarrow> ma" where
  "mult_ma n a b = (\<lambda>i j. \<Sum>k=0..<2^n. a i k * b k j)"


subsection \<open>Matrix Lemmas\<close>

lemma add_ma_diag_ma[simp]: "add_ma (diag_ma n x) (diag_ma n y) = diag_ma n (x+y)"
  by(simp add: diag_ma_def add_ma_def mk_sq_def fun_eq_iff)

lemma add_ma_diag_ma_0[simp]: "add_ma (diag_ma n 0) a = a"
  by (auto simp add: add_ma_def diag_ma_def mk_sq_def fun_eq_iff)

lemma add_ma_diag_ma_02[simp]: "add_ma a (diag_ma n 0) = a"
  by (auto simp add: add_ma_def diag_ma_def mk_sq_def fun_eq_iff)

lemma mult_ma_diag_ma_0[simp]: "mult_ma n (diag_ma n 0) a = diag_ma n 0"
  by (auto simp add: mult_ma_def diag_ma_def mk_sq_def fun_eq_iff)

lemma mult_ma_diag_ma_02[simp]: "mult_ma n a (diag_ma n 0) = diag_ma n 0"
  by (auto simp add: mult_ma_def diag_ma_def mk_sq_def fun_eq_iff)

lemma mult_ma_diag_ma_diag_ma[simp]: "mult_ma n (diag_ma n x) (diag_ma n y) = diag_ma n (x*y)"
  apply (auto simp add: mult_ma_def diag_ma_def mk_sq_def fun_eq_iff sum.neutral)
  subgoal for i
    apply(simp add: sum.remove[where x=i])
    done
  done


subsection "Real Quad Trees and Abstraction to Matrices"

type_synonym qtr = "real qtree"

fun compressed :: "qtr \<Rightarrow> bool" where
  "compressed (L x) = True" |
  "compressed (Q (L x0) (L x1) (L x2) (L x3)) = (\<not> (x1=0 \<and> x2=0 \<and> x0=x3))" |
  "compressed (Q t0 t1 t2 t3) = (compressed t0 \<and> compressed t1 \<and> compressed t2 \<and> compressed t3)"

lemma compressed_Q:
  "compressed (Q t1 t2 t3 t4) \<Longrightarrow> (compressed t1 \<and> compressed t2 \<and> compressed t3 \<and> compressed t4)"
  by(cases "Q t1 t2 t3 t4" rule: compressed.cases)(auto)

definition Qma :: "nat \<Rightarrow> ma \<Rightarrow> ma \<Rightarrow> ma \<Rightarrow> ma \<Rightarrow> ma" where
"Qma n a b c d =
  (\<lambda>i j. if i < 2^n then if j < 2^n then a i j else b i (j - 2^n) else
         if j < 2^n then c (i - 2^n) j else d (i - 2^n) (j - 2^n))"

lemma add_ma_Qma:
  "add_ma (Qma n a b c d) (Qma n a' b' c' d') =
  Qma n (add_ma a a') (add_ma b b') (add_ma c c') (add_ma d d')"
  by(simp add: Qma_def add_ma_def mk_sq_def fun_eq_iff)

lemma add_ma_diag_ma_Qma: "add_ma (diag_ma (Suc n) x) (Qma n a b c d) =
  Qma n (add_ma (diag_ma n x) a) b c (add_ma (diag_ma n x) d)"
  by(auto simp add: Qma_def diag_ma_def add_ma_def mk_sq_def fun_eq_iff)

lemma add_ma_Qma_diag_ma: "add_ma (Qma n a b c d) (diag_ma (Suc n) x) =
  Qma n (add_ma a (diag_ma n x)) b c (add_ma d (diag_ma n x))"
  by(auto simp add: Qma_def diag_ma_def add_ma_def mk_sq_def fun_eq_iff)

lemma diag_ma_Suc: "diag_ma (Suc n) x = Qma n (diag_ma n x) (diag_ma n 0) (diag_ma n 0) (diag_ma n x)"
  by(auto simp add: diag_ma_def Qma_def mk_sq_def fun_eq_iff)

text \<open>Abstraction function:\<close>

fun ma :: "nat \<Rightarrow> qtr \<Rightarrow> ma" where
  "ma n (L x) = diag_ma n x" |
  "ma (Suc n) (Q t0 t1 t2 t3) =
  Qma n (ma n t0) (ma n t1) (ma n t2) (ma n t3)"


subsection "Matrix Operations on Trees"

fun Qc :: "qtr \<Rightarrow> qtr \<Rightarrow> qtr \<Rightarrow> qtr \<Rightarrow> qtr" where
"Qc (L x0) (L x1) (L x2) (L x3) =
   (if x1=0 \<and> x2=0 \<and> x0=x3 then L x0 else Q (L x0) (L x1) (L x2) (L x3))" |
"Qc t1 t2 t3 t4 = Q t1 t2 t3 t4"

lemma ma_Suc_Qc: "ma (Suc n) (Qc t0 t1 t2 t3) = ma (Suc n) (Q t0 t1 t2 t3)"
by(induction t0 t1 t2 t3 rule: Qc.induct)(auto simp: diag_ma_Suc)

lemma compressed_Qc:
  "compressed (Qc t0 t1 t2 t3) = (compressed t0 \<and> compressed t1 \<and> compressed t2 \<and> compressed t3)"
by(induction t0 t1 t2 t3 rule: Qc.induct)(auto)

lemma height_Qc_Q:
  "height (Qc t0 t1 t2 t3) \<le> height (Q t0 t1 t2 t3)"
proof(induction t0 t1 t2 t3 rule: Qc.induct)
  case (1 x0 x1 x2 x3)
  then show ?case by simp
qed (insert Qc.simps,presburger+)

fun add :: "qtr \<Rightarrow> qtr \<Rightarrow> qtr" where
  "add (Q s0 s1 s2 s3) (Q t0 t1 t2 t3) = Qc (add s0 t0) (add s1 t1) (add s2 t2) (add s3 t3)" |
  "add (L x) (L y) = L(x+y)" |
  "add (L x) (Q t0 t1 t2 t3) = Qc (add (L x) t0) t1 t2 (add (L x) t3)" |
  "add (Q t0 t1 t2 t3) (L x) = Qc (add t0 (L x)) t1 t2 (add t3 (L x))"

fun mult :: "qtr \<Rightarrow> qtr \<Rightarrow> qtr" where
"mult (Q s0 s1 s2 s3) (Q t0 t1 t2 t3) =
  Qc (add (mult s0 t0) (mult s1 t2))
    (add (mult s0 t1) (mult s1 t3))
    (add (mult s2 t0) (mult s3 t2))
    (add (mult s2 t1) (mult s3 t3))" |
"mult (L x) (Q t0 t1 t2 t3) =
 Qc (mult (L x) t0)
    (mult (L x) t1)
    (mult (L x) t2)
    (mult (L x) t3)" |
"mult (Q t0 t1 t2 t3) (L x) =
 Qc (mult t0 (L x))
    (mult t1 (L x))
    (mult t2 (L x))
    (mult t3 (L x))" |
"mult (L x) (L y) = L(x*y)"

text \<open>Initialization of \<open>qtr\<close> from ma\<close>
fun qtr :: "nat \<Rightarrow> ma \<Rightarrow> qtr" where
"qtr 0 a = L(a 0 0)" |
"qtr (Suc n) a =
  (let t0 = qtr n a; t1 = qtr n (\<lambda>i j. a i (j+2^n));
       t2 = qtr n (\<lambda>i j. a (i+2^n) j); t3 = qtr n (\<lambda>i j. a (i+2^n) (j+2^n))
   in Q t0 t1 t2 t3)" 


subsection \<open>Correctness of Quad Tree Implementations\<close>

subsubsection \<open>@{const add}\<close>

lemma ma_add: "\<lbrakk> height s \<le> n; height t \<le> n \<rbrakk> \<Longrightarrow>
  ma n (add s t) = add_ma (ma n s) (ma n t)"
proof(induction s t arbitrary: n rule: add.induct)
  case 1
  then show ?case by(simp add: less_eq_nat.simps(2) add_ma_Qma ma_Suc_Qc split: nat.splits)
next
  case 2
  then show ?case by(simp)
next
  case 3
  then show ?case by(simp add: add_ma_diag_ma_Qma ma_Suc_Qc less_eq_nat.simps(2) split: nat.splits)
next
  case 4
  then show ?case by(simp add: add_ma_Qma_diag_ma ma_Suc_Qc less_eq_nat.simps(2) split: nat.splits)
qed

lemma height_add: "height (add s t) \<le> max (height s) (height t)"
proof(induction s t rule: add.induct)
  case (1 s1 s2 s3 s4 t1 t2 t3 t4)
  thus ?case
    using height_Qc_Q[of "add s1 t1" "add s2 t2" "add s3 t3" "add s4 t4"]
    by (auto simp: max.coboundedI1 max.coboundedI2
          simp del: max.absorb1 max.absorb2 max.absorb3 max.absorb4 elim!: le_trans)
next
  case (3 x t1 t2 t3 t4)
  thus ?case using height_Qc_Q[of "add (L x) t1" t2 t3 "add (L x) t4"]
    by auto
next
  case (4 t1 t2 t3 t4 x)
  then show ?case using height_Qc_Q[of "add t1 (L x)" t2 t3 "add t4 (L x)"]
    by auto
qed simp

lemma compressed_add: "\<lbrakk> compressed s; compressed t \<rbrakk> \<Longrightarrow> compressed (add s t)"
by(induction s t rule: add.induct) (auto simp: compressed_Qc dest: compressed_Q)

lemma Max4: "Max{n0,n1,n2,n3} = max n0 (max n1 (max n2 n3))"by simp

lemma height_mult: "height (mult s t) \<le> max (height s) (height t)"
proof(induction s t rule: mult.induct)
  case (1 s1 s2 s3 s4 t1 t2 t3 t4)
  let ?m11 = "mult s1 t1" let ?m23 = "mult s2 t3" let ?m12 = "mult s1 t2" let ?m24 = "mult s2 t4"
  let ?m31 = "mult s3 t1" let ?m43 = "mult s4 t3" let ?m32 = "mult s3 t2" let ?m44 = "mult s4 t4"
  show ?case
    using 1 height_Qc_Q[of "add ?m11 ?m23" "add ?m12 ?m24" "add ?m31 ?m43" "add ?m32 ?m44"]
       height_add[of ?m11 ?m23] height_add[of ?m12 ?m24] height_add[of ?m31 ?m43] height_add[of ?m32 ?m44]
    unfolding mult.simps height_qtree.simps One_nat_def add_Suc_right add_0_right max_Suc_Suc Max4
  by (smt (z3) order.trans le_max_iff_disj not_less_eq_eq)
next
  case (2 x t0 t1 t2 t3)
  thus ?case using height_Qc_Q[of "mult (L x) t0" "mult (L x) t1" "mult (L x) t2" "mult (L x) t3"]
    by (simp)
next
  case (3 t0 t1 t2 t3 x)
  thus ?case using height_Qc_Q[of "mult t0 (L x)" "mult t1 (L x)" "mult t2 (L x)" "mult t3 (L x)"]
    by simp
qed (simp)

subsubsection \<open>@{const mult}\<close>

lemma bij_betw_minus_ivlco_nat: "n \<le> a \<Longrightarrow> C = {a-n..<b-n} \<Longrightarrow> bij_betw (\<lambda>k::nat. k-n) {a..<b} C"
by(auto simp add: bij_betw_def inj_on_def image_minus_const_atLeastLessThan_nat)

lemma mult_ma_Qma_Qma:
  "mult_ma (Suc n) (Qma n a b c d) (Qma n a' b' c' d') =
             (Qma n (add_ma (mult_ma n a a') (mult_ma n b c'))
                        (add_ma (mult_ma n a b') (mult_ma n b d'))
                        (add_ma (mult_ma n c a') (mult_ma n d c'))
                        (add_ma (mult_ma n c b') (mult_ma n d d')))"
by(auto simp add: mult_ma_def add_ma_def Qma_def mk_sq_def fun_eq_iff sum_Un ivl_disj_un(17)[of 0 "2^n" "2*2^n",symmetric]
  intro:sum.reindex_bij_betw[of "\<lambda>k. k - 2^n" "{2 ^ n..<2 * 2 ^ n}" "{0..<2^n}", OF bij_betw_minus_ivlco_nat])

lemma ma_mult: "\<lbrakk> height s \<le> n; height t \<le> n \<rbrakk> \<Longrightarrow>
  ma n (mult s t) = mult_ma n (ma n s) (ma n t)"
proof(induction s t arbitrary: n rule: mult.induct)
  case (1 s1 s2 s3 s4 t1 t2 t3 t4) thus ?case
    by(simp add: mult_ma_Qma_Qma ma_add ma_Suc_Qc le_trans[OF  height_mult]
         less_eq_nat.simps(2) split: nat.splits)
next
  case 2 thus ?case
    by(simp add: diag_ma_Suc ma_Suc_Qc mult_ma_Qma_Qma
         less_eq_nat.simps(2) split: nat.splits)
next
  case 3 thus ?case
    by(simp add: diag_ma_Suc ma_Suc_Qc mult_ma_Qma_Qma
         less_eq_nat.simps(2) split: nat.splits)
qed simp

lemma compressed_mult: "\<lbrakk> compressed s; compressed t \<rbrakk> \<Longrightarrow> compressed (mult s t)"
proof(induction s t rule: mult.induct)
  case 1 thus ?case unfolding mult.simps by (metis compressed_Q compressed_Qc compressed_add)
next
  case 2 thus ?case unfolding mult.simps by (metis compressed_Q compressed_Qc)
next
  case 3 thus ?case unfolding mult.simps by (metis compressed_Q compressed_Qc)
next
  case 4 thus ?case by simp
qed

(*unused_thms*)

end
