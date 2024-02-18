section \<open>Quad Trees\<close>

theory Quad_Tree
imports Quad_Base
begin

(* TODO: remove - is [simp] after Isabelle23 *)
lemma diff_shunt: "({} = x - y) \<longleftrightarrow> (x \<le> y)"
  by blast

lemma mod_minus: "\<lbrakk> i < 2*m; \<not> i < m \<rbrakk> \<Longrightarrow> i mod m = i - (m::nat)"
  by (simp add: div_if modulo_nat_def)

definition select :: "bool \<Rightarrow> bool \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a" where
"select x y t0 t1 t2 t3 =
  (if x then
     if y then t0 else t1
   else
     if y then t2 else t3)"

abbreviation qf where
"qf q f i j d \<equiv> q (f i j)  (f i (j+d)) (f (i+d) j) (f (i+d) (j+d))"


subsection \<open>Compression\<close>

fun compressed :: "'a qtree \<Rightarrow> bool" where
  "compressed (L _) = True" |
  "compressed (Q t0 t1 t2 t3) = ((compressed t0 \<and> compressed t1 \<and> compressed t2 \<and> compressed t3)
    \<and> \<not> (\<exists>x. t0 = L x \<and> t1 = t0 \<and> t2 = t0 \<and> t3 = t0))"

fun Qc :: "'a qtree \<Rightarrow> 'a qtree \<Rightarrow> 'a qtree \<Rightarrow> 'a qtree \<Rightarrow> 'a qtree" where
  "Qc (L x0) (L x1) (L x2) (L x3) =
  (if x0=x1 \<and> x1=x2 \<and> x2=x3 then L x0 else Q (L x0) (L x1) (L x2) (L x3))" |
  "Qc t0 t1 t2 t3 = Q t0 t1 t2 t3"

text\<open>Compressing version of \<open>Q\<close>:\<close>
lemma compressed_Qc: "\<lbrakk>compressed t0; compressed t1; compressed t2; compressed t3 \<rbrakk> \<Longrightarrow>
  compressed (Qc t0 t1 t2 t3)"
  by(induction t0 t1 t2 t3 rule: Qc.induct) (auto split!: qtree.split)

lemma compressedQD: "compressed (Q t1 t2 t3 t4)
 \<Longrightarrow> compressed t1 \<and> compressed t2 \<and> compressed t3 \<and> compressed t4"
  using compressed.simps(2) by blast

lemma height_Qc_Q: "\<lbrakk> height s0 \<le> n; height s1 \<le> n; height s2 \<le> n; height s3 \<le> n \<rbrakk>
 \<Longrightarrow> height (Qc s0 s1 s2 s3) \<le> Suc n"
  apply(cases "(s0,s1,s2,s3)" rule: Qc.cases)
  using [[simp_depth_limit=1]]apply simp_all
  done

text \<open>Modify a quadrant addressed by \<open>x\<close> and \<open>y\<close>, and put things back together with \<open>Qc\<close>:\<close>

fun modify :: "('a qtree \<Rightarrow> 'a qtree) \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> 'a qtree *'a qtree *'a qtree *'a qtree \<Rightarrow> 'a qtree" where
"modify f x y (t0, t1, t2, t3) =
  (if x then
     if y then Qc (f t0) t1 t2 t3 else Qc t0 (f t1) t2 t3
   else
     if y then Qc t0 t1 (f t2) t3 else Qc t0 t1 t2 (f t3))"


subsection \<open>Abstraction function\<close>

fun get :: "nat \<Rightarrow> 'a qtree \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a"  where
  "get n (L b) _ _ = b" |
  "get (Suc n) (Q t0 t1 t2 t3) i j =
  get n (select (i < 2^n) (j < 2^n) t0 t1 t2 t3) (i mod 2^n) (j mod 2^n)"

lemma get_Qc:
  "height(Q t0 t1 t2 t3) \<le> n \<Longrightarrow> get n (Qc t0 t1 t2 t3) i j = get n (Q t0 t1 t2 t3) i j"
apply(cases n)
 apply simp
apply(cases "(t0,t1,t2,t3)" rule: Qc.cases)
apply(simp_all add: select_def)
done


subsection "Boolean Quadtrees"

type_synonym qtb = "bool qtree"

subsubsection \<open>Abstraction of boolean quadtrees to sets of points\<close>

text \<open>Superceded by the more general @{const get} abstraction.\<close>

type_synonym points = "(nat \<times> nat) set"

abbreviation sq :: "nat \<Rightarrow> points" where
  "sq (n::nat) \<equiv> {0..<2 ^ n} \<times> {0..<2 ^ n}"

definition shift :: "nat \<Rightarrow> nat \<Rightarrow> nat * nat \<Rightarrow> nat * nat" where
  "shift di dj = (\<lambda>(i,j). (i+di, j+dj))"

lemma shift_pair[simp]: "shift di dj (a,b) = (a+di,b+dj)"
  by(simp add: shift_def)

lemma in_shift_image: "(x,y) \<in> shift di dj ` M \<longleftrightarrow> di \<le> x \<and> dj \<le> y \<and> (x-di,y-dj) \<in> M"
  by(force simp: shift_def)

lemma inj_shift: "inj (shift i j)"
  by (auto simp: inj_def)

lemma shift_disj_shift: "\<lbrakk> s \<subseteq> sq n; s' \<subseteq> sq n;
  i \<ge> i' + 2^n \<or> i' \<ge> i + 2^n \<or> j \<ge> j' + 2^n \<or> j' \<ge> j + 2^n \<rbrakk> \<Longrightarrow>
  shift i j ` s \<inter> shift i' j' ` s' = {}"
by (auto simp add: in_shift_image)

text \<open>Convention: \<open>A, B :: points\<close>\<close>

text \<open>The layout of the 4 subquadrants @{term "Q t0 t1 t2 t3"} / @{term "Qsq A0 A1 A2 A3"}:
\<open>1 3
 0 2\<close>
That is, the \<open>x\<close> and \<open>y\<close> coordinates are shifted as follows (where 1 = $2^n$):
\<open>(0,1) (1,1)
 (0,0) (1,0)\<close>
\<close>

definition Qsq :: "nat \<Rightarrow> points \<Rightarrow> points \<Rightarrow> points \<Rightarrow> points \<Rightarrow> points" where
  "Qsq n A0 A1 A2 A3 =
  shift 0 0 ` A0 \<union> shift 0 (2^n) ` A1 \<union> shift (2^n) 0 ` A2 \<union> shift (2^n) (2^n) ` A3"

lemma sq_Suc_Qsq: "{0..<2 * 2 ^ n} \<times> {0..<2 * 2 ^ n} = Qsq n (sq n) (sq n) (sq n) (sq n)"
  by(auto simp: in_shift_image Qsq_def)

fun points :: "nat \<Rightarrow> qtb \<Rightarrow> (nat * nat) set" where
  "points n (L b) = (if b then sq n else {})" |
  "points (Suc n) (Q t0 t1 t2 t3) = Qsq n (points n t0) (points n t1) (points n t2) (points n t3)"

lemma points_subset: "height t \<le> n \<Longrightarrow> points n t \<subseteq> sq n"
proof(induction n t rule: points.induct)
  case 1
  then show ?case by simp
next
  case (2 n t0 t1 t2 t3)
  from "2.prems" have h: "height t0 \<le> n" "height t1 \<le> n" "height t2 \<le> n" "height t3 \<le> n"
    by (auto)
  thus ?case
    using "2.prems" "2.IH"(1)[OF h(1)] "2.IH"(2)[OF h(2)] "2.IH"(3)[OF h(3)] "2.IH"(4)[OF h(4)]
    by (auto simp add: Let_def shift_def Qsq_def)
next
  case 3 thus ?case
    by simp
qed

lemma point_Suc_Qc[simp]: "points (Suc n) (Qc t0 t1 t2 t3) = points (Suc n) (Q t0 t1 t2 t3)"
by(induction t0 t1 t2 t3 rule: Qc.induct) (auto simp: in_shift_image Qsq_def)

lemma get_points: "\<lbrakk> height t \<le> n; (i,j) \<in> sq n \<rbrakk> \<Longrightarrow> get n t i j = ((i,j) \<in> points n t)"
proof(induction n t i j rule: get.induct)
  case 1
  then show ?case by simp
next
  case (2 n t0 t1 t2 t3)
  thus ?case using points_subset[of t0 n] points_subset[of t1 n] points_subset[of t2 n]
    by(auto simp: select_def in_shift_image mod_minus Qsq_def)
next
  case 3
  then show ?case by simp
qed


subsubsection \<open>Union, Intersection Difference and Complement\<close>

fun union :: "qtb \<Rightarrow> qtb \<Rightarrow> qtb" where
  "union (L b) t = (if b then L True else t)" |
  "union t (L b) = (if b then L True else t)" |
  "union (Q s1 s2 s3 s4) (Q t1 t2 t3 t4) = Qc (union s1 t1) (union s2 t2) (union s3 t3) (union s4 t4)"

fun inter :: "qtb \<Rightarrow> qtb \<Rightarrow> qtb" where
  "inter (L b) t = (if b then t else L False)" |
  "inter t (L b) = (if b then t else L False)" |
  "inter (Q s1 s2 s3 s4) (Q t1 t2 t3 t4) = Qc (inter s1 t1) (inter s2 t2) (inter s3 t3) (inter s4 t4)"

fun negate :: "qtb \<Rightarrow> qtb" where
  "negate (L b) = L(\<not>b)" |
  "negate (Q t1 t2 t3 t4) = Q (negate t1) (negate t2) (negate t3) (negate t4)"

fun diff :: "qtb \<Rightarrow> qtb \<Rightarrow> qtb" where
  "diff (L b) t = (if b then negate t else L False)" |
  "diff t (L b) = (if b then L False else t)" |
  "diff (Q s1 s2 s3 s4) (Q t1 t2 t3 t4) = Qc (diff s1 t1) (diff s2 t2) (diff s3 t3) (diff s4 t4)"


lemma Qsq_union:
  "Qsq n A0 A1 A2 A3 \<union> Qsq n B0 B1 B2 B3 = Qsq n (A0 \<union> B0) (A1 \<union> B1) (A2 \<union> B2) (A3 \<union> B3)"
  by(auto simp: Qsq_def)

lemma points_union:
  "max (height t1) (height t2) \<le> n \<Longrightarrow> points n (union t1 t2) = points n t1 \<union> points n t2"
proof(induction t1 t2 arbitrary: n rule: union.induct)
  case 1 thus ?case using Un_absorb2[OF points_subset] by simp
next
  case 2 thus ?case using Un_absorb1[OF points_subset] by simp
next
  case 3
  from "3.prems" obtain m where "n = Suc m" by (auto dest: Suc_le_D)
  thus ?case using 3 by (simp add: Qsq_union)
qed

lemma height_union: "height (union t1 t2) \<le> max (height t1) (height t2)"
proof(induction t1 t2 rule: union.induct)
  case 3 then show ?case
    by(auto simp add: height_Qc_Q le_max_iff_disj simp del: max.absorb1 max.absorb2 max.absorb3 max.absorb4)
qed auto

lemma height_union2: "\<lbrakk> height t1 \<le> n; height t2 \<le> n \<rbrakk> \<Longrightarrow> height (union t1 t2) \<le> n"
by (meson height_union le_trans max.bounded_iff)

lemma get_union:
  "max (height t1) (height t2) \<le> n \<Longrightarrow> get n (union t1 t2) i j = (get n t1 i j \<or> get n t2 i j)"
proof(induction t1 t2 arbitrary: i j n rule: union.induct)
  case 3
  from "3.prems" obtain m where "n = Suc m" by (auto dest: Suc_le_D)
  thus ?case using 3 by (auto simp add: get_Qc height_union2 select_def)
qed auto

lemma compressed_union: "compressed t1 \<Longrightarrow> compressed t2 \<Longrightarrow> compressed(union t1 t2)"
proof(induction t1 t2 arbitrary: rule: union.induct)
  case 1 thus ?case using Un_absorb2[OF points_subset] by simp
next
  case 2 thus ?case using Un_absorb1[OF points_subset] by simp
next
  case 3
  thus ?case
    by (metis compressedQD compressed_Qc union.simps(3))
qed

lemma Qsq_inter:
  "\<lbrakk> A0 \<subseteq> sq n; A1 \<subseteq> sq n; A2 \<subseteq> sq n; A3 \<subseteq> sq n;
     B0 \<subseteq> sq n; B1 \<subseteq> sq n; B2 \<subseteq> sq n; B3 \<subseteq> sq n \<rbrakk>
 \<Longrightarrow> Qsq n A0 A1 A2 A3 \<inter> Qsq n B0 B1 B2 B3 = Qsq n (A0 \<inter> B0) (A1 \<inter> B1) (A2 \<inter> B2) (A3 \<inter> B3)"
by(simp add: Qsq_def Int_Un_distrib Int_Un_distrib2 shift_disj_shift image_Int inj_shift)

lemma points_inter: "n \<ge> max (height t1) (height t2) \<Longrightarrow>
  points n (inter t1 t2) = points n t1 \<inter> points n t2"
proof(induction t1 t2 arbitrary: n rule: inter.induct)
  case 1 thus ?case by (simp add: inf_absorb2[OF points_subset])
next
  case 2 thus ?case by (simp add: inf_absorb1[OF points_subset])
next
  case 3
  from "3.prems" obtain m where "n = Suc m" by (auto dest: Suc_le_D)
  thus ?case using "3.prems" "3.IH"[of m]
    by (simp add: Qsq_inter points_subset)
qed

lemma height_inter: "height (inter t1 t2) \<le> max (height t1) (height t2)"
proof(induction t1 t2 rule: inter.induct)
  case 3 then show ?case
    by(auto simp add: height_Qc_Q le_max_iff_disj simp del: max.absorb1 max.absorb2 max.absorb3 max.absorb4)
qed auto

lemma height_inter2: "\<lbrakk> height t1 \<le> n; height t2 \<le> n \<rbrakk> \<Longrightarrow> height (inter t1 t2) \<le> n"
by (meson height_inter le_trans max.bounded_iff)

lemma get_inter:
  "\<lbrakk> height t1 \<le> n; height t2 \<le> n \<rbrakk> \<Longrightarrow> get n (inter t1 t2) i j = (get n t1 i j \<and> get n t2 i j)"
proof(induction t1 t2 arbitrary: i j n rule: union.induct)
  case 3
  from "3.prems" obtain m where "n = Suc m" by (auto dest: Suc_le_D)
  thus ?case using 3 by (auto simp add: get_Qc height_inter2 select_def)
qed auto

lemma compressed_inter: "compressed t1 \<Longrightarrow> compressed t2 \<Longrightarrow> compressed(inter t1 t2)"
proof(induction t1 t2 arbitrary: rule: inter.induct)
  case 1 thus ?case using Un_absorb2[OF points_subset] by simp
next
  case 2 thus ?case using Un_absorb1[OF points_subset] by simp
next
  case 3
  thus ?case
    by (metis compressedQD compressed_Qc inter.simps(3))
qed

(* A proof on the level of sets (liked for intersection) seems complicated.
  Element-level proof is fast enough *)
lemma Qsq_diff: "\<lbrakk> B0 \<subseteq> sq n; B1 \<subseteq> sq n; B2 \<subseteq> sq n; B3 \<subseteq> sq n; A0 \<subseteq> sq n; A1 \<subseteq> sq n; A2 \<subseteq> sq n; A3 \<subseteq> sq n \<rbrakk> \<Longrightarrow>
  Qsq n B0 B1 B2 B3 - Qsq n A0 A1 A2 A3 = Qsq n (B0 - A0) (B1 - A1) (B2 - A2) (B3 - A3)"
by (auto simp add: in_shift_image Qsq_def)

lemma points_negate: "n \<ge> height t \<Longrightarrow> points n (negate t) = sq n - points n t"
proof(induction t arbitrary: n rule: negate.induct)
  case 1 thus ?case by (simp)
next                                                                                           
  case (2 t0 t1 t2 t3)
  obtain m where [simp]: "n = Suc m" using Suc_le_D "2.prems" by auto
  thus ?case using "2.prems" "2.IH"[of m]
    by(simp add: sq_Suc_Qsq Qsq_diff points_subset)
qed

lemma negate_eq_L_iff: "compressed t \<Longrightarrow> negate t = L x \<longleftrightarrow> t = L(\<not>x)"
by(cases t) auto

lemma compressed_negate: "compressed t \<Longrightarrow> compressed(negate t)"
proof(induction t)
  case L thus ?case by simp
next
  case Q
  thus ?case using negate_eq_L_iff by force
qed

lemma points_diff: "n \<ge> max (height t1) (height t2) \<Longrightarrow>
  points n (diff t1 t2) = points n t1 - points n t2"
proof(induction t1 t2 arbitrary: n rule: diff.induct)
  case 1 thus ?case by (simp add: points_negate)
next
  case 2 thus ?case using points_subset by (simp add: diff_shunt)
next
  case 3
  from "3.prems" obtain m where "n = Suc m" by (auto dest: Suc_le_D)
  thus ?case using "3.prems" "3.IH"[of m]
    by (simp add: Qsq_diff points_subset)
qed

lemma compressed_diff: "compressed t1 \<Longrightarrow> compressed t2 \<Longrightarrow> compressed(diff t1 t2)"
proof(induction t1 t2 arbitrary: rule: diff.induct)
  case 1 thus ?case
    by (simp add: compressed_negate)
next
  case 2 thus ?case by simp
next
  case 3
  thus ?case
    by (metis compressedQD compressed_Qc diff.simps(3))
qed


subsection "Operation \<open>put\<close>"

fun put  :: "nat \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> nat \<Rightarrow> 'a qtree \<Rightarrow> 'a qtree" where
"put i j a 0 (L _) = L a" |
"put i j a (Suc n) t = modify (put (i mod 2^n) (j mod 2^n) a n) (i < 2^n) (j < 2^n)
  (case t of L b \<Rightarrow> (L b, L b, L b, L b) | Q t0 t1 t2 t3 \<Rightarrow> (t0,t1,t2,t3))"

lemma points_put: "\<lbrakk> height t \<le> n; (i,j) \<in> sq n \<rbrakk> \<Longrightarrow>
 points n (put i j b n t) = (if b then points n t \<union> {(i,j)} else points n t - {(i,j)})"
proof(induction i j b n t rule: put.induct)
  case 1
  then show ?case by (simp)
next
  case 2
  thus ?case unfolding mem_Sigma_iff using points_subset
    apply(simp add: select_def sq_Suc_Qsq Qsq_def mod_minus split: qtree.split)
    by(fastforce simp: mod_minus in_shift_image)  (*SLOW*)
qed auto

lemma height_put: "height t \<le> n \<Longrightarrow> height (put i j a n t) \<le> n"
proof(induction i j a n t rule: put.induct)
  case 2
  then show ?case by (auto simp: height_Qc_Q split: qtree.split)
qed auto

lemma get_put: "\<lbrakk> height t \<le> n; (i,j) \<in> sq n; (i',j') \<in> sq n \<rbrakk> \<Longrightarrow>
  get n (put i j a n t) i' j' = (if i'=i \<and> j'=j then a else get n t i' j')"
proof(induction i j a n t arbitrary: i' j' rule: put.induct)
  case 1
  then show ?case by (auto)
next
  case 2
  thus ?case 
    by(auto simp add: select_def mod_minus get_Qc height_put less_diff_conv2 split!: qtree.split)
qed auto

lemma compressed_put:
  "\<lbrakk> height t \<le> n; compressed t \<rbrakk> \<Longrightarrow> compressed (put i j a n t)"
proof(induction i j a n t rule: put.induct)
  case 1
  then show ?case by (simp)
next
  case 2
  thus ?case by (auto simp add: compressed_Qc split: qtree.split)
qed auto


subsection \<open>Extract Square\<close>

(* TODO: \<open>(Q t0 t1 t2 t3 =: t)\<close> *)

fun get_sq :: "nat \<Rightarrow> 'a qtree \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a qtree" where
"get_sq n (L b) m i j = L b" |
"get_sq n t 0 i j = L (get n t i j)" |
"get_sq (Suc n) (Q t0 t1 t2 t3) (Suc m) i j =
  (if i mod 2^n + 2^(m+1) \<le> 2^n \<and> j mod 2^n + 2^(m+1) \<le> 2^n
      then get_sq n (select (i < 2^n) (j < 2^n) t0 t1 t2 t3) (m+1) (i mod 2^n) (j mod 2^n)
      else qf Qc (get_sq (Suc n) (Q t0 t1 t2 t3) m) i j (2^m))"

lemma shift_shift: "shift i j ` (shift i' j' ` s) = shift (i+i') (j+j') ` s"
using image_iff by(fastforce simp add: shift_def)
lemma shift_shift2: "shift i j ` (shift i' j' ` s) = shift (i'+i) (j'+j) ` s"
by(simp add: shift_shift Groups.add_ac)

lemma shift_split: "shift i j ` s =
  shift (i - i mod 2^n) (j - j mod 2^n) ` (shift (i mod 2^n) (j mod 2^n) ` s)"
by (simp add: shift_shift)

lemma plus_pow_aux: "(i::nat) + 2^m \<le> 2*2^n \<Longrightarrow> i < 2 * 2 ^ n"
by (metis add_leD1 le_neq_implies_less less_exp nat_add_left_cancel_less not_add_less1)

lemma Qsq_lem: "\<lbrakk> A0 \<subseteq> sq n; A1 \<subseteq> sq n; A2 \<subseteq> sq n; A3 \<subseteq> sq n;
  i + 2 ^ m \<le> 2 ^ Suc n; j + 2 ^ m \<le> 2 ^ Suc n;
  i mod 2 ^ n + 2 ^ m \<le> 2 ^ n; j mod 2 ^ n + 2 ^ m \<le> 2 ^ n \<rbrakk> \<Longrightarrow>
  Qsq n A0 A1 A2 A3 \<inter> shift i j ` sq m =
  shift (i - i mod 2^n) (j - j mod 2^n) ` select (i < 2 ^ n) (j < 2 ^ n) A0 A1 A2 A3 \<inter> shift i j ` sq m"
by (auto simp: select_def Qsq_def mod_minus plus_pow_aux)

lemma f_select: "f (select x y a b c d) = select x y (f a) (f b) (f c) (f d)"
by(simp add: select_def)

lemma height_get_sq: "m \<le> n \<Longrightarrow> height (get_sq n t m i j) \<le> m"
proof(induction n t m i j rule: get_sq.induct)
  case (3 n t0 t1 t2 t3 m i j)
  have *: "i mod 2 ^ n + 2 * 2 ^ m \<le> 2 ^ n \<Longrightarrow> Suc m \<le> n"
    using power_le_imp_le_exp[of "2::nat" "Suc m" n] by simp
  show ?case
    using "3.IH" "3.prems" * by (auto simp add: height_Qc_Q Let_def)
qed auto

lemma shift_Qsq: "shift i j ` Qsq n A0 A1 A2 A3 =
 Qsq n (shift i j ` A0) (shift i j ` A1) (shift i j ` A2) (shift i j ` A3)"
by(simp add: Qsq_def image_Un shift_shift add.commute)

lemma points_get_sq:
  "\<lbrakk> height t \<le> n; i + 2^m \<le> 2^n; j + 2^m \<le> 2^n \<rbrakk> \<Longrightarrow>
  shift i j ` points m (get_sq n t m i j) = points n t \<inter> (shift i j ` sq m)"
proof (induction n t m i j rule: get_sq.induct)
  case 2
  then show ?case by (auto simp: get_points)
next
  case (3 n t0 t1 t2 t3 m1 i j)
  define m where "m = Suc m1" (* needed?*)
  let ?t = "Q t0 t1 t2 t3"
  show ?case
  proof (cases "i mod 2^n + 2^m \<le> 2^n \<and> j mod 2^n + 2^m \<le> 2^n")
    case True
    let ?sel = "select (i < 2 ^ n) (j < 2 ^ n) t0 t1 t2 t3"
    let ?i = "i mod 2^n" let ?j = "j mod 2^n"
    have 1: "height ?sel \<le> n" using "3.prems" by(auto simp: select_def)
    have 2: "points m (get_sq (Suc n) ?t m i j) = points m (get_sq n ?sel m ?i ?j)"
      using True unfolding get_sq.simps m_def by(simp add: Let_def)
    have 3: "shift ?i ?j ` points m (get_sq n ?sel m ?i ?j) = points n ?sel \<inter> shift ?i ?j ` sq m"
      using "3.IH"(1) 1 True by (simp add: m_def)
    have "shift i j ` points (Suc m1) (get_sq (Suc n) ?t (Suc m1) i j) =
          shift i j ` points m (get_sq n ?sel m ?i ?j)"
      using True unfolding get_sq.simps m_def by(simp add: Let_def)
    also have "\<dots> = shift (i - ?i) (j - ?j) ` shift ?i ?j ` points m (get_sq n ?sel m ?i ?j)"
      by (meson shift_split)
    also have "\<dots> = shift (i - ?i) (j - ?j) ` (points n ?sel \<inter> shift ?i ?j ` sq m)"
      using "3.IH"(1) 1 True by (simp add: m_def)
    also have "\<dots> = shift (i - ?i) (j - ?j) ` points n ?sel \<inter> shift i j ` sq m"
      using image_Int[OF inj_shift] shift_split by presburger
    also have "\<dots> = shift (i - ?i) (j - ?j) ` select (i < 2 ^ n) (j < 2 ^ n) (points n t0) (points n t1) (points n t2) (points n t3) \<inter> shift i j ` sq m"
      by(simp add: f_select)
    also have "\<dots> = points (Suc n) (Q t0 t1 t2 t3) \<inter> shift i j ` sq (Suc m1)"
      using "3.prems" True
      apply(subst Qsq_lem[symmetric])
      by(auto simp: points_subset m_def)
    finally show ?thesis .
  next
    case False
    have "shift i j ` points (Suc m1) (get_sq (Suc n) (Q t0 t1 t2 t3) (Suc m1) i j) =
      shift i j ` qf (Qsq m1) (\<lambda>x y. points m1 (get_sq (Suc n) ?t m1 x y)) i j (2^m1)"
      using False unfolding get_sq.simps m_def
        by(simp add: Let_def m_def del: de_Morgan_conj)
    also have "\<dots> = qf (Qsq m1) (\<lambda>x y. shift i j ` points m1 (get_sq (Suc n) ?t m1 x y)) i j (2^m1)"
      by(simp add: shift_Qsq)
    also have "\<dots> = points (Suc n) (Q t0 t1 t2 t3) \<inter> shift i j ` sq (Suc m1)"
      using "3.IH"(2-5) "3.prems" False unfolding get_sq.simps m_def
      by(simp add: sq_Suc_Qsq Qsq_def shift_shift2 image_Int[OF inj_shift] image_Un Int_Un_distrib add.commute)
    finally show ?thesis .
  qed
qed auto

lemma get_get_sq:
  "\<lbrakk> height t \<le> n; i + 2^m \<le> 2^n; j + 2^m \<le> 2^n; i' < 2^m; j' < 2^m \<rbrakk> \<Longrightarrow>
  get m (get_sq n t m i j) i' j' = get n t (i+i') (j+j')"
proof (induction n t m i j arbitrary: i' j' rule: get_sq.induct)
  case (3 n t0 t1 t2 t3 m i j)
  let ?t = "Q t0 t1 t2 t3"
  let ?sel = "select (i < 2 ^ n) (j < 2 ^ n) t0 t1 t2 t3"
  show ?case
  proof (cases "i mod 2^n + 2^(m+1) \<le> 2^n \<and> j mod 2^n + 2^(m+1) \<le> 2^n")
    case True
    have "get (Suc m) (get_sq (Suc n) ?t (Suc m) i j) i' j'
          = get (m+1) (get_sq n ?sel (m+1) (i mod 2 ^ n) (j mod 2 ^ n)) i' j'"
      using True by(simp)
    also have "\<dots> = get n ?sel (i mod 2 ^ n + i') (j mod 2 ^ n + j')"
      using True "3.prems" by(subst "3.IH"(1))(simp_all add: select_def)
    also have "\<dots> = get (Suc n) ?t (i + i') (j + j')"
      using True "3.prems" by(auto simp add: select_def mod_minus)
    finally show ?thesis .
  next
    case False
    have *: "i + 2 * 2 ^ m \<le> 2 * 2 ^ n \<Longrightarrow> m \<le> Suc n"
      using power_le_imp_le_exp[of "2::nat" m n] by linarith
    show ?thesis using False "3.prems" (*SLOW*)
      by(auto simp add: "3.IH"(2-5) get_Qc mod_minus select_def height_Qc_Q height_get_sq * )
  qed
qed auto

lemma compressed_get_sq:
  "\<lbrakk> height t \<le> n; compressed t \<rbrakk> \<Longrightarrow> compressed (get_sq n t m i j)"
proof (induction n t m i j rule: get_sq.induct)
  case (3 n t0 t1 t2 t3 m i j)
  then show ?case by (simp add: compressed_Qc select_def)
qed auto


subsection \<open>From Matrix to Quadtree\<close>


subsubsection \<open>Matrix as function\<close>

(* TODO mk exercise *)

definition shift_mx where
"shift_mx mx x y = (\<lambda>i j. mx (i+x) (j+y))"

fun qt_of_fun :: "(nat \<Rightarrow> nat \<Rightarrow> 'a) \<Rightarrow> nat \<Rightarrow> 'a qtree" where
"qt_of_fun mx (Suc n) = qf Qc (\<lambda>x y. qt_of_fun (shift_mx mx x y) n) 0 0 (2^n)" |
"qt_of_fun mx 0 = L(mx 0 0)"

lemma points_qt_of_fun: "points n (qt_of_fun mx n) = {(i,j) \<in> sq n. mx i j}"
proof(induction n arbitrary: mx)
  case 0
  then show ?case by (auto)
next
  case (Suc n)
  then show ?case by(auto simp add: shift_mx_def Suc_length_conv sq_Suc_Qsq Qsq_def Let_def)
qed

lemma compressed_qt_of_fun: "compressed (qt_of_fun mx n)"
proof(induction n arbitrary: mx)
  case 0
  then show ?case by simp
next
  case (Suc n)
  then show ?case by(simp add:compressed_Qc)
qed


subsubsection \<open>Matrix as list of lists\<close>

type_synonym 'a mx = "'a list list"

definition "sq_mx n mx = (length mx = 2^n \<and> (\<forall>xs \<in> set mx. length xs = 2^n))"

lemma sq_mx_0: "sq_mx 0 mx = (\<exists>x. mx = [[x]])"
by(auto simp: sq_mx_def length_Suc_conv)

text \<open>Decompose matrix into submatrices\<close>

definition decomp where
"decomp n mx = (let mx01 = take (2^n) mx; mx23 = drop (2^n) mx
  in (map (take (2^n)) mx01, map (drop (2^n)) mx01, map (take (2^n)) mx23, map (drop (2^n)) mx23))"

lemma decomp_sq_mx: "sq_mx (Suc n) mx \<Longrightarrow> (mx0,mx1,mx2,mx3) = decomp n mx \<Longrightarrow>
  sq_mx n mx0 \<and> sq_mx n mx1 \<and> sq_mx n mx2 \<and> sq_mx n mx3"
by(auto simp add: sq_mx_def min_def decomp_def Let_def dest: in_set_takeD in_set_dropD)

text \<open>Quadtree of matrix:\<close>

fun qt_of :: "nat \<Rightarrow> 'a mx \<Rightarrow> 'a qtree" where
"qt_of (Suc n) mx =
  (let (mx0,mx1,mx2,mx3) = decomp n mx
   in Qc (qt_of n mx0) (qt_of n mx1) (qt_of n mx2) (qt_of n mx3))" |
"qt_of 0 [[x]] = L x"

lemma height_qt_of: "sq_mx n mx \<Longrightarrow> height(qt_of n mx) \<le> n"
proof(induction n mx rule: qt_of.induct)
  case (1 n mx)
  obtain mx0 mx1 mx2 mx3 where *: "decomp n mx = (mx0,mx1,mx2,mx3)" by (metis prod_cases4)
  show ?case
    using * 1 by (fastforce simp: height_Qc_Q dest!: decomp_sq_mx)
qed (auto simp: sq_mx_def)

lemma compressed_qt_of: "sq_mx n mx \<Longrightarrow> compressed(qt_of n mx)"
proof(induction n mx rule: qt_of.induct)
  case (1 n mx)
  obtain mx0 mx1 mx2 mx3 where *: "decomp n mx = (mx0,mx1,mx2,mx3)" by (metis prod_cases4)
  show ?case
    using * 1 decomp_sq_mx[OF "1.prems"]
     by (simp add: compressed_Qc)
qed (auto simp: sq_mx_def)

lemma points_qt_of: "sq_mx n mx \<Longrightarrow> points n (qt_of n mx) = {(i,j) \<in> sq n. mx ! i ! j}"
proof(induction n arbitrary: mx)
  case 0
  then show ?case by (auto simp: sq_mx_0 split: if_splits)
next
  case (Suc n)
  obtain mx0 mx1 mx2 mx3 where *: "(mx0,mx1,mx2,mx3) = decomp n mx" by (metis prod_cases4)
  note ** = decomp_sq_mx[OF Suc.prems *]
  show ?case using Suc * **
    by(auto simp: Qsq_def decomp_def Let_def sq_mx_def add.commute in_shift_image mult_2)
qed

lemma get_qt_of: "\<lbrakk> sq_mx n mx; (i,j) \<in> sq n \<rbrakk> \<Longrightarrow> get n (qt_of n mx) i j = mx ! i ! j"
proof(safe,induction n arbitrary: mx i j)
  case 0
  then show ?case by (auto simp: sq_mx_0 split: if_splits)
next
  case (Suc n)
  obtain mx0 mx1 mx2 mx3 where *: "(mx0,mx1,mx2,mx3) = decomp n mx" by (metis prod_cases4)
  note ** = decomp_sq_mx[OF Suc.prems(1) *]
  show ?case using Suc * **
    by(simp add: decomp_def Let_def get_Qc height_qt_of select_def sq_mx_def mod_minus)
qed


subsection \<open>From Quadtree to Matrix\<close>

definition Qmx :: "'a mx \<Rightarrow> 'a mx \<Rightarrow> 'a mx \<Rightarrow> 'a mx \<Rightarrow> 'a mx" where
"Qmx mx0 mx1 mx2 mx3 = map2 (@) mx0 mx1 @ map2 (@) mx2 mx3"

fun mx_of :: "nat \<Rightarrow> 'a qtree \<Rightarrow> 'a mx" where
"mx_of n (L x) = replicate (2^n) (replicate (2^n) x)" |
"mx_of (Suc n) (Q t0 t1 t2 t3) =
  Qmx (mx_of n t0) (mx_of n t1) (mx_of n t2) (mx_of n t3)"

lemma nth_Qmx_select: "\<lbrakk> sq_mx n mx0; sq_mx n mx1; sq_mx n mx2; sq_mx n mx3; i < 2*2^n; j < 2*2^n \<rbrakk> \<Longrightarrow>
  Qmx mx0 mx1 mx2 mx3 ! i ! j = select (i < 2^n) (j < 2^n) mx0 mx1 mx2 mx3 ! (i mod 2^n) ! (j mod 2^n)"
by(auto simp: sq_mx_def Qmx_def select_def nth_append mod_minus)

lemma sq_mx_mx_of: "height t \<le> n \<Longrightarrow> sq_mx n (mx_of n t)"
by(induction n t rule: mx_of.induct)
  (auto simp: sq_mx_def Qmx_def mult_2 elim: in_set_zipE)

lemma mx_of_points: "height t \<le> n \<Longrightarrow> points n t = {(i,j) \<in> sq n. mx_of n t ! i ! j}"
proof(induction n t rule: mx_of.induct)
  case (2 n t0 t1 t2 t3)
  then show ?case
    by (auto simp: Qsq_def nth_Qmx_select[of n] sq_mx_mx_of select_def in_shift_image mod_if
             split!: if_splits)
qed auto

lemma mx_of_get: "\<lbrakk> height t \<le> n; (i,j) \<in> sq n \<rbrakk> \<Longrightarrow> mx_of n t ! i ! j = get n t i j"
proof(induction n t arbitrary: i j rule: mx_of.induct)
  case (2 n)
  then show ?case
    by (simp add: nth_Qmx_select[of n] sq_mx_mx_of select_def)
qed auto

(*
unused_thms
*)

end
