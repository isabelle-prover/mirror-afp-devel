theory Carrier_Amalgamated_Free_Product
  imports Amalgamated_Free_Product
begin

section \<open>Carrier-based amalgamated free products\<close>

text \<open>
  The abstract amalgamated free product is refined here to words whose letters
  lie in fixed carrier sets. That carrier-level control matches the way loop
  representatives are produced on the topological side and is what eventually
  lets the Seifert--van Kampen theorem talk about concrete fundamental-group
  carriers.
\<close>

fun fpw_in_space :: "'a set => 'b set => ('a, 'b) free_product_word => bool" where
  "fpw_in_space G H WordNil = True"
| "fpw_in_space G H (WordLeft a rest) = (a \<in> G \<and> fpw_in_space G H rest)"
| "fpw_in_space G H (WordRight b rest) = (b \<in> H \<and> fpw_in_space G H rest)"

definition carrier_fpw_space :: "'a set => 'b set => (('a, 'b) free_product_word) set" where
  "carrier_fpw_space G H = {w. fpw_in_space G H w}"

lemma carrier_fpw_space_iff [simp]:
  "w \<in> carrier_fpw_space G H \<longleftrightarrow> fpw_in_space G H w"
  unfolding carrier_fpw_space_def by simp

inductive carrier_amalgam_step ::
  "'h set => ('h => 'a) => ('h => 'b) =>
    ('a, 'b) free_product_word => ('a, 'b) free_product_word => bool"
  for K :: "'h set" and i1 :: "'h => 'a" and i2 :: "'h => 'b"
where
  identify:
    "h \<in> K \<Longrightarrow>
      carrier_amalgam_step K i1 i2
        (WordLeft (i1 h) rest)
        (WordRight (i2 h) rest)"

inductive carrier_amalgam_equiv ::
  "'h set => ('h => 'a) => ('h => 'b) =>
    ('a, 'b) free_product_word => ('a, 'b) free_product_word => bool"
  for K :: "'h set" and i1 :: "'h => 'a" and i2 :: "'h => 'b"
where
  refl [intro!, simp]: "carrier_amalgam_equiv K i1 i2 w w"
| sym:
    "carrier_amalgam_equiv K i1 i2 u v \<Longrightarrow>
      carrier_amalgam_equiv K i1 i2 v u"
| trans:
    "carrier_amalgam_equiv K i1 i2 u v \<Longrightarrow>
      carrier_amalgam_equiv K i1 i2 v w \<Longrightarrow>
      carrier_amalgam_equiv K i1 i2 u w"
| step:
    "carrier_amalgam_step K i1 i2 u v \<Longrightarrow>
      carrier_amalgam_equiv K i1 i2 u v"
| left_context:
    "carrier_amalgam_equiv K i1 i2 u v \<Longrightarrow>
      carrier_amalgam_equiv K i1 i2 (WordLeft a u) (WordLeft a v)"
| right_context:
    "carrier_amalgam_equiv K i1 i2 u v \<Longrightarrow>
      carrier_amalgam_equiv K i1 i2 (WordRight b u) (WordRight b v)"

interpretation carrier_amalgam_equiv_equiv:
  equivalence_relation "carrier_amalgam_equiv K i1 i2"
proof
  show "carrier_amalgam_equiv K i1 i2 x x" for x
    by (rule carrier_amalgam_equiv.refl)
next
  show "carrier_amalgam_equiv K i1 i2 x y \<Longrightarrow> carrier_amalgam_equiv K i1 i2 y x" for x y
    by (rule carrier_amalgam_equiv.sym)
next
  show
    "carrier_amalgam_equiv K i1 i2 x y \<Longrightarrow>
      carrier_amalgam_equiv K i1 i2 y z \<Longrightarrow>
      carrier_amalgam_equiv K i1 i2 x z" for x y z
    by (rule carrier_amalgam_equiv.trans)
qed

definition carrier_amalgam_class ::
  "'h set => ('h => 'a) => ('h => 'b) =>
    ('a, 'b) free_product_word => (('a, 'b) free_product_word) set"
where
  "carrier_amalgam_class K i1 i2 w =
    equiv_class (carrier_amalgam_equiv K i1 i2) w"

lemma carrier_amalgam_class_eq_iff:
  "carrier_amalgam_class K i1 i2 u = carrier_amalgam_class K i1 i2 v
    \<longleftrightarrow> carrier_amalgam_equiv K i1 i2 u v"
  unfolding carrier_amalgam_class_def
  by (rule carrier_amalgam_equiv_equiv.equiv_class_eq_iff)

inductive carrier_fpw_reduction_step ::
  "'a set => 'b set =>
    ('a => 'a => 'a) => 'a => ('b => 'b => 'b) => 'b =>
    ('a, 'b) free_product_word => ('a, 'b) free_product_word => bool"
  for G1 :: "'a set" and G2 :: "'b set"
    and mult1 :: "'a => 'a => 'a" and one1 :: "'a"
    and mult2 :: "'b => 'b => 'b" and one2 :: "'b"
where
  combine_left:
    "\<lbrakk>a \<in> G1; b \<in> G1; mult1 a b \<in> G1; fpw_in_space G1 G2 rest\<rbrakk> \<Longrightarrow>
      carrier_fpw_reduction_step G1 G2 mult1 one1 mult2 one2
      (WordLeft a (WordLeft b rest))
      (WordLeft (mult1 a b) rest)"
| combine_right:
    "\<lbrakk>a \<in> G2; b \<in> G2; mult2 a b \<in> G2; fpw_in_space G1 G2 rest\<rbrakk> \<Longrightarrow>
      carrier_fpw_reduction_step G1 G2 mult1 one1 mult2 one2
      (WordRight a (WordRight b rest))
      (WordRight (mult2 a b) rest)"
| remove_left_one:
    "\<lbrakk>one1 \<in> G1; fpw_in_space G1 G2 rest\<rbrakk> \<Longrightarrow>
      carrier_fpw_reduction_step G1 G2 mult1 one1 mult2 one2
      (WordLeft one1 rest) rest"
| remove_right_one:
    "\<lbrakk>one2 \<in> G2; fpw_in_space G1 G2 rest\<rbrakk> \<Longrightarrow>
      carrier_fpw_reduction_step G1 G2 mult1 one1 mult2 one2
      (WordRight one2 rest) rest"
| context_left:
    "\<lbrakk>a \<in> G1; carrier_fpw_reduction_step G1 G2 mult1 one1 mult2 one2 u v\<rbrakk> \<Longrightarrow>
      carrier_fpw_reduction_step G1 G2 mult1 one1 mult2 one2
        (WordLeft a u) (WordLeft a v)"
| context_right:
    "\<lbrakk>b \<in> G2; carrier_fpw_reduction_step G1 G2 mult1 one1 mult2 one2 u v\<rbrakk> \<Longrightarrow>
      carrier_fpw_reduction_step G1 G2 mult1 one1 mult2 one2
        (WordRight b u) (WordRight b v)"

inductive carrier_fpw_reduction ::
  "'a set => 'b set =>
    ('a => 'a => 'a) => 'a => ('b => 'b => 'b) => 'b =>
    ('a, 'b) free_product_word => ('a, 'b) free_product_word => bool"
  for G1 :: "'a set" and G2 :: "'b set"
    and mult1 :: "'a => 'a => 'a" and one1 :: "'a"
    and mult2 :: "'b => 'b => 'b" and one2 :: "'b"
where
  refl [intro!, simp]: "carrier_fpw_reduction G1 G2 mult1 one1 mult2 one2 w w"
| sym:
    "carrier_fpw_reduction G1 G2 mult1 one1 mult2 one2 u v \<Longrightarrow>
      carrier_fpw_reduction G1 G2 mult1 one1 mult2 one2 v u"
| trans:
    "carrier_fpw_reduction G1 G2 mult1 one1 mult2 one2 u v \<Longrightarrow>
      carrier_fpw_reduction G1 G2 mult1 one1 mult2 one2 v w \<Longrightarrow>
      carrier_fpw_reduction G1 G2 mult1 one1 mult2 one2 u w"
| step:
    "carrier_fpw_reduction_step G1 G2 mult1 one1 mult2 one2 u v \<Longrightarrow>
      carrier_fpw_reduction G1 G2 mult1 one1 mult2 one2 u v"

lemma carrier_fpw_reduction_left_context:
  assumes "carrier_fpw_reduction G1 G2 mult1 one1 mult2 one2 u v"
    and "a \<in> G1"
  shows "carrier_fpw_reduction G1 G2 mult1 one1 mult2 one2 (WordLeft a u) (WordLeft a v)"
  using assms
proof (induction rule: carrier_fpw_reduction.induct)
  case (refl w)
  then show ?case by simp
next
  case (sym u v)
  then show ?case by (meson carrier_fpw_reduction.sym)
next
  case (trans u v w)
  then show ?case by (meson carrier_fpw_reduction.trans)
next
  case (step u v)
  then show ?case
    by (meson carrier_fpw_reduction.step carrier_fpw_reduction_step.context_left)
qed

lemma carrier_fpw_reduction_right_context:
  assumes "carrier_fpw_reduction G1 G2 mult1 one1 mult2 one2 u v"
    and "b \<in> G2"
  shows "carrier_fpw_reduction G1 G2 mult1 one1 mult2 one2 (WordRight b u) (WordRight b v)"
  using assms
proof (induction rule: carrier_fpw_reduction.induct)
  case (refl w)
  then show ?case by simp
next
  case (sym u v)
  then show ?case by (meson carrier_fpw_reduction.sym)
next
  case (trans u v w)
  then show ?case by (meson carrier_fpw_reduction.trans)
next
  case (step u v)
  then show ?case
    by (meson carrier_fpw_reduction.step carrier_fpw_reduction_step.context_right)
qed

lemma carrier_fpw_reduction_step_preserves_space:
  assumes step: "carrier_fpw_reduction_step G1 G2 mult1 one1 mult2 one2 u v"
  shows "fpw_in_space G1 G2 u" and "fpw_in_space G1 G2 v"
  using step
proof (induction rule: carrier_fpw_reduction_step.induct)
  case (combine_left a b rest)
  then show "fpw_in_space G1 G2 (WordLeft a (WordLeft b rest))"
    by simp
  show "fpw_in_space G1 G2 (WordLeft (mult1 a b) rest)"
    using combine_left by simp
next
  case (combine_right a b rest)
  then show "fpw_in_space G1 G2 (WordRight a (WordRight b rest))"
    by simp
  show "fpw_in_space G1 G2 (WordRight (mult2 a b) rest)"
    using combine_right by simp
next
  case (remove_left_one rest)
  then show "fpw_in_space G1 G2 (WordLeft one1 rest)"
    by simp
  show "fpw_in_space G1 G2 rest"
    using remove_left_one by simp
next
  case (remove_right_one rest)
  then show "fpw_in_space G1 G2 (WordRight one2 rest)"
    by simp
  show "fpw_in_space G1 G2 rest"
    using remove_right_one by simp
next
  case (context_left a u v)
  then show "fpw_in_space G1 G2 (WordLeft a u)"
    by simp
  show "fpw_in_space G1 G2 (WordLeft a v)"
    using context_left by simp
next
  case (context_right b u v)
  then show "fpw_in_space G1 G2 (WordRight b u)"
    by simp
  show "fpw_in_space G1 G2 (WordRight b v)"
    using context_right by simp
qed

lemma carrier_fpw_reduction_step_preserves_space_iff:
  assumes step: "carrier_fpw_reduction_step G1 G2 mult1 one1 mult2 one2 u v"
  shows "fpw_in_space G1 G2 u \<longleftrightarrow> fpw_in_space G1 G2 v"
  using carrier_fpw_reduction_step_preserves_space[OF step] by blast

lemma carrier_fpw_reduction_preserves_space_iff:
  assumes rel: "carrier_fpw_reduction G1 G2 mult1 one1 mult2 one2 u v"
  shows "fpw_in_space G1 G2 u \<longleftrightarrow> fpw_in_space G1 G2 v"
  using rel
proof (induction rule: carrier_fpw_reduction.induct)
  case (refl w)
  then show ?case by simp
next
  case (sym u v)
  then show ?case by simp
next
  case (trans u v w)
  then show ?case by blast
next
  case (step u v)
  then show ?case
    by (rule carrier_fpw_reduction_step_preserves_space_iff)
qed

inductive carrier_full_amalg_equiv ::
  "'a set => 'b set => 'h set => ('h => 'a) => ('h => 'b) =>
    ('a => 'a => 'a) => 'a => ('b => 'b => 'b) => 'b =>
    ('a, 'b) free_product_word => ('a, 'b) free_product_word => bool"
  for G1 :: "'a set" and G2 :: "'b set"
    and K :: "'h set" and i1 :: "'h => 'a" and i2 :: "'h => 'b"
    and mult1 :: "'a => 'a => 'a" and one1 :: "'a"
    and mult2 :: "'b => 'b => 'b" and one2 :: "'b"
where
  refl [intro!, simp]:
    "carrier_full_amalg_equiv G1 G2 K i1 i2 mult1 one1 mult2 one2 w w"
| sym:
    "carrier_full_amalg_equiv G1 G2 K i1 i2 mult1 one1 mult2 one2 u v \<Longrightarrow>
      carrier_full_amalg_equiv G1 G2 K i1 i2 mult1 one1 mult2 one2 v u"
| trans:
    "carrier_full_amalg_equiv G1 G2 K i1 i2 mult1 one1 mult2 one2 u v \<Longrightarrow>
      carrier_full_amalg_equiv G1 G2 K i1 i2 mult1 one1 mult2 one2 v w \<Longrightarrow>
      carrier_full_amalg_equiv G1 G2 K i1 i2 mult1 one1 mult2 one2 u w"
| of_amalg:
    "carrier_amalgam_equiv K i1 i2 u v \<Longrightarrow>
      carrier_full_amalg_equiv G1 G2 K i1 i2 mult1 one1 mult2 one2 u v"
| of_reduction:
    "carrier_fpw_reduction G1 G2 mult1 one1 mult2 one2 u v \<Longrightarrow>
      carrier_full_amalg_equiv G1 G2 K i1 i2 mult1 one1 mult2 one2 u v"

interpretation carrier_full_amalg_equiv_equiv:
  equivalence_relation
    "carrier_full_amalg_equiv G1 G2 K i1 i2 mult1 one1 mult2 one2"
proof
  show "carrier_full_amalg_equiv G1 G2 K i1 i2 mult1 one1 mult2 one2 x x" for x
    by (rule carrier_full_amalg_equiv.refl)
next
  show
    "carrier_full_amalg_equiv G1 G2 K i1 i2 mult1 one1 mult2 one2 x y \<Longrightarrow>
      carrier_full_amalg_equiv G1 G2 K i1 i2 mult1 one1 mult2 one2 y x" for x y
    by (rule carrier_full_amalg_equiv.sym)
next
  show
    "carrier_full_amalg_equiv G1 G2 K i1 i2 mult1 one1 mult2 one2 x y \<Longrightarrow>
      carrier_full_amalg_equiv G1 G2 K i1 i2 mult1 one1 mult2 one2 y z \<Longrightarrow>
      carrier_full_amalg_equiv G1 G2 K i1 i2 mult1 one1 mult2 one2 x z" for x y z
    by (rule carrier_full_amalg_equiv.trans)
qed

definition carrier_full_amalg_class ::
  "'a set => 'b set => 'h set => ('h => 'a) => ('h => 'b) =>
    ('a => 'a => 'a) => 'a => ('b => 'b => 'b) => 'b =>
    ('a, 'b) free_product_word => (('a, 'b) free_product_word) set"
where
  "carrier_full_amalg_class G1 G2 K i1 i2 mult1 one1 mult2 one2 w =
    equiv_class (carrier_full_amalg_equiv G1 G2 K i1 i2 mult1 one1 mult2 one2) w"

definition carrier_full_amalgamated_free_product_space ::
  "'a set => 'b set => 'h set => ('h => 'a) => ('h => 'b) =>
    ('a => 'a => 'a) => 'a => ('b => 'b => 'b) => 'b =>
    (('a, 'b) free_product_word) set set"
where
  "carrier_full_amalgamated_free_product_space G1 G2 K i1 i2 mult1 one1 mult2 one2 =
    carrier_full_amalg_class G1 G2 K i1 i2 mult1 one1 mult2 one2 ` carrier_fpw_space G1 G2"

lemma carrier_full_amalg_class_eq_iff:
  "carrier_full_amalg_class G1 G2 K i1 i2 mult1 one1 mult2 one2 u =
      carrier_full_amalg_class G1 G2 K i1 i2 mult1 one1 mult2 one2 v
    \<longleftrightarrow> carrier_full_amalg_equiv G1 G2 K i1 i2 mult1 one1 mult2 one2 u v"
  unfolding carrier_full_amalg_class_def
  by (rule carrier_full_amalg_equiv_equiv.equiv_class_eq_iff)

lemma carrier_full_amalg_class_in_space [intro]:
  assumes "fpw_in_space G1 G2 w"
  shows
    "carrier_full_amalg_class G1 G2 K i1 i2 mult1 one1 mult2 one2 w \<in>
      carrier_full_amalgamated_free_product_space G1 G2 K i1 i2 mult1 one1 mult2 one2"
  using assms
  unfolding carrier_full_amalgamated_free_product_space_def
  by simp

definition carrier_full_amalg_one ::
  "'a set => 'b set => 'h set => ('h => 'a) => ('h => 'b) =>
    ('a => 'a => 'a) => 'a => ('b => 'b => 'b) => 'b =>
    (('a, 'b) free_product_word) set"
where
  "carrier_full_amalg_one G1 G2 K i1 i2 mult1 one1 mult2 one2 =
    carrier_full_amalg_class G1 G2 K i1 i2 mult1 one1 mult2 one2 WordNil"

end
