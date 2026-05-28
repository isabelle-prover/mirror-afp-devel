theory Free_Product_Words
  imports Main
begin

section \<open>Free-product words\<close>

text \<open>
  Encodings of loops in the Seifert--van Kampen argument are expressed as words
  that alternate between generators from the left and right factors. This
  theory provides the basic word combinators, reversal operations, and
  reduction-oriented bookkeeping used by the later amalgamation quotients.
\<close>

datatype ('a, 'b) free_product_word =
    WordNil
  | WordLeft 'a "('a, 'b) free_product_word"
  | WordRight 'b "('a, 'b) free_product_word"

primrec fpw_concat ::
  "('a, 'b) free_product_word => ('a, 'b) free_product_word => ('a, 'b) free_product_word"
where
  "fpw_concat WordNil w2 = w2"
| "fpw_concat (WordLeft a rest) w2 = WordLeft a (fpw_concat rest w2)"
| "fpw_concat (WordRight b rest) w2 = WordRight b (fpw_concat rest w2)"

primrec fpw_length :: "('a, 'b) free_product_word => nat" where
  "fpw_length WordNil = 0"
| "fpw_length (WordLeft a rest) = Suc (fpw_length rest)"
| "fpw_length (WordRight b rest) = Suc (fpw_length rest)"

primrec fpw_reverse :: "('a, 'b) free_product_word => ('a, 'b) free_product_word" where
  "fpw_reverse WordNil = WordNil"
| "fpw_reverse (WordLeft a rest) = fpw_concat (fpw_reverse rest) (WordLeft a WordNil)"
| "fpw_reverse (WordRight b rest) = fpw_concat (fpw_reverse rest) (WordRight b WordNil)"

primrec fpw_map ::
  "('a => 'c) => ('b => 'd) => ('a, 'b) free_product_word => ('c, 'd) free_product_word"
where
  "fpw_map fl fr WordNil = WordNil"
| "fpw_map fl fr (WordLeft a rest) = WordLeft (fl a) (fpw_map fl fr rest)"
| "fpw_map fl fr (WordRight b rest) = WordRight (fr b) (fpw_map fl fr rest)"

lemma fpw_concat_nil_right [simp]:
  "fpw_concat w WordNil = w"
  by (induction w) simp_all

lemma fpw_concat_assoc [simp]:
  "fpw_concat (fpw_concat u v) w = fpw_concat u (fpw_concat v w)"
  by (induction u) simp_all

lemma fpw_reverse_concat [simp]:
  "fpw_reverse (fpw_concat u v) = fpw_concat (fpw_reverse v) (fpw_reverse u)"
  by (induction u) simp_all

lemma fpw_reverse_reverse [simp]:
  "fpw_reverse (fpw_reverse w) = w"
  by (induction w) simp_all

fun fpw_reduced :: "('a, 'b) free_product_word => bool" where
  "fpw_reduced WordNil = True"
| "fpw_reduced (WordLeft a WordNil) = True"
| "fpw_reduced (WordLeft a (WordLeft b rest)) = False"
| "fpw_reduced (WordLeft a (WordRight b rest)) = fpw_reduced (WordRight b rest)"
| "fpw_reduced (WordRight b WordNil) = True"
| "fpw_reduced (WordRight b (WordRight c rest)) = False"
| "fpw_reduced (WordRight b (WordLeft a rest)) = fpw_reduced (WordLeft a rest)"

fun fpw_inverse ::
  "('a::group_add, 'b::group_add) free_product_word =>
    ('a, 'b) free_product_word"
where
  "fpw_inverse WordNil = WordNil"
| "fpw_inverse (WordLeft a rest) =
     fpw_concat (fpw_inverse rest) (WordLeft (- a) WordNil)"
| "fpw_inverse (WordRight b rest) =
     fpw_concat (fpw_inverse rest) (WordRight (- b) WordNil)"

lemma fpw_inverse_concat:
  "fpw_inverse (fpw_concat u v) = fpw_concat (fpw_inverse v) (fpw_inverse u)"
  by (induction u) simp_all

lemma fpw_inverse_inverse [simp]:
  "fpw_inverse (fpw_inverse w) = w"
  by (induction w) (simp_all add: fpw_inverse_concat)

inductive fpw_reduction_step ::
  "('a::group_add, 'b::group_add) free_product_word =>
    ('a, 'b) free_product_word => bool"
where
  combine_left:
    "fpw_reduction_step
      (WordLeft a (WordLeft b rest))
      (WordLeft (a + b) rest)"
| combine_right:
    "fpw_reduction_step
      (WordRight a (WordRight b rest))
      (WordRight (a + b) rest)"
| remove_left_zero:
    "fpw_reduction_step (WordLeft 0 rest) rest"
| remove_right_zero:
    "fpw_reduction_step (WordRight 0 rest) rest"
| context_left:
    "fpw_reduction_step u v ==>
      fpw_reduction_step (WordLeft a u) (WordLeft a v)"
| context_right:
    "fpw_reduction_step u v ==>
      fpw_reduction_step (WordRight b u) (WordRight b v)"

inductive fpw_reduction ::
  "('a::group_add, 'b::group_add) free_product_word =>
    ('a, 'b) free_product_word => bool"
where
  refl [intro!, simp]: "fpw_reduction w w"
| sym: "fpw_reduction u v ==> fpw_reduction v u"
| trans: "fpw_reduction u v ==> fpw_reduction v w ==> fpw_reduction u w"
| step: "fpw_reduction_step u v ==> fpw_reduction u v"

lemma fpw_reduction_left_context:
  assumes "fpw_reduction u v"
  shows "fpw_reduction (WordLeft a u) (WordLeft a v)"
  using assms
proof (induction rule: fpw_reduction.induct)
  case (refl w)
  then show ?case by simp
next
  case (sym u v)
  then show ?case by (meson fpw_reduction.sym)
next
  case (trans u v w)
  then show ?case by (meson fpw_reduction.trans)
next
  case (step u v)
  then show ?case
    by (meson fpw_reduction.step fpw_reduction_step.context_left)
qed

lemma fpw_reduction_right_context:
  assumes "fpw_reduction u v"
  shows "fpw_reduction (WordRight b u) (WordRight b v)"
  using assms
proof (induction rule: fpw_reduction.induct)
  case (refl w)
  then show ?case by simp
next
  case (sym u v)
  then show ?case by (meson fpw_reduction.sym)
next
  case (trans u v w)
  then show ?case by (meson fpw_reduction.trans)
next
  case (step u v)
  then show ?case
    by (meson fpw_reduction.step fpw_reduction_step.context_right)
qed

end
