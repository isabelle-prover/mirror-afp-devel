theory Amalgamated_Free_Product
  imports Equivalence_Quotients Free_Product_Words
begin

section \<open>Amalgamation quotients of free-product words\<close>

text \<open>
  This is the purely algebraic target of the later topological theorem. Starting
  from free-product words, the theory quotients by the relations induced by the
  common interface and packages the resulting equivalence classes as the abstract
  amalgamated free product.
\<close>

inductive amalgam_step ::
  "('h => 'a) => ('h => 'b) =>
    ('a, 'b) free_product_word => ('a, 'b) free_product_word => bool"
  for i1 :: "'h => 'a" and i2 :: "'h => 'b"
where
  identify:
    "amalgam_step i1 i2 (WordLeft (i1 h) rest) (WordRight (i2 h) rest)"

inductive amalgam_equiv ::
  "('h => 'a) => ('h => 'b) =>
    ('a, 'b) free_product_word => ('a, 'b) free_product_word => bool"
  for i1 :: "'h => 'a" and i2 :: "'h => 'b"
where
  refl [intro!, simp]: "amalgam_equiv i1 i2 w w"
| sym: "amalgam_equiv i1 i2 u v ==> amalgam_equiv i1 i2 v u"
| trans: "amalgam_equiv i1 i2 u v ==> amalgam_equiv i1 i2 v w ==> amalgam_equiv i1 i2 u w"
| step: "amalgam_step i1 i2 u v ==> amalgam_equiv i1 i2 u v"
| left_context:
    "amalgam_equiv i1 i2 u v ==> amalgam_equiv i1 i2 (WordLeft a u) (WordLeft a v)"
| right_context:
    "amalgam_equiv i1 i2 u v ==> amalgam_equiv i1 i2 (WordRight b u) (WordRight b v)"

interpretation amalgam_equiv_equiv: equivalence_relation "amalgam_equiv i1 i2"
proof
  show "amalgam_equiv i1 i2 x x" for x
    by (rule amalgam_equiv.refl)
next
  show "amalgam_equiv i1 i2 x y ==> amalgam_equiv i1 i2 y x" for x y
    by (rule amalgam_equiv.sym)
next
  show "amalgam_equiv i1 i2 x y ==> amalgam_equiv i1 i2 y z ==> amalgam_equiv i1 i2 x z" for x y z
    by (rule amalgam_equiv.trans)
qed

definition amalgam_class ::
  "('h => 'a) => ('h => 'b) =>
    ('a, 'b) free_product_word => (('a, 'b) free_product_word) set"
where
  "amalgam_class i1 i2 w = equiv_class (amalgam_equiv i1 i2) w"

definition amalgamated_free_product_space ::
  "('h => 'a) => ('h => 'b) =>
    (('a, 'b) free_product_word) set set"
where
  "amalgamated_free_product_space i1 i2 = quotient_space (amalgam_equiv i1 i2)"

lemma amalgam_class_eq_iff:
  "amalgam_class i1 i2 u = amalgam_class i1 i2 v \<longleftrightarrow> amalgam_equiv i1 i2 u v"
  unfolding amalgam_class_def
  by (rule amalgam_equiv_equiv.equiv_class_eq_iff)

inductive full_amalg_equiv ::
  "('h => 'a::group_add) => ('h => 'b::group_add) =>
    ('a, 'b) free_product_word => ('a, 'b) free_product_word => bool"
  for i1 :: "'h => 'a" and i2 :: "'h => 'b"
where
  refl [intro!, simp]: "full_amalg_equiv i1 i2 w w"
| sym: "full_amalg_equiv i1 i2 u v ==> full_amalg_equiv i1 i2 v u"
| trans:
    "full_amalg_equiv i1 i2 u v ==> full_amalg_equiv i1 i2 v w ==> full_amalg_equiv i1 i2 u w"
| of_amalg:
    "amalgam_equiv i1 i2 u v ==> full_amalg_equiv i1 i2 u v"
| of_reduction:
    "fpw_reduction u v ==> full_amalg_equiv i1 i2 u v"

interpretation full_amalg_equiv_equiv: equivalence_relation "full_amalg_equiv i1 i2"
proof
  show "full_amalg_equiv i1 i2 x x" for x
    by (rule full_amalg_equiv.refl)
next
  show "full_amalg_equiv i1 i2 x y ==> full_amalg_equiv i1 i2 y x" for x y
    by (rule full_amalg_equiv.sym)
next
  show
    "full_amalg_equiv i1 i2 x y ==> full_amalg_equiv i1 i2 y z ==> full_amalg_equiv i1 i2 x z"
    for x y z
    by (rule full_amalg_equiv.trans)
qed

definition full_amalg_class ::
  "('h => 'a::group_add) => ('h => 'b::group_add) =>
    ('a, 'b) free_product_word => (('a, 'b) free_product_word) set"
where
  "full_amalg_class i1 i2 w = equiv_class (full_amalg_equiv i1 i2) w"

definition full_amalgamated_free_product_space ::
  "('h => 'a::group_add) => ('h => 'b::group_add) =>
    (('a, 'b) free_product_word) set set"
where
  "full_amalgamated_free_product_space i1 i2 =
     quotient_space (full_amalg_equiv i1 i2)"

lemma full_amalg_class_eq_iff:
  "full_amalg_class i1 i2 u = full_amalg_class i1 i2 v \<longleftrightarrow> full_amalg_equiv i1 i2 u v"
  unfolding full_amalg_class_def
  by (rule full_amalg_equiv_equiv.equiv_class_eq_iff)

lemma full_amalg_class_in_space [intro]:
  "full_amalg_class i1 i2 w \<in> full_amalgamated_free_product_space i1 i2"
  unfolding full_amalg_class_def full_amalgamated_free_product_space_def quotient_space_def
  by blast

definition full_amalg_one ::
  "('h => 'a::group_add) => ('h => 'b::group_add) =>
    (('a, 'b) free_product_word) set"
where
  "full_amalg_one i1 i2 = full_amalg_class i1 i2 WordNil"

end
