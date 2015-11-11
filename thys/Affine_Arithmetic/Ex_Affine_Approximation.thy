section {* Examples *}
theory Ex_Affine_Approximation
imports
  Affine_Code
begin

approximate_affine rotate45' "\<lambda>(x, y).
  (  FloatR 1 (- 1) * x + FloatR (- 435) (- 9) * y,
   FloatR 435 (- 9) * x +    FloatR 1 (- 1) * y)"

definition X'::"(real*real) aform"
  where "X' = aform_of_ivl (real_of_float 2, real_of_float 1) (real_of_float 3, real_of_float 5)"

fun rotate_aform where
  "rotate_aform x i = (((the o (\<lambda>x. rotate45' 30 (FloatR 1 (- 3)) x []))^^i) x)"

value "rotate_aform X' 70"

approximate_affine translate "\<lambda>(x, y). (FloatR 1024 (- 1) + x, FloatR 1024 (- 1) + y)"

fun translatei where "translatei x i = (((the o (\<lambda>x. translate 7 (FloatR 1 (- 7)) x []))^^i) x)"

value "translatei X' 50"

hide_const (open) X' rotate_aform translate translatei rotate45'

end
