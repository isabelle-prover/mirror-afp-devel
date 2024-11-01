section \<open>Code generation tests\<close>
theory Boustrophedon_Transform_Impl_Test
imports
  Boustrophedon_Transform_Impl
  Euler_Numbers
  "HOL-Library.Code_Lazy" 
  "HOL-Library.Code_Target_Numeral"
begin

text \<open>
  We now test all the various functions we have implemented.
\<close>
value "zigzag_number 100"
value "zigzag_numbers 100"
value "secant_number 100"
value "secant_numbers 100"
value "tangent_number 100"
value "tangent_numbers 100"
value "euler_number 100"
value "entringer_number 100 32"

value "Bernpolys 20 :: real poly list"
value "Bernpoly 10 :: real poly"
value "Bernpoly 51 :: real poly"
value "bernpoly 10 (1/2) :: real"

value "Euler_polys 20 :: rat poly list"
value "Euler_poly 10 :: rat poly"
value "Euler_poly 51 :: rat poly"
value "euler_poly 51 (3/2) :: real"

code_lazy_type stream

text \<open>
  As an example of the Boustrophedon transform, the following is the transform of the sequence
  $1, 0, 0, 0, \ldots$ with the exponential generating function $1$.
  The transformed sequence is the zigzag numbers, with the exponential generating
  function $\sec x + \tan x$.
\<close>
value "stake 20 (seidel_triangle_rows (1 ## sconst (0::int)))"
value "stake 20 (boustrophedon_stream (1 ## sconst (0::int)))"

text \<open>
  The following is another example from the paper by Millar et al: the
  Boustrophedon transform of the sequence $1, 1, 1, \ldots$ with the exponential
  generating function $e^x$.
  The exponential generating function of the transformed sequence is
  $e^x (\sec x + \tan x)$.
\<close>
value "stake 20 (seidel_triangle_rows (sconst (1::int)))"
value "stake 20 (boustrophedon_stream (sconst (1::int)))"

end