subsection \<open>Tests\<close>
theory Karatsuba_Sqrt_Test
imports
  Karatsuba_Sqrt_Float
  "HOL-Library.Code_Target_Numeral"
begin

value "sqrt_rem' 123456"
value "sqrt_rem 123456"
value "Discrete.sqrt 123456"
value "sqrt_int_floor 123456"
value "sqrt_nat_ceiling 123456"
value "sqrt_int_ceiling 123456"
value "sqrt_float_interval 64 (Ivl 123456 123456)"

end