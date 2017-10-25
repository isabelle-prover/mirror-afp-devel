(* Author: Lei Yu, University of Cambridge *)

section \<open>Code Generation Setup for Floats\<close>

theory Code_Float
  imports
    Conversion_IEEE_Float
begin

code_printing type_constructor float \<rightharpoonup>
  (SML) "real" and (OCaml) "float"

code_printing constant "Plus_zero :: float" \<rightharpoonup>
  (SML) "0.0" and (OCaml) "0.0"
declare Plus_zero_def[code del]

definition One :: float
  where "One = Abs_float (0, bias float_format, 0)"
declare One_def[code del]

code_printing constant "One :: float" \<rightharpoonup>
  (SML) "1.0" and (OCaml) "1.0"
declare one_real_code[code_unfold del]

code_printing constant "float_eq :: float \<Rightarrow> float \<Rightarrow> bool" \<rightharpoonup>
  (SML) "Real.== ((_:real), (_))" and (OCaml) "Pervasives.(=)"
declare float_eq_def[code del]

code_printing constant "Orderings.less_eq :: float \<Rightarrow> float \<Rightarrow> bool" \<rightharpoonup>
  (SML) "Real.<= ((_), (_))" and (OCaml) "Pervasives.(<=)"
declare less_float_def [code del]

code_printing constant "Orderings.less :: float \<Rightarrow> float \<Rightarrow> bool" \<rightharpoonup>
  (SML) "Real.< ((_), (_))" and (OCaml) "Pervasives.(<)"
declare less_eq_float_def[code del]

code_printing constant "op + :: float \<Rightarrow> float \<Rightarrow> float" \<rightharpoonup>
  (SML) "Real.+ ((_), (_))" and (OCaml) "Pervasives.( +. )"
declare plus_float_def[code del]

code_printing constant "op * :: float \<Rightarrow> float \<Rightarrow> float" \<rightharpoonup>
  (SML) "Real.* ((_), (_))" and (OCaml) "Pervasives.( *. )"
declare times_float_def [code del]

code_printing constant "op - :: float \<Rightarrow> float \<Rightarrow> float" \<rightharpoonup>
  (SML) "Real.- ((_), (_))" and (OCaml) "Pervasives.( -. )"
declare minus_float_def [code del]

code_printing constant "float_neg :: float \<Rightarrow> float" \<rightharpoonup>
  (SML) "Real.~" and (OCaml) "Pervasives.( ~-. )"
declare float_neg_def [code del]

code_printing constant "op / :: float \<Rightarrow> float \<Rightarrow> float" \<rightharpoonup>
  (SML) "Real.'/ ((_), (_))" and (OCaml) "Pervasives.( '/. )"
declare divide_float_def [code del]

code_printing constant "float_sqrt :: float \<Rightarrow> float" \<rightharpoonup>
  (SML) "Math.sqrt" and (OCaml) "Pervasives.sqrt"
declare sqrt_def[code del]

code_printing constant "Plus_infinity :: float" \<rightharpoonup>
  (SML) "Real.posInf"
declare Plus_infinity_def[code del]

code_printing constant "Minus_infinity :: float" \<rightharpoonup>
  (SML) "Real.negInf"
declare Minus_infinity_def[code del]

code_printing constant "Isnormal :: float \<Rightarrow> bool" \<rightharpoonup>
  (SML) "Real.isNormal"
declare [[code drop: "Isnormal"]]

code_printing constant "Finite :: float \<Rightarrow> bool" \<rightharpoonup>
  (SML) "Real.isFinite"
declare [[code drop: "Finite"]]

code_printing constant "Isnan :: float \<Rightarrow> bool" \<rightharpoonup>
  (SML) "Real.isNan"
declare [[code drop: "Isnan"]]

text \<open>Mapping natural numbers to floats.\<close>
fun float_of :: "nat \<Rightarrow> float"
where
  "float_of 0 = Plus_zero"
| "float_of (Suc n) = float_of n + One"

lemma "float_of 2 < float_of 3 + float_of 4"
  by eval

export_code float_of in SML

subsection \<open>Conversion from int\<close>

definition "float_of_int i = Float (real_of_int i)"

context includes integer.lifting begin
lift_definition float_of_integer::"integer \<Rightarrow> float" is float_of_int .
end

lemma float_of_int[code]:
  "float_of_int i = float_of_integer (integer_of_int i)"
  by (auto simp: float_of_integer_def)

code_printing
  constant "float_of_integer :: integer \<Rightarrow> float" \<rightharpoonup> (SML) "Real.fromLargeInt"
declare [[code drop: float_of_integer]]


subsection \<open>Conversion to and from software floats\<close>

lemma valid_man_exp_float_format:
  "valid_man_exp float_format m e \<longleftrightarrow> \<bar>m\<bar> < 4503599627370496 \<and> - 971 < e \<and> e < 973"
  by (simp add: valid_man_exp_def float_format_def bias_def bitlen_le_iff_power)

code_printing
  code_module "IEEE_Mantissa_Exponent" \<rightharpoonup> (SML)
\<open>
structure IEEE_Mantissa_Exponent =
struct
fun to_man_exp_float x =
  case Real.toManExp x of {man = m, exp = e} =>
    (Real.floor (Real.* (m, Math.pow (2.0, 53.0))), IntInf.- (e, 53))
fun from_man_exp_float m e =
  if IntInf.abs m < 4503599627370496 andalso ~971 < e andalso e < 973
  then Real.fromManExp {man = Real.fromLargeInt m, exp = e}
  else Real.posInf
end
\<close>
\<comment>\<open>compare with the definitions of @{term to_man_exp_float} and @{term from_man_exp_float}
  using @{thm valid_man_exp_float_format}\<close>
code_printing
  constant "to_man_exp_float :: float \<Rightarrow> integer * integer" \<rightharpoonup> (SML) "IEEE'_Mantissa'_Exponent.to'_man'_exp'_float" |
  constant "from_man_exp_float :: integer \<Rightarrow> integer \<Rightarrow> float" \<rightharpoonup> (SML) "IEEE'_Mantissa'_Exponent.from'_man'_exp'_float"
declare [[code drop: to_man_exp_float]]
declare [[code drop: from_man_exp_float]]

lemma
  "\<forall>m\<in>{-10000..<10000}. \<forall>e\<in>{0..<100}. Float_of_IEEE (IEEE_of_Float (Float.Float m e)) = Float.Float m e"
  by eval

lemma "(IEEE_of_Float (Float.Float 1 1000)) \<doteq> Plus_infinity"
  by eval

end
