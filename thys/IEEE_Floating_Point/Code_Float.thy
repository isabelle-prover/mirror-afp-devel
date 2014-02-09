(*=========================================================================*)
(* Code Generation Setup for Float                                         *)
(*=========================================================================*)

(* Author: Lei Yu, University of Cambridge *)

theory Code_Float
imports IEEE
begin

section{*Code Generation Setup for Floats*}

code_printing type_constructor float \<rightharpoonup>
  (SML) "real" and (OCaml) "float"

code_printing constant "Plus_zero :: float" \<rightharpoonup>
  (SML) "0.0" and (OCaml) "0.0"
declare Plus_zero_def[code del]

definition One :: float where
"One = Abs_float (0, bias float_format, 0)"
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


(* Mapping natual numbers to floats *)
fun float_of :: "nat \<Rightarrow> float" where
  "float_of 0 = Plus_zero"
| "float_of (Suc n) = float_of n +  One "


lemma "float_of 2 < float_of 3 + float_of 4"
apply eval
done 


export_code float_of in SML

end
