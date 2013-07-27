(*=========================================================================*)
(* Code Generation Setup for Float                                         *)
(*=========================================================================*)

(* Author: Lei Yu, University of Cambridge *)

theory Code_Float
imports IEEE
begin

section{*Code Generation Setup for Floats*}

code_type float
  (SML   "real")
  (OCaml "float")

code_const "Plus_zero :: float"
  (SML   "0.0")
  (OCaml "0.0")
declare Plus_zero_def[code del]

definition One :: float where
"One = Abs_float (0, bias float_format, 0)"
declare One_def[code del]

code_const "One :: float"
  (SML   "1.0")
  (OCaml "1.0")
declare one_real_code[code_unfold del]

code_const "float_eq :: float \<Rightarrow> float \<Rightarrow> bool"
  (SML   "Real.== ((_), (_))")
  (OCaml "Pervasives.(=)")
declare float_eq_def[code del]

code_const "Orderings.less_eq :: float \<Rightarrow> float \<Rightarrow> bool"
  (SML   "Real.<= ((_), (_))")
  (OCaml "Pervasives.(<=)")
declare less_float_def [code del]

code_const "Orderings.less :: float \<Rightarrow> float \<Rightarrow> bool"
  (SML   "Real.< ((_), (_))")
  (OCaml "Pervasives.(<)")
declare less_eq_float_def[code del]

code_const "op + :: float \<Rightarrow> float \<Rightarrow> float"
  (SML   "Real.+ ((_), (_))")
  (OCaml "Pervasives.( +. )")
declare plus_float_def[code del]

code_const "op * :: float \<Rightarrow> float \<Rightarrow> float"
  (SML   "Real.* ((_), (_))")
  (OCaml "Pervasives.( *. )")
declare times_float_def [code del]

code_const "op - :: float \<Rightarrow> float \<Rightarrow> float"
  (SML   "Real.- ((_), (_))")
  (OCaml "Pervasives.( -. )")
declare minus_float_def [code del]

code_const "float_neg :: float \<Rightarrow> float"
  (SML   "Real.~")
  (OCaml "Pervasives.( ~-. )")
declare float_neg_def [code del]

code_const "op / :: float \<Rightarrow> float \<Rightarrow> float"
  (SML   "Real.'/ ((_), (_))")
  (OCaml "Pervasives.( '/. )")
declare divide_float_def [code del]

code_const "float_eq :: float \<Rightarrow> float \<Rightarrow> bool"
  (SML   "Real.== ((_:real), (_))")


code_const "float_sqrt :: float \<Rightarrow> float"
  (SML   "Math.sqrt")
  (OCaml "Pervasives.sqrt")
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
