theory Wasm_Interpreter_Printing_Pure
  imports
    "../Wasm_Interpreter_Properties"
    Wasm_Type_Abs_Printing
    "HOL-Library.Code_Target_Numeral"
    "HOL-Library.Code_Bit_Shifts_for_Arithmetic"
begin

axiomatization where
  mem_grow_impl_is[code]: "mem_grow_impl m n = Some (mem_grow m n)"

definition "run = run_v (2^63) 300"

code_printing
  constant host_apply_impl \<rightharpoonup> (OCaml) "ImplWrapper.host'_apply'_impl"

export_code open run in OCaml

end
