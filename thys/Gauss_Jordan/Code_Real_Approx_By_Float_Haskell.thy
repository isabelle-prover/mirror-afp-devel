(*  
    Title:      Code_Real_Approx_By_Float_Haskell.thy
    Author:     Jose Divasón <jose.divasonm at unirioja.es>
    Author:     Jesús Aransay <jesus-maria.aransay at unirioja.es>
*)

section{*Serialization of real numbers in Haskell*}

theory Code_Real_Approx_By_Float_Haskell
imports "~~/src/HOL/Library/Code_Real_Approx_By_Float"
begin

text{*\textbf{WARNING} This theory implements mathematical reals by machine
reals in Haskell, in a similar way to the work done in the theory @{text "Code_Real_Approx_By_Float_Haskell"}.
This is inconsistent.*}

subsection{*Implementation of real numbers in Haskell*}

code_printing
  type_constructor real \<rightharpoonup> (Haskell) "Prelude.Double" (*Double precission*)
  | constant "0 :: real" \<rightharpoonup> (Haskell) "0.0"
  | constant "1 :: real" \<rightharpoonup> (Haskell) "1.0"
  | constant "real_of_integer" \<rightharpoonup> (Haskell) "Prelude.fromIntegral (_)"
  | class_instance real :: "HOL.equal" => (Haskell) - (*This is necessary. See the tutorial on code generation, page 29*)
  | constant "HOL.equal :: real \<Rightarrow> real \<Rightarrow> bool" \<rightharpoonup>
    (Haskell) "(_) == (_)"
  |  constant "op < :: real => real => bool" \<rightharpoonup>
    (Haskell) "_ < _"
  |  constant "op \<le> :: real => real => bool" \<rightharpoonup>
    (Haskell) "_ <= _"
  | constant "op + :: real \<Rightarrow> real \<Rightarrow> real" \<rightharpoonup>
    (Haskell) "(_) + (_)"
  | constant "op - :: real \<Rightarrow> real \<Rightarrow> real" \<rightharpoonup>
    (Haskell) "(_) - (_)"
  | constant "op * :: real \<Rightarrow> real \<Rightarrow> real" \<rightharpoonup>
    (Haskell) "(_) * (_)"
  | constant "op / :: real \<Rightarrow> real \<Rightarrow> real" \<rightharpoonup>
    (Haskell) " (_) '/ (_)"
  | constant "uminus :: real => real" \<rightharpoonup>
    (Haskell) "Prelude.negate"
  | constant "sqrt :: real => real" \<rightharpoonup>
    (Haskell) "Prelude.sqrt" 
  | constant Code_Real_Approx_By_Float.real_exp \<rightharpoonup>
    (Haskell) "Prelude.exp"
  | constant ln \<rightharpoonup>
    (Haskell) "Prelude.log"
  | constant cos \<rightharpoonup>
    (Haskell) "Prelude.cos"
  | constant sin \<rightharpoonup>
    (Haskell) "Prelude.sin"
  | constant tan \<rightharpoonup>
    (Haskell) "Prelude.tan"
  | constant pi \<rightharpoonup>
    (Haskell) "Prelude.pi"
  | constant arctan \<rightharpoonup>
    (Haskell) "Prelude.atan"
  | constant arccos \<rightharpoonup>
    (Haskell) "Prelude.acos"
  | constant arcsin \<rightharpoonup>
    (Haskell) "Prelude.asin"

text{*The following lemmas have to be removed from the code generator in order to be able to execute @{term "op <"} and @{term "op \<le>"}*}
declare real_less_code[code del]
declare real_less_eq_code[code del]

end
