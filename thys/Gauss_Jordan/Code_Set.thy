(*  
    Title:      Code_Set.thy
    Author:     Jose Divasón <jose.divasonm at unirioja.es>
    Author:     Jesús Aransay <jesus-maria.aransay at unirioja.es>
*)

section "Code set"

theory Code_Set
imports
  "~~/src/HOL/Library/Cardinality"
begin

text{*The following setup could help to get code generation for List.coset, 
  but it neither works correctly it complains that code
  equations for remove are missed, even when List.coset should be rewritten
  to an enum:*}

declare minus_coset_filter [code del]
declare remove_code(2) [code del]
declare insert_code(2) [code del]
declare inter_coset_fold [code del]
declare compl_coset[code del]
declare Cardinality.card'_code(2)[code del]

code_datatype set

text{*The following code equation could be useful to avoid the problem of
  code generation for List.coset []:*}

lemma [code]: "List.coset (l::'a::enum list) = set (enum_class.enum) - set l"
  by (metis Compl_eq_Diff_UNIV coset_def enum_UNIV)

text{*Now the following examples work:*}

value "UNIV::bool set"
value "List.coset ([]::bool list)"
value "UNIV::Enum.finite_2 set"
value "List.coset ([]::Enum.finite_2 list)"
value "List.coset ([]::Enum.finite_5 list)"

end
