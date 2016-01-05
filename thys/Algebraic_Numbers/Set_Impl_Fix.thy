(*  
    Author:      René Thiemann 
                 Akihisa Yamada
    License:     BSD
*)
subsection \<open>Fixing a Code-Equation in the Container framework\<close>

theory Set_Impl_Fix
imports
  "$AFP/Containers/Set_Impl"
begin

(* TODO: fix in AFP! *)
lemmas problematic_code = set_fold1_code(2)
declare problematic_code[code del]
lemmas set_fold1_new_code[code] = problematic_code[folded Collect_set_def]

end