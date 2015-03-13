section \<open>Defining hash-functions for standard types\<close>

theory Hash_Instances
imports
  Hash_Generator
begin

text \<open>For all of the following types, we register hashcode-functions.
  @{type int}, @{type nat}, @{type char}, @{type bool}, @{type unit}, @{type sum}, @{type option}, @{type list},
  and @{type prod}. For types without type parameters, we use plain @{const "hashcode"}, and for the 
  others we use generated ones.\<close>

derive (hashcode) hash_code int bool char unit nat

derive hash_code prod sum option list 

text \<open>There is no nead to ``derive hashable'' for these types, as they all are already instances.\<close>

end