theory Partition_Number_Imperative_Test
imports
  Partition_Number_Imperative
  "HOL-Library.Code_Target_Numeral"
begin

definition "partition_impl3_test n = 
  do {
    a \<leftarrow> partition_impl3 (nat_of_integer n);
    xs \<leftarrow> Array.freeze a;
    return (map integer_of_int xs)
  }"

ML_val \<open>@{code partition_impl3_test} 100 ()\<close>

end