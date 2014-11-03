section "Verification of $f$"
theory F_Spark_Specification
imports F_Spark_Declaration Global_Specification

begin

abbreviation bit__and' :: " [ int , int ] => int " where
  "bit__and' == Global_Specification.bit__and'"

abbreviation bit__or' :: " [ int , int ] => int " where
  "bit__or' == Global_Specification.bit__or'"

abbreviation bit__xor' :: " [ int , int ] => int " where
  "bit__xor' == Global_Specification.bit__xor'"

abbreviation f' :: "int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int" where
  "f' == Global_Specification.f'"


end
