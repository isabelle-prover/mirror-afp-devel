section "Verification of $k_l$"
theory K_L_Spark_Specification
imports K_L_Spark_Declaration Global_Specification

begin

abbreviation k_l' :: " int => int " where
  "k_l' == Global_Specification.k_l'"

end
