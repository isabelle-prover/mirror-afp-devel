header "Verification of $k_r$"
theory K_R_Spark_Specification
imports K_R_Spark_Declaration Global_Specification

begin

abbreviation k_r' :: " int => int " where
  "k_r' == Global_Specification.k_r'"

end
