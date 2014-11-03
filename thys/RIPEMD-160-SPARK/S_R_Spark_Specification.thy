section "Verification of $s_r$"
theory S_R_Spark_Specification
imports Global_Specification S_R_Spark_Declaration

begin

abbreviation s_r' :: " int => int " where
  "s_r' == Global_Specification.s_r'"

end
