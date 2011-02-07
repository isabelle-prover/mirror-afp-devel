header "Verification of $r_l$"
theory R_L_Spark_Specification
imports Global_Specification R_L_Spark_Declaration

begin

abbreviation r_l' :: " int => int " where
  "r_l' == Global_Specification.r_l'"

end
