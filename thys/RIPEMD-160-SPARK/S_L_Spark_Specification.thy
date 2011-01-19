header "Verification of $s_l$"
theory S_L_Spark_Specification
imports Global_Specification S_L_Spark_Declaration

begin

abbreviation s_l' :: " int => int " where
  "s_l' == Global_Specification.s_l'"

end
