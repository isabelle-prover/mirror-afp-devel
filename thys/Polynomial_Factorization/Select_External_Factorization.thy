theory Select_External_Factorization
imports 
  External_Factorization
  Factorization_Oracle
begin

overloading factorization_oracle_int_poly \<equiv> factorization_oracle_int_poly
begin

definition factorization_oracle_int_poly[code]: "factorization_oracle_int_poly = external_factorization"

end


end