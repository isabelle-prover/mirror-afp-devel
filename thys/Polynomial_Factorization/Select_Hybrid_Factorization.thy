theory Select_Hybrid_Factorization
imports 
  Hybrid_Factorization
  Factorization_Oracle
begin

overloading factorization_oracle_int_poly \<equiv> factorization_oracle_int_poly
begin

definition factorization_oracle_int_poly[code]: "factorization_oracle_int_poly = hybrid_factorization"

end


end