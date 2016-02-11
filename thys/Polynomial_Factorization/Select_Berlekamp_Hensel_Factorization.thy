theory Select_Berlekamp_Hensel_Factorization
imports 
  Berlekamp_Hensel_Factorization
  Factorization_Oracle
begin

overloading factorization_oracle_int_poly \<equiv> factorization_oracle_int_poly
begin

definition factorization_oracle_int_poly[code]: "factorization_oracle_int_poly = berlekamp_hensel_factorization"

end


end