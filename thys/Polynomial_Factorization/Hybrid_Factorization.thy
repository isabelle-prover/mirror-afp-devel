theory Hybrid_Factorization
imports
  Berlekamp_Hensel_Factorization
  External_Factorization
begin

definition "hybrid_factorization p = (if length p \<le> 10 then berlekamp_hensel_factorization p
  else external_factorization p)"

end