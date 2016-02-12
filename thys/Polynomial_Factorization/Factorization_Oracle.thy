section \<open>Factorization Oracle\<close>

text \<open>We define an overloaded constant which serves as an arbitrary factorization oracle
  for the rational factorization process. We provide three oracles.
  We implemented the Berlekamp-Hensel
  factorization algorithm, one can choose an external factorization algorithm,
  or one uses a hybrid approach where Berlekamp-Hensel is invoked on small inputs
  and the external one is invoked on larger ones. One just has to load exactly one of 
  the corresponding \emph{Select-\ldots-Factorization}-theory. 
  If this is not purely the Berlekamp-Hensel algorithm, one has to manually implement the
  external factorization algorithm.

  An example external oracle is available in Mathematica.hs\<close>

theory Factorization_Oracle
imports
  Gauss_Lemma
  Square_Free_Factorization
  Polynomial_Division
  "../Show/Show_Poly"
begin

fun list_to_poly :: "'a::comm_monoid_add list \<Rightarrow> 'a poly" where
  "list_to_poly (a # as) = pCons a (list_to_poly as)"
| "list_to_poly [] = 0"

text \<open>input to factorization-oracle: content-free and square-free, 
  non-zero integer polynomial f,
  output: fully factored polynomial over the integers.\<close>

consts factorization_oracle_int_poly :: "int list \<Rightarrow> int list list"

text \<open>Factorization oracle for rational polynomials.\<close>
definition factorization_oracle_rat_poly :: "rat poly \<Rightarrow> rat \<times> (rat poly \<times> nat) list" where
  "factorization_oracle_rat_poly p = (let
     (a,psi) = yun_factorization gcd_rat_poly p;
     ber_hen = (\<lambda> (q,i). let (b,f) = rat_to_normalized_int_poly q;
       fs = factorization_oracle_int_poly (coeffs f);
       gs = map (map of_int) fs;
       hsi = map (\<lambda> h. (list_to_poly h,Suc i)) gs
       in (b^Suc i, hsi));
     pre_result = map ber_hen psi;
     factors = concat (map snd pre_result);
     b = a * listprod (map fst pre_result);     
     sanity = True (* (p = smult b (listprod (map (\<lambda> (q,i). q^i) factors))) *)
   in if sanity then (b,factors) else Code.abort (String.implode
       (''error in factorization_oracle_rat_poly on input '' @ show (coeffs p))) (\<lambda> _. (b,factors)))"


end