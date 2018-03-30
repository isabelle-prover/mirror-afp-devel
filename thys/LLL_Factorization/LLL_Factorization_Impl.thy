(*
    Authors:    Jose Divasón
                Sebastiaan Joosten
                René Thiemann
                Akihisa Yamada
    License:    BSD
*)

section \<open>The LLL factorization algorithm\<close>

text \<open>This theory contains an implementation of a polynomial time factorization algorithm. 
  It first constructs a modular factorization. Afterwards it recursively 
  invokes the LLL basis reduction algorithm on one lattice to either split a polynomial into  
  two non-trivial factors, or to deduce irreducibility.\<close>

theory LLL_Factorization_Impl
  imports LLL_Basis_Reduction.LLL
    Factor_Bound_2
    Missing_Dvd_Int_Poly
    Berlekamp_Zassenhaus.Berlekamp_Zassenhaus
begin

hide_const (open) up_ring.coeff up_ring.monom
  Unique_Factorization.factors Divisibility.factors
  Unique_Factorization.factor Divisibility.factor 
  Divisibility.prime

(*
  Implementation of a polynomial-time factoring algorithm for \<int>[X], based on the book 
  "Modern Computer Algebra", second edition, pages 477-480.
*)

(*The following function obtains the generators of the lattice L \<subseteq> Z^j
 - L = {ux^i: 0\<le>i\<le>j-d}\<union>{mx^i: 0\<le>i\<le>d}
 - d = degree u.
 - We have to complete with zeroes up to dimension j
*)
definition factorization_lattice where "factorization_lattice u k m \<equiv>
    map (\<lambda>i. vec_of_poly_n (u * monom 1 i) (degree u + k)) [k>..0] @
    map (\<lambda>i. vec_of_poly_n (monom m i) (degree u + k)) [degree u >..0]"

fun max_degree_poly :: "int poly \<Rightarrow> int poly \<Rightarrow> int poly"
  where "max_degree_poly a b = (if degree a\<ge>degree b then a else b)"

fun choose_u :: "int poly list \<Rightarrow> int poly"
  where "choose_u [] = undefined"
  | "choose_u [gi] = gi" 
  | "choose_u (gi # gj # gs) = max_degree_poly gi (choose_u (gj # gs))"

lemma factorization_lattice_code[code]: "factorization_lattice u k m = (
  let n = degree u in
 map 
  (\<lambda>i. vec_of_poly_n (monom_mult i u) (n+k)) [k>..0] 
  @ map (\<lambda>i. vec_of_poly_n (monom m i) (n+k)) [n>..0]
)" unfolding factorization_lattice_def monom_mult_def
  by (auto simp: ac_simps Let_def)

(* 
  TODO: Is it possible to write here context instead of locale and then use these definitions 
  in the file Lattice_and_Factorization.thy without adding p pl? 
  That is, writing "LLL_short_polynomial f u" instead of "LLL_short_polynomial p pl f u".
  *)
locale LLL_implementation =
  fixes p pl :: int
begin

definition LLL_short_polynomial where
  "LLL_short_polynomial n u = poly_of_vec (short_vector 2 (factorization_lattice u (n - degree u) pl))" 

function LLL_reconstruction where 
  "LLL_reconstruction f us = (let 
     u = choose_u us in
      \<comment> \<open>sanity checks which are solely used to ensure termination\<close>
      if \<not> (degree u \<le> degree f \<and> degree u \<noteq> 0 \<and> pl \<noteq> 0) then 
          Code.abort (STR ''LLL_reconstruction is invoked with non-suitable arguments'') (\<lambda> _. [])
    else let 
     g = LLL_short_polynomial (degree f) u;
     f2 = gcd f g
    in if degree f2 = 0 then [f] 
      else let f1 = f div f2;
       (us1, us2) = partition (\<lambda> gi. poly_mod.dvdm p gi f1) us
       in LLL_reconstruction f1 us1 @ LLL_reconstruction f2 us2)"
  by pat_completeness auto
end

declare LLL_implementation.LLL_short_polynomial_def[code]

definition LLL_factorization :: "int poly \<Rightarrow> int poly list" where
  "LLL_factorization f = (let 
     \<comment> \<open>find suitable prime\<close>
     p = suitable_prime_bz f;
     \<comment> \<open>compute finite field factorization\<close>
     (_, fs) = finite_field_factorization_int p f;
     \<comment> \<open>determine exponent l and B\<close>
     n = degree f;
     no = \<parallel>f\<parallel>\<^sup>2;
     B = sqrt_int_ceiling (2^(5 * n * (n - 1)) * no^(2 * n - 1));
     l = find_exponent p B;
     \<comment> \<open>perform hensel lifting to lift factorization to mod (p^l)\<close>
     us = hensel_lifting p l f fs;
     \<comment> \<open>reconstruct integer factors via LLL algorithm\<close>
     pl = p^l
   in LLL_implementation.LLL_reconstruction p pl f us)"

end