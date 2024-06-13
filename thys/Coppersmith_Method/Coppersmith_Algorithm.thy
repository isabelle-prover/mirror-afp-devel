section \<open> Algorithm for Coppersmith's Method \<close>

text \<open> In this file, we formalize the algorithm for Coppersmith's method.
  We follow the descriptions in Chapter 19 of "Mathematics of Public Key Cryptography"
  by Steven Galbraith and Section 17.3 of "Introduction to Cryptography with Coding Theory" 
  by Trappe and Washington. 
  We first formalize an algorithm for a "lightweight" version of Coppersmith's method,
  and then formalize Coppersmith's method itself.
  Correctness proofs for these algorithms are in 
  "Towards\_Coppersmith.thy" and "Coppersmith.thy". \<close>

theory Coppersmith_Algorithm

imports "LLL_Factorization.LLL_Factorization"
begin

text \<open> This next definition forms the vector associated to a polynomial as in (19.1) of Galbraith. \<close>
definition vec_associated_to_poly:: "('a::{ring,power}) poly \<Rightarrow> 'a \<Rightarrow> 'a vec" where
  "vec_associated_to_poly p X = vec (degree p + 1) (\<lambda>j. (coeff p j) * X^j)"

abbreviation vec_associated_to_int_poly:: "int poly \<Rightarrow> int \<Rightarrow> int vec" where
  "vec_associated_to_int_poly \<equiv> vec_associated_to_poly"
abbreviation vec_associated_to_real_poly:: "real poly \<Rightarrow> real \<Rightarrow> real vec" where
  "vec_associated_to_real_poly \<equiv> vec_associated_to_poly"

definition int_poly_associated_to_vec:: "int vec \<Rightarrow> nat \<Rightarrow> int poly" where
  "int_poly_associated_to_vec v X = (
    let newvec = vec (dim_vec v) (\<lambda>j. floor (((v $ j)::real)/(X^j))) in
    \<Sum>i<(dim_vec v). monom (newvec $ i) i
  )"

subsection \<open> Lightweight method similar to Coppersmith \<close>

text \<open> In this section, we start with a more lightweight version of Coppersmith which 
  doesn't achieve the full bounds, but is built on similar ideas. \<close>

text \<open> This next definition constructs the g\_i's \<close>
definition g_i_vec:: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> int vec" where
  "g_i_vec M X i n = vec n (\<lambda>j. if j = i then M*X^i else 0)"

text \<open> This next definition should be called with degree d = p - 1 \<close>
definition form_basis_helper:: "int poly \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> int vec list" where
  "form_basis_helper p M X d = map (\<lambda>i. g_i_vec M X i (degree p + 1)) [0..<d + 1]"

definition form_basis:: "int poly => nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> int vec list" where
  "form_basis p M X d = (form_basis_helper p M X d) @ [vec_associated_to_int_poly p X]"

definition first_vector:: "int poly \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> int vec" where
  "first_vector p M X = (
    let cs_basis = form_basis p M X (degree p - 1) in 
    (short_vector 2 cs_basis)
  )"

definition towards_coppersmith:: "int poly \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> int poly" where
  "towards_coppersmith p M X = int_poly_associated_to_vec (first_vector p M X) X"

subsection \<open> Full Coppersmith \<close>
text \<open> In this section, we develop the full Coppersmith's algorithm. \<close>

definition vec_associated_to_int_poly_padded:: "nat \<Rightarrow> int poly \<Rightarrow> nat \<Rightarrow> int vec" where
  "vec_associated_to_int_poly_padded n p X = vec n (\<lambda>j. (coeff p j)*X^j)"

definition row_of_coppersmith_matrix:: "int poly \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> int vec"
  where "row_of_coppersmith_matrix p M X h i j =
  vec_associated_to_int_poly_padded ((degree p)*h) (smult (((M^(h-1-j)))) (p^j*(monom 1 i))) X"

definition form_basis_coppersmith_aux:: "int poly \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> int vec list"
  where "form_basis_coppersmith_aux p M X h j = (map (\<lambda>i. row_of_coppersmith_matrix p M X h i j) [0..<degree p])"

definition form_basis_coppersmith:: "int poly \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> int vec list"
  where "form_basis_coppersmith p M X h = concat (map (\<lambda>j. form_basis_coppersmith_aux p M X h j) [0..< (h::nat)])"

definition calculate_h_coppersmith_aux:: "int poly \<Rightarrow> real \<Rightarrow> int" where
  "calculate_h_coppersmith_aux p e = (let d = degree p in ((ceiling (((d-1)/(d*(e::real)) + 1)/d))::int))"

definition calculate_h_coppersmith:: "int poly \<Rightarrow> real \<Rightarrow> nat" where
  "calculate_h_coppersmith p e = (nat (calculate_h_coppersmith_aux p e))"

text \<open> Note that we pass 2 as a parameter to the LLL algorithm.  Any bound > 4/3 would work. \<close>
definition first_vector_coppersmith:: "int poly \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> real \<Rightarrow> int vec" where
  "first_vector_coppersmith p M X epsilon = (
    let cs_basis = form_basis_coppersmith p M X (calculate_h_coppersmith p epsilon) in 
    short_vector 2 cs_basis)"                                                                  

definition coppersmith:: "int poly \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> real \<Rightarrow> int poly" where
  "coppersmith p M X epsilon =
  int_poly_associated_to_vec (first_vector_coppersmith p M X epsilon) X"

end