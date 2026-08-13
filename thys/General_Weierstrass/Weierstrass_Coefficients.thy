theory Weierstrass_Coefficients
  imports
    "HOL-Computational_Algebra.Polynomial"
begin

section \<open>General Weierstrass coefficients\<close>

record 'a weierstrass_coeffs =
  a1 :: 'a
  a2 :: 'a
  a3 :: 'a
  a4 :: 'a
  a6 :: 'a

lemma weierstrass_coeffs_eqI:
  fixes W V :: "'a weierstrass_coeffs"
  assumes "a1 W = a1 V"
    and "a2 W = a2 V"
    and "a3 W = a3 V"
    and "a4 W = a4 V"
    and "a6 W = a6 V"
  shows "W = V"
  using assms by (cases W; cases V) simp

definition map_weierstrass_coeffs ::
    "('a \<Rightarrow> 'b) \<Rightarrow> 'a weierstrass_coeffs \<Rightarrow> 'b weierstrass_coeffs"
  where
  "map_weierstrass_coeffs f W =
    \<lparr>a1 = f (a1 W), a2 = f (a2 W), a3 = f (a3 W),
      a4 = f (a4 W), a6 = f (a6 W)\<rparr>"

lemma map_weierstrass_coeffs_simps [simp]:
  "a1 (map_weierstrass_coeffs f W) = f (a1 W)"
  "a2 (map_weierstrass_coeffs f W) = f (a2 W)"
  "a3 (map_weierstrass_coeffs f W) = f (a3 W)"
  "a4 (map_weierstrass_coeffs f W) = f (a4 W)"
  "a6 (map_weierstrass_coeffs f W) = f (a6 W)"
  by (simp_all add: map_weierstrass_coeffs_def)

lemma map_weierstrass_coeffs_id [simp]:
  "map_weierstrass_coeffs id W = W"
  by (cases W) (simp add: map_weierstrass_coeffs_def)

lemma map_weierstrass_coeffs_comp:
  "map_weierstrass_coeffs f (map_weierstrass_coeffs g W) =
    map_weierstrass_coeffs (f \<circ> g) W"
  by (cases W) (simp add: map_weierstrass_coeffs_def)

definition short_weierstrass_coeffs ::
    "'a::zero \<Rightarrow> 'a \<Rightarrow> 'a weierstrass_coeffs"
  where
  "short_weierstrass_coeffs A B =
    \<lparr>a1 = 0, a2 = 0, a3 = 0, a4 = A, a6 = B\<rparr>"

lemma short_weierstrass_coeffs_simps [simp]:
  "a1 (short_weierstrass_coeffs A B) = 0"
  "a2 (short_weierstrass_coeffs A B) = 0"
  "a3 (short_weierstrass_coeffs A B) = 0"
  "a4 (short_weierstrass_coeffs A B) = A"
  "a6 (short_weierstrass_coeffs A B) = B"
  by (simp_all add: short_weierstrass_coeffs_def)

end
