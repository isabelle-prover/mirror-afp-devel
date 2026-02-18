(*<*)
section \<open>Auxiliary material\<close>
theory Elliptic_Functions_Library
imports
  "HOL-Complex_Analysis.Complex_Analysis"
  "Algebraic_Numbers.Bivariate_Polynomials"
  "Dirichlet_Series.Dirichlet_Series_Analysis"
begin

(* TODO: Move? *)
lemma continuous_within_poly2:
  fixes f g :: "'a :: t2_space \<Rightarrow> 'b :: {real_normed_field}"
  assumes [continuous_intros]: "continuous (at F within A) f" "continuous (at F within A) g"
  shows "continuous (at F within A) (\<lambda>x. poly2 p (f x) (g x))"
  by (induction p) (auto intro!: continuous_intros continuous_within_poly)

lemma map_poly2_0 [simp]: "map_poly2 f 0 = 0"
  by (simp add: map_poly2_def)

lemma map_poly2_pCons [simp]:
  "p \<noteq> 0 \<or> q \<noteq> 0 \<Longrightarrow> map_poly2 f (pCons p q) = pCons (map_poly f p) (map_poly2 f q)"
  by (simp add: map_poly2_def)

lemma map_poly2_compose: "f 0 = 0 \<Longrightarrow> map_poly2 (f \<circ> g) p = map_poly2 f (map_poly2 g p)"
  by (rule poly_eqI) (auto simp: map_poly2_def coeff_map_poly map_poly_map_poly)
(* END TODO *)


(* TODO: Move *)
lemma has_fps_expansion_poly [fps_expansion_intros]:
  fixes F :: "'a :: {banach, real_normed_div_algebra, comm_ring_1} fps"
  assumes "f has_fps_expansion F"
  shows   "(\<lambda>x. poly p (f x)) has_fps_expansion (poly (map_poly fps_const p) F)"
  by (induction p) (auto intro!: fps_expansion_intros assms)

(* TODO Move *)
lemma has_fps_expansion_poly2 [fps_expansion_intros]:
  fixes F G :: "'a :: {banach, real_normed_div_algebra, comm_ring_1} fps"
  assumes "f has_fps_expansion F" "g has_fps_expansion G"
  shows   "(\<lambda>x. poly2 p (f x) (g x)) has_fps_expansion (poly2 (map_poly2 fps_const p) F G)"
  by (induction p) (auto intro!: fps_expansion_intros assms simp: )

(* TODO Move *)
lemma fps_nth_numeral_pos [simp]: "n > 0 \<Longrightarrow> fps_nth (numeral m) n = 0"
  by (subst fps_numeral_nth) auto

(* TODO Move *)
lemma divisor_sigma_of_real: 
  "divisor_sigma (of_real s :: 'a :: nat_power_normed_field) n = of_real (divisor_sigma s n)"
  by (simp add: divisor_sigma_def)

(* TODO Move *)
lemma
  assumes "c \<in> \<real>"
  shows   Re_divisor_sigma_Reals [simp]: "Re (divisor_sigma c n) = divisor_sigma (Re c) n"
    and   Im_divisor_sigma_Reals [simp]: "Im (divisor_sigma c n) = 0"
  using assms by (auto elim!: Reals_cases simp: divisor_sigma_of_real)

end
(*>*)