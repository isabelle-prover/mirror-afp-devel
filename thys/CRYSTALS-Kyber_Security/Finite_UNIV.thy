theory Finite_UNIV
imports 
  "HOL-Analysis.Finite_Cartesian_Product"
  "CRYSTALS-Kyber.Kyber_spec"

begin
section \<open>$R_q$ is Finite\<close>

text \<open>The module $R_q$ is finite. This can be reasoned in two steps: 
One, the set of possible coefficients of a polynomial in $R_q$ is finite since coefficients 
are in $\mathbb{z}_q$.
Two, the polynomials in $R_q$ have degree less than $n$.
Together, this implies that $R_q$ itself is a finite set.\<close>



lemma card_UNIV_qr:
 "card (UNIV :: 'a::qr_spec qr set) = (CARD('a)) ^ (degree (qr_poly' TYPE('a)))"
proof -
  let ?q = "(CARD('a))"
  let ?n = "degree (qr_poly' TYPE('a))"
  have fin: "finite (UNIV :: 'a mod_ring set)" by simp
  then obtain f where "bij_betw f (UNIV::'a mod_ring set) {0..< ?q}"
    by (metis CARD_mod_ring ex_bij_betw_finite_nat)
  have rew:"(UNIV :: 'a qr set) = (to_qr \<circ> Poly ) ` {xs :: 'a mod_ring list. length xs = ?n}"
  proof (safe, goal_cases)
    case (1 x)
    let ?xs = "coeffs (of_qr x)"
    define ys where "ys = ?xs @ replicate (?n-length ?xs) 0"
    have "length (coeffs (of_qr x)) \<le> degree (qr_poly' TYPE('a))"
    by (metis Suc_le_eq coeffs_eq_Nil deg_of_qr deg_qr_def length_coeffs_degree 
      list.size(3) zero_le)
    then have "length (coeffs (of_qr x)) + (degree (qr_poly' TYPE('a)) - length (coeffs (of_qr x))) =
      degree (qr_poly' TYPE('a))" by (subst add_diff_assoc) (auto simp add: 1)
    then have "length ys = ?n" unfolding ys_def by (auto) 
    moreover have "x = to_qr (Poly ys)" unfolding ys_def Poly_append_replicate_zero 
      Poly_coeffs to_qr_of_qr by simp
    ultimately have "\<exists> ys. length ys = ?n \<and> x = to_qr (Poly ys)" by blast
    then show ?case by force
  qed simp
  have "card (UNIV :: 'a qr set) = card {xs :: 'a mod_ring list. length xs = ?n}"
  proof (unfold rew, rule card_image, subst comp_inj_on_iff[symmetric], goal_cases)
    case 1
    then show ?case by (metis (mono_tags, lifting) coeff_Poly_eq inj_onI map_nth_default 
      mem_Collect_eq nat_int)
  next
    case 2
    then show ?case unfolding inj_on_def proof (safe, goal_cases)
      case (1 x xa y xb)
      moreover have "Poly xa mod qr_poly = Poly xa" using 1(1) 
        by (intro deg_mod_qr_poly) (metis coeff_Poly_eq deg_qr_pos degree_0 degree_qr_poly' 
          leading_coeff_0_iff nth_default_def)
      moreover have "Poly xb mod qr_poly = Poly xb" using 1(2)  
        by (intro deg_mod_qr_poly) (metis coeff_Poly_eq deg_qr_pos degree_0 degree_qr_poly' 
          leading_coeff_0_iff nth_default_def)
      ultimately show ?case unfolding to_qr_eq_iff  by (simp add: cong_def)
    qed
  qed
  also have "\<dots> = ?q^(?n)" using card_lists_length_eq[OF fin, of "nat ?n"] 
    by (auto)
  ultimately show ?thesis by auto
qed


lemma finite_qr [simp]:
  "finite (UNIV::'a::qr_spec qr set)" using card_UNIV_qr 
  by (metis card.infinite card_UNIV_option card_option nat.distinct(1) power_not_zero)

instantiation qr ::(qr_spec) finite
begin
instance
proof 
  show "finite (UNIV :: 'a ::qr_spec qr set)" using finite_qr by simp 
qed
end

text \<open>Moreover, there are only finitely many vectors (of fixed length) over a finite types and
only finitely many matrices (of fixed dimension) over a finite type.
This yields that $R_q^k$ and $R_q^{k\times k}$ are both finite.\<close>

lemma finite_vec: 
assumes "finite (UNIV :: 'a set)"
shows "finite (UNIV :: ('a, 'k::finite) vec set)"
proof -
  have "bij_betw vec_lambda (UNIV :: ('k \<Rightarrow> 'a) set) (UNIV :: ('a, 'k) vec set)" 
    by (metis UNIV_I bijI' vec_lambda_cases vec_lambda_inject)
  show ?thesis
  by (meson \<open>bij vec_lambda\<close> assms bij_betw_finite finite_UNIV_fun finite_class.finite_UNIV)
qed

lemma finite_mat:
assumes "finite (UNIV :: 'a set)"
shows "finite (UNIV :: (('a, 'k::finite) vec,'k) vec set)"
using finite_vec[OF finite_vec[OF assms]] by auto


lemma finite_UNIV_vec [simp]:
  "finite (UNIV:: ('a::qr_spec qr, 'k::finite) vec set)"
using finite_vec[OF finite_qr] .

lemma finite_UNIV_mat [simp]:
  "finite (UNIV:: (('a::qr_spec qr, 'k) vec, 'k::finite) vec set)"
using finite_mat[OF finite_qr] .

lemma finite_UNIV_vec_option [simp]:
  "finite (UNIV :: ('a::qr_spec qr,'k::finite option) vec set)"
by (simp add: finite_vec)

lemma finite_UNIV_mat_option [simp]:
  "finite (UNIV:: (('a::qr_spec qr, 'k::finite) vec, 'k option) vec set)"
using finite_vec[OF finite_qr] finite_vec by blast


end