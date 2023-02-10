theory NTT_Scheme

imports Crypto_Scheme
  Mod_Ring_Numeral
  "Number_Theoretic_Transform.NTT"

begin
section \<open>Number Theoretic Transform for Kyber\<close>

lemma Poly_strip_while:
"Poly (strip_while ((=) 0) x) = Poly x"
by (metis Poly_coeffs coeffs_Poly)



locale kyber_ntt = kyber_spec _ _ _ _"TYPE('a :: qr_spec)" "TYPE('k::finite)" +
fixes type_a :: "('a :: qr_spec) itself" 
  and type_k :: "('k ::finite) itself" 
  and \<omega> :: "('a::qr_spec) mod_ring"
  and \<mu> :: "'a mod_ring"
  and \<psi> :: "'a mod_ring"
  and \<psi>inv :: "'a mod_ring"
  and ninv :: "'a mod_ring"
  and mult_factor :: int
assumes
      omega_properties: "\<omega>^n = 1" "\<omega> \<noteq> 1" "(\<forall> m. \<omega>^m = 1 \<and> m\<noteq>0 \<longrightarrow> m \<ge> n)"
  and mu_properties: "\<mu> * \<omega> = 1" "\<mu> \<noteq> 1"
  and psi_properties: "\<psi>^2 = \<omega>" "\<psi>^n = -1"
  and psi_psiinv: "\<psi> * \<psi>inv = 1"
  and n_ninv: "(of_int_mod_ring n) * ninv = 1"
  and q_split: "q = mult_factor * n + 1"
begin
text \<open>Some properties of the roots $\omega$ and $\psi$ and their inverses $\mu$ and $\psi_inv$.\<close>
lemma mu_prop:
  "(\<forall> m. \<mu>^m = 1 \<and> m\<noteq>0 \<longrightarrow> m \<ge> n)"
by (metis mu_properties(1) mult.commute mult.right_neutral 
  omega_properties(3) power_mult_distrib power_one)

lemma mu_prop':
assumes "\<mu>^m' = 1" "m'\<noteq>0" shows "m' \<ge> n"
using mu_prop  assms by blast

lemma omega_prop':
assumes "\<omega>^m' = 1" "m'\<noteq>0" shows "m' \<ge> n"
using omega_properties(3)  assms by blast

lemma psi_props:
shows "\<psi>^(2*n) = 1"
      "\<psi>^(n*(2*a+1)) = -1"
      "\<psi>\<noteq>1"
proof -
  show "\<psi>^(2*n) = 1" 
  by (simp add: omega_properties(1) power_mult psi_properties)
  show "\<psi>^(n*(2*a+1)) = -1" 
  by (metis (no_types, lifting) mult.commute mult_1 power_add 
    power_minus1_even power_mult psi_properties(2))
  show "\<psi>\<noteq>1"
  using omega_properties(2) one_power2 psi_properties(1) by blast
qed

lemma psi_inv_exp:
"\<psi>^i * \<psi>inv ^i = 1"
using left_right_inverse_power psi_psiinv by blast

lemma inv_psi_exp:
"\<psi>inv^i * \<psi> ^i = 1"
by (simp add: mult.commute psi_inv_exp)


lemma negative_psi:
assumes "i<j"
shows "\<psi>^j * \<psi>inv ^i = \<psi>^(j-i)"
proof -
  have j: "\<psi>^j = \<psi>^(j-i) * \<psi>^i" using assms 
  by (metis add.commute le_add_diff_inverse nat_less_le power_add)
  show ?thesis unfolding j
  by (simp add: left_right_inverse_power psi_psiinv)
qed

lemma negative_psi':
assumes "i\<le>j"
shows "\<psi>inv^i * \<psi> ^j = \<psi>^(j-i)"
proof -
  have j: "\<psi>^j = \<psi>^i * \<psi>^(j-i)" using assms 
  by (metis le_add_diff_inverse power_add)
  show ?thesis unfolding j mult.assoc[symmetric] using inv_psi_exp[of i] by simp
qed

lemma psiinv_prop:
shows "\<psi>inv^2 = \<mu>"
proof -
  show "\<psi>inv^2 = \<mu>"
  by (metis (mono_tags, lifting) mu_properties(1) mult.commute 
    mult_cancel_right mult_cancel_right2 power_mult_distrib psi_properties(1) psi_psiinv)
qed

lemma n_ninv':
"ninv * (of_int_mod_ring n) = 1"
using n_ninv 
by (simp add: mult.commute)


text \<open>The \<open>map2\<close> function for polynomials.\<close>
definition map2_poly :: "('a mod_ring \<Rightarrow> 'a mod_ring \<Rightarrow> 'a mod_ring) \<Rightarrow> 
    'a mod_ring poly \<Rightarrow> 'a mod_ring poly \<Rightarrow> 'a mod_ring poly" where 
"map2_poly f p1 p2 = 
  Poly (map2 f (map (poly.coeff p1) [0..<nat n]) (map (poly.coeff p2) [0..<nat n]))"

text \<open>Additional lemmas on polynomials.\<close>
lemma Poly_map_coeff:
assumes "degree f < num"
shows "Poly (map (poly.coeff (f)) [0..<num]) = f"
proof (subst poly_eq_iff, safe)
  fix j
  show "poly.coeff (Poly (map (poly.coeff f) [0..<num])) j = poly.coeff f j"
  proof (cases "j<num")
    case True
    then show ?thesis
    unfolding coeff_Poly by (subst nth_default_nth, auto)
  next
    case False
    then have "j>degree f" using assms by auto
    then show ?thesis unfolding coeff_Poly using False
    by (simp add: coeff_eq_0 nth_default_beyond)
  qed
qed

lemma map_upto_n_mod: 
"(Poly (map f [0..<n]) mod qr_poly) = (Poly (map f [0..<n]) :: 'a mod_ring poly)"
proof -
  have "degree (Poly (map f [0::nat..<n])) < n" 
  by (metis Suc_pred' deg_Poly' deg_qr_n deg_qr_pos degree_0 diff_zero le_imp_less_Suc 
    length_map length_upt nat_int)
  then show ?thesis
  by (subst deg_mod_qr_poly, use deg_qr_n in \<open>auto\<close>)
qed


lemma coeff_of_qr_zero:
assumes "i\<ge>n"
shows "poly.coeff (of_qr (f :: 'a qr)) i = 0"
proof -
  have "degree (of_qr f) < i"
    using deg_of_qr deg_qr_n assms order_less_le_trans by auto
  then show ?thesis by (subst coeff_eq_0, auto)
qed

text \<open>Definition of NTT on polynomials. 
  In contrast to the ordinary NTT, we use a different exponent on the root of unity $\psi$.\<close>
definition ntt_coeff_poly :: "'a qr \<Rightarrow> nat \<Rightarrow> 'a mod_ring" where
  "ntt_coeff_poly g i = (\<Sum>j\<in>{0..<n}. (poly.coeff (of_qr g) j) * \<psi>^(j * (2*i+1)))"

definition ntt_coeffs :: "'a qr \<Rightarrow> 'a mod_ring list" where
  "ntt_coeffs g = map (ntt_coeff_poly g) [0..<n]"

definition ntt_poly :: "'a qr \<Rightarrow> 'a qr" where
"ntt_poly g = to_qr (Poly (ntt_coeffs g))"

text \<open>Definition of inverse NTT on polynomials.
  The inverse transformed is already scaled such that it is the true inverse of the NTT.\<close>
definition inv_ntt_coeff_poly :: "'a qr \<Rightarrow> nat \<Rightarrow> 'a mod_ring" where
  "inv_ntt_coeff_poly g' i = ninv * 
    (\<Sum>j\<in>{0..<n}. (poly.coeff (of_qr g') j) * \<psi>inv^(i*(2*j+1)))"

definition inv_ntt_coeffs :: "'a qr \<Rightarrow> 'a mod_ring list" where
  "inv_ntt_coeffs g' = map (inv_ntt_coeff_poly g') [0..<n]"

definition inv_ntt_poly :: "'a qr \<Rightarrow> 'a qr" where
  "inv_ntt_poly g = to_qr (Poly (inv_ntt_coeffs g))"


text \<open>Kyber is indeed in the NTT-domain with root of unity $\omega$.
Note, that our ntt on polynomials uses a slightly different exponent.
The root of unity $\omega$ defines an alternative NTT in Kyber.\<close>
text \<open>Have $7681 = 30*256 + 1$ and $3329 = 13 * 256 + 1$.\<close>
interpretation kyber_ntt: ntt "nat q" "nat n" "nat mult_factor" \<omega> \<mu>
proof (unfold_locales, goal_cases)
  case 2
  then show ?case  using q_gt_two by linarith
next
  case 3
  then show ?case 
    by (smt (verit, del_insts) int_nat_eq mult.commute nat_int_add 
    nat_mult_distrib of_nat_1 q_gt_two q_split zadd_int_left)
next
  case 4
  then show ?case using n_gt_1 by linarith
qed (use CARD_a nat_int in \<open>auto simp add: omega_properties mu_properties\<close>)


text \<open>Multiplication in of polynomials in $R_q$ is a negacyclic convolution 
(because we factored by $x^n + 1$, thus $x^n\equiv -1 \mod x^n+1$).
This is the reason why we needed to adapt the exponent in the NTT.\<close>
definition qr_mult_coeffs :: "'a qr \<Rightarrow> 'a qr \<Rightarrow> 'a qr" (infixl "\<star>" 70) where
  "qr_mult_coeffs f g = to_qr (map2_poly (*) (of_qr f) (of_qr g))"
 

text \<open>The definition of the exponentiation \<open>^\<close> only allows for natural exponents, 
thus we need to cheat a bit by introducing \<open>conv_sign x\<close>$\equiv (-1)^x$.\<close>
definition conv_sign :: "int \<Rightarrow> 'a mod_ring" where
"conv_sign x = (if x mod 2 = 0 then 1 else -1)"

text \<open>The definition of the negacyclic convolution.\<close>
definition negacycl_conv :: "'a qr \<Rightarrow> 'a qr \<Rightarrow> 'a qr" where
"negacycl_conv f g = 
  to_qr (Poly (map 
  (\<lambda>i. \<Sum>j<n. conv_sign ((int i - int j) div n) *  
    poly.coeff (of_qr f) j * poly.coeff (of_qr g) (nat ((int i - int j) mod n)))
  [0..<n]))"

lemma negacycl_conv_mod_qr_poly:
"of_qr (negacycl_conv f g) mod qr_poly = of_qr (negacycl_conv f g)"
unfolding negacycl_conv_def of_qr_to_qr by auto


text \<open>Representation of f modulo \<open>qr_poly\<close>.\<close>
lemma mod_div_qr_poly:
"(f :: 'a mod_ring poly) = (f mod qr_poly) + qr_poly * (f div qr_poly)"
by simp

text \<open>\<open>take_deg\<close> returns the first $n$ coefficients of a polynomial.\<close>
definition take_deg :: "nat \<Rightarrow> ('b::zero) poly \<Rightarrow> 'b poly"  where
"take_deg = (\<lambda>n. \<lambda>f. Poly (take n (coeffs f)))"

text \<open>\<open>drop_deg\<close> returns the coefficients of a polynomial strarting from the $n$-th coefficient.\<close>
definition drop_deg :: "nat \<Rightarrow> ('b::zero) poly \<Rightarrow> 'b poly"  where
"drop_deg = (\<lambda>n. \<lambda>f. Poly (drop n (coeffs f)))"

text \<open>\<open>take_deg\<close> and \<open>drop_deg\<close> return the modulo and divisor representants.\<close>
lemma take_deg_monom_drop_deg:
assumes "degree f \<ge> n"
shows "(f :: 'a mod_ring poly) = take_deg n f + (Polynomial.monom 1 n) * drop_deg n f"
proof -
  have "min (length (coeffs f)) n = n" using assms 
  by (metis bot_nat_0.not_eq_extremum degree_0 le_imp_less_Suc 
    length_coeffs_degree min.absorb1 min.absorb4)
  then show ?thesis
    unfolding take_deg_def drop_deg_def 
    apply (subst Poly_coeffs[of f,symmetric]) 
    apply (subst append_take_drop_id[of n "coeffs f", symmetric])
    apply (subst Poly_append)
    by (auto)
qed

lemma split_mod_qr_poly:
assumes "degree f \<ge> n"
shows "(f :: 'a mod_ring poly) = take_deg n f - drop_deg n f + qr_poly * drop_deg n f"
proof -
  have "(Polynomial.monom 1 n + 1) * drop_deg n f = 
    Polynomial.monom 1 n *  drop_deg n f + drop_deg n f"
    by (simp add: mult_poly_add_left)
  then show ?thesis 
    apply (subst take_deg_monom_drop_deg[OF assms])
    apply (unfold qr_poly_def qr_poly'_eq of_int_hom.map_poly_hom_add) 
    by auto
qed

text \<open>Lemmas on the degrees of \<open>take_deg\<close> and \<open>drop_deg\<close>.\<close>
lemma degree_drop_n:
"degree (drop_deg n f) = degree f - n"
unfolding drop_deg_def
by (simp add: degree_eq_length_coeffs)

lemma degree_drop_2n:
assumes "degree f < 2*n"
shows "degree (drop_deg n f) < n"
using assms unfolding degree_drop_n by auto

lemma degree_take_n:
"degree (take_deg n f) < n"
unfolding take_deg_def 
by (metis coeff_Poly_eq deg_qr_n deg_qr_pos degree_0 leading_coeff_0_iff 
  nth_default_take of_nat_eq_iff)

lemma deg_mult_of_qr:
"degree (of_qr (f ::'a qr) * of_qr g) < 2 * n"
by (metis add_less_mono deg_of_qr deg_qr_n degree_0 degree_mult_eq 
  mult_2 mult_eq_0_iff nat_int_comparison(1))

text \<open>Representation of a polynomial modulo \<open>qr_poly\<close> using \<open>take_deg\<close> and \<open>drop_deg\<close>.\<close>
lemma mod_qr_poly:
assumes "degree f \<ge> n" "degree f < 2*n"
shows "(f :: 'a mod_ring poly) mod qr_poly = take_deg n f - drop_deg n f "
proof -
  have "degree (take_deg n f - drop_deg n f) < deg_qr TYPE('a)" 
    using degree_diff_le_max[of "take_deg n f" "drop_deg n f"]
     degree_drop_2n[OF assms(2)]  degree_take_n
     by (metis deg_qr_n degree_diff_less nat_int)
  then have "(take_deg n f - drop_deg n f) mod qr_poly =
    take_deg n f - drop_deg n f" by (subst deg_mod_qr_poly, auto)
  then show ?thesis
    by (subst split_mod_qr_poly[OF assms(1)], auto)
qed

text \<open>Coefficients of \<open>take_deg\<close>, \<open>drop_deg\<close> and the modulo representant.\<close>
lemma coeff_take_deg:
assumes "i<n"
shows "poly.coeff (take_deg n f) i = poly.coeff (f::'a mod_ring poly) i"
using assms unfolding take_deg_def 
by (simp add: nth_default_coeffs_eq nth_default_take)

lemma coeff_drop_deg:
assumes "i<n"
shows "poly.coeff (drop_deg n f) i = poly.coeff (f::'a mod_ring poly) (i+n)"
using assms unfolding drop_deg_def 
by (simp add: nth_default_coeffs_eq nth_default_drop)

lemma coeff_mod_qr_poly:
assumes "degree (f::'a mod_ring poly) \<ge> n" "degree f < 2*n" "i<n"
shows "poly.coeff (f mod qr_poly) i = poly.coeff f i - poly.coeff f (i+n)"
apply (subst mod_qr_poly[OF assms(1) assms(2)]) 
apply (subst coeff_diff)
apply (unfold coeff_take_deg[OF assms(3)] coeff_drop_deg[OF assms(3)])
by auto

text \<open>More lemmas on the splitting of sums.\<close>

lemma sum_leq_split:
"(\<Sum>ia\<le>i+n. f ia) = (\<Sum>ia<n. f ia) + (\<Sum>ia\<in>{n..i+n}. f ia)"
proof -
  have *: "{..i + n} - {..<n} = {n..i + n}" 
  by (metis atLeastLessThanSuc_atLeastAtMost lessThan_Suc_atMost lessThan_minus_lessThan) 
  show ?thesis 
  by (subst sum.subset_diff[of "{..<n}" "{..i+n}" f]) (auto simp add: * add.commute)
qed

lemma less_diff:
assumes "l1<l2"
shows "{..<l2} - {..l1} = {l1<..<l2::nat}"
by (metis atLeastSucLessThan_greaterThanLessThan lessThan_Suc_atMost lessThan_minus_lessThan)

lemma sum_less_split:
assumes "l1<(l2::nat)"
shows "sum f {..<l2} = sum f {..l1} + sum f {l1<..<l2}"
by (subst sum.subset_diff[of "{..l1}" "{..<l2}" f]) 
   (auto simp add: assms add.commute order_le_less_trans less_diff[OF assms]) 

lemma div_minus_1:
assumes "(x::int) \<in> {-b..<0}"
shows "x div b = -1" 
using assms 
by (smt (verit, ccfv_SIG) atLeastLessThan_iff div_minus_minus div_pos_neg_trivial)

text \<open>A coefficient of polynomial multiplication is a coefficient of the negacyclic convolution.\<close>
lemma coeff_conv:
fixes f :: "'a qr"
assumes "i<n" 
shows "poly.coeff ((of_qr f) * (of_qr g) mod qr_poly) i = 
    (\<Sum>j<n. conv_sign ((int i - int j) div n) * 
      poly.coeff (of_qr f) j * poly.coeff (of_qr g) (nat ((int i - int j) mod n)))"
proof (cases "degree (of_qr f) + degree (of_qr g)<n")
  case True
  then have True':"degree ((of_qr f) * (of_qr g)) <n" using degree_mult_le 
  using order_le_less_trans by blast
  have "poly.coeff ((of_qr f) * (of_qr g) mod qr_poly) i = 
    poly.coeff ((of_qr f) * (of_qr g)) i" using True'
  by (metis deg_qr_n degree_qr_poly mod_poly_less nat_int)
  also have "\<dots> = (\<Sum>ia\<le>i. poly.coeff (of_qr f) ia * poly.coeff (of_qr g) (i - ia))" 
    unfolding coeff_mult by auto
  also have "\<dots> = (\<Sum>ia\<le>i. conv_sign ((int i - int ia) div int n) *
    poly.coeff (of_qr f) ia * 
    poly.coeff (of_qr g) (nat ((int i - int ia) mod n)))" 
  proof -
    have "i-ia = nat ((int i - int ia) mod n)" if "ia \<le> i" for ia
    using assms that by force
    moreover have "conv_sign ((int i - int ia) div int n) = 1" 
      if "ia \<le> i" for ia unfolding conv_sign_def 
      using assms that by force
    ultimately show ?thesis by auto
  qed
  also have "\<dots> = (\<Sum>ia<n. conv_sign ((int i - int ia) div int n) *
    poly.coeff (of_qr f) ia * 
    poly.coeff (of_qr g) (nat ((int i - int ia) mod n)))"
  proof -
    have "poly.coeff (of_qr f) ia *
       poly.coeff (of_qr g) (nat ((int i - int ia) mod int n)) = 0" 
      if "ia \<in> {i<..<n}" for ia 
    proof (subst mult_eq_0_iff, safe, goal_cases)
      case 1
      have deg_g: "nat ((int i - int ia) mod int n) \<le> degree (of_qr g)" 
        using le_degree[OF 1] by auto
      have "ia > degree (of_qr f)" 
      proof (rule ccontr)
        assume "\<not> degree (of_qr f) < ia"
        then have as: "ia \<le> degree (of_qr f)" by auto
        then have ni: "nat ((int i - int ia) mod int n) + ia = n + i" 
          using that  by (smt (verit, ccfv_threshold) True deg_g 
          greaterThanLessThan_iff int_nat_eq less_imp_of_nat_less 
          mod_add_self1 mod_pos_pos_trivial of_nat_0_le_iff of_nat_add 
          of_nat_mono)
        have "n + i \<le> degree (of_qr f) + degree (of_qr g)"
          unfolding ni[symmetric] using as deg_g by auto
        then show False using True by auto
      qed
      then show ?case 
      using coeff_eq_0 by blast
    qed
    then show ?thesis
      by (subst sum_less_split[OF \<open>i<n\<close>]) (simp add: sum.neutral)
  qed
  finally show ?thesis by blast
next
  case False
  then have *: "degree (of_qr f * of_qr g) \<ge> n"
  by (metis add.right_neutral add_0 deg_of_qr deg_qr_n degree_0 degree_mult_eq 
      linorder_not_le nat_int)
  have "poly.coeff (of_qr f * of_qr g) (i + n) = (\<Sum>ia<n.
        poly.coeff (of_qr f) ia * poly.coeff (of_qr g) (i + n - ia))" 
    unfolding coeff_mult using coeff_of_qr_zero 
    by (subst sum_leq_split[of _ i]) (auto)
  also have "\<dots> = (\<Sum>ia\<in>{i<..<n}.
        poly.coeff (of_qr f) ia * poly.coeff (of_qr g) (i + n - ia))" 
    using coeff_of_qr_zero by (subst sum_less_split[OF \<open>i<n\<close>]) auto
  also have "\<dots> = (\<Sum>ia\<in>{i<..<n}.
        poly.coeff (of_qr f) ia * poly.coeff (of_qr g) (nat ((int i - ia) mod n)))"
  proof -
    have "int i - int ia + int n \<in>{0..<n}" if "ia \<in> {i<..<n}" for ia using assms that by auto
    then have "int i + n-ia = (int i-ia) mod n" if "ia\<in>{i<..<n}" for ia
     using \<open>i<n\<close> that by (smt (verit, best) mod_add_self1 mod_rangeE)
    then have "i+n-ia = nat ((int i - ia) mod n)" if "ia\<in>{i<..<n}" for ia
    by (metis int_minus nat_int of_nat_add that)
    then show ?thesis by fastforce
  qed
  also have "\<dots> = - (\<Sum>ia\<in>{i<..<n}. conv_sign ((int i - int ia) div n) *
        poly.coeff (of_qr f) ia * poly.coeff (of_qr g) (nat ((int i - ia) mod n)))"
  proof -
    have negative:"(int i - int ia) \<in> {-n..<0}" if "ia \<in>{i<..<n}" for ia 
      using that by auto
    have "(int i - int ia) div n = -1" if "ia \<in>{i<..<n}" for ia
      using div_minus_1[OF negative[OF that]] .
    then have "conv_sign ((int i - int ia) div n) = -1" if "ia \<in>{i<..<n}" for ia 
      unfolding conv_sign_def using that by auto
    then have *: "(\<Sum>ia\<in>{i<..<n}. foo ia) =
      (\<Sum>x\<in>{i<..<n}. - (conv_sign ((int i - int x) div int n) * foo x))" 
    for foo by auto
    show ?thesis 
    by (subst sum_negf[symmetric], subst *) (simp add: mult.assoc) 
  qed
  finally have i_n: "poly.coeff (of_qr f * of_qr g) (i + n) = 
    - (\<Sum>ia\<in>{i<..<n}. conv_sign ((int i - int ia) div n) *
        poly.coeff (of_qr f) ia * poly.coeff (of_qr g) (nat ((int i - ia) mod n)))"
    by blast
  have i_n': "poly.coeff (of_qr f * of_qr g) i = 
      (\<Sum>ia\<le>i. conv_sign ((int i - int ia) div n) *
        poly.coeff (of_qr f) ia * poly.coeff (of_qr g) (nat ((int i - ia) mod n)))"
  proof -
    have "conv_sign ((int i - int ia) div n) = 1" if "ia \<le>i" for ia 
      using that assms conv_sign_def by force
    moreover have "i-ia \<in>{0..<n}" if "ia \<le>i" for ia using that assms by auto
    then have "i-ia = (nat ((int i - ia) mod n))" if "ia\<le>i" for ia
      using assms that by force
    ultimately show ?thesis unfolding coeff_mult 
    using assms less_imp_diff_less mod_less by auto
  qed  
  have calc: "poly.coeff (of_qr f * of_qr g) i - poly.coeff (of_qr f * of_qr g) (i + n) = 
    (\<Sum>ia<n. conv_sign ((int i - int ia) div n) *
        poly.coeff (of_qr f) ia * poly.coeff (of_qr g) (nat ((int i - ia) mod n)))" 
    by (subst i_n, subst i_n') 
       (metis (no_types, lifting) assms diff_minus_eq_add sum_less_split)
  show ?thesis unfolding coeff_mod_qr_poly[OF * deg_mult_of_qr assms] calc
    by auto
qed

text \<open>Polynomial multiplication in $R_q$ is the negacyclic convolution.\<close>

lemma mult_negacycl:
"f * g = negacycl_conv f g"
proof -
  have f_times_g: "f * g = to_qr ((of_qr f) * (of_qr g) mod qr_poly)"
    by (metis of_qr_mult to_qr_of_qr)
  have conv: "poly.coeff ((of_qr f) * (of_qr g) mod qr_poly) i = 
    (\<Sum>j<n. conv_sign ((int i - int j) div n) * 
    poly.coeff (of_qr f) j * poly.coeff (of_qr g) (nat ((int i - j) mod n)))" 
  if "i<n" for i using coeff_conv[OF that] by auto
  have "poly.coeff (of_qr (f*g)) i = 
    poly.coeff (of_qr (negacycl_conv f g)) i" for i 
  proof (cases "i<n")
    case True
    then show ?thesis unfolding negacycl_conv_def f_times_g of_qr_to_qr 
      map_upto_n_mod mod_mod_trivial coeff_Poly_eq 
      using conv[OF True] by (subst nth_default_nth[of i], auto)
  next
    case False
    then show ?thesis using coeff_of_qr_zero[of i "f*g"] 
      coeff_of_qr_zero[of i "negacycl_conv f g"] by auto 
  qed 
  then show ?thesis 
    using poly_eq_iff [of "of_qr (f * g)" "of_qr (negacycl_conv f g)"]
    by (metis to_qr_of_qr)
qed

text \<open>Additional lemmas on \<open>ntt_coeffs\<close>.\<close>

lemma length_ntt_coeffs:
"length (ntt_coeffs f) \<le> n"
unfolding ntt_coeffs_def by auto

lemma degree_Poly_ntt_coeffs:
"degree (Poly (ntt_coeffs f)) < n"
using length_ntt_coeffs 
by (smt (verit) deg_Poly' degree_0 degree_take_n diff_diff_cancel 
  diff_is_0_eq le_neq_implies_less less_nat_zero_code nat_le_linear 
  order.strict_trans1 power_0_left power_eq_0_iff)

lemma Poly_ntt_coeffs_mod_qr_poly:
  "Poly (ntt_coeffs f) mod qr_poly = Poly (ntt_coeffs f)"
using map_upto_n_mod ntt_coeffs_def by presburger


lemma nth_default_map:
assumes "i<na"
shows "nth_default x (map f [0..<na]) i = f i"
using assms 
by (simp add: nth_default_nth)


lemma nth_coeffs_negacycl:
assumes "j<n"
shows "poly.coeff (of_qr (negacycl_conv f g)) j =
  (\<Sum>i<n. conv_sign ((int j - int i) div int n) * poly.coeff (of_qr f) i *
   poly.coeff (of_qr g) (nat ((int j - int i) mod int n)))"
unfolding negacycl_conv_def of_qr_to_qr map_upto_n_mod coeff_Poly_eq 
 nth_default_map[OF assms] by auto


text \<open>Writing the convolution sign as a conditional if statement.\<close>
lemma conv_sign_if:
assumes "x<n" "y<n"
shows "conv_sign ((int x - int y) div int n) = (if int x - int y < 0 then -1 else 1)"
unfolding conv_sign_def 
proof (split if_splits, safe, goal_cases)
  case 1
  then have "int x - int y \<in> {-n..<0}" using assms by simp
  then have "(int x - int y) div int n mod 2 = 1"
    using div_minus_1 by presburger
  then show ?case by auto
next
  case 2
  then have "(int x - int y) div int n mod 2 = 0"
  using assms(1) by force
  then show ?case by auto
qed

text \<open>The convolution theorem on coefficients.\<close>

lemma ntt_coeff_poly_mult:
assumes "l<n"
shows "ntt_coeff_poly (f*g) l = ntt_coeff_poly f l * ntt_coeff_poly g l"
proof -
  define f1 where "f1 = (\<lambda>x. \<lambda> y.
        conv_sign ((int x - int y) div int n) *
        poly.coeff (of_qr f) y *
        poly.coeff (of_qr g) (nat ((int x - int y) mod int n)))"
  have "ntt_coeff_poly (f*g) l = (\<Sum>j = 0..<n. poly.coeff (of_qr (negacycl_conv f g)) j *
        \<psi>^(j*(2*l+1)))" unfolding ntt_coeff_poly_def mult_negacycl by auto
  also have "\<dots> = (\<Sum>j=0..<n. (\<Sum>i<n. f1 j i * \<psi>^(j*(2*l+1))))"
  proof (subst sum.cong[of "{0..<n}" "{0..<n}" 
      "(\<lambda>j. poly.coeff (of_qr (negacycl_conv f g)) j * \<psi>^(j*(2*l+1)))"
      "(\<lambda>j. (\<Sum>i<n. f1 j i * \<psi>^(j*(2*l+1))))"], 
      goal_cases)
    case (2 j)
    then have "j<n" by auto
    have "poly.coeff (of_qr (negacycl_conv f g)) j * \<psi> ^ (j * (2 * l + 1)) = 
      (\<Sum>na<n. (conv_sign ((int j - int na) div int n) *
         poly.coeff (of_qr f) na * poly.coeff (of_qr g) (nat ((int j - int na) mod int n))) *
        \<psi> ^ (j * (2 * l + 1)))"
      apply (subst nth_coeffs_negacycl[OF \<open>j<n\<close>])
      apply (subst sum_distrib_right)
      by auto
    also have "\<dots> = (\<Sum>na<n. f1 j na * \<psi> ^ (j * (2 * l + 1)))"
      unfolding f1_def by auto
    finally show ?case by blast
  qed auto
  also have "\<dots> = (\<Sum>i<n. \<Sum>j<n. f1 j i * \<psi> ^ (j * (2 * l + 1))) "
    by (subst atLeast0LessThan, subst sum.swap, auto) 
  also have "\<dots> = (\<Sum>i<n. poly.coeff (of_qr f) i * \<psi> ^ (i * (2 * l + 1)) * 
    (\<Sum>j<n. poly.coeff (of_qr g) (nat ((int j - int i) mod int n)) *
        (if int j - int i < 0 then -1 else 1) *
         \<psi>inv ^ (i * (2 * l + 1)) * \<psi> ^ (j * (2 * l + 1))))"
  proof (subst sum.cong[of "{..<n}" "{..<n}" "(\<lambda>i. (\<Sum>j<n. f1 j i * \<psi> ^ (j * (2 * l + 1))))"
    "(\<lambda>i. poly.coeff (of_qr f) i * \<psi> ^ (i * (2 * l + 1)) * 
        (\<Sum>j<n. poly.coeff (of_qr g) (nat ((int j - int i) mod int n)) *
        (if int j - int i < 0 then -1 else 1) *
         \<psi>inv ^ (i * (2 * l + 1)) * \<psi> ^ (j * (2 * l + 1))))"], goal_cases)
    case (2 i)
    then show ?case 
    proof (subst sum_distrib_left, subst sum.cong[of "{..<n}" "{..<n}" 
      "(\<lambda>j. f1 j i * \<psi> ^ (j * (2 * l + 1)))"
      "(\<lambda>j. poly.coeff (of_qr f) i * \<psi> ^ (i * (2 * l + 1)) *
        (poly.coeff (of_qr g) (nat ((int j - int i) mod int n)) *
        (if int j - int i < 0 then - 1 else 1) *
        \<psi>inv ^ (i * (2 * l + 1)) * \<psi> ^ (j * (2 * l + 1))))"], goal_cases)
      case (2 j)
      then have *: "conv_sign ((int j - int i) div int n) = 
        (if int j - int i < 0 then - 1 else 1)" using conv_sign_if by auto
      have "f1 j i * \<psi> ^ (j * (2 * l + 1)) = 
        \<psi> ^ (i * (2 * l + 1)) * f1 j i * \<psi>inv ^ (i * (2 * l + 1)) * \<psi> ^ (j * (2 * l + 1))"
        using psi_psiinv
        by (simp add: left_right_inverse_power)
      also have "\<dots> = poly.coeff (of_qr f) i * \<psi> ^ (i * (2 * l + 1)) *
      (poly.coeff (of_qr g) (nat ((int j - int i) mod int n)) *
      (if int j - int i < 0 then - 1 else 1) * \<psi>inv ^ (i * (2 * l + 1)) * \<psi> ^ (j * (2 * l + 1)))"
        unfolding f1_def mult.assoc  
        by (simp add: "*" mult.left_commute)
      finally show ?case  by blast
    qed auto
  qed auto
  also have "\<dots> = (\<Sum>i<n. poly.coeff (of_qr f) i * \<psi> ^ (i * (2 * l + 1)) * 
    (\<Sum>x<n. poly.coeff (of_qr g) x * \<psi> ^ (x * (2 * l + 1))))"
  proof -
    define x' where "x' = (\<lambda>j i. nat ((int j - int i) mod int n))"
    let ?if_inv = "(\<lambda>i j. (if int j - int i < 0 then - 1 else 1) * 
      \<psi>inv ^ (i * (2 * l + 1)) * \<psi> ^ (j * (2 * l + 1)))"
    have rewrite: "(if int j - int i < 0 then - 1 else 1) * 
      \<psi>inv ^ (i * (2 * l + 1)) * \<psi> ^ (j * (2 * l + 1)) = 
      \<psi> ^ ((x' j i) * (2 * l + 1))"  if "i<n" "j<n" for i j
    proof (cases "int j - int i <0")
      case True
      have lt: "i * (2 * l + 1) < n * (2 * l + 1)" using \<open>i<n\<close> 
      by (metis One_nat_def add_gr_0 lessI mult_less_mono1)
      have "?if_inv i j = (-1) * \<psi>inv ^ (i * (2 * l + 1)) * \<psi> ^ (j * (2 * l + 1))"
        using True by (auto split: if_splits) 
      also have "\<dots> = \<psi>^((n-i+j)* (2 * l + 1))" unfolding psi_props(2)[of l, symmetric] 
         negative_psi[OF lt]
         by (metis comm_semiring_class.distrib diff_mult_distrib power_add)
      also have "\<dots> = \<psi> ^ ((x' j i) * (2 * l + 1))" unfolding x'_def
      by (smt (verit, best) True mod_add_self2 mod_pos_pos_trivial nat_int_add 
        nat_less_le of_nat_0_le_iff of_nat_diff that(1))
      finally show ?thesis by blast
    next
      case False
      then have "i\<le>j" by auto 
      have lt: "i * (2 * l + 1) \<le> j * (2 * l + 1)" using \<open>i\<le>j\<close> 
      using add_gr_0 less_one mult_less_mono1 
      using mult_le_cancel2 by presburger
      have "?if_inv i j = \<psi>inv ^ (i * (2 * l + 1)) * \<psi> ^ (j * (2 * l + 1))"
        using False by (auto split: if_splits) 
      also have "\<dots> = \<psi>^((j-i)* (2 * l + 1))" 
        using negative_psi'[OF lt]  diff_mult_distrib by presburger
      also have "\<dots> = \<psi> ^ ((x' j i) * (2 * l + 1))" unfolding x'_def
        by (metis \<open>i \<le> j\<close> less_imp_diff_less mod_pos_pos_trivial nat_int 
          of_nat_0_le_iff of_nat_diff of_nat_less_iff that(2))
      finally show ?thesis by blast
    qed
    then have "(\<Sum>j<n. poly.coeff (of_qr g) (nat ((int j - int i) mod int n)) *
      (if int j - int i < 0 then - 1 else 1) * 
      \<psi>inv ^ (i * (2 * l + 1)) * \<psi> ^ (j * (2 * l + 1))) = 
      (\<Sum>x<n. poly.coeff (of_qr g) x * \<psi> ^ (x * (2 * l + 1)))"
      (is "(\<Sum>j<n. ?left j i) = _") if "i<n" for i
    proof -
      have *: "(\<Sum>j<n. ?left j i) = 
        (\<Sum>j<n. poly.coeff (of_qr g) (x' j i) * \<psi> ^ ((x' j i) * (2 * l + 1)))"
        using rewrite[OF that] x'_def
        by (smt (verit, ccfv_SIG) lessThan_iff mult.assoc sum.cong)
      have eq: "(\<lambda>j. x' j i) ` {..<n} = {..<n}" unfolding x'_def 
      proof (safe, goal_cases)
        case (1 _ j)
        with n_gt_zero show ?case
          by (simp add: nat_less_iff)
      next
        case (2 x)
        define j where "j = (x+i) mod n"
        have "j\<in>{..<n}" 
        by (metis j_def lessThan_iff mod_less_divisor n_gt_zero of_nat_0_less_iff)
        moreover have "x = nat ((int j - int i) mod int n)" unfolding j_def
        by (simp add: "2" mod_diff_cong zmod_int) 
        ultimately show ?case by auto
      qed
      have inj: "inj_on (\<lambda>j. x' j i) {..<n}" unfolding x'_def inj_on_def 
      proof (safe, goal_cases)
        case (1 x y)
        then have "((int x - int i) mod int n) = ((int y - int i) mod int n)"
          by (meson eq_nat_nat_iff mod_int_pos_iff n_gt_zero)
        then have "int x mod int n = int y mod int n"
          by (smt (z3) mod_diff_cong)
        then show ?case using 1 by auto
      qed
      show ?thesis unfolding * by (subst sum.reindex_cong[OF inj eq[symmetric], 
        of "(\<lambda>x. poly.coeff (of_qr g) x * \<psi> ^ (x * (2 * l + 1)))" 
        "(\<lambda>j. poly.coeff (of_qr g) (x' j i) * \<psi> ^ (x' j i * (2 * l + 1)))"], auto)
    qed
    then show ?thesis by force
  qed
  also have "\<dots> = (\<Sum>i<n. poly.coeff (of_qr f) i * \<psi> ^ (i * (2 * l + 1))) * 
    (\<Sum>x'<n. poly.coeff (of_qr g) x' * \<psi> ^ (x' * (2 * l + 1)))"
    unfolding sum_distrib_right by auto
  also have "\<dots> = ntt_coeff_poly f l * ntt_coeff_poly g l"
    unfolding ntt_coeff_poly_def atLeast0LessThan by auto
  finally show ?thesis by blast
qed


lemma ntt_coeffs_mult: 
assumes "i<n"
shows "ntt_coeffs (f*g) !i = ntt_coeffs f! i * ntt_coeffs g ! i"
unfolding ntt_coeffs_def using ntt_coeff_poly_mult[OF assms]
by (simp add: assms)

text \<open>Steps towards the convolution theorem.\<close>

lemma nth_default_ntt_coeff_mult:
"nth_default 0 (ntt_coeffs (f * g)) i =
 nth_default 0 (map2 (*) 
  (map (poly.coeff (Poly (ntt_coeffs f))) [0..<nat (int n)])
  (map (poly.coeff (Poly (ntt_coeffs g))) [0..<nat (int n)])) i"
(is "?left i = ?right i")
proof (cases "i\<in>{0..<n}")
  case True
  then have l: "?left i = ntt_coeffs (f * g) ! i"
    by (simp add: nth_default_nth ntt_coeffs_def)
  have *: "?right i = (poly.coeff (Poly (ntt_coeffs f)) i) * (poly.coeff (Poly (ntt_coeffs g)) i)"
    using True 
    by (metis (no_types, lifting) coeff_Poly_eq diff_zero length_map length_upt 
      map_nth_default mult_hom.hom_zero nat_int nth_default_map2 ntt_coeffs_def)
  then have r: "?right i = (ntt_coeffs f) ! i * (ntt_coeffs g) ! i"
    unfolding * unfolding coeff_Poly using nth_default_nth
    by (metis True atLeastLessThan_iff diff_zero length_map length_upt ntt_coeffs_def)
  show ?thesis unfolding l r using ntt_coeffs_mult True by auto
next
  case False
  then have "?left i = 0" unfolding ntt_coeffs_def
    by (simp add: nth_default_beyond)
  moreover have "?right i = 0" using False
  by (simp add: nth_default_def)
  ultimately show ?thesis by presburger
qed

lemma Poly_ntt_coeffs_mult:
"Poly (ntt_coeffs (f * g)) = Poly (map2 (*) 
  (map (poly.coeff (Poly (ntt_coeffs f))) [0..<nat (int n)])
  (map (poly.coeff (Poly (ntt_coeffs g))) [0..<nat (int n)]))"
apply (intro poly_eqI) apply (unfold coeff_Poly)
using nth_default_ntt_coeff_mult[of f g] by auto


text \<open>Convolution theorem for NTT\<close>
lemma ntt_mult:
"ntt_poly (f * g) = qr_mult_coeffs (ntt_poly f) (ntt_poly g)"
proof -
  have "Poly (ntt_coeffs (f*g)) mod qr_poly = 
    Poly (ntt_coeffs (f*g))"
    using Poly_ntt_coeffs_mod_qr_poly by force
  also have "\<dots> = Poly (coeffs (map2_poly (*) (Poly (ntt_coeffs f)) (Poly (ntt_coeffs g))))"
    unfolding map2_poly_def coeffs_Poly Poly_strip_while 
    using Poly_ntt_coeffs_mult by auto
  also have "\<dots> = (map2_poly (*) (of_qr (to_qr (Poly (ntt_coeffs f))))
         (of_qr (to_qr (Poly (ntt_coeffs g))))) mod qr_poly"
  unfolding of_qr_to_qr map_poly_def Poly_ntt_coeffs_mod_qr_poly
  by (metis Poly_coeffs Poly_ntt_coeffs_mod_qr_poly calculation)
  finally have "[Poly (ntt_coeffs (f * g)) = 
       (map2_poly (*) (of_qr (to_qr (Poly (ntt_coeffs f))))
         (of_qr (to_qr (Poly (ntt_coeffs g)))))] (mod qr_poly)"
  using cong_def by blast
  then have "to_qr (Poly (ntt_coeffs (f * g))) =
    to_qr (map2_poly (*) (of_qr (to_qr (Poly (ntt_coeffs f))))
         (of_qr (to_qr (Poly (ntt_coeffs g)))))"
  using of_qr_to_qr by auto
  then show ?thesis
    unfolding ntt_poly_def qr_mult_coeffs_def  
    by auto
qed

text \<open>Correctness of NTT on polynomials.\<close>

lemma inv_ntt_poly_correct:
"inv_ntt_poly (ntt_poly f) = f"
proof -
  have rew_sum: "(\<Sum>j = 0..<n. nth_default 0 
    (map (\<lambda>i. \<Sum>j = 0..<n. poly.coeff (of_qr f) j * \<psi> ^ (j * (2 * i + 1))) [0..<n])
     j * \<psi>inv ^ (i * (2 * j + 1))) = 
    (\<Sum>j = 0..<n. (\<Sum>j' = 0..<n. poly.coeff (of_qr f) j' * \<psi> ^ (j' * (2 * j + 1)))
     * \<psi>inv ^ (i * (2 * j + 1)))" 
    (is "(\<Sum>j = 0..<n. ?left j) = (\<Sum>j = 0..<n. ?right j)") for i
  proof (subst sum.cong[of "{0..<n}" "{0..<n}" ?left ?right], goal_cases)
    case (2 x)
    then show ?case by (subst nth_default_map[of x n], auto)
  qed auto
  have  "(\<Sum>j = 0..<n. \<Sum>j' = 0..<n. poly.coeff (of_qr f) j' * 
    \<psi> ^ (j' * (2 * j + 1)) * \<psi>inv ^ (i * (2 * j + 1))) = 
    (of_int_mod_ring n) * poly.coeff (of_qr f) i" if "i<n" for i
  proof -
    have rew_psi: "\<psi> ^ (j * (2 * j' + 1)) * \<psi>inv ^ (i * (2 * j' + 1)) =
      \<psi> ^ j * \<psi>inv ^ i * (\<psi> ^ (j * 2) * \<psi>inv ^ (i * 2)) ^ j'"
      if "j'<n" "j<n" for j' j
    by (smt (verit, ccfv_threshold) kyber_ntt.exp_rule mult.commute 
      power_add power_mult power_one_right)
    have "(\<Sum>j = 0..<n. \<Sum>j' = 0..<n. poly.coeff (of_qr f) j' * 
        \<psi> ^ (j' * (2 * j + 1)) * \<psi>inv ^ (i * (2 * j + 1))) = 
      (\<Sum>j' = 0..<n. poly.coeff (of_qr f) j' * \<psi>^j' * \<psi>inv^i *
        (\<Sum>j = 0..<n. (\<psi> ^ (j' * 2) * \<psi>inv ^ (i * 2))^j))"
    apply (subst sum_distrib_left, subst sum.swap)
     proof (subst sum.cong[of "{0..<n}" "{0..<n}"
      "(\<lambda>j. \<Sum>ia = 0..<n. poly.coeff (of_qr f) j * \<psi> ^ (j * (2 * ia + 1)) *
           \<psi>inv ^ (i * (2 * ia + 1)))"
      "(\<lambda>j. \<Sum>ia = 0..<n. poly.coeff (of_qr f) j * \<psi> ^ j * \<psi>inv ^ i *
           (\<psi> ^ (j * 2) * \<psi>inv ^ (i * 2)) ^ ia)"], goal_cases)
      case (2 j)
      then show ?case proof (subst sum.cong[of "{0..<n}" "{0..<n}"
      "(\<lambda>ia. poly.coeff (of_qr f) j * \<psi> ^ (j * (2 * ia + 1)) *
        \<psi>inv ^ (i * (2 * ia + 1)))"
      "(\<lambda>ia. poly.coeff (of_qr f) j * \<psi> ^ j * \<psi>inv ^ i *
        (\<psi> ^ (j * 2) * \<psi>inv ^ (i * 2)) ^ ia)"], goal_cases)
        case (2 j')
        then show ?case using rew_psi[of j' j] by simp
      qed auto
    qed auto
    also have "\<dots> = (\<Sum>j' = 0..<n. 
      (if j' = i then poly.coeff (of_qr f) j' * \<psi>^j' * \<psi>inv^i * (of_int_mod_ring n) else 0))" 
    proof (subst sum.cong[of "{0..<n}" "{0..<n}" 
      "(\<lambda>j'. poly.coeff (of_qr f) j' * \<psi> ^ j' * \<psi>inv ^ i *
        (\<Sum>j=0..<n. (\<psi> ^ (j' * 2) * \<psi>inv ^ (i * 2))^j))"
      "(\<lambda>j'. (if j' = i then poly.coeff (of_qr f) j' * \<psi>^j' * \<psi>inv^i * 
        (of_int_mod_ring n) else 0))"], goal_cases)
      case (2 j')
      then show ?case proof (cases "j' = i")
        case True
        then have "(\<Sum>j=0..<n. (\<psi> ^ (j' * 2) * \<psi>inv ^ (i * 2))^j) = of_int_mod_ring n"
          unfolding True psi_inv_exp 
          by (metis kyber_ntt.sum_rules(5) mult.right_neutral power_one sum.cong)
        then show ?thesis using True by auto
      next
        case False
        have not1: "\<psi> ^ (j' * 2) * \<psi>inv ^ (i * 2) \<noteq> 1"
        proof -
          have "\<omega>^j' * \<mu> ^i \<noteq> 1" 
          proof (cases "j'<i")
            case True
            have *: "\<omega>^j' * \<mu> ^i = \<mu>^(i-j')" using True 
            by (metis (no_types, lifting) le_add_diff_inverse less_or_eq_imp_le 
              mult.assoc mult_cancel_right2 power_add power_mult psi_inv_exp 
              psi_properties(1) psiinv_prop)
            show ?thesis proof (unfold *, rule ccontr)
              assume "\<not> \<mu> ^ (i - j') \<noteq> 1" 
              then have 1: "\<mu> ^ (i - j') = 1" by auto
              show False using mu_prop'[OF 1] \<open>j'\<noteq>i\<close>
              using True less_imp_diff_less that diff_is_0_eq leD by blast
            qed
          next
            case False
            have 2: "\<omega>^j' * \<mu> ^i = \<omega>^(j'-i)" using False
            by (smt (verit) Nat.add_diff_assoc ab_semigroup_mult_class.mult_ac(1) 
              add_diff_cancel_left' left_right_inverse_power linorder_not_less 
              mu_properties(1) mult.commute mult_numeral_1_right numeral_One power_add) 
            show ?thesis proof (unfold 2, rule ccontr)
              assume "\<not> \<omega> ^ (j' - i) \<noteq> 1" 
              then have 1: "\<omega> ^ (j' - i) = 1" by auto
              have "n > j' - i" using \<open>j' \<in> {0..<n}\<close> by auto
              then show False using omega_prop'[OF 1] \<open>j'\<noteq>i\<close>
              using False 
              by (meson diff_is_0_eq leD order_le_imp_less_or_eq)
            qed
          qed
          then show ?thesis
          by (metis mult.commute power_mult psi_properties(1) psiinv_prop) 
        qed
        have "(1 - \<psi> ^ (j' * 2) * \<psi>inv ^ (i * 2)) * 
          (\<Sum>j=0..<n. (\<psi> ^ (j' * 2) * \<psi>inv ^ (i * 2))^j) = 0"
        proof (subst kyber_ntt.geo_sum, goal_cases)
          case 1
          then show ?case using not1 by auto
        next
          case 2
          then show ?case 
          by (metis (no_types, opaque_lifting) cancel_comm_monoid_add_class.diff_cancel 
            mu_properties(1) mult.commute omega_properties(1) power_mult power_mult_distrib 
            power_one psi_properties(1) psiinv_prop)
        qed
        then have "(\<Sum>j=0..<n. (\<psi> ^ (j' * 2) * \<psi>inv ^ (i * 2))^j) = 0" 
          using not1 by auto
        then show ?thesis using False by auto
      qed
    qed auto
    also have "\<dots> = poly.coeff (of_qr f) i * \<psi>^i * \<psi>inv^i * (of_int_mod_ring n)"
      by (subst sum.delta[of "{0..<n}" i], use \<open>i<n\<close> in auto)
    also have "\<dots> = (of_int_mod_ring n) * poly.coeff (of_qr f) i"
      by (simp add: psi_inv_exp)
    finally show ?thesis by blast
  qed
  then have rew_coeff: "(map (\<lambda>i. ninv * (\<Sum>j = 0..<n. \<Sum>n = 0..<n.
    poly.coeff (of_qr f) n * \<psi> ^ (n * (2 * j + 1)) * \<psi>inv ^ (i * (2 * j + 1)))) [0..<n]) = 
    map (\<lambda>i. ninv * (of_int_mod_ring (int n) * poly.coeff (of_qr f) i)) [0..<n]"
  unfolding map_eq_conv by auto
  show ?thesis unfolding inv_ntt_poly_def ntt_poly_def inv_ntt_coeffs_def ntt_coeffs_def
    inv_ntt_coeff_poly_def ntt_coeff_poly_def of_qr_to_qr map_upto_n_mod coeff_Poly
    apply (subst rew_sum) 
    apply (subst sum_distrib_right) 
    apply (subst rew_coeff)
    apply (subst mult.assoc[symmetric]) 
    apply (subst n_ninv')
    apply (subst mult_1)
    apply (subst Poly_map_coeff)
    subgoal using deg_of_qr deg_qr_n by fastforce
    subgoal unfolding to_qr_of_qr by auto
  done
qed


lemma ntt_inv_poly_correct:
"ntt_poly (inv_ntt_poly f) = f"
proof -
  have rew_sum: "(\<Sum>j = 0..<n. nth_default 0 (map (\<lambda>i. ninv *
    (\<Sum>j' = 0..<n. poly.coeff (of_qr f) j' * \<psi>inv ^ (i * (2 * j' + 1)))) [0..<n]) j *
      \<psi> ^ (j * (2 * i + 1))) = 
    (\<Sum>j = 0..<n. ninv * (\<Sum>j' = 0..<n. poly.coeff (of_qr f) j' * \<psi>inv ^ (j * (2 * j' + 1)))
     * \<psi> ^ (j * (2 * i + 1)))" 
    (is "(\<Sum>j = 0..<n. ?left j) = (\<Sum>j = 0..<n. ?right j)") for i
  proof (subst sum.cong[of "{0..<n}" "{0..<n}" ?left ?right], goal_cases)
    case (2 x)
    then show ?case by (subst nth_default_map[of x n], auto)
  qed auto
  have  "(\<Sum>j = 0..<n. \<Sum>n = 0..<n. ninv * (poly.coeff (of_qr f) n *
    \<psi>inv ^ (j * (2 * n + 1))) * \<psi> ^ (j * (2 * i + 1))) = 
    ninv * (of_int_mod_ring (int n) * poly.coeff (of_qr f) i)" if "i<n" for i
  proof -
    have rew_psi: "\<psi>inv ^ (j' * (2 * j + 1)) * \<psi> ^ (j' * (2 * i + 1)) =
      (\<psi>inv ^ (j * 2) * \<psi> ^ (i * 2)) ^ j'"
      if "j'<n" "j<n" for j' j
    proof -
      have "\<psi>inv ^ (j' * (2 * j + 1)) * \<psi> ^ (j' * (2 * i + 1)) =
        \<psi>inv ^ (j' * (2 * j)) * \<psi> ^ (j' * (2 * i)) * \<psi>inv ^ j'  * \<psi> ^ j' "
      by (simp add: power_add)
      also have "\<dots> = (\<psi>inv ^ (2 * j) * \<psi> ^ (2 * i))^ j'"
      by (smt (verit, best) inv_psi_exp kyber_ntt.exp_rule mult.assoc 
        mult.commute mult.right_neutral power_mult) 
      also have "\<dots> = (\<psi>inv ^ (j * 2) * \<psi> ^ (i * 2)) ^ j'"
      by (simp add: mult.commute) 
      finally show ?thesis by blast
    qed
    have "(\<Sum>j = 0..<n. \<Sum>j' = 0..<n. ninv * (poly.coeff (of_qr f) j' *
    \<psi>inv ^ (j * (2 * j' + 1))) * \<psi> ^ (j * (2 * i + 1))) = 
      (\<Sum>j' = 0..<n. ninv * poly.coeff (of_qr f) j' * 
        (\<Sum>j = 0..<n. (\<psi>inv ^ (j' * 2) * \<psi> ^ (i * 2))^j))"
    apply (subst sum_distrib_left, subst sum.swap, unfold mult.assoc[symmetric])
    proof (subst sum.cong[of "{0..<n}" "{0..<n}"
      "(\<lambda>j. \<Sum>ia = 0..<n. ninv * poly.coeff (of_qr f) j * \<psi>inv ^ (ia * (2 * j + 1)) *
           \<psi> ^ (ia * (2 * i + 1)))"
      "(\<lambda>j. \<Sum>n = 0..<n. ninv * poly.coeff (of_qr f) j *
           (\<psi>inv ^ (j * 2) * \<psi> ^ (i * 2)) ^ n)"], goal_cases)
      case (2 j)
      then show ?case 
      proof (subst sum.cong[of "{0..<n}" "{0..<n}"
      "(\<lambda>ia. ninv * poly.coeff (of_qr f) j * \<psi>inv ^ (ia * (2 * j + 1)) *
        \<psi> ^ (ia * (2 * i + 1)))"
      "(\<lambda>ia. ninv * poly.coeff (of_qr f) j *
        (\<psi>inv ^ (j * 2) * \<psi> ^ (i * 2)) ^ ia)"], goal_cases)
        case (2 j')
        then show ?case using rew_psi[of j' j] by simp
      qed auto
    qed auto
    also have "\<dots> = (\<Sum>j' = 0..<n. 
      (if j' = i then ninv * poly.coeff (of_qr f) j' * 
        \<psi>inv^j' * \<psi>^i * (of_int_mod_ring n) else 0))" 
    (is "(\<Sum>j' = 0..<n. ?right j') = (\<Sum>j' = 0..<n. ?left j')")
    proof (subst sum.cong[of "{0..<n}" "{0..<n}" "?right" "?left"], goal_cases)
      case (2 j')
      then show ?case proof (cases "j' = i")
        case True
        then have "(\<Sum>j=0..<n. (\<psi>inv ^ (j' * 2) * \<psi> ^ (i * 2))^j) = of_int_mod_ring n"
          unfolding True psi_inv_exp 
          by (metis kyber_ntt.sum_const mult.commute mult.right_neutral 
          power_one psi_inv_exp sum.cong) 
        then show ?thesis using True
        by (simp add: inv_psi_exp)
      next
        case False
        have not1: "\<psi>inv ^ (j' * 2) * \<psi> ^ (i * 2) \<noteq> 1"
        proof -
          have "\<mu>^j' * \<omega> ^i \<noteq> 1" 
          proof (cases "j'<i")
            case True
            have *: "\<mu>^j' * \<omega> ^i = \<omega>^(i-j')" using True
            by (smt (verit, best) add.commute kyber_ntt.omega_properties(1) 
              le_add_diff_inverse left_right_inverse_power less_or_eq_imp_le 
              mu_properties(1) mult.left_commute mult_cancel_right1 power_add)
            show ?thesis proof (unfold *, rule ccontr)
              assume "\<not> \<omega> ^ (i - j') \<noteq> 1" 
              then have 1: "\<omega> ^ (i - j') = 1" by auto
              show False using omega_prop'[OF 1] \<open>j'\<noteq>i\<close>
              using True less_imp_diff_less that diff_is_0_eq leD by blast
            qed
          next
            case False
            have 2: "\<mu>^j' * \<omega> ^i = \<mu>^(j'-i)" using False
            by (smt (verit) Nat.add_diff_assoc ab_semigroup_mult_class.mult_ac(1) 
              add_diff_cancel_left' left_right_inverse_power linorder_not_less 
              mu_properties(1) mult.commute mult_numeral_1_right numeral_One power_add) 
            show ?thesis proof (unfold 2, rule ccontr)
              assume "\<not> \<mu> ^ (j' - i) \<noteq> 1" 
              then have 1: "\<mu> ^ (j' - i) = 1" by auto
              have "n > j' - i" using \<open>j' \<in> {0..<n}\<close> by auto
              then show False using mu_prop'[OF 1] \<open>j'\<noteq>i\<close>
              using False 
              by (meson diff_is_0_eq leD order_le_imp_less_or_eq)
            qed
          qed
          then show ?thesis
          by (metis mult.commute power_mult psi_properties(1) psiinv_prop) 
        qed
        have "(1 - \<psi>inv ^ (j' * 2) * \<psi> ^ (i * 2)) * 
          (\<Sum>j=0..<n. (\<psi>inv ^ (j' * 2) * \<psi> ^ (i * 2))^j) = 0"
        proof (subst kyber_ntt.geo_sum, goal_cases)
          case 1
          then show ?case using not1 by auto
        next
          case 2
          then show ?case 
          by (metis (no_types, opaque_lifting) cancel_comm_monoid_add_class.diff_cancel 
            mu_properties(1) mult.commute omega_properties(1) power_mult power_mult_distrib 
            power_one psi_properties(1) psiinv_prop)
        qed
        then have "(\<Sum>j=0..<n. (\<psi>inv ^ (j' * 2) * \<psi> ^ (i * 2))^j) = 0" 
          using not1 by auto
        then show ?thesis using False by auto
      qed
    qed auto
    also have "\<dots> = ninv * poly.coeff (of_qr f) i * \<psi>inv^i * \<psi>^i * (of_int_mod_ring n)"
      by (subst sum.delta[of "{0..<n}" i], use \<open>i<n\<close> in auto)
    also have "\<dots> = ninv * ((of_int_mod_ring n) * poly.coeff (of_qr f) i)"
      by (simp add: psi_inv_exp mult.commute)
    finally show ?thesis by blast
  qed
  then have rew_coeff: "(map (\<lambda>i. \<Sum>j = 0..<n. \<Sum>n = 0..<n. ninv * (poly.coeff (of_qr f) n *
    \<psi>inv ^ (j * (2 * n + 1))) * \<psi> ^ (j * (2 * i + 1))) [0..<n]) = 
    map (\<lambda>i. ninv * (of_int_mod_ring (int n) * poly.coeff (of_qr f) i)) [0..<n]"
  unfolding map_eq_conv by auto
  show ?thesis unfolding inv_ntt_poly_def ntt_poly_def inv_ntt_coeffs_def ntt_coeffs_def
    inv_ntt_coeff_poly_def ntt_coeff_poly_def of_qr_to_qr map_upto_n_mod coeff_Poly
    apply (subst rew_sum)
    apply (subst sum_distrib_left)
    apply (subst sum_distrib_right) 
    apply (subst rew_coeff)
    apply (subst mult.assoc[symmetric]) 
    apply (subst n_ninv')
    apply (subst mult_1)
    apply (subst Poly_map_coeff)
    subgoal using deg_of_qr deg_qr_n by fastforce
    subgoal unfolding to_qr_of_qr by auto
  done
qed

text \<open>The multiplication of two polynomials can be computed by the NTT.\<close>

lemma convolution_thm_ntt_poly:
  "f*g = inv_ntt_poly (qr_mult_coeffs (ntt_poly f) (ntt_poly g))"
unfolding ntt_mult[symmetric] inv_ntt_poly_correct by auto



end
end