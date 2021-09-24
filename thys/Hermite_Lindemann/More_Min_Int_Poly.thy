text \<open>This theory imports both univariate and multivariate polynomials and thereby 
  causes several overlaps in notation of polynomials.\<close>

theory More_Min_Int_Poly
  imports
    Algebraic_Numbers.Min_Int_Poly
    "HOL-Computational_Algebra.Computational_Algebra"
    More_Polynomial_HLW
begin

lemma min_int_poly_squarefree [intro]:
  fixes x :: "'a :: {field_char_0, field_gcd}"
  shows "squarefree (min_int_poly x)"
  by (rule irreducible_imp_squarefree) auto

lemma min_int_poly_conv_Gcd:
  fixes x :: "'a :: {field_char_0, field_gcd}"
  assumes "algebraic x"
  shows "min_int_poly x = Gcd {p. p \<noteq> 0 \<and> p represents x}"
proof (rule sym, rule Gcd_eqI, (safe)?)
  fix p assume p: "\<And>q. q \<in> {p. p \<noteq> 0 \<and> p represents x} \<Longrightarrow> p dvd q"
  show "p dvd min_int_poly x"
    using assms by (intro p) auto
next
  fix p assume p: "p \<noteq> 0" "p represents x"
  have "min_int_poly x represents x"
    using assms by auto
  hence "poly (gcd (of_int_poly (min_int_poly x)) (of_int_poly p)) x = 0"
    using p by (intro poly_gcd_eq_0I) auto
  hence "ipoly (gcd (min_int_poly x) p) x = 0"
    by (subst (asm) gcd_of_int_poly) auto
  hence "gcd (min_int_poly x) p represents x"
    using p unfolding represents_def by auto

  have "min_int_poly x dvd gcd (min_int_poly x) p \<or> is_unit (gcd (min_int_poly x) p)"
    by (intro irreducibleD') auto
  moreover from \<open>gcd (min_int_poly x) p represents x\<close> have "\<not>is_unit (gcd (min_int_poly x) p)"
    by (auto simp: represents_def)
  ultimately have "min_int_poly x dvd gcd (min_int_poly x) p"
    by blast
  also have "\<dots> dvd p"
    by blast
  finally show "min_int_poly x dvd p" .
qed auto

end
