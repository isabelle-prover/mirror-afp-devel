(*  
    Author:      René Thiemann 
                 Akihisa Yamada
    License:     BSD
*)
section \<open>Explicit Formulas for Roots\<close>

text \<open>We provide algorithms which use the explicit formulas to 
  compute the roots of polynomials of degree up to 2. For polynomials of degree
  3 and 4 have a look at the AFP entry "Cubic-Quartic-Equations".\<close>  

theory Explicit_Roots
imports   
  Polynomial_Interpolation.Missing_Polynomial
  Sqrt_Babylonian.Sqrt_Babylonian
begin

lemma roots0: assumes p: "p \<noteq> 0" and p0: "degree p = 0" 
  shows "{x. poly p x = 0} = {}"
  using degree0_coeffs[OF p0] p by auto

definition roots1 :: "'a :: field poly \<Rightarrow> 'a" where
  "roots1 p = (- coeff p 0 / coeff p 1)"

lemma roots1: fixes p :: "'a :: field poly"
  assumes p1: "degree p = 1" 
  shows "{x. poly p x = 0} = {roots1 p}"
  using degree1_coeffs[OF p1] unfolding roots1_def 
  by (auto simp: add_eq_0_iff nonzero_neg_divide_eq_eq2)

lemma roots2: fixes p :: "'a :: field_char_0 poly"
  assumes p2: "p = [: c, b, a :]" and a: "a \<noteq> 0"
  shows "{x. poly p x = 0} = { - ( b / (2 * a)) + e | e. e^2 = ( b / (2 * a))^2 - c/a}" (is "?l = ?r")
proof -
  define b2a where "b2a = b / (2 * a)"
  {
    fix x
    have "(x \<in> ?l) = (x * x * a + x * b + c = 0)" unfolding p2 by (simp add: field_simps)
    also have "\<dots> = ((x * x + 2 * x * b2a) + c/a = 0)" using a by (auto simp: b2a_def field_simps)
    also have "x * x + 2 * x * b2a = (x * x + 2 * x * b2a + b2a^2) - b2a^2" by simp
    also have "\<dots> = (x + b2a) ^ 2 - b2a ^ 2" 
      by (simp add: field_simps power2_eq_square)
    also have "(\<dots> + c / a = 0) = ((x + b2a) ^ 2 = b2a^2 - c/a)" by algebra
    also have "\<dots> = (x \<in> ?r)" unfolding b2a_def[symmetric] by (auto simp: field_simps)
    finally have "(x \<in> ?l) = (x \<in> ?r)" .
  }
  thus ?thesis by auto
qed

definition croots2 :: "complex poly \<Rightarrow> complex list" where
  "croots2 p = (let a = coeff p 2; b = coeff p 1; c = coeff p 0; b2a = b / (2 * a);
    bac = b2a^2 - c/a;
    e = csqrt bac 
    in
     remdups [- b2a + e, - b2a - e])"

definition complex_rat :: "complex \<Rightarrow> bool" where
  "complex_rat x = (Re x \<in> \<rat> \<and> Im x \<in> \<rat>)"

lemma croots2: assumes "degree p = 2"
  shows "{x. poly p x = 0} = set (croots2 p)"
proof -
  from degree2_coeffs[OF assms] obtain a b c 
  where p: "p = [:c, b, a:]" and a: "a \<noteq> 0" by auto
  note main = roots2[OF p a]
  have 2: "2 = Suc (Suc 0)" by simp
  have coeff: "coeff p 2 = a" "coeff p 1 = b" "coeff p 0 = c" unfolding p by (auto simp: 2)
  let ?b2a = "b / (2 * a)"
  define b2a where "b2a = ?b2a"
  let ?bac = "b2a^2 - c/a"
  define bac where "bac = ?bac"
  have roots: "set (croots2 p) = {- b2a + csqrt bac, - b2a - csqrt bac}"
    unfolding croots2_def Let_def coeff b2a_def[symmetric] bac_def[symmetric]
    by (auto split: if_splits)
  show ?thesis unfolding roots main b2a_def[symmetric] bac_def[symmetric]
    using power2_eq_iff by fastforce
qed

definition rroots2 :: "real poly \<Rightarrow> real list" where
  "rroots2 p = (let a = coeff p 2; b = coeff p 1; c = coeff p 0; b2a = b / (2 * a);
    bac = b2a^2 - c/a
  in if bac = 0 then [- b2a] else if bac < 0 then []
    else let e = sqrt bac
    in
     [- b2a + e, - b2a - e])"

definition rat_roots2 :: "rat poly \<Rightarrow> rat list" where
  "rat_roots2 p = (let a = coeff p 2; b = coeff p 1; c = coeff p 0; b2a = b / (2 * a);
    bac = b2a^2 - c/a
  in map (\<lambda> e. - b2a + e) (sqrt_rat bac))"

lemma rroots2: assumes "degree p = 2"
  shows "{x. poly p x = 0} = set (rroots2 p)"
proof -
  from degree2_coeffs[OF assms] obtain a b c 
  where p: "p = [:c, b, a:]" and a: "a \<noteq> 0" by auto
  note main = roots2[OF p a]
  have 2: "2 = Suc (Suc 0)" by simp
  have coeff: "coeff p 2 = a" "coeff p 1 = b" "coeff p 0 = c" unfolding p by (auto simp: 2)
  let ?b2a = "b / (2 * a)"
  define b2a where "b2a = ?b2a"
  let ?bac = "b2a^2 - c/a"
  define bac where "bac = ?bac"
  have roots: "set (rroots2 p) = (if bac < 0 then {} else {- b2a + sqrt bac, - b2a - sqrt bac})"
    unfolding rroots2_def Let_def coeff b2a_def[symmetric] bac_def[symmetric]
    by (auto split: if_splits)
  show ?thesis unfolding roots main b2a_def[symmetric] bac_def[symmetric]
    by auto
qed

lemma rat_roots2: assumes "degree p = 2"
  shows "{x. poly p x = 0} = set (rat_roots2 p)"
proof -
  from degree2_coeffs[OF assms] obtain a b c 
  where p: "p = [:c, b, a:]" and a: "a \<noteq> 0" by auto
  note main = roots2[OF p a]
  have 2: "2 = Suc (Suc 0)" by simp
  have coeff: "coeff p 2 = a" "coeff p 1 = b" "coeff p 0 = c" unfolding p by (auto simp: 2)
  let ?b2a = "b / (2 * a)"
  define b2a where "b2a = ?b2a"
  let ?bac = "b2a^2 - c/a"
  define bac where "bac = ?bac"
  have roots: "(rat_roots2 p) = (map (\<lambda> e. -b2a + e) (sqrt_rat bac))"
    unfolding rat_roots2_def Let_def coeff b2a_def[symmetric] bac_def[symmetric] by auto
  show ?thesis unfolding roots main b2a_def[symmetric] bac_def[symmetric]
    by (auto simp: power2_eq_square)
qed


text \<open>Determinining roots of complex polynomials of degree up to 2.\<close>

definition croots :: "complex poly \<Rightarrow> complex list" where
  "croots p = (if p = 0 \<or> degree p > 2 then [] 
    else (if degree p = 0 then [] else if degree p = 1 then [roots1 p]
    else croots2 p))"

lemma croots: assumes "p \<noteq> 0" "degree p \<le> 2"
  shows "set (croots p) = {x. poly p x = 0}"
  using assms unfolding croots_def
  using roots0[of p] roots1[of p] croots2[of p]
  by (auto split: if_splits)

text \<open>Determinining roots of real polynomials of degree up to 2.\<close>

definition rroots :: "real poly \<Rightarrow> real list" where
  "rroots p = (if p = 0 \<or> degree p > 2 then [] 
    else (if degree p = 0 then [] else if degree p = 1 then [roots1 p]
    else rroots2 p))"

lemma rroots: assumes "p \<noteq> 0" "degree p \<le> 2"
  shows "set (rroots p) = {x. poly p x = 0}"
  using assms unfolding rroots_def
  using roots0[of p] roots1[of p] rroots2[of p]
  by (auto split: if_splits)

end
