(*
    Authors:      Jose Divasón
                  Sebastiaan Joosten
                  René Thiemann
                  Akihisa Yamada
*)
section \<open>External Interface\<close>

text \<open>We provide two functions for external usage that work on lists and integers only,
  so that they can easily be accessed via these primitive datatypes.\<close>

theory Factorization_External_Interface
  imports      
    Factorize_Rat_Poly
    Factorize_Int_Poly
begin

declare Lcm_fin.set_eq_fold[code_unfold]

definition factor_int_poly :: "integer list \<Rightarrow> integer \<times> (integer list \<times> integer) list" where 
  "factor_int_poly p = map_prod integer_of_int (map (map_prod (map integer_of_int o coeffs) integer_of_nat)) 
     (factorize_int_poly (poly_of_list (map int_of_integer p)))"

text \<open>Just for clarifying the representation, we present a part of the soundness statement 
  of the factorization algorithm with conversions included\<close>
lemma factor_int_poly: assumes "factor_int_poly p = (c, qes)" 
  shows "poly_of_list (map int_of_integer p) = smult (int_of_integer c) 
    (\<Prod>(q, e)\<leftarrow>qes. poly_of_list (map int_of_integer q) ^ nat_of_integer e)" 
  (is "?p = ?prod")
proof -
  obtain C Qes where fact: "factorize_int_poly ?p = (C,Qes)" by force
  from square_free_factorization_prod_list[OF factorize_int_poly(1)[OF this]]
  have "?p = smult C (\<Prod>(x, y)\<leftarrow>Qes. x ^ y)" .
  also have "\<dots> = ?prod" using assms[unfolded factor_int_poly_def fact, symmetric]
    by (intro arg_cong2[of _ _ _ _ "\<lambda> x y. smult x (prod_list y)"], auto simp: o_def)
  finally show ?thesis .
qed

text \<open>Note that coefficients are listed with lowest coefficient as head of list\<close>
value "coeffs (monom 1 3) :: int list"
value "factor_int_poly [0,0,0,5]"
value "factor_int_poly [0,1,-2,1]"


definition integers_of_rat where "integers_of_rat x = map_prod integer_of_int integer_of_int (quotient_of x)" 
fun rat_of_integers where "rat_of_integers (n,d) = (rat_of_int (int_of_integer n) / rat_of_int (int_of_integer d))" 

definition integer_of_rat where "integer_of_rat x = integer_of_int (fst (quotient_of x))" 
definition rat_of_integer where "rat_of_integer x = rat_of_int (int_of_integer x)"

lemma integers_of_rat[simp]: "rat_of_integers (integers_of_rat x) = x" 
proof -
  obtain n d where id: "quotient_of x = (n,d)" by force
  from quotient_of_div[OF id]
  show ?thesis unfolding integers_of_rat_def id by auto
qed

lemma integer_of_rat[simp]: assumes "x \<in> \<int>" 
  shows "rat_of_integer (integer_of_rat x) = x" 
proof -
  from assms obtain y where x: "x = of_int y" unfolding Ints_def by auto
  hence id: "quotient_of x = (y,1)" by simp
  from quotient_of_div[OF id]
  show ?thesis unfolding integer_of_rat_def rat_of_integer_def id by auto
qed

definition factor_rat_poly :: "(integer \<times> integer) list \<Rightarrow> (integer \<times> integer) \<times> (integer list \<times> integer) list" where 
  "factor_rat_poly p = map_prod integers_of_rat (map (map_prod (map integer_of_rat o coeffs) integer_of_nat)) 
     (factorize_rat_poly (poly_of_list (map rat_of_integers p)))"

lemma factor_rat_poly: assumes "factor_rat_poly p = (c, qes)" 
  shows "poly_of_list (map rat_of_integers p) = smult (rat_of_integers c) 
    (\<Prod>(q, e)\<leftarrow>qes. poly_of_list (map rat_of_integer q) ^ nat_of_integer e)" 
  (is "?p = ?prod")
proof -
  obtain C Qes where fact: "factorize_rat_poly ?p = (C,Qes)" by force
  {
    fix a b
    assume ab: "(a,b) \<in> set Qes" 
    with fact[unfolded factorize_rat_poly_generic_def] have a: "a \<in> range of_int_poly" 
      by (auto split: prod.splits)
    have "map (\<lambda>x. rat_of_integer (integer_of_rat x)) (coeffs a) = map (\<lambda> x. x) (coeffs a)" 
      by (intro map_cong[OF refl integer_of_rat], insert a, force)   
    hence "Poly (map (\<lambda>x. rat_of_integer (integer_of_rat x)) (coeffs a)) = a" by simp       
  } note eq = this
  from square_free_factorization_prod_list[OF factorize_rat_poly(1)[OF fact]]
  have "?p = smult C (\<Prod>(x, y)\<leftarrow>Qes. x ^ y)" .
  also have "\<dots> = ?prod" using assms[unfolded factor_rat_poly_def fact, symmetric]
    apply (intro arg_cong2[of _ _ _ _ "\<lambda> x y. smult x (prod_list y)"])
    subgoal by simp
    subgoal using eq by (auto simp add: o_def intro!: arg_cong[of _ _ "\<lambda> x. x ^ _"])
    done
  finally show ?thesis .
qed

text \<open>Note that rational numbers in the input are encoded as pairs, whereas the polynomials
  in the output are just integer polynomials, i.e., only the constant factor is a rational number\<close>

value "factor_rat_poly [(1,6),(-1,3),(1,6)]" 

end
 