subsection \<open>Resultants of Multivariate Polynomials\<close>

text \<open>We utilize the conversion of multivariate polynomials into univariate polynomials
  for the definition of the resultant of multivariate polynomials via
  the resultant for univariate polynomials. In this way, we can use the algorithm
  to efficiently compute resultants for the multivariate case.\<close>

theory Multivariate_Resultant
  imports 
    Poly_Connection
    Algebraic_Numbers.Resultant
    Subresultants.Subresultant
    MPoly_Divide_Code
    MPoly_Container
begin

hide_const (open) 
  MPoly_Type.degree
  MPoly_Type.coeff
  Symmetric_Polynomials.lead_coeff

lemma det_sylvester_matrix_higher_degree: 
  "det (sylvester_mat_sub (degree f + n) (degree g) f g)
  = det (sylvester_mat_sub (degree f) (degree g) f g) * (lead_coeff g * (-1)^(degree g))^n"
proof (induct n)
  case (Suc n)
  let ?A = "sylvester_mat_sub (degree f + Suc n) (degree g) f g" 
  let ?d = "degree f + Suc n + degree g" 
  define h where "h i = ?A $$ (i,0) * cofactor ?A i 0" for i
  have mult_left_zero: "x = 0 \<Longrightarrow> x * y = 0" for x y :: 'a by auto
  have "det ?A = (\<Sum>i<?d. h i)" 
    unfolding h_def
    by (rule laplace_expansion_column[OF sylvester_mat_sub_carrier, of 0], force)
  also have "\<dots> = sum h ({degree g} \<union> ({..<?d} - {degree g}))" 
    by (rule sum.cong, auto)
  also have "\<dots> = sum h {degree g} + sum h ({..<?d} - {degree g})" 
    by (rule sum.union_disjoint, auto)
  also have "sum h ({..<?d} - {degree g}) = 0" 
    unfolding h_def
    by (intro sum.neutral ballI mult_left_zero, auto simp: sylvester_mat_sub_def coeff_eq_0)
  also have "sum h {degree g} = h (degree g)" by simp
  also have "\<dots> = lead_coeff g * cofactor ?A (degree g) 0" unfolding h_def
    by (rule arg_cong[of _ _ "\<lambda> x. x * _"], simp add: sylvester_mat_sub_def)
  also have "cofactor ?A (degree g) 0 = (-1)^(degree g) * det (sylvester_mat_sub (degree f + n) (degree g) f g)" 
    unfolding cofactor_def
  proof (intro arg_cong2[of _ _ _ _ "\<lambda> x y. (-1)^x * det y"], force)
    show "mat_delete ?A (degree g) 0 = sylvester_mat_sub (degree f + n) (degree g) f g" 
      unfolding sylvester_mat_sub_def
      by (intro eq_matI, auto simp: mat_delete_def coeff_eq_0)
  qed
  finally show ?case unfolding Suc by simp
qed simp

text \<open>The conversion of multivariate into univariate polynomials permits us to define resultants in the multivariate
  setting. Since in our application one of the polynomials is already univariate, we use a non-symmetric definition
  where only one of the input polynomials is multivariate.\<close>
definition resultant_mpoly_poly :: "nat \<Rightarrow> 'a :: comm_ring_1 mpoly \<Rightarrow> 'a poly \<Rightarrow> 'a mpoly" where
  "resultant_mpoly_poly x p q = resultant (mpoly_to_mpoly_poly x p) (map_poly Const q)"

text \<open>This lemma tells us that there is only a minor difference between computing the multivariate resultant and then
  plugging in values, or first inserting values and then evaluate the univariate resultant.\<close>
lemma insertion_resultant_mpoly_poly: "insertion \<alpha> (resultant_mpoly_poly x p q) = resultant (partial_insertion \<alpha> x p) q * 
  (lead_coeff q * (-1)^ degree q)^(degree (mpoly_to_mpoly_poly x p) - degree (partial_insertion \<alpha> x p))" 
proof -
  let ?pa = "partial_insertion \<alpha> x" 
  let ?a = "insertion \<alpha>" 
  let ?q = "map_poly Const q" 
  let ?m = "mpoly_to_mpoly_poly x" 
  interpret a: comm_ring_hom ?a by (rule comm_ring_hom_insertion)
  define m where "m = degree (?m p) - degree (?pa p)" 
  from degree_partial_insertion_le_mpoly[of \<alpha> x p] have deg: "degree (?m p) = degree (?pa p) + m" unfolding m_def by simp
  define k where "k = degree (?pa p) + m" 
  define l where "l = degree q" 
  have "resultant (?pa p) q = det (sylvester_mat_sub (degree (?pa p)) (degree q) (?pa p) q)" 
    unfolding resultant_def sylvester_mat_def by simp
  have "?a (resultant_mpoly_poly x p q) = ?a (det (sylvester_mat_sub (degree (?pa p) + m) (degree q) (?m p) ?q))" 
    unfolding resultant_mpoly_poly_def resultant_def sylvester_mat_def degree_map_poly_Const deg ..
  also have "\<dots> =
    det (a.mat_hom (sylvester_mat_sub (degree (?pa p) + m) (degree q) (?m p) ?q))" 
    unfolding a.hom_det ..
  also have "a.mat_hom (sylvester_mat_sub (degree (?pa p) + m) (degree q) (?m p) ?q)
    = sylvester_mat_sub (degree (?pa p) + m) (degree q) (?pa p) q" 
    unfolding k_def[symmetric] l_def[symmetric] 
    by (intro eq_matI, auto simp: sylvester_mat_sub_def coeff_map_poly)
  also have "det \<dots> = det (sylvester_mat_sub (degree (?pa p)) (degree q) (?pa p) q) * (lead_coeff q * (- 1) ^ degree q) ^ m" 
    by (subst det_sylvester_matrix_higher_degree, simp)
  also have "det (sylvester_mat_sub (degree (?pa p)) (degree q) (?pa p) q) = resultant (?pa p) q" 
    unfolding resultant_def sylvester_mat_def by simp
  finally show ?thesis unfolding m_def by auto
qed

lemma insertion_resultant_mpoly_poly_zero: fixes q :: "'a :: idom poly" 
  assumes q: "q \<noteq> 0" 
  shows "insertion \<alpha> (resultant_mpoly_poly x p q) = 0 \<longleftrightarrow> resultant (partial_insertion \<alpha> x p) q = 0" 
  unfolding insertion_resultant_mpoly_poly using q by auto

lemma vars_resultant: "vars (resultant p q) \<subseteq> \<Union> (vars ` (range (coeff p) \<union> range (coeff q)))" 
  unfolding resultant_def det_def sylvester_mat_def sylvester_mat_sub_def 
  apply simp
  apply (rule order.trans[OF vars_setsum]) 
  subgoal using finite_permutations by blast
  apply (rule UN_least)
  apply (rule order.trans[OF vars_mult]) 
  apply simp
  apply (rule order.trans[OF vars_prod])
  apply (rule UN_least)
  by auto

text \<open>By taking the resultant, one variable is deleted.\<close>
lemma vars_resultant_mpoly_poly: "vars (resultant_mpoly_poly x p q) \<subseteq> vars p - {x}" 
proof
  fix y
  assume "y \<in> vars (resultant_mpoly_poly x p q)" 
  from set_mp[OF vars_resultant this[unfolded resultant_mpoly_poly_def]] obtain i 
    where "y \<in> vars (coeff (mpoly_to_mpoly_poly x p) i) \<or> y \<in> vars (coeff (map_poly Const q) i)" 
    by auto
  moreover have "vars (coeff (map_poly Const q) i) = {}" 
    by (subst coeff_map_poly, auto)
  ultimately have "y \<in> vars (coeff (mpoly_to_mpoly_poly x p) i)" by auto
  thus "y \<in> More_MPoly_Type.vars p - {x}" using vars_coeff_mpoly_to_mpoly_poly by blast
qed

text \<open>For resultants, we manually have to select the implementation that 
  works on integral domains, because there is no factorial ring instance for @{typ "int mpoly"}.\<close>

lemma resultant_mpoly_poly_code[code]:
  "resultant_mpoly_poly x p q = resultant_impl_basic (mpoly_to_mpoly_poly x p) (map_poly Const q)"
  unfolding resultant_mpoly_poly_def div_exp_basic.resultant_impl by simp

end