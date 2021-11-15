section \<open>Representing Roots of Polynomials with Algebraic Coefficients\<close>

text \<open>We provide an algorithm to compute a non-zero integer polynomial $q$ from a polynomial
 $p$ with algebraic coefficients such that all roots of $p$ are also roots of $q$.

 In this way, we have a constructive proof that the set of complex algebraic numbers 
 is algebraically closed.\<close>

theory Roots_of_Algebraic_Poly
  imports 
    Algebraic_Numbers.Complex_Algebraic_Numbers
    Multivariate_Resultant
    Is_Int_To_Int
begin

subsection \<open>Preliminaries\<close>

hide_const (open) up_ring.monom
hide_const (open) MPoly_Type.monom

lemma map_mpoly_Const: "f 0 = 0 \<Longrightarrow> map_mpoly f (Const i) = Const (f i)" 
  by (intro mpoly_eqI, auto simp: coeff_map_mpoly mpoly_coeff_Const)

lemma map_mpoly_Var: "f 1 = 1 \<Longrightarrow> map_mpoly (f :: 'b :: zero_neq_one \<Rightarrow> _) (Var i) = Var i"
  by (intro mpoly_eqI, auto simp: coeff_map_mpoly coeff_Var when_def)

lemma map_mpoly_monom: "f 0 = 0 \<Longrightarrow> map_mpoly f (MPoly_Type.monom m a) = (MPoly_Type.monom m (f a))" 
  by (intro mpoly_eqI, unfold coeff_map_mpoly if_distrib coeff_monom, simp add: when_def)

lemma remove_key_single': 
  "remove_key v (Poly_Mapping.single w n) = (if v = w then 0 else Poly_Mapping.single w n)"
  by (metis add.right_neutral lookup_single_not_eq remove_key_single remove_key_sum single_zero)

context comm_monoid_add_hom
begin
lemma hom_Sum_any: assumes fin: "finite {x. f x \<noteq> 0}"
  shows "hom (Sum_any f) = Sum_any (\<lambda> x. hom (f x))" 
  unfolding Sum_any.expand_set hom_sum
  by (rule sum.mono_neutral_right[OF fin], auto)
 
lemma comm_monoid_add_hom_mpoly_map: "comm_monoid_add_hom (map_mpoly hom)" 
  by (unfold_locales; intro mpoly_eqI, auto simp: hom_add)

lemma map_mpoly_hom_Const: "map_mpoly hom (Const i) = Const (hom i)" 
  by (rule map_mpoly_Const, simp)

lemma map_mpoly_hom_monom: "map_mpoly hom (MPoly_Type.monom m a) = MPoly_Type.monom m (hom a)" 
  by (rule map_mpoly_monom, simp)
end

context comm_ring_hom
begin
lemma mpoly_to_poly_map_mpoly_hom: "mpoly_to_poly x (map_mpoly hom p) = map_poly hom (mpoly_to_poly x p)"
  by (rule poly_eqI, unfold coeff_mpoly_to_poly coeff_map_poly_hom, subst coeff_map_mpoly', auto)
 
lemma comm_ring_hom_mpoly_map: "comm_ring_hom (map_mpoly hom)" 
proof -
  interpret mp: comm_monoid_add_hom "map_mpoly hom" by (rule comm_monoid_add_hom_mpoly_map)
  show ?thesis
  proof (unfold_locales)
    show "map_mpoly hom 1 = 1"
      by (intro mpoly_eqI, simp add: MPoly_Type.coeff_def, transfer fixing: hom, transfer fixing: hom, auto simp: when_def)
    fix x y
    show "map_mpoly hom (x * y) = map_mpoly hom x * map_mpoly hom y" 
      apply (intro mpoly_eqI)
      apply (subst coeff_map_mpoly', force)
      apply (unfold coeff_mpoly_times) 
      apply (subst prod_fun_unfold_prod, blast, blast)
      apply (subst prod_fun_unfold_prod, blast, blast) 
      apply (subst coeff_map_mpoly', force)
      apply (subst coeff_map_mpoly', force)
      apply (subst hom_Sum_any) 
      subgoal 
      proof -
        let ?X = "{a. MPoly_Type.coeff x a \<noteq> 0}" 
        let ?Y = "{a. MPoly_Type.coeff y a \<noteq> 0}" 
        have fin: "finite (?X \<times> ?Y)" by auto
        show ?thesis 
          by (rule finite_subset[OF _ fin], auto)
      qed
      apply (rule Sum_any.cong)
      subgoal for mon pair by (cases pair, auto simp: hom_mult when_def)
      done
  qed
qed

lemma mpoly_to_mpoly_poly_map_mpoly_hom: 
  "mpoly_to_mpoly_poly x (map_mpoly hom p) = map_poly (map_mpoly hom) (mpoly_to_mpoly_poly x p)" 
proof -
  interpret mp: comm_ring_hom "map_mpoly hom" by (rule comm_ring_hom_mpoly_map)
  interpret mmp: map_poly_comm_monoid_add_hom "map_mpoly hom" ..
  show ?thesis unfolding mpoly_to_mpoly_poly_def 
    apply (subst mmp.hom_Sum_any, force)
    apply (rule Sum_any.cong)
    apply (unfold mp.map_poly_hom_monom map_mpoly_hom_monom)
    by auto
qed    
end

context inj_comm_ring_hom
begin
lemma inj_comm_ring_hom_mpoly_map: "inj_comm_ring_hom (map_mpoly hom)" 
proof -
  interpret mp: comm_ring_hom "map_mpoly hom" by (rule comm_ring_hom_mpoly_map)
  show ?thesis
  proof (unfold_locales)
    fix x
    assume 0: "map_mpoly hom x = 0"     
    show "x = 0" 
    proof (intro mpoly_eqI)
      fix m
      show "MPoly_Type.coeff x m = MPoly_Type.coeff 0 m" 
        using arg_cong[OF 0, of "\<lambda> p. MPoly_Type.coeff p m"] by simp
    qed
  qed
qed

lemma resultant_mpoly_poly_hom: "resultant_mpoly_poly x (map_mpoly hom p) (map_poly hom q) = map_mpoly hom (resultant_mpoly_poly x p q)"
proof -
  interpret mp: inj_comm_ring_hom "map_mpoly hom" by (rule inj_comm_ring_hom_mpoly_map)
  show ?thesis
  unfolding resultant_mpoly_poly_def 
  unfolding mpoly_to_mpoly_poly_map_mpoly_hom 
  apply (subst mp.resultant_map_poly[symmetric])
  subgoal by (subst mp.degree_map_poly_hom, unfold_locales, auto) 
  subgoal by (subst mp.degree_map_poly_hom, unfold_locales, auto) 
  subgoal
    apply (rule arg_cong[of _ _ "resultant _"], intro poly_eqI)
    apply (subst coeff_map_poly, force)+
    by (simp add: map_mpoly_hom_Const)
  done
qed
end

lemma map_insort_key: assumes [simp]: "\<And> x y. g1 x \<le> g1 y \<longleftrightarrow> g2 (f x) \<le> g2 (f y)"
  shows "map f (insort_key g1 a xs) = insort_key g2 (f a) (map f xs)" 
  by (induct xs, auto)

lemma map_sort_key: assumes [simp]: "\<And> x y. g1 x \<le> g1 y \<longleftrightarrow> g2 (f x) \<le> g2 (f y)"
  shows "map f (sort_key g1 xs) = sort_key g2 (map f xs)" 
  by (induct xs, auto simp: map_insort_key)

hide_const (open) MPoly_Type.degree
hide_const (open) MPoly_Type.coeffs
hide_const (open) MPoly_Type.coeff
hide_const (open) Symmetric_Polynomials.lead_coeff

subsection \<open>More Facts about Resultants\<close>

lemma resultant_iff_coprime_main:
  fixes f g :: "'a :: field poly"
  assumes deg: "degree f > 0 \<or> degree g > 0" 
shows "resultant f g = 0 \<longleftrightarrow> \<not> coprime f g" 
proof (cases "resultant f g = 0")
  case True
  from resultant_zero_imp_common_factor[OF deg True] True
  show ?thesis by simp
next
  case False
  from deg have fg: "f \<noteq> 0 \<or> g \<noteq> 0" by auto
  from resultant_non_zero_imp_coprime[OF False fg] deg False
  show ?thesis by auto
qed

lemma resultant_zero_iff_coprime: fixes f g :: "'a :: field poly" 
  assumes "f \<noteq> 0 \<or> g \<noteq> 0" 
  shows "resultant f g = 0 \<longleftrightarrow> \<not> coprime f g" 
proof (cases "degree f > 0 \<or> degree g > 0")
  case True
  thus ?thesis using resultant_iff_coprime_main[OF True] by simp
next
  case False
  hence "degree f = 0" "degree g = 0" by auto
  then obtain c d where f: "f = [:c:]" and g: "g = [:d:]" using degree0_coeffs by metis+
  from assms have cd: "c \<noteq> 0 \<or> d \<noteq> 0" unfolding f g by auto
  have res: "resultant f g = 1" unfolding f g resultant_const by auto
  have "coprime f g"  
    by (metis assms one_neq_zero res resultant_non_zero_imp_coprime)
  with res show ?thesis by auto
qed

text \<open>The problem with the upcoming lemma is that "root" and "irreducibility" refer to the same type.
  In the actual application we interested in "irreducibility" over the integers, but the roots
  we are interested in are either real or complex.\<close>
lemma resultant_zero_iff_common_root_irreducible: fixes f g :: "'a :: field poly"
  assumes irr: "irreducible g" 
  and root: "poly g a = 0" (* g has at least some root *)
shows "resultant f g = 0 \<longleftrightarrow> (\<exists> x. poly f x = 0 \<and> poly g x = 0)" 
proof -
  from irr root have deg: "degree g \<noteq> 0" using degree0_coeffs[of g] by fastforce
  show ?thesis
  proof 
    assume "\<exists> x. poly f x = 0 \<and> poly g x = 0" 
    then obtain x where "poly f x = 0" "poly g x = 0" by auto
    from resultant_zero[OF _ this] deg show "resultant f g = 0" by auto
  next
    assume "resultant f g = 0"
    from resultant_zero_imp_common_factor[OF _ this] deg
    have "\<not> coprime f g" by auto
    from this[unfolded not_coprime_iff_common_factor] obtain r where
       rf: "r dvd f" and rg: "r dvd g" and r: "\<not> is_unit r" by auto
    from rg r irr have "g dvd r"
      by (meson algebraic_semidom_class.irreducible_altdef)
    with rf have "g dvd f" by auto
    with root show "\<exists> x. poly f x = 0 \<and> poly g x = 0" 
      by (intro exI[of _ a], auto simp: dvd_def)
  qed
qed


lemma resultant_zero_iff_common_root_complex: fixes f g :: "complex poly"
  assumes g: "g \<noteq> 0" 
shows "resultant f g = 0 \<longleftrightarrow> (\<exists> x. poly f x = 0 \<and> poly g x = 0)" 
proof (cases "degree g = 0")
  case deg: False
  show ?thesis
  proof 
    assume "\<exists> x. poly f x = 0 \<and> poly g x = 0" 
    then obtain x where "poly f x = 0" "poly g x = 0" by auto
    from resultant_zero[OF _ this] deg show "resultant f g = 0" by auto
  next
    assume "resultant f g = 0"
    from resultant_zero_imp_common_factor[OF _ this] deg
    have "\<not> coprime f g" by auto
    from this[unfolded not_coprime_iff_common_factor] obtain r where
       rf: "r dvd f" and rg: "r dvd g" and r: "\<not> is_unit r" by auto
    from rg g have r0: "r \<noteq> 0" by auto
    with r have degr: "degree r \<noteq> 0" by simp
    hence "\<not> constant (poly r)"
      by (simp add: constant_degree)
    from fundamental_theorem_of_algebra[OF this] obtain a where root: "poly r a = 0" by auto
    from rf rg root show "\<exists> x. poly f x = 0 \<and> poly g x = 0" 
      by (intro exI[of _ a], auto simp: dvd_def)
  qed
next
  case deg: True
  from degree0_coeffs[OF deg] obtain c where gc: "g = [:c:]" by auto
  from gc g have c: "c \<noteq> 0" by auto
  hence "resultant f g \<noteq> 0" unfolding gc resultant_const by simp
  with gc c show ?thesis by auto
qed

subsection \<open>Systems of Polynomials\<close>

text \<open>Definition of solving a system of polynomials, one being multivariate\<close>
definition mpoly_polys_solution :: "'a :: field mpoly \<Rightarrow> (nat \<Rightarrow> 'a poly) \<Rightarrow> nat set \<Rightarrow> (nat \<Rightarrow> 'a) \<Rightarrow> bool" where
  "mpoly_polys_solution p qs N \<alpha> = (
       insertion \<alpha> p = 0 \<and>
       (\<forall> i \<in> N. poly (qs i) (\<alpha> (Suc i)) = 0))"

text \<open>The upcoming lemma shows how to eliminate single variables in multi-variate root-problems.
  Because of the problem mentioned in @{thm [source] resultant_zero_iff_common_root_irreducible},
  we here restrict to polynomials over the complex numbers. Since the result computations are homomorphisms,
  we are able to lift it to integer polynomials where we are interested in real or complex
  roots.\<close>
lemma resultant_mpoly_polys_solution: fixes p :: "complex mpoly" 
  assumes nz: "0 \<notin> qs ` N" 
  and i: "i \<in> N"
shows "mpoly_polys_solution (resultant_mpoly_poly (Suc i) p (qs i)) qs (N - {i}) \<alpha>
  \<longleftrightarrow> (\<exists> v. mpoly_polys_solution p qs N (\<alpha>((Suc i) := v)))" 
proof -
  let ?x = "Suc i" 
  let ?q = "qs i" 
  let ?mres = "resultant_mpoly_poly ?x p ?q"
  from i obtain M where N: "N = insert i M" and MN: "M = N - {i}" and iM: "i \<notin> M" by auto
  from nz i have nzq: "?q \<noteq> 0" by auto
  hence lc0: "lead_coeff (qs i) \<noteq> 0" by auto
  have "mpoly_polys_solution ?mres qs (N - {i}) \<alpha> \<longleftrightarrow>
   insertion \<alpha> ?mres = 0 \<and> (\<forall> i \<in> M. poly (qs i) (\<alpha> (Suc i)) = 0)" 
    unfolding mpoly_polys_solution_def MN ..
  also have "insertion \<alpha> ?mres = 0 \<longleftrightarrow> resultant (partial_insertion \<alpha> ?x p) ?q = 0" 
    by (rule insertion_resultant_mpoly_poly_zero[OF nzq])
  also have "\<dots> \<longleftrightarrow> (\<exists>v. poly (partial_insertion \<alpha> ?x p) v = 0 \<and> poly ?q v = 0)" 
    by (rule resultant_zero_iff_common_root_complex[OF nzq])
  also have "\<dots> \<longleftrightarrow> (\<exists>v. insertion (\<alpha>(?x := v)) p = 0 \<and> poly ?q v = 0)" (is "?lhs = ?rhs")
  proof (intro iff_exI conj_cong refl arg_cong[of _ _ "\<lambda> x. x = 0"])
    fix v
    have "poly (partial_insertion \<alpha> ?x p) v = poly (partial_insertion \<alpha> ?x p) ((\<alpha>(?x := v)) ?x)" by simp
    also have "\<dots> = insertion (\<alpha>(?x := v)) p" 
      by (rule insertion_partial_insertion, auto)
    finally show "poly (partial_insertion \<alpha> ?x p) v = insertion (\<alpha>(?x := v)) p" .
  qed
  also have "\<dots> \<and> (\<forall>i\<in>M. poly (qs i) (\<alpha> (Suc i)) = 0)
    \<longleftrightarrow> (\<exists>v. insertion (\<alpha>(?x := v)) p = 0 \<and> poly (qs i) v = 0 \<and> (\<forall>i\<in>M. poly (qs i) ((\<alpha>(?x := v)) (Suc i)) = 0))"
    using iM by auto
  also have "\<dots>  \<longleftrightarrow> (\<exists> v. mpoly_polys_solution p qs N (\<alpha>((Suc i) := v)))" 
    unfolding mpoly_polys_solution_def N by (intro iff_exI, auto)
  finally
  show ?thesis .
qed

text \<open>We now restrict solutions to be evaluated to zero outside the variable range. Then there are only finitely 
  many solutions for our applications.\<close>
definition mpoly_polys_zero_solution :: "'a :: field mpoly \<Rightarrow> (nat \<Rightarrow> 'a poly) \<Rightarrow> nat set \<Rightarrow> (nat \<Rightarrow> 'a) \<Rightarrow> bool" where
  "mpoly_polys_zero_solution p qs N \<alpha> = (mpoly_polys_solution p qs N \<alpha>
    \<and> (\<forall> i. i \<notin> insert 0 (Suc ` N) \<longrightarrow> \<alpha> i = 0))" 

lemma resultant_mpoly_polys_zero_solution: fixes p :: "complex mpoly" 
  assumes nz: "0 \<notin> qs ` N" 
  and i: "i \<in> N"
shows 
  "mpoly_polys_zero_solution (resultant_mpoly_poly (Suc i) p (qs i)) qs (N - {i}) \<alpha> 
    \<Longrightarrow> \<exists> v. mpoly_polys_zero_solution p qs N (\<alpha>(Suc i := v))" 
  "mpoly_polys_zero_solution p qs N \<alpha> 
    \<Longrightarrow> mpoly_polys_zero_solution (resultant_mpoly_poly (Suc i) p (qs i)) qs (N - {i}) (\<alpha>(Suc i := 0))" 
proof -
  assume "mpoly_polys_zero_solution (resultant_mpoly_poly (Suc i) p (qs i)) qs (N - {i}) \<alpha>" 
  hence 1: "mpoly_polys_solution (resultant_mpoly_poly (Suc i) p (qs i)) qs (N - {i}) \<alpha>" and 2: "(\<forall> i. i \<notin> insert 0 (Suc ` (N - {i})) \<longrightarrow> \<alpha> i = 0)" 
    unfolding mpoly_polys_zero_solution_def by auto
  from resultant_mpoly_polys_solution[of qs N _ p \<alpha>, OF nz i] 1 obtain v where "mpoly_polys_solution p qs N (\<alpha>(Suc i := v))" by auto
  with 2 have "mpoly_polys_zero_solution p qs N (\<alpha>(Suc i := v))" using i unfolding mpoly_polys_zero_solution_def by auto
  thus "\<exists> v. mpoly_polys_zero_solution p qs N (\<alpha>(Suc i := v))" ..
next
  assume "mpoly_polys_zero_solution p qs N \<alpha>" 
  from this[unfolded mpoly_polys_zero_solution_def] have 1: "mpoly_polys_solution p qs N \<alpha>" and 2: "\<forall>i. i \<notin> insert 0 (Suc ` N) \<longrightarrow> \<alpha> i = 0" by auto
  from 1 have "mpoly_polys_solution p qs N (\<alpha>(Suc i := \<alpha> (Suc i)))" by auto
  hence "\<exists> v. mpoly_polys_solution p qs N (\<alpha>(Suc i := v))" by blast
  with resultant_mpoly_polys_solution[of qs N _ p \<alpha>, OF nz i] have "mpoly_polys_solution (resultant_mpoly_poly (Suc i) p (qs i)) qs (N - {i}) \<alpha>" by auto
  hence "mpoly_polys_solution (resultant_mpoly_poly (Suc i) p (qs i)) qs (N - {i}) (\<alpha> (Suc i := 0))"
    unfolding mpoly_polys_solution_def 
    apply simp
    apply (subst insertion_irrelevant_vars[of _ _ \<alpha>])
    by (insert vars_resultant_mpoly_poly, auto)
  thus "mpoly_polys_zero_solution (resultant_mpoly_poly (Suc i) p (qs i)) qs (N - {i}) (\<alpha>(Suc i := 0))" 
    unfolding mpoly_polys_zero_solution_def using 2 by auto
qed

text \<open>The following two lemmas show that if we start with a system of polynomials with finitely
  many solutions, then the resulting polynomial cannot be the zero-polynomial.\<close>
lemma finite_resultant_mpoly_polys_non_empty: fixes p :: "complex mpoly" 
  assumes nz: "0 \<notin> qs ` N" 
  and i: "i \<in> N"
  and fin: "finite {\<alpha>. mpoly_polys_zero_solution p qs N \<alpha>}" 
shows "finite {\<alpha>. mpoly_polys_zero_solution (resultant_mpoly_poly (Suc i) p (qs i)) qs (N - {i}) \<alpha>}" 
proof -
  let ?solN = "mpoly_polys_zero_solution p qs N" 
  let ?solN1 = "mpoly_polys_zero_solution (resultant_mpoly_poly (Suc i) p (qs i)) qs (N - {i})" 
  let ?x = "Suc i" 
  note defs = mpoly_polys_zero_solution_def
  define zero where "zero \<alpha> = \<alpha>(?x := 0)" for \<alpha> :: "nat \<Rightarrow> complex" 
  {
    fix \<alpha>
    assume sol: "?solN1 \<alpha>" 
    from sol[unfolded defs] have 0: "\<alpha> ?x = 0" by auto
    from resultant_mpoly_polys_zero_solution(1)[of qs N i p, OF nz i sol] obtain v 
      where "?solN (\<alpha>(?x := v))" by auto
    hence sol: "\<alpha>(?x := v) \<in> {\<alpha>. ?solN \<alpha>}" by auto
    hence "zero (\<alpha>(?x := v)) \<in> zero ` {\<alpha>. ?solN \<alpha>}" by auto
    also have "zero (\<alpha>(?x := v)) = \<alpha>" using 0 by (auto simp: zero_def)
    finally have "\<alpha> \<in> zero ` {\<alpha>. ?solN \<alpha>}" .
  }
  hence "{\<alpha>. ?solN1 \<alpha>} \<subseteq> zero ` {\<alpha>. ?solN \<alpha>}" by blast
  from finite_subset[OF this finite_imageI[OF fin]]
  show ?thesis .
qed

lemma finite_resultant_mpoly_polys_empty: fixes p :: "complex mpoly" 
  assumes "finite {\<alpha>. mpoly_polys_zero_solution p qs {} \<alpha>}" 
  shows "p \<noteq> 0" 
proof
  define g where "g x = (\<lambda> i :: nat. if i = 0 then x else 0)" for x :: complex
  assume "p = 0" 
  hence "\<forall> x. mpoly_polys_zero_solution p qs {} (g x)" 
    unfolding mpoly_polys_zero_solution_def mpoly_polys_solution_def g_def by auto
  hence "range g \<subseteq> {\<alpha>. mpoly_polys_zero_solution p qs {} \<alpha>}" by auto
  from finite_subset[OF this assms] have "finite (range g)" .
  moreover have "inj g" unfolding g_def inj_on_def by metis
  ultimately have "finite (UNIV :: complex set)" by simp
  thus False using infinite_UNIV_char_0 by auto
qed

subsection \<open>Elimination of Auxiliary Variables\<close>

fun eliminate_aux_vars :: "'a :: comm_ring_1 mpoly \<Rightarrow> (nat \<Rightarrow> 'a poly) \<Rightarrow> nat list \<Rightarrow> 'a poly" where
  "eliminate_aux_vars p qs [] = mpoly_to_poly 0 p" 
| "eliminate_aux_vars p qs (i # is) = eliminate_aux_vars (resultant_mpoly_poly (Suc i) p (qs i)) qs is" 
      

lemma eliminate_aux_vars_of_int_poly: 
  "eliminate_aux_vars (map_mpoly (of_int :: _ \<Rightarrow> 'a :: {comm_ring_1,ring_char_0}) mp) (of_int_poly \<circ> qs) is
  = of_int_poly (eliminate_aux_vars mp qs is)"  
proof -
  let ?h = "of_int :: _ \<Rightarrow> 'a" 
  interpret mp: comm_ring_hom "(map_mpoly ?h)" 
    by (rule of_int_hom.comm_ring_hom_mpoly_map)
  show ?thesis
  proof (induct "is" arbitrary: mp)
    case Nil
    show ?case by (simp add: of_int_hom.mpoly_to_poly_map_mpoly_hom)
  next
    case (Cons i "is" mp)
    show ?case unfolding eliminate_aux_vars.simps Cons[symmetric]
      apply (rule arg_cong[of _ _ "\<lambda> x. eliminate_aux_vars x _ _"], unfold o_def)
      by (rule of_int_hom.resultant_mpoly_poly_hom)
  qed
qed

text \<open>The polynomial of the elimination process will represent the first value @{term "\<alpha> 0 :: complex"} of any
  solution to the multi-polynomial problem.\<close>
lemma eliminate_aux_vars: fixes p :: "complex mpoly" 
  assumes "distinct is" 
  and "vars p \<subseteq> insert 0 (Suc ` set is)" 
  and "finite {\<alpha>. mpoly_polys_zero_solution p qs (set is) \<alpha>}"
  and "0 \<notin> qs ` set is" 
  and "mpoly_polys_solution p qs (set is) \<alpha>" 
shows "poly (eliminate_aux_vars p qs is) (\<alpha> 0) = 0 \<and> eliminate_aux_vars p qs is \<noteq> 0"
  using assms
proof (induct "is" arbitrary: p)
  case (Nil p)
  from Nil(3) finite_resultant_mpoly_polys_empty[of p] 
  have p0: "p \<noteq> 0" by auto
  from Nil(2) have vars: "vars p \<subseteq> {0}" by auto
  note [simp] = poly_eq_insertion[OF this]
  from Nil(5)[unfolded mpoly_polys_solution_def] 
  have "insertion \<alpha> p = 0" by auto
  also have "insertion \<alpha> p = insertion (\<lambda>v. \<alpha> 0) p" 
    by (rule insertion_irrelevant_vars, insert vars, auto)
  finally
  show ?case using p0 mpoly_to_poly_inverse[OF vars] by (auto simp: poly_to_mpoly0)
next
  case (Cons i "is" p)
  let ?x = "Suc i" 
  let ?p = "resultant_mpoly_poly ?x p (qs i)"
  have dist: "distinct is" using Cons(2) by auto
  have vars: "vars ?p \<subseteq> insert 0 (Suc ` set is)" using Cons(3) vars_resultant_mpoly_poly[of ?x p "qs i"] by auto
  have fin: "finite {\<alpha>. mpoly_polys_zero_solution ?p qs (set is) \<alpha>}"
    using finite_resultant_mpoly_polys_non_empty[of qs "set (i # is)" i p, OF Cons(5)] Cons(2,4) by auto
  have 0: "0 \<notin> qs ` set is" using Cons(5) by auto
  have "(\<exists>v. mpoly_polys_solution p qs (set (i # is)) (\<alpha>(?x := v)))"
    using Cons(6) by (intro exI[of _ "\<alpha> ?x"], auto)
  from this resultant_mpoly_polys_solution[OF Cons(5), of i p \<alpha>]
  have "mpoly_polys_solution ?p qs (set (i # is) - {i}) \<alpha>" 
    by auto
  also have "set (i # is) - {i} = set is" using Cons(2) by auto
  finally have "mpoly_polys_solution ?p qs (set is) \<alpha>" by auto
  note IH = Cons(1)[OF dist vars fin 0 this]
  show ?case unfolding eliminate_aux_vars.simps using IH by simp
qed

subsection \<open>A Representing Polynomial for the Roots of a Polynomial with Algebraic Coefficients\<close>

text \<open>First convert an algebraic polynomial into a system of integer polynomials.\<close>
definition initial_root_problem :: "'a :: {is_rat,field_gcd} poly \<Rightarrow> int mpoly \<times> (nat \<times> 'a \<times> int poly) list" where
  "initial_root_problem p = (let 
      n = degree p;
      cs = coeffs p;
      rcs = remdups (filter (\<lambda> c. c \<notin> \<int>) cs);
      pairs = map (\<lambda> c. (c, min_int_poly c)) rcs;
      spairs = sort_key (\<lambda> (c,f). degree f) pairs; \<comment> \<open>sort by degree so that easy computations will be done first\<close>
      triples = zip [0 ..< length spairs] spairs;
      mpoly = (sum (\<lambda> i. let c = coeff p i in
            MPoly_Type.monom (Poly_Mapping.single 0 i) 1 * \<comment> \<open>$x_0 ^ i * ...$\<close>
             (case find (\<lambda> (j,d,f). d = c) triples of 
             None \<Rightarrow> Const (to_int c)
           | Some (j,pair) \<Rightarrow> Var (Suc j)))
             {..n})
     in (mpoly, triples))" 

text \<open>And then eliminate all auxiliary variables\<close>

definition representative_poly :: "'a :: {is_rat,field_char_0,field_gcd} poly \<Rightarrow> int poly" where
  "representative_poly p = (case initial_root_problem p of
     (mp, triples) \<Rightarrow> 
     let is = map fst triples;
         qs = (\<lambda> j. snd (snd (triples ! j)))
       in eliminate_aux_vars mp qs is)"


subsection \<open>Soundness Proof for Complex Algebraic Polynomials\<close>

lemma get_representative_complex: fixes p :: "complex poly"
  assumes p: "p \<noteq> 0" 
  and algebraic: "Ball (set (coeffs p)) algebraic"
  and res: "initial_root_problem p = (mp, triples)" 
  and "is": "is = map fst triples" 
  and qs: "\<And> j. j < length is \<Longrightarrow> qs j = snd (snd (triples ! j))" 
  and root: "poly p x = 0" 
shows "eliminate_aux_vars mp qs is represents x" 
proof -
  define rcs where "rcs = remdups (filter (\<lambda>c. c \<notin> \<int>) (coeffs p))" 
  define spairs where "spairs = sort_key (\<lambda>(c, f). degree f) (map (\<lambda>c. (c, min_int_poly c)) rcs)" 
  let ?find = "\<lambda> i. find (\<lambda>(j, d, f). d = coeff p i) triples" 
  define trans where "trans i = (case ?find i of None \<Rightarrow> Const (to_int (coeff p i)) 
     | Some (j, pair) \<Rightarrow> Var (Suc j))" for i 
  note res = res[unfolded initial_root_problem_def Let_def, folded rcs_def, folded spairs_def]
  have triples: "triples = zip [0..<length spairs] spairs" using res by auto
  note res = res[folded triples, folded trans_def]
  have mp: "mp = (\<Sum>i\<le>degree p. MPoly_Type.monom (Poly_Mapping.single 0 i) 1 * trans i)" using res by auto
  have dist_rcs: "distinct rcs" unfolding rcs_def by auto
  hence "distinct (map fst (map (\<lambda>c. (c, min_int_poly c)) rcs))" by (simp add: o_def)
  hence dist_spairs: "distinct (map fst spairs)" unfolding spairs_def 
    by (metis (no_types, lifting) distinct_map distinct_sort set_sort)
  {
    fix c
    assume "c \<in> set rcs" 
    hence "c \<in> set (coeffs p)" unfolding rcs_def by auto
    with algebraic have "algebraic c" by auto
  } note rcs_alg = this
  {
    fix c
    assume c: "c \<in> range (coeff p)" "c \<notin> \<int>" 
    hence "c \<in> set (coeffs p)" unfolding range_coeff by auto
    with c have crcs: "c \<in> set rcs" unfolding rcs_def by auto
    from rcs_alg[OF crcs] have "algebraic c" .
    from min_int_poly_represents[OF this]
    have "min_int_poly c represents c" .
    hence "\<exists> f. (c,f) \<in> set spairs \<and> f represents c" using crcs unfolding spairs_def by auto
  }
  have dist_is: "distinct is" unfolding "is" triples by simp
  note eliminate = eliminate_aux_vars[OF dist_is]
  let ?mp = "map_mpoly of_int mp :: complex mpoly" 
  have vars_mp: "vars mp \<subseteq> insert 0 (Suc ` set is)" 
    unfolding mp
    apply (rule order.trans[OF vars_setsum], force)
    apply (rule UN_least, rule order.trans[OF vars_mult], rule Un_least)
     apply (intro order.trans[OF vars_monom_single], force)
    subgoal for i 
    proof -
      show ?thesis 
      proof (cases "?find i")
        case None 
        show ?thesis unfolding trans_def None by auto
      next
        case (Some j_pair)
        then obtain j c f where find: "?find i = Some (j,c,f)" by (cases j_pair, auto)
        from find_Some_D[OF find] have "Suc j \<in> Suc ` (fst ` set triples)"  by force
        thus ?thesis unfolding trans_def find by (simp add: vars_Var "is")
      qed
    qed
    done
  hence varsMp: "vars ?mp \<subseteq> insert 0 (Suc ` set is)" using vars_map_mpoly_subset by auto
  note eliminate = eliminate[OF this]
  let ?f = "\<lambda> j. snd (snd (triples ! j))" 
  let ?c = "\<lambda> j. fst (snd (triples ! j))" 
  {
    fix j
    assume "j \<in> set is" 
    hence "(?c j, ?f j) \<in> set spairs" unfolding "is" triples by simp
    hence "?f j represents ?c j" "?f j = min_int_poly (?c j)" unfolding spairs_def 
      by (auto intro: min_int_poly_represents[OF rcs_alg])
  } note is_repr = this
  let ?qs = "(of_int_poly o qs) :: nat \<Rightarrow> complex poly" 
  {
    fix j
    assume "j \<in> set is" 
    hence "j < length is" unfolding "is" triples by simp
  } note j_len = this
  have qs_0: "0 \<notin> qs ` set is" 
  proof
    assume "0 \<in> qs ` set is" 
    then obtain j where j: "j \<in> set is" and 0: "qs j = 0" by auto
    from is_repr[OF j] have "?f j \<noteq> 0" by auto
    with 0 show False unfolding qs[OF j_len[OF j]] by auto
  qed
  hence qs0: "0 \<notin> ?qs ` set is" by auto
  note eliminate = eliminate[OF _ this] 
  define roots where "roots p = (SOME xs. set xs = {x . poly p x = 0})" for p :: "complex poly" 
  {
    fix p :: "complex poly" 
    assume "p \<noteq> 0" 
    from someI_ex[OF finite_list[OF poly_roots_finite[OF this]], folded roots_def]
    have "set (roots p) = {x. poly p x = 0}" .
  } note roots = this
  define qs_roots where "qs_roots = concat_lists (map (\<lambda> i. roots (?qs i)) [0 ..< length triples])" 
  define evals where "evals = concat (map (\<lambda> part. let 
    q = partial_insertion (\<lambda> i. part ! (i - 1)) 0 ?mp;
    new_roots = roots q
    in map (\<lambda> r. r # part) new_roots) qs_roots)"  
  define conv where "conv roots i = (if i \<le> length triples then roots ! i else 0 :: complex)" for roots i
  define alphas where "alphas = map conv evals" 
  {
    fix n
    assume n: "n \<in> {..degree p}"
    let ?cn = "coeff p n" 
    from n have mem: "?cn \<in> set (coeffs p)" using p unfolding Polynomial.coeffs_def by force
    {
      assume "?cn \<notin> \<int>"
      with mem have "?cn \<in> set rcs" unfolding rcs_def by auto
      hence "(?cn, min_int_poly ?cn) \<in> set spairs" unfolding spairs_def by auto
      hence "\<exists> i. (i, ?cn, min_int_poly ?cn) \<in> set triples" unfolding triples set_zip set_conv_nth 
        by force
      hence "?find n \<noteq> None" unfolding find_None_iff by auto
    }
  } note non_int_find = this
  have fin: "finite {\<alpha>. mpoly_polys_zero_solution ?mp ?qs (set is) \<alpha>}" 
  proof (rule finite_subset[OF _ finite_set[of alphas]], standard, clarify)
    fix \<alpha>
    assume sol: "mpoly_polys_zero_solution ?mp ?qs (set is) \<alpha>" 
    define part where "part = map (\<lambda> i. \<alpha> (Suc i)) [0 ..< length triples]" 
    {
      fix i
      assume "i > length triples" 
      hence "i \<notin> insert 0 (Suc ` set is)" unfolding triples "is" by auto
      hence "\<alpha> i = 0" using sol[unfolded mpoly_polys_zero_solution_def] by auto
    } note alpha0 = this
    {
      fix i
      assume "i < length triples" 
      hence i: "i \<in> set is" unfolding triples "is" by auto
      from qs0 i have 0: "?qs i \<noteq> 0" by auto
      from i sol[unfolded mpoly_polys_zero_solution_def mpoly_polys_solution_def] 
      have "poly (?qs i) (\<alpha> (Suc i)) = 0" by auto
      hence "\<alpha> (Suc i) \<in> set (roots (?qs i))" "poly (?qs i) (\<alpha> (Suc i)) = 0" using roots[OF 0] by auto
    } note roots2 = this
    hence part: "part \<in> set qs_roots" 
      unfolding part_def qs_roots_def concat_lists_listset listset by auto
    let ?gamma = "(\<lambda>i. part ! (i - 1))" 
    let ?f = "partial_insertion ?gamma 0 ?mp" 
    have "\<alpha> 0 \<in> set (roots ?f)" 
    proof -
      from sol[unfolded mpoly_polys_zero_solution_def mpoly_polys_solution_def]
      have "0 = insertion \<alpha> ?mp" by simp
      also have "\<dots> = insertion (\<lambda> i. if i \<le> length triples then \<alpha> i else part ! (i - 1)) ?mp" 
        (is "_ = insertion ?beta _")
      proof (rule insertion_irrelevant_vars)
        fix i
        assume "i \<in> vars ?mp" 
        from set_mp[OF varsMp this] have "i \<le> length triples" unfolding triples "is" by auto
        thus "\<alpha> i = ?beta i" by auto
      qed
      also have "\<dots> = poly (partial_insertion (?beta(0 := part ! 0)) 0 ?mp) (?beta 0)"
        by (subst insertion_partial_insertion, auto)
      also have "?beta(0 := part ! 0) = ?gamma" unfolding part_def 
        by (intro ext, auto)
      finally have root: "poly ?f (\<alpha> 0) = 0" by auto
      have "?f \<noteq> 0" 
      proof
        interpret mp: inj_comm_ring_hom "map_mpoly complex_of_int" 
          by (rule of_int_hom.inj_comm_ring_hom_mpoly_map)
        assume "?f = 0" 
        hence "0 = coeff ?f (degree p)" by simp
        also have "\<dots> = insertion ?gamma (coeff (mpoly_to_mpoly_poly 0 ?mp) (degree p))" 
          unfolding insertion_coeff_mpoly_to_mpoly_poly[symmetric] ..
        also have "coeff (mpoly_to_mpoly_poly 0 ?mp) (degree p) = map_mpoly of_int (coeff (mpoly_to_mpoly_poly 0 mp) (degree p))" 
          unfolding of_int_hom.mpoly_to_mpoly_poly_map_mpoly_hom 
          by (subst coeff_map_poly, auto)
        also have "coeff (mpoly_to_mpoly_poly 0 mp) (degree p) = 
          (\<Sum>x. MPoly_Type.monom (remove_key 0 x) (MPoly_Type.coeff mp x) when lookup x 0 = degree p)" 
          unfolding mpoly_to_mpoly_poly_def when_def
          by (subst coeff_hom.hom_Sum_any, force, unfold Polynomial.coeff_monom, auto)
        also have "\<dots> = (\<Sum>x. MPoly_Type.monom (remove_key 0 x)
           (\<Sum>xa\<le>degree p. let xx = Poly_Mapping.single 0 xa in
               \<Sum>(a, b). MPoly_Type.coeff (trans xa) b when x = xx + b when
                         a = xx) when
          lookup x 0 = degree p)" unfolding mp coeff_sum More_MPoly_Type.coeff_monom coeff_mpoly_times Let_def
          apply (subst prod_fun_unfold_prod, force, force)
          apply (unfold when_mult, subst when_commute)
          by (auto simp: when_def intro!: Sum_any.cong sum.cong if_cong arg_cong[of _ _ "MPoly_Type.monom _"])
        also have "\<dots> = (\<Sum>x. MPoly_Type.monom (remove_key 0 x)
           (\<Sum>i\<le>degree p. \<Sum>m. MPoly_Type.coeff (trans i) m when x = Poly_Mapping.single 0 i + m) when
          lookup x 0 = degree p)" 
          unfolding Sum_any_when_dependent_prod_left Let_def by simp
        also have "\<dots> = (\<Sum>x. MPoly_Type.monom (remove_key 0 x)
           (\<Sum>i \<in> {degree p}. \<Sum>m. MPoly_Type.coeff (trans i) m when x = Poly_Mapping.single 0 i + m) when
          lookup x 0 = degree p)" 
          apply (intro Sum_any.cong when_cong refl arg_cong[of _ _ "MPoly_Type.monom _"] sum.mono_neutral_right, force+)
          apply (intro ballI Sum_any_zeroI, auto simp: when_def)
          subgoal for i x
          proof (goal_cases)
            case 1
            hence "lookup x 0 > 0" by (auto simp: lookup_add)
            moreover have "0 \<notin> vars (trans i)" unfolding trans_def
              by (auto split: option.splits simp: vars_Var)
            ultimately show ?thesis 
              by (metis set_mp coeff_notin_vars in_keys_iff neq0_conv)
          qed
          done
        also have "\<dots> = (\<Sum>x. MPoly_Type.monom (remove_key 0 x)
            (\<Sum>m. MPoly_Type.coeff (trans (degree p)) m when x = Poly_Mapping.single 0 (degree p) + m) when
          lookup x 0 = degree p)" (is "_ = ?mid")
          by simp
        also have "insertion ?gamma (map_mpoly of_int \<dots>) \<noteq> 0" 
        proof (cases "?find (degree p)")
          case None
          from non_int_find[of "degree p"] None 
          have lcZ: "lead_coeff p \<in> \<int>" by auto
          have "?mid =  (\<Sum>x. MPoly_Type.monom (remove_key 0 x)
           (\<Sum>m. (to_int (lead_coeff p) when
                 x = Poly_Mapping.single 0 (degree p) + m when m = 0)) when
              lookup x 0 = degree p)" 
            using None unfolding trans_def None option.simps mpoly_coeff_Const when_def
            by (intro Sum_any.cong if_cong refl, intro arg_cong[of _ _ "MPoly_Type.monom _"] Sum_any.cong, auto)
          also have "\<dots> = (\<Sum>x. MPoly_Type.monom (remove_key 0 x)
           (to_int (lead_coeff p) when x = Poly_Mapping.single 0 (degree p)) when
               lookup x 0 = degree p when x = Poly_Mapping.single 0 (degree p))" 
            unfolding Sum_any_when_equal[of _ 0]
            by (intro Sum_any.cong, auto simp: when_def)
          also have "\<dots> = MPoly_Type.monom (remove_key 0 (Poly_Mapping.single 0 (degree p)))
           (to_int (lead_coeff p)) " 
            unfolding Sum_any_when_equal by simp
          also have "\<dots> = Const (to_int (lead_coeff p))" by (simp add: mpoly_monom_0_eq_Const)
          also have "map_mpoly of_int \<dots> = Const (lead_coeff p)" 
            unfolding of_int_hom.map_mpoly_hom_Const of_int_to_int[OF lcZ] by simp
          also have "insertion ?gamma \<dots> = lead_coeff p" by simp
          also have "\<dots> \<noteq> 0" using p by auto
          finally show ?thesis .
        next
          case Some
          from find_Some_D[OF this] Some obtain j f where mem: "(j,lead_coeff p,f) \<in> set triples" and
            Some: "?find (degree p) = Some (j, lead_coeff p, f)" by auto
          from mem have j: "j < length triples" unfolding triples set_zip by auto
          have "?mid = (\<Sum>x. if lookup x 0 = degree p
              then MPoly_Type.monom (remove_key 0 x)
                (\<Sum>m. 1 when m = Poly_Mapping.single (Suc j) 1 when x = Poly_Mapping.single 0 (degree p) + m)
            else 0)" 
            unfolding trans_def Some option.simps split when_def coeff_Var by auto
          also have "\<dots> = (\<Sum>x. if lookup x 0 = degree p
          then MPoly_Type.monom (remove_key 0 x) 1
                when x = Poly_Mapping.single 0 (degree p) + Poly_Mapping.single (Suc j) 1
              else 0 when x = Poly_Mapping.single 0 (degree p) + Poly_Mapping.single (Suc j) 1)" 
            apply (subst when_commute)
            apply (unfold Sum_any_when_equal)
            by (rule Sum_any.cong, auto simp: when_def)
          also have "\<dots> = (\<Sum>x. (MPoly_Type.monom (remove_key 0 x) 1 when lookup x 0 = degree p)
            when x = Poly_Mapping.single 0 (degree p) + Poly_Mapping.single (Suc j) 1)" 
            by (rule Sum_any.cong, auto simp: when_def)
          also have "\<dots> = MPoly_Type.monom (Poly_Mapping.single (Suc j) 1) 1"  
            unfolding Sum_any_when_equal unfolding when_def 
            by (simp add: lookup_add remove_key_add[symmetric]
              remove_key_single' lookup_single)
          also have "\<dots> = Var (Suc j)"
            by (intro mpoly_eqI, simp add: coeff_Var coeff_monom)
          also have "map_mpoly complex_of_int \<dots> = Var (Suc j)"
            by (simp add: map_mpoly_Var)
          also have "insertion ?gamma \<dots> = part ! j" by simp
          also have "\<dots> = \<alpha> (Suc j)" unfolding part_def using j by auto
          also have "\<dots> \<noteq> 0" 
          proof
            assume "\<alpha> (Suc j) = 0" 
            with roots2(2)[OF j] have root0: "poly (?qs j) 0 = 0" by auto
            from j "is" have ji: "j < length is" by auto
            hence jis: "j \<in> set is" unfolding "is" triples set_zip by auto
            from mem have tj: "triples ! j = (j, lead_coeff p, f)" unfolding triples set_zip by auto
            from root0[unfolded qs[OF ji] o_def tj] 
            have rootf: "poly f 0 = 0" by auto
            from is_repr[OF jis, unfolded tj] have rootlc: "ipoly f (lead_coeff p) = 0" 
              and f: "f = min_int_poly (lead_coeff p)" by auto
            from f have irr: "irreducible f" by auto
            from rootf have "[:0,1:] dvd f" using dvd_iff_poly_eq_0 by fastforce
            from this[unfolded dvd_def] obtain g where f: "f = [:0, 1:] * g" by auto
            from irreducibleD[OF irr f] have "is_unit g"
              by (metis is_unit_poly_iff one_neq_zero one_pCons pCons_eq_iff) 
            then obtain c where g: "g = [:c:]" and c: "c dvd 1" unfolding is_unit_poly_iff by auto
            from rootlc[unfolded f g] c have "lead_coeff p = 0" by auto
            with p show False by auto
          qed
          finally show ?thesis .
        qed
        finally show False by auto
      qed
      from roots[OF this] root show ?thesis by auto
    qed
    hence "\<alpha> 0 # part \<in> set evals" 
      unfolding evals_def set_concat Let_def set_map 
      by (auto intro!: bexI[OF _ part])
    hence "map \<alpha> [0 ..< Suc (length triples)] \<in> set evals" unfolding part_def
      by (metis Utility.map_upt_Suc)
    hence "conv (map \<alpha> [0 ..< Suc (length triples)]) \<in> set alphas" unfolding alphas_def by auto
    also have "conv (map \<alpha> [0 ..< Suc (length triples)]) = \<alpha>" 
    proof
      fix i
      show "conv (map \<alpha> [0..<Suc (length triples)]) i = \<alpha> i" 
        unfolding conv_def using alpha0
        by (cases "i < length triples"; cases "i = length triples"; auto simp: nth_append)
    qed
    finally show "\<alpha> \<in> set alphas" .
  qed
  note eliminate = eliminate[OF this]
  define \<alpha> where "\<alpha> x j = (if j = 0 then x else ?c (j - 1))" for x j
  have \<alpha>: "\<alpha> x (Suc j) = ?c j" "\<alpha> x 0 = x" for j x unfolding \<alpha>_def by auto
  interpret mp: inj_comm_ring_hom "map_mpoly complex_of_int" by (rule of_int_hom.inj_comm_ring_hom_mpoly_map)
  have ins: "insertion (\<alpha> x) ?mp = poly p x" for x
    unfolding poly_altdef mp mp.hom_sum insertion_sum insertion_mult mp.hom_mult
  proof (rule sum.cong[OF refl], subst mult.commute, rule arg_cong2[of _ _ _ _ "(*)"])
    fix n
    assume n: "n \<in> {..degree p}"
    let ?cn = "coeff p n" 
    from n have mem: "?cn \<in> set (coeffs p)" using p unfolding Polynomial.coeffs_def by force
    have "insertion (\<alpha> x) (map_mpoly complex_of_int (MPoly_Type.monom (Poly_Mapping.single 0 n) 1)) = (\<Prod>a. \<alpha> x a ^ (n when a = 0))" 
      unfolding of_int_hom.map_mpoly_hom_monom by (simp add: lookup_single)
    also have "\<dots> = (\<Prod>a. if a = 0 then \<alpha> x a ^ n else 1)" 
      by (rule Prod_any.cong, auto simp: when_def)
    also have "\<dots> = \<alpha> x 0 ^ n" by simp
    also have "\<dots> = x ^ n" unfolding \<alpha> ..
    finally show "insertion (\<alpha> x) (map_mpoly complex_of_int (MPoly_Type.monom (Poly_Mapping.single 0 n) 1)) = x ^ n" .
    show "insertion (\<alpha> x) (map_mpoly complex_of_int (trans n)) = ?cn" 
    proof (cases "?find n")
      case None
      with non_int_find[OF n] have ints: "?cn \<in> \<int>" by auto
      from None show ?thesis unfolding trans_def using ints 
        by (simp add: of_int_hom.map_mpoly_hom_Const of_int_to_int)
    next
      case (Some triple)
      from find_Some_D[OF this] this obtain j f 
        where mem: "(j,?cn,f) \<in> set triples" and Some: "?find n = Some (j,?cn,f)" 
        by (cases triple, auto)
      from mem have "triples ! j = (j,?cn,f)" unfolding triples set_zip by auto
      thus ?thesis unfolding trans_def Some by (simp add: map_mpoly_Var \<alpha>_def)
    qed
  qed
  from root have  "insertion (\<alpha> x) ?mp = 0" unfolding ins by auto
  hence "mpoly_polys_solution ?mp ?qs (set is) (\<alpha> x)" 
    unfolding mpoly_polys_solution_def
  proof (standard, intro ballI)
    fix j
    assume j: "j \<in> set is" 
    from is_repr[OF this]
    show "poly (?qs j) (\<alpha> x (Suc j)) = 0" unfolding \<alpha> qs[OF j_len[OF j]] o_def by auto
  qed
  note eliminate = eliminate[OF this, unfolded \<alpha> eliminate_aux_vars_of_int_poly]
  thus "eliminate_aux_vars mp qs is represents x" by auto
qed  

lemma representative_poly_complex: fixes x :: complex
  assumes p: "p \<noteq> 0" 
    and algebraic: "Ball (set (coeffs p)) algebraic"
    and root: "poly p x = 0" 
  shows "representative_poly p represents x"
proof -
  obtain mp triples where init: "initial_root_problem p = (mp, triples)" by force
  from get_representative_complex[OF p algebraic init refl _ root]
  show ?thesis unfolding representative_poly_def init Let_def by auto
qed 

subsection \<open>Soundness Proof for Real Algebraic Polynomials\<close>

text \<open>We basically use the result for complex algebraic polynomials which 
  are a superset of real algebraic polynomials.\<close>


lemma initial_root_problem_complex_of_real_poly: 
  "initial_root_problem (map_poly complex_of_real p) = 
   map_prod id (map (map_prod id (map_prod complex_of_real id))) (initial_root_problem p)"
proof -
  let ?c = "of_real :: real \<Rightarrow> complex" 
  let ?cp = "map_poly ?c" 
  let ?p = "?cp p :: complex poly" 
  define cn where "cn = degree ?p" 
  define n where "n = degree p" 
  have n: "cn = n" unfolding n_def cn_def by simp
  note def = initial_root_problem_def[of ?p]
  note def = def[folded cn_def, unfolded n]
  define ccs where "ccs = coeffs ?p"
  define cs where "cs = coeffs p" 
  have cs: "ccs = map ?c cs" 
    unfolding ccs_def cs_def by auto
  note def = def[folded ccs_def]
  define crcs where "crcs = remdups (filter (\<lambda>c. c \<notin> \<int>) ccs)" 
  define rcs where "rcs = remdups (filter (\<lambda>c. c \<notin> \<int>) cs)" 
  have rcs: "crcs = map ?c rcs" 
    unfolding crcs_def rcs_def cs by (induct cs, auto)
  define cpairs where "cpairs = map (\<lambda>c. (c, min_int_poly c)) crcs" 
  define pairs where "pairs = map (\<lambda>c. (c, min_int_poly c)) rcs" 
  have pairs: "cpairs = map (map_prod ?c id) pairs" 
    unfolding pairs_def cpairs_def rcs by auto
  define cspairs where "cspairs = sort_key (\<lambda>(c, y). degree y) cpairs" 
  define spairs where "spairs = sort_key (\<lambda>(c, y). degree y) pairs" 
  have spairs: "cspairs = map (map_prod ?c id) spairs" 
    unfolding spairs_def cspairs_def pairs 
    by (rule sym, rule map_sort_key, auto)
  define ctriples where "ctriples = zip [0..<length cspairs] cspairs" 
  define triples where "triples = zip [0..<length spairs] spairs" 
  have triples: "ctriples = map (map_prod id (map_prod ?c id)) triples" 
    unfolding ctriples_def triples_def spairs by (rule nth_equalityI, auto)
  note def = def[unfolded Let_def, folded crcs_def, folded cpairs_def, folded cspairs_def, folded ctriples_def,
      unfolded of_real_hom.coeff_map_poly_hom]
  note def2 = initial_root_problem_def[of p, unfolded Let_def, folded n_def cs_def, folded rcs_def, folded pairs_def,
      folded spairs_def, folded triples_def]
  show "initial_root_problem ?p = map_prod id (map (map_prod id (map_prod ?c id))) (initial_root_problem p)" 
    unfolding def def2 triples to_int_complex_of_real
    by (simp, intro sum.cong refl arg_cong[of _ _ "\<lambda> x. _ * x"], induct triples, auto)
qed


lemma representative_poly_real: fixes x :: real 
  assumes p: "p \<noteq> 0" 
  and algebraic: "Ball (set (coeffs p)) algebraic"
  and root: "poly p x = 0" 
shows "representative_poly p represents x" 
proof -
  obtain mp triples where init: "initial_root_problem p = (mp, triples)" by force
  define "is" where "is = map fst triples" 
  define qs where "qs = (\<lambda> j. snd (snd (triples ! j)))" 
  let ?c = "of_real :: real \<Rightarrow> complex" 
  let ?cp = "map_poly ?c" 
  let ?ct = "map (map_prod id (map_prod ?c id))" 
  let ?p = "?cp p :: complex poly" 
  have p: "?p \<noteq> 0" using p by auto
  have "initial_root_problem ?p = map_prod id ?ct (initial_root_problem p)" 
    by (rule initial_root_problem_complex_of_real_poly)
  from this[unfolded init] 
  have res: "initial_root_problem ?p = (mp, ?ct triples)" 
    by auto
  from root have "0 = ?c (poly p x)" by simp
  also have "\<dots> = poly ?p (?c x)" by simp
  finally have root: "poly ?p (?c x) = 0" by simp
  have qs: "j < length is \<Longrightarrow> qs j = snd (snd (?ct triples ! j))" for j
    unfolding is_def qs_def by (auto simp: set_conv_nth)
  have "is": "is = map fst (?ct triples)" unfolding is_def by auto 
  {
    fix cc
    assume "cc \<in> set (coeffs ?p)" 
    then obtain c where "c \<in> set (coeffs p)" and cc: "cc = ?c c" by auto
    from algebraic this(1) have "algebraic cc" 
      unfolding cc algebraic_complex_iff by auto
  }
  hence algebraic: "Ball (set (coeffs ?p)) algebraic" .. 
  from get_representative_complex[OF p this res "is" qs root]
  have "eliminate_aux_vars mp qs is represents ?c x" .
  hence "eliminate_aux_vars mp qs is represents x" by simp
  thus ?thesis unfolding representative_poly_def res init split Let_def qs_def is_def .
qed

subsection \<open>Algebraic Closedness of Complex Algebraic Numbers\<close>

(* TODO: could be generalised to arbitrary algebraically closed fields? *)
lemma complex_algebraic_numbers_are_algebraically_closed:
  assumes nc: "\<not> constant (poly p)"
    and alg: "Ball (set (coeffs p)) algebraic"
  shows "\<exists> z :: complex. algebraic z \<and> poly p z = 0"
proof -
  from fundamental_theorem_of_algebra[OF nc] obtain z where
    root: "poly p z = 0" by auto
  from algebraic_representsI[OF representative_poly_complex[OF _ alg root]] nc root
  have "algebraic z \<and> poly p z = 0" 
    using constant_degree degree_0 by blast
  thus ?thesis ..
qed


end