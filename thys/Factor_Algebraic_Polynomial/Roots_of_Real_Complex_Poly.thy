section \<open>Roots of Real and Complex Algebraic Polynomials\<close>

text \<open>We are now able to actually compute all roots of polynomials
  with real and complex algebraic coefficients. The main addition to
  calculating the representative polynomial for a superset of all roots
  is to find the genuine roots. For this we utilize the approximation algorithm
  via interval arithmetic.\<close>

theory Roots_of_Real_Complex_Poly
  imports
    Roots_of_Algebraic_Poly_Impl
    Roots_via_IA
    MPoly_Container
begin

hide_const (open) Module.smult

typedef (overloaded) 'a rf_poly = "{ p :: 'a :: idom poly. rsquarefree p}" 
  by (intro exI[of _ 1], auto simp: rsquarefree_def)

setup_lifting type_definition_rf_poly

context 
begin 
lifting_forget poly.lifting

lift_definition poly_rf :: "'a :: idom rf_poly \<Rightarrow> 'a poly" is "\<lambda> x. x" .

definition roots_of_poly_dummy :: "'a::{comm_ring_1,ring_no_zero_divisors} poly \<Rightarrow> _" 
  where "roots_of_poly_dummy p = (SOME xs. set xs = {r. poly p r = 0} \<and> distinct xs)"

lemma roots_of_poly_dummy_code[code]: 
  "roots_of_poly_dummy p = Code.abort (STR ''roots-of-poly-dummy'') (\<lambda> x. roots_of_poly_dummy p)" 
  by simp

lemma roots_of_poly_dummy: assumes p: "p \<noteq> 0" 
  shows "set (roots_of_poly_dummy p) = {x. poly p x = 0}" "distinct (roots_of_poly_dummy p)" 
proof -
  from someI_ex[OF finite_distinct_list[OF poly_roots_finite[OF p]], folded roots_of_poly_dummy_def]
  show "set (roots_of_poly_dummy p) = {x. poly p x = 0}" "distinct (roots_of_poly_dummy p)"  by auto
qed

lift_definition roots_of_complex_rf_poly_part1 :: "complex rf_poly \<Rightarrow> complex genuine_roots_aux" is
  "\<lambda> p. if Ball (set (Polynomial.coeffs p)) algebraic then 
        let q = representative_poly p;
         zeros = complex_roots_of_int_poly q
         in (p,zeros,Polynomial.degree p, filter_fun_complex p)
        else (p,roots_of_poly_dummy p,Polynomial.degree p, filter_fun_complex p)"
  subgoal for p
  proof -
    assume rp: "rsquarefree p" 
    hence card: "card {x. poly p x = 0} = Polynomial.degree p"
      using rsquarefree_card_degree rsquarefree_def by blast
    from rp have p: "p \<noteq> 0" unfolding rsquarefree_def by auto
    have ff: "filter_fun p (filter_fun_complex p)" by (rule filter_fun_complex) 
    show ?thesis
    proof (cases "Ball (set (Polynomial.coeffs p)) algebraic")
      case False 
      with roots_of_poly_dummy[OF p] ff
      show ?thesis using rp card by auto
    next
      case True
      from rp card representative_poly_complex[of p] 
        complex_roots_of_int_poly[of "representative_poly p"] ff
      show ?thesis unfolding Let_def rsquarefree_def using True by auto
    qed
  qed
  done


lift_definition roots_of_real_rf_poly_part1 :: "real rf_poly \<Rightarrow> real genuine_roots_aux" is
  "\<lambda> p. let n = count_roots p in 
        if Ball (set (Polynomial.coeffs p)) algebraic then 
        let q = representative_poly p;
         zeros = real_roots_of_int_poly q
         in (p,zeros,n, filter_fun_real p)
        else (p,roots_of_poly_dummy p,n, filter_fun_real p)"
  subgoal for p
  proof -
    assume rp: "rsquarefree p" 
    from rp have p: "p \<noteq> 0" unfolding rsquarefree_def by auto
    have ff: "filter_fun p (filter_fun_real p)" by (rule filter_fun_real) 
    show ?thesis
    proof (cases "Ball (set (Polynomial.coeffs p)) algebraic")
      case False 
      with roots_of_poly_dummy[OF p] ff
      show ?thesis using rp by (auto simp: Let_def count_roots_correct)
    next
      case True
      from rp representative_poly_real[of p] 
        real_roots_of_int_poly[of "representative_poly p"] ff
      show ?thesis unfolding Let_def rsquarefree_def using True 
        by (auto simp: count_roots_correct)
    qed
  qed
  done

definition roots_of_complex_rf_poly :: "complex rf_poly \<Rightarrow> complex list" where
  "roots_of_complex_rf_poly p = genuine_roots_impl (roots_of_complex_rf_poly_part1 p)" 

lemma roots_of_complex_rf_poly: "set (roots_of_complex_rf_poly p) = {x. poly (poly_rf p) x = 0}" 
  "distinct (roots_of_complex_rf_poly p)" 
  unfolding roots_of_complex_rf_poly_def genuine_roots_impl
  by (transfer, auto simp: genuine_roots_impl)

definition roots_of_real_rf_poly :: "real rf_poly \<Rightarrow> real list" where
  "roots_of_real_rf_poly p = genuine_roots_impl (roots_of_real_rf_poly_part1 p)" 

lemma roots_of_real_rf_poly: "set (roots_of_real_rf_poly p) = {x. poly (poly_rf p) x = 0}" 
  "distinct (roots_of_real_rf_poly p)" 
  unfolding roots_of_real_rf_poly_def genuine_roots_impl
  by (transfer, auto simp: genuine_roots_impl Let_def)

typedef (overloaded) 'a rf_polys = "{ (a :: 'a :: idom, ps :: ('a poly \<times> nat) list). Ball (fst ` set ps) rsquarefree}" 
  by (intro exI[of _ "(_,Nil)"], auto)

setup_lifting type_definition_rf_polys

lift_definition yun_polys :: "'a :: {euclidean_ring_gcd,field_char_0,semiring_gcd_mult_normalize} poly \<Rightarrow> 'a rf_polys"
  is "\<lambda> p. yun_factorization gcd p" 
  subgoal for p
    apply auto
    apply (intro square_free_rsquarefree)
    apply (insert yun_factorization[of p, OF refl])
    by (cases "yun_factorization gcd p", auto dest: square_free_factorizationD)
  done

context
  notes [[typedef_overloaded]]
begin
lift_definition (code_dt) yun_rf :: "'a :: idom rf_polys \<Rightarrow> 'a \<times> ('a rf_poly \<times> nat) list" is "\<lambda> x. x" 
  by (auto simp: list_all_iff, force)
end
end
definition polys_rf :: "'a :: idom rf_polys \<Rightarrow> 'a rf_poly list" where
  "polys_rf = map fst o snd o yun_rf" 

lemma yun_polys: assumes "p \<noteq> 0" 
  shows "poly p x = 0 \<longleftrightarrow> (\<exists> q \<in> set (polys_rf (yun_polys p)). poly (poly_rf q) x = 0)" 
  using assms unfolding polys_rf_def o_def
  apply transfer
  subgoal for p x
  proof -
    assume p: "p \<noteq> 0"
    obtain c ps where yun: "yun_factorization gcd p = (c,ps)" by force
    from yun_factorization[OF this] have sff: "square_free_factorization p (c, ps)" by auto
    from square_free_factorizationD'(1)[OF sff] p have c0: "c \<noteq> 0" by auto
    show ?thesis unfolding yun 
      unfolding square_free_factorizationD'(1)[OF sff] poly_smult poly_prod_list snd_conv
      mult_eq_0_iff prod_list_zero_iff
      using c0 by force
  qed
  done


definition roots_of_complex_rf_polys :: "complex rf_polys \<Rightarrow> complex list" where
  "roots_of_complex_rf_polys ps = concat (map roots_of_complex_rf_poly (polys_rf ps))" 

lemma roots_of_complex_rf_polys: 
  "set (roots_of_complex_rf_polys ps) = {x. \<exists> p \<in> set (polys_rf ps). poly (poly_rf p) x = 0 }" 
  unfolding roots_of_complex_rf_polys_def set_concat set_map image_comp o_def
    roots_of_complex_rf_poly by auto

definition roots_of_real_rf_polys :: "real rf_polys \<Rightarrow> real list" where
  "roots_of_real_rf_polys ps = concat (map roots_of_real_rf_poly (polys_rf ps))" 

lemma roots_of_real_rf_polys: 
  "set (roots_of_real_rf_polys ps) = {x. \<exists> p \<in> set (polys_rf ps). poly (poly_rf p) x = 0 }" 
  unfolding roots_of_real_rf_polys_def set_concat set_map image_comp o_def
    roots_of_real_rf_poly by auto

definition roots_of_complex_poly :: "complex poly \<Rightarrow> complex list" where
  "roots_of_complex_poly p = (if p = 0 then [] else roots_of_complex_rf_polys (yun_polys p))" 

lemma roots_of_complex_poly: assumes p: "p \<noteq> 0" 
  shows "set (roots_of_complex_poly p) = {x. poly p x = 0}"
  using p unfolding roots_of_complex_poly_def 
  by (simp add: roots_of_complex_rf_polys yun_polys[OF p])

definition roots_of_real_poly :: "real poly \<Rightarrow> real list" where
  "roots_of_real_poly p = (if p = 0 then [] else roots_of_real_rf_polys (yun_polys p))" 

lemma roots_of_real_poly: assumes p: "p \<noteq> 0" 
  shows "set (roots_of_real_poly p) = {x. poly p x = 0}"
  using p unfolding roots_of_real_poly_def 
  by (simp add: roots_of_real_rf_polys yun_polys[OF p])

lemma distinct_concat':
  "\<lbrakk> distinct (list_neq xs []);
     \<And> ys. ys \<in> set xs \<Longrightarrow> distinct ys;
     \<And> ys zs. \<lbrakk> ys \<in> set xs ; zs \<in> set xs ; ys \<noteq> zs \<rbrakk> \<Longrightarrow> set ys \<inter> set zs = {}
   \<rbrakk> \<Longrightarrow> distinct (concat xs)"
  by (induct xs, auto split: if_splits)

lemma roots_of_rf_yun_polys_distinct: assumes 
  rt: "\<And> p. set (rop p) = {x. poly (poly_rf p) x = 0}" 
  and dist: "\<And> p. distinct (rop p)" 
shows "distinct (concat (map rop (polys_rf (yun_polys p))))"
  using assms unfolding polys_rf_def
proof (transfer, goal_cases)
  case (1 rop p)
  obtain c fs where yun: "yun_factorization gcd p = (c,fs)" by force
  note sff = yun_factorization(1)[OF yun]
  note sff1 = square_free_factorizationD[OF sff]
  note sff2 = square_free_factorizationD'[OF sff]
  have rs: "(p,i) \<in> set fs \<Longrightarrow> rsquarefree p" for p i 
    by (intro square_free_rsquarefree, insert sff1(2), auto)
  note 1 = 1[OF rs]
  show ?case unfolding yun snd_conv map_map o_def using 1 sff1(3,5)
  proof (induct fs)
    case (Cons pi fs)
    obtain p i where pi: "pi = (p,i)" by force
    hence "(p,i) \<in> set (pi # fs)" by auto
    note p_i = Cons(2-4)[OF this]
    have IH: "distinct (concat (map (\<lambda>x. rop (fst x)) fs))" 
      by (rule Cons(1)[OF Cons(2,3,4)], insert Cons(5), auto)
    {
      fix x
      assume x: "x \<in> set (rop p)" "x \<in> (\<Union>x\<in>set fs. set (rop (fst x)))"
      from x[unfolded p_i] have rtp: "poly p x = 0" by auto
      from x obtain q j where qj: "(q,j) \<in> set fs" and x: "x \<in> set (rop q)" by force
      from Cons(2)[of q j] x qj have rtq: "poly q x = 0" by auto
      from Cons(5)[unfolded pi] qj have "(p,i) \<noteq> (q,j)" by auto
      from p_i(3)[OF _ this] qj have cop: "algebraic_semidom_class.coprime p q" by auto
      from rtp have dvdp: "[:-x,1:] dvd p" using poly_eq_0_iff_dvd by blast
      from rtq have dvdq: "[:-x,1:] dvd q" using poly_eq_0_iff_dvd by blast
      from cop dvdp dvdq have "is_unit [:-x,1:]" by (metis coprime_common_divisor)
      hence False by simp
    }
    thus ?case unfolding pi by (auto simp: p_i(2) IH)
  qed simp
qed

lemma distinct_roots_of_real_poly: "distinct (roots_of_real_poly p)"
  unfolding roots_of_real_poly_def roots_of_real_rf_polys_def
  using roots_of_rf_yun_polys_distinct[of roots_of_real_rf_poly p, OF roots_of_real_rf_poly]
  by auto

lemma distinct_roots_of_complex_poly: "distinct (roots_of_complex_poly p)"
  unfolding roots_of_complex_poly_def roots_of_complex_rf_polys_def
  using roots_of_rf_yun_polys_distinct[of roots_of_complex_rf_poly p, OF roots_of_complex_rf_poly]
  by auto


end