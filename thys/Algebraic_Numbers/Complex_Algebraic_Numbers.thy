(*  
    Author:      René Thiemann 
                 Akihisa Yamada
    License:     BSD
*)
section \<open>Complex Algebraic Numbers\<close>

text \<open>Since currently there is no immediate analog of Sturm's theorem for the complex numbers,
  we implement complex algebraic numbers via their real and imaginary part.
  
  The major algorithm in this theory is a factorization algorithm which factors a rational
  polynomial over the complex numbers. 

  This algorithm is then combined with explicit root algorithms to try to factor arbitrary  
  complex polymials.\<close>

theory Complex_Algebraic_Numbers
imports 
  Real_Roots
  Complex_Roots_Real_Poly
  Compare_Complex
begin

subsection \<open>Complex Roots\<close>

abbreviation complex_of_rat_poly :: "rat poly \<Rightarrow> complex poly" where
  "complex_of_rat_poly \<equiv> map_poly of_rat"

lemma poly_complex_of_rat_poly: "poly (complex_of_rat_poly p) = rpoly p" 
  by (rule rpoly.poly_map_poly_eval_poly)

lemma poly_complex_to_real: "(poly (complex_of_rat_poly p) (complex_of_real x) = 0)
  = (poly (real_of_rat_poly p) x = 0)"
proof -
  have id: "of_rat = complex_of_real o real_of_rat" by auto
  interpret cr: semiring_hom complex_of_real by (unfold_locales, auto)
  show ?thesis unfolding id
    by (subst map_poly_compose[symmetric], force+)
qed

lemma alg_poly_cnj: assumes "alg_poly x p"
  shows "alg_poly (cnj x) p"
proof -
  from assms have p: "p \<noteq> 0" and "rpoly p x = 0" by auto
  hence rt: "poly (complex_of_rat_poly p) x = 0" unfolding poly_complex_of_rat_poly by auto
  have "poly (complex_of_rat_poly p) (cnj x) = 0"
    by (rule complex_conjugate_root[OF _ rt], subst coeffs_map_poly, auto) 
       (metis Reals_of_real complex_of_real_of_rat)
  with p show ?thesis unfolding poly_complex_of_rat_poly by auto
qed

definition poly_1_2i :: "rat poly" where
  "poly_1_2i \<equiv> [: inverse 4, 0, 1:]"

lemma alg_poly_1_2i: "alg_poly (1 / (2 * \<i>)) poly_1_2i"
  unfolding alg_poly_def poly_1_2i_def 
  by (simp add: eval_poly_def)

definition root_poly_Re :: "rat poly \<Rightarrow> rat poly" where
  "root_poly_Re p = poly_mult_rat (1/2) (poly_add p p)"

definition root_poly_Im :: "rat poly \<Rightarrow> rat poly list" where
  "root_poly_Im p = (let fs = factors_of_rat_poly Uncertified_Factorization (poly_add p (poly_uminus p))
    in remdups ((if (\<exists> f \<in> set fs. coeff f 0 = 0) then [[:0,1:]] else [])) @ [ poly_mult poly_1_2i f . 
    f \<leftarrow> fs])"

context inj_field_hom_0
begin
lemma map_poly_pderiv: 
  "map_poly hom (pderiv p) = pderiv (map_poly hom p)"
proof (induct p rule: pderiv.induct)
  case (1 a p)
  show ?case
  proof (cases "p = 0")
    case True
    thus ?thesis by simp
  next
    case False
    hence id: "(p = 0) = False" "(map_poly hom p = 0) = False" by auto
    have id': "map_poly hom (pCons 0 (pderiv p))
      = pCons 0 (map_poly hom (pderiv p))" 
      by (cases "pderiv p = 0", auto)
    show ?thesis 
      unfolding pderiv.simps map_poly_pCons[OF disjI2[OF False]] 1[OF False, symmetric] id id' if_False map_poly_add
      by auto
  qed
qed
  
lemma map_poly_square_free_monic_poly: 
  "map_poly hom (square_free_monic_poly p) = square_free_monic_poly (map_poly hom p)"
  unfolding square_free_monic_poly_def map_poly_div map_poly_gcd map_poly_pderiv ..

lemma map_poly_square_free_poly: 
  "map_poly hom (square_free_poly p) = square_free_poly (map_poly hom p)"
proof (cases "p = 0")
  case True
  thus ?thesis unfolding square_free_poly_def by auto 
next
  case False
  hence id: "(p = 0) = False" "(map_poly hom p = 0) = False" by auto  
  show ?thesis unfolding square_free_poly_def id if_False map_poly_square_free_monic_poly
    map_poly_smult degree_map_poly
    by (subst coeff_map_poly, auto)
qed
end

lemma square_free_poly_0[simp]: "square_free_poly p = 0 \<longleftrightarrow> p = 0"
proof 
  assume "square_free_poly p = 0"
  from arg_cong[OF this, of "\<lambda> p. {x. poly p x = 0}", unfolded square_free_poly] 
  show "p = 0" using poly_all_0_iff_0 by blast
qed (auto simp: square_free_poly_def)

lemma alg_poly_square_free_poly_eq[simp]: "alg_poly x (square_free_poly p) = alg_poly x p"
  unfolding alg_poly_def rpoly.poly_map_poly_eval_poly[symmetric] rpoly.map_poly_square_free_poly 
    square_free_poly by simp

lemma alg_poly_square_free_poly: "alg_poly x p \<Longrightarrow> alg_poly x (square_free_poly p)"
  by simp

lemma alg_poly_root_poly: assumes "rpoly p x = 0" and p: "p \<noteq> 0"
  shows 
    "alg_poly (Re x) (root_poly_Re p)"
    "\<exists> q \<in> set (root_poly_Im p). alg_poly (Im x) q"
proof -
  let ?Rep = "root_poly_Re p"
  let ?Imp = "root_poly_Im p"
  from assms have ap: "alg_poly x p" by auto
  from alg_poly_cnj[OF this] have apc: "alg_poly (cnj x) p" .
  from alg_poly_mult_rat[OF _ alg_poly_add_complex[OF ap apc], of "1/2"]
  have "alg_poly (1 / 2 * (x + cnj x)) ?Rep" unfolding root_poly_Re_def by auto
  also have "1 / 2 * (x + cnj x) = of_real (Re x)"
    by (cases x, auto)
  finally have Rep: "?Rep \<noteq> 0" and rt: "rpoly ?Rep (complex_of_real (Re x)) = 0" unfolding alg_poly_def by auto
  from rt[folded poly_complex_of_rat_poly, unfolded poly_complex_to_real]
  have "rpoly ?Rep (Re x) = 0" unfolding poly_real_of_rat_poly .
  with Rep show "alg_poly (Re x) ?Rep" by auto 
  let ?q = "poly_add p (poly_uminus p)"
  let ?mode = Uncertified_Factorization
  from alg_poly_add_complex[OF ap alg_poly_uminus[OF apc]] 
  have apq: "alg_poly (x - cnj x) ?q" by auto
  from alg_poly_factors_rat_poly[OF this] obtain pi where pi: "pi \<in> set (factors_of_rat_poly ?mode ?q)"
    and appi: "alg_poly (x - cnj x) pi" by auto
  have id: "1 / (2 * \<i>) * (x - cnj x) = of_real (Im x)"
    by (cases x, auto)
  have "\<exists> qi \<in> set ?Imp. (alg_poly (1 / (2 * \<i>) * (x - cnj x)) qi)" 
  proof (cases "x - cnj x = 0")
    case False 
    have "1 / (2 * \<i>) \<noteq> 0" by auto
    from alg_poly_mult_complex[OF alg_poly_1_2i appi this False] pi
    show ?thesis unfolding root_poly_Im_def Let_def by auto
  next
    case True
    hence id2: "Im x = 0" by (cases x, auto)
    from appi[unfolded True alg_poly_def] have "coeff pi 0 = 0" by (cases pi, auto) 
      (metis add.right_neutral mult_zero_left poly_pCons rpoly.eval_poly_poly rpoly.hom_inj rpoly.hom_zero, 
       metis add.right_neutral mult_eq_0_iff poly_pCons rpoly.eval_poly_poly rpoly.hom_inj rpoly.hom_zero)
    with pi have mem: "[:0,1:] \<in> set ?Imp" unfolding root_poly_Im_def Let_def by auto    
    have "alg_poly (complex_of_real (Im x)) [:0,1:]" unfolding id2 alg_poly_def by (simp add: eval_poly_def)    
    with mem show ?thesis unfolding id by auto
  qed
  then obtain qi where qi: "qi \<in> set ?Imp" "qi \<noteq> 0" and rt: "rpoly qi (complex_of_real (Im x)) = 0" 
    unfolding id alg_poly_def by auto
  from rt[folded poly_complex_of_rat_poly, unfolded poly_complex_to_real]
  have "rpoly qi (Im x) = 0" unfolding poly_real_of_rat_poly .
  with qi show "\<exists> qi \<in> set ?Imp. alg_poly (Im x) qi" by auto 
qed

text \<open>Determine complex roots of a polynomial, 
   intended for polynomials of degree 3 or higher,
   for lower degree polynomials use @{const roots1} or @{const croots2}\<close>
definition complex_roots_of_rat_poly3 :: "rat poly \<Rightarrow> complex list" where
  "complex_roots_of_rat_poly3 p \<equiv> let n = degree p in if n = count_roots_rat p 
    then map (\<lambda> r. Complex r 0) (real_roots_of_rat_poly p) 
    else if n = 3 then 
    let x = hd (real_roots_of_rat_poly3 p);
        xx = Complex x 0;
        pp = complex_of_rat_poly p
      in xx # croots2 (pp div [:-xx,1:]) else
    let
        rp = root_poly_Re p;
        ip = root_poly_Im p;
        rxs = real_roots_of_rat_poly rp;
        ixs = (* TODO: is a remdups at this point required to avoid duplicates? test on 1 + 3x + 3x^4 *) 
          remdups (concat (map real_roots_of_rat_poly ip));
        rts = [Complex rx ix. rx <- rxs, ix <- ixs] 
    in filter (\<lambda> c. rpoly p c = 0) rts"

definition complex_roots_of_rat_poly_all :: "rat poly \<Rightarrow> complex list" where
  "complex_roots_of_rat_poly_all p = (let n = degree p in 
    if n \<ge> 3 then complex_roots_of_rat_poly3 p
    else if n = 1 then [roots1 (map_poly of_rat p)] else if n = 2 then croots2 (map_poly of_rat p)
    else [])"

lemma complex_roots_of_rat_poly3: assumes p: "p \<noteq> 0" 
  shows "set (complex_roots_of_rat_poly3 p) = {x. rpoly p x = 0}" (is "?l = ?r")
proof -
  def q \<equiv> "real_of_rat_poly p"
  let ?q = "map_poly complex_of_real q"
  from p have "q \<noteq> 0" unfolding q_def by auto
  hence q: "?q \<noteq> 0" by auto
  interpret cr: inj_ring_hom complex_of_real by (unfold_locales, auto)
  note d = complex_roots_of_rat_poly3_def Let_def
  show ?thesis
  proof (cases "degree p = count_roots_rat p")
    case False note oFalse = this
    show ?thesis
    proof (cases "degree p = 3")
      case False
      have "?l \<subseteq> ?r" unfolding d using False oFalse by auto
      moreover
      {
        fix x :: complex
        let ?rp = "root_poly_Re p"
        let ?ip = "root_poly_Im p"
        let ?x = "Complex (Re x) (Im x)"
        assume rt: "rpoly p x = 0"
        from alg_poly_root_poly[OF this p] obtain qi where 
          "?rp \<noteq> 0" "rpoly ?rp (Re x) = 0" and qi: "qi \<in> set ?ip" and "qi \<noteq> 0" "rpoly qi (Im x) = 0" by auto
        hence mem: "Re x \<in> set (real_roots_of_rat_poly ?rp)" "Im x \<in> set (real_roots_of_rat_poly qi)"
          by (auto simp: real_roots_of_rat_poly)    
        have x: "x = ?x" by (cases x, auto)
        with rt have rt: "rpoly p ?x = 0" by auto
        from False oFalse rt mem qi have "?x \<in> ?l" unfolding d by fastforce
        with x have "x \<in> ?l" by auto
      }
      ultimately show ?thesis by blast
    next
      case True
      let ?rr = "real_roots_of_rat_poly3 p"
      def pp \<equiv> "complex_of_rat_poly p"
      have id: "pp = map_poly of_real q" unfolding q_def pp_def
        by (subst map_poly_compose, auto simp: o_def)
      def y \<equiv> "hd ?rr"
      def z \<equiv> "complex_of_real y"
      def p2 \<equiv> "pp div [:-z,1:]"
      from True have 3: "degree q = 3" unfolding q_def by (simp add: degree_map_poly)
      with odd_degree_imp_real_root[of q] obtain x where rt: "poly q x = 0" by auto
      hence "x \<in> set ?rr" unfolding real_roots_of_rat_poly3[OF p] q_def
        poly_real_of_rat_poly by auto
      hence "y \<in> set ?rr" unfolding y_def by (cases ?rr, auto)
      hence "poly q y = 0" unfolding real_roots_of_rat_poly3[OF p] q_def
        poly_real_of_rat_poly by auto
      hence z: "poly pp z = 0" unfolding z_def id by simp      
      from True have 3: "degree pp = 3" unfolding pp_def
        by (subst degree_map_poly, auto)
      from False True have l: "?l = insert z (set (croots2 p2))"
        unfolding d y_def z_def pp_def p2_def by auto      
      have r: "?r = {x. poly pp x = 0}" unfolding poly_complex_of_rat_poly pp_def ..
      from z have "[:-z,1:] dvd pp" using poly_eq_0_iff_dvd by blast
      hence pp: "pp = [:-z,1:] * p2"
        using dvd_mult_div_cancel p2_def by metis
      from arg_cong[OF this, of degree, unfolded 3] have 2: "degree p2 = 2"
        using degree_mult_eq[of "[:-z,1:]" p2] by fastforce
      from croots2[OF this] 
      have id2: "set (croots2 p2) = {x. poly p2 x = 0}" by auto
      from 2 have "p2 \<noteq> 0" by auto
      thus ?thesis unfolding l id2 r pp by auto
    qed
  next
    case True
    from True have "?l = of_real ` {x. rpoly p x = 0}" unfolding d 
      using real_roots_of_rat_poly[OF p] by auto
    also have "{x. rpoly p x = (0 :: real)} = {x. poly q x = 0}" unfolding q_def poly_real_of_rat_poly ..
    finally have l: "?l = of_real ` {x. poly q x = 0}" .
    have r: "?r = {x. poly ?q x = 0}"
      unfolding poly_complex_of_rat_poly[symmetric] q_def
      by (subst map_poly_compose, auto simp: o_def)
    have "?thesis = (complex_of_real ` {x. poly q x = 0} = {x. poly ?q x = 0})" (is "_ = (?l = ?r)")
      unfolding l r by auto
    also have "?l = ?r"
    proof -
      have "?l \<subseteq> ?r" by auto
      have "card ?r \<le> degree ?q"
        by (rule poly_roots_degree[OF q])
      also have "\<dots> = card {x. poly q x = 0}"
        using True[unfolded count_roots_rat poly_real_of_rat_poly[symmetric] q_def[symmetric]] 
        unfolding q_def by (simp add: degree_map_poly)
      also have "\<dots> = card ?l"
        by (subst card_image, auto simp: inj_on_def)
      finally have "card ?r \<le> card ?l" .
      with `?l \<subseteq> ?r` poly_roots_finite[OF q] show "?l = ?r" by (metis card_seteq)
    qed
    finally show ?thesis by auto  
  qed
qed

lemma complex_roots_of_rat_poly_all: assumes p: "p \<noteq> 0"
  shows "set (complex_roots_of_rat_poly_all p) = {x. rpoly p x = 0}" (is "?l = ?r")
proof -
  note d = complex_roots_of_rat_poly_all_def Let_def
  show ?thesis
  proof (cases "degree p \<ge> 3")
    case True
    with complex_roots_of_rat_poly3[OF p] show ?thesis unfolding d by auto
  next
    case False
    let ?p = "map_poly (of_rat :: rat \<Rightarrow> complex) p"
    have r: "?r = {x. poly ?p x = 0}" unfolding poly_complex_of_rat_poly ..
    have deg: "degree ?p = degree p" 
      by (simp add: degree_map_poly)
    show ?thesis
    proof (cases "degree p = 1")
      case True
      hence l: "?l = {roots1 ?p}" unfolding d by auto
      from True have "degree ?p = 1" unfolding deg by auto
      from roots1[OF this] show ?thesis unfolding r l by simp
    next
      case False
      show ?thesis 
      proof (cases "degree p = 2")
        case True
        hence l: "?l = set (croots2 ?p)" unfolding d by auto
        from True have "degree ?p = 2" unfolding deg by auto
        from croots2[OF this] show ?thesis unfolding r l by simp
      next
        case False
        with `degree p \<noteq> 1` `degree p \<noteq> 2` `\<not> (degree p \<ge> 3)` have True: "degree p = 0" by auto
        hence l: "?l = {}" unfolding d by auto
        from True have "degree ?p = 0" unfolding deg by auto
        from roots0[OF _ this] p show ?thesis unfolding r l by simp
      qed
    qed
  qed
qed

text \<open>It now comes the preferred function to compute complex roots of a rational polynomial.\<close>
definition complex_roots_of_rat_poly :: "rat poly \<Rightarrow> complex list" where
  "complex_roots_of_rat_poly p = (
    let ps = (if degree p \<ge> 3 then factors_of_rat_poly Uncertified_Factorization p else [p])
    in concat (map complex_roots_of_rat_poly_all ps))"

lemma complex_roots_of_rat_poly: assumes p: "p \<noteq> 0"
  shows "set (complex_roots_of_rat_poly p) = {x. rpoly p x = 0}" (is "?l = ?r")
proof (cases "degree p \<ge> 3")
  case False
  hence "complex_roots_of_rat_poly p = complex_roots_of_rat_poly_all p"
    unfolding complex_roots_of_rat_poly_def Let_def by auto
  with complex_roots_of_rat_poly_all[OF p] show ?thesis by auto
next
  case True
  let ?mode = Uncertified_Factorization
  note factors_of_rat_poly = factors_of_rat_poly[of ?mode]
  {
    fix q
    assume "q \<in> set (factors_of_rat_poly ?mode p)"
    from factors_of_rat_poly(1)[OF refl this] have "q \<noteq> 0" by auto
    from complex_roots_of_rat_poly_all[OF this]
    have "set (complex_roots_of_rat_poly_all q) = {x. rpoly q x = 0}" by auto
  } note all = this
  from True have 
    "?l = (\<Union> ((\<lambda> p. set (complex_roots_of_rat_poly_all p)) ` set (factors_of_rat_poly ?mode p)))"
    unfolding complex_roots_of_rat_poly_def Let_def by auto    
  also have "\<dots> = (\<Union> ((\<lambda> p. {x. rpoly p x = 0}) ` set (factors_of_rat_poly ?mode p)))"
    using all by blast
  finally have l: "?l = (\<Union> ((\<lambda> p. {x. rpoly p x = 0}) ` set (factors_of_rat_poly ?mode p)))" .
  show ?thesis unfolding l factors_of_rat_poly(2)[OF refl p] by auto
qed

definition roots_of_complex_main :: "complex poly \<Rightarrow> complex list" where 
  "roots_of_complex_main p \<equiv> let n = degree p in 
    if n = 0 then [] else if n = 1 then [roots1 p] else if n = 2 then croots2 p
    else (complex_roots_of_rat_poly (map_poly to_rat p))"
  
definition roots_of_complex_poly :: "complex poly \<Rightarrow> complex list option" where
  "roots_of_complex_poly p \<equiv> let (c,pis) = yun_factorization p in
    if (c \<noteq> 0 \<and> (\<forall> (p,i) \<in> set pis. degree p \<le> 2 \<or> (\<forall> x \<in> set (coeffs p). x \<in> \<rat>))) then 
    Some (concat (map (roots_of_complex_main o fst) pis)) else None"

lemma roots_of_complex_main: assumes p: "p \<noteq> 0" and deg: "degree p \<le> 2 \<or> set (coeffs p) \<subseteq> \<rat>"
  shows "set (roots_of_complex_main p) = {x. poly p x = 0}" (is "?l = ?r")
proof -
  note d = roots_of_complex_main_def Let_def
  show ?thesis 
  proof (cases "degree p = 0")
    case True
    hence "?l = {}" unfolding d by auto
    with roots0[OF p True] show ?thesis by auto
  next
    case False note 0 = this
    show ?thesis
    proof (cases "degree p = 1")
      case True
      hence "?l = {roots1 p}" unfolding d by auto
      with roots1[OF True] show ?thesis by auto
    next
      case False note 1 = this
      show ?thesis
      proof (cases "degree p = 2")
        case True
        hence "?l = set (croots2 p)" unfolding d by auto
        with croots2[OF True] show ?thesis by auto
      next
        case False note 2 = this
        let ?q = "map_poly to_rat p"
        from 0 1 2 have l: "?l = set (complex_roots_of_rat_poly ?q)" unfolding d by auto
        from deg 0 1 2 have rat: "set (coeffs p) \<subseteq> \<rat>" by auto
        have "p = map_poly (of_rat o to_rat) p"
          by (rule sym, rule map_poly_eqI, insert rat, auto)
        also have "\<dots> = complex_of_rat_poly ?q"
          by (subst map_poly_compose, auto simp: to_rat)
        finally have id: "{x. poly p x = 0} = {x. poly (complex_of_rat_poly ?q) x = 0}" and q: "?q \<noteq> 0" 
          using p by auto
        from complex_roots_of_rat_poly[OF q, folded id[unfolded poly_complex_of_rat_poly] l] show ?thesis .
      qed
    qed
  qed
qed
 
lemma roots_of_complex_poly: assumes rt: "roots_of_complex_poly p = Some xs"
  shows "set xs = {x. poly p x = 0}"
proof -
  obtain c pis where yun: "yun_factorization p = (c,pis)" by force
  from rt[unfolded roots_of_complex_poly_def yun split Let_def]
  have c: "c \<noteq> 0" and pis: "\<And> p i. (p, i)\<in>set pis \<Longrightarrow> degree p \<le> 2 \<or> (\<forall>x\<in>set (coeffs p). x \<in> \<rat>)"
    and xs: "xs = concat (map (roots_of_complex_main \<circ> fst) pis)"
    by (auto split: if_splits)
  note yun = square_free_factorizationD(1,2,4)[OF yun_factorization(1)[OF yun]]
  from yun(1) have p: "p = smult c (\<Prod>(a, i)\<in>set pis. a ^ Suc i)" .
  have "{x. poly p x = 0} = {x. poly (\<Prod>(a, i)\<in>set pis. a ^ Suc i) x = 0}"
    unfolding p using c by auto
  also have "\<dots> = \<Union> ((\<lambda> p. {x. poly p x = 0}) ` fst ` set pis)" (is "_ = ?r")
    by (subst poly_setprod_0, force+)
  finally have r: "{x. poly p x = 0} = ?r" .
  {
    fix p i
    assume p: "(p,i) \<in> set pis"
    have "set (roots_of_complex_main p) = {x. poly p x = 0}"
      by (rule roots_of_complex_main, insert yun(2)[OF p] pis[OF p], auto)
  } note main = this
  have "set xs = \<Union> ((\<lambda> (p, i). set (roots_of_complex_main p)) ` set pis)" unfolding xs o_def
    by auto
  also have "\<dots> = ?r" using main by auto
  finally show ?thesis unfolding r by simp
qed

subsection \<open>Factorization of Complex Polynomials\<close>

definition factorize_complex_main :: "complex poly \<Rightarrow> (complex \<times> (complex \<times> nat) list) option" where
  "factorize_complex_main p \<equiv> let (c,pis) = yun_factorization p in
    if ((\<forall> (p,i) \<in> set pis. degree p \<le> 2 \<or> (\<forall> x \<in> set (coeffs p). x \<in> \<rat>))) then 
    Some (c, concat (map (\<lambda> (p,i). map (\<lambda> r. (r,i)) (remdups (roots_of_complex_main p))) pis)) else None"

definition factorize_complex_poly :: "complex poly \<Rightarrow> (complex \<times> (complex poly \<times> nat) list) option" where
  "factorize_complex_poly p \<equiv> map_option 
    (\<lambda> (c,ris). (c, map (\<lambda> (r,i). ([:-r,1:],Suc i)) ris)) (factorize_complex_main p)"

 
lemma factorize_complex_main: assumes rt: "factorize_complex_main p = Some (c,xis)"
  shows "p = smult c (\<Prod>(x, i)\<leftarrow>xis. [:- x, 1:] ^ Suc i)"
proof -
  obtain d pis where yun: "yun_factorization p = (d,pis)" by force
  from rt[unfolded factorize_complex_main_def yun split Let_def]
  have pis: "\<And> p i. (p, i)\<in>set pis \<Longrightarrow> degree p \<le> 2 \<or> (\<forall>x\<in>set (coeffs p). x \<in> \<rat>)"
    and xis: "xis = concat (map (\<lambda>(p, i). map (\<lambda>r. (r, i)) (remdups (roots_of_complex_main p))) pis)"
    and d: "d = c"
    by (auto split: if_splits)
  note yun = yun_factorization[OF yun[unfolded d]]
  note yun = square_free_factorizationD[OF yun(1)] yun(2)[unfolded snd_conv]
  let ?exp = "\<lambda> pis. \<Prod>(x, i)\<leftarrow>concat
    (map (\<lambda>(p, i). map (\<lambda>r. (r, i)) (remdups (roots_of_complex_main p))) pis). [:- x, 1:] ^ Suc i"
  from yun(1) have p: "p = smult c (\<Prod>(a, i)\<in>set pis. a ^ Suc i)" .
  also have "(\<Prod>(a, i)\<in>set pis. a ^ Suc i) = (\<Prod>(a, i)\<leftarrow>pis. a ^ Suc i)"
    by (rule setprod.distinct_set_conv_list[OF yun(5)])
  also have "\<dots> = ?exp pis" using pis yun(2,6)
  proof (induct pis)
    case (Cons pi pis)
    obtain p i where pi: "pi = (p,i)" by force
    let ?rts = "remdups (roots_of_complex_main p)"
    note Cons = Cons[unfolded pi]
    have IH: "(\<Prod>(a, i)\<leftarrow>pis. a ^ Suc i) = (?exp pis)"
      by (rule Cons(1)[OF Cons(2-4)], auto)
    from Cons(2-4)[of p i] have deg: "degree p \<le> 2 \<or> (\<forall>x\<in>set (coeffs p). x \<in> \<rat>)"
      and p: "square_free p" "degree p \<noteq> 0" "p \<noteq> 0" "monic p" by auto
    have "(\<Prod>(a, i)\<leftarrow>(pi # pis). a ^ Suc i) = p ^ Suc i * (\<Prod>(a, i)\<leftarrow>pis. a ^ Suc i)"
      unfolding pi by simp
    also have "(\<Prod>(a, i)\<leftarrow>pis. a ^ Suc i) = ?exp pis" by (rule IH)
    finally have id: "(\<Prod>(a, i)\<leftarrow>(pi # pis). a ^ Suc i) = p ^ Suc i * ?exp pis" by simp
    have "?exp (pi # pis) = ?exp [(p,i)] * ?exp pis" unfolding pi by simp
    also have "?exp [(p,i)] = (\<Prod>(x, i)\<leftarrow> (map (\<lambda>r. (r, i)) ?rts). [:- x, 1:] ^ Suc i)" 
      by simp
    also have "\<dots> = (\<Prod> x \<leftarrow> ?rts. [:- x, 1:])^Suc i"
      unfolding listprod_power by (rule arg_cong[of _ _ listprod], auto)
    also have "(\<Prod> x \<leftarrow> ?rts. [:- x, 1:]) = p" 
    proof -
      from fundamental_theorem_algebra_factorized[of p, unfolded `monic p`]
      obtain as where as: "p = (\<Prod>a\<leftarrow>as. [:- a, 1:])" by auto
      also have "\<dots> = (\<Prod>a\<in>set as. [:- a, 1:])"
      proof (rule sym, rule setprod.distinct_set_conv_list, rule ccontr)
        assume "\<not> distinct as" 
        from not_distinct_decomp[OF this] obtain as1 as2 as3 a where
          a: "as = as1 @ [a] @ as2 @ [a] @ as3" by blast
        def q \<equiv> "\<Prod>a\<leftarrow>as1 @ as2 @ as3. [:- a, 1:]"
        have "p = (\<Prod>a\<leftarrow>as. [:- a, 1:])" by fact
        also have "\<dots> = (\<Prod>a\<leftarrow>([a] @ [a]). [:- a, 1:]) * q"
          unfolding q_def a map_append listprod.append by (simp only: ac_simps)
        also have "\<dots> = [:-a,1:] * [:-a,1:] * q" by simp
        finally have "p = ([:-a,1:] * [:-a,1:]) * q" by simp
        hence "[:-a,1:] * [:-a,1:] dvd p" unfolding dvd_def ..
        with `square_free p`[unfolded square_free_def, rule_format, OF `p \<noteq> 0`, of "[:-a,1:]"] 
        show False by auto
      qed
      also have "set as = {x. poly p x = 0}" unfolding as poly_listprod 
        by (simp add: o_def, induct as, auto)
      also have "\<dots> = set ?rts" unfolding set_remdups
        by (rule roots_of_complex_main[symmetric], insert p deg, auto)
      also have "(\<Prod>a\<in>set ?rts. [:- a, 1:]) = (\<Prod>a\<leftarrow>?rts. [:- a, 1:])"
        by (rule setprod.distinct_set_conv_list, auto)
      finally show ?thesis by simp
    qed
    finally have id2: "?exp (pi # pis) = p ^ Suc i * ?exp pis" by simp
    show ?case unfolding id id2 ..
  qed simp
  also have "?exp pis = (\<Prod>(x, i)\<leftarrow>xis. [:- x, 1:] ^ Suc i)" unfolding xis ..
  finally show ?thesis unfolding p xis by simp
qed

lemma factorize_complex_poly: assumes fp: "factorize_complex_poly p = Some (c,qis)"
  shows 
  "p = smult c (\<Prod>(q, i)\<leftarrow>qis. q ^ i)" 
  "(q,i) \<in> set qis \<Longrightarrow> irreducible q \<and> i \<noteq> 0 \<and> monic q \<and> degree q = 1"
proof -
  from fp[unfolded factorize_complex_poly_def]
  obtain pis where fp: "factorize_complex_main p = Some (c,pis)"
    and qis: "qis = map (\<lambda>(r, i). ([:- r, 1:], Suc i)) pis"
    by auto
  from factorize_complex_main[OF fp] have p: "p = smult c (\<Prod>(x, i)\<leftarrow>pis. [:- x, 1:] ^ Suc i)" .
  show "p = smult c (\<Prod>(q, i)\<leftarrow>qis. q ^ i)" unfolding p qis
    by (rule arg_cong[of _ _ "\<lambda> p. smult c (listprod p)"], auto)
  show "(q,i) \<in> set qis \<Longrightarrow> irreducible q \<and> i \<noteq> 0 \<and> monic q \<and> degree q = 1"
    using linear_irreducible[of q] unfolding qis by auto
qed    
end
