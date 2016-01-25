(*  
    Author:      René Thiemann 
                 Akihisa Yamada
    License:     BSD
*)
section \<open>Polynomial Interpolation\<close>

text \<open>We combine the Newton interpolation and the Lagrange interpolation to a combined
  interpolation algorithm which is parametric. This parametric algorithm is then
  further extend from fields to also perform interpolation of integer polynomials.\<close>
theory Polynomial_Interpolation
imports 
  Newton_Interpolation
  Lagrange_Interpolation
begin

datatype interpolation_algorithm = Newton | Lagrange

fun interpolation_poly :: "interpolation_algorithm \<Rightarrow> ('a :: field \<times> 'a)list \<Rightarrow> 'a poly" where
  "interpolation_poly Newton = newton_interpolation_poly"
| "interpolation_poly Lagrange = lagrange_interpolation_poly"

definition interpolation_poly_int :: "interpolation_algorithm \<Rightarrow> (int \<times> int)list \<Rightarrow> int poly option" where
  "interpolation_poly_int alg xs_ys \<equiv> let 
     rxs_ys = map (\<lambda> (x,y). (of_int x, of_int y)) xs_ys;
     rp = interpolation_poly alg rxs_ys
     in if (\<forall> x \<in> set (coeffs rp). is_int_rat x) then
       Some (map_poly int_of_rat rp) else None"

lemma interpolation_poly: assumes dist: "distinct (map fst xs_ys)"
  and p: "p = interpolation_poly alg xs_ys"
  and xy: "(x,y) \<in> set xs_ys"
  shows "poly p x = y"
proof (cases alg)
  case Newton
  thus ?thesis using newton_interpolation_poly[OF dist _ xy] p by simp
next
  case Lagrange
  thus ?thesis using lagrange_interpolation[OF dist _ xy] p by simp
qed

lemma degree_interpolation_poly:  
  shows "degree (interpolation_poly alg xs_ys) \<le> length xs_ys - 1"
  using degree_lagrange_interpolation_poly[of xs_ys]
    degree_newton_interpolation_poly[of xs_ys]
  by (cases alg, auto)

lemma uniqueness_of_interpolation: fixes p :: "'a :: idom poly" 
  assumes cS: "card S = Suc n"
  and "degree p \<le> n" and "degree q \<le> n" and
   id: "\<And> x. x \<in> S \<Longrightarrow> poly p x = poly q x"
  shows "p = q"
proof -
  def f \<equiv> "p - q"
  let ?R = "{x. poly f x = 0}"
  have sub: "S \<subseteq> ?R" unfolding f_def using id by auto
  show ?thesis
  proof (cases "f = 0")
    case True thus ?thesis unfolding f_def by simp
  next
    case False note f = this
    let ?R = "{x. poly f x = 0}"
    from poly_roots_finite[OF f] have "finite ?R" .
    from card_mono[OF this sub] poly_roots_degree[OF f] 
    have "Suc n \<le> degree f" unfolding cS by auto
    also have "\<dots> \<le> n" unfolding f_def
      by (rule degree_diff_le, insert assms, auto)
    finally show ?thesis by auto
  qed
qed

lemma uniqueness_of_interpolation_point_list: fixes p :: "'a :: idom poly" 
  assumes dist: "distinct (map fst xs_ys)"
  and p: "\<And> x y. (x,y) \<in> set xs_ys \<Longrightarrow> poly p x = y" "degree p < length xs_ys" 
  and q: "\<And> x y. (x,y) \<in> set xs_ys \<Longrightarrow> poly q x = y" "degree q < length xs_ys" 
  shows "p = q"
proof -
  let ?xs = "map fst xs_ys"
  from q obtain n where len: "length xs_ys = Suc n" and dq: "degree q \<le> n" by (cases xs_ys, auto)
  from p have dp: "degree p \<le> n" unfolding len by auto
  from dist have card: "card (set ?xs) = Suc n" unfolding len[symmetric]
    using distinct_card by fastforce
  show "p = q"
  proof (rule uniqueness_of_interpolation[OF card dp dq])
    fix x
    assume "x \<in> set ?xs"
    then obtain y where "(x,y) \<in> set xs_ys" by auto
    from p(1)[OF this] q(1)[OF this] show "poly p x = poly q x" by simp
  qed  
qed

lemma exactly_one_poly_interpolation: assumes xs: "xs_ys \<noteq> []" and dist: "distinct (map fst xs_ys)"
  shows "\<exists>! p. degree p < length xs_ys \<and> (\<forall> x y. (x,y) \<in> set xs_ys \<longrightarrow> poly p x = (y :: 'a :: field))"
proof -
  let ?alg = "undefined"
  let ?p = "interpolation_poly ?alg xs_ys"
  note inter = interpolation_poly[OF dist refl]
  show ?thesis
  proof (rule ex1I[of _ ?p], intro conjI allI impI)
    show dp: "degree ?p < length xs_ys" using degree_interpolation_poly[of ?alg xs_ys] xs by (cases xs_ys, auto)
    show "\<And>x y. (x, y) \<in> set xs_ys \<Longrightarrow> poly (interpolation_poly ?alg xs_ys) x = y"
      by (rule inter)
    fix q 
    assume q: "degree q < length xs_ys \<and> (\<forall>x y. (x, y) \<in> set xs_ys \<longrightarrow> poly q x = y)"
    show "q = ?p"
      by (rule uniqueness_of_interpolation_point_list[OF dist _ _ inter dp], insert q, auto)
  qed
qed


lemma interpolation_poly_int_Some: assumes dist: "distinct (map fst xs_ys)"
  and p: "interpolation_poly_int alg xs_ys = Some p"
  shows "\<And> x y. (x,y) \<in> set xs_ys \<Longrightarrow> poly p x = y" "degree p \<le> length xs_ys - 1"
proof -
  let ?r = "rat_of_int"
  def rxs_ys \<equiv> "map (\<lambda>(x, y). (?r x, ?r y)) xs_ys"
  have dist: "distinct (map fst rxs_ys)" using dist unfolding distinct_map rxs_ys_def inj_on_def by force
  obtain rp where rp: "rp = interpolation_poly alg rxs_ys" by blast
  from p[unfolded interpolation_poly_int_def Let_def, folded rxs_ys_def rp]
  have p: "p = map_poly int_of_rat rp" and ball: "Ball (set (coeffs rp)) is_int_rat"
    by (auto split: if_splits)
  have id: "rp = map_poly ?r p" unfolding p
    by (rule sym, subst map_poly_compose, force+, rule map_poly_eqI, insert ball, auto)
  note inter = interpolation_poly[OF dist rp]
  {
    fix x y
    assume "(x,y) \<in> set xs_ys"
    hence "(?r x, ?r y) \<in> set rxs_ys" unfolding rxs_ys_def by auto
    from inter[OF this] have "poly rp (?r x) = ?r y" by auto
    from this[unfolded id ri.poly_map_poly] show "poly p x = y" by auto
  }
  show "degree p \<le> length xs_ys - 1" using degree_interpolation_poly[of alg rxs_ys, folded rp]
    unfolding id rxs_ys_def ri.degree_map_poly by simp
qed  
  

lemma interpolation_poly_int_None: assumes dist: "distinct (map fst xs_ys)"
  and p: "interpolation_poly_int alg xs_ys = None"
  and q: "\<And> x y. (x,y) \<in> set xs_ys \<Longrightarrow> poly q x = y"
  and dq: "degree q < length xs_ys"
  shows False
proof -
  let ?r = "rat_of_int"
  let ?rp = "map_poly ?r"
  def rxs_ys \<equiv> "map (\<lambda>(x, y). (?r x, ?r y)) xs_ys"
  have dist': "distinct (map fst rxs_ys)" using dist unfolding distinct_map rxs_ys_def inj_on_def by force
  obtain rp where rp: "rp = interpolation_poly alg rxs_ys" by blast
  note degrp = degree_interpolation_poly[of alg rxs_ys, folded rp]
  from q have q': "\<And> x y. (x,y) \<in> set rxs_ys \<Longrightarrow> poly (?rp q) x = y" unfolding rxs_ys_def 
    by auto
  have [simp]: "degree (?rp q) = degree q" by (rule ri.degree_map_poly)
  have id: "rp = ?rp q"
    by (rule uniqueness_of_interpolation_point_list[OF dist' interpolation_poly[OF dist' rp]],
    insert q' dq degrp, auto simp: rxs_ys_def)
  from p[unfolded interpolation_poly_int_def Let_def, folded rxs_ys_def rp]
  have "\<exists> c \<in> set (coeffs rp). c \<notin> \<int>" by (auto split: if_splits)
  from this[unfolded id ri.coeffs_map_poly] show False by auto
qed

end