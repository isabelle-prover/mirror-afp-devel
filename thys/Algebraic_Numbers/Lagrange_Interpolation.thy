(*  
    Author:      René Thiemann 
                 Akihisa Yamada
    License:     BSD
*)
section \<open>Lagrange Interpolation\<close>

text \<open>We formalized Lagrange interpolation, i.e., a method to interpolate a polynomial $p$
  from a list of points $(x_1,p(x_1)), (x_2, p(x_2)), \ldots$. The interpolation algorithm is proven
  to be sound and complete.\<close>

theory Lagrange_Interpolation
imports 
  Missing_Polynomial
  Ring_Hom_Poly
  Is_Rat_To_Rat
begin

definition lagrange_basis_poly :: "'a :: field list \<Rightarrow> 'a \<Rightarrow> 'a poly" where
  "lagrange_basis_poly xs xj \<equiv> let ys = filter (\<lambda> x. x \<noteq> xj) xs
    in listprod (map (\<lambda> xi. smult (inverse (xj - xi)) [: - xi, 1 :]) ys)"

definition lagrange_interpolation_poly :: "('a :: field \<times> 'a)list \<Rightarrow> 'a poly" where
  "lagrange_interpolation_poly xs_ys \<equiv> let 
    xs = map fst xs_ys
    in listsum (map (\<lambda> (xj,yj). smult yj (lagrange_basis_poly xs xj)) xs_ys)"

definition lagrange_interpolation_poly_int :: "(int \<times> int)list \<Rightarrow> int poly option" where
  "lagrange_interpolation_poly_int xs_ys \<equiv> let 
     rxs_ys = map (\<lambda> (x,y). (of_int x, of_int y)) xs_ys;
     rp = lagrange_interpolation_poly rxs_ys
     in if (\<forall> x \<in> set (coeffs rp). is_int_rat x) then
       Some (map_poly int_of_rat rp) else None"

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

lemma degree_lagrange_basis_poly: "degree (lagrange_basis_poly xs xj) \<le> length (filter (\<lambda> x. x \<noteq> xj) xs)"
  unfolding lagrange_basis_poly_def Let_def
  by (rule order.trans[OF degree_listprod_le], rule order_trans[OF listsum_mono[of _ _ "\<lambda> _. 1"]], 
  auto simp: o_def, induct xs, auto)

lemma degree_lagrange_interpolation_poly:  
  shows "degree (lagrange_interpolation_poly xs_ys) \<le> length xs_ys - 1"
proof -
  {
    fix a b
    assume ab: "(a,b) \<in> set xs_ys" 
    let ?xs = "filter (\<lambda>x. x\<noteq>a) (map fst xs_ys)"
    from ab have "a \<in> set (map fst xs_ys)" by force
    hence "Suc (length ?xs) \<le> length xs_ys"
      by (induct xs_ys, auto)
    hence "length ?xs \<le> length xs_ys - 1" by auto
  } note main = this
  show ?thesis
    unfolding lagrange_interpolation_poly_def Let_def
    by (rule degree_listsum_le, auto, rule order_trans[OF degree_lagrange_basis_poly], insert main, auto)
qed

lemma lagrange_basis_poly_1: 
  "poly (lagrange_basis_poly (map fst xs_ys) x) x = 1"
  unfolding lagrange_basis_poly_def Let_def poly_listprod
  by (rule listprod_neutral, auto)
  (metis field_class.field_inverse mult.commute right_diff_distrib right_minus_eq)

lemma lagrange_basis_poly_0: assumes "x' \<in> set (map fst xs_ys)" and "x' \<noteq> x" 
  shows "poly (lagrange_basis_poly (map fst xs_ys) x) x' = 0"
proof -
  let ?f = "\<lambda>xi. smult (inverse (x - xi)) [:- xi, 1:]"
  let ?xs = "filter (\<lambda>c. c\<noteq>x) (map fst xs_ys)"
  have mem: "?f x' \<in> set (map ?f ?xs)" using assms by auto
  show ?thesis
    unfolding lagrange_basis_poly_def Let_def poly_listprod listprod_map_remove1[OF mem]
    by simp
qed

lemma lagrange_interpolation: assumes dist: "distinct (map fst xs_ys)"
  and p: "p = lagrange_interpolation_poly xs_ys"
  shows "\<And> x y. (x,y) \<in> set xs_ys \<Longrightarrow> poly p x = y"
proof -
  let ?xs = "map fst xs_ys"
  {
    fix x y
    assume xy: "(x,y) \<in> set xs_ys"
    show "poly p x = y" unfolding p lagrange_interpolation_poly_def Let_def poly_listsum map_map o_def
    proof (subst listsum_map_remove1[OF xy], unfold split poly_smult lagrange_basis_poly_1,
      subst listsum_neutral)
      fix v
      assume "v \<in> set (map (\<lambda>xa. poly (case xa of (xj, yj) \<Rightarrow> smult yj (lagrange_basis_poly ?xs xj))
                               x)
                 (remove1 (x, y) xs_ys))" (is "_ \<in> set (map ?f ?xy)")
      then obtain xy' where mem: "xy' \<in> set ?xy" and v: "v = ?f xy'" by auto
      obtain x' y' where xy': "xy' = (x',y')" by force
      from v[unfolded this split] have v: "v = poly (smult y' (lagrange_basis_poly ?xs x')) x" .
      have neq: "x' \<noteq> x"
      proof
        assume "x' = x"
        with mem[unfolded xy'] have mem: "(x,y') \<in> set (remove1 (x,y) xs_ys)" by auto
        hence mem': "(x,y') \<in> set xs_ys" by (meson notin_set_remove1)
        from dist[unfolded distinct_map] have inj: "inj_on fst (set xs_ys)" by auto
        with mem' xy have y': "y' = y" unfolding inj_on_def by force
        from dist have "distinct xs_ys" using distinct_map by blast
        hence "(x,y) \<notin> set (remove1 (x,y) xs_ys)" by simp
        with mem[unfolded y']         
        show False by auto
      qed
      have "poly (lagrange_basis_poly ?xs x') x = 0"
        by (rule lagrange_basis_poly_0, insert xy mem[unfolded xy'] dist neq, force+) 
      thus "v = 0" unfolding v by simp
    qed simp
  } note sound = this
qed

lemma exactly_one_poly_interpolation: assumes xs: "xs_ys \<noteq> []" and dist: "distinct (map fst xs_ys)"
  shows "\<exists>! p. degree p < length xs_ys \<and> (\<forall> x y. (x,y) \<in> set xs_ys \<longrightarrow> poly p x = (y :: 'a :: field))"
proof -
  let ?p = "lagrange_interpolation_poly xs_ys"
  note lag = lagrange_interpolation[OF dist refl]
  show ?thesis
  proof (rule ex1I[of _ ?p], intro conjI allI impI)
    show dp: "degree ?p < length xs_ys" using degree_lagrange_interpolation_poly[of xs_ys] xs by (cases xs_ys, auto)
    show "\<And>x y. (x, y) \<in> set xs_ys \<Longrightarrow> poly (lagrange_interpolation_poly xs_ys) x = y"
      by (rule lag)
    fix q 
    assume q: "degree q < length xs_ys \<and> (\<forall>x y. (x, y) \<in> set xs_ys \<longrightarrow> poly q x = y)"
    show "q = ?p"
      by (rule uniqueness_of_interpolation_point_list[OF dist _ _ lag dp], insert q, auto)
  qed
qed
 
lemma lagrange_interpolation_int_Some: assumes dist: "distinct (map fst xs_ys)"
  and p: "lagrange_interpolation_poly_int xs_ys = Some p"
  shows "\<And> x y. (x,y) \<in> set xs_ys \<Longrightarrow> poly p x = y" "degree p \<le> length xs_ys - 1"
proof -
  let ?r = "rat_of_int"
  def rxs_ys \<equiv> "map (\<lambda>(x, y). (?r x, ?r y)) xs_ys"
  have dist: "distinct (map fst rxs_ys)" using dist unfolding distinct_map rxs_ys_def inj_on_def by force
  obtain rp where rp: "rp = lagrange_interpolation_poly rxs_ys" by blast
  from p[unfolded lagrange_interpolation_poly_int_def Let_def, folded rxs_ys_def rp]
  have p: "p = map_poly int_of_rat rp" and ball: "Ball (set (coeffs rp)) is_int_rat"
    by (auto split: if_splits)
  have id: "rp = map_poly ?r p" unfolding p
    by (rule sym, subst map_poly_compose, force+, rule map_poly_eqI, insert ball, auto)
  note lag = lagrange_interpolation[OF dist rp]
  {
    fix x y
    assume "(x,y) \<in> set xs_ys"
    hence "(?r x, ?r y) \<in> set rxs_ys" unfolding rxs_ys_def by auto
    from lag[OF this] have "poly rp (?r x) = ?r y" by auto
    from this[unfolded id ri.poly_map_poly] show "poly p x = y" by auto
  }
  show "degree p \<le> length xs_ys - 1" using degree_lagrange_interpolation_poly[of rxs_ys, folded rp]
    unfolding id rxs_ys_def ri.degree_map_poly by simp
qed  
  

lemma lagrange_interpolation_int_None: assumes dist: "distinct (map fst xs_ys)"
  and p: "lagrange_interpolation_poly_int xs_ys = None"
  and q: "\<And> x y. (x,y) \<in> set xs_ys \<Longrightarrow> poly q x = y"
  and dq: "degree q < length xs_ys"
  shows False
proof -
  let ?r = "rat_of_int"
  let ?rp = "map_poly ?r"
  def rxs_ys \<equiv> "map (\<lambda>(x, y). (?r x, ?r y)) xs_ys"
  have dist': "distinct (map fst rxs_ys)" using dist unfolding distinct_map rxs_ys_def inj_on_def by force
  obtain rp where rp: "rp = lagrange_interpolation_poly rxs_ys" by blast
  note degrp = degree_lagrange_interpolation_poly[of rxs_ys, folded rp]
  from q have q': "\<And> x y. (x,y) \<in> set rxs_ys \<Longrightarrow> poly (?rp q) x = y" unfolding rxs_ys_def 
    by auto
  have [simp]: "degree (?rp q) = degree q" by (rule ri.degree_map_poly)
  have id: "rp = ?rp q"
    by (rule uniqueness_of_interpolation_point_list[OF dist' lagrange_interpolation[OF dist' rp]],
    insert q' dq degrp, auto simp: rxs_ys_def)
  from p[unfolded lagrange_interpolation_poly_int_def Let_def, folded rxs_ys_def rp]
  have "\<exists> c \<in> set (coeffs rp). c \<notin> \<int>" by (auto split: if_splits)
  from this[unfolded id ri.coeffs_map_poly] show False by auto
qed


end
