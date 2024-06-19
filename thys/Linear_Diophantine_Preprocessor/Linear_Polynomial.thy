section \<open>Linear Polynomials\<close>

subsection \<open>An Abstract Type for Multivariate Linear Polynomials\<close>

theory Linear_Polynomial
  imports 
    Main
begin

typedef (overloaded) ('a :: zero,'v) lpoly = "{ c :: 'v option \<Rightarrow> 'a. finite {v. c v \<noteq> 0}}" 
  by (intro exI[of _ "\<lambda> _. 0"], auto)

setup_lifting type_definition_lpoly 

instantiation lpoly :: (ab_group_add,type)ab_group_add
begin

lift_definition uminus_lpoly :: "('a, 'b) lpoly \<Rightarrow> ('a, 'b) lpoly" is "\<lambda> c x.  - c x" by auto

lift_definition minus_lpoly :: "('a, 'b) lpoly \<Rightarrow> ('a, 'b) lpoly \<Rightarrow> ('a, 'b) lpoly" is "\<lambda> c1 c2 x.  c1 x - c2 x"
proof goal_cases
  case (1 c1 c2)
  have "{v. c1 v - c2 v \<noteq> 0} \<subseteq> {v. c1 v \<noteq> 0} \<union> {v. c2 v \<noteq> 0}" by auto
  from finite_subset[OF this] 1 show ?case by auto
qed

lift_definition plus_lpoly :: "('a, 'b) lpoly \<Rightarrow> ('a, 'b) lpoly \<Rightarrow> ('a, 'b) lpoly" is "\<lambda> c1 c2 x.  c1 x + c2 x"
proof goal_cases
  case (1 c1 c2)
  have "{v. c1 v + c2 v \<noteq> 0} \<subseteq> {v. c1 v \<noteq> 0} \<union> {v. c2 v \<noteq> 0}" by auto
  from finite_subset[OF this] 1 show ?case by auto
qed 

lift_definition zero_lpoly :: "('a, 'b) lpoly" is "\<lambda> c. 0" by auto

instance by (intro_classes; transfer, auto simp: ac_simps)
end
 
lift_definition var_l :: "'v \<Rightarrow> ('a :: {comm_monoid_mult,zero_neq_one}, 'v) lpoly" is "\<lambda> x. (\<lambda> c. 0)(Some x := 1)" by auto
lift_definition constant_l :: "('a :: zero, 'v) lpoly \<Rightarrow> 'a" is "\<lambda> c. c None" .
lift_definition coeff_l :: "('a :: zero, 'v) lpoly \<Rightarrow> 'v \<Rightarrow> 'a" is "\<lambda> c x. c (Some x)" . 
lift_definition vars_l :: "('a :: zero, 'v) lpoly \<Rightarrow> 'v set" is "\<lambda> c. { x. c (Some x) \<noteq> 0}" .

lemma finite_vars_l[simp,intro]: "finite (vars_l p)" 
proof (transfer, goal_cases)
  case (1 p)
  show ?case by (rule finite_subset[OF _ finite_imageI[OF 1, of the]], force)
qed

type_synonym ('a,'v) assign = "'v \<Rightarrow> 'a" 

lemma vars_l_var[simp]: "vars_l (var_l x) = {x}" by transfer auto

lemma vars_l_plus: "vars_l (p1 + p2) \<subseteq> vars_l p1 \<union> vars_l p2" 
  by (transfer, auto)

lemma vars_l_minus: "vars_l (p1 - p2) \<subseteq> vars_l p1 \<union> vars_l p2" 
  by (transfer, auto)

lemma vars_l_uminus[simp]: "vars_l (- p) = vars_l p" 
  by (transfer, auto)

lemma vars_l_zero[simp]: "vars_l 0 = {}" 
  by (transfer, auto)

definition eval_l :: "('a :: comm_ring, 'v) assign \<Rightarrow> ('a,'v) lpoly \<Rightarrow> 'a" where
  "eval_l \<alpha> p = constant_l p + sum (\<lambda> x. coeff_l p x * \<alpha> x) (vars_l p)" 

lemma eval_l_mono: assumes "finite V" "vars_l p \<subseteq> V" 
  shows "eval_l \<alpha> p = constant_l p + sum (\<lambda> x. coeff_l p x * \<alpha> x) V" 
proof -
  define W where "W = V - vars_l p"
  have [simp]: "(\<Sum>x\<in>W. coeff_l p x * \<alpha> x) = 0" 
    by (rule sum.neutral, unfold W_def, transfer, auto)
  have V: "V = W \<union> vars_l p" "W \<inter> vars_l p = {}" using assms unfolding W_def by auto
  show ?thesis unfolding eval_l_def using assms unfolding V 
    by (subst sum.union_disjoint[OF _ _ V(2)], auto)
qed

lemma eval_l_cong: assumes "\<And> x. x \<in> vars_l p \<Longrightarrow> \<alpha> x = \<beta> x" 
  shows "eval_l \<alpha> p = eval_l \<beta> p" 
  unfolding eval_l_mono[OF finite_vars_l subset_refl]
  by (intro arg_cong[of _ _ "\<lambda> x. _ + x"] sum.cong refl, insert assms, auto)
 
lemma eval_l_0[simp]: "eval_l \<alpha> 0 = 0" unfolding eval_l_def
  by (transfer, auto)

lemma eval_l_plus[simp]: "eval_l \<alpha> (p1 + p2) = eval_l \<alpha> p1 + eval_l \<alpha> p2" 
proof -
  have fin: "finite (vars_l p1 \<union> vars_l p2)" by auto
  show ?thesis
    apply (subst (1 2 3) eval_l_mono[OF fin])
    subgoal by auto
    subgoal by auto
    subgoal by (rule vars_l_plus)  
    subgoal by (transfer, auto simp: sum.distrib algebra_simps)
    done
qed

lemma eval_l_minus[simp]: "eval_l \<alpha> (p1 - p2) = eval_l \<alpha> p1 - eval_l \<alpha> p2" 
proof -
  have fin: "finite (vars_l p1 \<union> vars_l p2)" by auto
  show ?thesis
    apply (subst (1 2 3) eval_l_mono[OF fin])
    subgoal by auto
    subgoal by auto
    subgoal by (rule vars_l_minus)  
    subgoal by (transfer, auto simp: sum_subtractf algebra_simps)
    done
qed

lemma eval_l_uminus[simp]: "eval_l \<alpha> (- p) = - eval_l \<alpha> p" 
  unfolding eval_l_def
  by (transfer, auto simp: sum_negf)

lemma eval_l_var[simp]: "eval_l \<alpha> (var_l x) = \<alpha> x" 
  apply (subst eval_l_mono[of "{x}"])
    apply force
   apply force
  by (transfer, auto)

(* substitute x by p within q *)
lift_definition substitute_l :: "'v \<Rightarrow> ('a :: comm_ring, 'v) lpoly \<Rightarrow> ('a,'v) lpoly \<Rightarrow> ('a,'v) lpoly" is
  "\<lambda> x p q y. (q(Some x := 0)) y + q (Some x) * p y"
proof goal_cases
  case (1 x p1 p2)
  show ?case
    apply (rule finite_subset[of _ "{v. p1 v \<noteq> 0} \<union> {v. p2 v \<noteq> 0}"])
    using 1 by auto
qed

lemma vars_substitute_l: "vars_l (substitute_l x p q) \<subseteq> vars_l p \<union> (vars_l q - {x})" 
  by (transfer, auto)

lemma substitute_l_id: "x \<notin> vars_l q \<Longrightarrow> substitute_l x p q = q" 
  by transfer auto


lemma eval_substitute_l: "eval_l \<alpha> (substitute_l x p q) = eval_l (\<alpha>( x := eval_l \<alpha> p)) q" 
proof -
  have fin: "finite (insert x (vars_l p \<union> vars_l q))" 
      and fin2: "finite (vars_l p \<union> vars_l q)" by auto
  define V where "V = vars_l p \<union> vars_l q - {x}" 
  have V: "finite V" "x \<notin> V" unfolding V_def by auto
  show ?thesis
    apply (subst (1 2 3) eval_l_mono[OF fin])
    subgoal by auto
    subgoal by auto
    subgoal using vars_substitute_l[of x p q] by auto
    apply (unfold sum.insert_remove[OF fin2])
    apply (unfold V_def[symmetric])
    using V
    apply (transfer)
    apply (simp add: algebra_simps sum.distrib sum_distrib_left)
    apply (intro sum.cong)
     apply (auto simp: ac_simps)
    done
qed

lift_definition fun_of_lpoly :: "('a :: zero,'v) lpoly \<Rightarrow> 'v option \<Rightarrow> 'a" is "\<lambda> x. x" .

lift_definition smult_l :: "'a :: comm_ring \<Rightarrow> ('a,'v)lpoly \<Rightarrow> ('a,'v)lpoly" is
  "\<lambda> y c z. y * c z" 
proof (goal_cases)
  case 1
  show ?case by (rule finite_subset[OF _ 1], auto)
qed

lemma coeff_smult_l[simp]: "coeff_l (smult_l c p) x = c * coeff_l p x" 
  by transfer auto

lemma constant_smult_l[simp]: "constant_l (smult_l c p) = c * constant_l p" 
  by transfer auto

lemma eval_smult_l[simp]: "eval_l \<alpha> (smult_l c p) = c * eval_l \<alpha> p" 
  apply (subst (1 2) eval_l_mono[of "vars_l p"])
  subgoal by simp
  subgoal by simp
  subgoal by transfer auto
  unfolding eval_l_def coeff_smult_l
  by (auto simp: algebra_simps sum_distrib_left)

lift_definition const_l :: "'a :: zero \<Rightarrow> ('a,'v) lpoly" is "\<lambda> c. (\<lambda> z. 0)(None := c)" 
  by auto

lemma eval_l_const_l_constant: "eval_l \<alpha> (const_l (constant_l p)) = constant_l p" 
  unfolding eval_l_def
  by transfer auto

definition substitute_all_l :: "('v \<Rightarrow> ('a,'w) lpoly) \<Rightarrow> ('a :: comm_ring, 'v) lpoly \<Rightarrow> ('a, 'w) lpoly" where
  "substitute_all_l \<sigma> p = (const_l (constant_l p) + sum (\<lambda> x. smult_l (coeff_l p x) (\<sigma> x)) (vars_l p))" 

lemma eval_substitute_all_l: "eval_l \<alpha> (substitute_all_l \<sigma> p) = eval_l (\<lambda> x. eval_l \<alpha> (\<sigma> x)) p" 
proof -
  define xs where "xs = vars_l p" 
  have fin: "finite xs" unfolding xs_def by auto
  show ?thesis
    unfolding substitute_all_l_def
    unfolding eval_l_mono[OF finite_vars_l subset_refl, of _ p]
    unfolding eval_l_plus eval_l_const_l_constant
    unfolding xs_def[symmetric] using fin
  proof (intro arg_cong[of _ _ "\<lambda> x. _ + x"], induct xs rule: finite_induct)
    case *: (insert x xs)
    note IH = *(3)[OF *(1)]
    note sum = sum.insert[OF *(1-2)]
    show ?case unfolding sum eval_l_plus IH eval_smult_l by simp
  qed simp
qed

lift_definition sdiv_l :: "(int, 'v) lpoly \<Rightarrow> int \<Rightarrow> (int, 'v) lpoly" is "\<lambda> c q x. c x div q" 
proof (goal_cases)
  case 1
  show ?case by (rule finite_subset[OF _ 1], auto)
qed

definition "vars_l_list p = sorted_list_of_set (vars_l p)" 

lemma vars_l_list[simp]: "set (vars_l_list p) = vars_l p" 
  unfolding vars_l_list_def by simp

definition min_var :: "('a :: {linorder, ordered_ab_group_add_abs}, 'v :: linorder) lpoly \<Rightarrow> 'v" where
  "min_var p = (let 
     xcs = map (\<lambda> x. (x,coeff_l p x)) (vars_l_list p);
     axcs = map (map_prod id abs) xcs;
     m = min_list (map snd axcs)
   in (case filter (\<lambda> xa. snd xa = m) axcs of
     (x,a) # _ \<Rightarrow> x))" 

lemma min_var: "vars_l p \<noteq> {} \<Longrightarrow> coeff_l p (min_var p) \<noteq> 0" 
    "x \<in> vars_l p \<Longrightarrow> abs (coeff_l p (min_var p)) \<le> abs (coeff_l p x)"
proof -
  let ?m = "min_var p" 
  define xcs where "xcs = map (\<lambda> x. (x,coeff_l p x)) (vars_l_list p)" 
  define axcs where "axcs = map (map_prod id abs) xcs" 
  define m where "m = min_list (map snd axcs)" 
  define fxs where "fxs = filter (\<lambda> xa. snd xa = m) axcs" 
  {
    fix x
    assume x: "x \<in> vars_l p" 
    let ?c = "coeff_l p x" 
    from x have cx: "?c \<noteq> 0" by transfer auto
    from x have "(x, ?c) \<in> set xcs" unfolding xcs_def by force
    hence ax: "(x, abs ?c) \<in> set axcs" unfolding axcs_def by force
    hence "map snd axcs \<noteq> []" "abs ?c \<in> set (map snd axcs)" by force+
    with min_list_Min[OF this(1), folded m_def] 
    have m: "m = Min (set (map snd axcs))" "m \<in> set (map snd axcs)" "m \<le> abs ?c" by auto
    from m(2) have "m \<in> snd ` set fxs" unfolding fxs_def by force
    then obtain y m' xs where fxs: "fxs = ((y,m') # xs)" 
      by (cases fxs, auto simp: fxs_def)
    hence "(y,m') \<in> set fxs" by auto
    from this[unfolded fxs_def] have m': "m' = m" by auto
    with fxs have fxs: "fxs = ((y,m) # xs)" by auto
    have m': "?m = y" 
      unfolding min_var_def Let_def xcs_def[symmetric]
      unfolding axcs_def[symmetric]
      unfolding m_def[symmetric]
      unfolding fxs_def[symmetric]
      unfolding fxs by simp
    from fxs have "(y,m) \<in> set axcs" unfolding fxs_def 
      by (metis Cons_eq_filter_iff in_set_conv_decomp)
    then obtain c where "(y,c) \<in> set xcs" and mc: "m = abs c" unfolding axcs_def by auto
    hence c: "c = coeff_l p y" and y: "y \<in> vars_l p" unfolding xcs_def by auto
    hence c0: "c \<noteq> 0" by transfer auto
    show "abs (coeff_l p ?m) \<le> abs (coeff_l p x)" 
      unfolding m' using m(3) unfolding c mc .
    have "abs (coeff_l p ?m) \<noteq> 0" using c0 unfolding c m' by auto
  }
  thus "vars_l p \<noteq> {} \<Longrightarrow> coeff_l p (min_var p) \<noteq> 0" by auto
qed

definition gcd_coeffs_l :: "('a :: Gcd, 'v)lpoly \<Rightarrow> 'a" where
  "gcd_coeffs_l p = Gcd (coeff_l p ` vars_l p)"

lift_definition change_const :: "'a :: zero \<Rightarrow> ('a,'v)lpoly \<Rightarrow> ('a,'v)lpoly" is "\<lambda> x c. c(None := x)" 
proof goal_cases
  case (1 x c)
  hence f: "finite ((insert None) {v. c v \<noteq> 0})" by auto
  show ?case
    by (rule finite_subset[OF _ f], auto)
qed

lemma lpoly_fun_of_eqI: assumes "\<And> x. fun_of_lpoly p x = fun_of_lpoly q x" 
  shows "p = q" 
  using assms by transfer auto

lift_definition reorder_nontriv_var :: "'v \<Rightarrow> (int,'v) lpoly \<Rightarrow> 'v \<Rightarrow> (int,'v) lpoly" is
  "\<lambda> x c y. (\<lambda> z. c z div c (Some x))(Some x := 1, Some y := -1)"
proof (goal_cases)
  case (1 x c y)
  from 1 have fin: "finite (insert (Some y) (insert (Some x) ({v. c v \<noteq> 0})))" by auto
  show ?case by (rule finite_subset[OF _ fin], auto)
qed

lemma coeff_l_reorder_nontriv_var: "coeff_l (reorder_nontriv_var x p y)
  = (\<lambda> z. coeff_l p z div coeff_l p x)(x := 1, y := -1)" 
  by (transfer, auto simp: Let_def)

lemma vars_reorder_non_triv: "vars_l (reorder_nontriv_var x p y) \<subseteq> insert x (insert y (vars_l p))"
  by (transfer, auto simp: Let_def)


end