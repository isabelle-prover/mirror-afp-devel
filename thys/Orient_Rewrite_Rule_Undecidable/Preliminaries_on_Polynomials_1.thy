section \<open>Preliminaries: Extending the Library on Multivariate Polynomials\<close>

subsection \<open>Part 1 -- Extensions Without Importing Univariate Polynomials\<close>

theory Preliminaries_on_Polynomials_1
  imports 
    Polynomials.More_MPoly_Type
    Polynomials.MPoly_Type_Class_FMap
begin

type_synonym var = nat
type_synonym monom = "var \<Rightarrow>\<^sub>0 nat" 

definition substitute :: "(var \<Rightarrow> 'a mpoly) \<Rightarrow> 'a :: comm_semiring_1 mpoly \<Rightarrow> 'a mpoly" where
  "substitute \<sigma> p = insertion \<sigma> (replace_coeff Const p)" 

lemma Const_0: "Const 0 = 0"
  by (transfer, simp add: Const\<^sub>0_zero)

lemma Const_1: "Const 1 = 1"
  by (transfer, simp add: Const\<^sub>0_one)

lemma insertion_Var: "insertion \<alpha> (Var x) = \<alpha> x" 
  apply transfer
  by (metis One_nat_def Var\<^sub>0_def insertion.abs_eq insertion_single mapping_of_inverse monom.rep_eq mult.right_neutral mult_1 power.simps(2) power_0)

lemma insertion_Const: "insertion \<alpha> (Const a) = a"
  by (metis Const.abs_eq Const\<^sub>0_def insertion_single monom.abs_eq mult.right_neutral power_0 single_zero)

lemma insertion_power: "insertion \<alpha> (p^n) = (insertion \<alpha> p)^n" 
  by (induct n, auto simp: insertion_mult)

lemma insertion_monom_add: "insertion \<alpha> (monom (f + g) a) = insertion \<alpha> (monom f 1) * insertion \<alpha> (monom g a)" 
  by (metis insertion_mult mult_1 mult_monom)

lemma insertion_uminus: "insertion \<alpha> (- p) = - insertion \<alpha> p"
  by (metis add_eq_0_iff insertion_add insertion_zero)

lemma insertion_sum_list: "insertion \<alpha> (sum_list ps) = sum_list (map (insertion \<alpha>) ps)" 
  by (induct ps, auto simp: insertion_add)

lemma coeff_uminus: "coeff (- p) m = - coeff p m"
  by (simp add: coeff_def uminus_mpoly.rep_eq)

lemma insertion_substitute: "insertion \<alpha> (substitute \<sigma> p) = insertion (\<lambda> x. insertion \<alpha> (\<sigma> x)) p" 
  unfolding substitute_def
proof (induct p rule: mpoly_induct)
  case (monom m a)
  show ?case 
    apply (subst replace_coeff_monom)
    subgoal by (simp add: Const_0)
    subgoal proof (induct m arbitrary: a rule: poly_mapping_induct)
      case (single k v)
      show ?case by (simp add: insertion_mult insertion_Const insertion_power)  
    next
      case (sum f g k v a)
      from sum(1)[of 1] sum(2)[of a] show ?case 
        by (simp add: insertion_monom_add insertion_mult Const_1)
    qed
    done
next
  case (sum p1 p2 m a)
  then show ?case 
    apply (subst replace_coeff_add)
    subgoal by (simp add: Const_0)
    subgoal by (transfer', simp add: Const\<^sub>0_def single_add)
    by (simp add: insertion_add)
qed

lemma Const_add: "Const (x + y) = Const x + Const y" 
  by (transfer, auto simp: Const\<^sub>0_def single_add)

lemma substitute_add[simp]: "substitute \<sigma> (p + q) = substitute \<sigma> p + substitute \<sigma> q" 
  unfolding substitute_def insertion_add[symmetric] 
  by (subst replace_coeff_add, auto simp: Const_0 Const_add)

lemma Const_sum: "Const (sum f A) = sum (Const o f) A"
  by (metis Const_0 Const_add sum_comp_morphism)

lemma Const_sum_list: "Const (sum_list (map f xs)) = sum_list (map (Const o f) xs)"
  by (induct xs, auto simp: Const_0 Const_add)

lemma Const_0_eq[simp]: "Const x = 0 \<longleftrightarrow> x = 0" 
  by (smt (verit) Const.abs_eq Const\<^sub>0_def coeff_monom monom.abs_eq single_zero when_def zero_mpoly_def)

lemma Const_sum_any: "Const (Sum_any f) = Sum_any (Const o f)"
  unfolding Sum_any.expand_set Const_sum o_def
  by (intro sum.cong[OF _ refl], auto simp: Const_0)

lemma Const_mult: "Const (x * y) = Const x * Const y"
  by (metis Const.abs_eq Const\<^sub>0_def monom.abs_eq smult_conv_mult smult_monom)

lemma Const_power: "Const (x ^ e) = Const x ^ e" 
  by (induct e, auto simp: Const_1 Const_mult)

lemma lookup_replace_Const: "lookup (mapping_of (replace_coeff Const p)) l = Const (lookup (mapping_of p) l)" 
  by (metis Const_0 coeff_def coeff_replace_coeff)

lemma replace_coeff_mult: "replace_coeff Const (p * q) = replace_coeff Const p * replace_coeff Const q" 
  apply (subst coeff_eq[symmetric], intro ext, subst coeff_replace_coeff, rule Const_0)
  apply (unfold coeff_def)
  apply (unfold times_mpoly.rep_eq)
  apply (unfold Poly_Mapping.lookup_mult)
  apply (unfold Const_sum_any o_def Const_mult lookup_replace_Const)
  apply (unfold when_def if_distrib Const_0)
  by auto


lemma substitute_mult[simp]: "substitute \<sigma> (p * q) = substitute \<sigma> p * substitute \<sigma> q" 
  unfolding substitute_def insertion_mult[symmetric] replace_coeff_mult ..

lemma replace_coeff_Var[simp]: "replace_coeff Const (Var x) = Var x"
  by (metis Const_0 Const_1 Var.abs_eq Var\<^sub>0_def monom.abs_eq replace_coeff_monom)

lemma replace_coeff_Const[simp]: "replace_coeff Const (Const c) = Const (Const c)" 
  by (metis Const.abs_eq Const\<^sub>0_def Const_0 monom.abs_eq replace_coeff_monom)

lemma substitute_Var[simp]: "substitute \<sigma> (Var x) = \<sigma> x" 
  unfolding substitute_def by (simp add: insertion_Var)

lemma substitute_Const[simp]: "substitute \<sigma> (Const c) = Const c" 
  unfolding substitute_def by (simp add: insertion_Const)

lemma substitute_0[simp]: "substitute \<sigma> 0 = 0" 
  using substitute_Const[of \<sigma> 0, unfolded Const_0] .

lemma substitute_1[simp]: "substitute \<sigma> 1 = 1" 
  using substitute_Const[of \<sigma> 1, unfolded Const_1] .

lemma substitute_power[simp]: "substitute \<sigma> (p^e) = (substitute \<sigma> p)^e" 
  by (induct e, auto)

lemma substitute_monom[simp]: "substitute \<sigma> (monom (monomial e x) c) = Const c * (\<sigma> x)^e" 
  by (simp add: replace_coeff_monom substitute_def)

lemma substitute_sum_list: "substitute \<sigma> (sum_list (map f xs)) = sum_list (map (substitute \<sigma> o f) xs)"
  by (induct xs, auto)

lemma substitute_sum: "substitute \<sigma> (sum f xs) = sum (substitute \<sigma> o f) xs"
  by (induct xs rule: infinite_finite_induct, auto)

lemma substitute_prod: "substitute \<sigma> (prod f xs) = prod (substitute \<sigma> o f) xs"
  by (induct xs rule: infinite_finite_induct, auto)

definition vars_list where "vars_list = sorted_list_of_set o vars" 

lemma set_vars_list[simp]: "set (vars_list p) = vars p" 
  unfolding vars_list_def o_def using vars_finite[of p] by auto

lift_definition mpoly_coeff_filter :: "('a :: zero \<Rightarrow> bool) \<Rightarrow> 'a mpoly \<Rightarrow> 'a mpoly" is
  "\<lambda> f p. Poly_Mapping.mapp (\<lambda> m c. c when f c) p" .

lemma mpoly_coeff_filter: "coeff (mpoly_coeff_filter f p) m = (coeff p m when f (coeff p m))" 
  unfolding coeff_def by transfer (simp add: in_keys_iff mapp.rep_eq)

lemma total_degree_add: assumes "total_degree p \<le> d" "total_degree q \<le> d" 
  shows "total_degree (p + q) \<le> d" 
  using assms
proof transfer
  fix d and p q :: "(nat \<Rightarrow>\<^sub>0 nat) \<Rightarrow>\<^sub>0 'a" 
  let ?exp = "\<lambda> p. Max (insert (0 :: nat) ((\<lambda>m. sum (lookup m) (keys m)) ` keys p))" 
  assume d: "?exp p \<le> d" "?exp q \<le> d" 
  have "?exp (p + q) \<le> Max (insert (0 :: nat) ((\<lambda>m. sum (lookup m) (keys m)) ` (keys p \<union> keys q)))" 
    using Poly_Mapping.keys_add[of p q]
    by (intro Max_mono, auto)
  also have "\<dots> = max (?exp p) (?exp q)" 
    by (subst Max_Un[symmetric], auto simp: image_Un)
  also have "\<dots> \<le> d" using d by auto
  finally show "?exp (p + q) \<le> d" .
qed

lemma total_degree_Var[simp]: "total_degree (Var x :: 'a :: comm_semiring_1 mpoly) = Suc 0" 
  by (transfer, auto simp: Var\<^sub>0_def)

lemma total_degree_Const[simp]: "total_degree (Const x) = 0" 
  by (transfer, auto simp: Const\<^sub>0_def)

lemma total_degree_Const_mult: assumes "total_degree p \<le> d"
  shows "total_degree (Const x * p) \<le> d" 
  using assms
proof (transfer, goal_cases)
  case (1 p d x)
  have sub: "keys (Const\<^sub>0 x * p) \<subseteq> keys p" 
    by (rule order.trans[OF keys_mult], auto simp: Const\<^sub>0_def)
  show ?case
    by (rule order.trans[OF _ 1], rule Max_mono, insert sub, auto)
qed

lemma vars_0[simp]: "vars 0 = {}" 
  unfolding vars_def by (simp add: zero_mpoly.rep_eq)

lemma vars_1[simp]: "vars 1 = {}"
  unfolding vars_def by (simp add: one_mpoly.rep_eq)

lemma vars_Var[simp]: "vars (Var x :: 'a :: comm_semiring_1 mpoly) = {x}" 
  unfolding vars_def by (transfer, auto simp: Var\<^sub>0_def)

lemma vars_Const[simp]: "vars (Const c) = {}" 
  unfolding vars_def by (transfer, auto simp: Const\<^sub>0_def)

lemma coeff_sum_list: "coeff (sum_list ps) m = (\<Sum>p\<leftarrow>ps. coeff p m)"  
  by (induct ps, auto simp: coeff_add[symmetric]) 
    (metis coeff_monom monom_zero zero_when)

lemma coeff_Const_mult: "coeff (Const c * p) m = c * coeff p m" 
  by (metis Const.abs_eq Const\<^sub>0_def add_0 coeff_monom_mult monom.abs_eq)

lemma coeff_Const: "coeff (Const c) m = (if m = 0 then (c :: 'a :: comm_semiring_1) else 0)"
  by (simp add: Const.rep_eq Const\<^sub>0_def coeff_def lookup_single_not_eq)

lemma coeff_Var: "coeff (Var x) m = (if m = monomial 1 x then 1 :: 'a :: comm_semiring_1 else 0)"
  by (simp add: Var.rep_eq Var\<^sub>0_def coeff_def lookup_single_not_eq)



text \<open>list-based representations, so that polynomials can be converted to first-order terms\<close>

lift_definition monom_list :: "'a :: comm_semiring_1 mpoly \<Rightarrow> (monom \<times> 'a) list"
  is "\<lambda> p. map (\<lambda> m. (m, lookup p m)) (sorted_list_of_set (keys p))" .

lift_definition var_list :: "monom \<Rightarrow> (var \<times> nat) list"
  is "\<lambda> m. map (\<lambda> x. (x, lookup m x)) (sorted_list_of_set (keys m))" .

lemma monom_list: "p = (\<Sum> (m, c) \<leftarrow> monom_list p. monom m c)" 
  apply transfer
  subgoal for p
    apply (subst poly_mapping_sum_monomials[symmetric])
    apply (subst distinct_sum_list_conv_Sum)
     apply (unfold distinct_map, simp add: inj_on_def)
     apply (meson in_keys_iff monomial_inj)
    apply (unfold set_map image_comp o_def split)
    apply (subst set_sorted_list_of_set, force)
    by (smt (verit, best) finite_keys lookup_eq_zero_in_keys_contradict monomial_inj o_def sum.cong sum.reindex_nontrivial)
  done

lemma monom_list_coeff: "(m,c) \<in> set (monom_list p) \<Longrightarrow> coeff p m = c" 
  unfolding coeff_def by (transfer, auto)

lemma monom_list_keys: "(m,c) \<in> set (monom_list p) \<Longrightarrow> keys m \<subseteq> vars p" 
  unfolding vars_def by (transfer, auto)


lemma var_list: "monom m c = Const (c :: 'a :: comm_semiring_1) * (\<Prod> (x, e) \<leftarrow> var_list m. (Var x)^e)" 
proof transfer
  fix m :: monom and c :: 'a
  have set: "set (sorted_list_of_set (keys m)) = keys m" 
    by (subst set_sorted_list_of_set, force+)
  have id: "(\<Prod>(x, y)\<leftarrow>map (\<lambda>x. (x, lookup m x)) (sorted_list_of_set (keys m)). Var\<^sub>0 x ^ y)
    = (\<Prod> x \<in> keys m. Var\<^sub>0 x ^ lookup m x)" (is "?r1 = ?r2")
    apply (unfold map_map o_def split)
    apply (subst prod.distinct_set_conv_list[symmetric])
    by auto
  have "monomial c m = Const\<^sub>0 c * monomial 1 m"
    by (simp add: Const\<^sub>0_one monomial_mp)
  also have "monomial (1 :: 'a) m = ?r1" unfolding id 
  proof (induction m rule: poly_mapping_induct)
    case (single k v)
    then show ?case by (auto simp: Var\<^sub>0_power mult_single)    
  next
    case (sum f g k v)
    have id: "monomial (1 :: 'a) (f + g) = monomial 1 f * monomial 1 g" 
      by (simp add: mult_single)
    have keys: "keys (f + g) = keys f \<union> keys g" "keys f \<inter> keys g = {}" 
       apply (intro keys_plus_ninv_comm_monoid_add) 
      using sum(3-4) by simp
    show ?case unfolding id sum(1-2) unfolding keys(1)
      apply (subst prod.union_disjoint, force, force, rule keys)
      apply (intro arg_cong2[of _ _ _ _ "(*)"] prod.cong refl)
       apply (insert keys(2), simp add: disjoint_iff in_keys_iff lookup_add)
      by (metis add_cancel_left_left disjoint_iff_not_equal in_keys_iff plus_poly_mapping.rep_eq)
  qed
  finally show "monomial c m = Const\<^sub>0 c * ?r1" .
qed

lemma var_list_keys: "(x,e) \<in> set (var_list m) \<Longrightarrow> x \<in> keys m" 
  by (transfer, auto)

lemma vars_substitute: assumes "\<And> x. vars (\<sigma> x) \<subseteq> V" 
  shows "vars (substitute \<sigma> p) \<subseteq> V" 
proof -
  define mcs where "mcs = monom_list p" 
  show ?thesis unfolding monom_list[of p, folded mcs_def]
  proof (induct mcs)
    case (Cons mc mcs)
    obtain m c where mc: "mc = (m,c)" by force
    define xes where "xes = var_list m" 
    have monom: "vars (substitute \<sigma> (monom m c)) \<subseteq> V" unfolding var_list[of m, folded xes_def]
    proof (induct xes)
      case (Cons xe xes)
      obtain x e where xe: "xe = (x,e)" by force
      from assms have "vars (\<sigma> x) \<subseteq> V" .
      hence x: "vars ((\<sigma> x)^e) \<subseteq> V" 
      proof (induct e)
        case (Suc e)
        then show ?case 
          by (simp, intro order.trans[OF vars_mult], auto)
      qed force
      have id: "substitute \<sigma> (Const c * (\<Prod>a\<leftarrow>xe # xes. case a of (x, a) \<Rightarrow> Var x ^ a))
        = \<sigma> x ^ e * (Const c * substitute \<sigma> (\<Prod>(x, y)\<leftarrow>xes. Var x ^ y))" unfolding xe
        by (simp add: ac_simps)
      show ?case unfolding id 
        apply (rule order.trans[OF vars_mult])
        using Cons x by auto
    qed force
    show ?case unfolding mc 
      apply simp
      apply (rule order.trans[OF vars_add])
      using monom Cons by auto
  qed force
qed

lemma insertion_monom_nonneg: assumes "\<And> x. \<alpha> x \<ge> 0" and c: "(c :: 'a :: {linordered_nonzero_semiring,ordered_semiring_0}) \<ge> 0" 
  shows "insertion \<alpha> (monom m c) \<ge> 0" 
proof -
  define xes where "xes = var_list m" 
  show ?thesis unfolding var_list[of m c, folded xes_def]
  proof (induct xes)
    case Nil
    thus ?case using c by (auto simp: insertion_Const)
  next
    case (Cons xe xes)
    obtain x e where xe: "xe = (x,e)" by force
    have id: "insertion \<alpha> (Const c * (\<Prod>a\<leftarrow>xe # xes. case a of (x, a) \<Rightarrow> Var x ^ a))
      = \<alpha> x ^ e * insertion \<alpha> (Const c * (\<Prod>a\<leftarrow>xes. case a of (x, a) \<Rightarrow> Var x ^ a))" 
      unfolding xe
      by (simp add: insertion_mult insertion_power insertion_Var algebra_simps)
    show ?case unfolding id
    proof (intro mult_nonneg_nonneg Cons)
      show "0 \<le> \<alpha> x ^ e" using assms(1)[of x]
        by (induct e, auto)
    qed
  qed
qed 

lemma insertion_nonneg: assumes "\<And> x. \<alpha> x \<ge> (0 :: 'a :: linordered_idom)" 
  and "\<And> m. coeff p m \<ge> 0"  
shows "insertion \<alpha> p \<ge> 0" 
proof -
  define mcs where "mcs = monom_list p" 
  from monom_list[of p] have p: "p = (\<Sum>(m, c)\<leftarrow> mcs. monom m c)" unfolding mcs_def by auto
  have mcs: "(m,c) \<in> set mcs \<Longrightarrow> c \<ge> 0" for m c 
    using monom_list_coeff assms(2) unfolding mcs_def by auto
  show ?thesis using mcs unfolding p
  proof (induct mcs)
    case Nil
    thus ?case by (auto simp: insertion_Const)
  next
    case (Cons mc mcs)
    obtain m c where mc: "mc = (m,c)" by force
    with Cons have "c \<ge> 0" by auto
    from insertion_monom_nonneg[OF assms(1) this]
    have m: "0 \<le> insertion \<alpha> (monom m c)" by auto
    from Cons(1)[OF Cons(2)] 
    have IH: "0 \<le> insertion \<alpha> (\<Sum>a\<leftarrow>mcs. case a of (a, b) \<Rightarrow> monom a b)" by force
    show ?case unfolding mc using IH m
      by (auto simp: insertion_add)
  qed
qed 

lemma vars_sumlist: "vars (sum_list ps) \<subseteq> \<Union> (vars ` set ps)" 
  by (induct ps, insert vars_add, auto)

lemma coefficients_of_linear_poly: assumes linear: "total_degree (p :: 'a :: comm_semiring_1 mpoly) \<le> 1"  
  shows "\<exists> c a vs. p = Const c + (\<Sum>i\<leftarrow>vs. Const (a i) * Var i)
     \<and> distinct vs \<and> set vs = vars p \<and> sorted_list_of_set (vars p) = vs \<and> (\<forall> v \<in> set vs. a v \<noteq> 0)
     \<and> (\<forall> i. a i = coeff p (monomial 1 i)) \<and> (c = coeff p 0)" 
proof -
  have sum_zero: "(\<And> x. x \<in> set xs \<Longrightarrow> x = 0) \<Longrightarrow> sum_list (xs :: 'a list) = 0" for xs by (induct xs, auto)
  define a :: "var \<Rightarrow> 'a" where "a i = coeff p (monomial 1 i)" for i
  define vs where "vs = sorted_list_of_set (vars p)" 
  define c where "c = coeff p 0" 
  define q where "q = Const c + (\<Sum>i\<leftarrow> vs. Const (a i) * Var i)" 
  show ?thesis
  proof (intro exI[of _ vs] exI[of _ a] exI[of _ c] conjI ballI vs_def[symmetric] c_def allI a_def, 
      unfold q_def[symmetric])
    show "set vs = vars p" and dist: "distinct vs" 
      using sorted_list_of_set[of "vars p", folded vs_def] vars_finite[of p] by auto    
    show "p = q" 
      unfolding coeff_eq[symmetric]
    proof (intro ext)
      fix m
      have "coeff q m = coeff (Const c) m + (\<Sum>x\<leftarrow>vs. a x * coeff (Var x) m)" 
        unfolding q_def coeff_add[symmetric] coeff_sum_list map_map o_def coeff_Const_mult ..
      also have "\<dots> = coeff p m" 
      proof (cases "m = 0")
        case True
        thus ?thesis by (simp add: coeff_Const coeff_Var monomial_0_iff c_def)
      next
        case False
        from False have "coeff (Const (coeff p 0)) m + (\<Sum>x\<leftarrow>vs. a x * coeff (Var x) m) 
        = (\<Sum>x\<leftarrow>vs. a x * coeff (Var x) m)" unfolding coeff_Const by simp
        also have "\<dots> = coeff p m" 
        proof (cases "\<exists> i \<in> set vs. m = monomial 1 i")
          case True
          then obtain i where i: "i \<in> set vs" and m: "m = monomial 1 i" by auto
          from split_list[OF i] obtain bef aft where id: "vs = bef @ i # aft" by auto
          from id dist have i: "i \<notin> set bef" "i \<notin> set aft" by auto
          have [simp]: "(monomial (Suc 0) i = monomial (Suc 0) j) = (i = j)" for i j :: var
            using monomial_inj by fastforce
          show ?thesis 
            apply (subst id, unfold coeff_Var m, simp)
            apply (subst sum_zero, use i in force)
            apply (subst sum_zero, use i in force)
            by (simp add: a_def)
        next
          case mon: False
          hence one: "(\<Sum>x\<leftarrow>vs. a x * coeff (Var x) m) = 0" 
            by (intro sum_zero, auto simp: coeff_Var)
          have two: "coeff p m = 0" 
          proof (rule ccontr)
            assume n0: "coeff p m \<noteq> 0" 
            show False
            proof (cases "\<exists> i. m = monomial 1 i")
              case True
              with mon obtain i where i: "i \<notin> set vs" and m: "m = monomial 1 i" by auto
              from n0 m have "i \<in> vars p" unfolding vars_def coeff_def 
                by (metis UN_I in_keys_iff lookup_single_eq one_neq_zero)
              with i \<open>set vs = vars p\<close> show False by auto
            next
              case False
              have "sum (lookup m) (keys m) \<le> total_degree p" using n0 unfolding coeff_def
                apply transfer
                by transfer (metis (no_types, lifting) Max_ge finite.insertI finite_imageI finite_keys image_eqI in_keys_iff insertCI)
              also have "\<dots> \<le> 1" using linear .
              finally have linear: "sum (lookup m) (keys m) \<le> 1" by auto
              consider (single) x where "keys m = {x}" | (null) "keys m = {}" | 
                (two) x y k where "keys m = {x,y} \<union> k" and "x \<noteq> y" by blast
              thus False
              proof cases
                case null
                hence "m = 0" by simp
                with \<open>m \<noteq> 0\<close> show False by simp
              next
                case (single x)
                with linear have "lookup m x \<le> 1" by auto
                moreover from single have nz: "lookup m x \<noteq> 0"
                  by (metis in_keys_iff insertI1)
                ultimately have "lookup m x = 1" by auto
                with single have "m = monomial 1 x"
                  by (metis Diff_cancel Diff_eq_empty_iff keys_subset_singleton_imp_monomial)
                with False show False by auto
              next
                case (two x y k)
                define k' where "k' = k - {x,y}" 
                have "keys m = insert x (insert y k')" "x \<noteq> y" "x \<notin> k'" "y \<notin> k'" "finite k'" 
                  unfolding k'_def using two finite_keys[of m] by auto
                hence "lookup m x + lookup m y \<le> sum (lookup m) (keys m)" by simp
                also have "\<dots> \<le> 1" by fact
                finally have "lookup m x = 0 \<or> lookup m y = 0" by auto
                with two show False by blast
              qed
            qed
          qed
          from one two show ?thesis by simp
        qed
        finally show ?thesis by (simp add: c_def)
      qed
      finally show "coeff p m = coeff q m" ..
    qed
  
    fix v
    assume v: "v \<in> set vs" 
    hence "v \<in> vars p" using \<open>set vs = vars p\<close> by auto
    hence vq: "v \<in> vars q" unfolding \<open>p = q\<close> .
    from split_list[OF v] obtain bef aft where vs: "vs = bef @ v # aft" by auto
    with dist have vba: "v \<notin> set bef" "v \<notin> set aft" by auto
    show "a v \<noteq> 0" 
    proof
      assume a0: "a v = 0" 
      have "v \<in> vars p" by fact
      also have "p = q" by fact
      also have "vars q \<subseteq> vars (sum_list (map (\<lambda> x. Const (a x) * Var x) bef)) \<union> 
         vars (Const (a v) * Var v)
         \<union> vars (sum_list (map (\<lambda> x. Const (a x) * Var x) aft))" 
        unfolding q_def vs apply simp
        apply (rule order.trans[OF vars_add], simp)
        apply (rule order.trans[OF vars_add])
        by (insert vars_add, blast)
      also have "vars (Const (a v) * Var v) = {}" unfolding a0 Const_0 by simp
      finally obtain list where v: "v \<in> vars (sum_list (map (\<lambda> x. Const (a x) * Var x) list))"   
        and not_v: "v \<notin> set list" using vba by auto
      from set_mp[OF vars_sumlist v] obtain x where "x \<in> set list" and "v \<in> vars (Const (a x) * Var x)" 
        by auto
      with vars_mult[of "Const (a x)" "Var x"] not_v show False by auto
    qed
  qed
qed

text \<open>Introduce notion for degree of monom\<close>
definition degree_monom :: "(var \<Rightarrow>\<^sub>0 nat) \<Rightarrow> nat" where
  "degree_monom m = sum (lookup m) (keys m)" 

lemma total_degree_alt_def: "total_degree p = Max (insert 0 (degree_monom ` keys (mapping_of p)))"
  unfolding degree_monom_def
  by transfer' simp

lemma degree_monon_le_total_degree: assumes "coeff p m \<noteq> 0" 
  shows "degree_monom m \<le> total_degree p"
  using assms unfolding total_degree_alt_def by (simp add: coeff_keys)

lemma degree_monom_eq_total_degree: assumes "p \<noteq> 0" 
  shows "\<exists> m. coeff p m \<noteq> 0 \<and> degree_monom m = total_degree p" 
proof (cases "total_degree p = 0")
  case False
  thus ?thesis unfolding total_degree_alt_def
    by (metis (full_types) Max_in coeff_keys empty_not_insert finite_imageI finite_insert finite_keys image_iff insertE)
next  
  case True
  from assms obtain m where "coeff p m \<noteq> 0"
    using coeff_all_0 by auto
  with degree_monon_le_total_degree[OF this] True show ?thesis by auto
qed

lemma degree_add_leI: "degree p x \<le> d \<Longrightarrow> degree q x \<le> d \<Longrightarrow> degree (p + q) x \<le> d"  
  apply transfer
  subgoal for p x d q using Poly_Mapping.keys_add[of p q]
    by (intro Max.boundedI, auto)
  done

lemma degree_sum_leI: assumes "\<And> i. i \<in> A \<Longrightarrow> degree (p i) x \<le> d" 
  shows "degree (sum p A) x \<le> d" 
  using assms 
  by (induct A rule: infinite_finite_induct, auto intro: degree_add_leI)

lemma total_degree_sum_leI: assumes "\<And> i. i \<in> A \<Longrightarrow> total_degree (p i) \<le> d" 
  shows "total_degree (sum p A) \<le> d" 
  using assms 
  by (induct A rule: infinite_finite_induct, auto intro: total_degree_add)

lemma total_degree_monom: assumes "c \<noteq> 0"  
  shows "total_degree (monom m c) = degree_monom m"
  unfolding total_degree_alt_def using assms by auto

lemma degree_Var[simp]: "degree (Var x :: 'a :: comm_semiring_1 mpoly) x = 1" 
  by (transfer, unfold Var\<^sub>0_def, simp)

lemma Var_neq_0[simp]: "Var x \<noteq> (0 :: 'a :: comm_semiring_1 mpoly)" 
proof
  assume "Var x = (0 :: 'a mpoly)" 
  from arg_cong[OF this, of "\<lambda> p. degree p x"]
  show False by simp
qed

lemma degree_Const[simp]: "degree (Const c) x = 0" 
  by transfer (auto simp: Const\<^sub>0_def)

lemma vars_add_subI: "vars p \<subseteq> A \<Longrightarrow> vars q \<subseteq> A \<Longrightarrow> vars (p + q) \<subseteq> A" 
  by (metis le_supI subset_trans vars_add)

lemma vars_mult_subI: "vars p \<subseteq> A \<Longrightarrow> vars q \<subseteq> A \<Longrightarrow> vars (p * q) \<subseteq> A" 
  by (metis le_supI subset_trans vars_mult)

lemma vars_eqI: assumes "vars (p :: 'a :: comm_ring_1 mpoly) \<subseteq> V"
  "\<And> v. v \<in> V \<Longrightarrow> \<exists> a b. insertion a p \<noteq> insertion (a(v := b)) p" 
shows "vars p = V" 
proof (rule ccontr)
  assume "\<not> ?thesis" 
  with assms obtain v where "v \<in> V" and not: "v \<notin> vars p" by auto
  from assms(2)[OF this(1)] obtain a b where "insertion a p \<noteq> insertion (a(v := b)) p" by auto
  moreover have "insertion a p = insertion (a(v := b)) p" 
    by (rule insertion_irrelevant_vars, insert not, auto) 
  ultimately show False by auto
qed


end