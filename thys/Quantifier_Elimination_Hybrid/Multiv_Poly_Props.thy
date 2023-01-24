(* This file includes useful properties of multivariate polynomials.
 *)

theory Multiv_Poly_Props
  imports
    "HOL-Computational_Algebra.Computational_Algebra"
    "Polynomial_Interpolation.Ring_Hom_Poly"
    "Virtual_Substitution.ExecutiblePolyProps"
    "Sturm_Tarski.Pseudo_Remainder_Sequence"
    (* We use this entry for the mpoly, mpoly poly connection *)
    "Factor_Algebraic_Polynomial.Poly_Connection"
    "Virtual_Substitution.VSQuad"

begin


section "Some definitions for lists of polynomials"

abbreviation lead_coeffs:: "'a::zero Polynomial.poly list \<Rightarrow> 'a list"
  where "lead_coeffs p_list \<equiv> map Polynomial.lead_coeff p_list"

definition coeffs_list:: "'a::zero Polynomial.poly list \<Rightarrow> 'a list"
  where "coeffs_list p_list \<equiv> concat (map Polynomial.coeffs p_list)"

value "lead_coeffs [[:((Var 0 +(Const (3::real))*((Var 1)^2)):: real mpoly), 0, (1::real mpoly):]]"

abbreviation degrees:: "'a::zero Polynomial.poly list \<Rightarrow> nat list"
  where "degrees polys \<equiv> map Polynomial.degree polys"

value "degrees [[:((Var 0 +(Const (3::real))*((Var 1)^2)):: real mpoly), 0, (1::real mpoly):]]"

fun variables:: "real mpoly list \<Rightarrow> nat set"
  where "variables [] = {}"
  | "variables (h#T) = (vars h) \<union> (variables T)"

fun variables_list:: "real mpoly list \<Rightarrow> nat list"
  where "variables_list qs = sorted_list_of_set (variables qs)"

lemma variables_prop:
  shows "v \<in> variables qs \<longleftrightarrow> (\<exists>q \<in> set qs. v \<in> vars q)"
proof (induct qs)
  case Nil
  then show ?case by auto
next
  case (Cons a qs)
  then show ?case by simp
qed

lemma variables_finite:
  shows "finite (variables qs)"
proof (induct qs)
  case Nil
  then show ?case by auto
next
  case (Cons a qs)
  then show ?case
    by (simp add: vars_finite) 
qed

lemma variables_list_prop:
  shows "v \<in> set (variables_list qs) \<longleftrightarrow> (\<exists>q \<in> set qs. v \<in> vars q)"
  using variables_finite
  by (simp add: member_def variables_prop) 

section "Evaluating multivariate polynomials" 

definition eval_mpoly:: "real list \<Rightarrow> real mpoly \<Rightarrow> real"
  where "eval_mpoly L p = insertion (nth_default 0 L) p"

value "eval_mpoly [4, 1, 2] ((Var 0 +(Const (3::real))*((Var 1)^2)):: real mpoly)"

definition eval_mpoly_poly:: "real list \<Rightarrow> real mpoly Polynomial.poly \<Rightarrow> real Polynomial.poly"
  where "eval_mpoly_poly L p = map_poly (eval_mpoly L) p"

lemma eval_mpoly_poly_coeff1: "n \<le> Polynomial.degree (eval_mpoly_poly L p) \<Longrightarrow> Polynomial.coeff (eval_mpoly_poly L p) n = eval_mpoly L (Polynomial.coeff p n)"
  unfolding eval_mpoly_poly_def
  by (simp add: coeff_map_poly eval_mpoly_def) 

lemma eval_mpoly_poly_coeff2: "\<forall>n > Polynomial.degree (eval_mpoly_poly L p). Polynomial.coeff (eval_mpoly_poly L p) n = 0"
  using coeff_eq_0 by auto 

value "eval_mpoly_poly [4, 1, 2] [:((Var 0 +(Const (3::real))*((Var 1)^2)):: real mpoly), 0, (1::real mpoly):]"

definition eval_mpoly_poly_list:: "real list \<Rightarrow> real mpoly Polynomial.poly list \<Rightarrow> real Polynomial.poly list"
  where "eval_mpoly_poly_list L p_list = map (\<lambda>x. (eval_mpoly_poly L x)) p_list"

interpretation eval_mpoly_map_poly_comm_ring_hom: map_poly_comm_ring_hom "eval_mpoly val"
  apply (unfold_locales)
  by (auto simp add: eval_mpoly_def insertion_add insertion_mult)

interpretation eval_mpoly_map_poly_idom_hom: map_poly_idom_hom "eval_mpoly val"..

interpretation eval_mpoly_poly_comm_ring_hom: comm_ring_hom "eval_mpoly_poly val"
  apply unfold_locales
     apply (auto simp add: eval_mpoly_poly_def)
  using eval_mpoly_map_poly_comm_ring_hom.base.map_poly_hom_add apply force
  using eval_mpoly_map_poly_comm_ring_hom.hom_mult by auto

interpretation eval_mpoly_poly_map_poly_idom_hom: map_poly_idom_hom "eval_mpoly_poly val"..

section "Removing highest degree monomial"

definition one_less_degree:: "real mpoly Polynomial.poly \<Rightarrow> real mpoly Polynomial.poly"
  where "one_less_degree p = p - Polynomial.monom (Polynomial.lead_coeff p) (Polynomial.degree p)"

lemma one_less_degree_degree:
  assumes "Polynomial.degree p > 0"
  shows "Polynomial.degree(one_less_degree p) < Polynomial.degree p"
proof -
  obtain q where q:"Polynomial.degree p = Suc q"
    using assms not0_implies_Suc by blast
  from poly_as_sum_of_monoms[of p]
  have p_is: "p = (\<Sum>i\<le>q. Polynomial.monom (poly.coeff p i) i) + Polynomial.monom (Polynomial.lead_coeff p) (Polynomial.degree p)"
    by (simp add: q)
  then have e: "p - Polynomial.monom (Polynomial.lead_coeff p) (Polynomial.degree p) = (\<Sum>i\<le>q. Polynomial.monom (poly.coeff p i) i)"
    using diff_eq_eq by blast
  show ?thesis unfolding one_less_degree_def e
    by (smt (z3) Polynomial.coeff_diff Polynomial.lead_coeff_monom Zero_not_Suc p_is cancel_comm_monoid_add_class.diff_cancel degree_0 degree_add_eq_left degree_monom_eq e leading_coeff_0_iff linorder_neqE_nat q)
qed

lemma sublist_prefix_property:
  assumes "length og_list \<ge> length sub_list"
  assumes "\<forall>i < length sub_list. sub_list ! i = og_list ! i"
  shows "Sublist.prefix sub_list og_list"
  using assms
proof (induct "length sub_list" arbitrary: sub_list)
  case 0
  then show ?case by auto
next
  case (Suc x)
  then have "\<exists>a l. sub_list = append l [a]"
    by (metis length_greater_0_conv rev_exhaust zero_less_Suc)
  then obtain a l where al_prop: "sub_list = append l [a]" 
    by auto
  then have length_l: "List.length l = x"
    using Suc.hyps(2) by auto
  then have "prefix l og_list"
    by (metis Suc.hyps(1) Suc.hyps(2) Suc.prems(1) Suc.prems(2) Suc_leD al_prop butlast_snoc lessI nth_butlast order.strict_trans)   
  then have "\<exists>t. og_list = l @ t"
    using prefix_def by blast
  then obtain t where t_prop: "og_list = l @ t" by auto
  then have t_first: "og_list ! (length sub_list - 1) = (t ! 0)"
    by (metis Suc.hyps(2) diff_Suc_1 diff_self_eq_0 length_l less_irrefl nth_append)
  have "sub_list ! (length sub_list - 1) = a"
    using al_prop
    by fastforce 
  then have "og_list ! (length sub_list - 1) = a"
    using Suc.hyps(2) Suc.prems by fastforce
  then have t_zero: "t ! 0 = a"
    using t_prop t_first by auto
  have "length l = length sub_list - 1"
    using Suc.hyps(2) length_l by presburger
  then have "length t > 0"
    using assms
    by (metis Suc.hyps(2) Suc.prems(1) append.right_neutral bot_nat_0.not_eq_extremum diff_is_0_eq length_0_conv length_l lessI t_prop zero_less_diff) 
  then have "\<exists>t1. t = a # t1"
    using t_zero
    by (metis length_0_conv less_nat_zero_code list.exhaust nth_Cons_0) 
  then show ?case
    using t_prop al_prop
    by force 
qed

lemma one_less_degree_is_prefix:
  assumes "Polynomial.degree q > 0"
  shows "Sublist.prefix (Polynomial.coeffs (one_less_degree q)) (Polynomial.coeffs q)"
proof - 
  let ?sub_list = "Polynomial.coeffs (Multiv_Poly_Props.one_less_degree q)"
  have "\<forall>i < length ?sub_list. Polynomial.coeff (one_less_degree q) i = Polynomial.coeff q i"
    by (metis (no_types, lifting) Multiv_Poly_Props.one_less_degree_def Polynomial.coeff_diff Polynomial.coeff_monom assms coeffs_eq_Nil diff_zero length_0_conv length_coeffs_degree less_Suc_eq_0_disj not_less_eq one_less_degree_degree)
  then have "\<forall>i < length ?sub_list. ?sub_list ! i = (Polynomial.coeffs q) ! i"
    unfolding Polynomial.coeffs_def
    by (smt (verit, ccfv_SIG) add_0 assms degree_0 diff_zero length_map length_upt less_Suc_eq less_nat_zero_code list.size(3) nth_map_upt one_less_degree_degree order.strict_trans) 
  then show ?thesis
    using sublist_prefix_property assms
    by (smt (verit, del_insts) Suc_mono bot_nat_0.not_eq_extremum coeffs_eq_Nil degree_0 length_coeffs_degree less_imp_le_nat list.size(3) one_less_degree_degree order_less_subst1)
qed

lemma one_less_degree_is_strict_prefix:
  assumes "Polynomial.degree q > 0"
  shows "Sublist.strict_prefix (Polynomial.coeffs (Multiv_Poly_Props.one_less_degree q)) (Polynomial.coeffs q)"
proof -
  have "length (Polynomial.coeffs (Multiv_Poly_Props.one_less_degree q)) < length (Polynomial.coeffs q)"
    using one_less_degree_degree[of q] 
      assms
    by (metis coeffs_0_eq_Nil degree_0 length_coeffs_degree less_nat_zero_code list.size(3) not_less_eq) 
  then show ?thesis
    using one_less_degree_is_prefix assms
    by (metis less_irrefl_nat prefix_order.order_iff_strict) 
qed

lemma coeff_one_less_degree_var:
  assumes "0 < Polynomial.degree p"
  assumes "one_less_degree p \<noteq> 0"
  shows "i \<le> Polynomial.degree (one_less_degree p) \<Longrightarrow>
      poly.coeff p i = poly.coeff (one_less_degree p) i"
proof - 
  fix i
  assume i_leq: "i \<le> Polynomial.degree (one_less_degree p)"
  then have i_lt: "i < length (Polynomial.coeffs (Multiv_Poly_Props.one_less_degree p))"
    unfolding Polynomial.coeffs_def using assms by auto
  have i_lt2: "i < (Polynomial.degree p)"
    using i_leq one_less_degree_degree[of p] assms(1) by auto
  have len_map1: "length (map (poly.coeff p) [0..<Suc (Polynomial.degree p)]) = Polynomial.degree p + 1"
    by auto
  have len_map2: "length (Polynomial.coeffs (Multiv_Poly_Props.one_less_degree p))
    = Polynomial.degree (one_less_degree p) + 1"
    unfolding Polynomial.coeffs_def using assms(2) by auto
  have "p \<noteq> 0" 
    using assms(1) by auto
  then have same_coeff: "poly.coeff p i = (Polynomial.coeffs) p ! i"
    unfolding  Polynomial.coeffs_def using assms i_lt2 len_map1
    by (smt (verit, best) Suc_eq_plus1 add_0 le_simps(2) length_map less_imp_le_nat nth_map nth_upt)
  obtain zs where zs_prop: "Polynomial.coeffs p =
         (Polynomial.coeffs (Multiv_Poly_Props.one_less_degree p)) @ zs"
    using assms i_leq one_less_degree_is_prefix[of p] unfolding prefix_def
    by auto
  have same_coeff_2: "((Polynomial.coeffs (Multiv_Poly_Props.one_less_degree p)) @ zs) ! i = 
    (Polynomial.coeffs (one_less_degree p)) ! i"
    using i_lt
    by (simp add: nth_append)        
  show "poly.coeff p i = poly.coeff (one_less_degree p) i"
    using same_coeff same_coeff_2 zs_prop
    by (simp add: i_lt nth_coeffs_coeff) 
qed


lemma coeff_one_less_degree:
  assumes "one_less_degree p \<noteq> 0"
  shows "i \<le> Polynomial.degree (one_less_degree p) \<Longrightarrow>
      poly.coeff p i = poly.coeff (one_less_degree p) i"
proof - 
  have "Polynomial.degree p > 0"
    using assms
    by (metis (no_types, lifting) Multiv_Poly_Props.one_less_degree_def Polynomial.coeff_diff Polynomial.coeff_monom diff_zero eq_iff_diff_eq_0 eq_iff_diff_eq_0 le_degree leading_coeff_0_iff linorder_not_less zero_less_iff_neq_zero) 
  then show "\<And>i. i \<le> Polynomial.degree (one_less_degree p) \<Longrightarrow>
      poly.coeff p i = poly.coeff (one_less_degree p) i"
    using coeff_one_less_degree_var assms
    by auto
qed

lemma coeff_one_less_degree_subset:
  assumes "one_less_degree q \<noteq> 0"
  shows "set (Polynomial.coeffs (Multiv_Poly_Props.one_less_degree q)) \<subseteq> set (Polynomial.coeffs q)"
proof clarsimp
  fix x
  assume "x \<in> set (Polynomial.coeffs (Multiv_Poly_Props.one_less_degree q))"
  then obtain i where i_prop: "i \<le> Polynomial.degree (one_less_degree q)"
    "x = poly.coeff (one_less_degree q) i"
    unfolding Polynomial.coeffs_def using assms
    using atMost_upto by auto
  have "Polynomial.degree q > 0"
    using assms 
    by (metis (no_types, lifting) Multiv_Poly_Props.one_less_degree_def Polynomial.coeff_diff Polynomial.coeff_monom diff_zero eq_iff_diff_eq_0 eq_iff_diff_eq_0 le_degree leading_coeff_0_iff linorder_not_less zero_less_iff_neq_zero) 
  then show "x \<in> set (Polynomial.coeffs q)"
    using coeff_one_less_degree assms i_prop
    unfolding Polynomial.coeffs_def using one_less_degree_degree
    by (smt (verit, best) Polynomial.coeffs_def coeff_in_coeffs degree_0 le_trans less_imp_le_nat less_numeral_extra(3))
qed

lemma coeffs_between_one_less_degree:
  assumes "0 < Polynomial.degree p"
  assumes igt: "i > Polynomial.degree (one_less_degree p)"
  assumes ilt: "i < Polynomial.degree p"
  shows "poly.coeff p i = 0"
  using assms
  using Multiv_Poly_Props.one_less_degree_def coeff_eq_0 by fastforce 

lemma poly_p_altdef_one_less_degree:
  assumes deg_gt: "Polynomial.degree p > 0"
  assumes deg_is: "Polynomial.degree p = d"
  shows "poly p x = (\<Sum>i\<le>Polynomial.degree (one_less_degree p). Polynomial.coeff (one_less_degree p) i * x ^ i) 
      + (Polynomial.coeff p d)*(x^d)"
proof - 
  let ?lp = "(one_less_degree p)"
  let ?deg_lp = "Polynomial.degree ?lp"
  have "poly p x = (\<Sum>i\<le>d. Polynomial.coeff p i * x ^ i)"
    using assms poly_altdef by auto
  then have p_is: "poly p x = (\<Sum>i\<le>(d - 1). Polynomial.coeff p i * x ^ i) + (Polynomial.coeff p d)*(x^d)"
    using deg_gt
    by (metis (no_types, lifting) One_nat_def Suc_pred assms(2) sum.atMost_Suc) 
  have well_def: "?deg_lp \<le> d - 1"
    using one_less_degree_degree deg_gt deg_is 
    by (metis One_nat_def Suc_pred less_Suc_eq_le)
  then have sum1: "(\<Sum>i\<le>(d - 1). Polynomial.coeff p i * x ^ i) = (\<Sum>i\<le>Polynomial.degree ?lp. Polynomial.coeff p i * x ^ i)"
  proof - 
    have "\<And>i. (i > Polynomial.degree ?lp \<and> i \<le> d - 1) \<Longrightarrow> Polynomial.coeff p i = 0"
      using deg_is coeffs_between_one_less_degree
      by (metis One_nat_def Suc_pred deg_gt less_Suc_eq_le) 
    then show ?thesis using well_def
    proof (induct "d - 1 - ?deg_lp" arbitrary: d)
      case 0
      then show ?case 
        by (metis (no_types, lifting) diff_is_0_eq le_antisym) 
    next
      case (Suc xa)
      then have sum: "(\<Sum>i\<le>d - 1. poly.coeff p i * x ^ i) =
      (\<Sum>i\<le>d - 2. poly.coeff p i * x ^ i) + (poly.coeff p (d-1) * x ^ (d-1))"
        using  Nat.diff_diff_right One_nat_def Suc_le_mono Suc_pred add_diff_cancel_right' bot_nat_0.not_eq_extremum diff_is_0_eq le_numeral_extra(4) nat_1_add_1 sum.atMost_Suc zero_le
        by (smt (verit, del_insts))
      have h0: " xa = d - 1 - 1 - Polynomial.degree (Multiv_Poly_Props.one_less_degree p)"
        using Suc.hyps(2) by auto
      have h1: "(\<And>i. Polynomial.degree (Multiv_Poly_Props.one_less_degree p) < i \<and>
          i \<le> d - 1 - 1 \<Longrightarrow>
          poly.coeff p i = 0)"
        using Suc.prems(1) by auto
      have h2: "Polynomial.degree (Multiv_Poly_Props.one_less_degree p) \<le> d - 1 - 1"
        using Suc.prems Suc.hyps(2) by auto 
      have eq1: "(\<Sum>i\<le>d - 2. poly.coeff p i * x ^ i) = (\<Sum>i\<le>Polynomial.degree ?lp. Polynomial.coeff p i * x ^ i)"
        using Suc.hyps(1)[OF h0 h1 h2]
        by (metis (no_types, lifting) diff_diff_left one_add_one) 
      have dgt: "d - 1 > Polynomial.degree (one_less_degree p)"
        using Suc.prems Suc.hyps(2) by auto
      have eq2: "poly.coeff p (d-1) = 0"
        using Suc.prems
        using dgt by blast 
      then show ?case using sum eq1 eq2 
        by fastforce
    qed
  qed
  have sum2: "(\<Sum>i\<le>Polynomial.degree (one_less_degree p). Polynomial.coeff p i * x ^ i)
= (\<Sum>i\<le>Polynomial.degree (one_less_degree p). Polynomial.coeff (one_less_degree p) i * x ^ i)"
    using coeff_one_less_degree
    by (smt (verit, del_insts) Multiv_Poly_Props.one_less_degree_def Polynomial.coeff_monom atMost_iff bot_nat_0.extremum_uniqueI deg_gt degree_0 eq_iff_diff_eq_0 leading_coeff_0_iff nat_neq_iff sum.cong) 
  then show ?thesis
    using p_is sum1 sum2 
    by presburger
qed

section "Expressing as univariate"

definition transform:: "real mpoly list \<Rightarrow> real mpoly Polynomial.poly list"
  where "transform qs = (let vs = variables_list qs in
   map (\<lambda>q. (mpoly_to_mpoly_poly (nth vs (length vs - 1)) q)) qs)"

definition mpoly_to_mpoly_poly_alt :: "nat \<Rightarrow> 'a :: comm_ring_1 mpoly \<Rightarrow> 'a mpoly Polynomial.poly" where
  "mpoly_to_mpoly_poly_alt x p = (\<Sum>i\<in>{0..MPoly_Type.degree p x} .
        Polynomial.monom (isolate_variable_sparse p x i) i)" 

definition univariate_in:: "real mpoly list \<Rightarrow> nat \<Rightarrow> real mpoly Polynomial.poly list"
  where "univariate_in qs i =  map (mpoly_to_mpoly_poly_alt i) qs"

lemma degree_less_sum_max: 
  shows "MPoly_Type.degree (p+q) var \<le> max (MPoly_Type.degree p var) (MPoly_Type.degree q var)"
  by (simp add: degree_add_leq)

lemma mpoly_to_mpoly_poly_alt_sum_aux :
  shows "(\<Sum>i = 0..b.
        Polynomial.monom (isolate_variable_sparse (p + q) x i) i) =
    (\<Sum>i = 0..b. Polynomial.monom (isolate_variable_sparse p x i) i) +
    (\<Sum>i = 0..b. Polynomial.monom (isolate_variable_sparse q x i) i)"
proof (induct b)
  case 0
  then show ?case using isovarspar_sum[of p q x 0]
    by (simp add: add_monom)
next
  case (Suc x)
  then show ?case 
    using isovarspar_sum[of p q x "Suc x"]
  proof -
    have f1: "(\<Sum>n = 0..x. Polynomial.monom (isolate_variable_sparse (p + q) x n) n) = (\<Sum>n = 0..x. Polynomial.monom (isolate_variable_sparse p x n) n + Polynomial.monom (isolate_variable_sparse q x n) n)"
      by (simp add: isovarspar_sum monom_hom.hom_add)
    have "Polynomial.monom (isolate_variable_sparse (p + q) x (Suc x)) (Suc x) = Polynomial.monom (isolate_variable_sparse p x (Suc x)) (Suc x) + Polynomial.monom (isolate_variable_sparse q x (Suc x)) (Suc x)"
      by (simp add: add_monom isovarspar_sum)
    then have "(\<Sum>n = 0..x. Polynomial.monom (isolate_variable_sparse (p + q) x n) n) + Polynomial.monom (isolate_variable_sparse (p + q) x (Suc x)) (Suc x) = (\<Sum>n = 0..x. Polynomial.monom (isolate_variable_sparse p x n) n + Polynomial.monom (isolate_variable_sparse q x n) n) + (Polynomial.monom (isolate_variable_sparse p x (Suc x)) (Suc x) + Polynomial.monom (isolate_variable_sparse q x (Suc x)) (Suc x))"
      using f1 by presburger
    then have "(\<Sum>n = 0..Suc x. Polynomial.monom (isolate_variable_sparse (p + q) x n) n) = (\<Sum>n = 0..x. Polynomial.monom (isolate_variable_sparse p x n) n + Polynomial.monom (isolate_variable_sparse q x n) n) + (Polynomial.monom (isolate_variable_sparse p x (Suc x)) (Suc x) + Polynomial.monom (isolate_variable_sparse q x (Suc x)) (Suc x))"
      by (smt (z3) sum.atLeast0_atMost_Suc)
    then have "(\<Sum>n = 0..Suc x. Polynomial.monom (isolate_variable_sparse (p + q) x n) n) = (\<Sum>n = 0..Suc x. Polynomial.monom (isolate_variable_sparse p x n) n + Polynomial.monom (isolate_variable_sparse q x n) n)"
      by (smt (z3) sum.atLeast0_atMost_Suc)
    then show ?thesis
      by (smt (z3) Suc add_monom isovarspar_sum sum.atLeast0_atMost_Suc sum.distrib)
  qed 
qed

lemma isovar_sum_to_higher_degree:
  assumes "b \<ge> (MPoly_Type.degree p x)"
  shows "(\<Sum>i = 0..(MPoly_Type.degree p x). Polynomial.monom (isolate_variable_sparse p x i) i) = 
 (\<Sum>i = 0..b. Polynomial.monom (isolate_variable_sparse p x i) i)"
  using assms
proof (induct b) 
  case 0
  then show ?case
    by auto
next
  case (Suc b)
  then show ?case using isovar_greater_degree
    by (smt (z3) Orderings.order_eq_iff add.commute add_0 isolate_variable_sparse_ne_zeroD le_SucE monom_hom.hom_zero sum.atLeast0_atMost_Suc)
qed

lemma mpoly_to_mpoly_poly_alt_sum :
  shows "mpoly_to_mpoly_poly_alt x (p+q) = (mpoly_to_mpoly_poly_alt x p) + (mpoly_to_mpoly_poly_alt x q)"
proof -
  let ?deg = "max (MPoly_Type.degree p x) (MPoly_Type.degree q x)"
  have "(\<Sum>i = 0..MPoly_Type.degree (p + q) x.
        Polynomial.monom (isolate_variable_sparse (p + q) x i) i) =
    (\<Sum>i = 0..MPoly_Type.degree p x. Polynomial.monom (isolate_variable_sparse p x i) i) +
    (\<Sum>i = 0..MPoly_Type.degree q x. Polynomial.monom (isolate_variable_sparse q x i) i)"
  proof (induct ?deg arbitrary: p q)
    case 0
    then have "MPoly_Type.degree (p + q) x = 0 \<and> MPoly_Type.degree p x = 0 \<and> MPoly_Type.degree q x = 0"
      using degree_add_leq[of p x 0 q]
      by (metis le_zero_eq max.cobounded1 max.cobounded2)  
    then show ?case 
      using isovarspar_sum[of p q x]
      by (simp add: add_monom) 
  next
    case (Suc xa)
    let ?deg_sum = "MPoly_Type.degree (p+q) x"
    let ?deg_p = "(MPoly_Type.degree p x)"
    let ?deg_q = "(MPoly_Type.degree q x)"
    have "?deg_sum = max ?deg_p ?deg_q \<or> ?deg_sum < max ?deg_p ?deg_q"
      using degree_less_sum_max[of p q x] by auto
    moreover {
      assume *: "?deg_sum = max ?deg_p ?deg_q"
      have eq1: "(\<Sum>i = 0..?deg_p. Polynomial.monom (isolate_variable_sparse p x i) i) = 
 (\<Sum>i = 0..?deg_sum. Polynomial.monom (isolate_variable_sparse p x i) i)
" using * isovar_sum_to_higher_degree
        by (simp add: isovar_sum_to_higher_degree) 
      have eq2: "(\<Sum>i = 0..?deg_q. Polynomial.monom (isolate_variable_sparse q x i) i) = 
 (\<Sum>i = 0..?deg_sum. Polynomial.monom (isolate_variable_sparse q x i) i)" 
        using * isovar_sum_to_higher_degree
        by (simp add: isovar_sum_to_higher_degree) 
      then have "(\<Sum>i = 0..?deg_sum.
              Polynomial.monom (isolate_variable_sparse (p + q) x i) i) =
          (\<Sum>i = 0..?deg_p. Polynomial.monom (isolate_variable_sparse p x i) i) +
          (\<Sum>i = 0..?deg_q. Polynomial.monom (isolate_variable_sparse q x i) i)"
        by (simp add: eq1 eq2 mpoly_to_mpoly_poly_alt_sum_aux) 
    }
    moreover {
      assume *: "?deg_sum < max ?deg_p ?deg_q"
      let ?mx = "max ?deg_p ?deg_q"
      have eq1: "(\<Sum>i = 0..?deg_p. Polynomial.monom (isolate_variable_sparse p x i) i) = 
 (\<Sum>i = 0..?mx. Polynomial.monom (isolate_variable_sparse p x i) i)
" using * isovar_sum_to_higher_degree
        by (simp add: isovar_sum_to_higher_degree) 
      have eq2: "(\<Sum>i = 0..?deg_q. Polynomial.monom (isolate_variable_sparse q x i) i) = 
 (\<Sum>i = 0..?mx. Polynomial.monom (isolate_variable_sparse q x i) i)" 
        using * isovar_sum_to_higher_degree
        by (simp add: isovar_sum_to_higher_degree) 
      have eq3: "(\<Sum>i = 0..?deg_sum. Polynomial.monom (isolate_variable_sparse (p + q) x i) i) = 
      (\<Sum>i = 0..?mx. Polynomial.monom (isolate_variable_sparse (p + q) x i) i)" 
        using * isovar_sum_to_higher_degree
        by (simp add: isovar_sum_to_higher_degree) 
      then have "(\<Sum>i = 0..?deg_sum.
              Polynomial.monom (isolate_variable_sparse (p + q) x i) i) =
          (\<Sum>i = 0..?deg_p. Polynomial.monom (isolate_variable_sparse p x i) i) +
          (\<Sum>i = 0..?deg_q. Polynomial.monom (isolate_variable_sparse q x i) i)"
        using mpoly_to_mpoly_poly_alt_sum_aux eq1 eq2 eq3
        by auto
    }
    ultimately have  "(\<Sum>i = 0..?deg_sum.
              Polynomial.monom (isolate_variable_sparse (p + q) x i) i) =
          (\<Sum>i = 0..?deg_p. Polynomial.monom (isolate_variable_sparse p x i) i) +
          (\<Sum>i = 0..?deg_q. Polynomial.monom (isolate_variable_sparse q x i) i)"
      by fastforce
    then show ?case
      by fastforce 
  qed
  then show ?thesis
    by (simp add: mpoly_to_mpoly_poly_alt_def) 
qed

lemma multivar_as_univar: "mpoly_to_mpoly_poly_alt x p = mpoly_to_mpoly_poly x p"
proof (induct p rule: mpoly_induct)
  case (monom m a)
  have "a = 0 \<or> a \<noteq> 0" by auto
  moreover {
    assume *: "a = 0"
    then have " mpoly_to_mpoly_poly_alt x (MPoly_Type.monom m a) =
           mpoly_to_mpoly_poly x (MPoly_Type.monom m a)" 
      using mpoly_to_mpoly_poly_monom[of x m a]
      unfolding mpoly_to_mpoly_poly_alt_def
        isolate_variable_sparse_monom[of m a] 
      by auto
  }
  moreover {
    assume *: "a \<noteq>0"
    then  have "monomials (MPoly_Type.monom m a) = {m}"
      using MPolyExtension.monomials_monom by auto
    then have "(lookup m x) = MPoly_Type.degree (MPoly_Type.monom m a) x"
      using degree_eq_iff[of "(MPoly_Type.monom m a)" x]
      by (simp add: "*" degree_monom)
    then have h1: "(\<Sum>i = 0..MPoly_Type.degree (MPoly_Type.monom m a) x.
        Polynomial.monom (isolate_variable_sparse (MPoly_Type.monom m a) x i) i) = 
        (\<Sum>i = 0..(lookup m x).
        Polynomial.monom (isolate_variable_sparse (MPoly_Type.monom m a) x i) i)"
      by auto
    have "\<And>i. i < (lookup m x ) \<Longrightarrow> 
    Polynomial.monom (isolate_variable_sparse (MPoly_Type.monom m a) x i) i = 0"
      using isolate_variable_sparse_monom[of m a]
      by auto  
    then have "(\<Sum>i = 0..<(lookup m x).
        Polynomial.monom (isolate_variable_sparse (MPoly_Type.monom m a) x i) i) = 0"
      by simp
    then have h2: "(\<Sum>i = 0..(lookup m x).
        Polynomial.monom (isolate_variable_sparse (MPoly_Type.monom m a) x i) i) = Polynomial.monom (isolate_variable_sparse (MPoly_Type.monom m a) x (lookup m x)) 
            (lookup m x)"
      by (simp add: sum.head_if)
    have k1: "(\<Sum>i = 0..MPoly_Type.degree (MPoly_Type.monom m a) x.
        Polynomial.monom (isolate_variable_sparse (MPoly_Type.monom m a) x i) i) = 
        Polynomial.monom (isolate_variable_sparse (MPoly_Type.monom m a) x (lookup m x)) 
            (lookup m x)"
      using h1 h2 by auto 
    have "Abs_poly_mapping ((lookup m)(x := 0)) =
    Abs_poly_mapping (\<lambda>k. lookup m k when k \<noteq> x)"
      by (metis (full_types) "when"(1) "when"(2) fun_upd_apply) 
    then have "(Poly_Mapping.update x 0 m) = (remove_key x m)"
      unfolding remove_key_def update_def 
      by (auto)
    then have " MPoly_Type.monom (Poly_Mapping.update x 0 m) a =  MPoly_Type.monom (remove_key x m) a"
      by auto
    then have "isolate_variable_sparse (MPoly_Type.monom m a) x (lookup m x) = MPoly_Type.monom (remove_key x m) a"
      using ExecutiblePolyProps.isolate_variable_sparse_monom[of m a x "(lookup m x)"] *
      by auto 
    then have k2: "Polynomial.monom (isolate_variable_sparse (MPoly_Type.monom m a) x (lookup m x)) (lookup m x) = 
Polynomial.monom (MPoly_Type.monom (remove_key x m) a) (lookup m x)"
      by auto 
    have " mpoly_to_mpoly_poly_alt x (MPoly_Type.monom m a) =
           mpoly_to_mpoly_poly x (MPoly_Type.monom m a)" unfolding mpoly_to_mpoly_poly_alt_def 
      using k1 k2 mpoly_to_mpoly_poly_monom[of x m a]
      by auto
  }
  ultimately have " mpoly_to_mpoly_poly_alt x (MPoly_Type.monom m a) =
           mpoly_to_mpoly_poly x (MPoly_Type.monom m a)"
    by blast 
  then show ?case
    by blast 
next
  case (sum p1 p2 m a)
  then show ?case 
    using mpoly_to_mpoly_poly_add[of x p1 p2] mpoly_to_mpoly_poly_alt_sum[of x p1 p2]
    by auto
qed


section "Same mpoly eval means same polynomials"

lemma var_in_some_coeff:
  fixes p::"real mpoly Polynomial.poly"
  fixes w::"real mpoly"
  assumes "x \<in> vars ((poly p w)::real mpoly)"
  shows "x \<in> vars w \<or> (\<exists>i. x \<in> vars (poly.coeff p i))"
  using assms
proof (induct "Polynomial.degree p" arbitrary: p rule: less_induct)
  case less
  {assume *: "Polynomial.degree p = 0"
    then have "x \<in> vars w \<or> (\<exists>i. x \<in> vars (poly.coeff p i))"
      using poly_altdef[of p w]
      using local.less(2) by force 
  } moreover
  {assume *: "Polynomial.degree p > 0"
    then obtain xa where deg_is: "Polynomial.degree p = xa + 1"
      by (metis Suc_eq_plus1 less_numeral_extra(3) not0_implies_Suc)
    then have poly_p_w: "poly p w = (\<Sum>i\<le>xa. poly.coeff p i * w ^ i) + (poly.coeff p (xa + 1) * w ^ (xa + 1))"
      using poly_altdef[of p w]
      by (metis (no_types, lifting) Suc_eq_plus1 sum.atMost_Suc) 
    then have xin: "x \<in> vars (\<Sum>i\<le>xa. poly.coeff p i * w ^ i) \<or> x \<in> vars (poly.coeff p (xa + 1) * w ^ (xa + 1))"
      using vars_add
      using local.less(2) by auto 
    let ?q = "one_less_degree p"
    have less_deg: "(poly (one_less_degree p) w) = (\<Sum>i\<le>xa. poly.coeff p i * w ^ i)"
      using coeff_one_less_degree poly_altdef deg_is
      by (smt (verit, best) local.less(2) Suc_eq_plus1 poly_p_w add_diff_cancel_right' poly_p_altdef_one_less_degree sum.cong zero_less_Suc) 
    {assume **: "x \<in> vars (poly.coeff p (xa + 1) * w ^ (xa + 1))"
      then have "x \<in> vars w \<or> (\<exists>i. x \<in> vars (poly.coeff p i))" 
        using vars_mult[of "poly.coeff p (xa + 1)" "w ^ (xa + 1)"]
        by (meson not_in_mult not_in_pow) 
    }
    moreover {assume **:"x \<in> vars (\<Sum>i\<le>xa. poly.coeff p i * w ^ i) "
      then have "x \<in> vars (poly (one_less_degree p) w)"
        using less_deg by auto 
      then have "x \<in> vars w \<or> (\<exists>i. x \<in> vars (poly.coeff (one_less_degree p) i))"
        using less.hyps one_less_degree_degree *
        by simp 
      then have "x \<in> vars w \<or> (\<exists>i. x \<in> vars (poly.coeff p i))" 
        using coeff_one_less_degree
        by (metis coeff_eq_0 le_degree lessI zero_poly.rep_eq) 
    }
    ultimately have  "x \<in> vars w \<or> (\<exists>i. x \<in> vars (poly.coeff p i))" 
      using xin
      by auto
  } ultimately show ?case
    by auto
qed

fun zero_list:: "nat \<Rightarrow> ('a::zero) list"
  where "zero_list 0 = []"
  | "zero_list (Suc n) = (0::'a)#(zero_list n)"

lemma zero_list_len:
  shows "length (zero_list n) = n"
proof (induct n)
  case 0
  then show ?case by auto
next
  case (Suc n)
  then show ?case by auto
qed




lemma zero_list_member:
  shows "m < n \<Longrightarrow> (zero_list n) ! m = 0"
proof - 
  assume "m < n"
  then show "(zero_list n) ! m = 0"
    proof (induct n arbitrary: m)
      case 0
      then show ?case by auto
    next
      case (Suc n)  
      then show ?case
        using less_Suc_eq_0_disj by force
    qed
qed

lemma eval_mpoly_zero_is_zero: 
  assumes all_same: "\<And> L. eval_mpoly L p = 0"
  shows "p = 0"
  using assms 
proof (induct "List.length (sorted_list_of_set (vars p))" arbitrary: p rule: less_induct)
  case less 
  {assume *: "vars p = {}"
    then obtain k where k_prop: "p = Const k"
      using vars_empty_iff
      by blast 
    then have "k \<noteq> 0 \<Longrightarrow> False" using all_same
    proof - 
      assume *:"k\<noteq> 0"
      have "eval_mpoly [1] p = k"
        using k_prop unfolding eval_mpoly_def
        by auto
      then show "False"
        using less.prems * by auto 
    qed
    then have " p = 0"
      using k_prop
      using mpoly_Const_0 
      by blast 
  }  
  moreover {assume *: "vars p \<noteq> {}"
    then obtain k where "k \<in> vars p"
      by blast
    then have "MPoly_Type.degree p k > 0"
      using degree_pos_iff by blast
    let ?uni_conn = "mpoly_to_mpoly_poly_alt k p "
    have "Polynomial.degree ?uni_conn > 0"
      by (simp add: \<open>0 < MPoly_Type.degree p k\<close> multivar_as_univar)
    then have "?uni_conn \<noteq> 0"
      by auto 
    then have finset: "finite {x. Polynomial.poly ?uni_conn x = 0}"
      using poly_roots_finite[of ?uni_conn]
      by blast 
    then have "\<exists>(w::real). Polynomial.poly ?uni_conn (Const w) \<noteq> 0"
    proof - 
      have "(\<forall>(w::real). Const w \<in> {x. Polynomial.poly ?uni_conn x = 0}) \<Longrightarrow> False"
      proof -      
        assume "\<forall>w. Const w \<in> {x. Polynomial.poly ?uni_conn x = 0}"
        then have subset: "{x. \<exists> (w::real). Const w = x} \<subseteq>{x. Polynomial.poly ?uni_conn x = 0}"
          by auto
        have "bij_betw (\<lambda>x::real. Const x) {x. \<exists>(w::real). w = x} {x. \<exists> (w::real). Const w = x}"
        proof -
          have h1: "inj_on Const {x. \<exists>w. w = x}"
            unfolding inj_on_def by auto
          have h2: "Const ` {x. \<exists>w. w = x} = {x. \<exists>w. Const w = x}"
            unfolding image_def by auto
          show ?thesis using h1 h2 unfolding bij_betw_def 
            by auto
        qed
        then have set_eq: "finite {x. \<exists>(w::real). w = x} = finite  {x. \<exists> (w::real). Const w = x}"
          using bij_betw_finite[of _ "{x. \<exists>(w::real). w = x}" "{x. \<exists>w. Const w = x}"]
          by auto
        have h1: "\<not> (finite {x. \<exists>(w::real). w = x} )"
          using infinite_UNIV_char_0
          by auto 
        then have "\<not> (finite {x. \<exists> (w::real). Const w = x})"
          using set_eq h1 by auto 
        then have "\<not> (finite {x. Polynomial.poly ?uni_conn x = 0})"
          using  subset infinite_super by auto
        then show "False" using finset
          by auto
      qed  
      then show ?thesis 
        by auto
    qed
    then obtain w where w_prop: "((Polynomial.poly ?uni_conn (Const w))::real mpoly) \<noteq> 0"
      by auto 
    have vars: "vars ((Polynomial.poly ?uni_conn (Const w))::real mpoly)  \<subseteq> vars p - {k}"
    proof 
      fix x
      assume *: " x \<in> vars (poly (mpoly_to_mpoly_poly_alt k p) (Const w))"
      have "vars (Const w) = {}" by auto
      then have ex_i: "\<exists>i. x \<in> vars (poly.coeff (mpoly_to_mpoly_poly k p) i)"
        using var_in_some_coeff *
        by (metis empty_iff multivar_as_univar) 
      show "x \<in> vars p - {k}"
        using multivar_as_univar vars_coeff_mpoly_to_mpoly_poly
        using ex_i by blast
    qed
    then have "card (vars (poly (mpoly_to_mpoly_poly_alt k p) (Const w))) < card (vars p)"
      by (metis Diff_subset \<open>k \<in> vars p\<close> card_Diff1_less order_neq_le_trans psubset_card_mono psubset_subset_trans vars_finite)   
    then have vars_len: "length (sorted_list_of_set (vars (Polynomial.poly ?uni_conn (Const w))))
    < length (sorted_list_of_set (vars p))"
      by auto
    then have "\<exists>z. eval_mpoly z (Polynomial.poly ?uni_conn (Const w)) \<noteq> 0"
    proof -
      have "(\<And>L. eval_mpoly L (Polynomial.poly ?uni_conn (Const w)) = 0) \<Longrightarrow> (Polynomial.poly ?uni_conn (Const w))  = 0"
        using vars_len less.hyps by auto
      then show ?thesis using w_prop by auto 
    qed
    then obtain z where z_prop: "eval_mpoly z (Polynomial.poly ?uni_conn (Const w)) \<noteq> 0"
      by auto
    obtain update_z where update_z_prop: "update_z = (if length z > k then z else 
      append z (zero_list (k - (length z) + 1)))"
      by simp    
    then have update_z_len: "length update_z \<ge> k"
      using zero_list_len
      by (smt (z3) add_diff_inverse_nat length_append less_or_eq_imp_le linorder_le_less_linear nat_add_left_cancel_less not_add_less1)  
    obtain ell where ell_prop:
      "ell = list_update update_z k w"
      "(\<forall> i \<noteq> k. ell ! i = update_z ! i) \<and> ell ! k = w"
      using update_z_len 
      by (simp add: update_z_prop zero_list_len)
    have k_notin: "k \<notin> vars (Polynomial.poly ?uni_conn (Const w))"
      by (meson DiffE singletonI subsetD vars)
    then have "eval_mpoly update_z (Polynomial.poly ?uni_conn (Const w)) =
      eval_mpoly ell (Polynomial.poly ?uni_conn (Const w))"
      unfolding eval_mpoly_def
      by (metis ell_prop(1) list_update_id not_contains_insertion) 
    have same_except1: "(\<And>y. y \<noteq> k \<Longrightarrow> nth_default 0 update_z y = nth_default 0 ell y)"
      using update_z_prop
      by (metis ell_prop(1) ell_prop(2) length_list_update nth_default_eq_dflt_iff nth_default_nth) 
    have same_except2: "(\<And>y. y \<noteq> k \<Longrightarrow> nth_default 0 update_z y = nth_default 0 z y)"
    proof - 
      fix y 
      assume y_not: "y \<noteq> k"
      {assume *: "y \<ge> (length z)"
        then have h1: "nth_default 0 z y = 0"
          unfolding nth_default_def
          by auto
        have h2: "nth_default 0 update_z y = 0"
          unfolding nth_default_def using y_not update_z_prop zero_list_member
          by (smt (z3) "*" add_diff_cancel_left' diff_less_mono length_append linorder_not_le nth_append zero_list_len)
        then have "nth_default 0 update_z y = nth_default 0 z y"
          using h1 h2
          by auto
      } moreover
      {assume *: "y < (length z)"    
        then have "nth_default 0 update_z y = nth_default 0 z y"
          using update_z_prop y_not
          by (metis nth_default_append nth_default_nth) 
      }
      ultimately show "nth_default 0 update_z y = nth_default 0 z y" using update_z_prop zero_list_member
        using linorder_le_less_linear by blast 
    qed
    have h: "(\<And>y. y \<noteq> k \<Longrightarrow> nth_default 0 z y = nth_default 0 ell y)"
      using same_except1 same_except2
      by auto
    then have same1: "poly (map_poly (insertion (nth_default 0 z)) (mpoly_to_mpoly_poly k p)) w =
      (insertion (nth_default 0 ell)) p"
      using insertion_mpoly_to_mpoly_poly[of k "(nth_default 0 z)" "(nth_default 0 ell)" p]
        ell_prop(2)
      by (smt (verit, del_insts) One_nat_def add_Suc_right add_diff_inverse_nat ell_prop(1) length_append length_list_update lessI nth_default_def semiring_norm(51) update_z_prop zero_list_len) 
    have same2: "poly (map_poly (insertion (nth_default 0 z)) (mpoly_to_mpoly_poly k p)) w
      = eval_mpoly z (Polynomial.poly ?uni_conn (Const w))"
      unfolding eval_mpoly_def poly_def
      by (smt (verit, best) One_nat_def h \<open>eval_mpoly z (poly (mpoly_to_mpoly_poly_alt k p) (Const w)) \<noteq> 0\<close> k_notin add_diff_inverse_nat arith_extra_simps(6) ell_prop(1) eval_mpoly_def eval_mpoly_map_poly_comm_ring_hom.base.poly_map_poly insertion_const insertion_irrelevant_vars insertion_var length_append less.prems lessI multivar_as_univar nat_add_left_cancel_less poly_mpoly_to_mpoly_poly update_z_prop zero_list_len) 
    have same3: "eval_mpoly ell p = eval_mpoly z (Polynomial.poly ?uni_conn (Const w))"
      using same1 same2
      using eval_mpoly_def by force 
    then have "eval_mpoly ell p \<noteq> 0"
      using z_prop
      by presburger 
    then have "mpoly_to_mpoly_poly_alt k p \<noteq> 0 \<Longrightarrow> False"
      using insertion_mpoly_to_mpoly_poly w_prop
      by (meson local.less(2)) 
    then have "mpoly_to_mpoly_poly_alt k p = 0"
      by auto 
    then have " p = 0"
      using multivar_as_univar
      by (metis mpoly_to_mpoly_poly_0 mpoly_to_mpoly_poly_eq_iff) 
  }
  ultimately show ?case 
    by auto 
qed

section "Useful properties for decision proofs"

lemma eval_mpoly_same: 
  assumes all_same: "(\<And> L. eval_mpoly L p = eval_mpoly L q)"
  shows "p = q"
proof -
  have "\<And> L. eval_mpoly L (p - q) = 0"
    using all_same
    using eval_mpoly_map_poly_comm_ring_hom.base.hom_minus by fastforce
  then have "p - q = 0"
    using eval_mpoly_zero_is_zero
    by blast  
  then show ?thesis
    by auto 
qed

lemma univariate_in_eval:
  fixes qs:: "real mpoly list"
  fixes x y:: "real"
  shows "(map (\<lambda>p. (Polynomial.poly p x)) (map (\<lambda>q. eval_mpoly_poly (y#xs) q) (univariate_in qs 0))
 = map (eval_mpoly (x#xs)) qs)"
proof - 
  have "\<And>xa. xa \<in> set qs \<Longrightarrow>
          poly (eval_mpoly_poly (y # xs) (mpoly_to_mpoly_poly_alt 0 xa)) x =
          eval_mpoly (x # xs) xa"
  proof - 
    fix xa
    assume "xa \<in> set qs"
    have " (\<And>ya. ya \<noteq> 0 \<Longrightarrow> nth_default 0 (y # xs) ya = nth_default 0 (x # xs) ya)"
      by (metis nat.exhaust nth_default_Cons_Suc)
    then show "poly (eval_mpoly_poly (y # xs) (mpoly_to_mpoly_poly_alt 0 xa)) x =
          eval_mpoly (x # xs) xa"
      unfolding eval_mpoly_poly_def eval_mpoly_def 
      using insertion_mpoly_to_mpoly_poly[of 0 "(nth_default 0 (y # xs))"
          "(nth_default 0 (x # xs))" xa]
        multivar_as_univar[of 0 xa]
      by auto
  qed
  then show ?thesis unfolding univariate_in_def 
    by auto
qed



lemma lowering_poly_eval_var:
  fixes q:: "real mpoly Polynomial.poly"
  assumes not_in_vars: "\<forall>c \<in> set (Polynomial.coeffs q). 0 \<notin> vars c"
  assumes nonz: "q \<noteq> 0"
  fixes x y:: "real"
  shows "eval_mpoly_poly xs (map_poly (lowerPoly 0 1) q)
    = eval_mpoly_poly (y#xs) q"
proof - 
  let ?map_lp_q = "map_poly (lowerPoly 0 1) q"
  have zero_prop: "\<And>p. p \<in> set (Polynomial.coeffs q) \<Longrightarrow> (lowerPoly 0 1 p = 0  \<longleftrightarrow> p = 0)"
  proof - 
    fix p
    assume *: "p \<in> set (Polynomial.coeffs q)"
    let ?lp = "lowerPoly 0 1 p"
    have "\<forall>r::real mpoly. r = 0 \<longleftrightarrow> (\<forall>val. eval_mpoly val r = 0)"
      using eval_mpoly_zero_is_zero by auto
    have "0 \<notin> vars p"
      using * not_in_vars by auto
    then have match: "\<forall>y. eval_mpoly (y # xs) p =  eval_mpoly xs ?lp"
      by (simp add: eval_mpoly_def insertion_lowerPoly01) 
    then have d1: "lowerPoly 0 1 p = 0 \<Longrightarrow> p = 0" 
    proof - 
      assume is_zero: "lowerPoly 0 1 p = 0"
      then have "\<And> L. eval_mpoly L ?lp = 0"
        using eval_mpoly_zero_is_zero by auto
      then have "\<And> L. eval_mpoly L p = 0"
      proof - 
        fix L:: "real list"
        { assume *: "L = []"
          then have same_eval: "eval_mpoly (0 # L) p =  eval_mpoly L p "
            unfolding eval_mpoly_def
            by (smt (verit, ccfv_threshold) add_0 insertion_irrelevant_vars less_Suc0 list.size(3) list.size(4) nth_Cons_0 nth_default_Nil nth_default_def)
          then have "eval_mpoly (0 # L) p = eval_mpoly L ?lp"
            using match
            by (simp add: \<open>0 \<notin> vars p\<close> eval_mpoly_def insertion_lowerPoly01) 
          then have "eval_mpoly L p = 0"
            using is_zero same_eval by auto
        } moreover { assume *: "length L > 0"
          then obtain h T where "L = h # T"
            by (metis length_greater_0_conv neq_Nil_conv)
          then have same_eval: "eval_mpoly L p = eval_mpoly T ?lp"
            using match
            by (simp add: \<open>0 \<notin> vars p\<close> eval_mpoly_def insertion_lowerPoly01) 
          then have "eval_mpoly L p = 0"
            using is_zero same_eval by auto
        }
        ultimately show "eval_mpoly L p = 0"
          by blast
      qed
      then show "p = 0"
        using eval_mpoly_zero_is_zero by auto
    qed
    have d2: "p = 0 \<Longrightarrow> lowerPoly 0 1 p = 0" 
      using match eval_mpoly_zero_is_zero
      using lower0 by blast 
    then show "(lowerPoly 0 1 p = 0  \<longleftrightarrow> p = 0)"
      using d1 d2 by auto
  qed
  then have map_nonz: "?map_lp_q \<noteq> 0"
    using nonz
    by (simp add: lower0 map_poly_eq_0_iff) 
  have "Polynomial.degree q = length (Polynomial.coeffs q) - 1"
    using nonz degree_eq_length_coeffs by auto
  then have deg1: "Polynomial.degree ?map_lp_q \<le> Polynomial.degree q"
    unfolding map_poly_def
    by (metis degree_map_poly_le map_poly_def)
  have deg2: "Polynomial.degree ?map_lp_q \<ge> Polynomial.degree q"
    using zero_prop unfolding map_poly_def
    by (metis Ring_Hom_Poly.degree_map_poly coeff_in_coeffs le_degree leading_coeff_neq_0 map_poly_def nonz)    
  then have same_deg: "Polynomial.degree q = Polynomial.degree ?map_lp_q"
    using deg1 deg2 by auto
  have "q = poly_of_list (Polynomial.coeffs q)"
    "(map_poly (lowerPoly 0 1) q) = poly_of_list (Polynomial.coeffs (map_poly (lowerPoly 0 1) q))"
    using Poly_coeffs by auto
  have same_len: "length (Polynomial.coeffs q) = length (Polynomial.coeffs (map_poly (lowerPoly 0 1) q))"
    using nonz same_deg degree_eq_length_coeffs map_nonz
    by (simp add: length_coeffs_degree)
  have "\<And>i. i < length (Polynomial.coeffs q) \<Longrightarrow> eval_mpoly (y#xs) ((Polynomial.coeffs q) ! i) = eval_mpoly xs ((Polynomial.coeffs (map_poly (lowerPoly 0 1) q)) ! i)"
  proof - fix i
    assume *: "i < length (Polynomial.coeffs q)"
    then have not_in_vars: "0 \<notin> vars ((Polynomial.coeffs q) ! i)"
      using not_in_vars in_set_member 
      by auto 
    then have same_eval: "eval_mpoly (y#xs) ((Polynomial.coeffs q) ! i) = eval_mpoly xs ((lowerPoly 0 1) ((Polynomial.coeffs q) ! i))"
      by (simp add: eval_mpoly_def insertion_lowerPoly01)
    have "(Polynomial.coeffs (map_poly (lowerPoly 0 1) q)) ! i = 
      (lowerPoly 0 1) ((Polynomial.coeffs q) ! i)"
      using coeff_map_poly lower0 same_len  *
      by (metis nth_coeffs_coeff)
    then show "eval_mpoly (y#xs) ((Polynomial.coeffs q) ! i) = eval_mpoly xs ((Polynomial.coeffs (map_poly (lowerPoly 0 1) q)) ! i)"
      using same_eval by auto 
  qed
  then show ?thesis unfolding eval_mpoly_poly_def map_poly_def
    using same_len
    by (metis map_poly_def nth_map_conv) 
qed


lemma lowering_poly_eval:
  fixes q:: "real mpoly Polynomial.poly"
  assumes "\<forall>c \<in> set (Polynomial.coeffs q). 0 \<notin> vars c"
  fixes x y:: "real"
  shows "eval_mpoly_poly xs (map_poly (lowerPoly 0 1) q)
    = eval_mpoly_poly (y#xs) q"
  using lowering_poly_eval_var
  by (metis assms eval_mpoly_poly_comm_ring_hom.hom_zero map_poly_0) 

lemma reindexed_univ_qs_eval:
  assumes "univ_qs = univariate_in qs 0" 
  assumes "reindexed_univ_qs = map (map_poly (lowerPoly 0 1)) univ_qs"
  shows "map (eval_mpoly (x#xs)) qs =
  (map (\<lambda>p. (Polynomial.poly p x )) (map (\<lambda>q. eval_mpoly_poly xs q) reindexed_univ_qs))"
proof -
  have same: "\<And>i. i < length reindexed_univ_qs \<Longrightarrow> (map (\<lambda>p. (Polynomial.poly p x )) (map (\<lambda>q. eval_mpoly_poly xs q) reindexed_univ_qs)) ! i
  = (Polynomial.poly (eval_mpoly_poly xs (reindexed_univ_qs ! i)) x)"
    by simp
  have len1: "length univ_qs = length qs"
    using assms(1) unfolding univariate_in_def 
    by auto
  have len2: "length reindexed_univ_qs = length univ_qs"
    using assms(2) by auto
  have len: "length reindexed_univ_qs = length qs"
    using len1 len2 by auto
  have "\<And>i. i < length qs \<Longrightarrow> (Polynomial.poly (eval_mpoly_poly xs (reindexed_univ_qs ! i)) x) = 
  (eval_mpoly (x#xs) (qs ! i))"
  proof - 
    fix i
    assume "i < length qs"
    have "reindexed_univ_qs ! i =  (map_poly (lowerPoly 0 1)) ((univariate_in qs 0) ! i)"
      using assms
      using \<open>i < length qs\<close> len1 by auto 
    let ?q = "(univariate_in qs 0) ! i"
    let ?q1 = "mpoly_to_mpoly_poly 0 (qs ! i)"
    have "\<forall>c\<in>set (Polynomial.coeffs ?q1). 0 \<notin> vars c"
      using vars_coeff_mpoly_to_mpoly_poly[of 0 "qs ! i"] in_set_member
      unfolding Polynomial.coeffs_def
      by auto 
    then have "\<forall>c\<in>set (Polynomial.coeffs ?q). 0 \<notin> vars c"
      using multivar_as_univar
      by (metis \<open>i < length qs\<close> nth_map univariate_in_def) 
        (* Putting it all together *)
    then show "(Polynomial.poly (eval_mpoly_poly xs (reindexed_univ_qs ! i)) x) =
      (eval_mpoly (x#xs) (qs ! i))"
      using univariate_in_eval lowering_poly_eval assms
      by (smt (verit, ccfv_SIG) \<open>i < length qs\<close> length_map nth_map) 
  qed
  then show ?thesis
    using same len
    by (simp add: nth_map_conv) 
qed

value "variables_list [((Var 0 +(Const (3::real))*((Var 1)^2)):: real mpoly)]"

value "((Var 0 +(Const (3::real))*((Var 1)^2)):: real mpoly)"

value "(mpoly_to_mpoly_poly_alt (1::nat) ((Var 0 +(Const (3::real))*((Var 1)^2)):: real mpoly))::
real mpoly Polynomial.poly"


end