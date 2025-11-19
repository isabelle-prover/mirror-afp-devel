section \<open>Undecidability of KBO with Subterm Coefficients\<close>

theory KBO_Subterm_Coefficients_Undecidable
  imports 
    Hilbert10_to_Inequality
    Knuth_Bendix_Order.KBO
    Linear_Poly_Termination_Undecidable (* contains definition of encoding and TRS R *)
begin

lemma count_sum_list: "count (sum_list ms) x = sum_list (map (\<lambda> m. count m x) ms)" 
  by (induct ms, auto)

lemma sum_list_scf_list_prod: "sum_list (map f (scf_list scf as)) = sum_list (map (\<lambda> i. scf i * f (as ! i)) [0..<length as])" 
  unfolding scf_list_def 
  unfolding map_concat
  unfolding sum_list_concat map_map o_def
  apply (subst zip_nth_conv, force)
  unfolding map_map o_def split
  apply (rule arg_cong[of _ _ sum_list])
  by (intro nth_equalityI, auto simp: sum_list_replicate)

lemma count_vars_term_different_var: assumes x: "x \<notin> vars_term t" 
  shows "count (vars_term_ms (scf_term scf t)) x = 0" 
proof -
  from assms have "x \<notin> vars_term (scf_term scf t)"
    using vars_term_scf_subset by fastforce
  thus ?thesis 
    by (simp add: count_eq_zero_iff)
qed


context kbo
begin
definition kbo_orientation :: "('f,'v)rule set \<Rightarrow> bool" where
  "kbo_orientation R = (\<forall> (l,r) \<in> R. fst (kbo l r))" 
end

definition kbo_with_sc_termination :: "('f,'v)rule set \<Rightarrow> bool" where
  "kbo_with_sc_termination R = (\<exists> w w0 sc least pr_strict pr_weak. admissible_kbo w w0 pr_strict pr_weak least sc
     \<and> kbo.kbo_orientation w w0 sc least pr_strict pr_weak R)" 

context poly_input
begin

context
  fixes sc
  assumes sc: "sc (a_sym, Suc (Suc 0)) 0 = (1 :: nat)"
      "sc (a_sym, Suc (Suc 0)) (Suc 0) = 1"
begin
lemma count_vars_term_encode_num_nat:  
  "count (vars_term_ms (scf_term sc (encode_num x (int n)))) x = n" 
  unfolding encode_num_def nat_int
  by (induct n, auto simp add: scf_list_def sc)

lemma count_vars_term_encode_num:  
  "c \<ge> 0 \<Longrightarrow> int (count (vars_term_ms (scf_term sc (encode_num x c))) x) = c" 
  using count_vars_term_encode_num_nat[of x "nat c"] by auto

lemma count_vars_term_v_pow_e: 
  "count (vars_term_ms (scf_term sc ((v_t x ^^ e) t))) y 
  = (sc (v_sym x,1) 0)^e * count (vars_term_ms (scf_term sc t)) y" 
proof (induct e)
  case (Suc e)
  thus ?case
    by (simp split: if_splits add: scf_list_def sum_mset_sum_list sum_list_replicate count_sum_list sc
             flip: mset_replicate)
qed force

lemma count_vars_term_encode_monom: assumes c: "c \<ge> 0" 
  shows "int (count (vars_term_ms (scf_term sc (encode_monom x m c))) x) 
    = insertion (\<lambda> v. int (sc (v_sym v,1) 0)) (monom m c)" 
proof -
  define xes where "xes = var_list m" 
  from var_list[of m c] 
  have monom: "monom m c = Const c * (\<Prod>(x, e)\<leftarrow> xes . PVar x ^ e) " unfolding xes_def .
  show ?thesis unfolding encode_monom_def monom xes_def[symmetric]
  proof (induct xes)
    case Nil
    show ?case by (simp add: count_vars_term_encode_num[OF c] insertion_Const sc)
  next
    case (Cons xe xes)
    obtain x e where xe: "xe = (x,e)" by force
    show ?case 
      by (simp add: xe count_vars_term_v_pow_e Cons
          insertion_Const insertion_mult insertion_power insertion_Var when_def)
  qed
qed

text \<open>Lemma 4.5\<close>
(* the assumptions on sc(a) are in the context *)
lemma count_vars_term_encode_poly_generic: assumes "positive_poly r" 
  shows "int (count (vars_term_ms (scf_term sc (encode_poly x r))) x) = 
    insertion (\<lambda> v. int (sc (v_sym v,1) 0)) r" 
proof -
  define mcs where "mcs = monom_list r" 
  from monom_list[of r] have r: "r = (\<Sum>(m, c)\<leftarrow> mcs. monom m c)" unfolding mcs_def by auto
  have mcs: "(m,c) \<in> set mcs \<Longrightarrow> c \<ge> 0" for m c 
    using monom_list_coeff assms unfolding mcs_def positive_poly_def by auto
  show ?thesis unfolding encode_poly_def mcs_def[symmetric] unfolding r insertion_sum_list map_map o_def
    using mcs
  proof (induct mcs)
    case (Cons mc mcs)
    obtain m c where mc: "mc = (m,c)" by force
    from Cons(2) mc have c: "c \<ge> 0" by auto
    note monom = count_vars_term_encode_monom[OF this, of x m]
    show ?case
      apply (simp add: mc monom scf_list_def sc)
      apply (subst Cons(1))
      using Cons(2) by (auto simp: when_def)
  qed simp
qed
end

text \<open>Theorem 4.6\<close>
theorem kbo_sc_termination_R_imp_solution: 
  assumes "kbo_with_sc_termination R" 
  shows "positive_poly_problem p q" 
proof -
  from assms[unfolded kbo_with_sc_termination_def] obtain w w0 sc least pr_strict pr_weak
    where 
      "admissible_kbo w w0 pr_strict pr_weak least sc" 
    and orient: "kbo.kbo_orientation w w0 sc least pr_strict pr_weak R" 
    by blast
  interpret admissible_kbo w w0 pr_strict pr_weak least sc by fact
  define l where "l i = args lhs_R ! i" for i
  define r where "r i = args rhs_R ! i" for i
  define as :: "nat list" where "as = [0,1,2,3]" 
  have upt_as: "[0..<length as] = as" unfolding as_def by auto
  have lhs: "lhs_R = Fun f_sym (map l as)" unfolding lhs_R_def l_def as_def by simp
  have rhs: "rhs_R = Fun f_sym (map r as)" unfolding rhs_R_def r_def as_def by simp
  from orient[unfolded kbo_orientation_def R_def]
  have "fst (kbo lhs_R rhs_R)" by auto
  from this[unfolded kbo.simps[of lhs_R]]
  have "vars_term_ms (SCF rhs_R) \<subseteq># vars_term_ms (SCF lhs_R)" by (auto split: if_splits)
  hence count: "count (vars_term_ms (SCF rhs_R)) x \<le> count (vars_term_ms (SCF lhs_R)) x" for x 
    by (rule mset_subset_eq_count)  
  let ?f = "(f_sym, length as)" 
  {
    fix i
    assume i: "i \<in> set as" 
    from i have vl: "vars_term (l i) \<subseteq> {i}" unfolding l_def lhs_R_def as_def y1_def y2_def y3_def
      using vars_encode_poly[of i p] by auto
    from count_vars_term_different_var[of _ "l i" sc] vl
    have count_l_diff: "i \<noteq> j \<Longrightarrow> count (vars_term_ms (SCF (l i))) j = 0" for j by auto
    from i have vr: "vars_term (r i) \<subseteq> {i}" unfolding r_def rhs_R_def as_def y1_def y2_def y3_def
      using vars_encode_poly[of i q] by auto
    from count_vars_term_different_var[of _ "r i" sc] vr
    have count_r_diff: "i \<noteq> j \<Longrightarrow> count (vars_term_ms (SCF (r i))) j = 0" for j by auto
    {
      fix x
      have "count (vars_term_ms (SCF rhs_R)) x 
        = sum_list (map (\<lambda> i. count (vars_term_ms (SCF (r i))) x) (scf_list (sc ?f) as))" unfolding rhs
      apply (simp add: o_def)
      apply (unfold mset_map[symmetric] sum_mset_sum_list)
      apply (unfold count_sum_list map_map o_def)
      by simp
      also have "\<dots> = (\<Sum>i\<leftarrow>as. sc ?f i * count (vars_term_ms (SCF (r (as ! i)))) x)" 
        unfolding sum_list_scf_list_prod upt_as ..
      finally have "count (vars_term_ms (SCF rhs_R)) x = (\<Sum>i\<leftarrow>as. sc ?f i * count (vars_term_ms (SCF (r (as ! i)))) x)" .
    } note count_rhs = this
    {
      fix x
      have "count (vars_term_ms (SCF lhs_R)) x 
        = sum_list (map (\<lambda> i. count (vars_term_ms (SCF (l i))) x) (scf_list (sc ?f) as))" unfolding lhs
      apply (simp add: o_def)
      apply (unfold mset_map[symmetric] sum_mset_sum_list)
      apply (unfold count_sum_list map_map o_def)
      by simp
      also have "\<dots> = (\<Sum>i\<leftarrow>as. sc ?f i * count (vars_term_ms (SCF (l (as ! i)))) x)" 
        unfolding sum_list_scf_list_prod upt_as ..
      finally have "count (vars_term_ms (SCF lhs_R)) x = (\<Sum>i\<leftarrow>as. sc ?f i * count (vars_term_ms (SCF (l (as ! i)))) x)" .
    } note count_lhs = this
    note count_lhs count_rhs count_l_diff count_r_diff
  } note cf (* count-formulas *) = this[unfolded as_def]
  let ?f = "(f_sym, Suc (Suc (Suc (Suc 0))))" 

  {
    fix i :: nat
    assume i: "i \<in> {0,1,2,3}" 
    have "sc ?f i * count (vars_term_ms (SCF (r i))) i = count (vars_term_ms (SCF rhs_R)) i"
      by (subst cf(2), insert i, auto simp add: cf)
    also have "\<dots> \<le> count (vars_term_ms (SCF lhs_R)) i" by fact
    also have "\<dots> = sc ?f i * count (vars_term_ms (SCF (l i))) i" 
      by (subst cf(1), insert i, auto simp add: cf)
    finally have "count (vars_term_ms (SCF (r i))) i \<le> count (vars_term_ms (SCF (l i))) i"  
      using scf[of i "Suc (Suc (Suc (Suc 0)))" f_sym] i by auto
  } note count_le = this

  from count_le[of 0, unfolded r_def l_def rhs_R_def lhs_R_def y1_def]
  have "sc (a_sym, Suc (Suc 0)) 0 \<le> 1" 
    apply simp
    apply (unfold mset_map[symmetric] sum_mset_sum_list)
    by (simp add: count_sum_list sum_list_scf_list_prod)
  with scf[of 0 "Suc (Suc 0)" a_sym] 
  have a20: "sc (a_sym, Suc (Suc 0)) 0 = 1" by auto

  from count_le[of 1, unfolded r_def l_def rhs_R_def lhs_R_def y2_def]
  have "sc (a_sym, Suc (Suc 0)) 1 \<le> 1" 
    apply simp
    apply (unfold mset_map[symmetric] sum_mset_sum_list)
    by (simp add: count_sum_list sum_list_scf_list_prod)
  with scf[of 1 "Suc (Suc 0)" a_sym] 
  have a21: "sc (a_sym, Suc (Suc 0)) (Suc 0) = 1" by auto

  note encode = count_vars_term_encode_poly_generic[of sc, OF a20 a21] 

  have "Suc (count (vars_term_ms (SCF (encode_poly y3 q))) y3) = count (vars_term_ms (SCF (r 2))) 2"
    by (simp add: r_def rhs_R_def scf_list_def a20 a21 y3_def)
  also have "\<dots> \<le> count (vars_term_ms (SCF (l 2))) 2" using count_le[of 2] by simp
  also have "\<dots> = Suc (count (vars_term_ms (SCF (encode_poly y3 p))) y3)" 
    by (simp add: l_def lhs_R_def scf_list_def a20 a21 y3_def)
  finally have "int (count (vars_term_ms (SCF (encode_poly y3 q))) y3) \<le> int (count (vars_term_ms (SCF (encode_poly y3 p))) y3)" 
    by auto
  from this[unfolded encode[OF pq(1)] encode[OF pq(2)]]
  show ?thesis
    unfolding positive_poly_problem_def[OF pq]
    by (intro exI[of _ "\<lambda>v. int (sc (v_sym v, 1) 0)"], auto simp: positive_interpr_def scf)
qed
end

context solvable_poly_problem
begin

definition w0 :: nat where "w0 = 1" 

fun sc :: "symbol \<times> nat \<Rightarrow> nat \<Rightarrow> nat" where 
  "sc (v_sym i, Suc 0) _ = nat (\<alpha> i)" 
| "sc _ _ = 1" 

context fixes wr :: nat
begin
fun w_R :: "symbol \<times> nat \<Rightarrow> nat" where
  "w_R (f_sym,n) = (if n = 4 then 0 else 1)" 
| "w_R (a_sym,n) = (if n = 2 then 0 else 1)" 
| "w_R (o_sym,0) = wr" 
| "w_R _ = 1"
end

definition w_rhs where "w_rhs = weight_fun.weight (w_R 1) w0 sc rhs_R" 

abbreviation w where "w \<equiv> w_R w_rhs" 

definition least where "least f = (w (f, 0) = w0 \<and> (\<forall> g. w (g, 0) = w0 \<longrightarrow> (g, 0 :: nat) = (f, 0)))" 

lemma \<alpha>0: "\<alpha> x > 0" using \<alpha>(1) unfolding positive_interpr_def by auto

sublocale admissible_kbo w w0 "(\<lambda> _ _. False)" "(=)" least sc
  apply (unfold_locales)
  subgoal for f unfolding w0_def  
    by (cases f, auto simp add: weight_fun.weight.simps w_rhs_def rhs_R_def)
  subgoal by (simp add: w0_def)
  subgoal for f g n by (cases f, auto)
  subgoal for f unfolding least_def by auto
  subgoal for i n f by (cases f; cases n; cases "n - 1"; auto intro: \<alpha>0)
  by auto

lemma insertion_pos: "positive_poly r \<Longrightarrow> insertion \<alpha> r \<ge> 0" 
  unfolding positive_poly_def by (smt (verit) \<alpha>0 insertion_nonneg)

lemma count_vars_term_encode_poly: assumes "positive_poly r" 
  shows "count (vars_term_ms (SCF (encode_poly x r))) y = (nat (insertion \<alpha> r) when x = y)" 
proof (cases "y = x")
  case False
  with count_vars_term_different_var[of y "encode_poly x r" sc] vars_encode_poly[of x r]
  show ?thesis by (auto simp: when_def)
next
  case y: True
  from count_vars_term_encode_poly_generic[of sc _ x, OF _ _ assms]
  have "int (count (vars_term_ms (SCF (encode_poly x r))) x) 
    = insertion (\<lambda>v. int (sc (v_sym v, 1) 0)) r" by auto
  also have "(\<lambda>v. int (sc (v_sym v, 1) 0)) = \<alpha>" 
    by (intro ext, insert \<alpha>0, auto simp: order.order_iff_strict) 
  finally show ?thesis unfolding y
    using insertion_pos[OF assms] by auto
qed

text \<open>Theorem 4.7 in context\<close>
theorem kbo_with_sc_termination: "kbo_with_sc_termination R" 
  unfolding kbo_with_sc_termination_def
proof (intro exI conjI) 
  show "admissible_kbo w w0 (\<lambda> _ _. False) (=) least sc" ..
  show "kbo_orientation R" unfolding R_def kbo_orientation_def
  proof (clarify)
    {
      fix t :: "(symbol,var)term" 
      assume "(o_sym,0) \<notin> funas_term t" 
      hence "weight_fun.weight (w_R (Suc 0)) w0 sc t = weight t" (is "?id t")
      proof (induct t)
        case (Var x)
        show ?case by (auto simp: weight_fun.weight.simps)
      next
        case (Fun f ts)
        hence "t \<in> set ts \<Longrightarrow> ?id t" for t by auto
        hence IH: "map2 (\<lambda>ti i. weight_fun.weight (w_R (Suc 0)) w0 sc ti * sc (f, length ts) i) ts
           [0..<length ts] = 
          map2 (\<lambda>ti i. weight ti * sc (f, length ts) i) ts [0..<length ts]"  
          by (intro nth_equalityI, auto)
        have id: "w_R (Suc 0) (f, length ts) = w (f, length ts)" 
          using Fun(2) by (cases f; cases ts, auto)
        show ?case by (auto simp: id weight_fun.weight.simps Let_def IH)
      qed
    } note weight_switch = this

    from funas_encode_poly_q[of y3] 
    have o_q: "(o_sym,0) \<notin> funas_term (encode_poly y3 q)" by (auto simp: F_def)
    have "weight rhs_R = 3 + 3 * w0 + weight (encode_poly y3 q)" 
      unfolding rhs_R_def by (simp add: scf_list_def)
    also have "\<dots> = w_rhs" unfolding weight_switch[OF o_q, symmetric]
      unfolding w_rhs_def rhs_R_def by (simp add: weight_fun.weight.simps)
    also have "\<dots> < w0 + w_rhs" using w0 by auto
    also have "\<dots> \<le> weight lhs_R" unfolding lhs_R_def
      by (simp add: scf_list_def)
    finally have weight: "weight rhs_R < weight lhs_R" .
    from \<alpha>(2) insertion_pos[OF pq(1)] insertion_pos[OF pq(2)] 
    have sol: "nat (insertion \<alpha> q) \<le> nat (insertion \<alpha> p)" by auto
    have vars: "vars_term_ms (SCF rhs_R) \<subseteq># vars_term_ms (SCF lhs_R)" 
    proof (intro mset_subset_eqI)
      fix x
      show "count (vars_term_ms (SCF rhs_R)) x \<le> count (vars_term_ms (SCF lhs_R)) x" 
        unfolding rhs_R_def lhs_R_def using y_vars sol
        by (simp add: scf_list_def count_vars_term_encode_poly[OF pq(1)] count_vars_term_encode_poly[OF pq(2)])
    qed
    from weight vars show "fst (kbo lhs_R rhs_R)" 
      unfolding kbo.simps[of lhs_R rhs_R] by auto
  qed
qed

end

text \<open>Theorem 4.7 outside solvable-context\<close>

context poly_input
begin
theorem solvable_imp_kbo_with_sc_termination: 
  assumes "positive_poly_problem p q" 
  shows "kbo_with_sc_termination R" 
  by (rule solvable_poly_problem.kbo_with_sc_termination, unfold_locales, fact)

text \<open>Combining 4.6 and 4.7\<close>
corollary solvable_iff_kbo_with_sc_termination: 
  "positive_poly_problem p q \<longleftrightarrow> kbo_with_sc_termination R" 
  using solvable_imp_kbo_with_sc_termination kbo_sc_termination_R_imp_solution by blast
end
end