section \<open>Second-Order Conditions\<close>

theory Second_Derivative_Test
  imports First_Order_Conditions
begin

subsection \<open>Necessary Condition\<close>

lemma snd_derivative_nonneg_at_local_min_necessary:
  fixes f :: "real \<Rightarrow> real"
  assumes C2_cont_diff_at_xmin: "C_k_on 2 f (U :: real set)"
  assumes min_in_U: "(x_min :: real) \<in> U"
  assumes loc_min:   "local_minimizer f x_min"
  shows "deriv (deriv f) x_min \<ge> 0"
proof - 
  have "(\<exists> \<epsilon>. 0 < \<epsilon> \<and> {x_min - \<epsilon> .. x_min + \<epsilon>} \<subset> U)"
  proof - 
    have "(\<exists> \<epsilon>. 0 < \<epsilon> \<and> ball x_min \<epsilon> \<subset> U)"
      by (smt C2_cont_diff_at_xmin C_k_on_def assms(2) ball_subset_cball cball_eq_ball_iff 
          open_contains_cball_eq order_le_less_trans psubsetI)
    then show ?thesis
      by (metis Elementary_Metric_Spaces.open_ball cball_eq_atLeastAtMost centre_in_ball 
          open_contains_cball order_trans_rules(21))
  qed
  then obtain \<epsilon> where \<epsilon>_pos: "0 < \<epsilon>" and \<epsilon>_def: "{x_min - \<epsilon> .. x_min + \<epsilon>} \<subset> U"
    by blast
  have f_diff:    "(\<forall>y \<in> U. (f has_real_derivative (deriv f) y) (at y))"
    using C2_cont_diff C2_cont_diff_at_xmin by blast
  have f'_diff: "(\<forall>y \<in> U. (deriv f has_real_derivative (deriv (deriv f)) y) (at y))"
    using C2_cont_diff C2_cont_diff_at_xmin by blast
  have f''_contin: "continuous_on U (deriv (deriv f))"
    using C2_cont_diff assms(1) by blast

  have f'_0: "(deriv f) x_min = 0"
    using Fermat's_theorem_on_stationary_points
    by (meson assms(2,3) f_diff has_field_derivative_imp_has_derivative)
  
 \<comment> \<open>By local minimality at \(x_{\min}\), there is a \(\delta > 0\) such that for all \(h\) with
     \(\lvert h\rvert < \delta\), we have \(f(x_{\min} + h) \ge f(x_{\min})\).\<close>
  obtain \<delta> where \<delta>_pos: "\<delta> > 0" and \<delta>_prop: "\<forall>h. \<bar>h\<bar> < \<delta> \<longrightarrow> f (x_min + h) \<ge> f x_min"
    by (meson assms(3) local_minimizer_neighborhood)

  from f'_0 have second_deriv_limit_at_x_min: 
    "((\<lambda>h. (deriv f (x_min + h)) / h) \<longlongrightarrow> deriv (deriv f) x_min) (at 0)"
    by (smt (verit, best) DERIV_def Lim_cong_within assms(2) f'_diff)
      
  show ?thesis
  proof(rule ccontr)
    assume "\<not> 0 \<le> deriv (deriv f) x_min"
    then have BWOC: "0 > deriv (deriv f) x_min"
      by auto
    then obtain \<Delta> where \<Delta>_pos: "\<Delta> > 0" and 
      \<Delta>_def: "\<forall>\<delta>. 0 < \<delta> \<and> \<delta> \<le> \<Delta> \<longrightarrow> (\<forall>y. \<bar>y - x_min\<bar> < \<delta> \<longrightarrow> deriv (deriv f) y < 0)"
      by (metis C2_cont_diff_at_xmin C_k_on_def min_in_U at_within_open cont_at_neg_imp_loc_neg'
          continuous_on_eq_continuous_within f''_contin)
    
    \<comment> \<open>Choose \(h\) with \(0 < h < \min\{\delta,\Delta\}\) so that \(x_{\min} + h \in U\).\<close>
    obtain h where h_def: "h = min \<epsilon> (min (\<delta>/2) \<Delta>)" and h_pos: "0 < h"
      using \<epsilon>_pos \<delta>_pos \<Delta>_pos by fastforce
    have h_lt: "h \<le> \<epsilon> \<and> h < \<delta> \<and> h \<le> \<Delta>"
      using \<delta>_pos h_def by linarith
    have neigh_in_U: "x_min + h \<in> {x_min - \<epsilon> .. x_min + \<epsilon>}"
      using h_def h_pos by fastforce     

    have "f (x_min + h) < f x_min"
    proof(rule DERIV_neg_imp_decreasing_open[where a = x_min and f = f and b = "x_min + h"])
      show "x_min < x_min + h"
        using h_pos by simp
    next
      have "{x_min..x_min + h} \<subset> U"
        using \<epsilon>_def dual_order.strict_trans2 neigh_in_U by auto
      then show "continuous_on {x_min..x_min + h} f"
        by (meson C2_cont_diff C2_cont_diff_at_xmin continuous_on_subset 
            differentiable_imp_continuous_on le_less)
    next
      show "\<And>x. \<lbrakk>x_min < x; x < x_min + h\<rbrakk> \<Longrightarrow> \<exists>y. (f has_real_derivative y) (at x) \<and> y < 0"
      proof -
        fix x :: real
        assume x_min_lt_x: "x_min < x"
        assume x_lt_xmin_pls_h: "x < x_min + h"

        have xmin_x_subset: "{x_min  .. x} \<subseteq> {x_min - \<epsilon> .. x_min + \<epsilon>}"
            using neigh_in_U x_lt_xmin_pls_h by auto
        
        \<comment> \<open>By the Mean Value Theorem applied to \(f'\) on \([x_{\min}, x]\), 
            there exists some \(c\) with \(x_{\min} < c < x\) such that:\<close>
        have "\<exists>z > x_min. z < x \<and> deriv f (x) -  deriv f x_min = (x - x_min) * deriv(deriv f) z"
        proof(rule MVT2)
          show "x_min < x"
            using x_min_lt_x by auto
        next
          fix y :: real
          assume x_min_leq_y: "x_min \<le> y"
          assume y_leq_x: "y \<le> x"
                   
          from xmin_x_subset have "y \<in> U"
            using \<epsilon>_def atLeastAtMost_iff x_min_leq_y y_leq_x by blast         
          then show "(deriv f has_real_derivative deriv (deriv f) y) (at y)"
            using f'_diff by blast
        qed
        then obtain z where z_gt_x_min: "z > x_min" and 
                            z_lt_x: "z < x" and
                            z_def: "deriv f (x) -  deriv f x_min = (x - x_min) * deriv (deriv f) z"
          by blast
        then have mvt_f': "deriv f (x)  = (x - x_min) * deriv (deriv f) z"
          by (simp add: f'_0)

        then have x_diff_xmin_pos: "x - x_min > 0"
           using `x_min < x` by simp
        then have left_bound_satisfied: "\<bar>z - x_min\<bar> < x - x_min"
           using \<open>x_min < z\<close> \<open>z < x\<close> by auto
        then have "x - x_min < h"
           using `x < x_min + h` by simp
        then  have  "\<bar>z - x_min\<bar> < h"
          using left_bound_satisfied by fastforce
        then have "deriv (deriv f) z < 0"
           using \<Delta>_def h_lt h_pos by blast
        then  have "deriv f x < 0"
          by (metis x_diff_xmin_pos mvt_f' mult_pos_neg)
         moreover have "x \<in> U"
           using xmin_x_subset
           by (meson \<epsilon>_def atLeastAtMost_iff dual_order.strict_iff_not 
               subset_eq verit_comp_simplify(2) x_min_lt_x)
         ultimately show "\<exists>y. (f has_real_derivative y) (at x) \<and> y < 0"
           using f_diff by blast      
       qed
     qed
    then show False
      by (smt (verit, best) \<delta>_prop h_lt h_pos)
  qed
qed

subsection \<open>Sufficient Condition\<close>

lemma second_derivative_test:
  fixes f :: "real \<Rightarrow> real" and a :: real and b :: real and x_min :: real
  assumes valid_interval: "a < b"
  assumes twice_continuously_differentiable: "C_k_on 2 f {a <..< b}"   
  assumes min_exists: "x_min \<in> {a <..< b}"
  assumes fst_deriv_req: "(deriv f) x_min = 0"
  assumes snd_deriv_req: "deriv (deriv f) x_min > 0"    
  shows loc_min: "local_minimizer f x_min"
proof -
  from twice_continuously_differentiable
  have f''_cont: "continuous_on {a <..< b} (deriv (deriv f))"
    by (metis C_k_on_def Suc_1 lessI nat.simps(2) second_derivative_alt_def)
  then obtain \<Delta> where \<Delta>_pos: "\<Delta> > 0"
    and \<Delta>_prop: "\<forall>\<delta>. 0 < \<delta> \<and> \<delta> \<le> \<Delta> \<longrightarrow> (\<forall>y. \<bar>y - x_min\<bar> < \<delta> \<longrightarrow> deriv (deriv f) y > 0)"
    by (metis assms(3,5) at_within_open cont_at_pos_imp_loc_pos' continuous_on_eq_continuous_within 
        open_real_greaterThanLessThan)
    
  obtain \<delta> where \<delta>_min: "\<delta> = min \<Delta> (min ((x_min - a) / 2) ((b - x_min) / 2))"
    by blast

  have \<delta>_pos: "\<delta> > 0"
  proof (cases "\<delta> = \<Delta>")
    show "\<delta> = \<Delta> \<Longrightarrow> 0 < \<delta>"
      by (simp add: \<Delta>_pos)
  next
    assume "\<delta> \<noteq> \<Delta>"
    then have "\<delta> = min ((x_min - a) / 2) ((b - x_min) / 2)"
      using \<delta>_min by linarith
    then show "0 < \<delta>"
      using min_exists by force
  qed

  have neigh_of_x_min_contained_in_ab: "a < x_min - \<delta> \<and> x_min + \<delta> < b"
    by (smt (z3) \<delta>_min \<delta>_pos field_sum_of_halves)
    
  have local_min: "\<forall>x. \<bar>x - x_min\<bar> < \<delta> \<longrightarrow> f x \<ge> f x_min"
  proof clarify
    fix x 
    assume A: "\<bar>x - x_min\<bar> < \<delta>"
    consider (eq) "x = x_min" | (lt) "x < x_min" | (gt) "x > x_min"
      by linarith
    then show "f x \<ge> f x_min"
    proof cases
      case eq
      then show ?thesis 
        by simp
    next
      case lt
      have a_lt_x_and_xmin_lt_b: "a < x \<and> x_min < b"
        using A neigh_of_x_min_contained_in_ab by linarith
      have "f x > f x_min"
      proof (rule DERIV_neg_imp_decreasing_open[where a = x])
        show "x < x_min"
          by (simp add: lt)
      next
        fix y :: real
        assume x_lt_y: "x < y"
        assume y_lt_x_min: "y < x_min"
        \<comment> \<open>For \(x < x_{\min}\), apply the Mean Value Theorem to \(f\) on \([x, x_{\min}]\).\<close>
        have "\<exists>z > y. z < x_min \<and> deriv f x_min - deriv f y = (x_min - y) * deriv (deriv f) z"
        proof (rule MVT2[where a = y and b = x_min and f = "deriv f" and f' = "deriv (deriv f)"])
          show "y < x_min"
            by (simp add: y_lt_x_min)
        next
          fix z :: real
          assume y_lt_z: "y \<le> z" 
          assume z_lt_x_min: "z \<le> x_min"
          show "(deriv f has_real_derivative (deriv (deriv f)) z) (at z)"
          proof (subst C2_cont_diff[where f = f, where U = "{a <..< b}"])
            show "C_k_on 2 f {a<..<b}" 
              by (simp add: assms(2))
            show "z \<in> {a<..<b}" and True
              using a_lt_x_and_xmin_lt_b x_lt_y y_lt_z z_lt_x_min by auto
          qed
        qed
        then obtain z where 
          z_props: "y < z" "z < x_min" and 
          eq: "deriv f x_min - deriv f y = (x_min - y) * deriv (deriv f) z"
          by blast
        have "deriv f x_min = 0"
          using fst_deriv_req by simp
        hence "deriv f y = - (x_min - y) * deriv (deriv f) z"
          using eq by linarith
        moreover have "x_min - x > 0" 
          using lt by simp
        have "deriv (deriv f) z > 0"
          by (smt (verit) A \<Delta>_prop \<delta>_min x_lt_y z_props)
        ultimately have "deriv f y < 0"
          by (simp add: mult_less_0_iff y_lt_x_min)
        then show "\<exists>z. (f has_real_derivative z) (at y) \<and> z < 0"
          by (meson C2_cont_diff a_lt_x_and_xmin_lt_b assms(2) dual_order.strict_trans
                    greaterThanLessThan_iff x_lt_y y_lt_x_min)
      next
        have "continuous_on {a <..< b} f"
          by (simp add: C2_cont_diff assms(2) differentiable_imp_continuous_on)
        then show "continuous_on {x..x_min} f"
          by (smt (verit, del_insts) a_lt_x_and_xmin_lt_b atLeastAtMost_iff
                    continuous_on_subset greaterThanLessThan_iff subsetI)
      qed
      then show "f x_min \<le> f x"
        by simp
    next
      case gt
      have a_lt_xmin_and_x_lt_b: "a < x_min \<and> x < b"
        using A \<open>a < x_min - \<delta> \<and> x_min + \<delta> < b\<close> by linarith
      have "f x > f x_min"
      proof (rule DERIV_pos_imp_increasing_open[where a = x_min])
        show "x_min < x"
          by (simp add: gt)
      next
        fix y :: real
        assume y_gt_xmin: "x_min < y"
        assume y_lt_x: "y < x"
        \<comment> \<open>For \(x_{\min} < y\), apply the Mean Value Theorem to \(f'\) on \([x_{\min}, y]\).\<close>
        have "\<exists>z > x_min. z < y \<and> deriv f y - deriv f x_min = (y - x_min) * deriv (deriv f) z"
        proof (rule MVT2[where a = x_min and b = y and f = "deriv f" and f' = "deriv (deriv f)"])
          show "x_min < y"
            by (simp add: y_gt_xmin)
        next
          fix z :: real
          assume z_ge_xmin: "x_min \<le> z"
          assume z_le_y: "z \<le> y"
          show "(deriv f has_real_derivative (deriv (deriv f)) z) (at z)"
          proof (subst C2_cont_diff[where f = f and U = "{a<..<b}"])
            show "C_k_on 2 f {a<..<b}"
              by (simp add: assms(2))
            show "z \<in> {a<..<b}" and True
              using a_lt_xmin_and_x_lt_b y_lt_x z_ge_xmin z_le_y by auto
          qed
        qed
        then obtain z where
          z_props: "x_min < z" "z < y"
          and eq: "deriv f y - deriv f x_min = (y - x_min) * deriv (deriv f) z"
          by blast
        have "deriv f x_min = 0"
          using fst_deriv_req by simp
        hence "deriv f y = (y - x_min) * deriv (deriv f) z"
          using eq by simp
        moreover have "y - x_min > 0"
          using y_gt_xmin by simp
        moreover have "deriv (deriv f) z > 0"
          by (smt (verit, best) A \<Delta>_prop \<delta>_min y_lt_x z_props(1,2))
        ultimately have "deriv f y > 0"
          by auto
        then show "\<exists>d. (f has_real_derivative d) (at y) \<and> d > 0"
          by (meson C2_cont_diff a_lt_xmin_and_x_lt_b assms(2) dual_order.strict_trans
                    greaterThanLessThan_iff y_lt_x y_gt_xmin)
      next
        have "continuous_on {a <..< b} f"
          by (simp add: C2_cont_diff assms(2) differentiable_imp_continuous_on)
        then show "continuous_on {x_min..x} f"
          by (smt (verit, del_insts) a_lt_xmin_and_x_lt_b atLeastAtMost_iff
                    continuous_on_subset greaterThanLessThan_iff subsetI)
      qed
      then show ?thesis
        by simp
    qed
  qed
  show ?thesis
    by (rule local_minimizer_from_neighborhood, smt \<delta>_pos local_min)
qed

end