(* This file generalizes the previous univariate formalization of BKR
and Renegar (see https://www.isa-afp.org/entries/BenOr_Kozen_Reif.html) 
so as not to use the Cauchy root bound, which is specific to univariate 
polynomials and does not generalize to our multivariate setting.
 *)

theory Renegar_Modified

imports "BenOr_Kozen_Reif.Renegar_Decision"

begin

definition poly_f_nocrb :: "real poly list \<Rightarrow> real poly"
  where
    "poly_f_nocrb ps = 
  (if (check_all_const_deg ps = True) then  [:0, 1:] else 
  (pderiv (prod_list_var ps)) * (prod_list_var ps))"

lemma root_set_nocrb:
  assumes is_not_const: "check_all_const_deg qs = False"
  shows "{x. poly (poly_f qs) x = 0}
 = {x. poly (poly_f_nocrb qs) x = 0} \<union> {-(crb (prod_list_var qs)), (crb (prod_list_var qs))}"
proof - 
  have "\<forall>x \<in> {x. poly (poly_f qs) x = 0}. poly (poly_f qs) x = 0" by auto
  then have all: "\<forall>x \<in> {x. poly (poly_f qs) x = 0}. poly ((pderiv (prod_list_var qs)) * (prod_list_var qs)* ([:-(crb (prod_list_var qs)),1:]) * ([:(crb (prod_list_var qs)),1:])) x = 0"
    unfolding poly_f_def using is_not_const by presburger 
  have all1: "\<forall>x \<in> {x. poly (poly_f qs) x = 0}.
    ((poly ((pderiv (prod_list_var qs)) * (prod_list_var qs)) x = 0)
    \<or> (poly (([:-(crb (prod_list_var qs)),1:]) * ([:(crb (prod_list_var qs)),1:])) x = 0))"
  proof clarsimp
    fix x
    assume inset: "poly (poly_f qs) (real_of_int x) = 0 "
    assume "poly (pderiv (prod_list_var qs)) (real_of_int x) \<noteq> 0"
    assume "x * x \<noteq> crb (prod_list_var qs) * crb (prod_list_var qs)"
    have "poly ((pderiv (prod_list_var qs)) * (prod_list_var qs)* ([:-(crb (prod_list_var qs)),1:]) * ([:(crb (prod_list_var qs)),1:])) x = 0"
      using all inset by auto
    then show "poly (prod_list_var qs) (real_of_int x) = 0" using assms
      by (smt (verit, del_insts) \<open>poly (pderiv (prod_list_var qs)) (real_of_int x) \<noteq> 0\<close> \<open>x * x \<noteq> crb (prod_list_var qs) * crb (prod_list_var qs)\<close> mult.commute mult_eq_0_iff mult_minus_left of_int_eq_iff of_int_minus poly_mult poly_root_factor(3))
  qed
  have "\<forall>x. (poly (([:-(crb (prod_list_var qs)),1:]) * ([:(crb (prod_list_var qs)),1:])) x = 0 \<longrightarrow>
  (x = -(crb (prod_list_var qs)) \<or> x = (crb (prod_list_var qs))))"
    by (simp add: square_eq_iff)
  then have "\<forall>x \<in> {x. poly (poly_f qs) x = 0}.
    ((poly (poly_f_nocrb qs) x = 0)
    \<or> (x = -(crb (prod_list_var qs)) \<or> x = (crb (prod_list_var qs))))"
    using all1 unfolding poly_f_nocrb_def
    by (smt (verit, del_insts) all is_not_const of_int_minus poly_root_factor(2)) 
  then have subset1: "{x. poly (poly_f qs) x = 0}
 \<subseteq> {x. poly (poly_f_nocrb qs) x = 0} \<union> {-(crb (prod_list_var qs)), (crb (prod_list_var qs))}"
    using UnCI is_not_const mem_Collect_eq by fastforce
  have subset2: "{x. poly (poly_f_nocrb qs) x = 0} \<union> {-(crb (prod_list_var qs)), (crb (prod_list_var qs))} \<subseteq>
   {x. poly (poly_f qs) x = 0}"
    using Un_insert_right insert_iff is_not_const mem_Collect_eq of_int_minus poly_f_def poly_f_nocrb_def by auto
  then show ?thesis using subset1 subset2 by auto
qed

lemma nonzcrb_helper:
  assumes q_in: "q \<in> set qs"
  assumes qnonz: "q \<noteq> 0"
  assumes lengt: "length (sorted_list_of_set {(x::real). (\<exists>q \<in> set(qs). (q \<noteq> 0 \<and> poly q x = 0))} :: real list) > 0"
  shows " \<not>(\<exists>x \<ge> (real_of_int (crb (prod_list_var qs))). poly q x = 0)" 
proof clarsimp 
  fix x
  assume xgt: "real_of_int (crb (prod_list_var qs)) \<le> x" 
  assume pqz: "poly q x = 0"
  let ?zer_list = "sorted_list_of_set {(x::real). (\<exists>q \<in> set(qs). (q \<noteq> 0 \<and> poly q x = 0))} :: real list"
  have strict_sorted_h: "sorted_wrt (<) ?zer_list" using sorted_sorted_list_of_set
      strict_sorted_iff by auto
  have finset: "finite  {x. \<exists>q\<in>set qs. q \<noteq> 0 \<and> poly q x = 0}"
  proof - 
    have "\<forall>q \<in> set qs.  q\<noteq> 0 \<longrightarrow> finite {x. poly q x = 0} "
      using poly_roots_finite by auto
    then show ?thesis by auto
  qed
  have all_prop: "\<forall>x \<in> {x. \<exists>q\<in>set qs. q \<noteq> 0 \<and> poly q x = 0}. poly (prod_list_var qs) x = 0"
    using q_dvd_prod_list_var_prop
    by fastforce 
  then have "poly (prod_list_var qs) (sorted_list_of_set {x. \<exists>q\<in>set qs. q \<noteq> 0 \<and> poly q x = 0} ! 0) = 0"
    using finset set_sorted_list_of_set
    by (metis (no_types, lifting) lengt nth_mem) 
  then have crbgt: "crb (prod_list_var qs) > ?zer_list ! (length ?zer_list - 1)" using prod_list_var_nonzero crb_lem_pos[of "prod_list_var qs" "?zer_list ! (length ?zer_list - 1)"]
    by (metis (no_types, lifting) all_prop diff_less finset lengt less_numeral_extra(1) nth_mem set_sorted_list_of_set) 
  have x_in: "x \<in> {x. \<exists>q\<in>set qs. q \<noteq> 0 \<and> poly q x = 0}"
    using pqz q_in qnonz 
    by auto
  then have "x \<in> set ?zer_list"
    by (smt (verit, best) finset in_set_member mem_Collect_eq set_sorted_list_of_set) 
  then have "x \<le> ?zer_list ! (length ?zer_list - 1)" using strict_sorted_h
    by (meson all_prop x_in crb_lem_pos not_less prod_list_var_nonzero xgt)
  then show "False" using xgt crbgt 
    by auto
qed

lemma root_set_nocrb_var:
  assumes is_not_const: "check_all_const_deg qs = False"
  shows "({x. poly (poly_f qs) x = 0}::real set)
 = {x. poly (poly_f_nocrb qs) x = 0} \<union> (({-(crb (prod_list_var qs)), (crb (prod_list_var qs))})::real set)"
  using root_set_nocrb apply (auto)
     apply (smt (verit) of_int_minus poly_f_def poly_f_nocrb_def poly_root_factor(2))
    apply (simp add: is_not_const poly_f_def)
  using is_not_const apply blast
  by (metis (no_types, lifting) poly_f_def poly_f_nocrb_def poly_root_factor(2))

lemma nonzcrb:
  assumes q_in: "q \<in> set qs"
  assumes qnonz: "q \<noteq> 0"
  shows " \<not>(\<exists>x \<ge> (real_of_int (crb (prod_list_var qs))). poly q x = 0)" 
proof - 
  let ?zer_list = "(sorted_list_of_set {(x::real). (\<exists>q \<in> set(qs). (q \<noteq> 0 \<and> poly q x = 0))} :: real list)"
  have eo: "length ?zer_list = 0 \<or> length ?zer_list > 0"
    by auto 
  have h1: "length ?zer_list = 0 \<longrightarrow> \<not>(\<exists>x \<ge> (real_of_int (crb (prod_list_var qs))). poly q x = 0)"
    by (metis crb_lem_pos dvdE linorder_not_less mult_zero_left poly_mult prod_list_var_nonzero q_dvd_prod_list_var_prop q_in qnonz)
  have h2: "length ?zer_list > 0 \<longrightarrow> \<not>(\<exists>x \<ge> (real_of_int (crb (prod_list_var qs))). poly q x = 0)"
    using nonzcrb_helper assms
    by blast 
  show ?thesis using eo h1 h2 
    by auto 
qed

definition sgn_pos_inf_rat_list:: "real poly list \<Rightarrow> int list"
  where "sgn_pos_inf_rat_list l = map (\<lambda>x.  (Sturm_Tarski.sign (sgn_pos_inf x))) l"

definition sgn_neg_inf_rat_list:: "real poly list \<Rightarrow> int list"
  where "sgn_neg_inf_rat_list l = map (\<lambda>x.  (Sturm_Tarski.sign (sgn_neg_inf x))) l"

definition sgn_neg_inf_rat_list2:: "real poly list \<Rightarrow> rat list"
  where "sgn_neg_inf_rat_list2 l = map (\<lambda>x.  ((rat_of_int \<circ> Sturm_Tarski.sign) (sgn_neg_inf x))) l"

definition sgn_pos_inf_rat_list2:: "real poly list \<Rightarrow> rat list"
  where "sgn_pos_inf_rat_list2 l = map (\<lambda>x.  ((rat_of_int \<circ> Sturm_Tarski.sign) (sgn_pos_inf x))) l"

lemma root_ub_restate:
  fixes p:: "real poly"
  assumes pnonz: "p \<noteq> 0"
  fixes z::"real"
  assumes zgt: "\<forall>x. poly p x=0 \<longrightarrow> x < z"
  shows "x\<ge>z \<Longrightarrow> sgn (poly p x) = Sturm_Tarski.sign (sgn_pos_inf p)"
proof - 
  assume xgt: "x\<ge>z"
  have allx: "\<forall>x \<ge> z. sgn (poly p x) = sgn (poly p z)"
  proof clarsimp 
    fix x
    assume zleq: "z \<le> x"
    then have xnonz: "sgn (poly p x) \<noteq> 0"
      using zgt unfolding sgn_def by auto
    have znonz: "sgn (poly p z) \<noteq> 0"
      using zgt unfolding sgn_def by auto 
    have "Matrix_Equation_Construction.sgn (poly p x) \<noteq> Matrix_Equation_Construction.sgn (poly p z) \<Longrightarrow> False"
    proof - 
      assume neq: "Matrix_Equation_Construction.sgn (poly p x) \<noteq> Matrix_Equation_Construction.sgn (poly p z)"
      then have z_lt: "z < x" using zleq
        using less_eq_real_def by force
      have h1: "z < x \<Longrightarrow>
        Matrix_Equation_Construction.sgn (poly p z) \<noteq> 0 \<Longrightarrow>
        Matrix_Equation_Construction.sgn (poly p x) \<noteq> 0 \<Longrightarrow>
        \<not> poly p x < 0 \<Longrightarrow> 0 < poly p x"
        using zgt by fastforce
      have h2: "z < x \<Longrightarrow>
        Matrix_Equation_Construction.sgn (poly p z) \<noteq> 0 \<Longrightarrow>
        Matrix_Equation_Construction.sgn (poly p x) \<noteq> 0 \<Longrightarrow>
        \<not> poly p x < 0 \<Longrightarrow> poly p z < 0"
        by (metis neq sgn_def)
      have h3: "z < x \<Longrightarrow>
        Matrix_Equation_Construction.sgn (poly p z) \<noteq> 0 \<Longrightarrow>
        Matrix_Equation_Construction.sgn (poly p x) \<noteq> 0 \<Longrightarrow>
        \<not> 0 < poly p z \<Longrightarrow> 0 < poly p x"
        by (metis neq sgn_def) 
      have h4: "z < x \<Longrightarrow>
        Matrix_Equation_Construction.sgn (poly p z) \<noteq> 0 \<Longrightarrow>
        Matrix_Equation_Construction.sgn (poly p x) \<noteq> 0 \<Longrightarrow>
        \<not> 0 < poly p z \<Longrightarrow> poly p z < 0"
        using h2 h3 by linarith
       have "((poly p x) > 0 \<and> (poly p z) < 0) \<or> ((poly p x) < 0 \<and> (poly p z) > 0) "
         using z_lt znonz xnonz h1 h2 h3 h4
         by auto
      then have "\<exists>w. w > x \<and> w < z \<and> (poly p w = 0)"
        using poly_IVT_pos[of z x] poly_IVT_neg[of z x]
        by (metis \<open>z < x\<close> not_less_iff_gr_or_eq zgt) 
      then show "False"
        using zgt
        using zleq by linarith 
    qed
    then show "Matrix_Equation_Construction.sgn (poly p x) = Matrix_Equation_Construction.sgn (poly p z)"
      by auto
  qed
  have "(\<exists>ub.
          (\<forall>x\<ge>ub. sgn_class.sgn (poly p x) = sgn_pos_inf p))"
    using root_ub[of p] pnonz 
    by meson 
  then obtain ub where ub_prop: "(\<forall>x\<ge>ub. sgn_class.sgn (poly p x) = sgn_pos_inf p)"
    by auto
  let ?ub2 = "max ub (z+1)"
  have "(\<forall>x\<ge>?ub2. sgn_class.sgn (poly p x) = sgn_pos_inf p) \<and> (?ub2 > z)"
    using ub_prop by auto
  then have h1: "(Sturm_Tarski.sign(sgn_class.sgn (poly p ?ub2)::real)) = Sturm_Tarski.sign(sgn_pos_inf p) \<and> (?ub2 > z)"
    by auto
  have "(Sturm_Tarski.sign(sgn_class.sgn (poly p ?ub2)::real)) = (sgn (poly p ?ub2))"
    unfolding sign_def sgn_def by auto
  then have "(sgn (poly p ?ub2)) = (Sturm_Tarski.sign(sgn_pos_inf p)) \<and> (?ub2 > z)" 
    using h1
    by metis 
  then have "\<forall>x\<ge>z. sgn (poly p x) = Sturm_Tarski.sign (sgn_pos_inf p)"
    using allx 
    by (metis dual_order.refl max.absorb3 max.bounded_iff) 
  then show ?thesis using xgt
    by auto
qed

lemma limit_pos_infinity_helper1:
  assumes q_in: "q \<in> set qs"
  assumes qnonz: "q \<noteq> 0"
  assumes "x = (crb (prod_list_var qs))"
  shows "(if (poly q x > 0) then (1::int) else (if (poly q x = 0) then (0::rat) else (-1::rat))) 
    = ((Sturm_Tarski.sign (sgn_pos_inf q))::int)"
  using poly_sgn_eventually_at_top[unfolded eventually_at_top_linorder] 
proof - 
  have "(\<exists>ub. (\<forall>x. poly q x = 0 \<longrightarrow> x < ub \<longrightarrow>
          (\<forall>x\<ge>ub. sgn_class.sgn (poly q x) = sgn_pos_inf q)))"
    using root_ub[of q] qnonz 
    by meson 
  then obtain ub where ub_prop: "(\<forall>x. poly q x = 0 \<longrightarrow> x < ub \<longrightarrow>
          (\<forall>x\<ge>ub. sgn_class.sgn (poly q x) = sgn_pos_inf q))"
    by auto
  show ?thesis
    proof -
    have "q \<in> set qs \<and> q \<noteq> 0"
      using q_in qnonz by blast
    then have f1: "\<forall>r. \<not> real_of_int (crb (prod_list_var qs)) \<le> r \<or> 0 \<noteq> poly q r"
      by (metis (no_types) nonzcrb[of q])
    have f2: "real_of_int (crb (prod_list_var qs)) \<le> real_of_int x"
      using assms(3) by force
    then have f3: "0 \<noteq> poly q (real_of_int x)"
      using f1 by blast
    have comb1: "\<And>z x. \<lbrakk>q \<noteq> 0; \<forall>x. poly q x = 0 \<longrightarrow> x < z; z \<le> x\<rbrakk> \<Longrightarrow> of_rat (Matrix_Equation_Construction.sgn (poly q x)) = complex_of_int (Sturm_Tarski.sign (sgn_pos_inf q))"
       using assms(2) root_ub_restate[of q] by auto
    obtain rr :: real where
      "q \<noteq> 0 \<and> (0 = poly q rr \<longrightarrow> rr < real_of_int (crb (prod_list_var qs))) \<and> real_of_int (crb (prod_list_var qs)) \<le> real_of_int x \<longrightarrow> Sturm_Tarski.sign (sgn_pos_inf q) = Matrix_Equation_Construction.sgn (poly q (real_of_int x))"
      by (metis comb1)
    then have f4: "Sturm_Tarski.sign (sgn_pos_inf q) = Matrix_Equation_Construction.sgn (poly q (real_of_int x))"
      using f2 f1 linorder_not_less qnonz by blast
    have "Matrix_Equation_Construction.sgn (poly q (real_of_int x)) = (if 0 < poly q (real_of_int x) then 1 else if poly q (real_of_int x) < 0 then - 1 else 0) \<and> (if 0 < poly q (real_of_int x) then (1::rat) = (if 0 < poly q (real_of_int x) then 1 else if poly q (real_of_int x) < 0 then - 1 else 0) else (if 0 < poly q (real_of_int x) then 1::rat else if poly q (real_of_int x) < 0 then - 1 else 0) = (if poly q (real_of_int x) < 0 then - 1 else 0)) \<and> (if poly q (real_of_int x) < 0 then - (1::rat) = (if poly q (real_of_int x) < 0 then - 1 else 0) else (0::rat) = (if poly q (real_of_int x) < 0 then - 1 else 0))"
      by (simp add: sgn_def)
    moreover
    { assume "- (1::int) \<noteq> (if poly q (real_of_int x) < 0 then - 1 else 0)"
      then have "0 < poly q (real_of_int x)"
        using f3 by (metis (no_types) not_less_iff_gr_or_eq) }
    ultimately show ?thesis
      by (smt (verit) Rat.of_rat_1 f4 of_int_hom.hom_one) 
  qed
qed

lemma limit_pos_infinity_helper2:
  assumes q_in: "q \<in> set qs"
  assumes qnonz: "q = 0"
  assumes "x = (crb (prod_list_var qs))"
  shows "(if (poly q x > 0) then (1::rat) else (if (poly q x = 0) then (0::rat) else (-1::rat))) 
    = ((Sturm_Tarski.sign (sgn_pos_inf q))::int)"
proof - 
  have "0 = ((Sturm_Tarski.sign (sgn_pos_inf q)))"
    by (simp add: qnonz sgn_pos_inf_def) 
  then show ?thesis using qnonz
    by auto 
qed

lemma limit_pos_infinity_helper:
  assumes q_in: "q \<in> set qs"
  assumes "x = (crb (prod_list_var qs))"
  shows "(if (poly q x > 0) then (1::int) else (if (poly q x = 0) then 0 else -1)) 
    = ((Sturm_Tarski.sign (sgn_pos_inf q)))"
  using limit_pos_infinity_helper1 limit_pos_infinity_helper2 assms(2) q_in
  by (smt (verit) Rat.of_rat_1 Sturm_Tarski.sign_cases of_int_eq_iff of_int_hom.hom_one of_int_hom.hom_zero of_rat_0 of_rat_neg_one one_neq_neg_one zero_neq_neg_one)

lemma Sturm_Tarski_casting:
  shows "((Sturm_Tarski.sign x)) = rat_of_int (Sturm_Tarski.sign x)"
  by (simp add: Sturm_Tarski.sign_def)

lemma limit_pos_infinity:
  shows "consistent_sign_vec qs (crb (prod_list_var qs)) = sgn_pos_inf_rat_list qs"
  unfolding consistent_sign_vec_def sgn_pos_inf_rat_list_def 
  using limit_pos_infinity_helper Sturm_Tarski_casting
  apply (auto) 
    apply fastforce
   apply presburger
  by (metis of_int_hom.hom_one of_int_minus)

lemma nonzcrb_helper_neg:
  assumes q_in: "q \<in> set qs"
  assumes qnonz: "q \<noteq> 0"
  assumes lengt: "length (sorted_list_of_set {(x::real). (\<exists>q \<in> set(qs). (q \<noteq> 0 \<and> poly q x = 0))} :: real list) > 0"
  shows " \<not>(\<exists>x \<le> (real_of_int (-crb (prod_list_var qs))). poly q x = 0)" 
proof clarsimp 
  fix x
  assume xlt: "x \<le> - real_of_int (crb (prod_list_var qs))" 
  assume pqz: "poly q x = 0"
  let ?zer_list = "sorted_list_of_set {(x::real). (\<exists>q \<in> set(qs). (q \<noteq> 0 \<and> poly q x = 0))} :: real list"
  have strict_sorted_h: "sorted_wrt (<) ?zer_list" using sorted_sorted_list_of_set
      strict_sorted_iff by auto
  have finset: "finite  {x. \<exists>q\<in>set qs. q \<noteq> 0 \<and> poly q x = 0}"
  proof - 
    have all_q: "\<forall>q \<in> set qs.  q\<noteq> 0 \<longrightarrow> finite {x. poly q x = 0} "
      using poly_roots_finite by auto
    then show ?thesis by auto
  qed
  have all_x: "\<forall>x \<in> {x. \<exists>q\<in>set qs. q \<noteq> 0 \<and> poly q x = 0}. poly (prod_list_var qs) x = 0"
    using q_dvd_prod_list_var_prop
    by fastforce 
  then have "poly (prod_list_var qs) (sorted_list_of_set {x. \<exists>q\<in>set qs. q \<noteq> 0 \<and> poly q x = 0} ! 0) = 0"
    using finset set_sorted_list_of_set
    by (metis (no_types, lifting) lengt nth_mem) 
  then have crbgt: "-crb (prod_list_var qs) < ?zer_list ! 0" using prod_list_var_nonzero crb_lem_pos[of "prod_list_var qs" "?zer_list ! (length ?zer_list - 1)"]
    using crb_lem_neg by blast
  have x_in: "x \<in> {x. \<exists>q\<in>set qs. q \<noteq> 0 \<and> poly q x = 0}"
    using pqz q_in qnonz 
    by auto
  then have "x \<in> set ?zer_list"
    by (smt (verit, best) finset in_set_member mem_Collect_eq set_sorted_list_of_set) 
  then have "x \<ge> ?zer_list ! 0" using strict_sorted_h
    by (smt (verit) all_x x_in crb_lem_neg linorder_not_le of_int_hom.hom_uminus prod_list_var_nonzero xlt) 
  then show "False" using xlt crbgt 
    by auto
qed

lemma nonzcrb_neg:
  assumes q_in: "q \<in> set qs"
  assumes qnonz: "q \<noteq> 0"
  shows " \<not>(\<exists>x \<le> (real_of_int (-crb (prod_list_var qs))). poly q x = 0)" 
proof - 
  let ?zer_list = "(sorted_list_of_set {(x::real). (\<exists>q \<in> set(qs). (q \<noteq> 0 \<and> poly q x = 0))} :: real list)"
  have eo: "length ?zer_list = 0 \<or> length ?zer_list > 0"
    by auto 
  have h1: "length ?zer_list = 0 \<longrightarrow> \<not>(\<exists>x \<le> (real_of_int (-crb (prod_list_var qs))). poly q x = 0)"
    by (metis crb_lem_neg dvdE linorder_not_less mult_zero_left poly_mult prod_list_var_nonzero q_dvd_prod_list_var_prop q_in qnonz)
  have h2: "length ?zer_list > 0 \<longrightarrow> \<not>(\<exists>x \<le> (real_of_int (-crb (prod_list_var qs))). poly q x = 0)"
    using nonzcrb_helper_neg assms
    by blast 
  show ?thesis using eo h1 h2 
    by auto 
qed

lemma root_lb_restate:
  fixes p:: "real poly"
  assumes pnonz: "p \<noteq> 0"
  fixes z::"real"
  assumes zgt: "\<forall>x. poly p x=0 \<longrightarrow> x > z"
  shows "x\<le>z \<Longrightarrow> sgn (poly p x) = Sturm_Tarski.sign (sgn_neg_inf p)"
proof - 
  assume xlt: "x \<le> z"
  have allx: "\<forall>x \<le> z. sgn (poly p x) = sgn (poly p z)"
  proof clarsimp 
    fix x
    assume zleq: "x \<le> z"
    then have xnonz: "sgn (poly p x) \<noteq> 0"
      using zgt unfolding sgn_def by auto
    have znonz: "sgn (poly p z) \<noteq> 0"
      using zgt unfolding sgn_def by auto 
    have "Matrix_Equation_Construction.sgn (poly p x) \<noteq> Matrix_Equation_Construction.sgn (poly p z) \<Longrightarrow> False"
    proof - 
      assume neq: "Matrix_Equation_Construction.sgn (poly p x) \<noteq> Matrix_Equation_Construction.sgn (poly p z)"
      then have "x < z" using zleq
        using less_eq_real_def by force
      then have "((poly p x) > 0 \<and> (poly p z) < 0) \<or> ((poly p x) < 0 \<and> (poly p z) > 0) "
        using znonz xnonz zgt neq sgn_def
        by metis
      then have "\<exists>w. w < x \<and> w > z \<and> (poly p w = 0)"
        using poly_IVT_pos[of x z] poly_IVT_neg[of x z]
        by (metis \<open>x < z\<close> not_less_iff_gr_or_eq zgt) 
      then show "False"
        using zgt zleq 
        by linarith 
    qed
    then show "Matrix_Equation_Construction.sgn (poly p x) = Matrix_Equation_Construction.sgn (poly p z)"
      by auto
  qed
  have "(\<exists>ub. (\<forall>x\<le>ub. sgn_class.sgn (poly p x) = sgn_neg_inf p))"
    using root_lb[of p] pnonz 
    by meson 
  then obtain lb where ub_prop: "(\<forall>x\<le>lb. sgn_class.sgn (poly p x) = sgn_neg_inf p)"
    by auto
  let ?ub2 = "min lb (z-1)"
  have "(\<forall>x\<le>?ub2. sgn_class.sgn (poly p x) = sgn_neg_inf p) \<and> (?ub2 < z)"
    using ub_prop by auto
  then have h1: "(Sturm_Tarski.sign(sgn_class.sgn (poly p ?ub2)::real)) = Sturm_Tarski.sign(sgn_neg_inf p) \<and> (?ub2 < z)"
    by auto
  have "(Sturm_Tarski.sign(sgn_class.sgn (poly p ?ub2)::real)) = (sgn (poly p ?ub2))"
    unfolding sign_def sgn_def by auto
  then have "(sgn (poly p ?ub2)) = (Sturm_Tarski.sign(sgn_neg_inf p)) \<and> (?ub2 < z)" 
    using h1 by metis
  then show ?thesis using allx xlt
    by (metis min.absorb3 min.cobounded2)
qed

lemma limit_neg_infinity_helper1:
  assumes q_in: "q \<in> set qs"
  assumes qnonz: "q \<noteq> 0"
  assumes "x = -(crb (prod_list_var qs))"
  shows "(if (poly q x > 0) then 1 else (if (poly q x = 0) then 0 else -1)) 
    = ((Sturm_Tarski.sign (sgn_neg_inf q)))"
proof - 
  have "(\<exists>ub. (\<forall>x. poly q x = 0 \<longrightarrow> x < ub \<longrightarrow>
          (\<forall>x\<ge>ub. sgn_class.sgn (poly q x) = sgn_neg_inf q)))"
    using root_lb[of q] qnonz
    by (meson not_less_iff_gr_or_eq)  
  then obtain ub where ub_prop: "(\<forall>x. poly q x = 0 \<longrightarrow> x < ub \<longrightarrow>
          (\<forall>x\<ge>ub. sgn_class.sgn (poly q x) = sgn_neg_inf q))"
    by auto
  show ?thesis
  proof -
    have "q \<in> set qs \<and> q \<noteq> 0"
      using \<open>q \<in> set qs\<close> \<open>q \<noteq> 0\<close> by blast
    then have f1: "\<forall>r. \<not> r \<le> real_of_int (- crb (prod_list_var qs)) \<or> 0 \<noteq> poly q r"
      using nonzcrb_neg[of q] by auto
    have f2: "real_of_int x \<le> real_of_int (- crb (prod_list_var qs))"
      using \<open>x = - crb (prod_list_var qs)\<close> by fastforce
    obtain rr :: real where
      f3: "q \<noteq> 0 \<and> (0 = poly q rr \<longrightarrow> real_of_int (- crb (prod_list_var qs)) < rr) \<and> real_of_int x \<le> real_of_int (- crb (prod_list_var qs)) \<longrightarrow> Sturm_Tarski.sign (sgn_neg_inf q) = Matrix_Equation_Construction.sgn (poly q (real_of_int x))"
      by (metis assms(2) root_lb_restate[of q])
    have "\<not> rr \<le> real_of_int (- crb (prod_list_var qs)) \<or> 0 \<noteq> poly q rr"
      using f1 by blast
    then have "Sturm_Tarski.sign (sgn_neg_inf q) = Matrix_Equation_Construction.sgn (poly q (real_of_int x))"
      using f3 f2 \<open>q \<noteq> 0\<close> by linarith
    then show ?thesis
      by (smt (verit, best) Sturm_Tarski.sign_def of_int_eq_iff of_int_hom.hom_one of_int_hom.hom_zero of_rat_hom.hom_0_iff of_rat_hom.hom_1_iff of_rat_neg_one sgn_def)
  qed
    (*  by (smt (verit, del_insts) linorder_not_less of_rat_hom.eq_iff of_rat_of_int_eq sgn_def)  *)
qed

lemma limit_neg_infinity_helper2:
  assumes q_in: "q \<in> set qs"
  assumes qnonz: "q = 0"
  assumes "x = (-crb (prod_list_var qs))"
  shows "(if (poly q x > 0) then 1 else (if (poly q x = 0) then 0 else -1)) 
    = Sturm_Tarski.sign (sgn_neg_inf q)"
proof - 
  have " 0 = Sturm_Tarski.sign (sgn_neg_inf q)"
    by (simp add: qnonz sgn_neg_inf_def) 
  then show ?thesis using qnonz 
    by auto 
qed

lemma limit_neg_infinity_helper_var:
  assumes q_in: "q \<in> set qs"
  assumes "x = (-crb (prod_list_var qs))"
  shows "(if (poly q x > 0) then 1 else (if (poly q x = 0) then 0 else -1)) 
    = Sturm_Tarski.sign (sgn_neg_inf q)"
  using limit_neg_infinity_helper1 limit_neg_infinity_helper2  assms(2) q_in
  by blast

lemma limit_neg_infinity_helper:
  assumes q_in: "q \<in> set qs"
  assumes "x = (-crb (prod_list_var qs))"
  shows "(if (poly q x > 0) then 1 else (if (poly q x = 0) then 0 else -1)) 
    = (Sturm_Tarski.sign (sgn_neg_inf q))"
  using limit_neg_infinity_helper_var Sturm_Tarski_casting[of "(sgn_neg_inf q)"]
  using assms(2) q_in by presburger 

lemma limit_neg_infinity:
  shows "consistent_sign_vec qs (-(crb (prod_list_var qs))) = sgn_neg_inf_rat_list qs"
  using limit_neg_infinity_helper Sturm_Tarski_casting
    consistent_sign_vec_def sgn_neg_inf_rat_list_def
  apply (auto) apply fastforce apply presburger
  by (metis (mono_tags, opaque_lifting) of_int_eq_1_iff of_int_minus)

lemma csv_signs_at_same:
  shows "consistent_sign_vec qs x = signs_at qs x"
  unfolding consistent_sign_vec_def signs_at_def squash_def by auto

lemma complex_real_int_casting:
  fixes z:: "int"
  shows "(complex_of_real \<circ> real_of_int) z = complex_of_int z"
  by auto

lemma poly_f_ncrb_constant_connection:
  assumes is_const: "check_all_const_deg qs = True"
  shows "set (characterize_consistent_signs_at_roots (poly_f qs) qs) 
    = set (characterize_consistent_signs_at_roots (poly_f_nocrb qs) qs) \<union> {sgn_neg_inf_rat_list qs, sgn_pos_inf_rat_list qs}"
proof -  
  have h1: "(poly_f qs)  = [:0, 1:] "
    using assms unfolding poly_f_def by auto 
  have h2: "(poly_f_nocrb qs)  = [:0, 1:] "
    using assms unfolding poly_f_nocrb_def by auto 
  then have same_set1: "set (characterize_consistent_signs_at_roots (poly_f qs) qs) 
    = set (characterize_consistent_signs_at_roots (poly_f_nocrb qs) qs)"
    using h1 h2
    by auto
  have "{x. poly (poly_f qs) x = 0} = {0}"
    using h1 by auto
  then have "(characterize_root_list_p (poly_f qs)) = [0]"
    using h1 unfolding characterize_root_list_p_def  by auto 
  then have "(characterize_consistent_signs_at_roots (poly_f qs) qs)
    = (remdups (map (signs_at qs) [0]))"
    unfolding characterize_consistent_signs_at_roots_def by auto 
  then have "(characterize_consistent_signs_at_roots (poly_f qs) qs) = [signs_at qs 0]"
    by auto
  then have same_set2: "set (characterize_consistent_signs_at_roots (poly_f_nocrb qs) qs) = {signs_at qs 0}"
    using same_set1
    by auto
  have same1: "sgn_neg_inf_rat_list qs = sgn_pos_inf_rat_list qs"
    using is_const unfolding sgn_neg_inf_rat_list_def sgn_pos_inf_rat_list_def 
    unfolding sgn_neg_inf_def sgn_pos_inf_def
    using check_all_const_deg_prop by auto 
  have "\<And>q. q \<in> set qs \<Longrightarrow> poly q 0 = lead_coeff q"
    using is_const check_all_const_deg_prop
    by (metis poly_0_coeff_0) 
  then have same2_h: "map (\<lambda>x. rat_of_int (Sturm_Tarski.sign (sgn_class.sgn (lead_coeff x)))) qs =  
    map ((\<lambda>x. if 0 < x then 1 else if x < 0 then - 1 else 0) \<circ> (\<lambda>q. poly q 0)) qs"
    by simp
  then have "map rat_of_int (sgn_pos_inf_rat_list qs) = (signs_at qs 0)"
    using is_const check_all_const_deg_prop 
    unfolding sgn_pos_inf_rat_list_def sgn_pos_inf_def signs_at_def squash_def 
    by auto
  then have " map real_of_rat (map rat_of_int (sgn_pos_inf_rat_list qs)) =
    map of_rat (signs_at qs 0)"
    by auto
  then have "map real_of_int (sgn_pos_inf_rat_list qs) = map of_rat (signs_at qs 0)"
    by auto 
  then have "map complex_of_real (map real_of_int (sgn_pos_inf_rat_list qs)) = map of_rat (signs_at qs 0)"
    by auto
  then have same2: "(sgn_pos_inf_rat_list qs) = (signs_at qs 0)"
    using complex_real_int_casting
    by (metis list.map_comp map_eq_conv)
  show ?thesis
    using same_set1 same_set2 same1 same2  
    by auto
qed

lemma poly_f_ncrb_nonconstant_connection:
  assumes is_not_const: "check_all_const_deg qs = False"
  shows "set (characterize_consistent_signs_at_roots (poly_f qs) qs) 
    = set (characterize_consistent_signs_at_roots (poly_f_nocrb qs) qs) \<union> {sgn_neg_inf_rat_list qs, sgn_pos_inf_rat_list qs}"
proof - 
  let ?s1 = "{x. poly (poly_f qs) x = 0}"
  let ?s2 = "({x. poly (poly_f_nocrb qs) x = 0} \<union> ({-(crb (prod_list_var qs)), (crb (prod_list_var qs))}::real set))" 
  have same_set: "?s1 = ?s2"
    using root_set_nocrb_var[of qs] is_not_const 
    by auto
  then have same_map: "(\<lambda>x. (signs_at qs x)) ` ?s1 = (\<lambda>x. (signs_at qs x)) ` ?s2"
    by presburger
  have "set (characterize_consistent_signs_at_roots (poly_f qs) qs) = 
  set (map (signs_at qs) (characterize_root_list_p (poly_f qs)))"
    using characterize_consistent_signs_at_roots_def by auto
  then have "set (characterize_consistent_signs_at_roots (poly_f qs) qs) = 
  (\<lambda>x. (signs_at qs x)) ` {x. poly (poly_f qs) x = 0}"
    by (simp add: characterize_root_list_p_def poly_f_nonzero poly_roots_finite)
  then have "set (characterize_consistent_signs_at_roots (poly_f qs) qs) = 
  (\<lambda>x. (signs_at qs x)) ` ({x. poly (poly_f_nocrb qs) x = 0} \<union> ({-(crb (prod_list_var qs)), (crb (prod_list_var qs))}::real set))"
    using  same_map by auto 
  then have bigeq: "set (characterize_consistent_signs_at_roots (poly_f qs) qs) = 
  (\<lambda>x. (signs_at qs x)) ` {x. poly (poly_f_nocrb qs) x = 0} \<union> (\<lambda>x. (signs_at qs x)) ` ({-(crb (prod_list_var qs)), (crb (prod_list_var qs))}::real set)"
    by (metis image_Un)
  have crb_seteq: "(\<lambda>x. (signs_at qs x)) ` ({-(crb (prod_list_var qs)), (crb (prod_list_var qs))}::real set) =
    (\<lambda>x. (signs_at qs x)) ` ({-(crb (prod_list_var qs))}::real set) \<union>
    (\<lambda>x. (signs_at qs x)) ` ({(crb (prod_list_var qs))}::real set)"
    by blast
  have neg: "(\<lambda>x. (signs_at qs x)) ` ({-(crb (prod_list_var qs))}::real set) ={sgn_neg_inf_rat_list qs}"
    using limit_neg_infinity[of qs] csv_signs_at_same by auto
  have pos: "(\<lambda>x. (signs_at qs x)) ` ({(crb (prod_list_var qs))}::real set) ={sgn_pos_inf_rat_list qs}"
    using limit_pos_infinity[of qs] csv_signs_at_same by auto
  have "(\<lambda>x. (signs_at qs x)) ` ({-(crb (prod_list_var qs)), (crb (prod_list_var qs))}::real set) = {sgn_neg_inf_rat_list qs} \<union> {sgn_pos_inf_rat_list qs}"
    using crb_seteq neg pos by auto 
  then have "(\<lambda>x. (signs_at qs x)) ` ({-(crb (prod_list_var qs)), (crb (prod_list_var qs))}::real set)
    = {sgn_neg_inf_rat_list qs, sgn_pos_inf_rat_list qs}"
    by auto
  then have biggereq: "set (characterize_consistent_signs_at_roots (poly_f qs) qs) =
    signs_at qs ` {x. poly (poly_f_nocrb qs) x = 0} \<union>
    {sgn_neg_inf_rat_list qs, sgn_pos_inf_rat_list qs}"
    using bigeq by auto
  have key: "signs_at qs ` {x. poly (poly_f_nocrb qs) x = 0} = set (characterize_consistent_signs_at_roots (poly_f_nocrb qs) qs)"
    using characterize_consistent_signs_at_roots_def
      Groups.mult_ac(2) characterize_root_list_p_def is_not_const list.set_map mult_cancel_left mult_cancel_left1 poly_f_def poly_f_nocrb_def poly_f_nonzero poly_roots_finite set_remdups sorted_list_of_set(1)
  proof -
    have "poly_f_nocrb qs \<noteq> 0"
      by (metis mult_cancel_left1 poly_f_def poly_f_nocrb_def poly_f_nonzero)
    then have "set (remdups (map (signs_at qs) (sorted_list_of_set {r. poly (poly_f_nocrb qs) r = 0}))) = signs_at qs ` {r. poly (poly_f_nocrb qs) r = 0}"
      by (simp add: poly_roots_finite)
    then show ?thesis
      using characterize_consistent_signs_at_roots_def characterize_root_list_p_def by presburger
  qed
  then show ?thesis using biggereq
    by (metis image_image list.set_map)
qed

lemma poly_f_ncrb_connection:
  shows "set (characterize_consistent_signs_at_roots (poly_f qs) qs) 
    = set (characterize_consistent_signs_at_roots (poly_f_nocrb qs) qs) \<union> {sgn_neg_inf_rat_list qs, sgn_pos_inf_rat_list qs}"
  using poly_f_ncrb_nonconstant_connection poly_f_ncrb_constant_connection
  by blast

end