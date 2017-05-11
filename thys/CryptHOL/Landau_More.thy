(* Title: Landau_More.thy
  Author: Andreas Lochbihler, ETH Zurich
  Author: Manuel Eberl, TUM *)

theory Landau_More imports
  "../Landau_Symbols/Landau_Symbols"
begin

subsection \<open>Additions to @{theory Landau_Symbols}\<close>

lemma powr_realpow': "\<lbrakk> 0 \<le> x; n > 0 \<rbrakk> \<Longrightarrow> x powr real n = x ^ n"
by(cases "x = 0")(simp_all add: powr_realpow)

lemma bigtheta_powr_1 [landau_simp]: 
  "eventually (\<lambda>x. (f x :: real) \<ge> 0) at_top \<Longrightarrow> (\<lambda>x. f x powr 1) \<in> \<Theta>(f)"
  by (intro bigthetaI_cong) (auto elim!: eventually_mono)

lemma bigtheta_powr_0 [landau_simp]: 
  "eventually (\<lambda>x. (f x :: real) \<noteq> 0) at_top \<Longrightarrow> (\<lambda>x. f x powr 0) \<in> \<Theta>(\<lambda>_. 1)"
  by (intro bigthetaI_cong) (auto elim!: eventually_mono)

lemma bigtheta_powr_nonzero [landau_simp]: 
  "eventually (\<lambda>x. (f x :: real) \<noteq> 0) at_top \<Longrightarrow> (\<lambda>x. if f x = 0 then g x else h x) \<in> \<Theta>(h)"
  by (intro bigthetaI_cong) (auto elim!: eventually_mono)

lemma bigtheta_powr_nonzero' [landau_simp]: 
  "eventually (\<lambda>x. (f x :: real) \<noteq> 0) at_top \<Longrightarrow> (\<lambda>x. if f x \<noteq> 0 then g x else h x) \<in> \<Theta>(g)"
  by (intro bigthetaI_cong) (auto elim!: eventually_mono)

lemma bigtheta_powr_nonneg [landau_simp]: 
  "eventually (\<lambda>x. (f x :: real) \<ge> 0) at_top \<Longrightarrow> (\<lambda>x. if f x \<ge> 0 then g x else h x) \<in> \<Theta>(g)"
  by (intro bigthetaI_cong) (auto elim!: eventually_mono)

lemma bigtheta_powr_nonneg' [landau_simp]: 
  "eventually (\<lambda>x. (f x :: real) \<ge> 0) at_top \<Longrightarrow> (\<lambda>x. if f x < 0 then g x else h x) \<in> \<Theta>(h)"
  by (intro bigthetaI_cong) (auto elim!: eventually_mono)

lemma eventually_nonneg_at_top: 
  assumes "filterlim f at_top at_top"
  shows   "eventually_nonneg f"
proof -
  from assms have "eventually (\<lambda>x. f x \<ge> 0) at_top"
    by (simp add: filterlim_at_top)
  thus ?thesis unfolding eventually_nonneg_def by eventually_elim simp
qed

lemma eventually_nonzero_at_top: 
  assumes "filterlim f at_top at_top"
  shows   "eventually_nonzero f"
proof -
  from assms have "eventually (\<lambda>x. f x \<ge> 1) at_top"
    by (simp add: filterlim_at_top)
  thus ?thesis unfolding eventually_nonzero_def by eventually_elim simp
qed

lemma eventually_nonneg_at_top_ASSUMPTION [eventually_nonzero_simps]:
  "ASSUMPTION (filterlim f at_top at_top) \<Longrightarrow> eventually_nonneg f"
  by (simp add: ASSUMPTION_def eventually_nonneg_at_top)

lemma eventually_nonzero_at_top_ASSUMPTION [eventually_nonzero_simps]:
  "ASSUMPTION (filterlim f at_top at_top) \<Longrightarrow> eventually_nonzero f"
  by (simp add: ASSUMPTION_def eventually_nonzero_at_top)

lemma filterlim_at_top_iff_smallomega:
  fixes f :: "_ \<Rightarrow> 'a :: linordered_field"
  shows "filterlim f at_top at_top \<longleftrightarrow> f \<in> \<omega>(\<lambda>_. 1) \<and> eventually_nonneg f"
  unfolding eventually_nonneg_def
proof safe
  assume A: "filterlim f at_top at_top"
  thus B: "eventually (\<lambda>x. f x \<ge> 0) at_top" by (simp add: eventually_nonzero_simps)
  {
    fix c
    from A have "eventually (\<lambda>x. f x \<ge> c) at_top" by (simp add: filterlim_at_top)
    with B have "eventually (\<lambda>x. \<bar>f x\<bar> \<ge> c) at_top" 
      by eventually_elim (simp add: field_simps)
  }
  thus "f \<in> \<omega>(\<lambda>_. 1)" by (rule landau_omega.smallI)
next
  assume A: "f \<in> \<omega>(\<lambda>_. 1)" and B: "eventually (\<lambda>x. f x \<ge> 0) at_top"
  {
    fix c :: 'a assume "c > 0"
    from landau_omega.smallD[OF A this] B 
      have "eventually (\<lambda>x. f x \<ge> c) at_top" by eventually_elim simp
  }
  thus "filterlim f at_top at_top"
    by (subst filterlim_at_top_gt[of _ _ 0]) simp_all
qed

lemma smallomega_1_iff: 
  "eventually_nonneg f \<Longrightarrow> f \<in> \<omega>(\<lambda>_. 1) \<longleftrightarrow> filterlim f at_top at_top"
  by (simp add: filterlim_at_top_iff_smallomega)

lemma smallo_1_iff: 
  "eventually_nonneg f \<Longrightarrow> (\<lambda>_. 1) \<in> o(f) \<longleftrightarrow> filterlim f at_top at_top"
  by (simp add: filterlim_at_top_iff_smallomega smallomega_iff_smallo)

lemma eventually_nonneg_add1 [eventually_nonzero_simps]:
  assumes "eventually_nonneg f" "g \<in> o(f)"
  shows   "eventually_nonneg (\<lambda>x. f x + g x)"
  using  landau_o.smallD[OF assms(2) zero_less_one] assms(1) unfolding eventually_nonneg_def
  by eventually_elim simp_all

lemma eventually_nonneg_add2 [eventually_nonzero_simps]:
  assumes "eventually_nonneg g" "f \<in> o(g)"
  shows   "eventually_nonneg (\<lambda>x. f x + g x)"
  using  landau_o.smallD[OF assms(2) zero_less_one] assms(1) unfolding eventually_nonneg_def
  by eventually_elim simp_all

lemma eventually_nonneg_diff1 [eventually_nonzero_simps]:
  assumes "eventually_nonneg f" "g \<in> o(f)"
  shows   "eventually_nonneg (\<lambda>x. f x - g x)"
  using  landau_o.smallD[OF assms(2) zero_less_one] assms(1) unfolding eventually_nonneg_def
  by eventually_elim simp_all

lemma eventually_nonneg_diff2 [eventually_nonzero_simps]:
  assumes "eventually_nonneg (\<lambda>x. - g x)" "f \<in> o(g)"
  shows   "eventually_nonneg (\<lambda>x. f x - g x)"
  using  landau_o.smallD[OF assms(2) zero_less_one] assms(1) unfolding eventually_nonneg_def
  by eventually_elim simp_all
(* END TODO *)

   
lemma bigo_const_inverse [simp]:
  assumes "filterlim f at_top at_top"
  shows "(\<lambda>_ :: _ :: linorder. c) \<in> O(\<lambda>x. inverse (f x)) \<longleftrightarrow> c = 0"
proof -
  {
    assume A: "(\<lambda>_. 1) \<in> O(\<lambda>x. inverse (f x))"
    from assms have "(\<lambda>_. 1) \<in> o(f)"
      by (simp add: eventually_nonzero_simps smallomega_iff_smallo filterlim_at_top_iff_smallomega)
    also from assms A have "f \<in> O(\<lambda>_. 1)"
      by (simp add: eventually_nonzero_simps landau_divide_simps)
    finally have False by (simp add: landau_o.small_refl_iff)
  }
  thus ?thesis by (cases "c = 0") auto
qed
  
  lemma smallo_const_inverse [simp]:
  "filterlim f at_top at_top \<Longrightarrow> (\<lambda>_ :: _ :: linorder. c) \<in> o(\<lambda>x. inverse (f x)) \<longleftrightarrow> c = 0"
by(auto dest: landau_o.small_imp_big)

lemma bigo_powr_iff:
  assumes "0 < p" "eventually (\<lambda>x. f x \<ge> 0) at_top" "eventually (\<lambda>x. g x \<ge> 0) at_top"
  shows "(\<lambda>x. (f x :: real) powr p) \<in> O(\<lambda>x. g x powr p) \<longleftrightarrow> f \<in> O(g)" (is "?lhs \<longleftrightarrow> ?rhs")
proof
  assume ?lhs
  with assms bigo_powr[OF this, of "inverse p"] show ?rhs 
    by (simp add: powr_powr landau_simps)
qed (insert assms, simp_all add: bigo_powr_nonneg)

lemma bigo_neg_powr_iff:
  assumes "p < 0" "eventually (\<lambda>x. f x \<ge> 0) at_top" "eventually (\<lambda>x. g x \<ge> 0) at_top"
                  "eventually (\<lambda>x. f x \<noteq> 0) at_top" "eventually (\<lambda>x. g x \<noteq> 0) at_top"
  shows "(\<lambda>x. (f x :: real) powr p) \<in> O(\<lambda>x. g x powr p) \<longleftrightarrow> g \<in> O(f)" (is "?lhs \<longleftrightarrow> ?rhs")
proof -
  have "(\<lambda>x. f x powr p) \<in> O(\<lambda>x. g x powr p) \<longleftrightarrow>
          (\<lambda>x. (inverse (f x)) powr -p) \<in> O(\<lambda>x. (inverse (g x)) powr -p)"
    using assms by (intro landau_o.big.cong_ex) (auto simp: powr_minus elim: eventually_mono)
  also from assms have "\<dots> \<longleftrightarrow> ((\<lambda>x. inverse (f x)) \<in> O(\<lambda>x. inverse (g x)))"
    by (subst bigo_powr_iff) simp_all
  also from assms have "\<dots> \<longleftrightarrow> g \<in> O(f)" by (simp add: landau_o.big.inverse_cancel)
  finally show ?thesis .
qed

lemma bigo_abs_powr_iff [simp]:
  "0 < p \<Longrightarrow> (\<lambda>x. \<bar>f x :: real\<bar> powr p) \<in> O(\<lambda>x. \<bar>g x\<bar> powr p) \<longleftrightarrow> f \<in> O(g)"
  by(subst bigo_powr_iff; simp)

lemma smallo_powr_iff:
  assumes "0 < p" "eventually (\<lambda>x. f x \<ge> 0) at_top" "eventually (\<lambda>x. g x \<ge> 0) at_top"
  shows "(\<lambda>x. (f x :: real) powr p) \<in> o(\<lambda>x. g x powr p) \<longleftrightarrow> f \<in> o(g)" (is "?lhs \<longleftrightarrow> ?rhs")
proof
  assume ?lhs
  with assms smallo_powr[OF this, of "inverse p"] show ?rhs 
    by (simp add: powr_powr landau_simps)
qed (insert assms, simp_all add: smallo_powr_nonneg)

lemma smallo_neg_powr_iff:
  assumes "p < 0" "eventually (\<lambda>x. f x \<ge> 0) at_top" "eventually (\<lambda>x. g x \<ge> 0) at_top"
                  "eventually (\<lambda>x. f x \<noteq> 0) at_top" "eventually (\<lambda>x. g x \<noteq> 0) at_top"
  shows "(\<lambda>x. (f x :: real) powr p) \<in> o(\<lambda>x. g x powr p) \<longleftrightarrow> g \<in> o(f)" (is "?lhs \<longleftrightarrow> ?rhs")
proof -
  have "(\<lambda>x. f x powr p) \<in> o(\<lambda>x. g x powr p) \<longleftrightarrow>
          (\<lambda>x. (inverse (f x)) powr -p) \<in> o(\<lambda>x. (inverse (g x)) powr -p)"
    using assms by (intro landau_o.small.cong_ex) (auto simp: powr_minus elim: eventually_mono)
  also from assms have "\<dots> \<longleftrightarrow> ((\<lambda>x. inverse (f x)) \<in> o(\<lambda>x. inverse (g x)))"
    by (subst smallo_powr_iff) simp_all
  also from assms have "\<dots> \<longleftrightarrow> g \<in> o(f)" by (simp add: landau_o.small.inverse_cancel)
  finally show ?thesis .
qed
    
lemma smallo_abs_powr_iff [simp]:
  "0 < p \<Longrightarrow> (\<lambda>x. \<bar>f x :: real\<bar> powr p) \<in> o(\<lambda>x. \<bar>g x\<bar> powr p) \<longleftrightarrow> f \<in> o(g)"
  by(subst smallo_powr_iff; simp)

lemma const_in_smallo_const [simp]: "(\<lambda>_. b) \<in> o(\<lambda>_ :: _ :: linorder. c) \<longleftrightarrow> b = 0" (is "?lhs \<longleftrightarrow> ?rhs")
  by (cases "b = 0"; cases "c = 0") (simp_all add: landau_o.small_refl_iff)

lemma const_smallo_powr:
  assumes "filterlim f at_top at_top"
  shows "(\<lambda>_ :: _ :: linorder. c :: real) \<in> o(\<lambda>x. f x powr p) \<longleftrightarrow> p > 0 \<or> c = 0"
  by (rule linorder_cases[of p 0]; cases "c = 0")
     (insert assms smallo_powr_iff[of p "\<lambda>_. 1" f] smallo_neg_powr_iff[of p f "\<lambda>_. 1"],
      auto simp: landau_simps eventually_nonzero_simps smallo_1_iff[of f] not_less 
           dest: landau_o.small_asymmetric)

lemma bigo_const_powr:
  assumes "filterlim f at_top at_top"
  shows "(\<lambda>_ :: _ :: linorder. c :: real) \<in> O(\<lambda>x. f x powr p) \<longleftrightarrow> p \<ge> 0 \<or> c = 0"
proof -
  from assms have A: "(\<lambda>_. 1) \<in> o(f)" 
    by (simp add: filterlim_at_top_iff_smallomega smallomega_iff_smallo landau_o.small_imp_big)
  hence B: "(\<lambda>_. 1) \<in> O(f)" "f \<notin> O(\<lambda>_. 1)"
    by (auto simp: landau_o.small_imp_big dest: landau_o.small_big_asymmetric)
  show ?thesis
    by (rule linorder_cases[of p 0]; cases "c = 0")
       (insert insert assms A B bigo_powr_iff[of p "\<lambda>_. 1" f] bigo_neg_powr_iff[of p "\<lambda>_. 1" f],
        auto simp: landau_simps eventually_nonzero_simps not_less dest: landau_o.small_asymmetric)
qed

lemma filterlim_powr_at_top:
  "(b::real) > 1 \<Longrightarrow> filterlim (\<lambda>x. b powr x) at_top at_top"
  unfolding powr_def mult.commute[of _ "ln b"]
  by (auto intro!: filterlim_compose[OF exp_at_top] 
        filterlim_tendsto_pos_mult_at_top filterlim_ident)

lemma power_smallo_exponential:
  fixes b :: real
  assumes b: "b > 1"
  shows "(\<lambda>x. x powr n) \<in> o(\<lambda>x. b powr x)"
proof (rule smalloI_tendsto)
  from assms have "filterlim (\<lambda>x. x * ln b - n * ln x) at_top at_top" 
    by (simp add: filterlim_at_top_iff_smallomega eventually_nonzero_simps)
  hence "((\<lambda>x. exp (-(x * ln b - n * ln x))) \<longlongrightarrow> 0) at_top" (is ?A)
    by (intro filterlim_compose[OF exp_at_bot] 
              filterlim_compose[OF filterlim_uminus_at_bot_at_top])
  also have "?A \<longleftrightarrow> ((\<lambda>x. x powr n / b powr x) \<longlongrightarrow> 0) at_top"
    using b eventually_gt_at_top[of 0]
    by (intro tendsto_cong) 
       (auto simp: exp_diff powr_def field_simps exp_of_nat_mult elim: eventually_mono)
  finally show "((\<lambda>x. x powr n / b powr x) \<longlongrightarrow> 0) at_top" .
qed (insert assms, simp_all add: eventually_nonzero_simps)

lemma const_smallo_inverse_powr:
  assumes "filterlim f at_top at_top"
  shows "(\<lambda>_ :: _ :: linorder. c :: real) \<in> o(\<lambda>x. inverse (f x powr p)) \<longleftrightarrow> (p \<ge> 0 \<longrightarrow> c = 0)"
proof(cases p "0 :: real" rule: linorder_cases)
  case p: greater
  have "(\<lambda>_. c) \<in> o(\<lambda>x. inverse (f x powr p)) \<longleftrightarrow> (\<lambda>_. \<bar>c\<bar>) \<in> o(\<lambda>x. inverse (f x powr p))" by simp
  also have "\<bar>c\<bar> = \<bar>(\<bar>c\<bar> powr (inverse p))\<bar> powr p" using p by(simp add: powr_powr)
  also { have "eventually (\<lambda>x. f x \<ge> 0) at_top" using assms by(simp add: filterlim_at_top)
    then have "o(\<lambda>x. inverse (f x powr p)) = o(\<lambda>x. \<bar>inverse (f x)\<bar> powr p)"
      by(intro landau_o.small.cong)(auto elim!: eventually_rev_mp)
    also have "(\<lambda>_. \<bar>(\<bar>c\<bar> powr inverse p)\<bar> powr p) \<in> \<dots> \<longleftrightarrow> (\<lambda>_. \<bar>c\<bar> powr (inverse p)) \<in> o(\<lambda>x. inverse (f x))"
      using p by(rule smallo_abs_powr_iff)
    also note calculation }
  also have "(\<lambda>_. \<bar>c\<bar> powr (inverse p)) \<in> o(\<lambda>x. inverse (f x)) \<longleftrightarrow> c = 0" using assms by simp
  finally show ?thesis using p by simp
next
  case equal
  from assms have "eventually (\<lambda>x. f x \<ge> 1) at_top" using assms by(simp add: filterlim_at_top)
  then have "o(\<lambda>x. inverse (f x powr p)) = o(\<lambda>x. 1)"
    by(intro landau_o.small.cong)(auto simp add: equal elim!: eventually_rev_mp)
  then show ?thesis using equal by simp
next
  case less
  from assms have nonneg: "\<forall>\<^sub>F x in at_top. 0 \<le> f x" by(simp add: filterlim_at_top)
  with assms have "\<forall>\<^sub>F x in at_top. \<bar>\<bar>c\<bar> powr (1 / - p)\<bar> / d \<le> \<bar>f x\<bar>" (is "\<forall>\<^sub>F x in _. ?c \<le> _") if "d > 0" for d
    by(fastforce dest!: spec[where x="?c"] simp add: filterlim_at_top elim: eventually_rev_mp)
  then have "(\<lambda>_. \<bar>c\<bar> powr (1 / - p)) \<in> o(f)" by(intro landau_o.smallI)(simp add: field_simps)
  then have "(\<lambda>_. \<bar>\<bar>c\<bar> powr (1 / - p)\<bar> powr - p) \<in> o(\<lambda>x. \<bar>f x\<bar> powr - p)"
    using less by(subst smallo_powr_iff) simp_all
  also have "(\<lambda>_. \<bar>\<bar>c\<bar> powr (1 / - p)\<bar> powr - p) = (\<lambda>_. \<bar>c\<bar>)" using less by(simp add: powr_powr)
  also have "o(\<lambda>x. \<bar>f x\<bar> powr - p) = o(\<lambda>x. f x powr - p)" using nonneg
    by(auto intro!: landau_o.small.cong elim: eventually_rev_mp)
  finally have "(\<lambda>_. c) \<in> o(\<lambda>x. f x powr - p)" by simp
  with less show ?thesis by(simp add: powr_minus[symmetric])
qed

lemma bigo_const_inverse_powr:
  assumes "filterlim f at_top at_top"
  shows "(\<lambda>_ :: _ :: linorder. c :: real) \<in> O(\<lambda>x. inverse (f x powr p)) \<longleftrightarrow> c = 0 \<or> p \<le> 0"
proof(cases p "0 :: real" rule: linorder_cases)
  case p_pos: greater
  have "(\<lambda>_. c) \<in> O(\<lambda>x. inverse (f x powr p)) \<longleftrightarrow> (\<lambda>_. \<bar>c\<bar>) \<in> O(\<lambda>x. inverse (f x powr p))" by simp
  also have "\<bar>c\<bar> = \<bar>(\<bar>c\<bar> powr inverse p)\<bar> powr p" using p_pos by(simp add: powr_powr)
  also { have "eventually (\<lambda>x. f x \<ge> 0) at_top" using assms by(simp add: filterlim_at_top)
    then have "O(\<lambda>x. inverse (f x powr p)) = O(\<lambda>x. \<bar>inverse (f x)\<bar> powr p)"
      by(intro landau_o.big.cong)(auto elim!: eventually_rev_mp)
    also have "(\<lambda>_. \<bar>(\<bar>c\<bar> powr inverse p)\<bar> powr p) \<in> \<dots> \<longleftrightarrow> (\<lambda>_. \<bar>c\<bar> powr (inverse p)) \<in> O(\<lambda>x. inverse (f x))"
      using p_pos by(rule bigo_abs_powr_iff)
    also note calculation }
  also have "(\<lambda>_. \<bar>c\<bar> powr (inverse p)) \<in> O(\<lambda>x. inverse (f x)) \<longleftrightarrow> c = 0" using assms by simp
  finally show ?thesis using p_pos by simp
next
  case equal
  from assms have "eventually (\<lambda>x. f x \<ge> 1) at_top" using assms by(simp add: filterlim_at_top)
  then have "O(\<lambda>x. inverse (f x powr p)) = O(\<lambda>x. 1)"
    by(intro landau_o.big.cong)(auto simp add: equal elim!: eventually_rev_mp)
  then show ?thesis using equal by simp
next
  case less
  from assms have *: "\<forall>\<^sub>F x in at_top. 1 \<le> f x" by(simp add: filterlim_at_top)
  then have "(\<lambda>_. \<bar>c\<bar> powr (1 / - p)) \<in> O(f)" 
    by(intro bigoI[where c="\<bar>c\<bar> powr (1 / - p)"])
      (auto intro: order_trans[OF _ mult_left_mono, rotated] elim!: eventually_rev_mp[OF _ always_eventually])
  then have "(\<lambda>_. \<bar>\<bar>c\<bar> powr (1 / - p)\<bar> powr - p) \<in> O(\<lambda>x. \<bar>f x\<bar> powr - p)"
    using less by(subst bigo_powr_iff) simp_all
  also have "(\<lambda>_. \<bar>\<bar>c\<bar> powr (1 / - p)\<bar> powr - p) = (\<lambda>_. \<bar>c\<bar>)" using less by(simp add: powr_powr)
  also have "O(\<lambda>x. \<bar>f x\<bar> powr - p) = O(\<lambda>x. f x powr - p)" using *
    by(auto intro!: landau_o.big.cong elim: eventually_rev_mp)
  finally have "(\<lambda>_. c) \<in> O(\<lambda>x. f x powr - p)" by simp
  thus ?thesis using less by(simp add: powr_minus[symmetric])
qed

lemma tendsto_power_div_powr_0:
  fixes b :: real
  assumes b: "b > 1"
  shows "((\<lambda>x. x ^ n / b powr x) \<longlongrightarrow> 0) at_top"
proof (induct n)
  case 0
  show ?case using b
    by(simp add: inverse_eq_divide[symmetric] filterlim_compose[OF tendsto_inverse_0] filterlim_mono[OF filterlim_powr_at_top at_top_le_at_infinity order_refl])
next
  case (Suc k)
  show ?case
  proof (rule lhospital_at_top_at_top)
    show "eventually (\<lambda>x. DERIV (\<lambda>x. x ^ Suc k) x :> (real (Suc k) * x^k)) at_top"
      by eventually_elim (intro derivative_eq_intros, auto)
    show "eventually (\<lambda>x. DERIV (op powr b) x :> b powr x * (1 * ln b + 0 * x / b)) at_top"
      apply(eventually_elim; rule Transcendental.DERIV_powr)
      using b by(auto)
    show "\<forall>\<^sub>F x in at_top. b powr x * (1 * ln b + 0 * x / b) \<noteq> 0" using b by simp
    from tendsto_mult[OF tendsto_const Suc, of "real (Suc k) / ln b"]
    show "((\<lambda>x. real (Suc k) * x ^ k / (b powr x * (1 * ln b + 0 * x / b))) \<longlongrightarrow> 0) at_top"
      by(simp add: field_simps)
  qed (rule filterlim_powr_at_top[OF b])
qed

lemma poly_smallo_exp:
  assumes gf: "g \<in> O(f)"
  and n: "n \<ge> 0"
  and k: "k > 1"
  and f: "filterlim f at_top at_top"
  and g: "eventually (\<lambda>x. g x \<ge> 0) at_top"
  shows "(\<lambda>x. g x powr n) \<in> o(\<lambda>x. k powr f x :: real)"
proof -
  from f have f': "eventually (\<lambda>x. f x \<ge> 0) at_top" by (simp add: eventually_nonzero_simps)
  from gf obtain c where c: "c > 0" "eventually (\<lambda>x. \<bar>g x\<bar> \<le> c * \<bar>f x\<bar>) at_top" 
    by (elim landau_o.bigE)
  from c(2) g f' have "eventually (\<lambda>x. g x \<le> c * f x) at_top" by eventually_elim simp
  from c(2) g f' have "eventually (\<lambda>x. \<bar>g x powr n\<bar> \<le> \<bar>c powr n * f x powr n\<bar>) at_top"
    by eventually_elim (insert n c(1), auto simp: powr_mult [symmetric] intro!: powr_mono2)
  from landau_o.big_mono[OF this] c(1) 
    have "(\<lambda>x. g x powr n) \<in> O(\<lambda>x. f x powr n)" by simp
  also from power_smallo_exponential f
    have "(\<lambda>x. f x powr n) \<in> o(\<lambda>x. k powr f x)" by (rule smallo_compose) fact+
  finally show ?thesis .
qed

end
