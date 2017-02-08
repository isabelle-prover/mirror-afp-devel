(*
  File:   Landau_More.thy
  Author: Andreas Lochbihler, Manuel Eberl <eberlm@in.tum.de>

  Some more facts about Landau symbols.
*)
theory Landau_More
imports Landau_Simprocs
begin
  
lemma bigtheta_powr_1 [landau_simp]: 
  "eventually (\<lambda>x. (f x :: real) \<ge> 0) F \<Longrightarrow> (\<lambda>x. f x powr 1) \<in> \<Theta>[F](f)"
  by (intro bigthetaI_cong) (auto elim!: eventually_mono)

lemma bigtheta_powr_0 [landau_simp]: 
  "eventually (\<lambda>x. (f x :: real) \<noteq> 0) F \<Longrightarrow> (\<lambda>x. f x powr 0) \<in> \<Theta>[F](\<lambda>_. 1)"
  by (intro bigthetaI_cong) (auto elim!: eventually_mono)

lemma bigtheta_powr_nonzero [landau_simp]: 
  "eventually (\<lambda>x. (f x :: real) \<noteq> 0) F \<Longrightarrow> (\<lambda>x. if f x = 0 then g x else h x) \<in> \<Theta>[F](h)"
  by (intro bigthetaI_cong) (auto elim!: eventually_mono)

lemma bigtheta_powr_nonzero' [landau_simp]: 
  "eventually (\<lambda>x. (f x :: real) \<noteq> 0) F \<Longrightarrow> (\<lambda>x. if f x \<noteq> 0 then g x else h x) \<in> \<Theta>[F](g)"
  by (intro bigthetaI_cong) (auto elim!: eventually_mono)

lemma bigtheta_powr_nonneg [landau_simp]: 
  "eventually (\<lambda>x. (f x :: real) \<ge> 0) F \<Longrightarrow> (\<lambda>x. if f x \<ge> 0 then g x else h x) \<in> \<Theta>[F](g)"
  by (intro bigthetaI_cong) (auto elim!: eventually_mono)

lemma bigtheta_powr_nonneg' [landau_simp]: 
  "eventually (\<lambda>x. (f x :: real) \<ge> 0) F \<Longrightarrow> (\<lambda>x. if f x < 0 then g x else h x) \<in> \<Theta>[F](h)"
  by (intro bigthetaI_cong) (auto elim!: eventually_mono)    

lemma bigo_powr_iff:
  assumes "0 < p" "eventually (\<lambda>x. f x \<ge> 0) F" "eventually (\<lambda>x. g x \<ge> 0) F"
  shows "(\<lambda>x. (f x :: real) powr p) \<in> O[F](\<lambda>x. g x powr p) \<longleftrightarrow> f \<in> O[F](g)" (is "?lhs \<longleftrightarrow> ?rhs")
proof
  assume ?lhs
  with assms bigo_powr[OF this, of "inverse p"] show ?rhs 
    by (simp add: powr_powr landau_simps)
qed (insert assms, simp_all add: bigo_powr_nonneg)

lemma bigo_neg_powr_iff:
  assumes "p < 0" "eventually (\<lambda>x. f x \<ge> 0) F" "eventually (\<lambda>x. g x \<ge> 0) F"
                  "eventually (\<lambda>x. f x \<noteq> 0) F" "eventually (\<lambda>x. g x \<noteq> 0) F"
  shows "(\<lambda>x. (f x :: real) powr p) \<in> O[F](\<lambda>x. g x powr p) \<longleftrightarrow> g \<in> O[F](f)" (is "?lhs \<longleftrightarrow> ?rhs")
proof -
  have "(\<lambda>x. f x powr p) \<in> O[F](\<lambda>x. g x powr p) \<longleftrightarrow>
          (\<lambda>x. (inverse (f x)) powr -p) \<in> O[F](\<lambda>x. (inverse (g x)) powr -p)"
    using assms by (intro landau_o.big.cong_ex) (auto simp: powr_minus elim: eventually_mono)
  also from assms have "\<dots> \<longleftrightarrow> ((\<lambda>x. inverse (f x)) \<in> O[F](\<lambda>x. inverse (g x)))"
    by (subst bigo_powr_iff) simp_all
  also from assms have "\<dots> \<longleftrightarrow> g \<in> O[F](f)" by (simp add: landau_o.big.inverse_cancel)
  finally show ?thesis .
qed

lemma smallo_powr_iff:
  assumes "0 < p" "eventually (\<lambda>x. f x \<ge> 0) F" "eventually (\<lambda>x. g x \<ge> 0) F"
  shows "(\<lambda>x. (f x :: real) powr p) \<in> o[F](\<lambda>x. g x powr p) \<longleftrightarrow> f \<in> o[F](g)" (is "?lhs \<longleftrightarrow> ?rhs")
proof
  assume ?lhs
  with assms smallo_powr[OF this, of "inverse p"] show ?rhs 
    by (simp add: powr_powr landau_simps)
qed (insert assms, simp_all add: smallo_powr_nonneg)

lemma smallo_neg_powr_iff:
  assumes "p < 0" "eventually (\<lambda>x. f x \<ge> 0) F" "eventually (\<lambda>x. g x \<ge> 0) F"
                  "eventually (\<lambda>x. f x \<noteq> 0) F" "eventually (\<lambda>x. g x \<noteq> 0) F"
  shows "(\<lambda>x. (f x :: real) powr p) \<in> o[F](\<lambda>x. g x powr p) \<longleftrightarrow> g \<in> o[F](f)" (is "?lhs \<longleftrightarrow> ?rhs")
proof -
  have "(\<lambda>x. f x powr p) \<in> o[F](\<lambda>x. g x powr p) \<longleftrightarrow>
          (\<lambda>x. (inverse (f x)) powr -p) \<in> o[F](\<lambda>x. (inverse (g x)) powr -p)"
    using assms by (intro landau_o.small.cong_ex) (auto simp: powr_minus elim: eventually_mono)
  also from assms have "\<dots> \<longleftrightarrow> ((\<lambda>x. inverse (f x)) \<in> o[F](\<lambda>x. inverse (g x)))"
    by (subst smallo_powr_iff) simp_all
  also from assms have "\<dots> \<longleftrightarrow> g \<in> o[F](f)" by (simp add: landau_o.small.inverse_cancel)
  finally show ?thesis .
qed    

lemma const_smallo_powr:
  assumes "filterlim f at_top F" "F \<noteq> bot"
  shows "(\<lambda>_. c :: real) \<in> o[F](\<lambda>x. f x powr p) \<longleftrightarrow> p > 0 \<or> c = 0"
  by (rule linorder_cases[of p 0]; cases "c = 0")
     (insert assms smallo_powr_iff[of p "\<lambda>_. 1" F f] smallo_neg_powr_iff[of p f F "\<lambda>_. 1"],
      auto simp: landau_simps eventually_nonzero_simps smallo_1_iff[of F f] not_less 
           dest: landau_o.small_asymmetric simp: eventually_False landau_o.small_refl_iff)

lemma bigo_const_powr:
  assumes "filterlim f at_top F" "F \<noteq> bot"
  shows "(\<lambda>_. c :: real) \<in> O[F](\<lambda>x. f x powr p) \<longleftrightarrow> p \<ge> 0 \<or> c = 0"
proof -
  from assms have A: "(\<lambda>_. 1) \<in> o[F](f)"
    by (simp add: filterlim_at_top_iff_smallomega smallomega_iff_smallo landau_o.small_imp_big)
  hence B: "(\<lambda>_. 1) \<in> O[F](f)" "f \<notin> O[F](\<lambda>_. 1)" using assms
    by (auto simp: landau_o.small_imp_big dest: landau_o.small_big_asymmetric)
  show ?thesis
    by (rule linorder_cases[of p 0]; cases "c = 0")
       (insert insert assms A B bigo_powr_iff[of p "\<lambda>_. 1" F f] bigo_neg_powr_iff[of p "\<lambda>_. 1" F f],
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

lemma powr_fast_growth_tendsto:
  assumes gf: "g \<in> O[F](f)"
  and n: "n \<ge> 0"
  and k: "k > 1"
  and f: "filterlim f at_top F"
  and g: "eventually (\<lambda>x. g x \<ge> 0) F"
  shows "(\<lambda>x. g x powr n) \<in> o[F](\<lambda>x. k powr f x :: real)"
proof -
  from f have f': "eventually (\<lambda>x. f x \<ge> 0) F" by (simp add: eventually_nonzero_simps)
  from gf obtain c where c: "c > 0" "eventually (\<lambda>x. norm (g x) \<le> c * norm (f x)) F" 
    by (elim landau_o.bigE)
  from c(2) g f' have "eventually (\<lambda>x. g x \<le> c * f x) F" by eventually_elim simp
  from c(2) g f' have "eventually (\<lambda>x. norm (g x powr n) \<le> norm (c powr n * f x powr n)) F"
    by eventually_elim (insert n c(1), auto simp: powr_mult [symmetric] intro!: powr_mono2)
  from landau_o.big_mono[OF this] c(1) 
    have "(\<lambda>x. g x powr n) \<in> O[F](\<lambda>x. f x powr n)" by simp
  also from power_smallo_exponential f
    have "(\<lambda>x. f x powr n) \<in> o[F](\<lambda>x. k powr f x)" by (rule landau_o.small.compose) fact+
  finally show ?thesis .
qed

end