(*
  File:     More_Beta.thy
  Author:   Manuel Eberl, University of Innsbruck
*)
section \<open>Integral forms of the Beta function\<close>
theory More_Beta
  imports "HOL-Complex_Analysis.Complex_Analysis" More_Dominated_Convergence
begin

(* TODO: Move to HOL-Analysis.Gamma *)
lemma Gamma_legendre_duplication_real:
  fixes z :: real
  assumes "z \<notin> \<int>\<^sub>\<le>\<^sub>0" "z + 1/2 \<notin> \<int>\<^sub>\<le>\<^sub>0"
  shows "Gamma z * Gamma (z + 1/2) = 2 powr (1 - 2 * z) * sqrt pi * Gamma (2*z)"
proof -
  have "complex_of_real (Gamma z * Gamma (z + 1/2)) = Gamma (of_real z) * Gamma (of_real z + 1/2)"
    by (simp flip: Gamma_complex_of_real)
  also have "\<dots> = of_real (exp ((1 - 2 * z) * (ln 2)) * sqrt pi * Gamma (2 * z))"
    using assms of_real_in_nonpos_Ints_iff[of z, where ?'a = complex]
          of_real_in_nonpos_Ints_iff[of "z + 1/2", where ?'a = complex]
    by (subst Gamma_legendre_duplication) (auto simp: of_real_exp simp flip: Gamma_complex_of_real)
  also have "exp ((1 - 2 * z) * (ln 2)) = 2 powr (1 - 2 * z)"
    by (simp add: powr_def)
  finally show ?thesis
    by (simp only: of_real_eq_iff)
qed

(* TODO: Move to HOL-Analysis.Gamma *)
lemma Gamma_int_plus_half:
  "Gamma (real n + 1 / 2) = sqrt pi * fact (2 * n) / (4 ^ n * fact n)"
proof (cases "n = 0")
  case False
  hence "real n \<notin> \<int>\<^sub>\<le>\<^sub>0" "real n + 1 / 2 \<notin> \<int>\<^sub>\<le>\<^sub>0"
    by auto
  hence "Gamma (real n) * Gamma (real n + 1 / 2) =
           2 powr (1 - 2 * real n) * sqrt pi * Gamma (2 * real n)"
    by (rule Gamma_legendre_duplication_real)
  also have "Gamma (real n) = fact (n - 1)"
    using False by (simp flip: Gamma_fact add: of_nat_diff)
  also have "Gamma (2 * real n) = fact (2 * n - 1)"
    using False by (simp flip: Gamma_fact add: of_nat_diff)
  finally have "Gamma (real n + 1 / 2) = 2 powr (1 - 2 * real n) * sqrt pi * (fact (2 * n - 1) / fact (n - 1))"
    by (simp add: field_simps)
  also have "fact (2 * n - 1) / fact (n - 1) = fact (2 * n) / fact n / (2 :: real)"
    using False by (simp add: fact_reduce[of n] fact_reduce[of "n * 2"] field_simps)
  also have "2 powr (1 - 2 * real n) * sqrt pi * (fact (2 * n) / fact n / 2) =
               sqrt pi * fact (2 * n) / (4 ^ n * fact n)"
    by (simp add: powr_diff powr_realpow flip: powr_powr)
  finally show ?thesis .
qed (auto simp: Gamma_one_half_real)


(* TODO: stolen from Zeta_Library. Clean up. *)
lemma has_field_derivative_complex_powr_right:
  "w \<noteq> 0 \<Longrightarrow> ((\<lambda>z. w powr z) has_field_derivative Ln w * w powr z) (at z within A)"
  by (rule DERIV_subset, rule has_field_derivative_powr_right) auto

(* TODO: stolen from Zeta_Library. Clean up. *)
lemmas has_field_derivative_complex_powr_right' =
  has_field_derivative_complex_powr_right[THEN DERIV_chain2]

(* TODO: stolen from Zeta_Library. Clean up. *)
lemma uniform_limit_set_lebesgue_integral:
  fixes f :: "'a \<Rightarrow> 'b :: euclidean_space \<Rightarrow> 'c :: {banach, second_countable_topology}"
  assumes "set_integrable lborel X' g"
  assumes [measurable]: "X' \<in> sets borel"
  assumes [measurable]: "\<And>y. y \<in> Y \<Longrightarrow> set_borel_measurable borel X' (f y)"
  assumes "\<And>y. y \<in> Y \<Longrightarrow> (AE t\<in>X' in lborel. norm (f y t) \<le> g t)"
  assumes "eventually (\<lambda>x. X x \<in> sets borel \<and> X x \<subseteq> X') F"
  assumes "filterlim (\<lambda>x. set_lebesgue_integral lborel (X x) g)
             (nhds (set_lebesgue_integral lborel X' g)) F"
  shows "uniform_limit Y
           (\<lambda>x y. set_lebesgue_integral lborel (X x) (f y))
           (\<lambda>y. set_lebesgue_integral lborel X' (f y)) F"
proof (rule uniform_limitI, goal_cases)
  case (1 \<epsilon>)
  have integrable_g: "set_integrable lborel U g"
    if "U \<in> sets borel" "U \<subseteq> X'" for U
    by (rule set_integrable_subset[OF assms(1)]) (use that in auto)
  have "eventually (\<lambda>x. dist (set_lebesgue_integral lborel (X x) g)
                             (set_lebesgue_integral lborel X' g) < \<epsilon>) F"
    using \<open>\<epsilon> > 0\<close> assms by (auto simp: tendsto_iff)
  from this show ?case using \<open>eventually (\<lambda>_. _ \<and> _) F\<close>
  proof eventually_elim
    case (elim x)
    hence [measurable]:"X x \<in> sets borel" and "X x \<subseteq> X'" by auto
    have integrable: "set_integrable lborel U (f y)"
      if "y \<in> Y" "U \<in> sets borel" "U \<subseteq> X'" for y U
      apply (rule set_integrable_subset)
        apply (rule set_integrable_bound[OF assms(1)])
         apply (use assms(3) that in \<open>simp add: set_borel_measurable_def\<close>)
      using assms(4)[OF \<open>y \<in> Y\<close>] apply eventually_elim apply force
      using that apply simp_all
      done
    show ?case
    proof
      fix y assume "y \<in> Y"
      have "dist (set_lebesgue_integral lborel (X x) (f y))
                 (set_lebesgue_integral lborel X' (f y)) =
            norm (set_lebesgue_integral lborel X' (f y) -
                  set_lebesgue_integral lborel (X x) (f y))"
        by (simp add: dist_norm norm_minus_commute)
      also have "set_lebesgue_integral lborel X' (f y) -
                    set_lebesgue_integral lborel (X x) (f y) =
                 set_lebesgue_integral lborel (X' - X x) (f y)"
        unfolding set_lebesgue_integral_def
        apply (subst Bochner_Integration.integral_diff [symmetric])
        unfolding set_integrable_def [symmetric]
          apply (rule integrable; (fact | simp))
         apply (rule integrable; fact)
        apply (intro Bochner_Integration.integral_cong)
         apply (use \<open>X x \<subseteq> X'\<close> in \<open>auto simp: indicator_def\<close>)
        done
      also have "norm \<dots> \<le> (\<integral>t\<in>X'-X x. norm (f y t) \<partial>lborel)"
        by (intro set_integral_norm_bound integrable) (fact | simp)+
      also have "AE t\<in>X' - X x in lborel. norm (f y t) \<le> g t"
        using assms(4)[OF \<open>y \<in> Y\<close>] by eventually_elim auto
      with \<open>y \<in> Y\<close> have "(\<integral>t\<in>X'-X x. norm (f y t) \<partial>lborel) \<le> (\<integral>t\<in>X'-X x. g t \<partial>lborel)"
        by (intro set_integral_mono_AE set_integrable_norm integrable integrable_g) auto
      also have "\<dots> = (\<integral>t\<in>X'. g t \<partial>lborel) - (\<integral>t\<in>X x. g t \<partial>lborel)"
        unfolding set_lebesgue_integral_def
        apply (subst Bochner_Integration.integral_diff [symmetric])
        unfolding set_integrable_def [symmetric]
          apply (rule integrable_g; (fact | simp))
         apply (rule integrable_g; fact)
        apply (intro Bochner_Integration.integral_cong)
         apply (use \<open>X x \<subseteq> X'\<close> in \<open>auto simp: indicator_def\<close>)
        done
      also have "\<dots> \<le> dist (\<integral>t\<in>X x. g t \<partial>lborel) (\<integral>t\<in>X'. g t \<partial>lborel)"
        by (simp add: dist_norm)
      also have "\<dots> < \<epsilon>" by fact
      finally show "dist (set_lebesgue_integral lborel (X x) (f y))
                         (set_lebesgue_integral lborel X' (f y)) < \<epsilon>" .
    qed
  qed
qed

lemma Beta_nonneg_real:
  assumes "a > 0" "b > 0"
  shows   "Beta a (b::real) \<ge> 0"
  by (rule has_integral_nonneg[OF has_integral_Beta_real]) (use assms in auto)

text \<open>
  The Beta function is given by the following integral:
  \[B(a,b) = \int_0^1 t^{a-1} (1-t)^{b-1}\,\text{d}t\]
\<close>
lemma has_integral_Beta_complex:
  assumes a: "Re a > 0" and b: "Re b > 0"
  shows "((\<lambda>t. of_real t powr (a - 1) * of_real (1 - t) powr (b - 1)) 
           has_integral Beta a b) {0<..<1}"
    and "(\<lambda>t. of_real t powr (a - 1) * of_real (1 - t) powr (b - 1))
           absolutely_integrable_on {0<..<1}"
proof -
  define f :: "complex \<Rightarrow> complex \<Rightarrow> real \<Rightarrow> complex"
    where "f = (\<lambda>a b t. of_real t powr (a - 1) * of_real (1 - t) powr (b - 1))"
  define F where "F = (\<lambda>a b. integral {0..1} (f a b))"

  have integrable: "f w z absolutely_integrable_on A" 
    if wz: "Re w > 0" "Re z > 0" and A: "A \<subseteq> {0..1}" "A \<in> sets lebesgue" for A w z
  proof (rule set_integrable_subset)
    have "(\<lambda>t. t powr (Re w - 1) * (1 - t) powr (Re z - 1)) integrable_on {0..1}"
      using integrable_Beta'[of "Re w" "Re z"] wz by simp
    also have "?this \<longleftrightarrow> (\<lambda>x. norm (f w z x)) integrable_on {0..1}"
      by (intro integrable_cong)
         (auto simp: f_def norm_mult norm_powr_complex simp del: of_real_diff)
    finally have "(\<lambda>x. norm (f w z x)) absolutely_integrable_on {0..1}"
      by (rule nonnegative_absolutely_integrable_1) auto
    hence "integrable lebesgue (\<lambda>x. norm (indicator {0..1} x *\<^sub>R f w z x))"
      by (simp add: set_integrable_def)
    thus "f w z absolutely_integrable_on {0..1}" unfolding set_integrable_def 
      by (rule Bochner_Integration.integrable_norm_cancel) (simp add: f_def measurable_completion)
  qed (use A in auto)

  show "(\<lambda>t. of_real t powr (a - 1) * of_real (1 - t) powr (b - 1))
           absolutely_integrable_on {0<..<1}"
    using integrable[of a b "{0<..<1}"] a b
    by (simp add: f_def greaterThanLessThan_subseteq_atLeastAtMost_iff)

  have integral_eq: "integral A (f w z) = set_lebesgue_integral lborel A (f w z)"
    if wz: "Re w > 0" "Re z > 0" and A: "A \<subseteq> {0..1}" "A \<in> sets lborel" for A w z
  proof -
    have "integral A (f w z) = set_lebesgue_integral lebesgue A (f w z)"
      using integrable[OF wz, of A] A
      by (intro set_lebesgue_integral_eq_integral(2) [symmetric]) auto
    also have "\<dots> = set_lebesgue_integral lborel A (f w z)"
      unfolding set_lebesgue_integral_def
      by (rule integral_completion) (use A in \<open>auto simp: f_def\<close>)
    finally show ?thesis .
  qed

  have ana: "(\<lambda>w. F w z) analytic_on {w}" "(\<lambda>z. F w z) analytic_on {z}"
       if wz: "Re w > 0" "Re z > 0" for w z
  proof -
    define a where "a = Re w / 2"
    define b where "b = Re z / 2"
    have ab: "a > 0" "b > 0" "a < Re w" "b < Re z"
      using wz by (auto simp: a_def b_def)

    define A :: "(complex \<times> complex) set" where "A = {w. Re w > a} \<times> {z. Re z > b}"
    have A: "open A" "(w,z) \<in> A"
      using ab by (auto simp: A_def open_Times open_halfspace_Re_gt)
    
    have lim: "uniform_limit A (\<lambda>x (a,b). LBINT t:{x..1-x}. f a b t) 
                 (\<lambda>(a,b). LBINT t:{0..1}. f a b t) (at_right 0)"
      unfolding case_prod_unfold
    proof (intro uniform_limit_set_lebesgue_integral)
      have "(\<lambda>t. t powr (a - 1) * (1 - t) powr (b - 1)) integrable_on {0..1}"
        using integrable_Beta'[of a b] ab by simp
      hence "(\<lambda>t. t powr (a - 1) * (1 - t) powr (b - 1)) absolutely_integrable_on {0..1}"
        by (rule nonnegative_absolutely_integrable_1) auto
      thus "set_integrable lborel {0..1} (\<lambda>t. t powr (a - 1) * (1 - t) powr (b - 1))"
        by (simp add: set_integrable_def integrable_completion)
    next
      fix wz assume "wz \<in> A"
      then obtain w z where wz: "wz = (w, z)" "Re w > a" "Re z > b"
        by (auto simp: A_def)
      show "AE x\<in>{0..1} in lborel. norm (f (fst wz) (snd wz) x) \<le> x powr (a - 1) * (1 - x) powr (b - 1)"
      proof (intro always_eventually impI allI)
        fix x :: real assume x: "x \<in> {0..1}"
        have "norm (f (fst wz) (snd wz) x) = x powr (Re w - 1) * (1 - x) powr (Re z - 1)"
          using x wz by (simp add: f_def norm_mult norm_powr_complex del: of_real_diff)
        also have "\<dots> \<le> x powr (a - 1) * (1 - x) powr (b - 1)"
          by (intro mult_mono powr_mono') (use x ab wz in auto)
        finally show "norm (f (fst wz) (snd wz) x) \<le> x powr (a - 1) * (1 - x) powr (b - 1)" .
      qed
    next
      show "((\<lambda>x. LBINT t:{x..1-x}. t powr (a - 1) * (1 - t) powr (b - 1)) \<longlongrightarrow>
              (LBINT t:{0..1}. t powr (a - 1) * (1 - t) powr (b - 1))) (at_right 0)"
      proof (rule at_within.filterlim_set_lebesgue_integral_set)
        show "set_integrable lborel {0..1} (\<lambda>t. t powr (a - 1) * (1 - t) powr (b - 1))"
          using integrable_Beta[OF ab(1,2)] by simp
      next
        show "tendsto_set lborel (\<lambda>x::real. {x..1 - x}) {0..1} (at_right 0)"
        proof (rule tendsto_set_intros)
          show "((\<lambda>x::real. 1 - x) \<longlongrightarrow> 1) (at_right 0)"
            by real_asymp
        qed (auto intro: finite_imp_null_set_lborel)
      next
        show "\<forall>\<^sub>F x in at_right 0. {x::real..1 - x} \<subseteq> {0..1}"
          using eventually_at_right_less by eventually_elim auto
      qed (auto simp: set_borel_measurable_def)
    next
      have "eventually (\<lambda>x::real. x > 0) (at_right 0)"
        by real_asymp
      thus "\<forall>\<^sub>F (x::real) in at_right 0. {x..1 - x} \<in> sets borel \<and> {x..1 - x} \<subseteq> {0..1}"
        by eventually_elim auto
    qed (auto simp: f_def set_borel_measurable_def)

    show "(\<lambda>w. F w z) analytic_on {w}"
    proof -
      obtain R where R: "R > 0" "cball w R \<subseteq> {w. Re w > a}"
        using ab open_halfspace_Re_gt open_contains_cball by blast
      have "uniform_limit {w. Re w > a} (\<lambda>x w. LBINT t:{x..1-x}. f w z t) 
              (\<lambda>w. LBINT t:{0..1}. f w z t) (at_right 0)"
        using uniform_limit_compose'[OF lim, of "\<lambda>w. (w,z)" "{w. Re w > a}"] wz ab
        by (auto simp: Pi_def A_def)
      hence "uniform_limit (cball w R) (\<lambda>x w. LBINT t:{x..1-x}. f w z t) 
              (\<lambda>w. LBINT t:{0..1}. f w z t) (at_right 0)"
        by (rule uniform_limit_on_subset) fact
      also have "?this \<longleftrightarrow> uniform_limit (cball w R) (\<lambda>x w. integral {x..1-x} (f w z)) 
                             (\<lambda>w. integral {0..1} (f w z)) (at_right 0)"
      proof (rule uniform_limit_cong)
        have "eventually (\<lambda>y. y > 0) (at_right (0::real))"
          by real_asymp
        thus "\<forall>\<^sub>F y in at_right 0. \<forall>x\<in>cball w R.
                set_lebesgue_integral lborel {y..1-y} (f x z) = integral {y..1-y} (f x z)"
          by eventually_elim 
             (intro ballI integral_eq [symmetric], use R ab in \<open>auto simp: subset_iff\<close>)
      next
        show "set_lebesgue_integral lborel {0..1} (f x z) = integral {0..1} (f x z)" 
          if x: "x \<in> cball w R" for x
          by (subst integral_eq [symmetric])  (use wz x R ab in auto)
      qed
      finally have 1: \<dots> .
      have 2: "(\<lambda>w. integral {x..1-x} (f w z)) holomorphic_on cball w R" if x: "x > 0" for x
      proof -
        note [derivative_intros] = has_field_derivative_complex_powr_right'
        define f' where "f' = (\<lambda>x t. of_real (ln t) * f x z t)"
        have "(\<lambda>w. integral (cbox x (1-x)) (f w z)) holomorphic_on cball w R"
        proof (rule leibniz_rule_holomorphic)
          show "((\<lambda>w. f w z t) has_field_derivative f' w' t) (at w' within cball w R)"
            if "w' \<in> cball w R" "t \<in> cbox x (1 - x)" for w' t
            unfolding f_def f'_def using x that
            by (auto intro!: derivative_eq_intros simp: Ln_of_real)
        next
          show "f w' z integrable_on cbox x (1 - x)" if "w' \<in> cball w R" for w'
            by (intro set_lebesgue_integral_eq_integral(1) integrable)
               (use that ab R x in auto)
        qed (use x in \<open>auto simp: f_def f'_def case_prod_unfold intro!: continuous_intros\<close>)
        thus ?thesis 
          by simp
      qed
      have "eventually (\<lambda>x::real. x > 0) (at_right 0)"
        by real_asymp
      hence 3: "\<forall>\<^sub>F n in at_right 0. continuous_on (cball w R)
               (\<lambda>w. integral {n..1 - n} (f w z)) \<and>
               (\<lambda>w. integral {n..1 - n} (f w z)) holomorphic_on ball w R"
        by eventually_elim
           (intro conjI holomorphic_on_imp_continuous_on holomorphic_on_subset[OF 2], auto)
      have "(\<lambda>w. integral {0..1} (f w z)) holomorphic_on ball w R"
        using holomorphic_uniform_limit[OF 3 1] by auto
      thus "(\<lambda>w. F w z) analytic_on {w}" unfolding F_def
        using \<open>R > 0\<close> analytic_at_ball by blast
    qed

    show "(\<lambda>z. F w z) analytic_on {z}"
    proof -
      obtain R where R: "R > 0" "cball z R \<subseteq> {z. Re z > b}"
        using ab open_halfspace_Re_gt open_contains_cball by blast
      have "uniform_limit {z. Re z > b} (\<lambda>x z. LBINT t:{x..1-x}. f w z t) 
              (\<lambda>z. LBINT t:{0..1}. f w z t) (at_right 0)"
        using uniform_limit_compose'[OF lim, of "\<lambda>z. (w,z)" "{z. Re z > b}"] wz ab
        by (auto simp: Pi_def A_def)
      hence "uniform_limit (cball z R) (\<lambda>x z. LBINT t:{x..1-x}. f w z t) 
              (\<lambda>z. LBINT t:{0..1}. f w z t) (at_right 0)"
        by (rule uniform_limit_on_subset) fact
      also have "?this \<longleftrightarrow> uniform_limit (cball z R) (\<lambda>x z. integral {x..1-x} (f w z)) 
                             (\<lambda>z. integral {0..1} (f w z)) (at_right 0)"
      proof (rule uniform_limit_cong)
        have "eventually (\<lambda>y. y > 0) (at_right (0::real))"
          by real_asymp
        thus "\<forall>\<^sub>F y in at_right 0. \<forall>x\<in>cball z R.
                set_lebesgue_integral lborel {y..1-y} (f w x) = integral {y..1-y} (f w x)"
          by eventually_elim 
             (intro ballI integral_eq [symmetric], use R ab in \<open>auto simp: subset_iff\<close>)
      next
        show "set_lebesgue_integral lborel {0..1} (f w x) = integral {0..1} (f w x)" 
          if x: "x \<in> cball z R" for x
          by (subst integral_eq [symmetric])  (use wz x R ab in auto)
      qed
      finally have 1: \<dots> .
      have 2: "(\<lambda>z. integral {x..1-x} (f w z)) holomorphic_on cball z R" if x: "x > 0" for x
      proof -
        note [derivative_intros] = has_field_derivative_complex_powr_right'
        define f' where "f' = (\<lambda>x t. of_real (ln (1 - t)) * f w x t)"
        have "(\<lambda>z. integral (cbox x (1-x)) (f w z)) holomorphic_on cball z R"
        proof (rule leibniz_rule_holomorphic)
          show "((\<lambda>z. f w z t) has_field_derivative f' z' t) (at z' within cball z R)"
            if "z' \<in> cball z R" "t \<in> cbox x (1 - x)" for z' t
            unfolding f_def f'_def using x that
            by (auto intro!: derivative_eq_intros simp: Ln_of_real mult_ac simp del: of_real_diff)
        next
          show "f w z' integrable_on cbox x (1 - x)" if "z' \<in> cball z R" for z'
            by (intro set_lebesgue_integral_eq_integral(1) integrable)
               (use that ab R x in auto)
        qed (use x in \<open>auto simp: f_def f'_def case_prod_unfold intro!: continuous_intros\<close>)
        thus ?thesis 
          by simp
      qed
      have "eventually (\<lambda>x::real. x > 0) (at_right 0)"
        by real_asymp
      hence 3: "\<forall>\<^sub>F n in at_right 0. continuous_on (cball z R)
               (\<lambda>z. integral {n..1 - n} (f w z)) \<and>
               (\<lambda>z. integral {n..1 - n} (f w z)) holomorphic_on ball z R"
        by eventually_elim
           (intro conjI holomorphic_on_imp_continuous_on holomorphic_on_subset[OF 2], auto)
      have "(\<lambda>z. integral {0..1} (f w z)) holomorphic_on ball z R"
        using holomorphic_uniform_limit[OF 3 1] by auto
      thus "(\<lambda>z. F w z) analytic_on {z}" unfolding F_def
        using \<open>R > 0\<close> analytic_at_ball by blast
    qed
  qed

  have [holomorphic_intros]: "(\<lambda>a. F a b) holomorphic_on {a. Re a > 0}" if "Re b > 0" for b
    by (rule analytic_imp_holomorphic, subst analytic_on_analytic_at) 
       (use that in \<open>auto intro!: ana(1)\<close>)
  have [holomorphic_intros]: "(\<lambda>b. F a b) holomorphic_on {b. Re b > 0}" if "Re a > 0" for a
    by (rule analytic_imp_holomorphic, subst analytic_on_analytic_at) 
       (use that in \<open>auto intro!: ana(2)\<close>)

  have integrable: "f a b absolutely_integrable_on {0..1}" if ab: "Re a > 0" "Re b > 0" for a b
  proof (rule set_integrable_bound)
    show "(\<lambda>t. t powr (Re a - 1) * (1 - t) powr (Re b - 1)) absolutely_integrable_on {0..1}"
      using integrable_Beta[of "Re a" "Re b"] ab
      by (simp add: set_integrable_def integrable_completion)
  qed (simp_all add: f_def norm_mult norm_powr_complex set_borel_measurable_def measurable_completion
                del: of_real_diff)

  have 1: "F a b - Beta a b = 0" if ab: "a \<in> \<real>" "Re a > 0" "Re b > 0" for a b
  proof (rule analytic_continuation[of "\<lambda>z. F a z - Beta a z"])
    show "(\<lambda>z. F a z - Beta a z) holomorphic_on {b. Re b > 0}"
      using that by (auto intro!: holomorphic_intros elim!: Reals_cases nonpos_Ints_cases)
  next
    show "of_real 1 islimpt complex_of_real ` {0<..}"
      by (rule islimpt_isCont_image) (auto simp: eventually_at_filter intro: open_imp_islimpt)
  next
    fix z assume "z \<in> complex_of_real ` {0<..}"
    then obtain y where y: "z = of_real y" "y > 0"
      by auto
    from ab obtain x where x: "a = of_real x" "x > 0"
      by (auto elim!: Reals_cases)
    have "((\<lambda>t. complex_of_real (t powr (x - 1) * (1 - t) powr (y - 1)))
             has_integral (of_real (Beta x y))) {0..1}"
      by (intro has_integral_of_real has_integral_Beta_real x y)
    also have "?this \<longleftrightarrow> (f (of_real x) (of_real y) has_integral (of_real (Beta x y))) {0..1}"
      by (intro has_integral_cong) (auto simp: f_def powr_Reals_eq)
    also have "complex_of_real (Beta x y) = Beta (of_real x) (of_real y)"
      by (simp add: Beta_complex_of_real)
    finally show "F a z - Beta a z = 0"
      using x y by (simp add: F_def has_integral_iff)
  qed (use ab in \<open>auto simp: open_halfspace_Re_gt connected_halfspace_Re_gt\<close>)

  have 2: "F a b - Beta a b = 0" if ab: "Re a > 0" "Re b > 0" for a b
  proof (rule analytic_continuation[of "\<lambda>z. F z b - Beta z b"])
    show "(\<lambda>z. F z b - Beta z b) holomorphic_on {a. Re a > 0}"
      using that by (auto intro!: holomorphic_intros elim!: Reals_cases nonpos_Ints_cases)
  next
    show "of_real 1 islimpt complex_of_real ` {0<..}"
      by (rule islimpt_isCont_image) (auto simp: eventually_at_filter intro: open_imp_islimpt)
  next
    fix z assume "z \<in> complex_of_real ` {0<..}"
    thus "F z b - Beta z b = 0"
      using 1[of z b] ab by auto
  qed (use ab in \<open>auto simp: open_halfspace_Re_gt connected_halfspace_Re_gt\<close>)

  have "f a b integrable_on {0..1}"
    using assms integrable[of a b] set_lebesgue_integral_eq_integral(1) by blast
  hence "(f a b has_integral F a b) {0..1}"
    by (simp add: has_integral_iff F_def)
  also have "F a b = Beta a b"
    using 2[of a b] assms by simp
  finally show "((\<lambda>t. of_real t powr (a - 1) * of_real (1 - t) powr (b - 1)) 
                  has_integral Beta a b) {0<..<1}"
    by (simp add: f_def has_integral_Icc_iff_Ioo)
qed

text \<open>
  By change of variables, we can also derive the following integral:
  \[\frac{1}{2} B(a,b) = \int_0^{\frac{\pi}{2}} \sin^{2a-1} t \cos^{2b-1} t\,\text{d}t\]
\<close>
lemma has_integral_Beta_sin_cos_complex:
  assumes "Re a > 0" "Re b > 0"
  shows "(\<lambda>t. of_real (sin t) powr (2*a-1) * of_real (cos t) powr (2*b-1))
           absolutely_integrable_on {0..pi/2}" (is "?thesis1")
    and "((\<lambda>t. of_real (sin t) powr (2*a-1) * of_real (cos t) powr (2*b-1))
           has_integral (Beta a b / 2)) {0..pi/2}" (is "?thesis2")
proof -
  define f where "f = (\<lambda>t. (1/2) * (of_real t powr (a-1) * of_real (1 - t) powr (b-1)))"
  define I where "I = (1/2) * Beta a b"
  define g where "g = (\<lambda>t. sin t ^ 2 :: real)"
  define g' where "g' = (\<lambda>t. 2 * sin t * cos t :: real)"
  define h where "h = (\<lambda>t. of_real (sin t) powr (2*a-1) * of_real (cos t) powr (2*b-1))"

  have *: "sqrt x \<ge> (-1::real)" if "x \<ge> 0" for x
    by (rule order.trans[of _ 0]) (use that in auto)
  have **: "arcsin (sqrt x) * 2 \<le> pi" if "x \<in> {0..1}" for x :: real
    using arcsin_bounded[of "sqrt x"] that *[of x] by simp
  have bij: "bij_betw g {0..pi/2} {0..1}"
    by (rule bij_betwI[of _ _ _ "\<lambda>x. arcsin (sqrt x)"])
       (auto simp: g_def power_le_one_iff sin_ge_zero arcsin_nonneg arcsin_sin * **)

  have eq: "\<bar>g' t\<bar> *\<^sub>R f (g t) = h t"
    if t: "t \<in> {0..pi/2}" for t
  proof -
    have "\<bar>g' t\<bar> *\<^sub>R f (g t) = of_real (sin t * cos t) * 
             of_real (sin t ^ 2) powr (a - 1) * of_real (cos t ^ 2) powr (b - 1)" using t 
      by (simp add: g'_def f_def g_def scaleR_conv_of_real 
                    abs_mult sin_ge_zero cos_ge_zero cos_squared_eq flip: of_real_power)
    also have "\<dots> = of_real (sin t) powr ((a-1) + (a-1) + 1) * of_real (cos t) powr ((b-1) + (b-1) + 1)"
      unfolding powr_add using t 
      by (simp add: power2_eq_square powr_times_real sin_ge_zero cos_ge_zero)
    finally show ?thesis
      by (simp add: algebra_simps h_def)
  qed

  have "f absolutely_integrable_on (g ` {0..pi/2})"
    unfolding f_def using has_integral_Beta_complex[of a b] bij assms
    by (intro set_integrable_mult_right)
       (simp add: bij_betw_def f_def I_def absolutely_integrable_on_Icc_iff_Ioo has_integral_iff)
  moreover have "integral (g ` {0..pi/2}) f = I"
    unfolding f_def using has_integral_Beta_complex[of a b] bij assms
    by (subst integral_mult_right)
       (simp add: bij_betw_def f_def I_def integral_open_interval_real  has_integral_iff)
  ultimately have "f absolutely_integrable_on (g ` {0..pi/2}) \<and> integral (g ` {0..pi/2}) f = I"
    by blast
  also have "?this \<longleftrightarrow> (\<lambda>x. \<bar>g' x\<bar> *\<^sub>R f (g x)) absolutely_integrable_on {0..pi/2} \<and>
                       integral {0..pi/2} (\<lambda>x. \<bar>g' x\<bar> *\<^sub>R f (g x)) = I"
    by (subst eq_commute, rule has_absolute_integral_change_of_variables_real)
       (use bij in \<open>auto simp: g_def g'_def bij_betw_def intro!: derivative_eq_intros\<close>)
  also have "(\<lambda>x. \<bar>g' x\<bar> *\<^sub>R f (g x)) absolutely_integrable_on {0..pi/2} \<longleftrightarrow>
             h absolutely_integrable_on {0..pi/2}"
    by (rule set_integrable_cong) (use eq in auto)
  also have "integral {0..pi/2} (\<lambda>x. \<bar>g' x\<bar> *\<^sub>R f (g x)) = integral {0..pi/2} h"
    by (rule integral_cong) (use eq in auto)
  finally show ?thesis1 ?thesis2
    unfolding h_def I_def by (simp_all add: has_integral_iff set_lebesgue_integral_eq_integral(1))
qed
             
lemma has_integral_Beta_sin_cos_real:
  assumes "a > 0" "b > 0"
  shows "((\<lambda>t. sin t powr (2*a-1) * cos t powr (2*b-1)) has_integral (Beta a b / 2)) {0..pi/2}"
proof -
  have "((\<lambda>t. Re (of_real (sin t) powr (2 * of_real a - 1) * of_real (cos t) powr (2 * of_real b - 1)))
           has_integral (Re (Beta (of_real a) (of_real b) / 2))) {0..pi/2}"
    by (intro has_integral_Re has_integral_Beta_sin_cos_complex) (use assms in auto)
  also have "?this \<longleftrightarrow> ((\<lambda>t. sin t powr (2 * a - 1) * cos t powr (2 * b - 1)) has_integral 
                         (Re (Beta (of_real a) (of_real b) / 2))) {0..pi/2}"
    by (intro has_integral_cong)
       (simp_all flip: sin_of_real cos_of_real add: powr_Reals_eq sin_ge_zero cos_ge_zero)
  also have "Re (Beta (of_real a) (of_real b) / 2) = Beta a b / 2"
    by (subst Beta_complex_of_real) auto
  finally show ?thesis .
qed

lemma sin_power_integral_0_pi_half:
  "((\<lambda>t. sin t ^ n) has_integral (Beta ((real n + 1) / 2) (1/2)) / 2) {0..pi/2}"
proof -
  have "((\<lambda>t. sin t powr real n * (if cos t = 0 then 0 else 1))
          has_integral Beta ((real n + 1) / 2) (1 / 2) / 2) {0..pi/2}"
    using has_integral_Beta_sin_cos_real[of "real (n+1) / 2" "1 / 2"] 
    by (simp add: add_divide_distrib add_ac)
  also have "?this \<longleftrightarrow> ((\<lambda>t. sin t ^ n) has_integral Beta ((real n + 1) / 2) (1 / 2) / 2) {0..pi/2}"
  proof (rule has_integral_spike_eq)
    fix t assume t: "t \<in> {0..pi/2} - {0, pi/2}"
    have "sin t > 0" "cos t > 0"
      using t by (auto simp: sin_gt_zero cos_gt_zero)
    thus "sin t ^ n = sin t powr real n * (if cos t = 0 then 0 else 1)"
      by (auto simp: powr_realpow)
  qed auto
  finally show ?thesis
    by simp
qed

lemma cos_power_integral_0_pi_half:
  "((\<lambda>t. cos t ^ n) has_integral (Beta (1/2) ((real n + 1) / 2)) / 2) {0..pi/2}"
proof -
  have "((\<lambda>t. cos t powr real n * (if sin t = 0 then 0 else 1))
          has_integral Beta (1 / 2) ((real n + 1) / 2) / 2) {0..pi/2}"
    using has_integral_Beta_sin_cos_real[of  "1 / 2" "real (n+1) / 2"] 
    by (simp add: add_divide_distrib add_ac mult_ac)
  also have "?this \<longleftrightarrow> ((\<lambda>t. cos t ^ n) has_integral Beta (1 / 2) ((real n + 1) / 2) / 2) {0..pi/2}"
  proof (rule has_integral_spike_eq)
    fix t assume t: "t \<in> {0..pi/2} - {0, pi/2}"
    have "cos t > 0" "sin t > 0"
      using t by (auto simp: sin_gt_zero cos_gt_zero)
    thus "cos t ^ n = cos t powr real n * (if sin t = 0 then 0 else 1)"
      by (auto simp: powr_realpow)
  qed auto
  finally show ?thesis
    by simp
qed

lemma sin_power_even_integral_0_pi_half_real:
  "((\<lambda>t. sin t ^ (2*n)) has_integral (pi / 2 * fact (2 * n) / (fact n ^ 2 * 4 ^ n))) {0..pi/2}"
proof -
  have "((\<lambda>t. sin t ^ (2*n)) has_integral (Beta ((real (2*n) + 1) / 2) (1/2)) / 2) {0..pi/2}"
    by (rule sin_power_integral_0_pi_half)
  also have "Beta ((real (2*n) + 1) / 2) (1/2) = Gamma (real n + 1 / 2) * sqrt pi / fact n"
    by (simp add: Beta_def Gamma_one_half_real add_divide_distrib Gamma_fact)
  also have "\<dots> / 2 = pi / 2 * fact (2 * n) / (fact n ^ 2 * 4 ^ n)"
    by (subst Gamma_int_plus_half) (auto simp: algebra_simps power2_eq_square)
  finally show ?thesis .
qed

lemma cos_power_even_integral_0_pi_half_real:
  "((\<lambda>t. cos t ^ (2*n)) has_integral (pi / 2 * fact (2 * n) / (fact n ^ 2 * 4 ^ n))) {0..pi/2}"
proof -
  have "((\<lambda>t. cos t ^ (2*n)) has_integral (Beta (1/2) ((real (2*n) + 1) / 2)) / 2) {0..pi/2}"
    by (rule cos_power_integral_0_pi_half)
  also have "Beta (1/2) ((real (2*n) + 1) / 2) = Gamma (real n + 1 / 2) * sqrt pi / fact n"
    by (simp add: Beta_def Gamma_one_half_real add_divide_distrib Gamma_fact)
  also have "\<dots> / 2 = pi / 2 * fact (2 * n) / (fact n ^ 2 * 4 ^ n)"
    by (subst Gamma_int_plus_half) (auto simp: algebra_simps power2_eq_square)
  finally show ?thesis .
qed


text \<open>
  Lastly, we derive the following integral:
  \[B(a,b) = \int_0^\infty \frac{t^{a-1}}{(1+t)^{a+b}}\,\text{d}t\]
\<close>
lemma has_integral_Beta_0_infinity_complex:
  assumes "Re a > 0" "Re b > 0"
  shows "(\<lambda>t. of_real t powr (a - 1) / of_real (1 + t) powr (a + b))
           absolutely_integrable_on {0<..}" (is "?thesis1")
    and "((\<lambda>t. of_real t powr (a - 1) / of_real (1 + t) powr (a + b))
           has_integral (Beta a b)) {0<..}" (is "?thesis2")
proof -
  define f where "f = (\<lambda>t. of_real t powr (a - 1) / of_real (1 + t) powr (a + b))"
  define g where "g = (\<lambda>x. tan x ^ 2 :: real)"
  define g' where "g' = (\<lambda>x. 2 * tan x / cos x ^ 2 :: real)"
  define I where "I = Beta a b"
  define h where "h = (\<lambda>x. 2 * (of_real (sin x) powr (2 * a - 1) * of_real (cos x) powr (2 * b - 1)))"

  have bij: "bij_betw g {0<..<pi/2} {0<..}"
  proof (rule bij_betwI[of _ _ _ "\<lambda>t. arctan (sqrt t)"])
    have "tan x \<noteq> 0" if "x \<in> {0<..<pi/2}" for x :: real
      using tan_gt_zero[of x] that by auto
    thus "g \<in> {0<..<pi / 2} \<rightarrow> {0<..}"
      by (auto simp: g_def)
  next
    have "arctan (sqrt x) * 2 < pi" if "x > 0" for x
      using arctan_bounded[of "sqrt x"] that by auto
    thus "(\<lambda>t. arctan (sqrt t)) \<in> {0<..} \<rightarrow> {0<..<pi / 2}"
      by auto
  next
    show "arctan (sqrt (g x)) = x" if "x \<in> {0<..<pi/2}" for x
      using that tan_gt_zero[of x] by (auto simp: g_def arctan_tan)
  next
    show "g (arctan (sqrt y)) = y" if "y \<in> {0<..}" for y
      using that by (auto simp: g_def tan_arctan)
  qed

  have eq: "\<bar>g' x\<bar> *\<^sub>R f (g x) = h x" if x: "x \<in> {0<..<pi/2}" for x
  proof -
    define s where "s = ln (sin x)"
    define c where "c = ln (cos x)"
    have sc: "sin x = exp s" "cos x = exp c"
      using x sin_gt_zero[of x] cos_gt_zero[of x] by (simp_all add: s_def c_def)
    have "\<bar>g' x\<bar> *\<^sub>R f (g x) = 
            2 * of_real (tan x) * of_real (tan x ^ 2) powr (a - 1) / 
              (of_real (cos x ^ 2) * of_real (1 + tan x ^ 2) powr (a + b))"
      using x by (simp add: g'_def f_def g_def scaleR_conv_of_real tan_pos_pi2_le)
    also have "of_real (cos x ^ 2) * of_real (1 + tan x ^ 2) powr (a + b) =
                 exp (2 * (1 - a - b) * c)"
      using exp_double[of "complex_of_real c"]
      by (subst tan_sec) 
         (auto simp: sc powr_def Ln_Reals_eq ring_distribs exp_add exp_diff exp_minus
                     field_simps ln_div ln_realpow exp_of_real)
    also have "2 * of_real (tan x) * of_real ((tan x)\<^sup>2) powr (a - 1) =
               2 * exp ((2 * a - 1) * s) * exp ((1 - 2 * a) * c)"
      using x cos_gt_zero[of x] sin_gt_zero[of x]
            exp_double[of "complex_of_real s"] exp_double[of "complex_of_real c"]
      by (simp add: sc tan_def powr_def Ln_Reals_eq ring_distribs ln_realpow ln_div
                    exp_diff exp_add exp_minus field_simps exp_of_real power2_eq_square ln_mult)
    also have "2 * exp ((2 * a - 1) * s) * exp ((1 - 2 * a) * c) / exp (2 * (1 - a - b) * c) =
               2 * exp ((2 * a - 1) * s) * exp ((2 * b - 1) * c)"
      by (simp add: field_simps exp_add exp_diff exp_minus flip: power2_eq_square exp_double)
    also have "exp ((2 * a - 1) * s) = of_real (sin x) powr (2 * a - 1)"
      using sin_gt_zero[of x] x by (auto simp: powr_def s_def Ln_Reals_eq)
    also have "exp ((2 * b - 1) * c) = of_real (cos x) powr (2 * b - 1)"
      using cos_gt_zero[of x] x by (auto simp: powr_def c_def Ln_Reals_eq)
    finally show ?thesis
      by (simp add: h_def)
  qed

  have cos_nz: "cos x \<noteq> 0" if "x \<in> {0<..<pi/2}" for x :: real
    using cos_gt_zero[of x] that by simp

  have "h absolutely_integrable_on {0<..<pi/2}"
    using set_integrable_mult_right[OF has_integral_Beta_sin_cos_complex(1)[of a b], of 2] assms
    by (simp add: h_def absolutely_integrable_on_Icc_iff_Ioo)
  moreover have "integral {0<..<pi/2} h = I"
    using has_integral_mult_right[OF has_integral_Beta_sin_cos_complex(2)[of a b], of 2] assms
    unfolding has_integral_Icc_iff_Ioo by (simp add: h_def I_def has_integral_iff)
  ultimately have "h absolutely_integrable_on {0<..<pi/2} \<and> integral {0<..<pi/2} h = I"
    by blast

  also have "h absolutely_integrable_on {0<..<pi/2} \<longleftrightarrow>
               (\<lambda>x. \<bar>g' x\<bar> *\<^sub>R f (g x)) absolutely_integrable_on {0<..<pi/2}" 
    by (rule set_integrable_cong) (use eq in auto)
  also have "integral {0<..<pi/2} h = integral {0<..<pi/2} (\<lambda>x. \<bar>g' x\<bar> *\<^sub>R f (g x))"
    by (rule integral_cong) (use eq in auto)
  also have "(\<lambda>x. \<bar>g' x\<bar> *\<^sub>R f (g x)) absolutely_integrable_on {0<..<pi/2} \<and>
             integral {0<..<pi/2} (\<lambda>x. \<bar>g' x\<bar> *\<^sub>R f (g x)) = I \<longleftrightarrow>
        f absolutely_integrable_on (g ` {0<..<pi/2}) \<and> integral (g ` {0<..<pi/2}) f = I"
    using bij
    by (intro has_absolute_integral_change_of_variables_real)
       (auto simp: g_def g'_def field_simps bij_betw_def cos_nz intro!: derivative_eq_intros)
  also have "g ` {0<..<pi/2} = {0<..}"
    using bij by (simp add: bij_betw_def)
  finally show ?thesis1 ?thesis2
    unfolding f_def I_def by (simp_all add: has_integral_iff set_lebesgue_integral_eq_integral(1))
qed

lemma has_integral_Beta_0_infinity_real:
  assumes "a > 0" "b > (0::real)"
  shows "((\<lambda>t. t powr (a - 1) / (1 + t) powr (a + b)) has_integral (Beta a b)) {0<..}"
proof -
  have "((\<lambda>t. Re (of_real t powr (of_real a - 1) / of_real (1 + t) powr (of_real a + of_real b)))
           has_integral (Re (Beta (of_real a) (of_real b)))) {0<..}"
    by (intro has_integral_Re has_integral_Beta_0_infinity_complex) (use assms in auto)
  also have "?this \<longleftrightarrow> ((\<lambda>t. t powr (a - 1) / (1 + t) powr (a + b)) has_integral 
                         (Re (Beta (of_real a) (of_real b)))) {0<..}"
    by (intro has_integral_cong)
       (simp_all flip: sin_of_real cos_of_real add: powr_Reals_eq sin_ge_zero cos_ge_zero)
  also have "Re (Beta (of_real a) (of_real b)) = Beta a b"
    by (subst Beta_complex_of_real) auto
  finally show ?thesis .
qed

end
