section \<open>Abel's limit theorem on real power series\<close>

theory Abel_Limit_Theorem
  imports "HOL-Analysis.Generalised_Binomial_Theorem"
begin

text \<open> 
  Abel's theorem or Abel's limit theorem \<^cite>\<open>"wikipedia-contributors-2025"\<close> provides a 
  crucial link between the behavior of a power series inside its interval of 
  convergence (such as $(-1,1)$) and its value at the boundary such as $-1$ or $1$. 

  This section presents the proof of Abel's limit theorem, which relates a limit of a power series
  to the sum of its real coefficients, as shown below:

  $${\displaystyle \lim _{x\to 1^{-}}f(x)=f(1)=\sum _{k=0}^{\infty }a_{k}} \qquad \mbox{ where } 
  f(x)={\sum _{k=0}^{\infty }a_{k}x^{k}}$$
  if the power series has its radius of convergence equal to 1 and 
  $\sum _{k=0}^{\infty }a_{k}$ converges, where $a_k$ is the coefficient of the $k$-th term.
  
  That is, $f(x)$ is continuous from the left at 1. 
\<close>

text \<open> 
  The proof of continuity or the limit of $f(x)$ is based on the $\varepsilon$-$\delta$ definition. 
  This proof uses summation by parts or Abel transformation to express the power series $f(x)$ 
  as a power series whose coefficients are the partial sums ($\sum _{k=0}^{n}a_{k}$) of the 
  coefficients of $f(x)$, instead of $a_k$. Then the new power series is split into two parts. 
  The goal is to show that each part contributes to $\varepsilon/2$ for any $x$ satisfying $(1-x)<\delta$. 

  Several references~\<^cite>\<open>"wikipedia-contributors-2025" and "planetmathProofAbelx2019s" and "Holland2022-fq"\<close>
  are used to construct this proof. 
\<close>

theorem Abel_limit_theorem:
  fixes a :: "nat \<Rightarrow> real"
  defines "f1 \<equiv> (\<lambda>(x::real) n. a n * x ^ n)"
  defines "f \<equiv> (\<lambda>(x::real). \<Sum>n. f1 x n)"
  assumes summable_a: "summable a" and
       conv_radius_1: "conv_radius a = 1"
  shows "(f \<longlongrightarrow> (\<Sum>n. a n)) (at_left 1)"
proof -
  \<comment> \<open>This is the partial sum of coefficients up to @{text "n"}. \<close>
  let ?s = "\<lambda>n. (\<Sum>k\<le>n. a k)"

  \<comment> \<open>@{text "S"} is the infinite sum of the coefficients. \<close>
  obtain S where P_S: "(\<Sum>n. a n) = S"
    using summable_a by simp

  let ?fs_S = "\<lambda>x n. ((?s n - S) * x ^ n)"
  let ?fs_S_sum = "\<lambda>x. (\<Sum>n. ?fs_S x n)"

  have s_limit_S: "?s \<longlonglongrightarrow> S"
    using P_S summable_a summable_LIMSEQ' by blast

  have summable_f1: "\<forall>x. norm x < 1 \<longrightarrow> summable (\<lambda>n. f1 x n)"
    by (simp only: f1_def, auto, rule summable_in_conv_radius, simp add: conv_radius_1)

  \<comment> \<open>A geometric series sums to @{text "1 / (1 - x)"}. Therefore, @{text "(1-x)*(1 / (1 - x)) = 1"}. \<close>
  have geometric: "\<forall>x::real. norm x < 1 \<longrightarrow> (\<Sum>n. x ^ n) = 1 / (1 - x)"
    by (auto simp add: suminf_geometric)

  \<comment> \<open>The Cauchy product of a geometric series and a convergent power series is a power series
  whose coefficient for the nth term is the partial sum up to n, that is, @{text "?s n"}. \<close>
  have cauchy_product_to_partial_sum: "(\<Sum>n. x ^ n) * f x = (\<Sum>n. ?s n * x ^ n)"
    if a1: "norm x < 1" for x :: real
  proof -
    from a1 have x_lt_1: "\<bar>x\<bar> < 1"
      by (simp)

    show "(\<Sum>n. x ^ n) * f x = (\<Sum>n. ?s n * x ^ n)"
    proof -
      have f0: "\<forall>n. \<forall>i\<le>n. x ^ i * (a (n - i) * x ^ (n - i)) = a (n - i) * x ^ n"
        apply auto[1]
        by (metis le_add_diff_inverse power_add)

      have f1: "\<forall>n. (\<Sum>i\<le>n. x ^ i * (a (n - i) * x ^ (n - i))) = (\<Sum>i\<le>n. a (n - i) * x ^ n)"
        by (auto simp: f0)

      have f2: "\<forall>n. (\<Sum>i\<le>n. a (n - i)) = ?s n"
      proof (rule allI)
        fix n::nat
        show "(\<Sum>i\<le>n. a (n - i)) = ?s n"
          by (rule sum.reindex_bij_witness[of _ "\<lambda>i. n - i" "\<lambda>i. n - i"]) auto
      qed

      show ?thesis
        unfolding f_def f1_def
      proof (subst Cauchy_product)
        show "summable (\<lambda>k. norm (x ^ k))"
          by (simp add: power_abs x_lt_1)
      next
        show "summable (\<lambda>k. norm (a k * x ^ k))"
          by (metis abs_summable_in_conv_radius conv_radius_1 ereal_less(3) real_norm_def x_lt_1)
      next
        show "(\<Sum>k. \<Sum>i\<le>k. x ^ i * (a (k - i) * x ^ (k - i))) =
                (\<Sum>n. sum a {..n} * x ^ n)"
          by (subst f1) (use f2 in \<open>simp_all flip: sum_distrib_right\<close>)
      qed
    qed
  qed

  have summable_s_n_x_n: "\<forall>x::real. norm x < 1 \<longrightarrow> (summable (\<lambda>n. ?s n * x ^ n))"
  proof (rule allI, rule impI)
    fix x::real
    
    assume a1: "norm x < 1"
    from a1 have x_lt_1: "\<bar>x\<bar> < 1"
      by (simp)

    have "(\<Sum>n. ?s n * x ^ n) = (\<Sum>n. x ^ n) * f x"
      using cauchy_product_to_partial_sum real_norm_def x_lt_1 by presburger
    
    have f0: "(\<lambda>n. ?s n * x ^ n) = (\<lambda>n. \<Sum>i\<le>n. a i * x ^ n)"
      using sum_distrib_right by blast

    have f1: "... = (\<lambda>n. \<Sum>i\<le>n. (a i * x ^ i) * (x ^ (n - i)))"
      apply (simp only: mult.assoc)
      apply (subst power_add[symmetric])
      by simp

    show "summable (\<lambda>n. ?s n * x ^ n)"
      apply (simp only: f0 f1)
      apply (rule summable_Cauchy_product[where a = "\<lambda>n. (a n) * x ^ n" and b = "\<lambda>n. x ^ n"])
       apply (metis abs_summable_in_conv_radius conv_radius_1 ereal_less(3) real_norm_def x_lt_1)
      by (simp add: power_abs x_lt_1)
  qed

  \<comment> \<open> The power series @{text "f x"} is expressed as a convex combination of the partial sums. \<close>
  have f_x_to_partial_sum: "\<forall>x::real. norm x < 1 \<longrightarrow> f x = (1 - x) * (\<Sum>n. ?s n * x ^ n)"
  proof (rule allI, rule impI)
    fix x::real
    
    assume a1: "norm x < 1"
    from a1 have x_lt_1: "\<bar>x\<bar> < 1"
      by (simp)

    \<comment> \<open> Rewrite @{text "f x"} because @{text "(1 - x) * (\<Sum>n. x ^ n) = 1"}. \<close>
    have f_rewrite: "f x = (1 - x) * (\<Sum>n. x ^ n) * f x"
       using geometric x_lt_1 by fastforce

    \<comment> \<open> According to the Cauchy product result. \<close>
    then show "f x = (1 - x) * (\<Sum>n. ?s n * x ^ n)"
      using cauchy_product_to_partial_sum  mult.assoc by (metis real_norm_def x_lt_1)
  qed

  \<comment> \<open> The difference between @{text "f x"} and @{text "S"}, therefore, can be expressed as a 
  convex combination of the partial sum minus @{text "S"}. So the goal is to show RHS tends to 
  0 when @{text "x"} approaches 1 from left. \<close> 
  have f_x_minus_S: "\<forall>x::real. norm x < 1 \<longrightarrow> f x - S = (1 - x) * ?fs_S_sum x"
  proof (rule allI, rule impI)
    fix x::real
    
    assume a1: "norm x < 1"
    from a1 have x_lt_1: "\<bar>x\<bar> < 1"
      by (simp)

    have f0: "(1 - x) * (\<Sum>n. ?s n * x ^ n) - S = (1 - x) * (\<Sum>n. ?s n * x ^ n) - (1 - x) * S * (\<Sum>n. x ^ n)"
      apply (simp add: geometric)
      using geometric x_lt_1 by auto

    have f1: "... = (1 - x) * ((\<Sum>n. ?s n * x ^ n) - (\<Sum>n. S * x ^ n))"
      apply (subst suminf_mult)
       apply (rule summable_geometric)
       apply (simp add: x_lt_1)
      by (simp add: right_diff_distrib)

    show "f x - S = (1 - x) * ?fs_S_sum x"
      apply (simp only: f_x_to_partial_sum a1)
      apply (simp only: f0 f1)
      apply (subst suminf_diff)
        using real_norm_def summable_s_n_x_n x_lt_1 apply presburger
       apply (rule summable_mult)
        apply (simp add: x_lt_1)
      by (simp add: left_diff_distrib')
  qed

  have summable_norm_s_S: "\<forall>x::real. norm x < 1 \<longrightarrow> summable (\<lambda>n::nat. norm (?s n - S) * (norm x) ^ (n))"
  proof (rule allI, rule impI)
    fix x::real
    assume x_lt_1: "norm x < 1"
    obtain M where P_m: "\<forall>n. norm (?s n) \<le> M"
      using convergent_imp_bounded[of ?s] by (metis UNIV_I bounded_iff imageI s_limit_S)
    have "\<forall>n. norm (?s n - S) * (norm x) ^ (n) \<le> (M + norm S) * (norm x)^n"
    proof (rule allI)
      fix n :: nat
      have "norm (?s n - S) * (norm x) ^ (n) \<le> (norm (?s n) + norm S) * (norm x) ^ (n)"
        by (simp add: mult_mono)
      also have "... \<le> (M + norm S) * (norm x)^n"
        by (metis P_m add.commute add_le_cancel_left mult.commute mult_left_mono norm_ge_zero norm_power)
      finally show "norm (?s n - S) * (norm x) ^ (n) \<le> (M + norm S) * (norm x) ^ n"
        by blast
    qed
    moreover have "summable (\<lambda>n. (M + norm S) * (norm x)^n)"
      using x_lt_1 by (simp add: summable_mult summable_geometric)
    ultimately show "summable (\<lambda>n::nat. norm (?s n - S) * norm x ^ n)"
      using summable_comparison_test[of "\<lambda>n. norm (?s n - S) * (norm x) ^ (n)" "\<lambda>n. (M + norm S) * (norm x)^n"]
      by fastforce
  qed

  (* Here we use a direct proof, and we can also use summable_norm_s_S and summable_comparison_test *)
  have summable_norm_fs_S: "\<forall>x::real. norm x < 1 \<longrightarrow> summable (\<lambda>n. norm (?fs_S x n))"
  proof (rule allI, rule impI)
    fix x::real
    assume x_lt_1: "norm x < 1"
    obtain M where P_m: "\<forall>n. norm (?s n) \<le> M"
      using convergent_imp_bounded[of ?s] by (metis UNIV_I bounded_iff imageI s_limit_S)
    have "\<forall>n. norm (?fs_S x n) \<le> (M + norm S) * (norm x)^n"
    proof (rule allI)
      fix n :: nat
      have "norm ((?s n - S) * x ^ n) \<le> norm ((?s n - S)) * norm (x ^ n)"
        using norm_mult_ineq by blast
      also have "... \<le> (norm (?s n) + norm S) * norm (x ^ n)"
        by (simp add: mult_mono)
      also have "... \<le> (M + norm S) * (norm x)^n"
        by (metis P_m add.commute add_le_cancel_left mult.commute mult_left_mono norm_ge_zero norm_power)
      finally show "norm ((?s n - S) * x ^ n) \<le> (M + norm S) * norm x ^ n"
        by blast
    qed
    moreover have "summable (\<lambda>n. (M + norm S) * (norm x)^n)"
      using x_lt_1 by (simp add: summable_mult summable_geometric)
    ultimately show "summable (\<lambda>n. norm (?fs_S x n))"
      using summable_comparison_test[of "\<lambda>n. norm (?fs_S x n)" "\<lambda>n. (M + norm S) * (norm x)^n"]
      by fastforce
  qed

  \<comment> \<open>Use the $\varepsilon$-$\delta$ definition of a continuous function or a limit. \<close>
  have S_is_f_limit_from_left: "(f \<longlongrightarrow> S) (at_left (1))"
  proof (simp only: tendsto_iff eventually_at_left_field, simp only: dist_norm, rule allI, rule impI)
    \<comment> \<open>@{text "r"} is the difference of function @{text "f x"} from @{text "f 1"} \<close>
    fix r::real
    assume r_gt_0: "(0::real) < r"

    \<comment> \<open>Try to make both tail and head parts contribute r/2, so finally r. \<close>
    define e where "e = r/2"

    have e_gt_0: "0 < e"
      by (simp add: r_gt_0 e_def)

    \<comment> \<open>@{text "M"} is not necessary to be positive and can be 0. \<close>
    obtain M where P_M: "(\<forall>n \<ge> M. norm (?s n - S) < e)"
      using s_limit_S LIMSEQ_iff e_gt_0 real_norm_def by metis

    \<comment> \<open>Make  @{text "N"} be positive, which will be used later to ensure @{text "norm x ^ N < 1"} \<close>
    define N where "N = M + 1"

    \<comment> \<open>@{text "C"} is the sum of differences up to @{text "N"}. \<close>
    define C where "C = (\<Sum>k<N. norm (?s k - S))"

    have P_N: "(\<forall>n \<ge> N. norm (?s n - S) < e)"
      unfolding N_def using P_M by simp

    \<comment> \<open> Split the sum into two parts based on its index: @{text "{0..N-1}"} and @{text "{N..\<infinity>}"}, 
    also called the head part and the tail part. \<close>
    have fs_S_split: "\<forall>x::real. norm x < 1 \<longrightarrow> (1 - x) * ?fs_S_sum x 
      = (1 - x) * (\<Sum>n < N. ?fs_S x n) + (1 - x) * (\<Sum>n. ?fs_S x (n + N))"
    proof (rule allI, rule impI)
      fix x::real

      assume a1: "norm x < 1"
      from a1 have x_lt_1: "\<bar>x\<bar> < 1"
        by (simp)

      have "(\<Sum>n. ?fs_S x n) = (\<Sum>n<N. ?fs_S x n) + (\<Sum>n. ?fs_S x (n + N))" (is "... = ?fs_S_sum_hd + ?fs_S_sum_tl")
        apply (subst suminf_split_initial_segment[where k = N])
         using summable_norm_fs_S real_norm_def summable_norm_cancel x_lt_1 apply fastforce
        by linarith
          
      then show "(1 - x) * (\<Sum>n. ?fs_S x n) = (1 - x) * (\<Sum>n<N. ?fs_S x n) + (1 - x) * (\<Sum>n. ?fs_S x (n + N))"
        by (simp add: distrib_left)
    qed

    \<comment> \<open>For the tail part, it is less than @{text "e"}. \<close>
    have fs_S_tail: "\<forall>x::real. 0 < x \<and> norm x < 1 \<longrightarrow> norm ((1 - x) * (\<Sum>n. ?fs_S x (n + N))) < e"
    proof (rule allI, rule impI)
      fix x::real
      assume x_lt_1: "(0::real) < x \<and> norm x < 1"
      have x_N_le_1: "norm x ^ N < 1"
        using power_Suc_less_one P_N N_def x_lt_1 by fastforce
      have "norm ((1 - x) * (\<Sum>n. ?fs_S x (n + N))) \<le> norm ((1 - x)) * norm (\<Sum>n. ?fs_S x (n + N))"
        using norm_mult_ineq by blast
      also have "... \<le> (1 - x) * (\<Sum>n. norm (?fs_S x (n + N)))"
        apply (subgoal_tac "norm (1-x) = 1-x")
         apply (subgoal_tac "norm (\<Sum>n. ?fs_S x (n + N)) \<le> (\<Sum>n. norm (?fs_S x (n + N)))")
        subgoal by (simp add: mult_mono)
         apply (subst summable_norm)
          apply (subst summable_iff_shift)
          using summable_norm_fs_S x_lt_1 apply blast
         apply simp
        using x_lt_1 by fastforce
      also have "... \<le> (1 - x) * (\<Sum>n. norm (?s (n + N) - S) * (norm x) ^ (n + N))"
        by (smt (z3) norm_mult norm_power suminf_cong)
      also have "... \<le> (1 - x) * (\<Sum>n. e * (norm x) ^ (n + N))"
        apply (rule mult_mono)
           apply simp
          apply (rule suminf_le)
            apply (smt (verit) P_N le_add2 mult_right_mono norm_ge_zero zero_le_power)
           apply (subst summable_iff_shift)
           using summable_norm_s_S x_lt_1 apply blast
          apply (subst summable_iff_shift)
          using x_lt_1 apply force
         using x_lt_1 apply auto[1]
        by (smt (z3) calculation real_norm_def x_lt_1 zero_le_mult_iff)
      also have "... = (1 - x) * e * (norm x) ^ N * (\<Sum>n. (norm x) ^ (n))"
        apply (subst suminf_mult)
         using x_lt_1 apply force
        apply (simp only: power_add)
        apply (subgoal_tac "(\<Sum>n::nat. norm x ^ n * norm x ^ N) = norm x ^ N * (\<Sum>n::nat. norm x ^ n)")
         apply simp
        apply (subst suminf_mult[symmetric])
         using x_lt_1 apply auto[1]
        by (meson mult.commute)
      also have "... = (1 - x) * e * (norm x) ^ N * 1 / (1 - norm x)"
        apply (subst suminf_geometric)
         using x_lt_1 apply fastforce
        using times_divide_eq_right by blast
      also have "... = e * (norm x) ^ N"
        using x_lt_1 by fastforce
      also have "... < e"
        using x_N_le_1 using e_gt_0 by force
      finally show "norm ((1 - x) * (\<Sum>n. ?fs_S x (n + N))) < e"
        by blast
    qed

    \<comment> \<open>For the head part, it is bounded by @{text "C"}. \<close>
    have fs_S_head: "\<forall>x::real. 0 < x \<and> norm x < 1 \<longrightarrow> norm ((1 - x) * (\<Sum>n < N. ?fs_S x n)) \<le> (1-x)*C"
    proof (rule allI, rule impI)
      fix x::real
      assume x_lt_1: "(0::real) < x \<and> norm x < 1"
      have "norm ((1 - x) * (\<Sum>n < N. ?fs_S x n)) \<le> norm ((1 - x)) * norm (\<Sum>n < N. ?fs_S x n)"
        using norm_mult_ineq by blast
      also have "... \<le> (1 - x) * (\<Sum>n < N. norm (?fs_S x (n)))"
        apply (subgoal_tac "norm (1-x) = 1-x")
         apply (subgoal_tac "norm (\<Sum>n<N. ?fs_S x (n)) \<le> (\<Sum>n<N. norm (?fs_S x (n)))")
          apply (simp add: mult_mono)
         using norm_sum apply blast
        using x_lt_1 by fastforce
      also have "... \<le> (1 - x) * (\<Sum>n<N. norm (?s (n) - S) * (norm x) ^ (n))"
        by (smt (verit) norm_mult norm_power sum.cong)
      also have "... \<le> (1 - x) * (\<Sum>n<N. norm (?s (n) - S))"
        apply (rule mult_mono)
        subgoal by simp
          apply (rule sum_le_included[where i = "\<lambda>x. x"])
        subgoal by simp
        subgoal by simp
        subgoal by simp
          apply (smt (verit) mult_left_le power_le_one_iff real_norm_def x_lt_1)
         using x_lt_1 apply force
        by (simp add: sum_nonneg)
      finally show "norm ((1 - x) * (\<Sum>n < N. ?fs_S x n)) \<le> (1-x)*C"
        by (simp add: C_def)
    qed

    have C_nonneg: "C \<ge> 0"
      by (simp add: C_def N_def)
    
    show "\<exists>b<1::real. \<forall>y>b. y < (1::real) \<longrightarrow> norm (f y - S) < r"
    proof (cases "C = 0")
      case True
      then show ?thesis 
        \<comment> \<open>Any x between 0 and 1 because the head part is 0 and only consider the tail part \<close> 
      proof (intro exI[of _ "0.9"])
        show "(9::real) / (10::real) < 1 \<and> (\<forall>y>(9::real) / (10::real). y < 1 \<longrightarrow> norm (f y - S) < r)"
        proof (rule conjI)
          show "(9::real) / (10::real) < 1"
            by simp
          show "\<forall>y>(9::real) / (10::real). y < 1 \<longrightarrow> norm (f y - S) < r"
          proof (rule allI, rule impI, rule impI)
            fix y::real
            assume y_gt_0: "(9::real) / (10::real) < y"
            assume y_lt_1: "y < (1::real)"

            have "norm ((1 - y) * (\<Sum>n::nat<N. (?s n - S) * y ^ n) + 
                  (1 - y) * (\<Sum>n::nat. (?s (n + N) - S) * y ^ (n + N))) < r"
            proof (rule norm_triangle_lt)
              have "norm ((1 - y) * (\<Sum>n < N. ?fs_S y n)) \<le> (1-y)*C"
                apply (subst fs_S_head)
                 using y_gt_0 y_lt_1 apply force
                by simp
              also have "... = 0"
                by (simp add: True)
              also have head_0: "norm ((1 - y) * (\<Sum>n < N. ?fs_S y n)) = 0"
                using calculation by force
              also have tail_lt_e: "norm ((1 - y) * (\<Sum>n. ?fs_S y (n + N))) < e"
                apply (subst fs_S_tail)
                 using y_gt_0 y_lt_1 apply force
                by simp
              finally show "norm ((1 - y) * (\<Sum>n < N. ?fs_S y n)) + 
                            norm ((1 - y) * (\<Sum>n. ?fs_S y (n + N))) < r"
                using e_def e_gt_0 head_0 tail_lt_e by linarith
            qed
            then show "norm (f y - S) < r"
              apply (subst f_x_minus_S)
               using y_gt_0 y_lt_1 apply simp
              apply (subst fs_S_split)
               using y_gt_0 y_lt_1 apply simp
               by blast
           qed
         qed
      qed
    next
      case False
      then show ?thesis 
      \<comment> \<open> This witness is to ensure @{text "(1-x)*C \<le> e"}. \<close>
      proof (intro exI[of _ "1 - min (e/C) 1"])
        show "1 - min (e / C) 1 < 1 \<and> (\<forall>y>1 - min (e / C) 1. y < 1 \<longrightarrow> norm (f y - S) < r)"
        proof (rule conjI)
          show "1 - min (e / C) 1 < 1"
            using C_nonneg r_gt_0 False e_gt_0 by fastforce
          show "\<forall>y>1 - min (e / C) 1. y < 1 \<longrightarrow> norm (f y - S) < r"
          proof (rule allI, rule impI, rule impI)
            fix y::real
            assume y_gt_0: "(1::real) - min (e / C) (1::real) < y"
            assume y_lt_1: "y < (1::real)"
  
            have "norm ((1 - y) * (\<Sum>n < N. ?fs_S y n)) \<le> (1-y)*C"
              apply (subst fs_S_head)
               using y_gt_0 y_lt_1 apply force
              by simp
            also have "... \<le> e"
              by (smt (verit) C_nonneg False e_def pos_divide_less_eq y_gt_0)
            also have tail_lt_e: "norm ((1 - y) * (\<Sum>n. ?fs_S y (n + N))) < e"
              apply (subst fs_S_tail)
               using y_gt_0 y_lt_1 apply force
              by simp
            show "norm (f y - S) < r"
              apply (subst f_x_minus_S)
               using y_lt_1 y_gt_0 apply force
              apply (subst fs_S_split)
               using y_lt_1 y_gt_0 apply force
              apply (rule norm_triangle_lt)
              using calculation e_def tail_lt_e by linarith
          qed
        qed
      qed
    qed
  qed

  show "?thesis"
    using P_S S_is_f_limit_from_left by blast
qed

lemma filterlim_at_right_at_left_eq:
  shows "((\<lambda>x. f (-x)) \<longlongrightarrow> l) (at_right (-1)) \<longleftrightarrow> ((\<lambda>x. f (x)) \<longlongrightarrow> l) (at_left (1::real))"
  apply (rule iffI)
   apply (simp add: at_left_minus)
   apply (simp add: filterlim_filtermap)
  apply (subst at_right_minus)
  by (simp add: filterlim_filtermap)

text \<open> 
  Abel's limit theorem is also suitable for continuous from the right at -1.
\<close>
corollary Abel_limit_theorem':
  fixes a :: "nat \<Rightarrow> real"
  defines "f1 \<equiv> (\<lambda>(x::real) n. a n * x ^ n)"
  defines "f \<equiv> (\<lambda>(x::real). \<Sum>n. f1 x n)"
  assumes summable_a: "summable a" and 
       conv_radius_1: "conv_radius a = 1"
  shows "((\<lambda>x. f (-x)) \<longlongrightarrow> (\<Sum>n. a n)) (at_right (-1))"
  apply (simp add: filterlim_at_right_at_left_eq)
  using assms Abel_limit_theorem by blast

end