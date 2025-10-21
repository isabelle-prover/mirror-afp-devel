section \<open>Minimizer Implications\<close>

theory First_Order_Conditions
  imports Minimizers_Definition 
begin

notation norm ("\<parallel>_\<parallel>")

subsection \<open>Implications for a Given Minimizer Type\<close>

lemma strict_local_minimizer_imp_local_minimizer:
  assumes "strict_local_minimizer f x_star"
  shows "local_minimizer f x_star"
  by (smt (verit) Diff_iff assms local_minimizer_def singletonD strict_local_minimizer_def strict_local_minimizer_on_def)

lemma isolated_local_minimizer_imp_strict:
  assumes "isolated_local_minimizer f x_star"
  shows "strict_local_minimizer f x_star"
proof -
  \<comment> \<open>From isolated\_local\_minimizer we obtain an open set $U$
        such that $x^\star $ is the \emph{only} local minimizer.\<close>
  from assms obtain U where iso_props:
    "isolated_local_minimizer_on f x_star U"
    unfolding isolated_local_minimizer_def
    using isolated_local_minimizer_on_def by blast 

  \<comment> \<open>Unpack \texttt{isolated\_local\_minimizer\_on}: 
  \(x^\star\) is a \texttt{local\_minimizer\_on} \(U\), and \(x^\star\) is unique.\<close>

  from iso_props have lm_on: "local_minimizer_on f x_star U"
    unfolding isolated_local_minimizer_on_def using local_minimizer_on_def by presburger
  moreover from iso_props have unique_min: "{x \<in> U. local_minimizer f x} = {x_star}"
    unfolding isolated_local_minimizer_on_def by auto

  \<comment> \<open>From \texttt{local\_minimizer\_on}, we have: 
  \(U\) open, \(x^\star \in U\), and \(\forall x \in U.\; f(x^\star) \le f(x)\).\<close>

  from lm_on have open_U: "open U" and x_in_U: "x_star \<in> U" and le_prop: "\<forall>x \<in> U. f x_star \<le> f x"
    unfolding local_minimizer_on_def by auto

  \<comment> \<open>Assume, for contradiction, that \(x^\star\) is not a strict local minimizer.  
      Then there exists \(y \in U \setminus \{x^\star\}\) with \(f(y) \le f(x^\star)\).\<close>

  show "strict_local_minimizer f x_star"
  proof (rule ccontr)
    assume "\<not> strict_local_minimizer f x_star"
    then obtain y where y_props:
      "y \<in> U - {x_star}" and "f y \<le> f x_star"
      unfolding strict_local_minimizer_def strict_local_minimizer_on_def
      by (smt (verit, ccfv_SIG) open_U x_in_U)

    from y_props have "y \<in> U" and "y \<noteq> x_star"
      by auto

    \<comment> \<open>We already have \(f(x^\star) \le f(y)\) from @{thm le_prop} and \(y \in U\).  
      Together with \(f(y) \le f(x^\star)\), this yields \(f(x^\star) = f(y)\).\<close>

    from le_prop `y \<in> U` have "f x_star \<le> f y"
      by auto
    with `f y \<le> f x_star` have "f x_star = f y"
      by auto

    \<comment> \<open>Now we show that \(y\) is also a local minimizer, contradicting the uniqueness of \(x^\star\).  
      To prove this, we must exhibit an open set \(V\) around \(y\) such that  
      \(f(y) \le f(x)\) for all \(x \in V\).\<close>

    have "local_minimizer f y"
    proof -
      \<comment> \<open>Since \(U\) is open and \(y \in U\), there exists an open set \(V \subseteq U\) containing \(y\).\<close>
      obtain V where "open V" and "y \<in> V" and "V \<subseteq> U"
        using `open U` `y \<in> U` open_subset by auto

      \<comment> \<open>On this subset, \(f(y) = f(x^\star) \le f(x)\) for all \(x \in V\) (since \(V \subseteq U\)).\<close>

      moreover from le_prop and `f x_star = f y` have "\<forall>x \<in> V. f y \<le> f x"
        using calculation(3) by auto

      ultimately show "local_minimizer f y"
        unfolding local_minimizer_def local_minimizer_on_def by auto
    qed

    \<comment> \<open>Since \(y\) is a local minimizer and \(y \in U\), we have 
      \(y \in \{x \in U.\ \texttt{local\_minimizer}\ f\ x\}\).  
      By uniqueness, \(\{x \in U.\ \texttt{local\_minimizer}\ f\ x\} = \{x^\star\}\),  
      hence \(y = x^\star\), contradicting \(y \neq x^\star\).\<close>

    hence "y \<in> {x \<in> U. local_minimizer f x}"
      by (simp add: \<open>y \<in> U\<close>)
    with unique_min have "y = x_star" by auto
    thus False using `y \<noteq> x_star` by contradiction
  qed
  \<comment> \<open>Having reached a contradiction under the assumption that \(x^\star\) is not a strict local minimizer,  
      it follows that \(x^\star\) must indeed be a strict local minimizer.\<close>
qed

subsection \<open>Characterization of Non-Isolated Minimizers\<close>

lemma not_isolated_minimizer_def:
  assumes "local_minimizer f x_star"
  shows "(\<exists>x_seq::nat \<Rightarrow> real. (\<forall>n. local_minimizer f (x_seq n) \<and> x_seq n \<noteq> x_star) \<and> ((x_seq \<longlongrightarrow> x_star) at_top)) = (\<not> isolated_local_minimizer f x_star)"         
proof(safe)
  show "\<And>x_seq. isolated_local_minimizer f x_star \<Longrightarrow> \<forall>n. local_minimizer f (x_seq n) \<and> x_seq n \<noteq> x_star \<Longrightarrow> x_seq \<longlonglongrightarrow> x_star \<Longrightarrow> False"
  proof - 
    fix x_seq :: "nat \<Rightarrow>  real"
    assume x_star_isolated_minimizer: "isolated_local_minimizer f x_star"
    assume with_sequence_of_local_miniziers: "\<forall>n. local_minimizer f (x_seq n) \<and> x_seq n \<noteq> x_star"
    assume converging_to_x_star: "x_seq \<longlonglongrightarrow> x_star"
    have open_ball_with_unique_min: "\<exists>N > 0. \<forall>x \<in> ball x_star N. (local_minimizer f x \<longrightarrow> x = x_star)"
      by (simp add: isolated_local_minimizer_def2 x_star_isolated_minimizer)
    then obtain N where N_pos: "N > 0" and N_prop: "\<forall>x \<in> ball x_star N. (local_minimizer f x \<longrightarrow> x = x_star)"
      by blast
    \<comment> \<open>Use convergence to show \(x_{\mathrm{seq}}\) eventually lies in \(\mathrm{ball}(x^\star, N)\).\<close>
    from converging_to_x_star have "\<exists>M. \<forall>n \<ge> M. x_seq n \<in> ball x_star N"
      by (metis LIMSEQ_iff_nz N_pos dist_commute mem_ball)
    then obtain M where M_def: "\<forall>n \<ge> M. x_seq n \<in> ball x_star N"
      by auto
    then show False
      by (meson N_prop linorder_not_le order_less_irrefl with_sequence_of_local_miniziers)
  qed
next
  show "\<not> isolated_local_minimizer f x_star \<Longrightarrow> \<exists>x_seq. (\<forall>n. local_minimizer f (x_seq n) \<and> x_seq n \<noteq> x_star) \<and> x_seq \<longlonglongrightarrow> x_star"
  proof(rule ccontr) 
    assume not_isolated_minimizer: "\<not>isolated_local_minimizer f x_star"
    assume BWOC: "\<nexists>x_seq. (\<forall>n. local_minimizer f (x_seq n) \<and> x_seq n \<noteq> x_star) \<and> x_seq \<longlonglongrightarrow> x_star"

    have "\<exists>N > 0. \<forall>x. dist x x_star < N \<longrightarrow> f x_star \<le> f x"
      by (simp add: assms local_minimizer_def2)
    then obtain N where N_pos: "(N::nat) > 0" and x_star_min_on_N_ball: "\<forall>x. dist x x_star < 1/ real N \<longrightarrow> f x_star \<le> f x"
      by (metis dual_order.strict_trans ex_inverse_of_nat_less inverse_eq_divide)
    
    obtain S_n :: "nat \<Rightarrow> real set" where S_n_def: "S_n = (\<lambda>n. {x. dist x x_star < 1 /  (real n + N) \<and> x \<noteq> x_star \<and> local_minimizer f x})"
      by blast

    from not_isolated_minimizer
    have non_isolated: "\<forall>U. local_minimizer_on f x_star U \<longrightarrow> (\<exists>y \<in> U. y \<noteq> x_star \<and> local_minimizer f y)"
      by (smt (verit, best) Collect_cong assms isolated_local_minimizer_def local_minimizer_on_def singleton_conv2)

    have "\<forall>n::nat. \<exists>x. x \<in> S_n n"
    proof (intro allI)
      fix n::nat
      have pos_radius: "1 / (real n + N) > 0"
        using N_pos by simp

      obtain U where U_def: "U = ball x_star (1 / (real n + N))"  and open_U: "open U" and U_contains_x_star: "x_star \<in> U"
        using pos_radius by auto

      have U_contained_in_Inverse_N_Ball: "\<forall>x \<in> U. dist x x_star < 1 / N"
      proof(safe)
        fix x:: real
        assume x_in_U: "x \<in> U"
        then have "dist x x_star < (1 / (real n + N))"
          by (simp add: U_def dist_commute)
        also have  "... \<le> 1 / real N"
          by (simp add: N_pos frac_le)
        finally show "dist x x_star < 1 / real N".
      qed

      have ball_non_empty: "\<exists>y \<in> U. y \<noteq> x_star \<and> local_minimizer f y"
      proof -
        have "local_minimizer_on f x_star U"
          by (simp add: U_contains_x_star U_contained_in_Inverse_N_Ball local_minimizer_on_def open_U x_star_min_on_N_ball)
        then show "\<exists>y\<in>U. y \<noteq> x_star \<and> local_minimizer f y"
          by (simp add: non_isolated)
      qed
      then obtain y where y_in_ball: "y \<in> U" and "y \<noteq> x_star" and "local_minimizer f y"
        by blast
      then show "\<exists>x. x \<in> S_n n"
        by (smt (verit, best) S_n_def U_def dist_commute mem_Collect_eq mem_ball)
    qed
    then obtain x_seq where x_seq_def: "\<forall>n. x_seq n \<in> S_n n"
      by metis
    have x_seq_converges_to_x_star: "x_seq \<longlonglongrightarrow> x_star"
    proof (rule LIMSEQ_I)
      fix r :: real
      assume r_pos: "0 < r"
      obtain n_min where n_min_def: "1 / (real n_min + N) < r"
        using real_arch_inverse N_pos r_pos
        by (smt (verit, ccfv_SIG) frac_le inverse_eq_divide inverse_positive_iff_positive)
      show "\<exists>no. \<forall>n\<ge>no. norm (x_seq n - x_star) < r"
      proof (intro exI allI impI)
        fix n
        assume "n \<ge> n_min"
        then have n_large_enough: "1 / (real n + N) \<le> 1 / (real n_min + N)"
          using N_pos by (subst frac_le, simp_all)
        have "dist (x_seq n) x_star < 1 / (real n + N)"
          using x_seq_def S_n_def by auto
        also have "... \<le> 1 / (real n_min + N)"
          using n_large_enough by auto
        also have "... < r"
          using n_min_def by auto
        finally show "norm (x_seq n - x_star) < r"
          by (simp add: dist_real_def)
      qed
    qed
    have "\<exists>x_seq. (\<forall>n. local_minimizer f (x_seq n) \<and> x_seq n \<noteq> x_star) \<and> x_seq \<longlonglongrightarrow> x_star"
      using S_n_def x_seq_converges_to_x_star x_seq_def by blast
    then show False
      using BWOC by auto
  qed
qed

subsection \<open>First-Order Condition\<close>

theorem Fermat's_theorem_on_stationary_points:
  fixes f :: "real \<Rightarrow> real"
  assumes "(f has_derivative f') (at x_min)"
  assumes "local_minimizer f x_min"
  shows "(deriv f) x_min = 0"
  by (metis assms has_derivative_imp differential_zero_maxmin local_minimizer_def)

definition stand_basis_vector :: "'n::finite \<Rightarrow> real^'n"  \<comment> \<open>the i-th standard basis vector\<close>
  where   "stand_basis_vector i = (\<chi> j. if j = i then 1 else 0)"

lemma stand_basis_vector_index[simp]:   "(stand_basis_vector i) $ j = (if j = i then (1::real) else 0)"
  by (simp add: stand_basis_vector_def)

lemma stand_basis_vector_nonzero[simp]: "stand_basis_vector i \<noteq> 0"
  by (smt (verit, del_insts) stand_basis_vector_index zero_index)

lemma norm_stand_basis_vector[simp]:    "norm (stand_basis_vector i) = 1"
  by (smt (verit, best) axis_nth component_le_norm_cart norm_axis_1 norm_le_componentwise_cart real_norm_def stand_basis_vector_index)

lemma inner_stand_basis_vector[simp]:   "inner (stand_basis_vector i) (stand_basis_vector j) = (if i = j then 1 else 0)"
  by (metis axis_nth cart_eq_inner_axis norm_eq_1 norm_stand_basis_vector stand_basis_vector_index vector_eq)

lemma Basis_characterisation:
  "stand_basis_vector i \<in> (Basis :: (real^'n) set)"   and
  "\<forall>b\<in>(Basis::(real^'n)set). \<exists>i. b = stand_basis_vector i"
  by (metis (no_types, lifting) Basis_real_def axis_in_Basis_iff cart_eq_inner_axis 
      inner_stand_basis_vector insert_iff norm_axis_1 norm_eq_1 stand_basis_vector_index vector_eq,
      metis axis_index axis_nth cart_eq_inner_axis inner_stand_basis_vector stand_basis_vector_index vector_eq)

lemma stand_basis_expansion:
  fixes x :: "real^'n"
  shows "x = (\<Sum> j\<in>UNIV. (x $ j) *\<^sub>R stand_basis_vector j)"
proof -
  have "(\<Sum> j\<in>UNIV. (x $ j) *\<^sub>R stand_basis_vector j) $ k = x $ k" for k
  proof -
    have "(\<Sum> j\<in>UNIV. (x $ j) *\<^sub>R stand_basis_vector j) $ k
          = (\<Sum> j\<in>UNIV. (x $ j) * (stand_basis_vector j $ k))"
      by simp
    also have "\<dots> = (\<Sum> j\<in>UNIV. (x $ j) * (if j = k then 1 else 0))"
      by (smt (verit, best) stand_basis_vector_index sum.cong)
    also have "\<dots> = (\<Sum> j\<in>UNIV. (if j = k then x $ j else 0))"
      by (smt (verit, best) mult_cancel_left1 mult_cancel_right1 sum.cong)
    also have "\<dots> = x $ k"
      by (subst sum.delta, simp_all)
    finally show ?thesis.
  qed
  thus ?thesis
    by (simp add: vec_eq_iff)
qed

lemma has_derivative_affine:
  fixes a v :: "'a::real_normed_vector"
  shows "((\<lambda>t. a + t *\<^sub>R v) has_derivative (\<lambda>h. h *\<^sub>R v)) (at x)"
  unfolding has_derivative_def
proof safe
  have "a + y *\<^sub>R v - (a + netlimit (at x) *\<^sub>R v) - (y - netlimit (at x)) *\<^sub>R v = 0"  if "y \<noteq> netlimit (at x)" for y
    by (simp add: cross3_simps(32))
  then show "(\<lambda>y. (a + y *\<^sub>R v - (a + netlimit (at x) *\<^sub>R v) - (y - netlimit (at x)) *\<^sub>R v) /\<^sub>R \<parallel>y - netlimit (at x)\<parallel>) \<midarrow>x\<rightarrow> 0"
    by (simp add: scaleR_left_diff_distrib)
  show "bounded_linear (\<lambda>h. h *\<^sub>R v)"
    by (simp add: bounded_linearI' vector_space_assms(2))
qed

theorem Fermat's_theorem_on_stationary_points_mult:
  fixes f :: "real ^ 'n \<Rightarrow> real"
  assumes der_f: "(f has_derivative f') (at x_min)"
  assumes min_f: "local_minimizer f x_min"
  shows "GDERIV f x_min :> 0"
proof - 
 \<comment> \<open>Show that \(f'\) kills every standard-basis vector.\<close>

  {
    fix i :: 'n
    \<comment> \<open>Define the 1‑D slice \(g_i(t) = f(x_{\min} + t \cdot e_i)\).\<close>
    let ?g = "\<lambda>t::real. f (x_min + t *\<^sub>R stand_basis_vector i)"

    \<comment> \<open>Chain rule gives \(g_i'(0) = f'(e_i)\).\<close>
    from has_derivative_affine have g_der:
      "((\<lambda>t. f (x_min + t *\<^sub>R stand_basis_vector i))
      has_derivative (\<lambda>h. f' (h *\<^sub>R stand_basis_vector i))) (at 0)"
      by (metis (no_types) arithmetic_simps(50) der_f has_derivative_compose scaleR_simps(1))

    \<comment> \<open>\(0\) is a local minimizer of \(g_i\) because \(x_{\min}\) is one for \(f\).\<close>
    have g_min: "local_minimizer ?g 0"      
    proof(rule local_minimizer_from_neighborhood)
      obtain \<delta> where \<delta>_pos: "\<delta> > 0"
        and mono: "\<And>x. dist x_min x < \<delta> \<Longrightarrow> f x \<ge> f x_min"
        by (metis assms(2) dist_commute local_minimizer_def2)

      have "\<forall>x. \<bar>x - 0\<bar> < \<delta> \<longrightarrow> f (x_min + 0 *\<^sub>R stand_basis_vector i) \<le> f (x_min + x *\<^sub>R stand_basis_vector i)"
        using mono by (simp add: dist_norm)
      then show "\<exists>\<delta>>0. \<forall>x. \<bar>x - 0\<bar> < \<delta> \<longrightarrow> f (x_min + 0 *\<^sub>R stand_basis_vector i) \<le> f (x_min + x *\<^sub>R stand_basis_vector i)"
        using \<delta>_pos by blast
    qed

    \<comment> \<open>Apply the 1-D Fermat lemma to \(g_i\).\<close>
    from Fermat's_theorem_on_stationary_points 
    have "f' (stand_basis_vector i) = 0"
      using g_der g_min  by (metis has_derivative_imp scale_one)      
  }

    \<comment> \<open>Collecting the result for every \(i\):\<close>
  hence zero_on_basis: "\<And>i. f' (stand_basis_vector i) = 0".

  \<comment> \<open>Use linearity and the coordinate expansion to show \(f' = 0\) everywhere.\<close>
  {
    fix v :: "real^'n"
    \<comment> \<open>Expand \(v = \sum_j v_j \cdot e_j\) and push \(f'\) through the finite sum.\<close>
    have "f' v = 0"
    proof -
      have "f' v = f' (\<Sum>j\<in>UNIV. (v $ j) *\<^sub>R stand_basis_vector j)"
        by (metis stand_basis_expansion)
      also have "\<dots> = (\<Sum>j\<in>UNIV. (v $ j) *\<^sub>R f' (stand_basis_vector j))"
        by (smt (verit) assms differential_zero_maxmin local_minimizer_def scale_eq_0_iff sum.neutral)
      also have "\<dots> = 0"
        using zero_on_basis by simp
      finally show ?thesis.
    qed
  }
  hence f'_zero: "f' = (\<lambda>_. 0)"
    by (simp add: fun_eq_iff)

  \<comment> \<open>Translate \(f' = 0\) into the gradient statement.\<close>
  have "(f has_derivative (\<lambda>h. 0)) (at x_min)"
    using der_f f'_zero by simp
  hence "GDERIV f x_min :> (0::real^'n)"
    by (simp add: gderiv_def)
  thus ?thesis.
qed

end