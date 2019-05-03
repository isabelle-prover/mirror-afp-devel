(* Authors: R. Thiemann *)

subsection \<open>Farkas Lemma for Matrices\<close>

text \<open>In this part we convert the simplex-structures like linear polynomials, etc., into
  equivalent formulations using matrices and vectors. As a result we present Farkas' Lemma
  via matrices and vectors.\<close>

theory Matrix_Farkas
  imports Farkas
  Jordan_Normal_Form.Matrix
begin

lift_definition poly_of_vec :: "rat vec \<Rightarrow> linear_poly" is
  "\<lambda> v x. if (x < dim_vec v) then v $ x else 0" 
  by auto

definition val_of_vec :: "rat vec \<Rightarrow> rat valuation" where
  "val_of_vec v x = v $ x" 

lemma valuate_poly_of_vec: assumes "w \<in> carrier_vec n" 
  and "v \<in> carrier_vec n"  
shows "valuate (poly_of_vec v) (val_of_vec w) = v \<bullet> w"  
  using assms by (transfer, auto simp: val_of_vec_def scalar_prod_def intro: sum.mono_neutral_left)

definition constraints_of_mat_vec :: "rat mat \<Rightarrow> rat vec \<Rightarrow> rat le_constraint set" where
  "constraints_of_mat_vec A b = (\<lambda> i . Leqc (poly_of_vec (row A i)) (b $ i)) ` {0 ..< dim_row A}" 

lemma constraints_of_mat_vec_solution_main: assumes A: "A \<in> carrier_mat nr nc" 
  and x: "x \<in> carrier_vec nc"
  and b: "b \<in> carrier_vec nr" 
  and sol: "A *\<^sub>v x \<le> b" 
  and c: "c \<in> constraints_of_mat_vec A b" 
shows "val_of_vec x \<Turnstile>\<^sub>l\<^sub>e c" 
proof -
  from c[unfolded constraints_of_mat_vec_def] A obtain i where
    i: "i < nr" and c: "c = Leqc (poly_of_vec (row A i)) (b $ i)" by auto
  from i A have ri: "row A i \<in> carrier_vec nc" by auto
  from sol i A x b have sol: "(A *\<^sub>v x) $ i \<le> b $ i" unfolding less_eq_vec_def by auto
  thus "val_of_vec x \<Turnstile>\<^sub>l\<^sub>e c" unfolding c satisfiable_le_constraint.simps rel_of.simps
      valuate_poly_of_vec[OF x ri] using A x i by auto
qed

lemma vars_poly_of_vec: "vars (poly_of_vec v) \<subseteq> { 0 ..< dim_vec v}" 
  by (transfer', auto)

lemma finite_constraints_of_mat_vec: "finite (constraints_of_mat_vec A b)" 
  unfolding constraints_of_mat_vec_def by auto

lemma lec_rec_constraints_of_mat_vec: "lec_rel ` constraints_of_mat_vec A b \<subseteq> {Leq_Rel}" 
  unfolding constraints_of_mat_vec_def by auto

lemma constraints_of_mat_vec_solution_1: 
  assumes A: "A \<in> carrier_mat nr nc" 
    and b: "b \<in> carrier_vec nr" 
    and sol: "\<exists> x \<in> carrier_vec nc. A *\<^sub>v x \<le> b" 
  shows "\<exists> v. \<forall> c \<in> constraints_of_mat_vec A b. v \<Turnstile>\<^sub>l\<^sub>e c" 
  using constraints_of_mat_vec_solution_main[OF A _ b _] sol by blast

lemma constraints_of_mat_vec_solution_2: 
  assumes A: "A \<in> carrier_mat nr nc" 
    and b: "b \<in> carrier_vec nr" 
    and sol: "\<exists> v. \<forall> c \<in> constraints_of_mat_vec A b. v \<Turnstile>\<^sub>l\<^sub>e c" 
  shows "\<exists> x \<in> carrier_vec nc. A *\<^sub>v x \<le> b" 
proof -
  from sol obtain v where sol: "v \<Turnstile>\<^sub>l\<^sub>e c" if "c \<in> constraints_of_mat_vec A b" for c by auto
  define x where "x = vec nc (\<lambda> i. v i)" 
  show ?thesis
  proof (intro bexI[of _ x])
    show x: "x \<in> carrier_vec nc" unfolding x_def by auto
    have "row A i \<bullet> x \<le> b $ i" if "i < nr" for i
    proof -
      from that have "Leqc (poly_of_vec (row A i)) (b $ i) \<in> constraints_of_mat_vec A b" 
        unfolding constraints_of_mat_vec_def using A by auto
      from sol[OF this, simplified] have "valuate (poly_of_vec (row A i)) v \<le> b $ i" by simp
      also have "valuate (poly_of_vec (row A i)) v = valuate (poly_of_vec (row A i)) (val_of_vec x)" 
        by (rule valuate_depend, insert A that, 
          auto simp: x_def val_of_vec_def dest!: set_mp[OF vars_poly_of_vec])
      also have "\<dots> = row A i \<bullet> x" 
        by (subst valuate_poly_of_vec[OF x], insert that A x, auto)
      finally show ?thesis .
    qed
    thus "A *\<^sub>v x \<le> b" unfolding less_eq_vec_def using x A b by auto
  qed
qed

lemma constraints_of_mat_vec_solution: 
  assumes A: "A \<in> carrier_mat nr nc" 
    and b: "b \<in> carrier_vec nr" 
  shows "(\<exists> x \<in> carrier_vec nc. A *\<^sub>v x \<le> b) = 
    (\<exists> v. \<forall> c \<in> constraints_of_mat_vec A b. v \<Turnstile>\<^sub>l\<^sub>e c)" 
  using constraints_of_mat_vec_solution_1[OF assms] constraints_of_mat_vec_solution_2[OF assms]
  by blast    

lemma farkas_lemma_matrix: fixes A :: "rat mat" 
  assumes A: "A \<in> carrier_mat nr nc" 
  and b: "b \<in> carrier_vec nr" 
shows "(\<exists> x \<in> carrier_vec nc. A *\<^sub>v x \<le> b) \<longleftrightarrow> 
  (\<forall> y. y \<ge> 0\<^sub>v nr \<longrightarrow> mat_of_rows nr [y] * A = 0\<^sub>m 1 nc \<longrightarrow> y \<bullet> b \<ge> 0)" 
proof -
  define cs where "cs = constraints_of_mat_vec A b" 
  have fin: "finite {0 ..< nr}" by auto
  have dim: "dim_row A = nr" using A by simp
  have sum_id: "(\<Sum> i = 0..<nr. f i) = sum_list (map f [0..<nr])" for f 
    by (subst sum_list_distinct_conv_sum_set, auto)
  have "(\<exists> x \<in> carrier_vec nc. A *\<^sub>v x \<le> b) =
   (\<not> (\<nexists> v. \<forall> c \<in> cs. v \<Turnstile>\<^sub>l\<^sub>e c))" 
    unfolding constraints_of_mat_vec_solution[OF assms] cs_def by simp
  also have "\<dots> = (\<not> (\<nexists>v. \<forall>i\<in>{0..<nr}. v \<Turnstile>\<^sub>l\<^sub>e Le_Constraint Leq_Rel (poly_of_vec (row A i)) (b $ i)))" 
    unfolding cs_def constraints_of_mat_vec_def dim by auto
  also have "\<dots> = (\<nexists>C.
        (\<forall>i\<in>{0..<nr}. 0 \<le> C i) \<and>
         (\<Sum>i = 0..<nr. (C i *R poly_of_vec (row A i))) = 0 \<and>
         (\<Sum>i = 0..<nr. (C i * b $ i)) < 0)" 
    unfolding Farkas'_Lemma_indexed[OF 
        lec_rec_constraints_of_mat_vec[unfolded constraints_of_mat_vec_def], of A b,
        unfolded dim, OF fin] sum_id sum_list_lec le_constraint.simps 
        sum_list_Leq_Rel map_map o_def unfolding sum_id[symmetric] by simp
  also have "\<dots> = (\<forall> C. (\<forall>i\<in> {0..<nr}. 0 \<le> C i) \<longrightarrow> 
         (\<Sum>i = 0..<nr. (C i *R poly_of_vec (row A i))) = 0 \<longrightarrow>
         (\<Sum>i = 0..<nr. (C i * b $ i)) \<ge> 0)" 
    using not_less by blast
  also have "\<dots> = (\<forall> y. y \<ge> 0\<^sub>v nr \<longrightarrow> mat_of_rows nr [y] * A = 0\<^sub>m 1 nc \<longrightarrow> y \<bullet> b \<ge> 0)"
  proof ((standard; intro allI impI), goal_cases)
    case *: (1 y)
    define C where "C = (\<lambda> i. y $ i)" 
    note main = *(1)[rule_format, of C]
    from *(2) have y: "y \<in> carrier_vec nr" and nonneg: "\<And>i. i \<in> {0..<nr} \<Longrightarrow> 0 \<le> C i" 
      unfolding less_eq_vec_def C_def by auto
    have sum_0: "(\<Sum>i = 0..<nr. C i *R poly_of_vec (row A i)) = 0" unfolding C_def
      unfolding zero_coeff_zero coeff_sum 
    proof
      fix v
      have "(\<Sum>i = 0..<nr. coeff (y $ i *R poly_of_vec (row A i)) v) = 
            (\<Sum>i < nr. y $ i * coeff (poly_of_vec (row A i)) v)" by (rule sum.cong, auto)
      also have "\<dots> = 0" 
      proof (cases "v < nc")
        case False
        have "(\<Sum>i < nr. y $ i * coeff (poly_of_vec (row A i)) v) = 
              (\<Sum>i < nr. y $ i * 0)" 
          by (rule sum.cong[OF refl], rule arg_cong[of _ _ "\<lambda> x. _ * x"], insert A False, transfer, auto)
        also have "\<dots> = 0" by simp
        finally show ?thesis by simp
      next
        case True
        have "(\<Sum>i<nr. y $ i * coeff (poly_of_vec (row A i)) v) =
              (\<Sum>i<nr. y $ i * row A i $ v)" 
          by (rule sum.cong[OF refl], rule arg_cong[of _ _ "\<lambda> x. _ * x"], insert A True, transfer, auto)
        also have "\<dots> = (mat_of_rows nr [y] * A) $$ (0,v)" 
          unfolding mat_of_rows_def times_mat_def scalar_prod_def
          using A y True by (auto intro: sum.cong)
        also have "\<dots> = 0" unfolding *(3) using True by simp
        finally show ?thesis .
      qed
      finally show "(\<Sum>i = 0..<nr. coeff (y $ i *R poly_of_vec (row A i)) v) = 0" .
    qed
    from main[OF nonneg sum_0] have le: "0 \<le> (\<Sum>i = 0..<nr. C i * b $ i)" .
    thus ?case using y b unfolding scalar_prod_def C_def by auto
  next
    case *: (2 C)
    define y where "y = vec nr C" 
    have y: "y \<in> carrier_vec nr" unfolding y_def by auto
    note main = *(1)[rule_format, of y]
    from *(2) have y0: "y \<ge> 0\<^sub>v nr" unfolding less_eq_vec_def y_def by auto
    have prod0: "mat_of_rows nr [y] * A = 0\<^sub>m 1 nc" 
    proof -
      {
        fix j
        assume j: "j < nc"
        from arg_cong[OF *(3), of "\<lambda> x. coeff x j", unfolded coeff_sum]
        have "0 = (\<Sum>i = 0..<nr. C i * coeff (poly_of_vec (row A i)) j)" by simp
        also have "\<dots> = (\<Sum>i = 0..<nr. C i * row A i $ j)" 
          by (rule sum.cong[OF refl], rule arg_cong[of _ _ "\<lambda> x. _ * x"], insert A j, transfer, auto)
        also have "\<dots> = y \<bullet> col A j" unfolding scalar_prod_def y_def using A j 
          by (intro sum.cong, auto)
        finally have "y \<bullet> col A j = 0" by simp
      }
      thus ?thesis by (intro eq_matI, insert A y, auto)
    qed
    from main[OF y0 prod0] have "0 \<le> y \<bullet> b" .
    thus ?case unfolding scalar_prod_def y_def using b by auto
  qed
  finally show ?thesis .
qed

end


