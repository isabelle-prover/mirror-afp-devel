section \<open>The Weierstra\ss\ \<open>\<wp>\<close> Function\<close>
theory Weierstrass_Elliptic
imports 
  Elliptic_Functions
  Modular_Group
begin

text \<open>
  In this section, we will define the Weierstra\ss\ \<open>\<wp>\<close> function, which is in some sense
  the simplest and most fundamental elliptic function. All elliptic functions can be expressed
  solely in terms of \<open>\<wp>\<close> and \<open>\<wp>'\<close>.
\<close>


subsection \<open>Preliminary convergence results\<close>

text \<open>
  We first examine the uniform convergence of the series
    \[\sum_{\omega\in\Lambda^*} \frac{1}{(z-\omega)^n}\]
  and
    \[\sum_{\omega\in\Lambda} \frac{1}{(z-\omega)^n}\]
  for fixed $n \geq 3$.

  The second version is an elliptic function that we call the \<^emph>\<open>Eisenstein function\<close> because 
  setting $z = 0$ gives us the Eisenstein series. To our knowledge this function does not have a 
  name of its own in the literature.

  This is perhaps because it is up to a constant factor, equal to the $(n-2)$-nth derivative of
  the Weierstra\ss\ $\wp$ function (which we will define a bit afterwards).
\<close>

(* TODO Move. Or rather, fix whatever causes these problems. *)
lemmas [simp del] = div_mult_self1 div_mult_self2 div_mult_self3 div_mult_self4


context complex_lattice
begin

lemma \<omega>_upper:
  assumes "\<omega> \<in> lattice_layer k" and "\<alpha> > 0" and "k > 0"
  shows "norm \<omega> powr -\<alpha> \<le> (k*Inf_para) powr -\<alpha>"
  using lattice_layer_le_norm Inf_para_pos assms powr_mono2' by force

lemma sum_\<omega>_upper:
  assumes "\<alpha> > 0" and "k > 0"
  shows "(\<Sum>\<omega> \<in> lattice_layer k. norm \<omega> powr -\<alpha>) \<le> 8 * k powr (1-\<alpha>) * Inf_para powr -\<alpha>"
    (is "?lhs \<le> ?rhs")
proof -
  have "?lhs \<le> (8 * k) * (k*Inf_para) powr -\<alpha>"
    using sum_bounded_above [OF \<omega>_upper] card_lattice_layer [OF \<open>k>0\<close>] assms
    by fastforce
  also have "\<dots> = ?rhs"
    using Inf_para_pos by (simp add: powr_diff powr_minus powr_mult divide_simps)
  finally show ?thesis .
qed

lemma lattice_layer_lower:
  assumes "\<omega> \<in> lattice_layer k" and "k > 0"
  shows "(k * (if \<alpha> \<ge> 0 then Inf_para else Sup_para)) powr \<alpha> \<le> norm \<omega> powr \<alpha>"
proof (cases "\<alpha> \<ge> 0")
  case True
  have [simp]: "\<omega> \<noteq> 0"
    using assms by auto
  show ?thesis
    by (rule powr_mono2)
       (use True lattice_layer_le_norm[of \<omega> k] Inf_para_pos assms in auto)
next
  case False
  show ?thesis
    by (rule powr_mono2') (use False lattice_layer_ge_norm[of \<omega> k] assms in auto)
qed

lemma sum_lattice_layer_lower:
  fixes \<alpha> :: real
  assumes "k > 0"
  defines "C \<equiv> (if \<alpha> \<ge> 0 then Sup_para else Inf_para)"
  shows "8 * k powr (1-\<alpha>) * C powr -\<alpha> \<le> (\<Sum>\<omega> \<in> lattice_layer k. norm \<omega> powr -\<alpha>)"
    (is "?lhs \<le> ?rhs")
proof -
  from \<open>k > 0\<close> have "?lhs = (\<Sum>\<omega>\<in>lattice_layer k. (k * C) powr -\<alpha>)"
    by (simp add: powr_minus powr_diff field_simps powr_mult card_lattice_layer)
  also have "\<dots> \<le> ?rhs"
    unfolding C_def using lattice_layer_lower[of _ k "-\<alpha>"] \<open>k > 0\<close>
    by (cases "\<alpha> > 0"; intro sum_mono) (auto split: if_splits)
  finally show ?thesis .
qed

lemma converges_absolutely_iff_aux1:
  fixes \<alpha> :: real
  assumes "\<alpha> > 2"
  shows   "summable (\<lambda>i. \<Sum>\<omega>\<in>lattice_layer (Suc i). 1 / norm \<omega> powr \<alpha>)"
proof (rule summable_comparison_test')
  show "norm (\<Sum>\<omega>\<in>lattice_layer (Suc n). 1 / norm \<omega> powr \<alpha>) \<le>
          8 * real (Suc n) powr (1 - \<alpha>) * Inf_para powr -\<alpha>" for n
  proof -
    have "norm (\<Sum>\<omega>\<in>lattice_layer (Suc n). 1 / norm \<omega> powr \<alpha>) =
          (\<Sum>\<omega>\<in>lattice_layer (Suc n). norm \<omega> powr -\<alpha>)"
      unfolding real_norm_def
      by (subst abs_of_nonneg) (auto intro!: sum_nonneg simp: powr_minus field_simps)
    also have "\<dots> \<le> 8 * real (Suc n) powr (1 - \<alpha>) * Inf_para powr -\<alpha>"
      using sum_\<omega>_upper[of \<alpha> "Suc n"] assms by simp
    finally show ?thesis .
  qed
next
  show "summable (\<lambda>n. 8 * real (Suc n) powr (1 - \<alpha>) * Inf_para powr -\<alpha>)"
    by (subst summable_Suc_iff, intro summable_mult summable_mult2, subst summable_real_powr_iff)
       (use assms in auto)
qed

lemma converges_absolutely_iff_aux2:
  fixes \<alpha> :: real
  assumes "summable (\<lambda>i. \<Sum>\<omega>\<in>lattice_layer (Suc i). 1 / norm \<omega> powr \<alpha>)"
  shows   "\<alpha> > 2"
proof -
  define C where "C = (if \<alpha> > 0 then Sup_para else Inf_para)"
  have "C > 0"
    using Sup_para_pos Inf_para_pos by (auto simp: C_def)

  have "summable (\<lambda>n. 8 * real (Suc n) powr (1 - \<alpha>) * C powr -\<alpha>)"
  proof (rule summable_comparison_test')
    show "norm (8 * real (Suc n) powr (1 - \<alpha>) * C powr -\<alpha>) \<le>
            (\<Sum>\<omega>\<in>lattice_layer (Suc n). 1 / norm \<omega> powr \<alpha>)" for n
    proof -
      have "norm (8 * real (Suc n) powr (1 - \<alpha>) * C powr -\<alpha>) =
            8 * real (Suc n) powr (1 - \<alpha>) * C powr -\<alpha>"
        unfolding real_norm_def by (subst abs_of_nonneg) (auto intro!: sum_nonneg)
      also have "\<dots> \<le> (\<Sum>\<omega>\<in>lattice_layer (Suc n). 1 / norm \<omega> powr \<alpha>)"
        using sum_lattice_layer_lower[of "Suc n" \<alpha>]
        by (auto simp: powr_minus field_simps C_def split: if_splits)
      finally show ?thesis .
    qed
  qed fact
  hence "summable (\<lambda>n. 8 * C powr -\<alpha> * real n powr (1 - \<alpha>))"
    by (subst (asm) summable_Suc_iff) (simp add: mult_ac)
  hence "summable (\<lambda>n. real n powr (1 - \<alpha>))"
    using \<open>C > 0\<close> by (subst (asm) summable_cmult_iff) auto
  thus "\<alpha> > 2"
    by (subst (asm) summable_real_powr_iff) auto
qed

text \<open>Apostol's Lemma 1\<close>
lemma converges_absolutely_iff:
  fixes \<alpha>:: real
  shows "(\<lambda>\<omega>. 1 / norm \<omega> powr \<alpha>) summable_on \<Lambda>\<^sup>* \<longleftrightarrow> \<alpha> > 2"
    (is "?P \<longleftrightarrow> _")
proof -
  have "(\<lambda>\<omega>. 1 / norm \<omega> powr \<alpha>) summable_on \<Lambda>\<^sup>* \<longleftrightarrow>
        (\<lambda>\<omega>. 1 / norm \<omega> powr \<alpha>) summable_on (\<Union>i \<in> {0<..}. lattice_layer i)"
    by (simp add: lattice0_conv_layers)
  also have "\<dots> \<longleftrightarrow> (\<lambda>i. \<Sum>\<omega>\<in>lattice_layer i. 1 / norm \<omega> powr \<alpha>) summable_on {0<..}"
    using lattice_layer_disjoint
    by (intro summable_on_Union_iff has_sum_finite finite_lattice_layer refl)
       (auto simp: disjoint_family_on_def)
  also have "{0<..} = Suc ` UNIV"
    by (auto simp: image_iff) presburger?
  also have "(\<lambda>i. \<Sum>\<omega>\<in>lattice_layer i. 1 / norm \<omega> powr \<alpha>) summable_on Suc ` UNIV \<longleftrightarrow>
             (\<lambda>i. \<Sum>\<omega>\<in>lattice_layer (Suc i). 1 / norm \<omega> powr \<alpha>) summable_on UNIV"
    by (subst summable_on_reindex) (auto simp: o_def)
  also have "\<dots> \<longleftrightarrow> summable (\<lambda>i. \<Sum>\<omega>\<in>lattice_layer (Suc i). 1 / norm \<omega> powr \<alpha>)"
    by (rule summable_on_UNIV_nonneg_real_iff) (auto intro: sum_nonneg)
  also have "\<dots> \<longleftrightarrow> \<alpha> > 2"
    using converges_absolutely_iff_aux1 converges_absolutely_iff_aux2 by blast
  finally show ?thesis .
qed

lemma bounded_lattice_finite:
  assumes "bounded B"
  shows   "finite (\<Lambda> \<inter> B)"
  by (meson not_islimpt_lattice inf.bounded_iff islimpt_subset \<open>bounded B\<close> 
            bounded_infinite_imp_islimpt bounded_subset eq_refl)

lemma closed_subset_lattice: "\<Lambda>' \<subseteq> \<Lambda> \<Longrightarrow> closed \<Lambda>'"
  unfolding closed_limpt using not_islimpt_lattice islimpt_subset by blast

corollary closed_lattice0: "closed \<Lambda>\<^sup>*"
  unfolding lattice0_def by (rule closed_subset_lattice) auto

lemma weierstrass_summand_bound:
  assumes "\<alpha> \<ge> 1" and "R > 0" 
  obtains M where 
    "M > 0"
    "\<And>\<omega> z. \<lbrakk>\<omega> \<in> \<Lambda>; cmod \<omega> > R; cmod z \<le> R\<rbrakk> \<Longrightarrow> norm (z - \<omega>) powr -\<alpha> \<le> M * (norm \<omega> powr -\<alpha>)"
proof -
  obtain m where m: "of_int m > R / norm \<omega>1" "m \<ge> 0"
    by (metis ex_less_of_int le_less_trans linear not_le of_int_0_le_iff)
  obtain W where W: "W \<in> (\<Lambda> - cball 0 R) \<inter> cball 0 (norm W)"
  proof 
    show "of_int m * \<omega>1 \<in> (\<Lambda> - cball 0 R) \<inter> cball 0 (norm (of_int m * \<omega>1))"
      using m latticeI [of m 0]
      by (simp add: field_simps norm_mult)
  qed
  define PF where "PF \<equiv> (\<Lambda> - cball 0 R) \<inter> cball 0 (norm W)"
  have "finite PF"
    by (simp add: PF_def Diff_Int_distrib2 bounded_lattice_finite)
  then have "finite (norm ` PF)"
    by blast
  then obtain r where "r \<in> norm ` PF"  "r \<le> norm W" and r: "\<And>x. x \<in> norm ` PF \<Longrightarrow> r \<le> x"
    using PF_def W Min_le Min_in by (metis empty_iff image_eqI)
  then obtain \<omega>r where \<omega>r: "\<omega>r \<in> PF" "norm \<omega>r = r"
    by blast 
  with assms have "\<omega>r \<in> \<Lambda>" "\<omega>r \<noteq> 0" "r > 0"
    by (auto simp: PF_def)
  have minr: "r \<le> cmod \<omega>" if "\<omega> \<in> \<Lambda>" "cmod \<omega> > R" for \<omega>
    using r  \<open>r \<le> cmod W\<close> that unfolding PF_def by fastforce
  have "R < r"
    using \<omega>r by (simp add: PF_def)
  with \<open>R > 0\<close> have R_iff_r: "cmod \<omega> > R \<longleftrightarrow> cmod \<omega> \<ge> r" if "\<omega> \<in> \<Lambda>" for \<omega>
    using that by (auto simp: minr)
  define M where "M \<equiv> (1 - R/r) powr -\<alpha>"
  have "M > 0"
    unfolding M_def using \<open>R < r\<close> by auto
  moreover
  have "cmod (z - \<omega>) powr -\<alpha> \<le> M * cmod \<omega> powr -\<alpha>" 
    if "\<omega> \<in> \<Lambda>" "cmod z \<le> R" "R < cmod \<omega>" for z \<omega>
  proof -
    have "r \<le> cmod \<omega>"
      using minr that by blast
    then have "\<omega> \<noteq> 0"
      using \<open>0 < r\<close> that by force
    have "1 - R/r \<le> 1 - norm (z/\<omega>)"
      using that \<open>0 < r\<close> \<open>0 < R\<close> \<open>\<omega> \<noteq> 0\<close> \<open>r \<le> cmod \<omega>\<close>
      by (simp add: field_simps norm_divide) (metis mult.commute mult_mono norm_ge_zero)
    also have "\<dots> \<le> norm (1 - z/\<omega>)"
      by (metis norm_one norm_triangle_ineq2)
    also have "\<dots> = norm ((z - \<omega>) / \<omega>)"
      by (simp add: \<open>\<omega> \<noteq> 0\<close> norm_minus_commute diff_divide_distrib)
    finally have *: "1 - R/r \<le> norm ((z - \<omega>) / \<omega>)" .
    have ge_rR: "cmod (z - \<omega>) \<ge> r - R"
      by (smt (verit) \<open>r \<le> cmod \<omega>\<close> norm_minus_commute norm_triangle_ineq2 that(2))
    have "1/M \<le> norm ((z - \<omega>) / \<omega>) powr \<alpha>"
    proof -
      have "1/M = (1 - R / r) powr \<alpha>"
        by (simp add: M_def powr_minus_divide)
      also have "\<dots> \<le> norm ((z - \<omega>) / \<omega>) powr \<alpha>"
        using * \<open>0 < r\<close> \<open>R < r\<close> \<open>1 \<le> \<alpha>\<close> powr_mono2 by force
      finally show ?thesis .
    qed
    then show ?thesis
      using \<open>R > 0\<close> \<open>M > 0\<close> \<open>\<omega> \<noteq> 0\<close>
      by (simp add: mult.commute divide_simps powr_divide norm_divide powr_minus)
  qed
  ultimately show thesis
    using that by presburger
qed

text \<open>Lemma 2 on Apostol p. 8\<close>
lemma weierstrass_aux_converges_absolutely_in_disk:
  assumes "\<alpha> > 2" and "R > 0" and "z \<in> cball 0 R"
  shows "(\<lambda>\<omega>. cmod (z - \<omega>) powr -\<alpha>) summable_on (\<Lambda> - cball 0 R)"
proof -
  have \<Lambda>: "\<Lambda> - cball 0 R \<subseteq> \<Lambda>\<^sup>*"
    using assms by force
  obtain M where "M > 0" and M: "\<And>\<omega>. \<lbrakk>\<omega> \<in> \<Lambda>; cmod \<omega> > R\<rbrakk> \<Longrightarrow> cmod(z - \<omega>) powr -\<alpha> \<le> M * (cmod \<omega> powr -\<alpha>)"
    using weierstrass_summand_bound assms
    by (smt (verit, del_insts) less_eq_real_def mem_cball_0 one_le_numeral)
  have \<section>: "((\<lambda>\<omega>. 1 / cmod \<omega> powr \<alpha>) summable_on \<Lambda>\<^sup>*)"
    using \<open>\<alpha> > 2\<close> converges_absolutely_iff by blast
  have "(\<lambda>\<omega>. M * norm \<omega> powr -\<alpha>) summable_on \<Lambda>\<^sup>*"
    using summable_on_cmult_right [OF \<section>] by (simp add: powr_minus field_class.field_divide_inverse)
  with \<Lambda> have "(\<lambda>\<omega>. M * norm \<omega> powr -\<alpha>) summable_on \<Lambda> - cball 0 R"
    using summable_on_subset_banach by blast
  then show ?thesis
    by (rule summable_on_comparison_test) (use M in auto)
qed

lemma weierstrass_aux_converges_absolutely_in_disk':
  fixes \<alpha> :: nat and R :: real and z:: complex
  assumes "\<alpha> > 2" and "R > 0" and "z \<in> cball 0 R"
  shows "(\<lambda>\<omega>. 1 / norm (z - \<omega>) ^ \<alpha>) summable_on (\<Lambda> - cball 0 R)"
proof -
  have "(\<lambda>\<omega>. norm (z - \<omega>) powr -of_nat \<alpha>) summable_on (\<Lambda> - cball 0 R)"
    using assms by (intro weierstrass_aux_converges_absolutely_in_disk) auto
  also have "?this \<longleftrightarrow> ?thesis"
    unfolding powr_minus
    by (intro summable_on_cong refl, subst powr_realpow)
       (use assms in \<open>auto simp: field_simps\<close>)
  finally show ?thesis .
qed

lemma weierstrass_aux_converges_in_disk':
  fixes \<alpha> :: nat and R :: real and z:: complex
  assumes "\<alpha> > 2" and "R > 0" and "z \<in> cball 0 R"
  shows "(\<lambda>\<omega>. 1 / (z - \<omega>) ^ \<alpha>) summable_on (\<Lambda> - cball 0 R)"
  by (rule abs_summable_summable)
     (use weierstrass_aux_converges_absolutely_in_disk'[OF assms] 
      in  \<open>simp add: norm_divide norm_power\<close>)

lemma weierstrass_aux_converges_absolutely:
  fixes \<alpha> :: real
  assumes "\<alpha> > 2" and "\<Lambda>' \<subseteq> \<Lambda>"
  shows "(\<lambda>\<omega>. norm (z - \<omega>) powr -\<alpha>) summable_on \<Lambda>'"
proof (cases "z = 0")
  case True
  hence "(\<lambda>\<omega>. norm (z - \<omega>) powr -\<alpha>) summable_on \<Lambda>\<^sup>*"
    using converges_absolutely_iff[of \<alpha>] assms by (simp add: powr_minus field_simps)
  hence "(\<lambda>\<omega>. norm (z - \<omega>) powr -\<alpha>) summable_on \<Lambda>"
    by (simp add: lattice_lattice0 summable_on_insert_iff)
  thus ?thesis
    by (rule summable_on_subset_banach) fact
next
  case [simp]: False
  define R where "R = norm z"
  have "(\<lambda>\<omega>. norm (z - \<omega>) powr -\<alpha>) summable_on (\<Lambda> - cball 0 R)"
    using assms by (intro weierstrass_aux_converges_absolutely_in_disk) (auto simp: R_def)
  hence "(\<lambda>\<omega>. norm (z - \<omega>) powr -\<alpha>) summable_on (\<Lambda> - cball 0 R) \<union> (\<Lambda> \<inter> cball 0 R)"
    by (intro bounded_lattice_finite summable_on_union[OF _ summable_on_finite]) auto
  also have "\<dots> = \<Lambda>"
    by blast
  finally show ?thesis
    by (rule summable_on_subset) fact
qed

lemma weierstrass_aux_converges_absolutely':
  fixes \<alpha> :: nat
  assumes "\<alpha> > 2" and "\<Lambda>' \<subseteq> \<Lambda>"
  shows "(\<lambda>\<omega>. 1 / norm (z - \<omega>) ^ \<alpha>) summable_on \<Lambda>'"
  using weierstrass_aux_converges_absolutely[of "of_nat \<alpha>" \<Lambda>' z] assms
  by (simp add: powr_nat' powr_minus field_simps norm_power norm_divide powr_realpow')

lemma weierstrass_aux_converges:
  fixes \<alpha> :: real
  assumes "\<alpha> > 2" and "\<Lambda>' \<subseteq> \<Lambda>"
  shows "(\<lambda>\<omega>. (z - \<omega>) powr -\<alpha>) summable_on \<Lambda>'"
  by (rule abs_summable_summable)
     (use weierstrass_aux_converges_absolutely[OF assms] 
      in  \<open>simp add: norm_divide norm_powr_real_powr'\<close>)

lemma weierstrass_aux_converges':
  fixes \<alpha> :: nat
  assumes "\<alpha> > 2" and "\<Lambda>' \<subseteq> \<Lambda>"
  shows "(\<lambda>\<omega>. 1 / (z - \<omega>) ^ \<alpha>) summable_on \<Lambda>'"
  using weierstrass_aux_converges[of "of_nat \<alpha>" \<Lambda>' z] assms 
  by (simp add: powr_nat' powr_minus field_simps)

lemma
  fixes \<alpha> R :: real
  assumes "\<alpha> > 2" "R > 0"
  shows weierstrass_aux_converges_absolutely_uniformly_in_disk:
          "uniform_limit (cball 0 R)
                         (\<lambda>X z. \<Sum>\<omega>\<in>X. norm ((z - \<omega>) powr -\<alpha>))
                         (\<lambda>z. \<Sum>\<^sub>\<infinity>\<omega>\<in>\<Lambda>-cball 0 R. norm ((z - \<omega>) powr -\<alpha>))
                         (finite_subsets_at_top (\<Lambda> - cball 0 R))" (is ?th1)
  and   weierstrass_aux_converges_uniformly_in_disk:
          "uniform_limit (cball 0 R)
                         (\<lambda>X z. \<Sum>\<omega>\<in>X. (z - \<omega>) powr -\<alpha>)
                         (\<lambda>z. \<Sum>\<^sub>\<infinity>\<omega>\<in>\<Lambda>-cball 0 R. (z - \<omega>) powr -\<alpha>)
                         (finite_subsets_at_top (\<Lambda> - cball 0 R))" (is ?th2)
proof -
  obtain M where M:
    "M > 0" "\<And>\<omega> z. \<lbrakk>\<omega> \<in> \<Lambda>; norm \<omega> > R; norm z \<le> R\<rbrakk> \<Longrightarrow> norm (z - \<omega>) powr -\<alpha> \<le> M * norm \<omega> powr -\<alpha>"
    using weierstrass_summand_bound[of \<alpha> R] assms by auto

  have 1: "(\<lambda>\<omega>. M * norm \<omega> powr -\<alpha>) summable_on (\<Lambda> - cball 0 R)"
  proof -
    have "(\<lambda>\<omega>. 1 / norm \<omega> powr \<alpha>) summable_on \<Lambda>\<^sup>*"
      using assms by (subst converges_absolutely_iff) auto
    hence "(\<lambda>\<omega>. M * norm \<omega> powr -\<alpha>) summable_on \<Lambda>\<^sup>*"
      by (intro summable_on_cmult_right) (auto simp: powr_minus field_simps)
    thus "(\<lambda>\<omega>. M * norm \<omega> powr -\<alpha>) summable_on (\<Lambda> - cball 0 R)"
      by (rule summable_on_subset) (use assms in \<open>auto simp: lattice0_def\<close>)
  qed

  have 2: "norm ((z - \<omega>) powr -\<alpha>) \<le> M * norm \<omega> powr -\<alpha>"
    if "\<omega> \<in> \<Lambda> - cball 0 R" "z \<in> cball 0 R" for \<omega> z
  proof -
    have "norm ((z - \<omega>) powr -\<alpha>) = norm (z - \<omega>) powr -\<alpha>"
      by (auto simp add: powr_def)
    also have "\<dots> \<le> M * norm \<omega> powr -\<alpha>"
      using that by (intro M) auto
    finally show "norm ((z - \<omega>) powr -\<alpha>) \<le> M * norm \<omega> powr -\<alpha>"
      by simp
  qed

  show ?th1 ?th2
    by (rule Weierstrass_m_test_general[OF _ 1]; use 2 in simp)+
qed

lemma
  fixes n :: nat and R :: real
  assumes "n > 2" "R > 0"
  shows weierstrass_aux_converges_absolutely_uniformly_in_disk':
          "uniform_limit (cball 0 R)
                         (\<lambda>X z. \<Sum>\<omega>\<in>X. norm (1 / (z - \<omega>) ^ n))
                         (\<lambda>z. \<Sum>\<^sub>\<infinity>\<omega>\<in>\<Lambda>-cball 0 R. norm (1 / (z - \<omega>) ^ n))
                         (finite_subsets_at_top (\<Lambda> - cball 0 R))" (is ?th1)
  and   weierstrass_aux_converges_uniformly_in_disk':
          "uniform_limit (cball 0 R)
                         (\<lambda>X z. \<Sum>\<omega>\<in>X. 1 / (z - \<omega>) powr n)
                         (\<lambda>z. \<Sum>\<^sub>\<infinity>\<omega>\<in>\<Lambda>-cball 0 R. 1 / (z - \<omega>) ^ n)
                         (finite_subsets_at_top (\<Lambda> - cball 0 R))" (is ?th2)
proof -
  have "uniform_limit (cball 0 R)
           (\<lambda>X z. \<Sum>\<omega>\<in>X. norm ((z - \<omega>) powr -real n))
           (\<lambda>z. \<Sum>\<^sub>\<infinity>\<omega>\<in>\<Lambda>-cball 0 R. norm ((z - \<omega>) powr -real n))
           (finite_subsets_at_top (\<Lambda> - cball 0 R))"
    by (rule weierstrass_aux_converges_absolutely_uniformly_in_disk) (use assms in auto)
  also have "?this \<longleftrightarrow> ?th1"
    by (intro uniform_limit_cong eventually_finite_subsets_at_top_weakI sum.cong ballI)
       (auto simp: norm_divide norm_power powr_minus field_simps powr_nat
             intro!: infsum_cong)
  finally show ?th1 .
next
  have "uniform_limit (cball 0 R)
           (\<lambda>X z. \<Sum>\<omega>\<in>X. (z - \<omega>) powr -of_nat n)
           (\<lambda>z. \<Sum>\<^sub>\<infinity>\<omega>\<in>\<Lambda>-cball 0 R. (z - \<omega>) powr -of_nat n)
           (finite_subsets_at_top (\<Lambda> - cball 0 R))"
    using weierstrass_aux_converges_uniformly_in_disk[of "of_nat n" R] assms by auto
  also have "?this \<longleftrightarrow> ?th2"
    by (intro uniform_limit_cong eventually_finite_subsets_at_top_weakI sum.cong ballI)
       (auto simp: norm_divide norm_power powr_minus field_simps powr_nat
             intro!: infsum_cong)
  finally show ?th2 .
qed  


definition eisenstein_fun_aux :: "nat \<Rightarrow> complex \<Rightarrow> complex" where
  "eisenstein_fun_aux n z =
     (if n = 0 then 1 else if n < 3 \<or> z \<in> \<Lambda>\<^sup>* then 0 else (\<Sum>\<^sub>\<infinity>\<omega>\<in>\<Lambda>\<^sup>*. 1 / (z - \<omega>) ^ n))"

lemma eisenstein_fun_aux_at_pole_eq_0: "n > 0 \<Longrightarrow> z \<in> \<Lambda>\<^sup>* \<Longrightarrow> eisenstein_fun_aux n z = 0"
  by (simp add: eisenstein_fun_aux_def)

lemma eisenstein_fun_aux_has_sum:
  assumes "n \<ge> 3" "z \<notin> \<Lambda>\<^sup>*"
  shows   "((\<lambda>\<omega>. 1 / (z - \<omega>) ^ n) has_sum eisenstein_fun_aux n z) \<Lambda>\<^sup>*"
proof -
  have "eisenstein_fun_aux n z = (\<Sum>\<^sub>\<infinity>\<omega>\<in>\<Lambda>\<^sup>*. 1 / (z - \<omega>) ^ n)"
    using assms by (simp add: eisenstein_fun_aux_def)
  also have "((\<lambda>\<omega>. 1 / (z - \<omega>) ^ n) has_sum \<dots>) \<Lambda>\<^sup>*"
    using assms by (intro has_sum_infsum weierstrass_aux_converges') (auto simp: lattice0_def)
  finally show ?thesis .
qed

lemma eisenstein_fun_aux_minus: "eisenstein_fun_aux n (-z) = (-1) ^ n * eisenstein_fun_aux n z"
proof (cases "n < 3 \<or> z \<in> \<Lambda>\<^sup>*")
  case False
  have "eisenstein_fun_aux n (-z) = (\<Sum>\<^sub>\<infinity>\<omega>\<in>\<Lambda>\<^sup>*. 1 / (- z - \<omega>) ^ n)"
    using False by (auto simp: eisenstein_fun_aux_def lattice0_def uminus_in_lattice_iff)
  also have "\<dots> = (\<Sum>\<^sub>\<infinity>\<omega>\<in>uminus ` \<Lambda>\<^sup>*. 1 / (\<omega> - z) ^ n)"
    by (subst infsum_reindex) (auto simp: o_def minus_diff_commute inj_on_def)
  also have "uminus ` \<Lambda>\<^sup>* = \<Lambda>\<^sup>*"
    by (auto simp: lattice0_def uminus_in_lattice_iff image_def intro: bexI[of _ "-x" for x])
  also have "(\<lambda>\<omega>. 1 / (\<omega> - z) ^ n) = (\<lambda>\<omega>. (-1) ^ n * (1 / (z - \<omega>) ^ n))"
  proof
    fix \<omega> :: complex
    have "1 / (\<omega> - z) ^ n = (1 / (\<omega> - z)) ^ n"
      by (simp add: power_divide)
    also have "1 / (\<omega> - z) = (-1) / (z - \<omega>)"
      by (simp add: divide_simps)
    also have "\<dots> ^ n = (-1) ^ n * (1 / (z - \<omega>) ^ n)"
      by (subst power_divide) auto
    finally show "1 / (\<omega> - z) ^ n = (-1) ^ n * (1 / (z - \<omega>) ^ n)" .
  qed
  also have "(\<Sum>\<^sub>\<infinity>\<omega>\<in>\<Lambda>\<^sup>*. (-1) ^ n * (1 / (z - \<omega>) ^ n)) = (-1) ^ n * eisenstein_fun_aux n z"
    using False by (subst infsum_cmult_right') (auto simp: eisenstein_fun_aux_def)
  finally show ?thesis .
qed (auto simp: eisenstein_fun_aux_def lattice0_def uminus_in_lattice_iff)

lemma eisenstein_fun_aux_even_minus: "even n \<Longrightarrow> eisenstein_fun_aux n (-z) = eisenstein_fun_aux n z"
  by (simp add: eisenstein_fun_aux_minus)

lemma eisenstein_fun_aux_odd_minus: "odd n \<Longrightarrow> eisenstein_fun_aux n (-z) = -eisenstein_fun_aux n z"
  by (simp add: eisenstein_fun_aux_minus)

(* TODO generalise. The ball is not needed. *)
lemma eisenstein_fun_aux_has_field_derivative_aux:
  fixes \<alpha> :: nat and R :: real
  defines "F \<equiv> (\<lambda>\<alpha> z. \<Sum>\<^sub>\<infinity>\<omega>\<in>\<Lambda>-cball 0 R. 1 / (z - \<omega>) ^ \<alpha>)"
  assumes "\<alpha> > 2" "R > 0" "w \<in> ball 0 R"
  shows   "(F \<alpha> has_field_derivative -of_nat \<alpha> * F (Suc \<alpha>) w) (at w)"
proof -
  define \<alpha>' where "\<alpha>' = \<alpha> - 1"
  have \<alpha>': "\<alpha> = Suc \<alpha>'"
    using assms by (simp add: \<alpha>'_def)
  have 1: "\<forall>\<^sub>F n in finite_subsets_at_top (\<Lambda> - cball 0 R).
            continuous_on (cball 0 R) (\<lambda>z. \<Sum>\<omega>\<in>n. 1 / (z - \<omega>) ^ \<alpha>) \<and>
            (\<forall>z\<in>ball 0 R. ((\<lambda>z. \<Sum>\<omega>\<in>n. 1 / (z - \<omega>) ^ \<alpha>) has_field_derivative (\<Sum>\<omega>\<in>n. -\<alpha> / (z - \<omega>) ^ Suc \<alpha>)) (at z))"
    (* TODO FIXME: ugly *)
  proof (intro eventually_finite_subsets_at_top_weakI conjI continuous_intros derivative_intros ballI)
    fix z::complex and X n
    assume "finite X"  "X \<subseteq> \<Lambda> - cball 0 R"
        and "z \<in> ball 0 R"  "n \<in> X"
    then show "((\<lambda>z. 1 / (z - n) ^ \<alpha>) has_field_derivative of_int (- int \<alpha>) / (z - n) ^ Suc \<alpha>) (at z)"
     apply (auto intro!: derivative_eq_intros simp: divide_simps)
      apply (simp add: algebra_simps \<alpha>')
      done
  qed auto

  have "uniform_limit (cball 0 R)
                      (\<lambda>X z. \<Sum>\<omega>\<in>X. (z - \<omega>) powr of_real (-of_nat \<alpha>))
                      (\<lambda>z. \<Sum>\<^sub>\<infinity>\<omega>\<in>\<Lambda>-cball 0 R. (z - \<omega>) powr of_real (-of_nat \<alpha>))
                      (finite_subsets_at_top (\<Lambda> - cball 0 R))"
    using assms by (intro weierstrass_aux_converges_uniformly_in_disk) auto
  also have "?this \<longleftrightarrow> uniform_limit (cball 0 R) (\<lambda>X z. \<Sum>\<omega>\<in>X. 1 / (z - \<omega>) ^ \<alpha>) (F \<alpha>)
                         (finite_subsets_at_top (\<Lambda> - cball 0 R))"
    using assms unfolding F_def
    by (intro uniform_limit_cong eventually_finite_subsets_at_top_weakI)
       (auto simp: powr_minus powr_nat field_simps intro!: sum.cong infsum_cong)
  finally have 2: \<dots> .

  have 3: "finite_subsets_at_top (\<Lambda> - cball 0 R) \<noteq> bot"
    by simp

  obtain g where g: "continuous_on (cball 0 R) (F \<alpha>)"
                    "\<And>w. w \<in> ball 0 R \<Longrightarrow> (F \<alpha> has_field_derivative g w) (at w) \<and>
                        ((\<lambda>\<omega>. -of_nat \<alpha> / (w - \<omega>) ^ Suc \<alpha>) has_sum g w) (\<Lambda> - cball 0 R)"
    unfolding has_sum_def using has_complex_derivative_uniform_limit[OF 1 2 3 \<open>R > 0\<close>] by auto

  have "((\<lambda>\<omega>. -of_nat \<alpha> * (1 / (w - \<omega>) ^ Suc \<alpha>)) has_sum -of_nat \<alpha> * F (Suc \<alpha>) w) (\<Lambda> - cball 0 R)"
    unfolding F_def using assms
    by (intro has_sum_cmult_right has_sum_infsum weierstrass_aux_converges') auto
  moreover have "((\<lambda>\<omega>.  -of_nat \<alpha> * (1 / (w - \<omega>) ^ Suc \<alpha>)) has_sum g w) (\<Lambda> - cball 0 R)"
    using g(2)[of w] assms by simp
  ultimately have "g w = -of_nat \<alpha> * F (Suc \<alpha>) w"
    by (metis infsumI)
  thus ?thesis
    using g(2)[of w] assms by (simp add: F_def)
qed

lemma eisenstein_fun_aux_has_field_derivative:
  assumes z: "z \<notin> \<Lambda>\<^sup>*" and n: "n \<ge> 3"
  shows   "(eisenstein_fun_aux n has_field_derivative -of_nat n * eisenstein_fun_aux (Suc n) z) (at z)"
proof -
  define R where "R = norm z + 1"
  have R: "R > 0" "norm z < R"
    by (auto simp: R_def add_nonneg_pos)
  have "finite (\<Lambda> \<inter> cball 0 R)"
    by (simp add: bounded_lattice_finite)
  moreover have "\<Lambda>\<^sup>* \<inter> cball 0 R \<subseteq> \<Lambda> \<inter> cball 0 R"
    unfolding lattice0_def by blast
  ultimately have fin: "finite (\<Lambda>\<^sup>* \<inter> cball 0 R)"
    using finite_subset by blast
  define n' where "n' = n - 1"
  from n have n': "n = Suc n'"
    by (simp add: n'_def)

  define F1 where "F1 = (\<lambda>n z. \<Sum>\<^sub>\<infinity>\<omega>\<in>\<Lambda>-cball 0 R. 1 / (z - \<omega>) ^ n)"
  define F2 where "F2 = (\<lambda>n z. \<Sum>\<omega>\<in>\<Lambda>\<^sup>*\<inter>cball 0 R. 1 / (z - \<omega>) ^ n)"

  have "(F1 n has_field_derivative -of_nat n * F1 (Suc n) z) (at z)"
    unfolding F1_def
    by (rule eisenstein_fun_aux_has_field_derivative_aux) (use n in \<open>auto simp: R_def add_nonneg_pos\<close>)
  moreover have "(F2 n has_field_derivative -of_nat n * F2 (Suc n) z) (at z)"
    unfolding F2_def sum_distrib_left lattice0_def
    by (rule derivative_eq_intros refl sum.cong | use R z n in \<open>force simp: lattice0_def\<close>)+
       (simp add: divide_simps power3_eq_cube power4_eq_xxxx n')
  ultimately have "((\<lambda>z. F1 n z + F2 n z) has_field_derivative
                     (-of_nat n * F1 (Suc n) z) + (-of_nat n * F2 (Suc n) z)) (at z)"
    by (intro derivative_intros)
  also have "?this \<longleftrightarrow> (eisenstein_fun_aux n has_field_derivative (-of_nat n * F1 (Suc n) z) + (-of_nat n * F2 (Suc n) z)) (at z)"
  proof (intro has_field_derivative_cong_ev refl)
    have "eventually (\<lambda>z'. z' \<in> -\<Lambda>\<^sup>*) (nhds z)"
      using z by (intro eventually_nhds_in_open) (auto simp: closed_lattice0)
    thus "\<forall>\<^sub>F x in nhds z. x \<in> UNIV \<longrightarrow> F1 n x + F2 n x = eisenstein_fun_aux n x"
    proof eventually_elim
      case (elim z)
      have "((\<lambda>\<omega>. 1 / (z - \<omega>) ^ n) has_sum (F1 n z + F2 n z)) ((\<Lambda> - cball 0 R) \<union> (\<Lambda>\<^sup>* \<inter> cball 0 R))"
        unfolding F1_def F2_def using R fin n
        by (intro has_sum_Un_disjoint[OF has_sum_infsum has_sum_finite]
                  summable_on_subset[OF weierstrass_aux_converges']) auto
      also have "(\<Lambda> - cball 0 R) \<union> (\<Lambda>\<^sup>* \<inter> cball 0 R) = \<Lambda>\<^sup>*"
        using R unfolding lattice0_def by auto
      finally show ?case using elim n 
        unfolding F1_def F2_def by (simp add: infsumI eisenstein_fun_aux_def)
    qed
  qed auto
  also have "(-of_nat n * F1 (Suc n) z) + (-of_nat n * F2 (Suc n) z) = -of_nat n * (F1 (Suc n) z + F2 (Suc n) z)"
    by (simp add: algebra_simps)
  also have "F1 (Suc n) z + F2 (Suc n) z = eisenstein_fun_aux (Suc n) z"
  proof -
    have "((\<lambda>\<omega>. 1 / (z - \<omega>) ^ Suc n) has_sum (F1 (Suc n) z + F2 (Suc n) z)) ((\<Lambda> - cball 0 R) \<union> (\<Lambda>\<^sup>* \<inter> cball 0 R))"
      unfolding F1_def F2_def using R fin n
      by (intro has_sum_Un_disjoint[OF has_sum_infsum has_sum_finite] weierstrass_aux_converges') auto
    also have "(\<Lambda> - cball 0 R) \<union> (\<Lambda>\<^sup>* \<inter> cball 0 R) = \<Lambda>\<^sup>*"
      using R unfolding lattice0_def by auto
    finally show ?thesis using n z
      unfolding F1_def F2_def eisenstein_fun_aux_def by (simp add: infsumI)
  qed
  finally show ?thesis .
qed

lemmas eisenstein_fun_aux_has_field_derivative' [derivative_intros] =
  DERIV_chain2[OF eisenstein_fun_aux_has_field_derivative]

lemma higher_deriv_eisenstein_fun_aux:
  assumes z: "z \<notin> \<Lambda>\<^sup>*" and n: "n \<ge> 3"
  shows   "(deriv ^^ m) (eisenstein_fun_aux n) z =
             (-1) ^ m * pochhammer (of_nat n) m * eisenstein_fun_aux (n + m) z"
  using z n
proof (induction m arbitrary: z n)
  case 0
  thus ?case by simp
next
  case (Suc m z n)
  have ev: "eventually (\<lambda>z. z \<in> -\<Lambda>\<^sup>*) (nhds z)"
    using Suc.prems closed_lattice0 by (intro eventually_nhds_in_open) auto
  have "(deriv ^^ Suc m) (eisenstein_fun_aux n) z = deriv ((deriv ^^ m) (eisenstein_fun_aux n)) z"
    by simp
  also have "\<dots> = deriv (\<lambda>z. (-1)^ m * pochhammer (of_nat n) m * eisenstein_fun_aux (n + m) z) z"
    by (intro deriv_cong_ev eventually_mono[OF ev]) (use Suc in auto)
  also have "\<dots> = (-1) ^ Suc m * pochhammer (of_nat n) (Suc m) * eisenstein_fun_aux (Suc (n + m)) z"
    using Suc.prems
    by (intro DERIV_imp_deriv)
       (auto intro!: derivative_eq_intros simp: pochhammer_Suc algebra_simps)
  finally show ?case
    by simp
qed

lemma eisenstein_fun_aux_holomorphic: "eisenstein_fun_aux n holomorphic_on -\<Lambda>\<^sup>*"
proof (cases "n \<ge> 3")
  case True
  thus ?thesis
    using closed_lattice0
    by (subst holomorphic_on_open) (auto intro!: eisenstein_fun_aux_has_field_derivative)
next
  case False
  thus ?thesis
    by (cases "n = 0") (auto simp: eisenstein_fun_aux_def [abs_def])
qed

lemma eisenstein_fun_aux_holomorphic' [holomorphic_intros]:
  assumes "f holomorphic_on A" "\<And>z. z \<in> A \<Longrightarrow> f z \<notin> \<Lambda>\<^sup>*"
  shows   "(\<lambda>z. eisenstein_fun_aux n (f z)) holomorphic_on A"
proof -
  have "eisenstein_fun_aux n \<circ> f holomorphic_on A"
    by (rule holomorphic_on_compose_gen assms eisenstein_fun_aux_holomorphic)+ (use assms in auto)
  thus ?thesis by (simp add: o_def)
qed

lemma eisenstein_fun_aux_analytic: "eisenstein_fun_aux n analytic_on -\<Lambda>\<^sup>*"
  by (simp add: analytic_on_open closed_lattice0 open_Compl eisenstein_fun_aux_holomorphic)  

lemma eisenstein_fun_aux_analytic' [analytic_intros]: 
  assumes "f analytic_on A" "\<And>z. z \<in> A \<Longrightarrow> f z \<notin> \<Lambda>\<^sup>*"
  shows   "(\<lambda>z. eisenstein_fun_aux n (f z)) analytic_on A"
proof -
  have "eisenstein_fun_aux n \<circ> f analytic_on A"
    by (rule analytic_on_compose_gen assms eisenstein_fun_aux_analytic)+ (use assms in auto)
  thus ?thesis by (simp add: o_def)
qed

lemma eisenstein_fun_aux_continuous_on: "continuous_on (-\<Lambda>\<^sup>*) (eisenstein_fun_aux n)"
  using holomorphic_on_imp_continuous_on eisenstein_fun_aux_holomorphic by blast

lemma eisenstein_fun_aux_continuous_on' [continuous_intros]:
  assumes "continuous_on A f" "\<And>z. z \<in> A \<Longrightarrow> f z \<notin> \<Lambda>\<^sup>*"
  shows   "continuous_on A (\<lambda>z. eisenstein_fun_aux n (f z))"
  by (rule continuous_on_compose2[OF eisenstein_fun_aux_continuous_on assms(1)]) (use assms in auto)

lemma weierstrass_aux_translate:
  fixes \<alpha> :: real
  assumes "\<alpha> > 2"
  shows   "(\<Sum>\<^sub>\<infinity>\<omega>\<in>\<Lambda>. (z + w - \<omega>) powr -\<alpha>) = (\<Sum>\<^sub>\<infinity>\<omega>\<in>(+) (-w) ` \<Lambda>. (z - \<omega>) powr -\<alpha>)"
  by (subst infsum_reindex) (auto simp: o_def algebra_simps)

lemma weierstrass_aux_holomorphic:
  assumes "\<alpha> > 2" "\<Lambda>' \<subseteq> \<Lambda>" "finite (\<Lambda> - \<Lambda>')"
  shows   "(\<lambda>z. \<Sum>\<^sub>\<infinity>\<omega>\<in>\<Lambda>'. 1 / (z - \<omega>) ^ \<alpha>) holomorphic_on -\<Lambda>'"
proof -
  define M where "M = Max (insert 0 (norm ` (\<Lambda> - \<Lambda>')))"
  have M: "M \<ge> 0" "\<And>\<omega>. \<omega> \<in> \<Lambda> - \<Lambda>' \<Longrightarrow> M \<ge> norm \<omega>"
    using assms by (auto simp: M_def)
  have [simp]: "closed \<Lambda>'"
    using assms(2) by (rule closed_subset_lattice)

  have *: "(\<lambda>z. \<Sum>\<^sub>\<infinity>\<omega>\<in>\<Lambda>'. 1 / (z - \<omega>) ^ \<alpha>) holomorphic_on ball 0 R - \<Lambda>'" if R: "R > M" for R
  proof -
    define F where "F = (\<lambda>\<alpha> z. \<Sum>\<^sub>\<infinity>\<omega>\<in>\<Lambda>-cball 0 R. 1 / (z - \<omega>) ^ \<alpha>)"
    define G where "G = (\<lambda>\<alpha> z. \<Sum>\<omega>\<in>\<Lambda>'\<inter>cball 0 R. 1 / (z - \<omega>) ^ \<alpha>)"

    have "(F \<alpha> has_field_derivative -of_nat \<alpha> * F (Suc \<alpha>) z) (at z)" if z: "z \<in> ball 0 R" for z
      unfolding F_def using assms R M(1) z by (intro eisenstein_fun_aux_has_field_derivative_aux) auto
    hence "F \<alpha> holomorphic_on ball 0 R - \<Lambda>'"
      using holomorphic_on_open \<open>closed \<Lambda>'\<close> by blast
    hence "(\<lambda>z. F \<alpha> z + G \<alpha> z) holomorphic_on ball 0 R - \<Lambda>'"
      unfolding G_def using assms M R by (intro holomorphic_intros) auto
    also have "(\<lambda>z. F \<alpha> z + G \<alpha> z) = (\<lambda>z. \<Sum>\<^sub>\<infinity>\<omega>\<in>\<Lambda>'. 1 / (z - \<omega>) ^ \<alpha>)"
    proof
      fix z :: complex
      have "finite (\<Lambda> \<inter> cball 0 R)"
        by (intro bounded_lattice_finite) auto
      moreover have "\<Lambda>' \<inter> cball 0 R \<subseteq> \<Lambda> \<inter> cball 0 R"
        using assms by blast
      ultimately have "finite (\<Lambda>' \<inter> cball 0 R)"
        using finite_subset by blast
      hence "((\<lambda>\<omega>. 1 / (z - \<omega>) ^ \<alpha>) has_sum (F \<alpha> z + G \<alpha> z)) ((\<Lambda> - cball 0 R) \<union> (\<Lambda>' \<inter> cball 0 R))"
        unfolding F_def G_def using assms
        by (intro has_sum_Un_disjoint[OF has_sum_infsum has_sum_finite] weierstrass_aux_converges') auto
      also have "(\<Lambda> - cball 0 R) \<union> (\<Lambda>' \<inter> cball 0 R) = \<Lambda>'"
        using M R assms by (force simp: not_le)
      finally show "F \<alpha> z + G \<alpha> z = (\<Sum>\<^sub>\<infinity>\<omega>\<in>\<Lambda>'. 1 / (z - \<omega>) ^ \<alpha>)"
        by (simp add: infsumI)
    qed
    finally show ?thesis .
  qed

  have "(\<lambda>z. \<Sum>\<^sub>\<infinity>\<omega>\<in>\<Lambda>'. 1 / (z - \<omega>) ^ \<alpha>) holomorphic_on (\<Union>R\<in>{R. R > M}. ball 0 R - \<Lambda>')"
    by (rule holomorphic_on_UN_open) (use * \<open>closed \<Lambda>'\<close> in auto)
  also have "\<dots> = (\<Union>R\<in>{R. R > M}. ball 0 R) - \<Lambda>'"
    by blast
  also have "(\<Union>R\<in>{R. R > M}. ball 0 R) = (UNIV :: complex set)"
  proof (safe intro!: UN_I)
    fix z :: complex
    show "norm z + M + 1 > M" "z \<in> ball 0 (norm z + M + 1)"
      using M(1) by (auto intro: add_nonneg_pos)
  qed auto
  finally show ?thesis
    by (simp add: Compl_eq_Diff_UNIV)
qed


definition eisenstein_fun :: "nat \<Rightarrow> complex \<Rightarrow> complex" where
  "eisenstein_fun n z = (if n < 3 \<or> z \<in> \<Lambda> then 0 else (\<Sum>\<^sub>\<infinity>\<omega>\<in>\<Lambda>. 1 / (z - \<omega>) ^ n))"

lemma eisenstein_fun_has_sum:
  "n \<ge> 3 \<Longrightarrow> z \<notin> \<Lambda> \<Longrightarrow> ((\<lambda>\<omega>. 1 / (z - \<omega>) ^ n) has_sum eisenstein_fun n z) \<Lambda>"
  unfolding eisenstein_fun_def by (auto intro!: has_sum_infsum weierstrass_aux_converges')

lemma eisenstein_fun_at_pole_eq_0: "z \<in> \<Lambda> \<Longrightarrow> eisenstein_fun n z = 0"
  by (simp add: eisenstein_fun_def)

lemma eisenstein_fun_conv_eisenstein_fun_aux:
  assumes "n \<ge> 3" "z \<notin> \<Lambda>"
  shows   "eisenstein_fun n z = eisenstein_fun_aux n z + 1 / z ^ n"
proof -
  from assms have "eisenstein_fun n z = (\<Sum>\<^sub>\<infinity>\<omega>\<in>insert 0 \<Lambda>\<^sup>*. 1 / (z - \<omega>) ^ n)"
    by (simp add: eisenstein_fun_def lattice_lattice0)
  also from assms have "\<dots> = (\<Sum>\<^sub>\<infinity>\<omega>\<in>\<Lambda>\<^sup>*. 1 / (z - \<omega>) ^ n) + 1 / z ^ n"
    by (subst infsum_insert) (auto intro!: weierstrass_aux_converges' simp: lattice_lattice0)
  also from assms have "\<dots> = eisenstein_fun_aux n z + 1 / z ^ n"
    by (simp add: eisenstein_fun_aux_def lattice_lattice0)
  finally show ?thesis .
qed

lemma eisenstein_fun_altdef:
  "eisenstein_fun n z = (if n < 3 \<or> z \<in> \<Lambda> then 0 else eisenstein_fun_aux n z + 1 / z ^ n)"
  using eisenstein_fun_conv_eisenstein_fun_aux[of n z]
  by (auto simp: eisenstein_fun_def eisenstein_fun_aux_def lattice0_def)

lemma eisenstein_fun_minus: "eisenstein_fun n (-z) = (-1) ^ n * eisenstein_fun n z"
  by (auto simp: eisenstein_fun_altdef eisenstein_fun_aux_minus lattice0_def uminus_in_lattice_iff
                 power_minus' divide_simps)
     (auto simp: algebra_simps)

lemma eisenstein_fun_even_minus: "even n \<Longrightarrow> eisenstein_fun n (-z) = eisenstein_fun n z"
  by (simp add: eisenstein_fun_minus)

lemma eisenstein_fun_odd_minus: "odd n \<Longrightarrow> eisenstein_fun n (-z) = -eisenstein_fun n z"
  by (simp add: eisenstein_fun_minus)

lemma eisenstein_fun_has_field_derivative:
  assumes "n \<ge> 3" "z \<notin> \<Lambda>"
  shows   "(eisenstein_fun n has_field_derivative -of_nat n * eisenstein_fun (Suc n) z) (at z)"
proof -
  define n' where "n' = n - 1"
  have n': "n = Suc n'"
    using assms by (simp add: n'_def)
  have ev: "eventually (\<lambda>z. z \<in> -\<Lambda>) (nhds z)"
    using assms closed_lattice by (intro eventually_nhds_in_open) auto

  have "((\<lambda>z. eisenstein_fun_aux n z + 1 / z ^ n) has_field_derivative
        -of_nat n * eisenstein_fun (Suc n) z) (at z)"
    using assms
    apply (auto intro!: derivative_eq_intros)
     apply (auto simp: eisenstein_fun_conv_eisenstein_fun_aux lattice_lattice0 field_simps n')
    done
  also have "?this \<longleftrightarrow> ?thesis"
    using assms by (intro has_field_derivative_cong_ev refl eventually_mono[OF ev])
                   (auto simp: eisenstein_fun_conv_eisenstein_fun_aux)
  finally show ?thesis .
qed

lemmas eisenstein_fun_has_field_derivative' [derivative_intros] =
  DERIV_chain2[OF eisenstein_fun_has_field_derivative]

lemma eisenstein_fun_holomorphic: "eisenstein_fun n holomorphic_on -\<Lambda>"
proof (cases "n \<ge> 3")
  case True
  thus ?thesis using closed_lattice
    by (subst holomorphic_on_open) (auto intro!: eisenstein_fun_has_field_derivative)
qed (auto simp: eisenstein_fun_def [abs_def])

lemma higher_deriv_eisenstein_fun:
  assumes z: "z \<notin> \<Lambda>" and n: "n \<ge> 3"
  shows   "(deriv ^^ m) (eisenstein_fun n) z =
             (-1) ^ m * pochhammer (of_nat n) m * eisenstein_fun (n + m) z"
  using z n
proof (induction m arbitrary: z n)
  case 0
  thus ?case by simp
next
  case (Suc m z n)
  have ev: "eventually (\<lambda>z. z \<in> -\<Lambda>) (nhds z)"
    using Suc.prems closed_lattice by (intro eventually_nhds_in_open) auto
  have "(deriv ^^ Suc m) (eisenstein_fun n) z = deriv ((deriv ^^ m) (eisenstein_fun n)) z"
    by simp
  also have "\<dots> = deriv (\<lambda>z. (-1)^ m * pochhammer (of_nat n) m * eisenstein_fun (n + m) z) z"
    by (intro deriv_cong_ev eventually_mono[OF ev]) (use Suc in auto)
  also have "\<dots> = (-1) ^ Suc m * pochhammer (of_nat n) (Suc m) * eisenstein_fun (Suc (n + m)) z"
    using Suc.prems
    by (intro DERIV_imp_deriv)
       (auto intro!: derivative_eq_intros simp: pochhammer_Suc algebra_simps)
  finally show ?case
    by simp
qed

lemma eisenstein_fun_holomorphic' [holomorphic_intros]:
  assumes "f holomorphic_on A" "\<And>z. z \<in> A \<Longrightarrow> n < 3 \<or> f z \<notin> \<Lambda>"
  shows   "(\<lambda>z. eisenstein_fun n (f z)) holomorphic_on A"
proof (cases "n \<ge> 3")
  case True
  have "eisenstein_fun n \<circ> f holomorphic_on A"
    by (rule holomorphic_on_compose_gen assms eisenstein_fun_holomorphic)+ (use assms True in auto)
  thus ?thesis by (simp add: o_def)
qed (auto simp: eisenstein_fun_def)

lemma eisenstein_fun_analytic: "eisenstein_fun n analytic_on -\<Lambda>"
  by (simp add: analytic_on_open closed_lattice open_Compl eisenstein_fun_holomorphic)  

lemma eisenstein_fun_analytic' [analytic_intros]: 
  assumes "f analytic_on A" "\<And>z. z \<in> A \<Longrightarrow> n < 3 \<or> f z \<notin> \<Lambda>"
  shows   "(\<lambda>z. eisenstein_fun n (f z)) analytic_on A"
proof (cases "n \<ge> 3")
  case True
  have "eisenstein_fun n \<circ> f analytic_on A"
    by (rule analytic_on_compose_gen assms True eisenstein_fun_analytic)+ (use assms True in auto)
  thus ?thesis by (simp add: o_def)
qed (auto simp: eisenstein_fun_def)

lemma eisenstein_fun_continuous_on: "n \<ge> 3 \<Longrightarrow> continuous_on (-\<Lambda>) (eisenstein_fun n)"
  using holomorphic_on_imp_continuous_on eisenstein_fun_holomorphic by blast

lemma eisenstein_fun_continuous_on' [continuous_intros]:
  assumes "continuous_on A f" "\<And>z. z \<in> A \<Longrightarrow> n < 3 \<or> f z \<notin> \<Lambda>"
  shows   "continuous_on A (\<lambda>z. eisenstein_fun n (f z))"
proof (cases "n \<ge> 3")
  case True
  show ?thesis
    by (rule continuous_on_compose2[OF eisenstein_fun_continuous_on assms(1)])
       (use assms True in auto)
qed (auto simp: eisenstein_fun_def)

sublocale eisenstein_fun: complex_lattice_periodic \<omega>1 \<omega>2 "eisenstein_fun n"
proof
  have *: "eisenstein_fun n (w + z) = eisenstein_fun n w" if "z \<in> \<Lambda>" for w z
  proof (cases "n \<ge> 3 \<and> w \<notin> \<Lambda>")
    case True
    show ?thesis
    proof (rule has_sum_unique)
      show "((\<lambda>\<omega>. 1 / (w - \<omega>) ^ n) has_sum eisenstein_fun n w) \<Lambda>"
        by (rule eisenstein_fun_has_sum) (use True in auto)
    next
      have "((\<lambda>\<omega>. 1 / (w + z - \<omega>) ^ n) has_sum eisenstein_fun n (w + z)) \<Lambda>"
        by (rule eisenstein_fun_has_sum) (use True that in auto)
      also have "?this \<longleftrightarrow> ((\<lambda>\<omega>. 1 / (w - \<omega>) ^ n) has_sum eisenstein_fun n (w + z)) \<Lambda>"
        by (rule has_sum_reindex_bij_witness[of _ "(+) z" "(+) (-z)"])
           (use that in \<open>auto intro!: lattice_intros simp: algebra_simps\<close>)
      finally show "((\<lambda>\<omega>. 1 / (w - \<omega>) ^ n) has_sum eisenstein_fun n (w + z)) \<Lambda>" .
    qed
  qed (use that in \<open>auto simp: eisenstein_fun_def\<close>)
  show "eisenstein_fun n (z + \<omega>1) = eisenstein_fun n z"
       "eisenstein_fun n (z + \<omega>2) = eisenstein_fun n z" for z
    by (rule *; simp)+
qed

lemma is_pole_eisenstein_fun:
  assumes "n \<ge> 3" "z \<in> \<Lambda>"
  shows   "is_pole (eisenstein_fun n) z"
proof -
  have "eisenstein_fun_aux n \<midarrow>0\<rightarrow> eisenstein_fun_aux n 0"
    by (rule isContD, rule analytic_at_imp_isCont) (auto intro!: analytic_intros)
  moreover have "is_pole (\<lambda>w. 1 / w ^ n :: complex) 0"
    using assms is_pole_inverse_power[of n 0] by simp
  ultimately have "is_pole (\<lambda>w. eisenstein_fun_aux n w + 1 / w ^ n) 0"
    unfolding is_pole_def by (rule tendsto_add_filterlim_at_infinity)
  also have "eventually (\<lambda>w. w \<notin> \<Lambda>) (at 0)"
    using not_islimpt_lattice by (auto simp: islimpt_iff_eventually)
  hence "eventually (\<lambda>w. eisenstein_fun_aux n w + 1 / w ^ n = eisenstein_fun n w) (at 0)"
    by eventually_elim (use assms in \<open>auto simp: eisenstein_fun_altdef\<close>)
  hence "is_pole (\<lambda>w. eisenstein_fun_aux n w + 1 / w ^ n) 0 \<longleftrightarrow> is_pole (eisenstein_fun n) 0"
    by (intro is_pole_cong) auto
  also have "eisenstein_fun n = eisenstein_fun n \<circ> (\<lambda>w. w + z)"
    using assms by (auto simp: fun_eq_iff simp: rel_def uminus_in_lattice_iff eisenstein_fun.lattice_cong)
  also have "is_pole \<dots> 0 \<longleftrightarrow> is_pole (eisenstein_fun n) z"
    by (simp add: is_pole_shift_0' o_def add.commute)
  finally show ?thesis .
qed

sublocale eisenstein_fun: nicely_elliptic_function \<omega>1 \<omega>2 "eisenstein_fun n"
proof
  show "eisenstein_fun n nicely_meromorphic_on UNIV"
  proof (cases "n \<ge> 3")
    case True
    show ?thesis
    proof (rule nicely_meromorphic_onI_open)
      show "eisenstein_fun n analytic_on UNIV - \<Lambda>"
        using eisenstein_fun_analytic[of n] by (simp add: Compl_eq_Diff_UNIV)
      show "is_pole (eisenstein_fun n) z \<and> eisenstein_fun n z = 0" if "z \<in> \<Lambda>" for z
        using that by (simp add: True eisenstein_fun_def is_pole_eisenstein_fun)
      show "isolated_singularity_at (eisenstein_fun n) z" for z
      proof (rule analytic_nhd_imp_isolated_singularity[of _ "-(\<Lambda>-{z})"])
        show "open (- (\<Lambda> - {z}))"
          by (intro open_Compl closed_subset_lattice) auto
      qed (auto intro!: analytic_intros)
    qed simp
  qed (auto simp: eisenstein_fun_def [abs_def] intro!: analytic_on_imp_nicely_meromorphic_on)
qed

lemmas [elliptic_function_intros] =
  eisenstein_fun.elliptic_function_axioms eisenstein_fun.nicely_elliptic_function_axioms

end



subsection \<open>Definition and basic properties\<close>

text \<open>
  The Weierstra\ss\ \<open>\<wp>\<close> function is in a sense the most basic elliptic function, and we will see
  later on that all elliptic function can be written as a combination of \<open>\<wp>\<close> and \<open>\<wp>'\<close>.

  Its derivative, as we noted before, is equal to our Eisenstein function for $n = 3$ (up to
  a constant factor $-2$). The function \<open>\<wp>\<close> itself is somewhat more awkward to define.
\<close>

context complex_lattice begin

lemma minus_lattice_eq: "uminus ` \<Lambda> = \<Lambda>"
proof -
  have "uminus ` \<Lambda> \<subseteq> \<Lambda>"
    by (auto simp: uminus_in_lattice_iff)
  then show ?thesis
    using equation_minus_iff by blast
qed

lemma minus_latticemz_eq: "uminus ` \<Lambda>\<^sup>* = \<Lambda>\<^sup>*"
  by (simp add: lattice0_def inj_on_def image_set_diff minus_lattice_eq)

lemma bij_minus_latticemz: "bij_betw uminus \<Lambda>\<^sup>* \<Lambda>\<^sup>*"
  by (simp add: bij_betw_def inj_on_def minus_latticemz_eq)


definition weierstrass_fun_deriv ("\<wp>''") where
  "weierstrass_fun_deriv z = -2 * eisenstein_fun 3 z"

sublocale weierstrass_fun_deriv: elliptic_function \<omega>1 \<omega>2 weierstrass_fun_deriv
  unfolding weierstrass_fun_deriv_def by (intro elliptic_function_intros)

sublocale weierstrass_fun_deriv: nicely_elliptic_function \<omega>1 \<omega>2 weierstrass_fun_deriv
proof
  show "\<wp>' nicely_meromorphic_on UNIV"
    using eisenstein_fun.nicely_meromorphic unfolding weierstrass_fun_deriv_def
    by (intro nicely_meromorphic_on_uminus nicely_meromorphic_on_cmult_left)
qed

lemmas [elliptic_function_intros] =
  weierstrass_fun_deriv.elliptic_function_axioms weierstrass_fun_deriv.nicely_elliptic_function_axioms

lemma weierstrass_fun_deriv_minus [simp]: "\<wp>' (-z) = -\<wp>' z"
  by (simp add: weierstrass_fun_deriv_def eisenstein_fun_odd_minus)

lemma weierstrass_fun_deriv_has_field_derivative:
  assumes "z \<notin> \<Lambda>"
  shows   "(\<wp>' has_field_derivative 6 * eisenstein_fun 4 z) (at z)"
  unfolding weierstrass_fun_deriv_def
  using assms by (auto intro!: derivative_eq_intros)

lemma weierstrass_fun_deriv_holomorphic: "\<wp>' holomorphic_on -\<Lambda>"
  unfolding weierstrass_fun_deriv_def by (auto intro!: holomorphic_intros)

lemma weierstrass_fun_deriv_holomorphic' [holomorphic_intros]:
  assumes "f holomorphic_on A" "\<And>z. z \<in> A \<Longrightarrow> f z \<notin> \<Lambda>"
  shows   "(\<lambda>z. \<wp>' (f z)) holomorphic_on A"
  using assms unfolding weierstrass_fun_deriv_def by (auto intro!: holomorphic_intros)

lemma weierstrass_fun_deriv_analytic: "\<wp>' analytic_on -\<Lambda>"
  unfolding weierstrass_fun_deriv_def by (auto intro!: analytic_intros)

lemma weierstrass_fun_deriv_analytic' [analytic_intros]: 
  assumes "f analytic_on A" "\<And>z. z \<in> A \<Longrightarrow> f z \<notin> \<Lambda>"
  shows   "(\<lambda>z. \<wp>' (f z)) analytic_on A"
  using assms unfolding weierstrass_fun_deriv_def by (auto intro!: analytic_intros)

lemma weierstrass_fun_deriv_continuous_on: "continuous_on (-\<Lambda>) \<wp>'"
  unfolding weierstrass_fun_deriv_def by (auto intro!: continuous_intros)

lemma weierstrass_fun_deriv_continuous_on' [continuous_intros]:
  assumes "continuous_on A f" "\<And>z. z \<in> A \<Longrightarrow> f z \<notin> \<Lambda>"
  shows   "continuous_on A (\<lambda>z. \<wp>' (f z))"
  using assms unfolding weierstrass_fun_deriv_def by (auto intro!: continuous_intros)

lemma tendsto_weierstrass_fun_deriv [tendsto_intros]:
  assumes "(f \<longlongrightarrow> c) F" "c \<notin> \<Lambda>"
  shows   "((\<lambda>z. \<wp>' (f z)) \<longlongrightarrow> \<wp>' c) F"
proof (rule continuous_on_tendsto_compose[OF _ assms(1)])
  show "continuous_on (-\<Lambda>) \<wp>'"
    by (intro holomorphic_on_imp_continuous_on holomorphic_intros) auto
  show "eventually (\<lambda>z. f z \<in> -\<Lambda>) F"
    by (rule eventually_compose_filterlim[OF _ assms(1)], rule eventually_nhds_in_open)
       (use assms(2) in \<open>auto intro: closed_lattice\<close>)
qed (use assms(2) in auto)


text \<open>
  The following is the Weierstra\ss\ function minus its pole at the origin. By convention, it
  returns 0 at all its remaining poles.
\<close>
definition weierstrass_fun_aux :: "complex \<Rightarrow> complex" where
  "weierstrass_fun_aux z = (if z \<in> \<Lambda>\<^sup>* then 0 else (\<Sum>\<^sub>\<infinity> \<omega> \<in> \<Lambda>\<^sup>*. 1 / (z - \<omega>)\<^sup>2 - 1 / \<omega>\<^sup>2))"


(* Definition p.10 *)
text \<open>
  This is now the Weierstra\ss\ function. Again, it returns 0 at all its poles.
\<close>
definition weierstrass_fun :: "complex \<Rightarrow> complex" ("\<wp>")
  where "\<wp> z = (if z \<in> \<Lambda> then 0 else 1 / z\<^sup>2 + weierstrass_fun_aux z)"

lemma weierstrass_fun_aux_0 [simp]: "weierstrass_fun_aux 0 = 0"
  by (simp add: weierstrass_fun_aux_def)

lemma weierstrass_fun_at_pole: "\<omega> \<in> \<Lambda> \<Longrightarrow> \<wp> \<omega> = 0"
  by (simp add: weierstrass_fun_def)


lemma
  fixes R :: real
  assumes "R > 0"
  shows weierstrass_fun_aux_converges_absolutely_uniformly_in_disk:
          "uniform_limit (cball 0 R)
                         (\<lambda>X z. \<Sum>\<omega>\<in>X. norm (1 / (z - \<omega>)\<^sup>2 - 1 / \<omega>\<^sup>2))
                         (\<lambda>z. \<Sum>\<^sub>\<infinity>\<omega>\<in>\<Lambda>-cball 0 R. norm (1 / (z - \<omega>)\<^sup>2 - 1 / \<omega>\<^sup>2))
                         (finite_subsets_at_top (\<Lambda> - cball 0 R))" (is ?th1)
  and   weierstrass_fun_aux_converges_uniformly_in_disk:
          "uniform_limit (cball 0 R)
                         (\<lambda>X z. \<Sum>\<omega>\<in>X. 1 / (z - \<omega>)\<^sup>2 - 1 / \<omega>\<^sup>2)
                         (\<lambda>z. \<Sum>\<^sub>\<infinity>\<omega>\<in>\<Lambda>-cball 0 R. 1 / (z - \<omega>)\<^sup>2 - 1 / \<omega>\<^sup>2)
                         (finite_subsets_at_top (\<Lambda> - cball 0 R))" (is ?th2)
proof -
  obtain M where M:
    "M > 0" "\<And>\<omega> z. \<lbrakk>\<omega> \<in> \<Lambda>; norm \<omega> > R; norm z \<le> R\<rbrakk> \<Longrightarrow> norm (z - \<omega>) powr -2 \<le> M * norm \<omega> powr -2"
    using weierstrass_summand_bound[of 2 R] assms by auto

  have 1: "(\<lambda>\<omega>. 3 * M * R * norm \<omega> powr -3) summable_on (\<Lambda> - cball 0 R)"
  proof -
    have "(\<lambda>\<omega>. 1 / norm \<omega> powr 3) summable_on \<Lambda>\<^sup>*"
      using assms by (subst converges_absolutely_iff) auto
    hence "(\<lambda>\<omega>. 3 * M * R * norm \<omega> powr -3) summable_on \<Lambda>\<^sup>*"
      by (intro summable_on_cmult_right) (auto simp: powr_minus field_simps)
    thus "(\<lambda>\<omega>. 3 * M * R * norm \<omega> powr -3) summable_on (\<Lambda> - cball 0 R)"
      by (rule summable_on_subset) (use assms in \<open>auto simp: lattice0_def\<close>)
  qed

  have 2: "norm (1 / (z - \<omega>)\<^sup>2 - 1 / \<omega>\<^sup>2) \<le> 3 * M * R * norm \<omega> powr -3"
    if "\<omega> \<in> \<Lambda> - cball 0 R" "z \<in> cball 0 R" for \<omega> z
  proof -
    from that have nz: "\<omega> \<noteq> 0" "\<omega> \<noteq> z"
      using \<open>R > 0\<close> by auto
    hence "1 / (z - \<omega>)\<^sup>2 - 1 / \<omega>\<^sup>2 = z * (2 * \<omega> - z) / (\<omega>\<^sup>2 * (z - \<omega>)\<^sup>2)"
      using that by (auto simp: field_simps) (auto simp: power2_eq_square algebra_simps)
    also have "norm \<dots> = norm z * norm (2 * \<omega> - z) / norm \<omega> ^ 2 * norm (z - \<omega>) powr - 2"
      by (simp add: norm_divide norm_mult norm_power powr_minus divide_simps)
    also have "\<dots> \<le> R * (2 * norm \<omega> + norm z) / norm \<omega> ^ 2 * (M * norm \<omega> powr -2)"
      using assms that
      by (intro mult_mono frac_le mult_nonneg_nonneg M order.trans[OF norm_triangle_ineq4]) auto
    also have "\<dots> = M * R * (2 + norm z / norm \<omega>) / norm \<omega> ^ 3"
      using nz by (simp add: field_simps powr_minus power2_eq_square power3_eq_cube)
    also have "\<dots> \<le> M * R * 3 / norm \<omega> ^ 3"
      using nz assms M(1) that by (intro mult_left_mono divide_right_mono) auto
    finally show ?thesis
      by (simp add: field_simps powr_minus)
  qed

  show ?th1 ?th2 unfolding weierstrass_fun_aux_def
     by (rule Weierstrass_m_test_general[OF _ 1]; use 2 in simp)+
qed

lemma weierstrass_fun_has_field_derivative_aux:
  fixes R :: real
  defines "F \<equiv> (\<lambda>z. \<Sum>\<^sub>\<infinity>\<omega>\<in>\<Lambda>-cball 0 R. 1 / (z - \<omega>)\<^sup>2 - 1 / \<omega>\<^sup>2)"
  defines "F' \<equiv> (\<lambda>z. \<Sum>\<^sub>\<infinity>\<omega>\<in>\<Lambda>-cball 0 R. 1 / (z - \<omega>) ^ 3)"
  assumes "R > 0" "w \<in> ball 0 R"
  shows   "(F has_field_derivative -2 * F' w) (at w)"
proof -
  have 1: "\<forall>\<^sub>F n in finite_subsets_at_top (\<Lambda> - cball 0 R).
            continuous_on (cball 0 R) (\<lambda>z. \<Sum>\<omega>\<in>n. 1 / (z - \<omega>)\<^sup>2 - 1 / \<omega>\<^sup>2) \<and>
            (\<forall>z\<in>ball 0 R. ((\<lambda>z. \<Sum>\<omega>\<in>n. 1 / (z - \<omega>)\<^sup>2 - 1 / \<omega>\<^sup>2) has_field_derivative (\<Sum>\<omega>\<in>n. -2 / (z - \<omega>)^3)) (at z))"
    (* TODO FIXME: ugly *)
    apply (intro eventually_finite_subsets_at_top_weakI conjI continuous_intros derivative_intros ballI)
     apply force
    apply (rule derivative_eq_intros refl | force)+
    apply (simp add: divide_simps, simp add: algebra_simps power4_eq_xxxx power3_eq_cube)
    done

  have "uniform_limit (cball 0 R)
                      (\<lambda>X z. \<Sum>\<omega>\<in>X. 1 / (z - \<omega>)\<^sup>2 - 1 / \<omega>\<^sup>2)
                      (\<lambda>z. \<Sum>\<^sub>\<infinity>\<omega>\<in>\<Lambda>-cball 0 R. 1 / (z - \<omega>)\<^sup>2 - 1 / \<omega>\<^sup>2)
                      (finite_subsets_at_top (\<Lambda> - cball 0 R))"
    using assms by (intro weierstrass_fun_aux_converges_uniformly_in_disk) auto
  also have "?this \<longleftrightarrow> uniform_limit (cball 0 R) (\<lambda>X z. \<Sum>\<omega>\<in>X. 1 / (z - \<omega>)\<^sup>2 - 1 / \<omega>\<^sup>2) F
                         (finite_subsets_at_top (\<Lambda> - cball 0 R))"
    using assms unfolding F_def
    by (intro uniform_limit_cong eventually_finite_subsets_at_top_weakI)
       (auto simp: powr_minus powr_nat field_simps intro!: sum.cong infsum_cong)
  finally have 2: \<dots> .

  have 3: "finite_subsets_at_top (\<Lambda> - cball 0 R) \<noteq> bot"
    by simp

  obtain g where g: "continuous_on (cball 0 R) F"
                    "\<And>w. w \<in> ball 0 R \<Longrightarrow> (F has_field_derivative g w) (at w) \<and>
                        ((\<lambda>\<omega>. -2 / (w - \<omega>) ^ 3) has_sum g w) (\<Lambda> - cball 0 R)"
    unfolding has_sum_def using has_complex_derivative_uniform_limit[OF 1 2 3 \<open>R > 0\<close>] by auto

  have "((\<lambda>\<omega>. (-2) * (1 / (w - \<omega>) ^ 3)) has_sum (-2) * F' w) (\<Lambda> - cball 0 R)"
    unfolding F'_def using assms
    by (intro has_sum_cmult_right has_sum_infsum weierstrass_aux_converges_in_disk') auto
  moreover have "((\<lambda>\<omega>.  -2 * (1 / (w - \<omega>) ^ 3)) has_sum g w) (\<Lambda> - cball 0 R)"
    using g(2)[of w] assms by simp
  ultimately have "g w = -2 * F' w"
    by (metis infsumI)
  thus "(F has_field_derivative -2 * F' w) (at w)"
    using g(2)[of w] assms by simp
qed

lemma norm_summable_weierstrass_fun_aux: "(\<lambda>\<omega>. norm (1 / (z - \<omega>)\<^sup>2 - 1 / \<omega>\<^sup>2)) summable_on \<Lambda>"
proof -
  define R where "R = norm z + 1"
  have "(\<lambda>\<omega>. norm (1 / (z - \<omega>)\<^sup>2 - 1 / \<omega>\<^sup>2)) summable_on (\<Lambda> - cball 0 R)"
    unfolding summable_iff_has_sum_infsum has_sum_def
    by (rule tendsto_uniform_limitI[OF weierstrass_fun_aux_converges_absolutely_uniformly_in_disk])
       (auto simp: R_def add_nonneg_pos)
  hence "(\<lambda>\<omega>. norm (1 / (z - \<omega>)\<^sup>2 - 1 / \<omega>\<^sup>2)) summable_on ((\<Lambda> - cball 0 R) \<union> (\<Lambda> \<inter> cball 0 R))"
    by (intro summable_on_union[OF _ summable_on_finite]) (auto simp: bounded_lattice_finite)
  also have "\<dots> = \<Lambda>"
    by blast
  finally show ?thesis .
qed

lemma summable_weierstrass_fun_aux: "(\<lambda>\<omega>. 1 / (z - \<omega>)\<^sup>2 - 1 / \<omega>\<^sup>2) summable_on \<Lambda>"
  using norm_summable_weierstrass_fun_aux by (rule abs_summable_summable)

lemma weierstrass_summable: "(\<lambda>\<omega>. 1 / (z - \<omega>)\<^sup>2 - 1 / \<omega>\<^sup>2) summable_on \<Lambda>\<^sup>*"
  by (rule summable_on_subset[OF summable_weierstrass_fun_aux]) (auto simp: lattice0_def)

lemma weierstrass_fun_aux_has_sum:
  "z \<notin> \<Lambda>\<^sup>* \<Longrightarrow> ((\<lambda>\<omega>. 1 / (z - \<omega>)\<^sup>2 - 1 / \<omega>\<^sup>2) has_sum weierstrass_fun_aux z) \<Lambda>\<^sup>*"
  unfolding weierstrass_fun_aux_def by (simp add: weierstrass_summable)

lemma weierstrass_fun_aux_has_field_derivative:
  defines "F \<equiv> weierstrass_fun_aux"
  defines "F' \<equiv> (\<lambda>z. \<Sum>\<^sub>\<infinity>\<omega>\<in>\<Lambda>\<^sup>*. 1 / (z - \<omega>) ^ 3)"
  assumes z: "z \<notin> \<Lambda>\<^sup>*"
  shows   "(F has_field_derivative -2 * eisenstein_fun_aux 3 z) (at z)"
proof -
  define R where "R = norm z + 1"
  have R: "R > 0" "norm z < R"
    by (auto simp: R_def add_nonneg_pos)
  have "finite (\<Lambda> \<inter> cball 0 R)"
    by (simp add: bounded_lattice_finite)
  moreover have "\<Lambda>\<^sup>* \<inter> cball 0 R \<subseteq> \<Lambda> \<inter> cball 0 R"
    unfolding lattice0_def by blast
  ultimately have fin: "finite (\<Lambda>\<^sup>* \<inter> cball 0 R)"
    using finite_subset by blast

  define F1 where "F1 = (\<lambda>z. \<Sum>\<^sub>\<infinity>\<omega>\<in>\<Lambda>-cball 0 R. 1 / (z - \<omega>)\<^sup>2 - 1 / \<omega>\<^sup>2)"
  define F'1 where "F'1 = (\<lambda>z. \<Sum>\<^sub>\<infinity>\<omega>\<in>\<Lambda>-cball 0 R. 1 / (z - \<omega>) ^ 3)"
  define F2 where "F2 = (\<lambda>z. \<Sum>\<omega>\<in>\<Lambda>\<^sup>*\<inter>cball 0 R. 1 / (z - \<omega>)\<^sup>2 - 1 / \<omega>\<^sup>2)"
  define F'2 where "F'2 = (\<lambda>z. \<Sum>\<omega>\<in>\<Lambda>\<^sup>*\<inter>cball 0 R. 1 / (z - \<omega>) ^ 3)"

  have "(F1 has_field_derivative -2 * F'1 z) (at z)"
    unfolding F1_def F'1_def
    by (rule weierstrass_fun_has_field_derivative_aux) (auto simp: R_def add_nonneg_pos)
  moreover have "(F2 has_field_derivative -2 * F'2 z) (at z)"
    unfolding F2_def F'2_def sum_distrib_left lattice0_def
    by (rule derivative_eq_intros refl sum.cong | use R z in \<open>force simp: lattice0_def\<close>)+
       (simp add: divide_simps power3_eq_cube power4_eq_xxxx)
  ultimately have "((\<lambda>z. F1 z + F2 z) has_field_derivative (-2 * F'1 z) + (-2 * F'2 z)) (at z)"
    by (intro derivative_intros)
  also have "?this \<longleftrightarrow> (F has_field_derivative (-2 * F'1 z) + (-2 * F'2 z)) (at z)"
  proof (intro has_field_derivative_cong_ev refl)
    have "eventually (\<lambda>z'. z' \<in> -\<Lambda>\<^sup>*) (nhds z)"
      using z by (intro eventually_nhds_in_open) (auto simp: closed_lattice0)
    thus "\<forall>\<^sub>F x in nhds z. x \<in> UNIV \<longrightarrow> F1 x + F2 x = F x"
    proof eventually_elim
      case (elim z)
      have "((\<lambda>\<omega>. 1 / (z - \<omega>)^2 - 1 / \<omega>^2) has_sum (F1 z + F2 z)) ((\<Lambda> - cball 0 R) \<union> (\<Lambda>\<^sup>* \<inter> cball 0 R))"
        unfolding F1_def F2_def using R fin
        by (intro has_sum_Un_disjoint[OF has_sum_infsum has_sum_finite]
                  summable_on_subset_banach[OF summable_weierstrass_fun_aux]) auto
      also have "(\<Lambda> - cball 0 R) \<union> (\<Lambda>\<^sup>* \<inter> cball 0 R) = \<Lambda>\<^sup>*"
        using R unfolding lattice0_def by auto
      finally show ?case using elim
        unfolding F1_def F2_def F_def weierstrass_fun_aux_def by (simp add: infsumI)
    qed
  qed auto
  also have "(-2 * F'1 z) + (-2 * F'2 z) = -2 * (F'1 z + F'2 z)"
    by (simp add: algebra_simps)
  also have "F'1 z + F'2 z = F' z"
  proof -
    have "((\<lambda>\<omega>. 1 / (z - \<omega>)^3) has_sum (F'1 z + F'2 z)) ((\<Lambda> - cball 0 R) \<union> (\<Lambda>\<^sup>* \<inter> cball 0 R))"
      unfolding F'1_def F'2_def using R fin
      by (intro has_sum_Un_disjoint [OF has_sum_infsum has_sum_finite] weierstrass_aux_converges') auto
    also have "(\<Lambda> - cball 0 R) \<union> (\<Lambda>\<^sup>* \<inter> cball 0 R) = \<Lambda>\<^sup>*"
      using R unfolding lattice0_def by auto
    finally show "F'1 z + F'2 z = F' z"
      unfolding F'1_def F'2_def F'_def by (simp add: infsumI)
  qed
  finally show ?thesis
    using assms by (simp add: eisenstein_fun_aux_def)
qed

lemmas weierstrass_fun_aux_has_field_derivative' [derivative_intros] =
  weierstrass_fun_aux_has_field_derivative [THEN DERIV_chain2]

lemma weierstrass_fun_aux_holomorphic: "weierstrass_fun_aux holomorphic_on -\<Lambda>\<^sup>*"
  by (subst holomorphic_on_open)
     (auto intro!: weierstrass_fun_aux_has_field_derivative simp: closed_lattice0)

lemma weierstrass_fun_aux_holomorphic' [holomorphic_intros]:
  assumes "f holomorphic_on A" "\<And>z. z \<in> A \<Longrightarrow> f z \<notin> \<Lambda>\<^sup>*"
  shows   "(\<lambda>z. weierstrass_fun_aux (f z)) holomorphic_on A"
proof -
  have "weierstrass_fun_aux \<circ> f holomorphic_on A"
    by (rule holomorphic_on_compose_gen assms weierstrass_fun_aux_holomorphic)+ (use assms in auto)
  thus ?thesis by (simp add: o_def)
qed

lemma weierstrass_fun_aux_continuous_on: "continuous_on (-\<Lambda>\<^sup>*) weierstrass_fun_aux"
  using holomorphic_on_imp_continuous_on weierstrass_fun_aux_holomorphic by blast

lemma weierstrass_fun_aux_continuous_on' [continuous_intros]:
  assumes "continuous_on A f" "\<And>z. z \<in> A \<Longrightarrow> f z \<notin> \<Lambda>\<^sup>*"
  shows   "continuous_on A (\<lambda>z. weierstrass_fun_aux (f z))"
  by (rule continuous_on_compose2[OF weierstrass_fun_aux_continuous_on assms(1)]) (use assms in auto)

lemma weierstrass_fun_aux_analytic: "weierstrass_fun_aux analytic_on -\<Lambda>\<^sup>*"
  by (simp add: analytic_on_open closed_lattice0 open_Compl weierstrass_fun_aux_holomorphic)  

lemma weierstrass_fun_aux_analytic' [analytic_intros]: 
  assumes "f analytic_on A" "\<And>z. z \<in> A \<Longrightarrow> f z \<notin> \<Lambda>\<^sup>*"
  shows   "(\<lambda>z. weierstrass_fun_aux (f z)) analytic_on A"
proof -
  have "weierstrass_fun_aux \<circ> f analytic_on A"
    by (rule analytic_on_compose_gen assms weierstrass_fun_aux_analytic)+ (use assms in auto)
  thus ?thesis by (simp add: o_def)
qed

lemma deriv_weierstrass_fun_aux:
  "z \<notin> \<Lambda>\<^sup>* \<Longrightarrow> deriv weierstrass_fun_aux z = -2 * eisenstein_fun_aux 3 z"
  by (rule DERIV_imp_deriv derivative_eq_intros refl | assumption)+ simp


lemma weierstrass_fun_has_field_derivative:
  fixes R :: real
  assumes z: "z \<notin> \<Lambda>"
  shows   "(\<wp> has_field_derivative \<wp>' z) (at z)"
proof -
  note [derivative_intros] = weierstrass_fun_aux_has_field_derivative
  from z have [simp]: "z \<noteq> 0" "z \<notin> \<Lambda>\<^sup>*"
    by (auto simp: lattice0_def)
  define D where "D = -2 / z ^ 3 - 2 * eisenstein_fun_aux 3 z"

  have "((\<lambda>z. 1 / z\<^sup>2 + weierstrass_fun_aux z) has_field_derivative D) (at z)" unfolding D_def
    by (rule derivative_eq_intros refl | simp)+ (simp add: divide_simps power3_eq_cube power4_eq_xxxx)
  also have "?this \<longleftrightarrow> (weierstrass_fun has_field_derivative D) (at z)"
  proof (intro has_field_derivative_cong_ev refl)
    have "eventually (\<lambda>z. z \<in> -\<Lambda>) (nhds z)"
      using closed_lattice z by (intro eventually_nhds_in_open) auto
    thus "eventually (\<lambda>z. z \<in> UNIV \<longrightarrow> 1 / z ^ 2 + weierstrass_fun_aux z = \<wp> z) (nhds z)"
      by eventually_elim (simp add: weierstrass_fun_def)
  qed auto
  also have "D = -2 * eisenstein_fun 3 z"
    using z by (simp add: eisenstein_fun_conv_eisenstein_fun_aux D_def)
  finally show ?thesis by (simp add: weierstrass_fun_deriv_def)
qed

lemmas weierstrass_fun_has_field_derivative' [derivative_intros] =
  weierstrass_fun_has_field_derivative [THEN DERIV_chain2]

lemma weierstrass_fun_holomorphic: "\<wp> holomorphic_on -\<Lambda>"
  by (subst holomorphic_on_open)
     (auto intro!: weierstrass_fun_has_field_derivative simp: closed_lattice)

lemma weierstrass_fun_holomorphic' [holomorphic_intros]:
  assumes "f holomorphic_on A" "\<And>z. z \<in> A \<Longrightarrow> f z \<notin> \<Lambda>"
  shows   "(\<lambda>z. weierstrass_fun (f z)) holomorphic_on A"
proof -
  have "weierstrass_fun \<circ> f holomorphic_on A"
    by (rule holomorphic_on_compose_gen assms weierstrass_fun_holomorphic)+ (use assms in auto)
  thus ?thesis by (simp add: o_def)
qed

lemma weierstrass_fun_analytic: "\<wp> analytic_on -\<Lambda>"
  by (simp add: analytic_on_open closed_lattice open_Compl weierstrass_fun_holomorphic)  

lemma weierstrass_fun_analytic' [analytic_intros]: 
  assumes "f analytic_on A" "\<And>z. z \<in> A \<Longrightarrow> f z \<notin> \<Lambda>"
  shows   "(\<lambda>z. \<wp> (f z)) analytic_on A"
proof -
  have "\<wp> \<circ> f analytic_on A"
    by (rule analytic_on_compose_gen assms weierstrass_fun_analytic)+ (use assms in auto)
  thus ?thesis by (simp add: o_def)
qed

lemma weierstrass_fun_continuous_on: "continuous_on (-\<Lambda>) weierstrass_fun"
  using holomorphic_on_imp_continuous_on weierstrass_fun_holomorphic by blast

lemma weierstrass_fun_continuous_on' [continuous_intros]:
  assumes "continuous_on A f" "\<And>z. z \<in> A \<Longrightarrow> f z \<notin> \<Lambda>"
  shows   "continuous_on A (\<lambda>z. \<wp> (f z))"
  by (rule continuous_on_compose2[OF weierstrass_fun_continuous_on assms(1)]) (use assms in auto)

lemma tendsto_weierstrass_fun [tendsto_intros]:
  assumes "(f \<longlongrightarrow> c) F" "c \<notin> \<Lambda>"
  shows   "((\<lambda>z. \<wp> (f z)) \<longlongrightarrow> \<wp> c) F"
proof (rule continuous_on_tendsto_compose[OF _ assms(1)])
  show "continuous_on (-\<Lambda>) \<wp>"
    by (intro holomorphic_on_imp_continuous_on holomorphic_intros) auto
  show "eventually (\<lambda>z. f z \<in> -\<Lambda>) F"
    by (rule eventually_compose_filterlim[OF _ assms(1)], rule eventually_nhds_in_open)
       (use assms(2) in \<open>auto intro: closed_lattice\<close>)
qed (use assms(2) in auto)

lemma deriv_weierstrass_fun:
  assumes "z \<notin> \<Lambda>"
  shows   "deriv \<wp> z = \<wp>' z"
  by (rule DERIV_imp_deriv weierstrass_fun_has_field_derivative refl assms)+

text \<open>
  The following identity is to be read with care: for \<open>\<omega> = 0\<close> we get a division by zero,
  so the term \<open>1 / \<omega>\<^sup>2\<close> simply gets dropped.
\<close>
lemma weierstrass_fun_eq: 
  assumes "z \<notin> \<Lambda>"
  shows   "\<wp> z = (\<Sum>\<^sub>\<infinity> \<omega> \<in> \<Lambda>. (1 / (z - \<omega>) ^ 2) - 1 / \<omega> ^ 2)"
proof -
  have *: "((\<lambda>\<omega>. 1 / (z - \<omega>)\<^sup>2 - 1 / \<omega>\<^sup>2) has_sum \<wp> z - 1 / z^2) \<Lambda>\<^sup>*"
    using has_sum_infsum [OF weierstrass_summable, of z] assms
    by (simp add: weierstrass_fun_def weierstrass_fun_aux_def lattice0_def)
  have "((\<lambda>\<omega>. 1 / (z - \<omega>)\<^sup>2 - 1 / \<omega>\<^sup>2) has_sum ((1 / (z - 0)^2 - 1 / 0\<^sup>2) + (\<wp> z - 1 / z^2))) \<Lambda>"
    unfolding lattice_lattice0 by (rule has_sum_insert) (use * in auto)
  then show ?thesis
    by (simp add: infsumI)
qed


subsection \<open>Ellipticity and poles\<close>

(* Theorem 1.10 (4) *)
text \<open>
  It can easily be seen from its definition that \<open>\<wp>\<close> is an even elliptic function with a
  double pole at each lattice point and no other poles. Thus it has order 2.

  Its derivative is consequently an odd elliptic function with a triple pole at each lattice point,
  no other poles, and order 3.

  The results in this section correspond to Apostol's Theorems 1.9 and 1.10.
\<close>
lemma weierstrass_fun_minus: "\<wp> (-z) = \<wp> z"  
proof (cases "z \<in> \<Lambda>")
  case False
  have "(\<Sum>\<^sub>\<infinity> \<omega> \<in> \<Lambda>\<^sup>*. 1 / (- z - \<omega>)\<^sup>2 - 1 / \<omega>\<^sup>2) = (\<Sum>\<^sub>\<infinity> \<omega> \<in> \<Lambda>\<^sup>*. (1 / (z - \<omega>)\<^sup>2 - 1 / \<omega>\<^sup>2))"
    by (rule infsum_reindex_bij_witness[of _ uminus uminus])
       (auto intro!: lattice_intros simp: uminus_in_lattice0_iff power2_commute add_ac)
  thus ?thesis using False
    by (auto simp: weierstrass_fun_def weierstrass_fun_aux_def uminus_in_lattice0_iff lattice_lattice0)
qed (auto simp: weierstrass_fun_at_pole uminus_in_lattice_iff)

sublocale weierstrass_fun: complex_lattice_periodic \<omega>1 \<omega>2 \<wp>
proof
  have *: "\<wp> (z + \<omega>) = \<wp> z" if \<omega>: "\<omega> \<in> {\<omega>1, \<omega>2}" for \<omega> z
  proof (cases "z \<in> \<Lambda>")
    case z: True
    thus ?thesis
      by (subst (1 2) weierstrass_fun_at_pole) (use \<omega> in \<open>auto intro!: lattice_intros\<close>)
  next
    case z: False
    from \<omega> have \<omega>' [simp, intro]: "\<omega> \<in> \<Lambda>"
      by auto
    define f where "f = (\<lambda>z. \<wp> (z + \<omega>) - \<wp> z)"
    with \<open>z \<notin> \<Lambda>\<close> have "(f has_field_derivative 0) (at z)" if "z \<notin> \<Lambda>" for z
    proof -
      from that and \<omega> have "(f has_field_derivative (\<wp>' (z + \<omega>) - \<wp>' z)) (at z)"
        unfolding f_def by (auto intro!: derivative_eq_intros)
      also have "\<wp>' (z + \<omega>) = \<wp>' z"
        by (rule weierstrass_fun_deriv.lattice_cong) (auto simp: rel_def)
      finally show ?thesis
        by simp
    qed
    hence deriv: "\<forall>x\<in>UNIV - \<Lambda> - {}. (f has_field_derivative 0) (at x)"
      by blast
    have cont: "continuous_on (UNIV - \<Lambda>) f"
      by (auto simp: f_def intro!: continuous_intros)

    have *: "connected (UNIV - \<Lambda>)" "open (UNIV - \<Lambda>)" "finite ({} :: complex set)"
      by (auto simp: closed_lattice countable_lattice intro!: connected_open_diff_countable)

    obtain c where c: "\<And>z. z \<in> UNIV - \<Lambda> \<Longrightarrow> f z = c"
      using DERIV_zero_connected_constant[OF * cont deriv] by blast

    have "\<omega> / 2 \<notin> \<Lambda>"
      using of_\<omega>12_coords_in_lattice_iff \<omega> by (auto simp: in_lattice_conv_\<omega>12_coords)
    hence "f (-\<omega> / 2) = c"
      by (intro c) (auto simp: uminus_in_lattice_iff)
    also have "f (-\<omega> / 2) = 0"
      by (simp add: f_def weierstrass_fun_minus)
    finally have "f z = 0"
      using c that z by auto
    thus ?thesis
      by (simp add: f_def)
  qed

  show "\<wp> (z + \<omega>1) = \<wp> z" "\<wp> (z + \<omega>2) = \<wp> z" for z
    by (rule *; simp)+
qed

(* Theorem 1.10 (3) *)
lemma zorder_weierstrass_fun_pole:
  assumes "\<omega> \<in> \<Lambda>"
  shows   "zorder \<wp> \<omega> = -2"
proof -
  define R where "R = Inf_para"
  have R: "R > 0"
    using Inf_para_pos by (auto simp: R_def)
  have R': "ball 0 R \<inter> \<Lambda>\<^sup>* = {}"
    using Inf_para_le_norm by (force simp: R_def)

  have "zorder weierstrass_fun \<omega> = zorder (\<lambda>z. weierstrass_fun (z + \<omega>)) 0"
    by (rule zorder_shift)
  also have "(\<lambda>z. weierstrass_fun (z + \<omega>)) = weierstrass_fun"
    by (intro ext weierstrass_fun.lattice_cong) (auto simp: rel_def assms)
  also have "zorder weierstrass_fun 0 = -2"
  proof (rule zorder_eqI)
    show "open (ball 0 R :: complex set)" "(0 :: complex) \<in> ball 0 R"
      using R by auto
    show "(\<lambda>z. 1 + weierstrass_fun_aux z * z ^ 2) holomorphic_on ball 0 R" using R'
      by (intro holomorphic_intros holomorphic_on_subset[OF weierstrass_fun_aux_holomorphic]) auto
    show "\<And>w. \<lbrakk>w \<in> ball 0 R; w \<noteq> 0\<rbrakk>
         \<Longrightarrow> \<wp> w =
             (1 + weierstrass_fun_aux w * w\<^sup>2) *
             (w - 0) powi - 2"
      using R' 
      by (auto simp: weierstrass_fun_def field_simps power_numeral_reduce powi_minus_numeral_reduce
                              lattice0_def)
  qed auto
  finally show ?thesis .
qed

lemma is_pole_weierstrass_fun:
  assumes \<omega>:  "\<omega> \<in> \<Lambda>"
  shows   "is_pole \<wp> \<omega>"
proof -
  have "is_pole \<wp> 0"
  proof -
    have "eventually (\<lambda>z. z \<in> -\<Lambda>\<^sup>*) (nhds 0)"
      using closed_lattice0  by (intro eventually_nhds_in_open) auto
    hence ev: "eventually (\<lambda>z. z \<notin> \<Lambda>) (at 0)"
      unfolding eventually_at_filter by eventually_elim (auto simp: lattice0_def)
    have "\<Lambda> - \<Lambda>\<^sup>* = {0}" "\<Lambda>\<^sup>* \<subseteq> \<Lambda>"
      by (auto simp: insert_Diff_if lattice_lattice0)
    hence "weierstrass_fun_aux holomorphic_on -\<Lambda>\<^sup>*"
      by (auto intro!: holomorphic_intros)
    hence "continuous_on (-\<Lambda>\<^sup>*) weierstrass_fun_aux"
      using holomorphic_on_imp_continuous_on by blast
    moreover have "0 \<in> -\<Lambda>\<^sup>*"
      by (auto simp: lattice0_def)
    ultimately have "(weierstrass_fun_aux \<longlongrightarrow> weierstrass_fun_aux 0) (at 0)"
      using closed_lattice0 by (metis at_within_open closed_open continuous_on_def)
    moreover have "filterlim (\<lambda>z::complex. 1 / z ^ 2) at_infinity (at 0)"
      using is_pole_inverse_power[of 2 0] by (simp add: is_pole_def)
    ultimately have "filterlim (\<lambda>z. weierstrass_fun_aux z + 1 / z ^ 2) at_infinity (at 0)"
      by (rule tendsto_add_filterlim_at_infinity)
    also have "?this \<longleftrightarrow> filterlim weierstrass_fun at_infinity (at 0)"
      by (intro filterlim_cong refl eventually_mono[OF ev]) (auto simp: weierstrass_fun_def)
    finally show ?thesis
      by (simp add: is_pole_def)
  qed
  also have "\<wp> = \<wp> \<circ> (\<lambda>z. z + \<omega>)"
    by (auto simp: fun_eq_iff rel_def assms uminus_in_lattice_iff 
             intro!: weierstrass_fun.lattice_cong)
  also have "is_pole \<dots> 0 \<longleftrightarrow> is_pole \<wp> \<omega>"
    by (simp add: o_def is_pole_shift_0' add_ac)
  finally show "is_pole \<wp> \<omega>" .
qed

sublocale weierstrass_fun: nicely_elliptic_function \<omega>1 \<omega>2 \<wp>
proof
  show "\<wp> nicely_meromorphic_on UNIV"
  proof (rule nicely_meromorphic_onI_open)
    show "\<wp> analytic_on UNIV - \<Lambda>"
      by (auto intro!: analytic_intros)
  next
    fix z assume "z \<in> \<Lambda>"
    thus "is_pole \<wp> z \<and> \<wp> z = 0"
      by (auto simp: weierstrass_fun_at_pole is_pole_weierstrass_fun)
  next
    show "isolated_singularity_at \<wp> z" for z
    proof (rule analytic_nhd_imp_isolated_singularity[of _ "-(\<Lambda>-{z})"])
      show "open (- (\<Lambda> - {z}))"
        by (intro open_Compl closed_subset_lattice) auto
    qed (auto intro!: analytic_intros)
  qed auto
qed

sublocale weierstrass_fun: even_elliptic_function \<omega>1 \<omega>2 \<wp>
  by standard (auto simp: weierstrass_fun_minus)

lemmas [elliptic_function_intros] =
  weierstrass_fun.elliptic_function_axioms
  weierstrass_fun.nicely_elliptic_function_axioms

lemma is_pole_weierstrass_fun_iff: "is_pole \<wp> z \<longleftrightarrow> z \<in> \<Lambda>"
  by (meson ComplI analytic_on_analytic_at is_pole_weierstrass_fun
      nicely_elliptic_function.analytic_at_iff_not_pole
      weierstrass_fun.nicely_elliptic_function_axioms weierstrass_fun_analytic)

lemma is_pole_weierstrass_fun_deriv_iff: "is_pole \<wp>' z \<longleftrightarrow> z \<in> \<Lambda>"
proof -
  have "eventually (\<lambda>w. w \<notin> \<Lambda>) (at z)"
    using islimpt_iff_eventually not_islimpt_lattice by auto
  hence "eventually (\<lambda>w. \<wp>' w = deriv \<wp> w) (at z)"
    by eventually_elim (simp add: deriv_weierstrass_fun)
  hence "is_pole \<wp>' z \<longleftrightarrow> is_pole (deriv \<wp>) z"
    by (rule is_pole_cong) auto
  also have "\<dots> \<longleftrightarrow> is_pole \<wp> z"
    by (rule is_pole_deriv_iff) (auto intro!: meromorphic_intros)
  also have "\<dots> \<longleftrightarrow> z \<in> \<Lambda>"
    by (rule is_pole_weierstrass_fun_iff)
  finally show ?thesis .
qed

lemma zorder_weierstrass_fun_deriv_pole:
  assumes "z \<in> \<Lambda>"
  shows   "zorder \<wp>' z = -3"
proof -
  have "eventually (\<lambda>w. w \<notin> \<Lambda>) (at z)"
    using islimpt_iff_eventually not_islimpt_lattice by auto
  hence "eventually (\<lambda>w. \<wp>' w = deriv \<wp> w) (at z)"
    by eventually_elim (simp add: deriv_weierstrass_fun)
  hence "zorder \<wp>' z = zorder (deriv \<wp>) z"
    by (rule zorder_cong) auto
  also have "\<dots> = zorder \<wp> z - 1"
    by (subst zorder_deriv) (auto simp: is_pole_weierstrass_fun_iff assms)
  also have "\<dots> = -3"
    using assms by (simp add: zorder_weierstrass_fun_pole)
  finally show ?thesis .
qed

lemma order_weierstrass_fun [simp]: "elliptic_order \<wp> = 2"
proof -
  have "elliptic_order \<wp> = (\<Sum>z \<in> period_parallelogram 0 \<inter> \<Lambda>. nat (-zorder \<wp> z))"
    unfolding elliptic_order_def by (rule sum.cong) (auto simp: is_pole_weierstrass_fun_iff)
  also have "period_parallelogram 0 \<inter> \<Lambda> = {0}"
    by (auto elim!: latticeE simp: period_parallelogram_altdef zero_prod_def)
  finally show ?thesis
    by (simp add: zorder_weierstrass_fun_pole)
qed

lemma order_weierstrass_fun_deriv [simp]: "elliptic_order \<wp>' = 3"
proof -
  have "elliptic_order \<wp>' = (\<Sum>z \<in> period_parallelogram 0 \<inter> \<Lambda>. nat (-zorder \<wp>' z))"
    unfolding elliptic_order_def by (rule sum.cong) (auto simp: is_pole_weierstrass_fun_deriv_iff)
  also have "period_parallelogram 0 \<inter> \<Lambda> = {0}"
    by (auto elim!: latticeE simp: period_parallelogram_altdef zero_prod_def)
  also have "(\<Sum>z\<in>{0}. nat (- zorder \<wp>' z)) = nat (-zorder \<wp>' 0)"
    by simp
  finally show ?thesis
    by (simp add: zorder_weierstrass_fun_deriv_pole)
qed

sublocale weierstrass_fun: nonconst_nicely_elliptic_function \<omega>1 \<omega>2 \<wp>
  by standard auto

sublocale weierstrass_fun_deriv: nonconst_nicely_elliptic_function \<omega>1 \<omega>2 "\<wp>'"
  by standard auto


subsection \<open>The numbers $e_1, e_2, e_3$\<close>

text \<open>
  The values of \<open>\<wp>\<close> at the half-periods $\frac{1}{2}\omega_1$, $\frac{1}{2}\omega_2$, and
  $\frac{1}{2}(\omega_1+\omega_2)$ are exactly the roots of the polynomial $4X^3 - g_2X - g_3$.

  We call these values $e_1$, $e_2$, $e_3$.
\<close>

(* Definition p.13 *)
definition number_e1:: "complex" ("\<e>\<^sub>1") where
  "\<e>\<^sub>1 \<equiv> \<wp> (\<omega>1 / 2)"

definition number_e2:: "complex" ("\<e>\<^sub>2") where
  "\<e>\<^sub>2 \<equiv> \<wp> (\<omega>2 / 2)"

definition number_e3:: "complex" ("\<e>\<^sub>3") where
  "\<e>\<^sub>3 \<equiv> \<wp> ((\<omega>1 + \<omega>2) / 2)"

lemmas number_e123_defs = number_e1_def number_e2_def number_e3_def

text \<open>
  The half-lattice points are those that are equivalent to one of the three points
  $\frac{\omega_1}{2}$, $\frac{\omega_2}{2}$, and $\frac{\omega_1 + \omega_2}{2}$.
\<close>
lemma to_fund_parallelogram_half_period:
  assumes "\<omega> \<notin> \<Lambda>" "2 * \<omega> \<in> \<Lambda>"
  shows   "to_fund_parallelogram \<omega> \<in> {\<omega>1 / 2, \<omega>2 / 2, (\<omega>1 + \<omega>2) / 2}"
proof -
  from assms(2) obtain m n where "2 * \<omega> = of_\<omega>12_coords (of_int m, of_int n)"
    by (elim latticeE)
  hence mn: "\<omega> = of_\<omega>12_coords (of_int m / 2, of_int n / 2)"
    by (auto simp: of_\<omega>12_coords_def field_simps)
  have [simp]: "of_\<omega>12_coords (1 / 2, 1 / 2) = (\<omega>1 + \<omega>2) / 2"
    by (simp add: of_\<omega>12_coords_def field_simps)
  have "odd m \<or> odd n"
    using assms(1) unfolding mn by (auto simp: in_lattice_conv_\<omega>12_coords elim!: evenE)
  thus ?thesis
    by (cases "even m"; cases "even n")
       (auto elim!: evenE oddE simp: mn to_fund_parallelogram_def add_divide_distrib)
qed

lemma rel_half_period:
  assumes "\<omega> \<notin> \<Lambda>" "2 * \<omega> \<in> \<Lambda>"
  shows   "\<exists>\<omega>'\<in>{\<omega>1 / 2, \<omega>2 / 2, (\<omega>1 + \<omega>2) / 2}. rel \<omega> \<omega>'"
proof -
  have "rel \<omega> (to_fund_parallelogram \<omega>)"
    by auto
  with to_fund_parallelogram_half_period[OF assms] show ?thesis
    by blast
qed

lemma weierstass_fun_deriv_half_period_eq_0:
  assumes "\<omega> \<in> \<Lambda>"
  shows   "\<wp>' (\<omega> / 2) = 0"
  using weierstrass_fun_deriv.lattice_cong[of "-\<omega>/2" "\<omega>/2"] \<open>\<omega> \<in> \<Lambda>\<close>
  by (simp add: rel_def uminus_in_lattice_iff)

lemma weierstass_fun_deriv_half_root_eq_0 [simp]:
  "\<wp>' (\<omega>1 / 2) = 0" "\<wp>' (\<omega>2 / 2) = 0" "\<wp>' ((\<omega>1 + \<omega>2) / 2) = 0"
  by (rule weierstass_fun_deriv_half_period_eq_0; simp)+

lemma weierstrass_fun_at_half_period:
  assumes "\<omega> \<in> \<Lambda>" "\<omega> / 2 \<notin> \<Lambda>"
  shows   "\<wp> (\<omega> / 2) \<in> {\<e>\<^sub>1, \<e>\<^sub>2, \<e>\<^sub>3}"
proof -
  have "\<exists>\<omega>'\<in>{\<omega>1 / 2, \<omega>2 / 2, (\<omega>1 + \<omega>2) / 2}. rel (\<omega> / 2) \<omega>'"
    using rel_half_period[of "\<omega> / 2"] assms by auto
  thus ?thesis
    unfolding number_e123_defs using weierstrass_fun.lattice_cong by blast
qed

lemma weierstrass_fun_at_half_period':
  assumes "2 * \<omega> \<in> \<Lambda>" "\<omega> \<notin> \<Lambda>"
  shows   "\<wp> \<omega> \<in> {\<e>\<^sub>1, \<e>\<^sub>2, \<e>\<^sub>3}"
  using weierstrass_fun_at_half_period[of "2 * \<omega>"] assms by simp

text \<open>
  $\wp'$ has a simple zero at each half-lattice point, and no other zeros.
\<close>
lemma weierstrass_fun_deriv_eq_0_iff:
  assumes "z \<notin> \<Lambda>"
  shows   "\<wp>' z = 0 \<longleftrightarrow> 2 * z \<in> \<Lambda>"
proof
  assume "\<wp>' z = 0"
  define z' where "z' = to_fund_parallelogram z"
  have z': "\<wp>' z' = 0" "z' \<notin> \<Lambda>" "z' \<in> period_parallelogram 0"
    using \<open>\<wp>' z = 0\<close> assms by (auto simp: z'_def weierstrass_fun_deriv.eval_to_fund_parallelogram)
  have [simp]: "\<wp>' \<noteq> (\<lambda>_. 0)"
    using weierstrass_fun_deriv.elliptic_order_eq_0_iff_no_poles by auto
  have "{\<omega>1 / 2, \<omega>2 / 2, (\<omega>1 + \<omega>2) / 2, z'} \<subseteq> {z\<in>period_parallelogram 0. isolated_zero \<wp>' z}"
    using z' by (auto simp: period_parallelogram_altdef \<omega>12_coords.add
                   weierstrass_fun_deriv.isolated_zero_iff is_pole_weierstrass_fun_deriv_iff)

  hence "card {\<omega>1 / 2, \<omega>2 / 2, (\<omega>1 + \<omega>2) / 2, z'} \<le> card {z\<in>period_parallelogram 0. isolated_zero \<wp>' z}"
    by (intro card_mono weierstrass_fun_deriv.finite_zeros_in_parallelogram)
  also have "\<dots> \<le> 3"
    using weierstrass_fun_deriv.card_zeros_le_order[of 0] by simp
  finally have "2 * z' \<in> {\<omega>1, \<omega>2, \<omega>1 + \<omega>2}"
    by (auto simp: card_insert_if split: if_splits)
  also have "\<dots> \<subseteq> \<Lambda>"
    by auto
  finally have "2 * z' \<in> \<Lambda>" .
  thus "2 * z \<in> \<Lambda>" unfolding z'_def
    by (metis rel_to_fund_parallelogram_right mult_2 rel_add rel_lattice_trans_right)
next
  assume "2 * z \<in> \<Lambda>"
  thus "\<wp>' z = 0"
    using assms weierstass_fun_deriv_half_period_eq_0[of "2*z"] by auto
qed

lemma zorder_weierstrass_fun_deriv_zero:
  assumes "z \<notin> \<Lambda>" "2 * z \<in> \<Lambda>"
  shows   "zorder \<wp>' z = 1"
proof -
  have *: "\<wp>' \<noteq> (\<lambda>_. 0)"
    using is_pole_weierstrass_fun_deriv_iff[of 0] by auto
  note ** [simp] = weierstrass_fun_deriv.isolated_zero_iff[OF *] is_pole_weierstrass_fun_deriv_iff

  define w1 w2 w3 where "w1 = \<omega>1 / 2" "w2 = \<omega>2 / 2" "w3 = (\<omega>1 + \<omega>2) / 2"
  note w123_defs = this
  have [simp]: "w1 \<notin> \<Lambda>" "w2 \<notin> \<Lambda>" "w3 \<notin> \<Lambda>" "2 * w1 \<in> \<Lambda>" "2 * w2 \<in> \<Lambda>" "2 * w3 \<in> \<Lambda>"
   and "distinct [w1, w2, w3]"
    by (auto simp: w123_defs add_divide_distrib in_lattice_conv_\<omega>12_coords \<omega>12_coords.add)
  define A where "A = {w1, w2, w3}"
  have [simp, intro]: "finite A" and [simp]: "card A = 3"
    using \<open>distinct [w1, w2, w3]\<close> by (auto simp: A_def)

  have in_parallelogram: "A \<subseteq> period_parallelogram 0"
    unfolding A_def period_parallelogram_altdef by (auto simp: w123_defs \<omega>12_coords.add)
  have [simp]: "\<wp>' w = 0" if "w \<in> A" for w
    by (subst weierstrass_fun_deriv_eq_0_iff) (use that in \<open>auto simp: A_def\<close>)
  have [intro]: "isolated_zero \<wp>' w" if "w \<in> A" for w
    using that by (subst **) (auto simp: A_def)

  have "(\<Sum>w\<in>A. nat (zorder \<wp>' w)) \<le> elliptic_order \<wp>'"
    unfolding weierstrass_fun_deriv.zeros_eq_elliptic_order[of 0, symmetric] using in_parallelogram
    by (intro sum_mono2 weierstrass_fun_deriv.finite_zeros_in_parallelogram)
       (auto simp: A_def)
  also have "\<dots> = 3"
    by simp
  finally have le_3: "(\<Sum>w\<in>A. nat (zorder \<wp>' w)) \<le> 3" .

  have pos: "zorder \<wp>' w > 0" if "w \<in> A" for w
    by (rule zorder_isolated_zero_pos) (use that in \<open>auto intro!: analytic_intros simp: A_def\<close>)

  have zorder_eq_1: "zorder \<wp>' w = 1" if "w \<in> A" for w
  proof (rule ccontr)
    assume *: "zorder \<wp>' w \<noteq> 1"
    have "(\<Sum>w\<in>A. nat (zorder \<wp>' w)) > (\<Sum>w\<in>A. 1)"
    proof (rule sum_strict_mono_strong[of _ w])
      show "nat (zorder \<wp>' w) \<ge> 1" if "w \<in> A" for w
        using pos[of w] that by auto
    qed (use pos[of w] * \<open>w \<in> A\<close> in auto)
    with le_3 show False
      by simp
  qed

  from assms obtain w where w: "w \<in> A" "rel z w"
    using rel_half_period[of z] unfolding A_def w123_defs by metis
  with zorder_eq_1[of w] show ?thesis
    using weierstrass_fun_deriv.zorder.lattice_cong by metis
qed

end (* complex_lattice *)



subsection \<open>Injectivity of \<open>\<wp>\<close>\<close>

context complex_lattice
begin

text \<open>
  The function \<open>\<wp>\<close> is almost injective in the sense that $\wp(u) = \wp(v)$ iff 
  $u \sim v$ or $u \sim -v$. Another way to phrase this is that it is injective inside 
  period half-parallelograms.

  This is Exercise~1.3(a) in Apostol's book.
\<close>
theorem weierstrass_fun_eq_iff:
  assumes "u \<notin> \<Lambda>" "v \<notin> \<Lambda>"
  shows   "\<wp> u = \<wp> v \<longleftrightarrow> rel u v \<or> rel u (-v)"
proof (intro iffI)
  assume "rel u v \<or> rel u (-v)"
  thus "\<wp> u = \<wp> v"
    by (metis weierstrass_fun.lattice_cong weierstrass_fun_minus)
next
  assume *: "\<wp> u = \<wp> v"
  define c where "c = \<wp> u"
  define f where "f = (\<lambda>z. \<wp> z - c)"
  interpret f: elliptic_function_affine \<omega>1 \<omega>2 \<wp> 1 "-c" f
  proof -
    show "elliptic_function_affine \<omega>1 \<omega>2 \<wp> 1"
      by standard auto
  qed (simp_all add: f_def)
  interpret f: even_elliptic_function \<omega>1 \<omega>2 f
    by standard (simp_all add: f_def weierstrass_fun_minus)
  interpret f: elliptic_function_remove_sings \<omega>1 \<omega>2 f ..

  have ana: "f analytic_on {x}" if "x \<notin> \<Lambda>" for x using that
    unfolding f_def by (auto intro!: analytic_intros)
  have ana': "remove_sings f analytic_on {x}" if "x \<notin> \<Lambda>" for x using that
    by (auto simp: f.remove_sings.analytic_at_iff_not_pole f.is_pole_affine_iff 
                   is_pole_weierstrass_fun_iff)
  have [simp]: "remove_sings f x = f x" if "x \<notin> \<Lambda>" for x
    using ana[OF that] by simp
  have [simp]: "f u = 0" "f v = 0"
    using * by (auto simp: f_def c_def)

  have order: "elliptic_order f = 2"
    by (simp add: f.order_affine_eq)
  have nz: "remove_sings f \<noteq> (\<lambda>_. 0)"
  proof
    assume "remove_sings f = (\<lambda>_. 0)"
    hence "remove_sings f constant_on UNIV"
      by (auto simp: constant_on_def)
    thus False
      using f.remove_sings.elliptic_order_eq_0_iff order by simp
  qed
  have zero_f_iff [simp]: "isolated_zero f z \<longleftrightarrow> f z = 0" if "z \<notin> \<Lambda>" for z
    using that ana f.affine.isolated_zero_analytic_iff 
          f.affine.elliptic_order_eq_0_iff_const_cosparse local.order by auto

  define u' where "u' = to_half_fund_parallelogram u"
  define v' where "v' = to_half_fund_parallelogram v"
  define Z where "Z = {z \<in> period_parallelogram 0. z \<notin> \<Lambda> \<and> f z = 0}"
  define Z1 where "Z1 = {z \<in> half_fund_parallelogram. z \<notin> \<Lambda> \<and> f z = 0}"
  define Z2 where "Z2 = to_fund_parallelogram ` uminus ` Z1"

  have Z: "(\<Sum>z\<in>Z. nat (zorder f z)) = 2" "finite Z"
  proof -
    have "(\<Sum>z\<in>{z\<in>period_parallelogram 0. isolated_zero (remove_sings f) z}. 
                  nat (zorder (remove_sings f) z)) = 2 \<and>
          finite {z\<in>period_parallelogram 0. isolated_zero (remove_sings f) z}"
      using order f.remove_sings.zeros_eq_elliptic_order[of 0]
            f.remove_sings.finite_zeros_in_parallelogram[of 0] by simp
    also have "{z\<in>period_parallelogram 0. isolated_zero (remove_sings f) z} =
               {z\<in>period_parallelogram 0. z \<notin> \<Lambda> \<and> remove_sings f z = 0}"
      by (subst f.remove_sings.isolated_zero_iff)
         (use nz f.is_pole_affine_iff is_pole_weierstrass_fun_iff in auto)
    also have "\<dots> = {z\<in>period_parallelogram 0. z \<notin> \<Lambda> \<and> f z = 0}"
      by (intro Collect_cong conj_cong) auto
    finally show "(\<Sum>z\<in>Z. nat (zorder f z)) = 2" "finite Z"
      unfolding Z_def by auto
  qed
  have "finite Z1"
    by (rule finite_subset[OF _ Z(2)])
       (use half_fund_parallelogram_subset_period_parallelogram in \<open>auto simp: Z_def Z1_def\<close>)
  hence "finite Z2"
    by (simp_all add: Z2_def)
  note finite = \<open>finite Z\<close> \<open>finite Z1\<close> \<open>finite Z2\<close>

  have subset: "Z1 \<subseteq> Z" "Z2 \<subseteq> Z"
    unfolding Z_def Z1_def Z2_def
    using half_fund_parallelogram_subset_period_parallelogram 
    by (auto simp: uminus_in_lattice_iff f.affine.eval_to_fund_parallelogram f.even)

  have "card Z1 + card Z2 = card (Z1 \<union> Z2) + card (Z1 \<inter> Z2)"
    by (rule card_Un_Int) (use finite in auto)
  also have "card Z2 = card Z1" unfolding Z2_def image_image
    by (intro card_image inj_onI)
       (auto simp: Z1_def rel_minus_iff intro: rel_in_half_fund_parallelogram_imp_eq)
  also have "card (Z1 \<union> Z2) \<le> card Z"
    by (intro card_mono finite) (use subset in auto)
  also have "\<dots> = (\<Sum>z\<in>Z. 1)"
    by simp
  also have "card (Z1 \<inter> Z2) = (\<Sum>z\<in>Z1 \<inter> Z2. 1)"
    by simp
  also have "\<dots> = (\<Sum>z\<in>Z. if z \<in> Z1 \<inter> Z2 then 1 else 0)"
    by (intro sum.mono_neutral_cong_left) (use finite subset in auto)
  also have "(\<Sum>z\<in>Z. 1) + \<dots> = (\<Sum>z\<in>Z. if z \<in> Z1 \<inter> Z2 then 2 else 1)"
    by (subst sum.distrib [symmetric], intro sum.cong) auto
  also have "\<dots> \<le> (\<Sum>z\<in>Z. nat (zorder f z))"
  proof (intro sum_mono)
    fix z assume z: "z \<in> Z"
    hence "zorder f z > 0"
      by (intro zorder_isolated_zero_pos ana) (auto simp: Z_def)
    moreover have "zorder f z \<ge> 2" if z: "z \<in> Z1 \<inter> Z2"
    proof -
      obtain z' where "to_fund_parallelogram (-z') \<in> half_fund_parallelogram" "z' \<notin> \<Lambda>"
                      "z = to_fund_parallelogram (-z')" "z' \<in> half_fund_parallelogram"
        using z by (auto simp: Z1_def Z2_def uminus_in_lattice_iff)
      hence "2 * z \<in> \<Lambda>"
        by (metis in_half_fund_parallelogram_imp_half_lattice
              rel_in_half_fund_parallelogram_imp_eq rel_to_fund_parallelogram_left)
      moreover have "\<not>(\<forall>\<^sub>\<approx>z. f z = 0)" using nz
        using f.affine.elliptic_order_eq_0_iff_const_cosparse local.order by auto
      ultimately have "even (zorder f z)"
        by (intro f.even_zorder)
      with \<open>zorder f z > 0\<close> show "zorder f z \<ge> 2"
        by presburger
    qed
    ultimately show "(if z \<in> Z1 \<inter> Z2 then 2 else 1) \<le> nat (zorder f z)"
      by auto
  qed
  also have "\<dots> = 2"
    by (fact Z(1))
  finally have "card Z1 \<le> 1"
    by simp
  moreover have "card {u', v'} \<le> card Z1" using assms
    by (intro card_mono finite) (auto simp: Z1_def u'_def v'_def f.eval_to_half_fund_parallelogram)
  ultimately have "card {u', v'} \<le> 1"
    by simp
  hence "u' = v'"
    by (cases "u' = v'") simp_all
  thus "rel u v \<or> rel u (-v)"
    unfolding u'_def v'_def by (simp add: to_half_fund_parallelogram_eq_iff)
qed

text \<open>
  It is also surjective. Together with the fact that it is doubly periodic and even, this means
  that it takes on every value exactly once inside its period triangles, or twice within its
  period parallelograms. Note however that the multiplicities of the poles on the lattice points
  and of the values \<^term>\<open>\<e>\<^sub>1\<close>, \<^term>\<open>\<e>\<^sub>2\<close>, \<^term>\<open>\<e>\<^sub>3\<close> at the half-lattice points are 2.
\<close>
lemma surj_weierstrass_fun:
  obtains z where "z \<in> period_parallelogram w - \<Lambda>" "\<wp> z = c"
  using weierstrass_fun.surj[of w c]
  by (auto simp: is_pole_weierstrass_fun_iff)

lemma surj_weierstrass_fun_deriv:
  obtains z where "z \<in> period_parallelogram w - \<Lambda>" "\<wp>' z = c"
  using weierstrass_fun_deriv.surj[of w c]
  by (auto simp: is_pole_weierstrass_fun_deriv_iff)

end


context complex_lattice_swap
begin

lemma weierstrass_fun_aux_swap [simp]: "swap.weierstrass_fun_aux = weierstrass_fun_aux"
  unfolding weierstrass_fun_aux_def [abs_def] swap.weierstrass_fun_aux_def [abs_def] by auto

lemma weierstrass_fun_swap [simp]: "swap.weierstrass_fun = weierstrass_fun"
  unfolding weierstrass_fun_def [abs_def] swap.weierstrass_fun_def [abs_def] by auto

lemma number_e1_swap [simp]: "swap.number_e1 = number_e2"
  and number_e2_swap [simp]: "swap.number_e2 = number_e1"
  and number_e3_swap [simp]: "swap.number_e3 = number_e3"
  unfolding number_e2_def swap.number_e1_def number_e1_def swap.number_e2_def
            number_e3_def swap.number_e3_def by (simp_all add: add_ac)

end


subsection \<open>Invariance under lattice transformations\<close>

text \<open>
  We show how various concepts related to lattices (e.g.\ the Weierstra\ss\ $\wp$
  function, the numbers $e_1$, $e_2$, $e_3$) transform under various transformations of the lattice.
  Namely: complex conjugation, swapping the generators, stretching/rotation, and unimodular
  M\"obius transforms.
\<close>

locale complex_lattice_cnj = complex_lattice
begin

sublocale cnj: complex_lattice "cnj \<omega>1" "cnj \<omega>2"
  by unfold_locales (use fundpair in auto)

lemma bij_betw_lattice_cnj: "bij_betw cnj lattice cnj.lattice"
  by (rule bij_betwI[of _ _ _ cnj])
     (auto elim!: latticeE cnj.latticeE simp: of_\<omega>12_coords_def cnj.of_\<omega>12_coords_def
           intro!: lattice_intros cnj.lattice_intros)

lemma bij_betw_lattice0_cnj: "bij_betw cnj lattice0 cnj.lattice0"
  unfolding lattice0_def cnj.lattice0_def
  by (intro bij_betw_DiffI bij_betw_lattice_cnj) auto

lemma lattice_cnj_eq: "cnj.lattice = cnj ` lattice"
  using bij_betw_lattice_cnj by (auto simp: bij_betw_def)

lemma lattice0_cnj_eq: "cnj.lattice0 = cnj ` lattice0"
  using bij_betw_lattice0_cnj by (auto simp: bij_betw_def)

lemma eisenstein_fun_aux_cnj: "cnj.eisenstein_fun_aux n z = cnj (eisenstein_fun_aux n (cnj z))"
  unfolding eisenstein_fun_aux_def cnj.eisenstein_fun_aux_def
  by (subst infsum_reindex_bij_betw[OF bij_betw_lattice0_cnj, symmetric])
     (auto simp flip: infsum_cnj simp: lattice0_cnj_eq in_image_cnj_iff)

lemma weierstrass_fun_aux_cnj: "cnj.weierstrass_fun_aux z = cnj (weierstrass_fun_aux (cnj z))"
  unfolding weierstrass_fun_aux_def cnj.weierstrass_fun_aux_def
  by (subst infsum_reindex_bij_betw[OF bij_betw_lattice0_cnj, symmetric])
     (auto simp flip: infsum_cnj simp: lattice0_cnj_eq in_image_cnj_iff)

lemma weierstrass_fun_cnj: "cnj.weierstrass_fun z = cnj (weierstrass_fun (cnj z))"
  unfolding weierstrass_fun_def cnj.weierstrass_fun_def
  by (auto simp: lattice_cnj_eq in_image_cnj_iff weierstrass_fun_aux_cnj)

lemma number_e1_cnj [simp]: "cnj.number_e1 = cnj number_e1"
  and number_e2_cnj [simp]: "cnj.number_e2 = cnj number_e2"
  and number_e3_cnj [simp]: "cnj.number_e3 = cnj number_e3"
  by (simp_all add: number_e1_def cnj.number_e1_def number_e2_def 
                    cnj.number_e2_def number_e3_def cnj.number_e3_def weierstrass_fun_cnj)

end


locale complex_lattice_stretch = complex_lattice +
  fixes c :: complex
  assumes stretch_nonzero: "c \<noteq> 0"
begin

sublocale stretched: complex_lattice "c * \<omega>1" "c * \<omega>2"
  by unfold_locales (use fundpair in \<open>auto simp: stretch_nonzero fundpair_def\<close>)

lemma stretched_of_\<omega>12_coords: "stretched.of_\<omega>12_coords ab = c * of_\<omega>12_coords ab"
  unfolding stretched.of_\<omega>12_coords_def of_\<omega>12_coords_def
  by (auto simp: case_prod_unfold algebra_simps)

lemma stretched_\<omega>12_coords: "stretched.\<omega>12_coords ab = \<omega>12_coords (ab / c)"
  using stretch_nonzero stretched_of_\<omega>12_coords
  by (metis mult.commute nonzero_divide_eq_eq of_\<omega>12_coords_\<omega>12_coords stretched.\<omega>12_coords_eqI)

lemma stretched_\<omega>1_coord: "stretched.\<omega>1_coord ab = \<omega>1_coord (ab / c)"
  and stretched_\<omega>2_coord: "stretched.\<omega>2_coord ab = \<omega>2_coord (ab / c)"
  using stretched_\<omega>12_coords[of ab] by (simp_all add: stretched.\<omega>12_coords_def \<omega>12_coords_def)

lemma mult_into_stretched_lattice: "(*) c \<in> \<Lambda> \<rightarrow> stretched.lattice"
  by (auto elim!: latticeE simp: stretched.in_lattice_conv_\<omega>12_coords 
        stretched_\<omega>12_coords zero_prod_def)

lemma mult_into_stretched_lattice': "(*) (inverse c) \<in> stretched.lattice \<rightarrow> \<Lambda>"
proof -
  interpret inv: complex_lattice_stretch "c * \<omega>1" "c * \<omega>2" "inverse c"
    by unfold_locales (use stretch_nonzero in auto)
  from inv.mult_into_stretched_lattice show ?thesis
    by (simp add: inv.stretched.lattice_def stretched.lattice_def field_simps stretch_nonzero)
qed

lemma bij_betw_stretch_lattice: "bij_betw ((*) c) lattice stretched.lattice"
proof (rule bij_betwI[of _ _ _ "(*) (inverse c)"])
  show "(*) c \<in> \<Lambda> \<rightarrow> stretched.lattice"
    by (rule mult_into_stretched_lattice)
  show "(*) (inverse c) \<in> stretched.lattice \<rightarrow> \<Lambda>"
    by (rule mult_into_stretched_lattice')
qed (auto simp: stretch_nonzero)

lemma bij_betw_stretch_lattice0:
  "bij_betw ((*) c) lattice0 stretched.lattice0"
  unfolding lattice0_def stretched.lattice0_def
  by (intro bij_betw_DiffI bij_betw_stretch_lattice) auto

end

                                                                        
locale unimodular_moebius_transform_lattice = complex_lattice + unimodular_moebius_transform
begin

definition \<omega>1' where "\<omega>1' = of_int c * \<omega>2 + of_int d * \<omega>1"
definition \<omega>2' where "\<omega>2' = of_int a * \<omega>2 + of_int b * \<omega>1"

sublocale transformed: complex_lattice \<omega>1' \<omega>2'
proof unfold_locales
  define \<tau> where "\<tau> = \<omega>2 / \<omega>1"
  have "Im (\<phi> \<tau>) \<noteq> 0"
    using fundpair Im_transform_zero_iff[of \<tau>] unfolding \<tau>_def
    by (auto simp: fundpair_def complex_is_Real_iff)
  also have "\<phi> \<tau> = \<omega>2' / \<omega>1'"
    by (simp add: \<phi>_def \<omega>1'_def \<omega>2'_def moebius_def \<tau>_def divide_simps)
  finally show "fundpair (\<omega>1', \<omega>2')"
    by (simp add: \<phi>_def \<omega>1'_def \<omega>2'_def moebius_def \<tau>_def field_simps 
                  fundpair_def complex_is_Real_iff)
qed

lemma transformed_lattice_subset: "transformed.lattice \<subseteq> lattice"
proof safe
  fix z assume "z \<in> transformed.lattice"
  then obtain m n where mn: "z = of_int m * \<omega>1' + of_int n * \<omega>2'"
    by (elim transformed.latticeE) (auto simp: transformed.of_\<omega>12_coords_def)
  also have "of_int m * \<omega>1' + of_int n * \<omega>2' =
             of_int (d * m + b * n) * \<omega>1 + of_int (c * m + a * n) * \<omega>2"
    by (simp add: algebra_simps \<omega>1'_def \<omega>2'_def)
  finally show "z \<in> lattice"
    by (auto intro!: lattice_intros simp: ring_distribs mult.assoc)
qed

lemma transformed_lattice_eq: "transformed.lattice = lattice"
proof -
  interpret inverse_unimodular_moebius_transform a b c d ..
  interpret inv: unimodular_moebius_transform_lattice \<omega>1' \<omega>2' d "-b" "-c" a ..
  have [simp]: "inv.\<omega>1' = \<omega>1" "inv.\<omega>2' = \<omega>2"
    unfolding inv.\<omega>1'_def inv.\<omega>2'_def unfolding \<omega>1'_def \<omega>2'_def of_int_minus using unimodular
    by (simp_all add: algebra_simps flip: of_int_mult)
    
  have "inv.transformed.lattice \<subseteq> transformed.lattice"
    by (rule inv.transformed_lattice_subset)
  also have "inv.transformed.lattice = lattice"
    unfolding inv.transformed.lattice_def unfolding lattice_def by simp
  finally show ?thesis
    using transformed_lattice_subset by blast
qed  

lemma transformed_lattice0_eq: "transformed.lattice0 = lattice0"
  by (simp add: transformed.lattice0_def lattice0_def transformed_lattice_eq)

lemma eisenstein_fun_aux_transformed [simp]: "transformed.eisenstein_fun_aux = eisenstein_fun_aux"
  by (intro ext) (simp add: transformed.eisenstein_fun_aux_def eisenstein_fun_aux_def
                            transformed_lattice0_eq)

lemma weierstrass_fun_aux_transformed [simp]: "transformed.weierstrass_fun_aux = weierstrass_fun_aux"
  by (intro ext, unfold weierstrass_fun_aux_def transformed.weierstrass_fun_aux_def 
       transformed_lattice0_eq) simp_all

lemma weierstrass_fun_transformed [simp]: "transformed.weierstrass_fun = weierstrass_fun"
  by (intro ext, simp add: weierstrass_fun_def transformed.weierstrass_fun_def transformed_lattice_eq)

end


locale complex_lattice_apply_modgrp = complex_lattice +
  fixes f :: modgrp
begin

sublocale unimodular_moebius_transform_lattice 
  \<omega>1 \<omega>2 "modgrp_a f" "modgrp_b f" "modgrp_c f" "modgrp_d f"
  rewrites "modgrp.as_modgrp = (\<lambda>x. x)" and "modgrp.\<phi> = apply_modgrp"
    by unfold_locales simp_all

end



subsection \<open>Construction of arbitrary elliptic functions from \<open>\<wp>\<close>\<close>

text \<open>
  In this section we will show that any elliptic function can be written as a combination of
  \<open>\<wp>\<close> and \<open>\<wp>'\<close>. The key step is to show that every even elliptic function can be written as a
  rational function of \<open>\<wp>\<close>.

  The first step is to show that if $w \notin \Lambda$, the function $f(z) = \wp(z) - \wp(w)$
  has a double zero at $w$ if $w$ is a half-lattice point and simple zeros at $\pm w$ otherwise,
  and no other zeros.
\<close>

locale weierstrass_fun_minus_const = complex_lattice +
  fixes w :: complex and f :: "complex \<Rightarrow> complex"
  assumes not_in_lattice: "w \<notin> \<Lambda>"
  defines "f \<equiv> (\<lambda>z. \<wp> z - \<wp> w)"
begin

sublocale elliptic_function_affine \<omega>1 \<omega>2 \<wp> 1 "-\<wp> w" f
  unfolding f_def by unfold_locales (auto simp: f_def)

lemmas order_eq = order_affine_eq
lemmas is_pole_iff = is_pole_affine_iff
lemmas zorder_pole_eq = zorder_pole_affine

lemma isolated_zero_iff: "isolated_zero f z \<longleftrightarrow> rel z w \<or> rel z (-w)"
proof (cases "z \<in> \<Lambda>")
  case False
  hence "f analytic_on {z}"
    unfolding f_def by (auto intro!: analytic_intros)
  moreover have "\<not>(\<forall>\<^sub>\<approx>z. f z = 0)"
    using affine.elliptic_order_eq_0_iff_const_cosparse order_affine_eq by auto
  ultimately have "isolated_zero f z \<longleftrightarrow> \<wp> z = \<wp> w"
    by (subst affine.isolated_zero_analytic_iff) (auto simp: f_def)
  also have "\<dots> \<longleftrightarrow> rel z w \<or> rel z (-w)"
    by (rule weierstrass_fun_eq_iff) (use not_in_lattice False in auto)
  finally show ?thesis .
next
  case True
  thus ?thesis
    using not_in_lattice is_pole_iff is_pole_weierstrass_fun pole_is_not_zero
      pre_complex_lattice.rel_lattice_trans_left uminus_in_lattice_iff by blast
qed

lemma zorder_zero_eq:
  assumes "rel z w \<or> rel z (-w)"
  shows   "zorder f z = (if 2 * w \<in> \<Lambda> then 2 else 1)"
proof (cases "2 * w \<in> \<Lambda>")
  case False
  have z: "z \<notin> \<Lambda>"
    using assms not_in_lattice pre_complex_lattice.rel_lattice_trans_left
          uminus_in_lattice_iff by blast
  have z': "2 * z \<notin> \<Lambda>"
    using assms False z
    by (metis minus_zero minus_minus not_in_lattice weierstrass_fun_deriv.lattice_cong
        weierstrass_fun_deriv_eq_0_iff weierstrass_fun_deriv_minus z)
  have "zorder f z = 1"
  proof (rule zorder_zero_eqI')
    show "f analytic_on {z}"
      using not_in_lattice z by (auto simp: f_def intro!: analytic_intros)
  next
    show "(deriv ^^ i) f z = 0" if "i < nat 1" for i
      using that z not_in_lattice assms by (auto simp: f_def weierstrass_fun_eq_iff)
  next
    have "deriv f z = \<wp>' z" unfolding f_def
      by (rule DERIV_imp_deriv) (use z in \<open>auto intro!: derivative_eq_intros\<close>)
    also have "\<wp>' z \<noteq> 0"
      using not_in_lattice False z assms z' by (auto simp: weierstrass_fun_deriv_eq_0_iff)
    finally show "(deriv ^^ nat 1) f z \<noteq> 0"
      by simp
  qed auto
  with False show ?thesis
    by simp
next
  case True
  have z: "z \<notin> \<Lambda>"
    using assms not_in_lattice pre_complex_lattice.rel_lattice_trans_left
          uminus_in_lattice_iff by blast
  have z': "2 * z \<in> \<Lambda>"
    using assms True z
    by (metis minus_zero minus_minus not_in_lattice weierstrass_fun_deriv.lattice_cong
        weierstrass_fun_deriv_eq_0_iff weierstrass_fun_deriv_minus z)

  have "eventually (\<lambda>w. f w \<noteq> 0) (at 0)"
    by (simp add: affine.avoid' order_affine_eq)
  moreover have "eventually (\<lambda>w. w \<notin> \<Lambda>) (at 0)"
    using islimpt_iff_eventually not_islimpt_lattice by auto
  ultimately have ev: "eventually (\<lambda>w. f w \<noteq> 0 \<and> w \<notin> \<Lambda>) (at 0)"
    by eventually_elim auto
  obtain z0 where z0: "z0 \<notin> \<Lambda>" "f z0 \<noteq> 0"
    using eventually_happens[OF ev] by auto

  have "(\<Sum>z\<in>{z}. nat (zorder f z)) \<le>
        (\<Sum>z' | z' \<in> period_parallelogram z \<and> isolated_zero f z'. nat (zorder f z'))"
    using assms by (intro sum_mono2 affine.finite_zeros_in_parallelogram) (auto simp: isolated_zero_iff)
  also have "\<dots> = 2"
    using affine.zeros_eq_elliptic_order[of z] order_eq by simp
  finally have "zorder f z \<le> 2"
    by simp

  moreover have "zorder f z \<ge> int 2"
  proof (rule zorder_geI) (* TODO: ugly. better lemma? *)
    show "f holomorphic_on -\<Lambda>"
      by (auto intro!: holomorphic_intros simp: f_def)
  next
    show "z0 \<in> -\<Lambda>" "f z0 \<noteq> 0"
      using z0 by auto
  next
    show "open (-\<Lambda>)"
      using closed_lattice by auto
  next
    have "\<Lambda> sparse_in UNIV"
      using not_islimpt_lattice sparse_in_def by blast
    hence "connected (UNIV - \<Lambda>)"
      by (intro sparse_imp_connected) auto   
    also have "UNIV - \<Lambda> = -\<Lambda>"
      by auto
    finally show "connected (-\<Lambda>)" .
  next
    have "deriv f z = \<wp>' z"
      by (rule DERIV_imp_deriv) (auto simp: f_def intro!: derivative_eq_intros z)
    also have "\<dots> = 0"
      using True z z' weierstrass_fun_deriv_eq_0_iff by blast
    finally have "deriv f z = 0" .
    moreover have "f z = 0"
      using not_in_lattice z z' assms by (simp add: f_def weierstrass_fun_eq_iff)
    ultimately show "(deriv ^^ n) f z = 0" if "n < 2" for n
      using that by (cases n) auto
  qed (use z in \<open>auto intro!: analytic_intros simp: f_def\<close>)
  ultimately have "zorder f z = 2"
    by linarith
  thus ?thesis
    using True by simp
qed

lemma zorder_zero_eq':
  assumes "z \<notin> \<Lambda>"
  shows   "zorder f z = (if rel z w \<or> rel z (-w) then if 2 * w \<in> \<Lambda> then 2 else 1 else 0)"
proof (cases "rel z w \<or> rel z (-w)")
  case True
  thus ?thesis
    using zorder_zero_eq[OF True] by auto
next
  case False
  have "f analytic_on {z}"
    using assms by (auto simp: f_def intro!: analytic_intros)
  moreover have "f z \<noteq> 0"
    using assms not_in_lattice False by (auto simp: f_def weierstrass_fun_eq_iff)
  ultimately have "zorder f z = 0"
    by (intro zorder_eq_0I) auto
  thus ?thesis
    using False by simp
qed

end


lemma (in complex_lattice) zorder_weierstrass_fun_minus_const:
  assumes "w \<notin> \<Lambda>" "z \<notin> \<Lambda>"
  shows   "zorder (\<lambda>z. \<wp> z - \<wp> w) z = 
             (if rel z w \<or> rel z (-w) then if 2 * w \<in> \<Lambda> then 2 else 1 else 0)"
proof -
  interpret weierstrass_fun_minus_const \<omega>1 \<omega>2 w "\<lambda>z. \<wp> z - \<wp> w"
    by unfold_locales (use assms in auto)
  show ?thesis
    using zorder_zero_eq'[of z] assms by simp
qed


text \<open>
  We now construct an elliptic function 
  \[g(z) = \prod_{w\in A} (\wp(z) - \wp(w))^{h(w)}\]
  where $A \subseteq \mathbb{C}\setminus\Lambda$ is finite and $h : A \to \mathbb{Z}$.

  We will examine what the zeros and poles of this functions are and what their multiplicities are.

  This is roughly Exercise~1.3(b) in Apostol's book.
\<close>
locale elliptic_function_construct = complex_lattice +
  fixes A :: "complex set" and h :: "complex \<Rightarrow> int" and g :: "complex \<Rightarrow> complex"
  assumes finite [intro]: "finite A" and no_lattice_points: "A \<inter> \<Lambda> = {}"
  defines "g \<equiv> (\<lambda>z. (\<Prod>w\<in>A. (\<wp> z - \<wp> w) powi h w))"
begin

sublocale elliptic_function \<omega>1 \<omega>2 g
  unfolding g_def by (intro elliptic_function_intros)

sublocale even_elliptic_function \<omega>1 \<omega>2 g
  by standard (simp add: g_def weierstrass_fun_minus)

lemma no_lattice_points': "w \<notin> \<Lambda>" if "w \<in> A" for w
  using no_lattice_points that by blast

lemma eq_0_iff: "g z = 0 \<longleftrightarrow> (\<exists>w\<in>A. h w \<noteq> 0 \<and> (rel z w \<or> rel z (-w)))" if "z \<notin> \<Lambda>" for z
    using finite that by (auto simp: g_def weierstrass_fun_eq_iff no_lattice_points')

lemma nonzero_almost_everywhere: "eventually (\<lambda>z. g z \<noteq> 0) (cosparse UNIV)"
proof -
  have "{z. g z = 0} \<subseteq> \<Lambda> \<union> (\<Union>w\<in>A. (+) w ` \<Lambda>) \<union> (\<Union>w\<in>A. (+) (-w) ` \<Lambda>)"
    using eq_0_iff by (force simp: rel_def)
  moreover have "\<dots> sparse_in UNIV"
    by (intro sparse_in_union' sparse_in_UN_finite finite_imageI
              finite sparse_in_translate_UNIV lattice_sparse)
  ultimately have "{z. g z = 0} sparse_in UNIV"
    using sparse_in_subset2 by blast
  thus ?thesis
    by (simp add: eventually_cosparse)
qed

lemma eventually_nonzero_at: "eventually (\<lambda>z. g z \<noteq> 0) (at z)"
  using nonzero_almost_everywhere by (auto simp: eventually_cosparse_open_eq)

lemma zorder_eq:
  assumes z: "z \<notin> \<Lambda>"
  shows   "zorder g z = 
             (\<Sum>w\<in>A. if rel z w \<or> rel z (-w) then if 2*w \<in> \<Lambda> then 2 * h w else h w else 0)"
proof -
  have [simp]: "w \<notin> \<Lambda>" if "w \<in> A" for w
    using no_lattice_points that by blast

  have "zorder g z = (\<Sum>x\<in>A. zorder (\<lambda>z. (\<wp> z - \<wp> x) powi h x) z)"
    unfolding g_def
  proof (rule zorder_prod)
    show "\<forall>\<^sub>F z in at z. (\<Prod>x\<in>A. (\<wp> z - \<wp> x) powi h x) \<noteq> 0"
      using eventually_nonzero_at[of z] by (simp add: g_def)
  qed (auto intro!: meromorphic_intros)
  also have "\<dots> = (\<Sum>w\<in>A. if rel z w \<or> rel z (-w) then if 2*w \<in> \<Lambda> then 2 * h w else h w else 0)"
  proof (intro sum.cong refl)
    fix w assume "w \<in> A"
    have "zorder (\<lambda>z. (\<wp> z - \<wp> w) powi h w) z = h w * zorder (\<lambda>z. (\<wp> z - \<wp> w)) z"
    proof (cases "h w = 0")
      case [simp]: False
      have "\<forall>\<^sub>F z in at z. \<wp> z - \<wp> w \<noteq> 0"
        using eventually_nonzero_at[of z]
        by eventually_elim (use \<open>w \<in> A\<close> finite in \<open>auto simp: g_def\<close>)

      hence "\<exists>\<^sub>F z in at z. \<wp> z - \<wp> w \<noteq> 0"
        using eventually_frequently at_neq_bot by blast
      thus ?thesis
        by (intro zorder_power_int) (auto intro!: meromorphic_intros)
    qed auto
    also have "zorder (\<lambda>z. \<wp> z - \<wp> w) z =
                 (if rel z w \<or> rel z (-w) then if 2*w \<in> \<Lambda> then 2 else 1 else 0)"
      using zorder_weierstrass_fun_minus_const[of w z] z \<open>w \<in> A\<close> by simp
    also have "h w * \<dots> = (if rel z w \<or> rel z (-w) then if 2*w \<in> \<Lambda> then 2 * h w else h w else 0)"
      by auto
    finally show "zorder (\<lambda>z. (\<wp> z - \<wp> w) powi h w) z =  
                    (if rel z w \<or> rel z (-w) then if 2*w \<in> \<Lambda> then 2 * h w else h w else 0)" .
  qed
  finally show "zorder g z = (\<Sum>w\<in>A. if rel z w \<or> rel z (-w) then if 2*w \<in> \<Lambda> then 2 * h w else h w else 0)" .
qed

end


lemma (in even_elliptic_function) in_terms_of_weierstrass_fun_even_aux:
  assumes nontrivial: "\<not>eventually (\<lambda>z. f z = 0) (cosparse UNIV)"
  defines "Z \<equiv> {z\<in>half_fund_parallelogram - {0}. is_pole f z \<or> isolated_zero f z}"
  defines "h \<equiv> (\<lambda>z. if z \<in> Z then zorder f z div (if 2 * z \<in> \<Lambda> then 2 else 1) else 0)"
  obtains c where "eventually (\<lambda>z. f z = c * (\<Prod>w\<in>Z. (\<wp> z - \<wp> w) powi h w)) (cosparse UNIV)"
proof -
  define g where "g = (\<lambda>z. (\<Prod>w\<in>Z. (\<wp> z - \<wp> w) powi h w))"
  have [intro]: "finite Z"
  proof (rule finite_subset)
    show "Z \<subseteq> {z\<in>period_parallelogram 0. is_pole f z} \<union> {z\<in>period_parallelogram 0. isolated_zero f z}"
      using half_fund_parallelogram_subset_period_parallelogram by (auto simp: Z_def)
    show "finite ({z\<in>period_parallelogram 0. is_pole f z} \<union> {z\<in>period_parallelogram 0. isolated_zero f z})"
      by (intro finite_UnI finite_poles_in_parallelogram finite_zeros_in_parallelogram)
  qed
  have [simp]: "z \<notin> \<Lambda>" if "z \<in> Z" for z
    using that half_fund_parallelogram_in_lattice_iff[of z] unfolding Z_def by auto

  interpret g: elliptic_function_construct \<omega>1 \<omega>2 Z h g
    by unfold_locales (auto simp: g_def)

  have zorder_eq_aux: "zorder g z = zorder f z" if z: "z \<in> half_fund_parallelogram - \<Lambda>" for z
  proof -
    have "zorder g z = (\<Sum>w\<in>Z. if rel z w \<or> rel z (-w) then if 2*w \<in> \<Lambda> then 2 * h w else h w else 0)"
      by (rule g.zorder_eq) (use z in auto)
    also have "\<dots> = (\<Sum>w\<in>Z\<inter>{z}. if 2*w \<in> \<Lambda> then 2 * h w else h w)"
    proof (intro sum.mono_neutral_cong_right ballI)
      fix w assume w: "w \<in> Z - Z \<inter> {z}"
      thus "(if rel z w \<or> rel z (-w) then if 2 * w \<in> \<Lambda> then 2 * h w else h w else 0) = 0"
        using rel_in_half_fund_parallelogram_imp_eq[of z w] z by (auto simp: Z_def)
    qed auto
    also have "\<dots> = (if 2 * z \<in> \<Lambda> then 2 * h z else h z)"
      by (auto simp: h_def)
    also have "\<dots> = (if z \<in> Z then zorder f z else 0)"
      using even_zorder[of z] nontrivial by (auto simp: h_def)
    also have "\<dots> = zorder f z"
    proof (cases "z \<in> Z")
      case False
      hence "\<not>is_pole f z \<and> \<not>isolated_zero f z"
        using z by (auto simp: Z_def)
      moreover have "frequently (\<lambda>z. f z \<noteq> 0) (at z)"
        using nontrivial by (metis eventually_eq_imp_almost_everywhere_eq not_eventually)
      ultimately have "zorder f z = 0"
        by (intro not_pole_not_isolated_zero_imp_zorder_eq_0) (auto intro: meromorphic')
      thus ?thesis
        by simp
    qed auto
    finally show ?thesis .
  qed

  have zorder_eq: "zorder g z = zorder f z" if z: "z \<notin> \<Lambda>" for z
  proof -
    have "zorder g z = zorder g (to_half_fund_parallelogram z)"
      using g.zorder_to_half_fund_parallelogram by simp
    also have "\<dots> = zorder f (to_half_fund_parallelogram z)"
      by (rule zorder_eq_aux) (use z in auto)
    also have "\<dots> = zorder f z"
      using zorder_to_half_fund_parallelogram by simp
    finally show ?thesis .
  qed

  define h where "h = (\<lambda>z. f z / g z)"
  interpret h: elliptic_function \<omega>1 \<omega>2 h
    unfolding h_def by (intro elliptic_function_intros)

  have h_nonzero: "eventually (\<lambda>z. h z \<noteq> 0) (at z)" for z
  proof -
    have "eventually (\<lambda>z. f z \<noteq> 0) (at z)"
      using nontrivial frequently_def frequently_eq_imp_almost_everywhere_eq by blast
    thus ?thesis
      using g.eventually_nonzero_at by eventually_elim (auto simp: h_def)
  qed

  have zorder_h: "zorder h z = 0" if z: "z \<notin> \<Lambda>" for z
  unfolding h_def
  proof (subst zorder_divide)
    show "\<exists>\<^sub>F z in at z. f z \<noteq> 0"
      using nontrivial by (metis eventually_eq_imp_almost_everywhere_eq not_eventually)
    show "\<exists>\<^sub>F z in at z. g z \<noteq> 0"
      using eventually_frequently g.eventually_nonzero_at trivial_limit_at by blast
  qed (use z zorder_eq[of z] in \<open>auto intro!: meromorphic' g.meromorphic'\<close>)

  have zorder_h': "zorder h z = 0" if z: "z \<in> period_parallelogram 0" "z \<noteq> 0" for z
    by (rule zorder_h) (use z fund_period_parallelogram_in_lattice_iff[of z] in auto)

  have "elliptic_order h = 0"
  proof -
    have "elliptic_order h = (\<Sum>z\<in>(if is_pole h 0 then {0} else {}). nat (-zorder h z))"
      unfolding elliptic_order_def
      by (intro sum.mono_neutral_right h.finite_poles_in_parallelogram)
         (auto dest: zorder_h')
    also have "\<dots> = nat (-zorder h 0)"
      using zorder_neg_imp_is_pole[OF h.meromorphic', of 0] h_nonzero
            linorder_not_less[of "zorder h 0" 0] by auto
    finally have *: "elliptic_order h = nat (-zorder h 0)" .

    have "elliptic_order h = (\<Sum>z\<in>(if isolated_zero h 0 then {0} else {}). nat (zorder h z))"
      unfolding h.zeros_eq_elliptic_order[of 0, symmetric]
      by (intro sum.mono_neutral_right h.finite_zeros_in_parallelogram)
         (auto dest: zorder_h')
    also have "\<dots> = nat (zorder h 0)"
      using zorder_pos_imp_isolated_zero[OF h.meromorphic', of 0] h_nonzero
            linorder_not_less[of 0 "zorder h 0"] by auto
    finally have "elliptic_order h = nat (zorder h 0)" .
    with * show "elliptic_order h = 0"
      by simp
  qed
  then obtain c where c: "eventually (\<lambda>z. h z = c) (cosparse UNIV)"
    using h.elliptic_order_eq_0_iff_const_cosparse by blast
  moreover have "eventually (\<lambda>z. g z \<noteq> 0) (cosparse UNIV)"
    using g.nonzero_almost_everywhere by blast
  ultimately have "eventually (\<lambda>z. f z = c * g z) (cosparse UNIV)"
    by eventually_elim (auto simp: h_def)
  thus ?thesis
    using that[of c] unfolding g_def by blast
qed

text \<open>
  Finally, we show that any even elliptic function can be written as a rational function of $\wp$.
  This is Exercise~1.4 in Apostol's book.
\<close>
lemma (in even_elliptic_function) in_terms_of_weierstrass_fun_even:
  obtains p q :: "complex poly" where "q \<noteq> 0" "\<forall>\<^sub>\<approx>z. f z = poly p (\<wp> z) / poly q (\<wp> z)"
proof (cases "eventually (\<lambda>z. f z = 0) (cosparse UNIV)")
  case True
  thus ?thesis
    using that[of 1 0] by simp
next
  case False
  define Z where "Z = {z\<in>half_fund_parallelogram - {0}. is_pole f z \<or> isolated_zero f z}"
  define h where "h = (\<lambda>z. if z \<in> Z then zorder f z div (if 2 * z \<in> \<Lambda> then 2 else 1) else 0)"
  obtain c where *: "eventually (\<lambda>z. f z = c * (\<Prod>w\<in>Z. (\<wp> z - \<wp> w) powi h w)) (cosparse UNIV)"
    using False in_terms_of_weierstrass_fun_even_aux unfolding Z_def h_def by metis
  define p where "p = Polynomial.smult c (\<Prod>w\<in>{w\<in>Z. h w \<ge> 0}. [:-\<wp> w, 1:] ^ nat (h w))"
  define q where "q = (\<Prod>w\<in>{w\<in>Z. h w < 0}. [:-\<wp> w, 1:] ^ nat (-h w))"

  have finite: "finite Z"
  proof (rule finite_subset)
    show "Z \<subseteq> {z\<in>period_parallelogram 0. is_pole f z} \<union> {z\<in>period_parallelogram 0. isolated_zero f z}"
      using half_fund_parallelogram_subset_period_parallelogram by (auto simp: Z_def)
    show "finite ({z\<in>period_parallelogram 0. is_pole f z} \<union> {z\<in>period_parallelogram 0. isolated_zero f z})"
      by (intro finite_UnI finite_poles_in_parallelogram finite_zeros_in_parallelogram)
  qed

  show ?thesis
  proof (rule that[of q p])
    show "q \<noteq> 0"
      using finite by (auto simp: q_def)
  next
    show "\<forall>\<^sub>\<approx>z. f z = poly p (\<wp> z) / poly q (\<wp> z)"
      using *
    proof eventually_elim
      case (elim z)
      have "f z = c * (\<Prod>w\<in>Z. (\<wp> z - \<wp> w) powi h w)"
        by (fact elim)
      also have "Z = {w\<in>Z. h w \<ge> 0} \<union> {w\<in>Z. h w < 0}"
        by auto
      also have "c * (\<Prod>w\<in>\<dots>. (\<wp> z - \<wp> w) powi h w) = 
                   c * (\<Prod>w\<in>{w\<in>Z. h w \<ge> 0}. (\<wp> z - \<wp> w) powi h w) *
                   (\<Prod>w\<in>{w\<in>Z. h w < 0}. (\<wp> z - \<wp> w) powi h w)"
        by (subst prod.union_disjoint) (use finite in auto)
      also have "(\<Prod>w\<in>{w\<in>Z. h w \<ge> 0}. (\<wp> z - \<wp> w) powi h w) =
                 (\<Prod>w\<in>{w\<in>Z. h w \<ge> 0}. poly [:-\<wp> w, 1:] (\<wp> z) ^ (nat (h w)))"
        by (intro prod.cong) (auto simp: power_int_def)
      also have "c * \<dots> = poly p (\<wp> z)"
        by (simp add: p_def poly_prod)
      also have "(\<Prod>w\<in>{w\<in>Z. h w < 0}. (\<wp> z - \<wp> w) powi h w) =
                 (\<Prod>w\<in>{w\<in>Z. h w < 0}. inverse (poly [:-\<wp> w, 1:] (\<wp> z) ^ (nat (-h w))))"
        by (intro prod.cong) (auto simp: power_int_def field_simps)
      also have "\<dots> = inverse (poly q (\<wp> z))"
        unfolding q_def poly_prod by (subst prod_inversef [symmetric]) auto
      finally show ?case
        by (simp add: field_simps)
    qed
  qed
qed

text \<open>
  From this, we now show that any elliptic function $f$ can be written in the form
  $f(z) = g(\wp(z)) + \wp'(z) h(\wp(z))$ where $g, h$ are rational functions.

  The proof is fairly simple: We can split $f(z)$ into a sum $f(z) = f_1(z) + f_2(z)$ where
  $f_1$ is even and $f_2$ is odd by defining $f_1(z) = \frac{1}{2} (f(z) + f(-z))$ and
  $f_2(z) = \frac{1}{2} (f(z) - f(-z))$. We can then further define $f_3(z) = f_2(z) / \wp'(z)$ so
  that $f_3$ is also even.

  By our previous result, we know that $f_1$ and $f_3$ can be written as rational functions of
  $\wp$, so by combining everything we get the result we want.

  This result is Exercise~1.5 in Apostol's book.
\<close>
theorem (in even_elliptic_function) in_terms_of_weierstrass_fun:
  obtains p q r s :: "complex poly" where "q \<noteq> 0" "s \<noteq> 0"
     "\<forall>\<^sub>\<approx>z. f z = poly p (\<wp> z) / poly q (\<wp> z) + \<wp>' z * poly r (\<wp> z) / poly s (\<wp> z)"
proof -
  define f1 where "f1 = (\<lambda>z. (f z + f (-z)) / 2)"
  define f2 where "f2 = (\<lambda>z. (f z - f (-z)) / 2)"
  define f2' where "f2' = (\<lambda>z. f2 z / \<wp>' z)"

  note [elliptic_function_intros] = elliptic_function_compose_uminus[OF elliptic_function_axioms]

  interpret f1: elliptic_function \<omega>1 \<omega>2 f1
    unfolding f1_def by (intro elliptic_function_intros)
  interpret f1: even_elliptic_function \<omega>1 \<omega>2 f1
    by standard (auto simp: f1_def)
  obtain p q where pq: "q \<noteq> 0" "\<forall>\<^sub>\<approx>z. f1 z = poly p (\<wp> z) / poly q (\<wp> z)"
    using f1.in_terms_of_weierstrass_fun_even .

  interpret f2': elliptic_function \<omega>1 \<omega>2 f2'
    unfolding f2'_def f2_def by (intro elliptic_function_intros)
  interpret f2': even_elliptic_function \<omega>1 \<omega>2 f2'
    by standard (auto simp: f2'_def f2_def divide_simps)
  obtain r s where rs: "s \<noteq> 0" "\<forall>\<^sub>\<approx>z. f2' z = poly r (\<wp> z) / poly s (\<wp> z)"
    using f2'.in_terms_of_weierstrass_fun_even .

  have "eventually (\<lambda>z. \<wp>' z \<noteq> 0) (cosparse UNIV)"
    by (simp add: weierstrass_fun_deriv.avoid)
  with pq(2) and rs(2) have "\<forall>\<^sub>\<approx>z. f z = poly p (\<wp> z) / poly q (\<wp> z) + \<wp>' z * poly r (\<wp> z) / poly s (\<wp> z)"
  proof eventually_elim
    case (elim z)
    have "poly p (\<wp> z) / poly q (\<wp> z) + \<wp>' z * poly r (\<wp> z) / poly s (\<wp> z) =
          f1 z + \<wp>' z * (poly r (\<wp> z) / poly s (\<wp> z))"
      unfolding elim(1) by (simp add: divide_simps)
    also have "poly r (\<wp> z) / poly s (\<wp> z) = f2' z"
      using elim(2) by simp
    also have "\<wp>' z * f2' z = f2 z"
      using elim(3) by (simp add: f2'_def)
    also have "f1 z + f2 z = f z"
      by (simp add: f1_def f2_def field_simps)
    finally show ?case ..
  qed
  thus ?thesis
    using that[of q s p r] pq(1) rs(1) by simp
qed

end