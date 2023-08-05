section \<open>Accuracy with cutoff\label{sec:accuracy}\<close>

text \<open>This section verifies that each of the $l$ estimate have the required accuracy with high
probability assuming as long as the cutoff is below @{term "q_max"}, generalizing the result from
Section~\ref{sec:accuracy_wo_cutoff}.\<close>

theory Distributed_Distinct_Elements_Accuracy
  imports
    Distributed_Distinct_Elements_Accuracy_Without_Cutoff
    Distributed_Distinct_Elements_Cutoff_Level
begin

unbundle intro_cong_syntax

lemma (in semilattice_set) Union:
  assumes "finite I" "I \<noteq> {}"
  assumes "\<And>i. i \<in> I \<Longrightarrow> finite (Z i)"
  assumes "\<And>i. i \<in> I \<Longrightarrow> Z i \<noteq> {}"
  shows "F (\<Union> (Z ` I)) = F ((\<lambda>i. (F (Z i))) ` I)"
  using assms(1,2,3,4)
proof (induction I rule:finite_ne_induct)
  case (singleton x)
  then show ?case by simp
next
  case (insert x I)
  have "F (\<Union> (Z ` insert x I)) = F ((Z x) \<union> (\<Union> (Z ` I)))"
    by simp
  also have "... = f (F (Z x)) (F (\<Union> (Z ` I)))"
    using insert by (intro union finite_UN_I) auto
  also have "... = f (F {F (Z x)}) (F ((\<lambda>i. F (Z i)) ` I))"
    using insert(5,6) by (subst insert(4)) auto
  also have "... = F ({F (Z x)} \<union> (\<lambda>i. F (Z i)) ` I)"
    using insert(1,2) by (intro union[symmetric] finite_imageI) auto
  also have "... = F ((\<lambda>i. F (Z i)) ` insert x I)"
    by simp
  finally show ?case by simp
qed

text \<open>This is similar to the existing @{thm [source] hom_Max_commute} with the crucial difference
that it works even if the function is a homomorphism between distinct lattices.
An example application is @{term "Max (int ` A) = int (Max A)"}.\<close>

lemma hom_Max_commute':
  assumes "finite A" "A \<noteq> {}"
  assumes "\<And>x y. x \<in> A \<Longrightarrow> y \<in> A \<Longrightarrow> max (f x) (f y) = f (max x y)"
  shows "Max (f ` A) = f (Max A)"
  using assms by (induction A rule:finite_ne_induct) auto

context inner_algorithm_fix_A
begin

definition t\<^sub>c
  where "t\<^sub>c \<psi> \<sigma> = (Max ((\<lambda>j. \<tau>\<^sub>1 \<psi> A \<sigma> j + \<sigma>) ` {..<b})) - b_exp + 9"

definition s\<^sub>c (* tilde t *)
  where "s\<^sub>c \<psi> \<sigma> = nat (t\<^sub>c \<psi> \<sigma>)"

definition p\<^sub>c (* tilde p *)
  where "p\<^sub>c \<psi> \<sigma> = card {j\<in> {..<b}. \<tau>\<^sub>1 \<psi> A \<sigma> j + \<sigma> \<ge> s\<^sub>c \<psi> \<sigma>}"

definition Y\<^sub>c (* tilde A* *)
  where "Y\<^sub>c \<psi> \<sigma> = 2 ^ s\<^sub>c \<psi> \<sigma> * \<rho>_inv (p\<^sub>c \<psi> \<sigma>)"

lemma s\<^sub>c_eq_s:
  assumes "(f,g,h) \<in> sample_set \<Psi>"
  assumes "\<sigma> \<le> s f"
  shows "s\<^sub>c (f,g,h) \<sigma> = s f"
proof -
  have "int (Max (f ` A)) - int b_exp + 9 \<le> int (Max (f ` A)) - 26 + 9"
    using b_exp_ge_26 by (intro add_mono diff_left_mono) auto
  also have "... \<le> int (Max (f ` A))" by simp
  finally have 1:"int (Max (f ` A)) - int b_exp + 9 \<le> int (Max (f ` A))"
    by simp
  have "\<sigma> \<le> int (s f)" using assms(2) by simp
  also have "... = max 0 (t f)"
    unfolding s_def by simp
  also have "... \<le> max 0 (int (Max (f ` A)))"
    unfolding t_def using 1 by simp
  also have "... = int (Max (f ` A))"
    by simp
  finally have "\<sigma> \<le> int (Max (f ` A))"
    by simp
  hence 0: "int \<sigma> - 1 \<le> int (Max (f ` A))"
    by simp

  have c:"h \<in> sample_set (\<H> k (C\<^sub>7 * b\<^sup>2) [b]\<^sub>S)"
    using assms(1) sample_set_\<Psi> by auto
  hence h_range: "h x < b" for x
    using h_range_1 by simp

  have "(MAX j\<in>{..<b}. \<tau>\<^sub>1 (f, g, h) A \<sigma> j + int \<sigma>) =
    (MAX x\<in>{..<b}. Max ({int (f a) |a. a \<in> A \<and> h (g a) = x} \<union> {-1} \<union> {int \<sigma> -1}))"
    using fin_f[OF assms(1)] by (simp add:max_add_distrib_left max.commute \<tau>\<^sub>1_def)
  also have "... = Max (\<Union>x<b. {int (f a) |a. a \<in> A \<and> h (g a) = x} \<union> {- 1} \<union> {int \<sigma> - 1})"
    using fin_f[OF assms(1)] b_ne by (intro Max.Union[symmetric]) auto
  also have "... = Max ({int (f a) |a. a \<in> A} \<union> {- 1, int \<sigma> - 1})"
    using h_range by (intro arg_cong[where f="Max"]) auto
  also have "... = max (Max (int ` f ` A)) (int \<sigma> - 1)"
    using A_nonempty fin_A unfolding Setcompr_eq_image image_image
    by (subst Max.union) auto
  also have "... = max (int (Max (f ` A))) (int \<sigma> - 1)"
    using fin_A A_nonempty by (subst hom_Max_commute') auto
  also have "... = int (Max (f ` A))"
    by (intro max_absorb1 0)
  finally have "(MAX j\<in>{..<b}. \<tau>\<^sub>1 (f, g, h) A \<sigma> j + int \<sigma>) = Max (f ` A)" by simp

  thus ?thesis
    unfolding s\<^sub>c_def t\<^sub>c_def s_def t_def by simp
qed

lemma p\<^sub>c_eq_p:
  assumes "(f,g,h) \<in> sample_set \<Psi>"
  assumes "\<sigma> \<le> s f"
  shows "p\<^sub>c (f,g,h) \<sigma> = p (f,g,h)"
proof -
  have "{j \<in> {..<b}. int (s f) \<le> max (\<tau>\<^sub>0 (f, g, h) A j) (int \<sigma> - 1)} =
    {j \<in> {..<b}. int (s f) \<le> max (\<tau>\<^sub>0 (f, g, h) A j) (- 1)}"
    using assms(2) unfolding le_max_iff_disj by simp
  thus ?thesis
    unfolding p\<^sub>c_def p_def s\<^sub>c_eq_s[OF assms]
    by (simp add:max_add_distrib_left \<tau>\<^sub>1_def del:\<tau>\<^sub>0.simps)
qed

lemma Y\<^sub>c_eq_Y:
  assumes "(f,g,h) \<in> sample_set \<Psi>"
  assumes "\<sigma> \<le> s f"
  shows "Y\<^sub>c (f,g,h) \<sigma> = Y (f,g,h)"
  unfolding Y\<^sub>c_def Y_def s\<^sub>c_eq_s[OF assms] p\<^sub>c_eq_p[OF assms] by simp

lemma accuracy_single: "measure \<Psi> {\<psi>. \<exists>\<sigma> \<le> q_max. \<bar>Y\<^sub>c \<psi> \<sigma> - real X\<bar> > \<epsilon> * X} \<le> 1/2^4"
  (is "?L \<le> ?R")
proof -
  have "measure \<Psi> {\<psi>. \<exists>\<sigma> \<le> q_max. \<bar>Y\<^sub>c \<psi> \<sigma> - real X\<bar> > \<epsilon> * real X} \<le>
    measure \<Psi> {(f,g,h). \<bar>Y (f,g,h) - real X\<bar> >  \<epsilon> * real X \<or> s f < q_max}"
  proof (rule pmf_mono)
    fix \<psi>
    assume a:"\<psi> \<in> {\<psi>. \<exists>\<sigma>\<le>q_max. \<epsilon> * real X < \<bar>Y\<^sub>c \<psi> \<sigma> - real X\<bar>}"
    assume d:"\<psi> \<in> set_pmf (sample_pmf \<Psi>)"
    obtain \<sigma> where b:"\<sigma> \<le> q_max" and c:" \<epsilon> * real X < \<bar>Y\<^sub>c \<psi> \<sigma> - real X\<bar>"
      using a by auto
    obtain f g h where \<psi>_def: "\<psi> = (f,g,h)" by (metis prod_cases3)
    hence e:"(f,g,h) \<in> sample_set \<Psi>"
      using d unfolding sample_space_alt[OF sample_space_\<Psi>] by simp

    show "\<psi> \<in> {(f, g, h). \<epsilon> * real X < \<bar>Y (f, g, h) - real X\<bar> \<or> s f < q_max}"
    proof (cases "s f \<ge> q_max")
      case True
      hence f:"\<sigma> \<le> s f" using b by simp
      have "\<epsilon> * real X < \<bar>Y \<psi> - real X\<bar>"
        using Y\<^sub>c_eq_Y[OF e f] c unfolding \<psi>_def by simp
      then show ?thesis unfolding \<psi>_def by simp
    next
      case False
      then show ?thesis unfolding \<psi>_def by simp
    qed
  qed
  also have "... \<le> 1/2^4"
    using accuracy_without_cutoff by simp
  finally show ?thesis by simp
qed

lemma estimate1_eq:
  assumes "j < l"
  shows "estimate1 (\<tau>\<^sub>2 \<omega> A \<sigma>, \<sigma>) j = Y\<^sub>c (\<omega> j) \<sigma>" (is "?L = ?R")
proof -
  define t where "t = max 0 (Max ((\<tau>\<^sub>2 \<omega> A \<sigma> j) ` {..<b}) + \<sigma> - \<lfloor>log 2 b\<rfloor> + 9)"
  define p where "p = card { k. k \<in> {..<b} \<and> (\<tau>\<^sub>2 \<omega> A \<sigma> j k) + \<sigma> \<ge> t }"

  have 0: "int (nat x) = max 0 x" for x
    by simp
  have 1: "\<lfloor>log 2 b\<rfloor> = b_exp"
    unfolding b_def by simp

  have "b > 0"
    using b_min by simp
  hence 2: " {..<b} \<noteq> {}" by auto

  have "t = int (nat (Max ((\<tau>\<^sub>2 \<omega> A \<sigma> j) ` {..<b}) + \<sigma> - b_exp + 9))"
    unfolding t_def 0 1 by (rule refl)
  also have "... = int (nat (Max ((\<lambda>x. x + \<sigma>) ` (\<tau>\<^sub>2 \<omega> A \<sigma> j) ` {..<b}) - b_exp + 9))"
    by (intro_cong "[\<sigma>\<^sub>1 int,\<sigma>\<^sub>1 nat,\<sigma>\<^sub>2(+),\<sigma>\<^sub>2(-)]" more:hom_Max_commute) (simp_all add:2)
  also have "... = int (s\<^sub>c (\<omega> j) \<sigma>)"
    using assms
    unfolding s\<^sub>c_def t\<^sub>c_def \<tau>\<^sub>2_def image_image by simp
  finally have 3:"t = int (s\<^sub>c (\<omega> j) \<sigma>)"
    by simp

  have 4: "p = p\<^sub>c (\<omega> j) \<sigma>"
    using assms unfolding p_def p\<^sub>c_def 3 \<tau>\<^sub>2_def by simp

  have "?L = 2 powr t * ln (1-p/b) / ln(1-1/b)"
    unfolding estimate1.simps \<tau>_def \<tau>\<^sub>3_def
    by (simp only:t_def p_def Let_def)
  also have "... = 2 powr (s\<^sub>c (\<omega> j) \<sigma>) * \<rho>_inv p"
    unfolding 3 \<rho>_inv_def by (simp)
  also have "... = ?R"
    unfolding Y\<^sub>c_def 3 4 by (simp add:powr_realpow)
  finally show ?thesis
    by blast
qed

lemma estimate_result_1:
  "measure \<Omega> {\<omega>. (\<exists>\<sigma>\<le>q_max. \<epsilon>*X < \<bar>estimate (\<tau>\<^sub>2 \<omega> A \<sigma>,\<sigma>)-X\<bar>) } \<le> \<delta>/2" (is "?L \<le> ?R")
proof -
  define I :: "real set" where "I = {x. \<bar>x - real X\<bar> \<le> \<epsilon>*X}"

  define \<mu> where "\<mu> = measure \<Psi> {\<psi>. \<exists>\<sigma>\<le>q_max. Y\<^sub>c \<psi> \<sigma>\<notin>I}"

  have int_I: "interval I"
    unfolding interval_def I_def by auto

  have "\<mu> = measure \<Psi> {\<psi>. \<exists>\<sigma> \<le> q_max. \<bar>Y\<^sub>c \<psi> \<sigma> - real X\<bar> > \<epsilon> * X}"
    unfolding \<mu>_def I_def by (simp add:not_le)
  also have "... \<le>  1 / 2 ^ 4"
    by (intro accuracy_single)
  also have "... = 1/ 16"
    by simp
  finally have 1:"\<mu> \<le> 1 / 16" by simp

  have "(\<mu> + \<Lambda>) \<le> 1/16 + 1/16"
    unfolding \<Lambda>_def by (intro add_mono 1) auto
  also have "... \<le> 1/8"
    by simp
  finally have 2:"(\<mu> + \<Lambda>) \<le> 1/8"
    by simp

  hence 0: "(\<mu> + \<Lambda>) \<le> 1/2"
    by simp

  have "\<mu> \<ge> 0"
    unfolding \<mu>_def by simp
  hence 3: "\<mu> + \<Lambda> > 0"
    by (intro add_nonneg_pos \<Lambda>_gt_0)

  have "?L = measure \<Omega> {\<omega>. (\<exists>\<sigma>\<le>q_max. \<epsilon>*X < \<bar>median l (estimate1 (\<tau>\<^sub>2 \<omega> A \<sigma>,\<sigma>))-X\<bar>) }"
    by simp
  also have "... = measure \<Omega> {\<omega>. (\<exists>\<sigma>\<le>q_max. median l (estimate1 (\<tau>\<^sub>2 \<omega> A \<sigma>,\<sigma>)) \<notin> I)}"
    unfolding I_def by (intro measure_pmf_cong) auto
  also have "... \<le> measure \<Omega> {\<omega>. real(card{i\<in>{..<l}.(\<exists>\<sigma>\<le>q_max. Y\<^sub>c (\<omega> i) \<sigma>\<notin>I)})\<ge> real l/2}"
  proof (rule pmf_mono)
    fix \<omega>
    assume "\<omega> \<in> set_pmf \<Omega>" "\<omega> \<in> {\<omega>. \<exists>\<sigma>\<le>q_max. median l (estimate1 (\<tau>\<^sub>2 \<omega> A \<sigma>, \<sigma>)) \<notin> I}"
    then obtain \<sigma> where \<sigma>_def: "median l (estimate1 (\<tau>\<^sub>2 \<omega> A \<sigma>, \<sigma>)) \<notin> I" "\<sigma>\<le>q_max"
      by auto

    have "real l = 2 * real l - real l"
      by simp
    also have "... \<le> 2 * real l - 2 * card {i. i < l \<and> estimate1 (\<tau>\<^sub>2 \<omega> A \<sigma>, \<sigma>) i \<in> I}"
      using \<sigma>_def median_est[OF int_I, where n="l"] not_less
      by (intro diff_left_mono Nat.of_nat_mono) (auto simp del:estimate1.simps)
    also have "... = 2 * (real (card {..<l}) -card {i. i < l \<and> estimate1 (\<tau>\<^sub>2 \<omega> A \<sigma>, \<sigma>) i \<in> I})"
      by (simp del:estimate1.simps)
    also have "... = 2 * real (card {..<l} -card {i. i < l \<and> estimate1 (\<tau>\<^sub>2 \<omega> A \<sigma>, \<sigma>) i \<in> I})"
      by (intro_cong "[\<sigma>\<^sub>2 (*)]" more:of_nat_diff[symmetric] card_mono)
        (auto simp del:estimate1.simps)
    also have "... = 2 * real (card ({..<l} - {i. i < l \<and> estimate1 (\<tau>\<^sub>2 \<omega> A \<sigma>, \<sigma>) i \<in> I}))"
      by (intro_cong "[\<sigma>\<^sub>2 (*), \<sigma>\<^sub>1 of_nat]" more:card_Diff_subset[symmetric])
        (auto simp del:estimate1.simps)
    also have "... = 2 * real (card {i\<in>{..<l}. estimate1 (\<tau>\<^sub>2 \<omega> A \<sigma>, \<sigma>) i \<notin> I})"
      by (intro_cong "[\<sigma>\<^sub>2 (*), \<sigma>\<^sub>1 of_nat, \<sigma>\<^sub>1 card]") (auto simp del:estimate1.simps)
    also have "... = 2 * real (card {i \<in> {..<l}. Y\<^sub>c (\<omega> i) \<sigma> \<notin> I})"
      using estimate1_eq by (intro_cong "[\<sigma>\<^sub>2 (*), \<sigma>\<^sub>1 of_nat, \<sigma>\<^sub>1 card]" more:restr_Collect_cong) auto
    also have "... \<le> 2 * real (card {i \<in> {..<l}. (\<exists>\<sigma>\<le>q_max. Y\<^sub>c (\<omega> i) \<sigma> \<notin> I)})"
      using \<sigma>_def(2) by (intro mult_left_mono Nat.of_nat_mono card_mono) auto
    finally have "real l \<le> 2 * real (card {i \<in> {..<l}. (\<exists>\<sigma>\<le>q_max. Y\<^sub>c (\<omega> i) \<sigma> \<notin> I)})"
      by simp
    thus "\<omega> \<in> {\<omega>. real l/2 \<le> real (card {i \<in> {..<l}. \<exists>\<sigma>\<le>q_max. Y\<^sub>c (\<omega> i) \<sigma> \<notin> I})}"
      by simp
  qed
  also have "... = measure \<Omega> {\<omega>. real (card{i\<in>{..<l}. (\<exists>\<sigma>\<le>q_max. Y\<^sub>c (\<omega> i) \<sigma>\<notin>I)}) \<ge> (1/2)*real l}"
    unfolding sample_pmf_alt[OF \<Omega>.sample_space] p_def by simp
  also have "... \<le> exp (- real l * ((1/2) * ln (1 / (\<mu> + \<Lambda>)) - 2 * exp (- 1)))"
    using 0 unfolding \<mu>_def by (intro \<Omega>.tail_bound l_gt_0 \<Lambda>_gt_0) auto
  also have "... = exp (- (real l * ((1/2) * ln (1 / (\<mu> + \<Lambda>)) - 2 * exp (- 1))))"
    by simp
  also have "... \<le> exp (- (real l * ((1/2) * ln 8 - 2 * exp (- 1))))"
    using 2 3 l_gt_0 by (intro iffD2[OF exp_le_cancel_iff] le_imp_neg_le mult_left_mono diff_mono)
      (auto simp add:divide_simps)
  also have "... \<le> exp (- (real l * (1/4)))"
    by (intro iffD2[OF exp_le_cancel_iff] le_imp_neg_le mult_left_mono of_nat_0_le_iff)
     (approximation 5)
  also have "... \<le> exp (- (C\<^sub>6 * ln (2/ \<delta>)*(1/4)))"
    by (intro iffD2[OF exp_le_cancel_iff] le_imp_neg_le mult_right_mono l_lbound) auto
  also have "... = exp ( - ln (2/ \<delta>))"
    unfolding C\<^sub>6_def by simp
  also have "... = ?R"
    using \<delta>_gt_0 by (subst ln_inverse[symmetric]) auto
  finally show ?thesis
    by simp
qed

theorem estimate_result:
  "measure \<Omega> {\<omega>. \<bar>estimate (\<tau> \<omega> A)- X\<bar> >  \<epsilon> * X} \<le>  \<delta>"
  (is "?L \<le> ?R")
proof -
  let ?P = "measure \<Omega>"
  have "?L \<le> ?P {\<omega>. (\<exists>\<sigma>\<le>q_max.  \<epsilon>*real X<\<bar>estimate (\<tau>\<^sub>2 \<omega> A \<sigma>, \<sigma>)-real X\<bar>)\<or>q \<omega> A> q_max}"
    unfolding \<tau>_def \<tau>\<^sub>3_def not_le[symmetric]
    by (intro pmf_mono) auto
  also have "...\<le> ?P {\<omega>. (\<exists>\<sigma>\<le>q_max. \<epsilon>*real X<\<bar>estimate (\<tau>\<^sub>2 \<omega> A \<sigma>,\<sigma>)-X\<bar>)} + ?P {\<omega>. q \<omega> A> q_max}"
    by (intro pmf_add) auto
  also have "...\<le>  \<delta>/2 +  \<delta>/2"
    by (intro add_mono cutoff_level estimate_result_1)
  also have "... =  \<delta>"
    by simp
  finally show ?thesis
    by simp
qed

end

lemma (in inner_algorithm) estimate_result:
  assumes "A \<subseteq> {..<n}" "A \<noteq> {}"
  shows "measure \<Omega> {\<omega>. \<bar>estimate (\<tau> \<omega> A)- real (card A)\<bar> > \<epsilon> * real (card A)} \<le> \<delta>" (is "?L \<le> ?R")
proof -
  interpret inner_algorithm_fix_A
    using assms by unfold_locales auto
  have "?L = measure \<Omega> {\<omega>. \<bar>estimate (\<tau> \<omega> A)- X\<bar> > \<epsilon> * X}"
    unfolding X_def by simp
  also have "... \<le> ?R"
    by (intro estimate_result)
  finally show ?thesis
    by simp
qed

unbundle no_intro_cong_syntax

end