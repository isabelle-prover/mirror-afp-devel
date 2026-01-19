section \<open>Preliminary Results\<close>

theory Poly_Lemmas
  imports
    "HOL-Computational_Algebra.Polynomial"
    "Polynomial_Interpolation.Missing_Polynomial"
begin

text "Taken from Budan-Fourier.BF-Misc"
lemma order_linear[simp]: "order x [:-y, 1:] = (if x=y then 1 else 0)"
  by (auto simp add:order_power_n_n[where n=1,simplified] order_0I)

subsection "On Polynomial Roots"

lemma proots_empty: "proots p = {#} \<longleftrightarrow> p = 0 \<or> (\<forall>x. poly p x \<noteq> 0)"
proof standard
  show "proots p = {#} \<Longrightarrow> p = 0 \<or> (\<forall>x. poly p x \<noteq> 0)"
    using order_root count_empty count_proots by metis
next
  have "(\<forall>x. poly p x \<noteq> 0) \<Longrightarrow> proots p = {#}"
    by (simp add: multiset_eqI order_root)
  then show "p = 0 \<or> (\<forall>x. poly p x \<noteq> 0) \<Longrightarrow> proots p = {#}"
    by auto
qed

lemma proots_element: "x \<in># proots p \<or> p = 0 \<longleftrightarrow> poly p x = 0"
  by (cases "p = 0") auto

lemma proots_diff:
  assumes "p \<noteq> 0" "q \<noteq> 0"
  shows "set_mset (proots p - proots q) = {x. order x p > order x q}" (is "?L = ?R")
proof -
  have "?L = {x. count (proots p) x > count (proots q) x}"
    by (rule set_mset_diff)
  also have "\<dots> = ?R"
    using count_proots assms by simp
  finally show ?thesis by simp
qed

subsection \<open>On @{term "rsquarefree"}\<close>

text \<open>The following fact is an improved version of @{thm "rsquarefree_root_order"}, 
which does not require the assumption that @{term "p \<noteq> 0"}.\<close>

lemma rsquarefree_root_order': "rsquarefree p \<Longrightarrow> poly p x = 0 \<Longrightarrow> order x p = 1"
  using rsquarefree_root_order rsquarefree_def by auto

lemma rsquarefree_single_root[simp]: "rsquarefree [:-x,1:]"
proof -
  have "[:-x,1:] \<noteq> 0"
    by simp
  then show ?thesis
    unfolding rsquarefree_def by auto
qed

lemma rsquarefree_mul:
  assumes "rsquarefree p" "rsquarefree q"
    "\<forall> x. poly p x \<noteq> 0 \<or> poly q x \<noteq> 0"
  shows "rsquarefree(p * q)"
proof -
  have 11: "p \<noteq> 0" "q \<noteq> 0"
    using assms rsquarefree_def by auto
  then have 1: "p * q \<noteq> 0"
    by simp

  have "(\<forall>x. order x p = 0 \<or> order x p = 1)"
    "(\<forall>x. order x q = 0 \<or> order x q = 1)"
    using assms rsquarefree_def by auto
  then have 2: "(\<forall>x. order x (p * q) = 0 \<or> order x (p * q) = 1)"
    using 11 1 order_mult assms(3)
    by (metis comm_monoid_add_class.add_0 less_one order_gt_0_iff verit_sum_simplify)

  show ?thesis unfolding rsquarefree_def
    using 1 2  by auto
qed


subsection \<open>On Symmetric Differences\<close>

lemma card_sym_diff_finite:
  assumes "finite A" "finite B"
  shows "card (sym_diff A B) = card (A-B) + card (B-A)"
proof -
  have "(A-B) \<inter> (B-A) = {}"
    by blast
  then show ?thesis
    using assms card_Un_disjoint[of "(A-B)" "(B-A)"] by fast
qed

lemma card_add_diff_finite:
  assumes "finite A" "finite B"
  shows "card A + card (B-A) = card B + card (A-B)"
  using assms
proof -
  from assms have fi: "finite (A \<inter> B)"
    by simp

  have "card (B-A) = card B - card (A \<inter> B)"
    using fi card_Diff_subset_Int by (metis inf_commute)
  also have "card (A-B) = card A - card (A \<inter> B)"
    using fi card_Diff_subset_Int by blast
  moreover have "card A + (card B - card (A \<inter> B)) = card B + (card A - card (A \<inter> B))"
    using assms by (metis Nat.diff_add_assoc add.commute card_mono inf.cobounded1 inf.cobounded2)
  ultimately show ?thesis by argo
qed

lemma card_sub_int_diff_finite:
  assumes "finite A" "finite B"
  shows "int (card A) - card B = int (card (A-B)) - card (B-A)"
  using assms card_add_diff_finite by fastforce

lemma card_sub_int_diff_finite_real:
  assumes "finite A" "finite B"
  shows "real (card A) - card B = real (card (A-B)) - card (B-A)"
  using assms card_add_diff_finite by fastforce

subsection \<open>Characteristic Polynomial\<close>

text \<open>The characteristic polynomial associated to a set:\<close>
definition set_to_poly :: "'a::finite_field set \<Rightarrow> 'a poly" where
  "set_to_poly A \<equiv> \<Prod> a \<in> A. [:-a,1:]"

lemma set_to_poly_correct: "{x. poly (set_to_poly A) x = 0} = A"
proof (induct A rule: infinite_finite_induct)
  case (infinite A)
  then show ?case by simp
next
  case empty
  then show ?case unfolding set_to_poly_def by simp
next
  case (insert x F)
  have "set_to_poly (insert x F) = set_to_poly F * [:-x,1:]"
    unfolding set_to_poly_def by (simp add: insert.hyps(2))
  also have "{xa. poly (set_to_poly F * [:-x,1:]) xa = 0} =
      {xa. poly (set_to_poly F) xa = 0} \<union> {xa. poly ([:-x,1:]) xa = 0}"
    by auto
  moreover have 2: "{xa. poly (set_to_poly F) xa = 0} = F"
    by (simp add: insert.hyps(3))
  moreover have 3: "{xa. poly ([:-x,1:]) xa = 0} = {x}"
    by auto
  ultimately have "{xa. poly (set_to_poly (insert x F)) xa = 0} = F \<union> {x}"
     by simp
  then show ?case by simp
qed

lemma in_set_to_poly: "poly (set_to_poly A) x = 0 \<longleftrightarrow> x \<in> A"
  using set_to_poly_correct
  by auto

lemma set_to_poly_not0[simp]: "set_to_poly A \<noteq> 0"
  unfolding set_to_poly_def by auto

lemma set_to_poly_empty[simp]: "set_to_poly {} = 1"
  unfolding set_to_poly_def by simp

lemma set_to_poly_inj: "inj set_to_poly"
  by (metis injI set_to_poly_correct)

lemma rsquarefree_set_to_poly: "rsquarefree (set_to_poly A)"
proof (induct A rule: infinite_finite_induct)
  case (infinite A)
  then show ?case by simp
next
  case empty
  then show ?case
    by (simp add: rsquarefree_def set_to_poly_def)
next
  case (insert x F)
  then have 1: "set_to_poly (insert x F) = set_to_poly F * [:-x,1:]"
    by (simp add: set_to_poly_def)

  have "rsquarefree [:-x,1:]"
    using rsquarefree_single_root by simp
  also have "poly (set_to_poly F) x \<noteq> 0"
    using insert by (simp add: in_set_to_poly)
  moreover have "poly ([:-x,1:]) x = 0"
    using insert by simp
  ultimately have "rsquarefree( set_to_poly F * [:-x,1:])"
    using insert(3) rsquarefree_mul by fastforce

  then show ?case using 1
    by simp
qed

lemma set_to_poly_insert:
  assumes"x \<notin> A"
  shows "set_to_poly (insert x A) = set_to_poly A * [:-x,1:]"
  using assms set_to_poly_def by (simp add: set_to_poly_def)

lemma set_to_poly_mult: "set_to_poly X * set_to_poly Y = set_to_poly (X \<union> Y) * set_to_poly (X \<inter> Y)"
  by (simp add: prod.union_inter set_to_poly_def)

lemma set_to_poly_mult_distinct:
  assumes "X \<inter> Y = {}"
  shows "set_to_poly X * set_to_poly Y = set_to_poly (X \<union> Y)"
  by (simp add: set_to_poly_mult assms)

lemma set_to_poly_degree:
  "degree (set_to_poly A) = card A"
proof (induct A rule: infinite_finite_induct)
  case (infinite A)
  then show ?case by auto
next
  case empty
  then show ?case by auto
next
  case (insert x F)
  have "[:-x, 1:] \<noteq> 0" and "set_to_poly F \<noteq> 0"
    using set_to_poly_not0 by auto
  then have "degree (set_to_poly F * [:-x, 1:]) = degree (set_to_poly F) + degree [:-x, 1:]"
    using degree_mult_eq by blast
  also have "set_to_poly (insert x F) = set_to_poly F * [:-x, 1:]"
    using insert set_to_poly_insert by simp
  ultimately show ?case using insert
    by simp
qed

lemma set_to_poly_order:
  "order x (set_to_poly A) = (if x \<in> A then 1 else 0)"
proof (cases "x \<in> A")
  case True
  then show ?thesis
    by (simp add: in_set_to_poly rsquarefree_root_order' rsquarefree_set_to_poly)
next
  case False
  then show ?thesis using in_set_to_poly order_root
    by auto
qed

lemma set_to_poly_lead_coeff: "lead_coeff (set_to_poly A) = 1"
proof (induct A rule: infinite_finite_induct)
  case (infinite A)
  then show ?case by auto
next
  case empty
  then show ?case by auto
next
  case (insert x A)
  then have ins: "set_to_poly (insert x A) = set_to_poly A * [:-x,1:] "
    unfolding set_to_poly_def by simp
  then show ?case
    unfolding ins lead_coeff_mult using insert by simp
qed

lemma degree_sub_lead_coeff:
  assumes "degree p > 0"
  shows "degree (p - monom (lead_coeff p) (degree p)) < degree p"
  using assms by (simp add: coeff_eq_0 degree_lessI)

lemma remove_lead_from_monic:
  fixes p q :: "'a :: field poly"
  assumes "monic p"
  assumes "degree p > 0"
  shows "degree (p - monom 1 (degree p)) < degree p"
  using degree_sub_lead_coeff[OF assms(2)] assms(1) by simp

lemma poly_eqI_degree_monic:
  fixes p q :: "'a :: field poly"
  assumes "degree p = degree q"
  assumes "degree p \<le> card A"
  assumes "monic p" "monic q"
  assumes "\<And>x. x \<in> A \<Longrightarrow> poly p x = poly q x"
  shows "p = q"
proof (cases "degree p > 0")
  case True
  have "degree (p - monom 1 (degree p)) < card A"
    using remove_lead_from_monic[OF assms(3)] True assms(2) by simp
  moreover have "degree (q - monom 1 (degree q)) < card A"
    using remove_lead_from_monic[OF assms(4)] True assms(1,2) by simp
  ultimately have "p - monom 1 (degree p) = q - monom 1 (degree q)"
    using assms(1,5) by (intro poly_eqI_degree[of A]) auto
  thus ?thesis using assms(1) by simp
next
  case False
  hence "degree p = 0" "degree q = 0" using assms(1) by auto
  thus "p = q" using assms(3,4) monic_degree_0 by blast
qed

end
