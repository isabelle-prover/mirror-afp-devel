section \<open>Preliminary Results\<close>

theory Poly_Lemmas
  imports
    "HOL-Computational_Algebra.Polynomial"
    "Polynomial_Interpolation.Missing_Polynomial"
begin

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
  by (simp add: in_set_to_poly order_0I rsquarefree_root_order rsquarefree_set_to_poly)

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
