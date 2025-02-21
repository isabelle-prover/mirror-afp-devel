theory Infinite_Variables_Per_Type
  imports
    "HOL-Library.Countable_Set"
    "HOL-Cardinals.Cardinals"
    Fresh_Identifiers.Fresh
begin

lemma infinite_prods:
  fixes x :: "'a :: infinite"
  shows "infinite {p :: 'a \<times> 'a. fst p = x}"
proof -
  have "{p :: 'a \<times> 'a . fst p = x} = {x} \<times> UNIV"
    by auto

  then show ?thesis
    using finite_cartesian_productD2 infinite_UNIV
    by auto
qed

lemma surj_infinite_set: "surj g \<Longrightarrow> infinite {x. f x = ty} \<Longrightarrow> infinite {x. f (g x) = ty}"
  by (smt (verit) UNIV_I finite_imageI image_iff mem_Collect_eq rev_finite_subset subset_eq)

definition infinite_variables_per_type :: "('v \<Rightarrow> 'ty) \<Rightarrow> bool" where
  "infinite_variables_per_type \<V> \<equiv> \<forall>ty. infinite {x. \<V> x = ty}"

lemma obtain_type_preserving_inj:
  fixes \<V> :: "'v \<Rightarrow> 'ty"
  assumes
    finite_X: "finite X" and
    \<V>: "infinite_variables_per_type \<V>"
  obtains f :: "'v \<Rightarrow> 'v" where
    "inj f"
    "X \<inter> f ` Y = {}"
    "\<forall>x \<in> Y. \<V> (f x) = \<V> x"
proof

  {
    fix ty

    have "|{x. \<V> x = ty}| =o |{x. \<V> x = ty } - X|"
      using \<V> finite_X card_of_infinite_diff_finite ordIso_symmetric
      unfolding infinite_variables_per_type_def
      by blast

    then have "|{x. \<V> x = ty}| =o |{x. \<V> x = ty \<and> x \<notin> X}|"
      using set_diff_eq[of _ X]
      by auto

    then have "\<exists>g. bij_betw g {x. \<V> x = ty} {x. \<V> x = ty \<and> x \<notin> X}"
      using card_of_ordIso someI
      by blast
  }
  note exists_g = this

  define get_g where
    "\<And>ty. get_g ty \<equiv> SOME g. bij_betw g {x. \<V> x = ty} {x. \<V> x = ty \<and> x \<notin> X}"

  define f where
    "\<And>x. f x \<equiv> get_g (\<V> x) x"

  {
    fix y

    have "\<And>g. bij_betw g {x. \<V> x = \<V> y} {x. \<V> x = \<V> y \<and> x \<notin> X} \<Longrightarrow> g y \<in> {x. \<V> x = \<V> y \<and> x \<notin> X}"
      using exists_g bij_betwE
      by blast

    then have "f y \<in> {x. \<V> x = \<V> y \<and> x \<notin> X}"
      using exists_g[of "\<V> y"]
      unfolding f_def get_g_def
      by (smt (verit, ccfv_threshold) someI)
  }

  then show "X \<inter> f ` Y = {}"  "\<forall>y\<in>Y. \<V> (f y) = \<V> y"
    by auto

  show "inj f"
  proof (unfold inj_def, intro allI impI)
    fix x y
    assume "f x = f y"

    then show "x = y"
      using get_g_def f_def exists_g
      unfolding some_eq_ex[symmetric]
      by (smt (verit, ccfv_threshold) someI mem_Collect_eq bij_betw_iff_bijections)
  qed
qed

lemma obtain_type_preserving_injs:
  fixes \<V>\<^sub>1 \<V>\<^sub>2 :: "'v \<Rightarrow> 'ty"
  assumes
    finite_X: "finite X" and
    \<V>\<^sub>2: "infinite_variables_per_type \<V>\<^sub>2"
  obtains f f' :: "'v \<Rightarrow> 'v" where
    "inj f" "inj f'"
    "f ` X \<inter> f' ` Y = {}"
    "\<forall>x \<in> X. \<V>\<^sub>1 (f x) = \<V>\<^sub>1 x"
    "\<forall>x \<in> Y. \<V>\<^sub>2 (f' x) = \<V>\<^sub>2 x"
proof-

  obtain f' where f':
    "inj f'"
    "X \<inter> f' ` Y = {}"
    "\<forall>x \<in> Y. \<V>\<^sub>2 (f' x) = \<V>\<^sub>2 x"
    using obtain_type_preserving_inj[OF assms] .

  show ?thesis
    by (rule that[of id f']) (auto simp: f')
qed

lemma obtain_type_preserving_injs':
  fixes \<V>\<^sub>1 \<V>\<^sub>2 :: "'v \<Rightarrow> 'ty"
  assumes
    finite_Y: "finite Y" and
    \<V>\<^sub>1: "infinite_variables_per_type \<V>\<^sub>1"
  obtains f f' :: "'v \<Rightarrow> 'v" where
    "inj f" "inj f'"
    "f ` X \<inter> f' ` Y = {}"
    "\<forall>x \<in> X. \<V>\<^sub>1 (f x) = \<V>\<^sub>1 x"
    "\<forall>x \<in> Y. \<V>\<^sub>2 (f' x) = \<V>\<^sub>2 x"
  using obtain_type_preserving_injs[OF assms]
  by (metis inf_commute)

lemma exists_infinite_variables_per_type:
  assumes "|UNIV :: 'ty set| \<le>o |UNIV :: ('v :: infinite) set|"
  shows "\<exists>\<V> :: 'v \<Rightarrow> 'ty. infinite_variables_per_type \<V>"
proof-
  obtain g :: "'v \<Rightarrow> 'v \<times> 'v" where bij_g: "bij g"
    using Times_same_infinite_bij_betw_types bij_betw_inv infinite_UNIV
    by blast

  define f :: "'v \<Rightarrow> 'v" where
    "\<And>x. f x \<equiv> fst (g x)"

  {
    fix y

    have "{x. fst (g x) = y} = inv g ` {p. fst p = y}"
      by (smt (verit, ccfv_SIG) Collect_cong bij_g bij_image_Collect_eq bij_imp_bij_inv inv_inv_eq)

    then have "infinite {x. f x = y}"
      unfolding f_def
      using infinite_prods
      by (metis bij_g bij_is_surj finite_imageI image_f_inv_f)
  }

  moreover obtain f' ::  "'v \<Rightarrow> 'ty" where "surj f'"
    using assms
    by (metis card_of_ordLeq2 empty_not_UNIV)

  ultimately have "\<And>y. infinite {x. f' (f x) = y}"
    by (smt (verit, ccfv_SIG) Collect_mono finite_subset surjD)

  then show ?thesis
    unfolding infinite_variables_per_type_def
    by meson
qed

lemma obtain_infinite_variables_per_type:
  assumes "|UNIV :: 'ty set| \<le>o |UNIV :: 'v set|"
  obtains \<V> :: "'v :: infinite \<Rightarrow> 'ty" where "infinite_variables_per_type \<V>"
  using exists_infinite_variables_per_type[OF assms]
  by blast

end
