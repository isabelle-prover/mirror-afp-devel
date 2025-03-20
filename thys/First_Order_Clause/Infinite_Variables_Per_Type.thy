theory Infinite_Variables_Per_Type
  imports
    "HOL-Library.Countable_Set"
    "HOL-Cardinals.Cardinals"
    Fresh_Identifiers.Fresh
    Collect_Extra
begin

lemma infinite_prods:
  assumes "infinite (UNIV :: 'a set)"
  shows "infinite {p :: 'a \<times> 'a. fst p = x}"
proof -
  have "{p :: 'a \<times> 'a . fst p = x} = {x} \<times> UNIV"
    by auto

  then show ?thesis
    using finite_cartesian_productD2 assms
    by auto
qed

lemma surj_infinite_set: "surj g \<Longrightarrow> infinite {x. f x = \<tau>} \<Longrightarrow> infinite {x. f (g x) = \<tau>}"
  by (smt (verit) UNIV_I finite_imageI image_iff mem_Collect_eq rev_finite_subset subset_eq)

definition infinite_variables_per_type_on :: "'var set \<Rightarrow> ('var \<Rightarrow> 'ty) \<Rightarrow> bool" where
  "infinite_variables_per_type_on X \<V> \<equiv> \<forall>\<tau> \<in> \<V> ` X. infinite {x. \<V> x = \<tau>}"

abbreviation infinite_variables_per_type :: "('var \<Rightarrow> 'ty) \<Rightarrow> bool" where
  "infinite_variables_per_type \<equiv> infinite_variables_per_type_on UNIV"

lemma obtain_type_preserving_inj:
  fixes \<V> :: "'v \<Rightarrow> 'ty"
  assumes
    finite_X: "finite X" and
    \<V>: "infinite_variables_per_type \<V>"
  obtains f :: "'v \<Rightarrow> 'v" where
    "inj f"
    "X \<inter> f ` Y = {}"
    "\<forall>x \<in> Y. \<V> (f x) = \<V> x"
proof (rule that)

  {
    fix \<tau>
    assume "\<tau> \<in> range \<V>"

    then have "|{x. \<V> x = \<tau>}| =o |{x. \<V> x = \<tau> } - X|"
      using \<V> finite_X card_of_infinite_diff_finite ordIso_symmetric
      unfolding infinite_variables_per_type_on_def
      by blast

    then have "|{x. \<V> x = \<tau>}| =o |{x. \<V> x = \<tau> \<and> x \<notin> X}|"
      using set_diff_eq[of _ X]
      by auto

    then have "\<exists>g. bij_betw g {x. \<V> x = \<tau>} {x. \<V> x = \<tau> \<and> x \<notin> X}"
      using card_of_ordIso someI
      by blast
  }
  note exists_g = this

  define get_g where
    "\<And>\<tau>. get_g \<tau> \<equiv> SOME g. bij_betw g {x. \<V> x = \<tau>} {x. \<V> x = \<tau> \<and> x \<notin> X}"

  define f where
    "\<And>x. f x \<equiv> get_g (\<V> x) x"

  {
    fix y

    have "\<And>g. bij_betw g {x. \<V> x = \<V> y} {x. \<V> x = \<V> y \<and> x \<notin> X} \<Longrightarrow> g y \<in> {x. \<V> x = \<V> y \<and> x \<notin> X}"
      using exists_g bij_betwE
      by blast

    then have "f y \<in> {x. \<V> x = \<V> y \<and> x \<notin> X}"
      using exists_g get_g_def
      unfolding f_def 
      by (metis (no_types, lifting) ext rangeI verit_sko_ex')     
  }

  then show "X \<inter> f ` Y = {}"  "\<forall>y\<in>Y. \<V> (f y) = \<V> y"
    unfolding f_def
    by auto

  show "inj f"
  proof (unfold inj_def, intro allI impI)
    fix x y
    assume "f x = f y"

    then show "x = y"
      using get_g_def f_def exists_g
      unfolding some_eq_ex[symmetric]
      by (smt (verit) bij_betw_iff_bijections mem_Collect_eq rangeI)
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

lemma obtain_infinite_variables_per_type_on:
  assumes 
    infinite_UNIV: "infinite (UNIV :: 'v set)" and 
    finite_Y: "finite Y" and (* Could be made weaker: infinite (UNIV - Y) *)
    finite_Z: "finite Z" and (* Could be made weaker: infinite (UNIV - Z) *)
    disjoint: "Y \<inter> Z = {}"
  obtains \<V> :: "'v \<Rightarrow> 'ty"
  where "infinite_variables_per_type_on X \<V>" "\<forall>x \<in> Y. \<V> x = \<V>' x" "\<forall>x \<in> Z. \<V> x = \<V>'' x"
proof (cases "X = {}")
  case True
  define \<V> where "\<And>x. \<V> x \<equiv> if x \<in> Y then \<V>' x else \<V>'' x"

  show ?thesis
  proof (rule that[unfolded True])

    show "\<forall>x\<in>Y. \<V> x = \<V>' x"
      unfolding \<V>_def
      by simp
  next

    show "\<forall>x\<in>Z. \<V> x = \<V>'' x"
      using disjoint
      unfolding \<V>_def
      by auto
  qed (auto simp: infinite_variables_per_type_on_def)
next
  case False

  obtain g :: "'v \<Rightarrow> 'v \<times> 'v" where bij_g: "bij g"
    using Times_same_infinite_bij_betw_types bij_betw_inv infinite_UNIV 
    by blast

  define f :: "'v \<Rightarrow> 'v" where
    "\<And>x. f x \<equiv> if x \<in> Y \<union> Z then x else fst (g x)"

  define \<V> where "\<And>x. \<V> x \<equiv> if x \<in> Y then \<V>' x else \<V>'' x"

  {
    fix y

    have "{x. fst (g x) = y} = inv g ` {p. fst p = y}"
      by (smt (verit, ccfv_SIG) Collect_cong bij_g bij_image_Collect_eq bij_imp_bij_inv inv_inv_eq)

    then have "infinite {x. fst (g x) = y}"
      using infinite_prods[OF infinite_UNIV]
      by (metis bij_g bij_is_surj finite_imageI image_f_inv_f)

    then have "infinite {x. x \<notin> Y \<union> Z \<and> fst (g x) = y}"
      using finite_Y finite_Z
      unfolding Collect_not_mem_conj_eq
      by simp

    then have "infinite {x. f x = y}"
      unfolding f_def if_distrib if_distribR Collect_if_eq 
      by blast
  }

  then have \<V>_X: "\<forall>y \<in> \<V> ` f ` X. infinite {x. \<V> (f x) = y}"
    by (smt (verit, best) Collect_mono imageE rev_finite_subset)

  show ?thesis
  proof (rule that)

    show "infinite_variables_per_type_on X (\<V> \<circ> f)"
      using \<V>_X
      unfolding infinite_variables_per_type_on_def comp_def
      by (metis image_image)
  next

    show "\<forall>x\<in>Y. (\<V> \<circ> f) x = \<V>' x"
      unfolding f_def \<V>_def
      by auto
  next

    show "\<forall>x\<in>Z. (\<V> \<circ> f) x = \<V>'' x"
      using disjoint
      unfolding f_def \<V>_def
      by auto
  qed
qed

lemma obtain_infinite_variables_per_type_on':
  assumes infinite_UNIV: "infinite (UNIV :: 'v set)" and finite_Y: "finite Y" 
  obtains \<V> :: "'v \<Rightarrow> 'ty"
  where "infinite_variables_per_type_on X \<V>" "\<forall>x \<in> Y. \<V> x = \<V>' x"
  using obtain_infinite_variables_per_type_on[OF infinite_UNIV finite_Y, of "{}"]
  by auto

lemma obtain_infinite_variables_per_type_on'':
  assumes "finite Y"
  obtains \<V> :: "'v :: infinite \<Rightarrow> 'ty"
  where "infinite_variables_per_type_on X \<V>" "\<forall>x \<in> Y. \<V> x = \<V>' x"
  using obtain_infinite_variables_per_type_on'[OF infinite_UNIV assms].

lemma infinite_variables_per_type_on_subset: 
  "X \<subseteq> Y \<Longrightarrow> infinite_variables_per_type_on Y \<V> \<Longrightarrow> infinite_variables_per_type_on X \<V>"
  unfolding infinite_variables_per_type_on_def
  by blast

definition infinite_variables_for_all_types :: "('v \<Rightarrow> 'ty) \<Rightarrow> bool" where
  "infinite_variables_for_all_types \<V> \<equiv> \<forall>\<tau>. infinite {x. \<V> x = \<tau>}"

lemma exists_infinite_variables_for_all_types:
  assumes "|UNIV :: 'ty set| \<le>o |UNIV :: ('v :: infinite) set|"
  shows "\<exists>\<V> :: 'v \<Rightarrow> 'ty. infinite_variables_for_all_types \<V>"
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
      using infinite_prods[OF infinite_UNIV]
      by (metis bij_g bij_is_surj finite_imageI image_f_inv_f)
  }

  moreover obtain f' ::  "'v \<Rightarrow> 'ty" where "surj f'"
    using assms
    by (metis card_of_ordLeq2 empty_not_UNIV)

  ultimately have "\<And>y. infinite {x. f' (f x) = y}"
    by (smt (verit, ccfv_SIG) Collect_mono finite_subset surjD)

  then show ?thesis
    unfolding infinite_variables_for_all_types_def
    by meson
qed

lemma obtain_infinite_variables_for_all_types:
  assumes "|UNIV :: 'ty set| \<le>o |UNIV :: 'v set|"
  obtains \<V> :: "'v :: infinite \<Rightarrow> 'ty" where "infinite_variables_for_all_types \<V>"
  using exists_infinite_variables_for_all_types[OF assms]
  by blast

lemma infinite_variables_per_type_if_infinite_variables_for_all_types:
  "infinite_variables_for_all_types \<V> \<Longrightarrow> infinite_variables_per_type \<V>"
  unfolding infinite_variables_for_all_types_def infinite_variables_per_type_on_def
  by blast

end
