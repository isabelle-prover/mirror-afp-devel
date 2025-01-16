theory Infinite_Variables_Per_Type
  imports
    HOL_Extra
    "HOL-Library.Countable_Set" 
    "HOL-Cardinals.Cardinals"
    Fresh_Identifiers.Fresh
begin

lemma surj_infinite_set: "surj g \<Longrightarrow> infinite {x. f x = ty} \<Longrightarrow> infinite {x. f (g x) = ty}"
  by (smt (verit) UNIV_I finite_imageI image_iff mem_Collect_eq rev_finite_subset subset_eq)

definition infinite_variables_per_type where 
  "infinite_variables_per_type \<V> \<equiv> \<forall>ty. infinite {x. \<V> x = ty}"

lemma obtain_type_preserving_injs:
  fixes \<V>\<^sub>1 \<V>\<^sub>2 :: "'v \<Rightarrow> 'ty"
  assumes 
    infinite_UNIV: "infinite (UNIV :: 'v set)" and
    finite_X: "finite X" and
    \<V>\<^sub>2: "infinite_variables_per_type \<V>\<^sub>2"
  obtains f f' :: "'v \<Rightarrow> 'v" where
    "inj f" "inj f'"
    "f ` X \<inter> f' ` Y = {}"
    "\<forall>x \<in> X. \<V>\<^sub>1 (f x) = \<V>\<^sub>1 x"
    "\<forall>x \<in> Y. \<V>\<^sub>2 (f' x) = \<V>\<^sub>2 x"
proof
  have "\<And>ty. infinite ({x. \<V>\<^sub>2 x = ty} - X)"
    using \<V>\<^sub>2 finite_X
    unfolding infinite_variables_per_type_def
    by simp

  then have infinite: "\<And>ty. infinite {x. \<V>\<^sub>2 x = ty \<and> x \<notin> X}"
    by (simp add: set_diff_eq)

  have "\<And>ty. |{x. \<V>\<^sub>2 x = ty}| =o |{x. \<V>\<^sub>2 x = ty } - X|"
    using \<V>\<^sub>2 finite_X card_of_infinite_diff_finite ordIso_symmetric
    unfolding infinite_variables_per_type_def
    by blast

  then have "\<And>ty. |{x. \<V>\<^sub>2 x = ty}| =o |{x. \<V>\<^sub>2 x = ty \<and> x \<notin> X}|"
    using set_diff_eq[of _ X]
    by auto

  then have exists_g': "\<And>ty. \<exists>g'. bij_betw g' {x. \<V>\<^sub>2 x = ty} {x. \<V>\<^sub>2 x = ty \<and> x \<notin> X}"
    using card_of_ordIso someI 
    by blast

  define get_g' where
    "\<And>ty. get_g' ty \<equiv> SOME g'. bij_betw g' {x. \<V>\<^sub>2 x = ty} {x. \<V>\<^sub>2 x = ty \<and> x \<notin> X}"

  define f' where
    "\<And>x. f' x \<equiv> get_g' (\<V>\<^sub>2 x) x"

  define f :: "'v \<Rightarrow> 'v" where "f = id"

  moreover have "\<And>y. y \<in> Y \<Longrightarrow> \<exists>g'. bij_betw g' {x. \<V>\<^sub>2 x = \<V>\<^sub>2 y} {x. \<V>\<^sub>2 x = \<V>\<^sub>2 y \<and> x \<notin> X}"
    using exists_g'
    by simp

  moreover then have 
    "\<And>y. y \<in> Y \<Longrightarrow>
      (\<And> g'. ((bij_betw g' {x. \<V>\<^sub>2 x = \<V>\<^sub>2 y} {x. \<V>\<^sub>2 x = \<V>\<^sub>2 y \<and> x \<notin> X})
         \<Longrightarrow> (g' y \<in> {x. \<V>\<^sub>2 x = \<V>\<^sub>2 y \<and> x \<notin> X})))"
    using bij_betwE 
    by blast

  ultimately have ys: "\<And>y. y \<in> Y \<Longrightarrow> f' y \<in> {x. \<V>\<^sub>2 x = \<V>\<^sub>2 y \<and> x \<notin> X}" 
    unfolding f'_def get_g'_def
    by (smt (verit, ccfv_threshold) someI)

  then have "\<And>y. y\<in>Y \<Longrightarrow> f' y \<notin> X"
    by simp

  then show "f ` X \<inter> f' ` Y = {}"
    unfolding f_def
    by auto  

  show "\<forall>y\<in>Y. \<V>\<^sub>2 (f' y) = \<V>\<^sub>2 y"
    using ys
    by simp

  show "\<forall>x\<in>X. \<V>\<^sub>1 (f x) = \<V>\<^sub>1 x"
    unfolding f_def
    by simp

  show "inj f"
    unfolding f_def
    by simp

  have "\<And>x y. f' x = f' y \<Longrightarrow> \<V>\<^sub>2 y = \<V>\<^sub>2 x"
    using f'_def get_g'_def someI_ex[OF exists_g'] bij_betw_iff_bijections mem_Collect_eq
    by (smt (verit))

  then have "\<And>x y. f' x = f' y \<Longrightarrow> x = y"
    using f'_def get_g'_def exists_g' someI bij_betw_iff_bijections mem_Collect_eq some_eq_ex
    by (smt (z3))

  then show "inj f'"
    unfolding inj_def
    by simp  
qed

lemma exists_infinite_variables_per_type:
  assumes "|UNIV :: 'ty set| \<le>o |UNIV :: ('v :: infinite) set|"
  shows "\<exists>\<V> :: ('v :: infinite \<Rightarrow> 'ty). infinite_variables_per_type \<V>"
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
    unfolding infinite_variables_per_type_def
    by meson
qed

end
