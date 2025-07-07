section \<open>Miscelleanous missing theorems\<close>

theory Misc_Kraus_Maps
  imports
    Hilbert_Space_Tensor_Product.Hilbert_Space_Tensor_Product
    Hilbert_Space_Tensor_Product.Von_Neumann_Algebras
begin

unbundle cblinfun_syntax

lemma abs_summable_norm:
  assumes \<open>f abs_summable_on A\<close>
  shows \<open>(\<lambda>x. norm (f x)) abs_summable_on A\<close>
  using assms by simp

lemma abs_summable_on_add:
  assumes \<open>f abs_summable_on A\<close> and \<open>g abs_summable_on A\<close>
  shows \<open>(\<lambda>x. f x + g x) abs_summable_on A\<close>
proof -
  from assms have \<open>(\<lambda>x. norm (f x) + norm (g x)) summable_on A\<close>
    using summable_on_add by blast
  then show ?thesis
    apply (rule Infinite_Sum.abs_summable_on_comparison_test')
    using norm_triangle_ineq by blast
qed

lemma bdd_above_transform_mono_pos:
  assumes bdd: \<open>bdd_above ((\<lambda>x. g x) ` M)\<close>
  assumes gpos: \<open>\<And>x. x \<in> M \<Longrightarrow> g x \<ge> 0\<close>
  assumes mono: \<open>mono_on (Collect ((\<le>) 0)) f\<close>
  shows \<open>bdd_above ((\<lambda>x. f (g x)) ` M)\<close>
proof (cases \<open>M = {}\<close>)
  case True
  then show ?thesis
    by simp
next
  case False
  from bdd obtain B where B: \<open>g x \<le> B\<close> if \<open>x \<in> M\<close> for x
  by (meson bdd_above.unfold imageI)
  with gpos False have \<open>B \<ge> 0\<close>
    using dual_order.trans by blast
  have \<open>f (g x) \<le> f B\<close> if \<open>x \<in> M\<close> for x
    using mono _ _ B
    apply (rule mono_onD)
    by (auto intro!: gpos that  \<open>B \<ge> 0\<close>)
  then show ?thesis
    by fast
qed

lemma Ex_iffI:
  assumes \<open>\<And>x. P x \<Longrightarrow> Q (f x)\<close>
  assumes \<open>\<And>x. Q x \<Longrightarrow> P (g x)\<close>
  shows \<open>Ex P \<longleftrightarrow> Ex Q\<close>
  using assms(1) assms(2) by auto

lemma has_sum_Sigma'_banach:
  fixes A :: "'a set" and B :: "'a \<Rightarrow> 'b set"
    and f :: \<open>'a \<Rightarrow> 'b \<Rightarrow> 'c::banach\<close>
  assumes "((\<lambda>(x,y). f x y) has_sum S) (Sigma A B)"
  shows \<open>((\<lambda>x. infsum (f x) (B x)) has_sum S) A\<close>
  by (metis (no_types, lifting) assms has_sum_cong has_sum_imp_summable has_sum_infsum infsumI infsum_Sigma'_banach summable_on_Sigma_banach)

lemma infsum_Sigma_topological_monoid:
  fixes A :: "'a set" and B :: "'a \<Rightarrow> 'b set"
    and f :: \<open>'a \<times> 'b \<Rightarrow> 'c::{topological_comm_monoid_add, t3_space}\<close>
  assumes summableAB: "f summable_on (Sigma A B)"
  assumes summableB: \<open>\<And>x. x\<in>A \<Longrightarrow> (\<lambda>y. f (x, y)) summable_on (B x)\<close>
  shows "infsum f (Sigma A B) = (\<Sum>\<^sub>\<infinity>x\<in>A. \<Sum>\<^sub>\<infinity>y\<in>B x. f (x, y))"
proof -
  have 1: \<open>(f has_sum infsum f (Sigma A B)) (Sigma A B)\<close>
    by (simp add: assms)
  define b where \<open>b x = (\<Sum>\<^sub>\<infinity>y\<in>B x. f (x, y))\<close> for x
  have 2: \<open>((\<lambda>y. f (x, y)) has_sum b x) (B x)\<close> if \<open>x \<in> A\<close> for x
    using b_def assms(2) that by auto
  have 3: \<open>(b has_sum (\<Sum>\<^sub>\<infinity>x\<in>A. b x)) A\<close>
    using 1 2 by (metis has_sum_SigmaD infsumI)
  have 4: \<open>(f has_sum (\<Sum>\<^sub>\<infinity>x\<in>A. b x)) (Sigma A B)\<close>
    using 2 3 apply (rule has_sum_SigmaI)
    using assms by auto
  from 1 4 show ?thesis
    using b_def[abs_def] infsumI by blast
qed

lemma flip_eq_const: \<open>(\<lambda>y. y = x) = ((=) x)\<close>
  by auto

lemma sgn_ket[simp]: \<open>sgn (ket x) = ket x\<close>
  by (simp add: sgn_div_norm)

lemma tensor_op_in_tensor_vn:
  assumes \<open>a \<in> A\<close> and \<open>b \<in> B\<close>
  shows \<open>a \<otimes>\<^sub>o b \<in> A \<otimes>\<^sub>v\<^sub>N B\<close>
proof -
  have \<open>a \<otimes>\<^sub>o id_cblinfun \<in> A \<otimes>\<^sub>v\<^sub>N B\<close>
    by (metis (no_types, lifting) Un_iff assms(1) double_commutant_grows' image_iff tensor_vn_def)
  moreover have \<open>id_cblinfun \<otimes>\<^sub>o b \<in> A \<otimes>\<^sub>v\<^sub>N B\<close>
    by (simp add: assms(2) double_commutant_grows' tensor_vn_def)
  ultimately have \<open>(a \<otimes>\<^sub>o id_cblinfun) o\<^sub>C\<^sub>L (id_cblinfun \<otimes>\<^sub>o b) \<in> A \<otimes>\<^sub>v\<^sub>N B\<close>
    using commutant_mult tensor_vn_def by blast
  then show ?thesis
    by (simp add: comp_tensor_op)
qed

lemma commutant_tensor_vn_subset: 
  assumes \<open>von_neumann_algebra A\<close> and \<open>von_neumann_algebra B\<close>
  shows \<open>commutant A \<otimes>\<^sub>v\<^sub>N commutant B \<subseteq> commutant (A \<otimes>\<^sub>v\<^sub>N B)\<close>
proof -
  have 1: \<open>a \<otimes>\<^sub>o id_cblinfun \<in> commutant (A \<otimes>\<^sub>v\<^sub>N B)\<close> if \<open>a \<in> commutant A\<close> for a
    apply (simp add: tensor_vn_def)
    using that by (auto intro!: simp: commutant_def comp_tensor_op)
  have 2: \<open>id_cblinfun \<otimes>\<^sub>o b \<in> commutant (A \<otimes>\<^sub>v\<^sub>N B)\<close> if \<open>b \<in> commutant B\<close> for b
    apply (simp add: tensor_vn_def)
    using that by (auto intro!: simp: commutant_def comp_tensor_op)
  show ?thesis
    apply (subst tensor_vn_def)
    apply (rule double_commutant_in_vn_algI)
    using 1 2
    by (auto intro!: von_neumann_algebra_commutant von_neumann_algebra_tensor_vn assms)
qed

lemma commutant_span[simp]: \<open>commutant (span X) = commutant X\<close>
proof (rule order_antisym)
  have \<open>commutant X \<subseteq> commutant (cspan X)\<close>
    by (simp add: commutant_cspan)
  also have \<open>\<dots> \<subseteq> commutant (span X)\<close>
    by (simp add: commutant_antimono span_subset_cspan)
  finally show \<open>commutant X \<subseteq> commutant (span X)\<close>
    by -
  show \<open>commutant (span X) \<subseteq> commutant X\<close>
    by (simp add: commutant_antimono span_superset)
qed


lemma explicit_cblinfun_exists_0[simp]: \<open>explicit_cblinfun_exists (\<lambda>_ _. 0)\<close>
  by (auto intro!: explicit_cblinfun_exists_bounded[where B=0] simp: explicit_cblinfun_def)

lemma explicit_cblinfun_0[simp]: \<open>explicit_cblinfun (\<lambda>_ _. 0) = 0\<close>
  by (auto intro!: equal_ket Rep_ell2_inject[THEN iffD1] ext simp: Rep_ell2_explicit_cblinfun_ket zero_ell2.rep_eq)

lemma cnj_of_bool[simp]: \<open>cnj (of_bool b) = of_bool b\<close>
  by simp

lemma has_sum_single: 
  fixes f :: \<open>_ \<Rightarrow> _::{comm_monoid_add,t2_space}\<close>
  assumes "\<And>j. j \<noteq> i \<Longrightarrow> j\<in>A \<Longrightarrow> f j = 0"
  assumes \<open>s = (if i\<in>A then f i else 0)\<close>
  shows "HAS_SUM f A s"
  apply (subst has_sum_cong_neutral[where T=\<open>A \<inter> {i}\<close> and g=f])
  using assms by auto

lemma classical_operator_None[simp]: \<open>classical_operator (\<lambda>_. None) = 0\<close>
  by (auto intro!: equal_ket simp: classical_operator_ket inj_map_def classical_operator_exists_inj)

lemma has_sum_in_in_closedsubspace:
  assumes \<open>has_sum_in T f A l\<close>
  assumes \<open>\<And>x. x\<in>A \<Longrightarrow> f x \<in> S\<close>
  assumes \<open>closedin T S\<close>
  assumes \<open>csubspace S\<close>
  shows \<open>l \<in> S\<close>
proof -
  from assms
  have \<open>limitin T (sum f) l (finite_subsets_at_top A)\<close>
    by (simp add: has_sum_in_def)
  then have \<open>limitin T (\<lambda>F. if F\<subseteq>A then sum f F else 0) l (finite_subsets_at_top A)\<close>
    apply (rule limitin_transform_eventually[rotated])
    apply (rule eventually_finite_subsets_at_top_weakI)
    by simp
  then show \<open>l \<in> S\<close>
    apply (rule limitin_closedin)
    using assms by (auto intro!: complex_vector.subspace_0 simp: complex_vector.subspace_sum subsetD)
qed


lemma has_sum_coordinatewise:
  \<open>(f has_sum s) A \<longleftrightarrow> (\<forall>i. ((\<lambda>x. f x i) has_sum s i) A)\<close>
proof -
  have \<open>(f has_sum s) A \<longleftrightarrow> ((\<lambda>F. (\<Sum>x\<in>F. f x)) \<longlongrightarrow> s) (finite_subsets_at_top A)\<close>
    by (simp add: has_sum_def)
  also  have \<open>\<dots> \<longleftrightarrow> (\<forall>i. ((\<lambda>F. (\<Sum>x\<in>F. f x) i) \<longlongrightarrow> s i) (finite_subsets_at_top A))\<close>
    by (simp add: tendsto_coordinatewise)
  also have \<open>\<dots> \<longleftrightarrow> (\<forall>i. ((\<lambda>F. \<Sum>x\<in>F. f x i) \<longlongrightarrow> s i) (finite_subsets_at_top A))\<close>
  proof (rewrite at \<open>\<Sum>x\<in>F. f x i\<close> at \<open>\<lambda>F. \<hole>\<close> in \<open>\<forall>i. \<hole>\<close> to \<open>(\<Sum>x\<in>F. f x) i\<close> DEADID.rel_mono_strong)
    fix i
    show \<open>(\<Sum>x\<in>F. f x i) = (\<Sum>x\<in>F. f x) i\<close> for F
      apply (induction F rule:infinite_finite_induct)
      by auto
    show \<open>P = P\<close> for P :: bool
      by simp
  qed
  also have \<open>\<dots> \<longleftrightarrow> (\<forall>i. ((\<lambda>x. f x i) has_sum s i) A)\<close>
    by (simp add: has_sum_def)
  finally show ?thesis
    by - 
qed


lemma one_dim_butterfly:
  \<open>butterfly g h = (one_dim_iso g * cnj (one_dim_iso h)) *\<^sub>C 1\<close>
  apply (rule cblinfun_eq_on_canonical_basis)
  apply simp
  by (smt (verit, del_insts) Groups.mult_ac(2) cblinfun.scaleC_left of_complex_def of_complex_inner_1
      of_complex_inner_1' one_cblinfun_apply_one one_dim_apply_is_times_def one_dim_iso_def
      one_dim_scaleC_1)



lemma one_dim_tc_butterfly:
  fixes g :: \<open>'a :: one_dim\<close> and h :: \<open>'b :: one_dim\<close>
  shows \<open>tc_butterfly g h = (one_dim_iso g * cnj (one_dim_iso h)) *\<^sub>C 1\<close>
proof -
  have \<open>tc_butterfly g h = one_dim_iso (butterfly g h)\<close>
  by (metis (mono_tags, lifting) from_trace_class_one_dim_iso one_dim_iso_inj one_dim_iso_is_of_complex
      one_dim_iso_of_complex tc_butterfly.rep_eq)
  also have \<open>\<dots> = (one_dim_iso g * cnj (one_dim_iso h)) *\<^sub>C 1\<close>
    by (simp add: one_dim_butterfly)
  finally show ?thesis
    by -
qed

lemma one_dim_iso_of_real[simp]: \<open>one_dim_iso (of_real x) = of_real x\<close>
  apply (simp add: of_real_def)
  by (simp add: scaleR_scaleC del: of_complex_of_real_eq)

lemma filter_insert_if:
  \<open>Set.filter P (insert x M) = (if P x then insert x (Set.filter P M) else Set.filter P M)\<close>
  by auto

lemma filter_empty[simp]: \<open>Set.filter P {} = {}\<close>
  by auto

lemma has_sum_in_cong_neutral:
  fixes f g :: \<open>'a \<Rightarrow> 'b::comm_monoid_add\<close>
  assumes \<open>\<And>x. x\<in>T-S \<Longrightarrow> g x = 0\<close>
  assumes \<open>\<And>x. x\<in>S-T \<Longrightarrow> f x = 0\<close>
  assumes \<open>\<And>x. x\<in>S\<inter>T \<Longrightarrow> f x = g x\<close>
  shows "has_sum_in X f S x \<longleftrightarrow> has_sum_in X g T x"
proof -
  have \<open>eventually P (filtermap (sum f) (finite_subsets_at_top S))
      = eventually P (filtermap (sum g) (finite_subsets_at_top T))\<close> for P
  proof 
    assume \<open>eventually P (filtermap (sum f) (finite_subsets_at_top S))\<close>
    then obtain F0 where \<open>finite F0\<close> and \<open>F0 \<subseteq> S\<close> and F0_P: \<open>\<And>F. finite F \<Longrightarrow> F \<subseteq> S \<Longrightarrow> F \<supseteq> F0 \<Longrightarrow> P (sum f F)\<close>
      by (metis (no_types, lifting) eventually_filtermap eventually_finite_subsets_at_top)
    define F0' where \<open>F0' = F0 \<inter> T\<close>
    have [simp]: \<open>finite F0'\<close> \<open>F0' \<subseteq> T\<close>
      by (simp_all add: F0'_def \<open>finite F0\<close>)
    have \<open>P (sum g F)\<close> if \<open>finite F\<close> \<open>F \<subseteq> T\<close> \<open>F \<supseteq> F0'\<close> for F
    proof -
      have \<open>P (sum f ((F\<inter>S) \<union> (F0\<inter>S)))\<close>
        by (intro F0_P) (use \<open>F0 \<subseteq> S\<close> \<open>finite F0\<close> that in auto)
      also have \<open>sum f ((F\<inter>S) \<union> (F0\<inter>S)) = sum g F\<close>
        by (intro sum.mono_neutral_cong) (use that \<open>finite F0\<close> F0'_def assms in auto)
      finally show ?thesis .
    qed
    with \<open>F0' \<subseteq> T\<close> \<open>finite F0'\<close> show \<open>eventually P (filtermap (sum g) (finite_subsets_at_top T))\<close>
      by (metis (no_types, lifting) eventually_filtermap eventually_finite_subsets_at_top)
  next
    assume \<open>eventually P (filtermap (sum g) (finite_subsets_at_top T))\<close>
    then obtain F0 where \<open>finite F0\<close> and \<open>F0 \<subseteq> T\<close> and F0_P: \<open>\<And>F. finite F \<Longrightarrow> F \<subseteq> T \<Longrightarrow> F \<supseteq> F0 \<Longrightarrow> P (sum g F)\<close>
      by (metis (no_types, lifting) eventually_filtermap eventually_finite_subsets_at_top)
    define F0' where \<open>F0' = F0 \<inter> S\<close>
    have [simp]: \<open>finite F0'\<close> \<open>F0' \<subseteq> S\<close>
      by (simp_all add: F0'_def \<open>finite F0\<close>)
    have \<open>P (sum f F)\<close> if \<open>finite F\<close> \<open>F \<subseteq> S\<close> \<open>F \<supseteq> F0'\<close> for F
    proof -
      have \<open>P (sum g ((F\<inter>T) \<union> (F0\<inter>T)))\<close>
        by (intro F0_P) (use \<open>F0 \<subseteq> T\<close> \<open>finite F0\<close> that in auto)
      also have \<open>sum g ((F\<inter>T) \<union> (F0\<inter>T)) = sum f F\<close>
        by (intro sum.mono_neutral_cong) (use that \<open>finite F0\<close> F0'_def assms in auto)
      finally show ?thesis .
    qed
    with \<open>F0' \<subseteq> S\<close> \<open>finite F0'\<close> show \<open>eventually P (filtermap (sum f) (finite_subsets_at_top S))\<close>
      by (metis (no_types, lifting) eventually_filtermap eventually_finite_subsets_at_top)
  qed

  then have tendsto_x: "limitin X (sum f) x (finite_subsets_at_top S) \<longleftrightarrow> limitin X (sum g) x (finite_subsets_at_top T)" for x
    by (simp add: le_filter_def filterlim_def flip: filterlim_nhdsin_iff_limitin)
  then show ?thesis
    by (simp add: has_sum_in_def)
qed


lemma infsum_in_cong_neutral: 
  fixes f g :: \<open>'a \<Rightarrow> 'b::comm_monoid_add\<close>
  assumes \<open>\<And>x. x\<in>T-S \<Longrightarrow> g x = 0\<close>
  assumes \<open>\<And>x. x\<in>S-T \<Longrightarrow> f x = 0\<close>
  assumes \<open>\<And>x. x\<in>S\<inter>T \<Longrightarrow> f x = g x\<close>
  shows \<open>infsum_in X f S = infsum_in X g T\<close>
  apply (rule infsum_in_eqI')
  apply (rule has_sum_in_cong_neutral)
  using assms by auto

lemma filter_image: \<open>Set.filter P (f ` X) = f ` (Set.filter (\<lambda>x. P (f x)) X)\<close>
  by auto

lemma Sigma_image_left: \<open>(SIGMA x:f`A. B x) = (\<lambda>(x,y). (f x, y)) ` (SIGMA x:A. B (f x))\<close>
  by (auto intro!: image_eqI simp: split: prod.split)

lemma finite_subset_filter_image:
  assumes "finite B"
  assumes \<open>B \<subseteq> Set.filter P (f ` A)\<close>
  shows "\<exists>C\<subseteq>A. finite C \<and> B = f ` C"
proof -
  from assms have \<open>B \<subseteq> f ` A\<close>
    by auto
  then show ?thesis
    by (simp add: assms(1) finite_subset_image)
qed

definition \<open>card_le_1 M \<longleftrightarrow> (\<exists>x. M \<subseteq> {x})\<close>

lemma card_le_1_empty[iff]: \<open>card_le_1 {}\<close>
  by (simp add: card_le_1_def)

lemma card_le_1_signleton[iff]: \<open>card_le_1 {x}\<close>
  using card_le_1_def by fastforce

lemma sgn_tensor_ell2: \<open>sgn (h \<otimes>\<^sub>s k) = sgn h \<otimes>\<^sub>s sgn k\<close>
  by (simp add: sgn_div_norm norm_tensor_ell2 scaleR_scaleC tensor_ell2_scaleC1 tensor_ell2_scaleC2)

lemma is_ortho_set_tensor:
  assumes \<open>is_ortho_set B\<close>
  assumes \<open>is_ortho_set C\<close>
  shows \<open>is_ortho_set ((\<lambda>(x, y). x \<otimes>\<^sub>s y) ` (B \<times> C))\<close>
proof (intro is_ortho_set_def[THEN iffD2] conjI notI ballI impI)
  fix bc bc' :: \<open>('a \<times> 'b) ell2\<close>
  assume \<open>bc \<in> (\<lambda>(x, y). x \<otimes>\<^sub>s y) ` (B \<times> C)\<close> 
  then obtain b c where \<open>b \<in> B\<close> \<open>c \<in> C\<close> and bc: \<open>bc = b \<otimes>\<^sub>s c\<close>
    by fast
  assume \<open>bc' \<in> (\<lambda>(x, y). x \<otimes>\<^sub>s y) ` (B \<times> C)\<close>
  then obtain b' c' where \<open>b' \<in> B\<close> \<open>c' \<in> C\<close> and bc': \<open>bc' = b' \<otimes>\<^sub>s c'\<close>
    by fast
  assume \<open>bc \<noteq> bc'\<close>
  then consider (neqb) \<open>b \<noteq> b'\<close> | (neqc) \<open>c \<noteq> c'\<close>
    using bc bc' by blast
  then show \<open>is_orthogonal bc bc'\<close>
  proof cases
    case neqb
    with \<open>b \<in> B\<close> \<open>b' \<in> B\<close> \<open>is_ortho_set B\<close>
    have \<open>b \<bullet>\<^sub>C b' = 0\<close>
      by (simp add: is_ortho_setD)
    then show ?thesis
      by (simp add: bc bc')
  next
    case neqc
    with \<open>c \<in> C\<close> \<open>c' \<in> C\<close> \<open>is_ortho_set C\<close>
    have \<open>c \<bullet>\<^sub>C c' = 0\<close>
      by (simp add: is_ortho_setD)
    then show ?thesis
      by (simp add: bc bc')
  qed
next
  assume \<open>0 \<in> (\<lambda>(x, y). x \<otimes>\<^sub>s y) ` (B \<times> C)\<close>
  then obtain b c where \<open>b \<in> B\<close> \<open>c \<in> C\<close> and \<open>b \<otimes>\<^sub>s c = 0\<close>
    by auto
  then show False
    by (metis assms(1,2) is_ortho_set_def tensor_ell2_nonzero)
qed



end
