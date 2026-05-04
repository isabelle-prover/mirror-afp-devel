(*
  Author: Asta Halkjær Boserup, 2026.

  Inspiration:
  - "A Unifying Principal in Quantification Theory", 1963, Raymond M. Smullyan.
  - "First-Order Logic", 1968, Raymond M. Smullyan.
  - "First-Order Logic and Automated Theorem Proving", 1996, Melvin Fitting.
  - "FOL-Fitting", Stefan Berghofer.
*)

chapter \<open>Abstract Consistency Properties\<close>

theory Abstract_Consistency_Property imports
  "HOL-Cardinals.Cardinal_Order_Relation"
begin

section \<open>Utility\<close>

lemma Set_Diff_Un: \<open>X - (Y \<union> Z) = X - Y - Z\<close>
  by blast

lemma infinite_diff_finite: \<open>finite A \<Longrightarrow> infinite (- B) \<Longrightarrow> infinite (- (A \<union> B))\<close>
  by (metis Compl_Diff_eq double_complement finite_Diff2 sup_commute)

lemma infinite_Diff_fin_Un: \<open>infinite (X - Y) \<Longrightarrow> finite Z \<Longrightarrow> infinite (X - (Z \<union> Y))\<close>
  by (simp add: Set_Diff_Un Un_commute)

lemma infinite_Diff_subset: \<open>infinite (X - A) \<Longrightarrow> B \<subseteq> A \<Longrightarrow> infinite (X - B)\<close>
  by (meson Diff_cancel Diff_eq_empty_iff Diff_mono infinite_super)

lemma finite_bound:
  fixes X :: \<open>('a :: size) set\<close>
  assumes \<open>finite X\<close> \<open>X \<noteq> {}\<close>
  shows \<open>\<exists>x \<in> X. \<forall>y \<in> X. size y \<le> size x\<close>
  using assms by (induct X rule: finite_induct) force+

lemma infinite_UNIV_size:
  fixes f :: \<open>('a :: size) \<Rightarrow> 'a\<close>
  assumes \<open>\<And>x. size x < size (f x)\<close>
  shows \<open>infinite (UNIV :: 'a set)\<close>
proof
  assume \<open>finite (UNIV :: 'a set)\<close>
  then obtain x :: 'a where \<open>\<forall>y :: 'a. size y \<le> size x\<close>
    using finite_bound by fastforce
  moreover have \<open>size x < size (f x)\<close>
    using assms .
  ultimately show False
    using leD by blast
qed

lemma infinite_left: \<open>finite C \<Longrightarrow> infinite A \<Longrightarrow> |A| \<le>o |- B| \<Longrightarrow> |A| \<le>o |- (C \<union> B)|\<close>
  by (metis (no_types, opaque_lifting) Compl_Diff_eq card_of_infinite_diff_finite card_of_ordLeq_finite
      double_complement ordIso_iff_ordLeq ordLeq_transitive sup_commute)

lemma card_of_infinite_smaller_Union:
  assumes \<open>\<forall>x. |f x| <o |X|\<close> \<open>infinite X\<close>
  shows \<open>|\<Union>x \<in> X. f x| \<le>o |X|\<close>
  using assms by (metis (full_types) Field_card_of card_of_UNION_ordLeq_infinite
      card_of_well_order_on ordLeq_iff_ordLess_or_ordIso ordLess_or_ordLeq)

context wo_rel
begin

lemma underS_bound: \<open>a \<in> underS c \<Longrightarrow> b \<in> underS c \<Longrightarrow> a \<in> under b \<or> b \<in> under a\<close>
  by (meson BNF_Least_Fixpoint.underS_Field REFL Refl_under_in in_mono under_ofilter ofilter_linord)

lemma finite_underS_bound:
  assumes \<open>finite X\<close> \<open>X \<subseteq> underS a\<close> \<open>X \<noteq> {}\<close>
  shows \<open>\<exists>a \<in> X. \<forall>b \<in> X. b \<in> under a\<close>
  using assms
proof (induct X rule: finite_induct)
  case (insert x F)
  then show ?case
  proof (cases \<open>F = {}\<close>)
    case True
    then show ?thesis
      using insert underS_bound by fast
  next
    case False
    then show ?thesis
      using insert underS_bound by (metis TRANS insert_absorb insert_iff insert_subset under_trans)
  qed
qed simp

lemma finite_bound_under:
  assumes \<open>finite p\<close> \<open>p \<subseteq> (\<Union>a \<in> Field r. f a)\<close>
  shows \<open>\<exists>b. p \<subseteq> (\<Union>a \<in> under b. f a)\<close>
  using assms
proof (induct rule: finite_induct)
  case (insert x p)
  then obtain b where \<open>p \<subseteq> (\<Union>a \<in> under b. f a)\<close>
    by fast
  moreover obtain b' where \<open>x \<in> f b'\<close> \<open>b' \<in> Field r\<close>
    using insert(4) by blast
  then have \<open>x \<in> (\<Union>a \<in> under b'. f a)\<close>
    using REFL Refl_under_in by fast
  ultimately have \<open>{x} \<union> p \<subseteq> (\<Union>a \<in> under b. f a) \<union> (\<Union>a \<in> under b'. f a)\<close>
    by fast
  then show ?case
    by (metis SUP_union Un_commute insert_is_Un sup.absorb_iff2 ofilter_linord under_ofilter)
qed simp

lemma underS_trans: \<open>a \<in> underS b \<Longrightarrow> b \<in> underS c \<Longrightarrow> a \<in> underS c\<close>
  by (meson ANTISYM TRANS underS_underS_trans)

definition is_chain :: \<open>('a \<Rightarrow> 'a set) \<Rightarrow> bool\<close> where
  \<open>is_chain f \<equiv> \<forall>a \<in> Field r. \<forall>b \<in> Field r. b \<in> under a \<longrightarrow> f b \<subseteq> f a\<close>

lemma is_chainD: \<open>is_chain f \<Longrightarrow> b \<in> under a \<Longrightarrow> x \<in> f b \<Longrightarrow> x \<in> f a\<close>
  unfolding is_chain_def by (metis equals0D subsetD under_Field under_empty)

lemma chain_index:
  assumes ch: \<open>is_chain f\<close> and fin: \<open>finite F\<close> and ne: \<open>Field r \<noteq> {}\<close>
  shows \<open>F \<subseteq> (\<Union>a \<in> Field r. f a) \<Longrightarrow> \<exists>a \<in> Field r. F \<subseteq> f a\<close>
  using fin
proof (induct rule: finite_induct)
  case empty
  then show ?case
    using ne by blast
next
  case (insert x F)
  then have \<open>\<exists>a \<in> Field r. F \<subseteq> f a\<close> \<open>\<exists>b \<in> Field r. x \<in> f b\<close> \<open>F \<subseteq> (\<Union>x \<in> Field r. f x)\<close>
    using ch by simp_all
  then obtain a and b where f: \<open>F \<subseteq> f a\<close> \<open>x \<in> f b\<close> and nm: \<open>a \<in> Field r\<close> \<open>b \<in> Field r\<close>
    by blast
  have \<open>b \<in> under (max2 a b)\<close> \<open>a \<in> under (max2 a b)\<close>
    using nm  by (meson REFL Refl_under_in TRANS max2_greater_among subset_iff under_incl_iff)+
  have \<open>x \<in> f (max2 a b)\<close>
    using is_chainD ch \<open>b \<in> under (max2 a b)\<close> f(2) by blast
  moreover have \<open>F \<subseteq> f (max2 a b)\<close>
    using is_chainD ch \<open>a \<in> local.under (max2 a b)\<close> f(1) by blast
  ultimately show ?case
    using nm unfolding max2_def by auto
qed

end

section \<open>Finite Character\<close>

definition close :: \<open>'a set set \<Rightarrow> 'a set set\<close> where
  \<open>close C \<equiv> {S. (\<exists>S' \<in> C. S \<subseteq> S')}\<close>

definition subset_closed :: \<open>'a set set \<Rightarrow> bool\<close> where
  \<open>subset_closed C \<equiv> \<forall>S' \<in> C. \<forall>S \<subseteq> S'. S \<in> C\<close>

lemma subset_in_close: \<open>S \<subseteq> S' \<Longrightarrow> x \<union> S' \<in> C \<Longrightarrow> x \<union> S \<in> close C\<close>
  unfolding close_def by blast

lemma close_closed: \<open>subset_closed (close C)\<close>
  unfolding close_def subset_closed_def by blast

lemma close_subset: \<open>C \<subseteq> close C\<close>
  unfolding close_def by blast

definition finite_char :: \<open>'a set set \<Rightarrow> bool\<close> where
  \<open>finite_char C \<equiv> \<forall>S. S \<in> C \<longleftrightarrow> (\<forall>S' \<subseteq> S. finite S' \<longrightarrow> S' \<in> C)\<close>

definition mk_finite_char :: \<open>'a set set \<Rightarrow> 'a set set\<close> where
  \<open>mk_finite_char C \<equiv> {S. (\<forall>S' \<subseteq> S. finite S' \<longrightarrow> S' \<in> C)}\<close>

lemma finite_char: \<open>finite_char (mk_finite_char C)\<close>
  unfolding finite_char_def mk_finite_char_def by blast

lemma finite_char_closed: \<open>finite_char C \<Longrightarrow> subset_closed C\<close>
  unfolding finite_char_def subset_closed_def by (meson order_trans)

lemma finite_char_subset: \<open>subset_closed C \<Longrightarrow> C \<subseteq> mk_finite_char C\<close>
  unfolding mk_finite_char_def subset_closed_def by blast

lemma (in wo_rel) chain_union_closed:
  assumes \<open>finite_char C\<close> \<open>is_chain f\<close> \<open>\<forall>a \<in> Field r. f a \<in> C\<close> \<open>Field r \<noteq> {}\<close>
  shows \<open>(\<Union>a \<in> Field r. f a) \<in> C\<close>
  using assms chain_index unfolding finite_char_def by metis

definition maximal :: \<open>'a set set \<Rightarrow> 'a set \<Rightarrow> bool\<close> where
  \<open>maximal C S \<longleftrightarrow> (\<forall>S' \<in> C. S \<subseteq> S' \<longrightarrow> S = S')\<close>

section \<open>Consistency Properties\<close>

locale Params =
  fixes map_fm :: \<open>('x \<Rightarrow> 'x) \<Rightarrow> 'fm \<Rightarrow> 'fm\<close>
    and params_fm :: \<open>'fm \<Rightarrow> 'x set\<close>
    and is_param :: \<open>'x \<Rightarrow> bool\<close>
  assumes map_fm_id: \<open>map_fm id = id\<close>
    and finite_params_fm [simp]: \<open>\<And>p. finite (params_fm p)\<close>
    and map_params_fm: \<open>\<And>f g p. (\<forall>x \<in> params_fm p. f x = g x) \<Longrightarrow> map_fm f p = map_fm g p\<close>
begin

definition is_subst :: \<open>('x \<Rightarrow> 'x) \<Rightarrow> bool\<close> where
  \<open>is_subst f \<equiv> \<forall>x. is_param x \<longleftrightarrow> is_param (f x)\<close>

lemma is_subst_id [intro]: \<open>is_subst id\<close>
  unfolding is_subst_def by simp

definition mk_alt_consistency :: \<open>'fm set set \<Rightarrow> 'fm set set\<close> where
  \<open>mk_alt_consistency C \<equiv> {S. (\<exists>f. is_subst f \<and> map_fm f ` S \<in> C)}\<close>

lemma mk_alt_consistency_subset: \<open>C \<subseteq> mk_alt_consistency C\<close>
  unfolding mk_alt_consistency_def
proof
  fix x
  assume \<open>x \<in> C\<close>
  then have \<open>map_fm id ` x \<in> C\<close>
    using map_fm_id by simp
  then have \<open>\<exists>f. is_subst f \<and> map_fm f ` x \<in> C\<close>
    by blast
  then show \<open>x \<in> {S. \<exists>f. is_subst f \<and> map_fm f ` S \<in> C}\<close>
    by blast
qed

lemma mk_alt_consistency_closed:
  assumes \<open>subset_closed C\<close>
  shows \<open>subset_closed (mk_alt_consistency C)\<close>
  unfolding subset_closed_def mk_alt_consistency_def
proof safe
  fix S S' f
  assume \<open>is_subst f\<close> \<open>map_fm f ` S' \<in> C\<close> \<open>S \<subseteq> S'\<close>
  moreover have \<open>map_fm f ` S \<subseteq> map_fm f ` S'\<close>
    using \<open>S \<subseteq> S'\<close> by blast
  moreover have \<open>\<forall>S' \<in> C. \<forall>S \<subseteq> S'. S \<in> C\<close>
    using \<open>subset_closed C\<close> unfolding subset_closed_def by blast
  ultimately show \<open>\<exists>f. is_subst f \<and> map_fm f ` S \<in> C\<close>
    by blast
qed

abbreviation params :: \<open>'fm set \<Rightarrow> 'x set\<close> where
  \<open>params S \<equiv> \<Union>p \<in> S. params_fm p\<close>

lemma infinite_params: \<open>infinite (U - params B) \<Longrightarrow> infinite (U - params (set ps \<union> B))\<close>
  using finite_params_fm by (metis List.finite_set UN_Un finite_UN_I infinite_Diff_fin_Un)

lemma infinite_params_left: 
  assumes \<open>infinite A\<close> \<open>|A| \<le>o |U - params S|\<close>
  shows \<open>|A| \<le>o |U - params (set ps \<union> S)|\<close>
proof -
  have \<open>infinite (U - params S)\<close>
    using assms card_of_ordLeq_infinite by blast
  then have \<open>|U - params S| =o |U - params (set ps \<union> S)|\<close>
    by (simp add: Set_Diff_Un Un_commute card_of_infinite_diff_finite ordIso_symmetric)
  then show ?thesis
    using assms(2) ordLeq_ordIso_trans by blast
qed

definition enough_new :: \<open>'fm set \<Rightarrow> bool\<close> where
  \<open>enough_new S \<equiv> |UNIV :: 'fm set| \<le>o |Collect is_param - params S|\<close>

lemma enough_new_countable:
  assumes \<open>\<exists>to_nat :: 'fm \<Rightarrow> nat. inj to_nat\<close> \<open>infinite (Collect is_param - params S)\<close>
  shows \<open>enough_new S\<close>
  unfolding enough_new_def using assms
  by (meson UNIV_I card_of_ordLeqI infinite_iff_card_of_nat ordLeq_transitive)

lemma enough_new_all_param:
  assumes \<open>|UNIV :: 'fm set| \<le>o |UNIV - params S|\<close> \<open>\<And>x. is_param x\<close>
  shows \<open>enough_new S\<close>
  unfolding enough_new_def using assms by (simp add: Collect_cong)

end

datatype ('x, 'fm) kind
  = Cond \<open>'fm list \<Rightarrow> ('fm set set \<Rightarrow> 'fm set \<Rightarrow> bool) \<Rightarrow> bool\<close> \<open>'fm set \<Rightarrow> bool\<close>
  | Wits \<open>'fm \<Rightarrow> 'x \<Rightarrow> 'fm list\<close>

inductive (in Params) sat\<^sub>E :: \<open>('x, 'fm) kind \<Rightarrow> 'fm set set \<Rightarrow> bool\<close> where
  sat\<^sub>E_Cond [intro!]: \<open>(\<And>S ps Q. S \<in> C \<Longrightarrow> set ps \<subseteq> S \<Longrightarrow> P ps Q \<Longrightarrow> Q C S) \<Longrightarrow> sat\<^sub>E (Cond P H) C\<close>
| sat\<^sub>E_Wits [intro!]: \<open>(\<And>S p. S \<in> C \<Longrightarrow> p \<in> S \<Longrightarrow> (\<exists>x. is_param x \<and> set (W p x) \<union> S \<in> C)) \<Longrightarrow> sat\<^sub>E (Wits W) C\<close>

inductive_cases (in Params) sat\<^sub>E_CondE[elim!]: \<open>sat\<^sub>E (Cond P H) C\<close>
inductive_cases (in Params) sat\<^sub>E_WitsE[elim!]: \<open>sat\<^sub>E (Wits W) C\<close>

inductive (in Params) sat\<^sub>A :: \<open>('x, 'fm) kind \<Rightarrow> 'fm set set \<Rightarrow> bool\<close> where
  sat\<^sub>A_Cond [intro!]: \<open>(\<And>S ps Q. S \<in> C \<Longrightarrow> set ps \<subseteq> S \<Longrightarrow> P ps Q \<Longrightarrow> Q C S) \<Longrightarrow> sat\<^sub>A (Cond P H) C\<close>
| sat\<^sub>A_Wits [intro!]: \<open>(\<And>S p x. S \<in> C \<Longrightarrow> p \<in> S \<Longrightarrow> x \<notin> params S \<Longrightarrow> is_param x \<Longrightarrow> set (W p x) \<union> S \<in> C) \<Longrightarrow> sat\<^sub>A (Wits W) C\<close>

inductive_cases (in Params) sat\<^sub>A_CondE[elim!]: \<open>sat\<^sub>A (Cond P H) C\<close>
inductive_cases (in Params) sat\<^sub>A_WitsE[elim!]: \<open>sat\<^sub>A (Wits W) C\<close>

definition (in Params) prop\<^sub>E :: \<open>('x, 'fm) kind list \<Rightarrow> 'fm set set \<Rightarrow> bool\<close> where
  \<open>prop\<^sub>E Ks C \<equiv> \<forall>K \<in> set Ks. sat\<^sub>E K C\<close>

definition (in Params) prop\<^sub>A :: \<open>('x, 'fm) kind list \<Rightarrow> 'fm set set \<Rightarrow> bool\<close> where
  \<open>prop\<^sub>A Ks C \<equiv> \<forall>K \<in> set Ks. sat\<^sub>A K C\<close>

inductive (in Params) sat\<^sub>H :: \<open>('x, 'fm) kind \<Rightarrow> 'fm set \<Rightarrow> bool\<close> where
  sat\<^sub>H_Cond [intro!]: \<open>H S \<Longrightarrow> sat\<^sub>H (Cond P H) S\<close>
| sat\<^sub>H_Wits [intro!]: \<open>(\<And>p. p \<in> S \<Longrightarrow> (\<exists>x. is_param x \<and> set (W p x) \<subseteq> S)) \<Longrightarrow> sat\<^sub>H (Wits W) S\<close>

inductive_cases (in Params) sat\<^sub>H_CondE[elim!]: \<open>sat\<^sub>H (Cond P H) C\<close>
inductive_cases (in Params) sat\<^sub>H_WitsE[elim!]: \<open>sat\<^sub>H (Wits W) C\<close>

definition (in Params) prop\<^sub>H :: \<open>('x, 'fm) kind list \<Rightarrow> 'fm set \<Rightarrow> bool\<close> where
  \<open>prop\<^sub>H Ks S \<equiv> \<forall>K \<in> set Ks. sat\<^sub>H K S\<close>

theorem (in Params) sat\<^sub>H_Wits: \<open>sat\<^sub>E (Wits W) C \<Longrightarrow> S \<in> C \<Longrightarrow> maximal C S \<Longrightarrow> sat\<^sub>H (Wits W) S\<close>
  unfolding maximal_def by fast

subsection \<open>Consistency Kinds\<close>

locale Consistency_Kind = Params map_fm params_fm is_param
  for
    map_fm :: \<open>('x \<Rightarrow> 'x) \<Rightarrow> 'fm \<Rightarrow> 'fm\<close> and
    params_fm :: \<open>'fm \<Rightarrow> 'x set\<close> and
    is_param :: \<open>'x \<Rightarrow> bool\<close> +
  fixes K :: \<open>('x, 'fm) kind\<close>
  assumes respects_close: \<open>\<And>C. sat\<^sub>E K C \<Longrightarrow> sat\<^sub>E K (close C)\<close>
    and respects_alt: \<open>\<And>C. sat\<^sub>E K C \<Longrightarrow> subset_closed C \<Longrightarrow> sat\<^sub>A K (mk_alt_consistency C)\<close>
    and respects_fin: \<open>\<And>C. subset_closed C \<Longrightarrow> sat\<^sub>A K C \<Longrightarrow> sat\<^sub>A K (mk_finite_char C)\<close>
    and hintikka: \<open>\<And>C S. sat\<^sub>E K C \<Longrightarrow> S \<in> C \<Longrightarrow> maximal C S \<Longrightarrow> sat\<^sub>H K S\<close>

locale Consistency_Kinds = Params map_fm params_fm is_param
  for
    map_fm :: \<open>('x \<Rightarrow> 'x) \<Rightarrow> 'fm \<Rightarrow> 'fm\<close> and
    params_fm :: \<open>'fm \<Rightarrow> 'x set\<close> and
    is_param :: \<open>'x \<Rightarrow> bool\<close> +
  fixes Ks :: \<open>('x, 'fm) kind list\<close>
  assumes all_kinds: \<open>\<And>K. K \<in> set Ks \<Longrightarrow> Consistency_Kind map_fm params_fm is_param K\<close>
begin

lemma sat\<^sub>E: \<open>K \<in> set Ks \<Longrightarrow> prop\<^sub>E Ks C \<Longrightarrow> sat\<^sub>E K C\<close>
  unfolding prop\<^sub>E_def by blast

lemma prop\<^sub>E_close: \<open>prop\<^sub>E Ks C \<Longrightarrow> prop\<^sub>E Ks (close C)\<close>
  unfolding prop\<^sub>E_def using all_kinds Consistency_Kind.respects_close by fast

lemma prop\<^sub>E_alt: \<open>prop\<^sub>E Ks C \<Longrightarrow> subset_closed C \<Longrightarrow> prop\<^sub>A Ks (mk_alt_consistency C)\<close>
  unfolding prop\<^sub>E_def prop\<^sub>A_def using all_kinds Consistency_Kind.respects_alt by fast

lemma prop\<^sub>E_fin: \<open>subset_closed C \<Longrightarrow> prop\<^sub>A Ks C \<Longrightarrow> prop\<^sub>A Ks (mk_finite_char C)\<close>
  unfolding prop\<^sub>A_def using all_kinds Consistency_Kind.respects_fin by fast

definition mk_alt_fin :: \<open>'fm set set \<Rightarrow> 'fm set set\<close> where
  \<open>mk_alt_fin C \<equiv> mk_finite_char (mk_alt_consistency (close C))\<close>

lemma mk_alt_fin_subset_closed: \<open>subset_closed (mk_alt_fin C)\<close>
  unfolding mk_alt_fin_def using finite_char finite_char_closed by blast

lemma mk_alt_fin_finite_char: \<open>finite_char (mk_alt_fin C)\<close>
  unfolding mk_alt_fin_def using finite_char by blast

lemma mk_alt_fin_in: \<open>S \<in> C \<Longrightarrow> S \<in> mk_alt_fin C\<close>
  unfolding mk_alt_fin_def
  by (meson close_closed close_subset finite_char_subset in_mono mk_alt_consistency_closed mk_alt_consistency_subset)

theorem prop\<^sub>E: \<open>prop\<^sub>E Ks C \<Longrightarrow> prop\<^sub>A Ks (mk_alt_fin C)\<close>
  unfolding mk_alt_fin_def
  by (simp add: prop\<^sub>E_alt prop\<^sub>E_close prop\<^sub>E_fin close_closed mk_alt_consistency_closed)

end

fun (in Params) witness_kinds :: \<open>('x, 'fm) kind list \<Rightarrow> 'fm \<Rightarrow> 'fm set \<Rightarrow> 'fm set\<close> where
  \<open>witness_kinds [] p S = {}\<close>
| \<open>witness_kinds (Cond _ _ # Ks) p S = witness_kinds Ks p S\<close>
| \<open>witness_kinds (Wits W # Ks) p S =
  (let
    rest = witness_kinds Ks p S;
    a = SOME x. x \<in> Collect is_param - params (rest \<union> {p} \<union> S)
   in set (W p a) \<union> rest)\<close>

lemma (in Params) witness_kinds_new:
  assumes \<open>infinite (UNIV :: 'fm set)\<close> \<open>infinite (Collect is_param - params S)\<close>
  shows \<open>infinite (Collect is_param - params (witness_kinds Ks p S \<union> {p} \<union> S))\<close>
  using assms
proof (induct Ks p S rule: witness_kinds.induct)
  case (1 p S)
  then show ?case
    by (simp add: infinite_Diff_fin_Un)
next
  case (3 W Ks p S)
  then show ?case
    by (metis (no_types, lifting) infinite_params sup_assoc witness_kinds.simps(3))
qed simp_all

lemma (in Params) witness_kinds:
  assumes inf: \<open>infinite (UNIV :: 'fm set)\<close> and \<open>infinite (Collect is_param - params S)\<close> \<open>Wits W \<in> set Ks\<close>
  shows \<open>\<exists>x. is_param x \<and> set (W p x) \<subseteq> witness_kinds Ks p S\<close>
  using assms(2-)
proof (induct Ks p S rule: witness_kinds.induct)
  case (3 W' Ks p S)
  moreover have \<open>infinite (Collect is_param - params (witness_kinds Ks p S \<union> {p} \<union> S))\<close>
    using inf 3 witness_kinds_new by blast
  then have \<open>\<exists>x. x \<in> Collect is_param - params (witness_kinds Ks p S \<union> {p} \<union> S)\<close>
    by (metis equals0I finite.emptyI)
  then obtain x where x:
    \<open>(SOME x. x \<in> Collect is_param - params (witness_kinds Ks p S \<union> {p} \<union> S)) = x\<close>
    \<open>is_param x\<close>
    by (metis (mono_tags, lifting) DiffE mem_Collect_eq someI_ex)
  ultimately show ?case
    by (auto simp: Let_def)
qed simp_all

locale Maximal_Consistency = wo_rel \<open>|UNIV| :: 'fm rel\<close> + Consistency_Kinds map_fm params_fm is_param Ks
  for
    map_fm :: \<open>('x \<Rightarrow> 'x) \<Rightarrow> 'fm \<Rightarrow> 'fm\<close> and
    params_fm :: \<open>'fm \<Rightarrow> 'x set\<close> and
    is_param :: \<open>'x \<Rightarrow> bool\<close> and
    Ks :: \<open>('x, 'fm) kind list\<close> +
  assumes inf_univ: \<open>infinite (UNIV :: 'fm set)\<close>
begin

lemma Cinfinite_r: \<open>Cinfinite |UNIV :: 'fm set|\<close>
  by (simp add: cinfinite_def inf_univ)

lemma isLimOrd: isLimOrd
  using Cinfinite_r card_order_infinite_isLimOrd cinfinite_def by blast

lemma aboveS_ne: \<open>aboveS a \<noteq> {}\<close>
  by (simp add: isLimOrd isLimOrd_aboveS)

lemma params_left: \<open>enough_new S \<Longrightarrow> enough_new (set ps \<union> S)\<close>
  unfolding enough_new_def using infinite_params_left inf_univ by blast

definition witness :: \<open>'fm \<Rightarrow> 'fm set \<Rightarrow> 'fm set\<close> where
  \<open>witness \<equiv> witness_kinds Ks\<close>

definition extendS :: \<open>'fm set set \<Rightarrow> 'fm \<Rightarrow> 'fm set \<Rightarrow> 'fm set\<close> where
  \<open>extendS C a prev \<equiv> if ({a} \<union> prev \<in> C) then (witness a prev \<union> {a} \<union> prev) else prev\<close>

definition extendL :: \<open>'fm set set \<Rightarrow> ('fm \<Rightarrow> 'fm set) \<Rightarrow> 'fm \<Rightarrow> 'fm set\<close> where
  \<open>extendL C rec a \<equiv> \<Union>b \<in> underS a. rec b\<close>

definition extend :: \<open>'fm set set \<Rightarrow> 'fm set \<Rightarrow> 'fm \<Rightarrow> 'fm set\<close> where
  \<open>extend C S a \<equiv> worecZSL S (extendS C) (extendL C) a\<close>

lemma adm_woL_extendL: \<open>adm_woL (extendL C)\<close>
  unfolding extendL_def adm_woL_def by blast

definition Extend :: \<open>'fm set set \<Rightarrow> 'fm set \<Rightarrow> 'fm set\<close> where
  \<open>Extend C S \<equiv> \<Union>a. extend C S a\<close>

lemma finite_witness_kinds: \<open>finite (witness_kinds Qs p S)\<close>
  unfolding witness_def by (induct Qs p S rule: witness_kinds.induct) (simp_all add: Let_def)

lemma finite_witness: \<open>finite (witness p S)\<close>
  unfolding witness_def using finite_witness_kinds .

lemma finite_witness_kinds_params: \<open>finite (params (witness_kinds Qs p S))\<close>
  using finite_witness_kinds by simp

lemma finite_witness_params: \<open>finite (params (witness p S))\<close>
  using finite_witness by simp

lemma extend_zero [simp]: \<open>extend C S zero = S\<close>
  unfolding extend_def worecZSL_zero[OF adm_woL_extendL] ..

lemma extend_succ [simp]: \<open>extend C S (succ a) =
    (if {a} \<union> extend C S a \<in> C then witness a (extend C S a) \<union> {a} \<union> extend C S a else extend C S a)\<close>
  unfolding extend_def extendS_def worecZSL_succ[OF adm_woL_extendL aboveS_ne] ..

lemma extend_isLim [simp]:
  assumes \<open>isLim a\<close> \<open>a \<noteq> zero\<close>
  shows \<open>extend C S a = (\<Union>b \<in> underS a. extend C S b)\<close>
  unfolding extend_def extendL_def worecZSL_isLim[OF adm_woL_extendL assms] ..

lemma extend_subset: \<open>S \<subseteq> extend C S a\<close>
proof (induct a rule: well_order_inductZSL)
  case (Lim i)
  then show ?case
    using zero_smallest by (metis Field_card_of SUP_upper2 UNIV_I extend_isLim underS_I)
qed auto

lemma Extend_subset: \<open>S \<subseteq> Extend C S\<close>
  unfolding Extend_def using extend_subset by fast

lemma extend_underS: \<open>b \<in> underS a \<Longrightarrow> extend C S b \<subseteq> extend C S a\<close>
proof (induct a rule: well_order_inductZSL)
  case Zero
  then show ?case
    using underS_zero by blast
next
  case (Suc i)
  moreover from this have \<open>b = i \<or> b \<in> underS i\<close>
    using less_succ by (metis underS_E underS_I)
  ultimately show ?case
    by auto
next
  case (Lim i)
  then show ?case
    by auto
qed

lemma extend_under: \<open>b \<in> under a \<Longrightarrow> extend C S b \<subseteq> extend C S a\<close>
  using extend_underS supr_greater supr_under
  by (metis emptyE in_Above_under set_eq_subset underS_I under_empty)

lemma params_origin:
  assumes \<open>x \<in> params (extend C S a)\<close>
  shows \<open>x \<in> params S \<or> (\<exists>b \<in> underS a. x \<in> params (witness b (extend C S b) \<union> {b}))\<close>
  using assms
proof (induct a rule: well_order_inductZSL)
  case Zero
  then show ?case
    by simp
next
  case (Suc i)
  then consider
    (here) \<open>x \<in> params ({i} \<union> witness i (extend C S i))\<close> |
    (there) \<open>x \<in> params (extend C S i)\<close>
    using Suc(3) by (fastforce split: if_splits)
  then show ?case
  proof cases
    case here
    then show ?thesis
      using Suc(1) succ_diff succ_in by (metis sup_commute underS_I )
  next
    case there
    then show ?thesis
      using Suc by (metis in_mono underS_subset_under underS_succ)
  next
  qed
next
  case (Lim i)
  then obtain j where \<open>j \<in> underS i\<close> \<open>x \<in> params (extend C S j)\<close>
    unfolding extend_def extendL_def worecZSL_isLim[OF adm_woL_extendL Lim(1-2)]
    by blast
  then show ?case
    using Lim underS_trans[of _ j i] by meson
qed

lemma is_chain_extend: \<open>is_chain (extend C S)\<close>
  by (simp add: extend_under is_chain_def)

lemma extend_in_C_step:
  assumes \<open>prop\<^sub>A Ks C\<close> \<open>{a} \<union> extend C S a \<in> C\<close>
    and inf: \<open>infinite (Collect is_param - params ({a} \<union> extend C S a))\<close>
  shows \<open>extend C S (succ a) \<in> C\<close>
proof -
  have \<open>set Qs \<subseteq> set Ks \<Longrightarrow> witness_kinds Qs a (extend C S a) \<union> {a} \<union> extend C S a \<in> C\<close> for Qs
  proof (induct Qs)
    case Nil
    then show ?case
      using assms(2) by simp
  next
    case (Cons Q Qs)
    let ?S = \<open>extend C S a\<close>
    let ?rest = \<open>witness_kinds Qs a ?S\<close>

    have Q: \<open>Q \<in> set Ks\<close>
      using Cons.prems by simp

    have *: \<open>?rest \<union> {a} \<union> ?S \<in> C\<close>
      using Cons by simp

    show ?case
    proof (cases Q)
      case (Wits W)

      have \<open>infinite (Collect is_param - params (?rest \<union> {a} \<union> ?S))\<close>
        using finite_witness_kinds_params inf by (metis UN_Un Un_assoc infinite_Diff_fin_Un)
      then have **: \<open>\<exists>x. x \<in> Collect is_param - params (?rest \<union> {a} \<union> ?S)\<close>
        by (metis ex_in_conv finite.emptyI)
      then obtain x where x:
        \<open>(SOME x. x \<in> Collect is_param - params (?rest \<union> {a} \<union> ?S)) = x\<close>
        \<open>x \<notin> params (?rest \<union> {a} \<union> ?S)\<close>
        \<open>is_param x\<close>
        by (metis (mono_tags, lifting) DiffE mem_Collect_eq someI_ex)

      have \<open>a \<in> ?rest \<union> {a} \<union> ?S\<close>
        by simp
      then have \<open>\<forall>x. x \<notin> params (?rest \<union> {a} \<union> ?S) \<longrightarrow> is_param x \<longrightarrow> set (W a x) \<union> ?rest \<union> {a} \<union> ?S \<in> C\<close>
        using assms(1) * Q Wits unfolding prop\<^sub>A_def Un_assoc by fast
      then have \<open>set (W a x) \<union> ?rest \<union> {a} \<union> ?S \<in> C\<close>
        using x by fast

      moreover have \<open>witness_kinds (Q # Qs) a ?S = set (W a x) \<union> ?rest\<close>
        using Cons Wits x by (simp add: Let_def)
      ultimately show ?thesis
        by simp
    next
      case (Cond P)
      then show ?thesis
        using * by simp
    qed
  qed
  then have \<open>witness a (extend C S a) \<union> {a} \<union> extend C S a \<in> C\<close>
    unfolding witness_def by blast
  then show ?thesis
    unfolding extend_succ using assms(2) by simp
qed

lemma extend_in_C_stop:
  assumes \<open>extend C S a \<in> C\<close>
    and \<open>{a} \<union> extend C S a \<notin> C\<close>
  shows \<open>extend C S (succ a) \<in> C\<close>
  using assms extend_succ by auto


lemma infinite_succ_extend:
  assumes \<open>S \<in> C\<close> \<open>enough_new S\<close> \<open>isSucc p\<close>
  shows \<open>infinite (Collect is_param - params (extend C S p))\<close>
  using assms
proof (induct p rule: well_order_inductZSL)
  case Zero
  then show ?case
    using not_isSucc_zero by blast
next
  case (Suc i)
  then have *: \<open>|underS i| <o |UNIV :: 'fm set|\<close>
    using card_of_underS by (simp add: Cinfinite_r)

  let ?params = \<open>\<lambda>k. params ({k} \<union> witness k (extend C S k))\<close>
  let ?X = \<open>\<Union>k \<in> underS i. ?params k\<close>
  have \<open>|?X| <o |UNIV :: 'fm set|\<close>
  proof (cases \<open>finite (underS i)\<close>)
    case True
    then have \<open>finite ?X\<close>
      using finite_witness_params by simp
    then show ?thesis
      using Cinfinite_r unfolding cinfinite_def by (simp add: finite_ordLess_infinite)
  next
    case False
    moreover have \<open>\<forall>k. finite (?params k)\<close>
      using finite_witness_params by simp
    then have \<open>\<forall>k. |?params k| <o |underS i|\<close>
      using False by simp
    ultimately have \<open>|?X| \<le>o |underS i|\<close>
      using card_of_infinite_smaller_Union by fast
    then show ?thesis
      using * ordLeq_ordLess_trans by blast
  qed
  then have \<open>|?X| <o |Collect is_param - params S|\<close>
    using Suc(4) ordLess_ordLeq_trans unfolding enough_new_def by blast
  moreover have \<open>infinite (Collect is_param - params S)\<close>
    using Suc(4) Cinfinite_r unfolding cinfinite_def enough_new_def
    by (metis Field_card_of ordLeq_finite_Field)
  ultimately have \<open>|Collect is_param - params S - ?X| =o |Collect is_param - params S|\<close>
    using card_of_Un_diff_infinite by blast
  moreover from this have \<open>infinite (Collect is_param - params S - ?X)\<close>
    using \<open>infinite (Collect is_param - params S)\<close> card_of_ordIso_finite by blast
  moreover have \<open>\<And>a. a \<in> params (extend C S i) \<Longrightarrow> a \<in> params S \<or> a \<in> ?X\<close>
    using params_origin by simp
  then have \<open>params (extend C S i) \<subseteq> params S \<union> ?X\<close>
    by fast
  ultimately have \<open>infinite (Collect is_param - params (extend C S i))\<close>
    using infinite_Diff_subset by (metis (no_types, lifting) Set_Diff_Un)
  then show ?case
    using Suc extend_succ inf_univ witness_def witness_kinds_new by presburger
next
  case (Lim i)
  then show ?case
    using isLim_def by blast
qed

lemma extend_in_C:
  assumes \<open>prop\<^sub>A Ks C\<close> \<open>finite_char C\<close> \<open>S \<in> C\<close> \<open>enough_new S\<close>
  shows \<open>extend C S a \<in> C\<close>
  using assms
proof (induct a rule: well_order_inductZSL)
  case Zero
  then show ?case
    by (simp add: adm_woL_extendL extend_def worecZSL_zero)
next
  case (Suc i)
  have \<open>infinite (Collect is_param - params (extend C S (succ i)))\<close>
    using infinite_succ_extend aboveS_ne assms(3,4) isSucc_succ by blast
  then have \<open>infinite (Collect is_param - params (extend C S i))\<close>
    using extend_succ[of C S i]  by (metis UN_Un Un_upper2 infinite_Diff_subset)
  then have \<open>infinite (Collect is_param - params ({i} \<union> extend C S i))\<close>
    using finite_params_fm  by (simp add: Compl_eq_Diff_UNIV infinite_Diff_fin_Un)
  then show ?case
    using Suc extend_in_C_step extend_in_C_stop succ_in[of i] by blast
next
  case (Lim i)
  show ?case
  proof (rule ccontr)
    assume \<open>extend C S i \<notin> C\<close>
    then obtain S' where S': \<open>S' \<subseteq> (\<Union>a \<in> underS i. extend C S a)\<close> \<open>S' \<notin> C\<close> \<open>finite S'\<close>
      using Lim(5) unfolding finite_char_def extend_def extendL_def worecZSL_isLim[OF adm_woL_extendL Lim(1-2)]
      by blast
    then obtain as where as: \<open>S' \<subseteq> (\<Union>a \<in> as. extend C S a)\<close> \<open>as \<subseteq> underS i\<close> \<open>finite as\<close>
      by (metis finite_subset_Union finite_subset_image)
    moreover from this(1) have \<open>as \<noteq> {}\<close>
      using S' Lim unfolding finite_char_def
      by (metis Union_empty bot.extremum_uniqueI empty_subsetI image_empty)
    ultimately obtain j where \<open>\<forall>a \<in> as. a \<in> under j\<close> \<open>j \<in> underS i\<close>
      using finite_underS_bound by (metis in_mono)
    then have \<open>\<forall>a \<in> as. extend C S a \<subseteq> extend C S j\<close>
      using extend_under by fast
    then have \<open>S' \<subseteq> extend C S j\<close>
      using S' as(1) by blast
    then show False
      using Lim(3-) S'(2) as(2-3) \<open>\<forall>a\<in>as. a \<in> under j\<close> \<open>as \<noteq> {}\<close> \<open>j \<in> underS i\<close>
      by (meson Order_Relation.underS_Field finite_char_closed subsetD subset_closed_def)
  qed
qed

lemma Extend_in_C:
  assumes \<open>prop\<^sub>A Ks C\<close> \<open>finite_char C\<close> \<open>S \<in> C\<close> \<open>enough_new S\<close>
  shows \<open>Extend C S \<in> C\<close>
  unfolding Extend_def using assms chain_union_closed is_chain_extend extend_in_C by simp

theorem Extend_maximal:
  assumes \<open>subset_closed C\<close>
  shows \<open>maximal C (Extend C S)\<close>
  unfolding maximal_def Extend_def
proof (intro ballI impI)
  fix S'
  assume *: \<open>S' \<in> C\<close> \<open>(\<Union>x. extend C S x) \<subseteq> S'\<close>
  moreover have \<open>S' \<subseteq> (\<Union>x. extend C S x)\<close>
  proof (rule ccontr)
    assume \<open>\<not> S' \<subseteq> (\<Union>x. extend C S x)\<close>
    then have \<open>\<exists>z. z \<in> S' \<and> z \<notin> (\<Union>x. extend C S x)\<close>
      by blast
    then obtain a where a: \<open>a \<in> S'\<close> \<open>a \<notin> (\<Union>x. extend C S x)\<close>
      using *(1) by blast
    then have \<open>{a} \<union> extend C S a \<subseteq> S'\<close>
      using * by blast
    moreover have \<open>\<forall>S \<subseteq> S'. S \<in> C\<close>
      using assms \<open>S' \<in> C\<close> unfolding subset_closed_def by blast
    ultimately have \<open>{a} \<union> extend C S a \<in> C\<close>
      by blast
    then have \<open>a \<in> extend C S (succ a)\<close>
      using a by simp
    then show False
      using * a by blast
  qed
  ultimately show \<open>(\<Union>x. extend C S x) = S'\<close>
    by simp
qed

definition witnessed :: \<open>'fm set \<Rightarrow> bool\<close> where
  \<open>witnessed S \<equiv> \<forall>p \<in> S. \<exists>S'. infinite (Collect is_param - params S') \<and> witness p S' \<subseteq> S\<close>

theorem Extend_witnessed:
  assumes \<open>prop\<^sub>A Ks C\<close> \<open>finite_char C\<close> \<open>S \<in> C\<close> \<open>enough_new S\<close>
  shows \<open>witnessed (Extend C S)\<close>
  unfolding witnessed_def
proof safe
  fix p
  assume \<open>p \<in> Extend C S\<close>
  then have \<open>{p} \<union> extend C S p \<subseteq> Extend C S\<close>
    unfolding Extend_def by blast
  moreover have \<open>Extend C S \<in> C\<close>
    using Extend_in_C assms by blast
  ultimately have \<open>{p} \<union> extend C S p \<in> C\<close>
    using \<open>finite_char C\<close> finite_char_closed unfolding subset_closed_def by blast
  moreover have \<open>extend C S (succ p) \<in> C\<close>
    using assms extend_in_C by blast
  ultimately have \<open>witness p (extend C S p) \<union> {p} \<union> extend C S p \<in> C\<close>
    unfolding extend_succ by simp
  then have \<open>witness p (extend C S p) \<union> {p} \<union> extend C S p \<subseteq> Extend C S\<close>
    unfolding Extend_def using extend_succ \<open>{p} \<union> extend C S p \<in> C\<close> by fastforce
  moreover have \<open>infinite (Collect is_param - params (extend C S (succ p)))\<close>
    using infinite_succ_extend by (meson aboveS_ne assms(3,4) isSucc_def)
  then have \<open>infinite (Collect is_param - params (extend C S p))\<close>
    using extend_succ by (metis SUP_union Un_upper2 infinite_Diff_subset)
  ultimately show \<open>\<exists>S'. infinite (Collect is_param - params S') \<and> witness p S' \<subseteq> Extend C S\<close>
    by fast
qed

abbreviation mk_mcs :: \<open>'fm set set \<Rightarrow> 'fm set \<Rightarrow> 'fm set\<close> where
  \<open>mk_mcs C S \<equiv> Extend (mk_alt_fin C) S\<close>

theorem mk_mcs_rmaximal: \<open>maximal C (mk_mcs C S)\<close>
  using Extend_maximal maximal_def mk_alt_fin_in mk_alt_fin_subset_closed by meson

theorem mk_mcs_witnessed:
  assumes \<open>prop\<^sub>E Ks C\<close> \<open>S \<in> C\<close> \<open>enough_new S\<close>
  shows \<open>witnessed (mk_mcs C S)\<close>
  using assms Extend_witnessed prop\<^sub>E mk_alt_fin_finite_char mk_alt_fin_in by blast

section \<open>Hintikka Sets\<close>

lemma mk_mcs_hintikka:
  assumes \<open>prop\<^sub>E Ks C\<close> \<open>S \<in> C\<close> \<open>enough_new S\<close>
  shows \<open>prop\<^sub>H Ks (mk_mcs C S)\<close>
  unfolding prop\<^sub>H_def
proof
  fix K
  assume K: \<open>K \<in> set Ks\<close>
  show \<open>sat\<^sub>H K (mk_mcs C S)\<close>
  proof (cases K)
    case (Cond P H)
    moreover have \<open>maximal (mk_alt_fin C) (mk_mcs C S)\<close>
      using Extend_maximal mk_alt_fin_subset_closed by blast
    moreover have \<open>prop\<^sub>A Ks (mk_alt_fin C)\<close>
      using assms(1) prop\<^sub>E by blast
    then have \<open>mk_mcs C S \<in> mk_alt_fin C\<close>
      using assms(2-3) Extend_in_C mk_alt_fin_finite_char mk_alt_fin_in by blast
    moreover have \<open>sat\<^sub>E (Cond P H) (mk_alt_fin C)\<close>
      using \<open>prop\<^sub>A Ks (mk_alt_fin C)\<close> Cond K unfolding prop\<^sub>A_def by fast 
    ultimately show ?thesis
      using K all_kinds Consistency_Kind.hintikka by meson
  next
    case (Wits W)
    have \<open>witnessed (mk_mcs C S)\<close>
      using mk_mcs_witnessed[OF assms(1-3)] .
    then have \<open>\<forall>p \<in> mk_mcs C S. \<exists>x. is_param x \<and> set (W p x) \<subseteq> mk_mcs C S \<close>
      unfolding witnessed_def witness_def using inf_univ Wits witness_kinds K by fast
    then show ?thesis
      using Wits by fast
  qed
qed

end

locale Hintikka = Maximal_Consistency map_fm params_fm is_param Ks
  for
    map_fm :: \<open>('x \<Rightarrow> 'x) \<Rightarrow> 'fm \<Rightarrow> 'fm\<close> and
    params_fm :: \<open>'fm \<Rightarrow> 'x set\<close> and
    is_param :: \<open>'x \<Rightarrow> bool\<close> and
    Ks :: \<open>('x, 'fm) kind list\<close> +
  fixes H :: \<open>'fm set\<close>
  assumes hintikka: \<open>prop\<^sub>H Ks H\<close>
begin

lemma sat\<^sub>H: \<open>K \<in> set Ks \<Longrightarrow> sat\<^sub>H K H\<close>
  using hintikka unfolding prop\<^sub>H_def by blast

end

context Maximal_Consistency
begin

theorem mk_mcs_Hintikka:
  assumes \<open>prop\<^sub>E Ks C\<close> \<open>S \<in> C\<close> \<open>enough_new S\<close>
  shows \<open>Hintikka map_fm params_fm is_param Ks (mk_mcs C S)\<close>
  using assms mk_mcs_hintikka by unfold_locales

end

section \<open>Derivational Consistency\<close>

locale Derivational_Kind = Consistency_Kind map_fm params_fm is_param K
  for
    map_fm :: \<open>('x \<Rightarrow> 'x) \<Rightarrow> 'fm \<Rightarrow> 'fm\<close> and
    params_fm :: \<open>'fm \<Rightarrow> 'x set\<close> and
    is_param :: \<open>'x \<Rightarrow> bool\<close> and
    K :: \<open>('x, 'fm) kind\<close> +
  fixes consistent :: \<open>'fm set \<Rightarrow> bool\<close> (\<open>\<turnstile> _\<close> [51] 50)
  assumes kind: \<open>infinite (UNIV :: 'fm set) \<Longrightarrow> sat\<^sub>E K {A. enough_new A \<and> \<turnstile> A}\<close>

locale Derivational_Consistency = Maximal_Consistency map_fm params_fm is_param Ks
  for
    map_fm :: \<open>('x \<Rightarrow> 'x) \<Rightarrow> 'fm \<Rightarrow> 'fm\<close> and
    params_fm :: \<open>'fm \<Rightarrow> 'x set\<close> and
    is_param :: \<open>'x \<Rightarrow> bool\<close> and
    Ks :: \<open>('x, 'fm) kind list\<close> +
  fixes consistent :: \<open>'fm set \<Rightarrow> bool\<close> (\<open>\<turnstile> _\<close> [51] 50)
  assumes all_consistent: \<open>infinite (UNIV :: 'fm set) \<Longrightarrow> prop\<^sub>E Ks {A. enough_new A \<and> \<turnstile> A}\<close>
begin

theorem Consistency: \<open>prop\<^sub>E Ks {A. enough_new A \<and> \<turnstile> A}\<close>
  using all_consistent inf_univ unfolding prop\<^sub>E_def by fast

end

section \<open>Weak Derivational Consistency\<close>

locale Weak_Derivational_Kind = Consistency_Kind map_fm params_fm is_param K
  for
    map_fm :: \<open>('x \<Rightarrow> 'x) \<Rightarrow> 'fm \<Rightarrow> 'fm\<close> and
    params_fm :: \<open>'fm \<Rightarrow> 'x set\<close> and
    is_param :: \<open>'x \<Rightarrow> bool\<close> and
    K :: \<open>('x, 'fm) kind\<close> +
  fixes consistent :: \<open>'fm list \<Rightarrow> bool\<close> (\<open>\<turnstile> _\<close> [51] 50)
  assumes kind: \<open>infinite (Collect is_param) \<Longrightarrow> sat\<^sub>E K {S. \<exists>A. set A = S \<and> \<turnstile> A}\<close>

locale Weak_Derivational_Consistency = Maximal_Consistency map_fm params_fm is_param Ks
  for
    map_fm :: \<open>('x \<Rightarrow> 'x) \<Rightarrow> 'fm \<Rightarrow> 'fm\<close> and
    params_fm :: \<open>'fm \<Rightarrow> 'x set\<close> and
    is_param :: \<open>'x \<Rightarrow> bool\<close> and
    Ks :: \<open>('x, 'fm) kind list\<close> +
  fixes consistent :: \<open>'fm list \<Rightarrow> bool\<close> (\<open>\<turnstile> _\<close> [51] 50)
  assumes Consistency: \<open>infinite (UNIV :: 'x set) \<Longrightarrow> prop\<^sub>E Ks {S. \<exists>A. set A = S \<and> \<turnstile> A}\<close>


section \<open>Conflicts\<close>

locale Confl = Params map_fm params_fm is_param
  for
    map_fm :: \<open>('x \<Rightarrow> 'x) \<Rightarrow> 'fm \<Rightarrow> 'fm\<close> and
    params_fm :: \<open>'fm \<Rightarrow> 'x set\<close> and
    is_param :: \<open>'x \<Rightarrow> bool\<close> +
  fixes classify :: \<open>'fm list \<Rightarrow> 'fm list \<Rightarrow> bool\<close> (infix \<open>\<leadsto>\<^sub>\<crossmark>\<close> 50)
  assumes confl_map: \<open>\<And>ps qs f. ps \<leadsto>\<^sub>\<crossmark> qs \<Longrightarrow> map (map_fm f) ps \<leadsto>\<^sub>\<crossmark> map (map_fm f) qs\<close>
begin

inductive cond where
  cond [intro!]: \<open>ps \<leadsto>\<^sub>\<crossmark> qs \<Longrightarrow> cond ps (\<lambda>_ S. set qs \<inter> S = {})\<close>

inductive_cases condE[elim!]: \<open>cond ps Q\<close>

inductive hint where
  hint [intro!]: \<open>(\<And>ps qs q. ps \<leadsto>\<^sub>\<crossmark> qs \<Longrightarrow> set ps \<subseteq> H \<Longrightarrow> q \<in> set qs \<Longrightarrow> q \<notin> H) \<Longrightarrow> hint H\<close>

declare hint.simps[simp]

abbreviation kind :: \<open>('x, 'fm) kind\<close> where
  \<open>kind \<equiv> Cond cond hint\<close>

end

sublocale Confl \<subseteq> Consistency_Kind map_fm params_fm is_param kind
proof
  fix C
  assume conflC: \<open>sat\<^sub>E kind C\<close>
  then show \<open>sat\<^sub>E kind (close C)\<close>
  proof safe
    fix S ps qs q
    assume \<open>S \<in> close C\<close>
    then obtain S' where S': \<open>S' \<in> C\<close> and \<open>S \<subseteq> S'\<close>
      unfolding close_def by blast

    assume \<open>set ps \<subseteq> S\<close>
    then have *: \<open>set ps \<subseteq> S'\<close>
      using \<open>S \<subseteq> S'\<close> by blast

    assume **: \<open>ps \<leadsto>\<^sub>\<crossmark> qs\<close>
    then have \<open>\<forall>q \<in> set qs. q \<notin> S'\<close>
      using conflC S' * by blast
    then have \<open>\<forall>q \<in> set qs. q \<notin> S\<close>
      using \<open>S \<subseteq> S'\<close> by blast
    moreover assume \<open>q \<in> set qs\<close> \<open>q \<in> S\<close>
    ultimately show \<open>q \<in> {}\<close>
      using ** by auto
  qed
next
  fix C
  assume conflC: \<open>sat\<^sub>E kind C\<close>
  then show \<open>sat\<^sub>A kind (mk_alt_consistency C)\<close>
  proof safe
    fix S ps qs q

    assume \<open>S \<in> mk_alt_consistency C\<close>
    then obtain f where f: \<open>map_fm f ` S \<in> C\<close>
      unfolding mk_alt_consistency_def by blast

    let ?C = \<open>mk_alt_consistency C\<close>
    let ?S = \<open>map_fm f ` S\<close>

    assume \<open>set ps \<subseteq> S\<close>
    then have *: \<open>set (map (map_fm f) ps) \<subseteq> ?S\<close>
      by auto

    assume \<open>ps \<leadsto>\<^sub>\<crossmark> qs\<close>
    then have \<open>map (map_fm f) ps \<leadsto>\<^sub>\<crossmark> (map (map_fm f) qs)\<close>
      using confl_map by blast
    then have \<open>\<forall>q \<in> set  (map (map_fm f) qs). q \<notin> ?S\<close>
      using conflC f * by blast
    then have \<open>\<forall>q \<in> set qs. map_fm f q \<notin> ?S\<close>
      by simp
    then have \<open>\<forall>q \<in> set qs. q \<notin> S\<close>
      by blast
    moreover assume \<open>q \<in> set qs\<close> \<open>q \<in> S\<close>
    ultimately show \<open>q \<in> {}\<close>
      by auto
  qed
next
  fix C
  assume conflAC: \<open>sat\<^sub>A kind C\<close> and closedC: \<open>subset_closed C\<close>
  then show \<open>sat\<^sub>A kind (mk_finite_char C)\<close>
  proof safe
    fix S ps qs q
    assume \<open>S \<in> mk_finite_char C\<close>
    then have finc: \<open>\<forall>S' \<subseteq> S. finite S' \<longrightarrow> S' \<in> C\<close>
      unfolding mk_finite_char_def by blast

    have sc: \<open>\<forall>S' \<in> C. \<forall>S \<subseteq> S'. S \<in> C\<close>
      using closedC unfolding subset_closed_def by blast
    then have sc': \<open>\<And>S' x. x \<union> S' \<in> C \<Longrightarrow> \<forall>S \<subseteq> x \<union> S'. S \<in> C\<close>
      by blast

    assume *: \<open>set ps \<subseteq> S\<close> \<open>ps \<leadsto>\<^sub>\<crossmark> qs\<close> \<open>q \<in> set qs\<close> \<open>q \<in> S\<close>
    then have \<open>{q} \<union> set ps \<in> C\<close>
      using \<open>set ps \<subseteq> S\<close> finc by simp
    then have \<open>q \<in> {}\<close>
      using * conflAC by blast
    then show \<open>q \<in> {}\<close>
      by auto
  qed
next
  fix C S
  assume *: \<open>sat\<^sub>E kind C\<close> \<open>S \<in> C\<close> \<open>maximal C S\<close> 
  show \<open>sat\<^sub>H kind S\<close>
  proof safe
    fix ps qs q
    assume **: \<open>set ps \<subseteq> S\<close> \<open>ps \<leadsto>\<^sub>\<crossmark> qs\<close> \<open>q \<in> set qs\<close> \<open>q \<in> S\<close>
    then show False
      using * by blast
  qed
qed

locale Derivational_Confl = Confl map_fm params_fm is_param classify
  for
    map_fm :: \<open>('x \<Rightarrow> 'x) \<Rightarrow> 'fm \<Rightarrow> 'fm\<close> and
    params_fm :: \<open>'fm \<Rightarrow> 'x set\<close> and
    is_param :: \<open>'x \<Rightarrow> bool\<close> and
    classify :: \<open>'fm list \<Rightarrow> 'fm list \<Rightarrow> bool\<close> (infix \<open>\<leadsto>\<^sub>\<crossmark>\<close> 50) +
  fixes consistent :: \<open>'fm set \<Rightarrow> bool\<close> (\<open>\<turnstile> _\<close> [51] 50)
  assumes consistent: \<open>\<And>S ps qs x. set ps \<subseteq> S \<Longrightarrow> ps \<leadsto>\<^sub>\<crossmark> qs \<Longrightarrow> x \<in> set qs \<Longrightarrow> x \<in> S \<Longrightarrow> \<not> \<turnstile> S\<close>

sublocale Derivational_Confl \<subseteq> Derivational_Kind map_fm params_fm is_param kind consistent
  using infinite_params_left consistent by unfold_locales blast+


locale Weak_Derivational_Confl = Confl map_fm params_fm is_param classify
  for
    map_fm :: \<open>('x \<Rightarrow> 'x) \<Rightarrow> 'fm \<Rightarrow> 'fm\<close> and
    params_fm :: \<open>'fm \<Rightarrow> 'x set\<close> and
    is_param :: \<open>'x \<Rightarrow> bool\<close> and
    classify :: \<open>'fm list \<Rightarrow> 'fm list \<Rightarrow> bool\<close> (infix \<open>\<leadsto>\<^sub>\<crossmark>\<close> 50) +
  fixes consistent :: \<open>'fm list \<Rightarrow> bool\<close> (\<open>\<turnstile> _\<close> [51] 50)
  assumes consistent: \<open>\<And>A ps qs x. set ps \<subseteq> set A \<Longrightarrow> ps \<leadsto>\<^sub>\<crossmark> qs \<Longrightarrow> x \<in> set qs \<Longrightarrow> x \<in> set A \<Longrightarrow> \<not> \<turnstile> A\<close>

sublocale Weak_Derivational_Confl \<subseteq> Weak_Derivational_Kind map_fm params_fm is_param kind consistent
  using infinite_params_left consistent by unfold_locales blast+

section \<open>Alpha\<close>

locale Alpha = Params map_fm params_fm is_param
  for
    map_fm :: \<open>('x \<Rightarrow> 'x) \<Rightarrow> 'fm \<Rightarrow> 'fm\<close> and
    params_fm :: \<open>'fm \<Rightarrow> 'x set\<close> and
    is_param :: \<open>'x \<Rightarrow> bool\<close> +
  fixes classify :: \<open>'fm list \<Rightarrow> 'fm list \<Rightarrow> bool\<close> (infix \<open>\<leadsto>\<^sub>\<alpha>\<close> 50)
  assumes alpha_map: \<open>\<And>ps qs f. ps \<leadsto>\<^sub>\<alpha> qs \<longrightarrow> map (map_fm f) ps \<leadsto>\<^sub>\<alpha> map (map_fm f) qs\<close>
begin

inductive cond where
  cond [intro!]: \<open>ps \<leadsto>\<^sub>\<alpha> qs \<Longrightarrow> cond ps (\<lambda>C S. set qs \<union> S \<in> C)\<close>

inductive_cases condE[elim!]: \<open>cond ps Q\<close>

inductive hint where
  hint [intro!]: \<open>(\<And>ps qs q. ps \<leadsto>\<^sub>\<alpha> qs \<Longrightarrow> set ps \<subseteq> H \<Longrightarrow> q \<in> set qs \<Longrightarrow> q \<in> H) \<Longrightarrow> hint H\<close>

declare hint.simps[simp]

abbreviation kind :: \<open>('x, 'fm) kind\<close> where
  \<open>kind \<equiv> Cond cond hint\<close>

end

sublocale Alpha \<subseteq> Consistency_Kind map_fm params_fm is_param kind
proof
  fix C
  assume alphaC: \<open>sat\<^sub>E kind C\<close>
  then show \<open>sat\<^sub>E kind (close C)\<close>
  proof safe
    fix S ps qs q
    assume \<open>S \<in> close C\<close>
    then obtain S' where S': \<open>S' \<in> C\<close> and \<open>S \<subseteq> S'\<close>
      unfolding close_def by blast

    assume \<open>set ps \<subseteq> S\<close> \<open>ps \<leadsto>\<^sub>\<alpha> qs\<close>
    then have *: \<open>set ps \<subseteq> S'\<close>
      using \<open>S \<subseteq> S'\<close> by blast

    assume **: \<open>ps \<leadsto>\<^sub>\<alpha> qs\<close>
    then have \<open>set qs \<union> S' \<in> C\<close>
      using alphaC S' * by blast
    then show  \<open>set qs \<union> S \<in> close C\<close>
      using \<open>S \<subseteq> S'\<close> subset_in_close by blast
  qed
next
  fix C
  assume alphaC: \<open>sat\<^sub>E kind C\<close>
  then show \<open>sat\<^sub>A kind (mk_alt_consistency C)\<close>
  proof safe
    fix S ps qs

    assume \<open>S \<in> mk_alt_consistency C\<close>
    then obtain f where f: \<open>is_subst f\<close> \<open>map_fm f ` S \<in> C\<close>
      unfolding mk_alt_consistency_def by blast

    let ?C = \<open>mk_alt_consistency C\<close>
    let ?S = \<open>map_fm f ` S\<close>

    assume \<open>set ps \<subseteq> S\<close>
    then have *: \<open>set (map (map_fm f) ps) \<subseteq> ?S\<close>
      by auto

    assume \<open>ps \<leadsto>\<^sub>\<alpha> qs\<close>
    then have \<open>map (map_fm f) ps \<leadsto>\<^sub>\<alpha> (map (map_fm f) qs)\<close>
      using alpha_map by blast
    then have \<open>set (map (map_fm f) qs) \<union> ?S \<in> C\<close>
      using alphaC * f by blast
    then show \<open>set qs \<union> S \<in> ?C\<close>
      unfolding mk_alt_consistency_def using f by (auto simp: image_Un)
  qed
next
  fix C
  assume alphaAC: \<open>sat\<^sub>A kind C\<close> and closedC: \<open>subset_closed C\<close>
  then show \<open>sat\<^sub>A kind (mk_finite_char C)\<close>
  proof safe
    fix S ps qs q
    assume \<open>S \<in> mk_finite_char C\<close>
    then have finc: \<open>\<forall>S' \<subseteq> S. finite S' \<longrightarrow> S' \<in> C\<close>
      unfolding mk_finite_char_def by blast

    have sc: \<open>\<forall>S' \<in> C. \<forall>S \<subseteq> S'. S \<in> C\<close>
      using closedC unfolding subset_closed_def by blast
    then have sc': \<open>\<And>S' x. x \<union> S' \<in> C \<Longrightarrow> \<forall>S \<subseteq> x \<union> S'. S \<in> C\<close>
      by blast

    assume *: \<open>set ps \<subseteq> S\<close> and **: \<open>ps \<leadsto>\<^sub>\<alpha> qs\<close>

    show \<open>set qs \<union> S \<in> mk_finite_char C\<close>
      unfolding mk_finite_char_def
    proof safe
      fix S'
      let ?S' = \<open>set ps \<union> (S' - set qs)\<close>

      assume \<open>S' \<subseteq> set qs \<union> S\<close> and \<open>finite S'\<close>
      then have \<open>?S' \<subseteq> S\<close>
        using * by blast
      moreover have \<open>finite ?S'\<close>
        using \<open>finite S'\<close> by blast
      ultimately have \<open>?S' \<in> C\<close>
        using finc by blast
      then have \<open>set qs \<union> ?S' \<in> C\<close>
        using ** alphaAC by fast
      then show \<open>S' \<in> C\<close>
        using sc by fast
    qed
  qed
next
  fix C S
  assume *: \<open>sat\<^sub>E kind C\<close> \<open>S \<in> C\<close> \<open>maximal C S\<close> 
  show \<open>sat\<^sub>H kind S\<close>
  proof safe
    fix ps qs q
    assume **: \<open>set ps \<subseteq> S\<close> \<open>ps \<leadsto>\<^sub>\<alpha> qs\<close>
    then have \<open>set qs \<union> S \<in> C\<close>
      using * by blast
    moreover assume \<open>q \<in> set qs\<close>
    ultimately show \<open>q \<in> S\<close>
      using \<open>maximal C S\<close> unfolding maximal_def by fast
  qed
qed

locale Derivational_Alpha = Alpha map_fm params_fm is_param classify
  for
    map_fm :: \<open>('x \<Rightarrow> 'x) \<Rightarrow> 'fm \<Rightarrow> 'fm\<close> and
    params_fm :: \<open>'fm \<Rightarrow> 'x set\<close> and
    is_param :: \<open>'x \<Rightarrow> bool\<close> and
    classify :: \<open>'fm list \<Rightarrow> 'fm list \<Rightarrow> bool\<close> (infix \<open>\<leadsto>\<^sub>\<alpha>\<close> 50) +
  fixes consistent :: \<open>'fm set \<Rightarrow> bool\<close> (\<open>\<turnstile> _\<close> [51] 50)
  assumes consistent: \<open>\<And>S ps qs. set ps \<subseteq> S \<Longrightarrow> ps \<leadsto>\<^sub>\<alpha> qs \<Longrightarrow> \<turnstile> S \<Longrightarrow> \<turnstile> set qs \<union> S\<close>

sublocale Derivational_Alpha \<subseteq> Derivational_Kind map_fm params_fm is_param kind consistent
  using infinite_params_left consistent enough_new_def by unfold_locales blast+


locale Weak_Derivational_Alpha = Alpha map_fm params_fm is_param classify
  for
    map_fm :: \<open>('x \<Rightarrow> 'x) \<Rightarrow> 'fm \<Rightarrow> 'fm\<close> and
    params_fm :: \<open>'fm \<Rightarrow> 'x set\<close> and
    is_param :: \<open>'x \<Rightarrow> bool\<close> and
    classify :: \<open>'fm list \<Rightarrow> 'fm list \<Rightarrow> bool\<close> (infix \<open>\<leadsto>\<^sub>\<alpha>\<close> 50) +
  fixes consistent :: \<open>'fm list \<Rightarrow> bool\<close> (\<open>\<turnstile> _\<close> [51] 50)
  assumes consistent: \<open>\<And>A ps qs. set ps \<subseteq> set A \<Longrightarrow> ps \<leadsto>\<^sub>\<alpha> qs \<Longrightarrow> \<turnstile> A \<Longrightarrow> \<turnstile> qs @ A\<close>

sublocale Weak_Derivational_Alpha \<subseteq> Weak_Derivational_Kind map_fm params_fm is_param kind consistent
proof
  show \<open>sat\<^sub>E kind {S. \<exists>A. set A = S \<and> \<turnstile> A}\<close>
  proof safe
    fix ps qs A
    assume \<open>set ps \<subseteq> set A\<close> \<open>ps \<leadsto>\<^sub>\<alpha> qs\<close> \<open>\<turnstile> A\<close>
    then show \<open>\<exists>B. set B = set qs \<union> set A \<and> \<turnstile> B\<close>
      using consistent[of ps A qs] by (meson set_append)
  qed
qed

section \<open>Beta\<close>

locale Beta = Params map_fm params_fm is_param
  for
    map_fm :: \<open>('x \<Rightarrow> 'x) \<Rightarrow> 'fm \<Rightarrow> 'fm\<close> and
    params_fm :: \<open>'fm \<Rightarrow> 'x set\<close> and
    is_param :: \<open>'x \<Rightarrow> bool\<close> +
  fixes classify :: \<open>'fm list \<Rightarrow> 'fm list \<Rightarrow> bool\<close> (infix \<open>\<leadsto>\<^sub>\<beta>\<close> 50)
  assumes beta_map: \<open>\<And>ps qs f. ps \<leadsto>\<^sub>\<beta> qs \<longrightarrow> map (map_fm f) ps \<leadsto>\<^sub>\<beta> map (map_fm f) qs\<close>
begin

inductive cond where
  cond [intro!]: \<open>ps \<leadsto>\<^sub>\<beta> qs \<Longrightarrow> cond ps (\<lambda>C S. \<exists>q \<in> set qs. {q} \<union> S \<in> C)\<close>

inductive_cases condE[elim!]: \<open>cond ps Q\<close>

inductive hint where
  hint [intro!]: \<open>(\<And>ps qs. ps \<leadsto>\<^sub>\<beta> qs \<Longrightarrow> set ps \<subseteq> H \<Longrightarrow> \<exists>q \<in> set qs. q \<in> H) \<Longrightarrow> hint H\<close>

declare hint.simps[simp]

abbreviation kind :: \<open>('x, 'fm) kind\<close> where
  \<open>kind \<equiv> Cond cond hint\<close>

end

sublocale Beta \<subseteq> Consistency_Kind map_fm params_fm is_param kind
proof
  fix C
  assume betaC: \<open>sat\<^sub>E kind C\<close>
  then show \<open>sat\<^sub>E kind (close C)\<close>
  proof safe
    fix S ps qs q
    assume \<open>S \<in> close C\<close>
    then obtain S' where S': \<open>S' \<in> C\<close> and \<open>S \<subseteq> S'\<close>
      unfolding close_def by blast

    assume \<open>set ps \<subseteq> S\<close> \<open>ps \<leadsto>\<^sub>\<beta> qs\<close>
    then have *: \<open>set ps \<subseteq> S'\<close>
      using \<open>S \<subseteq> S'\<close> by blast

    assume **: \<open>ps \<leadsto>\<^sub>\<beta> qs\<close>
    then have \<open>\<exists>q \<in> set qs. {q} \<union> S' \<in> C\<close>
      using betaC S' * by blast
    then show \<open>\<exists>q \<in> set qs. insert q S \<in> close C\<close>
      using \<open>S \<subseteq> S'\<close> subset_in_close by (metis insert_is_Un)
  qed
next
  fix C
  assume betaC: \<open>sat\<^sub>E kind C\<close>
  then show \<open>sat\<^sub>A kind (mk_alt_consistency C)\<close>
  proof safe
    fix S ps qs

    assume \<open>S \<in> mk_alt_consistency C\<close>
    then obtain f where f: \<open>is_subst f\<close> \<open>map_fm f ` S \<in> C\<close>
      unfolding mk_alt_consistency_def by blast

    let ?C = \<open>mk_alt_consistency C\<close>
    let ?S = \<open>map_fm f ` S\<close>

    assume \<open>set ps \<subseteq> S\<close>
    then have *: \<open>set (map (map_fm f) ps) \<subseteq> ?S\<close>
      by auto

    assume \<open>ps \<leadsto>\<^sub>\<beta> qs\<close>
    then have \<open>map (map_fm f) ps \<leadsto>\<^sub>\<beta> (map (map_fm f) qs)\<close>
      using beta_map by blast
    then have \<open>\<exists>q \<in> set (map (map_fm f) qs). {q} \<union> ?S \<in> C\<close>
      using betaC * f by blast
    then show \<open>\<exists>q \<in> set qs. insert q S \<in> ?C\<close>
      unfolding mk_alt_consistency_def using f by (auto simp: image_Un)
  qed
next
  fix C
  assume betaAC: \<open>sat\<^sub>A kind C\<close> and closedC: \<open>subset_closed C\<close>
  then show \<open>sat\<^sub>A kind (mk_finite_char C)\<close>
  proof safe
    fix S ps qs q
    assume \<open>S \<in> mk_finite_char C\<close>
    then have finc: \<open>\<forall>S' \<subseteq> S. finite S' \<longrightarrow> S' \<in> C\<close>
      unfolding mk_finite_char_def by blast

    have sc: \<open>\<forall>S' \<in> C. \<forall>S \<subseteq> S'. S \<in> C\<close>
      using closedC unfolding subset_closed_def by blast
    then have sc': \<open>\<And>S' x. x \<union> S' \<in> C \<Longrightarrow> \<forall>S \<subseteq> x \<union> S'. S \<in> C\<close>
      by blast

    assume *: \<open>set ps \<subseteq> S\<close> and **: \<open>ps \<leadsto>\<^sub>\<beta> qs\<close>

    show \<open>\<exists>q \<in> set qs. insert q S \<in> mk_finite_char C\<close>
    proof (rule ccontr)
      assume \<open>\<not> ?thesis\<close>
      then have \<open>\<forall>q \<in> set qs. \<exists>Sq. Sq \<subseteq> insert q S \<and> finite Sq \<and> Sq \<notin> C\<close>
        unfolding mk_finite_char_def by blast
      then obtain f where f: \<open>\<forall>q \<in> set qs. f q \<subseteq> insert q S \<and> finite (f q) \<and> f q \<notin> C\<close>
        by metis

      let ?S' = \<open>set ps \<union> \<Union>{f q - {q} |q. q \<in> set qs}\<close>

      have \<open>?S' \<subseteq> S\<close>
        using * f by fast
      moreover have \<open>finite ?S'\<close>
        using f by auto
      ultimately have \<open>?S' \<in> C\<close>
        using finc by blast
      then have \<open>\<exists>q \<in> set qs. {q} \<union> ?S' \<in> C\<close>
        using ** betaAC by fast
      then have \<open>\<exists>q \<in> set qs. f q \<in> C\<close>
        using sc' by blast
      then show False
        using f by blast
    qed
  qed
next
  fix C S
  assume *: \<open>sat\<^sub>E kind C\<close> \<open>S \<in> C\<close> \<open>maximal C S\<close> 
  show \<open>sat\<^sub>H kind S\<close>
  proof safe
    fix ps qs
    assume **: \<open>set ps \<subseteq> S\<close> \<open>ps \<leadsto>\<^sub>\<beta> qs\<close>
    then have \<open>\<exists>q \<in> set qs. {q} \<union> S \<in> C\<close>
      using * by blast
    then show \<open>\<exists>q \<in> set qs. q \<in> S\<close>
      using \<open>maximal C S\<close> unfolding maximal_def by fast
  qed
qed

locale Derivational_Beta = Beta map_fm params_fm is_param classify
  for
    map_fm :: \<open>('x \<Rightarrow> 'x) \<Rightarrow> 'fm \<Rightarrow> 'fm\<close> and
    params_fm :: \<open>'fm \<Rightarrow> 'x set\<close> and
    is_param :: \<open>'x \<Rightarrow> bool\<close> and
    classify :: \<open>'fm list \<Rightarrow> 'fm list \<Rightarrow> bool\<close> (infix \<open>\<leadsto>\<^sub>\<beta>\<close> 50) +
  fixes consistent :: \<open>'fm set \<Rightarrow> bool\<close> (\<open>\<turnstile> _\<close> [51] 50)
  assumes consistent: \<open>\<And>S ps qs. set ps \<subseteq> S \<Longrightarrow> ps \<leadsto>\<^sub>\<beta> qs \<Longrightarrow> \<turnstile> S \<Longrightarrow> \<exists>q \<in> set qs. \<turnstile> {q} \<union> S\<close>

sublocale Derivational_Beta \<subseteq> Derivational_Kind map_fm params_fm is_param kind consistent
proof
  assume inf: \<open>infinite (UNIV :: 'fm set)\<close>
  then show \<open>sat\<^sub>E kind {A. enough_new A \<and> \<turnstile> A}\<close>
  proof safe
    fix S ps qs
    assume *: \<open>set ps \<subseteq> S\<close> \<open>ps \<leadsto>\<^sub>\<beta> qs\<close> \<open>\<turnstile> S\<close>
    then have \<open>\<exists>q \<in> set qs. \<turnstile> {q} \<union> S\<close>
      using consistent by blast
    moreover assume \<open>enough_new S\<close> 
    ultimately show \<open>\<exists>q\<in>set qs. insert q S \<in> {A. enough_new A \<and> \<turnstile> A}\<close>
      using infinite_params_left[OF inf] unfolding enough_new_def
      by (metis (no_types, lifting) empty_set insert_code(1) insert_is_Un mem_Collect_eq)
  qed
qed

locale Weak_Derivational_Beta = Beta map_fm params_fm is_param classify
  for
    map_fm :: \<open>('x \<Rightarrow> 'x) \<Rightarrow> 'fm \<Rightarrow> 'fm\<close> and
    params_fm :: \<open>'fm \<Rightarrow> 'x set\<close> and
    is_param :: \<open>'x \<Rightarrow> bool\<close> and
    classify :: \<open>'fm list \<Rightarrow> 'fm list \<Rightarrow> bool\<close> (infix \<open>\<leadsto>\<^sub>\<beta>\<close> 50) +
  fixes consistent :: \<open>'fm list \<Rightarrow> bool\<close> (\<open>\<turnstile> _\<close> [51] 50)
  assumes consistent: \<open>\<And>A ps qs. set ps \<subseteq> set A \<Longrightarrow> ps \<leadsto>\<^sub>\<beta> qs \<Longrightarrow> \<turnstile> A \<Longrightarrow> \<exists>q \<in> set qs. \<turnstile> q # A\<close>

sublocale Weak_Derivational_Beta \<subseteq> Weak_Derivational_Kind map_fm params_fm is_param kind consistent
proof
  show \<open>sat\<^sub>E kind {S. \<exists>A. set A = S \<and> \<turnstile> A}\<close>
  proof safe
    fix ps qs A
    assume *: \<open>set ps \<subseteq> set A\<close> \<open>ps \<leadsto>\<^sub>\<beta> qs\<close> \<open>\<turnstile> A\<close>
    then have \<open>\<exists>q \<in> set qs. \<turnstile> q # A\<close>
      using consistent by blast
    then show \<open>\<exists>q\<in>set qs. insert q (set A) \<in> {S. \<exists>A. set A = S \<and> \<turnstile> A}\<close>
      by (metis (mono_tags, lifting) CollectI list.simps(15))
  qed
qed

section \<open>Gamma\<close>

locale Gamma = Params map_fm params_fm is_param
  for
    map_tm :: \<open>('x \<Rightarrow> 'x) \<Rightarrow> 'tm \<Rightarrow> 'tm\<close> and
    map_fm :: \<open>('x \<Rightarrow> 'x) \<Rightarrow> 'fm \<Rightarrow> 'fm\<close> and
    params_fm :: \<open>'fm \<Rightarrow> 'x set\<close> and
    is_param :: \<open>'x \<Rightarrow> bool\<close> +
  fixes classify :: \<open>'fm list \<Rightarrow> ('fm set \<Rightarrow> 'tm set) \<times> ('tm \<Rightarrow> 'fm list) \<Rightarrow> bool\<close> (infix \<open>\<leadsto>\<^sub>\<gamma>\<close> 50)
  assumes gamma_map: \<open>\<And>ps F qs f. ps \<leadsto>\<^sub>\<gamma> (F, qs) \<Longrightarrow> (\<exists>G rs. map (map_fm f) ps \<leadsto>\<^sub>\<gamma> (G, rs) \<and>
      (\<forall>S. map_tm f ` F S \<subseteq> G (map_fm f ` S)) \<and>
      (\<forall>t. map (map_fm f) (qs t) = rs (map_tm f t)))\<close>
    and gamma_mono: \<open>\<And>ps F qs S S'. ps \<leadsto>\<^sub>\<gamma> (F, qs) \<Longrightarrow> S \<subseteq> S' \<Longrightarrow> F S \<subseteq> F S'\<close>
    and gamma_fin: \<open>\<And>ps F qs t A. ps \<leadsto>\<^sub>\<gamma> (F, qs) \<Longrightarrow> t \<in> F A \<Longrightarrow> \<exists>B \<subseteq> A. finite B \<and> t \<in> F B\<close>
begin

inductive cond where
  cond [intro!]: \<open>ps \<leadsto>\<^sub>\<gamma> (F, qs) \<Longrightarrow> cond ps (\<lambda>C S. \<forall>t \<in> F S. set (qs t) \<union> S \<in> C)\<close>

inductive_cases condE[elim!]: \<open>cond ps Q\<close>

inductive hint where
  hint [intro!]: \<open>(\<And>ps F qs. ps \<leadsto>\<^sub>\<gamma> (F, qs) \<Longrightarrow> set ps \<subseteq> H \<Longrightarrow> (\<forall>t \<in> F H. set (qs t) \<subseteq> H)) \<Longrightarrow> hint H\<close>

declare hint.simps[simp]

abbreviation kind :: \<open>('x, 'fm) kind\<close> where
  \<open>kind \<equiv> Cond cond hint\<close>

end

sublocale Gamma \<subseteq> Consistency_Kind map_fm params_fm is_param kind
proof
  fix C
  assume gammaC: \<open>sat\<^sub>E kind C\<close>
  then show \<open>sat\<^sub>E kind (close C)\<close>
  proof safe
    fix S ps qs F t
    assume \<open>S \<in> close C\<close>
    then obtain S' where S': \<open>S' \<in> C\<close> and \<open>S \<subseteq> S'\<close>
      unfolding close_def by blast

    assume \<open>set ps \<subseteq> S\<close>
    then have *: \<open>set ps \<subseteq> S'\<close>
      using \<open>S \<subseteq> S'\<close> by blast

    assume **: \<open>ps \<leadsto>\<^sub>\<gamma> (F, qs)\<close> \<open>t \<in> F S\<close>
    then have \<open>t \<in> F S'\<close>
      using ** gamma_mono \<open>S \<subseteq> S'\<close> by blast
    then have \<open>set (qs t) \<union> S' \<in> C\<close>
      using gammaC S' * ** by blast
    then have \<open>set (qs t) \<union> S \<in> close C\<close>
      using \<open>S \<subseteq> S'\<close> subset_in_close by blast
    then show \<open>set (qs t) \<union> S \<in> close C\<close>
      by (meson close_closed equalityE subset_closed_def sup.mono)
  qed
next
  fix C
  assume gammaC: \<open>sat\<^sub>E kind C\<close>
  then show \<open>sat\<^sub>A kind (mk_alt_consistency C)\<close>
  proof safe
    fix S ps F qs t

    assume \<open>S \<in> mk_alt_consistency C\<close>
    then obtain f where f: \<open>is_subst f\<close> \<open>map_fm f ` S \<in> C\<close>
      unfolding mk_alt_consistency_def by blast

    let ?C = \<open>mk_alt_consistency C\<close>
    let ?S = \<open>map_fm f ` S\<close>

    assume \<open>set ps \<subseteq> S\<close>
    then have *: \<open>set (map (map_fm f) ps) \<subseteq> ?S\<close>
      by auto

    assume **: \<open>ps \<leadsto>\<^sub>\<gamma> (F, qs)\<close> and t: \<open>t \<in> F S\<close>
    obtain rs G where rs:
      \<open>map (map_fm f) ps \<leadsto>\<^sub>\<gamma> (G, rs)\<close>
      \<open>\<forall>S. map_tm f ` F S \<subseteq> G (map_fm f ` S)\<close>
      \<open>\<forall>t. map (map_fm f) (qs t) = rs (map_tm f t)\<close>
      using gamma_map ** by meson
    then have \<open>set (rs (map_tm f t)) \<union> ?S \<in> C\<close>
      using gammaC f * t by blast
    then have \<open>set (map (map_fm f) (qs t)) \<union> ?S \<in> C\<close>
      using rs by simp
    then show \<open>set (qs t) \<union> S \<in> ?C\<close>
      unfolding mk_alt_consistency_def using f by (auto simp: image_Un)
  qed
next
  fix C
  assume gammaAC: \<open>sat\<^sub>A kind C\<close> and closedC: \<open>subset_closed C\<close>
  then show \<open>sat\<^sub>A kind (mk_finite_char C)\<close>
  proof safe
    fix S ps F qs t
    assume \<open>S \<in> mk_finite_char C\<close>
    then have finc: \<open>\<forall>S' \<subseteq> S. finite S' \<longrightarrow> S' \<in> C\<close>
      unfolding mk_finite_char_def by blast

    have sc: \<open>\<forall>S' \<in> C. \<forall>S \<subseteq> S'. S \<in> C\<close>
      using closedC unfolding subset_closed_def by blast
    then have sc': \<open>\<And>S' x. x \<union> S' \<in> C \<Longrightarrow> \<forall>S \<subseteq> x \<union> S'. S \<in> C\<close>
      by blast

    assume *: \<open>set ps \<subseteq> S\<close> and **: \<open>ps \<leadsto>\<^sub>\<gamma> (F, qs)\<close> and t: \<open>t \<in> F S\<close>

    show \<open>set (qs t) \<union> S \<in> mk_finite_char C\<close>
      unfolding mk_finite_char_def 
    proof safe
      fix S'
      assume 1: \<open>S' \<subseteq> set (qs t) \<union> S\<close> and 2: \<open>finite S'\<close>

      obtain A where A: \<open>A \<subseteq> S\<close> \<open>finite A\<close> \<open>S' \<subseteq> set (qs t) \<union> A\<close> 
        using 1 2 by (meson Diff_subset_conv equalityD2 finite_Diff)

      obtain B where B: \<open>B \<subseteq> S\<close> \<open>finite B\<close> \<open>t \<in> F B\<close>
        using ** t gamma_fin by meson

      let ?S = \<open>set ps \<union> A \<union> B\<close>

      have \<open>finite ?S\<close>
        using A(2) B(2) by blast
      moreover have \<open>?S \<subseteq> S\<close>
        using * A(1) B(1) by simp
      ultimately have \<open>?S \<in> C\<close>
        using finc by simp

      moreover have \<open>set ps \<subseteq> ?S\<close>
        by blast
      moreover have \<open>t \<in> F ?S\<close>
        using ** B(3) gamma_mono by blast
      ultimately have \<open>set (qs t) \<union> ?S \<in> C\<close>
        using ** gammaAC by blast

      moreover have \<open>S' \<subseteq> set (qs t) \<union> ?S\<close>
        using A(3) by blast
      ultimately show \<open>S' \<in> C\<close>
        using sc by blast
    qed
  qed
next
  fix C S
  assume *: \<open>sat\<^sub>E kind C\<close> \<open>S \<in> C\<close> \<open>maximal C S\<close> 
  show \<open>sat\<^sub>H kind S\<close>
  proof safe
    fix ps F qs t
    assume **: \<open>set ps \<subseteq> S\<close> \<open>ps \<leadsto>\<^sub>\<gamma> (F, qs)\<close>
    then have \<open>\<forall>t \<in> F S. set (qs t) \<union> S \<in> C\<close>
      using * by blast
    then have \<open>\<forall>t \<in> F S. set (qs t) \<subseteq> S\<close>
      using \<open>maximal C S\<close> unfolding maximal_def by fast
    then show \<open>t \<in> F S \<Longrightarrow> x \<in> set (qs t) \<Longrightarrow> x \<in> S\<close> for x
      by blast
  qed
qed

locale Derivational_Gamma = Gamma map_tm map_fm params_fm is_param classify
  for
    map_tm :: \<open>('x \<Rightarrow> 'x) \<Rightarrow> 'tm \<Rightarrow> 'tm\<close> and
    map_fm :: \<open>('x \<Rightarrow> 'x) \<Rightarrow> 'fm \<Rightarrow> 'fm\<close> and
    params_fm :: \<open>'fm \<Rightarrow> 'x set\<close> and
    is_param :: \<open>'x \<Rightarrow> bool\<close> and
    classify :: \<open>'fm list \<Rightarrow> ('fm set \<Rightarrow> 'tm set) \<times> ('tm \<Rightarrow> 'fm list) \<Rightarrow> bool\<close> (infix \<open>\<leadsto>\<^sub>\<gamma>\<close> 50) +
  fixes consistent :: \<open>'fm set \<Rightarrow> bool\<close> (\<open>\<turnstile> _\<close> [51] 50)
  assumes consistent: \<open>\<And>S ps F qs t. set ps \<subseteq> S \<Longrightarrow> ps \<leadsto>\<^sub>\<gamma> (F, qs) \<Longrightarrow> t \<in> F S \<Longrightarrow> \<turnstile> S \<Longrightarrow> \<turnstile> set (qs t) \<union> S\<close>

sublocale Derivational_Gamma \<subseteq> Derivational_Kind map_fm params_fm is_param kind consistent
  using infinite_params_left consistent enough_new_def by unfold_locales blast+

locale Weak_Derivational_Gamma = Gamma map_tm map_fm params_fm is_param classify
  for
    map_tm :: \<open>('x \<Rightarrow> 'x) \<Rightarrow> 'tm \<Rightarrow> 'tm\<close> and
    map_fm :: \<open>('x \<Rightarrow> 'x) \<Rightarrow> 'fm \<Rightarrow> 'fm\<close> and
    params_fm :: \<open>'fm \<Rightarrow> 'x set\<close> and
    is_param :: \<open>'x \<Rightarrow> bool\<close> and
    classify :: \<open>'fm list \<Rightarrow> ('fm set \<Rightarrow> 'tm set) \<times> ('tm \<Rightarrow> 'fm list) \<Rightarrow> bool\<close> (infix \<open>\<leadsto>\<^sub>\<gamma>\<close> 50) +
  fixes consistent :: \<open>'fm list \<Rightarrow> bool\<close> (\<open>\<turnstile> _\<close> [51] 50)
  assumes consistent: \<open>\<And>A ps F qs t. set ps \<subseteq> set A \<Longrightarrow> ps \<leadsto>\<^sub>\<gamma> (F, qs) \<Longrightarrow> t \<in> F (set A) \<Longrightarrow> \<turnstile> A \<Longrightarrow> \<turnstile> qs t @ A\<close>

sublocale Weak_Derivational_Gamma \<subseteq> Weak_Derivational_Kind map_fm params_fm is_param kind consistent
proof
  show \<open>sat\<^sub>E kind {S. \<exists>A. set A = S \<and> \<turnstile> A}\<close>
  proof safe
    fix ps qs A F t
    assume *: \<open>set ps \<subseteq> set A\<close> \<open>ps \<leadsto>\<^sub>\<gamma> (F, qs)\<close> \<open>\<turnstile> A\<close> \<open>t \<in> F (set A)\<close>
    then show \<open>\<exists>B. set B = set (qs t) \<union> set A \<and> \<turnstile> B\<close>
      using consistent[of ps A F qs t] by (meson set_append)
  qed
qed

locale Gamma_UNIV = Params map_fm params_fm is_param
  for
    map_tm :: \<open>('x \<Rightarrow> 'x) \<Rightarrow> 'tm \<Rightarrow> 'tm\<close> and
    map_fm :: \<open>('x \<Rightarrow> 'x) \<Rightarrow> 'fm \<Rightarrow> 'fm\<close> and
    params_fm :: \<open>'fm \<Rightarrow> 'x set\<close> and
    is_param :: \<open>'x \<Rightarrow> bool\<close> +
  fixes classify :: \<open>'fm list \<Rightarrow> ('tm \<Rightarrow> 'fm list) \<Rightarrow> bool\<close> (infix \<open>\<leadsto>\<^sub>\<gamma>''\<close> 50)
  assumes gamma_map_UNIV: \<open>\<And>ps qs f. ps \<leadsto>\<^sub>\<gamma>' qs \<Longrightarrow> \<exists>rs. map (map_fm f) ps \<leadsto>\<^sub>\<gamma>' rs \<and>
      (\<forall>t. map (map_fm f) (qs t) = rs (map_tm f t))\<close>
begin

abbreviation (input) classify_UNIV where
  \<open>classify_UNIV \<equiv> \<lambda>ps (F, qs). (F = (\<lambda>_. UNIV)) \<and> ps \<leadsto>\<^sub>\<gamma>' qs\<close>

end

sublocale Gamma_UNIV \<subseteq> Gamma map_tm map_fm params_fm is_param classify_UNIV
proof
  show \<open>\<And>ps F qs f.
       (case (F, qs) of (F, qs) \<Rightarrow> F = (\<lambda>_. UNIV) \<and> ps \<leadsto>\<^sub>\<gamma>' qs) \<Longrightarrow>
       \<exists>G rs.
          (case (G, rs) of (F, qs) \<Rightarrow> F = (\<lambda>_. UNIV) \<and> map (map_fm f) ps \<leadsto>\<^sub>\<gamma>' qs) \<and>
          (\<forall>S. map_tm f ` F S \<subseteq> G (map_fm f ` S)) \<and> (\<forall>t. map (map_fm f) (qs t) = rs (map_tm f t))\<close>
    using gamma_map_UNIV image_subset_iff by fastforce
  show \<open>\<And>ps F qs S S'. (case (F, qs) of (F, qs) \<Rightarrow> F = (\<lambda>_. UNIV) \<and> ps \<leadsto>\<^sub>\<gamma>' qs) \<Longrightarrow> S \<subseteq> S' \<Longrightarrow> F S \<subseteq> F S'\<close>
    by simp
  show \<open>\<And>ps F qs t A. (case (F, qs) of (F, qs) \<Rightarrow> F = (\<lambda>_. UNIV) \<and> ps \<leadsto>\<^sub>\<gamma>' qs) \<Longrightarrow> t \<in> F A \<Longrightarrow> \<exists>B\<subseteq>A. finite B \<and> t \<in> F B\<close>
    by blast
qed

section \<open>Delta\<close>

locale Delta = Params map_fm params_fm is_param
  for
    map_fm :: \<open>('x \<Rightarrow> 'x) \<Rightarrow> 'fm \<Rightarrow> 'fm\<close> and
    params_fm :: \<open>'fm \<Rightarrow> 'x set\<close> and
    is_param :: \<open>'x \<Rightarrow> bool\<close> +
  fixes \<delta> :: \<open>'fm \<Rightarrow> 'x \<Rightarrow> 'fm list\<close>
  assumes delta_map: \<open>\<And>p f x. is_param x \<Longrightarrow> is_subst f \<Longrightarrow> \<delta> (map_fm f p) (f x) = map (map_fm f) (\<delta> p x)\<close>
begin

abbreviation \<open>kind \<equiv> Wits \<delta>\<close>
end

sublocale Delta \<subseteq> Consistency_Kind map_fm params_fm is_param kind
proof
  fix C
  assume deltaC: \<open>sat\<^sub>E kind C\<close>
  then show \<open>sat\<^sub>E kind (close C)\<close>
  proof safe
    fix S p qs q
    assume \<open>S \<in> close C\<close>
    then obtain S' where S': \<open>S' \<in> C\<close> and \<open>S \<subseteq> S'\<close>
      unfolding close_def by blast

    assume \<open>p \<in> S\<close>
    then have *: \<open>p \<in> S'\<close>
      using \<open>S \<subseteq> S'\<close> by blast

    have \<open>\<exists>x. is_param x \<and> set (\<delta> p x) \<union> S' \<in> C\<close>
      using deltaC S' * by blast
    then show \<open>\<exists>x. is_param x \<and> set (\<delta> p x) \<union> S \<in> close C\<close>
      using \<open>S \<subseteq> S'\<close> by (metis subset_in_close)

  qed
next
  fix C
  assume deltaC: \<open>sat\<^sub>E kind C\<close>
  then show \<open>sat\<^sub>A kind (mk_alt_consistency C)\<close>
  proof safe
    fix S p qs x

    assume \<open>S \<in> mk_alt_consistency C\<close>
    then obtain f where f: \<open>is_subst f\<close> \<open>map_fm f ` S \<in> C\<close>
      unfolding mk_alt_consistency_def by blast

    let ?C = \<open>mk_alt_consistency C\<close>
    let ?S = \<open>map_fm f ` S\<close>

    assume \<open>p \<in> S\<close>
    then have *: \<open>map_fm f p \<in> ?S\<close>
      by auto

    assume x: \<open>x \<notin> params S\<close> \<open>is_param x\<close>
    obtain y where y: \<open>is_param y\<close> \<open>set (\<delta> (map_fm f p) y) \<union> ?S \<in> C\<close>
      using deltaC f * by blast

    let ?g = \<open>f(x := y)\<close>

    have g: \<open>is_subst ?g\<close>
      using f x y unfolding is_subst_def by simp

    have \<open>\<forall>x \<in> params S. f x = ?g x\<close>
      using x by simp
    then have S: \<open>\<forall>q \<in> S. map_fm ?g q = map_fm f q\<close>
      using map_params_fm by simp
    then have \<open>map_fm ?g p = map_fm f p\<close>
      using \<open>p \<in> S\<close> by auto

    moreover have \<open>set (\<delta> (map_fm f p) (?g x)) \<union> ?S \<in> C\<close>
      using y by simp
    ultimately have \<open>set (map (map_fm ?g) (\<delta> p x)) \<union> ?S \<in> C\<close>
      using delta_map x g by metis
    then have \<open>\<exists>f. is_subst f \<and> set (map (map_fm f) (\<delta> p x)) \<union> map_fm f ` S \<in> C\<close>
      using S g by (metis image_cong)
    then show \<open>set (\<delta> p x) \<union> S \<in> ?C\<close>
      unfolding mk_alt_consistency_def
      by (metis (mono_tags, lifting) image_Un image_set mem_Collect_eq)
  qed
next
  fix C
  assume deltaAC: \<open>sat\<^sub>A kind C\<close> and closedC: \<open>subset_closed C\<close>
  then show \<open>sat\<^sub>A kind (mk_finite_char C)\<close>
  proof safe
    fix S p qs x
    assume \<open>S \<in> mk_finite_char C\<close>
    then have finc: \<open>\<forall>S' \<subseteq> S. finite S' \<longrightarrow> S' \<in> C\<close>
      unfolding mk_finite_char_def by blast

    have sc: \<open>\<forall>S' \<in> C. \<forall>S \<subseteq> S'. S \<in> C\<close>
      using closedC unfolding subset_closed_def by blast
    then have sc': \<open>\<And>S' x. x \<union> S' \<in> C \<Longrightarrow> \<forall>S \<subseteq> x \<union> S'. S \<in> C\<close>
      by blast

    assume *: \<open>p \<in> S\<close> and x: \<open>x \<notin> params S\<close> \<open>is_param x\<close>
    show \<open>set (\<delta> p x) \<union> S \<in> mk_finite_char C\<close>
      unfolding mk_finite_char_def
    proof safe
      fix S'
      let ?S' = \<open>{p} \<union> (S' - set (\<delta> p x))\<close>

      assume \<open>S' \<subseteq> set (\<delta> p x) \<union> S\<close> and \<open>finite S'\<close>
      then have \<open>?S' \<subseteq> S\<close>
        using * by fast
      moreover have \<open>finite ?S'\<close>
        using \<open>finite S'\<close> by blast
      ultimately have \<open>?S' \<in> C\<close>
        using finc by blast
      moreover have \<open>\<forall>a \<in> ?S'. x \<notin> params_fm a\<close>
        using x \<open>?S' \<subseteq> S\<close> by blast
      ultimately have \<open>set (\<delta> p x) \<union> ?S' \<in> C\<close>
        using x deltaAC by blast
      then show \<open>S' \<in> C\<close>
        using sc by fast
    qed
  qed
next
  show \<open>\<And>C S. sat\<^sub>E kind C \<Longrightarrow> S \<in> C \<Longrightarrow> maximal C S \<Longrightarrow> sat\<^sub>H kind S\<close>
    using sat\<^sub>H_Wits .
qed

locale Derivational_Delta = Delta map_fm params_fm is_param \<delta>
  for
    map_fm :: \<open>('x \<Rightarrow> 'x) \<Rightarrow> 'fm \<Rightarrow> 'fm\<close> and
    params_fm :: \<open>'fm \<Rightarrow> 'x set\<close> and
    is_param :: \<open>'x \<Rightarrow> bool\<close> and
    \<delta> :: \<open>'fm \<Rightarrow> 'x \<Rightarrow> 'fm list\<close> +
  fixes consistent :: \<open>'fm set \<Rightarrow> bool\<close> (\<open>\<turnstile> _\<close> [51] 50)
  assumes consistent: \<open>\<And>S p x. p \<in> S \<Longrightarrow> is_param x \<Longrightarrow> x \<notin> params S \<Longrightarrow> \<turnstile> S \<Longrightarrow> \<turnstile> set (\<delta> p x) \<union> S\<close>

sublocale Derivational_Delta \<subseteq> Derivational_Kind map_fm params_fm is_param kind consistent
proof
  assume inf: \<open>infinite (UNIV :: 'fm set)\<close>
  show \<open>sat\<^sub>E kind {A. enough_new A \<and> \<turnstile> A}\<close>
  proof safe
    fix S p
    assume *: \<open>p \<in> S\<close> \<open>enough_new S\<close> \<open>\<turnstile> S\<close>
    then have \<open>infinite (Collect is_param - (params ({p} \<union> S)))\<close>
      unfolding enough_new_def using card_of_ordLeq_finite inf by auto
    then obtain x where \<open>is_param x\<close> \<open>x \<notin> params ({p} \<union> S)\<close>
      using infinite_imp_nonempty by blast
    then have \<open>\<exists>x. is_param x \<and> \<turnstile> set (\<delta> p x) \<union> S\<close>
      using *(1,3) consistent \<open>\<turnstile> S\<close> by fast
    then show \<open>\<exists>x. is_param x \<and> set (\<delta> p x) \<union> S \<in> {A. enough_new A \<and> \<turnstile> A}\<close>
      using * inf infinite_params_left unfolding enough_new_def by blast
  qed
qed

locale Weak_Derivational_Delta = Delta map_fm params_fm is_param \<delta>
  for
    map_fm :: \<open>('x \<Rightarrow> 'x) \<Rightarrow> 'fm \<Rightarrow> 'fm\<close> and
    params_fm :: \<open>'fm \<Rightarrow> 'x set\<close> and
    is_param :: \<open>'x \<Rightarrow> bool\<close> and
    \<delta> :: \<open>'fm \<Rightarrow> 'x \<Rightarrow> 'fm list\<close> +
  fixes consistent :: \<open>'fm list \<Rightarrow> bool\<close> (\<open>\<turnstile> _\<close> [51] 50)
  assumes consistent: \<open>\<And>A p x. p \<in> set A \<Longrightarrow> is_param x \<Longrightarrow> x \<notin> params (set A) \<Longrightarrow> \<turnstile> A \<Longrightarrow> \<turnstile> \<delta> p x @ A\<close>

sublocale Weak_Derivational_Delta \<subseteq> Weak_Derivational_Kind map_fm params_fm is_param kind consistent
proof
  assume inf: \<open>infinite (Collect is_param :: 'x set)\<close>
  show \<open>sat\<^sub>E kind {S. \<exists>A. set A = S \<and> \<turnstile> A}\<close>
  proof safe
    fix p A
    assume *: \<open>p \<in> set A\<close> \<open>\<turnstile> A\<close>
    then have \<open>infinite (Collect is_param - (params (set (p # A))))\<close>
      using inf finite_compl by fastforce
    then obtain x where \<open>is_param x\<close> \<open>x \<notin> params (set (p # A))\<close>
      using infinite_imp_nonempty by blast
    then have \<open>\<exists>x. is_param x \<and> \<turnstile> \<delta> p x @ A\<close>
      using * consistent[of p A x] by auto
    then show \<open>\<exists>x. is_param x \<and> set (\<delta> p x) \<union> set A \<in> {S. \<exists>A. set A = S \<and> \<turnstile> A}\<close>
      by (metis (mono_tags, lifting) CollectI set_append)
  qed
qed

section \<open>Modal\<close>

text \<open>
  The Hintikka property you want depends on the concrete logic.
  See Term-Modal Logics by Fitting, Thalmann and Voronkov, p. 156 bottom.
\<close>

locale Modal = Params map_fm params_fm is_param
  for
    map_fm :: \<open>('x \<Rightarrow> 'x) \<Rightarrow> 'fm \<Rightarrow> 'fm\<close> and
    params_fm :: \<open>'fm \<Rightarrow> 'x set\<close> and
    is_param :: \<open>'x \<Rightarrow> bool\<close> +
  fixes classify :: \<open>'fm list \<Rightarrow> ('fm set \<Rightarrow> 'fm set) \<times> 'fm list \<Rightarrow> bool\<close> (infix \<open>\<leadsto>\<^sub>\<box>\<close> 50)
    and hint :: \<open>'fm set \<Rightarrow> bool\<close>
  assumes modal_map: \<open>\<And>ps F qs f. ps \<leadsto>\<^sub>\<box> (F, qs) \<Longrightarrow> \<exists>G. map (map_fm f) ps \<leadsto>\<^sub>\<box> (G, map (map_fm f) qs) \<and>
      (\<forall>S. map_fm f ` F S \<subseteq> G (map_fm f ` S))\<close>
    and modal_mono: \<open>\<And>ps F qs S S'. ps \<leadsto>\<^sub>\<box> (F, qs) \<Longrightarrow> S \<subseteq> S' \<Longrightarrow> F S \<subseteq> F S'\<close>
    and modal_fin: \<open>\<And>ps F qs S A. ps \<leadsto>\<^sub>\<box> (F, qs) \<Longrightarrow> finite A \<Longrightarrow> A \<subseteq> F S \<Longrightarrow> \<exists>S' \<subseteq> S. finite S' \<and> A \<subseteq> F S'\<close>
begin

inductive cond where
  cond [intro!]: \<open>ps \<leadsto>\<^sub>\<box> (F, qs) \<Longrightarrow> cond ps (\<lambda>C S. set qs \<union> F S \<in> C)\<close>

inductive_cases condE[elim!]: \<open>cond ps Q\<close>

abbreviation kind :: \<open>('x, 'fm) kind\<close> where
  \<open>kind \<equiv> Cond cond hint\<close>

end

locale ModalH = Modal map_fm params_fm is_param classify hint
  for
    map_fm :: \<open>('x \<Rightarrow> 'x) \<Rightarrow> 'fm \<Rightarrow> 'fm\<close> and
    params_fm :: \<open>'fm \<Rightarrow> 'x set\<close> and
    is_param :: \<open>'x \<Rightarrow> bool\<close> and
    classify :: \<open>'fm list \<Rightarrow> ('fm set \<Rightarrow> 'fm set) \<times> 'fm list \<Rightarrow> bool\<close> (infix \<open>\<leadsto>\<^sub>\<box>\<close> 50) and
    hint :: \<open>'fm set \<Rightarrow> bool\<close> +
  assumes modal_hintikka: \<open>\<And>C S. sat\<^sub>E kind C \<Longrightarrow> S \<in> C \<Longrightarrow> maximal C S \<Longrightarrow> sat\<^sub>H kind S\<close>

sublocale ModalH \<subseteq> Consistency_Kind map_fm params_fm is_param kind
proof
  fix C
  assume modalC: \<open>sat\<^sub>E kind C\<close>
  then show \<open>sat\<^sub>E kind (close C)\<close>
  proof safe
    fix S ps F qs
    assume \<open>S \<in> close C\<close>
    then obtain S' where S': \<open>S' \<in> C\<close> and \<open>S \<subseteq> S'\<close>
      unfolding close_def by blast

    assume \<open>set ps \<subseteq> S\<close>
    then have *: \<open>set ps \<subseteq> S'\<close>
      using \<open>S \<subseteq> S'\<close> by blast

    assume **: \<open>ps \<leadsto>\<^sub>\<box> (F, qs)\<close>
    then have \<open>set qs \<union> F S' \<in> C\<close>
      using modalC S' * ** by blast
    then show \<open>set qs \<union> F S \<in> close C\<close>
      using \<open>S \<subseteq> S'\<close> subset_in_close ** modal_mono by metis
  qed
next
  fix C
  assume modalC: \<open>sat\<^sub>E kind C\<close> and closedC: \<open>subset_closed C\<close>
  then show \<open>sat\<^sub>A kind (mk_alt_consistency C)\<close>
  proof safe
    fix S ps F qs

    assume \<open>S \<in> mk_alt_consistency C\<close>
    then obtain f where f: \<open>is_subst f\<close> \<open>map_fm f ` S \<in> C\<close>
      unfolding mk_alt_consistency_def by blast

    let ?C = \<open>mk_alt_consistency C\<close>
    let ?S = \<open>map_fm f ` S\<close>

    assume \<open>set ps \<subseteq> S\<close>
    then have *: \<open>set (map (map_fm f) ps) \<subseteq> ?S\<close>
      by auto

    assume **: \<open>ps \<leadsto>\<^sub>\<box> (F, qs)\<close>
    obtain G where G:
      \<open>map (map_fm f) ps \<leadsto>\<^sub>\<box> (G, map (map_fm f) qs)\<close>
      \<open>\<forall>S. map_fm f ` F S \<subseteq> G (map_fm f ` S)\<close>
      using modal_map ** by meson
    then have \<open>set (map (map_fm f) qs) \<union> G ?S \<in> C\<close>
      using modalC f * by blast
    then have \<open>set (map (map_fm f) qs) \<union> map_fm f ` F S \<in> C\<close>
      using G closedC unfolding subset_closed_def by (meson Un_mono order_refl)
    then show \<open>set qs \<union> F S \<in> ?C\<close>
      unfolding mk_alt_consistency_def using f
      by (auto split: option.splits simp: image_Un)
  qed
next
  fix C
  assume modalAC: \<open>sat\<^sub>A kind C\<close> and closedC: \<open>subset_closed C\<close>
  then show \<open>sat\<^sub>A kind (mk_finite_char C)\<close>
  proof safe
    fix S ps F qs t
    assume S: \<open>S \<in> mk_finite_char C\<close>
    then have finc: \<open>\<forall>S' \<subseteq> S. finite S' \<longrightarrow> S' \<in> C\<close>
      unfolding mk_finite_char_def by blast

    have sc: \<open>\<forall>S' \<in> C. \<forall>S \<subseteq> S'. S \<in> C\<close>
      using closedC unfolding subset_closed_def by blast
    then have sc': \<open>\<And>S' x. x \<union> S' \<in> C \<Longrightarrow> \<forall>S \<subseteq> x \<union> S'. S \<in> C\<close>
      by blast

    assume *: \<open>set ps \<subseteq> S\<close> and **: \<open>ps \<leadsto>\<^sub>\<box> (F, qs)\<close>

    show \<open>set qs \<union> F S \<in> mk_finite_char C\<close>
      unfolding mk_finite_char_def 
    proof safe
      fix S'
      assume 1: \<open>S' \<subseteq> set qs \<union> F S\<close> and 2: \<open>finite S'\<close>

      obtain A where A: \<open>A \<subseteq> S\<close> \<open>finite A\<close> \<open>S' \<subseteq> set qs \<union> F A\<close> 
        using 1 2 ** modal_fin by (meson Diff_subset_conv finite_Diff)

      let ?S = \<open>set ps \<union> A\<close>

      have \<open>finite ?S\<close>
        using A(2) by blast
      moreover have \<open>?S \<subseteq> S\<close>
        using * A(1) by simp
      ultimately have \<open>?S \<in> C\<close>
        using finc by simp

      moreover have \<open>set ps \<subseteq> ?S\<close>
        by blast
      ultimately have \<open>set qs \<union> F ?S \<in> C\<close>
        using ** modalAC by blast

      moreover have \<open>S' \<subseteq> set qs \<union> F ?S\<close>
        using A(3) ** modal_mono by (meson Diff_subset_conv inf_sup_ord(4) subset_trans)
      ultimately show \<open>S' \<in> C\<close>
        using sc by blast
    qed
  qed
next
  fix C S
  assume *: \<open>sat\<^sub>E kind C\<close> \<open>S \<in> C\<close> \<open>maximal C S\<close> 
  then show \<open>sat\<^sub>H kind S\<close>
    using modal_hintikka by simp
qed

locale Derivational_Modal = ModalH map_fm params_fm is_param classify
  for
    map_fm :: \<open>('x \<Rightarrow> 'x) \<Rightarrow> 'fm \<Rightarrow> 'fm\<close> and
    params_fm :: \<open>'fm \<Rightarrow> 'x set\<close> and
    is_param :: \<open>'x \<Rightarrow> bool\<close> and
    classify :: \<open>'fm list \<Rightarrow> ('fm set \<Rightarrow> 'fm set) \<times> 'fm list \<Rightarrow> bool\<close> (infix \<open>\<leadsto>\<^sub>\<box>\<close> 50) +
  fixes consistent :: \<open>'fm set \<Rightarrow> bool\<close> (\<open>\<turnstile> _\<close> [51] 50)
  assumes consistent: \<open>\<And>S ps F qs. set ps \<subseteq> S \<Longrightarrow> ps \<leadsto>\<^sub>\<box> (F, qs) \<Longrightarrow> \<turnstile> S \<Longrightarrow> \<turnstile> set qs \<union> F S\<close>
    and params_subset: \<open>\<And>ps F qs S. ps \<leadsto>\<^sub>\<box> (F, qs) \<Longrightarrow> params (F S) \<subseteq> params S\<close>

sublocale Derivational_Modal \<subseteq> Derivational_Kind map_fm params_fm is_param kind consistent
proof
  assume inf: \<open>infinite (UNIV :: 'fm set)\<close>
  then show \<open>sat\<^sub>E kind {A. enough_new A \<and> \<turnstile> A}\<close>
  proof safe
    fix S ps F qs
    assume \<open>ps \<leadsto>\<^sub>\<box> (F, qs)\<close> \<open>enough_new S\<close>
    then have \<open>enough_new (F S)\<close>
      unfolding enough_new_def using params_subset[of ps F qs S] ordLeq_transitive
        card_of_mono1[of "Collect is_param - params S" "Collect is_param - params (F S)"]
      by blast
    then show \<open>enough_new (set qs \<union> F S)\<close>
      using infinite_params_left[OF inf] unfolding enough_new_def by blast
  qed (use consistent in blast)
qed

locale Weak_Derivational_Modal = ModalH map_fm params_fm is_param classify
  for
    map_fm :: \<open>('x \<Rightarrow> 'x) \<Rightarrow> 'fm \<Rightarrow> 'fm\<close> and
    params_fm :: \<open>'fm \<Rightarrow> 'x set\<close> and
    is_param :: \<open>'x \<Rightarrow> bool\<close> and
    classify :: \<open>'fm list \<Rightarrow> ('fm set \<Rightarrow> 'fm set) \<times> 'fm list \<Rightarrow> bool\<close> (infix \<open>\<leadsto>\<^sub>\<box>\<close> 50) +
  fixes consistent :: \<open>'fm list \<Rightarrow> bool\<close> (\<open>\<turnstile> _\<close> [51] 50)
  assumes consistent: \<open>\<And>S ps F qs S'. set ps \<subseteq> set S \<Longrightarrow> ps \<leadsto>\<^sub>\<box> (F, qs) \<Longrightarrow> \<turnstile> S \<Longrightarrow> set S' = F (set S) \<Longrightarrow> \<turnstile> qs @ S'\<close>
    and params_subset: \<open>\<And>ps F qs S. ps \<leadsto>\<^sub>\<box> (F, qs) \<Longrightarrow> params (F S) \<subseteq> params S\<close>
    and F_size: \<open>\<And>ps F qs S. ps \<leadsto>\<^sub>\<box> (F, qs) \<Longrightarrow> |F S| \<le>o |S|\<close>

sublocale Weak_Derivational_Modal \<subseteq> Weak_Derivational_Kind map_fm params_fm is_param kind consistent
proof
  assume inf: \<open>infinite (Collect is_param :: 'x set)\<close>
  show \<open>sat\<^sub>E kind {S. \<exists>A. set A = S \<and> \<turnstile> A}\<close>
  proof safe
    fix ps qs A F
    assume \<open>set ps \<subseteq> set A\<close> \<open>ps \<leadsto>\<^sub>\<box> (F, qs)\<close> \<open>\<turnstile> A\<close>
    then show \<open>\<exists>B. set B = set qs \<union> F (set A) \<and> \<turnstile> B\<close>
      using consistent[of ps A F qs] F_size
      by (metis card_of_ordLeq_infinite finite_list list.set_finite set_append)
  qed
qed

end
