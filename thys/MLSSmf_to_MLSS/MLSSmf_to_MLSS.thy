theory MLSSmf_to_MLSS
  imports MLSS_Extras MLSS_Decision_Proc.MLSS_Semantics
          MLSSmf_Defs Var_Fun_Composite MLSSmf_to_MLSS_Auxiliary MLSSmf_HF_Extras
begin

fun P_plus :: "'a set \<Rightarrow> 'a set set" where
  "P_plus s = Pow s - {{}}"
notation P_plus (\<open>P\<^sup>+\<close>)

lemma P_plus_finite[intro]: "finite S \<Longrightarrow> finite (P\<^sup>+ S)"
  unfolding P_plus.simps by blast

lemma mem_P_plus_finite[intro]: "finite S \<Longrightarrow> s \<in> P\<^sup>+ S \<Longrightarrow> finite s"
  unfolding P_plus.simps
  by (meson Diff_subset PowD finite_subset in_mono)

lemma mem_P_plus_not_empty[intro]: "finite S \<Longrightarrow> s \<in> P\<^sup>+ S \<Longrightarrow> s \<noteq> {}"
  unfolding P_plus.simps by blast

lemma pow_P_plus_finite[intro]: "finite S \<Longrightarrow> finite {s. s \<subseteq> P\<^sup>+ S}"
  unfolding P_plus.simps by blast

lemma pow_of_p_Plus_finite[intro]: "finite V \<Longrightarrow> finite (Pow (P\<^sup>+ V))"
  using vars_finite pow_P_plus_finite by auto

lemma mem_P_plus_subset[intro]: "\<alpha> \<in> P\<^sup>+ V \<Longrightarrow> \<alpha> \<subseteq> V"
  by simp

fun \<L> :: "'v set \<Rightarrow> 'v \<Rightarrow> 'v set set" where
  "\<L> V x = {\<alpha> \<in> P\<^sup>+ V. x \<in> \<alpha>}"

lemma \<L>_subset_P_plus:
  "\<L> V x \<subseteq> P\<^sup>+ V"
  by fastforce

lemma \<L>_finite[intro]: "finite V \<Longrightarrow> finite (\<L> V x)"
  using pow_of_p_Plus_finite by auto

lemma mem_\<L>_finite[intro]:
  assumes "x \<in> V"
    and "finite V"
      and "\<alpha> \<in> \<L> V x"
    shows "finite \<alpha>"
  apply (rule mem_P_plus_finite[where ?S = "V"])
  using \<open>finite V\<close> apply blast
  using assms by simp

lemma mem_\<L>_non_empty[intro]:
  assumes "x \<in> V"
      and "\<alpha> \<in> \<L> V x"
    shows "\<alpha> \<noteq> {}"
proof -
  from assms have "x \<in> \<alpha>" by simp
  then show ?thesis by blast
qed

locale normalized_MLSSmf_clause =
    fixes \<C> :: "('v, 'f) MLSSmf_clause"
  assumes norm_\<C>: "norm_clause \<C>"
begin

definition "V \<equiv> vars\<^sub>m \<C>"
definition "V_list \<equiv> var_list_clause \<C>"
definition "V_set_list \<equiv> filter ((\<noteq>) {}) (map set (subseqs V_list))"
definition "all_V_set_lists \<equiv> subseqs V_set_list"
definition "F \<equiv> funs\<^sub>m \<C>"
definition "F_list \<equiv> fun_list_clause \<C>"
declare V_def V_list_def V_set_list_def F_def F_list_def [simp]

lemma set_V_list: "set V_list = V"
  unfolding V_list_def V_def
  using set_var_list_clause by fast

lemma distinct_V_list: "distinct V_list"
  unfolding V_list_def by simp

lemma finite_V[intro]: "finite V"
  using V_def by auto

fun var_set_to_list :: "'v set \<Rightarrow> 'v list" where
  "var_set_to_list \<alpha> = filter (\<lambda>x. x \<in> \<alpha>) V_list"

lemma set_var_set_to_list[intro]: "\<alpha> \<subseteq> V \<Longrightarrow> set (var_set_to_list \<alpha>) = \<alpha>"
  using V_def V_list_def by auto

lemma distinct_var_set_to_list[intro]: "distinct (var_set_to_list \<alpha>)"
  using V_list_def by simp

lemma set_V_set_list: "set V_set_list = P\<^sup>+ V"
proof -
  have "set (filter ((\<noteq>) {}) (map set (subseqs V_list))) = set (map set (subseqs V_list)) - {{}}"
    by auto
  moreover
  have "P\<^sup>+ V = Pow V - {{}}" by simp
  moreover
  have "set (map set (subseqs V_list)) = Pow V"
    unfolding V_list_def V_def
    by (simp add: subseqs_powset)
  ultimately
  show ?thesis unfolding V_set_list_def by argo
qed

lemma distinct_V_set_list: "distinct V_set_list"
  unfolding V_set_list_def
  using distinct_V_list
  by (simp add: distinct_set_subseqs)

lemma set_all_V_set_lists: "set (map set all_V_set_lists) = Pow (P\<^sup>+ V)"
  unfolding all_V_set_lists_def
  using set_V_set_list
  by (simp add: subseqs_powset)

lemma distinct_all_V_set_lists: "distinct all_V_set_lists"
  unfolding all_V_set_lists_def
  using distinct_V_set_list distinct_subseqs by blast

lemma set_F_list: "set F_list = F"
  unfolding F_list_def F_def using set_fun_list_clause by fast

fun var_set_set_to_var_set_list :: "'v set set \<Rightarrow> 'v set list" where
  "var_set_set_to_var_set_list l = filter (\<lambda>\<alpha>. \<alpha> \<in> l) V_set_list"

lemma var_set_set_to_var_set_list_in_set_all_V_set_lists:
  "var_set_set_to_var_set_list l \<in> set all_V_set_lists"
  unfolding all_V_set_lists_def
  using filter_subseq by auto

lemma set_var_set_set_to_var_set_list[intro]: "l \<subseteq> P\<^sup>+ V \<Longrightarrow> set (var_set_set_to_var_set_list l) = l"
  using set_V_set_list by auto 

lemma distinct_var_set_set_to_var_set_list[intro]: "distinct (var_set_set_to_var_set_list l)"
  using distinct_V_set_list by auto

section \<open>Step 1 and 2: Generate new variables and add the corresponding conditions into the MLSS-formulae\<close>

text \<open>v_\<alpha> = \<Inter>{x\<in>\<alpha>} \ \<Union>{y\<notin>\<alpha>}\<close>

fun restriction_on_InterOfVars :: "'v list \<Rightarrow> ('v, 'f) Composite pset_atom set" where
  "restriction_on_InterOfVars [] = {}"
| "restriction_on_InterOfVars [x] = {Var (InterOfVars [x]) =\<^sub>s Var (Solo x)}"
| "restriction_on_InterOfVars (x # xs) =
   {Var (InterOfVarsAux (x # xs)) =\<^sub>s Var (Solo x) -\<^sub>s Var (InterOfVars xs),
    Var (InterOfVars (x # xs)) =\<^sub>s Var (Solo x) -\<^sub>s Var (InterOfVarsAux (x # xs))} \<union>
   restriction_on_InterOfVars xs"

lemma restriction_on_InterOfVar_finite: "finite (restriction_on_InterOfVars xs)"
  by (induction xs rule: restriction_on_InterOfVars.induct) auto

lemma restriction_on_InterOfVar_normalized: "normalized_MLSS_clause (AT ` restriction_on_InterOfVars xs)"
proof
  have "normalized_MLSS_literal lt" if "lt \<in> AT ` restriction_on_InterOfVars xs" for lt
    using that
    apply (induction xs rule: restriction_on_InterOfVars.induct)
      apply simp_all
      apply (meson normalized_MLSS_literal.eq)
     apply (meson normalized_MLSS_literal.diff)
    done
  then show "\<forall>lt\<in>AT ` restriction_on_InterOfVars xs. normalized_MLSS_literal lt"
    by blast
  from restriction_on_InterOfVar_finite show "finite (AT ` restriction_on_InterOfVars xs)"
    by auto
qed

lemma eval_InterOfVars:
  assumes "\<forall>a \<in> restriction_on_InterOfVars vs. I\<^sub>s\<^sub>a M a"
      and "vs \<noteq> []"
    shows "M (InterOfVars vs) = \<Sqinter>HF ((M \<circ> Solo) ` set vs)"
  using assms
proof (induction vs rule: restriction_on_InterOfVars.induct)
  case (2 x)
  then have "I\<^sub>s\<^sub>a M (Var (InterOfVars [x]) =\<^sub>s Var (Solo x))" by simp
  then have "M (InterOfVars [x]) = M (Solo x)" by simp
  moreover
  have "\<Sqinter>HF ((M \<circ> Solo) ` set [x]) = M (Solo x)"
    using HInter_singleton by auto
  ultimately
  show ?case by argo
next
  case (3 y x xs)
  then have IH: "M (InterOfVars (x # xs)) = \<Sqinter>HF ((M \<circ> Solo) ` set (x # xs))"
    by fastforce
  from "3.prems"(1) have "M (InterOfVars (y # x # xs)) = M (Solo y) \<sqinter> M (InterOfVars (x # xs))"
    by auto
  also have "... = M (Solo y) \<sqinter> \<Sqinter>HF ((M \<circ> Solo) ` set (x # xs))"
    using IH by presburger
  also have "... = \<Sqinter> (HF ((M \<circ> Solo) ` set (x # xs)) \<triangleleft> M (Solo y))"
    using HInter_def by force
  also have "... = \<Sqinter>HF ((M \<circ> Solo) ` (insert y (set (x # xs))))"
    using hinsert_def by auto
  also have "... = \<Sqinter> (HF ((M \<circ> Solo) ` set (y # x # xs)))"
    by simp
  finally show ?case .
qed blast

fun restriction_on_UnionOfVars :: "'v list \<Rightarrow> ('v, 'f) Composite pset_atom set" where
  "restriction_on_UnionOfVars [] = {Var (UnionOfVars []) =\<^sub>s \<emptyset> 0}"
| "restriction_on_UnionOfVars (x # xs) =
   insert (Var (UnionOfVars (x # xs)) =\<^sub>s Var (Solo x) \<squnion>\<^sub>s Var (UnionOfVars xs))
   (restriction_on_UnionOfVars xs)"

lemma restriction_on_UnionOfVar_finite: "finite (restriction_on_UnionOfVars xs)"
  by (induction xs) auto

lemma restriction_on_UnionOfVar_normalized: "normalized_MLSS_clause (AT ` restriction_on_UnionOfVars xs)"
proof
  have "normalized_MLSS_literal lt" if "lt \<in> AT ` restriction_on_UnionOfVars xs" for lt
    using that
    apply (induction xs rule: restriction_on_UnionOfVars.induct)
     apply simp_all
     apply (meson normalized_MLSS_literal.eq_empty)
    apply (meson normalized_MLSS_literal.union)
    done
  then show "\<forall>lt\<in>AT ` restriction_on_UnionOfVars xs. normalized_MLSS_literal lt"
    by blast
  from restriction_on_UnionOfVar_finite show "finite (AT ` restriction_on_UnionOfVars xs)"
    by auto
qed

lemma eval_UnionOfVar:
  assumes "\<forall>a \<in> restriction_on_UnionOfVars vs. I\<^sub>s\<^sub>a M a"
    shows "M (UnionOfVars vs) = \<Squnion>HF ((M \<circ> Solo) ` set vs)"
  using assms
proof (induction vs rule: restriction_on_UnionOfVars.induct)
  case (2 x xs)
  then have IH: "M (UnionOfVars xs) = \<Squnion>HF ((M \<circ> Solo) ` set xs)"
    by fastforce
  from "2.prems" have "M (UnionOfVars (x # xs)) = M (Solo x) \<squnion> M (UnionOfVars xs)"
    by simp
  also have "... = M (Solo x) \<squnion> \<Squnion>HF ((M \<circ> Solo) ` set xs)"
    using IH by presburger
  also have "... = \<Squnion> (HF ((M \<circ> Solo) ` set xs) \<triangleleft> M (Solo x))"
    using HInter_def by force
  also have "... = \<Squnion>HF ((M \<circ> Solo) ` (insert x (set xs)))"
    using hinsert_def by auto
  also have "... = \<Squnion> (HF ((M \<circ> Solo) ` set (x # xs)))"
    by simp
  finally show ?case .
qed auto

fun restriction_on_v :: "'v set \<Rightarrow> ('v, 'f) Composite pset_atom" where
  "restriction_on_v \<alpha> =
   Var v\<^bsub>\<alpha>\<^esub> =\<^sub>s Var (InterOfVars (var_set_to_list \<alpha>)) -\<^sub>s Var (UnionOfVars (var_set_to_list (V - \<alpha>)))"

lemma v_\<alpha>_in_vars_restriction_on_v: "v\<^bsub>\<alpha>\<^esub> \<in> vars (restriction_on_v \<alpha>)"
  by simp

definition introduce_v :: "('v, 'f) Composite pset_fm set" where
  "introduce_v \<equiv> AT `
    (restriction_on_v ` (P\<^sup>+ V) \<union>
    \<Union> ((restriction_on_InterOfVars \<circ> var_set_to_list) ` (P\<^sup>+ V)) \<union>
    \<Union> ((restriction_on_UnionOfVars \<circ> var_set_to_list) ` (Pow V)))"

lemma introduce_v_finite: "finite introduce_v"
proof -
  have "finite (P\<^sup>+ V)" by blast
  then have "finite (restriction_on_v ` (P\<^sup>+ V))" by blast
  moreover
  from restriction_on_InterOfVar_finite \<open>finite (P\<^sup>+ V)\<close>
  have "finite (\<Union> ((restriction_on_InterOfVars \<circ> var_set_to_list) ` (P\<^sup>+ V)))"
    by auto
  moreover
  from restriction_on_UnionOfVar_finite finite_V
  have "finite (\<Union> ((restriction_on_UnionOfVars \<circ> var_set_to_list) ` (Pow V)))"
    by force
  ultimately
  show ?thesis unfolding introduce_v_def by auto
qed

lemma introduce_v_normalized: "normalized_MLSS_clause introduce_v"
proof
  have "\<forall>lt \<in> AT ` (restriction_on_v ` P\<^sup>+ V). normalized_MLSS_literal lt"
    by auto (meson normalized_MLSS_literal.diff)
  moreover
  from restriction_on_InterOfVar_normalized
  have "\<forall>\<alpha> \<in> P\<^sup>+ V. \<forall>lt \<in> AT ` (restriction_on_InterOfVars \<circ> var_set_to_list) \<alpha>. normalized_MLSS_literal lt"
    using normalized_MLSS_clause.norm_\<C> by fastforce
  then have "\<forall>lt \<in> AT ` \<Union> ((restriction_on_InterOfVars \<circ> var_set_to_list) ` P\<^sup>+ V). normalized_MLSS_literal lt"
    by blast
  moreover
  from restriction_on_UnionOfVar_normalized
  have "\<forall>\<alpha> \<in> Pow V. \<forall>lt \<in> AT ` (restriction_on_UnionOfVars \<circ> var_set_to_list) \<alpha>. normalized_MLSS_literal lt"
    using normalized_MLSS_clause.norm_\<C> by fastforce
  then have "\<forall>lt \<in> AT ` \<Union> ((restriction_on_UnionOfVars \<circ> var_set_to_list) ` Pow V). normalized_MLSS_literal lt"
    by blast
  ultimately
  show "\<forall>lt \<in> introduce_v. normalized_MLSS_literal lt"
    unfolding introduce_v_def
    by (metis UnE image_Un)

  from introduce_v_finite show "finite introduce_v" by blast
qed

lemma v_\<alpha>_in_vars_introduce_v:
  "\<alpha> \<in> P\<^sup>+ V \<Longrightarrow> \<exists>a \<in> introduce_v. v\<^bsub>\<alpha>\<^esub> \<in> vars a"
proof -
  assume "\<alpha> \<in> P\<^sup>+ V"
  then have "AT (restriction_on_v \<alpha>) \<in> introduce_v"
    unfolding introduce_v_def by force
  moreover
  from v_\<alpha>_in_vars_restriction_on_v have "v\<^bsub>\<alpha>\<^esub> \<in> vars (restriction_on_v \<alpha>)" by fast
  then have "v\<^bsub>\<alpha>\<^esub> \<in> vars (AT (restriction_on_v \<alpha>))" by simp
  ultimately
  have "AT (restriction_on_v \<alpha>) \<in> introduce_v \<and> v\<^bsub>\<alpha>\<^esub> \<in> vars (AT (restriction_on_v \<alpha>))"
    by fastforce
  then show "\<exists>a \<in> introduce_v. v\<^bsub>\<alpha>\<^esub> \<in> vars a" by blast
qed

lemma eval_v:
  assumes "\<alpha> \<in> P\<^sup>+ V"
      and M_model: "\<forall>fm \<in> introduce_v. interp I\<^sub>s\<^sub>a M fm"
    shows "M v\<^bsub>\<alpha>\<^esub> = \<Sqinter>HF ((M \<circ> Solo) ` \<alpha>) - \<Squnion>HF ((M \<circ> Solo) ` (V - \<alpha>))"
proof -
  from \<open>\<alpha> \<in> P\<^sup>+ V\<close> have "set (var_set_to_list \<alpha>) = \<alpha>"
    by (meson mem_P_plus_subset set_var_set_to_list)
  have "V - \<alpha> \<subseteq> V" by blast
  with set_var_set_to_list have "set (var_set_to_list (V - \<alpha>)) = V - \<alpha>" by presburger
  from \<open>\<alpha> \<in> P\<^sup>+ V\<close> have "\<alpha> \<noteq> {}" by simp
  with \<open>set (var_set_to_list \<alpha>) = \<alpha>\<close> have "var_set_to_list \<alpha> \<noteq> []" by fastforce

  from \<open>\<alpha> \<in> P\<^sup>+ V\<close> have "AT (restriction_on_v \<alpha>) \<in> introduce_v" unfolding introduce_v_def by auto
  with M_model have "I\<^sub>s\<^sub>a M (restriction_on_v \<alpha>)" by fastforce
  then have "M v\<^bsub>\<alpha>\<^esub> = M (InterOfVars (var_set_to_list \<alpha>)) - M (UnionOfVars (var_set_to_list (V - \<alpha>)))"
    by simp
  moreover
  from \<open>\<alpha> \<in> P\<^sup>+ V\<close> have "AT ` (restriction_on_InterOfVars (var_set_to_list \<alpha>)) \<subseteq> introduce_v"
    unfolding introduce_v_def by auto
  with M_model have "\<forall>a\<in>restriction_on_InterOfVars (var_set_to_list \<alpha>). interp I\<^sub>s\<^sub>a M (AT a)"
    by blast
  then have "\<forall>a\<in>restriction_on_InterOfVars (var_set_to_list \<alpha>). I\<^sub>s\<^sub>a M a" by auto
  with eval_InterOfVars[where ?vs = "var_set_to_list \<alpha>" and ?M = M] M_model
  have "M (InterOfVars (var_set_to_list \<alpha>)) = \<Sqinter>HF ((M \<circ> Solo) ` set (var_set_to_list \<alpha>))"
    using \<open>var_set_to_list \<alpha> \<noteq> []\<close> by blast
  with \<open>set (var_set_to_list \<alpha>) = \<alpha>\<close> have "M (InterOfVars (var_set_to_list \<alpha>)) = \<Sqinter>HF ((M \<circ> Solo) ` \<alpha>)"
    by presburger
  moreover
  from \<open>\<alpha> \<in> P\<^sup>+ V\<close> have "V - \<alpha> \<in> Pow V" by blast
  then have "AT ` (restriction_on_UnionOfVars (var_set_to_list (V - \<alpha>))) \<subseteq> introduce_v"
    unfolding introduce_v_def
    by (smt (verit) UN_absorb comp_eq_dest_lhs image_Un sup.absorb_iff2 sup_assoc sup_commute)
  with M_model have "\<forall>a\<in>restriction_on_UnionOfVars (var_set_to_list (V - \<alpha>)). interp I\<^sub>s\<^sub>a M (AT a)"
    by blast
  then have "\<forall>a\<in>(restriction_on_UnionOfVars (var_set_to_list (V - \<alpha>))). I\<^sub>s\<^sub>a M a" by auto
  with eval_UnionOfVar[where ?vs = "var_set_to_list (V - \<alpha>)" and ?M = M] M_model
  have "M (UnionOfVars (var_set_to_list (V - \<alpha>))) = \<Squnion>HF ((M \<circ> Solo) ` set (var_set_to_list (V - \<alpha>)))"
    by blast
  with \<open>set (var_set_to_list (V - \<alpha>)) = V - \<alpha>\<close>
  have "M (UnionOfVars (var_set_to_list (V - \<alpha>))) = \<Squnion>HF ((M \<circ> Solo) ` (V - \<alpha>))"
    by presburger
  ultimately
  show ?thesis by argo
qed

lemma v_subset_Inter_of_values:
  assumes "\<alpha> \<noteq> {}"
      and "\<alpha> \<subseteq> V"
      and "\<forall>fm\<in>introduce_v. interp I\<^sub>s\<^sub>a M fm"
    shows "M (v\<^bsub>\<alpha>\<^esub>) \<le> \<Sqinter>HF (M ` (Solo ` \<alpha>))"
proof -
  from assms have "\<alpha> \<in> P\<^sup>+ V" by auto
  with eval_v assms have "M (v\<^bsub>\<alpha>\<^esub>) = \<Sqinter>HF ((M \<circ> Solo) ` \<alpha>) - \<Squnion>HF ((M \<circ> Solo) ` (V - \<alpha>))"
    by blast
  then have "M (v\<^bsub>\<alpha>\<^esub>) \<le> \<Sqinter>HF ((M \<circ> Solo) ` \<alpha>)" by auto
  then show ?thesis
    by (simp add: image_comp)
qed

fun restriction_on_UnionOfVennRegions :: "'v set list \<Rightarrow> ('v, 'f) Composite pset_atom set" where
  "restriction_on_UnionOfVennRegions [] = {Var (UnionOfVennRegions []) =\<^sub>s \<emptyset> 0}"
| "restriction_on_UnionOfVennRegions (\<alpha> # \<alpha>s) =
   insert (Var (UnionOfVennRegions (\<alpha> # \<alpha>s)) =\<^sub>s (Var v\<^bsub>\<alpha>\<^esub>) \<squnion>\<^sub>s (Var (UnionOfVennRegions \<alpha>s)))
   (restriction_on_UnionOfVennRegions \<alpha>s)"

definition "introduce_UnionOfVennRegions \<equiv> AT ` \<Union> (restriction_on_UnionOfVennRegions ` set all_V_set_lists)"

lemma introduce_UnionOfVennRegions_normalized: "normalized_MLSS_clause introduce_UnionOfVennRegions"
proof
  have "normalized_MLSS_literal lt" if "lt \<in> AT ` restriction_on_UnionOfVennRegions \<alpha>s" for lt \<alpha>s
    using that
    apply (induction \<alpha>s rule: restriction_on_UnionOfVennRegions.induct)
     apply simp_all
     apply (meson normalized_MLSS_literal.eq_empty)
    apply (meson normalized_MLSS_literal.union)
    done
  then show "\<forall>lt\<in>introduce_UnionOfVennRegions. normalized_MLSS_literal lt"
    unfolding introduce_UnionOfVennRegions_def
    by blast

  have "finite (restriction_on_UnionOfVennRegions \<alpha>s)" for \<alpha>s
    by (induction \<alpha>s) auto
  moreover
  have "finite (set all_V_set_lists)" by blast
  ultimately
  have "finite (\<Union> (restriction_on_UnionOfVennRegions ` set all_V_set_lists))"
    by simp
  then show "finite introduce_UnionOfVennRegions"
    unfolding introduce_UnionOfVennRegions_def by blast
qed

lemma eval_UnionOfVennRegions:
  assumes "\<forall>a \<in> restriction_on_UnionOfVennRegions \<alpha>s. I\<^sub>s\<^sub>a M a"
    shows "M (UnionOfVennRegions \<alpha>s) = \<Squnion>HF ((M \<circ> VennRegion) ` set \<alpha>s)"
  using assms
proof (induction \<alpha>s rule: restriction_on_UnionOfVennRegions.induct)
  case (2 \<alpha> \<alpha>s)
  then have IH: "M (UnionOfVennRegions \<alpha>s) = \<Squnion>HF ((M \<circ> VennRegion) ` set \<alpha>s)"
    by fastforce
  from "2.prems" have "I\<^sub>s\<^sub>a M (Var (UnionOfVennRegions (\<alpha> # \<alpha>s)) =\<^sub>s (Var v\<^bsub>\<alpha>\<^esub>) \<squnion>\<^sub>s (Var (UnionOfVennRegions \<alpha>s)))"
    by auto
  then have "M (UnionOfVennRegions (\<alpha> # \<alpha>s)) = M v\<^bsub>\<alpha>\<^esub> \<squnion> M (UnionOfVennRegions \<alpha>s)"
    by simp
  also have "... = M v\<^bsub>\<alpha>\<^esub> \<squnion> \<Squnion>HF ((M \<circ> VennRegion) ` set \<alpha>s)"
    using IH by presburger
  also have "... = \<Squnion> (HF ((M \<circ> VennRegion) ` set \<alpha>s) \<triangleleft> M v\<^bsub>\<alpha>\<^esub>)"
    using HInter_def by force
  also have "... = \<Squnion>HF ((M \<circ> VennRegion) ` (insert \<alpha> (set \<alpha>s)))"
    using hinsert_def by auto
  also have "... = \<Squnion>HF ((M \<circ> VennRegion) ` set (\<alpha> # \<alpha>s))"
    by simp
  finally show ?case .
qed auto

text \<open>\<Union>{v_\<alpha> | \<alpha> \<in> l} = \<Union>{v_\<beta> | \<beta> \<in> m} ==> w_{f,l} = w_{f, m}\<close>
fun restriction_on_FunOfUnionOfVennRegions :: "'v set list \<Rightarrow> 'v set list \<Rightarrow> 'f \<Rightarrow> ('v, 'f) Composite pset_fm list" where
  "restriction_on_FunOfUnionOfVennRegions l m f = [
    AF (Var (UnionOfVennRegions l) =\<^sub>s Var (UnionOfVennRegions m)),
    AT (Var w\<^bsub>f\<^esub>\<^bsub>set l\<^esub> =\<^sub>s Var w\<^bsub>f\<^esub>\<^bsub>set m\<^esub>)]"

lemma restriction_on_FunOfUnionOfVennRegions_normalized:
  "\<forall>lt \<in> set (restriction_on_FunOfUnionOfVennRegions l m f). normalized_MLSS_literal lt"
  apply simp_all
   apply (meson normalized_MLSS_literal.neq)
  apply (meson normalized_MLSS_literal.eq)
  done

fun choices_from_lists :: "'a list list \<Rightarrow> 'a list list" where
  "choices_from_lists [] = [[]]" |
  "choices_from_lists (xs # xss) = [x # ys. x \<leftarrow> xs, ys \<leftarrow> choices_from_lists xss]"

lemma choices_from_lists_complete:
  "\<forall>choice \<in> set (choices_from_lists xss). \<forall>xs \<in> set xss. \<exists>x \<in> set xs. x \<in> set choice"
  by (induction xss) auto

lemma choices_from_lists_sound:
  "\<forall>choice \<in> set (choices_from_lists xss). \<forall>x \<in> set choice. \<exists>xs \<in> set xss. x \<in> set xs"
  by (induction xss) auto

lemma valid_choice:
  assumes "\<forall>x \<in> set xs. f (g x) \<in> set (g x)"
    shows "map f (map g xs) \<in> set (choices_from_lists (map g xs))"
  using assms by (induction xs) auto

definition introduce_w :: "('v, 'f) Composite pset_fm set set" where
  "introduce_w \<equiv> set (map set (choices_from_lists (map
     (\<lambda>(l, m, f). restriction_on_FunOfUnionOfVennRegions l m f)
     (List.product all_V_set_lists (List.product all_V_set_lists F_list)))))"

lemma introduce_w_finite: "finite introduce_w \<and> (\<forall>fms \<in> introduce_w. finite fms)"
  unfolding introduce_w_def by auto

lemma introduce_w_normalized: "\<forall>clause \<in> introduce_w. normalized_MLSS_clause clause"
proof
  let ?fms_before_norm = "(map
     (\<lambda>(l, m, f). restriction_on_FunOfUnionOfVennRegions l m f)
     (List.product all_V_set_lists (List.product all_V_set_lists F_list)))"

  fix clause assume "clause \<in> introduce_w"
  then obtain choice where choice:
    "choice \<in> set (choices_from_lists ?fms_before_norm)" "clause = set choice"
    unfolding introduce_w_def by auto
  then have "normalized_MLSS_literal lt" if "lt \<in> set choice" for lt
    using that choices_from_lists_sound
    using restriction_on_FunOfUnionOfVennRegions_normalized
    by fastforce
  moreover
  from choice have "finite clause" by blast
  ultimately
  show "normalized_MLSS_clause clause"
    using \<open>clause = set choice\<close>
    by unfold_locales blast+
qed

lemma eval_w:
  assumes M_w: "\<exists>fms \<in> introduce_w. \<forall>fm \<in> fms. interp I\<^sub>s\<^sub>a M fm"
      and M_UnV: "\<forall>fm \<in> introduce_UnionOfVennRegions. interp I\<^sub>s\<^sub>a M fm"
    shows "\<forall>l \<subseteq> P\<^sup>+ V. \<forall>m \<subseteq> P\<^sup>+ V. \<forall>f \<in> F.
           \<Squnion>HF ((M \<circ> VennRegion) ` l) = \<Squnion>HF ((M \<circ> VennRegion) ` m) \<longrightarrow>
           M w\<^bsub>f\<^esub>\<^bsub>l\<^esub> = M w\<^bsub>f\<^esub>\<^bsub>m\<^esub>"
proof -
  let ?fms_before_norm = "map
     (\<lambda>(l, m, f). restriction_on_FunOfUnionOfVennRegions l m f)
     (List.product all_V_set_lists (List.product all_V_set_lists F_list))"
  from M_w obtain fms where "fms \<in> introduce_w" "\<forall>fm \<in> fms. interp I\<^sub>s\<^sub>a M fm"
    by blast
  from \<open>fms \<in> introduce_w\<close> obtain clause where "fms = set clause" "clause \<in> set (choices_from_lists ?fms_before_norm)"
    unfolding introduce_w_def by auto
  with choices_from_lists_complete
  have "\<forall>restriction_on_w \<in> set ?fms_before_norm. \<exists>fm \<in> set restriction_on_w. fm \<in> set clause"
    by blast
  with \<open>fms = set clause\<close> have "\<forall>restriction_on_w \<in> set ?fms_before_norm. \<exists>fm \<in> set restriction_on_w. fm \<in> fms"
    by blast
  with \<open>\<forall>fm \<in> fms. interp I\<^sub>s\<^sub>a M fm\<close> have restriction_on_w_all_hold:
    "\<forall>restriction_on_w \<in> set ?fms_before_norm. \<exists>fm \<in> set restriction_on_w. interp I\<^sub>s\<^sub>a M fm"
    by fast

  from set_all_V_set_lists have "restriction_on_UnionOfVennRegions (var_set_set_to_var_set_list l) \<subseteq>
                                 \<Union> (restriction_on_UnionOfVennRegions ` set all_V_set_lists)"
    if "l \<subseteq> P\<^sup>+ V" for l
    using that set_var_set_set_to_var_set_list var_set_set_to_var_set_list_in_set_all_V_set_lists
    by (meson Union_upper image_iff)
  with M_UnV have "\<forall>a\<in>restriction_on_UnionOfVennRegions (var_set_set_to_var_set_list l). I\<^sub>s\<^sub>a M a"
    if "l \<subseteq> P\<^sup>+ V" for l
    using that unfolding introduce_UnionOfVennRegions_def
    using var_set_set_to_var_set_list_in_set_all_V_set_lists by auto
  with eval_UnionOfVennRegions[of "var_set_set_to_var_set_list l" for l]
  have eval_UnV: "M (UnionOfVennRegions (var_set_set_to_var_set_list l)) = \<Squnion>HF ((M \<circ> VennRegion) ` l)"
    if "l \<subseteq> P\<^sup>+ V" for l
    using that set_var_set_set_to_var_set_list by metis
  
  {fix l m f assume lmf: "l \<subseteq> P\<^sup>+ V" "m \<subseteq> P\<^sup>+ V" "f \<in> F"
    let ?l = "var_set_set_to_var_set_list l"
    let ?m = "var_set_set_to_var_set_list m"
    have "(?l, ?m, f) \<in> set (List.product all_V_set_lists (List.product all_V_set_lists F_list))"
      using lmf set_F_list var_set_set_to_var_set_list_in_set_all_V_set_lists
      by simp
    then have "restriction_on_FunOfUnionOfVennRegions ?l ?m f \<in> set ?fms_before_norm"
      by force
    with restriction_on_w_all_hold
    have "\<exists>fm \<in> set (restriction_on_FunOfUnionOfVennRegions ?l ?m f). interp I\<^sub>s\<^sub>a M fm"
      by blast
    then have "interp I\<^sub>s\<^sub>a M (AF (Var (UnionOfVennRegions ?l) =\<^sub>s Var (UnionOfVennRegions ?m))) \<or>
               interp I\<^sub>s\<^sub>a M (AT (Var w\<^bsub>f\<^esub>\<^bsub>l\<^esub> =\<^sub>s Var w\<^bsub>f\<^esub>\<^bsub>m\<^esub>))"
      using lmf set_var_set_set_to_var_set_list by auto
    then have "M (UnionOfVennRegions ?l) \<noteq> M (UnionOfVennRegions ?m) \<or> M w\<^bsub>f\<^esub>\<^bsub>l\<^esub> = M w\<^bsub>f\<^esub>\<^bsub>m\<^esub>"
      by auto
    then have "M (UnionOfVennRegions ?l) = M (UnionOfVennRegions ?m) \<longrightarrow> M w\<^bsub>f\<^esub>\<^bsub>l\<^esub> = M w\<^bsub>f\<^esub>\<^bsub>m\<^esub>"
      by blast
    with eval_UnV lmf
    have "\<Squnion>HF ((M \<circ> VennRegion) ` l) = \<Squnion>HF ((M \<circ> VennRegion) ` m) \<longrightarrow>  M w\<^bsub>f\<^esub>\<^bsub>l\<^esub> = M w\<^bsub>f\<^esub>\<^bsub>m\<^esub>"
      by presburger
  }
  then show ?thesis by blast
qed

lemma lt_in_clause_in_introduce_w_E:
  assumes "\<exists>clause \<in> introduce_w. lt \<in> clause"
  shows "\<exists>l' m' f. l' \<in> set all_V_set_lists \<and> m' \<in> set all_V_set_lists \<and> f \<in> set F_list \<and>
                   lt \<in> set (restriction_on_FunOfUnionOfVennRegions l' m' f)"
proof -
  let ?xss = "map
    (\<lambda>(l, m, f). restriction_on_FunOfUnionOfVennRegions l m f)
    (List.product all_V_set_lists (List.product all_V_set_lists F_list))"
  from assms obtain clause where "clause \<in> introduce_w" "lt \<in> clause"
    by blast
  with choices_from_lists_sound obtain fms where "fms \<in> set ?xss" "lt \<in> set fms"
    unfolding introduce_w_def by force
  then show ?thesis by fastforce
qed

section \<open>Step 3: reduce each literal into MLSS\<close>

fun reduce_atom :: "('v, 'f) MLSSmf_atom \<Rightarrow> ('v, 'f) Composite pset_atom set" where
  "reduce_atom (Var\<^sub>m x \<in>\<^sub>m Var\<^sub>m y) = {
     Var (MemAux x) =\<^sub>s Single (Var (Solo x)),
     Var (Solo y) =\<^sub>s Var (Solo y) \<squnion>\<^sub>s Var (MemAux x)}" |
  "reduce_atom (Var\<^sub>m x =\<^sub>m App f (Var\<^sub>m y)) = {Var (Solo x) =\<^sub>s Var w\<^bsub>f\<^esub>\<^bsub>\<L> V y\<^esub>}" |
  "reduce_atom (Var\<^sub>m x =\<^sub>m Var\<^sub>m y \<squnion>\<^sub>m Var\<^sub>m z) = {Var (Solo x) =\<^sub>s Var (Solo y) \<squnion>\<^sub>s Var (Solo z)}" |
  "reduce_atom (Var\<^sub>m x =\<^sub>m Var\<^sub>m y -\<^sub>m Var\<^sub>m z) = {Var (Solo x) =\<^sub>s Var (Solo y) -\<^sub>s Var (Solo z)}" |
  "reduce_atom (Var\<^sub>m x =\<^sub>m Single\<^sub>m (Var\<^sub>m y)) = {Var (Solo x) =\<^sub>s Single (Var (Solo y))}" |
  "reduce_atom (Var\<^sub>m x =\<^sub>m Var\<^sub>m y) = {Var (Solo x) =\<^sub>s Var (Solo y)}" |
  "reduce_atom (Var\<^sub>m x =\<^sub>m \<emptyset>\<^sub>m n) = {Var (Solo x) =\<^sub>s \<emptyset> n}" |
  "reduce_atom (inc(f)) = {Var w\<^bsub>f\<^esub>\<^bsub>m\<^esub> =\<^sub>s Var w\<^bsub>f\<^esub>\<^bsub>m\<^esub> \<squnion>\<^sub>s Var w\<^bsub>f\<^esub>\<^bsub>l\<^esub> |l m.
                             l \<subseteq> P\<^sup>+ V \<and> m \<subseteq> P\<^sup>+ V \<and> l \<subseteq> m}" |
  "reduce_atom (dec(f)) = {Var w\<^bsub>f\<^esub>\<^bsub>l\<^esub> =\<^sub>s Var w\<^bsub>f\<^esub>\<^bsub>l\<^esub> \<squnion>\<^sub>s Var w\<^bsub>f\<^esub>\<^bsub>m\<^esub> |l m.
                             l \<subseteq> P\<^sup>+ V \<and> m \<subseteq> P\<^sup>+ V \<and> l \<subseteq> m}" |
  "reduce_atom (add(f)) = {Var w\<^bsub>f\<^esub>\<^bsub>l\<union>m\<^esub> =\<^sub>s Var w\<^bsub>f\<^esub>\<^bsub>l\<^esub> \<squnion>\<^sub>s Var w\<^bsub>f\<^esub>\<^bsub>m\<^esub> |l m.
                             l \<subseteq> P\<^sup>+ V \<and> m \<subseteq> P\<^sup>+ V}" |
  "reduce_atom (mul(f)) =
     {Var (InterOfWAux f l m) =\<^sub>s Var w\<^bsub>f\<^esub>\<^bsub>l\<^esub> -\<^sub>s Var w\<^bsub>f\<^esub>\<^bsub>m\<^esub> |l m. l \<subseteq> P\<^sup>+ V \<and> m \<subseteq> P\<^sup>+ V} \<union>
     {Var w\<^bsub>f\<^esub>\<^bsub>l\<inter>m\<^esub> =\<^sub>s Var w\<^bsub>f\<^esub>\<^bsub>l\<^esub> -\<^sub>s Var (InterOfWAux f l m) |l m. l \<subseteq> P\<^sup>+ V \<and> m \<subseteq> P\<^sup>+ V}" |
  "reduce_atom (f \<preceq>\<^sub>m g) = {Var w\<^bsub>g\<^esub>\<^bsub>l\<^esub> =\<^sub>s Var w\<^bsub>g\<^esub>\<^bsub>l\<^esub> \<squnion>\<^sub>s Var w\<^bsub>f\<^esub>\<^bsub>l\<^esub> |l. l \<subseteq> P\<^sup>+ V}" |
  "reduce_atom _ = {}"

lemma reduce_atom_finite: "finite (reduce_atom a)"
  apply (cases a rule: reduce_atom.cases)
                      apply (simp_all del: P_plus.simps)
proof (goal_cases)
  case (1 f)
  have "{Var w\<^bsub>f\<^esub>\<^bsub>m\<^esub> =\<^sub>s Var w\<^bsub>f\<^esub>\<^bsub>m\<^esub> \<squnion>\<^sub>s Var w\<^bsub>f\<^esub>\<^bsub>l\<^esub> |l m. l \<subseteq> P\<^sup>+ V \<and> m \<subseteq> P\<^sup>+ V \<and> l \<subseteq> m} \<subseteq>
        (\<lambda>(l, m). Var w\<^bsub>f\<^esub>\<^bsub>m\<^esub> =\<^sub>s Var w\<^bsub>f\<^esub>\<^bsub>m\<^esub> \<squnion>\<^sub>s Var w\<^bsub>f\<^esub>\<^bsub>l\<^esub>) ` ((Pow (P\<^sup>+ V)) \<times> (Pow (P\<^sup>+ V)))"
    by force
  moreover
  from pow_of_p_Plus_finite have "finite ((Pow (P\<^sup>+ V)) \<times> (Pow (P\<^sup>+ V)))"
    by blast
  then have "finite ((\<lambda>(l, m). Var w\<^bsub>f\<^esub>\<^bsub>m\<^esub> =\<^sub>s Var w\<^bsub>f\<^esub>\<^bsub>m\<^esub> \<squnion>\<^sub>s Var w\<^bsub>f\<^esub>\<^bsub>l\<^esub>) ` ((Pow (P\<^sup>+ V)) \<times> (Pow (P\<^sup>+ V))))"
    by blast
  ultimately
  show ?case by fastforce
next
  case (2 f)
  have "{Var w\<^bsub>f\<^esub>\<^bsub>l\<^esub> =\<^sub>s Var w\<^bsub>f\<^esub>\<^bsub>l\<^esub> \<squnion>\<^sub>s Var w\<^bsub>f\<^esub>\<^bsub>m\<^esub> |l m. l \<subseteq> P\<^sup>+ V \<and> m \<subseteq> P\<^sup>+ V \<and> l \<subseteq> m} \<subseteq>
        (\<lambda>(l, m). Var w\<^bsub>f\<^esub>\<^bsub>m\<^esub> =\<^sub>s Var w\<^bsub>f\<^esub>\<^bsub>m\<^esub> \<squnion>\<^sub>s Var w\<^bsub>f\<^esub>\<^bsub>l\<^esub>) ` ((Pow (P\<^sup>+ V)) \<times> (Pow (P\<^sup>+ V)))"
    by force
  moreover
  from pow_of_p_Plus_finite have "finite ((Pow (P\<^sup>+ V)) \<times> (Pow (P\<^sup>+ V)))"
    by blast
  then have "finite ((\<lambda>(l, m). Var w\<^bsub>f\<^esub>\<^bsub>l\<^esub> =\<^sub>s Var w\<^bsub>f\<^esub>\<^bsub>l\<^esub> \<squnion>\<^sub>s Var w\<^bsub>f\<^esub>\<^bsub>m\<^esub>) ` ((Pow (P\<^sup>+ V)) \<times> (Pow (P\<^sup>+ V))))"
    by blast
  ultimately
  show ?case by fastforce
next
  case (3 f)
  have "{Var w\<^bsub>f\<^esub>\<^bsub>l \<union> m\<^esub> =\<^sub>s Var w\<^bsub>f\<^esub>\<^bsub>l\<^esub> \<squnion>\<^sub>s Var w\<^bsub>f\<^esub>\<^bsub>m\<^esub> |l m. l \<subseteq> P\<^sup>+ V \<and> m \<subseteq> P\<^sup>+ V} =
        (\<lambda>(l, m). Var w\<^bsub>f\<^esub>\<^bsub>l \<union> m\<^esub> =\<^sub>s Var w\<^bsub>f\<^esub>\<^bsub>l\<^esub> \<squnion>\<^sub>s Var w\<^bsub>f\<^esub>\<^bsub>m\<^esub>) ` ((Pow (P\<^sup>+ V)) \<times> (Pow (P\<^sup>+ V)))"
    by force
  moreover
  from pow_of_p_Plus_finite have "finite ((Pow (P\<^sup>+ V)) \<times> (Pow (P\<^sup>+ V)))"
    by blast
  then have "finite ((\<lambda>(l, m). Var w\<^bsub>f\<^esub>\<^bsub>l \<union> m\<^esub> =\<^sub>s Var w\<^bsub>f\<^esub>\<^bsub>l\<^esub> \<squnion>\<^sub>s Var w\<^bsub>f\<^esub>\<^bsub>m\<^esub>) ` ((Pow (P\<^sup>+ V)) \<times> (Pow (P\<^sup>+ V))))"
    by blast
  ultimately
  show ?case by fastforce
next
  case (4 f)
  have "{Var (InterOfWAux f l m) =\<^sub>s Var w\<^bsub>f\<^esub>\<^bsub>l\<^esub> -\<^sub>s Var w\<^bsub>f\<^esub>\<^bsub>m\<^esub> |l m. l \<subseteq> P\<^sup>+ V \<and> m \<subseteq> P\<^sup>+ V} =
        (\<lambda>(l, m). Var (InterOfWAux f l m) =\<^sub>s Var w\<^bsub>f\<^esub>\<^bsub>l\<^esub> -\<^sub>s Var w\<^bsub>f\<^esub>\<^bsub>m\<^esub>) ` ((Pow (P\<^sup>+ V)) \<times> (Pow (P\<^sup>+ V)))"
    by force
  moreover
  from pow_of_p_Plus_finite have "finite ((Pow (P\<^sup>+ V)) \<times> (Pow (P\<^sup>+ V)))"
    by blast
  then have "finite ((\<lambda>(l, m). Var (InterOfWAux f l m) =\<^sub>s Var w\<^bsub>f\<^esub>\<^bsub>l\<^esub> -\<^sub>s Var w\<^bsub>f\<^esub>\<^bsub>m\<^esub>) ` ((Pow (P\<^sup>+ V)) \<times> (Pow (P\<^sup>+ V))))"
    by blast
  ultimately
  have 1: "finite {Var (InterOfWAux f l m) =\<^sub>s Var w\<^bsub>f\<^esub>\<^bsub>l\<^esub> -\<^sub>s Var w\<^bsub>f\<^esub>\<^bsub>m\<^esub> |l m. l \<subseteq> P\<^sup>+ V \<and> m \<subseteq> P\<^sup>+ V}"
    by argo

  have "{Var w\<^bsub>f\<^esub>\<^bsub>l \<inter> m\<^esub> =\<^sub>s Var w\<^bsub>f\<^esub>\<^bsub>l\<^esub> -\<^sub>s Var (InterOfWAux f l m) |l m. l \<subseteq> P\<^sup>+ V \<and> m \<subseteq> P\<^sup>+ V} =
        (\<lambda>(l, m). Var w\<^bsub>f\<^esub>\<^bsub>l \<inter> m\<^esub> =\<^sub>s Var w\<^bsub>f\<^esub>\<^bsub>l\<^esub> -\<^sub>s Var (InterOfWAux f l m)) ` ((Pow (P\<^sup>+ V)) \<times> (Pow (P\<^sup>+ V)))"
    by force
  moreover
  from pow_of_p_Plus_finite have "finite ((Pow (P\<^sup>+ V)) \<times> (Pow (P\<^sup>+ V)))"
    by blast
  then have "finite ((\<lambda>(l, m). Var w\<^bsub>f\<^esub>\<^bsub>l \<inter> m\<^esub> =\<^sub>s Var w\<^bsub>f\<^esub>\<^bsub>l\<^esub> -\<^sub>s Var (InterOfWAux f l m)) ` ((Pow (P\<^sup>+ V)) \<times> (Pow (P\<^sup>+ V))))"
    by blast
  ultimately
  have 2: "finite {Var w\<^bsub>f\<^esub>\<^bsub>l \<inter> m\<^esub> =\<^sub>s Var w\<^bsub>f\<^esub>\<^bsub>l\<^esub> -\<^sub>s Var (InterOfWAux f l m) |l m. l \<subseteq> P\<^sup>+ V \<and> m \<subseteq> P\<^sup>+ V}"
    by argo
  from 1 2 show ?case by blast
next
  case (5 f g)
  have "{Var w\<^bsub>g\<^esub>\<^bsub>l\<^esub> =\<^sub>s Var w\<^bsub>g\<^esub>\<^bsub>l\<^esub> \<squnion>\<^sub>s Var w\<^bsub>f\<^esub>\<^bsub>l\<^esub> |l. l \<subseteq> P\<^sup>+ V} =
        (\<lambda>l. Var w\<^bsub>g\<^esub>\<^bsub>l\<^esub> =\<^sub>s Var w\<^bsub>g\<^esub>\<^bsub>l\<^esub> \<squnion>\<^sub>s Var w\<^bsub>f\<^esub>\<^bsub>l\<^esub>) ` Pow (P\<^sup>+ V)"
    by blast
  with pow_of_p_Plus_finite show ?case by auto
qed

fun reduce_literal :: "('v, 'f) MLSSmf_literal \<Rightarrow> ('v, 'f) Composite pset_fm set" where
  "reduce_literal (AT\<^sub>m a) = AT ` (reduce_atom a)" |
  "reduce_literal (AF\<^sub>m a) = AF ` (reduce_atom a)"

lemma reduce_literal_finite: "finite (reduce_literal lt)"
  by (cases lt) (simp add: reduce_atom_finite)+

lemma reduce_literal_normalized:
  assumes "lt \<in> set \<C>"
    shows "normalized_MLSS_clause (reduce_literal lt)"
proof -
  from assms norm_\<C> have "norm_literal lt" by blast
  then show ?thesis
  proof (cases lt rule: norm_literal.cases)
    case (inc f)
    then have "reduce_literal lt =
      AT ` {Var w\<^bsub>f\<^esub>\<^bsub>m\<^esub> =\<^sub>s Var w\<^bsub>f\<^esub>\<^bsub>m\<^esub> \<squnion>\<^sub>s Var w\<^bsub>f\<^esub>\<^bsub>l\<^esub> |l m. l \<subseteq> P\<^sup>+ V \<and> m \<subseteq> P\<^sup>+ V \<and> l \<subseteq> m}"
      by simp
    then show ?thesis
      apply unfold_locales
      using normalized_MLSS_literal.union
       apply force
      by (meson reduce_literal_finite)
  next
    case (dec f)
    then have "reduce_literal lt =
      AT ` {Var w\<^bsub>f\<^esub>\<^bsub>l\<^esub> =\<^sub>s Var w\<^bsub>f\<^esub>\<^bsub>l\<^esub> \<squnion>\<^sub>s Var w\<^bsub>f\<^esub>\<^bsub>m\<^esub> |l m. l \<subseteq> P\<^sup>+ V \<and> m \<subseteq> P\<^sup>+ V \<and> l \<subseteq> m}"
      by simp
    then show ?thesis
      apply unfold_locales
      using normalized_MLSS_literal.union
       apply force
      by (meson reduce_literal_finite)
  next
    case (add f)
    then have "reduce_literal lt =
      AT ` {Var w\<^bsub>f\<^esub>\<^bsub>l\<union>m\<^esub> =\<^sub>s Var w\<^bsub>f\<^esub>\<^bsub>l\<^esub> \<squnion>\<^sub>s Var w\<^bsub>f\<^esub>\<^bsub>m\<^esub> |l m. l \<subseteq> P\<^sup>+ V \<and> m \<subseteq> P\<^sup>+ V}"
      by simp
    then show ?thesis
      apply unfold_locales
      using normalized_MLSS_literal.union
       apply force
      by (meson reduce_literal_finite)
  next
    case (mul f)
    then have "reduce_literal lt = AT ` (
      {Var (InterOfWAux f l m) =\<^sub>s Var w\<^bsub>f\<^esub>\<^bsub>l\<^esub> -\<^sub>s Var w\<^bsub>f\<^esub>\<^bsub>m\<^esub> |l m. l \<subseteq> P\<^sup>+ V \<and> m \<subseteq> P\<^sup>+ V} \<union>
      {Var w\<^bsub>f\<^esub>\<^bsub>l\<inter>m\<^esub> =\<^sub>s Var w\<^bsub>f\<^esub>\<^bsub>l\<^esub> -\<^sub>s Var (InterOfWAux f l m) |l m. l \<subseteq> P\<^sup>+ V \<and> m \<subseteq> P\<^sup>+ V})"
      by simp
    then show ?thesis
      apply unfold_locales
      using normalized_MLSS_literal.diff
       apply force
      by (meson reduce_literal_finite)
  next
    case (le f g)
    then have "reduce_literal lt =
      AT ` {Var w\<^bsub>g\<^esub>\<^bsub>l\<^esub> =\<^sub>s Var w\<^bsub>g\<^esub>\<^bsub>l\<^esub> \<squnion>\<^sub>s Var w\<^bsub>f\<^esub>\<^bsub>l\<^esub> |l. l \<subseteq> P\<^sup>+ V}"
      by simp
    then show ?thesis
      apply unfold_locales
      using normalized_MLSS_literal.union
       apply force
      by (meson reduce_literal_finite)
  next
    case (eq_empty x n)
    then have "reduce_literal lt = AT ` {Var (Solo x) =\<^sub>s \<emptyset> n}"
      by simp
    then show ?thesis 
      apply unfold_locales
      using normalized_MLSS_literal.eq_empty
       apply force
      by (meson reduce_literal_finite)
  next
    case (eq x y)
    then have "reduce_literal lt = AT ` {Var (Solo x) =\<^sub>s Var (Solo y)}"
      by simp
    then show ?thesis 
      apply unfold_locales
      using normalized_MLSS_literal.eq
       apply force
      by (meson reduce_literal_finite)
  next
    case (neq x y)
    then have "reduce_literal lt = AF ` {Var (Solo x) =\<^sub>s Var (Solo y)}"
      by simp
    then show ?thesis 
      apply unfold_locales
      using normalized_MLSS_literal.neq
       apply force
      by (meson reduce_literal_finite)
  next
    case (union x y z)
    then show ?thesis
      apply simp
      using normalized_MLSS_literal.union
      by (metis finite.emptyI finite.insertI normalized_MLSS_clause.intro singletonD)
  next
    case (diff x y z)
    then show ?thesis
      apply simp
      using normalized_MLSS_literal.diff
      by (metis finite.emptyI finite.insertI normalized_MLSS_clause.intro singletonD)
  next
    case (single x y)
    then show ?thesis
      apply simp
      using normalized_MLSS_literal.singleton
      by (metis finite.emptyI finite.insertI normalized_MLSS_clause.intro singletonD)
  next
    case (app x f y)
    then show ?thesis
      apply simp
      using normalized_MLSS_literal.eq
      using normalized_MLSS_clause_def by fastforce
  qed
qed

definition reduce_clause :: "('v, 'f) Composite pset_fm set" where
  "reduce_clause = \<Union> (reduce_literal ` set \<C>)"

lemma reduce_clause_finite: "finite reduce_clause"
proof -
  have "finite (set \<C>)" by simp
  have "\<forall>lt \<in> set \<C>. finite (reduce_literal lt)"
    using reduce_literal_finite by fast
  then have "finite reduce_clause"
    using \<open>finite (set \<C>)\<close>
    unfolding reduce_clause_def by simp
  then show ?thesis by argo
qed

lemma reduce_clause_normalized: "normalized_MLSS_clause reduce_clause"
  using reduce_literal_normalized
  by (simp add: normalized_MLSS_clause_def reduce_clause_def)

section \<open>Finalize: collect everything and get the final MLSS-formulae\<close>

definition reduced_dnf :: "('v, 'f) Composite pset_fm set set" where
  "reduced_dnf \<equiv> (\<lambda>fms. fms \<union> introduce_v \<union> introduce_UnionOfVennRegions \<union> reduce_clause) ` introduce_w"

lemma introduce_v_subset_reduced_fms: "\<forall>fms \<in> reduced_dnf. introduce_v \<subseteq> fms"
  unfolding reduced_dnf_def by blast

lemma introduce_w_subset_reduced_fms: "\<forall>fms \<in> reduced_dnf. \<exists>fms_w \<in> introduce_w. fms_w \<subseteq> fms"
  unfolding reduced_dnf_def by blast

lemma reduce_clause_subset_reduced_fms: "\<forall>fms \<in> reduced_dnf. reduce_clause \<subseteq> fms"
  unfolding reduced_dnf_def by blast

lemma introduce_UnionOfVennRegions_subset_reduced_fms:
  "\<forall>fms \<in> reduced_dnf. introduce_UnionOfVennRegions \<subseteq> fms"
  unfolding reduced_dnf_def by blast

lemma reduced_dnf_normalized:
  "\<forall>clause \<in> reduced_dnf. normalized_MLSS_clause clause"
proof
  fix clause assume "clause \<in> reduced_dnf"
  then obtain clause_w where "clause_w \<in> introduce_w" "clause = clause_w \<union> introduce_v \<union> introduce_UnionOfVennRegions \<union> reduce_clause"
    unfolding reduced_dnf_def by blast
  then show "normalized_MLSS_clause clause"
    using introduce_v_normalized introduce_UnionOfVennRegions_normalized reduce_clause_normalized introduce_w_normalized
    by (metis UnE finite_UnI normalized_MLSS_clause_def)
qed

lemma normalized_clause_contains_all_v_\<alpha>:
  assumes "clause \<in> reduced_dnf"
    shows "\<forall>\<alpha> \<in> P\<^sup>+ V. v\<^bsub>\<alpha>\<^esub> \<in> \<Union> (vars ` clause)"
proof
  fix \<alpha> assume "\<alpha> \<in> P\<^sup>+ V"
  with assms have "AT (restriction_on_v \<alpha>) \<in> clause"
    unfolding reduced_dnf_def introduce_v_def
    by blast
  moreover
  from v_\<alpha>_in_vars_restriction_on_v have "v\<^bsub>\<alpha>\<^esub> \<in> vars (restriction_on_v \<alpha>)"
    by blast
  ultimately
  show "v\<^bsub>\<alpha>\<^esub> \<in> \<Union> (vars ` clause)"
    by force
qed

definition is_model_for_reduced_dnf :: "(('v, 'f) Composite \<Rightarrow> hf) \<Rightarrow> bool" where
  "is_model_for_reduced_dnf \<M> \<equiv> \<exists>clause \<in> reduced_dnf. \<forall>fm \<in> clause. interp I\<^sub>s\<^sub>a \<M> fm"

end

end
