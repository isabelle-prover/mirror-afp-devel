theory Refine_Rigorous_Numerics
imports
  "../Refinement/Autoref_Misc" (* TODO: what is still needed there? *)
  "../Refinement/Weak_Set"
  "../Numerics/Runge_Kutta"
  "../IVP/Reachability_Analysis"
  "../../Affine_Arithmetic/Affine_Arithmetic"
begin

section \<open>interfaces\<close>

consts i_eucl :: interface \<comment> \<open>euclidean space\<close>
abbreviation "eucl_rel \<equiv> Id::('a::euclidean_space\<times>_) set"
lemmas [autoref_rel_intf] = REL_INTFI[of eucl_rel i_eucl]

consts i_apprs :: interface \<comment> \<open>dependent sets, TODO: can this be hidden in the evaluation?\<close>

consts i_coll :: "interface \<Rightarrow> interface" \<comment> \<open>collection of reachable sets\<close>

section \<open>hyperplanes\<close>

context begin interpretation autoref_syn .
lemma [autoref_rules]:
  shows
  "(Sctn, Sctn) \<in> eucl_rel \<rightarrow> eucl_rel \<rightarrow> Id"
  "(normal, normal) \<in> Id \<rightarrow> eucl_rel"
  "(pstn, pstn) \<in> Id \<rightarrow> eucl_rel"
  by auto
end

section \<open>Operations on Enclosures (Sets)\<close>

definition [refine_vcg_def]: "split_spec X = SPEC (\<lambda>(A, B). X \<subseteq> A \<union> B)"

definition [refine_vcg_def]: "Inf_spec X = SPEC (\<lambda>r. \<forall>x \<in> X. r \<le> x)"

definition [refine_vcg_def]: "Sup_spec X = SPEC (\<lambda>r. \<forall>x \<in> X. x \<le> r)"

definition [refine_vcg_def]: "Inf_inner X y = SPEC (\<lambda>r. \<forall>x \<in> X. r \<le> x \<bullet> y)" \<comment>"TODO: generic image of aforms, then Inf"

definition [refine_vcg_def]: "Sup_inner X y = SPEC (\<lambda>r. \<forall>x \<in> X. x \<bullet> y \<le> r)" \<comment>"TODO: generic image of aforms. then Sup"

definition [refine_vcg_def]: "inter_sctn_spec X sctn = SPEC (\<lambda>R. X \<inter> plane_of sctn \<subseteq> R)"

definition [refine_vcg_def]: "intersects_spec X sctn = SPEC (\<lambda>b. b \<or> X \<inter> plane_of sctn = {})"

definition [refine_vcg_def]: "reduce_spec X = SPEC (\<lambda>R. X \<subseteq> R)"

definition [refine_vcg_def]: "width_spec X = SPEC (top::real\<Rightarrow>_)"

definition [refine_vcg_def]: "ivl_of_set X = SPEC (\<lambda>(i, s). i \<le> s \<and> X \<subseteq> {i .. s})"

definition "strongest_direction T =
  (let
    b = fold (\<lambda>b' b. if abs (T \<bullet> b') \<ge> abs (T \<bullet> b) then b' else b) (Basis_list::'a::executable_euclidean_space list) 0
  in
    (sgn (T \<bullet> b) *\<^sub>R b, abs (T \<bullet> b)))"


lemma ivl_of_set_nres:
  fixes X::"'a::lattice set"
  shows "do { i \<leftarrow> Inf_spec X; s \<leftarrow> Sup_spec X; RETURN (inf i s, s)} \<le> ivl_of_set X"
  unfolding ivl_of_set_def Inf_spec_def Sup_spec_def
  by (refine_vcg) (auto simp: inf.coboundedI1)


subsubsection \<open>interval approximation of many\<close>

definition ivl_of_sets::"'a::lattice set set \<Rightarrow> ('a \<times> 'a) nres" where
  "ivl_of_sets (XS::'a set set) = SPEC (\<lambda>(i, s). (\<forall>X\<in>XS. X \<subseteq> {i..s} \<and> i \<le> s))"
lemmas [refine_vcg] = ivl_of_sets_def[THEN eq_refl, THEN order.trans]


subsection \<open>subset approximation\<close>

definition[refine_vcg_def]:  "subset_spec X Y = SPEC (\<lambda>b. b \<longrightarrow> X \<subseteq> Y)"

definition [refine_vcg_def]: "above_sctn X sctn = SPEC (\<lambda>b. b \<longrightarrow> (\<forall>x \<in> X. \<not>le_halfspace sctn x))"

lemma above_sctn_nres: "do { ii \<leftarrow> Inf_inner X (normal sctn); RETURN (ii > pstn sctn)} \<le> above_sctn X sctn"
  by (auto simp: above_sctn_def Inf_inner_def le_halfspace_def intro!: refine_vcg)

definition [refine_vcg_def]: "below_sctn X sctn = SPEC (\<lambda>b. b \<longrightarrow> (\<forall>x \<in> X. le_halfspace sctn x))"

lemma below_sctn_nres:
  "do { si \<leftarrow> Sup_inner X (normal sctn); RETURN (si \<le> pstn sctn)} \<le> below_sctn X sctn"
  by (auto simp: below_sctn_def Sup_inner_def le_halfspace_def intro!: refine_vcg)

definition [refine_vcg_def]: "disjoint_sets X Y = SPEC (\<lambda>b. b \<longrightarrow> X \<inter> Y = {})"


section \<open>Dependencies (Set of vectors)\<close>

definition "env_len env l = (\<forall>xs \<in> env. length xs = l)"


subsection \<open>singleton projection\<close>

definition [refine_vcg_def]: "nth_image_precond X n \<longleftrightarrow> X \<noteq> {} \<and> (\<forall>xs\<in>X. n < length xs \<and> env_len X (length xs))"

definition [refine_vcg_def]: "nth_image X n = SPEC (\<lambda>R. nth_image_precond X n \<and> (R = (\<lambda>x. x ! n) ` X))"


subsection \<open>projection\<close>

definition "project_env_precond env is \<equiv> (\<forall>i \<in> set is. \<forall>xs\<in>env. i < length xs \<and> env_len env (length xs))"

definition project_env where [refine_vcg_def]:
  "project_env env is = SPEC (\<lambda>R. project_env_precond env is \<and> env_len R (length is) \<and> (\<lambda>xs. map (\<lambda>i. xs ! i) is) ` env \<subseteq> R)"


subsection \<open>expressions\<close>

definition approx_slp_spec::"('a::real_inner) slp \<Rightarrow> 'a list set \<Rightarrow> 'a list set option nres"
  where [refine_vcg_def]: "approx_slp_spec slp env = SPEC
    (\<lambda>R. case R of Some R \<Rightarrow> \<forall>e\<in>env. let r = interpret_slp slp e in env_len R (length r) \<and> r \<in> R
      | None \<Rightarrow> True)"

lemma approx_slp_box_spec[THEN order_trans, refine_vcg]:
  "approx_slp_spec slp env \<le> SPEC (\<lambda>R. case R of Some R \<Rightarrow> \<forall>e\<in>env. interpret_slp slp e \<in> R | None \<Rightarrow> True)"
  by (refine_vcg) (auto simp: Let_def split: option.split)

definition approx_euclarithform_spec::
  "('a::ordered_euclidean_space, 'a) euclarithform \<Rightarrow> 'a set \<Rightarrow> bool nres"
where "approx_euclarithform_spec ea E = SPEC (\<lambda>r. r \<longrightarrow> (\<forall>e\<in>E. interpret_euclarithform ea [e]))"


subsection \<open>singleton environment\<close>

definition sings_spec where [refine_vcg_def]:
  "sings_spec X = SPEC (\<lambda>env. env_len env 1 \<and> X \<noteq> {} \<and> (env = (\<lambda>x. [x]) ` X))"


section \<open>Implementations\<close>

context begin
interpretation autoref_syn .

lemma eor_impl[autoref_rules]: "(\<lambda>r. scaleR r (sum_list Basis_list), eor) \<in> Id \<rightarrow> Id"
  by (auto simp: sum_list_Basis_list[symmetric] eor_def)

lemma roe_impl[autoref_rules]: "(\<lambda>e. e \<bullet> (hd Basis_list), roe) \<in> Id \<rightarrow> Id"
  by (auto simp: sum_list_Basis_list[symmetric] roe_def)

lemma strongest_direction_autoref[autoref_rules]:
  "(strongest_direction, strongest_direction) \<in> eucl_rel \<rightarrow> eucl_rel \<times>\<^sub>r eucl_rel"
  by auto

lemma [autoref_rules]:
  "(op =, op =) \<in> eucl_rel \<rightarrow> eucl_rel \<rightarrow> bool_rel"
  "(min, min) \<in> eucl_rel \<rightarrow> eucl_rel \<rightarrow> eucl_rel"
  "(max, max) \<in> eucl_rel \<rightarrow> eucl_rel \<rightarrow> eucl_rel"
  "(inf, inf) \<in> eucl_rel \<rightarrow> eucl_rel \<rightarrow> eucl_rel"
  "(sup, sup) \<in> eucl_rel \<rightarrow> eucl_rel \<rightarrow> eucl_rel"
  "(Basis_list, Basis_list) \<in> \<langle>eucl_rel\<rangle>list_rel"
  "(op +, op +) \<in> eucl_rel \<rightarrow> eucl_rel \<rightarrow> eucl_rel"
  "(op -, op -) \<in> eucl_rel \<rightarrow> eucl_rel \<rightarrow> eucl_rel"
  "(op /, op /) \<in> eucl_rel \<rightarrow> eucl_rel \<rightarrow> eucl_rel"
  "(op *, op *) \<in> eucl_rel \<rightarrow> eucl_rel \<rightarrow> eucl_rel"
  "(op \<bullet>, op \<bullet>) \<in> eucl_rel \<rightarrow> eucl_rel \<rightarrow> eucl_rel"
  "(op ^, op ^) \<in> eucl_rel \<rightarrow> nat_rel \<rightarrow> eucl_rel"
  "(int, int) \<in> nat_rel \<rightarrow> int_rel"
  "(Float, Float) \<in> int_rel \<rightarrow> int_rel \<rightarrow> Id"
  "(real_of_float, real_of_float) \<in> Id \<rightarrow> eucl_rel"
  "(op *\<^sub>R, op *\<^sub>R) \<in> eucl_rel \<rightarrow> eucl_rel \<rightarrow> eucl_rel"
  "(sum_list, sum_list) \<in> \<langle>eucl_rel\<rangle>list_rel \<rightarrow> eucl_rel"
  "(upto, upto) \<in> int_rel \<rightarrow> int_rel \<rightarrow> \<langle>int_rel\<rangle>list_rel"
  "(list_ex, list_ex) \<in> (eucl_rel \<rightarrow> bool_rel) \<rightarrow> \<langle>eucl_rel\<rangle>list_rel \<rightarrow> bool_rel"
  "(zip, zip) \<in> \<langle>int_rel\<rangle>list_rel \<rightarrow> \<langle>int_rel\<rangle>list_rel \<rightarrow> \<langle>int_rel \<times>\<^sub>r int_rel\<rangle>list_rel"
  "(upt, upt) \<in> nat_rel \<rightarrow> nat_rel \<rightarrow> \<langle>nat_rel\<rangle>list_rel"
  "(zip, zip) \<in> \<langle>int_rel\<rangle>list_rel \<rightarrow> \<langle>int_rel\<rangle>list_rel \<rightarrow> \<langle>int_rel \<times>\<^sub>r int_rel\<rangle>list_rel"
  "(zip, zip) \<in> \<langle>int_rel\<rangle>list_rel \<rightarrow> \<langle>eucl_rel\<rangle>list_rel \<rightarrow> \<langle>int_rel \<times>\<^sub>r eucl_rel\<rangle>list_rel"
  "(product_lists, product_lists) \<in> \<langle>\<langle>int_rel\<rangle>list_rel\<rangle>list_rel \<rightarrow> \<langle>\<langle>int_rel\<rangle>list_rel\<rangle>list_rel"
  "(floor, floor) \<in> eucl_rel \<rightarrow> int_rel"
  by auto

end

subsection \<open>locale for sets\<close>

text \<open>TODO: get rid of 'b / 'b list, then get rid of list!\<close>
locale approximate_sets = autoref_syn +
  fixes appr_of_ivl::"'a::executable_euclidean_space \<Rightarrow> 'a \<Rightarrow> 'b"
  fixes msum_appr::"'b \<Rightarrow> 'b \<Rightarrow> 'b"
  fixes set_of_appr::"'b \<Rightarrow> 'a set"
  fixes set_of_apprs::"'b list \<Rightarrow> 'a list set"
  fixes inf_of_appr::"'options \<Rightarrow> 'b \<Rightarrow> 'a"
  fixes sup_of_appr::"'options \<Rightarrow> 'b \<Rightarrow> 'a"
  fixes split_appr::"'options \<Rightarrow> 'b \<Rightarrow> 'b \<times> 'b"
  fixes appr_inf_inner::"'options \<Rightarrow> 'b \<Rightarrow> 'a \<Rightarrow> real"
  fixes appr_sup_inner::"'options \<Rightarrow> 'b \<Rightarrow> 'a \<Rightarrow> real"
  fixes inter_appr_plane::"'options \<Rightarrow> 'b \<Rightarrow> 'a sctn \<Rightarrow> 'b dres"
  fixes reduce_appr::"'options \<Rightarrow> 'b \<Rightarrow> 'b"
  fixes appr_Cons::"'b \<Rightarrow> 'b list \<Rightarrow> 'b list" \<comment>\<open>independent!\<close>
  fixes width_appr::"'options \<Rightarrow> 'b \<Rightarrow> real"
  fixes approx_slp::"'options \<Rightarrow> 'a slp \<Rightarrow> 'b list \<Rightarrow> 'b list option dres"
  fixes approx_euclarithform::"'options \<Rightarrow> ('a, 'a) euclarithform \<Rightarrow> 'b \<Rightarrow> bool dres"
  fixes appr_rel apprs_rel
  fixes optns::"'options"
  assumes appr_rel_internal: "appr_rel \<equiv> (\<lambda>R. br set_of_appr top O \<langle>R\<rangle>set_rel)"
  and apprs_rel_def: "apprs_rel \<equiv> br set_of_apprs top"
notes [autoref_rel_intf] = REL_INTFI[of appr_rel i_set]
notes [autoref_rel_intf] = REL_INTFI[of apprs_rel i_apprs]
notes [autoref_tyrel]    = ty_REL[where 'a="'a set list" and R="\<langle>\<langle>Id\<rangle>appr_rel\<rangle>list_rel"]
notes [autoref_tyrel]    = ty_REL[where 'a="'a" and R="eucl_rel"]
notes [autoref_tyrel]    = ty_REL[where 'a="real" and R="eucl_rel"]
assumes transfer_operations[unfolded comps, autoref_rules]:
  "SIDE_PRECOND (x \<le> y) \<Longrightarrow> (xi, x) \<in> eucl_rel \<Longrightarrow> (yi, y) \<in> eucl_rel \<Longrightarrow> (appr_of_ivl xi yi, atLeastAtMost $ x $ y) \<in> \<langle>eucl_rel\<rangle>appr_rel"
  "(appr_Cons, set_Cons) \<in> \<langle>eucl_rel\<rangle>appr_rel \<rightarrow> apprs_rel \<rightarrow> apprs_rel"
  "(msum_appr, op +) \<in> \<langle>eucl_rel\<rangle>appr_rel \<rightarrow> \<langle>eucl_rel\<rangle>appr_rel \<rightarrow> \<langle>eucl_rel\<rangle>appr_rel"
  "(RETURN o inf_of_appr optns, Inf_spec) \<in> \<langle>eucl_rel\<rangle>appr_rel \<rightarrow> \<langle>eucl_rel\<rangle>nres_rel"
  "(RETURN o sup_of_appr optns, Sup_spec) \<in> \<langle>eucl_rel\<rangle>appr_rel \<rightarrow> \<langle>eucl_rel\<rangle>nres_rel"
  "(RETURN o split_appr optns, split_spec) \<in> \<langle>eucl_rel\<rangle>appr_rel \<rightarrow> \<langle>\<langle>eucl_rel\<rangle>appr_rel \<times>\<^sub>r \<langle>eucl_rel\<rangle>appr_rel\<rangle>nres_rel"
  "(RETURN o2 appr_inf_inner optns, Inf_inner) \<in> \<langle>eucl_rel\<rangle>appr_rel \<rightarrow> eucl_rel \<rightarrow> \<langle>eucl_rel\<rangle>nres_rel"
  "(RETURN o2 appr_sup_inner optns, Sup_inner) \<in> \<langle>eucl_rel\<rangle>appr_rel \<rightarrow> eucl_rel \<rightarrow> \<langle>eucl_rel\<rangle>nres_rel"
  "(nres_of o2 inter_appr_plane optns, inter_sctn_spec) \<in> \<langle>eucl_rel\<rangle>appr_rel \<rightarrow> Id \<rightarrow> \<langle>\<langle>eucl_rel\<rangle>appr_rel\<rangle>nres_rel"
  "(RETURN o reduce_appr optns, reduce_spec) \<in> \<langle>eucl_rel\<rangle>appr_rel \<rightarrow> \<langle>\<langle>eucl_rel\<rangle>appr_rel\<rangle>nres_rel"
  "(RETURN o width_appr optns, width_spec) \<in> \<langle>eucl_rel\<rangle>appr_rel \<rightarrow> \<langle>eucl_rel\<rangle>nres_rel"
assumes approx_slp[unfolded comps, autoref_rules]:
  "(nres_of o2 approx_slp optns, approx_slp_spec) \<in> Id \<rightarrow> apprs_rel \<rightarrow> \<langle>\<langle>apprs_rel\<rangle>option_rel\<rangle>nres_rel"
assumes approx_euclarithform[unfolded comps]:
  "(nres_of o approx_euclarithform optns ef, approx_euclarithform_spec ef) \<in>
    \<langle>eucl_rel\<rangle>appr_rel \<rightarrow> \<langle>bool_rel\<rangle>nres_rel"
assumes set_of_appr_nonempty[simp]: "set_of_appr X \<noteq> {}"
assumes set_of_appr_compact: "compact (set_of_appr X)"
assumes set_of_appr_convex: "convex (set_of_appr X)"
assumes set_of_apprs_imp': "xs \<in> set_of_apprs XS \<Longrightarrow> length xs = length XS \<Longrightarrow> length ys = length YS \<Longrightarrow> set (zip ys YS) \<subseteq> set (zip xs XS) \<Longrightarrow> ys \<in> set_of_apprs YS"
assumes set_of_apprs_set_of_appr: "[x] \<in> set_of_apprs [X] \<longleftrightarrow> x \<in> set_of_appr X"
assumes set_of_apprs_switch: "x#y#xs \<in> set_of_apprs (X#Y#XS) \<Longrightarrow> y#x#xs \<in> set_of_apprs (Y#X#XS)"
assumes set_of_apprs_rotate: "x#xs \<in> set_of_apprs (X#XS) \<Longrightarrow> xs@[x] \<in> set_of_apprs (XS@[X])" \<comment>"TODO: better use the set (zip ...) property?"
assumes set_of_apprs_Nil[simp]: "xs \<in> set_of_apprs [] \<longleftrightarrow> xs = []"
assumes length_set_of_apprs: "xs \<in> set_of_apprs XS \<Longrightarrow> length xs = length XS"
assumes set_of_apprs_Cons_ex: "xs \<in> set_of_apprs (X#XS) \<Longrightarrow> (\<exists>y ys. xs = y#ys \<and> y \<in> set_of_appr X \<and> ys \<in> set_of_apprs XS)"
assumes set_of_apprs_ex_Cons: "xs \<in> set_of_apprs XS \<Longrightarrow> \<exists>x. x#xs \<in> set_of_apprs (X#XS)"
assumes set_of_apprs_Cons_copy: "x#xs \<in> set_of_apprs (X#XS) \<Longrightarrow> x#x#xs \<in> set_of_apprs (X#X#XS)"
assumes set_of_apprs_Cons_copy_unique: "y#x#xs \<in> set_of_apprs (X#X#XS) \<Longrightarrow> y = x"
begin

lemma appr_rel_def: "\<langle>Id\<rangle>appr_rel = br set_of_appr top"
  unfolding appr_rel_internal relAPP_def set_rel_id_simp[unfolded relAPP_def]
  by simp

lemmas [autoref_post_simps] = concat.simps append_Nil2 append.simps

definition "ncc (X::'a set) \<longleftrightarrow> X \<noteq> {} \<and> compact X \<and> convex X"

lemma ncc_imageD:
  assumes "ncc ((\<lambda>x. x ! i) ` env)"
  assumes "nth_image_precond env i"
  shows "compact ((\<lambda>x. x ! i) ` env)" "closed ((\<lambda>x. x ! i) ` env)" "bounded ((\<lambda>x. x ! i) ` env)"
    "((\<lambda>x. x ! i) ` env) \<noteq> {}" "convex ((\<lambda>x. x ! i) ` env)"
  using assms
  by (auto simp: ncc_def nth_image_precond_def compact_eq_bounded_closed)

lemma set_of_appr_ncc: "ncc (set_of_appr X)"
  by (auto simp: set_of_appr_convex set_of_appr_compact ncc_def)

definition "op_nres_ASSUME_bnd_ncc x = op_nres_ASSUME_bnd (ncc x)"
lemma ASSUME_ncc[autoref_op_pat_def]: "do {ASSUME (ncc x); f} \<equiv> op_nres_ASSUME_bnd_ncc x f"
  by (auto simp: op_nres_ASSUME_bnd_ncc_def)

lemma autoref_ASSUME_bnd_ncc[autoref_rules]:
  assumes "ncc X \<Longrightarrow> (m',m) \<in> \<langle>R\<rangle>nres_rel"
  assumes "(Xi, X) \<in> \<langle>Id\<rangle>appr_rel"
  shows "(m', (((OP op_nres_ASSUME_bnd_ncc) ::: \<langle>Id\<rangle>appr_rel \<rightarrow> \<langle>R\<rangle>nres_rel \<rightarrow> \<langle>R\<rangle>nres_rel)) $ X $ m)\<in>\<langle>R\<rangle>nres_rel"
  using assms
  by (auto simp: op_nres_ASSUME_bnd_ncc_def nres_rel_def appr_rel_def br_def set_of_appr_ncc
    intro!: ASSUME_refine_right)

definition "op_nres_ASSUME_bnd_all_ncc X = op_nres_ASSUME_bnd (\<forall>x \<in> X. ncc x)"
lemma ASSUME_all_ncc[autoref_op_pat_def]: "do {ASSUME (\<forall>x \<in> X. ncc x); f} \<equiv> op_nres_ASSUME_bnd_all_ncc X f"
  by (auto simp: op_nres_ASSUME_bnd_all_ncc_def)

lemma autoref_ASSUME_bnd_all_ncc[autoref_rules]:
  assumes "(\<And>x. x \<in> X \<Longrightarrow> ncc x) \<Longrightarrow> (m',m) \<in> \<langle>R\<rangle>nres_rel"
  assumes "(Xi, X) \<in> \<langle>\<langle>Id\<rangle>appr_rel\<rangle>list_wset_rel"
  shows "(m', (((OP op_nres_ASSUME_bnd_all_ncc) ::: \<langle>\<langle>Id\<rangle>appr_rel\<rangle>list_wset_rel \<rightarrow> \<langle>R\<rangle>nres_rel \<rightarrow> \<langle>R\<rangle>nres_rel)) $ X $ m)\<in>\<langle>R\<rangle>nres_rel"
  using assms
  by (auto simp: op_nres_ASSUME_bnd_all_ncc_def nres_rel_def appr_rel_def br_def set_of_appr_ncc
    list_wset_rel_def set_rel_def
    intro!: ASSUME_refine_right)

lemma [autoref_rules]: "(optns, optns) \<in> Id"
  by simp

lemma single_valued_appr_rel[relator_props]:
  "single_valued (\<langle>eucl_rel\<rangle>appr_rel)"
  "single_valued apprs_rel"
  by (auto simp: appr_rel_def apprs_rel_def)


lemmas [autoref_tyrel] = ty_REL[where 'a="'a set set" and R="\<langle>\<langle>Id\<rangle>appr_rel\<rangle>list_wset_rel"]

definition [simp, symmetric, autoref_op_pat_def]: "spec_env_len env \<equiv> SPEC (env_len env)"

lemma env_len_refine[autoref_rules]: "(\<lambda>x. RETURN (length x), spec_env_len) \<in> apprs_rel \<rightarrow> \<langle>Id\<rangle> nres_rel"
  by (auto simp: env_len_def nres_rel_def apprs_rel_def br_def length_set_of_apprs)

lemma sings_refine[autoref_rules]: "((\<lambda>x. RETURN ([x])), sings_spec) \<in> \<langle>Id\<rangle>appr_rel \<rightarrow> \<langle>apprs_rel\<rangle> nres_rel"
  by (auto simp: sings_spec_def appr_rel_def apprs_rel_def set_of_apprs_set_of_appr br_def nres_rel_def
    env_len_def
    intro!: RETURN_SPEC_refine
    dest!: set_of_apprs_Cons_ex)

lemma set_of_apprs_Cons: "x#xs \<in> set_of_apprs (X#XS) \<Longrightarrow> xs \<in> set_of_apprs XS"
  by (auto dest: set_of_apprs_Cons_ex)

lemma set_of_apprs_ConsE1:
  assumes "xs \<in> set_of_apprs XS"
  obtains x where "(x#xs) \<in> set_of_apprs (X#XS)"
  by (metis assms set_of_apprs_ex_Cons)

lemma set_of_apprs_ex_Cons2:
  assumes "x \<in> set_of_appr X"
  shows "\<exists>xs. x#xs \<in> set_of_apprs (X#XS)"
  apply (induct XS)
  using assms
  subgoal by (force simp: set_of_apprs_set_of_appr intro!: exI[where x=Nil])
  subgoal using set_of_apprs_ex_Cons set_of_apprs_switch by blast
  done

lemma set_of_apprs_ConsE2:
  assumes "x \<in> set_of_appr X"
  obtains xs where "x#xs \<in> set_of_apprs (X#XS)"
  by (metis set_of_apprs_ex_Cons2 assms)

lemma set_of_apprsE:
  assumes "xs \<in> set_of_apprs (X#XS)"
  obtains y ys where "xs = y # ys" "y \<in> set_of_appr X" "ys \<in> set_of_apprs XS"
  using set_of_apprs_Cons_ex assms by blast

lemma set_of_apprs_appendD:
  assumes "ys @ xs \<in> set_of_apprs (YS @ XS)"
  assumes "length ys = length YS"
  shows "ys \<in> set_of_apprs YS" "xs \<in> set_of_apprs XS"
proof -
  have *: "length xs = length XS"
    using assms(1) assms(2) length_set_of_apprs by fastforce
  show "ys \<in> set_of_apprs YS" "xs \<in> set_of_apprs XS"
    using assms
    by (auto simp: * set_of_apprs_imp')
qed

lemma set_of_apprs_projections:
  assumes "xs \<in> set_of_apprs XS"
  assumes "\<And>j. j \<in> set js \<Longrightarrow> j < length xs"
  shows "map (op ! xs) js \<in> set_of_apprs (map (op ! XS) js)"
  using assms(1)
  apply (rule set_of_apprs_imp')
  using assms length_set_of_apprs
  apply (force simp:  in_set_zip )+
  done

lemma set_of_apprs_nonempty: "set_of_apprs XS \<noteq> {}"
  apply (induct XS)
  subgoal by (force)
  subgoal by (metis Collect_cong Collect_mem_eq empty_iff set_of_apprs_ex_Cons)
  done

lemma set_of_apprs_appendE1:
  assumes "ys \<in> set_of_apprs YS"
  obtains xs where "xs@ys \<in> set_of_apprs (XS @ YS)"
  apply atomize_elim
  apply (induct XS)
  subgoal by (force intro!: exI[where x=Nil] assms)
  subgoal by (metis append_Cons set_of_apprs_ConsE1)
  done

lemma set_of_apprs_copy_nth:
  assumes
    "x # xs \<in> set_of_apprs (X # XS)"
    "X = XS ! i"
    "i < length XS"
  shows "x = xs ! i"
  using assms
proof (induction i arbitrary: x xs X XS)
  case 0 thus ?case
    by (metis add_right_cancel length_set_of_apprs list.size(4) list_exhaust_size_gt0 nth_Cons_0
      set_of_apprs_Cons_copy_unique)
next
  case (Suc i)
  show ?case
  proof (cases xs)
    case Nil thus ?thesis
      using Suc.prems length_set_of_apprs by fastforce
  next
    case (Cons y ys)
    then obtain Y YS where XS: "XS = Y # YS"
      by (meson Suc.prems(3) Suc_lessE length_Suc_conv)
    have "x # ys \<in> set_of_apprs (YS ! i # YS)"
      using Suc.prems(1) unfolding XS Cons Suc.prems(2)
      by (metis Suc.prems(1) Suc.prems(2) XS local.Cons nth_Cons_Suc set_of_apprs_Cons
        set_of_apprs_switch)
    then have "x = ys ! i" if "i < length YS"
      using refl that
      by (rule Suc.IH)
    then show ?thesis
      using Suc.prems
      by (auto simp: XS Cons)
  qed
qed

lemma
  set_of_apprs_nth_eqI:
  assumes "xs \<in> set_of_apprs XS"
  assumes "XS ! i = XS ! j"
  assumes "i < length XS" "j < length XS"
  shows "xs ! i = xs ! j"
  using length_set_of_apprs[OF assms(1)] assms
proof (induction arbitrary: i j rule: list_induct2)
  case (Cons x xs X XS)
  show ?case
    using Cons.prems set_of_apprs_copy_nth
    by (auto simp: nth_Cons elim: set_of_apprsE intro!: Cons.IH split: nat.split)
qed simp


lemma nth_append_cond:
  "i < length xs \<Longrightarrow> (xs @ ys) ! i = xs ! i"
  "i \<ge> length xs \<Longrightarrow> (xs @ ys) ! i = ys ! (i - length xs)"
  by (auto simp: nth_append)

lemma set_of_apprs_projectsE:
  assumes "jxs \<in> set_of_apprs (map (op ! XS) js)"
  assumes "\<And>j. j \<in> set js \<Longrightarrow> j < length XS"
  obtains ys where "jxs = map (op ! ys) js" "ys \<in> set_of_apprs XS"
proof -
  have len_jxs: "length jxs = length js" using assms(1) length_set_of_apprs by simp
  have map_eq: "map (op ! XS) [0..<length XS] = XS" (is "?m = _")
    by (auto intro!: nth_equalityI)
  with assms obtain xs where xs:
    "xs@jxs \<in> set_of_apprs (map (op ! XS) ([0..<length XS]@js))"
    by (metis set_of_apprs_appendE1 map_append)
  hence len_xs: "length xs = length ?m"
    using len_jxs length_set_of_apprs by fastforce
  from set_of_apprs_appendD[OF xs[unfolded map_append] this] have "xs \<in> set_of_apprs XS"
    by (simp add: map_eq)
  moreover
  have "jxs ! i = map (op ! xs) js ! i" if "i < length jxs" for i
  proof -
    let ?js = "map (op ! XS) js"
    have lens_eq: "length (jxs @ map (op ! xs) js) = length (?js @ ?js)"
      by (simp add: len_jxs)
    have "jxs ! i = (jxs @ map (op ! xs) js) ! i"
      using that by (auto simp: nth_append)
    also have "\<dots> = (jxs @ map (op ! xs) js) ! (length jxs + i)"
    proof -
      have "set (zip (jxs @ map (op ! xs) js) (?js @ ?js)) \<subseteq> set (zip (xs @ jxs) (map (op ! XS) ([0..<length XS] @ js)))"
        apply safe
        unfolding in_set_zip
        apply safe
      proof goal_cases
        case hyps: (1 a b n)
        show ?case
        proof (cases "n < length jxs")
          case True
          with hyps that len_jxs len_xs xs
          show ?thesis
            by (auto simp add: nth_append_cond intro!: exI[where x = "length xs + n"])
        next
          case False
          with hyps show ?thesis
            using that len_jxs len_xs xs assms
            by (intro exI[where x="(js ! (n - length jxs))"])
               (simp add: nth_append_cond trans_less_add1)
        qed
      qed
      with xs _ _  have "jxs @ map (op ! xs) js \<in> set_of_apprs (?js @ ?js)"
        by (rule set_of_apprs_imp') (simp_all add: len_xs len_jxs lens_eq)
      then show ?thesis
        apply (rule set_of_apprs_nth_eqI)
        using that len_jxs
        by (auto simp add: nth_append)
    qed
    also have "\<dots> = map (op ! xs) js ! i" by (simp add: nth_append)
    finally show ?thesis .
  qed
  then have "jxs = map (op ! xs) js"
    by (auto intro!: nth_equalityI len_jxs)
  ultimately show thesis by (intro that)
qed

lemma
  nth_in_set_of_apprsI:
  assumes "xs \<in> set_of_apprs XS"
  assumes "n < length xs"
  shows "[xs ! n] \<in> set_of_apprs [XS ! n]"
  using length_set_of_apprs[OF assms(1)] assms
  by (induction xs XS arbitrary: n rule: list_induct2)
     (auto simp: nth_Cons set_of_apprs_set_of_appr split: nat.split dest!: set_of_apprs_Cons_ex)

lemma
  nth_in_set_of_apprI:
  assumes "xs \<in> set_of_apprs XS"
  assumes "n < length xs"
  shows "xs ! n \<in> set_of_appr (XS ! n)"
  using nth_in_set_of_apprsI[OF assms]
  by (simp add: set_of_apprs_set_of_appr)

lemma tl_set_of_apprs: "tl ` set_of_apprs (x # xs) = set_of_apprs xs"
  apply (safe elim!: set_of_apprsE )
  subgoal by simp
  subgoal premises prems for ys
    by (rule set_of_apprs_ConsE1[OF prems, of x]) force
  done

lemma nth_image_refine[autoref_rules]:
  assumes "(xs, X) \<in> apprs_rel"
  assumes "(ni, n) \<in> Id"
  shows "((if ni < length xs then RETURN (nth xs ni) else SUCCEED), (OP nth_image::: apprs_rel \<rightarrow> Id \<rightarrow> \<langle>\<langle>Id\<rangle>appr_rel\<rangle>nres_rel) $ X $ n) \<in> \<langle>\<langle>Id\<rangle>appr_rel\<rangle>nres_rel"
  using assms
proof -
  have "x \<in> (\<lambda>x. x ! n) ` set_of_apprs xs"
    if "\<And>x. n < length xs" "x \<in> set_of_appr (xs ! n)"
    for x
    using that
    apply (subst (asm) set_of_apprs_set_of_appr[symmetric])
    apply (erule set_of_apprs_projectsE[of "[x]" xs "[n]" for x, simplified])
    using length_set_of_apprs set_of_apprs_nonempty
    by (auto simp: env_len_def)
  then show ?thesis using assms length_set_of_apprs set_of_apprs_nonempty
    by (auto simp: nth_image_def nth_image_precond_def nres_rel_def RETURN_RES_refine_iff
        appr_rel_def br_def apprs_rel_def env_len_def
        intro!: nth_in_set_of_apprI)
qed

lemma project_env_refine[autoref_rules]:
  assumes "PREFER_id R"
  assumes "(envi, env) \<in> apprs_rel"
  assumes "(isi, is) \<in> \<langle>R\<rangle>list_rel"
  shows
    "((if list_all (op > (length envi)) isi then RETURN (map (\<lambda>i. envi ! i) isi) else SUCCEED), project_env $ env $ is) \<in> \<langle>apprs_rel\<rangle>nres_rel"
  using assms
  by (auto
    simp: project_env_def nth_image_def nres_rel_def project_env_precond_def RETURN_RES_refine_iff
      list_all_iff apprs_rel_def br_def set_of_apprs_projections length_set_of_apprs env_len_def
    intro!: nth_in_set_of_apprI exI[where x="(\<lambda>xs. map (op ! xs) is) ` env"])

lemma image_Suc_nth_set_of_apprs_Cons:
  "(\<lambda>x. x ! Suc x2) ` set_of_apprs (x # xs) = (\<lambda>x. x ! x2) ` set_of_apprs xs"
  apply safe
  subgoal by (auto dest!: set_of_apprs_Cons_ex)
  subgoal by (drule set_of_apprs_ex_Cons) force
  done

lemma
  nth_image_of_set_of_apprs_iff:
  assumes "i < length xs"
  shows "(\<lambda>x. x ! i) ` set_of_apprs xs = set_of_appr (xs ! i)"
  using assms
proof (induct xs arbitrary: i)
  case (Cons x xs)
  have "xa \<in> (\<lambda>x. x ! 0) ` set_of_apprs (x # xs)" if "xa \<in> set_of_appr x" for xa
    using that
    by (force dest: set_of_apprs_ex_Cons2)
  then show ?case
    using Cons(2)
    by (auto simp: nth_Cons image_Suc_nth_set_of_apprs_Cons
        split: nat.split elim!: set_of_apprsE dest!: Cons(1))
qed simp

schematic_goal ivl_of_set_impl:
  assumes [autoref_rules]: "(ai, a) \<in> \<langle>eucl_rel\<rangle>appr_rel"
  shows "(nres_of (?f::?'r dres), ivl_of_set a) \<in> ?R"
  by (rule ivl_of_set_nres[THEN nres_rel_trans2]) autoref_monadic

concrete_definition ivl_of_set_impl for ai uses ivl_of_set_impl
lemma [autoref_rules]: "(\<lambda>x. nres_of (ivl_of_set_impl x), ivl_of_set) \<in> \<langle>eucl_rel\<rangle>appr_rel \<rightarrow> \<langle>Id \<times>\<^sub>r Id\<rangle>nres_rel"
  using ivl_of_set_impl.refine
  by auto

lemma ivl_of_sets_nres: "FORWEAK XS (RETURN (0, 0)) ivl_of_set (\<lambda>(i, s) (i', s'). RETURN (inf i i', sup s s')) \<le> ivl_of_sets XS"
  unfolding ivl_of_sets_def split_beta'
  by (rule FORWEAK_elementwise_rule) (auto simp: subset_iff le_infI1 le_infI2 le_supI1 le_supI2 ivl_of_set_def)

schematic_goal ivl_of_sets_impl:
  assumes [autoref_rules]: "(ai, a) \<in> \<langle>\<langle>eucl_rel\<rangle>appr_rel\<rangle>list_wset_rel"
  shows "(nres_of (?f::?'a dres), ivl_of_sets $ a) \<in> ?R"
  unfolding autoref_tag_defs
  apply (rule nres_rel_trans2)
  apply (rule ivl_of_sets_nres)
  by (autoref_monadic)

concrete_definition ivl_of_sets_impl for ai uses ivl_of_sets_impl
lemmas [autoref_rules] = ivl_of_sets_impl.refine

schematic_goal above_sctn_impl:
  assumes [autoref_rules]: "(ai, a) \<in> \<langle>eucl_rel\<rangle>appr_rel"
  assumes [autoref_rules]: "(sctni, sctn) \<in> Id"
  shows "(?f::?'r, above_sctn $ a $ sctn) \<in> ?R"
  unfolding autoref_tag_defs
  by (rule above_sctn_nres[THEN nres_rel_trans2]) autoref_monadic

concrete_definition above_sctn_impl for ai sctni uses above_sctn_impl
lemmas [autoref_rules] = above_sctn_impl.refine

schematic_goal below_sctn_impl:
  assumes [autoref_rules]: "(ai, a) \<in> \<langle>eucl_rel\<rangle>appr_rel"
  assumes [autoref_rules]: "(sctni, sctn) \<in> Id"
  shows "(?f::?'r, below_sctn $ a $ sctn) \<in> ?R"
  unfolding autoref_tag_defs
  by (rule below_sctn_nres[THEN nres_rel_trans2]) (autoref_monadic (plain))
concrete_definition below_sctn_impl uses below_sctn_impl
lemmas [autoref_rules] = below_sctn_impl.refine

lemma disjoint_sets_nres:
  fixes X Y::"'a::executable_euclidean_space set"
  shows "do {
    iX \<leftarrow> Inf_spec X;
    sX \<leftarrow> Sup_spec X;
    iY \<leftarrow> Inf_spec Y;
    sY \<leftarrow> Sup_spec Y;
    RETURN (list_ex (\<lambda>i. sX \<bullet> i < iY \<bullet> i \<or> sY \<bullet> i < iX \<bullet> i) Basis_list)
  } \<le> disjoint_sets X Y"
  by (force simp: Inf_spec_def Sup_spec_def disjoint_sets_def list_ex_iff eucl_le[where 'a='a]
    intro!: refine_vcg)

schematic_goal disjoint_sets_impl:
  assumes [autoref_rules]: "(ai, a) \<in> \<langle>eucl_rel\<rangle>appr_rel"
  assumes [autoref_rules]: "(bi, b) \<in> \<langle>eucl_rel\<rangle>appr_rel"
  shows "(?f::?'r, disjoint_sets $ a $ b) \<in> ?R"
  unfolding autoref_tag_defs
  by (rule disjoint_sets_nres[THEN nres_rel_trans2]) (autoref_monadic (plain))
concrete_definition disjoint_sets_impl for ai bi uses disjoint_sets_impl
lemmas [autoref_rules] = disjoint_sets_impl.refine

lemma intersects_nres:
  notes Inf_inner_def[refine_vcg]
  shows "(do {
    ii \<leftarrow> Inf_inner X (normal sctn);
    si \<leftarrow> Sup_inner X (normal sctn);
    RETURN (ii \<le> pstn sctn \<and> si \<ge> pstn sctn)
  }) \<le> intersects_spec X sctn"
  unfolding intersects_spec_def Inf_inner_def Sup_inner_def
  by refine_vcg (force simp: plane_of_def)

schematic_goal intersects_impl:
  assumes [autoref_rules]: "(ai, a) \<in> \<langle>eucl_rel\<rangle>appr_rel"
  assumes [autoref_rules]: "(sctni, sctn) \<in> Id"
  shows "(?f::?'r, intersects_spec $ a $ sctn) \<in> ?R"
  unfolding autoref_tag_defs
  by (rule intersects_nres[THEN nres_rel_trans2])
    (autoref_monadic (plain))
concrete_definition intersects_impl uses intersects_impl
lemmas [autoref_rules] = intersects_impl.refine

definition
"project_set X b y =
  do {
    i \<leftarrow> Inf_spec X;
    s \<leftarrow> Sup_spec X;
    ASSERT (i \<le> s);
    RETURN {(i + (y - i \<bullet> b) *\<^sub>R b) .. (s + (y - s \<bullet> b) *\<^sub>R b)}
  }"
sublocale autoref_op_pat_def project_set .

lemma projection_notempty:
  fixes b::'a
  assumes "b \<in> Basis \<or> -b \<in> Basis"
  assumes "x \<le> z"
  shows "x + (y - x \<bullet> b) *\<^sub>R b \<le> z + (y - z \<bullet> b) *\<^sub>R b"
proof -
  define b' where "b' \<equiv> - b"
  then have b_dest: "-b \<in> Basis \<Longrightarrow> b = -b' \<and> b' \<in> Basis"
    by simp
  show ?thesis using assms
    by (auto simp: eucl_le[where 'a='a] algebra_simps inner_Basis dest!: b_dest)
qed

schematic_goal project_set_impl:
  fixes b y
  assumes [unfolded autoref_tag_defs, simp]: "SIDE_PRECOND (b \<in> Basis \<or> -b \<in> Basis)"
  notes [simp] = projection_notempty
  assumes [autoref_rules]: "(Xi, X) \<in> \<langle>eucl_rel\<rangle>appr_rel"
  assumes [autoref_rules]: "(bi, b) \<in> Id"
  assumes [autoref_rules]: "(yi, y) \<in> Id"
  shows "(?f::?'r, project_set $ X $ b $ y) \<in> ?R"
  unfolding project_set_def[abs_def] autoref_tag_defs
  by autoref_monadic
concrete_definition project_set_impl for Xi bi yi uses project_set_impl
lemmas [autoref_rules] = project_set_impl.refine


text \<open>irects are for easy and exact exchange and management of sets as small hypercubes\<close>

definition set_of_irect::"int \<Rightarrow> int list \<Rightarrow> 'a set"
  where "set_of_irect m is =
    {(\<Sum>(i, b)\<leftarrow>zip is Basis_list. FloatR i (-m) *\<^sub>R b) ..
      (\<Sum>(i, b)\<leftarrow>zip is Basis_list. FloatR (i + 1) (-m) *\<^sub>R b)}"
sublocale autoref_op_pat_def set_of_irect .

definition irect_rel_internal: "irect_rel m S = br (set_of_irect m) top O \<langle>S\<rangle>set_rel"
lemma irect_rel_def[refine_rel_defs]: "\<langle>eucl_rel\<rangle>irect_rel m \<equiv> br (set_of_irect m) top"
  unfolding relAPP_def
  by (auto simp: irect_rel_internal)
lemmas [autoref_rel_intf] = REL_INTFI[of "irect_rel" "i_set"]

lemma set_of_irect_notempty: "set_of_irect m is \<noteq> {}"
  by (auto simp: set_of_irect_def in_set_zip intro!: sum_list_mono scaleR_right_mono)

schematic_goal set_of_irect_impl:
  notes [simp] = set_of_irect_def
  shows "(?f::?'r, set_of_irect) \<in> ?R"
  unfolding set_of_irect_def[abs_def] autoref_tag_defs
  using set_of_irect_notempty
  by autoref
concrete_definition set_of_irect_impl uses set_of_irect_impl
lemmas [autoref_rules] = set_of_irect_impl.refine

definition appr_of_irect::"'a set \<Rightarrow> 'a set"
  where [simp]: "appr_of_irect is = is"
sublocale autoref_op_pat_def appr_of_irect .
lemma appr_of_irect_autoref[autoref_rules]:
  shows "(set_of_irect_impl m, appr_of_irect) \<in> \<langle>eucl_rel\<rangle>(irect_rel m) \<rightarrow> \<langle>eucl_rel\<rangle>appr_rel"
  using set_of_irect_impl.refine[THEN fun_relD, THEN fun_relD]
  by (auto simp: irect_rel_def br_def)

end

end
