section \<open>Lifting root steps to single/parallel root/non-root steps\<close>
theory Lift_Root_Step
  imports
    Rewriting
    FOR_Certificate
    Context_Extensions
    Multihole_Context
begin

text \<open>Closure under all contexts\<close>
abbreviation "gctxtcl \<R> \<equiv> gctxtex_onp (\<lambda> C. True) \<R>"
abbreviation "gmctxtcl \<R> \<equiv> gctxtex_onp (\<lambda> C. True) \<R>"

text \<open>Extension under all non empty contexts\<close>
abbreviation "gctxtex_nempty \<R> \<equiv> gctxtex_onp (\<lambda> C. C \<noteq> \<box>\<^sub>G) \<R>"
abbreviation "gmctxtex_nempty \<R> \<equiv> gmctxtex_onp (\<lambda> C. C \<noteq> GMHole) \<R>"

text \<open>Closure under all contexts respecting the signature\<close>
abbreviation "gctxtcl_funas \<F> \<R> \<equiv> gctxtex_onp (\<lambda> C. funas_gctxt C \<subseteq> \<F>) \<R>"
abbreviation "gmctxtcl_funas \<F> \<R> \<equiv> gmctxtex_onp (\<lambda> C. funas_gmctxt C \<subseteq> \<F>) \<R>"

text \<open>Closure under all multihole contexts with at least one hole respecting the signature\<close>
abbreviation "gmctxtcl_funas_strict \<F> \<R> \<equiv> gmctxtex_onp (\<lambda> C. 0 < num_gholes C \<and> funas_gmctxt C \<subseteq> \<F>) \<R>"

text \<open>Extension under all non empty contexts respecting the signature\<close>
abbreviation "gctxtex_funas_nroot \<F> \<R> \<equiv> gctxtex_onp (\<lambda> C. funas_gctxt C \<subseteq> \<F> \<and> C \<noteq> \<box>\<^sub>G) \<R>"
abbreviation "gmctxtex_funas_nroot \<F> \<R> \<equiv> gmctxtex_onp (\<lambda> C. funas_gmctxt C \<subseteq> \<F> \<and> C \<noteq> GMHole) \<R>"

text \<open>Extension under all non empty contexts respecting the signature\<close>
abbreviation "gmctxtex_funas_nroot_strict \<F> \<R> \<equiv>
   gmctxtex_onp (\<lambda> C.  0 < num_gholes C \<and> funas_gmctxt C \<subseteq> \<F> \<and> C \<noteq> GMHole) \<R>"


subsection \<open>Rewrite steps equivalent definitions\<close>

definition gsubst_cl :: "('f, 'v) trs \<Rightarrow> 'f gterm rel" where
  "gsubst_cl \<R> = {(gterm_of_term (l \<cdot> \<sigma>), gterm_of_term (r \<cdot> \<sigma>)) |
    l r (\<sigma> :: 'v \<Rightarrow> ('f, 'v) Term.term). (l, r) \<in> \<R> \<and> ground (l \<cdot> \<sigma>) \<and> ground (r \<cdot> \<sigma>)}"

definition gnrrstepD :: "'f sig \<Rightarrow> 'f gterm rel \<Rightarrow> 'f gterm rel" where
  "gnrrstepD \<F> \<R> = gctxtex_funas_nroot \<F> \<R>"

definition grstepD :: "'f sig \<Rightarrow> 'f gterm rel \<Rightarrow> 'f gterm rel" where
  "grstepD \<F> \<R> = gctxtcl_funas \<F> \<R>"

definition gpar_rstepD :: "'f sig \<Rightarrow> 'f gterm rel \<Rightarrow> 'f gterm rel" where
  "gpar_rstepD \<F> \<R> = gmctxtcl_funas \<F> \<R>"

inductive_set gpar_rstepD' :: "'f sig \<Rightarrow> 'f gterm rel \<Rightarrow> 'f gterm rel" for \<F> :: "'f sig" and \<R> :: "'f gterm rel"
  where groot_step [intro]: "(s, t) \<in> \<R> \<Longrightarrow> (s, t) \<in> gpar_rstepD' \<F> \<R>"
     |  gpar_step_fun [intro]: "\<lbrakk>\<And> i. i < length ts \<Longrightarrow> (ss ! i, ts ! i) \<in> gpar_rstepD' \<F> \<R>\<rbrakk> \<Longrightarrow> length ss = length ts
             \<Longrightarrow> (f, length ts) \<in> \<F> \<Longrightarrow> (GFun f ss, GFun f ts) \<in> gpar_rstepD' \<F> \<R>"

subsection \<open>Interface between rewrite step definitions and sets\<close>

fun lift_root_step :: "('f \<times> nat) set \<Rightarrow> pos_step \<Rightarrow> ext_step \<Rightarrow> 'f gterm rel \<Rightarrow> 'f gterm rel" where
  "lift_root_step \<F> PAny ESingle \<R> = gctxtcl_funas \<F> \<R>"
| "lift_root_step \<F> PAny EStrictParallel \<R> = gmctxtcl_funas_strict \<F> \<R>"
| "lift_root_step \<F> PAny EParallel \<R> = gmctxtcl_funas \<F> \<R>"
| "lift_root_step \<F> PNonRoot ESingle \<R> = gctxtex_funas_nroot \<F> \<R>"
| "lift_root_step \<F> PNonRoot EStrictParallel \<R> = gmctxtex_funas_nroot_strict \<F> \<R>"
| "lift_root_step \<F> PNonRoot EParallel \<R> = gmctxtex_funas_nroot \<F> \<R>"
| "lift_root_step \<F> PRoot ESingle \<R> = \<R>"
| "lift_root_step \<F> PRoot EStrictParallel \<R> = \<R>"
| "lift_root_step \<F> PRoot EParallel \<R> = \<R> \<union> Restr Id (\<T>\<^sub>G \<F>)"

subsection \<open>Compatibility of used predicate extensions and signature closure\<close>

lemma compatible_p [simp]:
  "compatible_p (\<lambda> C. C \<noteq> \<box>\<^sub>G) (\<lambda> C. C \<noteq> GMHole)"
  "compatible_p (\<lambda> C. funas_gctxt C \<subseteq> \<F>) (\<lambda> C. funas_gmctxt C \<subseteq> \<F>)"
  "compatible_p (\<lambda> C. funas_gctxt C \<subseteq> \<F> \<and> C \<noteq> \<box>\<^sub>G) (\<lambda> C. funas_gmctxt C \<subseteq> \<F> \<and> C \<noteq> GMHole)"
  unfolding compatible_p_def
  by rule (case_tac C, auto)+

lemma gmctxtcl_funas_sigcl:
  "all_ctxt_closed \<F> (gmctxtcl_funas \<F> \<R>)"
  by (intro gmctxtex_onp_sig_closed) auto

lemma gctxtex_funas_nroot_sigcl:
  "all_ctxt_closed \<F> (gmctxtex_funas_nroot \<F> \<R>)"
  by (intro gmctxtex_onp_sig_closed) auto

lemma gmctxtcl_funas_strict_funcl:
  "function_closed \<F> (gmctxtcl_funas_strict \<F> \<R>)"
  by (intro gmctxtex_onp_fun_closed) (auto dest: list.set_sel)

lemma gmctxtex_funas_nroot_strict_funcl:
  "function_closed \<F> (gmctxtex_funas_nroot_strict \<F> \<R>)"
  by (intro gmctxtex_onp_fun_closed) (auto dest: list.set_sel)

lemma gctxtcl_funas_dist:
  "gctxtcl_funas \<F> \<R> = gctxtex_onp (\<lambda> C. C = \<box>\<^sub>G) \<R> \<union> gctxtex_funas_nroot \<F> \<R>"
  by (intro gctxtex_onp_pred_dist) auto

lemma gmctxtex_funas_nroot_dist:
  "gmctxtex_funas_nroot \<F> \<R> = gmctxtex_funas_nroot_strict \<F> \<R> \<union>
     gmctxtex_onp (\<lambda> C. num_gholes C = 0 \<and> funas_gmctxt C \<subseteq> \<F>) \<R>"
  by (intro gmctxtex_onp_pred_dist) auto

lemma gmctxtcl_funas_dist:
  "gmctxtcl_funas \<F> \<R> = gmctxtex_onp (\<lambda> C. num_gholes C = 0 \<and> funas_gmctxt C \<subseteq> \<F>) \<R> \<union>
     gmctxtex_onp (\<lambda> C. 0 < num_gholes C \<and> funas_gmctxt C \<subseteq> \<F>) \<R>"
  by (intro gmctxtex_onp_pred_dist) auto

lemma gmctxtcl_funas_strict_dist:
  "gmctxtcl_funas_strict \<F> \<R> = gmctxtex_funas_nroot_strict \<F> \<R> \<union> gmctxtex_onp (\<lambda> C. C = GMHole) \<R>"
  by (intro gmctxtex_onp_pred_dist) auto

lemma gmctxtex_onpzero_num_gholes_id [simp]:
  "gmctxtex_onp (\<lambda> C. num_gholes C = 0 \<and> funas_gmctxt C \<subseteq> \<F>) \<R> = Restr Id (\<T>\<^sub>G \<F>)" (is "?Ls = ?Rs")
proof -
  {fix s t assume "(s, t) \<in> ?Ls" from gmctxtex_onpE[OF this] obtain C us vs where
    *: "s = fill_gholes C us" "t = fill_gholes C vs" and
    len: "num_gholes C = length us" "length us = length vs" and
    inv: "num_gholes C = 0 \<and> funas_gmctxt C \<subseteq> \<F>" by auto
    then have "(s, t) \<in> ?Rs" using len inv unfolding *
      by (cases us; cases vs) (auto simp: \<T>\<^sub>G_funas_gterm_conv)}
  moreover have "?Rs \<subseteq> ?Ls"
    by (intro Restr_id_subset_gmctxtex_onp) auto
  ultimately show ?thesis by auto
qed

lemma gctxtex_onp_sign_trans_fst:
  assumes "(s, t) \<in> gctxtex_onp P R" and "s \<in> \<T>\<^sub>G \<F>"
  shows "(s, t) \<in> gctxtex_onp (\<lambda> C. funas_gctxt C \<subseteq> \<F> \<and> P C) R"
  using assms
  by (auto simp: \<T>\<^sub>G_equivalent_def elim!: gctxtex_onpE)

lemma gctxtex_onp_sign_trans_snd:
  assumes "(s, t) \<in> gctxtex_onp P R" and "t \<in> \<T>\<^sub>G \<F>"
  shows "(s, t) \<in> gctxtex_onp (\<lambda> C. funas_gctxt C \<subseteq> \<F> \<and> P C) R"
  using assms
  by (auto simp: \<T>\<^sub>G_equivalent_def elim!: gctxtex_onpE)

lemma gmctxtex_onp_sign_trans_fst:
  assumes "(s, t) \<in> gmctxtex_onp P R" and "s \<in> \<T>\<^sub>G \<F>"
  shows "(s, t) \<in> gmctxtex_onp (\<lambda> C. P C \<and> funas_gmctxt C \<subseteq> \<F>) R"
  using assms
  by (auto simp: \<T>\<^sub>G_equivalent_def simp add: gmctxtex_onpI)

lemma gmctxtex_onp_sign_trans_snd:
  assumes "(s, t) \<in> gmctxtex_onp P R" and "t \<in> \<T>\<^sub>G \<F>"
  shows "(s, t) \<in> gmctxtex_onp (\<lambda> C. P C \<and> funas_gmctxt C \<subseteq> \<F>) R"
  using assms
  by (auto simp: \<T>\<^sub>G_equivalent_def simp add: gmctxtex_onpI)

subsection \<open>Basic lemmas\<close>

lemma gsubst_cl:
  fixes \<R> :: "('f, 'v) trs" and \<sigma> :: "'v \<Rightarrow> ('f, 'v) term"
  assumes "(l, r) \<in> \<R>" and "ground (l \<cdot> \<sigma>)" "ground (r \<cdot> \<sigma>)"
  shows "(gterm_of_term (l \<cdot> \<sigma>), gterm_of_term (r \<cdot> \<sigma>)) \<in> gsubst_cl \<R>"
  using assms unfolding gsubst_cl_def by auto

lemma grstepD [simp]:
  "(s, t) \<in> \<R> \<Longrightarrow> (s, t) \<in> grstepD \<F> \<R>"
  by (auto simp: grstepD_def gctxtex_onp_def intro!: exI[of _ "\<box>\<^sub>G"])

lemma grstepD_ctxtI [intro]:
  "(l, r) \<in> \<R> \<Longrightarrow> funas_gctxt C \<subseteq> \<F> \<Longrightarrow> (C\<langle>l\<rangle>\<^sub>G, C\<langle>r\<rangle>\<^sub>G) \<in> grstepD \<F> \<R>"
  by (auto simp: grstepD_def gctxtex_onp_def intro!: exI[of _ "C"])

lemma gctxtex_funas_nroot_gctxtcl_funas_subseteq:
  "gctxtex_funas_nroot \<F> (grstepD \<F> \<R>) \<subseteq> grstepD \<F> \<R>"
  unfolding grstepD_def
  by (intro gctxtex_pred_cmp_subseteq) auto

lemma Restr_gnrrstepD_dist [simp]:
  "Restr (gnrrstepD \<F> \<R>) (\<T>\<^sub>G \<G>) = gnrrstepD (\<F> \<inter> \<G>) (Restr \<R> (\<T>\<^sub>G \<G>))"
  by (auto simp add: gnrrstepD_def)

lemma Restr_grstepD_dist [simp]:
  "Restr (grstepD \<F> \<R>) (\<T>\<^sub>G \<G>) = grstepD (\<F> \<inter> \<G>) (Restr \<R> (\<T>\<^sub>G \<G>))"
  by (auto simp add: grstepD_def)

lemma Restr_gpar_rstepD_dist [simp]:
  "Restr (gpar_rstepD \<F> \<R>) (\<T>\<^sub>G \<G>) = gpar_rstepD (\<F> \<inter> \<G>) (Restr \<R> (\<T>\<^sub>G \<G>))" (is "?Ls = ?Rs")
  by (auto simp: gpar_rstepD_def)

subsection \<open>Equivalence lemmas\<close>

lemma grrstep_subst_cl_conv:
  "grrstep \<R> = gsubst_cl \<R>"
  unfolding gsubst_cl_def grrstep_def rrstep_def rstep_r_p_s_def
  by (auto, metis ground_substI ground_term_of_gterm term_of_gterm_inv) blast

lemma gnrrstepD_gnrrstep_conv:
  "gnrrstep \<R> = gnrrstepD UNIV (gsubst_cl \<R>)" (is "?Ls = ?Rs")
proof -
  {fix s t assume "(s, t) \<in> ?Ls" then obtain l r C \<sigma> where
      mem: "(l, r) \<in> \<R>" "C \<noteq> \<box>" "term_of_gterm s = C\<langle>l \<cdot> (\<sigma> :: 'b \<Rightarrow> ('a, 'b) term)\<rangle>" "term_of_gterm t = C\<langle>r \<cdot> \<sigma>\<rangle>"
      unfolding gnrrstep_def inv_image_def nrrstep_def' by auto
    then have "(s, t) \<in> ?Rs" using gsubst_cl[OF mem(1)]
      using gctxtex_onpI[of "\<lambda> C. funas_gctxt C \<subseteq> UNIV \<and> C \<noteq> \<box>\<^sub>G" "gctxt_of_ctxt C" "gterm_of_term (l \<cdot> \<sigma>)"
        "gterm_of_term (r \<cdot> \<sigma>)" "gsubst_cl \<R>"]
      by (auto simp: gnrrstepD_def)}
  moreover
  {fix s t assume "(s, t) \<in> ?Rs" then have "(s, t) \<in> ?Ls"
      unfolding gnrrstepD_def gctxtex_onp_def gnrrstep_def inv_image_def nrrstep_def' gsubst_cl_def
      by auto (metis ctxt_of_gctxt.simps(1) ctxt_of_gctxt_inv ground_ctxt_of_gctxt ground_gctxt_of_ctxt_apply ground_substI)}
  ultimately show ?thesis by auto
qed

lemma grstepD_grstep_conv:
  "grstep \<R> = grstepD UNIV (gsubst_cl \<R>)" (is "?Ls = ?Rs")
proof -
  {fix s t assume "(s, t) \<in> ?Ls" then obtain C l r \<sigma> where
    mem: "(l, r) \<in> \<R>" "term_of_gterm s = C\<langle>l \<cdot> (\<sigma> :: 'b \<Rightarrow> ('a, 'b) term)\<rangle>" "term_of_gterm t = C\<langle>r \<cdot> \<sigma>\<rangle>"
      unfolding grstep_def inv_image_def by auto
    then have "(s, t) \<in> ?Rs" using grstepD_ctxtI[OF gsubst_cl[OF mem(1)], of \<sigma> "gctxt_of_ctxt C" UNIV]
      by (auto simp: grstepD_def gctxtex_onp_def)}
  moreover
  {fix s t assume "(s, t) \<in> ?Rs" then have "(s, t) \<in> ?Ls"
      by (auto simp: gctxtex_onp_def grstepD_def grstep_def gsubst_cl_def)
       (metis ctxt_of_gctxt_apply_gterm ground_ctxt_apply
        ground_ctxt_of_gctxt ground_substI gterm_of_term_inv rstep.intros)}
  ultimately show ?thesis by auto
qed

lemma gpar_rstep_gpar_rstepD_conv:
  "gpar_rstep \<R> = gpar_rstepD' UNIV (gsubst_cl \<R>)" (is "?Ls = ?Rs")
proof -
  {fix s t assume "(s, t) \<in> ?Rs"
    then have "(s, t) \<in> gpar_rstep \<R>"
      by induct (auto simp: gpar_rstep_def gsubst_cl_def)}
  moreover
  {fix s t assume ass: "(s, t) \<in> ?Ls" then obtain u v where
      "(u, v) \<in> par_rstep \<R>" "u = term_of_gterm s" "v = term_of_gterm t"
        by (simp add: gpar_rstep_def inv_image_def)
    then have "(s, t) \<in> ?Rs"
    proof (induct arbitrary: s t)
      case (root_step u v \<sigma>)
      then have "(s, t) \<in> gsubst_cl \<R>" unfolding gsubst_cl_def
        by auto (metis ground_substI ground_term_of_gterm term_of_gterm_inv)
      then show ?case by auto
    next
      case (par_step_fun ts ss f)
      then show ?case by (cases s; cases t) auto
    next
      case (par_step_var x)
      then show ?case by (cases s) auto
  qed}
  ultimately show ?thesis by auto
qed

lemma gmctxtcl_funas_idem:
  "gmctxtcl_funas \<F> (gmctxtcl_funas \<F> \<R>) \<subseteq> gmctxtcl_funas \<F> \<R>"
  by (intro gmctxtex_pred_cmp_subseteq)
    (auto elim!: less_eq_to_sup_mctxt_args, blast+)

lemma gpar_rstepD_gpar_rstepD'_conv:
  "gpar_rstepD \<F> \<R> = gpar_rstepD' \<F> \<R>" (is "?Ls = ?Rs")
proof -
  {fix s t assume "(s, t) \<in> ?Rs" then have "(s, t) \<in> ?Ls"
    proof induct
      case (groot_step s t) then show ?case unfolding gpar_rstepD_def
        using gmctxtex_onpI[of _ GMHole  "[s]" "[t]"]
        by auto
    next
      case (gpar_step_fun ts ss f)
      show ?case using gpar_step_fun(2-) unfolding gpar_rstepD_def
        using subsetD[OF gmctxtcl_funas_idem, of "(GFun f ss, GFun f ts)" \<F> \<R>]
        using gmctxtex_onpI[of _ "GMFun f (replicate (length ss) GMHole)" ss ts "gmctxtcl_funas \<F> \<R>"]
        by (auto simp del: fill_gholes.simps)
    qed}
  moreover
  {fix s t assume "(s, t) \<in> ?Ls" then obtain C ss ts where
    t: "s = fill_gholes C ss" "t = fill_gholes C ts" and
    inv: "num_gholes C = length ss" "num_gholes C = length ts" and
    pred: "funas_gmctxt C \<subseteq> \<F>" and rel: "\<forall> i < length ts. (ss ! i, ts ! i) \<in> \<R>"
      unfolding gpar_rstepD_def by auto
    have "(s, t) \<in> ?Rs" using inv pred rel unfolding t
    proof (induct rule: fill_gholes_induct2)
      case (GMHole x) then show ?case
        by (cases ts) auto
    next
      case (GMFun f Cs xs ys)
      from GMFun(1, 2, 5) have "i < length Cs \<Longrightarrow> \<forall> j < length (partition_gholes ys Cs ! i).
        (partition_gholes xs Cs ! i ! j, partition_gholes ys Cs ! i ! j) \<in> \<R>" for i
        by (auto simp: length_partition_by_nth partition_by_nth_nth(1, 2))
      from GMFun this show ?case unfolding partition_holes_fill_gholes_conv'
        by (intro gpar_step_fun) (auto, meson UN_I nth_mem subset_iff)
    qed}
  ultimately show ?thesis by auto
qed

subsection \<open>Signature preserving lemmas\<close>

lemma \<T>\<^sub>G_trans_closure_id [simp]:
  "(\<T>\<^sub>G \<F> \<times> \<T>\<^sub>G \<F>)\<^sup>+ = \<T>\<^sub>G \<F> \<times> \<T>\<^sub>G \<F>"
  by (auto simp: trancl_full_on)

lemma signature_pres_funas_cl [simp]:
  "\<R> \<subseteq> \<T>\<^sub>G \<F> \<times> \<T>\<^sub>G \<F> \<Longrightarrow> gctxtcl_funas \<F> \<R> \<subseteq> \<T>\<^sub>G \<F> \<times> \<T>\<^sub>G \<F>"
  "\<R> \<subseteq> \<T>\<^sub>G \<F> \<times> \<T>\<^sub>G \<F> \<Longrightarrow> gmctxtcl_funas \<F> \<R> \<subseteq> \<T>\<^sub>G \<F> \<times> \<T>\<^sub>G \<F>"
  apply (intro gctxtex_onp_in_signature) apply blast+
  apply (intro gmctxtex_onp_in_signature) apply blast+
  done

lemma relf_on_gmctxtcl_funas:
  assumes "\<R> \<subseteq> \<T>\<^sub>G \<F> \<times> \<T>\<^sub>G \<F>"
  shows "refl_on (\<T>\<^sub>G \<F>) (gmctxtcl_funas \<F> \<R>)"
proof -
  have "t \<in> \<T>\<^sub>G \<F> \<Longrightarrow> (t, t) \<in> gmctxtcl_funas \<F> \<R>" for t
    using gmctxtex_onpI[of _ "gmctxt_of_gterm t"]
    by (auto simp: \<T>\<^sub>G_funas_gterm_conv)
  then show ?thesis using assms
    by (auto simp: refl_on_def)
qed

lemma gtrancl_rel_sound:
  "\<R> \<subseteq> \<T>\<^sub>G \<F> \<times> \<T>\<^sub>G \<F> \<Longrightarrow> gtrancl_rel \<F> \<R> \<subseteq> \<T>\<^sub>G \<F> \<times> \<T>\<^sub>G \<F>"
  unfolding gtrancl_rel_def
  by (intro Restr_tracl_comp_simps(3)) (auto simp: gmctxt_cl_gmctxtex_onp_conv)


subsection \<open>@{const gcomp_rel} and @{const gtrancl_rel} lemmas\<close>

lemma gcomp_rel:
  "lift_root_step \<F> PAny EParallel (gcomp_rel \<F> \<R> \<S>) = lift_root_step \<F> PAny EParallel \<R> O lift_root_step \<F> PAny EParallel \<S>" (is "?Ls = ?Rs")
proof
  { fix s u assume "(s, u) \<in> gpar_rstepD' \<F> (\<R> O gpar_rstepD' \<F> \<S> \<union> gpar_rstepD' \<F> \<R> O \<S>)"
     then have "\<exists>t. (s, t) \<in> gpar_rstepD' \<F> \<R> \<and> (t, u) \<in> gpar_rstepD' \<F> \<S>"
    proof (induct)
      case (gpar_step_fun ts ss f)
      from Ex_list_of_length_P[of _ "\<lambda> u i. (ss ! i, u) \<in> gpar_rstepD' \<F> \<R> \<and> (u, ts ! i) \<in> gpar_rstepD' \<F> \<S>"]
      obtain us where l: "length us = length ts" and
        inv: "\<forall> i < length ts. (ss ! i, us ! i) \<in> gpar_rstepD' \<F> \<R> \<and> (us ! i, ts ! i) \<in> gpar_rstepD' \<F> \<S>"
        using gpar_step_fun(2, 3) by blast
      then show ?case using gpar_step_fun(3, 4)
        by (auto intro!: exI[of _ "GFun f us"])
    qed auto}
  then show "?Ls \<subseteq> ?Rs" unfolding gcomp_rel_def
    by (auto simp: gmctxt_cl_gmctxtex_onp_conv simp flip: gpar_rstepD_gpar_rstepD'_conv[unfolded gpar_rstepD_def])
next
  {fix s t u assume "(s, t) \<in> gpar_rstepD' \<F> \<R>" "(t, u) \<in> gpar_rstepD' \<F> \<S>"
    then have "(s, u) \<in> gpar_rstepD' \<F> (\<R> O gpar_rstepD' \<F> \<S> \<union> gpar_rstepD' \<F> \<R> O \<S>)"
    proof (induct arbitrary: u rule: gpar_rstepD'.induct)
      case (gpar_step_fun ts ss f) note IS = this
      show ?case
      proof (cases "(GFun f ts, u) \<in> \<S>")
        case True
        then have "(GFun f ss, u) \<in> gpar_rstepD' \<F> \<R> O \<S>" using IS(1, 3, 4)
          by auto
        then show ?thesis by auto
      next
        case False
        then obtain us where u[simp]: "u = GFun f us" and l: "length ts = length us"
          using IS(5) by (cases u) (auto elim!: gpar_rstepD'.cases)
        have "i < length us \<Longrightarrow>
         (ss ! i, us ! i) \<in> gpar_rstepD' \<F> (\<R> O gpar_rstepD' \<F> \<S> \<union> gpar_rstepD' \<F> \<R> O \<S>)" for i
          using IS(2, 5) False
          by (auto elim!: gpar_rstepD'.cases)
        then show ?thesis using l IS(3, 4) unfolding u
          by auto
      qed
    qed auto}
  then show "?Rs \<subseteq> ?Ls"
    by (auto simp: gmctxt_cl_gmctxtex_onp_conv gcomp_rel_def gpar_rstepD_gpar_rstepD'_conv[unfolded gpar_rstepD_def])
qed

lemma gmctxtcl_funas_in_rtrancl_gctxtcl_funas:
  assumes "\<R> \<subseteq> \<T>\<^sub>G \<F> \<times> \<T>\<^sub>G \<F>"
  shows "gmctxtcl_funas \<F> \<R> \<subseteq> (gctxtcl_funas \<F> \<R>)\<^sup>*" using assms
  by (intro gmctxtex_onp_gctxtex_onp_rtrancl) (auto simp: gmctxt_p_inv_def)

lemma R_in_gtrancl_rel:
  assumes "\<R> \<subseteq> \<T>\<^sub>G \<F> \<times> \<T>\<^sub>G \<F>"
  shows "\<R> \<subseteq> gtrancl_rel \<F> \<R>"
proof
  fix s t assume ass: "(s, t) \<in> \<R>"
  then have "(s, s) \<in> gmctxtcl_funas \<F> \<R>" "(t, t) \<in> gmctxtcl_funas \<F> \<R>" using assms
    using all_ctxt_closed_imp_reflx_on_sig[OF gmctxtcl_funas_sigcl, of \<F> \<R>]
    by auto
  then show "(s, t) \<in> gtrancl_rel \<F> \<R>" using ass
    by (auto simp: gmctxt_cl_gmctxtex_onp_conv relcomp_unfold gtrancl_rel_def)
qed

lemma trans_gtrancl_rel [simp]:
  "trans (gtrancl_rel \<F> \<R>)"
proof -
  have "(s, t) \<in> \<R> \<Longrightarrow> (s, t) \<in> gmctxtcl_funas \<F> \<R>" for s t
    by (metis bot.extremum funas_gmctxt.simps(2) gmctxtex_closure subsetD)
  then show ?thesis unfolding trans_def gtrancl_rel_def
    by (auto simp: gmctxt_cl_gmctxtex_onp_conv, meson relcomp3_I trancl_into_trancl2 trancl_trans)
qed

lemma gtrancl_rel_cl:
  assumes "\<R> \<subseteq> \<T>\<^sub>G \<F> \<times> \<T>\<^sub>G \<F>"
  shows "gmctxtcl_funas \<F> (gtrancl_rel \<F> \<R>) \<subseteq> (gmctxtcl_funas \<F> \<R>)\<^sup>+"
proof -
 have *:"(s, t) \<in> \<R> \<Longrightarrow> (s, t) \<in> gmctxtcl_funas \<F> \<R>" for s t
    by (metis bot.extremum funas_gmctxt.simps(2) gmctxtex_closure subsetD)
  have "gmctxtcl_funas \<F> ((gmctxtcl_funas \<F> \<R>)\<^sup>+) \<subseteq> (gmctxtcl_funas \<F> \<R>)\<^sup>+"
    unfolding gtrancl_rel_def using relf_on_gmctxtcl_funas[OF assms]
    by (intro gmctxtex_onp_substep_trancl, intro gmctxtex_pred_cmp_subseteq2)
       (auto simp: less_sup_gmctxt_args_funas_gmctxt refl_on_def)
  moreover have "gtrancl_rel \<F> \<R> \<subseteq> (gmctxtcl_funas \<F> \<R>)\<^sup>+"
    unfolding gtrancl_rel_def using *
    by (auto simp: gmctxt_cl_gmctxtex_onp_conv, meson trancl.trancl_into_trancl trancl_trans)
  ultimately show ?thesis using gmctxtex_onp_rel_mono by blast
qed

lemma gtrancl_rel_aux:
  "\<R> \<subseteq> \<T>\<^sub>G \<F> \<times> \<T>\<^sub>G \<F> \<Longrightarrow> gmctxtcl_funas \<F> (gtrancl_rel \<F> \<R>) O gtrancl_rel \<F> \<R> \<subseteq> gtrancl_rel \<F> \<R>"
  "\<R> \<subseteq> \<T>\<^sub>G \<F> \<times> \<T>\<^sub>G \<F> \<Longrightarrow> gtrancl_rel \<F> \<R> O gmctxtcl_funas \<F> (gtrancl_rel \<F> \<R>) \<subseteq> gtrancl_rel \<F> \<R>"
  using subsetD[OF gtrancl_rel_cl[of \<R> \<F>]] unfolding gtrancl_rel_def
  by (auto simp: gmctxt_cl_gmctxtex_onp_conv) (meson relcomp3_I trancl_trans)+


declare subsetI [rule del]
lemma gtrancl_rel:
  assumes "\<R> \<subseteq> \<T>\<^sub>G \<F> \<times> \<T>\<^sub>G \<F>" "compatible_p Q P"
    and "\<And> C. P C \<Longrightarrow> funas_gmctxt C \<subseteq> \<F>"
    and "\<And> C D. P C \<Longrightarrow> P D \<Longrightarrow> (C, D) \<in> comp_gmctxt \<Longrightarrow> P (C \<sqinter> D)"
  shows "(gctxtex_onp Q \<R>)\<^sup>+ \<subseteq> gmctxtex_onp P (gtrancl_rel \<F> \<R>)"
proof -
  have fst: "gctxtex_onp Q \<R> \<subseteq> gctxtex_onp Q (gtrancl_rel \<F> \<R>)"
    using R_in_gtrancl_rel[OF assms(1)]
    by (simp add: gctxtex_onp_rel_mono)
  have snd: "gctxtex_onp Q (gtrancl_rel \<F> \<R>) \<subseteq> gmctxtex_onp P (gtrancl_rel \<F> \<R>)"
    using assms(2)
    by auto
  have "(gmctxtex_onp P (gtrancl_rel \<F> \<R>))\<^sup>+ = gmctxtex_onp P (gtrancl_rel \<F> \<R>)"
    by (intro gmctxtex_onp_substep_tranclE[of _ "\<lambda> C. funas_gmctxt C \<subseteq> \<F>"])
      (auto simp: gtrancl_rel_aux[OF assms(1)] assms(3, 4) intro: funas_gmctxt_poss_gmctxt_subgm_at_funas)
  then show ?thesis using subset_trans[OF fst snd]
    using trancl_mono_set by fastforce
qed

lemma gtrancl_rel_subseteq_trancl_gctxtcl_funas:
  assumes "\<R> \<subseteq> \<T>\<^sub>G \<F> \<times> \<T>\<^sub>G \<F>"
  shows "gtrancl_rel \<F> \<R> \<subseteq> (gctxtcl_funas \<F> \<R>)\<^sup>+"
proof -
  have [dest!]: "(s, t) \<in> \<R> \<Longrightarrow> (s, t) \<in> (gctxtcl_funas \<F> \<R>)\<^sup>+" for s t
    using grstepD grstepD_def by blast
  have [dest!]: "(s, t) \<in> (gmctxtcl_funas \<F> \<R>)\<^sup>+ \<Longrightarrow> (s, t) \<in> (gctxtcl_funas \<F> \<R>)\<^sup>+ \<union> Restr Id (\<T>\<^sub>G \<F>)"
    for s t
    using gmctxtcl_funas_in_rtrancl_gctxtcl_funas[OF assms]
    using signature_pres_funas_cl[OF assms]
    apply (auto simp: gtrancl_rel_def rtrancl_eq_or_trancl intro!: subsetI)
    apply (metis rtranclD rtrancl_trancl_absorb trancl_mono)
    apply (metis mem_Sigma_iff trancl_full_on trancl_mono)+
    done
  then show ?thesis using gtrancl_rel_sound[OF assms]
    by (auto simp: gtrancl_rel_def rtrancl_eq_or_trancl gmctxt_cl_gmctxtex_onp_conv intro!: subsetI)
qed

lemma gmctxtex_onp_gtrancl_rel:
  assumes "\<R> \<subseteq> \<T>\<^sub>G \<F> \<times> \<T>\<^sub>G \<F>" and "\<And> C D. Q C \<Longrightarrow> funas_gctxt D \<subseteq> \<F> \<Longrightarrow> Q (C \<circ>\<^sub>G\<^sub>c D)"
    and "\<And>C. P C \<Longrightarrow> 0 < num_gholes C \<and> funas_gmctxt C \<subseteq> \<F>"
    and "\<And>C. P C \<Longrightarrow> gmctxt_p_inv C \<F> Q"
  shows "gmctxtex_onp P (gtrancl_rel \<F> \<R>) \<subseteq> (gctxtex_onp Q \<R>)\<^sup>+"
proof -
  {fix s t assume ass: "(s, t) \<in> gctxtex_onp Q ((gctxtcl_funas \<F> \<R>)\<^sup>+)"
    from gctxtex_onpE[OF ass] obtain C u v where
      *: "s = C\<langle>u\<rangle>\<^sub>G" "t = C\<langle>v\<rangle>\<^sub>G" and
      inv: "Q C" "(u, v) \<in> (gctxtcl_funas \<F> \<R>)\<^sup>+" by blast
    from inv(2) have "(s, t) \<in> (gctxtex_onp Q \<R>)\<^sup>+" unfolding *
    proof induct
      case (base y)
      then show ?case using assms(2)[OF inv(1)]
        by (auto elim!: gctxtex_onpE) (metis ctxt_ctxt_compose gctxtex_onpI trancl.r_into_trancl)
    next
      case (step y z)
      from step(2) have "(C\<langle>y\<rangle>\<^sub>G, C\<langle>z\<rangle>\<^sub>G) \<in>  gctxtex_onp Q \<R>" using assms(2)[OF inv(1)]
        by (auto elim!: gctxtex_onpE) (metis ctxt_ctxt_compose gctxtex_onpI) 
      then show ?case using step(3)
        by auto
    qed}
  then have con: "gctxtex_onp Q ((gctxtcl_funas \<F> \<R>)\<^sup>+) \<subseteq> (gctxtex_onp Q \<R>)\<^sup>+"
    using subrelI by blast
  have snd: "gmctxtex_onp P ((gctxtcl_funas \<F> \<R>)\<^sup>+) \<subseteq> (gctxtex_onp Q ((gctxtcl_funas \<F> \<R>)\<^sup>+))\<^sup>+"
    using assms(1)
    by (intro gmctxtex_onp_gctxtex_onp_trancl[OF assms(3) _ assms(4)]) auto
  have fst: "gmctxtex_onp P (gtrancl_rel \<F> \<R>) \<subseteq> gmctxtex_onp P ((gctxtcl_funas \<F> \<R>)\<^sup>+)"
    using gtrancl_rel_subseteq_trancl_gctxtcl_funas[OF assms(1)]
    by (simp add: gmctxtex_onp_rel_mono)
  show ?thesis using subset_trans[OF fst snd] con
    by (auto intro!: subsetI)
       (metis (no_types, lifting) in_mono rtrancl_trancl_trancl tranclD2 trancl_mono trancl_rtrancl_absorb)
qed

lemma gmctxtcl_funas_strict_gtrancl_rel:
  assumes "\<R> \<subseteq> \<T>\<^sub>G \<F> \<times> \<T>\<^sub>G \<F>"
  shows "gmctxtcl_funas_strict \<F> (gtrancl_rel \<F> \<R>) = (gctxtcl_funas \<F> \<R>)\<^sup>+" (is "?Ls = ?Rs")
proof
  show "?Ls \<subseteq> ?Rs"
    by (intro gmctxtex_onp_gtrancl_rel[OF assms]) (auto simp: gmctxt_p_inv_def)
next
  show "?Rs \<subseteq> ?Ls"
    by (intro gtrancl_rel[OF assms])
       (auto simp: compatible_p_def num_gholes_at_least1
          intro: subset_trans[OF inf_funas_gmctxt_subset2])
qed

lemma gmctxtex_funas_nroot_strict_gtrancl_rel:
  assumes "\<R> \<subseteq> \<T>\<^sub>G \<F> \<times> \<T>\<^sub>G \<F>"
  shows "gmctxtex_funas_nroot_strict \<F> (gtrancl_rel \<F> \<R>) = (gctxtex_funas_nroot \<F> \<R>)\<^sup>+"
 (is "?Ls = ?Rs")
proof
  show "?Ls \<subseteq> ?Rs"
    by (intro gmctxtex_onp_gtrancl_rel[OF assms])
       (auto simp: gmctxt_p_inv_def gmctxt_closing_def
        dest!: less_eq_gmctxt_Hole gctxt_of_gmctxt_hole_dest gctxt_compose_HoleE(1))
next
  show "?Rs \<subseteq> ?Ls"
    by (intro gtrancl_rel[OF assms])
       (auto simp: compatible_p_def num_gholes_at_least1
          elim!: comp_gmctxt.cases
          dest: gmctxt_of_gctxt_GMHole_Hole
          intro: subset_trans[OF inf_funas_gmctxt_subset2])
qed

lemma lift_root_step_sig':
  assumes "\<R> \<subseteq> \<T>\<^sub>G \<G> \<times> \<T>\<^sub>G \<H>" "\<F> \<subseteq> \<G>" "\<F> \<subseteq> \<H>"
  shows "lift_root_step \<F> W X \<R> \<subseteq> \<T>\<^sub>G \<G> \<times> \<T>\<^sub>G \<H>"
  using assms \<T>\<^sub>G_mono
  by (cases W; cases X) (auto simp add: Sigma_mono \<T>\<^sub>G_mono inf.coboundedI2)

lemmas lift_root_step_sig = lift_root_step_sig'[OF _ subset_refl subset_refl]

lemma lift_root_step_incr:
  "\<R> \<subseteq> \<S> \<Longrightarrow> lift_root_step \<F> W X \<R> \<subseteq> lift_root_step \<F> W X \<S>"
  by (cases W; cases X) (auto simp add: le_supI1 gctxtex_onp_rel_mono gmctxtex_onp_rel_mono)

lemma Restr_id_mono:
  "\<F> \<subseteq> \<G> \<Longrightarrow> Restr Id (\<T>\<^sub>G \<F>) \<subseteq> Restr Id (\<T>\<^sub>G \<G>)"
  by (meson Sigma_mono \<T>\<^sub>G_mono inf_mono subset_refl)

lemma lift_root_step_mono:
  "\<F> \<subseteq> \<G> \<Longrightarrow> lift_root_step \<F> W X \<R> \<subseteq> lift_root_step \<G> W X \<R>"
  by (cases W; cases X) (auto simp: Restr_id_mono intro: gmctxtex_onp_mono gctxtex_onp_mono,
   metis Restr_id_mono sup.coboundedI1 sup_commute)


lemma grstep_lift_root_step:
  "lift_root_step \<F> PAny ESingle (Restr (grrstep \<R>) (\<T>\<^sub>G \<F>)) = Restr (grstep \<R>) (\<T>\<^sub>G \<F>)"
  unfolding grstepD_grstep_conv grstepD_def grrstep_subst_cl_conv
  by auto

lemma prod_swap_id_on_refl [simp]:
  "Restr Id (\<T>\<^sub>G \<F>) \<subseteq> prod.swap ` (\<R> \<union> Restr Id (\<T>\<^sub>G \<F>))"
  by (auto intro: subsetI)

lemma swap_lift_root_step:
  "lift_root_step \<F> W X (prod.swap ` \<R>) = prod.swap ` lift_root_step \<F> W X \<R>"
  by (cases W; cases X) (auto simp add: image_mono swap_gmctxtex_onp swap_gctxtex_onp intro: subsetI)

lemma converse_lift_root_step:
  "(lift_root_step \<F> W X R)\<inverse> = lift_root_step \<F> W X (R\<inverse>)"
  by (cases W; cases X) (auto simp add: converse_gctxtex_onp converse_gmctxtex_onp intro: subsetI)

lemma lift_root_step_sig_transfer:
  assumes "p \<in> lift_root_step \<F> W X R" "snd ` R \<subseteq> \<T>\<^sub>G \<F>" "funas_gterm (fst p) \<subseteq> \<G>"
  shows "p \<in> lift_root_step \<G> W X R" using assms
proof -
  from assms have "p \<in> lift_root_step (\<F> \<inter> \<G>) W X R"
    by (cases p; cases W; cases X)
       (auto simp: gctxtex_onp_sign_trans_fst[of _ _ _ R \<G>] gctxtex_onp_sign_trans_snd[of _ _ _ R \<G>]
          gmctxtex_onp_sign_trans_fst gmctxtex_onp_sign_trans_snd simp flip: \<T>\<^sub>G_equivalent_def \<T>\<^sub>G_funas_gterm_conv
          intro: basic_trans_rules(30)[OF gctxtex_onp_sign_trans_fst[of _ _ _ R \<G>],
              where ?B = "gctxtex_onp P R" for P]
            basic_trans_rules(30)[OF gmctxtex_onp_sign_trans_fst[of _ _ _ R \<G>],
              where ?B = "gmctxtex_onp P R" for P])
   then show ?thesis
    by (meson inf.cobounded2 lift_root_step_mono subsetD)
qed


lemma lift_root_step_sig_transfer2:
  assumes "p \<in> lift_root_step \<F> W X R" "snd ` R \<subseteq> \<T>\<^sub>G \<G>" "funas_gterm (fst p) \<subseteq> \<G>"
  shows "p \<in> lift_root_step \<G> W X R"
proof -
  from assms have "p \<in> lift_root_step (\<F> \<inter> \<G>) W X R"
    by (cases p; cases W; cases X)
       (auto simp: gctxtex_onp_sign_trans_fst[of _ _ _ R \<G>] gctxtex_onp_sign_trans_snd[of _ _ _ R \<G>]
          gmctxtex_onp_sign_trans_fst gmctxtex_onp_sign_trans_snd simp flip: \<T>\<^sub>G_equivalent_def \<T>\<^sub>G_funas_gterm_conv
          intro: basic_trans_rules(30)[OF gctxtex_onp_sign_trans_fst[of _ _ _ R \<G>],
              where ?B = "gctxtex_onp P R" for P]
            basic_trans_rules(30)[OF gmctxtex_onp_sign_trans_fst[of _ _ _ R \<G>],
              where ?B = "gmctxtex_onp P R" for P])
   then show ?thesis
    by (meson inf.cobounded2 lift_root_step_mono subsetD)
qed

lemma lift_root_steps_sig_transfer:
  assumes "(s, t) \<in> (lift_root_step \<F> W X R)\<^sup>+" "snd ` R \<subseteq> \<T>\<^sub>G \<G>" "funas_gterm s \<subseteq> \<G>"
  shows "(s, t) \<in> (lift_root_step \<G> W X R)\<^sup>+"
  using assms(1,3)
proof (induct rule: converse_trancl_induct)
  case (base s)
  show ?case using lift_root_step_sig_transfer2[OF base(1) assms(2)] base(2) by (simp add: r_into_trancl)
next
  case (step s s')
  show ?case using lift_root_step_sig_transfer2[OF step(1) assms(2)] step(3,4)
      lift_root_step_sig'[of R UNIV \<G> \<G> W X, THEN subsetD, of "(s, s')"] assms(2)
    by (auto simp: \<T>\<^sub>G_funas_gterm_conv \<T>\<^sub>G_equivalent_def)
       (smt SigmaI UNIV_I image_subset_iff snd_conv subrelI trancl_into_trancl2)
qed

lemma lift_root_stepseq_sig_transfer:
  assumes "(s, t) \<in> (lift_root_step \<F> W X R)\<^sup>*" "snd ` R \<subseteq> \<T>\<^sub>G \<G>" "funas_gterm s \<subseteq> \<G>"
  shows "(s, t) \<in> (lift_root_step \<G> W X R)\<^sup>*"
  using assms by (auto simp flip: reflcl_trancl simp: lift_root_steps_sig_transfer)

lemmas lift_root_step_sig_transfer' = lift_root_step_sig_transfer[of "prod.swap p" \<F> W X "prod.swap ` R" \<G> for p \<F> W X \<G> R,
    unfolded swap_lift_root_step, OF imageI, THEN imageI [of _ _ prod.swap],
    unfolded image_comp comp_def fst_swap snd_swap swap_swap image_ident]

lemmas lift_root_steps_sig_transfer' = lift_root_steps_sig_transfer[of t s \<F> W X "prod.swap ` R" \<G> for t s \<F> W X \<G> R,
    THEN imageI [of _ _ prod.swap], unfolded swap_lift_root_step swap_trancl pair_in_swap_image
    image_comp comp_def snd_swap swap_swap swap_simp image_ident]

lemmas lift_root_stepseq_sig_transfer' = lift_root_stepseq_sig_transfer[of t s \<F> W X "prod.swap ` R" \<G> for t s \<F> W X \<G> R,
    THEN imageI [of _ _ prod.swap], unfolded swap_lift_root_step swap_rtrancl pair_in_swap_image
    image_comp comp_def snd_swap swap_swap swap_simp image_ident]

lemma lift_root_step_PRoot_ESingle [simp]:
  "lift_root_step \<F> PRoot ESingle \<R> = \<R>"
  by auto

lemma lift_root_step_PRoot_EStrictParallel [simp]:
  "lift_root_step \<F> PRoot EStrictParallel \<R> = \<R>"
  by auto

lemma lift_root_step_Parallel_conv:
  shows "lift_root_step \<F> W EParallel \<R> = lift_root_step \<F> W EStrictParallel \<R> \<union> Restr Id (\<T>\<^sub>G \<F>)"
  by (cases W) (auto simp: gmctxtcl_funas_dist gmctxtex_funas_nroot_dist)

lemma relax_pos_lift_root_step:
  "lift_root_step \<F> W X R \<subseteq> lift_root_step \<F> PAny X R"
  by (cases W; cases X) (auto simp: gctxtex_closure gmctxtex_closure)

lemma relax_pos_lift_root_steps:
  "(lift_root_step \<F> W X R)\<^sup>+ \<subseteq> (lift_root_step \<F> PAny X R)\<^sup>+"
  by (simp add: relax_pos_lift_root_step trancl_mono_set)

lemma relax_ext_lift_root_step:
  "lift_root_step \<F> W X R \<subseteq> lift_root_step \<F> W EParallel R"
  by (cases W; cases X) (auto simp: compatible_p_gctxtex_gmctxtex_subseteq)

lemma lift_root_step_StrictParallel_seq:
  assumes "R \<subseteq> \<T>\<^sub>G \<F> \<times> \<T>\<^sub>G \<F>"
  shows "lift_root_step \<F> PAny EStrictParallel R \<subseteq> (lift_root_step \<F> PAny ESingle R)\<^sup>+"
  using assms
  by (auto simp: gmctxt_p_inv_def intro!: gmctxtex_onp_gctxtex_onp_trancl)

lemma lift_root_step_Parallel_seq:
  assumes "R \<subseteq> \<T>\<^sub>G \<F> \<times> \<T>\<^sub>G \<F>"
  shows "lift_root_step \<F> PAny EParallel R \<subseteq> (lift_root_step \<F> PAny ESingle R)\<^sup>+ \<union> Restr Id (\<T>\<^sub>G \<F>)"
  unfolding lift_root_step_Parallel_conv using lift_root_step_StrictParallel_seq[OF assms]
  using Un_mono by blast

lemma lift_root_step_Single_to_Parallel:
  shows "lift_root_step \<F> PAny ESingle R \<subseteq> lift_root_step \<F> PAny EParallel R"
  by (simp add: compatible_p_gctxtex_gmctxtex_subseteq)

lemma trancl_partial_reflcl:
  "(X \<union> Restr Id Y)\<^sup>+ = X\<^sup>+ \<union> Restr Id Y"
proof (intro equalityI subrelI, goal_cases LR RL)
  case (LR a b) then show ?case by (induct) (auto dest: trancl_into_trancl)
qed (auto intro: trancl_mono)

lemma lift_root_step_Parallels_single:
  assumes "R \<subseteq> \<T>\<^sub>G \<F> \<times> \<T>\<^sub>G \<F>"
  shows "(lift_root_step \<F> PAny EParallel R)\<^sup>+ = (lift_root_step \<F> PAny ESingle R)\<^sup>+ \<union> Restr Id (\<T>\<^sub>G \<F>)"
  using trancl_mono_set[OF lift_root_step_Parallel_seq[OF assms]]
  using trancl_mono_set[OF lift_root_step_Single_to_Parallel, of \<F> R]
  by (auto simp: lift_root_step_Parallel_conv trancl_partial_reflcl)


lemma lift_root_Any_Single_eq:
  shows "lift_root_step \<F> PAny ESingle R = R \<union> lift_root_step \<F> PNonRoot ESingle R"
  by (auto simp: gctxtcl_funas_dist intro!: gctxtex_closure)

lemma lift_root_Any_EStrict_eq [simp]:
  shows "lift_root_step \<F> PAny EStrictParallel R = R \<union> lift_root_step \<F> PNonRoot EStrictParallel R"
  by (auto simp: gmctxtcl_funas_strict_dist)

lemma gar_rstep_lift_root_step:
  "lift_root_step \<F> PAny EParallel (Restr (grrstep \<R>) (\<T>\<^sub>G \<F>)) = Restr (gpar_rstep \<R>) (\<T>\<^sub>G \<F>)"
  unfolding grrstep_subst_cl_conv gpar_rstep_gpar_rstepD_conv
  unfolding gpar_rstepD_gpar_rstepD'_conv[symmetric]
  by (auto simp: gpar_rstepD_def)

lemma grrstep_lift_root_gnrrstep:
  "lift_root_step \<F> PNonRoot ESingle (Restr (grrstep \<R>) (\<T>\<^sub>G \<F>)) = Restr (gnrrstep \<R>) (\<T>\<^sub>G \<F>)"
  unfolding gnrrstepD_gnrrstep_conv grrstep_subst_cl_conv
  by (simp add: gnrrstepD_def)

(* Restoring Isabelle standard attributes to lemmas *)
declare subsetI [intro!] 
declare lift_root_step.simps[simp del]

lemma gpar_rstepD_grstepD_rtrancl_subseteq:
  assumes "\<R> \<subseteq> \<T>\<^sub>G \<F> \<times> \<T>\<^sub>G \<F>"
  shows "gpar_rstepD \<F> \<R> \<subseteq> (grstepD \<F> \<R>)\<^sup>*"
  using assms unfolding gpar_rstepD_def grstepD_def
  by (intro gmctxtex_onp_gctxtex_onp_rtrancl) (auto simp: \<T>\<^sub>G_equivalent_def gmctxt_p_inv_def)
end