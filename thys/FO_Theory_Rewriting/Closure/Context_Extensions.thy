theory Context_Extensions
  imports Regular_Tree_Relations.Ground_Ctxt
    Regular_Tree_Relations.Ground_Closure
    Ground_MCtxt
begin

section \<open>Multihole context and context closures over predicates\<close>

definition gctxtex_onp where
  "gctxtex_onp P \<R> = {(C\<langle>s\<rangle>\<^sub>G, C\<langle>t\<rangle>\<^sub>G) | C s t. P C \<and> (s, t) \<in> \<R>}"

definition gmctxtex_onp where
  "gmctxtex_onp P \<R> = {(fill_gholes C ss, fill_gholes C ts) | C ss ts.
    num_gholes C = length ss \<and> length ss = length ts \<and> P C \<and> (\<forall> i < length ts. (ss ! i , ts ! i) \<in> \<R>)}"

definition compatible_p where
  "compatible_p P Q \<equiv> (\<forall> C. P C \<longrightarrow> Q (gmctxt_of_gctxt C))"

subsection \<open>Elimination and introduction rules for the extensions\<close>

lemma gctxtex_onpE [elim]:
  assumes "(s, t) \<in> gctxtex_onp P \<R>"
  obtains C u v where "s = C\<langle>u\<rangle>\<^sub>G" "t = C\<langle>v\<rangle>\<^sub>G" "P C" "(u, v) \<in> \<R>"
  using assms unfolding gctxtex_onp_def by auto

lemma gctxtex_onp_neq_rootE [elim]:
  assumes "(GFun f ss, GFun g ts) \<in> gctxtex_onp P \<R>" and "f \<noteq> g"
  shows "(GFun f ss, GFun g ts) \<in> \<R>"
proof -
  obtain C u v where "GFun f ss = C\<langle>u\<rangle>\<^sub>G" "GFun g ts = C\<langle>v\<rangle>\<^sub>G" "(u, v) \<in> \<R>"
    using assms(1) by auto
  then show ?thesis using assms(2)
    by (cases C) auto
qed

lemma gctxtex_onp_neq_lengthE [elim]:
  assumes "(GFun f ss, GFun g ts) \<in> gctxtex_onp P \<R>" and "length ss \<noteq> length ts"
  shows "(GFun f ss, GFun g ts) \<in> \<R>"
proof -
  obtain C u v where "GFun f ss = C\<langle>u\<rangle>\<^sub>G" "GFun g ts = C\<langle>v\<rangle>\<^sub>G" "(u, v) \<in> \<R>"
    using assms(1) by auto
  then show ?thesis using assms(2)
    by (cases C) auto
qed

lemma gmctxtex_onpE [elim]:
  assumes "(s, t) \<in> gmctxtex_onp P \<R>"
  obtains C us vs where "s = fill_gholes C us" "t = fill_gholes C vs" "num_gholes C = length us"
    "length us = length vs" "P C" "\<forall> i < length vs. (us ! i, vs ! i) \<in> \<R>"
  using assms unfolding gmctxtex_onp_def by auto

lemma gmctxtex_onpE2 [elim]:
  assumes "(s, t) \<in> gmctxtex_onp P \<R>"
  obtains C us vs where "s =\<^sub>G\<^sub>f (C, us)" "t =\<^sub>G\<^sub>f (C, vs)"
    "P C" "\<forall> i < length vs. (us ! i, vs ! i) \<in> \<R>"
  using gmctxtex_onpE[OF assms] by (metis eq_gfill.intros)

lemma gmctxtex_onp_neq_rootE [elim]:
  assumes "(GFun f ss, GFun g ts) \<in> gmctxtex_onp P \<R>" and "f \<noteq> g"
  shows "(GFun f ss, GFun g ts) \<in> \<R>"
proof -
  obtain C us vs where "GFun f ss = fill_gholes C us" "GFun g ts = fill_gholes C vs"
    "num_gholes C = length us" "length us = length vs" "\<forall> i < length vs. (us ! i, vs ! i) \<in> \<R>"
    using assms(1) by auto
  then show ?thesis using assms(2)
    by (cases C; cases us; cases vs) auto
qed

lemma gmctxtex_onp_neq_lengthE [elim]:
  assumes "(GFun f ss, GFun g ts) \<in> gmctxtex_onp P \<R>" and "length ss \<noteq> length ts"
  shows "(GFun f ss, GFun g ts) \<in> \<R>"
proof -
  obtain C us vs where "GFun f ss = fill_gholes C us" "GFun g ts = fill_gholes C vs"
    "num_gholes C = length us" "length us = length vs" "\<forall> i < length vs. (us ! i, vs ! i) \<in> \<R>"
    using assms(1) by auto
  then show ?thesis using assms(2)
    by (cases C; cases us; cases vs) auto
qed

lemma gmctxtex_onp_listE:
  assumes "\<forall> i < length ts. (ss ! i, ts ! i) \<in> gmctxtex_onp Q \<R>" "length ss = length ts"
  obtains Ds sss tss where "length ts = length Ds" "length Ds = length sss" "length sss = length tss"
    "\<forall> i < length tss. length (sss ! i) = length (tss ! i)" "\<forall> D \<in> set Ds. Q D"
    "\<forall> i < length tss. ss ! i =\<^sub>G\<^sub>f (Ds ! i, sss ! i)" "\<forall> i < length tss. ts ! i =\<^sub>G\<^sub>f (Ds ! i, tss ! i)"
    "\<forall> i < length (concat tss). (concat sss ! i, concat tss ! i) \<in> \<R>"
proof -
 let ?P = "\<lambda> W i. ss ! i =\<^sub>G\<^sub>f (fst W, fst (snd W)) \<and> ts ! i =\<^sub>G\<^sub>f (fst W, snd (snd W)) \<and>
    Q (fst W) \<and> (\<forall> i < length (snd (snd W)). (fst (snd W) ! i, snd (snd W) ! i) \<in> \<R>)"
  have "\<forall> i < length ts. \<exists> x. ?P x i" using assms gmctxtex_onpE2[of "ss ! i" "ts ! i" Q \<R> for i]
    by auto metis
  from Ex_list_of_length_P[OF this] obtain W where
    P: "length W = length ts" "\<forall> i < length ts. ?P (W ! i) i" by blast
  define Ds sss tss where "Ds \<equiv> map fst W" and "sss \<equiv> map (fst \<circ> snd) W" and "tss \<equiv> map (snd \<circ> snd) W"
  from P have len: "length ts = length Ds" "length Ds = length sss" "length sss = length tss" and
    pred: "\<forall> D \<in> set Ds. Q D" and
    split: "\<forall> i < length Ds. ss ! i =\<^sub>G\<^sub>f (Ds ! i, sss ! i) \<and> ts ! i =\<^sub>G\<^sub>f (Ds ! i, tss ! i)"and
    rec: "\<forall>i < length Ds. \<forall> j < length (tss ! i). (sss ! i ! j, tss ! i ! j) \<in> \<R>"
    using assms(2) by (auto simp: Ds_def sss_def tss_def dest!: in_set_idx)
  from len split have inn: "\<forall> i < length tss. length (sss ! i) = length (tss ! i)"
    by auto (metis eqgfE(2))
  from inn len rec have "\<forall> i < length (concat tss). (concat sss ! i, concat tss ! i) \<in> \<R>"
    by (intro concat_nth_nthI) auto
  then show "(\<And>Ds sss tss. length ts = length Ds \<Longrightarrow> length Ds = length sss \<Longrightarrow> length sss = length tss \<Longrightarrow>
        \<forall>i<length tss. length (sss ! i) = length (tss ! i) \<Longrightarrow> \<forall>D\<in>set Ds. Q D \<Longrightarrow>
        \<forall>i<length tss. ss ! i =\<^sub>G\<^sub>f (Ds ! i, sss ! i) \<Longrightarrow> \<forall>i<length tss. ts ! i =\<^sub>G\<^sub>f (Ds ! i, tss ! i) \<Longrightarrow>
        \<forall>i<length (concat tss). (concat sss ! i, concat tss ! i) \<in> \<R> \<Longrightarrow> thesis) \<Longrightarrow> thesis"
    using pred split inn len by auto
qed

lemma gmctxtex_onp_doubleE [elim]:
  assumes "(s, t) \<in> gmctxtex_onp P (gmctxtex_onp Q \<R>)"
  obtains C Ds ss ts us vs where "s =\<^sub>G\<^sub>f (C, ss)" "t =\<^sub>G\<^sub>f (C, ts)" "P C" "\<forall> D \<in> set Ds. Q D"
    "num_gholes C = length Ds" "length Ds = length ss" "length ss = length ts" "length ts = length us" "length us = length vs"
    "\<forall> i < length Ds. ss ! i =\<^sub>G\<^sub>f (Ds ! i, us ! i) \<and> ts ! i =\<^sub>G\<^sub>f (Ds ! i, vs ! i)"
    "\<forall> i < length Ds. \<forall> j < length (vs ! i). (us ! i ! j, vs ! i ! j) \<in> \<R>"
proof -
  from gmctxtex_onpE2[OF assms] obtain C ss ts where
    split: "s =\<^sub>G\<^sub>f (C, ss)" "t =\<^sub>G\<^sub>f (C, ts)" and
    len: "num_gholes C = length ss" "length ss = length ts" and
    pred: "P C" and rec: "\<forall> i < length ts. (ss ! i, ts ! i) \<in> gmctxtex_onp Q \<R>"
      by (metis eqgfE(2))
  let ?P = "\<lambda> W i. ss ! i =\<^sub>G\<^sub>f (fst W, fst (snd W)) \<and> ts ! i =\<^sub>G\<^sub>f (fst W, snd (snd W)) \<and>
    Q (fst W) \<and> (\<forall> i < length (snd (snd W)). (fst (snd W) ! i, snd (snd W) ! i) \<in> \<R>)"
  have "\<forall> i < length ts. \<exists> x. ?P x i" using rec gmctxtex_onpE2[of "ss ! i" "ts ! i" Q \<R> for i]
    by auto metis
  from Ex_list_of_length_P[OF this] obtain W where
    P: "length W = length ts" "\<forall> i < length ts. ?P (W ! i) i" by blast
  define Ds us vs where "Ds \<equiv> map fst W" and "us \<equiv> map (fst \<circ> snd) W" and "vs \<equiv> map (snd \<circ> snd) W"
  from P have len': "length Ds = length ss" "length ss = length ts" "length ts = length us" "length us = length vs" and
    pred': "\<forall> D \<in> set Ds. Q D" and
    split': "\<forall> i < length Ds. ss ! i =\<^sub>G\<^sub>f (Ds ! i, us ! i) \<and> ts ! i =\<^sub>G\<^sub>f (Ds ! i, vs ! i)"and
    rec': "\<forall>i < length Ds. \<forall> j < length (vs ! i). (us ! i ! j, vs ! i ! j) \<in> \<R>"
  using len by (auto simp: Ds_def us_def vs_def dest!: in_set_idx)
  from len' len have "num_gholes C = length Ds" by simp
  from this split pred pred' len' split' rec' len
  show "(\<And>C ss ts Ds us vs. s =\<^sub>G\<^sub>f (C, ss) \<Longrightarrow> t =\<^sub>G\<^sub>f (C, ts) \<Longrightarrow> P C \<Longrightarrow>
    \<forall>D\<in>set Ds. Q D \<Longrightarrow> num_gholes C = length Ds \<Longrightarrow> length Ds = length ss \<Longrightarrow> length ss = length ts \<Longrightarrow>
    length ts = length us \<Longrightarrow> length us = length vs \<Longrightarrow>
    \<forall>i<length Ds. ss ! i =\<^sub>G\<^sub>f (Ds ! i, us ! i) \<and> ts ! i =\<^sub>G\<^sub>f (Ds ! i, vs ! i) \<Longrightarrow>
    \<forall>i<length Ds. \<forall>j<length (vs ! i). (us ! i ! j, vs ! i ! j) \<in> \<R> \<Longrightarrow> thesis) \<Longrightarrow> thesis"
      by blast
qed

lemma gctxtex_onpI [intro]:
  assumes "P C" and "(s, t) \<in> \<R>"
  shows "(C\<langle>s\<rangle>\<^sub>G, C\<langle>t\<rangle>\<^sub>G) \<in> gctxtex_onp P \<R>"
  using assms by (auto simp: gctxtex_onp_def)

lemma gmctxtex_onpI [intro]:
  assumes "P C" and "num_gholes C = length us" and "length us = length vs" 
    and "\<forall> i < length vs. (us ! i, vs ! i) \<in> \<R>"
  shows "(fill_gholes C us, fill_gholes C vs) \<in> gmctxtex_onp P \<R>"
  using assms unfolding gmctxtex_onp_def
  by force

lemma gmctxtex_onp_arg_monoI:
  assumes "P GMHole"
  shows "\<R> \<subseteq> gmctxtex_onp P \<R>" using assms
proof (intro subsetI)
  fix s assume mem: "s \<in> \<R>"
  have *: "(fill_gholes GMHole [fst s], fill_gholes GMHole [snd s]) = s" by auto
  have "(fill_gholes GMHole [fst s], fill_gholes GMHole [snd s]) \<in> gmctxtex_onp P \<R>"
    by (intro gmctxtex_onpI) (auto simp: assms mem)
  then show "s \<in> gmctxtex_onp P \<R>" unfolding * .
qed

lemma gmctxtex_onpI2 [intro]:
  assumes "P C" and "s =\<^sub>G\<^sub>f (C, ss)" "t =\<^sub>G\<^sub>f (C, ts)"
    and "\<forall> i < length ts. (ss ! i, ts ! i) \<in> \<R>"
  shows "(s, t) \<in> gmctxtex_onp P \<R>"
  using eqgfE[OF assms(2)] eqgfE[OF assms(3)]
  using gmctxtex_onpI[of P, OF assms(1) _ _ assms(4)]
  by (simp add: \<open>num_gholes C = length ss\<close>)

lemma gctxtex_onp_hold_cond [simp]:
  "(s, t) \<in> gctxtex_onp P \<R> \<Longrightarrow> groot s \<noteq> groot t \<Longrightarrow> P \<box>\<^sub>G"
  "(s, t) \<in> gctxtex_onp P \<R> \<Longrightarrow> length (gargs s) \<noteq> length (gargs t) \<Longrightarrow> P \<box>\<^sub>G"
  by (auto elim!: gctxtex_onpE, case_tac C; auto)+

subsection \<open>Monotonicity rules for the extensions\<close>

lemma gctxtex_onp_rel_mono:
  "\<L> \<subseteq> \<R> \<Longrightarrow> gctxtex_onp P \<L> \<subseteq> gctxtex_onp P \<R>"
  unfolding gctxtex_onp_def by auto

lemma gmctxtex_onp_rel_mono:
  "\<L> \<subseteq> \<R> \<Longrightarrow> gmctxtex_onp P \<L> \<subseteq> gmctxtex_onp P \<R>"
  unfolding gmctxtex_onp_def
  by auto (metis subsetD)

lemma compatible_p_gctxtex_gmctxtex_subseteq [dest]:
  "compatible_p P Q \<Longrightarrow> gctxtex_onp P \<R> \<subseteq> gmctxtex_onp Q \<R>"
  unfolding compatible_p_def
  by (auto simp: apply_gctxt_fill_gholes gmctxtex_onpI)

lemma compatible_p_mono1:
  "P \<le> R \<Longrightarrow> compatible_p R Q \<Longrightarrow> compatible_p P Q"
  unfolding compatible_p_def by auto

lemma compatible_p_mono2:
  "Q \<le> R \<Longrightarrow> compatible_p P Q \<Longrightarrow> compatible_p P R"
  unfolding compatible_p_def by auto

lemma gctxtex_onp_mono [intro]:
  "P \<le> Q \<Longrightarrow> gctxtex_onp P \<R> \<subseteq> gctxtex_onp Q \<R>"
  by auto

lemma gctxtex_onp_mem:
  "P \<le> Q \<Longrightarrow> (s, t) \<in> gctxtex_onp P \<R> \<Longrightarrow> (s, t) \<in> gctxtex_onp Q \<R>"
  by auto

lemma gmctxtex_onp_mono [intro]:
  "P \<le> Q \<Longrightarrow> gmctxtex_onp P \<R> \<subseteq> gmctxtex_onp Q \<R>"
  by (auto elim!: gmctxtex_onpE)

lemma gmctxtex_onp_mem:
  "P \<le> Q \<Longrightarrow> (s, t) \<in> gmctxtex_onp P \<R> \<Longrightarrow> (s, t) \<in> gmctxtex_onp Q \<R>"
  by (auto dest!: gmctxtex_onp_mono)

lemma gctxtex_eqI [intro]:
  "P = Q \<Longrightarrow> \<R> = \<L> \<Longrightarrow> gctxtex_onp P \<R> = gctxtex_onp Q \<L>"
  by auto

lemma gmctxtex_eqI [intro]:
  "P = Q \<Longrightarrow> \<R> = \<L> \<Longrightarrow> gmctxtex_onp P \<R> = gmctxtex_onp Q \<L>"
  by auto

subsection \<open>Relation swap and converse\<close>

lemma swap_gctxtex_onp:
  "gctxtex_onp P (prod.swap ` \<R>) = prod.swap ` gctxtex_onp P \<R>"
  by (auto simp: gctxtex_onp_def image_def) force+

lemma swap_gmctxtex_onp:
  "gmctxtex_onp P (prod.swap ` \<R>) = prod.swap ` gmctxtex_onp P \<R>"
  by (auto simp: gmctxtex_onp_def image_def) force+

lemma converse_gctxtex_onp:
  "(gctxtex_onp P \<R>)\<inverse> = gctxtex_onp P (\<R>\<inverse>)"
  by (auto simp: gctxtex_onp_def)

lemma converse_gmctxtex_onp:
  "(gmctxtex_onp P \<R>)\<inverse> = gmctxtex_onp P (\<R>\<inverse>)"
  by (auto simp: gmctxtex_onp_def) force+

subsection \<open>Subset equivalence for context extensions over predicates\<close>

lemma gctxtex_onp_closure_predI:
  assumes "\<And> C s t. P C \<Longrightarrow> (s, t) \<in> \<R> \<Longrightarrow> (C\<langle>s\<rangle>\<^sub>G, C\<langle>t\<rangle>\<^sub>G) \<in> \<R>"
  shows "gctxtex_onp P \<R> \<subseteq> \<R>"
  using assms by auto

lemma gmctxtex_onp_closure_predI:
  assumes "\<And> C ss ts. P C \<Longrightarrow> num_gholes C = length ss \<Longrightarrow> length ss = length ts \<Longrightarrow>
    (\<forall> i < length ts. (ss ! i, ts ! i) \<in> \<R>) \<Longrightarrow> (fill_gholes C ss, fill_gholes C ts) \<in> \<R>"
  shows "gmctxtex_onp P \<R> \<subseteq> \<R>"
  using assms by auto

lemma gctxtex_onp_closure_predE:
  assumes "gctxtex_onp P \<R> \<subseteq> \<R>"
  shows  "\<And> C s t. P C \<Longrightarrow> (s, t) \<in> \<R> \<Longrightarrow> (C\<langle>s\<rangle>\<^sub>G, C\<langle>t\<rangle>\<^sub>G) \<in> \<R>"
  using assms by auto

lemma gctxtex_closure [intro]:
  "P \<box>\<^sub>G \<Longrightarrow> \<R> \<subseteq> gctxtex_onp P \<R>"
  by (auto simp: gctxtex_onp_def) force

lemma gmctxtex_closure [intro]:
  assumes "P GMHole"
  shows "\<R> \<subseteq> (gmctxtex_onp P \<R>)"
proof -
  {fix s t assume "(s, t) \<in> \<R>" then have "(s, t) \<in> gmctxtex_onp P \<R>" 
      using gmctxtex_onpI[of P GMHole "[s]" "[t]"] assms by auto}
  then show ?thesis by auto
qed

lemma gctxtex_pred_cmp_subseteq:
  assumes "\<And> C D. P C \<Longrightarrow> Q D \<Longrightarrow> Q (C \<circ>\<^sub>G\<^sub>c D)"
  shows "gctxtex_onp P (gctxtex_onp Q \<R>) \<subseteq> gctxtex_onp Q \<R>"
  using assms by (auto simp: gctxtex_onp_def) (metis ctxt_ctxt_compose)

lemma gctxtex_pred_cmp_subseteq2:
  assumes "\<And> C D. P C \<Longrightarrow> Q D \<Longrightarrow> P (C \<circ>\<^sub>G\<^sub>c D)"
  shows "gctxtex_onp P (gctxtex_onp Q \<R>) \<subseteq> gctxtex_onp P \<R>"
  using assms by (auto simp: gctxtex_onp_def) (metis ctxt_ctxt_compose)

lemma gmctxtex_pred_cmp_subseteq:
  assumes "\<And> C D. C \<le> D \<Longrightarrow> P C \<Longrightarrow> (\<forall> Ds \<in> set (sup_gmctxt_args C D). Q Ds) \<Longrightarrow> Q D"
  shows "gmctxtex_onp P (gmctxtex_onp Q \<R>) \<subseteq> gmctxtex_onp Q \<R>" (is "?Ls \<subseteq> ?Rs")
proof -
  {fix s t assume "(s, t) \<in> ?Ls"
    then obtain C Ds ss ts us vs where
      split: "s =\<^sub>G\<^sub>f (C, ss)" "t =\<^sub>G\<^sub>f (C, ts)" and
      len: "num_gholes C = length Ds" "length Ds = length ss" "length ss = length ts"
        "length ts = length us" "length us = length vs" and
      pred: "P C" "\<forall> D \<in> set Ds. Q D" and
      split': "\<forall> i < length Ds. ss ! i =\<^sub>G\<^sub>f (Ds ! i, us ! i) \<and> ts ! i =\<^sub>G\<^sub>f (Ds ! i, vs ! i)" and
      rec: " \<forall>i<length Ds. \<forall>j<length (vs ! i). (us ! i ! j, vs ! i ! j) \<in> \<R>"
      by auto
    from pred(2) assms[OF _ pred(1), of "fill_gholes_gmctxt C Ds"] len
    have P: "Q (fill_gholes_gmctxt C Ds)"
      by (simp add: fill_gholes_gmctxt_less_eq)
    have mem: "\<forall> i < length (concat vs). (concat us ! i, concat vs ! i) \<in> \<R>"
      using rec split' len
      by (intro concat_nth_nthI) (auto, metis eqgfE(2))
    have "(s, t) \<in> ?Rs" using split' split len
      by (intro gmctxtex_onpI2[of Q, OF P _ _ mem])
        (metis eqgfE(1) fill_gholes_gmctxt_sound)+}
  then show ?thesis by auto
qed

lemma gmctxtex_pred_cmp_subseteq2:
  assumes "\<And> C D. C \<le> D \<Longrightarrow> P C \<Longrightarrow> (\<forall> Ds \<in> set (sup_gmctxt_args C D). Q Ds) \<Longrightarrow> P D"
  shows "gmctxtex_onp P (gmctxtex_onp Q \<R>) \<subseteq> gmctxtex_onp P \<R>" (is "?Ls \<subseteq> ?Rs")
proof -
    {fix s t assume "(s, t) \<in> ?Ls"
    then obtain C Ds ss ts us vs where
      split: "s =\<^sub>G\<^sub>f (C, ss)" "t =\<^sub>G\<^sub>f (C, ts)" and
      len: "num_gholes C = length Ds" "length Ds = length ss" "length ss = length ts"
        "length ts = length us" "length us = length vs" and
      pred: "P C" "\<forall> D \<in> set Ds. Q D" and
      split': "\<forall> i < length Ds. ss ! i =\<^sub>G\<^sub>f (Ds ! i, us ! i) \<and> ts ! i =\<^sub>G\<^sub>f (Ds ! i, vs ! i)" and
      rec: " \<forall>i<length Ds. \<forall>j<length (vs ! i). (us ! i ! j, vs ! i ! j) \<in> \<R>"
      by auto
    from pred(2) assms[OF _ pred(1), of "fill_gholes_gmctxt C Ds"] len
    have P: "P (fill_gholes_gmctxt C Ds)"
      by (simp add: fill_gholes_gmctxt_less_eq)
    have mem: "\<forall> i < length (concat vs). (concat us ! i, concat vs ! i) \<in> \<R>" using rec split' len
      by (intro concat_nth_nthI) (auto, metis eqgfE(2))
    have "(s, t) \<in> ?Rs" using split' split len
      by (intro gmctxtex_onpI2[of P, OF P _ _ mem])
        (metis eqgfE(1) fill_gholes_gmctxt_sound)+}
  then show ?thesis by auto
qed

lemma gctxtex_onp_idem [simp]:
  assumes "P \<box>\<^sub>G" and "\<And> C D. P C \<Longrightarrow> Q D \<Longrightarrow> Q (C \<circ>\<^sub>G\<^sub>c D)"
  shows "gctxtex_onp P (gctxtex_onp Q \<R>) = gctxtex_onp Q \<R>" (is "?Ls = ?Rs")
  by (simp add: assms gctxtex_pred_cmp_subseteq gctxtex_closure subset_antisym)

lemma gctxtex_onp_idem2 [simp]:
  assumes "Q \<box>\<^sub>G" and "\<And> C D. P C \<Longrightarrow> Q D \<Longrightarrow> P (C \<circ>\<^sub>G\<^sub>c D)"
  shows "gctxtex_onp P (gctxtex_onp Q \<R>) = gctxtex_onp P \<R>" (is "?Ls = ?Rs")
  using gctxtex_pred_cmp_subseteq2[of P Q, OF assms(2)]
  using gctxtex_closure[of Q, OF assms(1)] in_mono
  by auto fastforce

lemma gmctxtex_onp_idem [simp]:
  assumes "P GMHole"
    and "\<And> C D. C \<le> D \<Longrightarrow> P C \<Longrightarrow> (\<forall> Ds \<in> set (sup_gmctxt_args C D). Q Ds) \<Longrightarrow> Q D"
  shows "gmctxtex_onp P (gmctxtex_onp Q \<R>) = gmctxtex_onp Q \<R>"
  using gmctxtex_pred_cmp_subseteq[of P Q \<R>] gmctxtex_closure[of P] assms
  by auto

subsection \<open>@{const gmctxtex_onp} subset equivalence @{const gctxtex_onp} transitive closure\<close>

text \<open>The following definition demands that if we arbitrarily fill a multihole context C with terms
  induced by signature F such that one hole remains then the predicate Q holds\<close>
definition "gmctxt_p_inv C \<F> Q \<equiv> (\<forall> D. gmctxt_closing C D \<longrightarrow> num_gholes D = 1 \<longrightarrow> funas_gmctxt D \<subseteq> \<F>
  \<longrightarrow> Q (gctxt_of_gmctxt D))"

lemma gmctxt_p_invE:
  "gmctxt_p_inv C \<F> Q \<Longrightarrow> C \<le> D \<Longrightarrow> ghole_poss D \<subseteq> ghole_poss C \<Longrightarrow> num_gholes D = 1 \<Longrightarrow>
    funas_gmctxt D \<subseteq> \<F> \<Longrightarrow> Q (gctxt_of_gmctxt D)"
  unfolding gmctxt_closing_def gmctxt_p_inv_def
  using less_eq_gmctxt_prime by blast

lemma gmctxt_closing_gmctxt_p_inv_comp:
  "gmctxt_closing C D \<Longrightarrow> gmctxt_p_inv C \<F> Q \<Longrightarrow> gmctxt_p_inv D \<F> Q"
  unfolding gmctxt_closing_def gmctxt_p_inv_def
  by auto (meson less_eq_gmctxt_prime order_trans)

lemma GMHole_gmctxt_p_inv_GHole [simp]:
  "gmctxt_p_inv GMHole \<F> Q \<Longrightarrow> Q \<box>\<^sub>G"
  by (auto dest: gmctxt_p_invE)
  

lemma gmctxtex_onp_gctxtex_onp_trancl:
  assumes sig: "\<And> C. P C \<Longrightarrow> 0 < num_gholes C \<and> funas_gmctxt C \<subseteq> \<F>" "\<R> \<subseteq> \<T>\<^sub>G \<F> \<times> \<T>\<^sub>G \<F>"
    and "\<And> C. P C \<Longrightarrow> gmctxt_p_inv C \<F> Q"
  shows "gmctxtex_onp P \<R> \<subseteq> (gctxtex_onp Q \<R>)\<^sup>+"
proof
  fix s t assume "(s, t) \<in> gmctxtex_onp P \<R>"
  then obtain C ss ts where
    split: "s = fill_gholes C ss" "t = fill_gholes C ts" and
    inv: "num_gholes C = length ss" "num_gholes C = length ts" and
    pred: "P C" and rec: "\<forall> i < length ts. (ss ! i, ts ! i) \<in> \<R>"
    by auto
  from pred have "0 < num_gholes C" "funas_gmctxt C \<subseteq> \<F>" using sig by auto
  from this inv assms(3)[OF pred] rec show "(s, t) \<in> (gctxtex_onp Q \<R>)\<^sup>+" unfolding split
  proof (induct "num_gholes C" arbitrary: C ss ts)
    case (Suc x) note IS = this then show ?case
    proof (cases C)
      case GMHole then show ?thesis
        using IS(2-) gctxtex_closure unfolding gmctxt_p_inv_def gmctxt_closing_def
        by (metis One_nat_def fill_gholes_GMHole gctxt_of_gmctxt.simps(1)
         gmctxt_order_bot.bot.extremum_unique less_eq_gmctxt_prime num_gholes.simps(1) r_into_trancl' subsetD subsetI)
    next
      case [simp]: (GMFun f Cs) note IS = IS[unfolded GMFun]
      let ?rep = "\<lambda> x. replicate (num_gholes (GMFun f Cs) - 1) x"
      let ?Ds1 = "?rep GMHole @ [gmctxt_of_gterm (last ss)]"
      let ?Ds2 = "map gmctxt_of_gterm (butlast ts) @ [GMHole]"
      let ?D1 = "fill_gholes_gmctxt (GMFun f Cs) ?Ds1"
      let ?D2 = "fill_gholes_gmctxt (GMFun f Cs) ?Ds2"
      have holes: "num_gholes (GMFun f Cs) = length ?Ds1" "num_gholes (GMFun f Cs) = length ?Ds2"
        using IS(2, 5, 6) by auto
      from holes(2) have [simp]: "num_gholes ?D2 = Suc 0"
        by (auto simp: num_gholes_fill_gholes_gmctxt simp del: fill_gholes_gmctxt.simps)
      from holes(1) have h: "x = num_gholes ?D1" using IS(2)
        by (auto simp: num_gholes_fill_gholes_gmctxt simp del: fill_gholes_gmctxt.simps)
      from holes have less: "GMFun f Cs \<le> ?D1" "GMFun f Cs \<le> ?D2"
        by (auto simp del: fill_gholes_gmctxt.simps intro: fill_gholes_gmctxt_less_eq)
      have "ghole_poss ?D1 \<subseteq> ghole_poss (GMFun f Cs)" using less(1) IS(2, 3)
        by (intro fill_gholes_gmctxt_ghole_poss_subseteq) (auto simp: nth_append)
      then have ext: "gmctxt_p_inv ?D1 \<F> Q" using less(1) IS(7)
        using gmctxt_closing_def gmctxt_closing_gmctxt_p_inv_comp less_eq_gmctxt_prime
        by blast
      have split_last_D1_ss: "fill_gholes C (butlast ts @ [last ss]) =\<^sub>G\<^sub>f (?D1, concat (map (\<lambda> x. [x]) (butlast ts) @ [[]]))"
        using holes(1) IS(2, 5, 6) unfolding GMFun
        by (intro fill_gholes_gmctxt_sound)
          (auto simp: nth_append eq_gfill.simps nth_butlast)
      have split_last_D2_ss: "fill_gholes C (butlast ts @ [last ss]) =\<^sub>G\<^sub>f (?D2, concat (?rep [] @ [[last ss]]))"
        using holes(2) IS(2, 5, 6) unfolding GMFun
        by (intro fill_gholes_gmctxt_sound) (auto simp: nth_append
           eq_gfill.simps nth_butlast last_conv_nth intro: last_nthI)
      have split_last_ts: "fill_gholes C ts =\<^sub>G\<^sub>f (?D2, concat (?rep [] @ [[last ts]]))"
        using holes(2) IS(2, 5, 6) unfolding GMFun
        by (intro fill_gholes_gmctxt_sound) (auto simp: nth_append
           eq_gfill.simps nth_butlast last_conv_nth intro: last_nthI)
      from eqgfE[OF split_last_ts] have last_eq: "fill_gholes C ts = fill_gholes ?D2 [last ts]"
        by (auto simp del: fill_gholes.simps fill_gholes_gmctxt.simps)
      have trans: "fill_gholes ?D1 (butlast ts) = fill_gholes ?D2 [last ss]"
        using eqgfE[OF split_last_D1_ss] eqgfE[OF split_last_D2_ss]
        by (auto simp del: fill_gholes.simps fill_gholes_gmctxt.simps)
      have "ghole_poss ?D2 \<subseteq> ghole_poss (GMFun f Cs)" using less(2) IS(2, 3, 6)
        by (intro fill_gholes_gmctxt_ghole_poss_subseteq) (auto simp: nth_append)
      then have "Q (gctxt_of_gmctxt ?D2)" using less(2)
        using subsetD[OF assms(2)] IS(2 -  6, 8) holes(2)
        by (intro gmctxt_p_invE[OF IS(7)])
          (auto simp del: fill_gholes_gmctxt.simps simp: num_gholes_fill_gholes_gmctxt
            in_set_conv_nth \<T>\<^sub>G_equivalent_def nth_butlast, metis less_SucI subsetD)
      from gctxtex_onpI[of Q _ "last ss" "last ts" \<R>, OF this] IS(2, 3, 5, 6, 8)
      have mem: "(fill_gholes ?D2 [last ss], fill_gholes ?D2 [last ts]) \<in> gctxtex_onp Q \<R>"
        using fill_gholes_apply_gctxt[of ?D2 "last ss"]
        using fill_gholes_apply_gctxt[of ?D2 "last ts"]
        by (auto simp del: gctxt_of_gmctxt.simps fill_gholes_gmctxt.simps fill_gholes.simps)
          (metis IS(2) IS(3) append_butlast_last_id diff_Suc_1 length_butlast
           length_greater_0_conv lessI nth_append_length)
      show ?thesis
      proof (cases x)
        case 0 then show ?thesis using mem IS(2 - 6) eqgfE[OF split_last_D2_ss] last_eq
          by (cases ss; cases ts)
          (auto simp del: gctxt_of_gmctxt.simps fill_gholes_gmctxt.simps fill_gholes.simps,
            metis IS(3, 5) length_0_conv less_not_refl)
      next
        case [simp]: (Suc nat)
        have "fill_gholes C ss =\<^sub>G\<^sub>f (?D1, concat (map (\<lambda> x. [x]) (butlast ss) @ [[]]))"
          using holes(1) IS(2, 5, 6) unfolding GMFun
          by (intro fill_gholes_gmctxt_sound)
            (auto simp del: fill_gholes_gmctxt.simps fill_gholes.simps
              simp: nth_append nth_butlast eq_gfill.intros last_nthI)
        from eqgfE[OF this] have l: "fill_gholes C ss = fill_gholes ?D1 (butlast ss)"
          by (auto simp del: fill_gholes_gmctxt.simps fill_gholes.simps)
        from IS(1)[OF h _ _ _ _ ext, of "butlast ss" "butlast ts"] IS(2-) holes(2) h assms(2)
        have "(fill_gholes ?D1 (butlast ss), fill_gholes ?D1 (butlast ts)) \<in> (gctxtex_onp Q \<R>)\<^sup>+"
          by (auto simp del: gctxt_of_gmctxt.simps fill_gholes_gmctxt.simps fill_gholes.simps
            simp: \<T>\<^sub>G_equivalent_def)
            (smt Suc.prems(1) Suc.prems(4) diff_Suc_1 last_conv_nth length_butlast
           length_greater_0_conv lessI less_SucI mem_Sigma_iff nth_butlast sig(2) subset_iff \<T>\<^sub>G_funas_gterm_conv)
        then have "(fill_gholes ?D1 (butlast ss), fill_gholes ?D2 [last ts]) \<in> (gctxtex_onp Q \<R>)\<^sup>+"
          using mem unfolding trans
          by (auto simp del: gctxt_of_gmctxt.simps fill_gholes_gmctxt.simps fill_gholes.simps)
        then show ?thesis unfolding last_eq l
          by (auto simp del:  fill_gholes_gmctxt.simps fill_gholes.simps)
      qed
    qed
  qed auto
qed

lemma gmctxtex_onp_gctxtex_onp_rtrancl:
  assumes sig: "\<And> C. P C \<Longrightarrow> funas_gmctxt C \<subseteq> \<F>" "\<R> \<subseteq> \<T>\<^sub>G \<F> \<times> \<T>\<^sub>G \<F>"
    and "\<And> C D. P C \<Longrightarrow> gmctxt_p_inv C \<F> Q"
  shows "gmctxtex_onp P \<R> \<subseteq> (gctxtex_onp Q \<R>)\<^sup>*"
proof
  fix s t assume "(s, t) \<in> gmctxtex_onp P \<R>"
  then obtain C ss ts where
    split: "s = fill_gholes C ss" "t = fill_gholes C ts" and
    inv: "num_gholes C = length ss" "num_gholes C = length ts" and
    pred: "P C" and rec: "\<forall> i < length ts. (ss ! i, ts ! i) \<in> \<R>"
    by auto
  then show "(s, t) \<in> (gctxtex_onp Q \<R>)\<^sup>*"
  proof (cases "num_gholes C")
    case 0 then show ?thesis using inv unfolding split
      by auto
  next
    case (Suc nat)
    from split inv pred rec assms
    have "(s, t) \<in> gmctxtex_onp (\<lambda> C. P C \<and> 0 < num_gholes C) \<R>" unfolding split
      by auto (metis (no_types, lifting) Suc gmctxtex_onpI zero_less_Suc)
    moreover have "gmctxtex_onp (\<lambda> C. P C \<and> 0 < num_gholes C) \<R> \<subseteq> (gctxtex_onp Q \<R>)\<^sup>+" using assms
      by (intro gmctxtex_onp_gctxtex_onp_trancl) auto
    ultimately show ?thesis by auto
  qed
qed

lemma rtrancl_gmctxtex_onp_rtrancl_gctxtex_onp_eq:
  assumes sig: "\<And> C. P C \<Longrightarrow> funas_gmctxt C \<subseteq> \<F>" "\<R> \<subseteq> \<T>\<^sub>G \<F> \<times> \<T>\<^sub>G \<F>"
    and "\<And> C D. P C \<Longrightarrow> gmctxt_p_inv C \<F> Q"
    and "compatible_p Q P"
  shows "(gmctxtex_onp P \<R>)\<^sup>* = (gctxtex_onp Q \<R>)\<^sup>*" (is "?Ls\<^sup>* = ?Rs\<^sup>*")
proof -
  from assms(4) have "?Rs \<subseteq> ?Ls" by auto
  then have "?Rs\<^sup>* \<subseteq> ?Ls\<^sup>*"
    by (simp add: rtrancl_mono) 
  moreover from gmctxtex_onp_gctxtex_onp_rtrancl[OF assms(1 - 3), of P]
  have "?Ls\<^sup>* \<subseteq> ?Rs\<^sup>*"
    by (simp add: rtrancl_subset_rtrancl) 
  ultimately show ?thesis by blast
qed

subsection \<open>Extensions to reflexive transitive closures\<close>

lemma gctxtex_onp_substep_trancl:
  assumes "gctxtex_onp P \<R> \<subseteq> \<R>"
  shows "gctxtex_onp P (\<R>\<^sup>+) \<subseteq> \<R>\<^sup>+"
proof -
  {fix s t assume "(s, t) \<in> gctxtex_onp P (\<R>\<^sup>+)"
    then obtain C u v where rec: "(u, v) \<in> \<R>\<^sup>+" "P C" and t: "s = C\<langle>u\<rangle>\<^sub>G" "t = C\<langle>v\<rangle>\<^sub>G"
      by auto
    from rec have "(s, t) \<in> \<R>\<^sup>+" unfolding t
    proof (induct)
      case (base y)
      then show ?case using assms by auto
    next
      case (step y z)
      from assms step(2, 4) have "(C\<langle>y\<rangle>\<^sub>G, C\<langle>z\<rangle>\<^sub>G) \<in> \<R>" by auto
      then show ?case using step by auto
    qed}
  then show ?thesis by auto
qed

lemma gctxtex_onp_substep_rtrancl:
  assumes "gctxtex_onp P \<R> \<subseteq> \<R>"
  shows "gctxtex_onp P (\<R>\<^sup>*) \<subseteq> \<R>\<^sup>*"
  using gctxtex_onp_substep_trancl[OF assms]
  by (smt gctxtex_onpE gctxtex_onpI rtrancl_eq_or_trancl subrelI subset_eq)

lemma gctxtex_onp_substep_trancl_diff_pred [intro]:
  assumes "\<And> C D. P C \<Longrightarrow> Q D \<Longrightarrow> Q (D \<circ>\<^sub>G\<^sub>c C)"
  shows "gctxtex_onp Q ((gctxtex_onp P \<R>)\<^sup>+) \<subseteq> (gctxtex_onp Q \<R>)\<^sup>+"
proof
  fix s t assume "(s, t) \<in> gctxtex_onp Q ((gctxtex_onp P \<R>)\<^sup>+)"
  from gctxtex_onpE[OF this] obtain C u v where
    *: "s = C\<langle>u\<rangle>\<^sub>G" "t = C\<langle>v\<rangle>\<^sub>G" and inv: "Q C" and mem: "(u, v) \<in> (gctxtex_onp P \<R>)\<^sup>+"
    by blast
  show "(s, t) \<in> (gctxtex_onp Q \<R>)\<^sup>+" using mem * inv
  proof (induct arbitrary: s t)
    case (base y)
    then show ?case using assms
      by (auto elim!: gctxtex_onpE intro!: r_into_trancl) (metis ctxt_ctxt_compose gctxtex_onpI) 
  next
    case (step y z)
    from step(2) have "(C\<langle>y\<rangle>\<^sub>G, C\<langle>z\<rangle>\<^sub>G) \<in> gctxtex_onp Q \<R>"
      using assms[OF _ step(6)]
        by (auto elim!: gctxtex_onpE) (metis ctxt_ctxt_compose gctxtex_onpI) 
    then show ?case using step(3)[of s "C\<langle>y\<rangle>\<^sub>G"] step(1, 2, 4-)
      by auto
  qed
qed

lemma gctxtcl_pres_trancl:
  assumes "(s, t) \<in> \<R>\<^sup>+" and "gctxtex_onp P \<R> \<subseteq> \<R>" and "P C"
  shows "(C\<langle>s\<rangle>\<^sub>G, C\<langle>t\<rangle>\<^sub>G) \<in> \<R>\<^sup>+"
  using gctxtex_onp_substep_trancl [OF assms(2)] assms(1, 3)
  by auto

lemma gctxtcl_pres_rtrancl:
  assumes "(s, t) \<in> \<R>\<^sup>*" and "gctxtex_onp P \<R> \<subseteq> \<R>" and "P C"
  shows "(C\<langle>s\<rangle>\<^sub>G, C\<langle>t\<rangle>\<^sub>G) \<in> \<R>\<^sup>*"
  using assms(1) gctxtcl_pres_trancl[OF _ assms(2, 3)]
  unfolding rtrancl_eq_or_trancl
  by (cases "s = t") auto


lemma gmctxtex_onp_substep_trancl: 
  assumes "gmctxtex_onp P \<R> \<subseteq> \<R>"
    and "Id_on (snd ` \<R>) \<subseteq> \<R>"
  shows "gmctxtex_onp P (\<R>\<^sup>+) \<subseteq> \<R>\<^sup>+"
proof -
  {fix s t assume "(s, t) \<in> gmctxtex_onp P (\<R>\<^sup>+)"
    from gmctxtex_onpE[OF this] obtain C us vs where
      *: "s = fill_gholes C us" "t = fill_gholes C vs" and
      len: "num_gholes C = length us" "length us = length vs" and
      inv: "P C" "\<forall> i < length vs. (us ! i, vs ! i) \<in> \<R>\<^sup>+" by auto
    have "(s, t) \<in> \<R>\<^sup>+" using len(2) inv(2) len(1) inv(1) unfolding *
    proof (induction rule: trancl_list_induct)
      case (base xs ys)
      then have "(fill_gholes C xs, fill_gholes C ys) \<in> \<R>" using assms(1)
        by blast
      then show ?case by auto
    next
      case (step xs ys i z)
      have sub: "set ys \<subseteq> snd ` \<R>" using step(1, 2)
        by (auto simp: image_def) (metis in_set_idx snd_conv tranclD2)
      from step have lft: "(fill_gholes C xs, fill_gholes C ys) \<in> \<R>\<^sup>+" by auto
      have "(fill_gholes C ys, fill_gholes C (ys[i := z])) \<in> gmctxtex_onp P \<R>"
        using step(3, 4) sub assms step(1, 6)
        by (intro gmctxtex_onpI[of P, OF step(7), of ys "ys[i := z]" \<R>])
          (simp add: Id_on_eqI nth_list_update subset_iff)+
      then have "(fill_gholes C ys, fill_gholes C (ys[i := z])) \<in> \<R>" using assms(1) by blast
      then show ?case using lft by auto
    qed}
  then show ?thesis by auto
qed

lemma gmctxtex_onp_substep_tranclE:
  assumes "trans \<R>" and "gmctxtex_onp Q \<R> O \<R> \<subseteq> \<R>" and "\<R> O gmctxtex_onp Q \<R> \<subseteq> \<R>"
    and "\<And> p C. P C \<Longrightarrow> p \<in> poss_gmctxt C \<Longrightarrow> Q (subgm_at C p)"
    and "\<And> C D. P C \<Longrightarrow> P D \<Longrightarrow> (C, D) \<in> comp_gmctxt \<Longrightarrow> P (C \<sqinter> D)"
  shows "(gmctxtex_onp P \<R>)\<^sup>+ = gmctxtex_onp P \<R>" (is "?Ls = ?Rs")
proof
  show "?Rs \<subseteq> ?Ls" using trancl_mono_set by fastforce
next
  {fix s t assume "(s, t) \<in> ?Ls" then have "(s, t) \<in> ?Rs"
    proof induction
      case (step t u)
      from step(3) obtain C us vs where
        *: "s = fill_gholes C us" "t = fill_gholes C vs" and
        l: "num_gholes C = length us" "length us = length vs" and
        inv: "P C" "\<forall>i<length vs. (us ! i, vs ! i) \<in> \<R>"
        by auto
      from step(2) obtain D xs ys where
        **: "t = fill_gholes D xs" "u = fill_gholes D ys" and
        l': "num_gholes D = length xs" "length xs = length ys" and
        inv': "P D" "\<forall>i<length ys. (xs ! i, ys ! i) \<in> \<R>"
        by auto
      let ?C' = "C \<sqinter> D"
      let ?sss = "unfill_gholes ?C' s" let ?uss = "unfill_gholes ?C' u"
      have less: "?C' \<le> gmctxt_of_gterm s" "?C' \<le> gmctxt_of_gterm u"
        using eq_gfill.intros eqgf_less_eq inf.coboundedI1 inf.coboundedI2 l(1) l'(1)
        unfolding * ** unfolding l'(2)
        by metis+
      from *(2) **(1) have comp: "(C, D) \<in> comp_gmctxt" using l l'
        using eqgf_comp_gmctxt by fastforce
      then have P: "P ?C'" using inv(1) inv'(1) assms(5) by blast
      moreover have l'': "num_gholes ?C' = length ?sss" "length ?sss = length ?uss"
        using less by auto
      moreover have fill: "fill_gholes ?C' ?sss = s" "fill_gholes ?C' ?uss = u"
        using less by (simp add: fill_unfill_gholes)+
      moreover have "\<forall> i < length ?uss. (?sss ! i, ?uss ! i) \<in> \<R>"
      proof (rule, rule)
        fix i assume i: "i < length (unfill_gholes ?C' u)"
        then obtain p where pos: "p \<in> ghole_poss ?C'"
          "unfill_gholes ?C' s ! i = gsubt_at (fill_gholes ?C' ?sss) p"
          "unfill_gholes ?C' u ! i = gsubt_at (fill_gholes ?C' ?uss) p"
          using fill l'' fill_gholes_ghole_poss
          by (metis eq_gfill.intros ghole_poss_ghole_poss_list_conv length_ghole_poss_list_num_gholes nth_mem)
        from comp_gmctxt_inf_ghole_poss_cases[OF comp pos(1)]
        consider (a) "p \<in> ghole_poss C \<and> p \<in> ghole_poss D" |
                 (b) "p \<in> ghole_poss C \<and> p \<in> poss_gmctxt D" |
                 (c) "p \<in> ghole_poss D \<and> p \<in> poss_gmctxt C" by blast
        then show "(unfill_gholes ?C' s ! i, unfill_gholes ?C' u ! i) \<in> \<R>" unfolding pos fill
        proof cases
          case a
          then show "(gsubt_at s p, gsubt_at u p) \<in> \<R>"
            using assms(1) *(2) l l' inv(2) inv'(2) unfolding * **
            using ghole_poss_nth_subt_at
            by (metis "*"(2) "**"(1) eq_gfill.intros trancl_id trancl_into_trancl2)
        next
          case b
          then have sp: "gsubt_at t p =\<^sub>G\<^sub>f (subgm_at D p, gmctxt_subtgm_at_fill_args p D xs)"
            "gsubt_at u p =\<^sub>G\<^sub>f (subgm_at D p, gmctxt_subtgm_at_fill_args p D ys)"
            using poss_gmctxt_fill_gholes_split[of _ D _ p] ** l'
            by force+
          have "(gsubt_at t p, gsubt_at u p) \<in> gmctxtex_onp Q \<R>" using inv'(2)
            using assms(4)[OF inv'(1) conjunct2[OF b]] eqgfE[OF sp(1)] eqgfE[OF sp(2)]
            by (auto simp: gmctxt_subtgm_at_fill_args_def intro!: gmctxtex_onpI)
          moreover have "(gsubt_at s p, gsubt_at t p) \<in> \<R>"
            using * l inv(2)
            using ghole_poss_nth_subt_at[OF _ conjunct1[OF b]]
            by auto (metis eq_gfill.intros)
          ultimately show "(gsubt_at s p, gsubt_at u p) \<in> \<R>"
            using assms(3) by auto
        next
         case c
         then have sp: "gsubt_at s p =\<^sub>G\<^sub>f (subgm_at C p, gmctxt_subtgm_at_fill_args p C us)"
            "gsubt_at t p =\<^sub>G\<^sub>f (subgm_at C p, gmctxt_subtgm_at_fill_args p C vs)"
            using poss_gmctxt_fill_gholes_split[of _ C _ p] * l
            by force+
          have "(gsubt_at s p, gsubt_at t p) \<in> gmctxtex_onp Q \<R>" using inv(2)
            using assms(4)[OF inv(1) conjunct2[OF c]] eqgfE[OF sp(1)] eqgfE[OF sp(2)]
            by (auto simp: gmctxt_subtgm_at_fill_args_def intro!: gmctxtex_onpI)
          moreover have "(gsubt_at t p, gsubt_at u p) \<in> \<R>"
            using ** l' inv'(2)
            using ghole_poss_nth_subt_at[OF _ conjunct1[OF c]]
            by auto (metis eq_gfill.intros)
          ultimately show "(gsubt_at s p, gsubt_at u p) \<in> \<R>"
            using assms(2) by auto
        qed
      qed
      ultimately show ?case by (metis gmctxtex_onpI)
    qed simp}
  then show "?Ls \<subseteq> ?Rs" by auto
qed

subsection \<open>Restr to set, union and predicate distribution\<close>

lemma Restr_gctxtex_onp_dist [simp]:
  "Restr (gctxtex_onp P \<R>) (\<T>\<^sub>G \<F>) =
    gctxtex_onp (\<lambda> C. funas_gctxt C \<subseteq> \<F> \<and> P C) (Restr \<R> (\<T>\<^sub>G \<F>))"
  by (auto simp: gctxtex_onp_def \<T>\<^sub>G_equivalent_def) blast

lemma Restr_gmctxtex_onp_dist [simp]:
  "Restr (gmctxtex_onp P \<R>) (\<T>\<^sub>G \<F>) =
     gmctxtex_onp  (\<lambda> C. funas_gmctxt C \<subseteq> \<F> \<and> P C) (Restr \<R> (\<T>\<^sub>G \<F>))"
  by (auto elim!: gmctxtex_onpE simp: \<T>\<^sub>G_equivalent_def SUP_le_iff gmctxtex_onpI)
    (metis in_set_idx subsetD)+


lemma Restr_id_subset_gmctxtex_onp [intro]:
  assumes "\<And> C. num_gholes C = 0 \<and> funas_gmctxt C \<subseteq> \<F> \<Longrightarrow> P C"
  shows "Restr Id (\<T>\<^sub>G \<F>) \<subseteq> gmctxtex_onp P \<R>"
proof
  fix s t assume "(s, t) \<in> Restr Id (\<T>\<^sub>G \<F>)"
  then show "(s, t) \<in> gmctxtex_onp P \<R>" using assms[of "gmctxt_of_gterm t"]
    using gmctxtex_onpI[of P "gmctxt_of_gterm t" "[]" "[]" \<R>]
    by (auto simp: \<T>\<^sub>G_equivalent_def)
qed

lemma Restr_id_subset_gmctxtex_onp2 [intro]:
  assumes "\<And> f n. (f, n) \<in> \<F> \<Longrightarrow> P (GMFun f (replicate n GMHole))"
   and "\<And> C Ds. num_gholes C = length Ds \<Longrightarrow> P C \<Longrightarrow> \<forall> D \<in> set Ds. P D \<Longrightarrow> P (fill_gholes_gmctxt C Ds)"
 shows "Restr Id (\<T>\<^sub>G \<F>) \<subseteq> gmctxtex_onp P \<R>"
proof
  fix s t assume "(s, t) \<in> Restr Id (\<T>\<^sub>G \<F>)"
  then have *: "s = t" "t \<in> \<T>\<^sub>G \<F>" by auto
  have "P (gmctxt_of_gterm t)" using *(2)
  proof (induct)
    case (const a)
    show ?case using assms(1)[OF const] by auto
  next
    case (ind f n ss)
    let ?C = "GMFun f (replicate (length ss) GMHole)"
    have "P (fill_gholes_gmctxt ?C (map gmctxt_of_gterm ss))"
      using assms(1)[OF ind(1)] ind
      by (intro assms(2)) (auto simp: in_set_conv_nth)
    then show ?case
      by (metis fill_gholes_gmctxt_GMFun_replicate_length gmctxt_of_gterm.simps length_map) 
  qed
  from gmctxtex_onpI[of P, OF this] show "(s, t) \<in> gmctxtex_onp P \<R>" unfolding *
    by auto
qed


lemma gctxtex_onp_union [simp]:
  "gctxtex_onp P (\<R> \<union> \<L>) = gctxtex_onp P \<R> \<union> gctxtex_onp P \<L>"
  by auto

lemma gctxtex_onp_pred_dist:
  assumes "\<And> C. P C \<longleftrightarrow> Q C \<or> R C"
  shows "gctxtex_onp P \<R> = gctxtex_onp Q \<R> \<union> gctxtex_onp R \<R>"
  using assms by auto fastforce

lemma gmctxtex_onp_pred_dist:
  assumes "\<And> C. P C \<longleftrightarrow> Q C \<or> R C"
  shows "gmctxtex_onp P \<R> = gmctxtex_onp Q \<R> \<union> gmctxtex_onp R \<R>"
  using assms by (auto elim!: gmctxtex_onpE)

lemma trivial_gctxtex_onp [simp]: "gctxtex_onp (\<lambda> C. C = \<box>\<^sub>G) \<R> = \<R>"
  using gctxtex_closure by force

lemma trivial_gmctxtex_onp [simp]: "gmctxtex_onp (\<lambda> C. C = GMHole) \<R> = \<R>"
proof
  show "gmctxtex_onp (\<lambda>C. C = GMHole) \<R> \<subseteq> \<R>"
    by (auto elim!: gmctxtex_onpE) force
next
  show "\<R> \<subseteq> gmctxtex_onp (\<lambda>C. C = GMHole) \<R>"
    by (intro gmctxtex_closure) auto
qed

subsection \<open>Distribution of context closures over relation composition\<close>

lemma gctxtex_onp_relcomp_inner:
  "gctxtex_onp P (\<R> O \<L>) \<subseteq> gctxtex_onp P \<R> O gctxtex_onp P \<L>"
  by auto

lemma gmctxtex_onp_relcomp_inner:
  "gmctxtex_onp P (\<R> O \<L>) \<subseteq> gmctxtex_onp P \<R> O gmctxtex_onp P \<L>"
proof
  fix s t
  assume "(s, t) \<in> gmctxtex_onp P (\<R> O \<L>)"
  from gmctxtex_onpE[OF this] obtain C us vs where
    *: "s = fill_gholes C us" "t = fill_gholes C vs" and
    len: "num_gholes C = length us" "length us = length vs" and
    inv: "P C" "\<forall> i < length vs. (us ! i, vs ! i) \<in> \<R> O \<L>" by blast
  obtain zs where l: "length vs = length zs" and
    rel: "\<forall> i < length zs. (us ! i, zs ! i) \<in> \<R>" "\<forall> i < length zs. (zs ! i, vs ! i) \<in> \<L>"
    using len(2) inv(2) Ex_list_of_length_P[of _ "\<lambda> y i. (us ! i, y) \<in> \<R> \<and> (y, vs ! i) \<in> \<L>"]
    by (auto simp: relcomp_unfold) metis
  from len l rel inv have "(s, fill_gholes C zs) \<in> gmctxtex_onp P \<R>" unfolding *
    by auto
  moreover from len l rel inv have "(fill_gholes C zs, t) \<in> gmctxtex_onp P \<L>" unfolding *
    by auto
  ultimately show "(s, t) \<in> gmctxtex_onp P \<R> O gmctxtex_onp P \<L>"
    by auto
qed

subsection \<open>Signature preserving and signature closed\<close>

definition function_closed where
  "function_closed \<F> \<R> \<longleftrightarrow> (\<forall> f ss ts. (f, length ts) \<in> \<F> \<longrightarrow> 0 \<noteq> length ts \<longrightarrow>
    length ss = length ts \<longrightarrow> (\<forall> i. i < length ts \<longrightarrow> (ss ! i, ts ! i) \<in> \<R>) \<longrightarrow>
    (GFun f ss, GFun f ts) \<in> \<R>)"

lemma function_closedD: "function_closed \<F> \<R> \<Longrightarrow>
  (f,length ts) \<in> \<F> \<Longrightarrow> 0 \<noteq> length ts \<Longrightarrow> length ss = length ts \<Longrightarrow>
  \<lbrakk>\<And> i. i < length ts \<Longrightarrow> (ss ! i, ts ! i) \<in> \<R>\<rbrakk> \<Longrightarrow>
  (GFun f ss, GFun f ts) \<in> \<R>"
  unfolding function_closed_def by blast

lemma all_ctxt_closed_imp_function_closed:
  "all_ctxt_closed \<F> \<R> \<Longrightarrow> function_closed \<F> \<R>"
  unfolding all_ctxt_closed_def function_closed_def
  by auto

lemma all_ctxt_closed_imp_reflx_on_sig:
  assumes "all_ctxt_closed \<F> \<R>"
  shows "Restr Id (\<T>\<^sub>G \<F>) \<subseteq> \<R>"
proof -
  {fix s assume "(s, s) \<in> Restr Id (\<T>\<^sub>G \<F>)" then have "(s, s) \<in> \<R>"
    proof (induction s)
      case (GFun f ts)
      then show ?case using all_ctxt_closedD[OF assms]
        by (auto simp: \<T>\<^sub>G_equivalent_def UN_subset_iff)
    qed}
  then show ?thesis by auto
qed

lemma function_closed_un_id_all_ctxt_closed:
  "function_closed \<F> \<R> \<Longrightarrow> Restr Id (\<T>\<^sub>G \<F>) \<subseteq> \<R> \<Longrightarrow> all_ctxt_closed \<F> \<R>"
  unfolding all_ctxt_closed_def
  by (auto dest: function_closedD simp: subsetD)

lemma gctxtex_onp_in_signature [intro]:
  assumes "\<And> C. P C \<Longrightarrow> funas_gctxt C \<subseteq> \<F>" "\<And> C. P C \<Longrightarrow> funas_gctxt C \<subseteq> \<G>"
    and "\<R> \<subseteq> \<T>\<^sub>G \<F> \<times> \<T>\<^sub>G \<G>"
  shows "gctxtex_onp P \<R> \<subseteq> \<T>\<^sub>G \<F> \<times> \<T>\<^sub>G \<G>" using assms
  by (auto simp: gctxtex_onp_def \<T>\<^sub>G_equivalent_def) blast+

lemma gmctxtex_onp_in_signature [intro]:
  assumes "\<And> C. P C \<Longrightarrow> funas_gmctxt C \<subseteq> \<F>" "\<And> C. P C \<Longrightarrow> funas_gmctxt C \<subseteq> \<G>"
    and "\<R> \<subseteq> \<T>\<^sub>G \<F> \<times> \<T>\<^sub>G \<G>"
  shows "gmctxtex_onp P \<R> \<subseteq> \<T>\<^sub>G \<F> \<times> \<T>\<^sub>G \<G>" using assms
  by (auto simp: gmctxtex_onp_def \<T>\<^sub>G_equivalent_def in_set_conv_nth) force+

lemma gctxtex_onp_in_signature_tranc [intro]:
  "gctxtex_onp P \<R> \<subseteq> \<T>\<^sub>G \<F> \<times> \<T>\<^sub>G \<F> \<Longrightarrow> (gctxtex_onp P \<R>)\<^sup>+ \<subseteq> \<T>\<^sub>G \<F> \<times> \<T>\<^sub>G \<F>"
  by (auto simp: Restr_simps)

lemma gmctxtex_onp_in_signature_tranc [intro]:
  "gmctxtex_onp P \<R> \<subseteq> \<T>\<^sub>G \<F> \<times> \<T>\<^sub>G \<F> \<Longrightarrow> (gmctxtex_onp P \<R>)\<^sup>+ \<subseteq> \<T>\<^sub>G \<F> \<times> \<T>\<^sub>G \<F>"
  by (auto simp: Restr_simps)

lemma gmctxtex_onp_fun_closed [intro!]:
  assumes "\<And> f n. (f, n) \<in> \<F> \<Longrightarrow> n \<noteq> 0 \<Longrightarrow> P (GMFun f (replicate n GMHole))"
    and "\<And> C Ds. P C \<Longrightarrow> num_gholes C = length Ds \<Longrightarrow> 0 < num_gholes C \<Longrightarrow>
      \<forall> D \<in> set Ds. P D \<Longrightarrow> P (fill_gholes_gmctxt C Ds)"
  shows "function_closed \<F> (gmctxtex_onp P \<R>)" unfolding function_closed_def
proof (rule allI, intro allI, intro impI)
  fix f ss ts assume sig: "(f, length ts) \<in> \<F>"
    and len: "0 \<noteq> length ts" "length ss = length ts"
    and mem: "\<forall> i < length ts. (ss ! i, ts ! i) \<in> gmctxtex_onp P \<R>"
  let ?C = "GMFun f (replicate (length ts) GMHole)"
  from mem len obtain Ds sss tss where
    l': "length ts = length Ds" "length Ds = length sss" "length sss = length tss" and
    inn: "\<forall> i < length tss. length (sss ! i) = length (tss ! i)" and
    eq: "\<forall> i < length tss. ss ! i =\<^sub>G\<^sub>f (Ds ! i, sss ! i)" "\<forall> i < length tss. ts ! i =\<^sub>G\<^sub>f (Ds ! i, tss ! i)" and
    inv: "\<forall> i < length (concat tss). (concat sss ! i, concat tss ! i) \<in> \<R>" "\<forall> D \<in> set Ds. P D"
    by (auto elim!: gmctxtex_onp_listE)
  have *: "fill_gholes ?C ss = GFun f ss" "fill_gholes ?C ts = GFun f ts"
    using len assms(1) by (auto simp del: fill_gholes.simps)
  have s: "GFun f ss =\<^sub>G\<^sub>f (fill_gholes_gmctxt ?C Ds, concat sss)"
    using assms(1) l' eq(1) inn len inv(1) unfolding *[symmetric]
    by (intro fill_gholes_gmctxt_sound) auto
  have t: "GFun f ts =\<^sub>G\<^sub>f (fill_gholes_gmctxt ?C Ds, concat tss)"
    using assms(1) eq l' inn len inv(1) unfolding *[symmetric]
    by (intro fill_gholes_gmctxt_sound) auto
  then show "(GFun f ss, GFun f ts) \<in> gmctxtex_onp P \<R>"
    unfolding eqgfE[OF s] eqgfE[OF t]
    using eqgfE(2)[OF s] eqgfE(2)[OF t] sig len l' inv
    using assms(1)[OF sig] assms(2)[of "GMFun f (replicate (length ts) GMHole)" Ds]
    using gmctxtex_onpI[of P "fill_gholes_gmctxt (GMFun f (replicate (length ts) GMHole)) Ds" "concat sss" "concat tss" \<R>]
    by (auto simp del: fill_gholes_gmctxt.simps fill_gholes.simps)
qed

declare subsetI[rule del]
lemma gmctxtex_onp_sig_closed [intro]:
  assumes "\<And> f n. (f, n) \<in> \<F> \<Longrightarrow> P (GMFun f (replicate n GMHole))"
    and  "\<And> C Ds. num_gholes C = length Ds \<Longrightarrow> P C \<Longrightarrow> \<forall> D \<in> set Ds. P D \<Longrightarrow> P (fill_gholes_gmctxt C Ds)"
  shows "all_ctxt_closed \<F> (gmctxtex_onp P \<R>)" using assms
  by (intro function_closed_un_id_all_ctxt_closed) auto
declare subsetI[intro!]

lemma gmctxt_cl_gmctxtex_onp_conv:
  "gmctxt_cl \<F> \<R> = gmctxtex_onp (\<lambda> C. funas_gmctxt C \<subseteq> \<F>) \<R>" (is "?Ls = ?Rs")
proof -
  have sig_cl: "all_ctxt_closed \<F> (?Rs)" by (intro gmctxtex_onp_sig_closed) auto
  {fix s t assume "(s, t) \<in> ?Ls" then have "(s, t) \<in> ?Rs"
    proof induct
      case (step ss ts f)
      then show ?case using all_ctxt_closedD[OF sig_cl]
        by force
    qed (intro subsetD[OF gmctxtex_onp_arg_monoI], auto)}
  moreover
  {fix s t assume "(s, t) \<in> ?Rs"
    from gmctxtex_onpE[OF this] obtain C us vs where
      terms: "s = fill_gholes C us" "t = fill_gholes C vs" and
      fill_inv: "num_gholes C = length us" "length us = length vs" and
      rel: "funas_gmctxt C \<subseteq> \<F>" "\<forall> i < length vs. (us ! i, vs ! i) \<in> \<R>" by blast
    have "(s, t) \<in> ?Ls" unfolding terms using fill_inv rel
    proof (induct C arbitrary: us vs)
      case GMHole
      then show ?case using rel(2) by (cases vs; cases us) auto
    next
      case (GMFun f Ds)
      show ?case using GMFun(2-) unfolding partition_holes_fill_gholes_conv'
        by (intro all_ctxt_closedD[OF gmctxt_cl_is_all_ctxt_closed[of \<F> \<R>]])
           (auto simp: partition_by_nth_nth SUP_le_iff length_partition_gholes_nth intro!: GMFun(1))
    qed}
  ultimately show ?thesis by auto
qed

end