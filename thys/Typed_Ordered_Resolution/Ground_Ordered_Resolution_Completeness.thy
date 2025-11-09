theory Ground_Ordered_Resolution_Completeness
  imports 
    Ground_Ordered_Resolution 
    Relation_Extra
    First_Order_Clause.HOL_Extra
begin

subsection \<open>Mode Construction\<close>

context ground_ordered_resolution_calculus
begin

context 
  fixes N :: "'t clause set"
begin

function epsilon :: "'t clause \<Rightarrow> 't set" where
  "epsilon C = {A | A C'. 
    C \<in> N \<and>
    C = add_mset (Pos A) C' \<and>
    select C = {#} \<and>
    is_strictly_maximal (Pos A) C \<and>
    \<not> (\<Union>D \<in> {D \<in> N. D \<prec>\<^sub>c C}. epsilon D) \<TTurnstile> C}"
  by auto

termination epsilon
proof (relation "{(x, y). x \<prec>\<^sub>c y}")
  show "wf {(x, y). x \<prec>\<^sub>c y}"
    using wfp_def by blast
next
  show "\<And>C D. D \<in> {D \<in> N. D \<prec>\<^sub>c C} \<Longrightarrow> (D, C) \<in> {(x, y). x \<prec>\<^sub>c y}"
    by simp
qed

declare epsilon.simps[simp del]

end


lemma epsilon_eq_empty_or_singleton: "epsilon N C = {} \<or> (\<exists>A. epsilon N C = {A})"
proof -

  have "\<exists>\<^sub>\<le>\<^sub>1A. is_strictly_maximal (Pos A) C"
    by (metis (mono_tags, lifting) Uniq_def literal.inject(1)
        literal.order.Uniq_is_strictly_maximal_in_mset)

  hence "\<exists>\<^sub>\<le>\<^sub>1A. \<exists>C'. 
    C = add_mset (Pos A) C' \<and> is_strictly_maximal (Pos A) C"
    by (simp add: Uniq_def)

  hence Uniq_epsilon: "\<exists>\<^sub>\<le>\<^sub>1A. \<exists>C'.
    C \<in> N \<and>
    C = add_mset (Pos A) C' \<and>
    select C = {#} \<and>
    is_strictly_maximal (Pos A) C \<and>
    \<not> (\<Union>D \<in> {D \<in> N. D \<prec>\<^sub>c C}. epsilon N D) \<TTurnstile> C"
    using Uniq_antimono'
    by (smt (verit) Uniq_def Uniq_prodI case_prod_conv)

  show ?thesis
    unfolding epsilon.simps[of N C]
    using Collect_eq_if_Uniq[OF Uniq_epsilon]
    by (smt (verit, best) Collect_cong Collect_empty_eq Uniq_def Uniq_epsilon case_prod_conv
        insertCI mem_Collect_eq)
qed

definition rewrite_sys where
  "rewrite_sys N C \<equiv> (\<Union>D \<in> {D \<in> N. D \<prec>\<^sub>c C}. epsilon N D)"

lemma rewrite_sys_subset_if_less_cls: "C \<prec>\<^sub>c D \<longrightarrow> rewrite_sys N C \<subseteq> rewrite_sys N D"
  unfolding rewrite_sys_def
  by fastforce

lemma mem_epsilonE:
  assumes rule_in: "A \<in> epsilon N C"
  obtains C' where
    "C \<in> N" and
    "C = add_mset (Pos A) C'" and
    "select C = {#}" and
    "is_strictly_maximal (Pos A) C" and
    "\<not> rewrite_sys N C \<TTurnstile> C"
  using rule_in
  unfolding epsilon.simps[of N C] mem_Collect_eq Let_def rewrite_sys_def
  by (metis (no_types, lifting))

lemma epsilon_unfold: "epsilon N C = {A | A C'.
    C \<in> N \<and>
    C = add_mset (Pos A) C' \<and>
    select C = {#} \<and>
    is_strictly_maximal (Pos A) C \<and>
    \<not> rewrite_sys N C \<TTurnstile> C}"
  by (simp add: epsilon.simps[of N C] rewrite_sys_def)

lemma epsilon_subset_if_less_cls: "C \<prec>\<^sub>c D \<Longrightarrow> epsilon N C \<subseteq> rewrite_sys N D"
  unfolding rewrite_sys_def
  using epsilon_unfold 
  by blast

lemma
  assumes
    "D \<preceq>\<^sub>c C" and
    C_prod: "A \<in> epsilon N C" and
    L_in: "L \<in># D"
  shows
    lesseq_trm_if_pos: "is_pos L \<Longrightarrow> atm_of L \<preceq>\<^sub>t A" and
    less_trm_if_neg: "is_neg L \<Longrightarrow> atm_of L \<prec>\<^sub>t A"
proof -
  from C_prod obtain C' where
    C_def: "C = add_mset (Pos A) C'" and
    C_max_lit: "is_strictly_maximal (Pos A) C"
    by (auto elim: mem_epsilonE)

  have "Pos A \<prec>\<^sub>l L" if "is_pos L" and "\<not> atm_of L \<preceq>\<^sub>t A"
  proof -

    from that(2) have "A \<prec>\<^sub>t atm_of L"
      by order

    hence "multp (\<prec>\<^sub>t) {#A#} {#atm_of L#}"
      by auto

    with that(1) show "Pos A \<prec>\<^sub>l L"
      by (metis (no_types, lifting) Pos_atm_of_iff less\<^sub>l_def
          literal_to_mset.simps(1))
  qed

  moreover have "Pos A \<prec>\<^sub>l L" if "is_neg L" and "\<not> atm_of L \<prec>\<^sub>t A"
  proof -

    from that(2) have "A \<preceq>\<^sub>t atm_of L"
      by order

    hence "multp (\<prec>\<^sub>t) {#A#} {#atm_of L, atm_of L#}"
      by auto

    with that(1) show "Pos A \<prec>\<^sub>l L"
      by (cases L) (simp_all add: less\<^sub>l_def)
  qed

  moreover have False if "Pos A \<prec>\<^sub>l L"
  proof -

    have "C \<prec>\<^sub>c D"
      unfolding less\<^sub>c_def
    proof (rule multp_if_maximal_of_lhs_is_less)

      show "Pos A \<in># C"
        by (simp add: C_def)
    next

      show "L \<in># D"
        using L_in 
        by simp
    next

      show "is_maximal (Pos A) C"
        using C_max_lit
        by auto
    next

      show "Pos A \<prec>\<^sub>l L"
        using that 
        by simp
    qed simp_all

    with \<open>D \<preceq>\<^sub>c C\<close> show False
      by order
  qed

  ultimately show "is_pos L \<Longrightarrow> atm_of L \<preceq>\<^sub>t A" and "is_neg L \<Longrightarrow> atm_of L \<prec>\<^sub>t A"
    by metis+
qed

lemma less_trm_iff_less_cls_if_mem_epsilon:
  assumes C_prod: "A\<^sub>C \<in> epsilon N C" and D_prod: "A\<^sub>D \<in> epsilon N D"
  shows "A\<^sub>C \<prec>\<^sub>t A\<^sub>D \<longleftrightarrow> C \<prec>\<^sub>c D"
proof -
  from C_prod
  obtain C' where
    "C \<in> N" and
    C_def: "C = add_mset (Pos A\<^sub>C) C'" and
    "is_strictly_maximal (Pos A\<^sub>C) C"
    by (auto elim!: mem_epsilonE)

  hence "\<forall>L \<in># C'. L \<prec>\<^sub>l Pos A\<^sub>C"
    unfolding is_strictly_maximal_def
    by auto

  from D_prod
  obtain D' where
    "D \<in> N" and
    D_def: "D = add_mset (Pos A\<^sub>D) D'" and
    "is_strictly_maximal (Pos A\<^sub>D) D"
    by (auto elim!: mem_epsilonE)

  hence "\<forall>L \<in># D'. L\<prec>\<^sub>l Pos A\<^sub>D"
    unfolding is_strictly_maximal_def
    by auto

  show ?thesis
  proof (rule iffI)
    assume "A\<^sub>C \<prec>\<^sub>t A\<^sub>D"

    hence "Pos A\<^sub>C \<prec>\<^sub>l Pos A\<^sub>D"
      by (simp add: less\<^sub>l_def)

    moreover hence "\<forall>L \<in># C'. L \<prec>\<^sub>l Pos A\<^sub>D"
      using \<open>\<forall>L \<in># C'. L \<prec>\<^sub>l Pos A\<^sub>C\<close>
      by fastforce

    ultimately show "C \<prec>\<^sub>c D"
      using one_step_implies_multp[of D C _ "{#}"] less\<^sub>c_def
      by (simp add: D_def C_def)
  next
    assume "C \<prec>\<^sub>c D"

    hence "epsilon N C \<subseteq> (\<Union> (epsilon N ` {x \<in> N. x \<prec>\<^sub>c D}))"
      using \<open>C \<in> N\<close>
      by auto

    hence "A\<^sub>C \<in> (\<Union> (epsilon N ` {x \<in> N. x \<prec>\<^sub>c D}))"
      using C_prod 
      by auto

    hence "A\<^sub>C \<noteq> A\<^sub>D"
      by (metis D_prod rewrite_sys_def mem_epsilonE true_cls_add_mset true_lit_iff)

    moreover have "\<not> (A\<^sub>D \<prec>\<^sub>t A\<^sub>C)"
    proof (rule notI)
      assume "A\<^sub>D \<prec>\<^sub>t A\<^sub>C"

      then have "Pos A\<^sub>D \<prec>\<^sub>l Pos A\<^sub>C"
        by (simp add: less\<^sub>l_def)

      moreover have "\<forall>L \<in># D'. L \<prec>\<^sub>l Pos A\<^sub>C"
        using \<open>\<forall>L \<in># D'. L \<prec>\<^sub>l Pos A\<^sub>D\<close>
        using calculation literal.order.order.strict_trans 
        by blast

      ultimately have "D \<prec>\<^sub>c C"
        using one_step_implies_multp[of C D _ "{#}"] less\<^sub>c_def
        by (simp add: D_def C_def)

      thus False
        using \<open>C \<prec>\<^sub>c D\<close> 
        by order
    qed

    ultimately show "A\<^sub>C \<prec>\<^sub>t A\<^sub>D"
      by order
  qed
qed

lemma false_cls_if_productive_epsilon:
  assumes C_prod: "A \<in> epsilon N C" and "D \<in> N" and "C \<prec>\<^sub>c D"
  shows "\<not> rewrite_sys N D \<TTurnstile> C - {#Pos A#}"
proof -

  from C_prod obtain C' where
    C_in: "C \<in> N" and
    C_def: "C = add_mset (Pos A) C'" and
    "select C = {#}" and
    Pox_A_max: "is_strictly_maximal (Pos A) C" and
    "\<not> rewrite_sys N C \<TTurnstile> C"
    by (rule mem_epsilonE) blast

  from \<open>D \<in> N\<close> \<open>C \<prec>\<^sub>c D\<close> have "A \<in> rewrite_sys N D"
    using C_prod epsilon_subset_if_less_cls 
    by auto

  from \<open>D \<in> N\<close> have "rewrite_sys N D \<subseteq> (\<Union>D \<in> N. epsilon N D)"
    by (auto simp: rewrite_sys_def)

  have "\<not> rewrite_sys N D \<TTurnstile> C'"
    unfolding true_cls_def Set.bex_simps
  proof (intro ballI)
    fix L 
    assume L_in: "L \<in># C'"

    hence "L \<in># C"
      by (simp add: C_def)

    have "C' \<prec>\<^sub>c C"
      by (metis (mono_tags, lifting) C_def add.comm_neutral
          add_mset_add_single add_mset_not_empty
          clause.order.multiset_extension_def empty_iff
          one_step_implies_multp set_mset_empty)

    hence "C' \<preceq>\<^sub>c C"
      by order

    show "\<not> rewrite_sys N D \<TTurnstile>l L"
    proof (cases L)
      case (Pos A\<^sub>L)

      moreover have "A\<^sub>L \<notin> rewrite_sys N D"
      proof -

        have "\<forall>y\<in>#C'. y \<prec>\<^sub>l Pos A"
          using Pox_A_max C_def is_strictly_maximal_def 
          by auto

        with Pos have "A\<^sub>L \<notin> insert A (rewrite_sys N C)"
          using L_in \<open>\<not> rewrite_sys N C \<TTurnstile> C\<close> C_def
          by blast

        moreover have "A\<^sub>L \<notin> (\<Union>D' \<in> {D' \<in> N. C \<prec>\<^sub>c D' \<and> D' \<prec>\<^sub>c D}. epsilon N D')"
        proof -
          have "A\<^sub>L \<preceq>\<^sub>t A"
            using Pos lesseq_trm_if_pos[OF \<open>C' \<preceq>\<^sub>c C\<close> C_prod \<open>L \<in># C'\<close>]
            by simp

          thus ?thesis
            using less_trm_iff_less_cls_if_mem_epsilon
            using C_prod calculation rewrite_sys_def
            by fastforce
        qed

        moreover have "rewrite_sys N D =
          insert A (rewrite_sys N C) \<union> (\<Union>D' \<in> {D' \<in> N. C \<prec>\<^sub>c D' \<and> D' \<prec>\<^sub>c D}. epsilon N D')"
        proof -

          have "rewrite_sys N D = (\<Union>D' \<in> {D' \<in> N. D' \<prec>\<^sub>c D}. epsilon N D')"
            by (simp only: rewrite_sys_def)

          also have 
            "\<dots> = (\<Union>D' \<in> {D' \<in> {y \<in> N. y \<prec>\<^sub>c C} \<union> {C} \<union> {y \<in> N. C \<prec>\<^sub>c y}. D' \<prec>\<^sub>c D}. epsilon N D')"
            using C_in clause.order.antisym_conv3 
            by auto

          also have 
            "\<dots> = (\<Union>D' \<in> {y \<in> N. y \<prec>\<^sub>c C \<and> y \<prec>\<^sub>c D} \<union> {C} \<union> {y \<in> N. C \<prec>\<^sub>c y \<and> y \<prec>\<^sub>c D}. epsilon N D')"
            using \<open>C \<prec>\<^sub>c D\<close> 
            by auto

          also have "\<dots> = (\<Union>D' \<in> {y \<in> N. y \<prec>\<^sub>c C} \<union> {C} \<union> {y \<in> N. C \<prec>\<^sub>c y \<and> y \<prec>\<^sub>c D}. epsilon N D')"
            by (metis (lifting) assms(3) clause.order.order.strict_trans)

          also have 
            "\<dots> = rewrite_sys N C \<union> epsilon N C \<union> (\<Union>D' \<in> {y \<in> N. C \<prec>\<^sub>c y \<and> y \<prec>\<^sub>c D}. epsilon N D')"
            by (auto simp: rewrite_sys_def)

          finally show ?thesis
            using C_prod
            by (metis (no_types, lifting) empty_iff insertE insert_is_Un
                epsilon_eq_empty_or_singleton sup_commute)
        qed

        ultimately show ?thesis
          by simp
      qed
      ultimately show ?thesis
        by simp
    next
      case (Neg A\<^sub>L)

      moreover have "A\<^sub>L \<in> rewrite_sys N D"
        using Neg \<open>L \<in># C\<close> \<open>C \<prec>\<^sub>c D\<close> \<open>\<not> rewrite_sys N C \<TTurnstile> C\<close> rewrite_sys_subset_if_less_cls
        by blast

      ultimately show ?thesis
        by simp
    qed
  qed

  thus "\<not> rewrite_sys N D \<TTurnstile> C - {#Pos A#}"
    by (simp add: C_def)
qed

lemma neg_notin_Interp_not_produce:
  "Neg A \<in># C \<Longrightarrow> A \<notin> rewrite_sys N D \<union> epsilon N D \<Longrightarrow> C \<preceq>\<^sub>c D \<Longrightarrow> A \<notin> epsilon N D''"
  by (smt (verit, del_insts) Neg_atm_of_iff UN_I Un_iff clause.order.order.strict_trans1
      clause.order.not_less less_trm_if_neg literal.sel(2) mem_Collect_eq mem_epsilonE 
      rewrite_sys_def  term.order.order.asym)

lemma lift_interp_entails:
  assumes
    D_in: "D \<in> N" and
    D_entailed: "rewrite_sys N D \<TTurnstile> D" and
    C_in: "C \<in> N" and
    D_lt_C: "D \<prec>\<^sub>c C"
  shows "rewrite_sys N C \<TTurnstile> D"
proof -

  from D_entailed obtain L A where
    L_in: "L \<in># D" and
    L_eq_disj_L_eq: "L = Pos A \<and> A \<in> rewrite_sys N D \<or> L = Neg A \<and> A \<notin> rewrite_sys N D"
    unfolding true_cls_def true_lit_iff 
    by metis

  have "rewrite_sys N D \<subseteq> rewrite_sys N C"
    using D_lt_C rewrite_sys_subset_if_less_cls 
    by auto

  from L_eq_disj_L_eq 
  show "rewrite_sys N C \<TTurnstile> D"
  proof (elim disjE conjE)
    assume "L = Pos A" and "A \<in> rewrite_sys N D"

    thus "rewrite_sys N C \<TTurnstile> D"
      using L_in \<open>rewrite_sys N D \<subseteq> rewrite_sys N C\<close> 
      by auto
  next
    assume L: "L = Neg A" and A: "A \<notin> rewrite_sys N D"

    have "A \<notin> rewrite_sys N C"
    proof (cases "A \<in> epsilon N C")
      case True

      then show ?thesis
        by (meson mem_epsilonE pos_literal_in_imp_true_cls strictly_maximal_in_clause)
    next
      case False

      then have "A \<notin> epsilon N D"
        using D_entailed mem_epsilonE 
        by blast

      then show ?thesis
        using neg_notin_Interp_not_produce A L_in
        unfolding rewrite_sys_def L
        by blast
    qed

    thus "rewrite_sys N C \<TTurnstile> D"
      using L_in \<open>L = Neg A\<close> 
      by blast
  qed
qed

lemma produces_imp_in_interp:
  assumes "Neg A \<in># C" and D_prod: "A \<in> epsilon N D"
  shows "A \<in> rewrite_sys N C"
proof -
  from D_prod have "Pos A \<in># D" and "is_strictly_maximal (Pos A) D"
    by (auto elim: mem_epsilonE)

  have "D \<prec>\<^sub>c C"
    unfolding less\<^sub>c_def
  proof (rule multp_if_maximal_of_lhs_is_less)

    show "Pos A \<in># D"
      using \<open>Pos A \<in># D\<close> .
  next

    show "Neg A \<in># C"
      using \<open>Neg A \<in># C\<close> .
  next

    show "Pos A \<prec>\<^sub>l Neg A"
      by (simp add: less\<^sub>l_def)
  next

    show "is_maximal (Pos A) D"
      using \<open>is_strictly_maximal (Pos A) D\<close> 
      by auto
  qed simp_all

  hence "\<not> (\<prec>\<^sub>c)\<^sup>=\<^sup>= C D"
    using clause.order.not_less 
    by blast

  thus ?thesis
  proof (rule contrapos_np)

    from D_prod show  "A \<notin> rewrite_sys N C \<Longrightarrow> (\<prec>\<^sub>c)\<^sup>=\<^sup>= C D"
      using \<open>D \<prec>\<^sub>c C\<close> epsilon_subset_if_less_cls 
      by blast
  qed
qed

lemma split_Union_epsilon:
  assumes D_in: "D \<in> N"
  shows "(\<Union>C \<in> N. epsilon N C) =
    rewrite_sys N D \<union> epsilon N D \<union> (\<Union>C \<in> {C \<in> N. D \<prec>\<^sub>c C}. epsilon N C)"
proof -

  have "N = {C \<in> N. C \<prec>\<^sub>c D} \<union> {D} \<union> {C \<in> N. D \<prec>\<^sub>c C}"
  proof (rule partition_set_around_element)

    show "totalp_on N (\<prec>\<^sub>c)"
      using clause.order.totalp_on_less .
  next

    show "D \<in> N"
      using D_in 
      by simp
  qed

  hence "(\<Union>C \<in> N. epsilon N C) =
      (\<Union>C \<in> {C \<in> N. C \<prec>\<^sub>c D}. epsilon N C) \<union> epsilon N D \<union> (\<Union>C \<in> {C \<in> N. D \<prec>\<^sub>c C}. epsilon N C)"
    by auto

  thus "(\<Union>C \<in> N. epsilon N C) =
    rewrite_sys N D \<union> epsilon N D \<union> (\<Union>C \<in> {C \<in> N. D \<prec>\<^sub>c C}. epsilon N C)"
    by (simp add: rewrite_sys_def)
qed

lemma split_Union_epsilon':
  assumes D_in: "D \<in> N"
  shows "(\<Union>C \<in> N. epsilon N C) = rewrite_sys N D \<union> (\<Union>C \<in> {C \<in> N. D \<preceq>\<^sub>c C}. epsilon N C)"
  using split_Union_epsilon[OF D_in] D_in 
  by auto

lemma lift_entailment_to_Union:
  fixes N D
  assumes
    D_in: "D \<in> N" and
    R\<^sub>D_entails_D: "rewrite_sys N D \<TTurnstile> D"
  shows
    "(\<Union>C \<in> N. epsilon N C) \<TTurnstile> D"
  using lift_interp_entails
  by (smt (verit, best) D_in R\<^sub>D_entails_D UN_iff produces_imp_in_interp split_Union_epsilon'
      subsetD sup_ge1 true_cls_def true_lit_iff)

lemma true_cls_if_productive_epsilon:
  assumes "A \<in> epsilon N C" "C \<prec>\<^sub>c D"
  shows "rewrite_sys N D \<TTurnstile> C"
  by (meson assms epsilon_subset_if_less_cls mem_epsilonE in_mono is_strictly_maximal_def
      pos_literal_in_imp_true_cls)

lemma model_preconstruction:
  fixes
    N :: "'t clause set" and
    C :: "'t clause"
  defines
    "entails \<equiv> \<lambda>E C. E \<TTurnstile> C"
  assumes "saturated N" and "{#} \<notin> N" and C_in: "C \<in> N"
  shows
    "epsilon N C = {} \<longleftrightarrow> entails (rewrite_sys N C) C"
    "(\<Union>D \<in> N. epsilon N D) \<TTurnstile> C"
    "D \<in> N \<Longrightarrow> C \<prec>\<^sub>c D \<Longrightarrow> entails (rewrite_sys N D) C"
  unfolding atomize_all atomize_conj atomize_imp
  using clause.order.wfp C_in
proof (induction C arbitrary: D rule: wfp_induct_rule)
  case (less C)
  note IH = less.IH

  from \<open>{#} \<notin> N\<close> \<open>C \<in> N\<close> have "C \<noteq> {#}"
    by metis

  define I :: "'t set" where
    "I = rewrite_sys N C"

  have i: "(epsilon N C = {}) \<longleftrightarrow> entails (rewrite_sys N C) C"
  proof (rule iffI)

    show "entails (rewrite_sys N C) C \<Longrightarrow> epsilon N C = {}"
      unfolding entails_def rewrite_sys_def
      by (metis (no_types) empty_iff equalityI mem_epsilonE rewrite_sys_def subsetI)
  next
    assume "epsilon N C = {}"

    show "entails (rewrite_sys N C) C"
    proof (cases "\<exists>A. Neg A \<in># C \<and> (Neg A \<in># select C \<or> select C = {#} \<and> is_maximal (Neg A) C)")
      case ex_neg_lit_sel_or_max: True

      then obtain A where
        "Neg A \<in># C" and
        sel_or_max: "select C = {#} \<and> is_maximal (Neg A) C \<or> is_maximal (Neg A) (select C)"
        by (metis (lifting) Neg_atm_of_iff empty_iff
            literal.order.ex_maximal_in_mset maximal_in_clause
            mset_subset_eqD select_negative_literals select_subset
            set_mset_empty)

      then obtain C' where
        C_def: "C = add_mset (Neg A) C'"
        by (metis mset_add)

      show ?thesis
      proof (cases "A \<in> rewrite_sys N C")
        case True

        then obtain D where
          "A \<in> epsilon N D" and "D \<in> N" and "D \<prec>\<^sub>c C"
          unfolding rewrite_sys_def 
          by auto

        then obtain D' where
          D_def: "D = add_mset (Pos A) D'" and
          sel_D: "select D = {#}" and
          max_t_t': "is_strictly_maximal (Pos A) D" and
          "\<not> entails (rewrite_sys N D) D"
          by (metis (lifting) IH empty_iff mem_epsilonE)

        define \<iota> :: "'t clause inference" where
          "\<iota> = Infer [D, C] (C' + D')"

        have resolution: "resolution D C (C' + D')"
        proof (rule resolutionI)

          show "C = add_mset (Neg A) C'"
            by (simp add: C_def)
        next

          show "D = add_mset (Pos A) D'"
            by (simp add: D_def)
        next

          show "D \<prec>\<^sub>c C"
            using \<open>D \<prec>\<^sub>c C\<close> .
        next

          show "select C = {#} \<and> is_maximal (Neg A) C \<or> is_maximal (Neg A) (select C)"
            using sel_or_max 
            by auto
        next

          show "select D = {#}"
            using sel_D by blast
        next

          show "is_strictly_maximal (Pos A) D"
            using max_t_t' .
        qed simp_all

        hence "\<iota> \<in> G_Inf"
          by (auto simp only: \<iota>_def G_Inf_def)

        moreover have "\<And>t. t \<in> set (prems_of \<iota>) \<longrightarrow> t \<in> N"
          using \<open>C \<in> N\<close> \<open>D \<in> N\<close>
          by (auto simp: \<iota>_def)

        ultimately have "\<iota> \<in> Inf_from N"
          by (auto simp: Inf_from_def)

        hence "\<iota> \<in> Red_I N"
          using \<open>saturated N\<close>
          by (auto simp: saturated_def)

        then obtain DD where
          DD_subset: "DD \<subseteq> N" and
          "finite DD" and
          DD_entails_CD: "G_entails (insert D DD) {C' + D'}" and
          ball_DD_lt_C: "\<forall>D \<in> DD. D \<prec>\<^sub>c C"
          unfolding Red_I_def redundant_infer_def mem_Collect_eq
          by (auto simp: \<iota>_def)

        moreover have "\<forall>D \<in> insert D DD. entails (rewrite_sys N C) D"
          using IH[THEN conjunct2, THEN conjunct2, rule_format, of _ C]
          using \<open>C \<in> N\<close> \<open>D \<in> N\<close> \<open>D \<prec>\<^sub>c C \<close> DD_subset ball_DD_lt_C
          by blast

        ultimately have "entails (rewrite_sys N C) (C' + D')"
          using DD_entails_CD
          unfolding entails_def G_entails_def
          by (simp add: I_def true_clss_def)

        moreover have "\<not> entails (rewrite_sys N D) D'"
          using \<open>\<not> entails (rewrite_sys N D) D\<close>
          using D_def entails_def
          by fastforce

        moreover have "D' \<prec>\<^sub>c D"
          by (metis (lifting) D_def add.comm_neutral add_mset_add_single
              add_mset_not_empty clause.order.multiset_extension_def
              empty_iff one_step_implies_multp set_mset_empty)

        moreover have "\<not> entails (rewrite_sys N C) D'"
          using D_def \<open>A \<in> epsilon N D\<close> \<open>D \<prec>\<^sub>c C\<close> entails_def
            false_cls_if_productive_epsilon less.prems
          by fastforce

        then show "entails (rewrite_sys N C) C"
          using C_def entails_def
          using calculation(1) by fastforce
      next
        case False

        thus ?thesis
          using \<open>Neg A \<in># C\<close>
          by (auto simp add: entails_def true_cls_def)
      qed
    next
      case False

      hence "select C = {#}"
        using select_subset select_negative_literals
        by (metis (no_types, opaque_lifting) Neg_atm_of_iff mset_subset_eqD multiset_nonemptyE)

      from False obtain A where Pos_A_in: "Pos A \<in># C" and max_Pos_A: "is_maximal (Pos A) C"
        by (metis Neg_atm_of_iff \<open>C \<noteq> {#}\<close> \<open>select C = {#}\<close> literal.collapse(1)
            literal.order.ex_maximal_in_mset maximal_in_clause)

      then obtain C' where C_def: "C = add_mset (Pos A) C'"
        by (meson mset_add)

      show ?thesis
      proof (cases "entails (rewrite_sys N C) C'")
        case True

        then show ?thesis
          using C_def entails_def
          by force
      next
        case False

        show ?thesis
        proof (cases "is_strictly_maximal (Pos A) C")
          case strictly_maximal: True
          then show ?thesis
            using \<open>epsilon N C = {}\<close> \<open>select C = {#}\<close> less.prems
            unfolding epsilon_unfold[of N C] Collect_empty_eq
            unfolding C_def entails_def 
            by blast
        next
          case False

          hence "count C (Pos A) \<ge> 2"
            using max_Pos_A
            using C_def is_maximal_def is_strictly_maximal_def
            by fastforce

          then obtain C' where C_def: "C = add_mset (Pos A) (add_mset (Pos A) C')"
            by (metis two_le_countE)

          define \<iota> :: "'t clause inference" where
            "\<iota> = Infer [C] (add_mset (Pos A) C')"

          have eq_fact: "factoring C (add_mset (Pos A) C')"
          proof (rule factoringI)

            show "C = add_mset (Pos A) (add_mset (Pos A) C')"
              by (simp add: C_def)
          next

            show "select C = {#}"
              using \<open>select C = {#}\<close> .
          next

            show "is_maximal (Pos A) C"
              using max_Pos_A .
          qed simp_all

          hence "\<iota> \<in> G_Inf"
            by (auto simp: \<iota>_def G_Inf_def)

          moreover have "\<And>t. t \<in> set (prems_of \<iota>) \<longrightarrow> t \<in> N"
            using \<open>C \<in> N\<close>
            by (auto simp add: \<iota>_def)

          ultimately have "\<iota> \<in> Inf_from N"
            by (auto simp: Inf_from_def)

          hence "\<iota> \<in> Red_I N"
            using \<open>saturated N\<close>
            by (auto simp: saturated_def)

          then obtain DD where
            DD_subset: "DD \<subseteq> N" and
            "finite DD" and
            DD_entails_concl: "G_entails DD {add_mset (Pos A) C'}" and
            ball_DD_lt_C: "\<forall>D \<in> DD. D \<prec>\<^sub>c C"
            unfolding Red_I_def redundant_infer_def
            by (auto simp: \<iota>_def)

          moreover have "\<forall>D \<in> DD. entails (rewrite_sys N C) D"
            using IH[THEN conjunct2, rule_format, of _ C]
            using \<open>C \<in> N \<close> DD_subset ball_DD_lt_C
            by blast

          ultimately have "entails (rewrite_sys N C) (add_mset (Pos A) C')"
            using DD_entails_concl
            unfolding G_entails_def entails_def
            by (simp add: I_def true_clss_def)

          then show ?thesis
            using C_def entails_def
            by fastforce
        qed
      qed
    qed
  qed

  moreover have iia: "entails (\<Union> (epsilon N ` N)) C"
    using epsilon_eq_empty_or_singleton[of N C]
  proof (elim disjE exE)
    assume "epsilon N C = {}"

    hence "entails (rewrite_sys N C) C"
      by (simp only: i)

    thus ?thesis
      using lift_entailment_to_Union[OF \<open>C \<in> N\<close>] entails_def 
      by argo
  next
    fix A
    assume "epsilon N C = {A}"

    hence eps: "A \<in> epsilon N C"
      by simp

    from eps have "Pos A \<in># C"
      unfolding epsilon.simps[of N C] mem_Collect_eq
      by force

    moreover from eps have "A \<in> \<Union> (epsilon N `N)"
      using \<open>C \<in> N\<close> UN_upper
      by fast

    ultimately show ?thesis
      using entails_def 
      by blast
  qed

  moreover have iib: "entails (rewrite_sys N D) C" if "D \<in> N" and "C \<prec>\<^sub>c D"
    using epsilon_eq_empty_or_singleton[of N C]
  proof (elim disjE exE)
    assume "epsilon N C = {}"

    hence "entails (rewrite_sys N C) C"
      unfolding i
      by simp

    thus ?thesis
      using lift_interp_entails[OF \<open>C \<in> N\<close> _ that] entails_def 
      by argo
  next
    fix A assume "epsilon N C = {A}"

    thus ?thesis
      by (simp add: entails_def that(1,2) true_cls_if_productive_epsilon)
  qed

  ultimately show ?case
    by (simp add: entails_def)
qed

lemma model_construction:
  fixes
    N :: "'t clause set" and
    C :: "'t clause"
  defines "entails \<equiv> \<lambda>E C. E \<TTurnstile> C"
  assumes "saturated N" and "{#} \<notin> N" and C_in: "C \<in> N"
  shows "entails (\<Union>D \<in> N. epsilon N D) C"
  unfolding atomize_conj atomize_imp
  using epsilon_eq_empty_or_singleton[of N C]
proof (elim disjE exE)
  assume "epsilon N C = {}"

  hence "entails (rewrite_sys N C) C"
    using model_preconstruction(1)[OF assms(2,3,4)]
    by (metis entails_def)

  thus ?thesis
    using lift_entailment_to_Union(1)[OF \<open>C \<in> N\<close>]
    by (simp only: entails_def)
next
  fix A assume "epsilon N C = {A}"

  thus ?thesis
    using C_in assms(2,3) entails_def model_preconstruction(2) 
    by blast 
qed

subsection \<open>Static Refutational Completeness\<close>

lemma statically_complete:
  fixes N :: "'t clause set"
  assumes "saturated N" and "G_entails N {{#}}"
  shows "{#} \<in> N"
  using \<open>G_entails N {{#}}\<close>
proof (rule contrapos_pp)
  assume "{#} \<notin> N"

  define I :: "'t set" where
    "I = (\<Union>D \<in> N. epsilon N D)"

  show "\<not> G_entails N G_Bot"
    unfolding G_entails_def not_all not_imp
  proof (intro exI conjI)

    show "I \<TTurnstile>s N"
      unfolding I_def
      using model_construction[OF \<open>saturated N\<close> \<open>{#} \<notin> N\<close>]
      by (simp add: true_clss_def)
  next

    show "\<not> I \<TTurnstile>s G_Bot"
      by simp
  qed
qed

sublocale statically_complete_calculus where
  Bot = G_Bot and
  Inf = G_Inf and
  entails = G_entails and
  Red_I = Red_I and
  Red_F = Red_F
  using statically_complete
  by unfold_locales simp

end

end
