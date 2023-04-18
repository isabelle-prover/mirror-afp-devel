section \<open>Expressivity of Hyper Hoare Logic\<close>

text \<open>In this file, we define program hyperproperties (definition 7), and prove theorem 3.\<close>

subsection \<open>Program Hyperproperties\<close>

theory ProgramHyperproperties
  imports Logic
begin

text \<open>Definition 7\<close>

type_synonym 'a hyperproperty = "('a \<times> 'a) set \<Rightarrow> bool"

definition set_of_traces where
  "set_of_traces C = { (\<sigma>, \<sigma>') |\<sigma> \<sigma>'. \<langle>C, \<sigma>\<rangle> \<rightarrow> \<sigma>' }"

definition hypersat where
  "hypersat C H \<longleftrightarrow> H (set_of_traces C)"

definition copy_p_state where
  "copy_p_state to_pvar to_lval \<sigma> x = to_lval (\<sigma> (to_pvar x))"

definition recover_p_state where
  "recover_p_state to_pval to_lvar l x = to_pval (l (to_lvar x))"

lemma injective_then_exists_inverse:
  assumes "injective to_lvar"
  shows "\<exists>to_pvar. (\<forall>x. to_pvar (to_lvar x) = x)"
proof -
  let ?to_pvar = "\<lambda>y. SOME x. to_lvar x = y"
  have "\<And>x. ?to_pvar (to_lvar x) = x"
    by (metis (mono_tags, lifting) assms injective_def someI)
  then show ?thesis
    by force
qed

lemma single_step_then_in_sem:
  assumes "single_sem C \<sigma> \<sigma>'"
      and "(l, \<sigma>) \<in> S"
    shows "(l, \<sigma>') \<in> sem C S"
  using assms(1) assms(2) in_sem by fastforce

lemma in_set_of_traces:
  "(\<sigma>, \<sigma>') \<in> set_of_traces C \<longleftrightarrow> \<langle>C, \<sigma>\<rangle> \<rightarrow> \<sigma>'"
  by (simp add: set_of_traces_def)


lemma in_set_of_traces_then_in_sem:
  assumes "(\<sigma>, \<sigma>') \<in> set_of_traces C"
      and "(l, \<sigma>) \<in> S"
    shows "(l, \<sigma>') \<in> sem C S"
  using in_set_of_traces assms single_step_then_in_sem by metis

lemma set_of_traces_same:
  assumes "\<And>x. to_pvar (to_lvar x) = x"
      and "\<And>x. to_pval (to_lval x) = x"
      and "S = {(copy_p_state to_pvar to_lval \<sigma>, \<sigma>) |\<sigma>. True}"
    shows "{(recover_p_state to_pval to_lvar l, \<sigma>') |l \<sigma>'. (l, \<sigma>') \<in> sem C S} = set_of_traces C"
(is "?A = ?B")
proof
  show "?A \<subseteq> ?B"
  proof (rule subsetPairI)
    fix \<sigma> \<sigma>' assume asm0: "(\<sigma>, \<sigma>') \<in> {(recover_p_state to_pval to_lvar l, \<sigma>') |l \<sigma>'. (l, \<sigma>') \<in> sem C S}"
    then obtain l where "\<sigma> = recover_p_state to_pval to_lvar l" "(l, \<sigma>') \<in> sem C S"
      by blast
    then obtain x where "(l, x) \<in> S" "\<langle>C, x\<rangle> \<rightarrow> \<sigma>'"
      by (metis fst_conv in_sem snd_conv)
    then have "l = copy_p_state to_pvar to_lval x"
      using assms(3) by blast
    moreover have "\<sigma> = x"
    proof (rule ext)
      fix y show "\<sigma> y = x y"
        by (simp add: \<open>\<sigma> = recover_p_state to_pval to_lvar l\<close> assms(1) assms(2) calculation copy_p_state_def recover_p_state_def)
    qed
    ultimately show "(\<sigma>, \<sigma>') \<in> set_of_traces C"
      by (simp add: \<open>\<langle>C, x\<rangle> \<rightarrow> \<sigma>'\<close> set_of_traces_def)
  qed
  show "?B \<subseteq> ?A"
  proof (rule subsetPairI)
    fix \<sigma> \<sigma>' assume asm0: "(\<sigma>, \<sigma>') \<in> set_of_traces C"
    let ?l = "copy_p_state to_pvar to_lval \<sigma>"
    have "(?l, \<sigma>) \<in> S"
      using assms(3) by blast
    then have "(?l, \<sigma>') \<in> sem C S"
      using asm0 in_set_of_traces_then_in_sem by blast
    moreover have "recover_p_state to_pval to_lvar ?l = \<sigma>"
    proof (rule ext)
      fix x show "recover_p_state to_pval to_lvar (copy_p_state to_pvar to_lval \<sigma>) x = \<sigma> x"
        by (simp add: assms(1) assms(2) copy_p_state_def recover_p_state_def)
    qed
    ultimately show "(\<sigma>, \<sigma>') \<in> {(recover_p_state to_pval to_lvar l, \<sigma>') |l \<sigma>'. (l, \<sigma>') \<in> sem C S}"
      by force
    qed
qed

text \<open>Theorem 3\<close>

theorem proving_hyperproperties:

  fixes to_lvar :: "'pvar \<Rightarrow> 'lvar"
  fixes to_lval :: "'pval \<Rightarrow> 'lval"

  assumes "injective to_lvar"
      and "injective to_lval"

    shows "\<exists>P Q::('lvar, 'lval, 'pvar, 'pval) state hyperassertion. (\<forall>C. hypersat C H \<longleftrightarrow> \<Turnstile> {P} C {Q})"
proof -

  obtain to_pval :: "'lval \<Rightarrow> 'pval" where r1: "\<And>x. to_pval (to_lval x) = x"
    using assms(2) injective_then_exists_inverse by blast

  obtain to_pvar :: "'lvar \<Rightarrow> 'pvar" where r2: "\<And>x. to_pvar (to_lvar x) = x"
    using assms(1) injective_then_exists_inverse by blast

  let ?P = "\<lambda>S. S = {(copy_p_state to_pvar to_lval \<sigma>, \<sigma>) |\<sigma>. True }"
  let ?Q = "\<lambda>S. H { (recover_p_state to_pval to_lvar l, \<sigma>') |l \<sigma>'. (l, \<sigma>') \<in> S }"

  have "\<And>C. hypersat C H \<longleftrightarrow> \<Turnstile> {?P} C {?Q}"
  proof
    fix C
    assume "hypersat C H"
    show "\<Turnstile> {?P} C {?Q}"
    proof (rule hyper_hoare_tripleI)
      fix S assume "S = {(copy_p_state to_pvar to_lval \<sigma>, \<sigma>) |\<sigma>. True}"
      have "{(recover_p_state to_pval to_lvar l, \<sigma>') |l \<sigma>'. (l, \<sigma>') \<in> sem C S}
  = set_of_traces C"
        using \<open>S = {(copy_p_state to_pvar to_lval \<sigma>, \<sigma>) |\<sigma>. True}\<close> set_of_traces_same[of to_pvar to_lvar to_pval to_lval]
        r1 r2 by presburger
      then show "H {(recover_p_state to_pval to_lvar l, \<sigma>') |l \<sigma>'. (l, \<sigma>') \<in> sem C S}"
        using \<open>hypersat C H\<close> hypersat_def by metis
    qed
  next
    fix C
    let ?S = "{(copy_p_state to_pvar to_lval \<sigma>, \<sigma>) |\<sigma>. True }"
    assume "\<Turnstile> {?P} C {?Q}"
    then have "?Q (sem C ?S)"
      by (simp add: hyper_hoare_triple_def)
    moreover have "{(recover_p_state to_pval to_lvar l, \<sigma>') |l \<sigma>'. (l, \<sigma>') \<in> sem C ?S} = set_of_traces C"
      using r1 r2 set_of_traces_same[of to_pvar to_lvar to_pval to_lval]
      by presburger
    ultimately show "hypersat C H"
      by (simp add: hypersat_def)
  qed
  then show ?thesis 
    by auto
qed





text \<open>Hypersafety, hyperliveness\<close>

definition max_k where
  "max_k k S \<longleftrightarrow> finite S \<and> card S \<le> k"

definition hypersafety where
  "hypersafety P \<longleftrightarrow> (\<forall>S. \<not> P S \<longrightarrow> (\<forall>S'. S \<subseteq> S' \<longrightarrow> \<not> P S'))"

definition k_hypersafety where
  "k_hypersafety k P \<longleftrightarrow> (\<forall>S. \<not> P S \<longrightarrow> (\<exists>S'. S' \<subseteq> S \<and> max_k k S' \<and> (\<forall>S''. S' \<subseteq> S'' \<longrightarrow> \<not> P S'')))"

definition hyperliveness where
  "hyperliveness P \<longleftrightarrow> (\<forall>S. \<exists>S'. S \<subseteq> S' \<and> P S')"

lemma k_hypersafetyI:
  assumes "\<And>S. \<not> P S \<Longrightarrow> \<exists>S'. S' \<subseteq> S \<and> max_k k S' \<and> (\<forall>S''. S' \<subseteq> S'' \<longrightarrow> \<not> P S'')"
  shows "k_hypersafety k P"
  by (simp add: assms k_hypersafety_def)


lemma hypersafetyI:
  assumes "\<And>S S'. \<not> P S \<Longrightarrow> S \<subseteq> S' \<Longrightarrow> \<not> P S'"
  shows "hypersafety P"
  by (metis assms hypersafety_def)

lemma hyperlivenessI:
  assumes "\<And>S. \<exists>S'. S \<subseteq> S' \<and> P S'"
  shows "hyperliveness P"
  using assms hyperliveness_def by blast

lemma k_hypersafe_is_hypersafe:
  assumes "k_hypersafety k P"
  shows "hypersafety P"
  by (metis (full_types) assms dual_order.trans hypersafety_def k_hypersafety_def)


lemma one_safety_equiv:
  assumes "sat H"
  shows "k_hypersafety 1 H \<longleftrightarrow> (\<exists>P. \<forall>S. H S \<longleftrightarrow> (\<forall>\<tau> \<in> S. P \<tau>))" (is "?A \<longleftrightarrow> ?B")
proof
  assume ?B
  then obtain P where asm0: "\<And>S. H S \<longleftrightarrow> (\<forall>\<tau> \<in> S. P \<tau>)"
    by auto
  show ?A
  proof (rule k_hypersafetyI)
    fix S
    assume asm1: "\<not> H S"
    then obtain \<tau> where "\<tau> \<in> S" "\<not> P \<tau>"
      using asm0 by blast
    let ?S = "{\<tau>}"
    have "?S \<subseteq> S \<and> max_k 1 ?S \<and> (\<forall>S''. ?S \<subseteq> S'' \<longrightarrow> \<not> H S'')"
      using \<open>\<not> P \<tau>\<close> \<open>\<tau> \<in> S\<close> asm0 max_k_def by fastforce
    then show "\<exists>S'\<subseteq>S. max_k 1 S' \<and> (\<forall>S''. S' \<subseteq> S'' \<longrightarrow> \<not> H S'')" by blast
  qed
next
  assume ?A
  let ?P = "\<lambda>\<tau>. H {\<tau>}"
  have "\<And>S. H S \<longleftrightarrow> (\<forall>\<tau> \<in> S. ?P \<tau>)"
  proof
    fix S assume "H S"
    then show "\<forall>\<tau> \<in> S. ?P \<tau>"
      using \<open>k_hypersafety 1 H\<close> hypersafety_def k_hypersafe_is_hypersafe by auto
  next
    fix S assume asm0: "\<forall>\<tau> \<in> S. ?P \<tau>"
    show "H S"
    proof (rule ccontr)
      assume "\<not> H S"
      then obtain S' where "S' \<subseteq> S \<and> max_k 1 S' \<and> (\<forall>S''. S' \<subseteq> S'' \<longrightarrow> \<not> H S'')"
        by (metis \<open>k_hypersafety 1 H\<close> k_hypersafety_def)
      then show False
      proof (cases "S' = {}")
        case True
        then show ?thesis
          by (metis \<open>S' \<subseteq> S \<and> max_k 1 S' \<and> (\<forall>S''. S' \<subseteq> S'' \<longrightarrow> \<not> H S'')\<close> assms empty_subsetI sat_def)
      next
        case False
        then obtain \<tau> where "\<tau> \<in> S'"
          by blast
        then have "card S' = 1"
          by (metis False One_nat_def Suc_leI \<open>S' \<subseteq> S \<and> max_k 1 S' \<and> (\<forall>S''. S' \<subseteq> S'' \<longrightarrow> \<not> H S'')\<close> card_gt_0_iff le_antisym max_k_def)
        then have "S' = {\<tau>}"
          using \<open>\<tau> \<in> S'\<close> card_1_singletonE by auto
        then show ?thesis
          using \<open>S' \<subseteq> S \<and> max_k 1 S' \<and> (\<forall>S''. S' \<subseteq> S'' \<longrightarrow> \<not> H S'')\<close> asm0 by fastforce
      qed
    qed
  qed
  then show ?B by blast
qed





definition hoarify where
  "hoarify P Q S \<longleftrightarrow> (\<forall>p \<in> S. fst p \<in> P \<longrightarrow> snd p \<in> Q)"

lemma hoarify_hypersafety:
  "hypersafety (hoarify P Q)"
  by (metis (no_types, opaque_lifting) hoarify_def hypersafetyI subsetD)

theorem hypersafety_1_hoare_logic:
  "k_hypersafety 1 (hoarify P Q)"
proof (rule k_hypersafetyI)
  fix S assume "\<not> hoarify P Q S"
  then obtain \<tau> where "\<tau> \<in> S" "fst \<tau> \<in> P" "snd \<tau> \<notin> Q"      
    using hoarify_def by blast
  let ?S = "{\<tau>}"
  have "?S \<subseteq> S \<and> max_k 1 ?S \<and> (\<forall>S''. ?S \<subseteq> S'' \<longrightarrow> \<not> hoarify P Q S'')"
    by (metis Compl_iff One_nat_def \<open>\<tau> \<in> S\<close> \<open>fst \<tau> \<in> P\<close> \<open>snd \<tau> \<notin> Q\<close> card.empty card.insert compl_le_compl_iff empty_not_insert finite.intros(1) finite.intros(2) hoarify_def insert_absorb le_numeral_extra(4) max_k_def subset_Compl_singleton)
  then show "\<exists>S'\<subseteq>S. max_k 1 S' \<and> (\<forall>S''. S' \<subseteq> S'' \<longrightarrow> \<not> hoarify P Q S'')"
    by meson
qed

definition incorrectnessify where
  "incorrectnessify P Q S \<longleftrightarrow> (\<forall>\<sigma>' \<in> Q. \<exists>\<sigma> \<in> P. (\<sigma>, \<sigma>') \<in> S)"

lemma incorrectnessify_liveness:
  assumes "P \<noteq> {}"
  shows "hyperliveness (incorrectnessify P Q)"
proof (rule hyperlivenessI)
  fix S
  obtain \<sigma> where asm0: "\<sigma> \<in> P"
    using assms by blast
  let ?S = "S \<union> {(\<sigma>, \<sigma>') |\<sigma>'. \<sigma>' \<in> Q}"
  have "incorrectnessify P Q ?S"
    using asm0 incorrectnessify_def by force
  then show "\<exists>S'. S \<subseteq> S' \<and> incorrectnessify P Q S'"
    using sup.cobounded1 by blast
qed

definition real_incorrectnessify where
  "real_incorrectnessify P Q S \<longleftrightarrow> (\<forall>\<sigma> \<in> P. \<exists>\<sigma>' \<in> Q. (\<sigma>, \<sigma>') \<in> S)"

lemma real_incorrectnessify_liveness:
  assumes "Q \<noteq> {}"
  shows "hyperliveness (real_incorrectnessify P Q)"
  by (metis UNIV_I assms equals0I hyperliveness_def real_incorrectnessify_def subsetI)











text \<open>Verifying GNI\<close>

definition gni_hyperassertion :: "'n \<Rightarrow> 'n \<Rightarrow> ('n \<Rightarrow> 'v) hyperassertion" where
  "gni_hyperassertion h l S \<longleftrightarrow> (\<forall>\<sigma> \<in> S. \<forall>v. \<exists>\<sigma>' \<in> S. \<sigma>' h = v \<and> \<sigma> l = \<sigma>' l)"

definition semify where
  "semify \<Sigma> S = { (l, \<sigma>') |\<sigma>' \<sigma> l. (l, \<sigma>) \<in> S \<and> (\<sigma>, \<sigma>') \<in> \<Sigma> }"

definition hyperprop_hht where
  "hyperprop_hht P Q \<Sigma> \<longleftrightarrow> (\<forall>S. P S \<longrightarrow> Q (semify \<Sigma> S))"

text \<open>Footnote 4\<close>
theorem any_hht_hyperprop:
  "\<Turnstile> {P} C {Q} \<longleftrightarrow> hypersat C (hyperprop_hht P Q)" (is "?A \<longleftrightarrow> ?B")
proof
  have "\<And>S. semify (set_of_traces C) S = sem C S"
  proof -
    fix S
    have "\<And>l \<sigma>'. (l, \<sigma>') \<in> sem C S \<longleftrightarrow> (l, \<sigma>') \<in> semify (set_of_traces C) S"
    proof -
      fix l \<sigma>'
      have "(l, \<sigma>') \<in> sem C S \<longleftrightarrow> (\<exists>\<sigma>. (l, \<sigma>) \<in> S \<and> \<langle>C, \<sigma>\<rangle> \<rightarrow> \<sigma>')"
        by (simp add: in_sem)
      also have "... \<longleftrightarrow> (\<exists>\<sigma>. (l, \<sigma>) \<in> S \<and> (\<sigma>, \<sigma>') \<in> set_of_traces C)"
        using set_of_traces_def by fastforce
      then show "(l, \<sigma>') \<in> sem C S \<longleftrightarrow> (l, \<sigma>') \<in> semify (set_of_traces C) S"
        by (simp add: calculation semify_def)
    qed
    then show "semify (set_of_traces C) S = sem C S"
      by auto
  qed
  show "?A \<Longrightarrow> ?B"
    by (simp add: \<open>\<And>S. semify (set_of_traces C) S = sem C S\<close> hyper_hoare_tripleE hyperprop_hht_def hypersat_def)
  show "?B \<Longrightarrow> ?A"
    by (simp add: \<open>\<And>S. semify (set_of_traces C) S = sem C S\<close> hyper_hoare_triple_def hyperprop_hht_def hypersat_def)
qed

end