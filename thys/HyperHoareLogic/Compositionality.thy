section \<open>Compositionality Rules\<close>

theory Compositionality
  imports Logic Expressivity Loops
begin

text \<open>In this file, we prove the soundness of all compositionality rules presented in Appendix D (figure 11).\<close>

definition in_set where
  "in_set \<phi> S \<longleftrightarrow> \<phi> \<in> S"

subsection \<open>Linking rule\<close>

proposition rule_linking:
  assumes "\<And>\<phi>1 (\<phi>2 :: ('a, 'b, 'c, 'd) state). fst \<phi>1 = fst \<phi>2 \<and> ( \<Turnstile> { (in_set \<phi>1 :: (('a, 'b, 'c, 'd) state) hyperassertion) } C { in_set \<phi>2 } )
  \<Longrightarrow> ( \<Turnstile> { (P \<phi>1 :: (('a, 'b, 'c, 'd) state) hyperassertion) } C { Q \<phi>2 } )"
  shows "\<Turnstile> { ((\<lambda>S. \<forall>\<phi>1 \<in> S. P \<phi>1 S) :: (('a, 'b, 'c, 'd) state) hyperassertion) } C { (\<lambda>S. \<forall>\<phi>2 \<in> S. Q \<phi>2 S) }"
proof (rule hyper_hoare_tripleI)
  fix S assume asm0: "\<forall>\<phi>1\<in>S. P \<phi>1 S"
  show "\<forall>\<phi>2\<in>sem C S. Q \<phi>2 (sem C S)"
  proof (clarify)
    fix l \<sigma>' assume "(l, \<sigma>') \<in> sem C S"
    then obtain \<sigma> where "(l, \<sigma>) \<in> S" "single_sem C \<sigma> \<sigma>'"
      by (metis fst_conv in_sem snd_conv)
    then show "Q (l, \<sigma>') (sem C S)"
      by (metis (mono_tags, opaque_lifting) asm0 assms fst_eqD hyper_hoare_triple_def in_set_def single_step_then_in_sem)
  qed
qed


lemma rule_linking_alt:
  assumes "\<And>l \<sigma> \<sigma>'. single_sem C \<sigma> \<sigma>' \<Longrightarrow> ( \<Turnstile> { P (l, \<sigma>) } C { Q (l, \<sigma>') } )"
  shows "\<Turnstile> { (\<lambda>S. \<forall>\<omega> \<in> S. P \<omega> S) } C { (\<lambda>S. \<forall>\<omega>' \<in> S. Q \<omega>' S) }"
proof (rule hyper_hoare_tripleI)
  fix S assume asm0: "\<forall>\<omega>\<in>S. P \<omega> S"
  show "\<forall>\<omega>'\<in>sem C S. Q \<omega>' (sem C S)"
  proof (clarify)
    fix l \<sigma>' assume "(l, \<sigma>') \<in> sem C S"
    then obtain \<sigma> where "(l, \<sigma>) \<in> S" "single_sem C \<sigma> \<sigma>'"
      by (metis fst_conv in_sem snd_conv)
    then have "\<Turnstile> { P (l, \<sigma>) } C { Q (l, \<sigma>') }"
      by (simp add: assms)
    then show "Q (l, \<sigma>') (sem C S)"
      by (simp add: \<open>(l, \<sigma>) \<in> S\<close> asm0 hyper_hoare_tripleE)
  qed
qed

subsection \<open>Frame rules\<close>

lemma rule_lframe:

  fixes b :: "('a \<Rightarrow> ('lvar \<Rightarrow> 'lval)) \<Rightarrow> bool"
\<comment>\<open>b takes a mapping from keys to logical states (representing the tuple), and returns a boolean\<close>

  shows "\<Turnstile> { (\<lambda>S. \<forall>\<phi>. (\<forall>k. \<phi> k \<in> S) \<longrightarrow> b (fst \<circ> \<phi>)) } C { \<lambda>S. \<forall>\<phi>. (\<forall>k. \<phi> k \<in> S) \<longrightarrow> b (fst \<circ> \<phi>) }"

proof (rule hyper_hoare_tripleI)
  fix S :: "('lvar, 'lval, 'b, 'c) state set"
  assume asm0: "\<forall>\<phi>. (\<forall>k. \<phi> k \<in> S) \<longrightarrow> b (fst \<circ> \<phi>)"
  show "\<forall>\<phi>. (\<forall>k. \<phi> k \<in> sem C S) \<longrightarrow> b (fst \<circ> \<phi>)"
  proof (clarify)
    fix \<phi>' :: "'a \<Rightarrow> ('lvar, 'lval, 'b, 'c) state"
    assume asm1: "\<forall>k. \<phi>' k \<in> sem C S"
    let ?\<phi> = "\<lambda>k. SOME \<phi>k. fst \<phi>k = fst (\<phi>' k) \<and> \<phi>k \<in> S \<and> single_sem C (snd \<phi>k) (snd (\<phi>' k))"
    have r: "\<And>k. fst (?\<phi> k) = fst (\<phi>' k) \<and> (?\<phi> k) \<in> S \<and> single_sem C (snd (?\<phi> k)) (snd (\<phi>' k))"
    proof -
      fix k show "fst (?\<phi> k) = fst (\<phi>' k) \<and> (?\<phi> k) \<in> S \<and> single_sem C (snd (?\<phi> k)) (snd (\<phi>' k))"
      proof (rule someI_ex)
        show "\<exists>x. fst x = fst (\<phi>' k) \<and> x \<in> S \<and> \<langle>C, snd x\<rangle> \<rightarrow> snd (\<phi>' k)"
          by (metis asm1 fst_conv in_sem snd_conv)
      qed
    qed
    then have "b (fst \<circ> ?\<phi>)"
      using asm0 by presburger
    moreover have "fst \<circ> ?\<phi> = fst \<circ> \<phi>'"
      using ext r by fastforce
    then show "b (fst \<circ> \<phi>')"
      using calculation by presburger
  qed
qed

lemma rule_lframe_single:
  "\<Turnstile> { (\<lambda>S. \<forall>\<omega> \<in> S. P (fst \<omega>)) } C { \<lambda>S. \<forall>\<omega> \<in> S. P (fst \<omega>) }"
proof -
  let ?P = "\<lambda>\<phi>. P (\<phi> ())"
  have "\<Turnstile> { (\<lambda>S. \<forall>\<phi>. (\<forall>k. \<phi> k \<in> S) \<longrightarrow> ?P (fst \<circ> \<phi>)) } C { \<lambda>S. \<forall>\<phi>. (\<forall>k. \<phi> k \<in> S) \<longrightarrow> ?P (fst \<circ> \<phi>) }"
    using rule_lframe by fast
  moreover have "(\<lambda>S. \<forall>\<omega> \<in> S. P (fst \<omega>)) = (\<lambda>S. \<forall>\<phi>. (\<forall>k. \<phi> k \<in> S) \<longrightarrow> ?P (fst \<circ> \<phi>))"
    using ext by fastforce
  ultimately show ?thesis
    using forw_subst ssubst order_trans_rules(13) prop_subst basic_trans_rules(13)
    by fast
qed

definition differ_only_by_pset where
  "differ_only_by_pset vars a b \<longleftrightarrow> (\<forall>i. fst (a i) = fst (b i) \<and> differ_only_by_set vars (snd (a i)) (snd (b i)))"

lemma differ_only_by_psetI:
  assumes "\<And>i. fst (a i) = fst (b i) \<and> differ_only_by_set vars (snd (a i)) (snd (b i))"
  shows "differ_only_by_pset vars a b"
  by (simp add: assms differ_only_by_pset_def)

definition not_in_free_pvars_prop where
  "not_in_free_pvars_prop vars b \<longleftrightarrow> (\<forall>\<phi>1 \<phi>2. differ_only_by_pset vars \<phi>1 \<phi>2 \<longrightarrow> (b \<phi>1 \<longleftrightarrow> b \<phi>2))"

proposition rule_frame:

  fixes b :: "('a \<Rightarrow> ('lvar, 'lval, 'pvar, 'pval) state) \<Rightarrow> bool"
\<comment>\<open>b takes a mapping from keys to extended states (representing the tuple), and returns a boolean\<close>

  assumes "not_in_free_pvars_prop (written_vars C) b"

  shows "\<Turnstile> { (\<lambda>S. \<forall>\<phi>. (\<forall>k. \<phi> k \<in> S) \<longrightarrow> b \<phi>) } C { \<lambda>S. \<forall>\<phi>. (\<forall>k. \<phi> k \<in> S) \<longrightarrow> b \<phi> }"

proof (rule hyper_hoare_tripleI)
  fix S :: "('lvar, 'lval, 'pvar, 'pval) state set"
  assume asm0: "\<forall>\<phi>. (\<forall>k. \<phi> k \<in> S) \<longrightarrow> b \<phi>"
  show "\<forall>\<phi>. (\<forall>k. \<phi> k \<in> sem C S) \<longrightarrow> b \<phi>"
  proof (clarify)
    fix \<phi>' :: "'a \<Rightarrow> ('lvar, 'lval, 'pvar, 'pval) state"
    assume asm1: "\<forall>k. \<phi>' k \<in> sem C S"
    let ?\<phi> = "\<lambda>k. SOME \<phi>k. fst \<phi>k = fst (\<phi>' k) \<and> \<phi>k \<in> S \<and> single_sem C (snd \<phi>k) (snd (\<phi>' k))"
    have r: "\<And>k. fst (?\<phi> k) = fst (\<phi>' k) \<and> (?\<phi> k) \<in> S \<and> single_sem C (snd (?\<phi> k)) (snd (\<phi>' k))"
    proof -
      fix k show "fst (?\<phi> k) = fst (\<phi>' k) \<and> (?\<phi> k) \<in> S \<and> single_sem C (snd (?\<phi> k)) (snd (\<phi>' k))"
      proof (rule someI_ex)
        show "\<exists>x. fst x = fst (\<phi>' k) \<and> x \<in> S \<and> \<langle>C, snd x\<rangle> \<rightarrow> snd (\<phi>' k)"
          by (metis asm1 fst_conv in_sem snd_conv)
      qed
    qed
    then have "b ?\<phi>"
      using asm0 by presburger
    moreover have "differ_only_by_pset (written_vars C) ?\<phi> \<phi>'"
    proof (rule differ_only_by_psetI)
      fix i show "fst (SOME \<phi>k. fst \<phi>k = fst (\<phi>' i) \<and> \<phi>k \<in> S \<and> \<langle>C, snd \<phi>k\<rangle> \<rightarrow> snd (\<phi>' i)) = fst (\<phi>' i) \<and>
       differ_only_by_set (written_vars C) (snd (SOME \<phi>k. fst \<phi>k = fst (\<phi>' i) \<and> \<phi>k \<in> S \<and> \<langle>C, snd \<phi>k\<rangle> \<rightarrow> snd (\<phi>' i))) (snd (\<phi>' i))"
        by (metis (mono_tags, lifting) differ_only_by_set_def r written_vars_not_modified)
    qed
    ultimately show "b \<phi>'"
      using assms not_in_free_pvars_prop_def by blast
  qed
qed


subsection \<open>Logical Updates\<close>

definition equal_outside_set where
  "equal_outside_set vars l1 l2 \<longleftrightarrow> (\<forall>x. x \<notin> vars \<longrightarrow> l1 x = l2 x)"

lemma equal_outside_setI:
  assumes "\<And>x. x \<notin> vars \<Longrightarrow> l1 x = l2 x"
  shows "equal_outside_set vars l1 l2"
  using assms equal_outside_set_def by auto

lemma equal_outside_setE:
  assumes "equal_outside_set vars l1 l2"
      and "x \<notin> vars"
    shows "l1 x = l2 x"
  using assms equal_outside_set_def by meson

lemma equal_outside_sym:
  "equal_outside_set vars l l' \<longleftrightarrow> equal_outside_set vars l' l"
  by (metis equal_outside_set_def)

definition subset_mod_updates where
  "subset_mod_updates vars S S' \<longleftrightarrow> (\<forall>\<omega> \<in> S. \<exists>\<omega>' \<in> S'. snd \<omega> = snd \<omega>' \<and> equal_outside_set vars (fst \<omega>) (fst \<omega>'))"

lemma subset_mod_updatesI:
  assumes "\<And>\<omega>. \<omega> \<in> S \<Longrightarrow> (\<exists>\<omega>' \<in> S'. snd \<omega> = snd \<omega>' \<and> equal_outside_set vars (fst \<omega>) (fst \<omega>'))"
  shows "subset_mod_updates vars S S'"
  by (simp add: assms subset_mod_updates_def)

lemma subset_mod_updatesE:
  assumes "subset_mod_updates vars S S'"
      and "\<omega> \<in> S"
    shows "\<exists>\<omega>' \<in> S'. snd \<omega> = snd \<omega>' \<and> equal_outside_set vars (fst \<omega>) (fst \<omega>')"
  using assms(1) assms(2) subset_mod_updates_def by blast


definition same_mod_updates where
  "same_mod_updates vars S S' \<longleftrightarrow> subset_mod_updates vars S S' \<and> subset_mod_updates vars S' S"

lemma same_mod_updatesI:
  assumes "\<And>\<omega>. \<omega> \<in> S \<Longrightarrow> (\<exists>\<omega>' \<in> S'. snd \<omega> = snd \<omega>' \<and> equal_outside_set vars (fst \<omega>) (fst \<omega>'))"
      and "\<And>\<omega>'. \<omega>' \<in> S' \<Longrightarrow> (\<exists>\<omega> \<in> S. snd \<omega> = snd \<omega>' \<and> equal_outside_set vars (fst \<omega>') (fst \<omega>))"
    shows "same_mod_updates vars S S'"
  by (metis assms(1) assms(2) same_mod_updates_def subset_mod_updates_def)

lemma same_mod_updates_sym:
  "same_mod_updates vars S S' \<longleftrightarrow> same_mod_updates vars S' S"
  using same_mod_updates_def by blast

lemma same_mod_updates_refl:
  "same_mod_updates vars S S"
  by (metis equal_outside_set_def same_mod_updates_def subset_mod_updates_def)

lemma equal_outside_set_trans:
  assumes "equal_outside_set vars a b"
      and "equal_outside_set vars b c"
    shows "equal_outside_set vars a c"
  using equal_outside_set_def[of vars a b] equal_outside_set_def[of vars b c] equal_outside_set_def[of vars a c] assms
  by presburger

lemma subset_mod_updates_trans:
  assumes "subset_mod_updates vars S1 S2"
      and "subset_mod_updates vars S2 S3"
    shows "subset_mod_updates vars S1 S3"
proof (rule subset_mod_updatesI)
  fix \<omega>1 assume "\<omega>1 \<in> S1"
  then obtain \<omega>2 where "\<omega>2 \<in> S2" "snd \<omega>1 = snd \<omega>2 \<and> equal_outside_set vars (fst \<omega>1) (fst \<omega>2)"
    using assms(1) same_mod_updates_def subset_mod_updatesE by blast
  then show "\<exists>\<omega>'\<in>S3. snd \<omega>1 = snd \<omega>' \<and> equal_outside_set vars (fst \<omega>1) (fst \<omega>')"
    by (metis (no_types, lifting) assms(2) equal_outside_set_trans subset_mod_updatesE)
qed

lemma same_mod_updates_trans:
  assumes "same_mod_updates vars S1 S2"
      and "same_mod_updates vars S2 S3"
    shows "same_mod_updates vars S1 S3"
  by (meson assms(1) assms(2) same_mod_updates_def subset_mod_updates_trans)


lemma sem_update_commute_aux:
  assumes "subset_mod_updates vars S1 S2"
  shows "subset_mod_updates vars (sem C S1) (sem C S2)"
proof (rule subset_mod_updatesI)
  fix \<omega>1 assume asm0: "\<omega>1 \<in> sem C S1"
  then obtain l1 \<sigma> where "(l1, \<sigma>) \<in> S1" "single_sem C \<sigma> (snd \<omega>1)" "fst \<omega>1 = l1"
    by (metis in_sem)
  then obtain l2 where "(l2, \<sigma>) \<in> S2" "equal_outside_set vars l1 l2"
    using assms subset_mod_updatesE by fastforce
  then show "\<exists>\<omega>'\<in>sem C S2. snd \<omega>1 = snd \<omega>' \<and> equal_outside_set vars (fst \<omega>1) (fst \<omega>')"
    by (metis \<open>\<langle>C, \<sigma>\<rangle> \<rightarrow> snd \<omega>1\<close> \<open>fst \<omega>1 = l1\<close> fst_conv in_sem snd_conv)
qed


lemma sem_update_commute:
  assumes "same_mod_updates (vars :: 'a set) S1 S2"
  shows "same_mod_updates vars (sem C S1) (sem C S2)"
  using assms same_mod_updates_def sem_update_commute_aux by blast



type_synonym ('a, 'b, 'c, 'd) chyperassertion = "(('a \<Rightarrow> 'b) \<times> ('c \<Rightarrow> 'd)) set \<Rightarrow> bool"

definition invariant_on_updates :: "'a set \<Rightarrow> ('a, 'b, 'c, 'd) chyperassertion \<Rightarrow> bool" where
  "invariant_on_updates vars P \<longleftrightarrow> (\<forall>S S'. same_mod_updates vars S S' \<longrightarrow> (P S \<longleftrightarrow> P S'))"

lemma invariant_on_updatesI:
  assumes "\<And>S S'. same_mod_updates vars S S' \<Longrightarrow> P S \<Longrightarrow> P S'"
  shows "invariant_on_updates vars P"
  using assms invariant_on_updates_def same_mod_updates_sym by blast

definition entails_with_updates :: "'a set \<Rightarrow> ('a, 'b, 'c, 'd) chyperassertion \<Rightarrow> ('a, 'b, 'c, 'd) chyperassertion \<Rightarrow> bool"
  where
  "entails_with_updates vars P Q \<longleftrightarrow> (\<forall>S. P S \<longrightarrow> (\<exists>S'. same_mod_updates vars S S' \<and> Q S'))"

lemma entails_with_updatesI:
  assumes "\<And>S. P S \<Longrightarrow> (\<exists>S'. same_mod_updates vars S S' \<and> Q S')"
  shows "entails_with_updates vars P Q"
  by (simp add: assms entails_with_updates_def)


lemma entails_with_updatesE:
  assumes "entails_with_updates vars P Q"
      and "P S"
    shows "\<exists>S'. same_mod_updates vars S S' \<and> Q S'"
  by (meson assms(1) assms(2) entails_with_updates_def)


proposition rule_LUpdate:
  assumes "\<Turnstile> {P'} C {Q}"
      and "entails_with_updates vars P P'"
      and "invariant_on_updates vars Q"
    shows "\<Turnstile> {P} C {Q}"
proof (rule hyper_hoare_tripleI)
  fix S assume asm0: "P S"
  then obtain S' where "same_mod_updates vars S S' \<and> P' S'"
    using assms(2) entails_with_updatesE by blast
  then have "same_mod_updates vars (sem C S) (sem C S')"
    using sem_update_commute by blast
  moreover have "Q (sem C S')"
    using \<open>same_mod_updates vars S S' \<and> P' S'\<close> assms(1) hyper_hoare_tripleE by auto
  ultimately show "Q (sem C S)"
    using assms(3) invariant_on_updates_def by blast
qed




subsection \<open>Filters\<close>

lemma filter_prop_commute_aux:
  assumes "\<And>\<omega> \<omega>'. fst \<omega> = fst \<omega>' \<Longrightarrow> (f \<omega> \<longleftrightarrow> f \<omega>')"
  shows "Set.filter f (sem C S) = sem C (Set.filter f S)" (is "?A = ?B")
proof
  show "?A \<subseteq> ?B"
  proof
    fix \<omega>' assume "\<omega>' \<in> ?A"
    then obtain \<omega> where "\<omega> \<in> S" "single_sem C (snd \<omega>) (snd \<omega>')" "fst \<omega> = fst \<omega>'" "f \<omega>'"
      by (metis fst_conv in_sem member_filter snd_conv)
    then show "\<omega>' \<in> ?B"
      by (metis assms in_sem member_filter prod.collapse)
  qed
  show "?B \<subseteq> ?A"
  proof
    fix x assume "x \<in> sem C (Set.filter f S)"
    then show "x \<in> Set.filter f (sem C S)"
      by (metis assms fst_conv in_sem member_filter)
  qed
qed

definition commute_with_sem where
  "commute_with_sem f \<longleftrightarrow> (\<forall>S C. f (sem C S) = sem C (f S))"

lemma commute_with_semI:
  assumes "\<And>(S :: (('a \<Rightarrow> 'b) \<times> ('c \<Rightarrow> 'd)) set) C. f (sem C S) = sem C (f S)"
  shows "commute_with_sem f"
  by (simp add: assms commute_with_sem_def)

lemma filter_prop_commute:
  assumes "\<And>\<omega> \<omega>'. fst \<omega> = fst \<omega>' \<Longrightarrow> (f \<omega> \<longleftrightarrow> f \<omega>')"
  shows "commute_with_sem (Set.filter f)"
  using assms commute_with_sem_def filter_prop_commute_aux by blast

lemma rule_apply:
  assumes "\<Turnstile> {P} C {Q}"
      and "commute_with_sem f"
    shows "\<Turnstile> {P \<circ> f} C {Q \<circ> f}"
proof (rule hyper_hoare_tripleI)
  fix S assume "(P \<circ> f) S"
  then show "(Q \<circ> f) (sem C S)"
    by (metis assms(1) assms(2) commute_with_sem_def comp_apply hyper_hoare_tripleE)
qed

definition apply_filter where
  "apply_filter b P S \<longleftrightarrow> P (Set.filter b S)"

proposition rule_LFilter:
  assumes "\<Turnstile> {P} C {Q}"
  shows "\<Turnstile> { P \<circ> (Set.filter (b \<circ> fst)) } C { Q \<circ> (Set.filter (b \<circ> fst)) }"
  by (simp add: assms filter_prop_commute rule_apply)


definition differ_only_by_pset_single where
  "differ_only_by_pset_single vars a b \<longleftrightarrow> (fst a = fst b \<and> differ_only_by_set vars (snd a) (snd b))"

definition not_in_free_pvars_pexp where
  "not_in_free_pvars_pexp vars b \<longleftrightarrow> (\<forall>\<phi>1 \<phi>2. differ_only_by_set vars \<phi>1 \<phi>2 \<longrightarrow> (b \<phi>1 \<longleftrightarrow> b \<phi>2))"

lemma single_sem_differ_by_written_vars:
  assumes "single_sem C \<phi> \<phi>'"
  shows "differ_only_by_set (written_vars C) \<phi> \<phi>'"
  by (meson assms differ_only_by_set_def written_vars_not_modified)

lemma single_sem_not_free_vars:
  assumes "not_in_free_pvars_pexp (written_vars C) b"
      and "single_sem C \<phi> \<phi>'"
    shows "b \<phi> \<longleftrightarrow> b \<phi>'"
  using assms(1) assms(2) not_in_free_pvars_pexp_def single_sem_differ_by_written_vars by blast


proposition rule_PFilter:
  assumes "\<Turnstile> {P} C {Q}"
      and "not_in_free_pvars_pexp (written_vars C) b"
  shows "\<Turnstile> { P \<circ> (Set.filter (b \<circ> snd)) } C { Q \<circ> (Set.filter (b \<circ> snd)) }"
proof (rule hyper_hoare_tripleI)
  fix S assume asm0: "(P \<circ> Set.filter (b \<circ> snd)) S"
  let ?S = "Set.filter (b \<circ> snd) S"
  have "Q (sem C ?S)"
    using asm0 assms(1) hyper_hoare_tripleE by auto
  moreover have "sem C ?S = Set.filter (b \<circ> snd) (sem C S)" (is "?A = ?B")
  proof
    show "?B \<subseteq> ?A"
    proof
      fix \<phi>' assume "\<phi>' \<in> Set.filter (b \<circ> snd) (sem C S)"
      then obtain \<phi> where "\<phi> \<in> S" "fst \<phi> = fst \<phi>'" "single_sem C (snd \<phi>) (snd \<phi>')" "b (snd \<phi>')"
        by (metis comp_apply fst_conv in_sem member_filter snd_conv)
      then have "b (snd \<phi>)"
        using single_sem_not_free_vars[of C b "snd \<phi>" "snd \<phi>'"] assms(2)
        by simp
      then show "\<phi>' \<in> ?A"
        by (metis \<open>\<langle>C, snd \<phi>\<rangle> \<rightarrow> snd \<phi>'\<close> \<open>\<phi> \<in> S\<close> \<open>fst \<phi> = fst \<phi>'\<close> comp_apply in_sem member_filter prod.collapse)
    qed
    show "?A \<subseteq> ?B"
    proof
      fix \<phi>' assume "\<phi>' \<in> sem C (Set.filter (b \<circ> snd) S)"
      then obtain \<phi> where "\<phi> \<in> S" "fst \<phi> = fst \<phi>'" "single_sem C (snd \<phi>) (snd \<phi>')" "b (snd \<phi>)"
        by (metis (mono_tags, lifting) comp_apply fst_conv in_sem member_filter snd_conv)
      then have "b (snd \<phi>')"
        using assms(2) single_sem_not_free_vars by blast
      then show "\<phi>' \<in> ?B"
        by (metis \<open>\<langle>C, snd \<phi>\<rangle> \<rightarrow> snd \<phi>'\<close> \<open>\<phi> \<in> S\<close> \<open>fst \<phi> = fst \<phi>'\<close> comp_apply member_filter prod.collapse single_step_then_in_sem)
    qed
  qed
  ultimately show "(Q \<circ> Set.filter (b \<circ> snd)) (sem C S)"
    by auto
qed




subsection \<open>Other Compositionality Rules\<close>

proposition rule_False:
  "hyper_hoare_triple (\<lambda>_. False) C Q"
  by (simp add: hyper_hoare_triple_def)

proposition rule_True:
  "hyper_hoare_triple P C (\<lambda>_. True)"
  by (simp add: hyper_hoare_triple_def)


(* Other direction does not hold! *)
lemma sem_inter:
  "sem C (S1 \<inter> S2) \<subseteq> sem C S1 \<inter> sem C S2"
  by (simp add: sem_monotonic)


proposition rule_Union:
  assumes "\<Turnstile> {P} C {Q}"
      and "hyper_hoare_triple P' C Q'"
    shows "hyper_hoare_triple (join P P') C (join Q Q')"
proof (rule hyper_hoare_tripleI)
  fix S assume asm0: "join P P' S"
  then obtain S1 S2 where "S = S1 \<union> S2" "P S1" "P' S2"
    by (metis join_def)
  then have "sem C S = sem C S1 \<union> sem C S2"
    using sem_union by auto
  then show "join Q Q' (sem C S)"
    by (metis \<open>P S1\<close> \<open>P' S2\<close> assms(1) assms(2) hyper_hoare_tripleE join_def)
qed

proposition rule_IndexedUnion:
  assumes "\<And>x. \<Turnstile> {P x} C {Q x}"
  shows "hyper_hoare_triple (general_join P) C (general_join Q)"
proof (rule hyper_hoare_tripleI)
  fix S assume "general_join P S"
  then obtain F where asm0: "S = (\<Union>x. F x)" "\<And>x. P x (F x)"
    by (meson general_join_def)
  have "sem C S = (\<Union>x. sem C (F x))"
    by (simp add: asm0(1) sem_split_general)
  moreover have "\<And>x. Q x (sem C (F x))"
    using asm0(2) assms hyper_hoare_tripleE by blast
  ultimately show "general_join Q (sem C S)"
    by (metis general_join_def)
qed

proposition rule_And:
  assumes "\<Turnstile> {P} C {Q}"
      and "hyper_hoare_triple P' C Q'"
    shows "hyper_hoare_triple (conj P P') C (conj Q Q')"
proof (rule hyper_hoare_tripleI)
  fix S assume "Logic.conj P P' S"
  then show "Logic.conj Q Q' (sem C S)"
    by (metis assms(1) assms(2) conj_def hyper_hoare_tripleE)
qed

lemma rule_Forall:
  assumes "\<And>x. \<Turnstile> {P x} C {Q x}"
  shows "hyper_hoare_triple (forall P) C (forall Q)"
  by (metis assms forall_def hyper_hoare_triple_def)

lemma rule_Or:
  assumes "\<Turnstile> {P} C {Q}"
      and "\<Turnstile> {P'} C {Q'}"
    shows "hyper_hoare_triple (disj P P') C (disj Q Q')"
  by (metis assms(1) assms(2) disj_def hyper_hoare_triple_def)

corollary variant_if_rule:
  assumes "hyper_hoare_triple P C1 Q"
      and "hyper_hoare_triple P C2 Q"
      and "closed_by_union Q"
    shows "hyper_hoare_triple P (If C1 C2) Q"
  by (metis assms(1) assms(2) assms(3) if_rule join_closed_by_union)


text \<open>Simplifying the rule\<close>

definition stable_by_infinite_union :: "'a hyperassertion \<Rightarrow> bool" where
  "stable_by_infinite_union I \<longleftrightarrow> (\<forall>F. (\<forall>S \<in> F. I S) \<longrightarrow> I (\<Union>S \<in> F. S))"

lemma stable_by_infinite_unionE:
  assumes "stable_by_infinite_union I"
      and "\<And>S. S \<in> F \<Longrightarrow> I S"
    shows "I (\<Union>S \<in> F. S)"
  using assms(1) assms(2) stable_by_infinite_union_def by blast

lemma stable_by_union_and_constant_then_I:
  assumes "\<And>n. I n = I'"
      and "stable_by_infinite_union I'"
    shows "natural_partition I = I'"
proof (rule ext)
  fix S show "natural_partition I S = I' S"
  proof
    show "I' S \<Longrightarrow> natural_partition I S"
    proof -
      assume "I' S"
      show "natural_partition I S"
      proof (rule natural_partitionI)
        show "S = \<Union> (range (\<lambda>n. S))"
          by simp
        fix n show "I n S"
          by (simp add: \<open>I' S\<close> assms(1))
      qed
    qed
    assume asm0: "natural_partition I S"
    then obtain F where "S = (\<Union>n. F n)" "\<And>n. I n (F n)"
      using natural_partitionE by blast
    let ?F = "{F n |n. True}"
    have "I' (\<Union>S\<in>?F. S)"
      using assms(2)
    proof (rule stable_by_infinite_unionE[of I'])
      fix S assume "S \<in> {F n |n. True}"
      then show "I' S"
        using \<open>\<And>n. I n (F n)\<close> assms(1) by force
    qed
    moreover have "(\<Union>S\<in>?F. S) = S"
      using \<open>S = (\<Union>n. F n)\<close> by auto
    ultimately show "I' S" by blast
  qed
qed

corollary simpler_rule_while:
  assumes "hyper_hoare_triple I C I"
    and "stable_by_infinite_union I"
  shows "hyper_hoare_triple I (While C) I"
proof -
  let ?I = "\<lambda>n. I"
  have "hyper_hoare_triple (?I 0) (While C) (natural_partition ?I)"
    using while_rule[of ?I C]
    by (simp add: assms(1) assms(2) stable_by_union_and_constant_then_I)
  then show ?thesis
    by (simp add: assms(2) stable_by_union_and_constant_then_I)
qed


lemma rule_and3:
  assumes "\<Turnstile> {P1} C {Q1}"
      and "\<Turnstile> {P2} C {Q2}"
      and "\<Turnstile> {P3} C {Q3}"
    shows "\<Turnstile> { conj P1 (conj P2 P3) } C { conj Q1 (conj Q2 Q3) }"
  by (simp add: assms(1) assms(2) assms(3) rule_And)

definition not_empty where
  "not_empty S \<longleftrightarrow> S \<noteq> {}"

definition finite_not_empty where
  "finite_not_empty S \<longleftrightarrow> S \<noteq> {} \<and> finite S"

definition update_logical where
  "update_logical \<omega> i v = ((fst \<omega>)(i := v), snd \<omega>)"


lemma single_sem_prop:
  assumes "single_sem C (snd \<omega>) (snd \<omega>')"
      and "fst \<omega> = fst \<omega>'"
  shows "\<Turnstile> { (\<lambda>S. \<omega> \<in> S) } C { (\<lambda>S. \<omega>' \<in> S) }"
  by (metis assms(1) assms(2) hyper_hoare_tripleI in_sem prod.collapse)

lemma weaker_linking_rule:
  assumes "\<And>l \<sigma> \<sigma>'. \<Turnstile> { (\<lambda>S. (l, \<sigma>) \<in> S) } C { (\<lambda>S. (l, \<sigma>') \<in> S) } \<Longrightarrow> ( \<Turnstile> { P (l, \<sigma>) } C { Q (l, \<sigma>') } )"
  shows "\<Turnstile> { (\<lambda>S. \<forall>\<omega> \<in> S. P \<omega> S) } C { (\<lambda>S. \<forall>\<omega>' \<in> S. Q \<omega>' S) }"
  by (simp add: assms rule_linking_alt single_sem_prop)


definition general_union :: "'a hyperassertion \<Rightarrow> 'a hyperassertion" where
  "general_union P S \<longleftrightarrow> (\<exists>F. S = Union F \<and> (\<forall>S' \<in> F. P S'))"

lemma general_unionI:
  assumes "S = Union F"
      and "\<And>S'. S' \<in> F \<Longrightarrow> P S'"
    shows "general_union P S"
  using assms(1) assms(2) general_union_def by blast

lemma general_unionE:
  assumes "general_union P S"
  obtains F where "S = Union F" "\<And>S'. S' \<in> F \<Longrightarrow> P S'"
  by (metis assms general_union_def)


(* Derived *)
proposition rule_BigUnion:
  fixes P :: "((('a \<Rightarrow> 'b) \<times> ('c \<Rightarrow> 'd)) set \<Rightarrow> bool)"
  assumes "\<Turnstile> {P} C {Q}"
  shows "\<Turnstile> {general_union P} C {general_union Q}"
proof (rule consequence_rule)
  define PP :: "(('a \<Rightarrow> 'b) \<times> ('c \<Rightarrow> 'd)) set \<Rightarrow> (('a \<Rightarrow> 'b) \<times> ('c \<Rightarrow> 'd)) set \<Rightarrow> bool" where
  "PP = (\<lambda>_. P)"
  let ?P = "disj (general_join PP) (\<lambda>S. S = {})"
  show "entails (general_union P) ?P"
  proof (rule entailsI)
    fix S assume "general_union P S"
    then obtain F where "S = Union F" "\<And>S'. S' \<in> F \<Longrightarrow> P S'"
      by (metis general_union_def)
    have "general_join PP S \<or> S = {}"
    proof (cases "S = {}")
      case True
      then show ?thesis
        by simp
    next
      case False
      then obtain S' where "S' \<in> F"
        using \<open>S = \<Union> F\<close> by blast
      let ?F = "\<lambda>SS. if SS \<in> F then SS else S'"
      have "general_join PP S"
      proof (rule general_joinI)
        fix x show "PP x (?F x)"
          by (simp add: PP_def \<open>S' \<in> F\<close> \<open>\<And>S'. S' \<in> F \<Longrightarrow> P S'\<close>)
      next
        show "S = (\<Union>x. if x \<in> F then x else S')"
          using \<open>S = \<Union> F\<close> \<open>S' \<in> F\<close> by force
      qed
      then show ?thesis by simp
    qed
    then show "disj (general_join PP) (\<lambda>S. S = {}) S"
      by (simp add: disj_def)
  qed

  define QQ :: "(('a \<Rightarrow> 'b) \<times> ('c \<Rightarrow> 'd)) set \<Rightarrow> (('a \<Rightarrow> 'b) \<times> ('c \<Rightarrow> 'd)) set \<Rightarrow> bool" where
  "QQ = (\<lambda>_. Q)"
  let ?Q = "disj (general_join QQ) (\<lambda>S. S = {})"

  show "\<Turnstile> {Logic.disj (general_join PP) (\<lambda>S. S = {})} C {?Q}"
  proof (rule rule_Or)
    show "\<Turnstile> {(\<lambda>S. S = {})} C {\<lambda>S. S = {}}"
      by (metis (mono_tags, lifting) empty_iff equals0I hyper_hoare_triple_def in_sem)
        (* TODO: Prove this rule *)
    show "\<Turnstile> {general_join PP} C {general_join QQ}"
    proof (rule rule_IndexedUnion)
      fix x show "\<Turnstile> {PP x} C {QQ x}"
        by (simp add: PP_def QQ_def assms)
    qed
  qed
  show "entails (Logic.disj (general_join QQ) (\<lambda>S. S = {})) (general_union Q)"
  proof (rule entailsI)
    fix S assume "Logic.disj (general_join QQ) (\<lambda>S. S = {}) S"
    then show "general_union Q S"
    proof (cases "S = {}")
      case True
      then show ?thesis
        using general_union_def by auto
    next
      case False
      then obtain F where "\<And>x. QQ x (F x)" "S = \<Union> (range F)"
        by (metis (mono_tags, lifting) \<open>Logic.disj (general_join QQ) (\<lambda>S. S = {}) S\<close> disj_def general_join_def)
      then show ?thesis
        by (metis QQ_def general_unionI rangeE)
    qed
  qed
qed



proposition rule_Empty:
  "\<Turnstile> { (\<lambda>S. S = {}) } C { (\<lambda>S. S = {}) }"
proof (rule consequence_rule)
  let ?P = "general_union (\<lambda>_. False)"
  show "entails (\<lambda>S. S = {}) ?P"
    by (metis (full_types) Union_empty empty_iff entailsI general_unionI)
  show "entails ?P (\<lambda>S. S = {})"
    using entailsI[of ?P "\<lambda>S. S = {}"] general_union_def Sup_bot_conv(2) by metis
  show "\<Turnstile> {general_union (\<lambda>_. False)} C {general_union (\<lambda>_. False)}"
  proof (rule rule_BigUnion)
    show "\<Turnstile> {(\<lambda>_. False)} C {\<lambda>_. False}"
      using rule_False by auto
  qed
qed

definition has_subset where
  "has_subset P S \<longleftrightarrow> (\<exists>S'. S' \<subseteq> S \<and> P S')"

lemma has_subset_join_same:
  "entails (has_subset P) (join P (\<lambda>_. True))"
  "entails (join P (\<lambda>_. True)) (has_subset P)"
  using entailsI[of "has_subset P" "join P (\<lambda>_. True)"] has_subset_def join_def sup.absorb_iff2
   apply metis
  using UnCI entails_def[of "join P (\<lambda>_. True)" "has_subset P"] has_subset_def join_def subset_eq
  by metis


(* derived from join *)
proposition rule_AtLeast:
  assumes "\<Turnstile> {P} C {Q}"
  shows "\<Turnstile> {has_subset P} C {has_subset Q}"
proof (rule consequence_rule)
  let ?P = "join P (\<lambda>_. True)"
  let ?Q = "join Q (\<lambda>_. True)"
  show "\<Turnstile> {?P} C {?Q}"
    by (simp add: assms rule_True rule_Union)
qed (auto simp add: has_subset_join_same)

definition has_superset where
  "has_superset P S \<longleftrightarrow> (\<exists>S'. S \<subseteq> S' \<and> P S')"

proposition rule_AtMost:
  assumes "\<Turnstile> {P} C {Q}"
  shows "\<Turnstile> {has_superset P} C {has_superset Q}"
proof (rule hyper_hoare_tripleI)
  fix S :: "(('a \<Rightarrow> 'b) \<times> ('c \<Rightarrow> 'd)) set"
  assume "has_superset P S"
  then obtain S' where "S \<subseteq> S'" "P S'"
    by (meson has_superset_def)
  then have "Q (sem C S')"
    using assms hyper_hoare_tripleE by blast
  then show "has_superset Q (sem C S)"
    by (meson \<open>S \<subseteq> S'\<close> has_superset_def sem_monotonic)
qed




subsection \<open>Synchronous Reasoning (Proposition 14, Appendix H).\<close>

theorem if_sync_rule:
  assumes "\<Turnstile> {P} C1 {P1}"
      and "\<Turnstile> {P} C2 {P2}"
      and "\<Turnstile> {combine from_nat x P1 P2} C {combine from_nat x R1 R2}"
      and "\<Turnstile> {R1} C1' {Q1}"
      and "\<Turnstile> {R2} C2' {Q2}"

      and "not_free_var_hyper x P1"
      and "not_free_var_hyper x P2"
      and "from_nat 1 \<noteq> from_nat 2"

      and "not_free_var_hyper x R1"
      and "not_free_var_hyper x R2"

    shows "\<Turnstile> {P} If (Seq C1 (Seq C C1')) (Seq C2 (Seq C C2')) {join Q1 Q2}"
proof (rule hyper_hoare_tripleI)
  fix S assume asm0: "P S"
  have r0: "sem (stmt.If (Seq C1 (Seq C C1')) (Seq C2 (Seq C C2'))) S
  = sem C1' (sem C (sem C1 S)) \<union> sem C2' (sem C (sem C2 S))"
    by (simp add: sem_if sem_seq)
  moreover have "P1 (sem C1 S) \<and> P2 (sem C2 S)"
    using asm0 assms(1) assms(2) hyper_hoare_tripleE by blast

  let ?S1 = "(modify_lvar_to x (from_nat 1)) ` (sem C1 S)"
  let ?S2 = "(modify_lvar_to x (from_nat 2)) ` (sem C2 S)"
  let ?f1 = "Set.filter (\<lambda>\<phi>. fst \<phi> x = from_nat 1)"
  let ?f2 = "Set.filter (\<lambda>\<phi>. fst \<phi> x = from_nat 2)"

  have "P1 ?S1 \<and> P2 ?S2"
    by (meson \<open>P1 (sem C1 S) \<and> P2 (sem C2 S)\<close> assms(6) assms(7) not_free_var_hyper_def)
  moreover have rr1: "Set.filter (\<lambda>\<phi>. fst \<phi> x = from_nat 1) (?S1 \<union> ?S2) = ?S1"
    using injective_then_ok[of "from_nat 1" "from_nat 2" ?S1 x]
    by (metis (no_types, lifting) assms(8))
  moreover have rr2: "Set.filter (\<lambda>\<phi>. fst \<phi> x = from_nat 2) (?S1 \<union> ?S2) = ?S2"
    using injective_then_ok[of "from_nat 2" "from_nat 1" ?S2 x]
    by (metis (no_types, lifting) assms(8) sup_commute)
  ultimately have "combine from_nat x P1 P2 (?S1 \<union> ?S2)"
    by (metis combineI)
  then have "combine from_nat x R1 R2 (sem C (?S1 \<union> ?S2))"
    using assms(3) hyper_hoare_tripleE by blast
  moreover have "?f1 (sem C (?S1 \<union> ?S2)) = sem C ?S1"
    using recover_after_sem[of "from_nat 1" "from_nat 2" ?S1 x ?S2] assms(8) rr1 rr2
      member_filter[of _ "\<lambda>\<phi>. fst \<phi> x = from_nat 1"] member_filter[of _ "\<lambda>\<phi>. fst \<phi> x = from_nat 2"]
    by metis
  then have "R1 (sem C ?S1)"
    by (metis (mono_tags) calculation combine_def)
  then have "R1 (sem C (sem C1 S))"
    by (metis assms(9) not_free_var_hyper_def sem_of_modify_lvar)
  moreover have "?f2 (sem C (?S1 \<union> ?S2)) = sem C ?S2"
    using recover_after_sem[of "from_nat 2" "from_nat 1" ?S2 x ?S1] assms(8) rr1 rr2 sup_commute[of ]
      member_filter[of _ "\<lambda>\<phi>. fst \<phi> x = from_nat 1" "?S1 \<union> ?S2"] member_filter[of _ "\<lambda>\<phi>. fst \<phi> x = from_nat 2" "?S1 \<union> ?S2"]
    by metis
  then have "R2 (sem C ?S2)"
    by (metis (mono_tags) calculation(1) combine_def)
  then have "R2 (sem C (sem C2 S))"
    by (metis assms(10) not_free_var_hyper_def sem_of_modify_lvar)

  then show "join Q1 Q2 (sem (stmt.If (Seq C1 (Seq C C1')) (Seq C2 (Seq C C2'))) S)"
    by (metis (full_types) r0 assms(4) assms(5) calculation(2) hyper_hoare_tripleE join_def)
qed


definition update_lvar_set where
  "update_lvar_set u e S = { ((fst \<phi>')(u := e \<phi>'), snd \<phi>') |\<phi>'. \<phi>' \<in> S}"

lemma equal_outside_set_helper:
  "equal_outside_set {u} (fst \<phi>) (fst ((fst \<phi>)(u := x), snd \<phi>))"
  by (simp add: equal_outside_set_def)

lemma same_update_lvar_set:
  "same_mod_updates {u} S (update_lvar_set u e S)"
proof (rule same_mod_updatesI)
  show "\<And>\<omega>'. \<omega>' \<in> update_lvar_set u e S \<Longrightarrow> \<exists>\<omega>\<in>S. snd \<omega> = snd \<omega>' \<and> equal_outside_set {u} (fst \<omega>') (fst \<omega>)"
  proof -
    fix \<omega>' assume "\<omega>' \<in> update_lvar_set u e S"
    then obtain \<phi>' where "\<omega>' = ((fst \<phi>')(u := e \<phi>'), snd \<phi>')" "\<phi>' \<in> S"
      using mem_Collect_eq update_lvar_set_def[of u e S] by auto
    then show "\<exists>\<omega>\<in>S. snd \<omega> = snd \<omega>' \<and> equal_outside_set {u} (fst \<omega>') (fst \<omega>)"
      by (meson equal_outside_set_helper equal_outside_sym snd_eqD)
  qed
  show "\<And>\<omega>. \<omega> \<in> S \<Longrightarrow> \<exists>\<omega>'\<in>update_lvar_set u e S. snd \<omega> = snd \<omega>' \<and> equal_outside_set {u} (fst \<omega>) (fst \<omega>')"
    by (metis (mono_tags, lifting) equal_outside_set_helper mem_Collect_eq snd_conv update_lvar_set_def)
qed


lemma same_mod_updates_empty:
  assumes "same_mod_updates vars {} S'"
  shows "S' = {}"
  by (meson assms equals0D equals0I same_mod_updates_def subset_mod_updatesE)

definition not_fv_hyper where
  "not_fv_hyper t A \<longleftrightarrow> (\<forall>S S'. same_mod_updates {t} S S' \<and> A S \<longrightarrow> A S')"

lemma not_fv_hyperE:
  assumes "not_fv_hyper e I"
      and "same_mod_updates {e} S S'"
      and "I S"
    shows "I S'"
  by (meson assms(1) assms(2) assms(3) not_fv_hyper_def)

definition assign_exp_to_lvar where
  "assign_exp_to_lvar e l \<phi> = ((fst \<phi>)(l := e (snd \<phi>)), snd \<phi>)"

definition assign_exp_to_lvar_set where
  "assign_exp_to_lvar_set e l S = assign_exp_to_lvar e l ` S"

lemma same_outside_set_lvar_assign_exp:
  "snd \<phi> = snd (assign_exp_to_lvar e l \<phi>) \<and> equal_outside_set {l} (fst \<phi>) (fst (assign_exp_to_lvar e l \<phi>))"
  by (simp add: assign_exp_to_lvar_def equal_outside_set_def)


lemma assign_exp_to_lvar_set_same_mod_updates:
  "same_mod_updates {l} S (assign_exp_to_lvar_set e l S)"
proof (rule same_mod_updatesI)
  show "\<And>\<omega>. \<omega> \<in> S \<Longrightarrow> \<exists>\<omega>'\<in>assign_exp_to_lvar_set e l S. snd \<omega> = snd \<omega>' \<and> equal_outside_set {l} (fst \<omega>) (fst \<omega>')"
    by (metis assign_exp_to_lvar_set_def rev_image_eqI same_outside_set_lvar_assign_exp)
  show "\<And>\<omega>'. \<omega>' \<in> assign_exp_to_lvar_set e l S \<Longrightarrow> \<exists>\<omega>\<in>S. snd \<omega> = snd \<omega>' \<and> equal_outside_set {l} (fst \<omega>') (fst \<omega>)"
    by (metis (mono_tags, opaque_lifting) assign_exp_to_lvar_set_def equal_outside_sym imageE same_outside_set_lvar_assign_exp)
qed


lemma holds_forall_same_mod_updates:
  assumes "same_mod_updates vars S S'"
      and "holds_forall b S"
    shows "holds_forall b S'"
proof (rule holds_forallI)
  fix \<phi>' assume asm0: "\<phi>' \<in> S'"
  then obtain \<phi> where "\<phi> \<in> S" "snd \<phi> = snd \<phi>'"
    by (metis assms(1) same_mod_updates_def subset_mod_updatesE)
  then show "b (snd \<phi>')"
    by (metis assms(2) holds_forall_def)
qed

lemma not_fv_hyper_assign_exp:
  assumes "not_fv_hyper t A"
  shows "A S \<longleftrightarrow> A (assign_exp_to_lvar_set e t S)"
  by (metis assign_exp_to_lvar_set_same_mod_updates assms not_fv_hyper_def same_mod_updates_sym)

lemma holds_forall_same_assign_lvar:
  "holds_forall b S \<longleftrightarrow> holds_forall b (assign_exp_to_lvar_set e l S)" (is "?A \<longleftrightarrow> ?B")
proof
  show "?A \<Longrightarrow> ?B"
    by (simp add: assign_exp_to_lvar_def assign_exp_to_lvar_set_def holds_forall_def)
  show "?B \<Longrightarrow> ?A"
    by (simp add: assign_exp_to_lvar_def assign_exp_to_lvar_set_def holds_forall_def)
qed

definition e_recorded_in_t where
  "e_recorded_in_t e t S \<longleftrightarrow> (\<forall>\<phi>\<in>S. fst \<phi> t = e (snd \<phi>))"

lemma e_recorded_in_tI:
  assumes "\<And>\<phi>. \<phi>\<in>S \<Longrightarrow> fst \<phi> t = e (snd \<phi>)"
  shows "e_recorded_in_t e t S"
  by (simp add: assms e_recorded_in_t_def)

definition e_smaller_than_t where
  "e_smaller_than_t e t lt S \<longleftrightarrow> (\<forall>\<phi>\<in>S. lt (e (snd \<phi>)) (fst \<phi> t))"


lemma low_expI:
  assumes "\<And>\<phi> \<phi>'. \<phi> \<in> S \<and> \<phi>' \<in> S \<Longrightarrow> (e (snd \<phi>) = e (snd \<phi>'))"
  shows "low_exp e S"
  using low_exp_def assms by blast

lemma low_exp_forall_same_mod_updates:
  assumes "same_mod_updates vars S S'"
      and "low_exp b S"
    shows "low_exp b S'"
proof (rule low_expI)
  fix \<phi>' \<phi>'' assume asm0: "\<phi>' \<in> S' \<and> \<phi>'' \<in> S'"
  then obtain \<phi> where "\<phi> \<in> S" "snd \<phi> = snd \<phi>'"
    by (metis assms(1) same_mod_updates_def subset_mod_updatesE)
  then show "b (snd \<phi>') = b (snd \<phi>'')"
    using asm0 assms(1) assms(2) low_exp_def[of b S] same_mod_updates_def[of vars S S'] subset_mod_updatesE
    by metis
qed

lemma e_recorded_in_t_if_assigned:
  "e_recorded_in_t e t (assign_exp_to_lvar_set e t S)"
  by (simp add: assign_exp_to_lvar_def assign_exp_to_lvar_set_def e_recorded_in_t_def)

lemma low_exp_commute_assign_lvar:
  "low_exp b (assign_exp_to_lvar_set e t S) \<longleftrightarrow> low_exp b S" (is "?A \<longleftrightarrow> ?B")
proof
  assume ?A
  then show ?B
    by (meson assign_exp_to_lvar_set_same_mod_updates low_exp_forall_same_mod_updates same_mod_updates_sym)
next
  assume ?B
  then show ?A
    by (meson assign_exp_to_lvar_set_same_mod_updates low_exp_forall_same_mod_updates)
qed

end