theory TotalLogic
  imports Loops Compositionality SyntacticAssertions
begin

section \<open>Terminating Hyper-Triples\<close>

definition total_hyper_triple ("\<Turnstile>TERM {_} _ {_}" [51,0,0] 81) where
  "\<Turnstile>TERM {P} C {Q} \<longleftrightarrow> ( \<Turnstile> {P} C {Q} \<and> (\<forall>S. P S \<longrightarrow> (\<forall>\<phi> \<in> S. \<exists>\<sigma>'. single_sem C (snd \<phi>) \<sigma>' )))"

lemma total_hyper_triple_equiv:
  "\<Turnstile>TERM {P} C {Q} \<longleftrightarrow> ( \<Turnstile> {P} C {Q} \<and> (\<forall>S. P S \<longrightarrow> (\<forall>\<phi> \<in> S. \<exists>\<sigma>'. (fst \<phi>, \<sigma>') \<in> sem C S \<and> single_sem C (snd \<phi>) \<sigma>' )))"
  by (metis prod.collapse single_step_then_in_sem total_hyper_triple_def)

lemma total_hyper_tripleI:
  assumes "\<Turnstile> {P} C {Q}"
      and "\<And>\<phi> S. P S \<and> \<phi> \<in> S \<Longrightarrow> (\<exists>\<sigma>'. single_sem C (snd \<phi>) \<sigma>' )"
    shows "\<Turnstile>TERM {P} C {Q}"
  by (simp add: assms(1) assms(2) total_hyper_triple_def)

definition terminates_in where
  "terminates_in C S \<longleftrightarrow> (\<forall>\<phi> \<in> S. \<exists>\<sigma>'. single_sem C (snd \<phi>) \<sigma>')"

lemma terminates_inI:
  assumes "\<And>\<phi>. \<phi> \<in> S \<Longrightarrow> \<exists>\<sigma>'. single_sem C (snd \<phi>) \<sigma>'"
  shows "terminates_in C S"
  using assms terminates_in_def by blast

lemma iterate_sem_mono:
  assumes "S \<subseteq> S'"
  shows "iterate_sem n C S \<subseteq> iterate_sem n C S'"
  using assms
  by (induct n arbitrary: S S') (simp_all add: sem_monotonic)

lemma terminates_in_while_loop:
  assumes "wfP lt"
      and "\<And>\<phi> n. \<phi> \<in> iterate_sem n (Assume b;; C) S \<and> b (snd \<phi>) \<Longrightarrow> (\<exists>\<sigma>'. single_sem C (snd \<phi>) \<sigma>' \<and> (\<not> b \<sigma>' \<or> lt (e \<sigma>') (e (snd \<phi>))))"
  shows "terminates_in (while_cond b C) S"
proof (rule terminates_inI)
  fix \<phi> assume asm0: "\<phi> \<in> S"
  let ?S = "{\<phi>}"
  let ?R = "{(x, y). lt x y}"
  let ?Q = "{ e (snd \<phi>) |\<phi> n. b (snd \<phi>) \<and> \<phi> \<in> iterate_sem n (Assume b;; C) ?S}"

  show "\<exists>\<sigma>'. \<langle>while_cond b C, snd \<phi>\<rangle> \<rightarrow> \<sigma>'"
  proof (cases "b (snd \<phi>)")
    case False
    then show ?thesis
      by (metis SemAssume SemSeq SemWhileExit lnot_def while_cond_def)
  next
    case True
    show ?thesis
    proof (rule wfE_min)
      show "wf ?R"
        using assms(1) wfP_def by blast
      show "e (snd \<phi>) \<in> ?Q"
        using True asm0 iterate_sem.simps(1) by fastforce
      fix z assume asm1: "z \<in> ?Q" "(\<And>y. (y, z) \<in> {(x, y). lt x y} \<Longrightarrow> y \<notin> ?Q)"
      then obtain \<phi>' n where "z = e (snd \<phi>')" "b (snd \<phi>')" "\<phi>' \<in> iterate_sem n (Assume b;; C) ?S"
        by blast
      then obtain \<sigma>' where "single_sem C (snd \<phi>') \<sigma>' \<and> (\<not> b \<sigma>' \<or> lt (e \<sigma>') (e (snd \<phi>')))"
        using assms(2) iterate_sem_mono[of ?S S n "Assume b;; C"]
        by (meson asm0 empty_subsetI in_mono insert_subsetI)
      then have "\<not> b \<sigma>' \<or> e \<sigma>' \<notin> ?Q"
        using \<open>z = e (snd \<phi>')\<close> asm1(2) by blast
      moreover have "(fst \<phi>', \<sigma>') \<in> sem (Assume b;; C) (iterate_sem n (Assume b;; C) ?S)"
        by (metis (no_types, opaque_lifting) SemAssume SemSeq \<open>(\<langle>C, snd \<phi>'\<rangle> \<rightarrow> \<sigma>') \<and> (\<not> b \<sigma>' \<or> lt (e \<sigma>') (e (snd \<phi>')))\<close> \<open>\<phi>' \<in> iterate_sem n (Assume b ;; C) ?S\<close> \<open>b (snd \<phi>')\<close> single_step_then_in_sem surjective_pairing)
      ultimately have "\<not> b \<sigma>'"
        using iterate_sem.simps(2)[of n "Assume b;; C" "{\<phi>}"] mem_Collect_eq snd_conv
        by (metis (mono_tags, lifting))
      then have "(fst \<phi>', \<sigma>') \<in> iterate_sem (Suc n) (Assume b;; C) ?S"
        by (simp add: \<open>(fst \<phi>', \<sigma>') \<in> sem (Assume b ;; C) (iterate_sem n (Assume b ;; C) ?S)\<close>)
      then have "(fst \<phi>', \<sigma>') \<in> (\<Union>n. iterate_sem n (Assume b;; C) ?S)" by blast
      then have "(fst \<phi>', \<sigma>') \<in> filter_exp (lnot b) (\<Union>n. iterate_sem n (Assume b;; C) ?S)"
        using filter_exp_def[of "lnot b"] lnot_def[of b \<sigma>'] \<open>\<not> b \<sigma>'\<close> by force
      then have "(fst \<phi>', \<sigma>') \<in> sem (while_cond b C) ?S"
        by (simp add: assume_sem filter_exp_def sem_seq sem_while while_cond_def)
      then show "\<exists>\<sigma>'. \<langle>while_cond b C, snd \<phi>\<rangle> \<rightarrow> \<sigma>'"
        by (metis in_sem singletonD snd_conv)
    qed
  qed
qed

lemma total_hyper_triple_altI:
  assumes "\<And>S. P S \<Longrightarrow> Q (sem C S)"
      and "\<And>S. P S \<Longrightarrow> terminates_in C S"
    shows "\<Turnstile>TERM {P} C {Q}"
  by (metis assms(1) assms(2) hyper_hoare_tripleI terminates_in_def total_hyper_triple_def)



lemma syntactic_frame_preserved:
  assumes "terminates_in C S"
      and "wr C \<inter> fv F = {}"
      and "sat_assertion vals states F S"
      and "wf_assertion_aux nv (length states) F"
    shows "sat_assertion vals states F (sem C S)"
  using assms
proof (induct F arbitrary: vals states nv)
  case (AForallState F)
  then have "\<And>\<phi>. \<phi> \<in> sem C S \<Longrightarrow> sat_assertion vals (\<phi> # states) F (sem C S)"
  proof -
    fix \<phi> assume asm0: "\<phi> \<in> sem C S"
    then obtain \<sigma> where "single_sem C \<sigma> (snd \<phi>)" "(fst \<phi>, \<sigma>) \<in> S"
      using in_sem by blast
    then have "sat_assertion vals ((fst \<phi>, \<sigma>) # states) F (sem C S)"
      using AForallState.hyps AForallState.prems assms(1) by auto
    moreover have "agree_on (fv F) \<sigma> (snd \<phi>)"
      using AForallState.prems(2) \<open>\<langle>(C::(nat, nat) stmt), \<sigma>::nat \<Rightarrow> nat\<rangle> \<rightarrow> snd (\<phi>::(nat \<Rightarrow> nat) \<times> (nat \<Rightarrow> nat))\<close> wr_charact by auto
    moreover have "wf_assertion_aux nv (Suc (length states)) F"
      using AForallState.prems(4) by auto
    ultimately have "sat_assertion vals ((fst \<phi>, snd \<phi>) # states) F (sem C S)"
      using fv_wr_charact[of F \<sigma> "snd \<phi>" vals "fst \<phi>" states "sem C S"]
      by fast
    then show "sat_assertion vals (\<phi> # states) F (sem C S)"
      by simp
  qed
  then show ?case
    using AForallState.hyps AForallState.prems(2) assms(1) by auto
next
  case (AExistsState F)
  then obtain \<phi> where asm0: "\<phi> \<in> S" "sat_assertion vals (\<phi> # states) F S"
    by auto
  then obtain \<sigma>' where "single_sem C (snd \<phi>) \<sigma>'"
    using assms(1) terminates_in_def by blast
  then have "sat_assertion vals ((fst \<phi>, \<sigma>') # states) F S"
    by (metis AExistsState.prems(2) AExistsState.prems(4) asm0(2) fv.simps(6) fv_wr_charact prod.collapse wf_assertion_aux.simps(8) wr_charact)
  then show ?case
    by (metis AExistsState.hyps AExistsState.prems(2) AExistsState.prems(4) \<open>\<langle>C, snd \<phi>\<rangle> \<rightarrow> \<sigma>'\<close> asm0(1) assms(1) fv.simps(6) length_Cons prod.collapse sat_assertion.simps(4) single_step_then_in_sem wf_assertion_aux.simps(8))
qed (fastforce+)


theorem frame_rule_syntactic:
  assumes "\<Turnstile>TERM {P} C {Q}"
      and "wr C \<inter> fv F = {}" (* free *program* variables *)
      and "wf_assertion F" (* No unbound free variable *)
    shows "\<Turnstile>TERM {conj P (interp_assert F)} C {conj Q (interp_assert F)}"
proof (rule total_hyper_tripleI)
  let ?F = "interp_assert F"
  show "\<And>\<phi> S. Logic.conj P ?F S \<and> \<phi> \<in> S \<Longrightarrow> \<exists>\<sigma>'. \<langle>C, snd \<phi>\<rangle> \<rightarrow> \<sigma>'"
    by (metis assms(1) conj_def total_hyper_triple_def)
  show "\<Turnstile> {Logic.conj P ?F} C {Logic.conj Q ?F}"
  proof (rule hyper_hoare_tripleI)
    fix S assume asm0: "Logic.conj P ?F S"
    then have "terminates_in C S"
      by (simp add: \<open>\<And>\<phi> S. Logic.conj P ?F S \<and> \<phi> \<in> S \<Longrightarrow> \<exists>\<sigma>'. \<langle>C, snd \<phi>\<rangle> \<rightarrow> \<sigma>'\<close> terminates_in_def)
    moreover have "?F (sem C S)"
      by (metis asm0 assms(2) assms(3) calculation conj_def list.size(3) syntactic_frame_preserved)
    ultimately show "Logic.conj Q ?F (sem C S)"
      by (metis asm0 assms(1) conj_def hyper_hoare_tripleE total_hyper_triple_def)
  qed
qed




subsection \<open>Specialize rule\<close>


definition same_syn_sem_all :: "'a assertion \<Rightarrow> ((nat, 'a, nat, 'a) state \<Rightarrow> bool) \<Rightarrow> bool"
  where
  "same_syn_sem_all bsyn bsem \<longleftrightarrow>
  (\<forall>states vals S. length states > 0 \<longrightarrow> bsem (hd states) = sat_assertion vals states bsyn S)"

lemma same_syn_sem_allI:
  assumes "\<And>states vals S. length states > 0 \<Longrightarrow> bsem (hd states) \<longleftrightarrow> sat_assertion vals states bsyn S"
  shows "same_syn_sem_all bsyn bsem"
  by (simp add: assms same_syn_sem_all_def)

lemma transform_assume_valid:
  assumes "same_syn_sem_all bsyn bsem"
  shows "sat_assertion vals states A (Set.filter bsem S)
  \<longleftrightarrow> sat_assertion vals states (transform_assume bsyn A) S"
proof (induct A arbitrary: vals states)
  case (AForallState A)
  let ?S = "Set.filter (bsem) S"
  let ?A = "transform_assume bsyn A"
  have "sat_assertion vals states (AForallState A) ?S \<longleftrightarrow> (\<forall>\<phi>\<in>?S. sat_assertion vals (\<phi> # states) A ?S)"
    by force
  also have "... \<longleftrightarrow> (\<forall>\<phi>\<in>?S. sat_assertion vals (\<phi> # states) ?A S)"
    using AForallState by presburger
  also have "... \<longleftrightarrow> (\<forall>\<phi>\<in>S. bsem \<phi> \<longrightarrow> sat_assertion vals (\<phi> # states) ?A S)"
    by fastforce
  also have "... \<longleftrightarrow> (\<forall>\<phi>\<in>S. sat_assertion vals (\<phi> # states) bsyn S \<longrightarrow> sat_assertion vals (\<phi> # states) ?A S)"
    using assms same_syn_sem_all_def[of bsyn bsem] by auto
  also have "... \<longleftrightarrow> (\<forall>\<phi>\<in>S. sat_assertion vals (\<phi> # states) (AImp bsyn ?A) S)"
    using sat_assertion_Imp by fast
  also have "... \<longleftrightarrow> sat_assertion vals states (AForallState (AImp bsyn ?A)) S"
    using sat_assertion.simps(2) by force
  then show ?case
    using calculation transform_assume.simps(1) by fastforce
next
  case (AExistsState A)
  let ?S = "Set.filter (bsem) S"
  let ?A = "transform_assume bsyn A"
  have "sat_assertion vals states (AExistsState A) ?S \<longleftrightarrow> (\<exists>\<phi>\<in>?S. sat_assertion vals (\<phi> # states) A ?S)"
    by force
  also have "... \<longleftrightarrow> (\<exists>\<phi>\<in>?S. sat_assertion vals (\<phi> # states) ?A S)"
    using AExistsState by presburger
  also have "... \<longleftrightarrow> (\<exists>\<phi>\<in>S. bsem \<phi> \<and> sat_assertion vals (\<phi> # states) ?A S)"
    by force
  also have "... \<longleftrightarrow> (\<exists>\<phi>\<in>S. sat_assertion vals (\<phi> # states) bsyn S \<and> sat_assertion vals (\<phi> # states) ?A S)"
    using assms same_syn_sem_all_def[of bsyn bsem] by auto
  also have "... \<longleftrightarrow> (\<exists>\<phi>\<in>S. sat_assertion vals (\<phi> # states) (AAnd bsyn ?A) S)"
    by simp
  also have "... \<longleftrightarrow> sat_assertion vals states (AExistsState (AAnd bsyn ?A)) S"
    using sat_assertion.simps(3) by force
  then show ?case
    using calculation transform_assume.simps(2) by fastforce
next
  case (AForall A)
  let ?S = "Set.filter (bsem) S"
  let ?A = "transform_assume bsyn A"
  have "sat_assertion vals states (AForall A) ?S \<longleftrightarrow> (\<forall>v. sat_assertion (v # vals) states A ?S)"
    by force
  also have "... \<longleftrightarrow> (\<forall>v. sat_assertion (v # vals) states ?A S)"
    using AForall by presburger
  also have "... \<longleftrightarrow> sat_assertion vals states (AForall ?A) S"
    by simp
  then show ?case
    using calculation transform_assume.simps(3) by fastforce
next
  case (AExists A)
  let ?S = "Set.filter (bsem) S"
  let ?A = "transform_assume bsyn A"
  have "sat_assertion vals states (AExists A) ?S \<longleftrightarrow> (\<exists>v. sat_assertion (v # vals) states A ?S)"
    by force
  also have "... \<longleftrightarrow> (\<exists>v. sat_assertion (v # vals) states ?A S)"
    using AExists by presburger
  also have "... \<longleftrightarrow> sat_assertion vals states (AExists ?A) S"
    by simp
  then show ?case
    using calculation transform_assume.simps(4) by fastforce
qed (simp_all)


fun indep_of_set where
  "indep_of_set (AForall A) \<longleftrightarrow> indep_of_set A"
| "indep_of_set (AExists A) \<longleftrightarrow> indep_of_set A"
| "indep_of_set (AOr A B) \<longleftrightarrow> indep_of_set A \<and> indep_of_set B"
| "indep_of_set (AAnd A B) \<longleftrightarrow> indep_of_set A \<and> indep_of_set B"
| "indep_of_set (AComp _ _ _) \<longleftrightarrow> True"
| "indep_of_set (AConst _) \<longleftrightarrow> True"
| "indep_of_set (AForallState _) \<longleftrightarrow> False"
| "indep_of_set (AExistsState _) \<longleftrightarrow> False"

lemma indep_of_set_charact:
  assumes "indep_of_set A"
      and "sat_assertion vals states A S"
    shows "sat_assertion vals states A S'"
  using assms
by (induct A arbitrary: vals states) (auto)

lemma wf_exp_take:
  assumes "wf_exp nv ns e"
  shows "interp_exp vals states e = interp_exp (take nv vals) (take ns states) e"
  using assms
proof (induct e arbitrary: nv ns vals states)
  case (EQVar x)
  then show ?case
    by force
next
  case (EBinop e1 x2 e2)
  then show ?case
    by (metis interp_exp.simps(5) wf_exp.simps(4))
next
  case (EFun f e)
  then show ?case
    by (metis interp_exp.simps(6) wf_exp.simps(5))
qed (simp_all)

lemma wf_assertion_aux_take:
  assumes "wf_assertion_aux nv ns A"
  shows "sat_assertion vals states A S \<longleftrightarrow> sat_assertion (take nv vals) (take ns states) A S"
  using assms
proof (induct A arbitrary: nv ns vals states)
  case (AConst x)
  then show ?case
    by simp
next
  case (AComp x1a x2 x3a)
  then show ?case
    by (metis sat_assertion.simps(2) wf_assertion_aux.simps(2) wf_exp_take)
next
  case (AForallState A)
  then show ?case using AForallState.hyps[of nv "Suc ns" vals]
    by (metis sat_assertion.simps(3) take_Suc_Cons wf_assertion_aux.simps(7))
next
  case (AExistsState A)
  then show ?case using AExistsState.hyps[of nv "Suc ns" vals]
    by (metis sat_assertion.simps(4) take_Suc_Cons wf_assertion_aux.simps(8))
next
  case (AForall A)
  then show ?case using AForall.hyps[of "Suc nv" ns _ states]
    by (metis sat_assertion.simps(5) take_Suc_Cons wf_assertion_aux.simps(5))
next
  case (AExists A)
  then show ?case using AExists.hyps[of "Suc nv" ns _ states]
    by (metis sat_assertion.simps(6) take_Suc_Cons wf_assertion_aux.simps(6))
next
  case (AOr A1 A2)
  then show ?case
    by (metis sat_assertion.simps(8) wf_assertion_aux.simps(4))
next
  case (AAnd A1 A2)
  then show ?case
    by (metis sat_assertion.simps(7) wf_assertion_aux.simps(3))
qed

lemma syntactic_charact_for_equivalence:
  assumes "indep_of_set A"
      and "wf_assertion_aux (0::nat) (1::nat) A"
    shows "sat_assertion vals (\<phi> # states) A S \<longleftrightarrow> sat_assertion [] [\<phi>] A {}" (is "?A \<longleftrightarrow> ?B")
proof -
  have "?A \<longleftrightarrow> sat_assertion vals (\<phi> # states) A {}"
    using assms(1) indep_of_set_charact by blast
  also have "... \<longleftrightarrow> sat_assertion (take (0::nat) vals) (take (1::nat) (\<phi> # states)) A {}"
    using wf_assertion_aux_take[of 0 1 A vals "\<phi> # states" "{}"] assms(2)
    by blast
  ultimately show ?thesis by simp
qed


definition get_bsem where
  "get_bsem bsyn \<phi> \<longleftrightarrow> sat_assertion [] [\<phi>] bsyn {}"

lemma syntactic_charact_for_bsem:
  assumes "indep_of_set A"
      and "wf_assertion_aux (0::nat) (1::nat) A"
    shows "same_syn_sem_all A (get_bsem A)"
proof (rule same_syn_sem_allI)
  fix states :: "((nat \<Rightarrow> 'a) \<times> (nat \<Rightarrow> 'a)) list"
  fix vals S
  assume asm0: "0 < length states"
  then show "get_bsem A (hd states) = sat_assertion vals states A S"
    by (metis assms(1) assms(2) get_bsem_def length_greater_0_conv list.collapse syntactic_charact_for_equivalence)
qed



lemma get_bsem_is_bsem:
  assumes "same_syn_sem_all bsyn bsem"
  shows "bsem = get_bsem bsyn"
proof (rule ext)
  fix x
  have "bsem (hd [x]) = sat_assertion [] [x] bsyn {}"
    using assms same_syn_sem_all_def by fastforce
  then show "bsem x = get_bsem bsyn x"
    by (simp add: get_bsem_def)
qed


lemma free_vars_syn_sem:
  assumes "same_syn_sem_all bsyn bsem"
      and "fst \<phi> = fst \<phi>'"
      and "agree_on (fv bsyn) (snd \<phi>) (snd \<phi>')"
      and "bsem \<phi>"
      and "wf_assertion_aux 0 (Suc 0) bsyn"
    shows "bsem \<phi>'"
proof -
  have "sat_assertion [] (insert_at 0 (fst \<phi>, snd \<phi>') []) bsyn {}"
    using assms(3)
  proof (rule fv_wr_charact_aux)
    show "sat_assertion [] (insert_at 0 (fst \<phi>, snd \<phi>) []) bsyn {}"
      by (metis assms(1) assms(4) get_bsem_def get_bsem_is_bsem insert_at.simps(1) prod.collapse)
    show "wf_assertion_aux 0 (Suc (length [])) bsyn"
      by (simp add: assms(5))
  qed (simp)
  then show ?thesis
    by (metis assms(1) assms(2) get_bsem_def get_bsem_is_bsem insert_at.simps(1) prod.collapse)
qed


lemma free_vars_charact:
  assumes "wr C \<inter> fv bsyn = {}"
      and "same_syn_sem_all bsyn bsem"
      and "wf_assertion_aux 0 (Suc 0) bsyn"
    shows "sem C (Set.filter bsem S) = Set.filter bsem (sem C S)" (is "?A = ?B")
proof
  show "?A \<subseteq> ?B"
  proof
    fix x assume asm0: "x \<in> sem C (Set.filter bsem S)"
    then obtain \<sigma> where "(fst x, \<sigma>) \<in> Set.filter bsem S" "single_sem C \<sigma> (snd x)"
      by (meson in_sem)
    then have "agree_on (fv bsyn) \<sigma> (snd x)"
      using assms(1) wr_charact by blast
    then show "x \<in> Set.filter bsem (sem C S)"
      by (metis \<open>(fst x, \<sigma>) \<in> Set.filter bsem S\<close> \<open>\<langle>C, \<sigma>\<rangle> \<rightarrow> snd x\<close> assms(2) assms(3) free_vars_syn_sem fst_conv member_filter prod.collapse single_step_then_in_sem snd_conv)
  qed
  show "?B \<subseteq> ?A"
  proof
    fix x assume asm0: "x \<in> ?B"
    then obtain \<sigma> where "bsem x" "(fst x, \<sigma>) \<in> S" "single_sem C \<sigma> (snd x)"
      by (metis in_sem member_filter)
    then have "agree_on (fv bsyn) \<sigma> (snd x)"
      using assms(1) wr_charact by blast
    then have "bsem (fst x, \<sigma>)"
      using \<open>bsem x\<close> agree_on_sym assms(2) assms(3) free_vars_syn_sem by fastforce
    then show "x \<in> ?A"
      by (metis \<open>(fst x, \<sigma>) \<in> S\<close> \<open>\<langle>C, \<sigma>\<rangle> \<rightarrow> snd x\<close> in_sem member_filter)
  qed
qed


lemma filter_rule_semantic:
  assumes "\<Turnstile> {interp_assert P} C {interp_assert Q}"
      and "same_syn_sem_all bsyn bsem"
      and "wr C \<inter> fv bsyn = {}"
      and "wf_assertion_aux 0 (Suc 0) bsyn"
    shows "\<Turnstile> { interp_assert (transform_assume bsyn P) } C { interp_assert (transform_assume bsyn Q) }"
proof (rule hyper_hoare_tripleI)
  fix S assume asm0: "interp_assert (transform_assume bsyn P) S"
  then have "sat_assertion [] [] P (Set.filter bsem S)"
    using TotalLogic.transform_assume_valid assms(2) by blast
  then have "sat_assertion [] [] Q (sem C (Set.filter bsem S))"
    using assms(1) hyper_hoare_tripleE by blast
  moreover have "sem C (Set.filter bsem S) = Set.filter bsem (sem C S)"
    using assms(2) assms(3) assms(4) free_vars_charact by presburger
  ultimately show "interp_assert (transform_assume bsyn Q) (sem C S)"
    using TotalLogic.transform_assume_valid assms(2) by fastforce
qed

lemma filter_rule_syntactic:
  assumes "\<Turnstile> {interp_assert P} C {interp_assert Q}"
      and "indep_of_set b"
      and "wf_assertion_aux 0 1 b"
      and "wr C \<inter> fv b = {}"
    shows "\<Turnstile> { interp_assert (transform_assume b P) } C { interp_assert (transform_assume b Q) }"
  using assms(1) filter_rule_semantic
  by (metis One_nat_def assms(2) assms(3) assms(4) syntactic_charact_for_bsem)


definition terminates where
  "terminates C \<longleftrightarrow> (\<forall>\<sigma>. \<exists>\<sigma>'. single_sem C \<sigma> \<sigma>')"

lemma terminatesI:
  assumes "\<And>\<sigma>. \<exists>\<sigma>'. single_sem C \<sigma> \<sigma>'"
  shows "terminates C"
  using terminates_def assms by auto

lemma terminates_implies_total:
  assumes "\<Turnstile> {P} C {Q}"
      and "terminates C"
    shows "\<Turnstile>TERM {P} C {Q}"
  using assms(1)
proof (rule total_hyper_tripleI)
  fix \<phi> S assume asm0: "P S \<and> \<phi> \<in> S"
  then show "\<exists>\<sigma>'. \<langle>C, snd \<phi>\<rangle> \<rightarrow> \<sigma>'"
    by (metis assms(2) terminates_def)
qed

lemma terminates_seq:
  assumes "terminates C1"
      and "terminates C2"
    shows "terminates (C1;; C2)"
  by (meson SemSeq assms(1) assms(2) terminates_def)

lemma terminates_assign:
  "terminates (Assign x e)"
  by (meson SemAssign terminates_def)

lemma terminates_havoc:
  "terminates (Havoc c)"
  by (meson SemHavoc terminates_def)

lemma terminates_if:
  assumes "terminates C1"
      and "terminates C2"
    shows "terminates (If C1 C2)"
  by (meson SemIf2 assms(2) terminates_def)


lemma rule_lframe_exist:
   fixes b :: "('a \<Rightarrow> ('lvar \<Rightarrow> 'lval)) \<Rightarrow> bool"
    \<comment>\<open>b takes a mapping from keys to logical states (representing the tuple), and returns a boolean\<close>

   assumes "\<Turnstile>TERM {P} C {Q}"
     shows "\<Turnstile>TERM { conj P (\<lambda>S. \<exists>\<phi>. (\<forall>k. \<phi> k \<in> S) \<and> b (fst \<circ> \<phi>)) } C { conj Q (\<lambda>S. \<exists>\<phi>. (\<forall>k. \<phi> k \<in> S) \<and> b (fst \<circ> \<phi>)) }"

proof (rule total_hyper_tripleI)
  fix \<phi> S
  show "Logic.conj P (\<lambda>S. \<exists>\<phi>. (\<forall>k. \<phi> k \<in> S) \<and> b (fst \<circ> \<phi>)) S \<and> \<phi> \<in> S \<Longrightarrow> \<exists>\<sigma>'. \<langle>C, snd \<phi>\<rangle> \<rightarrow> \<sigma>'"
    by (metis (mono_tags, lifting) assms conj_def total_hyper_triple_equiv)
next
  show "\<Turnstile> {Logic.conj P (\<lambda>S. \<exists>\<phi>. (\<forall>k. \<phi> k \<in> S) \<and> b (fst \<circ> \<phi>))} C {Logic.conj Q (\<lambda>S. \<exists>\<phi>. (\<forall>k. \<phi> k \<in> S) \<and> b (fst \<circ> \<phi>))}"
  proof (rule hyper_hoare_tripleI)
    fix S :: "('lvar, 'lval, 'b, 'c) state set"
    assume asm0: "Logic.conj P (\<lambda>S. \<exists>\<phi>. (\<forall>k. \<phi> k \<in> S) \<and> b (fst \<circ> \<phi>)) S"
    then obtain \<phi> where "(\<forall>k. \<phi> k \<in> S) \<and> b (fst \<circ> \<phi>)"
      using conj_def[of P "\<lambda>S. \<exists>\<phi>. (\<forall>k. \<phi> k \<in> S) \<and> b (fst \<circ> \<phi>)" S] by blast
    let ?\<sigma> = "\<lambda>k. SOME \<sigma>'. (fst (\<phi> k), \<sigma>') \<in> sem C S \<and> single_sem C (snd (\<phi> k)) \<sigma>'"
    let ?\<phi> = "\<lambda>k. (fst (\<phi> k), ?\<sigma> k)"
    have r: "\<And>k. (fst (\<phi> k), ?\<sigma> k) \<in> sem C S \<and> single_sem C (snd (\<phi> k)) (?\<sigma> k)"
    proof -
      fix k show "(fst (\<phi> k), ?\<sigma> k) \<in> sem C S \<and> single_sem C (snd (\<phi> k)) (?\<sigma> k)"
      proof (rule someI_ex[of "\<lambda>\<sigma>'. (fst (\<phi> k), \<sigma>') \<in> sem C S \<and> single_sem C (snd (\<phi> k)) \<sigma>'"])
        show "\<exists>\<sigma>'. (fst (\<phi> k), \<sigma>') \<in> sem C S \<and> \<langle>C, snd (\<phi> k)\<rangle> \<rightarrow> \<sigma>'"
          by (metis (mono_tags, lifting) \<open>(\<forall>k. \<phi> k \<in> S) \<and> b (fst \<circ> \<phi>)\<close> asm0 assms conj_def total_hyper_triple_equiv)
      qed
    qed
    moreover have "fst \<circ> \<phi> = fst \<circ> ?\<phi>" by (rule ext) simp
    ultimately have "\<exists>\<phi>. (\<forall>k. \<phi> k \<in> sem C S) \<and> b (fst \<circ> \<phi>)"
      using \<open>(\<forall>k. \<phi> k \<in> S) \<and> b (fst \<circ> \<phi>)\<close> by force
    moreover have "Q (sem C S)"
      by (metis (mono_tags, lifting) asm0 assms conj_def hyper_hoare_tripleE total_hyper_triple_def)
    ultimately show "Logic.conj Q (\<lambda>S. \<exists>\<phi>. (\<forall>k. \<phi> k \<in> S) \<and> b (fst \<circ> \<phi>)) (sem C S)"
      using conj_def[of Q "\<lambda>S. \<exists>\<phi>. (\<forall>k. \<phi> k \<in> S) \<and> b (fst \<circ> \<phi>)"] by simp
  qed
qed

lemma terminates_if_then:
  assumes "terminates C1"
      and "terminates C2"
    shows "terminates (if_then_else b C1 C2)"
proof (rule terminatesI)
  fix \<sigma>
  show "\<exists>\<sigma>'. \<langle>if_then_else b C1 C2, \<sigma>\<rangle> \<rightarrow> \<sigma>'"
  proof (cases "b \<sigma>")
    case True
    then show ?thesis
      by (metis SemAssume SemIf1 SemSeq assms(1) if_then_else_def terminates_def)
  next
    case False
    then show ?thesis
      by (metis (no_types, opaque_lifting) SemAssume SemIf2 SemSeq assms(2) if_then_else_def lnot_def terminates_def)
  qed
qed


definition min_prop :: "(nat \<Rightarrow> bool) \<Rightarrow> nat" where
  "min_prop P = (SOME n. P n \<and> (\<forall>m. m < n \<longrightarrow> \<not> P m))"

lemma min_prop_charact:
  assumes "P n"
  shows "P (min_prop P) \<and> (\<forall>m. m < (min_prop P) \<longrightarrow> \<not> P m)"
  unfolding min_prop_def
  using min_prop_def[of P] assms exists_least_iff[of P] someI[of "\<lambda>n. P n \<and> (\<forall>m. m < n \<longrightarrow> \<not> P m)"]
  by blast


lemma hyper_tot_set_not_empty:
  assumes "\<Turnstile>TERM {P} C {Q}"
      and "P S"
      and "S \<noteq> {}"
    shows "sem C S \<noteq> {}"
  by (metis assms(1) assms(2) assms(3) ex_in_conv total_hyper_triple_equiv)

lemma iterate_sem_mod_updates_same:
  assumes "same_mod_updates vars S S'"
  shows "same_mod_updates vars (iterate_sem n C S) (iterate_sem n C S')"
  using assms
proof (induct n)
  case 0
  then show ?case by simp
next
  case (Suc n)
  then show ?case
    by (simp add: sem_update_commute)
qed


theorem while_synchronized_tot:
  assumes "wfP lt"
      and "\<And>n. not_fv_hyper t (I n)"
      and "\<And>n. \<Turnstile>TERM {conj (conj (I n) (holds_forall b)) (e_recorded_in_t e t)} C {conj (conj (I (Suc n)) (low_exp b)) (e_smaller_than_t e t lt)}"
    shows "\<Turnstile>TERM {conj (I 0) (low_exp b)} while_cond b C {conj (exists I) (holds_forall (lnot b))}"
proof (rule total_hyper_triple_altI)
  fix S assume asm0: "conj (I 0) (low_exp b) S"
  let ?S = "\<lambda>n. assign_exp_to_lvar_set e t (iterate_sem n (Assume b;; C) S)"

  have S_same: "\<And>n. same_mod_updates {t} (?S n) (iterate_sem n (Assume b;; C) S)"
    by (simp add: assign_exp_to_lvar_set_same_mod_updates same_mod_updates_sym)


  have triple: "\<And>n. \<Turnstile> {conj (I n) (holds_forall b)} Assume b ;; C {conj (I (Suc n)) (low_exp b)}"
  proof (rule hyper_hoare_tripleI)
    fix n S assume "conj (I n) (holds_forall b) S"
    let ?S = "assign_exp_to_lvar_set e t S"
    have "conj (I n) (holds_forall b) ?S"
      by (metis \<open>Logic.conj (I n) (holds_forall b) S\<close> assms(2) conj_def holds_forall_same_assign_lvar not_fv_hyper_assign_exp)
    then have "conj (conj (I n) (holds_forall b)) (e_recorded_in_t e t) ?S"
      by (simp add: conj_def e_recorded_in_t_if_assigned)
    then have "Logic.conj (I (Suc n)) (low_exp b) (sem (Assume b ;; C) ?S)"
      by (metis (mono_tags, lifting) assms(3) conj_def hyper_hoare_tripleE sem_assume_low_exp_seq(1) total_hyper_triple_def)
    moreover have "same_mod_updates {t} (sem (Assume b ;; C) ?S) (sem (Assume b ;; C) S)"
      by (simp add: assign_exp_to_lvar_set_same_mod_updates same_mod_updates_sym sem_update_commute)
    ultimately show "conj (I (Suc n)) (low_exp b) (sem (Assume b ;; C) S)"
      by (metis assms(2) conj_def low_exp_forall_same_mod_updates not_fv_hyperE)
  qed

  have "\<And>n. iterate_sem n (Assume b ;; C) S \<noteq> {} \<Longrightarrow> conj (I n) (low_exp b) (iterate_sem n (Assume b ;; C) S)"
  proof -
    fix n
    show "iterate_sem n (Assume b ;; C) S \<noteq> {} \<Longrightarrow> conj (I n) (low_exp b) (iterate_sem n (Assume b ;; C) S)"
    proof (induct n)
      case 0
      then show ?case
        by (simp add: asm0)
    next
      case (Suc n)
      then show ?case
        by (metis (full_types) conj_def false_then_empty_later holds_forall_empty hyper_hoare_tripleE iterate_sem.simps(2) lessI low_exp_two_cases triple)
    qed
  qed

  have terminates: "\<exists>n. iterate_sem n (Assume b;; C) S = {}"
  proof (rule ccontr)
    assume asm0: "\<not> (\<exists>n. iterate_sem n (Assume b ;; C) S = {})"
    
    let ?R = "{(x, y). lt x y}"
    let ?Q = "{ e (snd \<phi>) |\<phi> n. \<phi> \<in> ?S n}"

    obtain \<phi>0 where "\<phi>0 \<in> ?S 0"
      by (metis all_not_in_conv asm0 false_then_empty_later holds_forall_empty holds_forall_same_assign_lvar lessI)

    show False
    proof (rule wfE_min)
      show "wf ?R"
        using assms(1) wfP_def by blast
      show "e (snd \<phi>0) \<in> ?Q"
        using \<open>\<phi>0 \<in> assign_exp_to_lvar_set e t (iterate_sem 0 (Assume b ;; C) S)\<close> by blast
      fix z assume asm1: "z \<in> ?Q" "(\<And>y. (y, z) \<in> {(x, y). lt x y} \<Longrightarrow> y \<notin> ?Q)"
      then obtain \<phi> n where "z = e (snd \<phi>)" "\<phi> \<in> ?S n" by blast
      moreover have "conj (I n) (holds_forall b) (iterate_sem n (Assume b ;; C) S)"
      proof -
        have "conj (I n) (low_exp b) (iterate_sem n (Assume b ;; C) S)"
          using \<open>\<And>n. iterate_sem n (Assume b ;; C) S \<noteq> {} \<Longrightarrow> Logic.conj (I n) (low_exp b) (iterate_sem n (Assume b ;; C) S)\<close> asm0 by presburger
        moreover have "sem (Assume b;; C) (iterate_sem n (Assume b ;; C) S) \<noteq> {}"
          using asm0 iterate_sem.simps(2) by blast
        ultimately show ?thesis
          by (metis asm0 conj_def false_then_empty_later lessI low_exp_two_cases)
      qed
      then have "conj (conj (I n) (holds_forall b)) (e_recorded_in_t e t) (?S n)"
        by (metis (mono_tags, lifting) assms(2) conj_def e_recorded_in_t_if_assigned holds_forall_same_assign_lvar not_fv_hyper_assign_exp)
      then have "conj (conj (I (Suc n)) (low_exp b)) (e_smaller_than_t e t lt) (sem C (?S n))"
        using assms(3) hyper_hoare_tripleE total_hyper_triple_def by blast
      moreover obtain \<sigma>' where "\<langle>C, snd \<phi>\<rangle> \<rightarrow> \<sigma>'"
        by (meson \<open>Logic.conj (Logic.conj (I n) (holds_forall b)) (e_recorded_in_t e t) (assign_exp_to_lvar_set e t (iterate_sem n (Assume b ;; C) S))\<close> assms(3) calculation(2) total_hyper_triple_def)

      then have "(fst \<phi>, \<sigma>') \<in> sem (Assume b;; C) (?S n)"
        by (metis \<open>Logic.conj (Logic.conj (I n) (holds_forall b)) (e_recorded_in_t e t) (assign_exp_to_lvar_set e t (iterate_sem n (Assume b ;; C) S))\<close> calculation(2) conj_def prod.collapse sem_assume_low_exp_seq(1) single_step_then_in_sem)
      then have "lt (e \<sigma>') z"
        by (metis (no_types, lifting) \<open>Logic.conj (Logic.conj (I n) (holds_forall b)) (e_recorded_in_t e t) (assign_exp_to_lvar_set e t (iterate_sem n (Assume b ;; C) S))\<close> calculation(1) calculation(2) calculation(3) conj_def e_recorded_in_t_def e_smaller_than_t_def fst_conv sem_assume_low_exp_seq(1) snd_conv)

      moreover obtain \<sigma> where "(fst \<phi>, \<sigma>) \<in> ?S n" "single_sem (Assume b;; C) \<sigma> \<sigma>'"
        by (metis \<open>(fst \<phi>, \<sigma>') \<in> sem (Assume b ;; C) (assign_exp_to_lvar_set e t (iterate_sem n (Assume b ;; C) S))\<close> fst_conv in_sem snd_conv)
      then obtain l where "(l, \<sigma>) \<in> iterate_sem n (Assume b;; C) S"
        using assign_exp_to_lvar_def[of e t] assign_exp_to_lvar_set_def[of e t] image_iff prod.collapse snd_conv
        by fastforce
      then have "(l, \<sigma>') \<in> iterate_sem (Suc n) (Assume b;; C) S"
        by (metis \<open>\<langle>Assume b ;; C, \<sigma>\<rangle> \<rightarrow> \<sigma>'\<close> iterate_sem.simps(2) single_step_then_in_sem)
      then have "assign_exp_to_lvar e t (l, \<sigma>') \<in> ?S (Suc n)"
        by (simp add: assign_exp_to_lvar_set_def)
      then have "e \<sigma>' \<in> ?Q"
        by (metis (mono_tags, lifting) CollectI same_outside_set_lvar_assign_exp snd_conv)
      ultimately show False
        using asm1(2) by blast
    qed
  qed
    
  show "conj (exists I) (holds_forall (lnot b)) (sem (while_cond b C) S)"
  proof -
    let ?n_emp = "min_prop (\<lambda>n. iterate_sem n (Assume b;; C) S = {})"
    have rr: "iterate_sem ?n_emp (Assume b;; C) S = {} \<and> (\<forall>m<?n_emp. iterate_sem m (Assume b;; C) S \<noteq> {})"
      using min_prop_charact terminates by fast
    show ?thesis
    proof (cases "?n_emp")
      case 0
      then have "S = {}"
        using rr by auto
      then show ?thesis
        by (metis Loops.exists_def asm0 conj_def holds_forall_empty sem_assume_low_exp_seq(2) sem_seq)
    next
      case (Suc k)
      then have "iterate_sem k (Assume b;; C) S \<noteq> {}"
        using lessI rr by presburger
      then have "conj (I k) (low_exp b) (iterate_sem k (Assume b ;; C) S)"
        by (simp add: \<open>\<And>n. iterate_sem n (Assume b ;; C) S \<noteq> {} \<Longrightarrow> Logic.conj (I n) (low_exp b) (iterate_sem n (Assume b ;; C) S)\<close>)
      moreover have "holds_forall (lnot b) (iterate_sem k (Assume b;; C) S)"
      proof (rule ccontr)
        assume asm2: "\<not> holds_forall (lnot b) (iterate_sem k (Assume b ;; C) S)"
        then have "holds_forall b (iterate_sem k (Assume b ;; C) S)"
          by (metis calculation conj_def low_exp_two_cases)
        let ?S = "assign_exp_to_lvar_set e t (iterate_sem k (Assume b ;; C) S)"
        have "conj (conj (I k) (holds_forall b)) (e_recorded_in_t e t) ?S"
          by (metis (no_types, lifting) \<open>holds_forall b (iterate_sem k (Assume b ;; C) S)\<close> assign_exp_to_lvar_set_same_mod_updates assms(2) calculation conj_def e_recorded_in_t_if_assigned holds_forall_same_mod_updates not_fv_hyperE)
        moreover have "sem (Assume b) ?S = ?S"
          by (metis calculation conj_def sem_assume_low_exp(1))
        ultimately have "sem (Assume b;; C) ?S \<noteq> {}"
          by (metis asm2 assms(3) holds_forall_empty holds_forall_same_assign_lvar hyper_tot_set_not_empty sem_seq)

        moreover have "same_mod_updates {t} (sem (Assume b;; C) ?S) (assign_exp_to_lvar_set e t (iterate_sem ?n_emp (Assume b;; C) S))"
          by (metis Suc assign_exp_to_lvar_set_def assign_exp_to_lvar_set_same_mod_updates image_empty iterate_sem.simps(2) rr same_mod_updates_sym sem_update_commute)
        ultimately show False
          by (metis assign_exp_to_lvar_set_def image_empty rr same_mod_updates_empty same_mod_updates_sym)
      qed
      then have "\<exists>n. holds_forall (lnot b) (iterate_sem n (Assume b;; C) S) \<and> iterate_sem n (Assume b ;; C) S \<noteq> {}
     \<and> (\<forall>m. m < n \<longrightarrow> \<not> (holds_forall (lnot b) (iterate_sem m (Assume b;; C) S) \<and> iterate_sem m (Assume b ;; C) S \<noteq> {}))"
        using exists_least_iff[of "\<lambda>n. holds_forall (lnot b) (iterate_sem n (Assume b;; C) S) \<and> iterate_sem n (Assume b ;; C) S \<noteq> {}"]
        using \<open>iterate_sem k (Assume b ;; C) S \<noteq> {}\<close> by blast
      then obtain n where def_n: "holds_forall (lnot b) (iterate_sem n (Assume b;; C) S)" "iterate_sem n (Assume b ;; C) S \<noteq> {}"
        "\<And>m. m < n \<Longrightarrow> \<not> (holds_forall (lnot b) (iterate_sem m (Assume b;; C) S) \<and> iterate_sem m (Assume b ;; C) S \<noteq> {})" by blast
      moreover have "(\<forall>m. m < n \<longrightarrow> holds_forall b (iterate_sem m (Assume b;; C) S)) \<and> holds_forall (lnot b) (iterate_sem n (Assume b;; C) S)"
  
        by (metis \<open>\<And>n. iterate_sem n (Assume b ;; C) S \<noteq> {} \<Longrightarrow> Logic.conj (I n) (low_exp b) (iterate_sem n (Assume b ;; C) S)\<close> conj_def def_n(1) def_n(2) false_then_empty_later holds_forall_empty low_exp_two_cases)
      then have "sem (while_cond b C) S = iterate_sem n (Assume b;; C) S"
        using triple while_synchronized_case_1 asm0 by blast
      ultimately show ?thesis
        by (metis Loops.exists_def \<open>\<And>n. iterate_sem n (Assume b ;; C) S \<noteq> {} \<Longrightarrow> Logic.conj (I n) (low_exp b) (iterate_sem n (Assume b ;; C) S)\<close> conj_def)
    qed
  qed



  show "terminates_in (while_cond b C) S"
  proof (rule terminates_in_while_loop)
    show "wfP lt"
      by (simp add: assms(1))
    fix \<phi> n
    assume asm1: "\<phi> \<in> iterate_sem n (Assume b ;; C) S \<and> b (snd \<phi>)"
    let ?S = "iterate_sem n (Assume b ;; C) S"
    have "conj (I n) (low_exp b) ?S"
      using \<open>\<And>n. iterate_sem n (Assume b ;; C) S \<noteq> {} \<Longrightarrow> Logic.conj (I n) (low_exp b) (iterate_sem n (Assume b ;; C) S)\<close> asm1 by blast
    then have "conj (I n) (holds_forall b) ?S"
      by (metis asm1 conj_def holds_forall_def lnot_def low_exp_two_cases)
    let ?SS = "assign_exp_to_lvar_set e t ?S"
    have "conj (conj (I n) (holds_forall b)) (e_recorded_in_t e t) ?SS"
      by (metis (no_types, lifting) \<open>Logic.conj (I n) (holds_forall b) (iterate_sem n (Assume b ;; C) S)\<close> assign_exp_to_lvar_set_same_mod_updates assms(2) conj_def e_recorded_in_t_if_assigned holds_forall_same_mod_updates not_fv_hyperE)
    then have "conj (conj (I (Suc n)) (low_exp b)) (e_smaller_than_t e t lt) (sem C ?SS)"
      using assms(3) hyper_hoare_tripleE total_hyper_triple_def by blast
    moreover have "assign_exp_to_lvar e t \<phi> \<in> ?SS"
      by (simp add: asm1 assign_exp_to_lvar_set_def)
    then obtain \<sigma>' where "\<langle>C, snd (assign_exp_to_lvar e t \<phi>)\<rangle> \<rightarrow> \<sigma>'"
      by (meson \<open>Logic.conj (Logic.conj (I n) (holds_forall b)) (e_recorded_in_t e t) (assign_exp_to_lvar_set e t (iterate_sem n (Assume b ;; C) S))\<close> assms(3) total_hyper_triple_def)    
    then have "(\<langle>C, snd \<phi>\<rangle> \<rightarrow> \<sigma>') \<and> (fst (assign_exp_to_lvar e t \<phi>), \<sigma>') \<in> sem C ?SS"
      by (metis \<open>assign_exp_to_lvar e t \<phi> \<in> assign_exp_to_lvar_set e t (iterate_sem n (Assume b ;; C) S)\<close> assign_exp_to_lvar_def prod.collapse single_step_then_in_sem snd_conv)
    then have "lt (e \<sigma>') (fst (fst (assign_exp_to_lvar e t \<phi>), \<sigma>') t)"
      by (metis calculation conj_def e_smaller_than_t_def snd_conv)
    then show "\<exists>\<sigma>'. (\<langle>C, snd \<phi>\<rangle> \<rightarrow> \<sigma>') \<and> (\<not> b \<sigma>' \<or> lt (e \<sigma>') (e (snd \<phi>)))"
      by (metis \<open>(\<langle>C, snd \<phi>\<rangle> \<rightarrow> \<sigma>') \<and> (fst (assign_exp_to_lvar e t \<phi>), \<sigma>') \<in> sem C (assign_exp_to_lvar_set e t (iterate_sem n (Assume b ;; C) S))\<close> assign_exp_to_lvar_def fst_conv fun_upd_same)
  qed
qed

lemma total_consequence_rule:
  assumes "entails P P'"
    and "entails Q' Q"
      and "\<Turnstile>TERM {P'} C {Q'}"
    shows "\<Turnstile>TERM {P} C {Q}"
proof (rule total_hyper_tripleI)
  show "\<Turnstile> {P} C {Q}"
    using assms(1) assms(2) assms(3) consequence_rule total_hyper_triple_def by blast
  fix \<phi> S show "P S \<and> \<phi> \<in> S \<Longrightarrow> \<exists>\<sigma>'. \<langle>C, snd \<phi>\<rangle> \<rightarrow> \<sigma>'"
    by (meson assms(1) assms(3) entailsE total_hyper_triple_def)
qed

theorem WhileSyncTot:
  assumes "wfP lt"
      and "not_fv_hyper t I"
      and "\<Turnstile>TERM {conj I (\<lambda>S. \<forall>\<phi>\<in>S. b (snd \<phi>) \<and> fst \<phi> t = e (snd \<phi>))} C {conj (conj I (low_exp b)) (e_smaller_than_t e t lt)}"
    shows "\<Turnstile>TERM {conj I (low_exp b)} while_cond b C {conj I (holds_forall (lnot b))}"
proof -
  define I' where "I' = (\<lambda>(n::nat). I)"
  have "\<Turnstile>TERM {conj (conj I (holds_forall b)) (e_recorded_in_t e t)} C {conj (conj I (low_exp b)) (e_smaller_than_t e t lt)}"
  proof (rule total_consequence_rule)
    show "\<Turnstile>TERM {conj I (\<lambda>S. \<forall>\<phi>\<in>S. b (snd \<phi>) \<and> fst \<phi> t = e (snd \<phi>))} C {conj (conj I (low_exp b)) (e_smaller_than_t e t lt)}"
      using assms(3) by blast
    show "entails (Logic.conj (Logic.conj I (holds_forall b)) (e_recorded_in_t e t)) (Logic.conj I (\<lambda>S. \<forall>\<phi>\<in>S. b (snd \<phi>) \<and> fst \<phi> t = e (snd \<phi>)))"
      by (simp add: conj_def e_recorded_in_t_def entails_def holds_forall_def)
  qed (simp add: entails_refl)
  then have "\<Turnstile>TERM {Logic.conj (I' 0) (low_exp b)} while_cond b C {Logic.conj (Loops.exists I') (holds_forall (lnot b))}"
    using while_synchronized_tot[of lt t I' b e C] I'_def assms by blast
  then show ?thesis using I'_def
    by (simp add: Loops.exists_def conj_def hyper_hoare_triple_def total_hyper_triple_def)
qed




lemma total_hyper_tripleE:
  assumes "\<Turnstile>TERM {P} C {Q}"
      and "P S"
      and "\<phi> \<in> S"
    shows "\<exists>\<sigma>'. (fst \<phi>, \<sigma>') \<in> sem C S \<and> single_sem C (snd \<phi>) \<sigma>'"
  by (meson assms(1) assms(2) assms(3) total_hyper_triple_equiv)

theorem normal_while_tot:
  assumes "\<And>n. \<Turnstile> {P n} Assume b {Q n}"
      and "\<And>n. \<Turnstile>TERM {conj (Q n) (e_recorded_in_t e t)} C {conj (P (Suc n)) (e_smaller_than_t e t lt)}"
      and "\<Turnstile> {natural_partition P} Assume (lnot b) {R}"

      and "wfP lt"
      and "\<And>n. not_fv_hyper t (P n)"
      and "\<And>n. not_fv_hyper t (Q n)"

    shows "\<Turnstile>TERM {P 0} while_cond b C {R}"
proof (rule total_hyper_triple_altI)
  fix S assume asm0: "P 0 S"
  have "\<And>n. P n (iterate_sem n (Assume b;; C) S)"
  proof (rule indexed_invariant_then_power)
    fix n
    have "\<Turnstile> {Q n} C {P (Suc n)}"
    proof (rule hyper_hoare_tripleI)
      fix S assume asm1: "Q n S"
      let ?S = "assign_exp_to_lvar_set e t S"
      have "conj (Q n) (e_recorded_in_t e t) ?S"
        by (metis asm1 assms(6) conj_def e_recorded_in_t_if_assigned not_fv_hyper_assign_exp)
      then have "conj (P (Suc n)) (e_smaller_than_t e t lt) (sem C ?S)"
        using assms(2) hyper_hoare_tripleE total_hyper_triple_def by blast
      then show "P (Suc n) (sem C S)"
        using assign_exp_to_lvar_set_same_mod_updates[of t S e] assms(5) conj_def not_fv_hyperE same_mod_updates_sym[of "{t}"] sem_update_commute[of "{t}"]
        by metis
    qed
    then show " \<Turnstile> {P n} Assume b ;; C {P (Suc n)}"
      using assms(1) seq_rule total_hyper_triple_def by blast
  qed (simp add: asm0)
  then have "natural_partition P (\<Union>n. iterate_sem n (Assume b;; C) S)"
    by (simp add: natural_partitionI)
  then show "R (sem (while_cond b C) S)"
    by (metis (no_types, lifting) SUP_cong assms(3) hyper_hoare_triple_def sem_seq sem_while while_cond_def)

  show "terminates_in (while_cond b C) S"
  proof (rule terminates_in_while_loop)
    show "wfP lt"
      by (simp add: assms(4))
    fix \<phi> n
    assume asm1: "\<phi> \<in> iterate_sem n (Assume b ;; C) S \<and> b (snd \<phi>)"

    let ?S = "assign_exp_to_lvar_set e t (iterate_sem n (Assume b;; C) S)"
    let ?\<phi> = "assign_exp_to_lvar e t \<phi>"
    have "conj (P n) (e_recorded_in_t e t) ?S"
      by (metis \<open>\<And>n. P n (iterate_sem n (Assume b ;; C) S)\<close> assms(5) conj_def e_recorded_in_t_if_assigned not_fv_hyper_assign_exp)
    then have "conj (Q n) (e_recorded_in_t e t) (sem (Assume b) ?S)"
      
      by (metis (mono_tags, lifting) assms(1) assume_sem conj_def e_recorded_in_t_def hyper_hoare_tripleE member_filter)
    then have "conj (P (Suc n)) (e_smaller_than_t e t lt) (sem C (sem (Assume b) ?S))"
      using assms(2) hyper_hoare_tripleE total_hyper_triple_def by blast
    moreover have "?\<phi> \<in> (sem (Assume b) ?S)"
      by (metis asm1 assign_exp_to_lvar_set_def assume_sem comp_apply image_eqI member_filter same_outside_set_lvar_assign_exp)
    then obtain \<sigma>' where "(fst ?\<phi>, \<sigma>') \<in> sem C (sem (Assume b) ?S) \<and> \<langle>C, snd ?\<phi>\<rangle> \<rightarrow> \<sigma>'"
      using total_hyper_tripleE assms(2)[of n]
      using \<open>Logic.conj (Q n) (e_recorded_in_t e t) (sem (Assume b) (assign_exp_to_lvar_set e t (iterate_sem n (Assume b ;; C) S)))\<close> by blast
    then have "lt (e (snd (fst ?\<phi>, \<sigma>'))) (fst (fst ?\<phi>, \<sigma>') t)"
      by (metis calculation conj_def e_smaller_than_t_def)
    ultimately show "\<exists>\<sigma>'. \<langle>C, snd \<phi>\<rangle> \<rightarrow> \<sigma>' \<and> (\<not> b \<sigma>' \<or> lt (e \<sigma>') (e (snd \<phi>)))"
      by (metis \<open>(fst (assign_exp_to_lvar e t \<phi>), \<sigma>') \<in> sem C (sem (Assume b) (assign_exp_to_lvar_set e t (iterate_sem n (Assume b ;; C) S))) \<and> \<langle>C, snd (assign_exp_to_lvar e t \<phi>)\<rangle> \<rightarrow> \<sigma>'\<close> assign_exp_to_lvar_def fst_conv fun_upd_same snd_conv)
  qed
qed


definition e_smaller_than_t_weaker where
  "e_smaller_than_t_weaker e t u lt S \<longleftrightarrow> (\<forall>\<phi>\<in>S. \<exists>\<phi>'\<in>S. fst \<phi> u = fst \<phi>' u \<and> lt (e (snd \<phi>)) (fst \<phi>' t))"


lemma exists_terminates_loop:
  assumes "wfP lt"
      and "\<And>v. \<Turnstile> { (\<lambda>S. \<exists>\<phi>\<in>S. e (snd \<phi>) = v \<and> b (snd \<phi>) \<and> P \<phi> S) } if_then b C { (\<lambda>S. \<exists>\<phi>\<in>S. lt (e (snd \<phi>)) v \<and> P \<phi> S) }"
      and "\<And>\<phi>. \<Turnstile> { P \<phi> } while_cond b C { Q \<phi> }"
    shows "\<Turnstile> { (\<lambda>S. \<exists>\<phi>\<in>S. P \<phi> S) } while_cond b C { (\<lambda>S. \<exists>\<phi>\<in>S. Q \<phi> S)}"
proof (rule hyper_hoare_tripleI)
  fix S assume asm0: "\<exists>\<phi>\<in>S. P \<phi> S"
  then obtain \<phi> where "\<phi> \<in> S" "P \<phi> S" by blast
  show "\<exists>\<phi>\<in>sem (while_cond b C) S. Q \<phi> (sem (while_cond b C) S)"
  proof (cases "b (snd \<phi>)")
    case True

    let ?R = "{(x, y). lt x y}"
    let ?Q = "{ e (snd \<phi>') |\<phi>' n. \<phi>' \<in> iterate_sem n (if_then b C) S \<and> b (snd \<phi>') \<and> P \<phi>' (iterate_sem n (if_then b C) S) }"
  
    have main_res: "\<exists>n \<phi>'. \<phi>' \<in> iterate_sem n (if_then b C) S \<and> \<not> b (snd \<phi>') \<and> P \<phi>' (iterate_sem n (if_then b C) S)"
    proof (rule wfE_min)
      show "wf ?R"
        using assms(1) wfP_def by blast
      show "e (snd \<phi>) \<in> ?Q"
        using True \<open>P \<phi> S\<close> \<open>\<phi> \<in> S\<close> iterate_sem.simps(1) by fastforce
      fix z
      assume asm1: "z \<in> ?Q" "\<And>y. (y, z) \<in> ?R \<Longrightarrow> y \<notin> ?Q"
      then obtain n \<phi>' where "\<phi>' \<in> iterate_sem n (if_then b C) S" "b (snd \<phi>')" "P \<phi>' (iterate_sem n (if_then b C) S)" "z = e (snd \<phi>')"
        by blast
      then have "(\<lambda>S. \<exists>\<phi>\<in>S. (b (snd \<phi>) \<longrightarrow> lt (e (snd \<phi>)) z) \<and> P \<phi> S) (sem (if_then b C) ((iterate_sem n (if_then b C) S)))"
        using assms(2) hyper_hoare_tripleE by blast
      then obtain \<phi>'' where "(b (snd \<phi>'') \<longrightarrow> lt (e (snd \<phi>'')) z) \<and> P \<phi>'' (sem (if_then b C) ((iterate_sem n (if_then b C) S)))"
        "\<phi>'' \<in> (sem (if_then b C) ((iterate_sem n (if_then b C) S)))"
        by blast
      then have "\<not> b (snd \<phi>'')"
        by (metis (mono_tags, lifting) asm1(2) case_prodI iterate_sem.simps(2) mem_Collect_eq)
      then show "\<exists>n \<phi>'. \<phi>' \<in> iterate_sem n (if_then b C) S \<and> \<not> b (snd \<phi>') \<and> P \<phi>' (iterate_sem n (if_then b C) S)"
        by (metis \<open>(b (snd \<phi>'') \<longrightarrow> lt (e (snd \<phi>'')) z) \<and> P \<phi>'' (sem (if_then b C) (iterate_sem n (if_then b C) S))\<close> \<open>\<phi>'' \<in> sem (if_then b C) (iterate_sem n (if_then b C) S)\<close> iterate_sem.simps(2))
    qed
    then obtain n \<phi>' where "\<phi>' \<in> iterate_sem n (if_then b C) S" "\<not> b (snd \<phi>')" "P \<phi>' (iterate_sem n (if_then b C) S)"
      by blast
    then have "\<exists>\<phi>\<in>sem (while_cond b C) (iterate_sem n (if_then b C) S). Q \<phi> (sem (while_cond b C) (iterate_sem n (if_then b C) S))"
      using while_exists[of P b C Q] assms(3) hyper_hoare_tripleE by blast
    then show "\<exists>\<phi>\<in>sem (while_cond b C) S. Q \<phi> (sem (while_cond b C) S)"
      by (simp add: unroll_while_sem)
  next
    case False
    then show ?thesis
    using while_exists[of P b C Q] assms(3) hyper_hoare_tripleE \<open>P \<phi> S\<close> \<open>\<phi> \<in> S\<close> by blast
  qed
qed

definition t_closed where
  "t_closed P P_inf \<longleftrightarrow> (\<forall>S. converges_sets S \<and> (\<forall>n. P n (S n)) \<longrightarrow> P_inf (\<Union>n. S n))"

lemma t_closedE:
  assumes "t_closed P P_inf"
      and "converges_sets S"
      and "\<And>n. P n (S n)"
    shows "P_inf (\<Union>n. S n)"
  using TotalLogic.t_closed_def assms(1) assms(2) assms(3) by blast


subsection \<open>Total version of core rules\<close>

lemma total_skip_rule:
  "\<Turnstile>TERM {P} Skip {P}"
  by (meson SemSkip skip_rule total_hyper_triple_def)

lemma total_seq_rule:
  assumes "\<Turnstile>TERM {P} C1 {R}"
    and "\<Turnstile>TERM {R} C2 {Q}"
  shows "\<Turnstile>TERM {P} Seq C1 C2 {Q}"
proof (rule total_hyper_tripleI)
  show "\<Turnstile> {P} C1 ;; C2 {Q}"
    using assms(1) assms(2) seq_rule total_hyper_triple_def by blast
  fix \<phi> S assume "P S \<and> \<phi> \<in> S"
  then obtain \<sigma>' where "\<langle>C1, snd \<phi>\<rangle> \<rightarrow> \<sigma>'" "(fst \<phi>, \<sigma>') \<in> sem C1 S"
    using assms(1) total_hyper_tripleE by blast
  then obtain \<sigma>'' where "\<langle>C2, \<sigma>'\<rangle> \<rightarrow> \<sigma>''"
    using assms
    by (metis (full_types) \<open>P S \<and> \<phi> \<in> S\<close> hyper_hoare_tripleE snd_conv total_hyper_triple_def)
  then show "\<exists>\<sigma>''. \<langle>C1 ;; C2, snd \<phi>\<rangle> \<rightarrow> \<sigma>''"
    using SemSeq \<open>\<langle>C1, snd \<phi>\<rangle> \<rightarrow> \<sigma>'\<close> by blast
qed

lemma total_if_rule:
  assumes "\<Turnstile>TERM {P} C1 {Q1}"
      and "\<Turnstile>TERM {P} C2 {Q2}"
    shows "\<Turnstile>TERM {P} If C1 C2 {join Q1 Q2}"
proof (rule total_hyper_tripleI)
  show "\<Turnstile> {P} stmt.If C1 C2 {join Q1 Q2}"
    using assms(1) assms(2) if_rule total_hyper_triple_equiv by blast
  fix \<phi> S assume "P S \<and> \<phi> \<in> S"
  then show "\<exists>\<sigma>'. \<langle>stmt.If C1 C2, snd \<phi>\<rangle> \<rightarrow> \<sigma>'"
    using SemIf1 assms(1) total_hyper_tripleE by blast
qed


lemma total_rule_exists:
  assumes "\<And>x. \<Turnstile>TERM {P x} C {Q x}"
  shows "\<Turnstile>TERM {exists P} C {exists Q}"
  using total_hyper_tripleI[of "exists P" C "exists Q"]
  by (metis (mono_tags, lifting) Loops.exists_def assms hyper_hoare_triple_def total_hyper_triple_def)


lemma total_assign_rule:
  "\<Turnstile>TERM { (\<lambda>S. P { (l, \<sigma>(x := e \<sigma>)) |l \<sigma>. (l, \<sigma>) \<in> S }) } (Assign x e) {P}"
  using total_hyper_tripleI[of _ "Assign x e" P]
  using SemAssign assign_rule by fastforce

lemma total_havoc_rule:
  "\<Turnstile>TERM { (\<lambda>S. P { (l, \<sigma>(x := v)) |l \<sigma> v. (l, \<sigma>) \<in> S }) } (Havoc x) {P}"
  using total_hyper_tripleI[of _ "Havoc x" P]
  using SemHavoc havoc_rule by fastforce

lemma in_semI:
  assumes "\<phi> \<in> S"
      and "fst \<phi> = fst \<phi>'"
      and "single_sem C (snd \<phi>) (snd \<phi>')"
    shows "\<phi>' \<in> sem C S"
  using assms
  by (metis (no_types, lifting) prod.collapse single_step_then_in_sem)


theorem normal_while_tot_stronger:
  fixes P :: "nat \<Rightarrow> ('lvar, 'lval, 'pvar, 'pval) state set \<Rightarrow> bool"

  assumes "\<And>n. \<Turnstile> {P n} Assume b {Q n}"
      and "\<And>n. \<Turnstile>TERM {conj (Q n) (e_recorded_in_t e t)} C {conj (P (Suc n)) (e_smaller_than_t_weaker e t u lt)}"
      and "\<Turnstile> {natural_partition P} Assume (lnot b) {R}"

      and "wfP lt"
      and "\<And>n. not_fv_hyper t (P n)"
      and "\<And>n. not_fv_hyper t (Q n)"

      and "\<And>n. not_fv_hyper u (P n)"
      and "\<And>n. not_fv_hyper u (Q n)"

      and "(tr :: 'lval) \<noteq> fa"
      and "u \<noteq> t"

    shows "\<Turnstile>TERM {P 0} while_cond b C {R}"
proof (rule total_hyper_triple_altI)
  fix S :: "('lvar, 'lval, 'pvar, 'pval) state set"
  assume asm0: "P 0 S"
  have "\<And>n. P n (iterate_sem n (Assume b;; C) S)"
  proof (rule indexed_invariant_then_power)
    fix n
    have "\<Turnstile> {Q n} C {P (Suc n)}"
    proof (rule hyper_hoare_tripleI)
      fix S assume asm1: "Q n S"
      let ?S = "assign_exp_to_lvar_set e t S"
      have "conj (Q n) (e_recorded_in_t e t) ?S"
        by (metis asm1 assms(6) conj_def e_recorded_in_t_if_assigned not_fv_hyper_assign_exp)
      then have "conj (P (Suc n)) (e_smaller_than_t_weaker e t u lt) (sem C ?S)"
        using assms(2) hyper_hoare_tripleE total_hyper_triple_def by blast
      then show "P (Suc n) (sem C S)"
        using assign_exp_to_lvar_set_same_mod_updates[of t] assms(5) conj_def not_fv_hyperE[of t "P (Suc n)"] same_mod_updates_sym[of "{t}"] sem_update_commute[of "{t}"]
        by metis
    qed
    then show " \<Turnstile> {P n} Assume b ;; C {P (Suc n)}"
      using assms(1) seq_rule total_hyper_triple_def by blast
  qed (simp add: asm0)
  then have "natural_partition P (\<Union>n. iterate_sem n (Assume b;; C) S)"
    by (simp add: natural_partitionI)
  then show "R (sem (while_cond b C) S)"
    using SUP_cong assms(3) hyper_hoare_triple_def[of "natural_partition P" "Assume (lnot b)" R] sem_seq sem_while while_cond_def
    by metis


  show "terminates_in (while_cond b C) S"
  proof (rule terminates_in_while_loop)
    show "wfP lt"
      by (simp add: assms(4))
    fix \<phi> n
    assume asm1: "\<phi> \<in> iterate_sem n (Assume b ;; C) S \<and> b (snd \<phi>)"

    let ?S = "assign_exp_to_lvar_set e t (iterate_sem n (Assume b;; C) S)"
    let ?\<phi> = "assign_exp_to_lvar e t \<phi>"

    let ?SS = "update_lvar_set u (\<lambda>\<phi>'. if \<phi>' = ?\<phi> then tr else fa) ?S" 

    have SS_def: "?SS = { ((fst \<phi>')(u := if \<phi>' = ?\<phi> then tr else fa), snd \<phi>') |\<phi>'. \<phi>' \<in> ?S}"
      by (simp add: update_lvar_set_def)

    have same: "same_mod_updates {u} ?S ?SS"
      by (meson same_update_lvar_set)


    let ?\<phi>' = "((fst ?\<phi>)(u := tr), snd ?\<phi>)"

    have "conj (P n) (e_recorded_in_t e t) ?S"
      by (metis \<open>\<And>n. P n (iterate_sem n (Assume b ;; C) S)\<close> assms(5) conj_def e_recorded_in_t_if_assigned not_fv_hyper_assign_exp)
    moreover have "e_recorded_in_t e t ?SS"
    proof (rule e_recorded_in_tI)
      fix \<phi>' assume "\<phi>' \<in> ?SS"
      then show "fst \<phi>' t = e (snd \<phi>')" unfolding SS_def
        using assms(10) e_recorded_in_t_def e_recorded_in_t_if_assigned by fastforce
    qed

    then have "conj (P n) (e_recorded_in_t e t) ?SS"
      using assms(7) calculation conj_def not_fv_hyperE[of u "P n"] same
      by metis
    then have "conj (Q n) (e_recorded_in_t e t) (sem (Assume b) ?SS)"
      using assms(1) assume_sem[of b] conj_def e_recorded_in_t_def[of e t] hyper_hoare_tripleE[of "P n" "Assume b" "Q n"
          "update_lvar_set u (\<lambda>\<phi>'. if \<phi>' = assign_exp_to_lvar e t \<phi> then tr else fa) (assign_exp_to_lvar_set e t (iterate_sem n (Assume b ;; C) S))"] member_filter[of _ "b \<circ> snd"]
      by metis
    then have "conj (P (Suc n)) (e_smaller_than_t_weaker e t u lt) (sem C (sem (Assume b) ?SS))"
      using assms(2) hyper_hoare_tripleE total_hyper_triple_def by blast
    moreover have "?\<phi> \<in> (sem (Assume b) ?S)"
      by (metis asm1 assign_exp_to_lvar_set_def assume_sem comp_apply image_eqI member_filter same_outside_set_lvar_assign_exp)
    moreover have "?\<phi>' \<in> (sem (Assume b) ?SS)"
      unfolding SS_def
    proof (rule in_semI)
      show "((fst ?\<phi>)(u := if ?\<phi> = assign_exp_to_lvar e t \<phi> then tr else fa), snd ?\<phi>) \<in> {((fst \<phi>')(u := if \<phi>' = assign_exp_to_lvar e t \<phi> then tr else fa), snd \<phi>') |\<phi>'. \<phi>' \<in> assign_exp_to_lvar_set e t (iterate_sem n (Assume b ;; C) S)}"        
        using asm1 assign_exp_to_lvar_set_def by fastforce
      show "fst ((fst (assign_exp_to_lvar e t \<phi>))(u := if assign_exp_to_lvar e t \<phi> = assign_exp_to_lvar e t \<phi> then tr else fa), snd (assign_exp_to_lvar e t \<phi>)) =
    fst ((fst (assign_exp_to_lvar e t \<phi>))(u := tr), snd (assign_exp_to_lvar e t \<phi>))"
        by presburger
      show "\<langle>Assume
      b, snd ((fst (assign_exp_to_lvar e t \<phi>))(u := if assign_exp_to_lvar e t \<phi> = assign_exp_to_lvar e t \<phi> then tr else fa),
              snd (assign_exp_to_lvar e t \<phi>))\<rangle> \<rightarrow> snd ((fst (assign_exp_to_lvar e t \<phi>))(u := tr), snd (assign_exp_to_lvar e t \<phi>))"
        by (metis SemAssume asm1 same_outside_set_lvar_assign_exp snd_conv)
    qed
    then obtain \<sigma>' where "(fst ?\<phi>', \<sigma>') \<in> sem C (sem (Assume b) ?SS) \<and> \<langle>C, snd ?\<phi>'\<rangle> \<rightarrow> \<sigma>'"
      using total_hyper_tripleE assms(2)[of n]
      using \<open>Logic.conj (Q n) (e_recorded_in_t e t) (sem (Assume b) (update_lvar_set u (\<lambda>\<phi>'. if \<phi>' = assign_exp_to_lvar e t \<phi> then tr else fa) (assign_exp_to_lvar_set e t (iterate_sem n (Assume b ;; C) S))))\<close> by blast
    moreover obtain \<phi>' where "\<phi>' \<in> sem C (sem (Assume b) ?SS)" "fst (fst ?\<phi>', \<sigma>') u = fst \<phi>' u \<and> lt (e (snd (fst ?\<phi>', \<sigma>'))) (fst \<phi>' t)"
      using calculation conj_def[of "P (Suc n)" "e_smaller_than_t_weaker e t u lt"] e_smaller_than_t_weaker_def[of e t u lt]
      by meson
    then have "fst \<phi>' u = tr"
      by simp
    moreover have "fst ?\<phi> t = fst \<phi>' t \<and> single_sem C (snd \<phi>) (snd \<phi>')"
    proof -
      obtain \<phi>0 where "\<phi>0 \<in> sem (Assume b) ?SS" "fst \<phi>0 = fst \<phi>'" "single_sem C (snd \<phi>0) (snd \<phi>')"
        by (metis (no_types, lifting) \<open>\<phi>' \<in> sem C (sem (Assume b) (update_lvar_set u (\<lambda>\<phi>'. if \<phi>' = assign_exp_to_lvar e t \<phi> then tr else fa) (assign_exp_to_lvar_set e t (iterate_sem n (Assume b ;; C) S))))\<close> fst_conv in_sem snd_conv)
      then have "\<phi>0 \<in> ?SS"
        by (metis (no_types, lifting) assume_sem member_filter)
      then obtain \<phi>0' where 
        "\<phi>0' \<in> (assign_exp_to_lvar_set e t (iterate_sem n (Assume b ;; C) S))"
        "\<phi>0 = ((fst \<phi>0')(u := if \<phi>0' = assign_exp_to_lvar e t \<phi> then tr else fa), snd \<phi>0')"
        using SS_def by auto
      then have "\<phi>0 = ((fst ?\<phi>)(u := tr), snd ?\<phi>)"
        by (metis (full_types) \<open>fst \<phi>0 = fst \<phi>'\<close> assms(9) calculation(5) fst_conv fun_upd_same)
      then show ?thesis
        by (metis \<open>\<langle>C, snd \<phi>0\<rangle> \<rightarrow> snd \<phi>'\<close> \<open>fst \<phi>0 = fst \<phi>'\<close> assms(10) fst_conv fun_upd_other same_outside_set_lvar_assign_exp snd_conv)
    qed
    ultimately show "\<exists>\<sigma>'. (\<langle>C, snd \<phi>\<rangle> \<rightarrow> \<sigma>') \<and> (\<not> b \<sigma>' \<or> lt (e \<sigma>') (e (snd \<phi>)))"
      by (metis (no_types, lifting) \<open>fst (fst ((fst (assign_exp_to_lvar e t \<phi>))(u := tr), snd (assign_exp_to_lvar e t \<phi>)), \<sigma>') u = fst \<phi>' u \<and> lt (e (snd (fst ((fst (assign_exp_to_lvar e t \<phi>))(u := tr), snd (assign_exp_to_lvar e t \<phi>)), \<sigma>'))) (fst \<phi>' t)\<close> assign_exp_to_lvar_def fst_conv fun_upd_same snd_conv)
  qed
qed




end