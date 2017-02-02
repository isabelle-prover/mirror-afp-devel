theory Weak_Bisimilarity_Implies_Equivalence
imports
  Weak_Logical_Equivalence
begin

section \<open>Weak Bisimilarity Implies Weak Logical Equivalence\<close>

context indexed_weak_nominal_ts
begin

  lemma weak_bisimilarity_implies_weak_equivalence_Act:
    assumes "\<And>P Q. P \<approx>\<cdot> Q \<Longrightarrow> P \<Turnstile> x \<longleftrightarrow> Q \<Turnstile> x"
    and "P \<approx>\<cdot> Q"
    -- \<open>not needed: and @{prop "weak_formula x"}\<close>
    and "P \<Turnstile> Act \<alpha> x"
    shows "Q \<Turnstile> Act \<alpha> x"
  proof -
    have "finite (supp Q)"
      by (fact finite_supp)
    with `P \<Turnstile> Act \<alpha> x` obtain \<alpha>' x' P' where eq: "Act \<alpha> x = Act \<alpha>' x'" and trans: "P \<Rightarrow>\<langle>\<alpha>'\<rangle> P'" and valid: "P' \<Turnstile> x'" and fresh: "bn \<alpha>' \<sharp>* Q"
      by (metis valid_Act_strong)

    from `P \<approx>\<cdot> Q` and fresh and trans obtain Q' where trans': "Q \<Rightarrow>\<langle>\<alpha>'\<rangle> Q'" and bisim': "P' \<approx>\<cdot> Q'"
      by (metis weakly_bisimilar_weak_simulation_step)

    from eq obtain p where px: "x' = p \<bullet> x"
      by (auto simp add: Act_eq_iff Act\<^sub>\<alpha>_eq_iff alphas) (metis Rep_formula_inverse Tree\<^sub>\<alpha>.abs_eq_iff Tree\<^sub>\<alpha>_abs_rep permute_Tree\<^sub>\<alpha>.abs_eq permute_formula.rep_eq)

    with valid have "-p \<bullet> P' \<Turnstile> x"
      by (metis permute_minus_cancel(2) valid_eqvt)
    moreover from bisim' have "(-p \<bullet> P') \<approx>\<cdot> (-p \<bullet> Q')"
      by (metis weakly_bisimilar_eqvt)
    ultimately have "-p \<bullet> Q' \<Turnstile> x"
      using `\<And>P Q. P \<approx>\<cdot> Q \<Longrightarrow> P \<Turnstile> x \<longleftrightarrow> Q \<Turnstile> x` by metis
    with px have "Q' \<Turnstile> x'"
      by (metis permute_minus_cancel(1) valid_eqvt)

    with eq and trans' show "Q \<Turnstile> Act \<alpha> x"
      unfolding valid_Act by metis
  qed

  lemma weak_bisimilarity_implies_weak_equivalence_Pred:
    assumes "\<And>P Q. P \<approx>\<cdot> Q \<Longrightarrow> P \<Turnstile> x \<longleftrightarrow> Q \<Turnstile> x"
    and "P \<approx>\<cdot> Q"
    -- \<open>not needed: and @{prop "weak_formula x"}\<close>
    and "P \<Turnstile> Act \<tau> (Conj (binsert (Pred \<phi>) (bsingleton x)))"
    shows "Q \<Turnstile> Act \<tau> (Conj (binsert (Pred \<phi>) (bsingleton x)))"
  proof -
    let ?c = "Conj (binsert (Pred \<phi>) (bsingleton x))"

    have "bn \<tau>  \<sharp>* P"
      by (simp add: fresh_star_def)
    with `P \<Turnstile> Act \<tau> ?c` obtain P' where trans: "P \<Rightarrow>\<langle>\<tau>\<rangle> P'" and valid: "P' \<Turnstile> ?c"
      by (metis valid_Act_fresh)

    have "bn \<tau>  \<sharp>* Q"
      by (simp add: fresh_star_def)
    with `P \<approx>\<cdot> Q` and trans obtain Q' where trans': "Q \<Rightarrow>\<langle>\<tau>\<rangle> Q'" and bisim': "P' \<approx>\<cdot> Q'"
      by (metis weakly_bisimilar_weak_simulation_step)

    from valid have *: "P' \<turnstile> \<phi>" and **: "P' \<Turnstile> x"
      by (simp add: binsert.rep_eq)+

    from bisim' and * obtain Q'' where trans'': "Q' \<Rightarrow> Q''" and bisim'': "P' \<approx>\<cdot> Q''" and ***: "Q'' \<turnstile> \<phi>"
      by (metis is_weak_bisimulation_def weakly_bisimilar_is_weak_bisimulation)

    from bisim'' and ** have "Q'' \<Turnstile> x"
      using `\<And>P Q. P \<approx>\<cdot> Q \<Longrightarrow> P \<Turnstile> x \<longleftrightarrow> Q \<Turnstile> x` by metis
    with *** have "Q'' \<Turnstile> ?c"
      by (simp add: binsert.rep_eq)

    moreover from trans' and trans'' have "Q \<Rightarrow>\<langle>\<tau>\<rangle> Q''"
      using tau_refl weak_transition_weakI by blast

    ultimately show "Q \<Turnstile> Act \<tau> ?c"
      unfolding valid_Act by metis
  qed

  theorem weak_bisimilarity_implies_weak_equivalence: assumes "P \<approx>\<cdot> Q" shows "P \<equiv>\<cdot> Q"
  proof -
  {
    fix x :: "('idx, 'pred, 'act) formula"
    assume "weak_formula x"
      then have "\<And>P Q. P \<approx>\<cdot> Q \<Longrightarrow> P \<Turnstile> x \<longleftrightarrow> Q \<Turnstile> x"
    proof (induct rule: weak_formula.induct)
      case (wf_Conj xset) then show ?case
        by simp
    next
      case (wf_Not x) then show ?case
        by simp
    next
      case (wf_Act x \<alpha>) then show ?case
        by (metis weakly_bisimilar_symp weak_bisimilarity_implies_weak_equivalence_Act sympE)
    next
      case (wf_Pred x \<alpha> \<phi>) then show ?case
        by (metis weakly_bisimilar_symp weak_bisimilarity_implies_weak_equivalence_Pred sympE)
      qed
    }
    with assms show ?thesis
      unfolding weakly_logically_equivalent_def by simp
  qed

end

end
