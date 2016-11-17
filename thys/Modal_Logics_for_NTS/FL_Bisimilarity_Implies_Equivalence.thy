theory FL_Bisimilarity_Implies_Equivalence
imports
  FL_Logical_Equivalence
begin

section \<open>\texorpdfstring{$F/L$}{F/L}-Bisimilarity Implies Logical Equivalence\<close>

context indexed_effect_nominal_ts
begin

  lemma FL_bisimilarity_implies_equivalence_Act:
    assumes "f \<in>\<^sub>f\<^sub>s F"
    and "bn \<alpha> \<sharp>* F"
    and "x \<in> \<A>[L (\<alpha>, F)]"
    and "\<And>P Q. P \<sim>\<cdot>[L (\<alpha>, F)] Q \<Longrightarrow> P \<Turnstile> x \<longleftrightarrow> Q \<Turnstile> x"
    and "P \<sim>\<cdot>[F] Q"
    and "P \<Turnstile> Act f \<alpha> x"
    shows "Q \<Turnstile> Act f \<alpha> x"
  proof -
    have "finite (supp (\<langle>f\<rangle>Q, F))"
      by (fact finite_supp)
    with `P \<Turnstile> Act f \<alpha> x` obtain \<alpha>' x' P' where alpha: "Act f \<alpha> x = Act f \<alpha>' x'" and trans: "\<langle>f\<rangle>P \<rightarrow> \<langle>\<alpha>',P'\<rangle>" and valid: "P' \<Turnstile> x'" and fresh: "bn \<alpha>' \<sharp>* (\<langle>f\<rangle>Q, F)"
      by (metis valid_Act_strong)

    from `P \<sim>\<cdot>[F] Q` and `f \<in>\<^sub>f\<^sub>s F` and fresh and trans obtain Q' where trans': "\<langle>f\<rangle>Q \<rightarrow> \<langle>\<alpha>',Q'\<rangle>" and bisim': "P' \<sim>\<cdot>[L (\<alpha>',F)] Q'"
      by (metis FL_bisimilar_simulation_step)

    from alpha obtain p where p_\<alpha>: "\<alpha>' = p \<bullet> \<alpha>" and p_x: "x' = p \<bullet> x"
        and fresh_p: "(supp x - bn \<alpha>) \<sharp>* p \<and> (supp \<alpha> - bn \<alpha>) \<sharp>* p"
        and supp_p: "supp p \<subseteq> bn \<alpha> \<union> p \<bullet> bn \<alpha>"
      by (metis Act_eq_iff_perm_renaming)

    from valid and p_x have "-p \<bullet> P' \<Turnstile> x"
      by (metis permute_minus_cancel(2) valid_eqvt)

    moreover from fresh and p_\<alpha> have "(p \<bullet> bn \<alpha>) \<sharp>* F"
      by (simp add: bn_eqvt fresh_star_Pair)
    with `bn \<alpha> \<sharp>* F` and supp_p have "supp F \<sharp>* p"
      by (meson UnE fresh_def fresh_star_def subsetCE)
    with bisim' and p_\<alpha> have "(-p \<bullet> P') \<sim>\<cdot>[L (\<alpha>, F)] (-p \<bullet> Q')"
      by (metis FL_bisimilar_eqvt L_eqvt' permute_minus_cancel(2) supp_perm_eq)

    ultimately have "-p \<bullet> Q' \<Turnstile> x"
      using `\<And>P Q. P \<sim>\<cdot>[L (\<alpha>, F)] Q \<Longrightarrow> P \<Turnstile> x \<longleftrightarrow> Q \<Turnstile> x` by metis

    with p_x have "Q' \<Turnstile> x'"
      by (metis permute_minus_cancel(1) valid_eqvt)

    with alpha and trans' show "Q \<Turnstile> Act f \<alpha> x"
      unfolding valid_Act by metis
  qed

  theorem FL_bisimilarity_implies_equivalence: assumes "P \<sim>\<cdot>[F] Q" shows "FL_logically_equivalent F P Q"
  unfolding FL_logically_equivalent_def proof
    fix x :: "('idx, 'pred, 'act, 'effect) formula"
    show "x \<in> \<A>[F] \<longrightarrow> P \<Turnstile> x \<longleftrightarrow> Q \<Turnstile> x"
    proof
      assume "x \<in> \<A>[F]" then show "P \<Turnstile> x \<longleftrightarrow> Q \<Turnstile> x"
      using assms proof (induction x arbitrary: P Q)
        case Conj then show ?case
          by simp
      next
        case Not then show ?case
          by simp
      next
        case Pred then show ?case
          by (metis FL_bisimilar_is_L_bisimulation is_L_bisimulation_def symp_def valid_Pred)
      next
        case Act then show ?case
          by (metis FL_bisimilar_symp FL_bisimilarity_implies_equivalence_Act sympE)
      qed
    qed
  qed

end

end
