chapter \<open> Suppes' Theorem \label{sec:suppes-theorem} \<close>

theory Suppes_Theorem
  imports Probability_Logic
begin

no_notation FuncSet.funcset (infixr "\<rightarrow>" 60)

text \<open> An elementary completeness theorem for inequalities for probability logic
       is due to Patrick Suppes @{cite suppesProbabilisticInferenceConcept1966}. \<close>

text \<open> A consequence of this Suppes' theorem is an elementary form of \<^emph>\<open>collapse\<close>,
       which asserts that inequalities for probabilities are logically
       equivalent to the more restricted class of \<^emph>\<open>Dirac measures\<close> as
       defined in \S\ref{sec:dirac-measures}. \<close>

section \<open> Suppes' List Theorem \label{sec:suppes-theorem-for-lists} \<close>

text \<open> We first establish Suppes' theorem for lists of propositions. This
       is done by establishing our first completeness theorem using
       \<^emph>\<open>Dirac measures\<close>. \<close>

text \<open> First, we use the result from \S\ref{sec:basic-probability-inequality-results}
       that shows \<open>\<turnstile> \<phi> \<rightarrow> \<Squnion> \<Psi>\<close> implies \<open>\<P> \<phi> \<le> (\<Sum>\<psi>\<leftarrow>\<Psi>. \<P> \<psi>)\<close>.
       This can be understood as a \<^emph>\<open>soundness\<close> result. \<close>

text \<open> To show completeness, assume \<open>\<not> \<turnstile> \<phi> \<rightarrow> \<Squnion> \<Psi>\<close>. From this
       obtain a maximally consistent \<^term>\<open>\<Omega>\<close> such that \<open>\<phi> \<rightarrow> \<Squnion> \<Psi> \<notin> \<Omega>\<close>. 
       We then define \<^term>\<open>\<delta> \<chi> = (if (\<chi> \<in> \<Omega>) then 1 else 0)\<close> and 
       show \<^term>\<open>\<delta>\<close> is a  \<^emph>\<open>Dirac measure\<close> such that \<open>\<delta> \<phi> \<le> (\<Sum>\<psi>\<leftarrow>\<Psi>. \<delta> \<psi>)\<close>. \<close>

lemma (in classical_logic) dirac_list_summation_completeness:
  "(\<forall> \<delta> \<in> dirac_measures. \<delta> \<phi> \<le> (\<Sum>\<psi>\<leftarrow>\<Psi>. \<delta> \<psi>)) = \<turnstile> \<phi> \<rightarrow> \<Squnion> \<Psi>"
proof -
  {
    fix \<delta> :: "'a \<Rightarrow> real"
    assume "\<delta> \<in> dirac_measures"
    from this interpret probability_logic "(\<lambda> \<phi>. \<turnstile> \<phi>)" "(\<rightarrow>)" "\<bottom>" "\<delta>"
      unfolding dirac_measures_def
      by auto
    assume "\<turnstile> \<phi> \<rightarrow> \<Squnion> \<Psi>"
    hence "\<delta> \<phi> \<le> (\<Sum>\<psi>\<leftarrow>\<Psi>. \<delta> \<psi>)"
      using implication_list_summation_inequality
      by auto
  }
  moreover {
    assume "\<not> \<turnstile> \<phi> \<rightarrow> \<Squnion> \<Psi>"
    from this obtain \<Omega> where \<Omega>:
      "MCS \<Omega>"
      "\<phi> \<in> \<Omega>"
      "\<Squnion> \<Psi> \<notin> \<Omega>"
      by (meson
            insert_subset
            formula_consistent_def
            formula_maximal_consistency
            formula_maximally_consistent_extension
            formula_maximally_consistent_set_def_def
            set_deduction_base_theory
            set_deduction_reflection
            set_deduction_theorem)
    hence"\<forall> \<psi> \<in> set \<Psi>. \<psi> \<notin> \<Omega>"
      using arbitrary_disjunction_exclusion_MCS by blast
    define \<delta> where "\<delta> = (\<lambda> \<chi> . if \<chi>\<in>\<Omega> then (1 :: real) else 0)"
    from \<open>\<forall> \<psi> \<in> set \<Psi>. \<psi> \<notin> \<Omega>\<close> have "(\<Sum>\<psi>\<leftarrow>\<Psi>. \<delta> \<psi>) = 0"
      unfolding \<delta>_def
      by (induct \<Psi>, simp, simp)
    hence "\<not> \<delta> \<phi> \<le> (\<Sum>\<psi>\<leftarrow>\<Psi>. \<delta> \<psi>)"
      unfolding \<delta>_def
      by (simp add: \<Omega>(2))
    hence
      "\<exists> \<delta> \<in> dirac_measures. \<not> (\<delta> \<phi> \<le> (\<Sum>\<psi>\<leftarrow>\<Psi>. \<delta> \<psi>))"
      unfolding \<delta>_def
      using \<Omega>(1) MCS_dirac_measure by auto
  }
  ultimately show ?thesis by blast
qed

theorem (in classical_logic) list_summation_completeness:
  "(\<forall> \<P> \<in> probabilities. \<P> \<phi> \<le> (\<Sum>\<psi>\<leftarrow>\<Psi>. \<P> \<psi>)) = \<turnstile> \<phi> \<rightarrow> \<Squnion> \<Psi>"
  (is "?lhs = ?rhs")
proof
  assume ?lhs
  hence "\<forall> \<delta> \<in> dirac_measures. \<delta> \<phi> \<le> (\<Sum>\<psi>\<leftarrow>\<Psi>. \<delta> \<psi>)"
    unfolding dirac_measures_def probabilities_def
    by blast
  thus ?rhs
    using dirac_list_summation_completeness by blast
next
  assume ?rhs
  show ?lhs
  proof
    fix \<P> :: "'a \<Rightarrow> real"
    assume "\<P> \<in> probabilities"
    from this interpret probability_logic "(\<lambda> \<phi>. \<turnstile> \<phi>)" "(\<rightarrow>)" \<bottom> \<P>
      unfolding probabilities_def
      by auto
    show "\<P> \<phi> \<le> (\<Sum>\<psi>\<leftarrow>\<Psi>. \<P> \<psi>)"
      using \<open>?rhs\<close> implication_list_summation_inequality
      by simp
  qed
qed

text \<open> The collapse theorem asserts that to prove an inequalities for all 
       probabilities in probability logic, one only needs to consider the 
       case of functions which take on values of 0 or 1. \<close>

lemma (in classical_logic) suppes_collapse:
  "(\<forall> \<P> \<in> probabilities. \<P> \<phi> \<le> (\<Sum>\<psi>\<leftarrow>\<Psi>. \<P> \<psi>))
      = (\<forall> \<delta> \<in> dirac_measures. \<delta> \<phi> \<le> (\<Sum>\<psi>\<leftarrow>\<Psi>. \<delta> \<psi>))"
  by (simp add:
        dirac_list_summation_completeness
        list_summation_completeness)

lemma (in classical_logic) probability_member_neg:
  fixes \<P>
  assumes "\<P> \<in> probabilities"
  shows "\<P> (\<sim> \<phi>) = 1 - \<P> \<phi>"
proof -
  from assms interpret probability_logic "(\<lambda> \<phi>. \<turnstile> \<phi>)" "(\<rightarrow>)" \<bottom> \<P>
    unfolding probabilities_def
    by auto
  show ?thesis
    by (simp add: complementation)
qed

text \<open> Suppes' theorem has a philosophical interpretation.
       It asserts that if \<^term>\<open>\<Psi> :\<turnstile> \<phi>\<close>, then our \<^emph>\<open>uncertainty\<close>
       in \<^term>\<open>\<phi>\<close> is bounded above by our uncertainty in \<^term>\<open>\<Psi>\<close>.
       Here the uncertainty in the proposition \<^term>\<open>\<phi>\<close> is \<open>1 - \<P> \<phi>\<close>.
       Our uncertainty in \<^term>\<open>\<Psi>\<close>, on the other hand, is
       \<open>\<Sum>\<psi>\<leftarrow>\<Psi>. 1 - \<P> \<psi>\<close>. \<close>

theorem (in classical_logic) suppes_list_theorem:
  "\<Psi> :\<turnstile> \<phi> = (\<forall> \<P> \<in> probabilities. (\<Sum>\<psi>\<leftarrow>\<Psi>. 1 - \<P> \<psi>) \<ge> 1 - \<P> \<phi>)"
proof -
  have
    "\<Psi> :\<turnstile> \<phi> = (\<forall> \<P> \<in> probabilities. (\<Sum>\<psi> \<leftarrow> \<^bold>\<sim> \<Psi>. \<P> \<psi>) \<ge> \<P> (\<sim> \<phi>))"
    using
      list_summation_completeness
      weak_biconditional_weaken
      contra_list_curry_uncurry
      list_deduction_def
    by blast
  moreover have
    "\<forall> \<P> \<in> probabilities. (\<Sum>\<psi> \<leftarrow> (\<^bold>\<sim> \<Psi>). \<P> \<psi>) = (\<Sum>\<psi> \<leftarrow> \<Psi>. \<P> (\<sim> \<psi>))"
    by (induct \<Psi>, auto)
  ultimately show ?thesis
    using probability_member_neg
    by (induct \<Psi>, simp+)
qed

section \<open> Suppes' Set Theorem \<close>

text \<open> Suppes theorem also obtains for \<^emph>\<open>sets\<close>. \<close>

lemma (in classical_logic) dirac_set_summation_completeness:
  "(\<forall> \<delta> \<in> dirac_measures. \<delta> \<phi> \<le> (\<Sum>\<psi>\<in> set \<Psi>. \<delta> \<psi>)) = \<turnstile> \<phi> \<rightarrow> \<Squnion> \<Psi>"
  by (metis
        dirac_list_summation_completeness
        modus_ponens
        arbitrary_disjunction_remdups
        biconditional_left_elimination
        biconditional_right_elimination
        hypothetical_syllogism
        sum.set_conv_list)

theorem (in classical_logic) set_summation_completeness:
  "(\<forall> \<delta> \<in> probabilities. \<delta> \<phi> \<le> (\<Sum>\<psi>\<in> set \<Psi>. \<delta> \<psi>)) = \<turnstile> \<phi> \<rightarrow> \<Squnion> \<Psi>"
  by (metis
        dirac_list_summation_completeness
        dirac_set_summation_completeness
        list_summation_completeness
        sum.set_conv_list)

lemma (in classical_logic) suppes_set_collapse:
  "(\<forall> \<P> \<in> probabilities. \<P> \<phi> \<le> (\<Sum>\<psi> \<in> set \<Psi>. \<P> \<psi>))
      = (\<forall> \<delta> \<in> dirac_measures. \<delta> \<phi> \<le> (\<Sum>\<psi> \<in> set \<Psi>. \<delta> \<psi>))"
  by (simp add:
        dirac_set_summation_completeness
        set_summation_completeness)

text \<open> In our formulation of logic, there is not reason that \<open>\<sim> a = \<sim> b\<close>
       while \<^term>\<open>a \<noteq> b\<close>.  As a consequence the Suppes theorem
       for sets presented below is different than the one given in
       \S\ref{sec:suppes-theorem-for-lists}. \<close>

theorem (in classical_logic) suppes_set_theorem:
  "\<Psi> :\<turnstile> \<phi>
     = (\<forall> \<P> \<in> probabilities. (\<Sum>\<psi> \<in> set (\<^bold>\<sim> \<Psi>). \<P> \<psi>) \<ge> 1 - \<P> \<phi>)"
proof -
  have "\<Psi> :\<turnstile> \<phi>
          = (\<forall> \<P> \<in> probabilities. (\<Sum>\<psi> \<in> set (\<^bold>\<sim> \<Psi>). \<P> \<psi>) \<ge> \<P> (\<sim> \<phi>))"
    using
      contra_list_curry_uncurry
      list_deduction_def
      set_summation_completeness
      weak_biconditional_weaken
    by blast
  thus ?thesis
    using probability_member_neg
    by (induct \<Psi>, auto)
qed

section \<open> Converse Suppes' Theorem \<close>

text \<open> A formulation of the converse of Suppes' theorem obtains
       for lists/sets of \<^emph>\<open>logically disjoint\<close> propositions. \<close>

lemma (in probability_logic) exclusive_sum_list_identity:
  assumes "\<turnstile> \<Coprod> \<Phi>"
  shows "\<P> (\<Squnion> \<Phi>) = (\<Sum>\<phi>\<leftarrow>\<Phi>. \<P> \<phi>)"
  using assms
proof (induct \<Phi>)
  case Nil
  then show ?case
    by (simp add: gaines_weatherson_antithesis)
next
  case (Cons \<phi> \<Phi>)
  assume "\<turnstile> \<Coprod> (\<phi> # \<Phi>)"
  hence "\<turnstile> \<sim> (\<phi> \<sqinter> \<Squnion> \<Phi>)" "\<turnstile> \<Coprod> \<Phi>" by simp+
  hence "\<P> (\<Squnion>(\<phi> # \<Phi>)) = \<P> \<phi> + \<P> (\<Squnion> \<Phi>)"
        "\<P> (\<Squnion> \<Phi>) = (\<Sum>\<phi>\<leftarrow>\<Phi>. \<P> \<phi>)"
    using Cons.hyps probability_additivity by auto
  hence "\<P> (\<Squnion>(\<phi> # \<Phi>)) = \<P> \<phi> + (\<Sum>\<phi>\<leftarrow>\<Phi>. \<P> \<phi>)" by auto
  thus ?case by simp
qed

lemma sum_list_monotone:
  fixes f :: "'a \<Rightarrow> real"
  assumes "\<forall> x. f x \<ge> 0"
     and  "set \<Phi> \<subseteq> set \<Psi>"
     and  "distinct \<Phi>"
   shows "(\<Sum>\<phi>\<leftarrow>\<Phi>. f \<phi>) \<le> (\<Sum>\<psi>\<leftarrow>\<Psi>. f \<psi>)"
  using assms
proof -
  assume "\<forall> x. f x \<ge> 0"
  have "\<forall>\<Phi>. set \<Phi> \<subseteq> set \<Psi>
             \<longrightarrow> distinct \<Phi>
             \<longrightarrow> (\<Sum>\<phi>\<leftarrow>\<Phi>. f \<phi>) \<le> (\<Sum>\<psi>\<leftarrow>\<Psi>. f \<psi>)"
  proof (induct \<Psi>)
    case Nil
    then show ?case by simp
  next
    case (Cons \<psi> \<Psi>)
    {
      fix \<Phi>
      assume "set \<Phi> \<subseteq> set (\<psi> # \<Psi>)"
         and "distinct \<Phi>"
      have "(\<Sum>\<phi>\<leftarrow>\<Phi>. f \<phi>) \<le> (\<Sum>\<psi>'\<leftarrow>(\<psi> # \<Psi>). f \<psi>')"
      proof -
        {
          assume "\<psi> \<notin> set \<Phi>"
          with \<open>set \<Phi> \<subseteq> set (\<psi> # \<Psi>)\<close> have "set \<Phi> \<subseteq> set \<Psi>" by auto
          hence "(\<Sum>\<phi>\<leftarrow>\<Phi>. f \<phi>) \<le> (\<Sum>\<psi>\<leftarrow>\<Psi>. f \<psi>)"
            using Cons.hyps \<open>distinct \<Phi>\<close> by auto
          moreover have "f \<psi> \<ge> 0" using \<open>\<forall> x. f x \<ge> 0\<close> by metis
          ultimately have ?thesis by simp
        }
        moreover
        {
          assume "\<psi> \<in> set \<Phi>"
          hence "set \<Phi> = insert \<psi> (set (removeAll \<psi> \<Phi>))"
            by auto
          with \<open>set \<Phi> \<subseteq> set (\<psi> # \<Psi>)\<close> have "set (removeAll \<psi> \<Phi>) \<subseteq> set \<Psi>"
            by (metis
                  insert_subset
                  list.simps(15)
                  set_removeAll
                  subset_insert_iff)
          moreover from \<open>distinct \<Phi>\<close> have "distinct (removeAll \<psi> \<Phi>)"
            by (meson distinct_removeAll)
          ultimately have "(\<Sum>\<phi>\<leftarrow>(removeAll \<psi> \<Phi>). f \<phi>) \<le> (\<Sum>\<psi>\<leftarrow>\<Psi>. f \<psi>)"
            using Cons.hyps
            by simp
          moreover from \<open>\<psi> \<in> set \<Phi>\<close> \<open>distinct \<Phi>\<close>
          have "(\<Sum>\<phi>\<leftarrow>\<Phi>. f \<phi>) = f \<psi> + (\<Sum>\<phi>\<leftarrow>(removeAll \<psi> \<Phi>). f \<phi>)"
            using distinct_remove1_removeAll sum_list_map_remove1
            by fastforce
          ultimately have ?thesis using \<open>\<forall> x. f x \<ge> 0\<close>
            by simp
        }
        ultimately show ?thesis by blast
      qed
    }
    thus ?case by blast
  qed
  moreover assume "set \<Phi> \<subseteq> set \<Psi>" and "distinct \<Phi>"
  ultimately show ?thesis by blast
qed

lemma count_remove_all_sum_list:
  fixes f :: "'a \<Rightarrow> real"
  shows "real (count_list xs x) * f x + (\<Sum>x'\<leftarrow>(removeAll x xs). f x')
           = (\<Sum>x\<leftarrow>xs. f x)"
  by (induct xs, simp, simp, metis combine_common_factor mult_cancel_right1)

lemma (in classical_logic) dirac_exclusive_implication_completeness:
  "(\<forall> \<delta> \<in> dirac_measures. (\<Sum>\<phi>\<leftarrow>\<Phi>. \<delta> \<phi>) \<le> \<delta> \<psi>) = (\<turnstile> \<Coprod> \<Phi> \<and>  \<turnstile> \<Squnion> \<Phi> \<rightarrow> \<psi>)"
proof -
  {
    fix \<delta>
    assume "\<delta> \<in> dirac_measures"
    from this interpret probability_logic "(\<lambda> \<phi>. \<turnstile> \<phi>)" "(\<rightarrow>)" "\<bottom>" "\<delta>"
      unfolding dirac_measures_def
      by simp
    assume "\<turnstile> \<Coprod> \<Phi>" "\<turnstile> \<Squnion> \<Phi> \<rightarrow> \<psi>"
    hence "(\<Sum>\<phi>\<leftarrow>\<Phi>. \<delta> \<phi>) \<le> \<delta> \<psi>"
      using exclusive_sum_list_identity monotonicity by fastforce
  }
  moreover
  {
    assume "\<not> \<turnstile> \<Coprod> \<Phi>"
    hence "(\<exists> \<phi> \<in> set \<Phi>. \<exists> \<psi> \<in> set \<Phi>.
              \<phi> \<noteq> \<psi> \<and> \<not> \<turnstile> \<sim> (\<phi> \<sqinter> \<psi>)) \<or> (\<exists> \<phi> \<in> duplicates \<Phi>. \<not> \<turnstile> \<sim> \<phi>)"
      using exclusive_equivalence set_deduction_base_theory by blast
    hence "\<not> (\<forall> \<delta> \<in> dirac_measures. (\<Sum>\<phi>\<leftarrow>\<Phi>. \<delta> \<phi>) \<le> \<delta> \<psi>)"
    proof (elim disjE)
      assume "\<exists> \<phi> \<in> set \<Phi>. \<exists> \<chi> \<in> set \<Phi>. \<phi> \<noteq> \<chi> \<and> \<not> \<turnstile> \<sim> (\<phi> \<sqinter> \<chi>)"
      from this obtain \<phi> and \<chi>
        where \<phi>\<chi>_properties:
          "\<phi> \<in> set \<Phi>"
          "\<chi> \<in> set \<Phi>"
          "\<phi> \<noteq> \<chi>"
          "\<not> \<turnstile> \<sim> (\<phi> \<sqinter> \<chi>)"
        by blast
      from this obtain \<Omega> where \<Omega>: "MCS \<Omega>" "\<sim> (\<phi> \<sqinter> \<chi>) \<notin> \<Omega>"
        by (meson
              insert_subset
              formula_consistent_def
              formula_maximal_consistency
              formula_maximally_consistent_extension
              formula_maximally_consistent_set_def_def
              set_deduction_base_theory
              set_deduction_reflection
              set_deduction_theorem)
      let ?\<delta> = "\<lambda> \<chi>. if \<chi>\<in>\<Omega> then (1 :: real) else 0"
      from \<Omega> have "\<phi> \<in> \<Omega>" "\<chi> \<in> \<Omega>"
        by (metis
              formula_maximally_consistent_set_def_implication
              maximally_consistent_set_def
              conjunction_def
              negation_def)+
      with \<phi>\<chi>_properties have
          "(\<Sum>\<phi>\<leftarrow>[\<phi>, \<chi>]. ?\<delta> \<phi>) = 2"
          "set [\<phi>, \<chi>] \<subseteq> set \<Phi>"
          "distinct [\<phi>, \<chi>]"
          "\<forall>\<phi>. ?\<delta> \<phi> \<ge> 0"
        by simp+
      hence "(\<Sum>\<phi>\<leftarrow>\<Phi>. ?\<delta> \<phi>) \<ge> 2" using sum_list_monotone by metis
      hence "\<not> (\<Sum>\<phi>\<leftarrow>\<Phi>. ?\<delta> \<phi>) \<le> ?\<delta> (\<psi>)" by auto
      thus ?thesis
        using \<Omega>(1) MCS_dirac_measure
        by auto
    next
      assume "\<exists> \<phi> \<in> duplicates \<Phi>. \<not> \<turnstile> \<sim> \<phi>"
      from this obtain \<phi> where \<phi>: "\<phi> \<in> duplicates \<Phi>" "\<not> \<turnstile> \<sim> \<phi>"
        using
          exclusive_equivalence [where \<Gamma>="{}"]
          set_deduction_base_theory
        by blast
      from \<phi> obtain \<Omega> where \<Omega>: "MCS \<Omega>" "\<sim> \<phi> \<notin> \<Omega>"
        by (meson
              insert_subset
              formula_consistent_def
              formula_maximal_consistency
              formula_maximally_consistent_extension
              formula_maximally_consistent_set_def_def
              set_deduction_base_theory
              set_deduction_reflection
              set_deduction_theorem)
      hence "\<phi> \<in> \<Omega>"
        using negation_def by auto
      let ?\<delta> = "\<lambda> \<chi>. if \<chi>\<in>\<Omega> then (1 :: real) else 0"
      from \<phi> have "count_list \<Phi> \<phi> \<ge> 2"
        using duplicates_alt_def [where xs="\<Phi>"]
        by blast
      hence "real (count_list \<Phi> \<phi>) * ?\<delta> \<phi> \<ge> 2" using \<open>\<phi> \<in> \<Omega>\<close> by simp
      moreover
      {
        fix \<Psi>
        have "(\<Sum>\<phi>\<leftarrow>\<Psi>. ?\<delta> \<phi>) \<ge> 0" by (induct \<Psi>, simp, simp)
      }
      moreover have "(0::real)
                          \<le> (\<Sum>a\<leftarrow>removeAll \<phi> \<Phi>. if a \<in> \<Omega> then 1 else 0)"
        using \<open>\<And>\<Psi>. 0 \<le> (\<Sum>\<phi>\<leftarrow>\<Psi>. if \<phi> \<in> \<Omega> then 1 else 0)\<close>
        by presburger
      ultimately have "real (count_list \<Phi> \<phi>) * ?\<delta> \<phi>
                            + (\<Sum> \<phi> \<leftarrow> (removeAll \<phi> \<Phi>). ?\<delta> \<phi>) \<ge> 2"
        using \<open>2 \<le> real (count_list \<Phi> \<phi>) * (if \<phi> \<in> \<Omega> then 1 else 0)\<close>
        by linarith
      hence "(\<Sum>\<phi>\<leftarrow>\<Phi>. ?\<delta> \<phi>) \<ge> 2" by (metis count_remove_all_sum_list)
      hence "\<not> (\<Sum>\<phi>\<leftarrow>\<Phi>. ?\<delta> \<phi>) \<le> ?\<delta> (\<psi>)" by auto
      thus ?thesis
        using \<Omega>(1) MCS_dirac_measure
        by auto
    qed
  }
  moreover
  {
    assume "\<not> \<turnstile> \<Squnion> \<Phi> \<rightarrow> \<psi>"
    from this obtain \<Omega> \<phi>
      where
        \<Omega>: "MCS \<Omega>"
        and \<psi>: "\<psi> \<notin> \<Omega>"
        and \<phi>: "\<phi> \<in> set \<Phi>" "\<phi> \<in> \<Omega>"
      by (meson
            insert_subset
            formula_consistent_def
            formula_maximal_consistency
            formula_maximally_consistent_extension
            formula_maximally_consistent_set_def_def
            arbitrary_disjunction_exclusion_MCS
            set_deduction_base_theory
            set_deduction_reflection
            set_deduction_theorem)
    let ?\<delta> = "\<lambda> \<chi>. if \<chi>\<in>\<Omega> then (1 :: real) else 0"
    from \<phi> have "(\<Sum>\<phi>\<leftarrow>\<Phi>. ?\<delta> \<phi>) \<ge> 1"
    proof (induct \<Phi>)
      case Nil
      then show ?case by simp
    next
      case (Cons \<phi>' \<Phi>)
      obtain f :: "real list \<Rightarrow> real" where f:
        "\<forall>rs. f rs \<in> set rs \<and> \<not> 0 \<le> f rs \<or> 0 \<le> sum_list rs"
        using sum_list_nonneg by moura
      moreover have "f (map ?\<delta> \<Phi>) \<notin> set (map ?\<delta> \<Phi>) \<or> 0 \<le> f (map ?\<delta> \<Phi>)"
        by fastforce
      ultimately show ?case
        by (simp, metis Cons.hyps Cons.prems(1) \<phi>(2) set_ConsD)
    qed
    hence "\<not> (\<Sum>\<phi>\<leftarrow>\<Phi>. ?\<delta> \<phi>) \<le> ?\<delta> (\<psi>)" using \<psi> by auto
    hence "\<not> (\<forall> \<delta> \<in> dirac_measures. (\<Sum>\<phi>\<leftarrow>\<Phi>. \<delta> \<phi>) \<le> \<delta> \<psi>)"
      using \<Omega>(1) MCS_dirac_measure
      by auto
  }
  ultimately show ?thesis by blast
qed

theorem (in classical_logic) exclusive_implication_completeness:
  "(\<forall> \<P> \<in> probabilities. (\<Sum>\<phi>\<leftarrow>\<Phi>. \<P> \<phi>) \<le> \<P> \<psi>) = (\<turnstile> \<Coprod> \<Phi> \<and>  \<turnstile> \<Squnion> \<Phi> \<rightarrow> \<psi>)"
  (is "?lhs = ?rhs")
proof
  assume ?lhs
  thus ?rhs
    by (meson
          dirac_exclusive_implication_completeness
          dirac_measures_subset
          subset_eq)
next
  assume ?rhs
  show ?lhs
  proof
    fix \<P> :: "'a \<Rightarrow> real"
    assume "\<P> \<in> probabilities"
    from this interpret probability_logic "(\<lambda> \<phi>. \<turnstile> \<phi>)" "(\<rightarrow>)" \<bottom> \<P>
      unfolding probabilities_def
      by simp
    show "(\<Sum>\<phi>\<leftarrow>\<Phi>. \<P> \<phi>) \<le> \<P> \<psi>"
      using
        \<open>?rhs\<close>
        exclusive_sum_list_identity
        monotonicity
      by fastforce
  qed
qed

lemma (in classical_logic) dirac_inequality_completeness:
  "(\<forall> \<delta> \<in> dirac_measures. \<delta> \<phi> \<le> \<delta> \<psi>) = \<turnstile> \<phi> \<rightarrow> \<psi>"
proof -
  have "\<turnstile> \<Coprod> [\<phi>]"
    by (simp add: conjunction_right_elimination negation_def)
  hence "(\<turnstile> \<Coprod> [\<phi>] \<and>  \<turnstile> \<Squnion> [\<phi>] \<rightarrow> \<psi>) = \<turnstile> \<phi> \<rightarrow> \<psi>"
    by (metis
          arbitrary_disjunction.simps(1)
          arbitrary_disjunction.simps(2)
          disjunction_def implication_equivalence
          negation_def
          weak_biconditional_weaken)
  thus ?thesis
    using dirac_exclusive_implication_completeness [where \<Phi>="[\<phi>]"]
    by auto
qed

section \<open> Implication Inequality Completeness \<close>

text \<open> The following theorem establishes the converse of
       \<open>\<turnstile> \<phi> \<rightarrow> \<psi> \<Longrightarrow> \<P> \<phi> \<le> \<P> \<psi>\<close>, which was
       proved in \S\ref{sec:prob-logic-alt-def}. \<close>

theorem (in classical_logic) implication_inequality_completeness:
  "(\<forall> \<P> \<in> probabilities. \<P> \<phi> \<le> \<P> \<psi>) = \<turnstile> \<phi> \<rightarrow> \<psi>"
proof -
  have "\<turnstile> \<Coprod> [\<phi>]"
    by (simp add: conjunction_right_elimination negation_def)
  hence "(\<turnstile> \<Coprod> [\<phi>] \<and>  \<turnstile> \<Squnion> [\<phi>] \<rightarrow> \<psi>) = \<turnstile> \<phi> \<rightarrow> \<psi>"
    by (metis
          arbitrary_disjunction.simps(1)
          arbitrary_disjunction.simps(2)
          disjunction_def implication_equivalence
          negation_def
          weak_biconditional_weaken)
  thus ?thesis
    using exclusive_implication_completeness [where \<Phi>="[\<phi>]"]
    by simp
qed

section \<open> Characterizing Logical Exclusiveness In Probability Logic \<close>

text \<open> Finally, we can say that \<open>\<P> (\<Squnion> \<Phi>) = (\<Sum>\<phi>\<leftarrow>\<Phi>. \<P> \<phi>)\<close> if and only
       if the propositions in \<^term>\<open>\<Phi>\<close> are mutually exclusive (i.e. \<open>\<turnstile> \<Coprod> \<Phi>\<close>).
       This result also obtains for sets. \<close>

lemma (in classical_logic) dirac_exclusive_list_summation_completeness:
  "(\<forall> \<delta> \<in> dirac_measures. \<delta> (\<Squnion> \<Phi>) = (\<Sum>\<phi>\<leftarrow>\<Phi>. \<delta> \<phi>)) = \<turnstile> \<Coprod> \<Phi>"
  by (metis
        antisym_conv
        dirac_exclusive_implication_completeness
        dirac_list_summation_completeness
        trivial_implication)

theorem (in classical_logic) exclusive_list_summation_completeness:
  "(\<forall> \<P> \<in> probabilities. \<P> (\<Squnion> \<Phi>) = (\<Sum>\<phi>\<leftarrow>\<Phi>. \<P> \<phi>)) = \<turnstile> \<Coprod> \<Phi>"
  by (metis
        antisym_conv
        exclusive_implication_completeness
        list_summation_completeness
        trivial_implication)

lemma (in classical_logic) dirac_exclusive_set_summation_completeness:
  "(\<forall> \<delta> \<in> dirac_measures. \<delta> (\<Squnion> \<Phi>) = (\<Sum>\<phi> \<in> set \<Phi>. \<delta> \<phi>))
      = \<turnstile> \<Coprod> (remdups \<Phi>)"
  by (metis
        (mono_tags)
        eq_iff
        dirac_exclusive_implication_completeness
        dirac_set_summation_completeness
        trivial_implication
        set_remdups
        sum.set_conv_list    eq_iff
        dirac_exclusive_implication_completeness
        dirac_set_summation_completeness
        trivial_implication
        set_remdups
        sum.set_conv_list
        antisym_conv)

theorem (in classical_logic) exclusive_set_summation_completeness:
  "(\<forall> \<P> \<in> probabilities.
        \<P> (\<Squnion> \<Phi>) = (\<Sum>\<phi> \<in> set \<Phi>. \<P> \<phi>)) = \<turnstile> \<Coprod> (remdups \<Phi>)"
  by (metis
        (mono_tags, opaque_lifting)
        antisym_conv
        exclusive_list_summation_completeness
        exclusive_implication_completeness
        implication_inequality_completeness
        set_summation_completeness
        order.refl
        sum.set_conv_list)

lemma (in probability_logic) exclusive_list_set_inequality:
  assumes "\<turnstile> \<Coprod> \<Phi>"
  shows "(\<Sum>\<phi>\<leftarrow>\<Phi>. \<P> \<phi>) = (\<Sum>\<phi>\<in>set \<Phi>. \<P> \<phi>)"
proof -
  have "distinct (remdups \<Phi>)" using distinct_remdups by auto
  hence "duplicates (remdups \<Phi>) = {}"
    by (induct "\<Phi>", simp+)
  moreover have "set (remdups \<Phi>) = set \<Phi>"
    by (induct "\<Phi>", simp, simp add: insert_absorb)
  moreover have "(\<forall>\<phi> \<in> duplicates \<Phi>. \<turnstile> \<sim> \<phi>)
               \<and> (\<forall> \<phi> \<in> set \<Phi>. \<forall> \<psi> \<in> set \<Phi>. (\<phi> \<noteq> \<psi>) \<longrightarrow> \<turnstile> \<sim> (\<phi> \<sqinter> \<psi>))"
    using
      assms
      exclusive_elimination1
      exclusive_elimination2
      set_deduction_base_theory
    by blast
  ultimately have
    "(\<forall>\<phi>\<in>duplicates (remdups \<Phi>). \<turnstile> \<sim> \<phi>)
   \<and> (\<forall> \<phi> \<in> set (remdups \<Phi>). \<forall> \<psi> \<in> set (remdups \<Phi>).
          (\<phi> \<noteq> \<psi>) \<longrightarrow> \<turnstile> \<sim> (\<phi> \<sqinter> \<psi>))"
    by auto
  hence "\<turnstile> \<Coprod> (remdups \<Phi>)"
    by (meson exclusive_equivalence set_deduction_base_theory)
  hence "(\<Sum>\<phi>\<in>set \<Phi>. \<P> \<phi>) = \<P> (\<Squnion> \<Phi>)"
    by (metis
          arbitrary_disjunction_remdups
          biconditional_equivalence
          exclusive_sum_list_identity
          sum.set_conv_list)
  moreover have "(\<Sum>\<phi>\<leftarrow>\<Phi>. \<P> \<phi>) = \<P> (\<Squnion> \<Phi>)"
    by (simp add: assms exclusive_sum_list_identity)
  ultimately show ?thesis by metis
qed

notation FuncSet.funcset (infixr "\<rightarrow>" 60)

end
