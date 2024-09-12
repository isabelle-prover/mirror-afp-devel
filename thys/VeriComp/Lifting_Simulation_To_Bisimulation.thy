theory Lifting_Simulation_To_Bisimulation
  imports Well_founded
begin

definition stuck_state :: "('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> bool" where
  "stuck_state \<R> s \<longleftrightarrow> (\<nexists>s'. \<R> s s')"

definition simulation ::
  "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> ('b \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> ('c \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> ('c \<Rightarrow> 'c \<Rightarrow> bool) \<Rightarrow> bool"
where
  "simulation \<R>\<^sub>1 \<R>\<^sub>2 match order \<longleftrightarrow>
    (\<forall>i s1 s2 s1'. match i s1 s2 \<longrightarrow> \<R>\<^sub>1 s1 s1' \<longrightarrow>
      (\<exists>s2' i'. \<R>\<^sub>2\<^sup>+\<^sup>+ s2 s2' \<and> match i' s1' s2') \<or> (\<exists>i'. match i' s1' s2 \<and> order i' i))"

lemma finite_progress:
  fixes
    step1 :: "'s1 \<Rightarrow> 's1 \<Rightarrow> bool" and
    step2 :: "'s2 \<Rightarrow> 's2 \<Rightarrow> bool" and
    match :: "'i \<Rightarrow> 's1 \<Rightarrow> 's2 \<Rightarrow> bool" and
    order :: "'i \<Rightarrow> 'i \<Rightarrow> bool"
  assumes
    matching_states_agree_on_stuck:
      "\<forall>i s1 s2. match i s1 s2 \<longrightarrow> stuck_state step1 s1 \<longleftrightarrow> stuck_state step2 s2" and
    well_founded_order: "wfp order" and
    sim: "simulation step1 step2 match order"
  shows "match i s1 s2 \<Longrightarrow> step1 s1 s1' \<Longrightarrow>
    \<exists>m s1'' n s2'' i'. (step1 ^^ m) s1' s1'' \<and> (step2 ^^ Suc n) s2 s2'' \<and> match i' s1'' s2''"
  using well_founded_order
proof (induction i arbitrary: s1 s1' rule: wfp_induct_rule)
  case (less i)
  show ?case
    using sim[unfolded simulation_def, rule_format, OF \<open>match i s1 s2\<close> \<open>step1 s1 s1'\<close>]
  proof (elim disjE exE conjE)
    show "\<And>s2' i'. step2\<^sup>+\<^sup>+ s2 s2' \<Longrightarrow> match i' s1' s2' \<Longrightarrow> ?thesis"
      by (metis Suc_pred relpowp_0_I tranclp_power)
  next
    fix i'
    assume "match i' s1' s2" and "order i' i"

    have "\<not> stuck_state step1 s1"
      using \<open>step1 s1 s1'\<close> stuck_state_def by metis
    hence "\<not> stuck_state step2 s2"
      using \<open>match i s1 s2\<close> matching_states_agree_on_stuck by metis
    hence "\<not> stuck_state step1 s1'"
      using \<open>match i' s1' s2\<close> matching_states_agree_on_stuck by metis

    then obtain s1'' where "step1 s1' s1''"
      by (metis stuck_state_def)

    obtain m s1''' n s2' i'' where
      "(step1 ^^ m) s1'' s1'''" and
      "(step2 ^^ Suc n) s2 s2'" and
      "match i'' s1''' s2'"
      using less.IH[OF \<open>order i' i\<close> \<open>match i' s1' s2\<close> \<open>step1 s1' s1''\<close>] by metis

    show ?thesis
    proof (intro exI conjI)
      show "(step1 ^^ Suc m) s1' s1'''"
        using \<open>(step1 ^^ m) s1'' s1'''\<close> \<open>step1 s1' s1''\<close> by (metis relpowp_Suc_I2)
    next
      show "(step2 ^^ Suc n) s2 s2'"
        using \<open>(step2 ^^ Suc n) s2 s2'\<close> .
    next
      show "match i'' s1''' s2'"
        using \<open>match i'' s1''' s2'\<close> .
    qed
  qed
qed

context begin

private inductive match_bisim
  for \<R>\<^sub>1 :: "'a \<Rightarrow> 'a \<Rightarrow> bool" and \<R>\<^sub>2 :: "'b \<Rightarrow> 'b \<Rightarrow> bool" and
    match :: "'c \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> bool" and order :: "'c \<Rightarrow> 'c \<Rightarrow> bool"
where
  bisim_stuck: "stuck_state \<R>\<^sub>1 s1 \<Longrightarrow> stuck_state \<R>\<^sub>2 s2 \<Longrightarrow> match i s1 s2 \<Longrightarrow>
    match_bisim \<R>\<^sub>1 \<R>\<^sub>2 match order (0, 0) s1 s2" |

  bisim_steps: "match i s1\<^sub>0 s2\<^sub>0 \<Longrightarrow> \<R>\<^sub>1\<^sup>*\<^sup>* s1\<^sub>0 s1 \<Longrightarrow> (\<R>\<^sub>1 ^^ Suc m) s1 s1' \<Longrightarrow>
    \<R>\<^sub>2\<^sup>*\<^sup>* s2\<^sub>0 s2 \<Longrightarrow> (\<R>\<^sub>2 ^^ Suc n) s2 s2' \<Longrightarrow> match i' s1' s2' \<Longrightarrow>
    match_bisim \<R>\<^sub>1 \<R>\<^sub>2 match order (m, n) s1 s2"

theorem lift_strong_simulation_to_bisimulation:
  fixes
    step1 :: "'s1 \<Rightarrow> 's1 \<Rightarrow> bool" and
    step2 :: "'s2 \<Rightarrow> 's2 \<Rightarrow> bool" and
    match :: "'i \<Rightarrow> 's1 \<Rightarrow> 's2 \<Rightarrow> bool" and
    order :: "'i \<Rightarrow> 'i \<Rightarrow> bool"
  assumes
    matching_states_agree_on_stuck:
      "\<forall>i s1 s2. match i s1 s2 \<longrightarrow> stuck_state step1 s1 \<longleftrightarrow> stuck_state step2 s2" and
    well_founded_order: "wfp order" and
    sim: "simulation step1 step2 match order"
  obtains
    MATCH :: "nat \<times> nat \<Rightarrow> 's1 \<Rightarrow> 's2 \<Rightarrow> bool" and
    ORDER :: "nat \<times> nat \<Rightarrow> nat \<times> nat \<Rightarrow> bool"
  where
    "\<And>i s1 s2. match i s1 s2 \<Longrightarrow> (\<exists>j. MATCH j s1 s2)"
    "\<And>j s1 s2. MATCH j s1 s2 \<Longrightarrow>
      (\<exists>i. stuck_state step1 s1 \<and> stuck_state step2 s2 \<and> match i s1 s2) \<or>
      (\<exists>i s1' s2'. step1\<^sup>+\<^sup>+ s1 s1' \<and> step2\<^sup>+\<^sup>+ s2 s2' \<and> match i s1' s2')" and
    "wfp ORDER" and
    "right_unique step1 \<Longrightarrow> simulation step1 step2 (\<lambda>i s1 s2. MATCH i s1 s2) ORDER" and
    "right_unique step2 \<Longrightarrow> simulation step2 step1 (\<lambda>i s2 s1. MATCH i s1 s2) ORDER"
proof -
  define MATCH :: "nat \<times> nat \<Rightarrow> 's1 \<Rightarrow> 's2 \<Rightarrow> bool" where
    "MATCH = match_bisim step1 step2 match order"

  define ORDER :: "nat \<times> nat \<Rightarrow> nat \<times> nat \<Rightarrow> bool" where
    "ORDER = lex_prodp ((<) :: nat \<Rightarrow> nat \<Rightarrow> bool) ((<) :: nat \<Rightarrow> nat \<Rightarrow> bool)"

  have MATCH_if_match: "\<And>i s1 s2. match i s1 s2 \<Longrightarrow> \<exists>j. MATCH j s1 s2"
  proof -
    fix i s1 s2
    assume "match i s1 s2"

    have "stuck_state step1 s1 \<longleftrightarrow> stuck_state step2 s2"
      using \<open>match i s1 s2\<close> matching_states_agree_on_stuck by metis
    hence "(stuck_state step1 s1 \<and> stuck_state step2 s2) \<or> (\<exists>s1' s2'. step1 s1 s1' \<and> step2 s2 s2')"
      by (metis stuck_state_def)
    thus "\<exists>j. MATCH j s1 s2"
    proof (elim disjE conjE exE)
      show "stuck_state step1 s1 \<Longrightarrow> stuck_state step2 s2 \<Longrightarrow> \<exists>j. MATCH j s1 s2"
        by (metis MATCH_def \<open>match i s1 s2\<close> bisim_stuck)
    next
      fix s1' s2'
      assume "step1 s1 s1'" and "step2 s2 s2'"

      obtain m n s1'' s2'' i' where
        "(step1 ^^ m) s1' s1''" and
        "(step2 ^^ Suc n) s2 s2''" and
        "match i' s1'' s2''"
        using finite_progress[OF assms \<open>match i s1 s2\<close> \<open>step1 s1 s1'\<close>] by metis

      show "\<exists>j. MATCH j s1 s2"
      proof (intro exI)
        show "MATCH (m, n) s1 s2"
          unfolding MATCH_def
        proof (rule bisim_steps)
          show "match i s1 s2"
            using \<open>match i s1 s2\<close> .
        next
          show "step1\<^sup>*\<^sup>* s1 s1"
            by simp
        next
          show "(step1 ^^ Suc m) s1 s1''"
            using \<open>step1 s1 s1'\<close> \<open>(step1 ^^ m) s1' s1''\<close> by (metis relpowp_Suc_I2)
        next
          show "step2\<^sup>*\<^sup>* s2 s2"
            by simp
        next
          show "(step2 ^^ Suc n) s2 s2''"
            using \<open>(step2 ^^ Suc n) s2 s2''\<close> .
        next
          show "match i' s1'' s2''"
            using \<open>match i' s1'' s2''\<close> .
        qed
      qed
    qed
  qed

  show thesis
  proof (rule that)
    show "\<And>i s1 s2. match i s1 s2 \<Longrightarrow> \<exists>j. MATCH j s1 s2"
      using MATCH_if_match .
  next
    fix j :: "nat \<times> nat" and s1 :: 's1 and s2 :: 's2
    assume "MATCH j s1 s2"
    thus "(\<exists>i. stuck_state step1 s1 \<and> stuck_state step2 s2 \<and> match i s1 s2) \<or>
      (\<exists>i s1' s2'. step1\<^sup>+\<^sup>+ s1 s1' \<and> step2\<^sup>+\<^sup>+ s2 s2' \<and> match i s1' s2')"
      unfolding MATCH_def
    proof (cases step1 step2 match order j s1 s2 rule: match_bisim.cases)
      case (bisim_stuck i)
      thus ?thesis
        by blast
    next
      case (bisim_steps i s1\<^sub>0 s2\<^sub>0 m s1' n s2' i')
      hence "\<exists>i s1' s2'. step1\<^sup>+\<^sup>+ s1 s1' \<and> step2\<^sup>+\<^sup>+ s2 s2' \<and> match i s1' s2'"
        by (metis tranclp_power zero_less_Suc)
      thus ?thesis ..
    qed
  next
    show "wfp ORDER"
      unfolding ORDER_def
      using lex_prodp_wfP wfp_on_less well_founded_order by metis
  next
    assume "right_unique step1"
    show "simulation step1 step2 MATCH ORDER"
      unfolding simulation_def
    proof (intro allI impI)
      fix j :: "nat \<times> nat" and s1 s1' :: 's1 and s2 :: 's2
      assume "MATCH j s1 s2" and "step1 s1 s1'"
      hence "match_bisim step1 step2 match order j s1 s2"
        unfolding MATCH_def by metis
      thus "(\<exists>s2' j'. step2\<^sup>+\<^sup>+ s2 s2' \<and> MATCH j' s1' s2') \<or> (\<exists>j'. MATCH j' s1' s2 \<and> ORDER j' j)"
      proof (cases step1 step2 match order j s1 s2 rule: match_bisim.cases)
        case (bisim_stuck i)
        hence False
          using \<open>step1 s1 s1'\<close> stuck_state_def by metis
        thus ?thesis ..
      next
        case (bisim_steps i s1\<^sub>0 s2\<^sub>0 m s1'' n s2' i')

        have "(step1 ^^ m) s1' s1''"
          using \<open>step1 s1 s1'\<close> \<open>(step1 ^^ Suc m) s1 s1''\<close> \<open>right_unique step1\<close>
          by (metis relpowp_Suc_D2 right_uniqueD)

        show ?thesis
        proof (cases m)
          case 0
          hence "s1'' = s1'"
            using \<open>(step1 ^^ m) s1' s1''\<close> by simp

          have "step2\<^sup>+\<^sup>+ s2 s2'"
            using \<open>(step2 ^^ Suc n) s2 s2'\<close> by (metis tranclp_power zero_less_Suc)

          moreover have "\<exists>j'. MATCH j' s1' s2'"
            using \<open>match i' s1'' s2'\<close> \<open>s1'' = s1'\<close> MATCH_if_match by metis

          ultimately show ?thesis
            by metis
        next
          case (Suc m')
          define j' where
            "j' = (m', n)"

          have "MATCH j' s1' s2"
            unfolding MATCH_def j'_def
          proof (rule match_bisim.bisim_steps)
            show "match i s1\<^sub>0 s2\<^sub>0"
              using \<open>match i s1\<^sub>0 s2\<^sub>0\<close> .
          next
            show "step1\<^sup>*\<^sup>* s1\<^sub>0 s1'"
              using \<open>step1\<^sup>*\<^sup>* s1\<^sub>0 s1\<close> \<open>step1 s1 s1'\<close> by auto
          next
            show "(step1 ^^ Suc m') s1' s1''"
              using \<open>(step1 ^^ m) s1' s1''\<close> \<open>m = Suc m'\<close> by argo
          next
            show "step2\<^sup>*\<^sup>* s2\<^sub>0 s2"
              using \<open>step2\<^sup>*\<^sup>* s2\<^sub>0 s2\<close> .
          next
            show "(step2 ^^ Suc n) s2 s2'"
              using \<open>(step2 ^^ Suc n) s2 s2'\<close> .
          next
            show "match i' s1'' s2'"
              using \<open>match i' s1'' s2'\<close> .
          qed

          moreover have "ORDER j' j"
            unfolding ORDER_def \<open>j' = (m', n)\<close> \<open>j = (m, n)\<close> \<open>m = Suc m'\<close>
            by (simp add: lex_prodp_def)

          ultimately show ?thesis
            by metis
        qed
      qed
    qed
  next
    assume "right_unique step2"
    show "simulation step2 step1 (\<lambda>i s2 s1. MATCH i s1 s2) ORDER"
      unfolding simulation_def
    proof (intro allI impI)
      fix j :: "nat \<times> nat" and s1 :: 's1 and s2 s2' :: 's2
      assume "MATCH j s1 s2" and "step2 s2 s2'"
      hence "match_bisim step1 step2 match order j s1 s2"
        unfolding MATCH_def by metis
      thus "(\<exists>s1' j'. step1\<^sup>+\<^sup>+ s1 s1' \<and> MATCH j' s1' s2') \<or> (\<exists>j'. MATCH j' s1 s2' \<and> ORDER j' j)"
      proof (cases step1 step2 match order j s1 s2 rule: match_bisim.cases)
        case (bisim_stuck i)
        hence "stuck_state step2 s2"
          by argo
        hence False
          using \<open>step2 s2 s2'\<close> stuck_state_def by metis
        thus ?thesis ..
      next
        case (bisim_steps i s1\<^sub>0 s2\<^sub>0 m s1' n s2'' i')
        show ?thesis
        proof (cases n)
          case 0
          hence "s2'' = s2'"
            using \<open>step2 s2 s2'\<close> \<open>(step2 ^^ Suc n) s2 s2''\<close> \<open>right_unique step2\<close>
            by (metis One_nat_def relpowp_1 right_uniqueD)

          have "step1\<^sup>+\<^sup>+ s1 s1'"
            using \<open>(step1 ^^ Suc m) s1 s1'\<close>
            by (metis less_Suc_eq_0_disj tranclp_power)

          moreover have "\<exists>j'. MATCH j' s1' s2'"
            using \<open>match i' s1' s2''\<close> \<open>s2'' = s2'\<close> MATCH_if_match by metis

          ultimately show ?thesis
            by metis
        next
          case (Suc n')

          define j' where
            "j' = (m, n')"

          have "MATCH j' s1 s2'"
            unfolding MATCH_def j'_def
          proof (rule match_bisim.bisim_steps)
            show "match i s1\<^sub>0 s2\<^sub>0"
              using \<open>match i s1\<^sub>0 s2\<^sub>0\<close> .
          next
            show "step1\<^sup>*\<^sup>* s1\<^sub>0 s1"
              using \<open>step1\<^sup>*\<^sup>* s1\<^sub>0 s1\<close> .
          next
            show "(step1 ^^ Suc m) s1 s1'"
              using \<open>(step1 ^^ Suc m) s1 s1'\<close> .
          next
            show "step2\<^sup>*\<^sup>* s2\<^sub>0 s2'"
              using \<open>step2\<^sup>*\<^sup>* s2\<^sub>0 s2\<close> \<open>step2 s2 s2'\<close> by auto
          next
            show "(step2 ^^ Suc n') s2' s2''"
              using \<open>step2 s2 s2'\<close> \<open>(step2 ^^ Suc n) s2 s2''\<close> \<open>right_unique step2\<close>
              by (metis Suc relpowp_Suc_D2 right_uniqueD)
          next
            show "match i' s1' s2''"
              using \<open>match i' s1' s2''\<close> .
          qed

          moreover have "ORDER j' j"
            unfolding ORDER_def \<open>j' = (m, n')\<close> \<open>j = (m, n)\<close> \<open>n = Suc n'\<close>
            by (simp add: lex_prodp_def)

          ultimately show ?thesis
            by metis
        qed
      qed
    qed
  qed
qed

end

definition safe_state where
  "safe_state \<R> \<F> s \<longleftrightarrow> (\<forall>s'. \<R>\<^sup>*\<^sup>* s s' \<longrightarrow> stuck_state \<R> s' \<longrightarrow> \<F> s')"

lemma step_preserves_safe_state:
  "\<R> s s' \<Longrightarrow> safe_state \<R> \<F> s \<Longrightarrow> safe_state \<R> \<F> s'"
  by (simp add: safe_state_def converse_rtranclp_into_rtranclp)

lemma rtranclp_step_preserves_safe_state:
  "\<R>\<^sup>*\<^sup>* s s' \<Longrightarrow> safe_state \<R> \<F> s \<Longrightarrow> safe_state \<R> \<F> s'"
  by (simp add: rtranclp_induct step_preserves_safe_state)

lemma tranclp_step_preserves_safe_state:
  "\<R>\<^sup>+\<^sup>+ s s' \<Longrightarrow> safe_state \<R> \<F> s \<Longrightarrow> safe_state \<R> \<F> s'"
  by (simp add: step_preserves_safe_state tranclp_induct)

lemma safe_state_before_step_if_safe_state_after:
  assumes "right_unique \<R>"
  shows "\<R> s s' \<Longrightarrow> safe_state \<R> \<F> s' \<Longrightarrow> safe_state \<R> \<F> s"
  by (smt (verit, ccfv_threshold) assms converse_rtranclpE right_uniqueD safe_state_def
      stuck_state_def)

lemma safe_state_before_rtranclp_step_if_safe_state_after:
  assumes "right_unique \<R>"
  shows "\<R>\<^sup>*\<^sup>* s s' \<Longrightarrow> safe_state \<R> \<F> s' \<Longrightarrow> safe_state \<R> \<F> s"
  by (smt (verit, best) assms converse_rtranclp_induct safe_state_before_step_if_safe_state_after)

lemma safe_state_before_tranclp_step_if_safe_state_after:
  assumes "right_unique \<R>"
  shows "\<R>\<^sup>+\<^sup>+ s s' \<Longrightarrow> safe_state \<R> \<F> s' \<Longrightarrow> safe_state \<R> \<F> s"
  by (meson assms safe_state_before_rtranclp_step_if_safe_state_after tranclp_into_rtranclp)

lemma safe_state_if_all_states_safe:
  fixes \<R> \<F> s
  assumes "\<And>s. \<F> s \<or> (\<exists>s'. \<R> s s')"
  shows "safe_state \<R> \<F> s"
  using assms by (metis safe_state_def stuck_state_def)

lemma
  fixes \<R> \<F> s
  shows "safe_state \<R> \<F> s \<Longrightarrow> \<F> s \<or> (\<exists>s'. \<R> s s')"
  by (metis rtranclp.rtrancl_refl safe_state_def stuck_state_def)

lemma matching_states_agree_on_stuck_if_they_agree_on_final:
  assumes
    final1_stuck: "\<forall>s1. final1 s1 \<longrightarrow> (\<nexists>s1'. step1 s1 s1')" and
    final2_stuck: "\<forall>s2. final2 s2 \<longrightarrow> (\<nexists>s2'. step2 s2 s2')" and
    matching_states_agree_on_final: "\<forall>i s1 s2. match i s1 s2 \<longrightarrow> final1 s1 \<longleftrightarrow> final2 s2" and
    matching_states_are_safe:
      "\<forall>i s1 s2. match i s1 s2 \<longrightarrow> safe_state step1 final1 s1 \<and> safe_state step2 final2 s2"
  shows "\<forall>i s1 s2. match i s1 s2 \<longrightarrow> stuck_state step1 s1 \<longleftrightarrow> stuck_state step2 s2"
    using assms by (metis rtranclp.rtrancl_refl safe_state_def stuck_state_def)

locale wellbehaved_transition_system =
  fixes \<R> :: "'s \<Rightarrow> 's \<Rightarrow> bool" and \<F> :: "'s \<Rightarrow> bool" and \<S> :: "'s \<Rightarrow> bool"
  assumes
    determ: "right_unique \<R>" and
    stuck_if_final: "\<And>x. \<F> x \<Longrightarrow> stuck_state \<R> x" and
    safe_if_invar: "\<And>x. \<S> x \<Longrightarrow> safe_state \<R> \<F> x"

lemma (in wellbehaved_transition_system) final_iff_stuck_if_invar:
  fixes x
  assumes "\<S> x"
  shows "\<F> x \<longleftrightarrow> stuck_state \<R> x"
proof (intro iffI)
  assume "\<F> x"
  thus "stuck_state \<R> x"
    by (fact stuck_if_final)
next
  assume "stuck_state \<R> x"
  thus "\<F> x"
    by (metis assms rtranclp.rtrancl_refl safe_if_invar safe_state_def stuck_state_def)
qed

lemma wellbehaved_transition_systems_agree_on_final_iff_agree_on_stuck:
  fixes
    \<R>\<^sub>a :: "'a \<Rightarrow> 'a \<Rightarrow> bool" and \<F>\<^sub>a :: "'a \<Rightarrow> bool" and
    \<R>\<^sub>b :: "'b \<Rightarrow> 'b \<Rightarrow> bool" and \<F>\<^sub>b :: "'b \<Rightarrow> bool" and
    \<M> :: "'i \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> bool"
  assumes
    "wellbehaved_transition_system \<R>\<^sub>a \<F>\<^sub>a (\<lambda>a. \<exists>i b. \<M> i a b)" and
    "wellbehaved_transition_system \<R>\<^sub>b \<F>\<^sub>b (\<lambda>b. \<exists>i a. \<M> i a b)" and
    "\<M> i a b"
  shows "(\<F>\<^sub>a a \<longleftrightarrow> \<F>\<^sub>b b) \<longleftrightarrow> (stuck_state \<R>\<^sub>a a \<longleftrightarrow> stuck_state \<R>\<^sub>b b)"
  using assms
  by (metis (mono_tags, lifting) wellbehaved_transition_system.final_iff_stuck_if_invar)

corollary lift_strong_simulation_to_bisimulation':
  fixes
    step1 :: "'s1 \<Rightarrow> 's1 \<Rightarrow> bool" and
    step2 :: "'s2 \<Rightarrow> 's2 \<Rightarrow> bool" and
    match :: "'i \<Rightarrow> 's1 \<Rightarrow> 's2 \<Rightarrow> bool" and
    order :: "'i \<Rightarrow> 'i \<Rightarrow> bool"
  assumes
    "right_unique step1" and
    "right_unique step2" and
    final1_stuck: "\<forall>s1. final1 s1 \<longrightarrow> (\<nexists>s1'. step1 s1 s1')" and
    final2_stuck: "\<forall>s2. final2 s2 \<longrightarrow> (\<nexists>s2'. step2 s2 s2')" and
    matching_states_agree_on_final:
      "\<forall>i s1 s2. match i s1 s2 \<longrightarrow> final1 s1 \<longleftrightarrow> final2 s2" and
    matching_states_are_safe:
      "\<forall>i s1 s2. match i s1 s2 \<longrightarrow> safe_state step1 final1 s1 \<and> safe_state step2 final2 s2" and
    order_well_founded: "wfp order" and
    sim: "simulation step1 step2 match order"
  obtains
    MATCH :: "nat \<times> nat \<Rightarrow> 's1 \<Rightarrow> 's2 \<Rightarrow> bool" and
    ORDER :: "nat \<times> nat \<Rightarrow> nat \<times> nat \<Rightarrow> bool"
  where
    "\<And>i s1 s2. match i s1 s2 \<Longrightarrow> (\<exists>j. MATCH j s1 s2)"
    "\<And>j s1 s2. MATCH j s1 s2 \<Longrightarrow> final1 s1 \<longleftrightarrow> final2 s2" and
    "\<And>j s1 s2. MATCH j s1 s2 \<Longrightarrow> stuck_state step1 s1 \<longleftrightarrow> stuck_state step2 s2" and
    "\<And>j s1 s2. MATCH j s1 s2 \<Longrightarrow> safe_state step1 final1 s1 \<and> safe_state step2 final2 s2" and
    "wfp ORDER" and
    "simulation step1 step2 (\<lambda>i s1 s2. MATCH i s1 s2) ORDER" and
    "simulation step2 step1 (\<lambda>i s2 s1. MATCH i s1 s2) ORDER"
proof -
  have matching_states_agree_on_stuck:
    "\<forall>i s1 s2. match i s1 s2 \<longrightarrow> stuck_state step1 s1 \<longleftrightarrow> stuck_state step2 s2"
    using matching_states_agree_on_stuck_if_they_agree_on_final[OF final1_stuck final2_stuck
        matching_states_agree_on_final matching_states_are_safe] .

  obtain
    MATCH :: "nat \<times> nat \<Rightarrow> 's1 \<Rightarrow> 's2 \<Rightarrow> bool" and
    ORDER :: "nat \<times> nat \<Rightarrow> nat \<times> nat \<Rightarrow> bool"
  where
    MATCH_if_match: "\<And>i s1 s2. match i s1 s2 \<Longrightarrow> \<exists>j. MATCH j s1 s2" and
    MATCH_spec: "\<And>j s1 s2. MATCH j s1 s2 \<Longrightarrow>
      (\<exists>i. stuck_state step1 s1 \<and> stuck_state step2 s2 \<and> match i s1 s2) \<or>
      (\<exists>i s1' s2'. step1\<^sup>+\<^sup>+ s1 s1' \<and> step2\<^sup>+\<^sup>+ s2 s2' \<and> match i s1' s2')" and
    "wfp ORDER" and
    "simulation step1 step2 MATCH ORDER" and
    "simulation step2 step1 (\<lambda>i s2 s1. MATCH i s1 s2) ORDER"
    using \<open>right_unique step1\<close> \<open>right_unique step2\<close>
    using lift_strong_simulation_to_bisimulation[
        OF matching_states_agree_on_stuck
        order_well_founded sim]
    by (smt (verit))

  have wellbehaved1: "wellbehaved_transition_system step1 final1 (\<lambda>a. \<exists>i b. MATCH i a b)"
  proof unfold_locales
    show "right_unique step1"
      using \<open>right_unique step1\<close> .
  next
    show "\<And>x. final1 x \<Longrightarrow> stuck_state step1 x"
      unfolding stuck_state_def
      using final1_stuck by metis
  next
    show "\<And>x. \<exists>i b. MATCH i x b \<Longrightarrow> safe_state step1 final1 x"
      by (meson MATCH_spec assms(1) matching_states_are_safe safe_state_before_tranclp_step_if_safe_state_after)
  qed

  have wellbehaved2: "wellbehaved_transition_system step2 final2 (\<lambda>b. \<exists>i a. MATCH i a b)"
  proof unfold_locales
    show "right_unique step2"
      using \<open>right_unique step2\<close> .
  next
    show "\<And>x. final2 x \<Longrightarrow> stuck_state step2 x"
      unfolding stuck_state_def
      using final2_stuck by metis
  next
    show "\<And>x. \<exists>i a. MATCH i a x \<Longrightarrow> safe_state step2 final2 x"
      by (meson MATCH_spec assms(2) matching_states_are_safe
          safe_state_before_tranclp_step_if_safe_state_after)
  qed

  show thesis
  proof (rule that)
    show "\<And>i s1 s2. match i s1 s2 \<Longrightarrow> \<exists>j. MATCH j s1 s2"
      using MATCH_if_match .
  next
    show "\<And>j s1 s2. MATCH j s1 s2 \<Longrightarrow> stuck_state step1 s1 \<longleftrightarrow> stuck_state step2 s2"
      using MATCH_spec
      by (metis stuck_state_def tranclpD)

    then show "\<And>j s1 s2. MATCH j s1 s2 \<Longrightarrow> final1 s1 \<longleftrightarrow> final2 s2"
      using wellbehaved_transition_systems_agree_on_final_iff_agree_on_stuck[
          OF wellbehaved1 wellbehaved2]
      by blast
  next
    fix j s1 s2
    assume "MATCH j s1 s2"
    then show "safe_state step1 final1 s1 \<and> safe_state step2 final2 s2"
      using wellbehaved_transition_system.safe_if_invar[OF wellbehaved1, of s1]
      using wellbehaved_transition_system.safe_if_invar[OF wellbehaved2, of s2]
      by blast
  next
    show "wfp ORDER"
      using \<open>wfp ORDER\<close> .
  next
    show "simulation step1 step2 (\<lambda>i s1 s2. MATCH i s1 s2) ORDER"
      using \<open>simulation step1 step2 (\<lambda>i s1 s2. MATCH i s1 s2) ORDER\<close> .
  next
    show "simulation step2 step1 (\<lambda>i s2 s1. MATCH i s1 s2) ORDER"
      using \<open>simulation step2 step1 (\<lambda>i s2 s1. MATCH i s1 s2) ORDER\<close> .
  qed
qed

end