theory Lifting_Simulation_To_Bisimulation
  imports
    Main
    "VeriComp.Well_founded"
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
      case (bisim_steps m s1' i s2\<^sub>0 n\<^sub>1 n\<^sub>2 s2' i')
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
  "safe_state \<R> \<F> s \<longleftrightarrow> (\<forall>s'. \<R>\<^sup>*\<^sup>* s s' \<longrightarrow> \<F> s' \<or> (\<exists>s''. \<R> s' s''))"

lemma step_preserves_safe_state:
  "\<R> s s' \<Longrightarrow> safe_state \<R> \<F> s \<Longrightarrow> safe_state \<R> \<F> s'"
  by (simp add: converse_rtranclp_into_rtranclp safe_state_def)

lemma rtranclp_step_preserves_safe_state:
  "\<R>\<^sup>*\<^sup>* s s' \<Longrightarrow> safe_state \<R> \<F> s \<Longrightarrow> safe_state \<R> \<F> s'"
  by (simp add: rtranclp_induct step_preserves_safe_state)

lemma tranclp_step_preserves_safe_state:
  "\<R>\<^sup>+\<^sup>+ s s' \<Longrightarrow> safe_state \<R> \<F> s \<Longrightarrow> safe_state \<R> \<F> s'"
  by (simp add: step_preserves_safe_state tranclp_induct)

lemma safe_state_before_step_if_safe_state_after:
  assumes "right_unique \<R>"
  shows "\<R> s s' \<Longrightarrow> safe_state \<R> \<F> s' \<Longrightarrow> safe_state \<R> \<F> s"
  by (metis (full_types) assms converse_rtranclpE right_uniqueD safe_state_def)

lemma safe_state_before_rtranclp_step_if_safe_state_after:
  assumes "right_unique \<R>"
  shows "\<R>\<^sup>*\<^sup>* s s' \<Longrightarrow> safe_state \<R> \<F> s' \<Longrightarrow> safe_state \<R> \<F> s"
  by (smt (verit, best) assms converse_rtranclp_induct safe_state_before_step_if_safe_state_after)

lemma safe_state_before_tranclp_step_if_safe_state_after:
  assumes "right_unique \<R>"
  shows "\<R>\<^sup>+\<^sup>+ s s' \<Longrightarrow> safe_state \<R> \<F> s' \<Longrightarrow> safe_state \<R> \<F> s"
  by (meson assms safe_state_before_rtranclp_step_if_safe_state_after tranclp_into_rtranclp)

lemma safe_state_if_all_states_safe:
  assumes "\<And>s. \<F> s \<or> (\<exists>s'. \<R> s s')"
  shows "safe_state \<R> \<F> s"
  using assms by (simp add: safe_state_def)

lemma matching_states_agree_on_stuck_if_they_agree_on_final:
  assumes
    final1_stuck: "\<forall>s1. final1 s1 \<longrightarrow> (\<nexists>s1'. step1 s1 s1')" and
    final2_stuck: "\<forall>s2. final2 s2 \<longrightarrow> (\<nexists>s2'. step2 s2 s2')" and
    matching_states_agree_on_final: "\<forall>i s1 s2. match i s1 s2 \<longrightarrow> final1 s1 \<longleftrightarrow> final2 s2" and
    matching_states_are_safe:
      "\<forall>i s1 s2. match i s1 s2 \<longrightarrow> safe_state step1 final1 s1 \<and> safe_state step2 final2 s2"
  shows "\<forall>i s1 s2. match i s1 s2 \<longrightarrow> stuck_state step1 s1 \<longleftrightarrow> stuck_state step2 s2"
    using assms by (metis rtranclp.rtrancl_refl safe_state_def stuck_state_def)


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

  show thesis
  proof (rule that)
    show "\<And>i s1 s2. match i s1 s2 \<Longrightarrow> \<exists>j. MATCH j s1 s2"
      using MATCH_if_match .
  next
    show "\<And>j s1 s2. MATCH j s1 s2 \<Longrightarrow> final1 s1 = final2 s2"
      using MATCH_spec
      by (metis converse_tranclpE final1_stuck final2_stuck matching_states_agree_on_final)
  next
    show "\<And>j s1 s2. MATCH j s1 s2 \<Longrightarrow> stuck_state step1 s1 = stuck_state step2 s2"
      using MATCH_spec
      by (metis stuck_state_def tranclpD)
  next
    fix j s1 s2
    assume "MATCH j s1 s2"
    then show "safe_state step1 final1 s1 \<and> safe_state step2 final2 s2"
      apply -
      apply (drule MATCH_spec)
      apply (elim disjE exE conjE)
      using matching_states_are_safe apply metis
      using safe_state_before_tranclp_step_if_safe_state_after
      by (metis assms(1) assms(2) matching_states_are_safe)
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