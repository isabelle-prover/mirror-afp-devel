section \<open>Simulations Between Dynamic Executions\<close>

theory Simulation
  imports
    Semantics
    Inf
    Well_founded
    Lifting_Simulation_To_Bisimulation
begin

subsection \<open>Backward simulation\<close>

locale backward_simulation =
  L1: semantics step1 final1 +
  L2: semantics step2 final2
  for
    step1 :: "'state1 \<Rightarrow> 'state1 \<Rightarrow> bool" and final1 :: "'state1 \<Rightarrow> bool" and
    step2 :: "'state2 \<Rightarrow> 'state2 \<Rightarrow> bool" and final2 :: "'state2 \<Rightarrow> bool" +
  fixes
    match :: "'index \<Rightarrow> 'state1 \<Rightarrow> 'state2 \<Rightarrow> bool" and
    order :: "'index \<Rightarrow> 'index \<Rightarrow> bool" (infix "\<sqsubset>" 70)
  assumes
    wfp_order:
      "wfp (\<sqsubset>)" and
    match_final:
      "match i s1 s2 \<Longrightarrow> final2 s2 \<Longrightarrow> final1 s1" and
    simulation:
      "match i s1 s2 \<Longrightarrow> step2 s2 s2' \<Longrightarrow>
        (\<exists>i' s1'. step1\<^sup>+\<^sup>+ s1 s1' \<and> match i' s1' s2') \<or> (\<exists>i'. match i' s1 s2' \<and> i' \<sqsubset> i)"
begin

text \<open>
A simulation is defined between two @{locale semantics} L1 and L2.
A @{term match} predicate expresses that two states from L1 and L2 are equivalent.
The @{term match} predicate is also parameterized with an ordering used to avoid stuttering.
The only two assumptions of a backward simulation are that a final state in L2 will also be a final in L1,and that a step in L2 will either represent a non-empty sequence of steps in L1 or will result in an equivalent state.
Stuttering is ruled out by the requirement that the index on the @{term match} predicate decreases with respect to the well-founded @{term order} ordering.
\<close>

lemma lift_simulation_plus:
  "step2\<^sup>+\<^sup>+ s2 s2' \<Longrightarrow> match i1 s1 s2 \<Longrightarrow>
    (\<exists>i2 s1'. step1\<^sup>+\<^sup>+ s1 s1' \<and> match i2 s1' s2') \<or>
    (\<exists>i2. match i2 s1 s2' \<and> order\<^sup>+\<^sup>+ i2 i1)"
  thm tranclp_induct
proof(induction s2' arbitrary: i1 s1 rule: tranclp_induct)
  case (base s2')
  from simulation[OF base.prems(1) base.hyps(1)] show ?case
    by auto
next
  case (step s2' s2'')
  show ?case
    using step.IH[OF \<open>match i1 s1 s2\<close>]
  proof
    assume "\<exists>i2 s1'. step1\<^sup>+\<^sup>+ s1 s1' \<and> match i2 s1' s2'"
    then obtain i2 s1' where "step1\<^sup>+\<^sup>+ s1 s1'" and "match i2 s1' s2'" by auto
    from simulation[OF \<open>match i2 s1' s2'\<close> \<open>step2 s2' s2''\<close>] show ?thesis
    proof
      assume "\<exists>i3 s1''. step1\<^sup>+\<^sup>+ s1' s1'' \<and> match i3 s1'' s2''"
      then obtain i3 s1'' where "step1\<^sup>+\<^sup>+ s1' s1''" and "match i3 s1'' s2''" by auto
      then show ?thesis
        using tranclp_trans[OF \<open>step1\<^sup>+\<^sup>+ s1 s1'\<close>] by auto
    next
      assume "\<exists>i3. match i3 s1' s2'' \<and> i3 \<sqsubset> i2"
      then obtain i3 where "match i3 s1' s2''" and "i3 \<sqsubset> i2" by auto
      then show ?thesis
        using \<open>step1\<^sup>+\<^sup>+ s1 s1'\<close> by auto
    qed
  next
    assume "\<exists>i2. match i2 s1 s2' \<and> (\<sqsubset>)\<^sup>+\<^sup>+ i2 i1"
    then obtain i3 where "match i3 s1 s2'" and "(\<sqsubset>)\<^sup>+\<^sup>+ i3 i1" by auto
    then show ?thesis
      using simulation[OF \<open>match i3 s1 s2'\<close> \<open>step2 s2' s2''\<close>] by auto
  qed
qed

lemma lift_simulation_eval:
  "L2.eval s2 s2' \<Longrightarrow> match i1 s1 s2 \<Longrightarrow> \<exists>i2 s1'. L1.eval s1 s1' \<and> match i2 s1' s2'"
proof(induction s2 arbitrary: i1 s1 rule: converse_rtranclp_induct)
  case (base s2)
  thus ?case by auto
next
  case (step s2 s2'')
  from simulation[OF \<open>match i1 s1 s2\<close> \<open>step2 s2 s2''\<close>] show ?case
  proof
    assume "\<exists>i2 s1'. step1\<^sup>+\<^sup>+ s1 s1' \<and> match i2 s1' s2''"
    thus ?thesis
      by (meson rtranclp_trans step.IH tranclp_into_rtranclp)
  next
    assume "\<exists>i2. match i2 s1 s2'' \<and> i2 \<sqsubset> i1"
    thus ?thesis
      by (auto intro: step.IH)
  qed
qed

lemma match_inf:
  assumes
    "match i s1 s2" and
    "inf step2 s2"
  shows "inf step1 s1"
proof -
  from assms have "inf_wf step1 order i s1"
  proof (coinduction arbitrary: i s1 s2)
    case inf_wf
    obtain s2' where "step2 s2 s2'" and "inf step2 s2'"
      using inf_wf(2) by (auto elim: inf.cases)
    from simulation[OF \<open>match i s1 s2\<close> \<open>step2 s2 s2'\<close>] show ?case
      using \<open>inf step2 s2'\<close> by auto
  qed
  thus ?thesis using inf_wf_to_inf
    by (auto intro: inf_wf_to_inf wfp_order)
qed

subsubsection \<open>Preservation of behaviour\<close>

text \<open>
The main correctness theorem states that, for any two matching programs, any not wrong behaviour of the later is also a behaviour of the former.
In other words, if the compiled program does not crash, then its behaviour, whether it terminates or not, is a also a valid behaviour of the source program.
\<close>

lemma simulation_behaviour :
  "L2.state_behaves s\<^sub>2 b\<^sub>2 \<Longrightarrow> \<not>is_wrong b\<^sub>2 \<Longrightarrow> match i s\<^sub>1 s\<^sub>2 \<Longrightarrow>
    \<exists>b\<^sub>1 i'. L1.state_behaves s\<^sub>1 b\<^sub>1 \<and> rel_behaviour (match i') b\<^sub>1 b\<^sub>2"
proof(induction rule: L2.state_behaves.cases)
  case (state_terminates s2 s2')
  then obtain i' s1' where "L1.eval s\<^sub>1 s1'" and "match i' s1' s2'"
    using lift_simulation_eval by blast
  hence "final1 s1'"
    by (auto intro: state_terminates.hyps match_final)
  hence "L1.state_behaves s\<^sub>1 (Terminates s1')"
    using L1.final_finished
    by (simp add: L1.state_terminates \<open>L1.eval s\<^sub>1 s1'\<close>)
  moreover have "rel_behaviour (match i') (Terminates s1') b\<^sub>2"
    by (simp add: \<open>match i' s1' s2'\<close> state_terminates.hyps)
  ultimately show ?case by blast
next
  case (state_diverges s2)
  then show ?case
    using match_inf L1.state_diverges by fastforce
next
  case (state_goes_wrong s2 s2')
  then show ?case using \<open>\<not>is_wrong b\<^sub>2\<close> by simp
qed

end

subsection \<open>Forward simulation\<close>

locale forward_simulation =
  L1: semantics step1 final1 +
  L2: semantics step2 final2
  for
    step1 :: "'state1 \<Rightarrow> 'state1 \<Rightarrow> bool" and final1 :: "'state1 \<Rightarrow> bool" and
    step2 :: "'state2 \<Rightarrow> 'state2 \<Rightarrow> bool" and final2 :: "'state2 \<Rightarrow> bool" +
  fixes
    match :: "'index \<Rightarrow> 'state1 \<Rightarrow> 'state2 \<Rightarrow> bool" and
    order :: "'index \<Rightarrow> 'index \<Rightarrow> bool" (infix "\<sqsubset>" 70)
  assumes
    wfp_order:
      "wfp (\<sqsubset>)" and
    match_final:
      "match i s1 s2 \<Longrightarrow> final1 s1 \<Longrightarrow> final2 s2" and
    simulation:
      "match i s1 s2 \<Longrightarrow> step1 s1 s1' \<Longrightarrow>
        (\<exists>i' s2'. step2\<^sup>+\<^sup>+ s2 s2' \<and> match i' s1' s2') \<or> (\<exists>i'. match i' s1' s2 \<and> i' \<sqsubset> i)"
begin

lemma lift_simulation_plus:
  "step1\<^sup>+\<^sup>+ s1 s1' \<Longrightarrow> match i s1 s2 \<Longrightarrow>
    (\<exists>i' s2'. step2\<^sup>+\<^sup>+ s2 s2' \<and> match i' s1' s2') \<or>
    (\<exists>i'. match i' s1' s2 \<and> order\<^sup>+\<^sup>+ i' i)"
proof (induction s1' arbitrary: i s2 rule: tranclp_induct)
  case (base s1')
  with simulation[OF base.prems(1) base.hyps(1)] show ?case
    by auto
next
  case (step s1' s1'')
  show ?case
    using step.IH[OF \<open>match i s1 s2\<close>]
  proof (elim disjE exE conjE)
    fix i' s2'
    assume "step2\<^sup>+\<^sup>+ s2 s2'" and "match i' s1' s2'"

    have "(\<exists>i' s2'a. step2\<^sup>+\<^sup>+ s2' s2'a \<and> match i' s1'' s2'a) \<or> (\<exists>i'a. match i'a s1'' s2' \<and> i'a \<sqsubset> i')"
      using simulation[OF \<open>match i' s1' s2'\<close> \<open>step1 s1' s1''\<close>] .
    thus ?thesis
    proof (elim disjE exE conjE)
      fix i'' s2''
      assume "step2\<^sup>+\<^sup>+ s2' s2''" and "match i'' s1'' s2''"
      thus ?thesis
        using tranclp_trans[OF \<open>step2\<^sup>+\<^sup>+ s2 s2'\<close>] by auto
    next
      fix i''
      assume "match i'' s1'' s2'" and "i'' \<sqsubset> i'"
      thus ?thesis
        using \<open>step2\<^sup>+\<^sup>+ s2 s2'\<close> by auto
    qed
  next
    fix i'
    assume "match i' s1' s2" and "(\<sqsubset>)\<^sup>+\<^sup>+ i' i"
    then show ?thesis
      using simulation[OF \<open>match i' s1' s2\<close> \<open>step1 s1' s1''\<close>] by auto
  qed
qed

lemma lift_simulation_eval:
  "L1.eval s1 s1' \<Longrightarrow> match i s1 s2 \<Longrightarrow> \<exists>i' s2'. L2.eval s2 s2' \<and> match i' s1' s2'"
proof(induction s1 arbitrary: i s2 rule: converse_rtranclp_induct)
  case (base s2)
  thus ?case by auto
next
  case (step s1 s1'')
  show ?case
    using simulation[OF \<open>match i s1 s2\<close> \<open>step1 s1 s1''\<close>]
  proof (elim disjE exE conjE)
    fix i' s2'
    assume "step2\<^sup>+\<^sup>+ s2 s2'" and "match i' s1'' s2'"
    thus ?thesis
      by (auto intro: rtranclp_trans dest!: tranclp_into_rtranclp step.IH)
  next
    fix i'
    assume "match i' s1'' s2" and "i' \<sqsubset> i"
    thus ?thesis
      by (auto intro: step.IH)
  qed
qed

lemma match_inf:
  assumes "match i s1 s2" and "inf step1 s1"
  shows "inf step2 s2"
proof -
  from assms have "inf_wf step2 order i s2"
  proof (coinduction arbitrary: i s1 s2)
    case inf_wf
    obtain s1' where step_s1: "step1 s1 s1'" and inf_s1': "inf step1 s1'"
      using inf_wf(2) by (auto elim: inf.cases)
    from simulation[OF \<open>match i s1 s2\<close> step_s1] show ?case
      using inf_s1' by auto
  qed
  thus ?thesis using inf_wf_to_inf
    by (auto intro: inf_wf_to_inf wfp_order)
qed


subsubsection \<open>Preservation of behaviour\<close>

lemma simulation_behaviour :
  "L1.state_behaves s1 b1 \<Longrightarrow> \<not> is_wrong b1 \<Longrightarrow> match i s1 s2 \<Longrightarrow>
    \<exists>b2 i'. L2.state_behaves s2 b2 \<and> rel_behaviour (match i') b1 b2"
proof(induction rule: L1.state_behaves.cases)
  case (state_terminates s1 s1')
  then obtain i' s2' where steps_s2: "L2.eval s2 s2'" and match_s1'_s2': "match i' s1' s2'"
    using lift_simulation_eval by blast
  hence "final2 s2'"
    by (auto intro: state_terminates.hyps match_final)
  hence "L2.state_behaves s2 (Terminates s2')"
    using L2.final_finished L2.state_terminates[OF steps_s2]
    by simp
  moreover have "rel_behaviour (match i') b1 (Terminates s2')"
    by (simp add: \<open>match i' s1' s2'\<close> state_terminates.hyps)
  ultimately show ?case by blast
next
  case (state_diverges s2)
  then show ?case
    using match_inf[THEN L2.state_diverges] by fastforce
next
  case (state_goes_wrong s2 s2')
  then show ?case using \<open>\<not>is_wrong b1\<close> by simp
qed


subsubsection \<open>Forward to backward\<close>

lemma state_behaves_forward_to_backward:
  assumes
    match_s1_s2: "match i s1 s2" and
    safe_s1: "L1.safe s1" and
    behaves_s2: "L2.state_behaves s2 b2" and
    right_unique2: "right_unique step2"
  shows "\<exists>b1 i. L1.state_behaves s1 b1 \<and> rel_behaviour (match i) b1 b2"
proof -
  obtain b1 where behaves_s1: "L1.state_behaves s1 b1"
    using L1.left_total_state_behaves
    by (auto elim: left_totalE)

  have not_wrong_b1: "\<not> is_wrong b1"
    by (rule L1.safe_state_behaves_not_wrong[OF safe_s1 behaves_s1])

  obtain i' where "L2.state_behaves s2 b2" and rel_b1_B2: "rel_behaviour (match i') b1 b2"
    using simulation_behaviour[OF behaves_s1 not_wrong_b1 match_s1_s2]
    using L2.right_unique_state_behaves[OF right_unique2, THEN right_uniqueD]
    using behaves_s2
    by auto

  show ?thesis
    using behaves_s1 rel_b1_B2 by auto
qed

end

subsection \<open>Bisimulation\<close>

locale bisimulation =
  forward_simulation step1 final1 step2 final2 match order\<^sub>f +
  backward_simulation step1 final1 step2 final2 match order\<^sub>b
  for
    step1 :: "'state1 \<Rightarrow> 'state1 \<Rightarrow> bool" and final1 :: "'state1 \<Rightarrow> bool" and
    step2 :: "'state2 \<Rightarrow> 'state2 \<Rightarrow> bool" and final2 :: "'state2 \<Rightarrow> bool" and
    match :: "'index \<Rightarrow> 'state1 \<Rightarrow> 'state2 \<Rightarrow> bool" and
    order\<^sub>f :: "'index \<Rightarrow> 'index \<Rightarrow> bool" and
    order\<^sub>b :: "'index \<Rightarrow> 'index \<Rightarrow> bool"

lemma (in bisimulation) agree_on_final:
  assumes "match i s1 s2"
  shows "final1 s1 \<longleftrightarrow> final2 s2"
  by (meson assms forward_simulation.match_final forward_simulation_axioms match_final)

lemma obtains_bisimulation_from_forward_simulation:
  fixes
    step1 :: "'state1 \<Rightarrow> 'state1 \<Rightarrow> bool" and final1 :: "'state1 \<Rightarrow> bool" and
    step2 :: "'state2 \<Rightarrow> 'state2 \<Rightarrow> bool" and final2 :: "'state2 \<Rightarrow> bool" and
    match :: "'index \<Rightarrow> 'state1 \<Rightarrow> 'state2 \<Rightarrow> bool" and
    lt :: "'index \<Rightarrow> 'index \<Rightarrow> bool"
  assumes "right_unique step1" and "right_unique step2" and
    final1_stuck: "\<forall>s1. final1 s1 \<longrightarrow> (\<nexists>s1'. step1 s1 s1')" and
    final2_stuck: "\<forall>s2. final2 s2 \<longrightarrow> (\<nexists>s2'. step2 s2 s2')" and
    matching_states_agree_on_final: "\<forall>i s1 s2. match i s1 s2 \<longrightarrow> final1 s1 \<longleftrightarrow> final2 s2" and
    matching_states_are_safe:
      "\<forall>i s1 s2. match i s1 s2 \<longrightarrow> safe_state step1 final1 s1 \<and> safe_state step2 final2 s2" and
    "wfP lt" and
    fsim: "\<forall>i s1 s2 s1'. match i s1 s2 \<longrightarrow> step1 s1 s1' \<longrightarrow>
      (\<exists>i' s2'. step2\<^sup>+\<^sup>+ s2 s2' \<and> match i' s1' s2') \<or> (\<exists>i'. match i' s1' s2 \<and> lt i' i)"
  obtains
    MATCH :: "nat \<times> nat \<Rightarrow> 'state1 \<Rightarrow> 'state2 \<Rightarrow> bool" and
    ORDER :: "nat \<times> nat \<Rightarrow> nat \<times> nat \<Rightarrow> bool"
  where
    "bisimulation step1 final1 step2 final2 MATCH ORDER ORDER"
proof -
  have "simulation step1 step2 match lt"
    using fsim unfolding simulation_def by metis

  obtain
    MATCH :: "nat \<times> nat \<Rightarrow> 'state1 \<Rightarrow> 'state2 \<Rightarrow> bool" and
    ORDER :: "nat \<times> nat \<Rightarrow> nat \<times> nat \<Rightarrow> bool"
  where
    "(\<And>i s1 s2. match i s1 s2 \<Longrightarrow> \<exists>j. MATCH j s1 s2)" and
    "(\<And>j s1 s2. MATCH j s1 s2 \<Longrightarrow> final1 s1 = final2 s2)" and
    "(\<And>j s1 s2. MATCH j s1 s2 \<Longrightarrow> stuck_state step1 s1 = stuck_state step2 s2)" and
    "(\<And>j s1 s2. MATCH j s1 s2 \<Longrightarrow> safe_state step1 final1 s1 \<and> safe_state step2 final2 s2)" and
    "wfP ORDER" and
    fsim': "simulation step1 step2 MATCH ORDER" and
    bsim': "simulation step2 step1 (\<lambda>i s2 s1. MATCH i s1 s2) ORDER"
    using lift_strong_simulation_to_bisimulation'[OF assms(1,2) final1_stuck final2_stuck
        matching_states_agree_on_final matching_states_are_safe \<open>wfP lt\<close>
        \<open>simulation step1 step2 match lt\<close>]
    by blast

  have "bisimulation step1 final1 step2 final2 MATCH ORDER ORDER"
  proof unfold_locales
    show "\<And>i s1 s2. MATCH i s1 s2 \<Longrightarrow> final1 s1 \<Longrightarrow> final2 s2"
      using \<open>\<And>s2 s1 j. MATCH j s1 s2 \<Longrightarrow> final1 s1 = final2 s2\<close> by metis
  next
    show "\<And>i s1 s2. MATCH i s1 s2 \<Longrightarrow> final2 s2 \<Longrightarrow> final1 s1"
      using \<open>\<And>s2 s1 j. MATCH j s1 s2 \<Longrightarrow> final1 s1 = final2 s2\<close> by metis
  next
    show "wfP ORDER"
      using \<open>wfP ORDER\<close> .
  next
    show "\<And>i s1 s2 s1'. MATCH i s1 s2 \<Longrightarrow> step1 s1 s1' \<Longrightarrow>
      (\<exists>i' s2'. step2\<^sup>+\<^sup>+ s2 s2' \<and> MATCH i' s1' s2') \<or> (\<exists>i'. MATCH i' s1' s2 \<and> ORDER i' i)"
      using fsim' unfolding simulation_def by metis
  next
    show "\<And>i s1 s2 s2'. MATCH i s1 s2 \<Longrightarrow> step2 s2 s2' \<Longrightarrow>
      (\<exists>i' s1'. step1\<^sup>+\<^sup>+ s1 s1' \<and> MATCH i' s1' s2') \<or> (\<exists>i'. MATCH i' s1 s2' \<and> ORDER i' i)"
      using bsim' unfolding simulation_def by metis
  next
    show "\<And>s. final1 s \<Longrightarrow> finished step1 s"
      by (simp add: final1_stuck finished_def)
  next
    show "\<And>s. final2 s \<Longrightarrow> finished step2 s"
      by (simp add: final2_stuck finished_def)
  qed

  thus thesis
    using that by metis
qed

corollary ex_bisimulation_from_forward_simulation:
  fixes
    step1 :: "'state1 \<Rightarrow> 'state1 \<Rightarrow> bool" and final1 :: "'state1 \<Rightarrow> bool" and
    step2 :: "'state2 \<Rightarrow> 'state2 \<Rightarrow> bool" and final2 :: "'state2 \<Rightarrow> bool" and
    match :: "'index \<Rightarrow> 'state1 \<Rightarrow> 'state2 \<Rightarrow> bool" and
    lt :: "'index \<Rightarrow> 'index \<Rightarrow> bool"
  assumes "right_unique step1" and "right_unique step2" and
    final1_stuck: "\<forall>s1. final1 s1 \<longrightarrow> (\<nexists>s1'. step1 s1 s1')" and
    final2_stuck: "\<forall>s2. final2 s2 \<longrightarrow> (\<nexists>s2'. step2 s2 s2')" and
    matching_states_agree_on_final: "\<forall>i s1 s2. match i s1 s2 \<longrightarrow> final1 s1 \<longleftrightarrow> final2 s2" and
    matching_states_are_safe:
      "\<forall>i s1 s2. match i s1 s2 \<longrightarrow> safe_state step1 final1 s1 \<and> safe_state step2 final2 s2" and
    "wfP lt" and
    fsim: "\<forall>i s1 s2 s1'. match i s1 s2 \<longrightarrow> step1 s1 s1' \<longrightarrow>
      (\<exists>i' s2'. step2\<^sup>+\<^sup>+ s2 s2' \<and> match i' s1' s2') \<or> (\<exists>i'. match i' s1' s2 \<and> lt i' i)"
  shows "\<exists>(MATCH :: nat \<times> nat \<Rightarrow> 'state1 \<Rightarrow> 'state2 \<Rightarrow> bool) ORDER\<^sub>f ORDER\<^sub>b.
    bisimulation step1 final1 step2 final2 MATCH ORDER\<^sub>f ORDER\<^sub>b"
  using obtains_bisimulation_from_forward_simulation[OF assms] by metis

lemma obtains_bisimulation_from_backward_simulation:
  fixes
    step1 :: "'state1 \<Rightarrow> 'state1 \<Rightarrow> bool" and final1 :: "'state1 \<Rightarrow> bool" and
    step2 :: "'state2 \<Rightarrow> 'state2 \<Rightarrow> bool" and final2 :: "'state2 \<Rightarrow> bool" and
    match :: "'index \<Rightarrow> 'state1 \<Rightarrow> 'state2 \<Rightarrow> bool" and
    lt :: "'index \<Rightarrow> 'index \<Rightarrow> bool"
  assumes "right_unique step1" and "right_unique step2" and
    final1_stuck: "\<forall>s1. final1 s1 \<longrightarrow> (\<nexists>s1'. step1 s1 s1')" and
    final2_stuck: "\<forall>s2. final2 s2 \<longrightarrow> (\<nexists>s2'. step2 s2 s2')" and
    matching_states_agree_on_final: "\<forall>i s1 s2. match i s1 s2 \<longrightarrow> final1 s1 \<longleftrightarrow> final2 s2" and
    matching_states_are_safe:
      "\<forall>i s1 s2. match i s1 s2 \<longrightarrow> safe_state step1 final1 s1 \<and> safe_state step2 final2 s2" and
    "wfP lt" and
    bsim: "\<forall>i s1 s2 s2'. match i s1 s2 \<longrightarrow> step2 s2 s2' \<longrightarrow>
      (\<exists>i' s1'. step1\<^sup>+\<^sup>+ s1 s1' \<and> match i' s1' s2') \<or> (\<exists>i'. match i' s1 s2' \<and> lt i' i)"
  obtains
    MATCH :: "nat \<times> nat \<Rightarrow> 'state1 \<Rightarrow> 'state2 \<Rightarrow> bool" and
    ORDER :: "nat \<times> nat \<Rightarrow> nat \<times> nat \<Rightarrow> bool"
  where
    "bisimulation step1 final1 step2 final2 MATCH ORDER ORDER"
proof -
  have matching_states_agree_on_final': "\<forall>i s2 s1. (\<lambda>i s2 s1. match i s1 s2) i s2 s1 \<longrightarrow> final2 s2 \<longleftrightarrow> final1 s1"
    using matching_states_agree_on_final by simp

  have matching_states_are_safe':
      "\<forall>i s2 s1. (\<lambda>i s2 s1. match i s1 s2) i s2 s1 \<longrightarrow> safe_state step2 final2 s2 \<and> safe_state step1 final1 s1"
    using matching_states_are_safe by simp

  have "simulation step2 step1 (\<lambda>i s2 s1. match i s1 s2) lt"
    using bsim unfolding simulation_def by metis

  obtain
    MATCH :: "nat \<times> nat \<Rightarrow> 'state2 \<Rightarrow> 'state1 \<Rightarrow> bool" and
    ORDER :: "nat \<times> nat \<Rightarrow> nat \<times> nat \<Rightarrow> bool"
  where
    "(\<And>i s1 s2. match i s1 s2 \<Longrightarrow> \<exists>j. MATCH j s2 s1)" and
    "(\<And>j s1 s2. MATCH j s2 s1 \<Longrightarrow> final1 s1 = final2 s2)" and
    "(\<And>j s1 s2. MATCH j s2 s1 \<Longrightarrow> stuck_state step1 s1 = stuck_state step2 s2)" and
    "(\<And>j s1 s2. MATCH j s2 s1 \<Longrightarrow> safe_state step1 final1 s1 \<and> safe_state step2 final2 s2)" and
    "wfP ORDER" and
    fsim': "simulation step1 step2 (\<lambda>i s1 s2. MATCH i s2 s1) ORDER" and
    bsim': "simulation step2 step1 (\<lambda>i s2 s1. MATCH i s2 s1) ORDER"
    using lift_strong_simulation_to_bisimulation'[OF assms(2,1) final2_stuck final1_stuck
        matching_states_agree_on_final' matching_states_are_safe' \<open>wfP lt\<close>
        \<open>simulation step2 step1 (\<lambda>i s2 s1. match i s1 s2) lt\<close>]
    by (smt (verit))

  have "bisimulation step1 final1 step2 final2 (\<lambda>i s1 s2. MATCH i s2 s1) ORDER ORDER"
  proof unfold_locales
    show "\<And>i s1 s2. MATCH i s2 s1 \<Longrightarrow> final1 s1 \<Longrightarrow> final2 s2"
      using \<open>\<And>s2 s1 j. MATCH j s2 s1 \<Longrightarrow> final1 s1 = final2 s2\<close> by metis
  next
    show "\<And>i s1 s2. MATCH i s2 s1 \<Longrightarrow> final2 s2 \<Longrightarrow> final1 s1"
      using \<open>\<And>s2 s1 j. MATCH j s2 s1 \<Longrightarrow> final1 s1 = final2 s2\<close> by metis
  next
    show "wfP ORDER"
      using \<open>wfP ORDER\<close> .
  next
    show "\<And>i s1 s2 s1'. MATCH i s2 s1 \<Longrightarrow> step1 s1 s1' \<Longrightarrow>
      (\<exists>i' s2'. step2\<^sup>+\<^sup>+ s2 s2' \<and> MATCH i' s2' s1') \<or> (\<exists>i'. MATCH i' s2 s1' \<and> ORDER i' i)"
      using fsim' unfolding simulation_def by metis
  next
    show "\<And>i s1 s2 s2'. MATCH i s2 s1 \<Longrightarrow> step2 s2 s2' \<Longrightarrow>
      (\<exists>i' s1'. step1\<^sup>+\<^sup>+ s1 s1' \<and> MATCH i' s2' s1') \<or> (\<exists>i'. MATCH i' s2' s1 \<and> ORDER i' i)"
      using bsim' unfolding simulation_def by metis
  next
    show "\<And>s. final1 s \<Longrightarrow> finished step1 s"
      by (simp add: final1_stuck finished_def)
  next
    show "\<And>s. final2 s \<Longrightarrow> finished step2 s"
      by (simp add: final2_stuck finished_def)
  qed

  thus thesis
    using that by metis
qed

corollary ex_bisimulation_from_backward_simulation:
  fixes
    step1 :: "'state1 \<Rightarrow> 'state1 \<Rightarrow> bool" and final1 :: "'state1 \<Rightarrow> bool" and
    step2 :: "'state2 \<Rightarrow> 'state2 \<Rightarrow> bool" and final2 :: "'state2 \<Rightarrow> bool" and
    match :: "'index \<Rightarrow> 'state1 \<Rightarrow> 'state2 \<Rightarrow> bool" and
    lt :: "'index \<Rightarrow> 'index \<Rightarrow> bool"
  assumes "right_unique step1" and "right_unique step2" and
    final1_stuck: "\<forall>s1. final1 s1 \<longrightarrow> (\<nexists>s1'. step1 s1 s1')" and
    final2_stuck: "\<forall>s2. final2 s2 \<longrightarrow> (\<nexists>s2'. step2 s2 s2')" and
    matching_states_agree_on_final: "\<forall>i s1 s2. match i s1 s2 \<longrightarrow> final1 s1 \<longleftrightarrow> final2 s2" and
    matching_states_are_safe:
      "\<forall>i s1 s2. match i s1 s2 \<longrightarrow> safe_state step1 final1 s1 \<and> safe_state step2 final2 s2" and
    "wfP lt" and
    bsim: "\<forall>i s1 s2 s2'. match i s1 s2 \<longrightarrow> step2 s2 s2' \<longrightarrow>
      (\<exists>i' s1'. step1\<^sup>+\<^sup>+ s1 s1' \<and> match i' s1' s2') \<or> (\<exists>i'. match i' s1 s2' \<and> lt i' i)"
  shows "\<exists>(MATCH :: nat \<times> nat \<Rightarrow> 'state1 \<Rightarrow> 'state2 \<Rightarrow> bool) ORDER\<^sub>f ORDER\<^sub>b.
    bisimulation step1 final1 step2 final2 MATCH ORDER\<^sub>f ORDER\<^sub>b"
  using obtains_bisimulation_from_backward_simulation[OF assms] by metis


subsection \<open>Composition of simulations\<close>

definition rel_comp ::
  "('a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> bool) \<Rightarrow> ('d \<Rightarrow> 'c \<Rightarrow> 'e \<Rightarrow> bool) \<Rightarrow> ('a \<times> 'd) \<Rightarrow> 'b \<Rightarrow> 'e \<Rightarrow> bool" where
  "rel_comp r1 r2 i \<equiv> (r1 (fst i) OO r2 (snd i))"


subsubsection \<open>Composition of backward simulations\<close>

lemma backward_simulation_composition:
  assumes
    "backward_simulation step1 final1 step2 final2 match1 order1"
    "backward_simulation step2 final2 step3 final3 match2 order2"
  shows
    "backward_simulation step1 final1 step3 final3
      (rel_comp match1 match2) (lex_prodp order1\<^sup>+\<^sup>+ order2)"
proof intro_locales
  show "semantics step1 final1"
    by (auto intro: backward_simulation.axioms assms)
next
  show "semantics step3 final3"
    by (auto intro: backward_simulation.axioms assms)
next
  show "backward_simulation_axioms step1 final1 step3 final3
    (rel_comp match1 match2) (lex_prodp order1\<^sup>+\<^sup>+ order2)"
  proof
    show "wfp (lex_prodp order1\<^sup>+\<^sup>+ order2)"
      using assms[THEN backward_simulation.wfp_order]
      by (simp add: lex_prodp_wfP wfp_tranclp)
  next
    fix i s1 s3
    assume
      match: "rel_comp match1 match2 i s1 s3" and
      final: "final3 s3"
    obtain i1 i2 s2 where "match1 i1 s1 s2" and "match2 i2 s2 s3" and "i = (i1, i2)"
      using match unfolding rel_comp_def by auto
    thus "final1 s1"
      using final assms[THEN backward_simulation.match_final]
      by simp
  next
    fix i s1 s3 s3'
    assume
      match: "rel_comp match1 match2 i s1 s3" and
      step: "step3 s3 s3'"
    obtain i1 i2 s2 where "match1 i1 s1 s2" and "match2 i2 s2 s3" and i_def: "i = (i1, i2)"
      using match unfolding rel_comp_def by auto
    from backward_simulation.simulation[OF assms(2) \<open>match2 i2 s2 s3\<close> step]
    show "(\<exists>i' s1'. step1\<^sup>+\<^sup>+ s1 s1' \<and> rel_comp match1 match2 i' s1' s3') \<or>
       (\<exists>i'. rel_comp match1 match2 i' s1 s3' \<and> lex_prodp order1\<^sup>+\<^sup>+ order2 i' i)"
      (is "(\<exists>i' s1'. ?STEPS i' s1') \<or> ?STALL")
    proof
      assume "\<exists>i2' s2'. step2\<^sup>+\<^sup>+ s2 s2' \<and> match2 i2' s2' s3'"
      then obtain i2' s2' where "step2\<^sup>+\<^sup>+ s2 s2'" and "match2 i2' s2' s3'" by auto
      from backward_simulation.lift_simulation_plus[OF assms(1) \<open>step2\<^sup>+\<^sup>+ s2 s2'\<close> \<open>match1 i1 s1 s2\<close>]
      show ?thesis
      proof
        assume "\<exists>i2 s1'. step1\<^sup>+\<^sup>+ s1 s1' \<and> match1 i2 s1' s2'"
        then obtain i2 s1' where "step1\<^sup>+\<^sup>+ s1 s1'" and "match1 i2 s1' s2'" by auto
        hence "?STEPS (i2, i2') s1'"
          by (auto intro: \<open>match2 i2' s2' s3'\<close> simp: rel_comp_def)
        thus ?thesis by auto
      next
        assume "\<exists>i2. match1 i2 s1 s2' \<and> order1\<^sup>+\<^sup>+ i2 i1"
        then obtain i2'' where "match1 i2'' s1 s2'" and "order1\<^sup>+\<^sup>+ i2'' i1" by auto
        hence ?STALL
          unfolding rel_comp_def i_def lex_prodp_def
          using \<open>match2 i2' s2' s3'\<close> by auto
        thus ?thesis by simp
      qed
    next
      assume "\<exists>i2'. match2 i2' s2 s3' \<and> order2 i2' i2"
      then obtain i2' where "match2 i2' s2 s3'" and "order2 i2' i2" by auto
      hence ?STALL
        unfolding rel_comp_def i_def lex_prodp_def
        using \<open>match1 i1 s1 s2\<close> by auto
      thus ?thesis by simp
    qed
  qed
qed

context
  fixes r :: "'i \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool"
begin

fun rel_comp_pow where
  "rel_comp_pow [] x y = False" |
  "rel_comp_pow [i] x y = r i x y" |
  "rel_comp_pow (i # is) x z = (\<exists>y. r i x y \<and> rel_comp_pow is y z)"

end

lemma backward_simulation_pow:
  assumes
    "backward_simulation step final step final match order"
  shows
    "backward_simulation step final step final (rel_comp_pow match) (lexp order\<^sup>+\<^sup>+)"
proof intro_locales
  show "semantics step final"
    by (auto intro: backward_simulation.axioms assms)
next
  show "backward_simulation_axioms step final step final (rel_comp_pow match) (lexp order\<^sup>+\<^sup>+)"
  proof unfold_locales
    show "wfp (lexp order\<^sup>+\<^sup>+)"
      using assms[THEN backward_simulation.wfp_order]
      by (simp add: lex_list_wfP wfp_tranclp)
  next
    fix "is" s1 s2
    assume "rel_comp_pow match is s1 s2" and "final s2"
    thus "final s1" thm rel_comp_pow.induct
    proof (induction "is" s1 s2 rule: rel_comp_pow.induct)
      case (1 x y)
      then show ?case by simp
    next
      case (2 i x y)
      then show ?case
        using backward_simulation.match_final[OF assms(1)] by simp
    next
      case (3 i1 i2 "is" x z)
      from "3.prems"[simplified] obtain y where
        match: "match i1 x y" and "rel_comp_pow match (i2 # is) y z"
        by auto
      hence "final y" using "3.IH" "3.prems" by simp
      thus ?case
        using "3.prems" match backward_simulation.match_final[OF assms(1)] by auto
    qed
  next
    fix "is" s1 s3 s3'
    assume "rel_comp_pow match is s1 s3" and "step s3 s3'"
    hence "(\<exists>is' s1'. step\<^sup>+\<^sup>+ s1 s1' \<and> length is' = length is \<and> rel_comp_pow match is' s1' s3') \<or>
      (\<exists>is'. rel_comp_pow match is' s1 s3' \<and> lexp order\<^sup>+\<^sup>+ is' is)"
    proof (induction "is" s1 s3 arbitrary: s3' rule: rel_comp_pow.induct)
      case 1
      then show ?case by simp
    next
      case (2 i s1 s3)
      from backward_simulation.simulation[OF assms(1) "2.prems"[simplified]] show ?case
      proof
        assume "\<exists>i' s1'. step\<^sup>+\<^sup>+ s1 s1' \<and> match i' s1' s3'"
        then obtain i' s1' where "step\<^sup>+\<^sup>+ s1 s1'" and "match i' s1' s3'" by auto
        hence "step\<^sup>+\<^sup>+ s1 s1' \<and> rel_comp_pow match [i'] s1' s3'" by simp
        thus ?thesis
          by (metis length_Cons)
      next
        assume "\<exists>i'. match i' s1 s3' \<and> order i' i"
        then obtain i' where "match i' s1 s3'" and "order i' i" by auto
        hence "rel_comp_pow match [i'] s1 s3' \<and> lexp order\<^sup>+\<^sup>+ [i'] [i]"
          by (simp add: lexp_head tranclp.r_into_trancl)
        thus ?thesis by blast
      qed
    next
      case (3 i1 i2 "is" s1 s3)
      from "3.prems"[simplified] obtain s2 where
        "match i1 s1 s2" and 0: "rel_comp_pow match (i2 # is) s2 s3"
        by auto
      from "3.IH"[OF 0 "3.prems"(2)] show ?case
      proof
        assume "\<exists>is' s2'. step\<^sup>+\<^sup>+ s2 s2' \<and> length is' = length (i2 # is) \<and>
          rel_comp_pow match is' s2' s3'"
        then obtain i2' is' s2' where
          "step\<^sup>+\<^sup>+ s2 s2'" and "length is' = length is" and "rel_comp_pow match (i2' # is') s2' s3'"
          by (metis Suc_length_conv)
        from backward_simulation.lift_simulation_plus[OF assms(1) \<open>step\<^sup>+\<^sup>+ s2 s2'\<close> \<open>match i1 s1 s2\<close>]
        show ?thesis
        proof
          assume "\<exists>i2 s1'. step\<^sup>+\<^sup>+ s1 s1' \<and> match i2 s1' s2'"
          thus ?thesis
            using \<open>rel_comp_pow match (i2' # is') s2' s3'\<close>
            by (metis \<open>length is' = length is\<close> length_Cons rel_comp_pow.simps(3))
        next
          assume "\<exists>i2. match i2 s1 s2' \<and> order\<^sup>+\<^sup>+ i2 i1"
          then obtain i1' where "match i1' s1 s2'" and "order\<^sup>+\<^sup>+ i1' i1" by auto
          hence "rel_comp_pow match (i1' # i2' # is') s1 s3'"
            using \<open>rel_comp_pow match (i2' # is') s2' s3'\<close> by auto
          moreover have "lexp order\<^sup>+\<^sup>+ (i1' # i2' # is') (i1 # i2 # is)"
            using \<open>order\<^sup>+\<^sup>+ i1' i1\<close> \<open>length is' = length is\<close>
            by (auto intro: lexp_head)
          ultimately show ?thesis by fast
        qed
      next
        assume "\<exists>i'. rel_comp_pow match i' s2 s3' \<and> lexp order\<^sup>+\<^sup>+ i' (i2 # is)"
        then obtain i2' is' where
          "rel_comp_pow match (i2' # is') s2 s3'" and "lexp order\<^sup>+\<^sup>+ (i2' # is') (i2 # is)"
          by (metis lexp.simps)
        thus ?thesis
          by (metis \<open>match i1 s1 s2\<close> lexp.simps(1) rel_comp_pow.simps(3))
      qed
    qed
    thus "(\<exists>is' s1'. step\<^sup>+\<^sup>+ s1 s1' \<and> rel_comp_pow match is' s1' s3') \<or>
      (\<exists>is'. rel_comp_pow match is' s1 s3' \<and> lexp order\<^sup>+\<^sup>+ is' is)"
      by auto
  qed
qed


subsubsection \<open>Composition of forward simulations\<close>

lemma forward_simulation_composition:
  assumes
    "forward_simulation step1 final1 step2 final2 match1 order1"
    "forward_simulation step2 final2 step3 final3 match2 order2"
  defines "ORDER \<equiv> \<lambda>i i'. lex_prodp order2\<^sup>+\<^sup>+ order1 (prod.swap i) (prod.swap i')"
  shows "forward_simulation step1 final1 step3 final3 (rel_comp match1 match2) ORDER"
proof intro_locales
  show "semantics step1 final1"
    using assms
    by (auto intro: forward_simulation.axioms)
next
  show "semantics step3 final3"
    using assms
    by (auto intro: forward_simulation.axioms)
next
  show "forward_simulation_axioms step1 final1 step3 final3 (rel_comp match1 match2) ORDER"
  proof unfold_locales
    have "wfp order1" and "wfp order2"
      using assms(1,2)[THEN forward_simulation.wfp_order] .

    hence "wfp (\<lambda>i i'. lex_prodp order2\<^sup>+\<^sup>+ order1 (prod.swap i) (prod.swap i'))"
      by (metis (no_types, lifting) lex_prodp_wfP wfp_if_convertible_to_wfp wfp_tranclp)

    thus "wfp ORDER"
      by (simp add: ORDER_def)
  next
    fix i s1 s3
    assume
      match: "rel_comp match1 match2 i s1 s3" and
      final: "final1 s1"
    obtain i1 i2 s2 where "match1 i1 s1 s2" and "match2 i2 s2 s3" and "i = (i1, i2)"
      using match unfolding rel_comp_def by auto
    thus "final3 s3"
      using final assms(1,2)[THEN forward_simulation.match_final]
      by simp
  next
    fix i s1 s3 s1'
    assume
      match: "rel_comp match1 match2 i s1 s3" and
      step: "step1 s1 s1'"
    obtain i1 i2 s2 where "match1 i1 s1 s2" and "match2 i2 s2 s3" and i_def: "i = (i1, i2)"
      using match unfolding rel_comp_def by auto
    from forward_simulation.simulation[OF assms(1) \<open>match1 i1 s1 s2\<close> step]
    show "(\<exists>i' s3'. step3\<^sup>+\<^sup>+ s3 s3' \<and> rel_comp match1 match2 i' s1' s3') \<or>
       (\<exists>i'. rel_comp match1 match2 i' s1' s3 \<and> ORDER i' i)"
      (is "(\<exists>i' s1'. ?STEPS i' s1') \<or> (\<exists>i'. ?STALL i')")
    proof (elim disjE exE conjE)
      fix i1' s2'
      assume "step2\<^sup>+\<^sup>+ s2 s2'" and "match1 i1' s1' s2'"
      from forward_simulation.lift_simulation_plus[OF assms(2) \<open>step2\<^sup>+\<^sup>+ s2 s2'\<close> \<open>match2 i2 s2 s3\<close>]
      show ?thesis
      proof (elim disjE exE conjE)
        fix i2' s3'
        assume "step3\<^sup>+\<^sup>+ s3 s3'" and "match2 i2' s2' s3'"
        hence "?STEPS (i1', i2') s3'"
          by (auto intro: \<open>match1 i1' s1' s2'\<close> simp: rel_comp_def)
        thus ?thesis by auto
      next
        fix i2''
        assume "match2 i2'' s2' s3" and "order2\<^sup>+\<^sup>+ i2'' i2"
        hence "?STALL (i1', i2'')"
          unfolding rel_comp_def i_def comp_def prod.swap_def prod.sel
        proof (intro conjI)
          show "(match1 i1' OO match2 i2'') s1' s3"
            using \<open>match1 i1' s1' s2'\<close> \<open>match2 i2'' s2' s3\<close>
            by (auto simp add: relcompp_apply)
        next
          show "ORDER (i1', i2'') (i1, i2)"
            unfolding ORDER_def lex_prodp_def prod.swap_def prod.sel
            using \<open>order2\<^sup>+\<^sup>+ i2'' i2\<close> by argo
        qed
        thus ?thesis
          by metis
      qed
    next
      fix i1'
      assume "match1 i1' s1' s2" and "order1 i1' i1"
      hence "?STALL (i1', i2)"
        unfolding rel_comp_def i_def prod.sel
        using \<open>match2 i2 s2 s3\<close> by (auto simp: ORDER_def lex_prodp_def)
      thus ?thesis
        by metis
    qed
  qed
qed


subsubsection \<open>Composition of bisimulations\<close>

lemma bisimulation_composition:
  fixes
    step1 :: "'s1 \<Rightarrow> 's1 \<Rightarrow> bool" and final1 :: "'s1 \<Rightarrow> bool" and
    step2 :: "'s2 \<Rightarrow> 's2 \<Rightarrow> bool" and final2 :: "'s2 \<Rightarrow> bool" and
    step3 :: "'s3 \<Rightarrow> 's3 \<Rightarrow> bool" and final3 :: "'s3 \<Rightarrow> bool" and
    match1 :: "'i \<Rightarrow> 's1 \<Rightarrow> 's2 \<Rightarrow> bool" and order1\<^sub>f order1\<^sub>b :: "'i \<Rightarrow> 'i \<Rightarrow> bool" and
    match2 :: "'j \<Rightarrow> 's2 \<Rightarrow> 's3 \<Rightarrow> bool" and order2\<^sub>f order2\<^sub>b :: "'j \<Rightarrow> 'j \<Rightarrow> bool"
  assumes
    "bisimulation step1 final1 step2 final2 match1 order1\<^sub>f order1\<^sub>b"
    "bisimulation step2 final2 step3 final3 match2 order2\<^sub>f order2\<^sub>b"
  obtains
    ORDER\<^sub>f :: "'i \<times> 'j \<Rightarrow> 'i \<times> 'j \<Rightarrow> bool" and
    ORDER\<^sub>b :: "'i \<times> 'j \<Rightarrow> 'i \<times> 'j \<Rightarrow> bool" and
    MATCH :: "'i \<times> 'j \<Rightarrow> 's1 \<Rightarrow> 's3 \<Rightarrow> bool"
  where "bisimulation step1 final1 step3 final3 MATCH ORDER\<^sub>f ORDER\<^sub>b"
proof atomize_elim
  have
    forward12: "forward_simulation step1 final1 step2 final2 match1 order1\<^sub>f" and
    forward23: "forward_simulation step2 final2 step3 final3 match2 order2\<^sub>f" and
    backward12: "backward_simulation step1 final1 step2 final2 match1 order1\<^sub>b" and
    backward23: "backward_simulation step2 final2 step3 final3 match2 order2\<^sub>b"
    using assms by (simp_all add: bisimulation.axioms)

  obtain
    ORDER\<^sub>f ORDER\<^sub>b :: "'i \<times> 'j \<Rightarrow> 'i \<times> 'j \<Rightarrow> bool" and
    MATCH :: "'i \<times> 'j \<Rightarrow> 's1 \<Rightarrow> 's3 \<Rightarrow> bool" where
    "forward_simulation step1 final1 step3 final3 MATCH ORDER\<^sub>f" and
    "backward_simulation step1 final1 step3 final3 MATCH ORDER\<^sub>b"
    unfolding atomize_conj
    using forward_simulation_composition[OF forward12 forward23]
    using backward_simulation_composition[OF backward12 backward23]
    by metis

  thus "\<exists>(MATCH :: 'i \<times> 'j \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> bool) ORDER\<^sub>f ORDER\<^sub>b.
    (bisimulation step1 final1 step3 final3 MATCH ORDER\<^sub>f ORDER\<^sub>b)"
    using bisimulation.intro by blast
qed


subsection \<open>Miscellaneous\<close>

definition lockstep_backward_simulation where
  "lockstep_backward_simulation step1 step2 match \<equiv>
    \<forall>s1 s2 s2'. match s1 s2 \<longrightarrow> step2 s2 s2' \<longrightarrow> (\<exists>s1'. step1 s1 s1' \<and> match s1' s2')"

definition plus_backward_simulation where
  "plus_backward_simulation step1 step2 match \<equiv>
    \<forall>s1 s2 s2'. match s1 s2 \<longrightarrow> step2 s2 s2' \<longrightarrow> (\<exists>s1'. step1\<^sup>+\<^sup>+ s1 s1' \<and> match s1' s2')"

lemma
  assumes "lockstep_backward_simulation step1 step2 match"
  shows "plus_backward_simulation step1 step2 match"
unfolding plus_backward_simulation_def
proof safe
  fix s1 s2 s2'
  assume "match s1 s2" and "step2 s2 s2'"
  then obtain s1' where "step1 s1 s1'" and "match s1' s2'"
    using assms(1) unfolding lockstep_backward_simulation_def by blast
  then show "\<exists>s1'. step1\<^sup>+\<^sup>+ s1 s1' \<and> match s1' s2'"
    by auto
qed

lemma lockstep_to_plus_backward_simulation:
  fixes
    match :: "'state1 \<Rightarrow> 'state2 \<Rightarrow> bool" and
    step1 :: "'state1 \<Rightarrow> 'state1 \<Rightarrow> bool" and
    step2 :: "'state2 \<Rightarrow> 'state2 \<Rightarrow> bool"
  assumes
    lockstep_simulation: "\<And>s1 s2 s2'. match s1 s2 \<Longrightarrow> step2 s2 s2' \<Longrightarrow> (\<exists>s1'. step1 s1 s1' \<and> match s1' s2')" and
    match: "match s1 s2" and
    step: "step2 s2 s2'"
  shows "\<exists>s1'. step1\<^sup>+\<^sup>+ s1 s1' \<and> match s1' s2'"
proof -
  obtain s1' where "step1 s1 s1'" and "match s1' s2'"
    using lockstep_simulation[OF match step] by auto
  thus ?thesis by auto
qed

lemma lockstep_to_option_backward_simulation:
  fixes
    match :: "'state1 \<Rightarrow> 'state2 \<Rightarrow> bool" and
    step1 :: "'state1 \<Rightarrow> 'state1 \<Rightarrow> bool" and
    step2 :: "'state2 \<Rightarrow> 'state2 \<Rightarrow> bool" and
    measure :: "'state2 \<Rightarrow> nat"
  assumes
    lockstep_simulation: "\<And>s1 s2 s2'. match s1 s2 \<Longrightarrow> step2 s2 s2' \<Longrightarrow> (\<exists>s1'. step1 s1 s1' \<and> match s1' s2')" and
    match: "match s1 s2" and
    step: "step2 s2 s2'"
  shows "(\<exists>s1'. step1 s1 s1' \<and> match s1' s2') \<or> match s1 s2' \<and> measure s2' < measure s2"
  using lockstep_simulation[OF match step] ..

lemma plus_to_star_backward_simulation:
  fixes
    match :: "'state1 \<Rightarrow> 'state2 \<Rightarrow> bool" and
    step1 :: "'state1 \<Rightarrow> 'state1 \<Rightarrow> bool" and
    step2 :: "'state2 \<Rightarrow> 'state2 \<Rightarrow> bool" and
    measure :: "'state2 \<Rightarrow> nat"
  assumes
    star_simulation: "\<And>s1 s2 s2'. match s1 s2 \<Longrightarrow> step2 s2 s2' \<Longrightarrow> (\<exists>s1'. step1\<^sup>+\<^sup>+ s1 s1' \<and> match s1' s2')" and
    match: "match s1 s2" and
    step: "step2 s2 s2'"
  shows "(\<exists>s1'. step1\<^sup>+\<^sup>+ s1 s1' \<and> match s1' s2') \<or> match s1 s2' \<and> measure s2' < measure s2"
  using star_simulation[OF match step] ..

lemma lockstep_to_plus_forward_simulation:
  fixes
    match :: "'state1 \<Rightarrow> 'state2 \<Rightarrow> bool" and
    step1 :: "'state1 \<Rightarrow> 'state1 \<Rightarrow> bool" and
    step2 :: "'state2 \<Rightarrow> 'state2 \<Rightarrow> bool"
  assumes
    lockstep_simulation: "\<And>s1 s2 s2'. match s1 s2 \<Longrightarrow> step1 s1 s1' \<Longrightarrow> (\<exists>s2'. step2 s2 s2' \<and> match s1' s2')" and
    match: "match s1 s2" and
    step: "step1 s1 s1'"
  shows "\<exists>s2'. step2\<^sup>+\<^sup>+ s2 s2' \<and> match s1' s2'"
proof -
  obtain s2' where "step2 s2 s2'" and "match s1' s2'"
    using lockstep_simulation[OF match step] by auto
  thus ?thesis by auto
qed

end