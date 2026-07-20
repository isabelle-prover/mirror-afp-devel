(* Kirstin Peters, TU Berlin, 2015 concerning the reduction semantics and
   Kirstin Peters, University of Augsburg, 2026 for the labelled semantics *)

theory SimulationRelations
  imports ProcessCalculi
begin

section \<open>Simulation Relations\<close>

text \<open>Simulation relations are a special kind of property on relations on processes. They usually
      require that steps are (strongly or weakly) preserved and/or reflected modulo the relation.
      We consider different kinds of simulation relations.\<close>

subsection \<open>Simulation\<close>

text \<open>A weak (reduction) simulation is relation R such that if (P, Q) in R and P evolves to some P'
      then there exists some Q' such that Q evolves to Q' and (P', Q') in R.\<close>

abbreviation weak_reduction_simulation :: "('proc \<times> 'proc) set \<Rightarrow> 'proc processCalculus \<Rightarrow> bool"
  where
  "weak_reduction_simulation Rel Cal \<equiv>
   \<forall>P Q P'. (P, Q) \<in> Rel \<and> P \<longmapsto>Cal* P' \<longrightarrow> (\<exists>Q'. Q \<longmapsto>Cal* Q' \<and> (P', Q') \<in> Rel)"

text \<open>A weak barbed simulation is weak reduction simulation that weakly preserves barbs.\<close>

abbreviation weak_barbed_simulation
  :: "('proc \<times> 'proc) set \<Rightarrow> ('proc, 'barbs) calculusWithBarbs \<Rightarrow> bool" where
  "weak_barbed_simulation Rel CWB \<equiv>
   weak_reduction_simulation Rel (Calculus CWB) \<and> rel_weakly_preserves_barbs Rel CWB"

text \<open>A weak labelled simulation is relation R such that if (P, Q) in R and P evolves to some P'
      using label a then there exists some Q' such that Q evolves to Q' using a and (P', Q') in R.\<close>

abbreviation weak_labelled_simulation
  :: "('proc \<times> 'proc) set \<Rightarrow> ('proc, 'lab) labelledProcessCalculus \<Rightarrow> bool" where
  "weak_labelled_simulation Rel Cal \<equiv>
   \<forall>P Q \<alpha> P'. (P, Q) \<in> Rel \<and> P \<midarrow>\<Zcat>\<alpha>\<rightarrow>Cal* P' \<longrightarrow> (\<exists>Q'. Q \<midarrow>\<Zcat>\<alpha>\<rightarrow>Cal* Q' \<and> (P', Q') \<in> Rel)"

text \<open>A weak labelled simulation also simulates words of labels including the empty word.\<close>

lemma weak_labelled_simulation_internal:
  fixes Rel    :: "('proc \<times> 'proc) set"
    and Cal    :: "('proc, 'lab) labelledProcessCalculus"
    and P Q P' :: "'proc"
  assumes simulation: "weak_labelled_simulation Rel Cal"
      and relation:   "(P, Q) \<in> Rel"
      and execution:  "P \<rightarrow>Cal* P'"
    shows "\<exists>Q'. Q \<rightarrow>Cal* Q' \<and> (P', Q') \<in> Rel"
proof -
  from execution have "P \<midarrow>\<Zcat>\<tau>-Cal\<rightarrow>Cal* P'"
    unfolding weakLabelledStep_def
    by simp
  with simulation relation obtain Q' where A1: "Q \<midarrow>\<Zcat>\<tau>-Cal\<rightarrow>Cal* Q'" and A2: "(P', Q') \<in> Rel"
    by blast
  from A1 have "Q \<rightarrow>Cal* Q'"
    unfolding weakLabelledStep_def
    by simp
  with A2 show "\<exists>Q'. Q \<rightarrow>Cal* Q' \<and> (P', Q') \<in> Rel"
    by blast
qed

lemma weak_labelled_simulation_word:
  fixes Rel    :: "('proc \<times> 'proc) set"
    and Cal    :: "('proc, 'lab) labelledProcessCalculus"
    and P Q P' :: "'proc"
    and w      :: "'lab list"
  assumes simulation: "weak_labelled_simulation Rel Cal"
      and relation:   "(P, Q) \<in> Rel"
      and execution:  "P \<midarrow>\<frown>w\<rightarrow>Cal* P'"
    shows "\<exists>Q'. Q \<midarrow>\<frown>w\<rightarrow>Cal* Q' \<and> (P', Q') \<in> Rel"
  using execution simulation relation
proof induct
  case (WLS_Nil P Cal P')
  assume "P \<rightarrow>Cal* P'" and "weak_labelled_simulation Rel Cal" and "(P, Q) \<in> Rel"
  then obtain Q' where A1: "Q \<rightarrow>Cal* Q'" and A2: "(P', Q') \<in> Rel"
    using weak_labelled_simulation_internal[of Rel Cal P Q P']
    by blast
  from A1 have "Q \<midarrow>\<frown>[]\<rightarrow>Cal* Q'"
    using weakLabelledSequence.WLS_Nil[of Q Cal Q']
    by simp
  with A2 show "\<exists>Q'. Q \<midarrow>\<frown>[]\<rightarrow>Cal* Q' \<and> (P', Q') \<in> Rel"
    by blast
next
  case (WLS_Cons P w Cal P' \<alpha> P'')
  from WLS_Cons(2) have IH: "weak_labelled_simulation Rel Cal \<and> (P, Q) \<in> Rel \<Longrightarrow>
                             \<exists>Q'. Q \<midarrow>\<frown>w\<rightarrow>Cal* Q' \<and> (P', Q') \<in> Rel"
    by simp
  assume A1: "weak_labelled_simulation Rel Cal" and "(P, Q) \<in> Rel"
  with IH obtain Q' where A2: "Q \<midarrow>\<frown>w\<rightarrow>Cal* Q'" and A3: "(P', Q') \<in> Rel"
    by blast
  assume "P' \<midarrow>\<Zcat>\<alpha>\<rightarrow>Cal* P''"
  with A1 A2 A3 obtain Q'' where A4: "Q' \<midarrow>\<Zcat>\<alpha>\<rightarrow>Cal* Q''" and A5: "(P'', Q'') \<in> Rel"
    by blast
  from A2 A4 have "Q \<midarrow>\<frown>(w@[\<alpha>])\<rightarrow>Cal* Q''"
    using weakLabelledSequence.WLS_Cons[of Q w Cal Q' \<alpha> Q'']
    by simp
  with A5 show "\<exists>Q''. Q \<midarrow>\<frown>(w@[\<alpha>])\<rightarrow>Cal* Q'' \<and> (P'', Q'') \<in> Rel"
    by blast
qed

text \<open>The reflexive and/or transitive closure of a weak simulation is a weak simulation.\<close>

lemma weak_reduction_simulation_and_closures:
  fixes Rel :: "('proc \<times> 'proc) set"
    and Cal :: "'proc processCalculus"
  assumes simulation: "weak_reduction_simulation Rel Cal"
  shows "weak_reduction_simulation (Rel\<^sup>=) Cal"
    and "weak_reduction_simulation (Rel\<^sup>+) Cal"
    and "weak_reduction_simulation (Rel\<^sup>*) Cal"
proof -
  from simulation show A: "weak_reduction_simulation (Rel\<^sup>=) Cal"
    by (auto simp add: refl, blast)
  have B: "\<And>Rel. weak_reduction_simulation Rel Cal \<Longrightarrow> weak_reduction_simulation (Rel\<^sup>+) Cal"
  proof clarify
    fix Rel P Q P'
    assume B1: "weak_reduction_simulation Rel Cal"
    assume "(P, Q) \<in> Rel\<^sup>+" and "P \<longmapsto>Cal* P'"
    thus "\<exists>Q'. Q \<longmapsto>Cal* Q' \<and> (P', Q') \<in> Rel\<^sup>+"
    proof (induct arbitrary: P')
      fix Q P'
      assume "(P, Q) \<in> Rel" and "P \<longmapsto>Cal* P'"
      with B1 obtain Q' where "Q \<longmapsto>Cal* Q'" and "(P', Q') \<in> Rel"
        by blast
      thus "\<exists>Q'. Q \<longmapsto>Cal* Q' \<and> (P', Q') \<in> Rel\<^sup>+"
        by auto
    next
      case (step Q R P')
      assume "\<And>P'. P \<longmapsto>Cal* P' \<Longrightarrow> (\<exists>Q'. Q \<longmapsto>Cal* Q' \<and> (P', Q') \<in> Rel\<^sup>+)"
         and "P \<longmapsto>Cal* P'"
      from this obtain Q' where B2: "Q \<longmapsto>Cal* Q'" and B3: "(P', Q') \<in> Rel\<^sup>+"
        by blast
      assume "(Q, R) \<in> Rel"
      with B1 B2 obtain R' where B4: "R \<longmapsto>Cal* R'" and B5: "(Q', R') \<in> Rel\<^sup>+"
        by blast
      from B3 B5 have "(P', R') \<in> Rel\<^sup>+"
        by simp
      from B4 this show "\<exists>R'. R \<longmapsto>Cal* R' \<and> (P', R') \<in> Rel\<^sup>+"
        by blast
    qed
  qed
  with simulation show "weak_reduction_simulation (Rel\<^sup>+) Cal"
    by blast
  from simulation A B[where Rel="Rel\<^sup>="]
  show "weak_reduction_simulation (Rel\<^sup>*) Cal"
      using trancl_reflcl[of Rel]
    by fast
qed

lemma weak_barbed_simulation_and_closures:
  fixes Rel :: "('proc \<times> 'proc) set"
    and CWB :: "('proc, 'barbs) calculusWithBarbs"
  assumes simulation: "weak_barbed_simulation Rel CWB"
  shows "weak_barbed_simulation (Rel\<^sup>=) CWB"
    and "weak_barbed_simulation (Rel\<^sup>+) CWB"
    and "weak_barbed_simulation (Rel\<^sup>*) CWB"
proof -
  from simulation show "weak_barbed_simulation (Rel\<^sup>=) CWB"
      using weak_reduction_simulation_and_closures(1)[where Rel="Rel" and Cal="Calculus CWB"]
            weak_preservation_of_barbs_and_closures(1)[where Rel="Rel" and CWB="CWB"]
    by blast
next
  from simulation show "weak_barbed_simulation (Rel\<^sup>+) CWB"
      using weak_reduction_simulation_and_closures(2)[where Rel="Rel" and Cal="Calculus CWB"]
            weak_preservation_of_barbs_and_closures(2)[where Rel="Rel" and CWB="CWB"]
    by blast
next
  from simulation show "weak_barbed_simulation (Rel\<^sup>*) CWB"
      using weak_reduction_simulation_and_closures(3)[where Rel="Rel" and Cal="Calculus CWB"]
            weak_preservation_of_barbs_and_closures(3)[where Rel="Rel" and CWB="CWB"]
    by blast
qed

lemma weak_labelled_simulation_and_closures:
  fixes Rel :: "('proc \<times> 'proc) set"
    and Cal :: "('proc, 'lab) labelledProcessCalculus"
  assumes simulation: "weak_labelled_simulation Rel Cal"
  shows "weak_labelled_simulation (Rel\<^sup>=) Cal"
    and "weak_labelled_simulation (Rel\<^sup>+) Cal"
    and "weak_labelled_simulation (Rel\<^sup>*) Cal"
proof -
  from simulation show A: "weak_labelled_simulation (Rel\<^sup>=) Cal"
    by (auto simp add: refl, blast)
  have B: "\<And>Rel. weak_labelled_simulation Rel Cal \<Longrightarrow> weak_labelled_simulation (Rel\<^sup>+) Cal"
  proof clarify
    fix Rel P Q \<alpha> P'
    assume B1: "weak_labelled_simulation Rel Cal"
    assume "(P, Q) \<in> Rel\<^sup>+" and "P \<midarrow>\<Zcat>\<alpha>\<rightarrow>Cal* P'"
    thus "\<exists>Q'. Q \<midarrow>\<Zcat>\<alpha>\<rightarrow>Cal* Q' \<and> (P', Q') \<in> Rel\<^sup>+"
    proof (induct arbitrary: P')
      fix Q P'
      assume "(P, Q) \<in> Rel" and "P \<midarrow>\<Zcat>\<alpha>\<rightarrow>Cal* P'"
      with B1 obtain Q' where "Q \<midarrow>\<Zcat>\<alpha>\<rightarrow>Cal* Q'" and "(P', Q') \<in> Rel"
        by blast
      thus "\<exists>Q'. Q \<midarrow>\<Zcat>\<alpha>\<rightarrow>Cal* Q' \<and> (P', Q') \<in> Rel\<^sup>+"
        by auto
    next
      case (step Q R P')
      assume "\<And>P'. P \<midarrow>\<Zcat>\<alpha>\<rightarrow>Cal* P' \<Longrightarrow> (\<exists>Q'. Q \<midarrow>\<Zcat>\<alpha>\<rightarrow>Cal* Q' \<and> (P', Q') \<in> Rel\<^sup>+)"
         and "P \<midarrow>\<Zcat>\<alpha>\<rightarrow>Cal* P'"
      from this obtain Q' where B2: "Q \<midarrow>\<Zcat>\<alpha>\<rightarrow>Cal* Q'" and B3: "(P', Q') \<in> Rel\<^sup>+"
        by blast
      assume "(Q, R) \<in> Rel"
      with B1 B2 obtain R' where B4: "R \<midarrow>\<Zcat>\<alpha>\<rightarrow>Cal* R'" and B5: "(Q', R') \<in> Rel\<^sup>+"
        by blast
      from B3 B5 have "(P', R') \<in> Rel\<^sup>+"
        by simp
      from B4 this show "\<exists>R'. R \<midarrow>\<Zcat>\<alpha>\<rightarrow>Cal* R' \<and> (P', R') \<in> Rel\<^sup>+"
        by blast
    qed
  qed
  with simulation show "weak_labelled_simulation (Rel\<^sup>+) Cal"
    by blast
  from simulation A B[where Rel="Rel\<^sup>="]
  show "weak_labelled_simulation (Rel\<^sup>*) Cal"
      using trancl_reflcl[of Rel]
    by fast
qed

text \<open>In the case of a simulation weak preservation of barbs can be replaced by the weaker
      condition that whenever (P, Q) in the relation and P has a barb then Q have to be able to
      reach this barb.\<close>

abbreviation weak_barbed_preservation_cond
  :: "('proc \<times> 'proc) set \<Rightarrow> ('proc, 'barbs) calculusWithBarbs \<Rightarrow> bool" where
  "weak_barbed_preservation_cond Rel CWB \<equiv> \<forall>P Q a. (P, Q) \<in> Rel \<and> P\<down><CWB>a \<longrightarrow> Q\<Down><CWB>a"

lemma weak_preservation_of_barbs:
  fixes Rel :: "('proc \<times> 'proc) set"
    and CWB :: "('proc, 'barbs) calculusWithBarbs"
  assumes preservation: "rel_weakly_preserves_barbs Rel CWB"
  shows "weak_barbed_preservation_cond Rel CWB"
proof clarify
  fix P Q a
  have "P \<longmapsto>(Calculus CWB)* P"
    by (simp add: steps_refl)
  moreover assume "P\<down><CWB>a"
  ultimately have "P\<Down><CWB>a"
    by blast
  moreover assume "(P, Q) \<in> Rel"
  ultimately show "Q\<Down><CWB>a"
    using preservation
    by blast
qed

lemma simulation_impl_equality_of_preservation_of_barbs_conditions:
  fixes Rel :: "('proc \<times> 'proc) set"
    and CWB :: "('proc, 'barbs) calculusWithBarbs"
  assumes simulation: "weak_reduction_simulation Rel (Calculus CWB)"
  shows "rel_weakly_preserves_barbs Rel CWB = weak_barbed_preservation_cond Rel CWB"
proof
  assume "rel_weakly_preserves_barbs Rel CWB"
  thus "weak_barbed_preservation_cond Rel CWB"
    using weak_preservation_of_barbs[where Rel="Rel" and CWB="CWB"]
    by blast
next
  assume condition: "weak_barbed_preservation_cond Rel CWB"
  show "rel_weakly_preserves_barbs Rel CWB"
  proof clarify
    fix P Q a P'
    assume "(P, Q) \<in> Rel" and "P \<longmapsto>(Calculus CWB)* P'"
    with simulation obtain Q' where A1: "Q \<longmapsto>(Calculus CWB)* Q'" and A2: "(P', Q') \<in> Rel"
      by blast
    assume "P'\<down><CWB>a"
    with A2 condition obtain Q'' where A3: "Q' \<longmapsto>(Calculus CWB)* Q''" and A4: "Q''\<down><CWB>a"
      by blast
    from A1 A3 have "Q \<longmapsto>(Calculus CWB)* Q''"
      by (rule steps_add)
    with A4 show "Q\<Down><CWB>a"
      by blast
  qed
qed

text \<open>A strong reduction simulation is relation R such that for each pair (P, Q) in R and each
      step of P to some P' there exists some Q' such that there is a step of Q to Q' and (P', Q')
      in R.\<close>

abbreviation strong_reduction_simulation :: "('proc \<times> 'proc) set \<Rightarrow> 'proc processCalculus \<Rightarrow> bool"
  where
  "strong_reduction_simulation Rel Cal \<equiv>
   \<forall>P Q P'. (P, Q) \<in> Rel \<and> P \<longmapsto>Cal P' \<longrightarrow> (\<exists>Q'. Q \<longmapsto>Cal Q' \<and> (P', Q') \<in> Rel)"

text \<open>A strong barbed simulation is strong reduction simulation that preserves barbs.\<close>

abbreviation strong_barbed_simulation
  :: "('proc \<times> 'proc) set \<Rightarrow> ('proc, 'barbs) calculusWithBarbs \<Rightarrow> bool" where
  "strong_barbed_simulation Rel CWB \<equiv>
   strong_reduction_simulation Rel (Calculus CWB) \<and> rel_preserves_barbs Rel CWB"

text \<open>A strong labelled simulation is relation R such that for each pair (P, Q) in R and each
      step of P to some P' there exists some Q' such that there is a step of Q to Q' and (P', Q')
      in R.\<close>

abbreviation strong_labelled_simulation
  :: "('proc \<times> 'proc) set \<Rightarrow> ('proc, 'lab) labelledProcessCalculus \<Rightarrow> bool" where
  "strong_labelled_simulation Rel Cal \<equiv>
   \<forall>P Q \<alpha> P'. (P, Q) \<in> Rel \<and> P \<midarrow>\<alpha>\<rightarrow>Cal P' \<longrightarrow> (\<exists>Q'. Q \<midarrow>\<alpha>\<rightarrow>Cal Q' \<and> (P', Q') \<in> Rel)"

text \<open>A strong strong simulation is also a weak simulation.\<close>

lemma strong_impl_weak_reduction_simulation:
  fixes Rel :: "('proc \<times> 'proc) set"
    and Cal :: "'proc processCalculus"
  assumes simulation: "strong_reduction_simulation Rel Cal"
  shows "weak_reduction_simulation Rel Cal"
proof clarify
  fix P Q P'
  assume A1: "(P, Q) \<in> Rel"
  assume "P \<longmapsto>Cal* P'"
  from this obtain n where "P \<longmapsto>Cal\<^bsup>n\<^esup> P'"
    by (auto simp add: steps_def)
  thus "\<exists>Q'. Q \<longmapsto>Cal* Q' \<and> (P', Q') \<in> Rel"
  proof (induct n arbitrary: P')
    case 0
    assume "P \<longmapsto>Cal\<^bsup>0\<^esup> P'"
    hence "P = P'"
      by (simp add: steps_refl)
    moreover have "Q \<longmapsto>Cal* Q"
      by (rule steps_refl)
    ultimately show "\<exists>Q'. Q \<longmapsto>Cal* Q' \<and> (P', Q') \<in> Rel"
      using A1
      by blast
  next
    case (Suc n P'')
    assume "P \<longmapsto>Cal\<^bsup>Suc n\<^esup> P''"
    from this obtain P' where A2: "P \<longmapsto>Cal\<^bsup>n\<^esup>P'" and A3: "P' \<longmapsto>Cal P''"
      by auto
    assume "\<And>P'. P \<longmapsto>Cal\<^bsup>n\<^esup> P' \<Longrightarrow> \<exists>Q'. Q \<longmapsto>Cal* Q' \<and> (P', Q') \<in> Rel"
    with A2 obtain Q' where A4: "Q \<longmapsto>Cal* Q'" and A5: "(P', Q') \<in> Rel"
      by blast
    from simulation A5 A3 obtain Q'' where A6: "Q' \<longmapsto>Cal Q''" and A7: "(P'', Q'') \<in> Rel"
      by blast
    from A4 A6 have "Q \<longmapsto>Cal* Q''"
      using steps_add[where P="Q" and Q="Q'" and R="Q''"]
      by (simp add: step_to_steps)
    with A7 show "\<exists>Q'. Q \<longmapsto>Cal* Q' \<and> (P'', Q') \<in> Rel"
      by blast
  qed
qed

lemma strong_barbed_simulation_impl_weak_preservation_of_barbs:
  fixes Rel :: "('proc \<times> 'proc) set"
    and CWB :: "('proc, 'barbs) calculusWithBarbs"
  assumes simulation: "strong_barbed_simulation Rel CWB"
  shows "rel_weakly_preserves_barbs Rel CWB"
proof clarify
  fix P Q a P'
  assume "(P, Q) \<in> Rel" and "P \<longmapsto>(Calculus CWB)* P'"
  with simulation obtain Q' where A1: "Q \<longmapsto>(Calculus CWB)* Q'" and A2: "(P', Q') \<in> Rel"
    using strong_impl_weak_reduction_simulation[where Rel="Rel" and Cal="Calculus CWB"]
    by blast
  assume "P'\<down><CWB>a"
  with simulation A2 have "Q'\<down><CWB>a"
    by blast
  with A1 show "Q\<Down><CWB>a"
    by blast
qed

lemma strong_impl_weak_barbed_simulation:
  fixes Rel :: "('proc \<times> 'proc) set"
    and CWB :: "('proc, 'barbs) calculusWithBarbs"
  assumes simulation: "strong_barbed_simulation Rel CWB"
  shows "weak_barbed_simulation Rel CWB"
  using simulation
        strong_impl_weak_reduction_simulation[where Rel="Rel" and Cal="Calculus CWB"]
        strong_barbed_simulation_impl_weak_preservation_of_barbs[where Rel="Rel" and CWB="CWB"]
  by blast

lemma strong_simulation_impl_preservation_weak_internal_steps:
  fixes Rel    :: "('proc \<times> 'proc) set"
    and Cal    :: "('proc, 'lab) labelledProcessCalculus"
    and P Q P' :: "'proc"
  assumes simulation: "strong_labelled_simulation Rel Cal"
      and relation:   "(P, Q) \<in> Rel"
      and steps:      "P \<rightarrow>Cal* P'"
    shows "\<exists>Q'. Q \<rightarrow>Cal* Q' \<and> (P', Q') \<in> Rel"
  using steps simulation relation
proof (induct)
  case (WTS_refl P Cal)
  assume "(P, Q) \<in> Rel"
  moreover have "Q \<rightarrow>Cal* Q"
    using weakTauStep.WTS_refl[of Q Cal] .
  ultimately show "\<exists>Q'. Q \<rightarrow>Cal* Q' \<and> (P, Q') \<in> Rel"
    by blast
next
  case (WTS_trans P Cal P' P'')
  from WTS_trans(2) have IH: "strong_labelled_simulation Rel Cal \<and> (P, Q) \<in> Rel \<Longrightarrow>
                              \<exists>Q'. Q \<rightarrow>Cal* Q' \<and> (P', Q') \<in> Rel"
    by simp
  assume A1: "strong_labelled_simulation Rel Cal" and "(P, Q) \<in> Rel"
  with IH obtain Q' where A2: "Q \<rightarrow>Cal* Q'" and A3: "(P', Q') \<in> Rel"
    by blast
  assume "P' \<midarrow>\<tau>-Cal\<rightarrow>Cal P''"
  with A1 A3 obtain Q'' where A4: "Q' \<midarrow>\<tau>-Cal\<rightarrow>Cal Q''" and A5: "(P'', Q'') \<in> Rel"
    by blast
  from A2 A4 have "Q \<rightarrow>Cal* Q''"
    using weakTauStep.WTS_trans[of Q Cal Q' Q'']
    by simp
  with A5 show "\<exists>Q''. Q \<rightarrow>Cal* Q'' \<and> (P'', Q'') \<in> Rel"
    by blast
qed

lemma strong_impl_weak_labelled_simulation:
  fixes Rel :: "('proc \<times> 'proc) set"
    and Cal :: "('proc, 'lab) labelledProcessCalculus"
  assumes simulation: "strong_labelled_simulation Rel Cal"
  shows "weak_labelled_simulation Rel Cal"
proof clarify
  fix P Q \<alpha> P'
  assume A1: "(P, Q) \<in> Rel"
  assume "P \<midarrow>\<Zcat>\<alpha>\<rightarrow>Cal* P'"
  thus "\<exists>Q'. Q \<midarrow>\<Zcat>\<alpha>\<rightarrow>Cal* Q' \<and> (P', Q') \<in> Rel"
    unfolding weakLabelledStep_def
  proof (cases "\<alpha> = \<tau>-Cal", simp_all)
    assume "\<alpha> = \<tau>-Cal"
    assume "P \<rightarrow>Cal* P'"
    with simulation A1 show "\<exists>Q'. Q \<rightarrow>Cal* Q' \<and> (P', Q') \<in> Rel"
      using strong_simulation_impl_preservation_weak_internal_steps[of Rel Cal P Q P']
      by simp
  next
    assume A2: "\<alpha> \<noteq> \<tau>-Cal" and "P \<midarrow>\<alpha>\<rightarrow>Cal* P'"
    then obtain R S where A3: "P \<rightarrow>Cal* R" and A4: "R \<midarrow>\<alpha>\<rightarrow>Cal S" and A5: "S \<rightarrow>Cal* P'"
      unfolding weakLabelledActionStep_def
      by blast
    from simulation A1 A3 obtain R' where A6: "Q \<rightarrow>Cal* R'" and A7: "(R, R') \<in> Rel"
      using strong_simulation_impl_preservation_weak_internal_steps[of Rel Cal P Q R]
      by blast
    from simulation A4 A7 obtain S' where A8: "R' \<midarrow>\<alpha>\<rightarrow>Cal S'" and A9: "(S, S') \<in> Rel"
      by blast
    from simulation A5 A9 obtain Q' where A10: "S' \<rightarrow>Cal* Q'" and A11: "(P', Q') \<in> Rel"
      using strong_simulation_impl_preservation_weak_internal_steps[of Rel Cal S S' P']
      by blast
    from A2 A6 A8 A10 have "Q \<midarrow>\<alpha>\<rightarrow>Cal* Q'"
      unfolding weakLabelledActionStep_def
      by blast
    with A11 show "\<exists>Q'. Q \<midarrow>\<alpha>\<rightarrow>Cal* Q' \<and> (P', Q') \<in> Rel"
      by blast
  qed
qed

text \<open>The reflexive and/or transitive closure of a strong simulation is a strong simulation.\<close>

lemma strong_reduction_simulation_and_closures:
  fixes Rel :: "('proc \<times> 'proc) set"
    and Cal :: "'proc processCalculus"
  assumes simulation: "strong_reduction_simulation Rel Cal"
  shows "strong_reduction_simulation (Rel\<^sup>=) Cal"
    and "strong_reduction_simulation (Rel\<^sup>+) Cal"
    and "strong_reduction_simulation (Rel\<^sup>*) Cal"
proof -
  from simulation show A: "strong_reduction_simulation (Rel\<^sup>=) Cal"
    by (auto simp add: refl, blast)
  have B: "\<And>Rel. strong_reduction_simulation Rel Cal \<Longrightarrow> strong_reduction_simulation (Rel\<^sup>+) Cal"
  proof clarify
    fix Rel P Q P'
    assume B1: "strong_reduction_simulation Rel Cal"
    assume "(P, Q) \<in> Rel\<^sup>+" and "P \<longmapsto>Cal P'"
    thus "\<exists>Q'. Q \<longmapsto>Cal Q' \<and> (P', Q') \<in> Rel\<^sup>+"
    proof (induct arbitrary: P')
      fix Q P'
      assume "(P, Q) \<in> Rel" and "P \<longmapsto>Cal P'"
      with B1 obtain Q' where "Q \<longmapsto>Cal Q'" and "(P', Q') \<in> Rel"
        by blast
      thus "\<exists>Q'. Q \<longmapsto>Cal Q' \<and> (P', Q') \<in> Rel\<^sup>+"
        by auto
    next
      case (step Q R P')
      assume "\<And>P'. P \<longmapsto>Cal P' \<Longrightarrow> (\<exists>Q'. Q \<longmapsto>Cal Q' \<and> (P', Q') \<in> Rel\<^sup>+)"
         and "P \<longmapsto>Cal P'"
      from this obtain Q' where B2: "Q \<longmapsto>Cal Q'" and B3: "(P', Q') \<in> Rel\<^sup>+"
        by blast
      assume "(Q, R) \<in> Rel"
      with B1 B2 obtain R' where B4: "R \<longmapsto>Cal R'" and B5: "(Q', R') \<in> Rel\<^sup>+"
        by blast
      from B3 B5 have "(P', R') \<in> Rel\<^sup>+"
        by simp
      with B4 show "\<exists>R'. R \<longmapsto>Cal R' \<and> (P', R') \<in> Rel\<^sup>+"
        by blast
    qed
  qed
  with simulation show "strong_reduction_simulation (Rel\<^sup>+) Cal"
    by blast
  from simulation A B[where Rel="Rel\<^sup>="]
  show "strong_reduction_simulation (Rel\<^sup>*) Cal"
    using trancl_reflcl[of Rel]
    by fast
qed

lemma strong_barbed_simulation_and_closures:
  fixes Rel :: "('proc \<times> 'proc) set"
    and CWB :: "('proc, 'barbs) calculusWithBarbs"
  assumes simulation: "strong_barbed_simulation Rel CWB"
  shows "strong_barbed_simulation (Rel\<^sup>=) CWB"
    and "strong_barbed_simulation (Rel\<^sup>+) CWB"
    and "strong_barbed_simulation (Rel\<^sup>*) CWB"
proof -
  from simulation show "strong_barbed_simulation (Rel\<^sup>=) CWB"
      using strong_reduction_simulation_and_closures(1)[where Rel="Rel" and Cal="Calculus CWB"]
            preservation_of_barbs_and_closures(1)[where Rel="Rel" and CWB="CWB"]
    by blast
next
  from simulation show "strong_barbed_simulation (Rel\<^sup>+) CWB"
      using strong_reduction_simulation_and_closures(2)[where Rel="Rel" and Cal="Calculus CWB"]
            preservation_of_barbs_and_closures(2)[where Rel="Rel" and CWB="CWB"]
    by blast
next
  from simulation show "strong_barbed_simulation (Rel\<^sup>*) CWB"
      using strong_reduction_simulation_and_closures(3)[where Rel="Rel" and Cal="Calculus CWB"]
            preservation_of_barbs_and_closures(3)[where Rel="Rel" and CWB="CWB"]
    by blast
qed

lemma strong_labelled_simulation_and_closures:
  fixes Rel :: "('proc \<times> 'proc) set"
    and Cal :: "('proc, 'lab) labelledProcessCalculus"
  assumes simulation: "strong_labelled_simulation Rel Cal"
  shows "strong_labelled_simulation (Rel\<^sup>=) Cal"
    and "strong_labelled_simulation (Rel\<^sup>+) Cal"
    and "strong_labelled_simulation (Rel\<^sup>*) Cal"
proof -
  from simulation show A: "strong_labelled_simulation (Rel\<^sup>=) Cal"
    by (auto simp add: refl, blast)
  have B: "\<And>Rel. strong_labelled_simulation Rel Cal \<Longrightarrow> strong_labelled_simulation (Rel\<^sup>+) Cal"
  proof clarify
    fix Rel P Q \<alpha> P'
    assume B1: "strong_labelled_simulation Rel Cal"
    assume "(P, Q) \<in> Rel\<^sup>+" and "P \<midarrow>\<alpha>\<rightarrow>Cal P'"
    thus "\<exists>Q'. Q \<midarrow>\<alpha>\<rightarrow>Cal Q' \<and> (P', Q') \<in> Rel\<^sup>+"
    proof (induct arbitrary: P')
      fix Q P'
      assume "(P, Q) \<in> Rel" and "P \<midarrow>\<alpha>\<rightarrow>Cal P'"
      with B1 obtain Q' where "Q \<midarrow>\<alpha>\<rightarrow>Cal Q'" and "(P', Q') \<in> Rel"
        by blast
      thus "\<exists>Q'. Q \<midarrow>\<alpha>\<rightarrow>Cal Q' \<and> (P', Q') \<in> Rel\<^sup>+"
        by auto
    next
      case (step Q R P')
      assume "\<And>P'. P \<midarrow>\<alpha>\<rightarrow>Cal P' \<Longrightarrow> (\<exists>Q'. Q \<midarrow>\<alpha>\<rightarrow>Cal Q' \<and> (P', Q') \<in> Rel\<^sup>+)"
         and "P \<midarrow>\<alpha>\<rightarrow>Cal P'"
      from this obtain Q' where B2: "Q \<midarrow>\<alpha>\<rightarrow>Cal Q'" and B3: "(P', Q') \<in> Rel\<^sup>+"
        by blast
      assume "(Q, R) \<in> Rel"
      with B1 B2 obtain R' where B4: "R \<midarrow>\<alpha>\<rightarrow>Cal R'" and B5: "(Q', R') \<in> Rel\<^sup>+"
        by blast
      from B3 B5 have "(P', R') \<in> Rel\<^sup>+"
        by simp
      with B4 show "\<exists>R'. R \<midarrow>\<alpha>\<rightarrow>Cal R' \<and> (P', R') \<in> Rel\<^sup>+"
        by blast
    qed
  qed
  with simulation show "strong_labelled_simulation (Rel\<^sup>+) Cal"
    by blast
  from simulation A B[where Rel="Rel\<^sup>="]
  show "strong_labelled_simulation (Rel\<^sup>*) Cal"
    using trancl_reflcl[of Rel]
    by fast
qed

subsection \<open>Contrasimulation\<close>

text \<open>A weak (reduction) contrasimulation is relation R such that if (P, Q) in R and P evolves to
      some P' then there exists some Q' such that Q evolves to Q' and (Q', P') in R.\<close>

abbreviation weak_reduction_contrasimulation
  :: "('proc \<times> 'proc) set \<Rightarrow> 'proc processCalculus \<Rightarrow> bool" where
  "weak_reduction_contrasimulation Rel Cal \<equiv>
   \<forall>P Q P'. (P, Q) \<in> Rel \<and> P \<longmapsto>Cal* P' \<longrightarrow> (\<exists>Q'. Q \<longmapsto>Cal* Q' \<and> (Q', P') \<in> Rel)"

text \<open>A weak barbed contrasimulation is weak reduction contrasimulation that weakly preserves
      barbs.\<close>

abbreviation weak_barbed_contrasimulation
  :: "('proc \<times> 'proc) set \<Rightarrow> ('proc, 'barbs) calculusWithBarbs \<Rightarrow> bool" where
  "weak_barbed_contrasimulation Rel CWB \<equiv>
   weak_reduction_contrasimulation Rel (Calculus CWB) \<and> rel_weakly_preserves_barbs Rel CWB"

text \<open>A weak labelled contrasimulation is relation R such that if (P, Q) in R and P evolves to
      some P' using word w of labels then there exists some Q' such that Q evolves to Q' using w
      and (Q', P') in R.\<close>

abbreviation weak_labelled_contrasimulation
  :: "('proc \<times> 'proc) set \<Rightarrow> ('proc, 'lab) labelledProcessCalculus \<Rightarrow> bool" where
  "weak_labelled_contrasimulation Rel Cal \<equiv>
   \<forall>P Q w P'. (P, Q) \<in> Rel \<and> P \<midarrow>\<frown>w\<rightarrow>Cal* P' \<longrightarrow> (\<exists>Q'. Q \<midarrow>\<frown>w\<rightarrow>Cal* Q' \<and> (Q', P') \<in> Rel)"

text \<open>The reflexive and/or transitive closure of a weak contrasimulation is a weak
      contrasimulation.\<close>

lemma weak_reduction_contrasimulation_and_closures:
  fixes Rel :: "('proc \<times> 'proc) set"
    and Cal :: "'proc processCalculus"
  assumes contrasimulation: "weak_reduction_contrasimulation Rel Cal"
  shows "weak_reduction_contrasimulation (Rel\<^sup>=) Cal"
    and "weak_reduction_contrasimulation (Rel\<^sup>+) Cal"
    and "weak_reduction_contrasimulation (Rel\<^sup>*) Cal"
proof -
  from contrasimulation show A: "weak_reduction_contrasimulation (Rel\<^sup>=) Cal"
    by (auto simp add: refl, blast)
  have B: "\<And>Rel. weak_reduction_contrasimulation Rel Cal
           \<Longrightarrow> weak_reduction_contrasimulation (Rel\<^sup>+) Cal"
  proof clarify
    fix Rel P Q P'
    assume B1: "weak_reduction_contrasimulation Rel Cal"
    assume "(P, Q) \<in> Rel\<^sup>+" and "P \<longmapsto>Cal* P'"
    thus "\<exists>Q'. Q \<longmapsto>Cal* Q' \<and> (Q', P') \<in> Rel\<^sup>+"
    proof (induct arbitrary: P')
      fix Q P'
      assume "(P, Q) \<in> Rel" and "P \<longmapsto>Cal* P'"
      with B1 obtain Q' where "Q \<longmapsto>Cal* Q'" and "(Q', P') \<in> Rel"
        by blast
      thus "\<exists>Q'. Q \<longmapsto>Cal* Q' \<and> (Q', P') \<in> Rel\<^sup>+"
        by auto
    next
      case (step Q R P')
      assume "\<And>P'. P \<longmapsto>Cal* P' \<Longrightarrow> (\<exists>Q'. Q \<longmapsto>Cal* Q' \<and> (Q', P') \<in> Rel\<^sup>+)"
         and "P \<longmapsto>Cal* P'"
      from this obtain Q' where B2: "Q \<longmapsto>Cal* Q'" and B3: "(Q', P') \<in> Rel\<^sup>+"
        by blast
      assume "(Q, R) \<in> Rel"
      with B1 B2 obtain R' where B4: "R \<longmapsto>Cal* R'" and B5: "(R', Q') \<in> Rel\<^sup>+"
        by blast
      from B5 B3 have "(R', P') \<in> Rel\<^sup>+"
        by simp
      with B4 show "\<exists>R'. R \<longmapsto>Cal* R' \<and> (R', P') \<in> Rel\<^sup>+"
        by blast
    qed
  qed
  with contrasimulation show "weak_reduction_contrasimulation (Rel\<^sup>+) Cal"
    by blast
  from contrasimulation A B[where Rel="Rel\<^sup>="]
  show "weak_reduction_contrasimulation (Rel\<^sup>*) Cal"
    using trancl_reflcl[of Rel]
    by fast
qed

lemma weak_barbed_contrasimulation_and_closures:
  fixes Rel :: "('proc \<times> 'proc) set"
    and CWB :: "('proc, 'barbs) calculusWithBarbs"
  assumes contrasimulation: "weak_barbed_contrasimulation Rel CWB"
  shows "weak_barbed_contrasimulation (Rel\<^sup>=) CWB"
    and "weak_barbed_contrasimulation (Rel\<^sup>+) CWB"
    and "weak_barbed_contrasimulation (Rel\<^sup>*) CWB"
proof -
  from contrasimulation show "weak_barbed_contrasimulation (Rel\<^sup>=) CWB"
    using weak_reduction_contrasimulation_and_closures(1)[where Rel="Rel" and Cal="Calculus CWB"]
          weak_preservation_of_barbs_and_closures(1)[where Rel="Rel" and CWB="CWB"]
    by blast
next
  from contrasimulation show "weak_barbed_contrasimulation (Rel\<^sup>+) CWB"
    using weak_reduction_contrasimulation_and_closures(2)[where Rel="Rel" and Cal="Calculus CWB"]
          weak_preservation_of_barbs_and_closures(2)[where Rel="Rel" and CWB="CWB"]
    by blast
next
  from contrasimulation show "weak_barbed_contrasimulation (Rel\<^sup>*) CWB"
    using weak_reduction_contrasimulation_and_closures(3)[where Rel="Rel" and Cal="Calculus CWB"]
          weak_preservation_of_barbs_and_closures(3)[where Rel="Rel" and CWB="CWB"]
    by blast
qed

lemma weak_labelled_contrasimulation_and_closures:
  fixes Rel :: "('proc \<times> 'proc) set"
    and Cal :: "('proc, 'lab) labelledProcessCalculus"
  assumes contrasimulation: "weak_labelled_contrasimulation Rel Cal"
  shows "weak_labelled_contrasimulation (Rel\<^sup>=) Cal"
    and "weak_labelled_contrasimulation (Rel\<^sup>+) Cal"
    and "weak_labelled_contrasimulation (Rel\<^sup>*) Cal"
proof -
  from contrasimulation show A: "weak_labelled_contrasimulation (Rel\<^sup>=) Cal"
    by (auto simp add: refl, blast)
  have B: "\<And>Rel. weak_labelled_contrasimulation Rel Cal
           \<Longrightarrow> weak_labelled_contrasimulation (Rel\<^sup>+) Cal"
  proof clarify
    fix Rel P Q w P'
    assume B1: "weak_labelled_contrasimulation Rel Cal"
    assume "(P, Q) \<in> Rel\<^sup>+" and "P \<midarrow>\<frown>w\<rightarrow>Cal* P'"
    thus "\<exists>Q'. Q \<midarrow>\<frown>w\<rightarrow>Cal* Q' \<and> (Q', P') \<in> Rel\<^sup>+"
    proof (induct arbitrary: P')
      fix Q P'
      assume "(P, Q) \<in> Rel" and "P \<midarrow>\<frown>w\<rightarrow>Cal* P'"
      with B1 obtain Q' where "Q \<midarrow>\<frown>w\<rightarrow>Cal* Q'" and "(Q', P') \<in> Rel"
        by blast
      thus "\<exists>Q'. Q \<midarrow>\<frown>w\<rightarrow>Cal* Q' \<and> (Q', P') \<in> Rel\<^sup>+"
        by auto
    next
      case (step Q R P')
      assume "\<And>P'. P \<midarrow>\<frown>w\<rightarrow>Cal* P' \<Longrightarrow> (\<exists>Q'. Q \<midarrow>\<frown>w\<rightarrow>Cal* Q' \<and> (Q', P') \<in> Rel\<^sup>+)"
         and "P \<midarrow>\<frown>w\<rightarrow>Cal* P'"
      from this obtain Q' where B2: "Q \<midarrow>\<frown>w\<rightarrow>Cal* Q'" and B3: "(Q', P') \<in> Rel\<^sup>+"
        by blast
      assume "(Q, R) \<in> Rel"
      with B1 B2 obtain R' where B4: "R \<midarrow>\<frown>w\<rightarrow>Cal* R'" and B5: "(R', Q') \<in> Rel\<^sup>+"
        by blast
      from B5 B3 have "(R', P') \<in> Rel\<^sup>+"
        by simp
      with B4 show "\<exists>R'. R \<midarrow>\<frown>w\<rightarrow>Cal* R' \<and> (R', P') \<in> Rel\<^sup>+"
        by blast
    qed
  qed
  with contrasimulation show "weak_labelled_contrasimulation (Rel\<^sup>+) Cal"
    by blast
  from contrasimulation A B[where Rel="Rel\<^sup>="]
  show "weak_labelled_contrasimulation (Rel\<^sup>*) Cal"
    using trancl_reflcl[of Rel]
    by fast
qed

subsection \<open>Coupled Simulation\<close>

text \<open>A weak (reduction) coupled simulation is relation R such that if (P, Q) in R and P evolves to
      some P' then there exists some Q' such that Q evolves to Q' and (P', Q') in R and there exits
      some Q' such that Q evolves to Q' and (Q', P') in R.\<close>

abbreviation weak_reduction_coupled_simulation
  :: "('proc \<times> 'proc) set \<Rightarrow> 'proc processCalculus \<Rightarrow> bool" where
  "weak_reduction_coupled_simulation Rel Cal \<equiv>
   \<forall>P Q P'. (P, Q) \<in> Rel \<and> P \<longmapsto>Cal* P'
   \<longrightarrow> (\<exists>Q'. Q \<longmapsto>Cal* Q' \<and> (P', Q') \<in> Rel) \<and> (\<exists>Q'. Q \<longmapsto>Cal* Q' \<and> (Q', P') \<in> Rel)"

text \<open>A weak barbed coupled simulation is weak reduction coupled simulation that weakly preserves
      barbs.\<close>

abbreviation weak_barbed_coupled_simulation
  :: "('proc \<times> 'proc) set \<Rightarrow> ('proc, 'barbs) calculusWithBarbs \<Rightarrow> bool" where
  "weak_barbed_coupled_simulation Rel CWB \<equiv>
   weak_reduction_coupled_simulation Rel (Calculus CWB) \<and> rel_weakly_preserves_barbs Rel CWB"

text \<open>A weak labelled coupled simulation is relation R such that if (P, Q) in R and P evolves to
      some P' using label a then there exists some Q' such that Q evolves to Q' using a and
      (P', Q') in R (simulation) and there exits some Q' such that Q evolves to Q' and (Q', P) in
      R (coupling).\<close>

abbreviation weak_labelled_coupled_simulation
  :: "('proc \<times> 'proc) set \<Rightarrow> ('proc, 'lab) labelledProcessCalculus \<Rightarrow> bool" where
  "weak_labelled_coupled_simulation Rel Cal \<equiv>
   \<forall>P Q. (P, Q) \<in> Rel \<longrightarrow> (\<forall>\<alpha> P'. P \<midarrow>\<Zcat>\<alpha>\<rightarrow>Cal* P' \<longrightarrow> (\<exists>Q'. Q \<midarrow>\<Zcat>\<alpha>\<rightarrow>Cal* Q' \<and> (P', Q') \<in> Rel))
                          \<and> (\<exists>Q'. Q \<rightarrow>Cal* Q' \<and> (Q', P) \<in> Rel)"

text \<open>A weak labelled coupled simulation also simulates words of labels including the empty word.\<close>

lemma weak_labelled_coupled_simulation_internal:
  fixes Rel    :: "('proc \<times> 'proc) set"
    and Cal    :: "('proc, 'lab) labelledProcessCalculus"
    and P Q P' :: "'proc"
  assumes simulation: "weak_labelled_coupled_simulation Rel Cal"
      and relation:   "(P, Q) \<in> Rel"
      and execution:  "P \<rightarrow>Cal* P'"
    shows "\<exists>Q'. Q \<rightarrow>Cal* Q' \<and> (P', Q') \<in> Rel"
proof -
  from execution have "P \<midarrow>\<Zcat>\<tau>-Cal\<rightarrow>Cal* P'"
    unfolding weakLabelledStep_def
    by simp
  with simulation relation obtain Q' where A1: "Q \<midarrow>\<Zcat>\<tau>-Cal\<rightarrow>Cal* Q'" and A2: "(P', Q') \<in> Rel"
    by blast
  from A1 have "Q \<rightarrow>Cal* Q'"
    unfolding weakLabelledStep_def
    by simp
  with A2 show "\<exists>Q'. Q \<rightarrow>Cal* Q' \<and> (P', Q') \<in> Rel"
    by blast
qed

lemma weak_labelled_coupled_simulation_word:
  fixes Rel    :: "('proc \<times> 'proc) set"
    and Cal    :: "('proc, 'lab) labelledProcessCalculus"
    and P Q P' :: "'proc"
    and w      :: "'lab list"
  assumes simulation: "weak_labelled_coupled_simulation Rel Cal"
      and relation:   "(P, Q) \<in> Rel"
      and execution:  "P \<midarrow>\<frown>w\<rightarrow>Cal* P'"
    shows "\<exists>Q'. Q \<midarrow>\<frown>w\<rightarrow>Cal* Q' \<and> (P', Q') \<in> Rel"
  using execution simulation relation
proof induct
  case (WLS_Nil P Cal P')
  assume "P \<rightarrow>Cal* P'" and "weak_labelled_coupled_simulation Rel Cal" and "(P, Q) \<in> Rel"
  then obtain Q' where A1: "Q \<rightarrow>Cal* Q'" and A2: "(P', Q') \<in> Rel"
    using weak_labelled_coupled_simulation_internal[of Rel Cal P Q P']
    by blast
  from A1 have "Q \<midarrow>\<frown>[]\<rightarrow>Cal* Q'"
    using weakLabelledSequence.WLS_Nil[of Q Cal Q']
    by simp
  with A2 show "\<exists>Q'. Q \<midarrow>\<frown>[]\<rightarrow>Cal* Q' \<and> (P', Q') \<in> Rel"
    by blast
next
  case (WLS_Cons P w Cal P' \<alpha> P'')
  from WLS_Cons(2) have IH: "weak_labelled_coupled_simulation Rel Cal \<and> (P, Q) \<in> Rel \<Longrightarrow>
                             \<exists>Q'. Q \<midarrow>\<frown>w\<rightarrow>Cal* Q' \<and> (P', Q') \<in> Rel"
    by simp
  assume A1: "weak_labelled_coupled_simulation Rel Cal" and "(P, Q) \<in> Rel"
  with IH obtain Q' where A2: "Q \<midarrow>\<frown>w\<rightarrow>Cal* Q'" and A3: "(P', Q') \<in> Rel"
    by blast
  assume "P' \<midarrow>\<Zcat>\<alpha>\<rightarrow>Cal* P''"
  with A1 A2 A3 obtain Q'' where A4: "Q' \<midarrow>\<Zcat>\<alpha>\<rightarrow>Cal* Q''" and A5: "(P'', Q'') \<in> Rel"
    by blast
  from A2 A4 have "Q \<midarrow>\<frown>(w@[\<alpha>])\<rightarrow>Cal* Q''"
    using weakLabelledSequence.WLS_Cons[of Q w Cal Q' \<alpha> Q'']
    by simp
  with A5 show "\<exists>Q''. Q \<midarrow>\<frown>(w@[\<alpha>])\<rightarrow>Cal* Q'' \<and> (P'', Q'') \<in> Rel"
    by blast
qed

text \<open>A weak coupled simulation combines the conditions on a weak simulation and a weak
      contrasimulation.\<close>

lemma weak_reduction_coupled_simulation_versus_simulation_and_contrasimulation:
  fixes Rel :: "('proc \<times> 'proc) set"
    and Cal :: "'proc processCalculus"
  shows "weak_reduction_coupled_simulation Rel Cal
         = (weak_reduction_simulation Rel Cal \<and> weak_reduction_contrasimulation Rel Cal)"
  by blast

lemma weak_barbed_coupled_simulation_versus_simulation_and_contrasimulation:
  fixes Rel :: "('proc \<times> 'proc) set"
    and CWB :: "('proc, 'barbs) calculusWithBarbs"
  shows "weak_barbed_coupled_simulation Rel CWB
         = (weak_barbed_simulation Rel CWB \<and> weak_barbed_contrasimulation Rel CWB)"
  by blast

lemma weak_labelled_coupled_simulation_versus_simulation_and_contrasimulation:
  fixes Rel :: "('proc \<times> 'proc) set"
    and Cal :: "('proc, 'lab) labelledProcessCalculus"
  shows "weak_labelled_coupled_simulation Rel Cal
         = (weak_labelled_simulation Rel Cal \<and> weak_labelled_contrasimulation Rel Cal)"
proof auto
  fix P Q w P'
  assume A1: "weak_labelled_coupled_simulation Rel Cal" and "(P, Q) \<in> Rel" and "P \<midarrow>\<frown>w\<rightarrow>Cal* P'"
  then obtain Q' where A2: "Q \<midarrow>\<frown>w\<rightarrow>Cal* Q'" and A3: "(P', Q') \<in> Rel"
    using weak_labelled_coupled_simulation_word[of Rel Cal P Q w P']
    by blast
  from A1 A3 obtain Q'' where A4: "Q' \<rightarrow>Cal* Q''" and A5: "(Q'', P') \<in> Rel"
    by blast
  from A2 A4 have "Q \<midarrow>\<frown>w\<rightarrow>Cal* Q''"
    using weakLabelledSequence_extend_by_internal[of Q w Cal Q' Q'']
    by simp
  with A5 show "\<exists>Q''. Q \<midarrow>\<frown>w\<rightarrow>Cal* Q'' \<and> (Q'', P') \<in> Rel"
    by blast
next
  fix P Q
  assume "weak_labelled_contrasimulation Rel Cal" and "(P, Q) \<in> Rel"
  moreover have "P \<midarrow>\<frown>[]\<rightarrow>Cal* P"
    using WTS_refl[of P Cal ] WLS_Nil[of P Cal P]
    by simp
  ultimately obtain Q' where A1: "Q \<midarrow>\<frown>[]\<rightarrow>Cal* Q'" and A2: "(Q', P) \<in> Rel"
    by blast
  hence "Q \<rightarrow>Cal* Q'"
    using internal_weakLabelledSequence[of Q Cal Q']
    by simp
  with A2 show "\<exists>Q'. Q \<rightarrow>Cal* Q' \<and> (Q', P) \<in> Rel"
    by blast
qed

text \<open>The reflexive and/or transitive closure of a weak coupled simulation is a weak coupled
      simulation.\<close>

lemma weak_reduction_coupled_simulation_and_closures:
  fixes Rel :: "('proc \<times> 'proc) set"
    and Cal :: "'proc processCalculus"
  assumes coupledSimulation: "weak_reduction_coupled_simulation Rel Cal"
  shows "weak_reduction_coupled_simulation (Rel\<^sup>=) Cal"
    and "weak_reduction_coupled_simulation (Rel\<^sup>+) Cal"
    and "weak_reduction_coupled_simulation (Rel\<^sup>*) Cal"
  using weak_reduction_simulation_and_closures[where Rel="Rel" and Cal="Cal"]
        weak_reduction_contrasimulation_and_closures[where Rel="Rel" and Cal="Cal"]
        weak_reduction_coupled_simulation_versus_simulation_and_contrasimulation[where Rel="Rel"
          and Cal="Cal"]
        coupledSimulation
  by auto

lemma weak_barbed_coupled_simulation_and_closures:
  fixes Rel :: "('proc \<times> 'proc) set"
    and CWB :: "('proc, 'barbs) calculusWithBarbs"
  assumes coupledSimulation: "weak_barbed_coupled_simulation Rel CWB"
  shows "weak_barbed_coupled_simulation (Rel\<^sup>=) CWB"
    and "weak_barbed_coupled_simulation (Rel\<^sup>+) CWB"
    and "weak_barbed_coupled_simulation (Rel\<^sup>*) CWB"
proof -
  from coupledSimulation show "weak_barbed_coupled_simulation (Rel\<^sup>=) CWB"
    using weak_reduction_coupled_simulation_and_closures(1)[where Rel="Rel" and Cal="Calculus CWB"]
          weak_preservation_of_barbs_and_closures(1)[where Rel="Rel" and CWB="CWB"]
    by blast
next
  from coupledSimulation show "weak_barbed_coupled_simulation (Rel\<^sup>+) CWB"
    using weak_reduction_coupled_simulation_and_closures(2)[where Rel="Rel" and Cal="Calculus CWB"]
          weak_preservation_of_barbs_and_closures(2)[where Rel="Rel" and CWB="CWB"]
    by blast
next
  from coupledSimulation show "weak_barbed_coupled_simulation (Rel\<^sup>*) CWB"
    using weak_reduction_coupled_simulation_and_closures(3)[where Rel="Rel" and Cal="Calculus CWB"]
          weak_preservation_of_barbs_and_closures(3)[where Rel="Rel" and CWB="CWB"]
    by blast
qed

lemma weak_labelled_coupled_simulation_and_closures:
  fixes Rel :: "('proc \<times> 'proc) set"
    and Cal :: "('proc, 'lab) labelledProcessCalculus"
  assumes coupledSimulation: "weak_labelled_coupled_simulation Rel Cal"
  shows "weak_labelled_coupled_simulation (Rel\<^sup>=) Cal"
    and "weak_labelled_coupled_simulation (Rel\<^sup>+) Cal"
    and "weak_labelled_coupled_simulation (Rel\<^sup>*) Cal"
proof -
  from coupledSimulation have A1: "weak_labelled_simulation Rel Cal"
                          and A2: "weak_labelled_contrasimulation Rel Cal"
    using weak_labelled_coupled_simulation_versus_simulation_and_contrasimulation[where Rel="Rel"
            and Cal="Cal"]
    by simp_all
  from A1 have A3: "weak_labelled_simulation (Rel\<^sup>=) Cal"
           and A4: "weak_labelled_simulation (Rel\<^sup>+) Cal"
           and A5: "weak_labelled_simulation (Rel\<^sup>*) Cal"
    using weak_labelled_simulation_and_closures[where Rel="Rel" and Cal="Cal"]
    by simp_all
  from A2 have A6: "weak_labelled_contrasimulation (Rel\<^sup>=) Cal"
           and A7: "weak_labelled_contrasimulation (Rel\<^sup>+) Cal"
           and A8: "weak_labelled_contrasimulation (Rel\<^sup>*) Cal"
    using weak_labelled_contrasimulation_and_closures[where Rel="Rel" and Cal="Cal"]
    by simp_all
  from A3 A6 show "weak_labelled_coupled_simulation (Rel\<^sup>=) Cal"
    using weak_labelled_coupled_simulation_versus_simulation_and_contrasimulation[where Rel="Rel\<^sup>="
            and Cal="Cal"]
    by simp
  from A4 A7 show "weak_labelled_coupled_simulation (Rel\<^sup>+) Cal"
    using weak_labelled_coupled_simulation_versus_simulation_and_contrasimulation[where Rel="Rel\<^sup>+"
            and Cal="Cal"]
    by simp
  from A5 A8 show "weak_labelled_coupled_simulation (Rel\<^sup>*) Cal"
    using weak_labelled_coupled_simulation_versus_simulation_and_contrasimulation[where Rel="Rel\<^sup>*"
            and Cal="Cal"]
    by simp
qed

subsection \<open>Correspondence Simulation\<close>

text \<open>A weak (reduction) correspondence simulation is relation R such that
      (1) if (P, Q) in R and P evolves to some P' then there exists some Q' such that Q evolves to
          Q' and (P', Q') in R, and
      (2) if (P, Q) in R and Q evolves to some Q' then there exists some P'' and Q'' such that P
          evolves to P'' and Q' evolves to Q'' and (P'', Q'') in R.\<close>

abbreviation weak_reduction_correspondence_simulation
  :: "('proc \<times> 'proc) set \<Rightarrow> 'proc processCalculus \<Rightarrow> bool" where
  "weak_reduction_correspondence_simulation Rel Cal \<equiv>
   (\<forall>P Q P'. (P, Q) \<in> Rel \<and> P \<longmapsto>Cal* P' \<longrightarrow> (\<exists>Q'. Q \<longmapsto>Cal* Q' \<and> (P', Q') \<in> Rel))
   \<and> (\<forall>P Q Q'. (P, Q) \<in> Rel \<and> Q \<longmapsto>Cal* Q'
      \<longrightarrow> (\<exists>P'' Q''. P \<longmapsto>Cal* P'' \<and> Q' \<longmapsto>Cal* Q'' \<and> (P'', Q'') \<in> Rel))"

text \<open>A weak barbed correspondence simulation is weak reduction correspondence simulation that
      weakly respects barbs.\<close>

abbreviation weak_barbed_correspondence_simulation
  :: "('proc \<times> 'proc) set \<Rightarrow> ('proc, 'barbs) calculusWithBarbs \<Rightarrow> bool" where
  "weak_barbed_correspondence_simulation Rel CWB \<equiv>
   weak_reduction_correspondence_simulation Rel (Calculus CWB)
   \<and> rel_weakly_respects_barbs Rel CWB"

text \<open>A weak labelled correspondence simulation is relation R such that
      (1) if (P, Q) in R and P evolves to some P' using label a then there exists some Q' such that
          Q evolves to Q' using a and (P', Q') in R, and
      (2) if (P, Q) in R and Q evolves to some Q' using label a then there exists some P'' and Q''
          such that P evolves to P'' using a and Q' evolves to Q'' using only internal steps and
          (P'', Q'') in R.\<close>

abbreviation weak_labelled_correspondence_simulation
  :: "('proc \<times> 'proc) set \<Rightarrow> ('proc, 'lab) labelledProcessCalculus \<Rightarrow> bool" where
  "weak_labelled_correspondence_simulation Rel Cal \<equiv>
   (\<forall>P Q \<alpha> P'. (P, Q) \<in> Rel \<and> P \<midarrow>\<Zcat>\<alpha>\<rightarrow>Cal* P' \<longrightarrow> (\<exists>Q'. Q \<midarrow>\<Zcat>\<alpha>\<rightarrow>Cal* Q' \<and> (P', Q') \<in> Rel))
   \<and> (\<forall>P Q \<alpha> Q'. (P, Q) \<in> Rel \<and> Q \<midarrow>\<Zcat>\<alpha>\<rightarrow>Cal* Q'
      \<longrightarrow> (\<exists>P'' Q''. P \<midarrow>\<Zcat>\<alpha>\<rightarrow>Cal* P'' \<and> Q' \<rightarrow>Cal* Q'' \<and> (P'', Q'') \<in> Rel))"

text \<open>For each weak correspondence simulation R there exists a weak coupled simulation that
      contains all pairs of R in both directions.\<close>

inductive_set cSim_cs :: "('proc \<times> 'proc) set \<Rightarrow> 'proc processCalculus \<Rightarrow> ('proc \<times> 'proc) set"
    for Rel :: "('proc \<times> 'proc) set"
    and Cal :: "'proc processCalculus"
  where
  left:  "\<lbrakk>Q \<longmapsto>Cal* Q'; (P', Q') \<in> Rel\<rbrakk> \<Longrightarrow> (P', Q) \<in> cSim_cs Rel Cal"
| right: "\<lbrakk>P \<longmapsto>Cal* P'; (Q, P) \<in> Rel\<rbrakk> \<Longrightarrow> (P', Q) \<in> cSim_cs Rel Cal"
| trans: "\<lbrakk>(P, Q) \<in> cSim_cs Rel Cal; (Q, R) \<in> cSim_cs Rel Cal\<rbrakk> \<Longrightarrow> (P, R) \<in> cSim_cs Rel Cal"

lemma weak_reduction_correspondence_simulation_impl_coupled_simulation:
  fixes Rel :: "('proc \<times> 'proc) set"
    and Cal :: "'proc processCalculus"
  assumes corrSim: "weak_reduction_correspondence_simulation Rel Cal"
  shows "weak_reduction_coupled_simulation (cSim_cs Rel Cal) Cal"
    and "\<forall>P Q. (P, Q) \<in> Rel \<longrightarrow> (P, Q) \<in> cSim_cs Rel Cal \<and> (Q, P) \<in> cSim_cs Rel Cal"
proof -
  show "weak_reduction_coupled_simulation (cSim_cs Rel Cal) Cal"
  proof (rule allI, rule allI, rule allI, rule impI, erule conjE)
    fix P Q P'
    assume "(P, Q) \<in> cSim_cs Rel Cal" and "P \<longmapsto>Cal* P'"
    thus "(\<exists>Q'. Q \<longmapsto>Cal* Q' \<and> (P', Q') \<in> cSim_cs Rel Cal)
          \<and> (\<exists>Q'. Q \<longmapsto>Cal* Q' \<and> (Q', P') \<in> cSim_cs Rel Cal)"
    proof (induct arbitrary: P')
      case (left Q Q' P)
      assume "(P, Q') \<in> Rel" and "P \<longmapsto>Cal* P'"
      with corrSim obtain Q'' where A1: "Q' \<longmapsto>Cal* Q''" and A2: "(P', Q'') \<in> Rel"
        by blast
      assume A3: "Q \<longmapsto>Cal* Q'"
      from this A1 have A4: "Q \<longmapsto>Cal* Q''"
        by (rule steps_add[where P="Q" and Q="Q'" and R="Q''"])
      have "Q'' \<longmapsto>Cal* Q''"
        by (rule steps_refl)
      with A2 have A5: "(Q'', P') \<in> cSim_cs Rel Cal"
        by (simp add: cSim_cs.right)
      from A1 A2 have "(P', Q') \<in> cSim_cs Rel Cal"
        by (rule cSim_cs.left)
      with A4 A5 A3 show ?case
        by blast
    next
      case (right P P' Q P'')
      assume "P \<longmapsto>Cal* P'" and "P' \<longmapsto>Cal* P''"
      hence B1: "P \<longmapsto>Cal* P''"
        by (rule steps_add[where P="P" and Q="P'" and R="P''"])
      assume B2: "(Q, P) \<in> Rel"
      with corrSim B1 obtain Q''' P''' where B3: "Q \<longmapsto>Cal* Q'''" and B4: "P'' \<longmapsto>Cal* P'''"
                                       and B5: "(Q''', P''') \<in> Rel"
        by blast
      from B4 B5 have B6: "(Q''', P'') \<in> cSim_cs Rel Cal"
        by (rule cSim_cs.left)
      have B7: "Q \<longmapsto>Cal* Q"
        by (rule steps_refl)
      from B1 B2 have "(P'', Q) \<in> cSim_cs Rel Cal"
        by (rule cSim_cs.right)
      with B3 B6 B7 show ?case
        by blast
    next
      case (trans P Q R P')
      assume "P \<longmapsto>Cal* P'"
         and "\<And>P'. P \<longmapsto>Cal* P' \<Longrightarrow> (\<exists>Q'. Q \<longmapsto>Cal* Q' \<and> (P', Q') \<in> cSim_cs Rel Cal)
                                     \<and> (\<exists>Q'. Q \<longmapsto>Cal* Q' \<and> (Q', P') \<in> cSim_cs Rel Cal)"
      from this obtain Q1 Q2 where C1: "Q \<longmapsto>Cal* Q1" and C2: "(Q1, P') \<in> cSim_cs Rel Cal"
                             and C3: "Q \<longmapsto>Cal* Q2" and C4: "(P', Q2) \<in> cSim_cs Rel Cal"
        by blast
      assume C5: "\<And>Q'. Q \<longmapsto>Cal* Q' \<Longrightarrow> (\<exists>R'. R \<longmapsto>Cal* R' \<and> (Q', R') \<in> cSim_cs Rel Cal)
                                         \<and> (\<exists>R'. R \<longmapsto>Cal* R' \<and> (R', Q') \<in> cSim_cs Rel Cal)"
      with C1 obtain R1 where C6: "R \<longmapsto>Cal* R1" and C7: "(R1, Q1) \<in> cSim_cs Rel Cal"
        by blast
      from C7 C2 have C8: "(R1, P') \<in> cSim_cs Rel Cal"
        by (rule cSim_cs.trans)
      from C3 C5 obtain R2 where C9: "R \<longmapsto>Cal* R2" and C10: "(Q2, R2) \<in> cSim_cs Rel Cal"
        by blast
      from C4 C10 have "(P', R2) \<in> cSim_cs Rel Cal"
        by (rule cSim_cs.trans)
      with C6 C8 C9 show ?case
        by blast
    qed
  qed
next
  show "\<forall>P Q. (P, Q) \<in> Rel \<longrightarrow> (P, Q) \<in> cSim_cs Rel Cal \<and> (Q, P) \<in> cSim_cs Rel Cal"
  proof clarify
    fix P Q
    have "Q \<longmapsto>Cal* Q"
      by (rule steps_refl)
    moreover assume "(P, Q) \<in> Rel"
    ultimately show "(P, Q) \<in> cSim_cs Rel Cal \<and> (Q, P) \<in> cSim_cs Rel Cal"
      by (simp add: cSim_cs.left cSim_cs.right)
  qed
qed

lemma weak_barbed_correspondence_simulation_impl_coupled_simulation:
  fixes Rel :: "('proc \<times> 'proc) set"
    and CWB :: "('proc, 'barbs) calculusWithBarbs"
  assumes corrSim: "weak_barbed_correspondence_simulation Rel CWB"
  shows "weak_barbed_coupled_simulation (cSim_cs Rel (Calculus CWB)) CWB"
    and "\<forall>P Q. (P, Q) \<in> Rel \<longrightarrow> (P, Q) \<in> cSim_cs Rel (Calculus CWB)
                                \<and> (Q, P) \<in> cSim_cs Rel (Calculus CWB)"
proof -
  show "weak_barbed_coupled_simulation (cSim_cs Rel (Calculus CWB)) CWB"
  proof
    from corrSim
    show "weak_reduction_coupled_simulation (cSim_cs Rel (Calculus CWB)) (Calculus CWB)"
      using weak_reduction_correspondence_simulation_impl_coupled_simulation(1)[where Rel="Rel"
            and Cal="Calculus CWB"]
      by blast
  next
    show "rel_weakly_preserves_barbs (cSim_cs Rel (Calculus CWB)) CWB"
    proof clarify
      fix P Q a P'
      assume "(P, Q) \<in> cSim_cs Rel (Calculus CWB)" and "P \<longmapsto>(Calculus CWB)* P'" and "P'\<down><CWB>a"
      thus "Q\<Down><CWB>a"
      proof (induct arbitrary: P')
        case (left Q Q' P P')
        assume "(P, Q') \<in> Rel" and "P \<longmapsto>(Calculus CWB)* P'" and "P'\<down><CWB>a"
        with corrSim obtain Q'' where A1: "Q' \<longmapsto>(Calculus CWB)* Q''" and A2: "Q''\<down><CWB>a"
          by blast
        assume "Q \<longmapsto>(Calculus CWB)* Q'"
        from this A1 have "Q \<longmapsto>(Calculus CWB)* Q''"
          by (rule steps_add)
        with A2 show "Q\<Down><CWB>a"
          by blast
      next
        case (right P P' Q P'')
        assume "(Q, P) \<in> Rel"
        moreover assume "P \<longmapsto>(Calculus CWB)* P'" and "P' \<longmapsto>(Calculus CWB)* P''"
        hence "P \<longmapsto>(Calculus CWB)* P''"
          by (rule steps_add)
        moreover assume "P''\<down><CWB>a"
        ultimately show "Q\<Down><CWB>a"
          using corrSim
          by blast
      next
        case (trans P Q R P')
        assume "\<And>P'. P \<longmapsto>(Calculus CWB)* P' \<Longrightarrow> P'\<down><CWB>a \<Longrightarrow> Q\<Down><CWB>a"
           and "P \<longmapsto>(Calculus CWB)* P'" and "P'\<down><CWB>a"
           and "\<And>Q'. Q \<longmapsto>(Calculus CWB)* Q' \<Longrightarrow> Q'\<down><CWB>a \<Longrightarrow> R\<Down><CWB>a"
        thus "R\<Down><CWB>a"
          by blast
      qed
    qed
  qed
next
  from corrSim show "\<forall>P Q. (P, Q) \<in> Rel \<longrightarrow> (P, Q) \<in> cSim_cs Rel (Calculus CWB)
                                            \<and> (Q, P) \<in> cSim_cs Rel (Calculus CWB)"
    using weak_reduction_correspondence_simulation_impl_coupled_simulation(2)[where Rel="Rel"
          and Cal="Calculus CWB"]
    by blast
qed

text \<open>The reflexive and/or transitive closure of a weak correspondence simulation is a weak
      correspondence simulation.\<close>

lemma reduction_correspondence_simulation_condition_trans:
  fixes Cal   :: "'proc processCalculus"
    and P Q R :: "'proc"
    and Rel   :: "('proc \<times> 'proc) set"
  assumes A1: "\<forall>Q'. Q \<longmapsto>Cal* Q' \<longrightarrow> (\<exists>P'' Q''. P \<longmapsto>Cal* P'' \<and> Q' \<longmapsto>Cal* Q'' \<and> (P'', Q'') \<in> Rel)"
      and A2: "\<forall>R'. R \<longmapsto>Cal* R' \<longrightarrow> (\<exists>Q'' R''. Q \<longmapsto>Cal* Q'' \<and> R' \<longmapsto>Cal* R'' \<and> (Q'', R'') \<in> Rel)"
      and A3: "weak_reduction_simulation Rel Cal"
      and A4: "trans Rel"
  shows "\<forall>R'. R \<longmapsto>Cal* R' \<longrightarrow> (\<exists>P'' R''. P \<longmapsto>Cal* P'' \<and> R' \<longmapsto>Cal* R'' \<and> (P'', R'') \<in> Rel)"
proof clarify
  fix R'
  assume "R \<longmapsto>Cal* R'"
  with A2 obtain Q'' R'' where A5: "Q \<longmapsto>Cal* Q''" and A6: "R' \<longmapsto>Cal* R''"
                           and A7: "(Q'', R'') \<in> Rel"
    by blast
  from A1 A5 obtain P''' Q''' where A8: "P \<longmapsto>Cal* P'''" and A9: "Q'' \<longmapsto>Cal* Q'''"
                               and A10: "(P''', Q''') \<in> Rel"
    by blast
  from A3 A7 A9 obtain R''' where A11: "R'' \<longmapsto>Cal* R'''" and A12: "(Q''', R''') \<in> Rel"
    by blast
  from A6 A11 have A13: "R' \<longmapsto>Cal* R'''"
    by (rule steps_add[where P="R'" and Q="R''" and R="R'''"])
  from A4 A10 A12 have "(P''', R''') \<in> Rel"
    unfolding trans_def
    by blast
  with A8 A13 show "\<exists>P'' R''. P \<longmapsto>Cal* P'' \<and> R' \<longmapsto>Cal* R'' \<and> (P'', R'') \<in> Rel"
    by blast
qed

lemma weak_reduction_correspondence_simulation_and_closures:
  fixes Rel :: "('proc \<times> 'proc) set"
    and Cal :: "'proc processCalculus"
  assumes corrSim: "weak_reduction_correspondence_simulation Rel Cal"
  shows "weak_reduction_correspondence_simulation (Rel\<^sup>=) Cal"
    and "weak_reduction_correspondence_simulation (Rel\<^sup>+) Cal"
    and "weak_reduction_correspondence_simulation (Rel\<^sup>*) Cal"
proof -
  show A: "weak_reduction_correspondence_simulation (Rel\<^sup>=) Cal"
  proof
    from corrSim show "weak_reduction_simulation (Rel\<^sup>=) Cal"
      using weak_reduction_simulation_and_closures(1)[where Rel="Rel" and Cal="Cal"]
      by blast
  next
    show "\<forall>P Q Q'. (P, Q) \<in> Rel\<^sup>= \<and> Q \<longmapsto>Cal* Q'
          \<longrightarrow> (\<exists>P'' Q''. P \<longmapsto>Cal* P'' \<and> Q' \<longmapsto>Cal* Q'' \<and> (P'', Q'') \<in> Rel\<^sup>=)"
    proof clarify
      fix P Q Q'
      assume "(P, Q) \<in> Rel\<^sup>=" and A1: "Q \<longmapsto>Cal* Q'"
      moreover have "P = Q \<Longrightarrow> \<exists>P'' Q''. P \<longmapsto>Cal* P'' \<and> Q' \<longmapsto>Cal* Q'' \<and> (P'', Q'') \<in> Rel\<^sup>="
      proof -
        assume "P = Q"
        moreover have "Q' \<longmapsto>Cal* Q'"
          by (rule steps_refl)
        ultimately show "\<exists>P'' Q''. P \<longmapsto>Cal* P'' \<and> Q' \<longmapsto>Cal* Q'' \<and> (P'', Q'') \<in> Rel\<^sup>="
          using A1
          by blast
      qed
      moreover
      have "(P, Q) \<in> Rel \<Longrightarrow> \<exists>P'' Q''. P \<longmapsto>Cal* P'' \<and> Q' \<longmapsto>Cal* Q'' \<and> (P'', Q'') \<in> Rel\<^sup>="
      proof -
        assume "(P, Q) \<in> Rel"
        with corrSim A1 obtain P'' Q'' where "P \<longmapsto>Cal* P''" and "Q' \<longmapsto>Cal* Q''"
                                         and "(P'', Q'') \<in> Rel"
          by blast
        thus "\<exists>P'' Q''. P \<longmapsto>Cal* P'' \<and> Q' \<longmapsto>Cal* Q'' \<and> (P'', Q'') \<in> Rel\<^sup>="
          by auto
      qed
      ultimately show "\<exists>P'' Q''. P \<longmapsto>Cal* P'' \<and> Q' \<longmapsto>Cal* Q'' \<and> (P'', Q'') \<in> Rel\<^sup>="
        by auto
    qed
  qed
  have B: "\<And>Rel. weak_reduction_correspondence_simulation Rel Cal
           \<Longrightarrow> weak_reduction_correspondence_simulation (Rel\<^sup>+) Cal"
  proof
    fix Rel
    assume "weak_reduction_correspondence_simulation Rel Cal"
    thus "weak_reduction_simulation (Rel\<^sup>+) Cal"
      using weak_reduction_simulation_and_closures(2)[where Rel="Rel" and Cal="Cal"]
      by blast
  next
    fix Rel
    assume B1: "weak_reduction_correspondence_simulation Rel Cal"
    show "\<forall>P Q Q'. (P, Q) \<in> Rel\<^sup>+ \<and> Q \<longmapsto>Cal* Q'
          \<longrightarrow> (\<exists>P'' Q''. P \<longmapsto>Cal* P'' \<and> Q' \<longmapsto>Cal* Q'' \<and> (P'', Q'') \<in> Rel\<^sup>+)"
    proof clarify
      fix P Q Q'
      assume "(P, Q) \<in> Rel\<^sup>+" and "Q \<longmapsto>Cal* Q'"
      thus "\<exists>P'' Q''. P \<longmapsto>Cal* P'' \<and> Q' \<longmapsto>Cal* Q'' \<and> (P'', Q'') \<in> Rel\<^sup>+"
      proof (induct arbitrary: Q')
        fix Q Q'
        assume "(P, Q) \<in> Rel" and "Q \<longmapsto>Cal* Q'"
        with B1 obtain P'' Q'' where B2: "P \<longmapsto>Cal* P''" and B3: "Q' \<longmapsto>Cal* Q''"
                                 and B4: "(P'', Q'') \<in> Rel"
          by blast
        from B4 have "(P'', Q'') \<in> Rel\<^sup>+"
          by simp
        with B2 B3 show "\<exists>P'' Q''. P \<longmapsto>Cal* P'' \<and> Q' \<longmapsto>Cal* Q'' \<and> (P'', Q'') \<in> Rel\<^sup>+"
          by blast
      next
        case (step Q R R')
        assume "\<And>Q'. Q \<longmapsto>Cal* Q'
                \<Longrightarrow> \<exists>P'' Q''. P \<longmapsto>Cal* P'' \<and> Q' \<longmapsto>Cal* Q'' \<and> (P'', Q'') \<in> Rel\<^sup>+"
        moreover assume "(Q, R) \<in> Rel"
        with B1
        have "\<And>R'. R \<longmapsto>Cal* R' \<Longrightarrow> \<exists>Q'' R''. Q \<longmapsto>Cal* Q'' \<and> R' \<longmapsto>Cal* R'' \<and> (Q'', R'') \<in> Rel\<^sup>+"
          by blast
        moreover from B1 have "weak_reduction_simulation (Rel\<^sup>+) Cal"
          using weak_reduction_simulation_and_closures(2)[where Rel="Rel" and Cal="Cal"]
          by blast
        moreover have "trans (Rel\<^sup>+)"
          using trans_trancl[of Rel]
          by blast
        moreover assume "R \<longmapsto>Cal* R'"
        ultimately show "\<exists>P'' R''. P \<longmapsto>Cal* P'' \<and> R' \<longmapsto>Cal* R'' \<and> (P'', R'') \<in> Rel\<^sup>+"
          using reduction_correspondence_simulation_condition_trans[where Rel="Rel\<^sup>+"]
          by blast
      qed
    qed
  qed
  from corrSim B[where Rel="Rel"] show "weak_reduction_correspondence_simulation (Rel\<^sup>+) Cal"
    by blast
  from A B[where Rel="Rel\<^sup>="]
  show "weak_reduction_correspondence_simulation (Rel\<^sup>*) Cal"
    using trancl_reflcl[of Rel]
    by auto
qed

lemma weak_barbed_correspondence_simulation_and_closures:
  fixes Rel :: "('proc \<times> 'proc) set"
    and CWB :: "('proc, 'barbs) calculusWithBarbs"
  assumes corrSim: "weak_barbed_correspondence_simulation Rel CWB"
  shows "weak_barbed_correspondence_simulation (Rel\<^sup>=) CWB"
    and "weak_barbed_correspondence_simulation (Rel\<^sup>+) CWB"
    and "weak_barbed_correspondence_simulation (Rel\<^sup>*) CWB"
proof -
  from corrSim show "weak_barbed_correspondence_simulation (Rel\<^sup>=) CWB"
    using weak_reduction_correspondence_simulation_and_closures(1)[where Rel="Rel"
            and Cal="Calculus CWB"]
          weak_respection_of_barbs_and_closures(1)[where Rel="Rel" and CWB="CWB"]
    by fast
next
  from corrSim show "weak_barbed_correspondence_simulation (Rel\<^sup>+) CWB"
    using weak_reduction_correspondence_simulation_and_closures(2)[where Rel="Rel"
            and Cal="Calculus CWB"]
          weak_respection_of_barbs_and_closures(3)[where Rel="Rel" and CWB="CWB"]
    by blast
next
  from corrSim show "weak_barbed_correspondence_simulation (Rel\<^sup>*) CWB"
    using weak_reduction_correspondence_simulation_and_closures(3)[where Rel="Rel"
            and Cal="Calculus CWB"]
          weak_respection_of_barbs_and_closures(5)[where Rel="Rel" and CWB="CWB"]
    by blast
qed

lemma labelled_correspondence_simulation_condition_trans:
  fixes Cal   :: "('proc, 'lab) labelledProcessCalculus"
    and P Q R :: "'proc"
    and \<alpha>     :: "'lab"
    and Rel   :: "('proc \<times> 'proc) set"
  assumes A1: "\<forall>Q'. Q \<midarrow>\<Zcat>\<alpha>\<rightarrow>Cal* Q' \<longrightarrow>
               (\<exists>P'' Q''. P \<midarrow>\<Zcat>\<alpha>\<rightarrow>Cal* P'' \<and> Q' \<rightarrow>Cal* Q'' \<and> (P'', Q'') \<in> Rel)"
      and A2: "\<forall>R'. R \<midarrow>\<Zcat>\<alpha>\<rightarrow>Cal* R' \<longrightarrow>
               (\<exists>Q'' R''. Q \<midarrow>\<Zcat>\<alpha>\<rightarrow>Cal* Q'' \<and> R' \<rightarrow>Cal* R'' \<and> (Q'', R'') \<in> Rel)"
      and A3: "weak_labelled_simulation Rel Cal"
      and A4: "trans Rel"
  shows "\<forall>R'. R \<midarrow>\<Zcat>\<alpha>\<rightarrow>Cal* R' \<longrightarrow> (\<exists>P'' R''. P \<midarrow>\<Zcat>\<alpha>\<rightarrow>Cal* P'' \<and> R' \<rightarrow>Cal* R'' \<and> (P'', R'') \<in> Rel)"
proof clarify
  fix R'
  assume "R \<midarrow>\<Zcat>\<alpha>\<rightarrow>Cal* R'"
  with A2 obtain Q'' R'' where A5: "Q \<midarrow>\<Zcat>\<alpha>\<rightarrow>Cal* Q''" and A6: "R' \<rightarrow>Cal* R''"
                           and A7: "(Q'', R'') \<in> Rel"
    by blast
  from A1 A5 obtain P''' Q''' where A8: "P \<midarrow>\<Zcat>\<alpha>\<rightarrow>Cal* P'''" and A9: "Q'' \<rightarrow>Cal* Q'''"
                                and A10: "(P''', Q''') \<in> Rel"
    by blast
  from A9 have "Q'' \<midarrow>\<Zcat>\<tau>-Cal\<rightarrow>Cal* Q'''"
    unfolding weakLabelledStep_def
    by simp
  with A3 A7 obtain R''' where A11: "R'' \<midarrow>\<Zcat>\<tau>-Cal\<rightarrow>Cal* R'''" and A12: "(Q''', R''') \<in> Rel"
    by blast
  from A6 A11 have A13: "R' \<rightarrow>Cal* R'''"
    unfolding weakLabelledStep_def
    using weakTauSteps_trans[of R' Cal R'' R''']
    by simp
  from A4 A10 A12 have "(P''', R''') \<in> Rel"
    unfolding trans_def
    by blast
  with A8 A13 show "\<exists>P'' R''. P \<midarrow>\<Zcat>\<alpha>\<rightarrow>Cal* P'' \<and> R' \<rightarrow>Cal* R'' \<and> (P'', R'') \<in> Rel"
    by blast
qed

lemma weak_labelled_correspondence_simulation_and_closures:
  fixes Rel :: "('proc \<times> 'proc) set"
    and Cal :: "('proc, 'lab) labelledProcessCalculus"
  assumes corrSim: "weak_labelled_correspondence_simulation Rel Cal"
  shows "weak_labelled_correspondence_simulation (Rel\<^sup>=) Cal"
    and "weak_labelled_correspondence_simulation (Rel\<^sup>+) Cal"
    and "weak_labelled_correspondence_simulation (Rel\<^sup>*) Cal"
proof -
  show A: "weak_labelled_correspondence_simulation (Rel\<^sup>=) Cal"
  proof
    from corrSim show "weak_labelled_simulation (Rel\<^sup>=) Cal"
      using weak_labelled_simulation_and_closures(1)[where Rel="Rel" and Cal="Cal"]
      by blast
  next
    show "\<forall>P Q \<alpha> Q'. (P, Q) \<in> Rel\<^sup>= \<and> Q \<midarrow>\<Zcat>\<alpha>\<rightarrow>Cal* Q'
          \<longrightarrow> (\<exists>P'' Q''. P \<midarrow>\<Zcat>\<alpha>\<rightarrow>Cal* P'' \<and> Q' \<rightarrow>Cal* Q'' \<and> (P'', Q'') \<in> Rel\<^sup>=)"
    proof clarify
      fix P Q \<alpha> Q'
      assume "(P, Q) \<in> Rel\<^sup>=" and A1: "Q \<midarrow>\<Zcat>\<alpha>\<rightarrow>Cal* Q'"
      moreover have "P = Q \<Longrightarrow> \<exists>P'' Q''. P \<midarrow>\<Zcat>\<alpha>\<rightarrow>Cal* P'' \<and> Q' \<rightarrow>Cal* Q'' \<and> (P'', Q'') \<in> Rel\<^sup>="
      proof -
        assume "P = Q"
        moreover have "Q' \<rightarrow>Cal* Q'"
          using WTS_refl[of Q' Cal]
          by simp
        ultimately show "\<exists>P'' Q''. P \<midarrow>\<Zcat>\<alpha>\<rightarrow>Cal* P'' \<and> Q' \<rightarrow>Cal* Q'' \<and> (P'', Q'') \<in> Rel\<^sup>="
          using A1
          by blast
      qed
      moreover
      have "(P, Q) \<in> Rel \<Longrightarrow> \<exists>P'' Q''. P \<midarrow>\<Zcat>\<alpha>\<rightarrow>Cal* P'' \<and> Q' \<rightarrow>Cal* Q'' \<and> (P'', Q'') \<in> Rel\<^sup>="
      proof -
        assume "(P, Q) \<in> Rel"
        with corrSim A1 obtain P'' Q'' where "P \<midarrow>\<Zcat>\<alpha>\<rightarrow>Cal* P''" and "Q' \<rightarrow>Cal* Q''"
                                         and "(P'', Q'') \<in> Rel"
          by blast
        thus "\<exists>P'' Q''. P \<midarrow>\<Zcat>\<alpha>\<rightarrow>Cal* P'' \<and> Q' \<rightarrow>Cal* Q'' \<and> (P'', Q'') \<in> Rel\<^sup>="
          by auto
      qed
      ultimately show "\<exists>P'' Q''. P \<midarrow>\<Zcat>\<alpha>\<rightarrow>Cal* P'' \<and> Q' \<rightarrow>Cal* Q'' \<and> (P'', Q'') \<in> Rel\<^sup>="
        by auto
    qed
  qed
  have B: "\<And>Rel. weak_labelled_correspondence_simulation Rel Cal
           \<Longrightarrow> weak_labelled_correspondence_simulation (Rel\<^sup>+) Cal"
  proof
    fix Rel
    assume "weak_labelled_correspondence_simulation Rel Cal"
    thus "weak_labelled_simulation (Rel\<^sup>+) Cal"
      using weak_labelled_simulation_and_closures(2)[where Rel="Rel" and Cal="Cal"]
      by blast
  next
    fix Rel
    assume B1: "weak_labelled_correspondence_simulation Rel Cal"
    show "\<forall>P Q \<alpha> Q'. (P, Q) \<in> Rel\<^sup>+ \<and> Q \<midarrow>\<Zcat>\<alpha>\<rightarrow>Cal* Q'
          \<longrightarrow> (\<exists>P'' Q''. P \<midarrow>\<Zcat>\<alpha>\<rightarrow>Cal* P'' \<and> Q' \<rightarrow>Cal* Q'' \<and> (P'', Q'') \<in> Rel\<^sup>+)"
    proof clarify
      fix P Q \<alpha> Q'
      assume "(P, Q) \<in> Rel\<^sup>+" and "Q \<midarrow>\<Zcat>\<alpha>\<rightarrow>Cal* Q'"
      thus "\<exists>P'' Q''. P \<midarrow>\<Zcat>\<alpha>\<rightarrow>Cal* P'' \<and> Q' \<rightarrow>Cal* Q'' \<and> (P'', Q'') \<in> Rel\<^sup>+"
      proof (induct arbitrary: Q')
        fix Q Q'
        assume "(P, Q) \<in> Rel" and "Q \<midarrow>\<Zcat>\<alpha>\<rightarrow>Cal* Q'"
        with B1 obtain P'' Q'' where B2: "P \<midarrow>\<Zcat>\<alpha>\<rightarrow>Cal* P''" and B3: "Q' \<rightarrow>Cal* Q''"
                                 and B4: "(P'', Q'') \<in> Rel"
          by blast
        from B4 have "(P'', Q'') \<in> Rel\<^sup>+"
          by simp
        with B2 B3 show "\<exists>P'' Q''. P \<midarrow>\<Zcat>\<alpha>\<rightarrow>Cal* P'' \<and> Q' \<rightarrow>Cal* Q'' \<and> (P'', Q'') \<in> Rel\<^sup>+"
          by blast
      next
        case (step Q R R')
        assume "\<And>Q'. Q \<midarrow>\<Zcat>\<alpha>\<rightarrow>Cal* Q'
                \<Longrightarrow> \<exists>P'' Q''. P \<midarrow>\<Zcat>\<alpha>\<rightarrow>Cal* P'' \<and> Q' \<rightarrow>Cal* Q'' \<and> (P'', Q'') \<in> Rel\<^sup>+"
        moreover assume "(Q, R) \<in> Rel"
        with B1 have "\<And>R'. R \<midarrow>\<Zcat>\<alpha>\<rightarrow>Cal* R' \<Longrightarrow>
                      \<exists>Q'' R''. Q \<midarrow>\<Zcat>\<alpha>\<rightarrow>Cal* Q'' \<and> R' \<rightarrow>Cal* R'' \<and> (Q'', R'') \<in> Rel\<^sup>+"
          by blast
        moreover from B1 have "weak_labelled_simulation (Rel\<^sup>+) Cal"
          using weak_labelled_simulation_and_closures(2)[where Rel="Rel" and Cal="Cal"]
          by blast
        moreover have "trans (Rel\<^sup>+)"
          using trans_trancl[of Rel]
          by blast
        moreover assume "R \<midarrow>\<Zcat>\<alpha>\<rightarrow>Cal* R'"
        ultimately show "\<exists>P'' R''. P \<midarrow>\<Zcat>\<alpha>\<rightarrow>Cal* P'' \<and> R' \<rightarrow>Cal* R'' \<and> (P'', R'') \<in> Rel\<^sup>+"
            using labelled_correspondence_simulation_condition_trans[of Q \<alpha> Cal P "Rel\<^sup>+" R]
          by blast
      qed
    qed
  qed
  from corrSim B[where Rel="Rel"] show "weak_labelled_correspondence_simulation (Rel\<^sup>+) Cal"
    by blast
  from A B[where Rel="Rel\<^sup>="]
  show "weak_labelled_correspondence_simulation (Rel\<^sup>*) Cal"
      using trancl_reflcl[of Rel]
    by auto
qed

subsection \<open>Bisimulation\<close>

text \<open>A weak (reduction) bisimulation is a relation R such that
      (1) if (P, Q) in R and P evolves to some P' then there exists some Q' such that Q evolves to
          Q' and (P', Q') in R, and
      (2) if (P, Q) in R and Q evolves to some Q' then there exists some P' such that P evolves to
          P' and (P', Q') in R.\<close>

abbreviation weak_reduction_bisimulation :: "('proc \<times> 'proc) set \<Rightarrow> 'proc processCalculus \<Rightarrow> bool"
  where
  "weak_reduction_bisimulation Rel Cal \<equiv>
   (\<forall>P Q P'. (P, Q) \<in> Rel \<and> P \<longmapsto>Cal* P' \<longrightarrow> (\<exists>Q'. Q \<longmapsto>Cal* Q' \<and> (P', Q') \<in> Rel))
   \<and> (\<forall>P Q Q'. (P, Q) \<in> Rel \<and> Q \<longmapsto>Cal* Q' \<longrightarrow> (\<exists>P'. P \<longmapsto>Cal* P' \<and> (P', Q') \<in> Rel))"

text \<open>A weak barbed bisimulation is weak reduction bisimulation that weakly respects barbs.\<close>

abbreviation weak_barbed_bisimulation
  :: "('proc \<times> 'proc) set \<Rightarrow> ('proc, 'barbs) calculusWithBarbs \<Rightarrow> bool" where
  "weak_barbed_bisimulation Rel CWB \<equiv>
   weak_reduction_bisimulation Rel (Calculus CWB) \<and> rel_weakly_respects_barbs Rel CWB"

text \<open>A weak labelled bisimulation is a relation R such that
      (1) if (P, Q) in R and P evolves to some P' using a then there exists some Q' such that Q
          evolves to Q' using a and (P', Q') in R, and
      (2) if (P, Q) in R and Q evolves to some Q' using a then there exists some P' such that P
          evolves to P' using a and (P', Q') in R.\<close>

abbreviation weak_labelled_bisimulation
  :: "('proc \<times> 'proc) set \<Rightarrow> ('proc, 'lab) labelledProcessCalculus \<Rightarrow> bool" where
  "weak_labelled_bisimulation Rel Cal \<equiv>
   (\<forall>P Q \<alpha> P'. (P, Q) \<in> Rel \<and> P \<midarrow>\<Zcat>\<alpha>\<rightarrow>Cal* P' \<longrightarrow> (\<exists>Q'. Q \<midarrow>\<Zcat>\<alpha>\<rightarrow>Cal* Q' \<and> (P', Q') \<in> Rel))
   \<and> (\<forall>P Q \<alpha> Q'. (P, Q) \<in> Rel \<and> Q \<midarrow>\<Zcat>\<alpha>\<rightarrow>Cal* Q' \<longrightarrow> (\<exists>P'. P \<midarrow>\<Zcat>\<alpha>\<rightarrow>Cal* P' \<and> (P', Q') \<in> Rel))"

text \<open>A symetric weak simulation is a weak bisimulation.\<close>

lemma symm_weak_reduction_simulation_is_bisimulation:
  fixes Rel :: "('proc \<times> 'proc) set"
    and Cal :: "'proc processCalculus"
  assumes "sym Rel"
      and "weak_reduction_simulation Rel Cal"
  shows "weak_reduction_bisimulation Rel Cal"
  using assms symD[of Rel]
  by blast

lemma symm_weak_barbed_simulation_is_bisimulation:
  fixes Rel :: "('proc \<times> 'proc) set"
    and CWB :: "('proc, 'barbs) calculusWithBarbs"
  assumes "sym Rel"
      and "weak_barbed_simulation Rel Cal"
    shows "weak_barbed_bisimulation Rel Cal"
  using assms symD[of Rel]
  by blast

lemma symm_weak_labelled_simulation_is_bisimulation:
  fixes Rel :: "('proc \<times> 'proc) set"
    and Cal :: "('proc, 'lab) labelledProcessCalculus"
  assumes "sym Rel"
      and "weak_labelled_simulation Rel Cal"
    shows "weak_labelled_bisimulation Rel Cal"
  using assms symD[of Rel]
  by blast

text \<open>If a relation as well as its inverse are weak simulations, then this relation is a weak
      bisimulation.\<close>

lemma weak_reduction_simulations_impl_bisimulation:
  fixes Rel :: "('proc \<times> 'proc) set"
    and Cal :: "'proc processCalculus"
  assumes sim:    "weak_reduction_simulation Rel Cal"
      and simInv: "weak_reduction_simulation (Rel\<inverse>) Cal"
    shows "weak_reduction_bisimulation Rel Cal"
proof auto
  fix P Q P'
  assume "(P, Q) \<in> Rel" and "P \<longmapsto>Cal* P'"
  with sim show "\<exists>Q'. Q \<longmapsto>Cal* Q' \<and> (P', Q') \<in> Rel"
    by simp
next
  fix P Q Q'
  assume "(P, Q) \<in> Rel"
  hence "(Q, P) \<in> Rel\<inverse>"
    by simp
  moreover assume "Q \<longmapsto>Cal* Q'"
  ultimately obtain P' where A1: "P \<longmapsto>Cal* P'" and A2: "(Q', P') \<in> Rel\<inverse>"
    using simInv
    by blast
  from A2 have "(P', Q') \<in> Rel"
    by induct
  with A1 show "\<exists>P'. P \<longmapsto>Cal* P' \<and> (P', Q') \<in> Rel"
    by blast
qed

lemma weak_labelled_simulations_impl_bisimulation:
  fixes Rel :: "('proc \<times> 'proc) set"
    and Cal :: "('proc, 'lab) labelledProcessCalculus"
  assumes sim:    "weak_labelled_simulation Rel Cal"
      and simInv: "weak_labelled_simulation (Rel\<inverse>) Cal"
    shows "weak_labelled_bisimulation Rel Cal"
proof auto
  fix P Q \<alpha> P'
  assume "(P, Q) \<in> Rel" and "P \<midarrow>\<Zcat>\<alpha>\<rightarrow>Cal* P'"
  with sim show "\<exists>Q'. Q \<midarrow>\<Zcat>\<alpha>\<rightarrow>Cal* Q' \<and> (P', Q') \<in> Rel"
    by simp
next
  fix P Q \<alpha> Q'
  assume "(P, Q) \<in> Rel"
  hence "(Q, P) \<in> Rel\<inverse>"
    by simp
  moreover assume "Q \<midarrow>\<Zcat>\<alpha>\<rightarrow>Cal* Q'"
  ultimately obtain P' where A1: "P \<midarrow>\<Zcat>\<alpha>\<rightarrow>Cal* P'" and A2: "(Q', P') \<in> Rel\<inverse>"
    using simInv
    by blast
  from A2 have "(P', Q') \<in> Rel"
    by induct
  with A1 show "\<exists>P'. P \<midarrow>\<Zcat>\<alpha>\<rightarrow>Cal* P' \<and> (P', Q') \<in> Rel"
    by blast
qed

lemma weak_reduction_bisimulations_impl_inverse_is_simulation:
  fixes Rel :: "('proc \<times> 'proc) set"
    and Cal :: "'proc processCalculus"
  assumes bisim: "weak_reduction_bisimulation Rel Cal"
  shows "weak_reduction_simulation (Rel\<inverse>) Cal"
proof clarify
  fix P Q P'
  assume "(Q, P) \<in> Rel"
  moreover assume "P \<longmapsto>Cal* P'"
  ultimately obtain Q' where A1: "Q \<longmapsto>Cal* Q'" and A2: "(Q', P') \<in> Rel"
    using bisim
    by blast
  from A2 have "(P', Q') \<in> Rel\<inverse>"
    by simp
  with A1 show "\<exists>Q'. Q \<longmapsto>Cal* Q' \<and> (P', Q') \<in> Rel\<inverse>"
    by blast
qed

lemma weak_labelled_bisimulations_impl_inverse_is_simulation:
  fixes Rel :: "('proc \<times> 'proc) set"
    and Cal :: "('proc, 'lab) labelledProcessCalculus"
  assumes bisim: "weak_labelled_bisimulation Rel Cal"
  shows "weak_labelled_simulation (Rel\<inverse>) Cal"
proof clarify
  fix P Q \<alpha> P'
  assume "(Q, P) \<in> Rel"
  moreover assume "P \<midarrow>\<Zcat>\<alpha>\<rightarrow>Cal* P'"
  ultimately obtain Q' where A1: "Q \<midarrow>\<Zcat>\<alpha>\<rightarrow>Cal* Q'" and A2: "(Q', P') \<in> Rel"
    using bisim
    by blast
  from A2 have "(P', Q') \<in> Rel\<inverse>"
    by simp
  with A1 show "\<exists>Q'. Q \<midarrow>\<Zcat>\<alpha>\<rightarrow>Cal* Q' \<and> (P', Q') \<in> Rel\<inverse>"
    by blast
qed

lemma weak_reduction_simulations_iff_bisimulation:
  fixes Rel :: "('proc \<times> 'proc) set"
    and Cal :: "'proc processCalculus"
  shows "(weak_reduction_simulation Rel Cal \<and> weak_reduction_simulation (Rel\<inverse>) Cal)
         = weak_reduction_bisimulation Rel Cal"
  using weak_reduction_simulations_impl_bisimulation[where Rel="Rel" and Cal="Cal"]
        weak_reduction_bisimulations_impl_inverse_is_simulation[where Rel="Rel" and Cal="Cal"]
  by blast

lemma weak_barbed_simulations_iff_bisimulation:
  fixes Rel :: "('proc \<times> 'proc) set"
    and CWB :: "('proc, 'barbs) calculusWithBarbs"
  shows "(weak_barbed_simulation Rel CWB \<and> weak_barbed_simulation (Rel\<inverse>) CWB)
         = weak_barbed_bisimulation Rel CWB"
proof (rule iffI, erule conjE)
  assume sim: "weak_barbed_simulation Rel CWB"
     and rev: "weak_barbed_simulation (Rel\<inverse>) CWB"
  hence "weak_reduction_bisimulation Rel (Calculus CWB)"
    using weak_reduction_simulations_impl_bisimulation[where Rel="Rel" and Cal="Calculus CWB"]
    by blast
  moreover from sim have "rel_weakly_preserves_barbs Rel CWB"
    by simp
  moreover from rev have "rel_weakly_reflects_barbs Rel CWB"
    by simp
  ultimately show "weak_barbed_bisimulation Rel CWB"
    by blast
next
  assume bisim: "weak_barbed_bisimulation Rel CWB"
  hence "weak_barbed_simulation Rel CWB"
    by blast
  moreover from bisim have "weak_reduction_simulation (Rel\<inverse>) (Calculus CWB)"
    using weak_reduction_bisimulations_impl_inverse_is_simulation[where Rel="Rel"]
    by simp
  moreover from bisim have "rel_weakly_reflects_barbs Rel CWB"
    by blast
  hence "rel_weakly_preserves_barbs (Rel\<inverse>) CWB"
    by simp
  ultimately show "weak_barbed_simulation Rel CWB \<and> weak_barbed_simulation (Rel\<inverse>) CWB"
    by blast
qed

lemma weak_labelled_simulations_iff_bisimulation:
  fixes Rel :: "('proc \<times> 'proc) set"
    and Cal :: "('proc, 'lab) labelledProcessCalculus"
  shows "(weak_labelled_simulation Rel Cal \<and> weak_labelled_simulation (Rel\<inverse>) Cal)
         = weak_labelled_bisimulation Rel Cal"
  using weak_labelled_simulations_impl_bisimulation[where Rel="Rel" and Cal="Cal"]
        weak_labelled_bisimulations_impl_inverse_is_simulation[where Rel="Rel" and Cal="Cal"]
  by blast

text \<open>A weak bisimulation is a weak correspondence simulation.\<close>

lemma weak_reduction_bisimulation_is_correspondence_simulation:
  fixes Rel :: "('proc \<times> 'proc) set"
    and Cal :: "'proc processCalculus"
  assumes bisim: "weak_reduction_bisimulation Rel Cal"
  shows "weak_reduction_correspondence_simulation Rel Cal"
proof
  from bisim show "weak_reduction_simulation Rel Cal"
    by blast
next
  show "\<forall>P Q Q'. (P, Q) \<in> Rel \<and> Q \<longmapsto>Cal* Q'
        \<longrightarrow> (\<exists>P'' Q''. P \<longmapsto>Cal* P'' \<and> Q' \<longmapsto>Cal* Q'' \<and> (P'', Q'') \<in> Rel)"
  proof clarify
    fix P Q Q'
    assume "(P, Q) \<in> Rel" and "Q \<longmapsto>Cal* Q'"
    with bisim obtain P' where "P \<longmapsto>Cal* P'" and "(P', Q') \<in> Rel"
      by blast
    moreover have "Q' \<longmapsto>Cal* Q'"
      by (rule steps_refl)
    ultimately show "(\<exists>P'' Q''. P \<longmapsto>Cal* P'' \<and> Q' \<longmapsto>Cal* Q'' \<and> (P'', Q'') \<in> Rel)"
      by blast
  qed
qed

lemma weak_barbed_bisimulation_is_correspondence_simulation:
  fixes Rel :: "('proc \<times> 'proc) set"
    and CWB :: "('proc, 'barbs) calculusWithBarbs"
  assumes bisim: "weak_barbed_bisimulation Rel CWB"
  shows "weak_barbed_correspondence_simulation Rel CWB"
  using bisim weak_reduction_bisimulation_is_correspondence_simulation[where Rel="Rel"
              and Cal="Calculus CWB"]
  by blast

lemma weak_labelled_bisimulation_is_correspondence_simulation:
  fixes Rel :: "('proc \<times> 'proc) set"
    and Cal :: "('proc, 'lab) labelledProcessCalculus"
  assumes bisim: "weak_labelled_bisimulation Rel Cal"
  shows "weak_labelled_correspondence_simulation Rel Cal"
proof
  from bisim show "weak_labelled_simulation Rel Cal"
    by blast
next
  show "\<forall>P Q \<alpha> Q'. (P, Q) \<in> Rel \<and> Q \<midarrow>\<Zcat>\<alpha>\<rightarrow>Cal* Q'
        \<longrightarrow> (\<exists>P'' Q''. P \<midarrow>\<Zcat>\<alpha>\<rightarrow>Cal* P'' \<and> Q' \<rightarrow>Cal* Q'' \<and> (P'', Q'') \<in> Rel)"
  proof clarify
    fix P Q \<alpha> Q'
    assume "(P, Q) \<in> Rel" and "Q \<midarrow>\<Zcat>\<alpha>\<rightarrow>Cal* Q'"
    with bisim obtain P' where "P \<midarrow>\<Zcat>\<alpha>\<rightarrow>Cal* P'" and "(P', Q') \<in> Rel"
      by blast
    moreover have "Q' \<rightarrow>Cal* Q'"
      using WTS_refl[of Q' Cal]
      by simp
    ultimately show "(\<exists>P'' Q''. P \<midarrow>\<Zcat>\<alpha>\<rightarrow>Cal* P'' \<and> Q' \<rightarrow>Cal* Q'' \<and> (P'', Q'') \<in> Rel)"
      by blast
  qed
qed

text \<open>The reflexive, symmetric, and/or transitive closure of a weak bisimulation is a weak
      bisimulation.\<close>

lemma weak_reduction_bisimulation_and_closures:
  fixes Rel :: "('proc \<times> 'proc) set"
    and Cal :: "'proc processCalculus"
  assumes bisim: "weak_reduction_bisimulation Rel Cal"
  shows "weak_reduction_bisimulation (Rel\<^sup>=) Cal"
    and "weak_reduction_bisimulation (symcl Rel) Cal"
    and "weak_reduction_bisimulation (Rel\<^sup>+) Cal"
    and "weak_reduction_bisimulation (symcl (Rel\<^sup>=)) Cal"
    and "weak_reduction_bisimulation (Rel\<^sup>*) Cal"
    and "weak_reduction_bisimulation ((symcl (Rel\<^sup>=))\<^sup>+) Cal"
proof -
  from bisim show A: "weak_reduction_bisimulation (Rel\<^sup>=) Cal"
    by (auto simp add: refl, blast+)
  have B: "\<And>Rel. weak_reduction_bisimulation Rel Cal
           \<Longrightarrow> weak_reduction_bisimulation (symcl Rel) Cal"
    by (auto simp add: symcl_def, blast+)
  from bisim B[where Rel="Rel"] show "weak_reduction_bisimulation (symcl Rel) Cal"
    by blast
  have C: "\<And>Rel. weak_reduction_bisimulation Rel Cal
           \<Longrightarrow> weak_reduction_bisimulation (Rel\<^sup>+) Cal"
  proof
    fix Rel
    assume "weak_reduction_bisimulation Rel Cal"
    thus "weak_reduction_simulation (Rel\<^sup>+) Cal"
      using weak_reduction_simulation_and_closures(2)[where Rel="Rel" and Cal="Cal"]
      by blast
  next
    fix Rel
    assume C1: "weak_reduction_bisimulation Rel Cal"
    show "\<forall>P Q Q'. (P, Q) \<in> Rel\<^sup>+ \<and> Q \<longmapsto>Cal* Q'
          \<longrightarrow> (\<exists>P'. P \<longmapsto>Cal* P' \<and> (P', Q') \<in> Rel\<^sup>+)"
    proof clarify
      fix P Q Q'
      assume "(P, Q) \<in> Rel\<^sup>+" and "Q \<longmapsto>Cal* Q'"
      thus "\<exists>P'. P \<longmapsto>Cal* P' \<and> (P', Q') \<in> Rel\<^sup>+"
      proof (induct arbitrary: Q')
        fix Q Q'
        assume "(P, Q) \<in> Rel" and "Q \<longmapsto>Cal* Q'"
        with C1 obtain P' where "P \<longmapsto>Cal* P'" and "(P', Q') \<in> Rel"
          by blast
        thus "\<exists>P'. P \<longmapsto>Cal* P' \<and> (P', Q') \<in> Rel\<^sup>+"
          by auto
      next
        case (step Q R R')
        assume "(Q, R) \<in> Rel" and "R \<longmapsto>Cal* R'"
        with C1 obtain Q' where C2: "Q \<longmapsto>Cal* Q'" and C3: "(Q', R') \<in> Rel\<^sup>+"
          by blast
        assume "\<And>Q'. Q \<longmapsto>Cal* Q' \<Longrightarrow> \<exists>P'. P \<longmapsto>Cal* P' \<and> (P', Q') \<in> Rel\<^sup>+"
        with C2 obtain P' where C4: "P \<longmapsto>Cal* P'" and C5: "(P', Q') \<in> Rel\<^sup>+"
          by blast
        from C5 C3 have "(P', R') \<in> Rel\<^sup>+"
          by simp
        with C4 show "\<exists>P'. P \<longmapsto>Cal* P' \<and> (P', R') \<in> Rel\<^sup>+"
          by blast
      qed
    qed
  qed
  from bisim C[where Rel="Rel"] show "weak_reduction_bisimulation (Rel\<^sup>+) Cal"
    by blast
  from A B[where Rel="Rel\<^sup>="] show "weak_reduction_bisimulation (symcl (Rel\<^sup>=)) Cal"
    by blast
  from A C[where Rel="Rel\<^sup>="] show "weak_reduction_bisimulation (Rel\<^sup>*) Cal"
    using trancl_reflcl[of Rel]
    by auto
  from A B[where Rel="Rel\<^sup>="] C[where Rel="symcl (Rel\<^sup>=)"]
  show "weak_reduction_bisimulation ((symcl (Rel\<^sup>=))\<^sup>+) Cal"
    by blast
qed

lemma weak_barbed_bisimulation_and_closures:
  fixes Rel :: "('proc \<times> 'proc) set"
    and CWB :: "('proc, 'barbs) calculusWithBarbs"
  assumes bisim: "weak_barbed_bisimulation Rel CWB"
  shows "weak_barbed_bisimulation (Rel\<^sup>=) CWB"
    and "weak_barbed_bisimulation (symcl Rel) CWB"
    and "weak_barbed_bisimulation (Rel\<^sup>+) CWB"
    and "weak_barbed_bisimulation (symcl (Rel\<^sup>=)) CWB"
    and "weak_barbed_bisimulation (Rel\<^sup>*) CWB"
    and "weak_barbed_bisimulation ((symcl (Rel\<^sup>=))\<^sup>+) CWB"
proof -
  from bisim show "weak_barbed_bisimulation (Rel\<^sup>=) CWB"
    using weak_reduction_bisimulation_and_closures(1)[where Rel="Rel" and Cal="Calculus CWB"]
          weak_respection_of_barbs_and_closures(1)[where Rel="Rel" and CWB="CWB"]
    by fast
next
  from bisim show "weak_barbed_bisimulation (symcl Rel) CWB"
    using weak_reduction_bisimulation_and_closures(2)[where Rel="Rel" and Cal="Calculus CWB"]
          weak_respection_of_barbs_and_closures(2)[where Rel="Rel" and CWB="CWB"]
    by blast
next
  from bisim show "weak_barbed_bisimulation (Rel\<^sup>+) CWB"
    using weak_reduction_bisimulation_and_closures(3)[where Rel="Rel" and Cal="Calculus CWB"]
          weak_respection_of_barbs_and_closures(3)[where Rel="Rel" and CWB="CWB"]
    by blast
next
  from bisim show "weak_barbed_bisimulation (symcl (Rel\<^sup>=)) CWB"
    using weak_reduction_bisimulation_and_closures(4)[where Rel="Rel" and Cal="Calculus CWB"]
          weak_respection_of_barbs_and_closures(4)[where Rel="Rel" and CWB="CWB"]
    by blast
next
  from bisim show "weak_barbed_bisimulation (Rel\<^sup>*) CWB"
    using weak_reduction_bisimulation_and_closures(5)[where Rel="Rel" and Cal="Calculus CWB"]
          weak_respection_of_barbs_and_closures(5)[where Rel="Rel" and CWB="CWB"]
    by blast
next
  from bisim show "weak_barbed_bisimulation ((symcl (Rel\<^sup>=))\<^sup>+) CWB"
    using weak_reduction_bisimulation_and_closures(6)[where Rel="Rel" and Cal="Calculus CWB"]
          weak_respection_of_barbs_and_closures(6)[where Rel="Rel" and CWB="CWB"]
    by blast
qed

lemma weak_labelled_bisimulation_and_closures:
  fixes Rel :: "('proc \<times> 'proc) set"
    and Cal :: "('proc, 'lab) labelledProcessCalculus"
  assumes bisim: "weak_labelled_bisimulation Rel Cal"
  shows "weak_labelled_bisimulation (Rel\<^sup>=) Cal"
    and "weak_labelled_bisimulation (symcl Rel) Cal"
    and "weak_labelled_bisimulation (Rel\<^sup>+) Cal"
    and "weak_labelled_bisimulation (symcl (Rel\<^sup>=)) Cal"
    and "weak_labelled_bisimulation (Rel\<^sup>*) Cal"
    and "weak_labelled_bisimulation ((symcl (Rel\<^sup>=))\<^sup>+) Cal"
proof -
  from bisim show A: "weak_labelled_bisimulation (Rel\<^sup>=) Cal"
    by (auto simp add: refl, blast+)
  have B: "\<And>Rel. weak_labelled_bisimulation Rel Cal
           \<Longrightarrow> weak_labelled_bisimulation (symcl Rel) Cal"
    by (auto simp add: symcl_def, blast+)
  from bisim B[where Rel="Rel"] show "weak_labelled_bisimulation (symcl Rel) Cal"
    by blast
  have C: "\<And>Rel. weak_labelled_bisimulation Rel Cal
           \<Longrightarrow> weak_labelled_bisimulation (Rel\<^sup>+) Cal"
  proof
    fix Rel
    assume "weak_labelled_bisimulation Rel Cal"
    thus "weak_labelled_simulation (Rel\<^sup>+) Cal"
      using weak_labelled_simulation_and_closures(2)[where Rel="Rel" and Cal="Cal"]
      by blast
  next
    fix Rel
    assume C1: "weak_labelled_bisimulation Rel Cal"
    show "\<forall>P Q \<alpha> Q'. (P, Q) \<in> Rel\<^sup>+ \<and> Q \<midarrow>\<Zcat>\<alpha>\<rightarrow>Cal* Q'
          \<longrightarrow> (\<exists>P'. P \<midarrow>\<Zcat>\<alpha>\<rightarrow>Cal* P' \<and> (P', Q') \<in> Rel\<^sup>+)"
    proof clarify
      fix P Q \<alpha> Q'
      assume "(P, Q) \<in> Rel\<^sup>+" and "Q \<midarrow>\<Zcat>\<alpha>\<rightarrow>Cal* Q'"
      thus "\<exists>P'. P \<midarrow>\<Zcat>\<alpha>\<rightarrow>Cal* P' \<and> (P', Q') \<in> Rel\<^sup>+"
      proof (induct arbitrary: Q')
        fix Q Q'
        assume "(P, Q) \<in> Rel" and "Q \<midarrow>\<Zcat>\<alpha>\<rightarrow>Cal* Q'"
        with C1 obtain P' where "P \<midarrow>\<Zcat>\<alpha>\<rightarrow>Cal* P'" and "(P', Q') \<in> Rel"
          by blast
        thus "\<exists>P'. P \<midarrow>\<Zcat>\<alpha>\<rightarrow>Cal* P' \<and> (P', Q') \<in> Rel\<^sup>+"
          by auto
      next
        case (step Q R R')
        assume "(Q, R) \<in> Rel" and "R \<midarrow>\<Zcat>\<alpha>\<rightarrow>Cal* R'"
        with C1 obtain Q' where C2: "Q \<midarrow>\<Zcat>\<alpha>\<rightarrow>Cal* Q'" and C3: "(Q', R') \<in> Rel\<^sup>+"
          by blast
        assume "\<And>Q'. Q \<midarrow>\<Zcat>\<alpha>\<rightarrow>Cal* Q' \<Longrightarrow> \<exists>P'. P \<midarrow>\<Zcat>\<alpha>\<rightarrow>Cal* P' \<and> (P', Q') \<in> Rel\<^sup>+"
        with C2 obtain P' where C4: "P \<midarrow>\<Zcat>\<alpha>\<rightarrow>Cal* P'" and C5: "(P', Q') \<in> Rel\<^sup>+"
          by blast
        from C5 C3 have "(P', R') \<in> Rel\<^sup>+"
          by simp
        with C4 show "\<exists>P'. P \<midarrow>\<Zcat>\<alpha>\<rightarrow>Cal* P' \<and> (P', R') \<in> Rel\<^sup>+"
          by blast
      qed
    qed
  qed
  from bisim C[where Rel="Rel"] show "weak_labelled_bisimulation (Rel\<^sup>+) Cal"
    by blast
  from A B[where Rel="Rel\<^sup>="] show "weak_labelled_bisimulation (symcl (Rel\<^sup>=)) Cal"
    by blast
  from A C[where Rel="Rel\<^sup>="] show "weak_labelled_bisimulation (Rel\<^sup>*) Cal"
    using trancl_reflcl[of Rel]
    by auto
  from A B[where Rel="Rel\<^sup>="] C[where Rel="symcl (Rel\<^sup>=)"]
  show "weak_labelled_bisimulation ((symcl (Rel\<^sup>=))\<^sup>+) Cal"
    by blast
qed

text \<open>A strong (reduction) bisimulation is a relation R such that
      (1) if (P, Q) in R and P' is a derivative of P then there exists some Q' such that Q' is a
          derivative of Q and (P', Q') in R, and
      (2) if (P, Q) in R and Q' is a derivative of Q then there exists some P' such that P' is a
          derivative of P and (P', Q') in R.\<close>

abbreviation strong_reduction_bisimulation
  :: "('proc \<times> 'proc) set \<Rightarrow> 'proc processCalculus \<Rightarrow> bool" where
  "strong_reduction_bisimulation Rel Cal \<equiv>
   (\<forall>P Q P'. (P, Q) \<in> Rel \<and> P \<longmapsto>Cal P' \<longrightarrow> (\<exists>Q'. Q \<longmapsto>Cal Q' \<and> (P', Q') \<in> Rel))
   \<and> (\<forall>P Q Q'. (P, Q) \<in> Rel \<and> Q \<longmapsto>Cal Q' \<longrightarrow> (\<exists>P'. P \<longmapsto>Cal P' \<and> (P', Q') \<in> Rel))"

text \<open>A strong barbed bisimulation is strong reduction bisimulation that respects barbs.\<close>

abbreviation strong_barbed_bisimulation
  :: "('proc \<times> 'proc) set \<Rightarrow> ('proc, 'barbs) calculusWithBarbs \<Rightarrow> bool" where
  "strong_barbed_bisimulation Rel CWB \<equiv>
   strong_reduction_bisimulation Rel (Calculus CWB) \<and> rel_respects_barbs Rel CWB"

text \<open>A strong labelled bisimulation is a relation R such that
      (1) if (P, Q) in R and P' is a derivative of P using a then there exists some Q' such that
          Q' is a derivative of Q using a and (P', Q') in R, and
      (2) if (P, Q) in R and Q' is a derivative of Q using a then there exists some P' such that
          P' is a derivative of P using a and (P', Q') in R.\<close>

abbreviation strong_labelled_bisimulation
  :: "('proc \<times> 'proc) set \<Rightarrow> ('proc, 'lab) labelledProcessCalculus \<Rightarrow> bool" where
  "strong_labelled_bisimulation Rel Cal \<equiv>
   (\<forall>P Q \<alpha> P'. (P, Q) \<in> Rel \<and> P \<midarrow>\<alpha>\<rightarrow>Cal P' \<longrightarrow> (\<exists>Q'. Q \<midarrow>\<alpha>\<rightarrow>Cal Q' \<and> (P', Q') \<in> Rel))
   \<and> (\<forall>P Q \<alpha> Q'. (P, Q) \<in> Rel \<and> Q \<midarrow>\<alpha>\<rightarrow>Cal Q' \<longrightarrow> (\<exists>P'. P \<midarrow>\<alpha>\<rightarrow>Cal P' \<and> (P', Q') \<in> Rel))"

text \<open>A symetric strong simulation is a strong bisimulation.\<close>

lemma symm_strong_reduction_simulation_is_bisimulation:
  fixes Rel :: "('proc \<times> 'proc) set"
    and Cal :: "'proc processCalculus"
  assumes "sym Rel"
      and "strong_reduction_simulation Rel Cal"
    shows "strong_reduction_bisimulation Rel Cal"
  using assms symD[of Rel]
  by blast

lemma symm_strong_barbed_simulation_is_bisimulation:
  fixes Rel :: "('proc \<times> 'proc) set"
    and CWB :: "('proc, 'barbs) calculusWithBarbs"
  assumes "sym Rel"
      and "strong_barbed_simulation Rel CWB"
    shows "strong_barbed_bisimulation Rel CWB"
  using assms symD[of Rel]
  by blast

lemma symm_strong_labelled_simulation_is_bisimulation:
  fixes Rel :: "('proc \<times> 'proc) set"
    and Cal :: "('proc, 'lab) labelledProcessCalculus"
  assumes "sym Rel"
      and "strong_labelled_simulation Rel Cal"
    shows "strong_labelled_bisimulation Rel Cal"
  using assms symD[of Rel]
  by blast

text \<open>If a relation as well as its inverse are strong simulations, then this relation is a strong
      bisimulation.\<close>

lemma strong_reduction_simulations_impl_bisimulation:
  fixes Rel :: "('proc \<times> 'proc) set"
    and Cal :: "'proc processCalculus"
  assumes sim:    "strong_reduction_simulation Rel Cal"
      and simInv: "strong_reduction_simulation (Rel\<inverse>) Cal"
    shows "strong_reduction_bisimulation Rel Cal"
proof auto
  fix P Q P'
  assume "(P, Q) \<in> Rel" and "P \<longmapsto>Cal P'"
  with sim show "\<exists>Q'. Q \<longmapsto>Cal Q' \<and> (P', Q') \<in> Rel"
    by simp
next
  fix P Q Q'
  assume "(P, Q) \<in> Rel"
  hence "(Q, P) \<in> Rel\<inverse>"
    by simp
  moreover assume "Q \<longmapsto>Cal Q'"
  ultimately obtain P' where A1: "P \<longmapsto>Cal P'" and A2: "(Q', P') \<in> Rel\<inverse>"
    using simInv
    by blast
  from A2 have "(P', Q') \<in> Rel"
    by induct
  with A1 show "\<exists>P'. P \<longmapsto>Cal P' \<and> (P', Q') \<in> Rel"
    by blast
qed

lemma strong_labelled_simulations_impl_bisimulation:
  fixes Rel :: "('proc \<times> 'proc) set"
    and Cal :: "('proc, 'lab) labelledProcessCalculus"
  assumes sim:    "strong_labelled_simulation Rel Cal"
      and simInv: "strong_labelled_simulation (Rel\<inverse>) Cal"
    shows "strong_labelled_bisimulation Rel Cal"
proof auto
  fix P Q \<alpha> P'
  assume "(P, Q) \<in> Rel" and "P \<midarrow>\<alpha>\<rightarrow>Cal P'"
  with sim show "\<exists>Q'. Q \<midarrow>\<alpha>\<rightarrow>Cal Q' \<and> (P', Q') \<in> Rel"
    by simp
next
  fix P Q \<alpha> Q'
  assume "(P, Q) \<in> Rel"
  hence "(Q, P) \<in> Rel\<inverse>"
    by simp
  moreover assume "Q \<midarrow>\<alpha>\<rightarrow>Cal Q'"
  ultimately obtain P' where A1: "P \<midarrow>\<alpha>\<rightarrow>Cal P'" and A2: "(Q', P') \<in> Rel\<inverse>"
    using simInv
    by blast
  from A2 have "(P', Q') \<in> Rel"
    by induct
  with A1 show "\<exists>P'. P \<midarrow>\<alpha>\<rightarrow>Cal P' \<and> (P', Q') \<in> Rel"
    by blast
qed

lemma strong_reduction_bisimulations_impl_inverse_is_simulation:
  fixes Rel :: "('proc \<times> 'proc) set"
    and Cal :: "'proc processCalculus"
  assumes bisim: "strong_reduction_bisimulation Rel Cal"
  shows "strong_reduction_simulation (Rel\<inverse>) Cal"
proof clarify
  fix P Q P'
  assume "(Q, P) \<in> Rel"
  moreover assume "P \<longmapsto>Cal P'"
  ultimately obtain Q' where A1: "Q \<longmapsto>Cal Q'" and A2: "(Q', P') \<in> Rel"
    using bisim
    by blast
  from A2 have "(P', Q') \<in> Rel\<inverse>"
    by simp
  with A1 show "\<exists>Q'. Q \<longmapsto>Cal Q' \<and> (P', Q') \<in> Rel\<inverse>"
    by blast
qed

lemma strong_labelled_bisimulations_impl_inverse_is_simulation:
  fixes Rel :: "('proc \<times> 'proc) set"
    and Cal :: "('proc, 'lab) labelledProcessCalculus"
  assumes bisim: "strong_labelled_bisimulation Rel Cal"
  shows "strong_labelled_simulation (Rel\<inverse>) Cal"
proof clarify
  fix P Q \<alpha> P'
  assume "(Q, P) \<in> Rel"
  moreover assume "P \<midarrow>\<alpha>\<rightarrow>Cal P'"
  ultimately obtain Q' where A1: "Q \<midarrow>\<alpha>\<rightarrow>Cal Q'" and A2: "(Q', P') \<in> Rel"
    using bisim
    by blast
  from A2 have "(P', Q') \<in> Rel\<inverse>"
    by simp
  with A1 show "\<exists>Q'. Q \<midarrow>\<alpha>\<rightarrow>Cal Q' \<and> (P', Q') \<in> Rel\<inverse>"
    by blast
qed

lemma strong_reduction_simulations_iff_bisimulation:
  fixes Rel :: "('proc \<times> 'proc) set"
    and Cal :: "'proc processCalculus"
  shows "(strong_reduction_simulation Rel Cal \<and> strong_reduction_simulation (Rel\<inverse>) Cal)
         = strong_reduction_bisimulation Rel Cal"
  using strong_reduction_simulations_impl_bisimulation[where Rel="Rel" and Cal="Cal"]
        strong_reduction_bisimulations_impl_inverse_is_simulation[where Rel="Rel"]
  by blast

lemma strong_barbed_simulations_iff_bisimulation:
  fixes Rel :: "('proc \<times> 'proc) set"
    and CWB :: "('proc, 'barbs) calculusWithBarbs"
  shows "(strong_barbed_simulation Rel CWB \<and> strong_barbed_simulation (Rel\<inverse>) CWB)
         = strong_barbed_bisimulation Rel CWB"
proof (rule iffI, erule conjE)
  assume sim: "strong_barbed_simulation Rel CWB"
     and rev: "strong_barbed_simulation (Rel\<inverse>) CWB"
  hence "strong_reduction_bisimulation Rel (Calculus CWB)"
    using strong_reduction_simulations_impl_bisimulation[where Rel="Rel" and Cal="Calculus CWB"]
    by blast
  moreover from sim have "rel_preserves_barbs Rel CWB"
    by simp
  moreover from rev have "rel_reflects_barbs Rel CWB"
    by simp
  ultimately show "strong_barbed_bisimulation Rel CWB"
    by blast
next
  assume bisim: "strong_barbed_bisimulation Rel CWB"
  hence "strong_barbed_simulation Rel CWB"
    by blast
  moreover from bisim have "strong_reduction_simulation (Rel\<inverse>) (Calculus CWB)"
    using strong_reduction_bisimulations_impl_inverse_is_simulation[where Rel="Rel"]
    by simp
  moreover from bisim have "rel_reflects_barbs Rel CWB"
    by blast
  hence "rel_preserves_barbs (Rel\<inverse>) CWB"
    by simp
  ultimately
  show "strong_barbed_simulation Rel CWB \<and> strong_barbed_simulation (Rel\<inverse>) CWB"
    by blast
qed

lemma strong_labelled_simulations_iff_bisimulation:
  fixes Rel :: "('proc \<times> 'proc) set"
    and Cal :: "('proc, 'lab) labelledProcessCalculus"
  shows "(strong_labelled_simulation Rel Cal \<and> strong_labelled_simulation (Rel\<inverse>) Cal)
         = strong_labelled_bisimulation Rel Cal"
  using strong_labelled_simulations_impl_bisimulation[where Rel="Rel" and Cal="Cal"]
        strong_labelled_bisimulations_impl_inverse_is_simulation[where Rel="Rel"]
  by blast

text \<open>A strong bisimulation is a weak bisimulation.\<close>

lemma strong_impl_weak_reduction_bisimulation:
  fixes Rel :: "('proc \<times> 'proc) set"
    and Cal :: "'proc processCalculus"
  assumes bisim: "strong_reduction_bisimulation Rel Cal"
  shows "weak_reduction_bisimulation Rel Cal"
proof
  from bisim show "weak_reduction_simulation Rel Cal"
    using strong_impl_weak_reduction_simulation[where Rel="Rel" and Cal="Cal"]
    by blast
next
  show "\<forall>P Q Q'. (P, Q) \<in> Rel \<and> Q \<longmapsto>Cal* Q' \<longrightarrow> (\<exists>P'. P \<longmapsto>Cal* P' \<and> (P', Q') \<in> Rel)"
  proof clarify
    fix P Q Q'
    assume A1: "(P, Q) \<in> Rel"
    assume "Q \<longmapsto>Cal* Q'"
    from this obtain n where "Q \<longmapsto>Cal\<^bsup>n\<^esup> Q'"
      by (auto simp add: steps_def)
    thus "\<exists>P'. P \<longmapsto>Cal* P' \<and> (P', Q') \<in> Rel"
    proof (induct n arbitrary: Q')
      case 0
      assume "Q \<longmapsto>Cal\<^bsup>0\<^esup> Q'"
      hence "Q = Q'"
        by (simp add: steps_refl)
      moreover have "P \<longmapsto>Cal* P"
        by (rule steps_refl)
      ultimately show "\<exists>P'. P \<longmapsto>Cal* P' \<and> (P', Q') \<in> Rel"
        using A1
        by blast
    next
      case (Suc n Q'')
      assume "Q \<longmapsto>Cal\<^bsup>Suc n\<^esup> Q''"
      from this obtain Q' where A2: "Q \<longmapsto>Cal\<^bsup>n\<^esup>Q'" and A3: "Q' \<longmapsto>Cal Q''"
        by auto
      assume "\<And>Q'. Q \<longmapsto>Cal\<^bsup>n\<^esup> Q' \<Longrightarrow> \<exists>P'. P \<longmapsto>Cal* P' \<and> (P', Q') \<in> Rel"
      with A2 obtain P' where A4: "P \<longmapsto>Cal* P'" and A5: "(P', Q') \<in> Rel"
        by blast
      from bisim A5 A3 obtain P'' where A6: "P' \<longmapsto>Cal P''" and A7: "(P'', Q'') \<in> Rel"
        by blast
      from A4 A6 have "P \<longmapsto>Cal* P''"
        using steps_add[where P="P" and Q="P'" and R="P''"]
        by (simp add: step_to_steps)
      with A7 show "\<exists>P'. P \<longmapsto>Cal* P' \<and> (P', Q'') \<in> Rel"
        by blast
    qed
  qed
qed

lemma strong_barbed_bisimulation_impl_weak_respection_of_barbs:
  fixes Rel :: "('proc \<times> 'proc) set"
    and CWB :: "('proc, 'barbs) calculusWithBarbs"
  assumes bisim: "strong_barbed_bisimulation Rel CWB"
  shows "rel_weakly_respects_barbs Rel CWB"
proof
  from bisim show "rel_weakly_preserves_barbs Rel CWB"
    using strong_barbed_simulation_impl_weak_preservation_of_barbs[where Rel="Rel" and CWB="CWB"]
    by blast
next
  show "rel_weakly_reflects_barbs Rel CWB"
  proof clarify
    fix P Q a Q'
    assume "(P, Q) \<in> Rel" and "Q \<longmapsto>(Calculus CWB)* Q'"
    with bisim obtain P' where A1: "P \<longmapsto>(Calculus CWB)* P'" and A2: "(P', Q') \<in> Rel"
      using strong_impl_weak_reduction_bisimulation[where Rel="Rel" and Cal="Calculus CWB"]
      by blast
    assume "Q'\<down><CWB>a"
    with bisim A2 have "P'\<down><CWB>a"
      by blast
    with A1 show "P\<Down><CWB>a"
      by blast
  qed
qed

lemma strong_impl_weak_barbed_bisimulation:
  fixes Rel :: "('proc \<times> 'proc) set"
    and CWB :: "('proc, 'barbs) calculusWithBarbs"
  assumes bisim: "strong_barbed_bisimulation Rel CWB"
  shows "weak_barbed_bisimulation Rel CWB"
  using bisim strong_impl_weak_reduction_bisimulation[where Rel="Rel" and Cal="Calculus CWB"]
        strong_barbed_bisimulation_impl_weak_respection_of_barbs[where Rel="Rel" and CWB="CWB"]
  by blast

lemma strong_labelled_bisimulation_impl_weak_simulation_of_internal:
  fixes Rel    :: "('proc \<times> 'proc) set"
    and Cal    :: "('proc, 'lab) labelledProcessCalculus"
    and P Q Q' :: "'proc"
  assumes bisim:    "strong_labelled_bisimulation Rel Cal"
      and relation: "(P, Q) \<in> Rel"
      and internal: "Q \<rightarrow>Cal* Q'"
    shows "\<exists>P'. P \<rightarrow>Cal* P' \<and> (P', Q') \<in> Rel"
  using internal bisim relation
proof induct
  case (WTS_refl Q Cal)
  have "P \<rightarrow>Cal* P"
    using weakTauStep.WTS_refl[of P Cal]
    by simp
  moreover assume "(P, Q) \<in> Rel"
  ultimately show "\<exists>P'. P \<rightarrow>Cal* P' \<and> (P', Q) \<in> Rel"
    by blast
next
  case (WTS_trans Q Cal Q' Q'')
  from WTS_trans(2) have IH: "(strong_labelled_simulation Rel Cal \<and> (\<forall>P Q \<alpha> Q'. (P, Q) \<in> Rel \<and>
    Q \<midarrow>\<alpha>\<rightarrow>Cal Q' \<longrightarrow> (\<exists>P'. P \<midarrow>\<alpha>\<rightarrow>Cal P' \<and> (P', Q') \<in> Rel))) \<and> (P, Q) \<in> Rel \<Longrightarrow>
    \<exists>P'. P \<rightarrow>Cal* P' \<and> (P', Q') \<in> Rel"
    by simp
  assume A1: "strong_labelled_simulation Rel Cal \<and>
    (\<forall>P Q \<alpha> Q'. (P, Q) \<in> Rel \<and> Q \<midarrow>\<alpha>\<rightarrow>Cal Q' \<longrightarrow> (\<exists>P'. P \<midarrow>\<alpha>\<rightarrow>Cal P' \<and> (P', Q') \<in> Rel))"
    and "(P, Q) \<in> Rel"
  with IH obtain P' where A2: "P \<rightarrow>Cal* P'" and A3: "(P', Q') \<in> Rel"
    by blast
  assume "Q' \<midarrow>\<tau>-Cal\<rightarrow>Cal Q''"
  with A1 A3 obtain P'' where A4: "P' \<midarrow>\<tau>-Cal\<rightarrow>Cal P''" and A5: "(P'', Q'') \<in> Rel"
    by blast
  from A4 have "P' \<rightarrow>Cal* P''"
    using WTS_refl[of P' Cal] weakTauStep.WTS_trans[of P' Cal P' P'']
    by simp
  with A2 have "P \<rightarrow>Cal* P''"
    using weakTauSteps_trans[of P Cal P' P'']
    by simp
  with A5 show "\<exists>P''. P \<rightarrow>Cal* P'' \<and> (P'', Q'') \<in> Rel"
    by blast
qed

lemma strong_impl_weak_labelled_bisimulation:
  fixes Rel :: "('proc \<times> 'proc) set"
    and Cal :: "('proc, 'lab) labelledProcessCalculus"
  assumes bisim: "strong_labelled_bisimulation Rel Cal"
  shows "weak_labelled_bisimulation Rel Cal"
proof
  from bisim show "weak_labelled_simulation Rel Cal"
    using strong_impl_weak_labelled_simulation[where Rel="Rel" and Cal="Cal"]
    by blast
next
  show "\<forall>P Q \<alpha> Q'. (P, Q) \<in> Rel \<and> Q \<midarrow>\<Zcat>\<alpha>\<rightarrow>Cal* Q' \<longrightarrow> (\<exists>P'. P \<midarrow>\<Zcat>\<alpha>\<rightarrow>Cal* P' \<and> (P', Q') \<in> Rel)"
  proof clarify
    fix P Q \<alpha> Q'
    assume A1: "(P, Q) \<in> Rel" and A2: "Q \<midarrow>\<Zcat>\<alpha>\<rightarrow>Cal* Q'"
    thus "\<exists>P'. P \<midarrow>\<Zcat>\<alpha>\<rightarrow>Cal* P' \<and> (P', Q') \<in> Rel"
    proof (cases "\<alpha> = \<tau>-Cal")
      assume B1: "\<alpha> = \<tau>-Cal"
      with A2 have "Q \<rightarrow>Cal* Q'"
        unfolding weakLabelledStep_def
        by simp
      with bisim A1 obtain P' where B2: "P \<rightarrow>Cal* P'" and B3: "(P', Q') \<in> Rel"
        using strong_labelled_bisimulation_impl_weak_simulation_of_internal[of Rel Cal P Q Q']
        by blast
      from B1 B2 have "P \<midarrow>\<Zcat>\<alpha>\<rightarrow>Cal* P'"
        unfolding weakLabelledStep_def
        by simp
      with B3 show "\<exists>P'. P \<midarrow>\<Zcat>\<alpha>\<rightarrow>Cal* P' \<and> (P', Q') \<in> Rel"
        by blast
    next
      assume B1: "\<alpha> \<noteq> \<tau>-Cal" and "Q \<midarrow>\<Zcat>\<alpha>\<rightarrow>Cal* Q'"
      then obtain R S where B2: "Q \<rightarrow>Cal* R" and B3: "R \<midarrow>\<alpha>\<rightarrow>Cal S" and B4: "S \<rightarrow>Cal* Q'"
        unfolding weakLabelledStep_def weakLabelledActionStep_def
        by auto
      from bisim A1 B2 obtain T where B5: "P \<rightarrow>Cal* T" and B6: "(T, R) \<in> Rel"
        using strong_labelled_bisimulation_impl_weak_simulation_of_internal[of Rel Cal P Q R]
        by blast
      from bisim B3 B6 obtain U where B7: "T \<midarrow>\<alpha>\<rightarrow>Cal U" and B8: "(U, S) \<in> Rel"
        by blast
      from bisim B4 B8 obtain P' where B9: "U \<rightarrow>Cal* P'" and B10: "(P', Q') \<in> Rel"
        using strong_labelled_bisimulation_impl_weak_simulation_of_internal[of Rel Cal U S Q']
        by blast
      from B1 B5 B7 B9 have "P \<midarrow>\<Zcat>\<alpha>\<rightarrow>Cal* P'"
        unfolding weakLabelledStep_def weakLabelledActionStep_def
        by auto
      with B10 show "\<exists>P'. P \<midarrow>\<Zcat>\<alpha>\<rightarrow>Cal* P' \<and> (P', Q') \<in> Rel"
        by blast
    qed
  qed
qed

text \<open>The reflexive, symmetric, and/or transitive closure of a strong bisimulation is a strong
      bisimulation.\<close>

lemma strong_reduction_bisimulation_and_closures:
  fixes Rel :: "('proc \<times> 'proc) set"
    and Cal :: "'proc processCalculus"
  assumes bisim: "strong_reduction_bisimulation Rel Cal"
  shows "strong_reduction_bisimulation (Rel\<^sup>=) Cal"
    and "strong_reduction_bisimulation (symcl Rel) Cal"
    and "strong_reduction_bisimulation (Rel\<^sup>+) Cal"
    and "strong_reduction_bisimulation (symcl (Rel\<^sup>=)) Cal"
    and "strong_reduction_bisimulation (Rel\<^sup>*) Cal"
    and "strong_reduction_bisimulation ((symcl (Rel\<^sup>=))\<^sup>+) Cal"
proof -
  from bisim show A: "strong_reduction_bisimulation (Rel\<^sup>=) Cal"
    by (auto simp add: refl, blast+)
  have B: "\<And>Rel. strong_reduction_bisimulation Rel Cal
           \<Longrightarrow> strong_reduction_bisimulation (symcl Rel) Cal"
    by (auto simp add: symcl_def, blast+)
  from bisim B[where Rel="Rel"] show "strong_reduction_bisimulation (symcl Rel) Cal"
    by blast
  have C: "\<And>Rel. strong_reduction_bisimulation Rel Cal
           \<Longrightarrow> strong_reduction_bisimulation (Rel\<^sup>+) Cal"
  proof
    fix Rel
    assume "strong_reduction_bisimulation Rel Cal"
    thus "strong_reduction_simulation (Rel\<^sup>+) Cal"
      using strong_reduction_simulation_and_closures(2)[where Rel="Rel" and Cal="Cal"]
      by blast
  next
    fix Rel
    assume C1: "strong_reduction_bisimulation Rel Cal"
    show "\<forall>P Q Q'. (P, Q) \<in> Rel\<^sup>+ \<and> Q \<longmapsto>Cal Q' \<longrightarrow> (\<exists>P'. P \<longmapsto>Cal P' \<and> (P', Q') \<in> Rel\<^sup>+)"
    proof clarify
      fix P Q Q'
      assume "(P, Q) \<in> Rel\<^sup>+" and "Q \<longmapsto>Cal Q'"
      thus "\<exists>P'. P \<longmapsto>Cal P' \<and> (P', Q') \<in> Rel\<^sup>+"
      proof (induct arbitrary: Q')
        fix Q Q'
        assume "(P, Q) \<in> Rel" and "Q \<longmapsto>Cal Q'"
        with C1 obtain P' where "P \<longmapsto>Cal P'" and "(P', Q') \<in> Rel"
          by blast
        thus "\<exists>P'. P \<longmapsto>Cal P' \<and> (P', Q') \<in> Rel\<^sup>+"
          by auto
      next
        case (step Q R R')
        assume "(Q, R) \<in> Rel" and "R \<longmapsto>Cal R'"
        with C1 obtain Q' where C2: "Q \<longmapsto>Cal Q'" and C3: "(Q', R') \<in> Rel\<^sup>+"
          by blast
        assume "\<And>Q'. Q \<longmapsto>Cal Q' \<Longrightarrow> \<exists>P'. P \<longmapsto>Cal P' \<and> (P', Q') \<in> Rel\<^sup>+"
        with C2 obtain P' where C4: "P \<longmapsto>Cal P'" and C5: "(P', Q') \<in> Rel\<^sup>+"
          by blast
        from C5 C3 have "(P', R') \<in> Rel\<^sup>+"
          by simp
        with C4 show "\<exists>P'. P \<longmapsto>Cal P' \<and> (P', R') \<in> Rel\<^sup>+"
          by blast
      qed
    qed
  qed
  from bisim C[where Rel="Rel"] show "strong_reduction_bisimulation (Rel\<^sup>+) Cal"
    by blast
  from A B[where Rel="Rel\<^sup>="]
  show "strong_reduction_bisimulation (symcl (Rel\<^sup>=)) Cal"
    by blast
  from A C[where Rel="Rel\<^sup>="]
  show "strong_reduction_bisimulation (Rel\<^sup>*) Cal"
    using trancl_reflcl[of Rel]
    by auto
  from A B[where Rel="Rel\<^sup>="] C[where Rel="symcl (Rel\<^sup>=)"]
  show "strong_reduction_bisimulation ((symcl (Rel\<^sup>=))\<^sup>+) Cal"
    by blast
qed

lemma strong_barbed_bisimulation_and_closures:
  fixes Rel :: "('proc \<times> 'proc) set"
    and CWB :: "('proc, 'barbs) calculusWithBarbs"
  assumes bisim: "strong_barbed_bisimulation Rel CWB"
  shows "strong_barbed_bisimulation (Rel\<^sup>=) CWB"
    and "strong_barbed_bisimulation (symcl Rel) CWB"
    and "strong_barbed_bisimulation (Rel\<^sup>+) CWB"
    and "strong_barbed_bisimulation (symcl (Rel\<^sup>=)) CWB"
    and "strong_barbed_bisimulation (Rel\<^sup>*) CWB"
    and "strong_barbed_bisimulation ((symcl (Rel\<^sup>=))\<^sup>+) CWB"
proof -
  from bisim show "strong_barbed_bisimulation (Rel\<^sup>=) CWB"
    using strong_reduction_bisimulation_and_closures(1)[where Rel="Rel" and Cal="Calculus CWB"]
          respection_of_barbs_and_closures(1)[where Rel="Rel" and CWB="CWB"]
    by fast
next
  from bisim show "strong_barbed_bisimulation (symcl Rel) CWB"
    using strong_reduction_bisimulation_and_closures(2)[where Rel="Rel" and Cal="Calculus CWB"]
          respection_of_barbs_and_closures(2)[where Rel="Rel" and CWB="CWB"]
    by blast
next
  from bisim show "strong_barbed_bisimulation (Rel\<^sup>+) CWB"
    using strong_reduction_bisimulation_and_closures(3)[where Rel="Rel" and Cal="Calculus CWB"]
          respection_of_barbs_and_closures(3)[where Rel="Rel" and CWB="CWB"]
    by blast
next
  from bisim show "strong_barbed_bisimulation (symcl (Rel\<^sup>=)) CWB"
    using strong_reduction_bisimulation_and_closures(4)[where Rel="Rel" and Cal="Calculus CWB"]
          respection_of_barbs_and_closures(4)[where Rel="Rel" and CWB="CWB"]
    by blast
next
  from bisim show "strong_barbed_bisimulation (Rel\<^sup>*) CWB"
    using strong_reduction_bisimulation_and_closures(5)[where Rel="Rel" and Cal="Calculus CWB"]
          respection_of_barbs_and_closures(5)[where Rel="Rel" and CWB="CWB"]
    by blast
next
  from bisim show "strong_barbed_bisimulation ((symcl (Rel\<^sup>=))\<^sup>+) CWB"
    using strong_reduction_bisimulation_and_closures(6)[where Rel="Rel" and Cal="Calculus CWB"]
          respection_of_barbs_and_closures(6)[where Rel="Rel" and CWB="CWB"]
    by blast
qed

lemma strong_labelled_bisimulation_and_closures:
  fixes Rel :: "('proc \<times> 'proc) set"
    and Cal :: "('proc, 'lab) labelledProcessCalculus"
  assumes bisim: "strong_labelled_bisimulation Rel Cal"
  shows "strong_labelled_bisimulation (Rel\<^sup>=) Cal"
    and "strong_labelled_bisimulation (symcl Rel) Cal"
    and "strong_labelled_bisimulation (Rel\<^sup>+) Cal"
    and "strong_labelled_bisimulation (symcl (Rel\<^sup>=)) Cal"
    and "strong_labelled_bisimulation (Rel\<^sup>*) Cal"
    and "strong_labelled_bisimulation ((symcl (Rel\<^sup>=))\<^sup>+) Cal"
proof -
  from bisim show A: "strong_labelled_bisimulation (Rel\<^sup>=) Cal"
    by (auto simp add: refl, blast+)
  have B: "\<And>Rel. strong_labelled_bisimulation Rel Cal
           \<Longrightarrow> strong_labelled_bisimulation (symcl Rel) Cal"
    by (auto simp add: symcl_def, blast+)
  from bisim B[where Rel="Rel"] show "strong_labelled_bisimulation (symcl Rel) Cal"
    by blast
  have C: "\<And>Rel. strong_labelled_bisimulation Rel Cal \<Longrightarrow> strong_labelled_bisimulation (Rel\<^sup>+) Cal"
  proof
    fix Rel
    assume "strong_labelled_bisimulation Rel Cal"
    thus "strong_labelled_simulation (Rel\<^sup>+) Cal"
      using strong_labelled_simulation_and_closures(2)[where Rel="Rel" and Cal="Cal"]
      by blast
  next
    fix Rel
    assume C1: "strong_labelled_bisimulation Rel Cal"
    show "\<forall>P Q \<alpha> Q'. (P, Q) \<in> Rel\<^sup>+ \<and> Q \<midarrow>\<alpha>\<rightarrow>Cal Q' \<longrightarrow> (\<exists>P'. P \<midarrow>\<alpha>\<rightarrow>Cal P' \<and> (P', Q') \<in> Rel\<^sup>+)"
    proof clarify
      fix P Q \<alpha> Q'
      assume "(P, Q) \<in> Rel\<^sup>+" and "Q \<midarrow>\<alpha>\<rightarrow>Cal Q'"
      thus "\<exists>P'. P \<midarrow>\<alpha>\<rightarrow>Cal P' \<and> (P', Q') \<in> Rel\<^sup>+"
      proof (induct arbitrary: Q')
        fix Q Q'
        assume "(P, Q) \<in> Rel" and "Q \<midarrow>\<alpha>\<rightarrow>Cal Q'"
        with C1 obtain P' where "P \<midarrow>\<alpha>\<rightarrow>Cal P'" and "(P', Q') \<in> Rel"
          by blast
        thus "\<exists>P'. P \<midarrow>\<alpha>\<rightarrow>Cal P' \<and> (P', Q') \<in> Rel\<^sup>+"
          by auto
      next
        case (step Q R R')
        assume "(Q, R) \<in> Rel" and "R \<midarrow>\<alpha>\<rightarrow>Cal R'"
        with C1 obtain Q' where C2: "Q \<midarrow>\<alpha>\<rightarrow>Cal Q'" and C3: "(Q', R') \<in> Rel\<^sup>+"
          by blast
        assume "\<And>Q'. Q \<midarrow>\<alpha>\<rightarrow>Cal Q' \<Longrightarrow> \<exists>P'. P \<midarrow>\<alpha>\<rightarrow>Cal P' \<and> (P', Q') \<in> Rel\<^sup>+"
        with C2 obtain P' where C4: "P \<midarrow>\<alpha>\<rightarrow>Cal P'" and C5: "(P', Q') \<in> Rel\<^sup>+"
          by blast
        from C5 C3 have "(P', R') \<in> Rel\<^sup>+"
          by simp
        with C4 show "\<exists>P'. P \<midarrow>\<alpha>\<rightarrow>Cal P' \<and> (P', R') \<in> Rel\<^sup>+"
          by blast
      qed
    qed
  qed
  from bisim C[where Rel="Rel"] show "strong_labelled_bisimulation (Rel\<^sup>+) Cal"
    by blast
  from A B[where Rel="Rel\<^sup>="]
  show "strong_labelled_bisimulation (symcl (Rel\<^sup>=)) Cal"
    by blast
  from A C[where Rel="Rel\<^sup>="]
  show "strong_labelled_bisimulation (Rel\<^sup>*) Cal"
    using trancl_reflcl[of Rel]
    by auto
  from A B[where Rel="Rel\<^sup>="] C[where Rel="symcl (Rel\<^sup>=)"]
  show "strong_labelled_bisimulation ((symcl (Rel\<^sup>=))\<^sup>+) Cal"
    by blast
qed

subsection \<open>Step Closure of Relations\<close>

text \<open>The step closure of a relation on process terms is the transitive closure of the union of
      the relation and the inverse of the reduction relation of the respective calculus.\<close>

inductive_set stepsClosure :: "('a \<times> 'a) set \<Rightarrow> 'a processCalculus \<Rightarrow> ('a \<times> 'a) set"
    for Rel :: "('a \<times> 'a) set"
    and Cal :: "'a processCalculus"
  where
  rel:   "(P, Q) \<in> Rel \<Longrightarrow> (P, Q) \<in> stepsClosure Rel Cal" |
  steps: "P \<longmapsto>Cal* P' \<Longrightarrow> (P', P) \<in> stepsClosure Rel Cal" |
  trans: "\<lbrakk>(P, Q) \<in> stepsClosure Rel Cal; (Q, R) \<in> stepsClosure Rel Cal\<rbrakk>
          \<Longrightarrow> (P, R) \<in> stepsClosure Rel Cal"

abbreviation stepsClosureInfix ::
    "'a \<Rightarrow> ('a \<times> 'a) set \<Rightarrow> 'a processCalculus \<Rightarrow> 'a \<Rightarrow> bool" (\<open>_ \<R>\<mapsto><_,_> _\<close> [75, 75, 75, 75] 80)
  where
  "P \<R>\<mapsto><Rel,Cal> Q \<equiv> (P, Q) \<in> stepsClosure Rel Cal"

inductive_set stepsClosureLS
  :: "('a \<times> 'a) set \<Rightarrow> ('a, 'b) labelledProcessCalculus \<Rightarrow> ('a \<times> 'a) set"
    for Rel :: "('a \<times> 'a) set"
    and Cal :: "('a, 'b) labelledProcessCalculus"
  where
  rel:   "(P, Q) \<in> Rel \<Longrightarrow> (P, Q) \<in> stepsClosureLS Rel Cal" |
  steps: "P \<rightarrow>Cal* P' \<Longrightarrow> (P', P) \<in> stepsClosureLS Rel Cal" |
  trans: "\<lbrakk>(P, Q) \<in> stepsClosureLS Rel Cal; (Q, R) \<in> stepsClosureLS Rel Cal\<rbrakk>
          \<Longrightarrow> (P, R) \<in> stepsClosureLS Rel Cal"

abbreviation stepsClosureLSInfix
  :: "'a \<Rightarrow> ('a \<times> 'a) set \<Rightarrow> ('a, 'b) labelledProcessCalculus \<Rightarrow> 'a \<Rightarrow> bool"
  (\<open>_ \<R>\<rightarrow><_,_> _\<close> [75, 75, 75, 75] 80) where
  "P \<R>\<rightarrow><Rel,Cal> Q \<equiv> (P, Q) \<in> stepsClosureLS Rel Cal"

text \<open>Applying the steps closure twice does not change the relation.\<close>

lemma steps_closure_of_steps_closure:
  fixes Rel :: "('a \<times> 'a) set"
    and Cal :: "'a processCalculus"
  shows "stepsClosure (stepsClosure Rel Cal) Cal = stepsClosure Rel Cal"
proof auto
  fix P Q
  assume "P \<R>\<mapsto><stepsClosure Rel Cal,Cal> Q"
  thus "P \<R>\<mapsto><Rel,Cal> Q"
  proof induct
    case (rel P Q)
    assume "P \<R>\<mapsto><Rel,Cal> Q"
    thus "P \<R>\<mapsto><Rel,Cal> Q"
      by simp
  next
    case (steps P P')
    assume "P \<longmapsto>Cal* P'"
    thus "P' \<R>\<mapsto><Rel,Cal> P"
      by (rule stepsClosure.steps)
  next
    case (trans P Q R)
    assume "P \<R>\<mapsto><Rel,Cal> Q" and "Q \<R>\<mapsto><Rel,Cal> R"
    thus "P \<R>\<mapsto><Rel,Cal> R"
      by (rule stepsClosure.trans)
  qed
next
  fix P Q
  assume "P \<R>\<mapsto><Rel,Cal> Q"
  thus "P \<R>\<mapsto><stepsClosure Rel Cal,Cal> Q"
    by (rule stepsClosure.rel)
qed

lemma steps_closure_LS_of_steps_closure_LS:
  fixes Rel :: "('a \<times> 'a) set"
    and Cal :: "('a, 'b) labelledProcessCalculus"
  shows "stepsClosureLS (stepsClosureLS Rel Cal) Cal = stepsClosureLS Rel Cal"
proof auto
  fix P Q
  assume "P \<R>\<rightarrow><stepsClosureLS Rel Cal,Cal> Q"
  thus "P \<R>\<rightarrow><Rel,Cal> Q"
  proof induct
    case (rel P Q)
    assume "P \<R>\<rightarrow><Rel,Cal> Q"
    thus "P \<R>\<rightarrow><Rel,Cal> Q"
      by simp
  next
    case (steps P P')
    assume "P \<rightarrow>Cal* P'"
    thus "P' \<R>\<rightarrow><Rel,Cal> P"
      by (rule stepsClosureLS.steps)
  next
    case (trans P Q R)
    assume "P \<R>\<rightarrow><Rel,Cal> Q" and "Q \<R>\<rightarrow><Rel,Cal> R"
    thus "P \<R>\<rightarrow><Rel,Cal> R"
      by (rule stepsClosureLS.trans)
  qed
next
  fix P Q
  assume "P \<R>\<rightarrow><Rel,Cal> Q"
  thus "P \<R>\<rightarrow><stepsClosureLS Rel Cal,Cal> Q"
    by (rule stepsClosureLS.rel)
qed

text \<open>The steps closure is a preorder.\<close>

lemma stepsClosure_refl:
  fixes Rel :: "('a \<times> 'a) set"
    and Cal :: "'a processCalculus"
  shows "refl (stepsClosure Rel Cal)"
  unfolding refl_on_def
proof auto
  fix P
  have "P \<longmapsto>Cal* P"
    by (rule steps_refl)
  thus "P \<R>\<mapsto><Rel,Cal> P"
    by (rule stepsClosure.steps)
qed

lemma stepsClosureLS_refl:
  fixes Rel :: "('a \<times> 'a) set"
    and Cal :: "('a, 'b) labelledProcessCalculus"
  shows "refl (stepsClosureLS Rel Cal)"
  unfolding refl_on_def
proof auto
  fix P
  have "P \<rightarrow>Cal* P"
    by (rule WTS_refl)
  thus "P \<R>\<rightarrow><Rel,Cal> P"
    by (rule stepsClosureLS.steps)
qed

lemma refl_trans_closure_of_rel_impl_steps_closure:
  fixes Rel :: "('a \<times> 'a) set"
    and Cal :: "'a processCalculus"
    and P Q :: "'a"
  assumes "(P, Q) \<in> Rel\<^sup>*"
  shows "P \<R>\<mapsto><Rel,Cal> Q"
  using assms
proof induct
  show "P \<R>\<mapsto><Rel,Cal> P"
    using stepsClosure_refl[of Rel Cal]
    unfolding refl_on_def
    by simp
next
  case (step Q R)
  assume "(Q, R) \<in> Rel" and "P \<R>\<mapsto><Rel,Cal> Q"
  thus "P \<R>\<mapsto><Rel,Cal> R"
    using stepsClosure.rel[of Q R Rel Cal] stepsClosure.trans[of P Q Rel Cal R]
    by blast
qed

lemma refl_trans_closure_of_rel_impl_steps_closure_LS:
  fixes Rel :: "('a \<times> 'a) set"
    and Cal :: "('a, 'b) labelledProcessCalculus"
    and P Q :: "'a"
  assumes "(P, Q) \<in> Rel\<^sup>*"
  shows "P \<R>\<rightarrow><Rel,Cal> Q"
  using assms
proof induct
  show "P \<R>\<rightarrow><Rel,Cal> P"
    using stepsClosureLS_refl[of Rel Cal]
    unfolding refl_on_def
    by simp
next
  case (step Q R)
  assume "(Q, R) \<in> Rel" and "P \<R>\<rightarrow><Rel,Cal> Q"
  thus "P \<R>\<rightarrow><Rel,Cal> R"
    using stepsClosureLS.rel[of Q R Rel Cal] stepsClosureLS.trans[of P Q Rel Cal R]
    by blast
qed

text \<open>The steps closure of a relation is always a weak reduction simulation.\<close>

lemma steps_closure_is_weak_reduction_simulation:
  fixes Rel :: "('a \<times> 'a) set"
    and Cal :: "'a processCalculus"
  shows "weak_reduction_simulation (stepsClosure Rel Cal) Cal"
proof clarify
  fix P Q P'
  assume "P \<R>\<mapsto><Rel,Cal> Q" and "P \<longmapsto>Cal* P'"
  thus "\<exists>Q'. Q \<longmapsto>Cal* Q' \<and> P' \<R>\<mapsto><Rel,Cal> Q'"
  proof (induct arbitrary: P')
    case (rel P Q)
    assume "P \<longmapsto>Cal* P'"
    hence "P' \<R>\<mapsto><Rel,Cal> P"
      by (rule stepsClosure.steps)
    moreover assume "(P, Q) \<in> Rel"
    hence "P \<R>\<mapsto><Rel,Cal> Q"
      by (simp add: stepsClosure.rel)
    ultimately have "P' \<R>\<mapsto><Rel,Cal> Q"
      by (rule stepsClosure.trans)
    thus "\<exists>Q'. Q \<longmapsto>Cal* Q' \<and> P' \<R>\<mapsto><Rel,Cal> Q'"
      using steps_refl[where Cal="Cal" and P="Q"]
      by blast
  next
    case (steps P P' P'')
    assume "P \<longmapsto>Cal* P'" and "P' \<longmapsto>Cal* P''"
    hence "P \<longmapsto>Cal* P''"
      by (rule steps_add)
    moreover have "P'' \<R>\<mapsto><Rel,Cal> P''"
      using stepsClosure_refl[where Rel="Rel" and Cal="Cal"]
      unfolding refl_on_def
      by simp
    ultimately show "\<exists>Q'. P \<longmapsto>Cal* Q' \<and> P'' \<R>\<mapsto><Rel,Cal> Q'"
      by blast
  next
    case (trans P Q R)
    assume "P \<longmapsto>Cal* P'"
       and "\<And>P'. P \<longmapsto>Cal* P' \<Longrightarrow> \<exists>Q'. Q \<longmapsto>Cal* Q' \<and> P' \<R>\<mapsto><Rel,Cal> Q'"
    from this obtain Q' where A1: "Q \<longmapsto>Cal* Q'" and A2: "P' \<R>\<mapsto><Rel,Cal> Q'"
      by blast
    assume "\<And>Q'. Q \<longmapsto>Cal* Q' \<Longrightarrow> \<exists>R'. R \<longmapsto>Cal* R' \<and> Q' \<R>\<mapsto><Rel,Cal> R'"
    with A1 obtain R' where A3: "R \<longmapsto>Cal* R'" and A4: "Q' \<R>\<mapsto><Rel,Cal> R'"
      by blast
    from A2 A4 have "P' \<R>\<mapsto><Rel,Cal> R'"
      by (rule stepsClosure.trans)
    with A3 show "\<exists>R'. R \<longmapsto>Cal* R' \<and> P' \<R>\<mapsto><Rel,Cal> R'"
      by blast
  qed
qed

text \<open>If Rel is a weak simulation and its inverse is a weak contrasimulation, then the steps
      closure of Rel is a contrasimulation.\<close>

lemma inverse_contrasimulation_impl_reverse_pair_in_steps_closure:
  fixes Rel :: "('a \<times> 'a) set"
    and Cal :: "'a processCalculus"
    and P Q :: "'a"
  assumes con:  "weak_reduction_contrasimulation (Rel\<inverse>) Cal"
      and pair: "(P, Q) \<in> Rel"
  shows "Q \<R>\<mapsto><Rel,Cal> P"
proof -
  from pair have "(Q, P) \<in> Rel\<inverse>"
    by simp
  moreover have "Q \<longmapsto>Cal* Q"
    by (rule steps_refl)
  ultimately obtain P' where A1: "P \<longmapsto>Cal* P'" and A2: "(P', Q) \<in> Rel\<inverse>"
    using con
    by blast
  from A2 have "Q \<R>\<mapsto><Rel,Cal> P'"
    by (simp add: stepsClosure.rel)
  moreover from A1 have "P' \<R>\<mapsto><Rel,Cal> P"
    by (rule stepsClosure.steps)
  ultimately show "Q \<R>\<mapsto><Rel,Cal> P"
    by (rule stepsClosure.trans)
qed

lemma simulation_and_inverse_contrasimulation_impl_steps_closure_is_contrasimulation:
  fixes Rel :: "('a \<times> 'a) set"
    and Cal :: "'a processCalculus"
  assumes sim: "weak_reduction_simulation Rel Cal"
      and con: "weak_reduction_contrasimulation (Rel\<inverse>) Cal"
    shows "weak_reduction_contrasimulation (stepsClosure Rel Cal) Cal"
proof clarify
  fix P Q P'
  assume "P \<R>\<mapsto><Rel,Cal> Q" and "P \<longmapsto>Cal* P'"
  thus "\<exists>Q'. Q \<longmapsto>Cal* Q' \<and> Q' \<R>\<mapsto><Rel,Cal> P'"
  proof (induct arbitrary: P')
    case (rel P Q)
    assume "(P, Q) \<in> Rel" and "P \<longmapsto>Cal* P'"
    with sim obtain Q' where A1: "Q \<longmapsto>Cal* Q'" and A2: "(P', Q') \<in> Rel"
      by blast
    from A2 con have "Q' \<R>\<mapsto><Rel,Cal> P'"
      using inverse_contrasimulation_impl_reverse_pair_in_steps_closure[where Rel="Rel"]
      by blast
    with A1 show "\<exists>Q'. Q \<longmapsto>Cal* Q' \<and> Q' \<R>\<mapsto><Rel,Cal> P'"
      by blast
  next
    case (steps P P' P'')
    assume "P \<longmapsto>Cal* P'" and "P' \<longmapsto>Cal* P''"
    hence "P \<longmapsto>Cal* P''"
      by (rule steps_add)
    thus "\<exists>Q'. P \<longmapsto>Cal* Q' \<and> Q' \<R>\<mapsto><Rel,Cal> P''"
      using stepsClosure_refl[where Rel="Rel" and Cal="Cal"]
      unfolding refl_on_def
      by blast
  next
    case (trans P Q R)
    assume "\<And>P'. P \<longmapsto>Cal* P' \<Longrightarrow> \<exists>Q'. Q \<longmapsto>Cal* Q' \<and> Q' \<R>\<mapsto><Rel,Cal> P'"
       and "P \<longmapsto>Cal* P'"
    from this obtain Q' where A1: "Q \<longmapsto>Cal* Q'" and A2: "Q' \<R>\<mapsto><Rel,Cal> P'"
      by blast
    assume "\<And>Q'. Q \<longmapsto>Cal* Q' \<Longrightarrow> \<exists>R'. R \<longmapsto>Cal* R' \<and> R' \<R>\<mapsto><Rel,Cal> Q'"
    with A1 obtain R' where A3: "R \<longmapsto>Cal* R'" and A4: "R' \<R>\<mapsto><Rel,Cal> Q'"
      by blast
    from A4 A2 have "R' \<R>\<mapsto><Rel,Cal> P'"
      by (rule stepsClosure.trans)
    with A3 show "\<exists>R'. R \<longmapsto>Cal* R' \<and> R' \<R>\<mapsto><Rel,Cal> P'"
      by blast
  qed
qed

text \<open>Accordingly, if Rel is a weak simulation and its inverse is a weak contrasimulation, then the
      steps closure of Rel is a coupled simulation.\<close>

lemma simulation_and_inverse_contrasimulation_impl_steps_closure_is_coupled_simulation:
  fixes Rel :: "('a \<times> 'a) set"
    and Cal :: "'a processCalculus"
  assumes sim: "weak_reduction_simulation Rel Cal"
      and con: "weak_reduction_contrasimulation (Rel\<inverse>) Cal"
    shows "weak_reduction_coupled_simulation (stepsClosure Rel Cal) Cal"
  using sim con simulation_and_inverse_contrasimulation_impl_steps_closure_is_contrasimulation
        steps_closure_is_weak_reduction_simulation[where Rel="Rel" and Cal="Cal"]
  by simp

text \<open>If the relation that is closed under steps is a (contra)simulation, then we can conclude from
      a pair in the closure on a pair in the original relation.\<close>

lemma stepsClosure_simulation_impl_refl_trans_closure_of_Rel:
  fixes Rel :: "('a \<times> 'a) set"
    and Cal :: "'a processCalculus"
    and P Q :: "'a"
  assumes A1: "P \<R>\<mapsto><Rel,Cal> Q"
      and A2: "weak_reduction_simulation Rel Cal"
    shows "\<exists>Q'. Q \<longmapsto>Cal* Q' \<and> (P, Q') \<in> Rel\<^sup>*"
proof -
  have "\<forall>P'. P \<longmapsto>Cal* P' \<longrightarrow> (\<exists>Q'. Q \<longmapsto>Cal* Q' \<and> (P', Q') \<in> Rel\<^sup>*)"
    using A1
  proof induct
    case (rel P Q)
    assume "(P, Q) \<in> Rel"
    with A2 have "\<forall>P'. P \<longmapsto>Cal* P' \<longrightarrow> (\<exists>Q'. Q \<longmapsto>Cal* Q' \<and> (P', Q') \<in> Rel)"
      by blast
    thus "\<forall>P'. P \<longmapsto>Cal* P' \<longrightarrow> (\<exists>Q'. Q \<longmapsto>Cal* Q' \<and> (P', Q') \<in> Rel\<^sup>*)"
      by blast
  next
    case (steps P P')
    assume A: "P \<longmapsto>Cal* P'"
    show "\<forall>P''. P' \<longmapsto>Cal* P'' \<longrightarrow> (\<exists>Q'. P \<longmapsto>Cal* Q' \<and> (P'', Q') \<in> Rel\<^sup>*)"
    proof clarify
      fix P''
      assume "P' \<longmapsto>Cal* P''"
      with A have "P \<longmapsto>Cal* P''"
        by (rule steps_add)
      moreover have "(P'', P'') \<in> Rel\<^sup>*"
        by simp
      ultimately show "\<exists>Q'. P \<longmapsto>Cal* Q' \<and> (P'', Q') \<in> Rel\<^sup>*"
        by blast
    qed
  next
    case (trans P Q R)
    assume A1: "\<forall>P'. P \<longmapsto>Cal* P' \<longrightarrow> (\<exists>Q'. Q \<longmapsto>Cal* Q' \<and> (P', Q') \<in> Rel\<^sup>*)"
       and A2: "\<forall>Q'. Q \<longmapsto>Cal* Q' \<longrightarrow> (\<exists>R'. R \<longmapsto>Cal* R' \<and> (Q', R') \<in> Rel\<^sup>*)"
    show "\<forall>P'. P \<longmapsto>Cal* P' \<longrightarrow> (\<exists>R'. R \<longmapsto>Cal* R' \<and> (P', R') \<in> Rel\<^sup>*)"
    proof clarify
      fix P'
      assume "P \<longmapsto>Cal* P'"
      with A1 obtain Q' where A3: "Q \<longmapsto>Cal* Q'" and A4: "(P', Q') \<in> Rel\<^sup>*"
        by blast
      from A2 A3 obtain R' where A5: "R \<longmapsto>Cal* R'" and A6: "(Q', R') \<in> Rel\<^sup>*"
        by blast
      from A4 A6 have "(P', R') \<in> Rel\<^sup>*"
        by simp
      with A5 show "\<exists>R'. R \<longmapsto>Cal* R' \<and> (P', R') \<in> Rel\<^sup>*"
        by blast
    qed
  qed
  moreover have "P \<longmapsto>Cal* P"
    by (rule steps_refl)
  ultimately show ?thesis
    by blast
qed

lemma stepsClosure_contrasimulation_impl_refl_trans_closure_of_Rel:
  fixes Rel :: "('a \<times> 'a) set"
    and Cal :: "'a processCalculus"
    and P Q :: "'a"
  assumes A1: "P \<R>\<mapsto><Rel,Cal> Q"
      and A2: "weak_reduction_contrasimulation Rel Cal"
    shows "\<exists>Q'. Q \<longmapsto>Cal* Q' \<and> (Q', P) \<in> Rel\<^sup>*"
proof -
  have "\<forall>P'. P \<longmapsto>Cal* P' \<longrightarrow> (\<exists>Q'. Q \<longmapsto>Cal* Q' \<and> (Q', P') \<in> Rel\<^sup>*)"
    using A1
  proof induct
    case (rel P Q)
    assume "(P, Q) \<in> Rel"
    with A2 have "\<forall>P'. P \<longmapsto>Cal* P' \<longrightarrow> (\<exists>Q'. Q \<longmapsto>Cal* Q' \<and> (Q', P') \<in> Rel)"
      by blast
    thus "\<forall>P'. P \<longmapsto>Cal* P' \<longrightarrow> (\<exists>Q'. Q \<longmapsto>Cal* Q' \<and> (Q', P') \<in> Rel\<^sup>*)"
      by blast
  next
    case (steps P P')
    assume A: "P \<longmapsto>Cal* P'"
    show "\<forall>P''. P' \<longmapsto>Cal* P'' \<longrightarrow> (\<exists>Q'. P \<longmapsto>Cal* Q' \<and> (Q', P'') \<in> Rel\<^sup>*)"
    proof clarify
      fix P''
      assume "P' \<longmapsto>Cal* P''"
      with A have "P \<longmapsto>Cal* P''"
        by (rule steps_add)
      moreover have "(P'', P'') \<in> Rel\<^sup>*"
        by simp
      ultimately show "\<exists>Q'. P \<longmapsto>Cal* Q' \<and> (Q', P'') \<in> Rel\<^sup>*"
        by blast
    qed
  next
    case (trans P Q R)
    assume A1: "\<forall>P'. P \<longmapsto>Cal* P' \<longrightarrow> (\<exists>Q'. Q \<longmapsto>Cal* Q' \<and> (Q', P') \<in> Rel\<^sup>*)"
       and A2: "\<forall>Q'. Q \<longmapsto>Cal* Q' \<longrightarrow> (\<exists>R'. R \<longmapsto>Cal* R' \<and> (R', Q') \<in> Rel\<^sup>*)"
    show "\<forall>P'. P \<longmapsto>Cal* P' \<longrightarrow> (\<exists>R'. R \<longmapsto>Cal* R' \<and> (R', P') \<in> Rel\<^sup>*)"
    proof clarify
      fix P'
      assume "P \<longmapsto>Cal* P'"
      with A1 obtain Q' where A3: "Q \<longmapsto>Cal* Q'" and A4: "(Q', P') \<in> Rel\<^sup>*"
        by blast
      from A2 A3 obtain R' where A5: "R \<longmapsto>Cal* R'" and A6: "(R', Q') \<in> Rel\<^sup>*"
        by blast
      from A4 A6 have "(R', P') \<in> Rel\<^sup>*"
        by simp
      with A5 show "\<exists>R'. R \<longmapsto>Cal* R' \<and> (R', P') \<in> Rel\<^sup>*"
        by blast
    qed
  qed
  moreover have "P \<longmapsto>Cal* P"
    by (rule steps_refl)
  ultimately show ?thesis
    by blast
qed

lemma stepsClosure_contrasimulation_of_inverse_impl_refl_trans_closure_of_Rel:
  fixes Rel :: "('a \<times> 'a) set"
    and Cal :: "'a processCalculus"
    and P Q :: "'a"
  assumes A1: "P \<R>\<mapsto><Rel\<inverse>,Cal> Q"
      and A2: "weak_reduction_contrasimulation (Rel\<inverse>) Cal"
    shows "\<exists>Q'. Q \<longmapsto>Cal* Q' \<and> (P, Q') \<in> Rel\<^sup>*"
proof -
  have "\<forall>P'. P \<longmapsto>Cal* P' \<longrightarrow> (\<exists>Q'. Q \<longmapsto>Cal* Q' \<and> (P', Q') \<in> Rel\<^sup>*)"
    using A1
  proof induct
    case (rel P Q)
    assume "(P, Q) \<in> Rel\<inverse>"
    with A2 have "\<forall>P'. P \<longmapsto>Cal* P' \<longrightarrow> (\<exists>Q'. Q \<longmapsto>Cal* Q' \<and> (Q', P') \<in> Rel\<inverse>)"
      by blast
    thus "\<forall>P'. P \<longmapsto>Cal* P' \<longrightarrow> (\<exists>Q'. Q \<longmapsto>Cal* Q' \<and> (P', Q') \<in> Rel\<^sup>*)"
      by blast
  next
    case (steps P P')
    assume A: "P \<longmapsto>Cal* P'"
    show "\<forall>P''. P' \<longmapsto>Cal* P'' \<longrightarrow> (\<exists>Q'. P \<longmapsto>Cal* Q' \<and> (P'', Q') \<in> Rel\<^sup>*)"
    proof clarify
      fix P''
      assume "P' \<longmapsto>Cal* P''"
      with A have "P \<longmapsto>Cal* P''"
        by (rule steps_add)
      moreover have "(P'', P'') \<in> Rel\<^sup>*"
        by simp
      ultimately show "\<exists>Q'. P \<longmapsto>Cal* Q' \<and> (P'', Q') \<in> Rel\<^sup>*"
        by blast
    qed
  next
    case (trans P Q R)
    assume A1: "\<forall>P'. P \<longmapsto>Cal* P' \<longrightarrow> (\<exists>Q'. Q \<longmapsto>Cal* Q' \<and> (P', Q') \<in> Rel\<^sup>*)"
       and A2: "\<forall>Q'. Q \<longmapsto>Cal* Q' \<longrightarrow> (\<exists>R'. R \<longmapsto>Cal* R' \<and> (Q', R') \<in> Rel\<^sup>*)"
    show "\<forall>P'. P \<longmapsto>Cal* P' \<longrightarrow> (\<exists>R'. R \<longmapsto>Cal* R' \<and> (P', R') \<in> Rel\<^sup>*)"
    proof clarify
      fix P'
      assume "P \<longmapsto>Cal* P'"
      with A1 obtain Q' where A3: "Q \<longmapsto>Cal* Q'" and A4: "(P', Q') \<in> Rel\<^sup>*"
        by blast
      from A3 A2 obtain R' where A5: "R \<longmapsto>Cal* R'" and A6: "(Q', R') \<in> Rel\<^sup>*"
        by blast
      from A4 A6 have "(P', R') \<in> Rel\<^sup>*"
        by simp
      with A5 show "\<exists>R'. R \<longmapsto>Cal* R' \<and> (P', R') \<in> Rel\<^sup>*"
        by blast
    qed
  qed
  moreover have "P \<longmapsto>Cal* P"
    by (rule steps_refl)
  ultimately show ?thesis
    by blast
qed

end