(* Kirstin Peters, TU Berlin, 2015 concerning the reduction semantics and
   Kirstin Peters, University of Augsburg, 2026 for the labelled semantics *)

theory OperationalCorrespondence
  imports SourceTargetRelation
begin

section \<open>Operational Correspondence\<close>

text \<open>We consider different variants of operational correspondence. This criterion consists of a
      completeness and a soundness condition and is often defined with respect to a relation TRel
      on target terms. Operational completeness modulo TRel ensures that an encoding preserves
      source term behaviour modulo TRel by requiring that each sequence of source term steps can be
      mimicked by its translation such that the respective derivatives are related by TRel. The two
      labelled variants differ in the requirements on labels. The former does not require any
      relation between the label used in the source term steps and the one used in the target term
      step, whereas the latter relates these label by the label encoding.\<close>

abbreviation (in encoding) operational_complete :: "('procT \<times> 'procT) set \<Rightarrow> bool" where
  "operational_complete TRel \<equiv>
   \<forall>S S'. S \<longmapsto>Source* S' \<longrightarrow> (\<exists>T. \<lbrakk>S\<rbrakk> \<longmapsto>Target* T \<and> (\<lbrakk>S'\<rbrakk>, T) \<in> TRel)"

abbreviation (in encodingLS) operational_complete :: "('procT \<times> 'procT) set \<Rightarrow> bool" where
  "operational_complete TRel \<equiv>
   \<forall>S \<alpha> S'. S \<midarrow>\<Zcat>\<alpha>\<rightarrow>Source* S' \<longrightarrow> (\<exists>\<beta> T. \<lbrakk>S\<rbrakk> \<midarrow>\<Zcat>\<beta>\<rightarrow>Target* T \<and> (\<lbrakk>S'\<rbrakk>, T) \<in> TRel)"

abbreviation (in encodingLS_encL) operational_complete_encL :: "('procT \<times> 'procT) set \<Rightarrow> bool"
  where
  "operational_complete_encL TRel \<equiv>
   \<forall>S \<alpha> S'. S \<midarrow>\<Zcat>\<alpha>\<rightarrow>Source* S' \<longrightarrow> (\<exists>\<beta> T. \<lbrakk>S\<rbrakk> \<midarrow>\<Zcat>\<beta>\<rightarrow>Target* T \<and> (\<lbrakk>S'\<rbrakk>, T) \<in> TRel \<and> \<lblot>\<alpha>\<rblot> = \<beta>)"

text \<open>We call an encoding strongly operational complete modulo TRel if each source term step has to
      be mimicked by single target term step of its translation.\<close>

abbreviation (in encoding) strongly_operational_complete :: "('procT \<times> 'procT) set \<Rightarrow> bool" where
  "strongly_operational_complete TRel \<equiv>
   \<forall>S S'. S \<longmapsto>Source S' \<longrightarrow> (\<exists>T. \<lbrakk>S\<rbrakk> \<longmapsto>Target T \<and> (\<lbrakk>S'\<rbrakk>, T) \<in> TRel)"

abbreviation (in encodingLS) strongly_operational_complete :: "('procT \<times> 'procT) set \<Rightarrow> bool"
  where
  "strongly_operational_complete TRel \<equiv>
   \<forall>S \<alpha> S'. S \<midarrow>\<alpha>\<rightarrow>Source S' \<longrightarrow> (\<exists>\<beta> T. \<lbrakk>S\<rbrakk> \<midarrow>\<beta>\<rightarrow>Target T \<and> (\<lbrakk>S'\<rbrakk>, T) \<in> TRel)"

abbreviation (in encodingLS_encL) strongly_operational_complete_encL
  :: "('procT \<times> 'procT) set \<Rightarrow> bool" where
  "strongly_operational_complete_encL TRel \<equiv>
   \<forall>S \<alpha> S'. S \<midarrow>\<alpha>\<rightarrow>Source S' \<longrightarrow> (\<exists>\<beta> T. \<lbrakk>S\<rbrakk> \<midarrow>\<beta>\<rightarrow>Target T \<and> (\<lbrakk>S'\<rbrakk>, T) \<in> TRel \<and> \<lblot>\<alpha>\<rblot> = \<beta>)"

text \<open>Operational soundness ensures that the encoding does not introduce new behaviour. An encoding
      is weakly operational sound modulo TRel if each sequence of target term steps is part of the
      translation of a sequence of source term steps such that the derivatives are related by TRel.
      It allows for intermediate states on the translation of source term step that are not the
      result of translating a source term.\<close>

abbreviation (in encoding) weakly_operational_sound :: "('procT \<times> 'procT) set \<Rightarrow> bool" where
  "weakly_operational_sound TRel \<equiv>
   \<forall>S T. \<lbrakk>S\<rbrakk> \<longmapsto>Target* T \<longrightarrow> (\<exists>S' T'. S \<longmapsto>Source* S' \<and> T \<longmapsto>Target* T' \<and> (\<lbrakk>S'\<rbrakk>, T') \<in> TRel)"

abbreviation (in encodingLS) weakly_operational_sound :: "('procT \<times> 'procT) set \<Rightarrow> bool" where
  "weakly_operational_sound TRel \<equiv> \<forall>S \<beta> T. \<lbrakk>S\<rbrakk> \<midarrow>\<Zcat>\<beta>\<rightarrow>Target* T \<longrightarrow>
   (\<exists>S' \<alpha> T'. S \<midarrow>\<Zcat>\<alpha>\<rightarrow>Source* S' \<and> T \<rightarrow>Target* T' \<and> (\<lbrakk>S'\<rbrakk>, T') \<in> TRel)"

abbreviation (in encodingLS_encL) weakly_operational_sound_encL
  :: "('procT \<times> 'procT) set \<Rightarrow> bool" where
  "weakly_operational_sound_encL TRel \<equiv> \<forall>S \<beta> T. \<lbrakk>S\<rbrakk> \<midarrow>\<Zcat>\<beta>\<rightarrow>Target* T \<longrightarrow>
   (\<exists>S' \<alpha> T'. S \<midarrow>\<Zcat>\<alpha>\<rightarrow>Source* S' \<and> T \<rightarrow>Target* T' \<and> (\<lbrakk>S'\<rbrakk>, T') \<in> TRel \<and> \<lblot>\<alpha>\<rblot> = \<beta>)"

text \<open>And encoding is operational sound modulo TRel if each sequence of target term steps is the
      translation of a sequence of source term steps such that the derivatives are related by TRel.
      This criterion does not allow for intermediate states, i.e., does not allow to reach a target
      term from an encoded source term that is not related by TRel to the translation of a source
      term.\<close>

abbreviation (in encoding) operational_sound :: "('procT \<times> 'procT) set \<Rightarrow> bool" where
  "operational_sound TRel \<equiv> \<forall>S T. \<lbrakk>S\<rbrakk> \<longmapsto>Target* T \<longrightarrow> (\<exists>S'. S \<longmapsto>Source* S' \<and> (\<lbrakk>S'\<rbrakk>, T) \<in> TRel)"

abbreviation (in encodingLS) operational_sound :: "('procT \<times> 'procT) set \<Rightarrow> bool" where
  "operational_sound TRel \<equiv>
   \<forall>S \<beta> T. \<lbrakk>S\<rbrakk> \<midarrow>\<Zcat>\<beta>\<rightarrow>Target* T \<longrightarrow> (\<exists>\<alpha> S'. S \<midarrow>\<Zcat>\<alpha>\<rightarrow>Source* S' \<and> (\<lbrakk>S'\<rbrakk>, T) \<in> TRel)"

abbreviation (in encodingLS_encL) operational_sound_encL :: "('procT \<times> 'procT) set \<Rightarrow> bool" where
  "operational_sound_encL TRel \<equiv>
   \<forall>S \<beta> T. \<lbrakk>S\<rbrakk> \<midarrow>\<Zcat>\<beta>\<rightarrow>Target* T \<longrightarrow> (\<exists>\<alpha> S'. S \<midarrow>\<Zcat>\<alpha>\<rightarrow>Source* S' \<and> (\<lbrakk>S'\<rbrakk>, T) \<in> TRel \<and> \<lblot>\<alpha>\<rblot> = \<beta>)"

text \<open>Strong operational soundness modulo TRel is a stricter variant of operational soundness,
      where a single target term step has to be mapped on a single source term step.\<close>

abbreviation (in encoding) strongly_operational_sound :: "('procT \<times> 'procT) set \<Rightarrow> bool" where
  "strongly_operational_sound TRel \<equiv>
   \<forall>S T. \<lbrakk>S\<rbrakk> \<longmapsto>Target T \<longrightarrow> (\<exists>S'. S \<longmapsto>Source S' \<and> (\<lbrakk>S'\<rbrakk>, T) \<in> TRel)"

abbreviation (in encodingLS) strongly_operational_sound :: "('procT \<times> 'procT) set \<Rightarrow> bool" where
  "strongly_operational_sound TRel \<equiv>
   \<forall>S \<beta> T. \<lbrakk>S\<rbrakk> \<midarrow>\<beta>\<rightarrow>Target T \<longrightarrow> (\<exists>\<alpha> S'. S \<midarrow>\<alpha>\<rightarrow>Source S' \<and> (\<lbrakk>S'\<rbrakk>, T) \<in> TRel)"

abbreviation (in encodingLS_encL) strongly_operational_sound_encL
  :: "('procT \<times> 'procT) set \<Rightarrow> bool" where
  "strongly_operational_sound_encL TRel \<equiv>
   \<forall>S \<beta> T. \<lbrakk>S\<rbrakk> \<midarrow>\<beta>\<rightarrow>Target T \<longrightarrow> (\<exists>\<alpha> S'. S \<midarrow>\<alpha>\<rightarrow>Source S' \<and> (\<lbrakk>S'\<rbrakk>, T) \<in> TRel \<and> \<lblot>\<alpha>\<rblot> = \<beta>)"

text \<open>An encoding is weakly operational corresponding modulo TRel if it is operational complete and
      weakly operational sound modulo TRel.\<close>

abbreviation (in encoding) weakly_operational_corresponding :: "('procT \<times> 'procT) set \<Rightarrow> bool"
  where
  "weakly_operational_corresponding TRel \<equiv>
   operational_complete TRel \<and> weakly_operational_sound TRel"

abbreviation (in encodingLS) weakly_operational_corresponding :: "('procT \<times> 'procT) set \<Rightarrow> bool"
  where
  "weakly_operational_corresponding TRel \<equiv>
   operational_complete TRel \<and> weakly_operational_sound TRel"

abbreviation (in encodingLS_encL) weakly_operational_corresponding_encL
  :: "('procT \<times> 'procT) set \<Rightarrow> bool" where
  "weakly_operational_corresponding_encL TRel \<equiv>
   operational_complete_encL TRel \<and> weakly_operational_sound_encL TRel"

text \<open>Operational correspondence modulo TRel is the combination of operational completeness and
      operational soundness modulo TRel.\<close>

abbreviation (in encoding) operational_corresponding :: "('procT \<times> 'procT) set \<Rightarrow> bool" where
  "operational_corresponding TRel \<equiv> operational_complete TRel \<and> operational_sound TRel"

abbreviation (in encodingLS) operational_corresponding :: "('procT \<times> 'procT) set \<Rightarrow> bool" where
  "operational_corresponding TRel \<equiv> operational_complete TRel \<and> operational_sound TRel"

abbreviation (in encodingLS_encL) operational_corresponding_encL
  :: "('procT \<times> 'procT) set \<Rightarrow> bool" where
  "operational_corresponding_encL TRel \<equiv>
   operational_complete_encL TRel \<and> operational_sound_encL TRel"

text \<open>An encoding is strongly operational corresponding modulo TRel if it is strongly operational
      complete and strongly operational sound modulo TRel.\<close>

abbreviation (in encoding) strongly_operational_corresponding :: "('procT \<times> 'procT) set \<Rightarrow> bool"
  where
  "strongly_operational_corresponding TRel \<equiv>
   strongly_operational_complete TRel \<and> strongly_operational_sound TRel"

abbreviation (in encodingLS) strongly_operational_corresponding :: "('procT \<times> 'procT) set \<Rightarrow> bool"
  where
  "strongly_operational_corresponding TRel \<equiv>
   strongly_operational_complete TRel \<and> strongly_operational_sound TRel"

abbreviation (in encodingLS_encL) strongly_operational_corresponding_encL
  :: "('procT \<times> 'procT) set \<Rightarrow> bool" where
  "strongly_operational_corresponding_encL TRel \<equiv>
   strongly_operational_complete_encL TRel \<and> strongly_operational_sound_encL TRel"

subsection \<open>Trivial Operational Correspondence Results\<close>

text \<open>Every encoding is (weakly) operational corresponding modulo the all relation on target
      terms, which is a weak reduction bisimulation.\<close>

lemma (in encoding) operational_correspondence_modulo_all_relation:
  shows "operational_complete {(T1, T2). True}"
    and "weakly_operational_sound {(T1, T2). True}"
    and "operational_sound {(T1, T2). True}"
  using steps_refl[where Cal="Source"] steps_refl[where Cal="Target"]
  by blast+

lemma all_relation_is_weak_reduction_bisimulation:
  fixes Cal :: "'a processCalculus"
  shows "weak_reduction_bisimulation {(a, b). True} Cal"
  using steps_refl[where Cal="Cal"]
  by blast

lemma (in encoding) operational_correspondence_modulo_some_target_relation:
  shows "\<exists>TRel. weakly_operational_corresponding TRel"
    and "\<exists>TRel. operational_corresponding TRel"
    and "\<exists>TRel. weakly_operational_corresponding TRel \<and> weak_reduction_bisimulation TRel Target"
    and "\<exists>TRel. operational_corresponding TRel \<and> weak_reduction_bisimulation TRel Target"
  using operational_correspondence_modulo_all_relation
        all_relation_is_weak_reduction_bisimulation[where Cal="Target"]
  by blast+

text \<open>Also in the labelled case without the requirement on encoded labels very encoding is (weakly)
      operational corresponding modulo the all relation on target terms, but in this case the all
      relation is not a bisumulation. For the case with encoded labels the all relation does not
      imply operational correspondence.\<close>

lemma (in encodingLS) operational_correspondence_modulo_all_relation:
  shows "operational_complete {(T1, T2). True}"
    and "weakly_operational_sound {(T1, T2). True}"
    and "operational_sound {(T1, T2). True}"
proof auto
  fix S \<alpha> S'
  have "\<lbrakk>S\<rbrakk> \<midarrow>\<Zcat>\<tau>-Target\<rightarrow>Target* \<lbrakk>S\<rbrakk>"
    using WTS_refl[of "\<lbrakk>S\<rbrakk>" Target]
    unfolding weakLabelledStep_def
    by simp
  thus "\<exists>\<beta> T'. \<lbrakk>S\<rbrakk> \<midarrow>\<Zcat>\<beta>\<rightarrow>Target* T'"
    by blast
next
  fix S \<beta> T'
  have "S \<midarrow>\<Zcat>\<tau>-Source\<rightarrow>Source* S"
    using WTS_refl[of S Source]
    unfolding weakLabelledStep_def
    by simp
  thus "\<exists>S' \<alpha>. S \<midarrow>\<Zcat>\<alpha>\<rightarrow>Source* S'"
    by blast
next
  fix S \<beta> T'
  have "T' \<rightarrow>Target* T'"
    using WTS_refl[of T' Target]
    by simp
  thus "\<exists>T''. T' \<rightarrow>Target* T''"
    by blast
next
  fix S \<beta> T'
  have "S \<midarrow>\<Zcat>\<tau>-Source\<rightarrow>Source* S"
    using WTS_refl[of S Source]
    unfolding weakLabelledStep_def
    by simp
  thus "\<exists>\<alpha> S'. S \<midarrow>\<Zcat>\<alpha>\<rightarrow>Source* S'"
    by blast
qed

lemma (in encodingLS) operational_correspondence_modulo_some_target_relation:
  shows "\<exists>TRel. weakly_operational_corresponding TRel"
    and "\<exists>TRel. operational_corresponding TRel"
  using operational_correspondence_modulo_all_relation
  by blast+

text \<open>Strong operational correspondence requires that the source can perform a step iff their
      translations can perform a step. Again the all relation is used as an example for a target
      term relation that allows to obtain this result, i.e., again this results holds modulo a weak
      reduction bisimulation.\<close>

lemma (in encoding) strong_operational_correspondence_modulo_some_target_relation:
  shows "(\<exists>TRel. strongly_operational_corresponding TRel)
         = (\<forall>S. (\<exists>S'. S \<longmapsto>Source S') \<longleftrightarrow> (\<exists>T. \<lbrakk>S\<rbrakk> \<longmapsto>Target T))"
    and "(\<exists>TRel. strongly_operational_corresponding TRel
          \<and> weak_reduction_bisimulation TRel Target)
         = (\<forall>S. (\<exists>S'. S \<longmapsto>Source S') \<longleftrightarrow> (\<exists>T. \<lbrakk>S\<rbrakk> \<longmapsto>Target T))"
proof -
  have A1: "\<exists>TRel. strongly_operational_corresponding TRel
            \<Longrightarrow> \<forall>S. (\<exists>S'. S \<longmapsto>Source S') \<longleftrightarrow> (\<exists>T. \<lbrakk>S\<rbrakk> \<longmapsto>Target T)"
    by blast
  moreover have A2: "\<forall>S. (\<exists>S'. S \<longmapsto>Source S') \<longleftrightarrow> (\<exists>T. \<lbrakk>S\<rbrakk> \<longmapsto>Target T)
                     \<Longrightarrow> \<exists>TRel. strongly_operational_corresponding TRel
                          \<and> weak_reduction_bisimulation TRel Target"
  proof -
    assume "\<forall>S. (\<exists>S'. S \<longmapsto>Source S') \<longleftrightarrow> (\<exists>T. \<lbrakk>S\<rbrakk> \<longmapsto>Target T)"
    hence "strongly_operational_corresponding {(T1, T2). True}"
      by simp
    thus "\<exists>TRel. strongly_operational_corresponding TRel
          \<and> weak_reduction_bisimulation TRel Target"
      using all_relation_is_weak_reduction_bisimulation[where Cal="Target"]
      by blast
  qed
  ultimately show "(\<exists>TRel. strongly_operational_corresponding TRel
                    \<and> weak_reduction_bisimulation TRel Target)
                   = (\<forall>S. (\<exists>S'. S \<longmapsto>Source S') \<longleftrightarrow> (\<exists>T. \<lbrakk>S\<rbrakk> \<longmapsto>Target T))"
    by blast
  from A1 A2 show "(\<exists>TRel. strongly_operational_corresponding TRel)
                   = (\<forall>S. (\<exists>S'. S \<longmapsto>Source S') \<longleftrightarrow> (\<exists>T. \<lbrakk>S\<rbrakk> \<longmapsto>Target T))"
    by blast
qed

text \<open>Strong operational correspondence requires that the source can perform a labelled step iff
      their translations can perform a labelled step. Note that this results holds only for the
      variant without a requirement on the labels. It does not hold for encoded labeles. Moreover,
      again the all relation is used in this proof, which is not a bisumulation in the labelled
      case.\<close>

lemma (in encodingLS) strong_operational_correspondence_modulo_some_target_relation:
  shows "(\<exists>TRel. strongly_operational_corresponding TRel) =
         (\<forall>S. (\<exists>\<alpha> S'. S \<midarrow>\<alpha>\<rightarrow>Source S') \<longleftrightarrow> (\<exists>\<beta> T. \<lbrakk>S\<rbrakk> \<midarrow>\<beta>\<rightarrow>Target T))"
proof -
  have "(\<exists>TRel. strongly_operational_corresponding TRel)
        \<Longrightarrow> (\<forall>S. (\<exists>\<alpha> S'. S \<midarrow>\<alpha>\<rightarrow>Source S') \<longleftrightarrow> (\<exists>\<beta> T. \<lbrakk>S\<rbrakk> \<midarrow>\<beta>\<rightarrow>Target T))"
    by blast
  moreover have "(\<forall>S. (\<exists>\<alpha> S'. S \<midarrow>\<alpha>\<rightarrow>Source S') \<longleftrightarrow> (\<exists>\<beta> T. \<lbrakk>S\<rbrakk> \<midarrow>\<beta>\<rightarrow>Target T))
                 \<Longrightarrow> strongly_operational_corresponding {(T1, T2). True}"
    by simp
  ultimately show "(\<exists>TRel. strongly_operational_corresponding TRel)
                   = (\<forall>S. (\<exists>\<alpha> S'. S \<midarrow>\<alpha>\<rightarrow>Source S') \<longleftrightarrow> (\<exists>\<beta> T. \<lbrakk>S\<rbrakk> \<midarrow>\<beta>\<rightarrow>Target T))"
    by blast
qed

subsection \<open>(Strong) Operational Completeness vs (Strong) Simulation\<close>

text \<open>An encoding is operational complete modulo a weak simulation on target terms TRel iff there
      is a relation, like indRelRTPO, that relates at least all source terms to their literal
      translations, includes TRel, and is a weak simulation. We show that also for the labelled
      case without encoded labels we can conclude from the simulation to operational completeness.
      Note, however, that such a weak labelled simulation without encoded labels that relates all
      source terms with their literal translations usually does not exist. And indeed the if and
      if result holds only for the reduction case or the labelled case with encoded labels.\<close>

lemma (in encoding) weak_reduction_simulation_impl_OCom:
  fixes Rel  :: "(('procS, 'procT) Proc \<times> ('procS, 'procT) Proc) set"
    and TRel :: "('procT \<times> 'procT) set"
  assumes A1: "\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel"
      and A2: "\<forall>S T. (SourceTerm S, TargetTerm T) \<in> Rel \<longrightarrow> (\<lbrakk>S\<rbrakk>, T) \<in> TRel\<^sup>*"
      and A3: "weak_reduction_simulation Rel (STCal Source Target)"
    shows "operational_complete (TRel\<^sup>*)"
proof clarify
  fix S S'
  from A1 have "(SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel"
    by simp
  moreover assume "S \<longmapsto>Source* S'"
  hence "SourceTerm S \<longmapsto>(STCal Source Target)* (SourceTerm S')"
    by (simp add: STCal_steps(1))
  ultimately obtain Q' where A5: "TargetTerm (\<lbrakk>S\<rbrakk>) \<longmapsto>(STCal Source Target)* Q'"
                         and A6: "(SourceTerm S', Q') \<in> Rel"
    using A3
    by blast
  from A5 obtain T where A7: "T \<in>T Q'" and A8: "\<lbrakk>S\<rbrakk> \<longmapsto>Target* T"
    by (auto simp add: STCal_steps(2))
  from A2 A6 A7 have "(\<lbrakk>S'\<rbrakk>, T) \<in> TRel\<^sup>*"
    by simp
  with A8 show "\<exists>T. \<lbrakk>S\<rbrakk> \<longmapsto>Target* T \<and> (\<lbrakk>S'\<rbrakk>, T) \<in> TRel\<^sup>*"
    by blast
qed

lemma (in encodingLS) weak_labelled_simulation_impl_OCom:
  fixes Rel  :: "(('procS, 'procT) Proc \<times> ('procS, 'procT) Proc) set"
    and TRel :: "('procT \<times> 'procT) set"
  assumes encoding:   "\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel"
      and target:     "\<forall>S T. (SourceTerm S, TargetTerm T) \<in> Rel \<longrightarrow> (\<lbrakk>S\<rbrakk>, T) \<in> TRel\<^sup>*"
      and simulation: "weak_labelled_simulation Rel (STLCal Source Target)"
    shows "operational_complete (TRel\<^sup>*)"
proof clarify
  fix S \<beta> S'
  obtain \<alpha> where A1: "\<beta> \<in>SL \<langle>SourceTerm S, \<alpha>\<rangle>"
    unfolding getSourceLabel_def
    by blast
  from encoding have A2: "(SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel"
    by simp
  assume "S \<midarrow>\<Zcat>\<beta>\<rightarrow>Source* S'"
  with A1 have "SourceTerm S \<midarrow>\<Zcat>\<alpha>\<rightarrow>(STLCal Source Target)* (SourceTerm S')"
    using STLCal_weakLabelledSteps(1)[of S \<alpha> "SourceTerm S'"]
    by blast
  with simulation A2 obtain Q' where A3: "TargetTerm (\<lbrakk>S\<rbrakk>) \<midarrow>\<Zcat>\<alpha>\<rightarrow>(STLCal Source Target)* Q'"
                                 and A4: "(SourceTerm S', Q') \<in> Rel"
    by blast
  from A1 A3 obtain \<beta>' T where A5: "\<beta>' \<in>TL \<langle>TargetTerm (\<lbrakk>S\<rbrakk>), \<alpha>\<rangle>" and A6: "T \<in>T Q'"
                           and A7: "\<lbrakk>S\<rbrakk> \<midarrow>\<Zcat>\<beta>'\<rightarrow>Target* T"
    using STLCal_weakLabelledSteps(2)[of "\<lbrakk>S\<rbrakk>" \<alpha> Q']
    by blast
  from target A4 A6 have "(\<lbrakk>S'\<rbrakk>, T) \<in> TRel\<^sup>*"
    by simp
  with A7 show "\<exists>\<beta>' T. \<lbrakk>S\<rbrakk> \<midarrow>\<Zcat>\<beta>'\<rightarrow>Target* T \<and> (\<lbrakk>S'\<rbrakk>, T) \<in> TRel\<^sup>*"
    by blast
qed

lemma (in encodingLS_encL) weak_labelled_simulation_encL_impl_OCom:
  fixes Rel  :: "(('procS, 'procT) Proc \<times> ('procS, 'procT) Proc) set"
    and TRel :: "('procT \<times> 'procT) set"
  assumes encoding:   "\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel"
      and target:     "\<forall>S T. (SourceTerm S, TargetTerm T) \<in> Rel \<longrightarrow> (\<lbrakk>S\<rbrakk>, T) \<in> TRel\<^sup>*"
      and simulation: "weak_labelled_simulation_encL Rel"
    shows "operational_complete_encL (TRel\<^sup>*)"
proof clarify
  fix S \<alpha>' S'
  obtain \<alpha> where A1: "\<alpha>' \<in>SL \<langle>SourceTerm S, \<alpha>\<rangle>"
    unfolding getSourceLabel_def
    by blast
  from encoding have A2: "(SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel"
    by simp
  assume "S \<midarrow>\<Zcat>\<alpha>'\<rightarrow>Source* S'"
  with A1 have "SourceTerm S \<midarrow>\<Zcat>\<alpha>\<rightarrow>(STLCal Source Target)* (SourceTerm S')"
    using STLCal_weakLabelledSteps(1)[of S \<alpha> "SourceTerm S'"]
    by blast
  with simulation A2 obtain \<beta> Q' where A3: "TargetTerm (\<lbrakk>S\<rbrakk>) \<midarrow>\<Zcat>\<beta>\<rightarrow>(STLCal Source Target)* Q'"
                                   and A4: "(SourceTerm S', Q') \<in> Rel"
                                   and A5: "\<langle>SourceTerm S, \<alpha>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>TargetTerm (\<lbrakk>S\<rbrakk>), \<beta>\<rangle>"
    by blast
  from A3 obtain \<beta>' T where A6: "\<beta>' \<in>TL \<langle>TargetTerm (\<lbrakk>S\<rbrakk>), \<beta>\<rangle>" and A7: "T \<in>T Q'"
                        and A8: "\<lbrakk>S\<rbrakk> \<midarrow>\<Zcat>\<beta>'\<rightarrow>Target* T"
    using STLCal_weakLabelledSteps(2)[of "\<lbrakk>S\<rbrakk>" \<beta> Q']
    by blast
  from target A4 A7 have A9: "(\<lbrakk>S'\<rbrakk>, T) \<in> TRel\<^sup>*"
    by simp
  from A1 A5 A6 have "\<lblot>\<alpha>'\<rblot> = \<beta>'"
    unfolding related_labels_def encLST_def getSourceLabel_def getTargetLabel_def
    by blast
  with A8 A9 show "\<exists>\<beta>' T. \<lbrakk>S\<rbrakk> \<midarrow>\<Zcat>\<beta>'\<rightarrow>Target* T \<and> (\<lbrakk>S'\<rbrakk>, T) \<in> TRel\<^sup>* \<and> \<lblot>\<alpha>'\<rblot> = \<beta>'"
    by blast
qed

lemma (in encoding) OCom_iff_indRelRTPO_is_weak_reduction_simulation:
  fixes TRel :: "('procT \<times> 'procT) set"
  shows "(operational_complete (TRel\<^sup>*) \<and> weak_reduction_simulation (TRel\<^sup>+) Target)
         = weak_reduction_simulation (indRelRTPO TRel) (STCal Source Target)"
proof (rule iffI, erule conjE)
  assume oc:  "operational_complete (TRel\<^sup>*)"
     and sim: "weak_reduction_simulation (TRel\<^sup>+) Target"
  show "weak_reduction_simulation (indRelRTPO TRel) (STCal Source Target)"
  proof clarify
    fix P Q P'
    assume "P \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> Q" and "P \<longmapsto>(STCal Source Target)* P'"
    thus "\<exists>Q'. Q \<longmapsto>(STCal Source Target)* Q' \<and> P' \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> Q'"
    proof (induct arbitrary: P')
      case (encR S)
      assume "SourceTerm S \<longmapsto>(STCal Source Target)* P'"
      from this obtain S' where A1: "S' \<in>S P'" and A2: "S \<longmapsto>Source* S'"
        by (auto simp add: STCal_steps(1))
      from oc A2 obtain T where A3: "\<lbrakk>S\<rbrakk> \<longmapsto>Target* T" and A4: "(\<lbrakk>S'\<rbrakk>, T) \<in> TRel\<^sup>*"
        by blast
      from A3 have "TargetTerm (\<lbrakk>S\<rbrakk>) \<longmapsto>(STCal Source Target)* (TargetTerm T)"
        by (simp add: STCal_steps(2))
      moreover have "P' \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> TargetTerm T"
      proof -
        from A4 have "\<lbrakk>S'\<rbrakk> = T \<or> (\<lbrakk>S'\<rbrakk>, T) \<in> TRel\<^sup>+"
          using rtrancl_eq_or_trancl[of "\<lbrakk>S'\<rbrakk>" T TRel]
          by blast
        moreover from A1 have A5: "P' \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> TargetTerm (\<lbrakk>S'\<rbrakk>)"
          by (simp add: indRelRTPO.encR)
        hence "\<lbrakk>S'\<rbrakk> = T \<Longrightarrow> P' \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> TargetTerm T"
          by simp
        moreover have "(\<lbrakk>S'\<rbrakk>, T) \<in> TRel\<^sup>+ \<Longrightarrow> P' \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> TargetTerm T"
        proof -
          assume "(\<lbrakk>S'\<rbrakk>, T) \<in> TRel\<^sup>+"
          hence "TargetTerm (\<lbrakk>S'\<rbrakk>) \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> TargetTerm T"
          proof induct
            fix T
            assume "(\<lbrakk>S'\<rbrakk>, T) \<in> TRel"
            thus "TargetTerm (\<lbrakk>S'\<rbrakk>) \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> TargetTerm T"
              by (rule indRelRTPO.target)
          next
            case (step TQ TR)
            assume "TargetTerm (\<lbrakk>S'\<rbrakk>) \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> TargetTerm TQ"
            moreover assume "(TQ, TR) \<in> TRel"
            hence "TargetTerm TQ \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> TargetTerm TR"
              by (rule indRelRTPO.target)
            ultimately show "TargetTerm (\<lbrakk>S'\<rbrakk>) \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> TargetTerm TR"
              by (rule indRelRTPO.trans)
          qed
          with A5 show "P' \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> TargetTerm T"
            by (rule indRelRTPO.trans)
        qed
        ultimately show "P' \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> TargetTerm T"
          by blast
      qed
      ultimately
      show "\<exists>Q'. TargetTerm (\<lbrakk>S\<rbrakk>) \<longmapsto>(STCal Source Target)* Q' \<and> P' \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> Q'"
        by blast
    next
      case (source S)
      then obtain S' where B1: "S' \<in>S P'"
        by (auto simp add: STCal_steps(1))
      hence "P' \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> P'"
        by (simp add: indRelRTPO.source)
      with source show "\<exists>Q'. SourceTerm S \<longmapsto>(STCal Source Target)* Q' \<and> P' \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> Q'"
        by blast
    next
      case (target T1 T2)
      assume "TargetTerm T1 \<longmapsto>(STCal Source Target)* P'"
      from this obtain T1' where C1: "T1' \<in>T P'" and C2: "T1 \<longmapsto>Target* T1'"
        by (auto simp add: STCal_steps(2))
      assume "(T1, T2) \<in> TRel"
      hence "(T1, T2) \<in> TRel\<^sup>+"
        by simp
      with C2 sim obtain T2' where C3: "T2 \<longmapsto>Target* T2'" and C4: "(T1', T2') \<in> TRel\<^sup>+"
        by blast
      from C3 have "TargetTerm T2 \<longmapsto>(STCal Source Target)* (TargetTerm T2')"
        by (simp add: STCal_steps(2))
      moreover from C4 have "TargetTerm T1' \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> TargetTerm T2'"
      proof induct
        fix T2'
        assume "(T1', T2') \<in> TRel"
        thus "TargetTerm T1' \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> TargetTerm T2'"
          by (rule indRelRTPO.target)
      next
        case (step TQ TR)
        assume "TargetTerm T1' \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> TargetTerm TQ"
        moreover assume "(TQ, TR) \<in> TRel"
        hence "TargetTerm TQ \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> TargetTerm TR"
          by (rule indRelRTPO.target)
        ultimately show "TargetTerm T1' \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> TargetTerm TR"
          by (rule indRelRTPO.trans)
      qed
      with C1 have "P' \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> TargetTerm T2'"
        by simp
      ultimately show "\<exists>Q'. TargetTerm T2 \<longmapsto>(STCal Source Target)* Q' \<and> P' \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> Q'"
        by blast
    next
      case (trans P Q R)
      assume "P \<longmapsto>(STCal Source Target)* P'"
         and "\<And>P'. P \<longmapsto>(STCal Source Target)* P'
              \<Longrightarrow> \<exists>Q'. Q \<longmapsto>(STCal Source Target)* Q' \<and> P' \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> Q'"
      from this obtain Q' where D1: "Q \<longmapsto>(STCal Source Target)* Q'" and D2: "P' \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> Q'"
        by blast
      assume "\<And>Q'. Q \<longmapsto>(STCal Source Target)* Q'
              \<Longrightarrow> \<exists>R'. R \<longmapsto>(STCal Source Target)* R' \<and> Q' \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> R'"
      with D1 obtain R' where D3: "R \<longmapsto>(STCal Source Target)* R'" and D4: "Q' \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> R'"
        by blast
      from D2 D4 have "P' \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> R'"
        by (rule indRelRTPO.trans)
      with D3 show "\<exists>R'. R \<longmapsto>(STCal Source Target)* R' \<and> P' \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> R'"
        by blast
    qed
  qed
next
  have "\<forall>S. SourceTerm S \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> TargetTerm (\<lbrakk>S\<rbrakk>)"
    by (simp add: indRelRTPO.encR)
  moreover have "\<forall>S T. SourceTerm S \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> TargetTerm T \<longrightarrow> (\<lbrakk>S\<rbrakk>, T) \<in> TRel\<^sup>*"
    using indRelRTPO_to_TRel(2)[where TRel="TRel"] trans_closure_of_TRel_refl_cond
    by simp
  moreover assume sim: "weak_reduction_simulation (indRelRTPO TRel) (STCal Source Target)"
  ultimately have "operational_complete (TRel\<^sup>*)"
    using weak_reduction_simulation_impl_OCom[where Rel="indRelRTPO TRel" and TRel="TRel"]
    by simp
  moreover from sim have "weak_reduction_simulation (TRel\<^sup>+) Target"
    using indRelRTPO_impl_TRel_is_weak_reduction_simulation[where TRel="TRel"]
    by simp
  ultimately show "operational_complete (TRel\<^sup>*) \<and> weak_reduction_simulation (TRel\<^sup>+) Target"
    by simp
qed

lemma (in encodingLS_encL) OCom_iff_indRelRTPO_is_weak_labelled_simulation_encL:
  fixes TRel :: "('procT \<times> 'procT) set"
  shows "(operational_complete_encL (TRel\<^sup>*) \<and> weak_labelled_simulation (TRel\<^sup>+) Target) =
         (weak_labelled_simulation_encL (indRelRTPO TRel))"
proof (rule iffI, erule conjE)
  assume oc: "operational_complete_encL (TRel\<^sup>*)" and sim: "weak_labelled_simulation (TRel\<^sup>+) Target"
  show "weak_labelled_simulation_encL (indRelRTPO TRel)"
  proof auto
    fix P Q \<alpha> P'
    assume "P \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> Q" and "P \<midarrow>\<Zcat>\<alpha>\<rightarrow>(STLCal Source Target)* P'"
    thus "\<exists>\<beta> Q'. Q \<midarrow>\<Zcat>\<beta>\<rightarrow>(STLCal Source Target)* Q' \<and> P' \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> Q' \<and> \<langle>P, \<alpha>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>Q, \<beta>\<rangle>"
    proof (induct arbitrary: \<alpha> P')
      case (encR S)
      assume "SourceTerm S \<midarrow>\<Zcat>\<alpha>\<rightarrow>(STLCal Source Target)* P'"
      from this obtain \<alpha>' S' where A1: "\<alpha>' \<in>SL \<langle>SourceTerm S, \<alpha>\<rangle>" and A2: "S' \<in>S P'"
                               and A3: "S \<midarrow>\<Zcat>\<alpha>'\<rightarrow>Source* S'"
        using STLCal_weakLabelledSteps(1)[of S \<alpha> P']
        by blast
      from oc A3 obtain \<beta>' T where A4: "\<lbrakk>S\<rbrakk> \<midarrow>\<Zcat>\<beta>'\<rightarrow>Target* T" and A5: "(\<lbrakk>S'\<rbrakk>, T) \<in> TRel\<^sup>*"
                               and A6: "\<lblot>\<alpha>'\<rblot> = \<beta>'"
        by blast
      obtain \<beta> where A7: "\<beta>' \<in>TL \<langle>TargetTerm (\<lbrakk>S\<rbrakk>), \<beta>\<rangle>"
        unfolding getTargetLabel_def
        by blast
      with A4 have A8: "TargetTerm (\<lbrakk>S\<rbrakk>) \<midarrow>\<Zcat>\<beta>\<rightarrow>(STLCal Source Target)* (TargetTerm T)"
        using STLCal_weakLabelledSteps(2)[of "\<lbrakk>S\<rbrakk>" \<beta> "TargetTerm T"]
        by blast
      moreover have "P' \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> TargetTerm T"
      proof -
        from A5 have "\<lbrakk>S'\<rbrakk> = T \<or> (\<lbrakk>S'\<rbrakk>, T) \<in> TRel\<^sup>+"
          using rtrancl_eq_or_trancl[of "\<lbrakk>S'\<rbrakk>" T TRel]
          by blast
        moreover from A2 have B: "P' \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> TargetTerm (\<lbrakk>S'\<rbrakk>)"
          by (simp add: indRelRTPO.encR)
        hence "\<lbrakk>S'\<rbrakk> = T \<Longrightarrow> P' \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> TargetTerm T"
          by simp
        moreover have "(\<lbrakk>S'\<rbrakk>, T) \<in> TRel\<^sup>+ \<Longrightarrow> P' \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> TargetTerm T"
        proof -
          assume "(\<lbrakk>S'\<rbrakk>, T) \<in> TRel\<^sup>+"
          hence "TargetTerm (\<lbrakk>S'\<rbrakk>) \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> TargetTerm T"
          proof induct
            fix T
            assume "(\<lbrakk>S'\<rbrakk>, T) \<in> TRel"
            thus "TargetTerm (\<lbrakk>S'\<rbrakk>) \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> TargetTerm T"
              by (rule indRelRTPO.target)
          next
            case (step TQ TR)
            assume "TargetTerm (\<lbrakk>S'\<rbrakk>) \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> TargetTerm TQ"
            moreover assume "(TQ, TR) \<in> TRel"
            hence "TargetTerm TQ \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> TargetTerm TR"
              by (rule indRelRTPO.target)
            ultimately show "TargetTerm (\<lbrakk>S'\<rbrakk>) \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> TargetTerm TR"
              by (rule indRelRTPO.trans)
          qed
          with B show "P' \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> TargetTerm T"
            by (rule indRelRTPO.trans)
        qed
        ultimately show "P' \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> TargetTerm T"
          by blast
      qed
      moreover from A1 A6 A7 have "\<langle>SourceTerm S, \<alpha>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>TargetTerm (\<lbrakk>S\<rbrakk>), \<beta>\<rangle>"
        unfolding related_labels_def encLST_def
        by blast
      ultimately show "\<exists>\<beta> Q'. TargetTerm (\<lbrakk>S\<rbrakk>) \<midarrow>\<Zcat>\<beta>\<rightarrow>(STLCal Source Target)* Q' \<and>
                       P' \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> Q' \<and> \<langle>SourceTerm S, \<alpha>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>TargetTerm (\<lbrakk>S\<rbrakk>), \<beta>\<rangle>"
        by blast
    next
      case (source S)
      assume A1: "SourceTerm S \<midarrow>\<Zcat>\<alpha>\<rightarrow>(STLCal Source Target)* P'"
      then obtain S' where "S' \<in>S P'"
        using STLCal_weakLabelledSteps(1)[of S \<alpha> P']
        by blast
      hence A2: "P' \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> P'"
        by (simp add: indRelRTPO.source)
      have "\<langle>SourceTerm S, \<alpha>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>SourceTerm S, \<alpha>\<rangle>"
        unfolding related_labels_def
        by simp
      with A1 A2 show "\<exists>\<beta> Q'. SourceTerm S \<midarrow>\<Zcat>\<beta>\<rightarrow>(STLCal Source Target)* Q' \<and> P' \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> Q' \<and>
                       \<langle>SourceTerm S, \<alpha>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>SourceTerm S, \<beta>\<rangle>"
        by blast
    next
      case (target T1 T2)
      assume "TargetTerm T1 \<midarrow>\<Zcat>\<alpha>\<rightarrow>(STLCal Source Target)* P'"
      from this obtain \<alpha>' T1' where C1: "\<alpha>' \<in>TL \<langle>TargetTerm T1, \<alpha>\<rangle>" and C2: "T1' \<in>T P'"
                                and C3: "T1 \<midarrow>\<Zcat>\<alpha>'\<rightarrow>Target* T1'"
        using STLCal_weakLabelledSteps(2)[of T1 \<alpha> P']
        by blast
      assume "(T1, T2) \<in> TRel"
      hence "(T1, T2) \<in> TRel\<^sup>+"
        by simp
      with C3 sim obtain T2' where C4: "T2 \<midarrow>\<Zcat>\<alpha>'\<rightarrow>Target* T2'" and C5: "(T1', T2') \<in> TRel\<^sup>+"
        by blast
      from C1 C4 have "TargetTerm T2 \<midarrow>\<Zcat>\<alpha>\<rightarrow>(STLCal Source Target)* (TargetTerm T2')"
        using STLCal_weakLabelledSteps(2)[of T2 \<alpha> "TargetTerm T2'"]
        unfolding getTargetLabel_def
        by blast
      moreover from C5 have "TargetTerm T1' \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> TargetTerm T2'"
      proof induct
        fix T2'
        assume "(T1', T2') \<in> TRel"
        thus "TargetTerm T1' \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> TargetTerm T2'"
          by (rule indRelRTPO.target)
      next
        case (step TQ TR)
        assume "TargetTerm T1' \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> TargetTerm TQ"
        moreover assume "(TQ, TR) \<in> TRel"
        hence "TargetTerm TQ \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> TargetTerm TR"
          by (rule indRelRTPO.target)
        ultimately show "TargetTerm T1' \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> TargetTerm TR"
          by (rule indRelRTPO.trans)
      qed
      with C2 have "P' \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> TargetTerm T2'"
        by simp
      moreover have "\<langle>TargetTerm T1, \<alpha>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>TargetTerm T2, \<alpha>\<rangle>"
        unfolding related_labels_def
        by simp
      ultimately show "\<exists>\<beta> Q'. TargetTerm T2 \<midarrow>\<Zcat>\<beta>\<rightarrow>(STLCal Source Target)* Q' \<and> P' \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> Q' \<and>
                       \<langle>TargetTerm T1, \<alpha>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>TargetTerm T2, \<beta>\<rangle>"
        by blast
    next
      case (trans P Q R)
      assume "P \<midarrow>\<Zcat>\<alpha>\<rightarrow>(STLCal Source Target)* P'"
         and "\<And>\<alpha> P'. P \<midarrow>\<Zcat>\<alpha>\<rightarrow>(STLCal Source Target)* P' \<Longrightarrow>
              \<exists>\<beta> Q'. Q \<midarrow>\<Zcat>\<beta>\<rightarrow>(STLCal Source Target)* Q' \<and> P' \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> Q' \<and> \<langle>P, \<alpha>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>Q, \<beta>\<rangle>"
      then obtain \<beta> Q' where A1: "Q \<midarrow>\<Zcat>\<beta>\<rightarrow>(STLCal Source Target)* Q'" and A2: "P' \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> Q'"
                         and A3: "\<langle>P, \<alpha>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>Q, \<beta>\<rangle>"
        by blast
      assume "\<And>\<alpha> Q'. Q \<midarrow>\<Zcat>\<alpha>\<rightarrow>(STLCal Source Target)* Q' \<Longrightarrow>
              \<exists>\<beta> R'. R \<midarrow>\<Zcat>\<beta>\<rightarrow>(STLCal Source Target)* R' \<and> Q' \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> R' \<and> \<langle>Q, \<alpha>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>R, \<beta>\<rangle>"
      with A1 obtain \<gamma> R' where A4: "R \<midarrow>\<Zcat>\<gamma>\<rightarrow>(STLCal Source Target)* R'"
                            and A5: "Q' \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> R'" and A6: "\<langle>Q, \<beta>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>R, \<gamma>\<rangle>"
        by blast
      from A2 A5 have A7: "P' \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> R'"
        by (rule indRelRTPO.trans)
      assume "P \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> Q" and "Q \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> R"
      with A3 A6 have "\<langle>P, \<alpha>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>R, \<gamma>\<rangle>"
        using related_labels_trans_no_T_to_S[of P \<alpha> Q \<beta> R \<gamma>] indRelRTPO_to_TRel(3)[of P Q TRel]
              indRelRTPO_to_TRel(3)[of Q R TRel]
        by blast
      with A4 A7
      show "\<exists>\<gamma> R'. R \<midarrow>\<Zcat>\<gamma>\<rightarrow>(STLCal Source Target)* R' \<and> P' \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> R' \<and> \<langle>P, \<alpha>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>R, \<gamma>\<rangle>"
        by blast
    qed
  qed
next
  have "\<forall>S. SourceTerm S \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> TargetTerm (\<lbrakk>S\<rbrakk>)"
    by (simp add: indRelRTPO.encR)
  moreover have "\<forall>S T. SourceTerm S \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> TargetTerm T \<longrightarrow> (\<lbrakk>S\<rbrakk>, T) \<in> TRel\<^sup>*"
    using indRelRTPO_to_TRel(2)[where TRel="TRel"] trans_closure_of_TRel_refl_cond
    by simp
  moreover assume sim: "weak_labelled_simulation_encL (indRelRTPO TRel)"
  ultimately have "operational_complete_encL (TRel\<^sup>*)"
    using weak_labelled_simulation_encL_impl_OCom[of "indRelRTPO TRel" "TRel"]
    by simp
  moreover from sim have "weak_labelled_simulation (TRel\<^sup>+) Target"
    using indRelRTPO_impl_TRel_is_weak_labelled_simulation_encL[of "TRel"]
    by simp
  ultimately show "operational_complete_encL (TRel\<^sup>*) \<and> weak_labelled_simulation (TRel\<^sup>+) Target"
    by simp
qed

lemma (in encoding) OCom_iff_weak_reduction_simulation:
  fixes TRel :: "('procT \<times> 'procT) set"
  shows "(operational_complete (TRel\<^sup>*)
         \<and> weak_reduction_simulation (TRel\<^sup>+) Target)
         = (\<exists>Rel. (\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel)
            \<and> (\<forall>T1 T2. (T1, T2) \<in> TRel \<longrightarrow> (TargetTerm T1, TargetTerm T2) \<in> Rel)
            \<and> (\<forall>T1 T2. (TargetTerm T1, TargetTerm T2) \<in> Rel \<longrightarrow> (T1, T2) \<in> TRel\<^sup>+)
            \<and> (\<forall>S T. (SourceTerm S, TargetTerm T) \<in> Rel \<longrightarrow> (\<lbrakk>S\<rbrakk>, T) \<in> TRel\<^sup>*)
            \<and> weak_reduction_simulation Rel (STCal Source Target))"
proof (rule iffI, erule conjE)
  have "\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> indRelRTPO TRel"
    by (simp add: indRelRTPO.encR)
  moreover have "\<forall>T1 T2. (T1, T2) \<in> TRel \<longrightarrow> TargetTerm T1 \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> TargetTerm T2"
    by (simp add: indRelRTPO.target)
  moreover have "\<forall>T1 T2. TargetTerm T1 \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> TargetTerm T2 \<longrightarrow> (T1, T2) \<in> TRel\<^sup>+"
      using indRelRTPO_to_TRel(4)[where TRel="TRel"]
    by simp
  moreover have "\<forall>S T. SourceTerm S \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> TargetTerm T \<longrightarrow> (\<lbrakk>S\<rbrakk>, T) \<in> TRel\<^sup>*"
      using indRelRTPO_to_TRel(2)[where TRel="TRel"] trans_closure_of_TRel_refl_cond
    by simp
  moreover assume "operational_complete (TRel\<^sup>*)"
              and "weak_reduction_simulation (TRel\<^sup>+) Target"
  hence "weak_reduction_simulation (indRelRTPO TRel) (STCal Source Target)"
      using OCom_iff_indRelRTPO_is_weak_reduction_simulation[where TRel="TRel"]
    by simp
  ultimately show "\<exists>Rel. (\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel)
                   \<and> (\<forall>T1 T2. (T1, T2) \<in> TRel \<longrightarrow> (TargetTerm T1, TargetTerm T2) \<in> Rel)
                   \<and> (\<forall>T1 T2. (TargetTerm T1, TargetTerm T2) \<in> Rel \<longrightarrow> (T1, T2) \<in> TRel\<^sup>+)
                   \<and> (\<forall>S T. (SourceTerm S, TargetTerm T) \<in> Rel \<longrightarrow> (\<lbrakk>S\<rbrakk>, T) \<in> TRel\<^sup>*)
                   \<and> weak_reduction_simulation Rel (STCal Source Target)"
    by blast
next
  assume "\<exists>Rel. (\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel)
          \<and> (\<forall>T1 T2. (T1, T2) \<in> TRel \<longrightarrow> (TargetTerm T1, TargetTerm T2) \<in> Rel)
          \<and> (\<forall>T1 T2. (TargetTerm T1, TargetTerm T2) \<in> Rel \<longrightarrow> (T1, T2) \<in> TRel\<^sup>+)
          \<and> (\<forall>S T. (SourceTerm S, TargetTerm T) \<in> Rel \<longrightarrow> (\<lbrakk>S\<rbrakk>, T) \<in> TRel\<^sup>*)
          \<and> weak_reduction_simulation Rel (STCal Source Target)"
  from this obtain Rel where A1: "\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel"
    and A2: "\<forall>T1 T2. (T1, T2) \<in> TRel \<longrightarrow> (TargetTerm T1, TargetTerm T2) \<in> Rel"
    and A3: "\<forall>T1 T2. (TargetTerm T1, TargetTerm T2) \<in> Rel \<longrightarrow> (T1, T2) \<in> TRel\<^sup>+"
    and A4: "\<forall>S T. (SourceTerm S, TargetTerm T) \<in> Rel \<longrightarrow> (\<lbrakk>S\<rbrakk>, T) \<in> TRel\<^sup>*"
    and A5: "weak_reduction_simulation Rel (STCal Source Target)"
    by blast
  from A1 A4 A5 have "operational_complete (TRel\<^sup>*)"
      using weak_reduction_simulation_impl_OCom[where Rel="Rel" and TRel="TRel"]
    by simp
  moreover from A2 A3 A5 have "weak_reduction_simulation (TRel\<^sup>+) Target"
      using rel_with_target_impl_transC_TRel_is_weak_reduction_simulation[where Rel="Rel" and
             TRel="TRel"]
    by simp
  ultimately show "operational_complete (TRel\<^sup>*)
                   \<and> weak_reduction_simulation (TRel\<^sup>+) Target"
    by simp
qed

lemma (in encodingLS_encL) OCom_iff_weak_labelled_simulation_encL:
  fixes TRel :: "('procT \<times> 'procT) set"
  shows "(operational_complete_encL (TRel\<^sup>*) \<and> weak_labelled_simulation (TRel\<^sup>+) Target)
         = (\<exists>Rel. (\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel)
            \<and> (\<forall>T1 T2. (T1, T2) \<in> TRel \<longrightarrow> (TargetTerm T1, TargetTerm T2) \<in> Rel)
            \<and> (\<forall>T1 T2. (TargetTerm T1, TargetTerm T2) \<in> Rel \<longrightarrow> (T1, T2) \<in> TRel\<^sup>+)
            \<and> (\<forall>S T. (SourceTerm S, TargetTerm T) \<in> Rel \<longrightarrow> (\<lbrakk>S\<rbrakk>, T) \<in> TRel\<^sup>*)
            \<and> weak_labelled_simulation_encL Rel)"
proof (rule iffI, erule conjE)
  have "\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> indRelRTPO TRel"
    by (simp add: indRelRTPO.encR)
  moreover have "\<forall>T1 T2. (T1, T2) \<in> TRel \<longrightarrow> TargetTerm T1 \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> TargetTerm T2"
    by (simp add: indRelRTPO.target)
  moreover have "\<forall>T1 T2. TargetTerm T1 \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> TargetTerm T2 \<longrightarrow> (T1, T2) \<in> TRel\<^sup>+"
      using indRelRTPO_to_TRel(4)[where TRel="TRel"]
    by simp
  moreover have "\<forall>S T. SourceTerm S \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> TargetTerm T \<longrightarrow> (\<lbrakk>S\<rbrakk>, T) \<in> TRel\<^sup>*"
      using indRelRTPO_to_TRel(2)[where TRel="TRel"] trans_closure_of_TRel_refl_cond
    by simp
  moreover assume "operational_complete_encL (TRel\<^sup>*)" and "weak_labelled_simulation (TRel\<^sup>+) Target"
  hence "weak_labelled_simulation_encL (indRelRTPO TRel)"
      using OCom_iff_indRelRTPO_is_weak_labelled_simulation_encL[where TRel="TRel"]
    by simp
  ultimately show "\<exists>Rel. (\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel)
                   \<and> (\<forall>T1 T2. (T1, T2) \<in> TRel \<longrightarrow> (TargetTerm T1, TargetTerm T2) \<in> Rel)
                   \<and> (\<forall>T1 T2. (TargetTerm T1, TargetTerm T2) \<in> Rel \<longrightarrow> (T1, T2) \<in> TRel\<^sup>+)
                   \<and> (\<forall>S T. (SourceTerm S, TargetTerm T) \<in> Rel \<longrightarrow> (\<lbrakk>S\<rbrakk>, T) \<in> TRel\<^sup>*)
                   \<and> weak_labelled_simulation_encL Rel"
    by blast
next
  assume "\<exists>Rel. (\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel)
          \<and> (\<forall>T1 T2. (T1, T2) \<in> TRel \<longrightarrow> (TargetTerm T1, TargetTerm T2) \<in> Rel)
          \<and> (\<forall>T1 T2. (TargetTerm T1, TargetTerm T2) \<in> Rel \<longrightarrow> (T1, T2) \<in> TRel\<^sup>+)
          \<and> (\<forall>S T. (SourceTerm S, TargetTerm T) \<in> Rel \<longrightarrow> (\<lbrakk>S\<rbrakk>, T) \<in> TRel\<^sup>*)
          \<and> weak_labelled_simulation_encL Rel"
  from this obtain Rel where A1: "\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel"
    and A2: "\<forall>T1 T2. (T1, T2) \<in> TRel \<longrightarrow> (TargetTerm T1, TargetTerm T2) \<in> Rel"
    and A3: "\<forall>T1 T2. (TargetTerm T1, TargetTerm T2) \<in> Rel \<longrightarrow> (T1, T2) \<in> TRel\<^sup>+"
    and A4: "\<forall>S T. (SourceTerm S, TargetTerm T) \<in> Rel \<longrightarrow> (\<lbrakk>S\<rbrakk>, T) \<in> TRel\<^sup>*"
    and A5: "weak_labelled_simulation_encL Rel"
    by blast
  from A1 A4 A5 have "operational_complete_encL (TRel\<^sup>*)"
    using weak_labelled_simulation_encL_impl_OCom[where Rel="Rel" and TRel="TRel"]
    by simp
  moreover from A2 A3 A5 have "weak_labelled_simulation (TRel\<^sup>+) Target"
    using rel_with_target_impl_transC_TRel_is_weak_labelled_simulation_encL[where Rel="Rel" and
            TRel="TRel"]
    by simp
  ultimately show "operational_complete_encL (TRel\<^sup>*) \<and> weak_labelled_simulation (TRel\<^sup>+) Target"
    by simp
qed

text \<open>An encoding is strongly operational complete modulo a strong simulation on target terms TRel
      iff there is a relation, like indRelRTPO, that relates at least all source terms to their
      literal translations, includes TRel, and is a strong simulation. As for the weak version
      above this holds for the reduction case and the labelled case with encoded labels.\<close>

lemma (in encoding) strong_reduction_simulation_impl_SOCom:
  fixes Rel  :: "(('procS, 'procT) Proc \<times> ('procS, 'procT) Proc) set"
    and TRel :: "('procT \<times> 'procT) set"
  assumes rel:  "\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel"
      and trel: "\<forall>S T. (SourceTerm S, TargetTerm T) \<in> Rel \<longrightarrow> (\<lbrakk>S\<rbrakk>, T) \<in> TRel\<^sup>*"
      and sim:  "strong_reduction_simulation Rel (STCal Source Target)"
    shows "strongly_operational_complete (TRel\<^sup>*)"
proof clarify
  fix S S'
  from rel have "(SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel"
    by simp
  moreover assume "S \<longmapsto>Source S'"
  hence "SourceTerm S \<longmapsto>(STCal Source Target) (SourceTerm S')"
    by (simp add: STCal_step(1))
  ultimately obtain Q' where A1: "TargetTerm (\<lbrakk>S\<rbrakk>) \<longmapsto>(STCal Source Target) Q'"
                         and A2: "(SourceTerm S', Q') \<in> Rel"
    using sim
    by blast
  from A1 obtain T where A3: "T \<in>T Q'" and A4: "\<lbrakk>S\<rbrakk> \<longmapsto>Target T"
    by (auto simp add: STCal_step(2))
  from trel A2 A3 have "(\<lbrakk>S'\<rbrakk>, T) \<in> TRel\<^sup>*"
    by simp
  with A4 show "\<exists>T. \<lbrakk>S\<rbrakk> \<longmapsto>Target T \<and> (\<lbrakk>S'\<rbrakk>, T) \<in> TRel\<^sup>*"
    by blast
qed

lemma (in encodingLS) strong_labelled_simulation_impl_SOCom:
  fixes Rel  :: "(('procS, 'procT) Proc \<times> ('procS, 'procT) Proc) set"
    and TRel :: "('procT \<times> 'procT) set"
  assumes rel:  "\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel"
      and trel: "\<forall>S T. (SourceTerm S, TargetTerm T) \<in> Rel \<longrightarrow> (\<lbrakk>S\<rbrakk>, T) \<in> TRel\<^sup>*"
      and sim:  "strong_labelled_simulation Rel (STLCal Source Target)"
    shows "strongly_operational_complete (TRel\<^sup>*)"
proof clarify
  fix S \<alpha> S'
  obtain \<alpha>' where A1: "\<alpha> \<in>SL \<langle>SourceTerm S, \<alpha>'\<rangle>"
    unfolding getSourceLabel_def
    by blast
  from rel have "(SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel"
    by simp
  moreover assume "S \<midarrow>\<alpha>\<rightarrow>Source S'"
  with A1 have "SourceTerm S \<midarrow>\<alpha>'\<rightarrow>(STLCal Source Target) (SourceTerm S')"
    using STLCal_labelledStep(1)[of S \<alpha>' "SourceTerm S'"]
    by blast
  ultimately obtain \<beta>' Q' where A2: "TargetTerm (\<lbrakk>S\<rbrakk>) \<midarrow>\<beta>'\<rightarrow>(STLCal Source Target) Q'"
                            and A3: "(SourceTerm S', Q') \<in> Rel"
    using sim
    by blast
  from A2 obtain \<beta> T where A4: "T \<in>T Q'" and A5: "\<lbrakk>S\<rbrakk> \<midarrow>\<beta>\<rightarrow>Target T"
                       and A6: "\<beta> \<in>TL \<langle>TargetTerm (\<lbrakk>S\<rbrakk>), \<beta>'\<rangle>"
    using STLCal_labelledStep(2)[of "\<lbrakk>S\<rbrakk>" \<beta>' Q']
    by blast
  from trel A3 A4 have "(\<lbrakk>S'\<rbrakk>, T) \<in> TRel\<^sup>*"
    by simp
  with A5 show "\<exists>\<beta> T. \<lbrakk>S\<rbrakk> \<midarrow>\<beta>\<rightarrow>Target T \<and> (\<lbrakk>S'\<rbrakk>, T) \<in> TRel\<^sup>*"
    by blast
qed

lemma (in encodingLS_encL) strong_labelled_simulation_impl_SOCom_encL:
  fixes Rel  :: "(('procS, 'procT) Proc \<times> ('procS, 'procT) Proc) set"
    and TRel :: "('procT \<times> 'procT) set"
  assumes rel:  "\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel"
      and trel: "\<forall>S T. (SourceTerm S, TargetTerm T) \<in> Rel \<longrightarrow> (\<lbrakk>S\<rbrakk>, T) \<in> TRel\<^sup>*"
      and sim:  "strong_labelled_simulation_encL Rel"
    shows "strongly_operational_complete_encL (TRel\<^sup>*)"
proof clarify
  fix S \<alpha> S'
  obtain \<alpha>' where A1: "\<alpha> \<in>SL \<langle>SourceTerm S, \<alpha>'\<rangle>"
    unfolding getSourceLabel_def
    by blast
  from rel have "(SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel"
    by simp
  moreover assume "S \<midarrow>\<alpha>\<rightarrow>Source S'"
  with A1 have "SourceTerm S \<midarrow>\<alpha>'\<rightarrow>(STLCal Source Target) (SourceTerm S')"
    using STLCal_labelledStep(1)[of S \<alpha>' "SourceTerm S'"]
    by blast
  ultimately obtain \<beta>' Q' where A2: "TargetTerm (\<lbrakk>S\<rbrakk>) \<midarrow>\<beta>'\<rightarrow>(STLCal Source Target) Q'"
                            and A3: "(SourceTerm S', Q') \<in> Rel"
                            and A4: "\<langle>SourceTerm S, \<alpha>'\<rangle> \<equiv>\<lparr>\<rparr> \<langle>TargetTerm (\<lbrakk>S\<rbrakk>), \<beta>'\<rangle>"
    using sim
    by blast
  from A2 obtain \<beta> T where A5: "T \<in>T Q'" and A6: "\<lbrakk>S\<rbrakk> \<midarrow>\<beta>\<rightarrow>Target T"
                       and A7: "\<beta> \<in>TL \<langle>TargetTerm (\<lbrakk>S\<rbrakk>), \<beta>'\<rangle>"
    using STLCal_labelledStep(2)[of "\<lbrakk>S\<rbrakk>" \<beta>' Q']
    by blast
  from trel A3 A5 have A8: "(\<lbrakk>S'\<rbrakk>, T) \<in> TRel\<^sup>*"
    by simp
  from A1 A4 A7 have "\<lblot>\<alpha>\<rblot> = \<beta>"
    unfolding related_labels_def encLST_def getSourceLabel_def getTargetLabel_def
    by auto
  with A6 A8 show "\<exists>\<beta> T. \<lbrakk>S\<rbrakk> \<midarrow>\<beta>\<rightarrow>Target T \<and> (\<lbrakk>S'\<rbrakk>, T) \<in> TRel\<^sup>* \<and> \<lblot>\<alpha>\<rblot> = \<beta>"
    by blast
qed

lemma (in encoding) SOCom_iff_indRelRTPO_is_strong_reduction_simulation:
  fixes TRel :: "('procT \<times> 'procT) set"
  shows "(strongly_operational_complete (TRel\<^sup>*)
         \<and> strong_reduction_simulation (TRel\<^sup>+) Target)
         = strong_reduction_simulation (indRelRTPO TRel) (STCal Source Target)"
proof (rule iffI, erule conjE)
  assume soc: "strongly_operational_complete (TRel\<^sup>*)"
     and sim: "strong_reduction_simulation (TRel\<^sup>+) Target"
  show "strong_reduction_simulation (indRelRTPO TRel) (STCal Source Target)"
  proof clarify
    fix P Q P'
    assume "P \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> Q" and "P \<longmapsto>(STCal Source Target) P'"
    thus "\<exists>Q'. Q \<longmapsto>(STCal Source Target) Q' \<and> P' \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> Q'"
    proof (induct arbitrary: P')
      case (encR S)
      assume "SourceTerm S \<longmapsto>(STCal Source Target) P'"
      from this obtain S' where A1: "S' \<in>S P'" and A2: "S \<longmapsto>Source S'"
        by (auto simp add: STCal_step(1))
      from soc A2 obtain T where A3: "\<lbrakk>S\<rbrakk> \<longmapsto>Target T" and A4: "(\<lbrakk>S'\<rbrakk>, T) \<in> TRel\<^sup>*"
        by blast
      from A3 have "TargetTerm (\<lbrakk>S\<rbrakk>) \<longmapsto>(STCal Source Target) (TargetTerm T)"
        by (simp add: STCal_step(2))
      moreover have "P' \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> TargetTerm T"
      proof -
        from A4 have "\<lbrakk>S'\<rbrakk> = T \<or> (\<lbrakk>S'\<rbrakk>, T) \<in> TRel\<^sup>+"
            using rtrancl_eq_or_trancl[of "\<lbrakk>S'\<rbrakk>" T TRel]
          by blast
        moreover from A1 have A5: "P' \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> TargetTerm (\<lbrakk>S'\<rbrakk>)"
          by (simp add: indRelRTPO.encR)
        hence "\<lbrakk>S'\<rbrakk> = T \<Longrightarrow> P' \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> TargetTerm T"
          by simp
        moreover have "(\<lbrakk>S'\<rbrakk>, T) \<in> TRel\<^sup>+ \<Longrightarrow> P' \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> TargetTerm T"
        proof -
          assume "(\<lbrakk>S'\<rbrakk>, T) \<in> TRel\<^sup>+"
          hence "TargetTerm (\<lbrakk>S'\<rbrakk>) \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> TargetTerm T"
          proof induct
            fix TQ
            assume "(\<lbrakk>S'\<rbrakk>, TQ) \<in> TRel"
            thus "TargetTerm (\<lbrakk>S'\<rbrakk>) \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> TargetTerm TQ"
              by (rule indRelRTPO.target)
          next
            case (step TQ TR)
            assume "TargetTerm (\<lbrakk>S'\<rbrakk>) \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> TargetTerm TQ"
            moreover assume "(TQ, TR) \<in> TRel"
            hence "TargetTerm TQ \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> TargetTerm TR"
              by (rule indRelRTPO.target)
            ultimately show "TargetTerm (\<lbrakk>S'\<rbrakk>) \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> TargetTerm TR"
              by (rule indRelRTPO.trans)
          qed
          with A5 show "P' \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> TargetTerm T"
            by (rule indRelRTPO.trans)
        qed
        ultimately show "P' \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> TargetTerm T"
          by blast
      qed
      ultimately
      show "\<exists>Q'. TargetTerm (\<lbrakk>S\<rbrakk>) \<longmapsto>(STCal Source Target) Q' \<and> P' \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> Q'"
        by blast
    next
      case (source S)
      then obtain S' where B1: "S' \<in>S P'"
        by (auto simp add: STCal_step(1))
      hence "P' \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> P'"
        by (simp add: indRelRTPO.source)
      with source show "\<exists>Q'. SourceTerm S \<longmapsto>(STCal Source Target) Q' \<and> P' \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> Q'"
        by blast
    next
      case (target T1 T2)
      assume "TargetTerm T1 \<longmapsto>(STCal Source Target) P'"
      from this obtain T1' where C1: "T1' \<in>T P'" and C2: "T1 \<longmapsto>Target T1'"
        by (auto simp add: STCal_step(2))
      assume "(T1, T2) \<in> TRel"
      hence "(T1, T2) \<in> TRel\<^sup>+"
        by simp
      with C2 sim obtain T2' where C3: "T2 \<longmapsto>Target T2'" and C4: "(T1', T2') \<in> TRel\<^sup>+"
        by blast
      from C3 have "TargetTerm T2 \<longmapsto>(STCal Source Target) (TargetTerm T2')"
        by (simp add: STCal_step(2))
      moreover from C4 have "TargetTerm T1' \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> TargetTerm T2'"
      proof induct
        fix T2'
        assume "(T1', T2') \<in> TRel"
        thus "TargetTerm T1' \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> TargetTerm T2'"
          by (rule indRelRTPO.target)
      next
        case (step TQ TR)
        assume "TargetTerm T1' \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> TargetTerm TQ"
        moreover assume "(TQ, TR) \<in> TRel"
        hence "TargetTerm TQ \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> TargetTerm TR"
          by (rule indRelRTPO.target)
        ultimately show "TargetTerm T1' \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> TargetTerm TR"
          by (rule indRelRTPO.trans)
      qed
      with C1 have "P' \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> TargetTerm T2'"
        by simp
      ultimately show "\<exists>Q'. TargetTerm T2 \<longmapsto>(STCal Source Target) Q' \<and> P' \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> Q'"
        by blast
    next
      case (trans P Q R)
      assume "P \<longmapsto>(STCal Source Target) P'"
         and "\<And>P'. P \<longmapsto>(STCal Source Target) P'
              \<Longrightarrow> \<exists>Q'. Q \<longmapsto>(STCal Source Target) Q' \<and> P' \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> Q'"
      from this obtain Q' where D1: "Q \<longmapsto>(STCal Source Target) Q'"
                            and D2: "P' \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> Q'"
        by blast
      assume "\<And>Q'. Q \<longmapsto>(STCal Source Target) Q'
              \<Longrightarrow> \<exists>R'. R \<longmapsto>(STCal Source Target) R' \<and> Q' \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> R'"
      with D1 obtain R' where D3: "R \<longmapsto>(STCal Source Target) R'"
                          and D4: "Q' \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> R'"
        by blast
      from D2 D4 have "P' \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> R'"
        by (rule indRelRTPO.trans)
      with D3 show "\<exists>R'. R \<longmapsto>(STCal Source Target) R' \<and> P' \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> R'"
        by blast
    qed
  qed
next
  have "\<forall>S. SourceTerm S \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> TargetTerm (\<lbrakk>S\<rbrakk>)"
    by (simp add: indRelRTPO.encR)
  moreover have "\<forall>S T. SourceTerm S \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> TargetTerm T \<longrightarrow> (\<lbrakk>S\<rbrakk>, T) \<in> TRel\<^sup>*"
      using indRelRTPO_to_TRel(2)[where TRel="TRel"] trans_closure_of_TRel_refl_cond
    by simp
  moreover assume sim: "strong_reduction_simulation (indRelRTPO TRel) (STCal Source Target)"
  ultimately have "strongly_operational_complete (TRel\<^sup>*)"
      using strong_reduction_simulation_impl_SOCom[where Rel="indRelRTPO TRel" and TRel="TRel"]
    by simp
  moreover from sim have "strong_reduction_simulation (TRel\<^sup>+) Target"
      using indRelRTPO_impl_TRel_is_strong_reduction_simulation[where TRel="TRel"]
    by simp
  ultimately show "strongly_operational_complete (TRel\<^sup>*)
                   \<and> strong_reduction_simulation (TRel\<^sup>+) Target"
    by simp
qed

lemma (in encodingLS_encL) SOCom_iff_indRelRTPO_is_strong_labelled_simulation_encL:
  fixes TRel :: "('procT \<times> 'procT) set"
  shows "(strongly_operational_complete_encL (TRel\<^sup>*)
         \<and> strong_labelled_simulation (TRel\<^sup>+) Target)
         = strong_labelled_simulation_encL (indRelRTPO TRel)"
proof (rule iffI, erule conjE)
  assume soc: "strongly_operational_complete_encL (TRel\<^sup>*)"
     and sim: "strong_labelled_simulation (TRel\<^sup>+) Target"
  show "strong_labelled_simulation_encL (indRelRTPO TRel)"
  proof clarify
    fix P Q \<alpha> P'
    assume "P \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> Q" and "P \<midarrow>\<alpha>\<rightarrow>(STLCal Source Target) P'"
    thus "\<exists>\<beta> Q'. Q \<midarrow>\<beta>\<rightarrow>(STLCal Source Target) Q' \<and> P' \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> Q' \<and> \<langle>P, \<alpha>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>Q, \<beta>\<rangle>"
    proof (induct arbitrary: \<alpha> P')
      case (encR S)
      assume "SourceTerm S \<midarrow>\<alpha>\<rightarrow>(STLCal Source Target) P'"
      from this obtain \<alpha>' S' where A1: "\<alpha>' \<in>SL \<langle>SourceTerm S, \<alpha>\<rangle>" and A2: "S' \<in>S P'"
                               and A3: "S \<midarrow>\<alpha>'\<rightarrow>Source S'"
        using STLCal_labelledStep(1)[of S \<alpha> P']
        by blast
      from soc A3 obtain \<beta>' T where A4: "\<lbrakk>S\<rbrakk> \<midarrow>\<beta>'\<rightarrow>Target T" and A5: "(\<lbrakk>S'\<rbrakk>, T) \<in> TRel\<^sup>*"
                                and A6: "\<lblot>\<alpha>'\<rblot> = \<beta>'"
        by blast
      obtain \<beta> where A7: "\<beta>' \<in>TL \<langle>TargetTerm (\<lbrakk>S\<rbrakk>), \<beta>\<rangle>"
        unfolding getTargetLabel_def
        by blast
      with A4 have "TargetTerm (\<lbrakk>S\<rbrakk>) \<midarrow>\<beta>\<rightarrow>(STLCal Source Target) (TargetTerm T)"
        using STLCal_labelledStep(2)[of "\<lbrakk>S\<rbrakk>" \<beta> "TargetTerm T"]
        by blast
      moreover have "P' \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> TargetTerm T"
      proof -
        from A5 have "\<lbrakk>S'\<rbrakk> = T \<or> (\<lbrakk>S'\<rbrakk>, T) \<in> TRel\<^sup>+"
            using rtrancl_eq_or_trancl[of "\<lbrakk>S'\<rbrakk>" T TRel]
          by blast
        moreover from A2 have B: "P' \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> TargetTerm (\<lbrakk>S'\<rbrakk>)"
          by (simp add: indRelRTPO.encR)
        hence "\<lbrakk>S'\<rbrakk> = T \<Longrightarrow> P' \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> TargetTerm T"
          by simp
        moreover have "(\<lbrakk>S'\<rbrakk>, T) \<in> TRel\<^sup>+ \<Longrightarrow> P' \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> TargetTerm T"
        proof -
          assume "(\<lbrakk>S'\<rbrakk>, T) \<in> TRel\<^sup>+"
          hence "TargetTerm (\<lbrakk>S'\<rbrakk>) \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> TargetTerm T"
          proof induct
            fix TQ
            assume "(\<lbrakk>S'\<rbrakk>, TQ) \<in> TRel"
            thus "TargetTerm (\<lbrakk>S'\<rbrakk>) \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> TargetTerm TQ"
              by (rule indRelRTPO.target)
          next
            case (step TQ TR)
            assume "TargetTerm (\<lbrakk>S'\<rbrakk>) \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> TargetTerm TQ"
            moreover assume "(TQ, TR) \<in> TRel"
            hence "TargetTerm TQ \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> TargetTerm TR"
              by (rule indRelRTPO.target)
            ultimately show "TargetTerm (\<lbrakk>S'\<rbrakk>) \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> TargetTerm TR"
              by (rule indRelRTPO.trans)
          qed
          with B show "P' \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> TargetTerm T"
            by (rule indRelRTPO.trans)
        qed
        ultimately show "P' \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> TargetTerm T"
          by blast
      qed
      moreover from A1 A6 A7 have "\<lparr>SourceTerm S, \<alpha>\<rparr>\<mapsto>\<langle>TargetTerm (\<lbrakk>S\<rbrakk>), \<beta>\<rangle>"
        unfolding encLST_def
        by blast
      hence "\<langle>SourceTerm S, \<alpha>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>TargetTerm (\<lbrakk>S\<rbrakk>), \<beta>\<rangle>"
        unfolding related_labels_def
        by simp
      ultimately show "\<exists>\<beta> Q'. TargetTerm (\<lbrakk>S\<rbrakk>) \<midarrow>\<beta>\<rightarrow>(STLCal Source Target) Q' \<and> P' \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> Q' \<and>
                       \<langle>SourceTerm S, \<alpha>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>TargetTerm (\<lbrakk>S\<rbrakk>), \<beta>\<rangle>"
        by blast
    next
      case (source S)
      assume A1: "SourceTerm S \<midarrow>\<alpha>\<rightarrow>(STLCal Source Target) P'"
      then obtain S' where "S' \<in>S P'"
        using STLCal_labelledStep(1)[of S \<alpha> P']
        by blast
      hence A2: "P' \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> P'"
        by (simp add: indRelRTPO.source)
      have "\<langle>SourceTerm S, \<alpha>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>SourceTerm S, \<alpha>\<rangle>"
        unfolding related_labels_def
        by simp
      with A1 A2 show "\<exists>\<beta> Q'. SourceTerm S \<midarrow>\<beta>\<rightarrow>(STLCal Source Target) Q' \<and> P' \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> Q' \<and>
                       \<langle>SourceTerm S, \<alpha>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>SourceTerm S, \<beta>\<rangle>"
        by blast
    next
      case (target T1 T2)
      assume "TargetTerm T1 \<midarrow>\<alpha>\<rightarrow>(STLCal Source Target) P'"
      from this obtain \<alpha>' T1' where A1: "\<alpha>' \<in>TL \<langle>TargetTerm T1, \<alpha>\<rangle>" and A2: "T1' \<in>T P'"
                                and A3: "T1 \<midarrow>\<alpha>'\<rightarrow>Target T1'"
        using STLCal_labelledStep(2)[of T1 \<alpha> P']
        by blast
      assume "(T1, T2) \<in> TRel"
      hence "(T1, T2) \<in> TRel\<^sup>+"
        by simp
      with A3 sim obtain T2' where A4: "T2 \<midarrow>\<alpha>'\<rightarrow>Target T2'" and A5: "(T1', T2') \<in> TRel\<^sup>+"
        by blast
      from A1 A4 have "TargetTerm T2 \<midarrow>\<alpha>\<rightarrow>(STLCal Source Target) (TargetTerm T2')"
        using STLCal_labelledStep(2)[of T2 \<alpha> "TargetTerm T2'"]
        unfolding getTargetLabel_def
        by blast
      moreover from A5 have "TargetTerm T1' \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> TargetTerm T2'"
      proof induct
        fix T2'
        assume "(T1', T2') \<in> TRel"
        thus "TargetTerm T1' \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> TargetTerm T2'"
          by (rule indRelRTPO.target)
      next
        case (step TQ TR)
        assume "TargetTerm T1' \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> TargetTerm TQ"
        moreover assume "(TQ, TR) \<in> TRel"
        hence "TargetTerm TQ \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> TargetTerm TR"
          by (rule indRelRTPO.target)
        ultimately show "TargetTerm T1' \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> TargetTerm TR"
          by (rule indRelRTPO.trans)
      qed
      with A2 have "P' \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> TargetTerm T2'"
        by simp
      moreover have "\<langle>TargetTerm T1, \<alpha>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>TargetTerm T2, \<alpha>\<rangle>"
        unfolding related_labels_def
        by simp
      ultimately show "\<exists>\<beta> Q'. TargetTerm T2 \<midarrow>\<beta>\<rightarrow>(STLCal Source Target) Q' \<and> P' \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> Q' \<and>
                       \<langle>TargetTerm T1, \<alpha>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>TargetTerm T2, \<beta>\<rangle>"
        by blast
    next
      case (trans P Q R)
      assume "P \<midarrow>\<alpha>\<rightarrow>(STLCal Source Target) P'"
         and "\<And>\<alpha> P'. P \<midarrow>\<alpha>\<rightarrow>(STLCal Source Target) P' \<Longrightarrow>
              \<exists>\<beta> Q'. Q \<midarrow>\<beta>\<rightarrow>(STLCal Source Target) Q' \<and> P' \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> Q' \<and> \<langle>P, \<alpha>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>Q, \<beta>\<rangle>"
      then obtain \<beta> Q' where A1: "Q \<midarrow>\<beta>\<rightarrow>(STLCal Source Target) Q'" and A2: "P' \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> Q'"
                         and A3: "\<langle>P, \<alpha>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>Q, \<beta>\<rangle>"
        by blast
      assume "\<And>\<beta> Q'. Q \<midarrow>\<beta>\<rightarrow>(STLCal Source Target) Q' \<Longrightarrow>
              \<exists>\<gamma> R'. R \<midarrow>\<gamma>\<rightarrow>(STLCal Source Target) R' \<and> Q' \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> R' \<and> \<langle>Q, \<beta>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>R, \<gamma>\<rangle>"
      with A1 obtain \<gamma> R' where A4: "R \<midarrow>\<gamma>\<rightarrow>(STLCal Source Target) R'" and A5: "Q' \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> R'"
                            and A6: "\<langle>Q, \<beta>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>R, \<gamma>\<rangle>"
        by blast
      from A2 A5 have A7: "P' \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> R'"
        by (rule indRelRTPO.trans)
      assume "P \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> Q"
      hence A8: "\<not>(P \<in> ProcT \<and> Q \<in> ProcS)"
        using indRelRTPO_to_TRel(3)[of P Q TRel]
        by blast
      assume "Q \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> R"
      hence "\<not>(Q \<in> ProcT \<and> R \<in> ProcS)"
        using indRelRTPO_to_TRel[of Q R TRel]
        by blast
      with A3 A6 A8 have "\<langle>P, \<alpha>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>R, \<gamma>\<rangle>"
        using related_labels_trans_no_T_to_S[of P \<alpha> Q \<beta> R \<gamma>]
        by simp
      with A4 A7
      show "\<exists>\<gamma> R'. R \<midarrow>\<gamma>\<rightarrow>(STLCal Source Target) R' \<and> P' \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> R' \<and> \<langle>P, \<alpha>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>R, \<gamma>\<rangle>"
        by blast
    qed
  qed
next
  have "\<forall>S. SourceTerm S \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> TargetTerm (\<lbrakk>S\<rbrakk>)"
    by (simp add: indRelRTPO.encR)
  moreover have "\<forall>S T. SourceTerm S \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> TargetTerm T \<longrightarrow> (\<lbrakk>S\<rbrakk>, T) \<in> TRel\<^sup>*"
      using indRelRTPO_to_TRel(2)[where TRel="TRel"] trans_closure_of_TRel_refl_cond
    by simp
  moreover assume sim: "strong_labelled_simulation_encL (indRelRTPO TRel)"
  ultimately have "strongly_operational_complete_encL (TRel\<^sup>*)"
      using strong_labelled_simulation_impl_SOCom_encL[where Rel="indRelRTPO TRel" and TRel="TRel"]
    by simp
  moreover from sim have "strong_labelled_simulation (TRel\<^sup>+) Target"
      using indRelRTPO_impl_TRel_is_strong_labelled_simulation_encL[where TRel="TRel"]
    by simp
  ultimately show "strongly_operational_complete_encL (TRel\<^sup>*)
                   \<and> strong_labelled_simulation (TRel\<^sup>+) Target"
    by simp
qed

lemma (in encoding) SOCom_iff_strong_reduction_simulation:
  fixes TRel :: "('procT \<times> 'procT) set"
  shows "(strongly_operational_complete (TRel\<^sup>*)
         \<and> strong_reduction_simulation (TRel\<^sup>+) Target)
         = (\<exists>Rel. (\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel)
            \<and> (\<forall>T1 T2. (T1, T2) \<in> TRel \<longrightarrow> (TargetTerm T1, TargetTerm T2) \<in> Rel)
            \<and> (\<forall>T1 T2. (TargetTerm T1, TargetTerm T2) \<in> Rel \<longrightarrow> (T1, T2) \<in> TRel\<^sup>+)
            \<and> (\<forall>S T. (SourceTerm S, TargetTerm T) \<in> Rel \<longrightarrow> (\<lbrakk>S\<rbrakk>, T) \<in> TRel\<^sup>*)
            \<and> strong_reduction_simulation Rel (STCal Source Target))"
proof (rule iffI, erule conjE)
  have "\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> indRelRTPO TRel"
    by (simp add: indRelRTPO.encR)
  moreover have "\<forall>T1 T2. (T1, T2) \<in> TRel \<longrightarrow> TargetTerm T1 \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> TargetTerm T2"
    by (simp add: indRelRTPO.target)
  moreover have "\<forall>T1 T2. TargetTerm T1 \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> TargetTerm T2 \<longrightarrow> (T1, T2) \<in> TRel\<^sup>+"
      using indRelRTPO_to_TRel(4)[where TRel="TRel"]
    by simp
  moreover have "\<forall>S T. SourceTerm S \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> TargetTerm T \<longrightarrow> (\<lbrakk>S\<rbrakk>, T) \<in> TRel\<^sup>*"
      using indRelRTPO_to_TRel(2)[where TRel="TRel"] trans_closure_of_TRel_refl_cond
    by simp
  moreover assume "strongly_operational_complete (TRel\<^sup>*)"
              and "strong_reduction_simulation (TRel\<^sup>+) Target"
  hence "strong_reduction_simulation (indRelRTPO TRel) (STCal Source Target)"
      using SOCom_iff_indRelRTPO_is_strong_reduction_simulation[where TRel="TRel"]
    by simp
  ultimately show "\<exists>Rel. (\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel)
                   \<and> (\<forall>T1 T2. (T1, T2) \<in> TRel \<longrightarrow> (TargetTerm T1, TargetTerm T2) \<in> Rel)
                   \<and> (\<forall>T1 T2. (TargetTerm T1, TargetTerm T2) \<in> Rel \<longrightarrow> (T1, T2) \<in> TRel\<^sup>+)
                   \<and> (\<forall>S T. (SourceTerm S, TargetTerm T) \<in> Rel \<longrightarrow> (\<lbrakk>S\<rbrakk>, T) \<in> TRel\<^sup>*)
                   \<and> strong_reduction_simulation Rel (STCal Source Target)"
    by blast
next
  assume "\<exists>Rel. (\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel)
          \<and> (\<forall>T1 T2. (T1, T2) \<in> TRel \<longrightarrow> (TargetTerm T1, TargetTerm T2) \<in> Rel)
          \<and> (\<forall>T1 T2. (TargetTerm T1, TargetTerm T2) \<in> Rel \<longrightarrow> (T1, T2) \<in> TRel\<^sup>+)
          \<and> (\<forall>S T. (SourceTerm S, TargetTerm T) \<in> Rel \<longrightarrow> (\<lbrakk>S\<rbrakk>, T) \<in> TRel\<^sup>*)
          \<and> strong_reduction_simulation Rel (STCal Source Target)"
  from this obtain Rel where A1: "\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel"
    and A2: "\<forall>T1 T2. (T1, T2) \<in> TRel \<longrightarrow> (TargetTerm T1, TargetTerm T2) \<in> Rel"
    and A3: "\<forall>T1 T2. (TargetTerm T1, TargetTerm T2) \<in> Rel \<longrightarrow> (T1, T2) \<in> TRel\<^sup>+"
    and A4: "\<forall>S T. (SourceTerm S, TargetTerm T) \<in> Rel \<longrightarrow> (\<lbrakk>S\<rbrakk>, T) \<in> TRel\<^sup>*"
    and A5: "strong_reduction_simulation Rel (STCal Source Target)"
    by blast
  from A1 A4 A5 have "strongly_operational_complete (TRel\<^sup>*)"
      using strong_reduction_simulation_impl_SOCom[where Rel="Rel" and TRel="TRel"]
    by simp
  moreover from A2 A3 A5 have "strong_reduction_simulation (TRel\<^sup>+) Target"
      using rel_with_target_impl_transC_TRel_is_strong_reduction_simulation[where Rel="Rel" and
             TRel="TRel"]
    by simp
  ultimately show "strongly_operational_complete (TRel\<^sup>*)
                   \<and> strong_reduction_simulation (TRel\<^sup>+) Target"
    by simp
qed

lemma (in encodingLS_encL) SOCom_iff_strong_labelled_simulation_encL:
  fixes TRel :: "('procT \<times> 'procT) set"
  shows "(strongly_operational_complete_encL (TRel\<^sup>*)
         \<and> strong_labelled_simulation (TRel\<^sup>+) Target)
         = (\<exists>Rel. (\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel)
            \<and> (\<forall>T1 T2. (T1, T2) \<in> TRel \<longrightarrow> (TargetTerm T1, TargetTerm T2) \<in> Rel)
            \<and> (\<forall>T1 T2. (TargetTerm T1, TargetTerm T2) \<in> Rel \<longrightarrow> (T1, T2) \<in> TRel\<^sup>+)
            \<and> (\<forall>S T. (SourceTerm S, TargetTerm T) \<in> Rel \<longrightarrow> (\<lbrakk>S\<rbrakk>, T) \<in> TRel\<^sup>*)
            \<and> strong_labelled_simulation_encL Rel)"
proof (rule iffI, erule conjE)
  have "\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> indRelRTPO TRel"
    by (simp add: indRelRTPO.encR)
  moreover have "\<forall>T1 T2. (T1, T2) \<in> TRel \<longrightarrow> TargetTerm T1 \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> TargetTerm T2"
    by (simp add: indRelRTPO.target)
  moreover have "\<forall>T1 T2. TargetTerm T1 \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> TargetTerm T2 \<longrightarrow> (T1, T2) \<in> TRel\<^sup>+"
    using indRelRTPO_to_TRel(4)[where TRel="TRel"]
    by simp
  moreover have "\<forall>S T. SourceTerm S \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> TargetTerm T \<longrightarrow> (\<lbrakk>S\<rbrakk>, T) \<in> TRel\<^sup>*"
    using indRelRTPO_to_TRel(2)[where TRel="TRel"] trans_closure_of_TRel_refl_cond
    by simp
  moreover assume "strongly_operational_complete_encL (TRel\<^sup>*)"
              and "strong_labelled_simulation (TRel\<^sup>+) Target"
  hence "strong_labelled_simulation_encL (indRelRTPO TRel)"
    using SOCom_iff_indRelRTPO_is_strong_labelled_simulation_encL[where TRel="TRel"]
    by simp
  ultimately show "\<exists>Rel. (\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel)
                   \<and> (\<forall>T1 T2. (T1, T2) \<in> TRel \<longrightarrow> (TargetTerm T1, TargetTerm T2) \<in> Rel)
                   \<and> (\<forall>T1 T2. (TargetTerm T1, TargetTerm T2) \<in> Rel \<longrightarrow> (T1, T2) \<in> TRel\<^sup>+)
                   \<and> (\<forall>S T. (SourceTerm S, TargetTerm T) \<in> Rel \<longrightarrow> (\<lbrakk>S\<rbrakk>, T) \<in> TRel\<^sup>*)
                   \<and> strong_labelled_simulation_encL Rel"
    by blast
next
  assume "\<exists>Rel. (\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel)
          \<and> (\<forall>T1 T2. (T1, T2) \<in> TRel \<longrightarrow> (TargetTerm T1, TargetTerm T2) \<in> Rel)
          \<and> (\<forall>T1 T2. (TargetTerm T1, TargetTerm T2) \<in> Rel \<longrightarrow> (T1, T2) \<in> TRel\<^sup>+)
          \<and> (\<forall>S T. (SourceTerm S, TargetTerm T) \<in> Rel \<longrightarrow> (\<lbrakk>S\<rbrakk>, T) \<in> TRel\<^sup>*)
          \<and> strong_labelled_simulation_encL Rel"
  then obtain Rel where A1: "\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel"
    and A2: "\<forall>T1 T2. (T1, T2) \<in> TRel \<longrightarrow> (TargetTerm T1, TargetTerm T2) \<in> Rel"
    and A3: "\<forall>T1 T2. (TargetTerm T1, TargetTerm T2) \<in> Rel \<longrightarrow> (T1, T2) \<in> TRel\<^sup>+"
    and A4: "\<forall>S T. (SourceTerm S, TargetTerm T) \<in> Rel \<longrightarrow> (\<lbrakk>S\<rbrakk>, T) \<in> TRel\<^sup>*"
    and A5: "strong_labelled_simulation_encL Rel"
    by blast
  from A1 A4 A5 have "strongly_operational_complete_encL (TRel\<^sup>*)"
    using strong_labelled_simulation_impl_SOCom_encL[where Rel="Rel" and TRel="TRel"]
    by simp
  moreover from A2 A3 A5 have "strong_labelled_simulation (TRel\<^sup>+) Target"
    using rel_with_target_impl_transC_TRel_is_strong_labelled_simulation_encL[where Rel="Rel" and
           TRel="TRel"]
    by simp
  ultimately show "strongly_operational_complete_encL (TRel\<^sup>*)
                   \<and> strong_labelled_simulation (TRel\<^sup>+) Target"
    by simp
qed

lemma (in encodingFunction) target_relation_from_source_target_relation:
  fixes Rel :: "(('procS, 'procT) Proc \<times> ('procS, 'procT) Proc) set"
  assumes stre: "\<forall>S T. (SourceTerm S, TargetTerm T) \<in> Rel
                 \<longrightarrow> (TargetTerm (\<lbrakk>S\<rbrakk>), TargetTerm T) \<in> Rel\<^sup>="
  shows "\<exists>TRel. (\<forall>T1 T2. (T1, T2) \<in> TRel \<longrightarrow> (TargetTerm T1, TargetTerm T2) \<in> Rel)
            \<and> (\<forall>T1 T2. (TargetTerm T1, TargetTerm T2) \<in> Rel \<longrightarrow> (T1, T2) \<in> TRel\<^sup>+)
            \<and> (\<forall>S T. (SourceTerm S, TargetTerm T) \<in> Rel \<longrightarrow> (\<lbrakk>S\<rbrakk>, T) \<in> TRel\<^sup>*)"
proof -
  define TRel where "TRel = {(T1, T2). (TargetTerm T1, TargetTerm T2) \<in> Rel}"
  from TRel_def have "\<forall>T1 T2. (T1, T2) \<in> TRel \<longrightarrow> (TargetTerm T1, TargetTerm T2) \<in> Rel"
    by simp
  moreover from TRel_def
  have "\<forall>T1 T2. (TargetTerm T1, TargetTerm T2) \<in> Rel \<longrightarrow> (T1, T2) \<in> TRel\<^sup>+"
    by blast
  moreover from stre TRel_def
  have "\<forall>S T. (SourceTerm S, TargetTerm T) \<in> Rel \<longrightarrow> (\<lbrakk>S\<rbrakk>, T) \<in> TRel\<^sup>*"
    by blast
  ultimately show ?thesis
    by blast
qed

lemma (in encoding) SOCom_modulo_TRel_iff_strong_reduction_simulation:
  shows "(\<exists>TRel. strongly_operational_complete (TRel\<^sup>*)
         \<and> strong_reduction_simulation (TRel\<^sup>+) Target)
         = (\<exists>Rel. (\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel)
           \<and> (\<forall>S T. (SourceTerm S, TargetTerm T) \<in> Rel \<longrightarrow> (TargetTerm (\<lbrakk>S\<rbrakk>), TargetTerm T) \<in> Rel\<^sup>=)
           \<and> strong_reduction_simulation Rel (STCal Source Target))"
proof (rule iffI)
  assume "\<exists>TRel. strongly_operational_complete (TRel\<^sup>*)
          \<and> strong_reduction_simulation (TRel\<^sup>+) Target"
  from this obtain TRel where "strongly_operational_complete (TRel\<^sup>*)"
                          and "strong_reduction_simulation (TRel\<^sup>+) Target"
    by blast
  hence "strong_reduction_simulation (indRelRTPO TRel) (STCal Source Target)"
      using SOCom_iff_indRelRTPO_is_strong_reduction_simulation[where TRel="TRel"]
    by simp
  moreover have "\<forall>S. SourceTerm S \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> TargetTerm (\<lbrakk>S\<rbrakk>)"
    by (simp add: indRelRTPO.encR)
  moreover have "\<forall>S T. SourceTerm S \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> TargetTerm T
                 \<longrightarrow> (TargetTerm (\<lbrakk>S\<rbrakk>), TargetTerm T) \<in> (indRelRTPO TRel)\<^sup>="
      using indRelRTPO_relates_source_target[where TRel="TRel"]
    by simp
  ultimately show "\<exists>Rel. (\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel)
                   \<and> (\<forall>S T. (SourceTerm S, TargetTerm T) \<in> Rel
                      \<longrightarrow> (TargetTerm (\<lbrakk>S\<rbrakk>), TargetTerm T) \<in> Rel\<^sup>=)
                   \<and> strong_reduction_simulation Rel (STCal Source Target)"
    by blast
next
  assume "\<exists>Rel. (\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel)
          \<and> (\<forall>S T. (SourceTerm S, TargetTerm T) \<in> Rel \<longrightarrow> (TargetTerm (\<lbrakk>S\<rbrakk>), TargetTerm T) \<in> Rel\<^sup>=)
          \<and> strong_reduction_simulation Rel (STCal Source Target)"
  from this obtain Rel where A1: "\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel"
                         and A2: "(\<forall>S T. (SourceTerm S, TargetTerm T) \<in> Rel
                                  \<longrightarrow> (TargetTerm (\<lbrakk>S\<rbrakk>), TargetTerm T) \<in> Rel\<^sup>=)"
                         and A3: "strong_reduction_simulation Rel (STCal Source Target)"
    by blast
  from A2 obtain TRel where "\<forall>T1 T2. (T1, T2) \<in> TRel \<longrightarrow> (TargetTerm T1, TargetTerm T2) \<in> Rel"
   and "\<forall>T1 T2. (TargetTerm T1, TargetTerm T2) \<in> Rel \<longrightarrow> (T1, T2) \<in> TRel\<^sup>+"
   and "\<forall>S T. (SourceTerm S, TargetTerm T) \<in> Rel \<longrightarrow> (\<lbrakk>S\<rbrakk>, T) \<in> TRel\<^sup>*"
      using target_relation_from_source_target_relation[where Rel="Rel"]
    by blast
  with A1 A3 have "strongly_operational_complete (TRel\<^sup>*)
                   \<and> strong_reduction_simulation (TRel\<^sup>+) Target"
      using SOCom_iff_strong_reduction_simulation[where TRel="TRel"]
    by blast
  thus "\<exists>TRel. strongly_operational_complete (TRel\<^sup>*)
        \<and> strong_reduction_simulation (TRel\<^sup>+) Target"
    by blast
qed

lemma (in encodingLS_encL) SOCom_modulo_TRel_iff_strong_labelled_simulation_encL:
  shows "(\<exists>TRel. strongly_operational_complete_encL (TRel\<^sup>*)
         \<and> strong_labelled_simulation (TRel\<^sup>+) Target)
         = (\<exists>Rel. (\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel)
           \<and> (\<forall>S T. (SourceTerm S, TargetTerm T) \<in> Rel \<longrightarrow> (TargetTerm (\<lbrakk>S\<rbrakk>), TargetTerm T) \<in> Rel\<^sup>=)
           \<and> strong_labelled_simulation_encL Rel)"
proof (rule iffI)
  assume "\<exists>TRel. strongly_operational_complete_encL (TRel\<^sup>*)
          \<and> strong_labelled_simulation (TRel\<^sup>+) Target"
  from this obtain TRel where "strongly_operational_complete_encL (TRel\<^sup>*)"
                          and "strong_labelled_simulation (TRel\<^sup>+) Target"
    by blast
  hence "strong_labelled_simulation_encL (indRelRTPO TRel)"
    using SOCom_iff_indRelRTPO_is_strong_labelled_simulation_encL[where TRel="TRel"]
    by simp
  moreover have "\<forall>S. SourceTerm S \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> TargetTerm (\<lbrakk>S\<rbrakk>)"
    by (simp add: indRelRTPO.encR)
  moreover have "\<forall>S T. SourceTerm S \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> TargetTerm T
                 \<longrightarrow> (TargetTerm (\<lbrakk>S\<rbrakk>), TargetTerm T) \<in> (indRelRTPO TRel)\<^sup>="
    using indRelRTPO_relates_source_target[where TRel="TRel"]
    by simp
  ultimately show "\<exists>Rel. (\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel)
                   \<and> (\<forall>S T. (SourceTerm S, TargetTerm T) \<in> Rel
                      \<longrightarrow> (TargetTerm (\<lbrakk>S\<rbrakk>), TargetTerm T) \<in> Rel\<^sup>=)
                   \<and> strong_labelled_simulation_encL Rel"
    by blast
next
  assume "\<exists>Rel. (\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel)
          \<and> (\<forall>S T. (SourceTerm S, TargetTerm T) \<in> Rel \<longrightarrow> (TargetTerm (\<lbrakk>S\<rbrakk>), TargetTerm T) \<in> Rel\<^sup>=)
          \<and> strong_labelled_simulation_encL Rel"
  then obtain Rel where A1: "\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel"
                    and A2: "(\<forall>S T. (SourceTerm S, TargetTerm T) \<in> Rel
                              \<longrightarrow> (TargetTerm (\<lbrakk>S\<rbrakk>), TargetTerm T) \<in> Rel\<^sup>=)"
                    and A3: "strong_labelled_simulation_encL Rel"
    by blast
  from A2 obtain TRel where "\<forall>T1 T2. (T1, T2) \<in> TRel \<longrightarrow> (TargetTerm T1, TargetTerm T2) \<in> Rel"
   and "\<forall>T1 T2. (TargetTerm T1, TargetTerm T2) \<in> Rel \<longrightarrow> (T1, T2) \<in> TRel\<^sup>+"
   and "\<forall>S T. (SourceTerm S, TargetTerm T) \<in> Rel \<longrightarrow> (\<lbrakk>S\<rbrakk>, T) \<in> TRel\<^sup>*"
      using target_relation_from_source_target_relation[where Rel="Rel"]
    by blast
  with A1 A3 have "strongly_operational_complete_encL (TRel\<^sup>*)
                   \<and> strong_labelled_simulation (TRel\<^sup>+) Target"
      using SOCom_iff_strong_labelled_simulation_encL[where TRel="TRel"]
    by blast
  thus "\<exists>TRel. strongly_operational_complete_encL (TRel\<^sup>*)
        \<and> strong_labelled_simulation (TRel\<^sup>+) Target"
    by blast
qed

subsection \<open>Weak Operational Soundness vs Contrasimulation\<close>

text \<open>If the inverse of a relation that includes TRel and relates source terms and their literal
      translations is a contrasimulation, then the encoding is weakly operational sound. Note that
      this result does not hold in the labelled case without encoded labels, because
      contrasimulation will relate a given sequences of steps in the target with a single label on
      an arbitrary long sequence in the source. Without the relation on encoded labels, we cannot
      conclude that the sequence of steps in the source consists only of a single label.\<close>

lemma (in encoding) weak_reduction_contrasimulation_impl_WOSou:
  fixes Rel  :: "(('procS, 'procT) Proc \<times> ('procS, 'procT) Proc) set"
    and TRel :: "('procT \<times> 'procT) set"
  assumes A1: "\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel"
      and A2: "\<forall>S T. (SourceTerm S, TargetTerm T) \<in> Rel \<longrightarrow> (\<lbrakk>S\<rbrakk>, T) \<in> TRel\<^sup>*"
      and A3: "weak_reduction_contrasimulation (Rel\<inverse>) (STCal Source Target)"
  shows "weakly_operational_sound (TRel\<^sup>*)"
proof clarify
  fix S T
  from A1 have "(TargetTerm (\<lbrakk>S\<rbrakk>), SourceTerm S) \<in> Rel\<inverse>"
    by simp
  moreover assume "\<lbrakk>S\<rbrakk> \<longmapsto>Target* T"
  hence "TargetTerm (\<lbrakk>S\<rbrakk>) \<longmapsto>(STCal Source Target)* (TargetTerm T)"
    by (simp add: STCal_steps(2))
  ultimately obtain Q' where A5: "SourceTerm S \<longmapsto>(STCal Source Target)* Q'"
                         and A6: "(Q', TargetTerm T) \<in> Rel\<inverse>"
    using A3
    by blast
  from A5 obtain S' where A7: "S' \<in>S Q'" and A8: "S \<longmapsto>Source* S'"
    by (auto simp add: STCal_steps(1))
  have "Q' \<longmapsto>(STCal Source Target)* Q'"
    by (simp add: steps_refl)
  with A6 A3 obtain P'' where A9:  "TargetTerm T \<longmapsto>(STCal Source Target)* P''"
                          and A10: "(P'', Q') \<in> Rel\<inverse>"
    by blast
  from A9 obtain T' where A11: "T' \<in>T P''" and A12: "T \<longmapsto>Target* T'"
    by (auto simp add: STCal_steps(2))
  from A10 have "(Q', P'') \<in> Rel"
    by induct
  with A2 A7 A11 have "(\<lbrakk>S'\<rbrakk>, T') \<in> TRel\<^sup>*"
    by simp
  with A8 A12 show "\<exists>S' T'. S \<longmapsto>Source* S' \<and> T \<longmapsto>Target* T' \<and> (\<lbrakk>S'\<rbrakk>, T') \<in> TRel\<^sup>*"
    by blast
qed

lemma (in encodingLS_encL) weak_labelled_contrasimulation_impl_WOSou_encL:
  fixes Rel  :: "(('procS, 'procT) Proc \<times> ('procS, 'procT) Proc) set"
    and TRel :: "('procT \<times> 'procT) set"
  assumes rel:  "\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel"
      and trel: "\<forall>S T. (SourceTerm S, TargetTerm T) \<in> Rel \<longrightarrow> (\<lbrakk>S\<rbrakk>, T) \<in> TRel\<^sup>*"
      and sim:  "weak_labelled_contrasimulation_encL (Rel\<inverse>)"
  shows "weakly_operational_sound_encL (TRel\<^sup>*)"
proof clarify
  fix S \<beta> T
  obtain \<beta>' where A1: "\<beta> \<in>TL \<langle>TargetTerm (\<lbrakk>S\<rbrakk>), \<beta>'\<rangle>"
    unfolding getTargetLabel_def
    by blast
  from rel have "(TargetTerm (\<lbrakk>S\<rbrakk>), SourceTerm S) \<in> Rel\<inverse>"
    by simp
  moreover assume "\<lbrakk>S\<rbrakk> \<midarrow>\<Zcat>\<beta>\<rightarrow>Target* T"
  with A1 have "TargetTerm (\<lbrakk>S\<rbrakk>) \<midarrow>\<Zcat>\<beta>'\<rightarrow>(STLCal Source Target)* (TargetTerm T)"
    using STLCal_weakLabelledSteps(2)[of "\<lbrakk>S\<rbrakk>" \<beta>' "TargetTerm T"]
    by blast
  hence "TargetTerm (\<lbrakk>S\<rbrakk>) \<midarrow>\<frown>[\<beta>']\<rightarrow>(STLCal Source Target)* (TargetTerm T)"
    using weakLabelledSequence_single[of "TargetTerm (\<lbrakk>S\<rbrakk>)" \<beta>' "STLCal Source Target"
            "TargetTerm T"]
    by simp
  ultimately obtain v P' where A2: "SourceTerm S \<midarrow>\<frown>v\<rightarrow>(STLCal Source Target)* P'"
                           and A3: "(P', TargetTerm T) \<in> Rel\<inverse>"
                           and A4: "\<langle>TargetTerm (\<lbrakk>S\<rbrakk>), [\<beta>']\<rangle> \<equiv>\<lparr>\<rparr>* \<langle>SourceTerm S, v\<rangle>"
    using sim
    by blast
  from A4 have A5: "length v = 1"
    using related_words_length[of "TargetTerm (\<lbrakk>S\<rbrakk>)" "[\<beta>']" "SourceTerm S" v]
    by simp
  from A4 have "\<lparr>SourceTerm S, v\<rparr>\<mapsto>*\<langle>TargetTerm (\<lbrakk>S\<rbrakk>), [\<beta>']\<rangle>"
    using kinds_of_encoded_word(1)[of "TargetTerm (\<lbrakk>S\<rbrakk>)" "[\<beta>']" "SourceTerm S" v]
    unfolding related_words_def
    by blast
  with A5 obtain \<alpha>' P'' Q'' where A6: "v = [\<alpha>']" and A7: "\<lparr>P'', \<alpha>'\<rparr>\<mapsto>\<langle>Q'', \<beta>'\<rangle>"
    using encoded_word_decompose[of "SourceTerm S" v "TargetTerm (\<lbrakk>S\<rbrakk>)" "[\<beta>']"]
    by auto
  from A2 A6 obtain \<alpha> S' where A8:  "\<alpha> \<in>SL \<langle>SourceTerm S, \<alpha>'\<rangle>" and A9: "S' \<in>S P'"
                           and A10: "S \<midarrow>\<Zcat>\<alpha>\<rightarrow>Source* S'"
    using STLCal_weakLabelledSteps(1)[of S \<alpha>' P']
          weakLabelledSequence_single_rev[of "SourceTerm S" \<alpha>' "STLCal Source Target" P']
    by blast
  have "P' \<midarrow>\<frown>[]\<rightarrow>(STLCal Source Target)* P'"
    using WTS_refl[of P' "STLCal Source Target"] WLS_Nil[of P' "STLCal Source Target" P']
    by simp
  with sim A3 obtain w Q' where A11: "TargetTerm T \<midarrow>\<frown>w\<rightarrow>(STLCal Source Target)* Q'"
                            and A12: "(Q', P') \<in> Rel\<inverse>"
                            and A13: "\<langle>P', []\<rangle> \<equiv>\<lparr>\<rparr>* \<langle>TargetTerm T, w\<rangle>"
    by blast
  from A13 have "w = []"
    using related_words_length[of P' "[]" "TargetTerm T" w]
    by simp
  with A11 have "TargetTerm T \<rightarrow>(STLCal Source Target)* Q'"
    using weakLabelledSequence_decompose(1)[of "TargetTerm T" w "STLCal Source Target" Q']
    by simp
  then obtain T' where A14: "T' \<in>T Q'" and A15: "T \<rightarrow>Target* T'"
    using STLCal_weakTauSteps(2)[of T Q']
    by blast
  from A12 have "(P', Q') \<in> Rel"
    by induct
  with trel A9 A14 have A16: "(\<lbrakk>S'\<rbrakk>, T') \<in> TRel\<^sup>*"
    by simp
  from A1 A7 A8 have "\<lblot>\<alpha>\<rblot> = \<beta>"
    unfolding encLST_def getSourceLabel_def getTargetLabel_def
    by blast
  with A10 A15 A16
  show "\<exists>S' \<alpha> T'. S \<midarrow>\<Zcat>\<alpha>\<rightarrow>Source* S' \<and> T \<rightarrow>Target* T' \<and> (\<lbrakk>S'\<rbrakk>, T') \<in> TRel\<^sup>* \<and> \<lblot>\<alpha>\<rblot> = \<beta>"
    by blast
qed

subsection \<open>(Strong) Operational Soundness vs (Strong) Simulation\<close>

text \<open>An encoding is operational sound modulo a relation TRel whose inverse is a weak reduction
      simulation on target terms iff there is a relation, like indRelRTPO, that relates at least
      all source terms to their literal translations, includes TRel, and whose inverse is a weak
      simulation.\<close>

lemma (in encoding) weak_reduction_simulation_impl_OSou:
  fixes Rel  :: "(('procS, 'procT) Proc \<times> ('procS, 'procT) Proc) set"
    and TRel :: "('procT \<times> 'procT) set"
  assumes A1: "\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel"
      and A2: "\<forall>S T. (SourceTerm S, TargetTerm T) \<in> Rel \<longrightarrow> (\<lbrakk>S\<rbrakk>, T) \<in> TRel\<^sup>*"
      and A3: "weak_reduction_simulation (Rel\<inverse>) (STCal Source Target)"
  shows "operational_sound (TRel\<^sup>*)"
proof clarify
  fix S T
  from A1 have "(TargetTerm (\<lbrakk>S\<rbrakk>), SourceTerm S) \<in> Rel\<inverse>"
    by simp
  moreover assume "\<lbrakk>S\<rbrakk> \<longmapsto>Target* T"
  hence "TargetTerm (\<lbrakk>S\<rbrakk>) \<longmapsto>(STCal Source Target)* (TargetTerm T)"
    by (simp add: STCal_steps(2))
  ultimately obtain Q' where A5: "SourceTerm S \<longmapsto>(STCal Source Target)* Q'"
                         and A6: "(TargetTerm T, Q') \<in> Rel\<inverse>"
    using A3
    by blast
  from A5 obtain S' where A7: "S' \<in>S Q'" and A8: "S \<longmapsto>Source* S'"
    by (auto simp add: STCal_steps(1))
  from A6 have "(Q', TargetTerm T) \<in> Rel"
    by induct
  with A2 A7 have "(\<lbrakk>S'\<rbrakk>, T) \<in> TRel\<^sup>*"
    by simp
  with A8 show "\<exists>S'. S \<longmapsto>Source* S' \<and> (\<lbrakk>S'\<rbrakk>, T) \<in> TRel\<^sup>*"
    by blast
qed

lemma (in encodingLS) weak_labelled_simulation_impl_OSou:
  fixes Rel  :: "(('procS, 'procT) Proc \<times> ('procS, 'procT) Proc) set"
    and TRel :: "('procT \<times> 'procT) set"
  assumes rel:  "\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel"
      and trel: "\<forall>S T. (SourceTerm S, TargetTerm T) \<in> Rel \<longrightarrow> (\<lbrakk>S\<rbrakk>, T) \<in> TRel\<^sup>*"
      and sim:  "weak_labelled_simulation (Rel\<inverse>) (STLCal Source Target)"
  shows "operational_sound (TRel\<^sup>*)"
proof clarify
  fix S \<beta> T
  obtain \<beta>' where A1: "\<beta> \<in>TL \<langle>TargetTerm (\<lbrakk>S\<rbrakk>), \<beta>'\<rangle>"
    unfolding getTargetLabel_def
    by blast
  from rel have "(TargetTerm (\<lbrakk>S\<rbrakk>), SourceTerm S) \<in> Rel\<inverse>"
    by simp
  moreover assume "\<lbrakk>S\<rbrakk> \<midarrow>\<Zcat>\<beta>\<rightarrow>Target* T"
  with A1 have "TargetTerm (\<lbrakk>S\<rbrakk>) \<midarrow>\<Zcat>\<beta>'\<rightarrow>(STLCal Source Target)* (TargetTerm T)"
    using STLCal_weakLabelledSteps(2)[of "\<lbrakk>S\<rbrakk>" \<beta>' "TargetTerm T"]
    by blast
  ultimately obtain P' where A2: "SourceTerm S \<midarrow>\<Zcat>\<beta>'\<rightarrow>(STLCal Source Target)* P'"
                         and A3: "(TargetTerm T, P') \<in> Rel\<inverse>"
    using sim
    by blast
  from A2 obtain \<beta>'' S' where A4: "\<beta>'' \<in>SL \<langle>SourceTerm S, \<beta>'\<rangle>" and A5: "S' \<in>S P'"
                          and A6: "S \<midarrow>\<Zcat>\<beta>''\<rightarrow>Source* S'"
    using STLCal_weakLabelledSteps(1)[of S \<beta>' P']
    by blast
  from A3 have "(P', TargetTerm T) \<in> Rel"
    by induct
  with trel A5 have "(\<lbrakk>S'\<rbrakk>, T) \<in> TRel\<^sup>*"
    by simp
  with A6 show "\<exists>\<alpha> S'. S \<midarrow>\<Zcat>\<alpha>\<rightarrow>Source* S' \<and> (\<lbrakk>S'\<rbrakk>, T) \<in> TRel\<^sup>*"
    by blast
qed

lemma (in encodingLS_encL) weak_labelled_simulation_impl_OSou_encL:
  fixes Rel  :: "(('procS, 'procT) Proc \<times> ('procS, 'procT) Proc) set"
    and TRel :: "('procT \<times> 'procT) set"
  assumes rel:  "\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel"
      and trel: "\<forall>S T. (SourceTerm S, TargetTerm T) \<in> Rel \<longrightarrow> (\<lbrakk>S\<rbrakk>, T) \<in> TRel\<^sup>*"
      and sim:  "weak_labelled_simulation_encL (Rel\<inverse>)"
  shows "operational_sound_encL (TRel\<^sup>*)"
proof clarify
  fix S \<beta> T
  obtain \<beta>' where A1: "\<beta> \<in>TL \<langle>TargetTerm (\<lbrakk>S\<rbrakk>), \<beta>'\<rangle>"
    unfolding getTargetLabel_def
    by blast
  from rel have "(TargetTerm (\<lbrakk>S\<rbrakk>), SourceTerm S) \<in> Rel\<inverse>"
    by simp
  moreover assume "\<lbrakk>S\<rbrakk> \<midarrow>\<Zcat>\<beta>\<rightarrow>Target* T"
  with A1 have "TargetTerm (\<lbrakk>S\<rbrakk>) \<midarrow>\<Zcat>\<beta>'\<rightarrow>(STLCal Source Target)* (TargetTerm T)"
    using STLCal_weakLabelledSteps(2)[of "\<lbrakk>S\<rbrakk>" \<beta>' "TargetTerm T"]
    by blast
  ultimately obtain \<alpha>' P' where A2: "SourceTerm S \<midarrow>\<Zcat>\<alpha>'\<rightarrow>(STLCal Source Target)* P'"
                            and A3: "(TargetTerm T, P') \<in> Rel\<inverse>"
                            and A4: "\<langle>TargetTerm (\<lbrakk>S\<rbrakk>), \<beta>'\<rangle> \<equiv>\<lparr>\<rparr> \<langle>SourceTerm S, \<alpha>'\<rangle>"
    using sim
    by blast
  from A2 obtain \<alpha> S' where A5: "\<alpha> \<in>SL \<langle>SourceTerm S, \<alpha>'\<rangle>" and A6: "S' \<in>S P'"
                        and A7: "S \<midarrow>\<Zcat>\<alpha>\<rightarrow>Source* S'"
    using STLCal_weakLabelledSteps(1)[of S \<alpha>' P']
    by blast
  from A3 have "(P', TargetTerm T) \<in> Rel"
    by induct
  with trel A6 have A8: "(\<lbrakk>S'\<rbrakk>, T) \<in> TRel\<^sup>*"
    by simp
  from A4 have "\<lparr>SourceTerm S, \<alpha>'\<rparr>\<mapsto>\<langle>TargetTerm (\<lbrakk>S\<rbrakk>), \<beta>'\<rangle>"
    using kinds_of_encoded_label(1)[of "TargetTerm (\<lbrakk>S\<rbrakk>)" \<beta>' "SourceTerm S" \<alpha>']
    unfolding related_labels_def
    by blast
  with A1 A5 have "\<lblot>\<alpha>\<rblot> = \<beta>"
    unfolding encLST_def getSourceLabel_def getTargetLabel_def
    by blast
  with A7 A8 show "\<exists>\<alpha> S'. S \<midarrow>\<Zcat>\<alpha>\<rightarrow>Source* S' \<and> (\<lbrakk>S'\<rbrakk>, T) \<in> TRel\<^sup>* \<and> \<lblot>\<alpha>\<rblot> = \<beta>"
    by blast
qed

lemma (in encoding) OSou_iff_inverse_of_indRelRTPO_is_weak_reduction_simulation:
  fixes TRel :: "('procT \<times> 'procT) set"
  shows "(operational_sound (TRel\<^sup>*)
         \<and> weak_reduction_simulation ((TRel\<^sup>+)\<inverse>) Target)
         = weak_reduction_simulation ((indRelRTPO TRel)\<inverse>) (STCal Source Target)"
proof (rule iffI, erule conjE)
  assume os:  "operational_sound (TRel\<^sup>*)"
     and sim: "weak_reduction_simulation ((TRel\<^sup>+)\<inverse>) Target"
  show "weak_reduction_simulation ((indRelRTPO TRel)\<inverse>) (STCal Source Target)"
  proof clarify
    fix P Q P'
    assume "Q \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> P" and "P \<longmapsto>(STCal Source Target)* P'"
    thus "\<exists>Q'. Q \<longmapsto>(STCal Source Target)* Q' \<and> (P', Q') \<in> (indRelRTPO TRel)\<inverse>"
    proof (induct arbitrary: P')
      case (encR S)
      assume "TargetTerm (\<lbrakk>S\<rbrakk>) \<longmapsto>(STCal Source Target)* P'"
      from this obtain T where A1: "T \<in>T P'" and A2: "\<lbrakk>S\<rbrakk> \<longmapsto>Target* T"
        by (auto simp add: STCal_steps(2))
      from os A2 obtain S' where A3: "S \<longmapsto>Source* S'" and A4: "(\<lbrakk>S'\<rbrakk>, T) \<in> TRel\<^sup>*"
        by blast
      from A3 have "SourceTerm S \<longmapsto>(STCal Source Target)* (SourceTerm S')"
        by (simp add: STCal_steps(1))
      moreover have "SourceTerm S' \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> P'"
      proof -
        from A4 have "\<lbrakk>S'\<rbrakk> = T \<or> (\<lbrakk>S'\<rbrakk>, T) \<in> TRel\<^sup>+"
          using rtrancl_eq_or_trancl[of "\<lbrakk>S'\<rbrakk>" T TRel]
          by blast
        moreover have A5: "SourceTerm S' \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> TargetTerm (\<lbrakk>S'\<rbrakk>)"
          by (simp add: indRelRTPO.encR)
        with A1 have "\<lbrakk>S'\<rbrakk> = T \<Longrightarrow> SourceTerm S' \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> P'"
          by simp
        moreover have "(\<lbrakk>S'\<rbrakk>, T) \<in> TRel\<^sup>+ \<Longrightarrow> SourceTerm S' \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> P'"
        proof -
          assume "(\<lbrakk>S'\<rbrakk>, T) \<in> TRel\<^sup>+"
          hence "TargetTerm (\<lbrakk>S'\<rbrakk>) \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> TargetTerm T"
            by (rule transitive_closure_of_TRel_to_indRelRTPO)
          with A5 have "SourceTerm S' \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> TargetTerm T"
            by (rule indRelRTPO.trans)
          with A1 show "SourceTerm S' \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> P'"
            by simp
        qed
        ultimately show "SourceTerm S' \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> P'"
          by blast
      qed
      hence "(P', SourceTerm S') \<in> (indRelRTPO TRel)\<inverse>"
        by simp
      ultimately
      show "\<exists>Q'. SourceTerm S \<longmapsto>(STCal Source Target)* Q' \<and> (P', Q') \<in> (indRelRTPO TRel)\<inverse>"
        by blast
    next
      case (source S)
      then obtain S' where B1: "S' \<in>S P'"
        by (auto simp add: STCal_steps(1))
      hence "(P', P') \<in> (indRelRTPO TRel)\<inverse>"
        by (simp add: indRelRTPO.source)
      with source
      show "\<exists>Q'. SourceTerm S \<longmapsto>(STCal Source Target)* Q' \<and> (P', Q') \<in> (indRelRTPO TRel)\<inverse>"
        by blast
    next
      case (target T1 T2)
      assume "TargetTerm T2 \<longmapsto>(STCal Source Target)* P'"
      from this obtain T2' where C1: "T2' \<in>T P'" and C2: "T2 \<longmapsto>Target* T2'"
        by (auto simp add: STCal_steps(2))
      assume "(T1, T2) \<in> TRel"
      hence "(T2, T1) \<in> (TRel\<^sup>+)\<inverse>"
        by simp
      with C2 sim obtain T1' where C3: "T1 \<longmapsto>Target* T1'" and C4: "(T2', T1') \<in> (TRel\<^sup>+)\<inverse>"
        by blast
      from C3 have "TargetTerm T1 \<longmapsto>(STCal Source Target)* (TargetTerm T1')"
        by (simp add: STCal_steps(2))
      moreover from C4 have "(T1', T2') \<in> TRel\<^sup>+"
        by induct
      hence "TargetTerm T1' \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> TargetTerm T2'"
        by (rule transitive_closure_of_TRel_to_indRelRTPO)
      with C1 have "(P', TargetTerm T1') \<in> (indRelRTPO TRel)\<inverse>"
        by simp
      ultimately
      show "\<exists>Q'. TargetTerm T1 \<longmapsto>(STCal Source Target)* Q' \<and> (P', Q') \<in> (indRelRTPO TRel)\<inverse>"
        by blast
    next
      case (trans P Q R R')
      assume "R \<longmapsto>(STCal Source Target)* R'"
         and "\<And>R'. R \<longmapsto>(STCal Source Target)* R'
              \<Longrightarrow> \<exists>Q'. Q \<longmapsto>(STCal Source Target)* Q' \<and> (R', Q') \<in> (indRelRTPO TRel)\<inverse>"
      from this obtain Q' where D1: "Q \<longmapsto>(STCal Source Target)* Q'"
                            and D2: "(R', Q') \<in> (indRelRTPO TRel)\<inverse>"
        by blast
      assume "\<And>Q'. Q \<longmapsto>(STCal Source Target)* Q'
              \<Longrightarrow> \<exists>P'. P \<longmapsto>(STCal Source Target)* P' \<and> (Q', P') \<in> (indRelRTPO TRel)\<inverse>"
      with D1 obtain P' where D3: "P \<longmapsto>(STCal Source Target)* P'"
                          and D4: "(Q', P') \<in> (indRelRTPO TRel)\<inverse>"
        by blast
      from D4 D2 have "(R', P') \<in> (indRelRTPO TRel)\<inverse>"
        by (simp add: indRelRTPO.trans[where P="P'" and Q="Q'" and R="R'"])
      with D3 show "\<exists>P'. P \<longmapsto>(STCal Source Target)* P' \<and> (R', P') \<in> (indRelRTPO TRel)\<inverse>"
        by blast
    qed
  qed
next
  have "\<forall>S. SourceTerm S \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> TargetTerm (\<lbrakk>S\<rbrakk>)"
    by (simp add: indRelRTPO.encR)
  moreover have "\<forall>S T. SourceTerm S \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> TargetTerm T \<longrightarrow> (\<lbrakk>S\<rbrakk>, T) \<in> TRel\<^sup>*"
    using indRelRTPO_to_TRel(2)[where TRel="TRel"] trans_closure_of_TRel_refl_cond
    by simp
  moreover
  assume sim: "weak_reduction_simulation ((indRelRTPO TRel)\<inverse>) (STCal Source Target)"
  ultimately have "operational_sound (TRel\<^sup>*)"
    using weak_reduction_simulation_impl_OSou[where Rel="indRelRTPO TRel" and TRel="TRel"]
    by simp
  moreover from sim have "weak_reduction_simulation ((TRel\<^sup>+)\<inverse>) Target"
    using indRelRTPO_impl_TRel_is_weak_reduction_simulation_rev[where TRel="TRel"]
    by simp
  ultimately show "operational_sound (TRel\<^sup>*) \<and> weak_reduction_simulation ((TRel\<^sup>+)\<inverse>) Target"
    by simp
qed

lemma (in encodingLS_encL) OSou_iff_inverse_of_indRelRTPO_is_weak_labelled_simulation_encL:
  fixes TRel :: "('procT \<times> 'procT) set"
  shows "(operational_sound_encL (TRel\<^sup>*)
         \<and> weak_labelled_simulation ((TRel\<^sup>+)\<inverse>) Target)
         = weak_labelled_simulation_encL ((indRelRTPO TRel)\<inverse>)"
proof (rule iffI, erule conjE)
  assume os:  "operational_sound_encL (TRel\<^sup>*)"
     and sim: "weak_labelled_simulation ((TRel\<^sup>+)\<inverse>) Target"
  show "weak_labelled_simulation_encL ((indRelRTPO TRel)\<inverse>)"
  proof clarify
    fix P Q \<alpha> P'
    assume "Q \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> P" and "P \<midarrow>\<Zcat>\<alpha>\<rightarrow>(STLCal Source Target)* P'"
    thus "\<exists>\<beta> Q'. Q \<midarrow>\<Zcat>\<beta>\<rightarrow>(STLCal Source Target)* Q' \<and> (P', Q') \<in> (indRelRTPO TRel)\<inverse> \<and>
          \<langle>P, \<alpha>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>Q, \<beta>\<rangle>"
    proof (induct arbitrary: \<alpha> P')
      case (encR S)
      assume "TargetTerm (\<lbrakk>S\<rbrakk>) \<midarrow>\<Zcat>\<alpha>\<rightarrow>(STLCal Source Target)* P'"
      then obtain \<alpha>' T where A1: "\<alpha>' \<in>TL \<langle>TargetTerm (\<lbrakk>S\<rbrakk>), \<alpha>\<rangle>" and A2: "T \<in>T P'"
                         and A3: "\<lbrakk>S\<rbrakk> \<midarrow>\<Zcat>\<alpha>'\<rightarrow>Target* T"
        using STLCal_weakLabelledSteps(2)[of "\<lbrakk>S\<rbrakk>" \<alpha> P']
        by blast
      from os A3 obtain \<beta>' S' where A4: "S \<midarrow>\<Zcat>\<beta>'\<rightarrow>Source* S'" and A5: "(\<lbrakk>S'\<rbrakk>, T) \<in> TRel\<^sup>*"
                                and A6: "\<lblot>\<beta>'\<rblot> = \<alpha>'"
        by blast
      obtain \<beta> where A7: "\<beta>' \<in>SL \<langle>SourceTerm S, \<beta>\<rangle>"
        unfolding getSourceLabel_def
        by blast
      with A4 have "SourceTerm S \<midarrow>\<Zcat>\<beta>\<rightarrow>(STLCal Source Target)* (SourceTerm S')"
        using STLCal_weakLabelledSteps(1)[of S \<beta> "SourceTerm S'"]
        by blast
      moreover have "SourceTerm S' \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> P'"
      proof -
        from A5 have "\<lbrakk>S'\<rbrakk> = T \<or> (\<lbrakk>S'\<rbrakk>, T) \<in> TRel\<^sup>+"
          using rtrancl_eq_or_trancl[of "\<lbrakk>S'\<rbrakk>" T TRel]
          by blast
        moreover have A5: "SourceTerm S' \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> TargetTerm (\<lbrakk>S'\<rbrakk>)"
          by (simp add: indRelRTPO.encR)
        with A2 have "\<lbrakk>S'\<rbrakk> = T \<Longrightarrow> SourceTerm S' \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> P'"
          by simp
        moreover have "(\<lbrakk>S'\<rbrakk>, T) \<in> TRel\<^sup>+ \<Longrightarrow> SourceTerm S' \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> P'"
        proof -
          assume "(\<lbrakk>S'\<rbrakk>, T) \<in> TRel\<^sup>+"
          hence "TargetTerm (\<lbrakk>S'\<rbrakk>) \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> TargetTerm T"
            by (rule transitive_closure_of_TRel_to_indRelRTPO)
          with A5 have "SourceTerm S' \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> TargetTerm T"
            by (rule indRelRTPO.trans)
          with A2 show "SourceTerm S' \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> P'"
            by simp
        qed
        ultimately show "SourceTerm S' \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> P'"
          by blast
      qed
      hence "(P', SourceTerm S') \<in> (indRelRTPO TRel)\<inverse>"
        by simp
      moreover from A1 A6 A7 have "\<lparr>SourceTerm S, \<beta>\<rparr>\<mapsto>\<langle>TargetTerm (\<lbrakk>S\<rbrakk>), \<alpha>\<rangle>"
        unfolding encLST_def
        by blast
      hence "\<langle>TargetTerm (\<lbrakk>S\<rbrakk>), \<alpha>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>SourceTerm S, \<beta>\<rangle>"
        unfolding related_labels_def
        by simp
      ultimately show "\<exists>\<beta> Q'. SourceTerm S \<midarrow>\<Zcat>\<beta>\<rightarrow>(STLCal Source Target)* Q' \<and>
                       (P', Q') \<in> (indRelRTPO TRel)\<inverse> \<and> \<langle>TargetTerm (\<lbrakk>S\<rbrakk>), \<alpha>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>SourceTerm S, \<beta>\<rangle>"
        by blast
    next
      case (source S)
      assume A1: "SourceTerm S \<midarrow>\<Zcat>\<alpha>\<rightarrow>(STLCal Source Target)* P'"
      then obtain S' where "S' \<in>S P'"
        using STLCal_weakLabelledSteps(1)[of S \<alpha> P']
        by blast
      hence A2: "(P', P') \<in> (indRelRTPO TRel)\<inverse>"
        by (simp add: indRelRTPO.source)
      have "\<langle>SourceTerm S, \<alpha>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>SourceTerm S, \<alpha>\<rangle>"
        unfolding related_labels_def
        by simp
      with A1 A2 show "\<exists>\<beta> Q'. SourceTerm S \<midarrow>\<Zcat>\<beta>\<rightarrow>(STLCal Source Target)* Q' \<and>
                       (P', Q') \<in> (indRelRTPO TRel)\<inverse> \<and> \<langle>SourceTerm S, \<alpha>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>SourceTerm S, \<beta>\<rangle>"
        by blast
    next
      case (target T1 T2)
      assume "TargetTerm T2 \<midarrow>\<Zcat>\<alpha>\<rightarrow>(STLCal Source Target)* P'"
      then obtain \<alpha>' T2' where A1: "\<alpha>' \<in>TL \<langle>TargetTerm T2, \<alpha>\<rangle>" and A2: "T2' \<in>T P'"
                           and A3: "T2 \<midarrow>\<Zcat>\<alpha>'\<rightarrow>Target* T2'"
        using STLCal_weakLabelledSteps(2)[of T2 \<alpha> P']
        by blast
      assume "(T1, T2) \<in> TRel"
      hence "(T2, T1) \<in> (TRel\<^sup>+)\<inverse>"
        by simp
      with sim A3 obtain T1' where A4: "T1 \<midarrow>\<Zcat>\<alpha>'\<rightarrow>Target* T1'" and A5: "(T2', T1') \<in> (TRel\<^sup>+)\<inverse>"
        by blast
      from A1 A4 have "TargetTerm T1 \<midarrow>\<Zcat>\<alpha>\<rightarrow>(STLCal Source Target)* (TargetTerm T1')"
        using STLCal_weakLabelledSteps(2)[of T1 \<alpha> "TargetTerm T1'"]
        unfolding getTargetLabel_def
        by blast
      moreover from A5 have "(T1', T2') \<in> TRel\<^sup>+"
        by induct
      hence "TargetTerm T1' \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> TargetTerm T2'"
        by (rule transitive_closure_of_TRel_to_indRelRTPO)
      with A2 have "(P', TargetTerm T1') \<in> (indRelRTPO TRel)\<inverse>"
        by simp
      moreover have "\<langle>TargetTerm T2, \<alpha>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>TargetTerm T1, \<alpha>\<rangle>"
        unfolding related_labels_def
        by simp
      ultimately show "\<exists>\<beta> Q'. TargetTerm T1 \<midarrow>\<Zcat>\<beta>\<rightarrow>(STLCal Source Target)* Q' \<and>
                       (P', Q') \<in> (indRelRTPO TRel)\<inverse> \<and> \<langle>TargetTerm T2, \<alpha>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>TargetTerm T1, \<beta>\<rangle>"
        by blast
    next
      case (trans P Q R \<gamma> R')
      assume "R \<midarrow>\<Zcat>\<gamma>\<rightarrow>(STLCal Source Target)* R'"
         and "\<And>\<gamma> R'. R \<midarrow>\<Zcat>\<gamma>\<rightarrow>(STLCal Source Target)* R' \<Longrightarrow>
              \<exists>\<beta> Q'. Q \<midarrow>\<Zcat>\<beta>\<rightarrow>(STLCal Source Target)* Q' \<and> (R', Q') \<in> (indRelRTPO TRel)\<inverse> \<and>
              \<langle>R, \<gamma>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>Q, \<beta>\<rangle>"
      then obtain \<beta> Q' where A1: "Q \<midarrow>\<Zcat>\<beta>\<rightarrow>(STLCal Source Target)* Q'"
                         and A2: "(R', Q') \<in> (indRelRTPO TRel)\<inverse>" and A3: "\<langle>R, \<gamma>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>Q, \<beta>\<rangle>"
        by blast
      assume "\<And>\<beta> Q'. Q \<midarrow>\<Zcat>\<beta>\<rightarrow>(STLCal Source Target)* Q' \<Longrightarrow>
              \<exists>\<alpha> P'. P \<midarrow>\<Zcat>\<alpha>\<rightarrow>(STLCal Source Target)* P' \<and> (Q', P') \<in> (indRelRTPO TRel)\<inverse> \<and>
              \<langle>Q, \<beta>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>P, \<alpha>\<rangle>"
      with A1 obtain \<alpha> P' where A4: "P \<midarrow>\<Zcat>\<alpha>\<rightarrow>(STLCal Source Target)* P'"
                            and A5: "(Q', P') \<in> (indRelRTPO TRel)\<inverse>" and A6: "\<langle>Q, \<beta>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>P, \<alpha>\<rangle>"
        by blast
      from A2 A5 have A7: "(R', P') \<in> (indRelRTPO TRel)\<inverse>"
        using indRelRTPO.trans[of P' Q' TRel R']
        by simp
      assume "P \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> Q"
      hence A8: "\<not>(P \<in> ProcT \<and> Q \<in> ProcS)"
        using indRelRTPO_to_TRel(3)[of P Q TRel]
        by blast
      assume "Q \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> R"
      hence "\<not>(Q \<in> ProcT \<and> R \<in> ProcS)"
        using indRelRTPO_to_TRel(3)[of Q R TRel]
        by blast
      with A3 A6 A8 have "\<langle>R, \<gamma>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>P, \<alpha>\<rangle>"
        using related_labels_trans_no_T_to_S[of P \<alpha> Q \<beta> R \<gamma>] related_labels_sym[of Q \<beta> P \<alpha>]
              related_labels_sym[of R \<gamma> Q \<beta>] related_labels_sym[of P \<alpha> R \<gamma>]
        by simp
      with A4 A7 show "\<exists>\<alpha> P'. P \<midarrow>\<Zcat>\<alpha>\<rightarrow>(STLCal Source Target)* P' \<and> (R', P') \<in> (indRelRTPO TRel)\<inverse> \<and>
                       \<langle>R, \<gamma>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>P, \<alpha>\<rangle>"
        by blast
    qed
  qed
next
  have "\<forall>S. SourceTerm S \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> TargetTerm (\<lbrakk>S\<rbrakk>)"
    by (simp add: indRelRTPO.encR)
  moreover have "\<forall>S T. SourceTerm S \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> TargetTerm T \<longrightarrow> (\<lbrakk>S\<rbrakk>, T) \<in> TRel\<^sup>*"
    using indRelRTPO_to_TRel(2)[where TRel="TRel"] trans_closure_of_TRel_refl_cond
    by simp
  moreover assume sim: "weak_labelled_simulation_encL ((indRelRTPO TRel)\<inverse>)"
  ultimately have "operational_sound_encL (TRel\<^sup>*)"
    using weak_labelled_simulation_impl_OSou_encL[where Rel="indRelRTPO TRel" and TRel="TRel"]
    by simp
  moreover from sim have "weak_labelled_simulation ((TRel\<^sup>+)\<inverse>) Target"
    using indRelRTPO_impl_TRel_is_weak_labelled_simulation_encL_rev[where TRel="TRel"]
    by simp
  ultimately show "operational_sound_encL (TRel\<^sup>*) \<and> weak_labelled_simulation ((TRel\<^sup>+)\<inverse>) Target"
    by simp
qed

lemma (in encoding) OSou_iff_weak_reduction_simulation:
  fixes TRel :: "('procT \<times> 'procT) set"
  shows "(operational_sound (TRel\<^sup>*)
         \<and> weak_reduction_simulation ((TRel\<^sup>+)\<inverse>) Target)
         = (\<exists>Rel. (\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel)
            \<and> (\<forall>T1 T2. (T1, T2) \<in> TRel \<longrightarrow> (TargetTerm T1, TargetTerm T2) \<in> Rel)
            \<and> (\<forall>T1 T2. (TargetTerm T1, TargetTerm T2) \<in> Rel \<longrightarrow> (T1, T2) \<in> TRel\<^sup>+)
            \<and> (\<forall>S T. (SourceTerm S, TargetTerm T) \<in> Rel \<longrightarrow> (\<lbrakk>S\<rbrakk>, T) \<in> TRel\<^sup>*)
            \<and> weak_reduction_simulation (Rel\<inverse>) (STCal Source Target))"
proof (rule iffI, erule conjE)
  have "\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> indRelRTPO TRel"
    by (simp add: indRelRTPO.encR)
  moreover have "\<forall>T1 T2. (T1, T2) \<in> TRel \<longrightarrow> TargetTerm T1 \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> TargetTerm T2"
    by (simp add: indRelRTPO.target)
  moreover have "\<forall>T1 T2. TargetTerm T1 \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> TargetTerm T2 \<longrightarrow> (T1, T2) \<in> TRel\<^sup>+"
    using indRelRTPO_to_TRel(4)[where TRel="TRel"]
    by simp
  moreover have "\<forall>S T. SourceTerm S \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> TargetTerm T \<longrightarrow> (\<lbrakk>S\<rbrakk>, T) \<in> TRel\<^sup>*"
    using indRelRTPO_to_TRel(2)[where TRel="TRel"] trans_closure_of_TRel_refl_cond
    by simp
  moreover assume "operational_sound (TRel\<^sup>*)"
              and "weak_reduction_simulation ((TRel\<^sup>+)\<inverse>) Target"
  hence "weak_reduction_simulation ((indRelRTPO TRel)\<inverse>) (STCal Source Target)"
    using OSou_iff_inverse_of_indRelRTPO_is_weak_reduction_simulation[where TRel="TRel"]
    by simp
  ultimately show "\<exists>Rel. (\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel)
                   \<and> (\<forall>T1 T2. (T1, T2) \<in> TRel \<longrightarrow> (TargetTerm T1, TargetTerm T2) \<in> Rel)
                   \<and> (\<forall>T1 T2. (TargetTerm T1, TargetTerm T2) \<in> Rel \<longrightarrow> (T1, T2) \<in> TRel\<^sup>+)
                   \<and> (\<forall>S T. (SourceTerm S, TargetTerm T) \<in> Rel \<longrightarrow> (\<lbrakk>S\<rbrakk>, T) \<in> TRel\<^sup>*)
                   \<and> weak_reduction_simulation (Rel\<inverse>) (STCal Source Target)"
    by blast
next
  assume "\<exists>Rel. (\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel)
          \<and> (\<forall>T1 T2. (T1, T2) \<in> TRel \<longrightarrow> (TargetTerm T1, TargetTerm T2) \<in> Rel)
          \<and> (\<forall>T1 T2. (TargetTerm T1, TargetTerm T2) \<in> Rel \<longrightarrow> (T1, T2) \<in> TRel\<^sup>+)
          \<and> (\<forall>S T. (SourceTerm S, TargetTerm T) \<in> Rel \<longrightarrow> (\<lbrakk>S\<rbrakk>, T) \<in> TRel\<^sup>*)
          \<and> weak_reduction_simulation (Rel\<inverse>) (STCal Source Target)"
  from this obtain Rel where A1: "\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel"
    and A2: "\<forall>T1 T2. (T1, T2) \<in> TRel \<longrightarrow> (TargetTerm T1, TargetTerm T2) \<in> Rel"
    and A3: "\<forall>T1 T2. (TargetTerm T1, TargetTerm T2) \<in> Rel \<longrightarrow> (T1, T2) \<in> TRel\<^sup>+"
    and A4: "\<forall>S T. (SourceTerm S, TargetTerm T) \<in> Rel \<longrightarrow> (\<lbrakk>S\<rbrakk>, T) \<in> TRel\<^sup>*"
    and A5: "weak_reduction_simulation (Rel\<inverse>) (STCal Source Target)"
    by blast
  from A1 A4 A5 have "operational_sound (TRel\<^sup>*)"
    using weak_reduction_simulation_impl_OSou[where Rel="Rel" and TRel="TRel"]
    by simp
  moreover from A2 A3 A5 have "weak_reduction_simulation ((TRel\<^sup>+)\<inverse>) Target"
    using rel_with_target_impl_transC_TRel_is_weak_reduction_simulation_rev[where Rel="Rel" and
            TRel="TRel"]
    by simp
  ultimately show "operational_sound (TRel\<^sup>*) \<and> weak_reduction_simulation ((TRel\<^sup>+)\<inverse>) Target"
    by simp
qed

lemma (in encodingLS_encL) OSou_iff_weak_labelled_simulation_encL:
  fixes TRel :: "('procT \<times> 'procT) set"
  shows "(operational_sound_encL (TRel\<^sup>*)
         \<and> weak_labelled_simulation ((TRel\<^sup>+)\<inverse>) Target)
         = (\<exists>Rel. (\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel)
            \<and> (\<forall>T1 T2. (T1, T2) \<in> TRel \<longrightarrow> (TargetTerm T1, TargetTerm T2) \<in> Rel)
            \<and> (\<forall>T1 T2. (TargetTerm T1, TargetTerm T2) \<in> Rel \<longrightarrow> (T1, T2) \<in> TRel\<^sup>+)
            \<and> (\<forall>S T. (SourceTerm S, TargetTerm T) \<in> Rel \<longrightarrow> (\<lbrakk>S\<rbrakk>, T) \<in> TRel\<^sup>*)
            \<and> weak_labelled_simulation_encL (Rel\<inverse>))"
proof (rule iffI, erule conjE)
  have "\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> indRelRTPO TRel"
    by (simp add: indRelRTPO.encR)
  moreover have "\<forall>T1 T2. (T1, T2) \<in> TRel \<longrightarrow> TargetTerm T1 \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> TargetTerm T2"
    by (simp add: indRelRTPO.target)
  moreover have "\<forall>T1 T2. TargetTerm T1 \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> TargetTerm T2 \<longrightarrow> (T1, T2) \<in> TRel\<^sup>+"
    using indRelRTPO_to_TRel(4)[where TRel="TRel"]
    by simp
  moreover have "\<forall>S T. SourceTerm S \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> TargetTerm T \<longrightarrow> (\<lbrakk>S\<rbrakk>, T) \<in> TRel\<^sup>*"
    using indRelRTPO_to_TRel(2)[where TRel="TRel"] trans_closure_of_TRel_refl_cond
    by simp
  moreover assume "operational_sound_encL (TRel\<^sup>*)"
              and "weak_labelled_simulation ((TRel\<^sup>+)\<inverse>) Target"
  hence "weak_labelled_simulation_encL ((indRelRTPO TRel)\<inverse>)"
    using OSou_iff_inverse_of_indRelRTPO_is_weak_labelled_simulation_encL[where TRel="TRel"]
    by simp
  ultimately show "\<exists>Rel. (\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel)
                   \<and> (\<forall>T1 T2. (T1, T2) \<in> TRel \<longrightarrow> (TargetTerm T1, TargetTerm T2) \<in> Rel)
                   \<and> (\<forall>T1 T2. (TargetTerm T1, TargetTerm T2) \<in> Rel \<longrightarrow> (T1, T2) \<in> TRel\<^sup>+)
                   \<and> (\<forall>S T. (SourceTerm S, TargetTerm T) \<in> Rel \<longrightarrow> (\<lbrakk>S\<rbrakk>, T) \<in> TRel\<^sup>*)
                   \<and> weak_labelled_simulation_encL (Rel\<inverse>)"
    by blast
next
  assume "\<exists>Rel. (\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel)
          \<and> (\<forall>T1 T2. (T1, T2) \<in> TRel \<longrightarrow> (TargetTerm T1, TargetTerm T2) \<in> Rel)
          \<and> (\<forall>T1 T2. (TargetTerm T1, TargetTerm T2) \<in> Rel \<longrightarrow> (T1, T2) \<in> TRel\<^sup>+)
          \<and> (\<forall>S T. (SourceTerm S, TargetTerm T) \<in> Rel \<longrightarrow> (\<lbrakk>S\<rbrakk>, T) \<in> TRel\<^sup>*)
          \<and> weak_labelled_simulation_encL (Rel\<inverse>)"
  from this obtain Rel where A1: "\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel"
    and A2: "\<forall>T1 T2. (T1, T2) \<in> TRel \<longrightarrow> (TargetTerm T1, TargetTerm T2) \<in> Rel"
    and A3: "\<forall>T1 T2. (TargetTerm T1, TargetTerm T2) \<in> Rel \<longrightarrow> (T1, T2) \<in> TRel\<^sup>+"
    and A4: "\<forall>S T. (SourceTerm S, TargetTerm T) \<in> Rel \<longrightarrow> (\<lbrakk>S\<rbrakk>, T) \<in> TRel\<^sup>*"
    and A5: "weak_labelled_simulation_encL (Rel\<inverse>)"
    by blast
  from A1 A4 A5 have "operational_sound_encL (TRel\<^sup>*)"
    using weak_labelled_simulation_impl_OSou_encL[where Rel="Rel" and TRel="TRel"]
    by simp
  moreover from A2 A3 A5 have "weak_labelled_simulation ((TRel\<^sup>+)\<inverse>) Target"
    using rel_with_target_impl_transC_TRel_is_weak_labelled_simulation_encL_rev[where Rel="Rel" and
            TRel="TRel"]
    by simp
  ultimately show "operational_sound_encL (TRel\<^sup>*) \<and> weak_labelled_simulation ((TRel\<^sup>+)\<inverse>) Target"
    by simp
qed

text \<open>An encoding is strongly operational sound modulo a relation TRel whose inverse is a strong
      reduction simulation on target terms iff there is a relation, like indRelRTPO, that relates
      at least all source terms to their literal translations, includes TRel, and whose inverse is
      a strong simulation.\<close>

lemma (in encoding) strong_reduction_simulation_impl_SOSou:
  fixes Rel  :: "(('procS, 'procT) Proc \<times> ('procS, 'procT) Proc) set"
    and TRel :: "('procT \<times> 'procT) set"
  assumes A1: "\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel"
      and A2: "\<forall>S T. (SourceTerm S, TargetTerm T) \<in> Rel \<longrightarrow> (\<lbrakk>S\<rbrakk>, T) \<in> TRel\<^sup>*"
      and A3: "strong_reduction_simulation (Rel\<inverse>) (STCal Source Target)"
  shows "strongly_operational_sound (TRel\<^sup>*)"
proof clarify
  fix S T
  from A1 have "(TargetTerm (\<lbrakk>S\<rbrakk>), SourceTerm S) \<in> Rel\<inverse>"
    by simp
  moreover assume "\<lbrakk>S\<rbrakk> \<longmapsto>Target T"
  hence "TargetTerm (\<lbrakk>S\<rbrakk>) \<longmapsto>(STCal Source Target) (TargetTerm T)"
    by (simp add: STCal_step(2))
  ultimately obtain Q' where A5: "SourceTerm S \<longmapsto>(STCal Source Target) Q'"
                         and A6: "(TargetTerm T, Q') \<in> Rel\<inverse>"
    using A3
    by blast
  from A5 obtain S' where A7: "S' \<in>S Q'" and A8: "S \<longmapsto>Source S'"
    by (auto simp add: STCal_step(1))
  from A6 have "(Q', TargetTerm T) \<in> Rel"
    by induct
  with A2 A7 have "(\<lbrakk>S'\<rbrakk>, T) \<in> TRel\<^sup>*"
    by simp
  with A8 show "\<exists>S'. S \<longmapsto>Source S' \<and> (\<lbrakk>S'\<rbrakk>, T) \<in> TRel\<^sup>*"
    by blast
qed

lemma (in encodingLS) strong_labelled_simulation_impl_SOSou:
  fixes Rel  :: "(('procS, 'procT) Proc \<times> ('procS, 'procT) Proc) set"
    and TRel :: "('procT \<times> 'procT) set"
  assumes rel:  "\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel"
      and trel: "\<forall>S T. (SourceTerm S, TargetTerm T) \<in> Rel \<longrightarrow> (\<lbrakk>S\<rbrakk>, T) \<in> TRel\<^sup>*"
      and sim:  "strong_labelled_simulation (Rel\<inverse>) (STLCal Source Target)"
  shows "strongly_operational_sound (TRel\<^sup>*)"
proof clarify
  fix S \<beta> T
  obtain \<beta>' where A1: "\<beta> \<in>TL \<langle>TargetTerm (\<lbrakk>S\<rbrakk>), \<beta>'\<rangle>"
    unfolding getTargetLabel_def
    by blast
  from rel have "(TargetTerm (\<lbrakk>S\<rbrakk>), SourceTerm S) \<in> Rel\<inverse>"
    by simp
  moreover assume "\<lbrakk>S\<rbrakk> \<midarrow>\<beta>\<rightarrow>Target T"
  with A1 have "TargetTerm (\<lbrakk>S\<rbrakk>) \<midarrow>\<beta>'\<rightarrow>(STLCal Source Target) (TargetTerm T)"
    using STLCal_labelledStep(2)[of "\<lbrakk>S\<rbrakk>" \<beta>' "TargetTerm T"]
    by blast
  ultimately obtain Q' where A2: "SourceTerm S \<midarrow>\<beta>'\<rightarrow>(STLCal Source Target) Q'"
                         and A3: "(TargetTerm T, Q') \<in> Rel\<inverse>"
    using sim
    by blast
  from A2 obtain \<beta>'' S' where A4: "\<beta>'' \<in>SL \<langle>SourceTerm S, \<beta>'\<rangle>" and A5: "S' \<in>S Q'"
                          and A6: "S \<midarrow>\<beta>''\<rightarrow>Source S'"
    using STLCal_labelledStep(1)[of S \<beta>' Q']
    by blast
  from A3 have "(Q', TargetTerm T) \<in> Rel"
    by induct
  with trel A5 have "(\<lbrakk>S'\<rbrakk>, T) \<in> TRel\<^sup>*"
    by simp
  with A6 show "\<exists>\<alpha> S'. S \<midarrow>\<alpha>\<rightarrow>Source S' \<and> (\<lbrakk>S'\<rbrakk>, T) \<in> TRel\<^sup>*"
    by blast
qed

lemma (in encodingLS_encL) strong_labelled_simulation_impl_SOSou_encL:
  fixes Rel  :: "(('procS, 'procT) Proc \<times> ('procS, 'procT) Proc) set"
    and TRel :: "('procT \<times> 'procT) set"
  assumes rel:  "\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel"
      and trel: "\<forall>S T. (SourceTerm S, TargetTerm T) \<in> Rel \<longrightarrow> (\<lbrakk>S\<rbrakk>, T) \<in> TRel\<^sup>*"
      and sim:  "strong_labelled_simulation_encL (Rel\<inverse>)"
  shows "strongly_operational_sound_encL (TRel\<^sup>*)"
proof clarify
  fix S \<beta> T
  obtain \<beta>' where A1: "\<beta> \<in>TL \<langle>TargetTerm (\<lbrakk>S\<rbrakk>), \<beta>'\<rangle>"
    unfolding getTargetLabel_def
    by blast
  from rel have "(TargetTerm (\<lbrakk>S\<rbrakk>), SourceTerm S) \<in> Rel\<inverse>"
    by simp
  moreover assume "\<lbrakk>S\<rbrakk> \<midarrow>\<beta>\<rightarrow>Target T"
  with A1 have "TargetTerm (\<lbrakk>S\<rbrakk>) \<midarrow>\<beta>'\<rightarrow>(STLCal Source Target) (TargetTerm T)"
    using STLCal_labelledStep(2)[of "\<lbrakk>S\<rbrakk>" \<beta>' "TargetTerm T"]
    by blast
  ultimately obtain \<alpha>' Q' where A2: "SourceTerm S \<midarrow>\<alpha>'\<rightarrow>(STLCal Source Target) Q'"
                            and A3: "(TargetTerm T, Q') \<in> Rel\<inverse>"
                            and A4: "\<langle>TargetTerm (\<lbrakk>S\<rbrakk>), \<beta>'\<rangle> \<equiv>\<lparr>\<rparr> \<langle>SourceTerm S, \<alpha>'\<rangle>"
    using sim
    by blast
  from A2 obtain \<alpha> S' where A5: "\<alpha> \<in>SL \<langle>SourceTerm S, \<alpha>'\<rangle>" and A6: "S' \<in>S Q'"
                        and A7: "S \<midarrow>\<alpha>\<rightarrow>Source S'"
    using STLCal_labelledStep(1)[of S \<alpha>' Q']
    by blast
  from A3 have "(Q', TargetTerm T) \<in> Rel"
    by induct
  with trel A6 have A8: "(\<lbrakk>S'\<rbrakk>, T) \<in> TRel\<^sup>*"
    by simp
  from A4 have "\<lparr>SourceTerm S, \<alpha>'\<rparr>\<mapsto>\<langle>TargetTerm (\<lbrakk>S\<rbrakk>), \<beta>'\<rangle>"
    using kinds_of_encoded_label(1)[of "TargetTerm (\<lbrakk>S\<rbrakk>)" \<beta>' "SourceTerm S" \<alpha>']
    unfolding related_labels_def
    by blast
  with A1 A5 have "\<lblot>\<alpha>\<rblot> = \<beta>"
    unfolding encLST_def getSourceLabel_def getTargetLabel_def
    by blast
  with A7 A8 show "\<exists>\<alpha> S'. S \<midarrow>\<alpha>\<rightarrow>Source S' \<and> (\<lbrakk>S'\<rbrakk>, T) \<in> TRel\<^sup>* \<and> \<lblot>\<alpha>\<rblot> = \<beta>"
    by blast
qed

lemma (in encoding) SOSou_iff_inverse_of_indRelRTPO_is_strong_reduction_simulation:
  fixes TRel :: "('procT \<times> 'procT) set"
  shows "(strongly_operational_sound (TRel\<^sup>*)
         \<and> strong_reduction_simulation ((TRel\<^sup>+)\<inverse>) Target)
         = strong_reduction_simulation ((indRelRTPO TRel)\<inverse>) (STCal Source Target)"
proof (rule iffI, erule conjE)
  assume os:  "strongly_operational_sound (TRel\<^sup>*)"
     and sim: "strong_reduction_simulation ((TRel\<^sup>+)\<inverse>) Target"
  show "strong_reduction_simulation ((indRelRTPO TRel)\<inverse>) (STCal Source Target)"
  proof clarify
    fix P Q P'
    assume "Q \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> P"
    moreover assume "P \<longmapsto>(STCal Source Target) P'"
    ultimately show "\<exists>Q'. Q \<longmapsto>(STCal Source Target) Q' \<and> (P', Q') \<in> (indRelRTPO TRel)\<inverse>"
    proof (induct arbitrary: P')
      case (encR S)
      assume "TargetTerm (\<lbrakk>S\<rbrakk>) \<longmapsto>(STCal Source Target) P'"
      from this obtain T where A1: "T \<in>T P'" and A2: "\<lbrakk>S\<rbrakk> \<longmapsto>Target T"
        by (auto simp add: STCal_step(2))
      from os A2 obtain S' where A3: "S \<longmapsto>Source S'" and A4: "(\<lbrakk>S'\<rbrakk>, T) \<in> TRel\<^sup>*"
        by blast
      from A3 have "SourceTerm S \<longmapsto>(STCal Source Target) (SourceTerm S')"
        by (simp add: STCal_step(1))
      moreover have "SourceTerm S' \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> P'"
      proof -
        from A4 have "\<lbrakk>S'\<rbrakk> = T \<or> (\<lbrakk>S'\<rbrakk>, T) \<in> TRel\<^sup>+"
          using rtrancl_eq_or_trancl[of "\<lbrakk>S'\<rbrakk>" T TRel]
          by blast
        moreover have A5: "SourceTerm S' \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> TargetTerm (\<lbrakk>S'\<rbrakk>)"
          by (simp add: indRelRTPO.encR)
        with A1 have "\<lbrakk>S'\<rbrakk> = T \<Longrightarrow> SourceTerm S' \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> P'"
          by simp
        moreover have "(\<lbrakk>S'\<rbrakk>, T) \<in> TRel\<^sup>+ \<Longrightarrow> SourceTerm S' \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> P'"
        proof -
          assume "(\<lbrakk>S'\<rbrakk>, T) \<in> TRel\<^sup>+"
          hence "TargetTerm (\<lbrakk>S'\<rbrakk>) \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> TargetTerm T"
            by (rule transitive_closure_of_TRel_to_indRelRTPO)
          with A5 have "SourceTerm S' \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> TargetTerm T"
            by (rule indRelRTPO.trans)
          with A1 show "SourceTerm S' \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> P'"
            by simp
        qed
        ultimately show "SourceTerm S' \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> P'"
          by blast
      qed
      hence "(P', SourceTerm S') \<in> (indRelRTPO TRel)\<inverse>"
        by simp
      ultimately
      show "\<exists>Q'. SourceTerm S \<longmapsto>(STCal Source Target) Q' \<and> (P', Q') \<in> (indRelRTPO TRel)\<inverse>"
        by blast
    next
      case (source S)
      then obtain S' where B1: "S' \<in>S P'"
        by (auto simp add: STCal_step(1))
      hence "(P', P') \<in> (indRelRTPO TRel)\<inverse>"
        by (simp add: indRelRTPO.source)
      with source
      show "\<exists>Q'. SourceTerm S \<longmapsto>(STCal Source Target) Q' \<and> (P', Q') \<in> (indRelRTPO TRel)\<inverse>"
        by blast
    next
      case (target T1 T2)
      assume "TargetTerm T2 \<longmapsto>(STCal Source Target) P'"
      from this obtain T2' where C1: "T2' \<in>T P'" and C2: "T2 \<longmapsto>Target T2'"
        by (auto simp add: STCal_step(2))
      assume "(T1, T2) \<in> TRel"
      hence "(T2, T1) \<in> (TRel\<^sup>+)\<inverse>"
        by simp
      with C2 sim obtain T1' where C3: "T1 \<longmapsto>Target T1'" and C4: "(T2', T1') \<in> (TRel\<^sup>+)\<inverse>"
        by blast
      from C3 have "TargetTerm T1 \<longmapsto>(STCal Source Target) (TargetTerm T1')"
        by (simp add: STCal_step(2))
      moreover from C4 have "(T1', T2') \<in> TRel\<^sup>+"
        by induct
      hence "TargetTerm T1' \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> TargetTerm T2'"
        by (rule transitive_closure_of_TRel_to_indRelRTPO)
      with C1 have "(P', TargetTerm T1') \<in> (indRelRTPO TRel)\<inverse>"
        by simp
      ultimately
      show "\<exists>Q'. TargetTerm T1 \<longmapsto>(STCal Source Target) Q' \<and> (P', Q') \<in> (indRelRTPO TRel)\<inverse>"
        by blast
    next
      case (trans P Q R R')
      assume "R \<longmapsto>(STCal Source Target) R'"
         and "\<And>R'. R \<longmapsto>(STCal Source Target) R'
              \<Longrightarrow> \<exists>Q'. Q \<longmapsto>(STCal Source Target) Q' \<and> (R', Q') \<in> (indRelRTPO TRel)\<inverse>"
      from this obtain Q' where D1: "Q \<longmapsto>(STCal Source Target) Q'"
                            and D2: "(R', Q') \<in> (indRelRTPO TRel)\<inverse>"
        by blast
      assume "\<And>Q'. Q \<longmapsto>(STCal Source Target) Q'
              \<Longrightarrow> \<exists>P'. P \<longmapsto>(STCal Source Target) P' \<and> (Q', P') \<in> (indRelRTPO TRel)\<inverse>"
      with D1 obtain P' where D3: "P \<longmapsto>(STCal Source Target) P'"
                          and D4: "(Q', P') \<in> (indRelRTPO TRel)\<inverse>"
        by blast
      from D4 D2 have "(R', P') \<in> (indRelRTPO TRel)\<inverse>"
        by (simp add: indRelRTPO.trans[where P="P'" and Q="Q'" and R="R'"])
      with D3 show "\<exists>P'. P \<longmapsto>(STCal Source Target) P' \<and> (R', P') \<in> (indRelRTPO TRel)\<inverse>"
        by blast
    qed
  qed
next
  have "\<forall>S. SourceTerm S \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> TargetTerm (\<lbrakk>S\<rbrakk>)"
    by (simp add: indRelRTPO.encR)
  moreover have "\<forall>S T. SourceTerm S \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> TargetTerm T \<longrightarrow> (\<lbrakk>S\<rbrakk>, T) \<in> TRel\<^sup>*"
    using indRelRTPO_to_TRel(2)[where TRel="TRel"] trans_closure_of_TRel_refl_cond
    by simp
  moreover
  assume sim: "strong_reduction_simulation ((indRelRTPO TRel)\<inverse>) (STCal Source Target)"
  ultimately have "strongly_operational_sound (TRel\<^sup>*)"
    using strong_reduction_simulation_impl_SOSou[where Rel="indRelRTPO TRel" and TRel="TRel"]
    by simp
  moreover from sim have "strong_reduction_simulation ((TRel\<^sup>+)\<inverse>) Target"
    using indRelRTPO_impl_TRel_is_strong_reduction_simulation_rev[where TRel="TRel"]
    by simp
  ultimately
  show "strongly_operational_sound (TRel\<^sup>*) \<and> strong_reduction_simulation ((TRel\<^sup>+)\<inverse>) Target"
    by simp
qed

lemma (in encodingLS_encL) SOSou_iff_inverse_of_indRelRTPO_is_strong_labelled_simulation_encL:
  fixes TRel :: "('procT \<times> 'procT) set"
  shows "(strongly_operational_sound_encL (TRel\<^sup>*)
         \<and> strong_labelled_simulation ((TRel\<^sup>+)\<inverse>) Target)
         = strong_labelled_simulation_encL ((indRelRTPO TRel)\<inverse>)"
proof (rule iffI, erule conjE)
  assume os:  "strongly_operational_sound_encL (TRel\<^sup>*)"
     and sim: "strong_labelled_simulation ((TRel\<^sup>+)\<inverse>) Target"
  show "strong_labelled_simulation_encL ((indRelRTPO TRel)\<inverse>)"
  proof clarify
    fix P Q \<alpha> P'
    assume "Q \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> P"
    moreover assume "P \<midarrow>\<alpha>\<rightarrow>(STLCal Source Target) P'"
    ultimately show "\<exists>\<beta> Q'. Q \<midarrow>\<beta>\<rightarrow>(STLCal Source Target) Q' \<and> (P', Q') \<in> (indRelRTPO TRel)\<inverse> \<and>
                     \<langle>P, \<alpha>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>Q, \<beta>\<rangle>"
    proof (induct arbitrary: \<alpha> P')
      case (encR S)
      assume "TargetTerm (\<lbrakk>S\<rbrakk>) \<midarrow>\<alpha>\<rightarrow>(STLCal Source Target) P'"
      then obtain \<alpha>' T where A1: "\<alpha>' \<in>TL \<langle>TargetTerm (\<lbrakk>S\<rbrakk>), \<alpha>\<rangle>" and A2: "T \<in>T P'"
                         and A3: "\<lbrakk>S\<rbrakk> \<midarrow>\<alpha>'\<rightarrow>Target T"
        using STLCal_labelledStep(2)[of "\<lbrakk>S\<rbrakk>" \<alpha> P']
        by blast
      from os A3 obtain \<beta>' S' where A4: "S \<midarrow>\<beta>'\<rightarrow>Source S'" and A5: "(\<lbrakk>S'\<rbrakk>, T) \<in> TRel\<^sup>*"
                                and A6: "\<lblot>\<beta>'\<rblot> = \<alpha>'"
        by blast
      obtain \<beta> where A7: "\<beta>' \<in>SL \<langle>SourceTerm S, \<beta>\<rangle>"
        unfolding getSourceLabel_def
        by blast
      from A4 A7 have "SourceTerm S \<midarrow>\<beta>\<rightarrow>(STLCal Source Target) (SourceTerm S')"
        using STLCal_labelledStep(1)[of S \<beta> "SourceTerm S'"]
        by blast
      moreover have "SourceTerm S' \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> P'"
      proof -
        from A5 have "\<lbrakk>S'\<rbrakk> = T \<or> (\<lbrakk>S'\<rbrakk>, T) \<in> TRel\<^sup>+"
          using rtrancl_eq_or_trancl[of "\<lbrakk>S'\<rbrakk>" T TRel]
          by blast
        moreover have B: "SourceTerm S' \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> TargetTerm (\<lbrakk>S'\<rbrakk>)"
          by (simp add: indRelRTPO.encR)
        with A2 have "\<lbrakk>S'\<rbrakk> = T \<Longrightarrow> SourceTerm S' \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> P'"
          by simp
        moreover have "(\<lbrakk>S'\<rbrakk>, T) \<in> TRel\<^sup>+ \<Longrightarrow> SourceTerm S' \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> P'"
        proof -
          assume "(\<lbrakk>S'\<rbrakk>, T) \<in> TRel\<^sup>+"
          hence "TargetTerm (\<lbrakk>S'\<rbrakk>) \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> TargetTerm T"
            by (rule transitive_closure_of_TRel_to_indRelRTPO)
          with B have "SourceTerm S' \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> TargetTerm T"
            by (rule indRelRTPO.trans)
          with A2 show "SourceTerm S' \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> P'"
            by simp
        qed
        ultimately show "SourceTerm S' \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> P'"
          by blast
      qed
      hence "(P', SourceTerm S') \<in> (indRelRTPO TRel)\<inverse>"
        by simp
      moreover from A1 A6 A7 have "\<lparr>SourceTerm S, \<beta>\<rparr>\<mapsto>\<langle>TargetTerm (\<lbrakk>S\<rbrakk>), \<alpha>\<rangle>"
        unfolding encLST_def
        by blast
      hence "\<langle>TargetTerm (\<lbrakk>S\<rbrakk>), \<alpha>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>SourceTerm S, \<beta>\<rangle>"
        unfolding related_labels_def
        by simp
      ultimately show "\<exists>\<beta> Q'. SourceTerm S \<midarrow>\<beta>\<rightarrow>(STLCal Source Target) Q' \<and>
                       (P', Q') \<in> (indRelRTPO TRel)\<inverse> \<and> \<langle>TargetTerm (\<lbrakk>S\<rbrakk>), \<alpha>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>SourceTerm S, \<beta>\<rangle>"
        by blast
    next
      case (source S)
      assume A1: "SourceTerm S \<midarrow>\<alpha>\<rightarrow>(STLCal Source Target) P'"
      then obtain S' where A2: "S' \<in>S P'"
        using STLCal_labelledStep(1)[of S \<alpha> P']
        by blast
      hence A3: "(P', P') \<in> (indRelRTPO TRel)\<inverse>"
        by (simp add: indRelRTPO.source)
      have "\<langle>SourceTerm S, \<alpha>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>SourceTerm S, \<alpha>\<rangle>"
        unfolding related_labels_def
        by simp
      with A1 A3 show "\<exists>\<beta> Q'. SourceTerm S \<midarrow>\<beta>\<rightarrow>(STLCal Source Target) Q' \<and>
                       (P', Q') \<in> (indRelRTPO TRel)\<inverse> \<and> \<langle>SourceTerm S, \<alpha>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>SourceTerm S, \<beta>\<rangle>"
        by blast
    next
      case (target T1 T2)
      assume "TargetTerm T2 \<midarrow>\<alpha>\<rightarrow>(STLCal Source Target) P'"
      then obtain \<alpha>' T2' where A1: "\<alpha>' \<in>TL \<langle>TargetTerm T2, \<alpha>\<rangle>" and A2: "T2' \<in>T P'"
                           and A3: "T2 \<midarrow>\<alpha>'\<rightarrow>Target T2'"
        using STLCal_labelledStep(2)[of T2 \<alpha> P']
        by blast
      assume "(T1, T2) \<in> TRel"
      hence "(T2, T1) \<in> (TRel\<^sup>+)\<inverse>"
        by simp
      with sim A3 obtain T1' where A4: "T1 \<midarrow>\<alpha>'\<rightarrow>Target T1'" and A5: "(T2', T1') \<in> (TRel\<^sup>+)\<inverse>"
        by blast
      from A1 A4 have "TargetTerm T1 \<midarrow>\<alpha>\<rightarrow>(STLCal Source Target) (TargetTerm T1')"
        using STLCal_labelledStep(2)[of T1 \<alpha> "TargetTerm T1'"]
        unfolding getTargetLabel_def
        by blast
      moreover from A5 have "(T1', T2') \<in> TRel\<^sup>+"
        by induct
      hence "TargetTerm T1' \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> TargetTerm T2'"
        by (rule transitive_closure_of_TRel_to_indRelRTPO)
      with A2 have "(P', TargetTerm T1') \<in> (indRelRTPO TRel)\<inverse>"
        by simp
      moreover have "\<langle>TargetTerm T2, \<alpha>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>TargetTerm T1, \<alpha>\<rangle>"
        unfolding related_labels_def
        by simp
      ultimately show "\<exists>\<beta> Q'. TargetTerm T1 \<midarrow>\<beta>\<rightarrow>(STLCal Source Target) Q' \<and>
                       (P', Q') \<in> (indRelRTPO TRel)\<inverse> \<and> \<langle>TargetTerm T2, \<alpha>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>TargetTerm T1, \<beta>\<rangle>"
        by blast
    next
      case (trans P Q R \<gamma> R')
      assume "R \<midarrow>\<gamma>\<rightarrow>(STLCal Source Target) R'"
         and "\<And>\<gamma> R'. R \<midarrow>\<gamma>\<rightarrow>(STLCal Source Target) R' \<Longrightarrow> \<exists>\<beta> Q'. Q \<midarrow>\<beta>\<rightarrow>(STLCal Source Target) Q' \<and>
              (R', Q') \<in> (indRelRTPO TRel)\<inverse> \<and> \<langle>R, \<gamma>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>Q, \<beta>\<rangle>"
      then obtain \<beta> Q' where A1: "Q \<midarrow>\<beta>\<rightarrow>(STLCal Source Target) Q'"
                         and A2: "(R', Q') \<in> (indRelRTPO TRel)\<inverse>" and A3: "\<langle>R, \<gamma>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>Q, \<beta>\<rangle>"
        by blast
      assume "\<And>\<beta> Q'. Q \<midarrow>\<beta>\<rightarrow>(STLCal Source Target) Q' \<Longrightarrow> \<exists>\<alpha> P'. P \<midarrow>\<alpha>\<rightarrow>(STLCal Source Target) P' \<and>
              (Q', P') \<in> (indRelRTPO TRel)\<inverse> \<and> \<langle>Q, \<beta>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>P, \<alpha>\<rangle>"
      with A1 obtain \<alpha> P' where A4: "P \<midarrow>\<alpha>\<rightarrow>(STLCal Source Target) P'"
                            and A5: "(Q', P') \<in> (indRelRTPO TRel)\<inverse>" and A6: "\<langle>Q, \<beta>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>P, \<alpha>\<rangle>"
        by blast
      from A2 A5 have A7: "(R', P') \<in> (indRelRTPO TRel)\<inverse>"
        using indRelRTPO.trans[where P="P'" and Q="Q'" and R="R'"]
        by simp
      assume "P \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> Q"
      hence A8: "\<not>(P \<in> ProcT \<and> Q \<in> ProcS)"
        using indRelRTPO_to_TRel(3)[of P Q TRel]
        by blast
      assume "Q \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> R"
      hence "\<not>(Q \<in> ProcT \<and> R \<in> ProcS)"
        using indRelRTPO_to_TRel(3)[of Q R TRel]
        by blast
      with A3 A6 A8 have "\<langle>R, \<gamma>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>P, \<alpha>\<rangle>"
        using related_labels_trans_no_T_to_S[of P \<alpha> Q \<beta> R \<gamma>] related_labels_sym[of Q \<beta> P \<alpha>]
              related_labels_sym[of R \<gamma> Q \<beta>] related_labels_sym[of P \<alpha> R \<gamma>]
        by simp
      with A4 A7 show "\<exists>\<alpha> P'. P \<midarrow>\<alpha>\<rightarrow>(STLCal Source Target) P' \<and> (R', P') \<in> (indRelRTPO TRel)\<inverse> \<and>
                       \<langle>R, \<gamma>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>P, \<alpha>\<rangle>"
        by blast
    qed
  qed
next
  have "\<forall>S. SourceTerm S \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> TargetTerm (\<lbrakk>S\<rbrakk>)"
    by (simp add: indRelRTPO.encR)
  moreover have "\<forall>S T. SourceTerm S \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> TargetTerm T \<longrightarrow> (\<lbrakk>S\<rbrakk>, T) \<in> TRel\<^sup>*"
    using indRelRTPO_to_TRel(2)[where TRel="TRel"] trans_closure_of_TRel_refl_cond
    by simp
  moreover assume sim: "strong_labelled_simulation_encL ((indRelRTPO TRel)\<inverse>)"
  ultimately have "strongly_operational_sound_encL (TRel\<^sup>*)"
    using strong_labelled_simulation_impl_SOSou_encL[where Rel="indRelRTPO TRel" and TRel="TRel"]
    by simp
  moreover from sim have "strong_labelled_simulation ((TRel\<^sup>+)\<inverse>) Target"
    using indRelRTPO_impl_TRel_is_strong_labelled_simulation_encL_rev[where TRel="TRel"]
    by simp
  ultimately
  show "strongly_operational_sound_encL (TRel\<^sup>*) \<and> strong_labelled_simulation ((TRel\<^sup>+)\<inverse>) Target"
    by simp
qed

lemma (in encoding) SOSou_iff_strong_reduction_simulation:
  fixes TRel :: "('procT \<times> 'procT) set"
  shows "(strongly_operational_sound (TRel\<^sup>*) \<and> strong_reduction_simulation ((TRel\<^sup>+)\<inverse>) Target)
         = (\<exists>Rel. (\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel)
            \<and> (\<forall>T1 T2. (T1, T2) \<in> TRel \<longrightarrow> (TargetTerm T1, TargetTerm T2) \<in> Rel)
            \<and> (\<forall>T1 T2. (TargetTerm T1, TargetTerm T2) \<in> Rel \<longrightarrow> (T1, T2) \<in> TRel\<^sup>+)
            \<and> (\<forall>S T. (SourceTerm S, TargetTerm T) \<in> Rel \<longrightarrow> (\<lbrakk>S\<rbrakk>, T) \<in> TRel\<^sup>*)
            \<and> strong_reduction_simulation (Rel\<inverse>) (STCal Source Target))"
proof (rule iffI, erule conjE)
  have "\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> indRelRTPO TRel"
    by (simp add: indRelRTPO.encR)
  moreover have "\<forall>T1 T2. (T1, T2) \<in> TRel \<longrightarrow> TargetTerm T1 \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> TargetTerm T2"
    by (simp add: indRelRTPO.target)
  moreover have "\<forall>T1 T2. TargetTerm T1 \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> TargetTerm T2 \<longrightarrow> (T1, T2) \<in> TRel\<^sup>+"
    using indRelRTPO_to_TRel(4)[where TRel="TRel"]
    by simp
  moreover have "\<forall>S T. SourceTerm S \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> TargetTerm T \<longrightarrow> (\<lbrakk>S\<rbrakk>, T) \<in> TRel\<^sup>*"
    using indRelRTPO_to_TRel(2)[where TRel="TRel"] trans_closure_of_TRel_refl_cond
    by simp
  moreover assume "strongly_operational_sound (TRel\<^sup>*)"
              and "strong_reduction_simulation ((TRel\<^sup>+)\<inverse>) Target"
  hence "strong_reduction_simulation ((indRelRTPO TRel)\<inverse>) (STCal Source Target)"
    using SOSou_iff_inverse_of_indRelRTPO_is_strong_reduction_simulation[where TRel="TRel"]
    by simp
  ultimately show "\<exists>Rel. (\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel)
                   \<and> (\<forall>T1 T2. (T1, T2) \<in> TRel \<longrightarrow> (TargetTerm T1, TargetTerm T2) \<in> Rel)
                   \<and> (\<forall>T1 T2. (TargetTerm T1, TargetTerm T2) \<in> Rel \<longrightarrow> (T1, T2) \<in> TRel\<^sup>+)
                   \<and> (\<forall>S T. (SourceTerm S, TargetTerm T) \<in> Rel \<longrightarrow> (\<lbrakk>S\<rbrakk>, T) \<in> TRel\<^sup>*)
                   \<and> strong_reduction_simulation (Rel\<inverse>) (STCal Source Target)"
    by blast
next
  assume "\<exists>Rel. (\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel)
          \<and> (\<forall>T1 T2. (T1, T2) \<in> TRel \<longrightarrow> (TargetTerm T1, TargetTerm T2) \<in> Rel)
          \<and> (\<forall>T1 T2. (TargetTerm T1, TargetTerm T2) \<in> Rel \<longrightarrow> (T1, T2) \<in> TRel\<^sup>+)
          \<and> (\<forall>S T. (SourceTerm S, TargetTerm T) \<in> Rel \<longrightarrow> (\<lbrakk>S\<rbrakk>, T) \<in> TRel\<^sup>*)
          \<and> strong_reduction_simulation (Rel\<inverse>) (STCal Source Target)"
  from this obtain Rel where A1: "\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel"
    and A2: "\<forall>T1 T2. (T1, T2) \<in> TRel \<longrightarrow> (TargetTerm T1, TargetTerm T2) \<in> Rel"
    and A3: "\<forall>T1 T2. (TargetTerm T1, TargetTerm T2) \<in> Rel \<longrightarrow> (T1, T2) \<in> TRel\<^sup>+"
    and A4: "\<forall>S T. (SourceTerm S, TargetTerm T) \<in> Rel \<longrightarrow> (\<lbrakk>S\<rbrakk>, T) \<in> TRel\<^sup>*"
    and A5: "strong_reduction_simulation (Rel\<inverse>) (STCal Source Target)"
    by blast
  from A1 A4 A5 have "strongly_operational_sound (TRel\<^sup>*)"
    using strong_reduction_simulation_impl_SOSou[where Rel="Rel" and TRel="TRel"]
    by simp
  moreover from A2 A3 A5 have "strong_reduction_simulation ((TRel\<^sup>+)\<inverse>) Target"
    using rel_with_target_impl_transC_TRel_is_strong_reduction_simulation_rev[where Rel="Rel" and
            TRel="TRel"]
    by simp
  ultimately
  show "strongly_operational_sound (TRel\<^sup>*) \<and> strong_reduction_simulation ((TRel\<^sup>+)\<inverse>) Target"
    by simp
qed

lemma (in encodingLS_encL) SOSou_iff_strong_labelled_simulation_encL:
  fixes TRel :: "('procT \<times> 'procT) set"
  shows "(strongly_operational_sound_encL (TRel\<^sup>*) \<and> strong_labelled_simulation ((TRel\<^sup>+)\<inverse>) Target)
         = (\<exists>Rel. (\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel)
            \<and> (\<forall>T1 T2. (T1, T2) \<in> TRel \<longrightarrow> (TargetTerm T1, TargetTerm T2) \<in> Rel)
            \<and> (\<forall>T1 T2. (TargetTerm T1, TargetTerm T2) \<in> Rel \<longrightarrow> (T1, T2) \<in> TRel\<^sup>+)
            \<and> (\<forall>S T. (SourceTerm S, TargetTerm T) \<in> Rel \<longrightarrow> (\<lbrakk>S\<rbrakk>, T) \<in> TRel\<^sup>*)
            \<and> strong_labelled_simulation_encL (Rel\<inverse>))"
proof (rule iffI, erule conjE)
  have "\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> indRelRTPO TRel"
    by (simp add: indRelRTPO.encR)
  moreover have "\<forall>T1 T2. (T1, T2) \<in> TRel \<longrightarrow> TargetTerm T1 \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> TargetTerm T2"
    by (simp add: indRelRTPO.target)
  moreover have "\<forall>T1 T2. TargetTerm T1 \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> TargetTerm T2 \<longrightarrow> (T1, T2) \<in> TRel\<^sup>+"
    using indRelRTPO_to_TRel(4)[where TRel="TRel"]
    by simp
  moreover have "\<forall>S T. SourceTerm S \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> TargetTerm T \<longrightarrow> (\<lbrakk>S\<rbrakk>, T) \<in> TRel\<^sup>*"
    using indRelRTPO_to_TRel(2)[where TRel="TRel"] trans_closure_of_TRel_refl_cond
    by simp
  moreover assume "strongly_operational_sound_encL (TRel\<^sup>*)"
              and "strong_labelled_simulation ((TRel\<^sup>+)\<inverse>) Target"
  hence "strong_labelled_simulation_encL ((indRelRTPO TRel)\<inverse>)"
    using SOSou_iff_inverse_of_indRelRTPO_is_strong_labelled_simulation_encL[where TRel="TRel"]
    by simp
  ultimately show "\<exists>Rel. (\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel)
                   \<and> (\<forall>T1 T2. (T1, T2) \<in> TRel \<longrightarrow> (TargetTerm T1, TargetTerm T2) \<in> Rel)
                   \<and> (\<forall>T1 T2. (TargetTerm T1, TargetTerm T2) \<in> Rel \<longrightarrow> (T1, T2) \<in> TRel\<^sup>+)
                   \<and> (\<forall>S T. (SourceTerm S, TargetTerm T) \<in> Rel \<longrightarrow> (\<lbrakk>S\<rbrakk>, T) \<in> TRel\<^sup>*)
                   \<and> strong_labelled_simulation_encL (Rel\<inverse>)"
    by blast
next
  assume "\<exists>Rel. (\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel)
          \<and> (\<forall>T1 T2. (T1, T2) \<in> TRel \<longrightarrow> (TargetTerm T1, TargetTerm T2) \<in> Rel)
          \<and> (\<forall>T1 T2. (TargetTerm T1, TargetTerm T2) \<in> Rel \<longrightarrow> (T1, T2) \<in> TRel\<^sup>+)
          \<and> (\<forall>S T. (SourceTerm S, TargetTerm T) \<in> Rel \<longrightarrow> (\<lbrakk>S\<rbrakk>, T) \<in> TRel\<^sup>*)
          \<and> strong_labelled_simulation_encL (Rel\<inverse>)"
  then obtain Rel where A1: "\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel"
    and A2: "\<forall>T1 T2. (T1, T2) \<in> TRel \<longrightarrow> (TargetTerm T1, TargetTerm T2) \<in> Rel"
    and A3: "\<forall>T1 T2. (TargetTerm T1, TargetTerm T2) \<in> Rel \<longrightarrow> (T1, T2) \<in> TRel\<^sup>+"
    and A4: "\<forall>S T. (SourceTerm S, TargetTerm T) \<in> Rel \<longrightarrow> (\<lbrakk>S\<rbrakk>, T) \<in> TRel\<^sup>*"
    and A5: "strong_labelled_simulation_encL (Rel\<inverse>)"
    by blast
  from A1 A4 A5 have "strongly_operational_sound_encL (TRel\<^sup>*)"
    using strong_labelled_simulation_impl_SOSou_encL[where Rel="Rel" and TRel="TRel"]
    by simp
  moreover from A2 A3 A5 have "strong_labelled_simulation ((TRel\<^sup>+)\<inverse>) Target"
    using rel_with_target_impl_transC_TRel_is_strong_labelled_simulation_encL_rev[where Rel="Rel"
            and TRel="TRel"]
    by simp
  ultimately
  show "strongly_operational_sound_encL (TRel\<^sup>*) \<and> strong_labelled_simulation ((TRel\<^sup>+)\<inverse>) Target"
    by simp
qed

lemma (in encoding) SOSou_modulo_TRel_iff_strong_reduction_simulation:
  shows "(\<exists>TRel. strongly_operational_sound (TRel\<^sup>*)
         \<and> strong_reduction_simulation ((TRel\<^sup>+)\<inverse>) Target)
         = (\<exists>Rel. (\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel)
           \<and> (\<forall>S T. (SourceTerm S, TargetTerm T) \<in> Rel \<longrightarrow> (TargetTerm (\<lbrakk>S\<rbrakk>), TargetTerm T) \<in> Rel\<^sup>=)
           \<and> strong_reduction_simulation (Rel\<inverse>) (STCal Source Target))"
proof (rule iffI)
  assume "\<exists>TRel. strongly_operational_sound (TRel\<^sup>*)
          \<and> strong_reduction_simulation ((TRel\<^sup>+)\<inverse>) Target"
  from this obtain TRel where "strongly_operational_sound (TRel\<^sup>*)"
                          and "strong_reduction_simulation ((TRel\<^sup>+)\<inverse>) Target"
    by blast
  hence "strong_reduction_simulation ((indRelRTPO TRel)\<inverse>) (STCal Source Target)"
    using SOSou_iff_inverse_of_indRelRTPO_is_strong_reduction_simulation[where TRel="TRel"]
    by simp
  moreover have "\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> indRelRTPO TRel"
    by (simp add: indRelRTPO.encR)
  moreover have "\<forall>S T. (SourceTerm S, TargetTerm T) \<in> indRelRTPO TRel
                 \<longrightarrow> (TargetTerm (\<lbrakk>S\<rbrakk>), TargetTerm T) \<in> (indRelRTPO TRel)\<^sup>="
    using indRelRTPO_relates_source_target[where TRel="TRel"]
    by simp
  ultimately show "\<exists>Rel. (\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel)
                   \<and> (\<forall>S T. (SourceTerm S, TargetTerm T) \<in> Rel
                      \<longrightarrow> (TargetTerm (\<lbrakk>S\<rbrakk>), TargetTerm T) \<in> Rel\<^sup>=)
                   \<and> strong_reduction_simulation (Rel\<inverse>) (STCal Source Target)"
    by blast
next
  assume "\<exists>Rel. (\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel)
          \<and> (\<forall>S T. (SourceTerm S, TargetTerm T) \<in> Rel
             \<longrightarrow> (TargetTerm (\<lbrakk>S\<rbrakk>), TargetTerm T) \<in> Rel\<^sup>=)
          \<and> strong_reduction_simulation (Rel\<inverse>) (STCal Source Target)"
  from this obtain Rel where A1: "\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel"
   and A2: "(\<forall>S T. (SourceTerm S, TargetTerm T) \<in> Rel
            \<longrightarrow> (TargetTerm (\<lbrakk>S\<rbrakk>), TargetTerm T) \<in> Rel\<^sup>=)"
   and A3: "strong_reduction_simulation (Rel\<inverse>) (STCal Source Target)"
    by blast
  from A2 obtain TRel where "\<forall>T1 T2. (T1, T2) \<in> TRel \<longrightarrow> (TargetTerm T1, TargetTerm T2) \<in> Rel"
   and "\<forall>T1 T2. (TargetTerm T1, TargetTerm T2) \<in> Rel \<longrightarrow> (T1, T2) \<in> TRel\<^sup>+"
   and "\<forall>S T. (SourceTerm S, TargetTerm T) \<in> Rel \<longrightarrow> (\<lbrakk>S\<rbrakk>, T) \<in> TRel\<^sup>*"
    using target_relation_from_source_target_relation[where Rel="Rel"]
    by blast
  with A1 A3
  have "strongly_operational_sound (TRel\<^sup>*) \<and> strong_reduction_simulation ((TRel\<^sup>+)\<inverse>) Target"
    using SOSou_iff_strong_reduction_simulation[where TRel="TRel"]
    by blast
  thus "\<exists>TRel. strongly_operational_sound (TRel\<^sup>*) \<and> strong_reduction_simulation ((TRel\<^sup>+)\<inverse>) Target"
    by blast
qed

lemma (in encodingLS_encL) SOSou_modulo_TRel_iff_strong_labelled_simulation_encL:
  shows "(\<exists>TRel. strongly_operational_sound_encL (TRel\<^sup>*)
         \<and> strong_labelled_simulation ((TRel\<^sup>+)\<inverse>) Target)
         = (\<exists>Rel. (\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel)
           \<and> (\<forall>S T. (SourceTerm S, TargetTerm T) \<in> Rel \<longrightarrow> (TargetTerm (\<lbrakk>S\<rbrakk>), TargetTerm T) \<in> Rel\<^sup>=)
           \<and> strong_labelled_simulation_encL (Rel\<inverse>))"
proof (rule iffI)
  assume "\<exists>TRel. strongly_operational_sound_encL (TRel\<^sup>*)
          \<and> strong_labelled_simulation ((TRel\<^sup>+)\<inverse>) Target"
  then obtain TRel where "strongly_operational_sound_encL (TRel\<^sup>*)"
                     and "strong_labelled_simulation ((TRel\<^sup>+)\<inverse>) Target"
    by blast
  hence "strong_labelled_simulation_encL ((indRelRTPO TRel)\<inverse>)"
    using SOSou_iff_inverse_of_indRelRTPO_is_strong_labelled_simulation_encL[where TRel="TRel"]
    by simp
  moreover have "\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> indRelRTPO TRel"
    by (simp add: indRelRTPO.encR)
  moreover have "\<forall>S T. (SourceTerm S, TargetTerm T) \<in> indRelRTPO TRel
                 \<longrightarrow> (TargetTerm (\<lbrakk>S\<rbrakk>), TargetTerm T) \<in> (indRelRTPO TRel)\<^sup>="
    using indRelRTPO_relates_source_target[where TRel="TRel"]
    by simp
  ultimately show "\<exists>Rel. (\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel)
                   \<and> (\<forall>S T. (SourceTerm S, TargetTerm T) \<in> Rel
                      \<longrightarrow> (TargetTerm (\<lbrakk>S\<rbrakk>), TargetTerm T) \<in> Rel\<^sup>=)
                   \<and> strong_labelled_simulation_encL (Rel\<inverse>)"
    by blast
next
  assume "\<exists>Rel. (\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel)
          \<and> (\<forall>S T. (SourceTerm S, TargetTerm T) \<in> Rel
             \<longrightarrow> (TargetTerm (\<lbrakk>S\<rbrakk>), TargetTerm T) \<in> Rel\<^sup>=)
          \<and> strong_labelled_simulation_encL (Rel\<inverse>)"
  then obtain Rel where A1: "\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel"
   and A2: "(\<forall>S T. (SourceTerm S, TargetTerm T) \<in> Rel
            \<longrightarrow> (TargetTerm (\<lbrakk>S\<rbrakk>), TargetTerm T) \<in> Rel\<^sup>=)"
   and A3: "strong_labelled_simulation_encL (Rel\<inverse>)"
    by blast
  from A2 obtain TRel where "\<forall>T1 T2. (T1, T2) \<in> TRel \<longrightarrow> (TargetTerm T1, TargetTerm T2) \<in> Rel"
   and "\<forall>T1 T2. (TargetTerm T1, TargetTerm T2) \<in> Rel \<longrightarrow> (T1, T2) \<in> TRel\<^sup>+"
   and "\<forall>S T. (SourceTerm S, TargetTerm T) \<in> Rel \<longrightarrow> (\<lbrakk>S\<rbrakk>, T) \<in> TRel\<^sup>*"
    using target_relation_from_source_target_relation[where Rel="Rel"]
    by blast
  with A1 A3
  have "strongly_operational_sound_encL (TRel\<^sup>*) \<and> strong_labelled_simulation ((TRel\<^sup>+)\<inverse>) Target"
    using SOSou_iff_strong_labelled_simulation_encL[where TRel="TRel"]
    by blast
  thus "\<exists>TRel. strongly_operational_sound_encL (TRel\<^sup>*) \<and>
        strong_labelled_simulation ((TRel\<^sup>+)\<inverse>) Target"
    by blast
qed

subsection \<open>Weak Operational Correspondence vs Correspondence Similarity\<close>

text \<open>If there exists a relation that relates at least all source terms and their literal
      translations, includes TRel, and is a correspondence simulation then the encoding is weakly
      operational corresponding w.r.t. TRel.\<close>

lemma (in encoding) weak_reduction_correspondence_simulation_impl_WOC:
  fixes Rel  :: "(('procS, 'procT) Proc \<times> ('procS, 'procT) Proc) set"
    and TRel :: "('procT \<times> 'procT) set"
  assumes enc:  "\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel"
      and tRel: "(\<forall>S T. (SourceTerm S, TargetTerm T) \<in> Rel \<longrightarrow> (\<lbrakk>S\<rbrakk>, T) \<in> TRel\<^sup>*)"
      and cs:   "weak_reduction_correspondence_simulation Rel (STCal Source Target)"
  shows "weakly_operational_corresponding (TRel\<^sup>*)"
proof
  from enc tRel cs show "operational_complete (TRel\<^sup>*)"
    using weak_reduction_simulation_impl_OCom[where TRel="TRel"]
    by simp
next
  show "weakly_operational_sound (TRel\<^sup>*)"
  proof clarify
    fix S T
    from enc have "(SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel"
      by simp
    moreover assume "\<lbrakk>S\<rbrakk> \<longmapsto>Target* T"
    hence "TargetTerm (\<lbrakk>S\<rbrakk>) \<longmapsto>(STCal Source Target)* (TargetTerm T)"
      by (simp add: STCal_steps(2))
    ultimately obtain P' Q' where A1: "SourceTerm S \<longmapsto>(STCal Source Target)* P'"
      and A2: "TargetTerm T \<longmapsto>(STCal Source Target)* Q'" and A3: "(P', Q') \<in> Rel"
      using cs
      by blast
    from A1 obtain S' where A4: "S' \<in>S P'" and A5: "S \<longmapsto>Source* S'"
      by (auto simp add: STCal_steps(1))
    from A2 obtain T' where A6: "T' \<in>T Q'" and A7: "T \<longmapsto>Target* T'"
      by (auto simp: STCal_steps(2))
    from tRel A3 A4 A6 have "(\<lbrakk>S'\<rbrakk>, T') \<in> TRel\<^sup>*"
      by simp
    with A5 A7 show "\<exists>S' T'. S \<longmapsto>Source* S' \<and> T \<longmapsto>Target* T' \<and> (\<lbrakk>S'\<rbrakk>, T') \<in> TRel\<^sup>*"
      by blast
  qed
qed

lemma (in encodingLS) weak_labelled_correspondence_simulation_impl_WOC:
  fixes Rel  :: "(('procS, 'procT) Proc \<times> ('procS, 'procT) Proc) set"
    and TRel :: "('procT \<times> 'procT) set"
  assumes enc:  "\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel"
      and tRel: "(\<forall>S T. (SourceTerm S, TargetTerm T) \<in> Rel \<longrightarrow> (\<lbrakk>S\<rbrakk>, T) \<in> TRel\<^sup>*)"
      and cs:   "weak_labelled_correspondence_simulation Rel (STLCal Source Target)"
  shows "weakly_operational_corresponding (TRel\<^sup>*)"
proof
  from enc tRel cs show "operational_complete (TRel\<^sup>*)"
    using weak_labelled_simulation_impl_OCom[where TRel="TRel"]
    by simp
next
  show "weakly_operational_sound (TRel\<^sup>*)"
  proof clarify
    fix S \<beta> T
    obtain \<beta>' where A1: "\<beta> \<in>TL \<langle>TargetTerm (\<lbrakk>S\<rbrakk>), \<beta>'\<rangle>"
      unfolding getTargetLabel_def
      by blast
    from enc have A2: "(SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel"
      by simp
    assume "\<lbrakk>S\<rbrakk> \<midarrow>\<Zcat>\<beta>\<rightarrow>Target* T"
    with A1 have "TargetTerm (\<lbrakk>S\<rbrakk>) \<midarrow>\<Zcat>\<beta>'\<rightarrow>(STLCal Source Target)* (TargetTerm T)"
      using STLCal_weakLabelledSteps(2)[of "\<lbrakk>S\<rbrakk>" \<beta>' "TargetTerm T"]
      by blast
    with cs A2 obtain P' Q' where A3: "SourceTerm S \<midarrow>\<Zcat>\<beta>'\<rightarrow>(STLCal Source Target)* P'"
      and A4: "TargetTerm T \<rightarrow>(STLCal Source Target)* Q'" and A5: "(P', Q') \<in> Rel"
      by blast
    from A1 A3 obtain \<beta>'' S' where A6: "\<beta>'' \<in>SL \<langle>SourceTerm S, \<beta>'\<rangle>" and A7: "S' \<in>S P'"
                               and A8: "S \<midarrow>\<Zcat>\<beta>''\<rightarrow>Source* S'"
      using STLCal_weakLabelledSteps(1)[of S \<beta>' P']
      by blast
    from A4 obtain T' where A9: "T' \<in>T Q'" and A10: "T \<rightarrow>Target* T'"
      using STLCal_weakTauSteps(2)[of T Q']
      by blast
    from tRel A5 A7 A9 have "(\<lbrakk>S'\<rbrakk>, T') \<in> TRel\<^sup>*"
      by simp
    with A8 A10 show "\<exists>S' \<alpha> T'. S \<midarrow>\<Zcat>\<alpha>\<rightarrow>Source* S' \<and> T \<rightarrow>Target* T' \<and> (\<lbrakk>S'\<rbrakk>, T') \<in> TRel\<^sup>*"
      by blast
  qed
qed

lemma (in encodingLS_encL) weak_labelled_correspondence_simulation_impl_WOC_encL:
  fixes Rel  :: "(('procS, 'procT) Proc \<times> ('procS, 'procT) Proc) set"
    and TRel :: "('procT \<times> 'procT) set"
  assumes enc:  "\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel"
      and tRel: "(\<forall>S T. (SourceTerm S, TargetTerm T) \<in> Rel \<longrightarrow> (\<lbrakk>S\<rbrakk>, T) \<in> TRel\<^sup>*)"
      and cs:   "weak_labelled_correspondence_simulation_encL Rel"
    shows "weakly_operational_corresponding_encL (TRel\<^sup>*)"
proof
  from enc tRel cs show "operational_complete_encL (TRel\<^sup>*)"
    using weak_labelled_simulation_encL_impl_OCom[where TRel="TRel"]
    by simp
next
  show "weakly_operational_sound_encL (TRel\<^sup>*)"
  proof clarify
    fix S \<beta> T
    obtain \<beta>' where A1: "\<beta> \<in>TL \<langle>TargetTerm (\<lbrakk>S\<rbrakk>), \<beta>'\<rangle>"
      unfolding getTargetLabel_def
      by blast
    from enc have A2: "(SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel"
      by simp
    assume "\<lbrakk>S\<rbrakk> \<midarrow>\<Zcat>\<beta>\<rightarrow>Target* T"
    with A1 have "TargetTerm (\<lbrakk>S\<rbrakk>) \<midarrow>\<Zcat>\<beta>'\<rightarrow>(STLCal Source Target)* (TargetTerm T)"
      using STLCal_weakLabelledSteps(2)[of "\<lbrakk>S\<rbrakk>" \<beta>' "TargetTerm T"]
      by blast
    with cs A2 obtain \<alpha>' P' Q' where A3: "SourceTerm S \<midarrow>\<Zcat>\<alpha>'\<rightarrow>(STLCal Source Target)* P'"
                                 and A4: "TargetTerm T \<rightarrow>(STLCal Source Target)* Q'"
                                 and A5: "(P', Q') \<in> Rel"
                                 and A6: "\<langle>SourceTerm S, \<alpha>'\<rangle> \<equiv>\<lparr>\<rparr> \<langle>TargetTerm (\<lbrakk>S\<rbrakk>), \<beta>'\<rangle>"
      by blast
    from A1 A3 obtain \<alpha> S' where A7: "\<alpha> \<in>SL \<langle>SourceTerm S, \<alpha>'\<rangle>" and A8: "S' \<in>S P'"
                             and A9: "S \<midarrow>\<Zcat>\<alpha>\<rightarrow>Source* S'"
      using STLCal_weakLabelledSteps(1)[of S \<alpha>' P']
      by blast
    from A4 obtain T' where A10: "T' \<in>T Q'" and A11: "T \<rightarrow>Target* T'"
      using STLCal_weakTauSteps(2)[of T Q']
      by blast
    from tRel A5 A8 A10 have A12: "(\<lbrakk>S'\<rbrakk>, T') \<in> TRel\<^sup>*"
      by simp
    from A6 have "\<lparr>SourceTerm S, \<alpha>'\<rparr>\<mapsto>\<langle>TargetTerm (\<lbrakk>S\<rbrakk>), \<beta>'\<rangle>"
      using kinds_of_encoded_label(1)[of "TargetTerm (\<lbrakk>S\<rbrakk>)" \<beta>' "SourceTerm S" \<alpha>']
      unfolding related_labels_def
      by blast
    with A1 A7 have "\<lblot>\<alpha>\<rblot> = \<beta>"
      unfolding encLST_def getSourceLabel_def getTargetLabel_def
      by blast
    with A9 A11 A12
    show "\<exists>S' \<alpha> T'. S \<midarrow>\<Zcat>\<alpha>\<rightarrow>Source* S' \<and> T \<rightarrow>Target* T' \<and> (\<lbrakk>S'\<rbrakk>, T') \<in> TRel\<^sup>* \<and> \<lblot>\<alpha>\<rblot> = \<beta>"
      by blast
  qed
qed

text \<open>An encoding is weakly operational corresponding w.r.t. a correspondence simulation on
      target terms TRel iff there exists a relation, like indRelRTPO, that relates at least all
      source terms and their literal translations, includes TRel, and is a correspondence
      simulation.\<close>

lemma (in encoding) WOC_iff_indRelRTPO_is_reduction_correspondence_simulation:
  fixes TRel :: "('procT \<times> 'procT) set"
  shows "(weakly_operational_corresponding (TRel\<^sup>*)
         \<and> weak_reduction_correspondence_simulation (TRel\<^sup>+) Target)
         = weak_reduction_correspondence_simulation (indRelRTPO TRel) (STCal Source Target)"
proof (rule iffI, erule conjE)
  assume woc: "weakly_operational_corresponding (TRel\<^sup>*)"
     and csi: "weak_reduction_correspondence_simulation (TRel\<^sup>+) Target"
  show "weak_reduction_correspondence_simulation (indRelRTPO TRel) (STCal Source Target)"
  proof
    from woc csi show sim: "weak_reduction_simulation (indRelRTPO TRel) (STCal Source Target)"
      using OCom_iff_indRelRTPO_is_weak_reduction_simulation[where TRel="TRel"]
      by simp
    show "\<forall>P Q Q'. P \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> Q \<and> Q \<longmapsto>(STCal Source Target)* Q'
          \<longrightarrow> (\<exists>P'' Q''. P \<longmapsto>(STCal Source Target)* P'' \<and> Q' \<longmapsto>(STCal Source Target)* Q''
          \<and> P'' \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> Q'')"
    proof clarify
      fix P Q Q'
      assume "P \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> Q" and "Q \<longmapsto>(STCal Source Target)* Q'"
      thus "\<exists>P'' Q''. P \<longmapsto>(STCal Source Target)* P'' \<and> Q' \<longmapsto>(STCal Source Target)* Q''
            \<and> P'' \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> Q''"
      proof (induct arbitrary: Q')
        case (encR S)
        assume "TargetTerm (\<lbrakk>S\<rbrakk>) \<longmapsto>(STCal Source Target)* Q'"
        from this obtain T where A1: "T \<in>T Q'" and A2: "\<lbrakk>S\<rbrakk> \<longmapsto>Target* T"
          by (auto simp add: STCal_steps(2))
        from A2 woc obtain S' T' where A3: "S \<longmapsto>Source* S'" and A4: "T \<longmapsto>Target* T'"
                                   and A5: "(\<lbrakk>S'\<rbrakk>, T') \<in> TRel\<^sup>*"
          by blast
        from A3 have "SourceTerm S \<longmapsto>(STCal Source Target)* (SourceTerm S')"
          by (simp add: STCal_steps(1))
        moreover from A4 have "TargetTerm T \<longmapsto>(STCal Source Target)* (TargetTerm T')"
          by (simp add: STCal_steps(2))
        moreover have "SourceTerm S' \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> TargetTerm T'"
        proof -
          have A6: "SourceTerm S' \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> TargetTerm (\<lbrakk>S'\<rbrakk>)"
            by (rule indRelRTPO.encR)
          from A5 have "\<lbrakk>S'\<rbrakk> = T' \<or> (\<lbrakk>S'\<rbrakk>, T') \<in> TRel\<^sup>+"
            using rtrancl_eq_or_trancl[of "\<lbrakk>S'\<rbrakk>" T' TRel]
            by blast
          moreover from A6 have "\<lbrakk>S'\<rbrakk> = T' \<Longrightarrow> SourceTerm S' \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> TargetTerm T'"
            by simp
          moreover have "(\<lbrakk>S'\<rbrakk>, T') \<in> TRel\<^sup>+ \<Longrightarrow> SourceTerm S' \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> TargetTerm T'"
          proof -
            assume "(\<lbrakk>S'\<rbrakk>, T') \<in> TRel\<^sup>+"
            hence "TargetTerm (\<lbrakk>S'\<rbrakk>) \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> TargetTerm T'"
              by (simp add: transitive_closure_of_TRel_to_indRelRTPO[where TRel="TRel"])
            with A6 show "SourceTerm S' \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> TargetTerm T'"
              by (rule indRelRTPO.trans)
          qed
          ultimately show "SourceTerm S' \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> TargetTerm T'"
            by blast
        qed
        ultimately show "\<exists>P'' Q''. SourceTerm S \<longmapsto>(STCal Source Target)* P''
                         \<and> Q' \<longmapsto>(STCal Source Target)* Q'' \<and> P'' \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> Q''"
          using A1
          by blast
      next
        case (source S)
        assume B1: "SourceTerm S \<longmapsto>(STCal Source Target)* Q'"
        moreover have "Q' \<longmapsto>(STCal Source Target)* Q'"
          by (rule steps_refl)
        moreover from B1 obtain S' where "S' \<in>S Q'"
          by (auto simp add: STCal_steps(1))
        hence "Q' \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> Q'"
          by (simp add: indRelRTPO.source)
        ultimately show "\<exists>P'' Q''. SourceTerm S \<longmapsto>(STCal Source Target)* P''
                         \<and> Q' \<longmapsto>(STCal Source Target)* Q'' \<and> P'' \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> Q''"
          by blast
      next
        case (target T1 T2)
        assume "TargetTerm T2 \<longmapsto>(STCal Source Target)* Q'"
        from this obtain T2' where C1: "T2' \<in>T Q'" and C2: "T2 \<longmapsto>Target* T2'"
          by (auto simp add: STCal_steps(2))
        assume "(T1, T2) \<in> TRel"
        hence "(T1, T2) \<in> TRel\<^sup>+"
          by simp
        with C2 csi obtain T1' T2'' where C3: "T1 \<longmapsto>Target* T1'" and C4: "T2' \<longmapsto>Target* T2''"
                                      and C5: "(T1', T2'') \<in> TRel\<^sup>+"
          by blast
        from C3 have "TargetTerm T1 \<longmapsto>(STCal Source Target)* (TargetTerm T1')"
          by (simp add: STCal_steps(2))
        moreover from C1 C4 have "Q' \<longmapsto>(STCal Source Target)* (TargetTerm T2'')"
          by (simp add: STCal_steps(2))
        moreover from C5 have "TargetTerm T1' \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> (TargetTerm T2'')"
          by (simp add: transitive_closure_of_TRel_to_indRelRTPO)
        ultimately show "\<exists>P'' Q''. TargetTerm T1 \<longmapsto>(STCal Source Target)* P''
                         \<and> Q' \<longmapsto>(STCal Source Target)* Q'' \<and> P'' \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> Q''"
          by blast
      next
        case (trans P Q R R')
        assume "R \<longmapsto>(STCal Source Target)* R'"
           and "\<And>R'. R \<longmapsto>(STCal Source Target)* R' \<Longrightarrow> \<exists>Q'' R''. Q \<longmapsto>(STCal Source Target)* Q''
                \<and> R' \<longmapsto>(STCal Source Target)* R'' \<and> Q'' \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> R''"
           and "\<And>Q'. Q \<longmapsto>(STCal Source Target)* Q' \<Longrightarrow> \<exists>P'' Q''. P \<longmapsto>(STCal Source Target)* P''
                \<and> Q' \<longmapsto>(STCal Source Target)* Q'' \<and> P'' \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> Q''"
        moreover have "trans (indRelRTPO TRel)"
          using indRelRTPO.trans
          unfolding trans_def
          by blast
        ultimately show ?case
          using sim reduction_correspondence_simulation_condition_trans[where P="P" and
                  Rel="indRelRTPO TRel" and Cal="STCal Source Target" and Q="Q" and R="R"]
          by blast
      qed
    qed
  qed
next
  assume csi: "weak_reduction_correspondence_simulation (indRelRTPO TRel) (STCal Source Target)"
  show "weakly_operational_corresponding (TRel\<^sup>*)
        \<and> weak_reduction_correspondence_simulation (TRel\<^sup>+) Target"
  proof
    have " \<forall>S. SourceTerm S \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> TargetTerm (\<lbrakk>S\<rbrakk>)"
      by (simp add: indRelRTPO.encR)
    moreover have "\<forall>S T. SourceTerm S \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> TargetTerm T \<longrightarrow> (\<lbrakk>S\<rbrakk>, T) \<in> TRel\<^sup>*"
      using indRelRTPO_to_TRel(2)[where TRel="TRel"] trans_closure_of_TRel_refl_cond
      by simp
    ultimately show "weakly_operational_corresponding (TRel\<^sup>*)"
      using weak_reduction_correspondence_simulation_impl_WOC[where Rel="indRelRTPO TRel" and
              TRel="TRel"] csi
      by simp
  next
    from csi show "weak_reduction_correspondence_simulation (TRel\<^sup>+) Target"
      using indRelRTPO_impl_TRel_is_weak_reduction_correspondence_simulation[where TRel="TRel"]
      by simp
  qed
qed

lemma (in encodingLS_encL) indRelRTPO_labelled_correspondence_simulation_encL_trans:
  fixes P Q R :: "('procS, 'procT) Proc"
  assumes csQP:   "\<forall>\<beta> Q'. Q \<midarrow>\<Zcat>\<beta>\<rightarrow>(STLCal Source Target)* Q' \<longrightarrow>
                   (\<exists>\<alpha> P'' Q''. P \<midarrow>\<Zcat>\<alpha>\<rightarrow>(STLCal Source Target)* P'' \<and>
                    Q' \<rightarrow>(STLCal Source Target)* Q'' \<and> P'' \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> Q'' \<and> \<langle>P, \<alpha>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>Q, \<beta>\<rangle>)"
      and csRQ:   "\<forall>\<gamma> R'. R \<midarrow>\<Zcat>\<gamma>\<rightarrow>(STLCal Source Target)* R' \<longrightarrow>
                   (\<exists>\<beta> Q'' R''. Q \<midarrow>\<Zcat>\<beta>\<rightarrow>(STLCal Source Target)* Q'' \<and>
                    R' \<rightarrow>(STLCal Source Target)* R'' \<and> Q'' \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> R'' \<and> \<langle>Q, \<beta>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>R, \<gamma>\<rangle>)"
      and relPQ:  "P \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> Q"
      and relQR:  "Q \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> R"
      and trel:   "weak_labelled_correspondence_simulation (TRel\<^sup>+) Target"
    shows "\<forall>\<gamma> R'. R \<midarrow>\<Zcat>\<gamma>\<rightarrow>(STLCal Source Target)* R' \<longrightarrow>
           (\<exists>\<alpha> P'' R''. P \<midarrow>\<Zcat>\<alpha>\<rightarrow>(STLCal Source Target)* P'' \<and>
            R' \<rightarrow>(STLCal Source Target)* R'' \<and> P'' \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> R'' \<and> \<langle>P, \<alpha>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>R, \<gamma>\<rangle>)"
  using source_or_target[of P] source_or_target[of Q] source_or_target[of R]
proof auto
  fix \<gamma> R' SP SQ SR
  assume "SP \<in>S P" and "SQ \<in>S Q" and "SR \<in>S R"
  with relPQ relQR have A1: "SP = SR"
    using indRelRTPO_to_TRel
    by simp
  assume A2: "SourceTerm SR \<midarrow>\<Zcat>\<gamma>\<rightarrow>(STLCal Source Target)* R'"
  with A1 have "SourceTerm SP \<midarrow>\<Zcat>\<gamma>\<rightarrow>(STLCal Source Target)* R'"
    by simp
  moreover have "R' \<rightarrow>(STLCal Source Target)* R'"
    using WTS_refl[of R' "STLCal Source Target"]
    by simp
  moreover from A2 obtain SR' where "SR' \<in>S R'"
    using STLCal_weakLabelledSteps(1)[of SR \<gamma> R']
    by blast
  hence "R' \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> R'"
    using indRelRTPO.source[of SR' TRel]
    by simp
  moreover have "\<langle>SourceTerm SP, \<gamma>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>SourceTerm SR, \<gamma>\<rangle>"
    unfolding related_labels_def
    by simp
  ultimately show "\<exists>\<alpha> P''. SourceTerm SP \<midarrow>\<Zcat>\<alpha>\<rightarrow>(STLCal Source Target)* P'' \<and>
                   (\<exists>R''. R' \<rightarrow>(STLCal Source Target)* R'' \<and> P'' \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> R'' \<and>
                    \<langle>SourceTerm SP, \<alpha>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>SourceTerm SR, \<gamma>\<rangle>)"
    by blast
next
  fix \<gamma> R' SP SQ TR
  assume "TargetTerm TR \<midarrow>\<Zcat>\<gamma>\<rightarrow>(STLCal Source Target)* R'" and "TR \<in>T R"
  with csRQ obtain \<alpha> P'' R'' where A1: "Q \<midarrow>\<Zcat>\<alpha>\<rightarrow>(STLCal Source Target)* P''"
                               and A2: "R' \<rightarrow>(STLCal Source Target)* R''"
                               and A3: "P'' \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> R''" and A4: "\<langle>Q, \<alpha>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>TargetTerm TR, \<gamma>\<rangle>"
    by blast
  assume "SP \<in>S P" and "SQ \<in>S Q"
  with relPQ have A5: "Q = SourceTerm SP"
    using indRelRTPO_to_TRel(1)[of P Q TRel]
    by simp
  with A1 have A6: "SourceTerm SP \<midarrow>\<Zcat>\<alpha>\<rightarrow>(STLCal Source Target)* P''"
    by simp
  from A4 A5 have "\<langle>SourceTerm SP, \<alpha>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>TargetTerm TR, \<gamma>\<rangle>"
    by simp
  with A2 A3 A6 show "\<exists>\<alpha> P''. SourceTerm SP \<midarrow>\<Zcat>\<alpha>\<rightarrow>(STLCal Source Target)* P'' \<and>
                      (\<exists>R''. R' \<rightarrow>(STLCal Source Target)* R'' \<and> P'' \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> R'' \<and>
                       \<langle>SourceTerm SP, \<alpha>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>TargetTerm TR, \<gamma>\<rangle>)"
    by blast
next
  fix \<gamma> R' SP TQ SR
  assume "TQ \<in>T Q" and "SR \<in>S R"
  with relQR have False
    using indRelRTPO_to_TRel(3)[of Q R TRel]
    by simp
  thus "\<exists>\<alpha> P''. SourceTerm SP \<midarrow>\<Zcat>\<alpha>\<rightarrow>(STLCal Source Target)* P'' \<and>
        (\<exists>R''. R' \<rightarrow>(STLCal Source Target)* R'' \<and> P'' \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> R'' \<and>
         \<langle>SourceTerm SP, \<alpha>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>SourceTerm SR, \<gamma>\<rangle>)"
    by simp
next
  fix \<gamma> R' SP TQ TR
  assume A1: "TQ \<in>T Q" and "TR \<in>T R"
  with relQR have A2: "(TQ, TR) \<in> TRel\<^sup>+"
    using indRelRTPO_to_TRel(4)[of Q R TRel]
    by simp
  assume "TargetTerm TR \<midarrow>\<Zcat>\<gamma>\<rightarrow>(STLCal Source Target)* R'"
  then obtain \<gamma>' TR' where A3: "\<gamma>' \<in>TL \<langle>TargetTerm TR, \<gamma>\<rangle>" and A4: "TR' \<in>T R'"
                       and A5: "TR \<midarrow>\<Zcat>\<gamma>'\<rightarrow>Target* TR'"
    using STLCal_weakLabelledSteps(2)[of TR \<gamma> R']
    by blast
  from trel A2 A5 obtain TQ'' TR'' where A6: "TQ \<midarrow>\<Zcat>\<gamma>'\<rightarrow>Target* TQ''" and A7: "TR' \<rightarrow>Target* TR''"
                                     and A8: "(TQ'', TR'') \<in> TRel\<^sup>+"
    by blast
  from A3 A6 have A9: "TargetTerm TQ \<midarrow>\<Zcat>\<gamma>\<rightarrow>(STLCal Source Target)* TargetTerm TQ''"
    using STLCal_weakLabelledSteps(2)[of TQ \<gamma> "TargetTerm TQ''"]
    unfolding getTargetLabel_def
    by blast
  assume A10: "SP \<in>S P"
  with csQP A1 A9 obtain \<alpha> P''' Q''' where A11: "SourceTerm SP \<midarrow>\<Zcat>\<alpha>\<rightarrow>(STLCal Source Target)* P'''"
                                       and A12: "TargetTerm TQ'' \<rightarrow>(STLCal Source Target)* Q'''"
                                       and A13: "P''' \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> Q'''" and A14: "\<langle>P, \<alpha>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>Q, \<gamma>\<rangle>"
    by blast
  from A12 obtain TQ''' where A15: "TQ''' \<in>T Q'''" and A16: "TQ'' \<rightarrow>Target* TQ'''"
    using STLCal_weakTauSteps(2)[of TQ'' Q''']
    by blast
  from A16 have "TQ'' \<midarrow>\<Zcat>\<tau>-Target\<rightarrow>Target* TQ'''"
    unfolding weakLabelledStep_def
    by simp
  with trel A8 obtain TR''' where A17: "TR'' \<midarrow>\<Zcat>\<tau>-Target\<rightarrow>Target* TR'''"
                              and A18: "(TQ''', TR''') \<in> TRel\<^sup>+"
    by blast
  from A4 A7 A17 have A19: "R' \<rightarrow>(STLCal Source Target)* TargetTerm TR'''"
    using weakTauSteps_trans[of TR' Target TR'' TR''']
          STLCal_weakTauSteps(2)[of TR' "TargetTerm TR'''"]
    unfolding weakLabelledStep_def
    by auto
  from A18 have "TargetTerm TQ''' \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> TargetTerm TR'''"
    using transitive_closure_of_TRel_to_indRelRTPO[of TQ''' TR''' TRel]
    by blast
  with A13 A15 have A20: "P''' \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> TargetTerm TR'''"
    using indRelRTPO.trans[of P''' Q''' TRel "TargetTerm TR'''"]
    by simp
  from A1 A10 A14 have "\<langle>SourceTerm SP, \<alpha>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>TargetTerm TR, \<gamma>\<rangle>"
    using related_labels_exchange_processes[of P \<alpha> Q \<gamma> "SourceTerm SP" "TargetTerm TR"]
    by simp
  with A11 A19 A20 show "\<exists>\<alpha> P''. SourceTerm SP \<midarrow>\<Zcat>\<alpha>\<rightarrow>(STLCal Source Target)* P'' \<and>
                         (\<exists>R''. R' \<rightarrow>(STLCal Source Target)* R'' \<and> P'' \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> R'' \<and>
                          \<langle>SourceTerm SP, \<alpha>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>TargetTerm TR, \<gamma>\<rangle>)"
    by blast
next
  fix \<gamma> R' TP SQ SR
  assume "TP \<in>T P" and "SQ \<in>S Q"
  with relPQ have False
    using indRelRTPO_to_TRel(3)[of P Q]
    by simp
  thus "\<exists>\<alpha> P''. TargetTerm TP \<midarrow>\<Zcat>\<alpha>\<rightarrow>(STLCal Source Target)* P'' \<and>
        (\<exists>R''. R' \<rightarrow>(STLCal Source Target)* R'' \<and> P'' \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> R'' \<and>
         \<langle>TargetTerm TP, \<alpha>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>SourceTerm SR, \<gamma>\<rangle>)"
    by simp
next
  fix \<gamma> R' TP SQ TR
  assume "TP \<in>T P" and "SQ \<in>S Q"
  with relPQ have False
    using indRelRTPO_to_TRel(3)[of P Q]
    by simp
  thus "\<exists>\<alpha> P''. TargetTerm TP \<midarrow>\<Zcat>\<alpha>\<rightarrow>(STLCal Source Target)* P'' \<and>
        (\<exists>R''. R' \<rightarrow>(STLCal Source Target)* R'' \<and> P'' \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> R'' \<and>
         \<langle>TargetTerm TP, \<alpha>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>TargetTerm TR, \<gamma>\<rangle>)"
    by simp
next
  fix \<gamma> R' TP TQ SR
  assume "TQ \<in>T Q" and "SR \<in>S R"
  with relQR have False
    using indRelRTPO_to_TRel(3)[of Q R]
    by simp
  thus "\<exists>\<alpha> P''. TargetTerm TP \<midarrow>\<Zcat>\<alpha>\<rightarrow>(STLCal Source Target)* P'' \<and>
        (\<exists>R''. R' \<rightarrow>(STLCal Source Target)* R'' \<and> P'' \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> R'' \<and>
         \<langle>TargetTerm TP, \<alpha>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>SourceTerm SR, \<gamma>\<rangle>)"
    by simp
next
  fix \<gamma> R' TP TQ TR
  assume A1: "TQ \<in>T Q" and "TR \<in>T R"
  with relQR have A2: "(TQ, TR) \<in> TRel\<^sup>+"
    using indRelRTPO_to_TRel(4)[of Q R TRel]
    by simp
  assume "TargetTerm TR \<midarrow>\<Zcat>\<gamma>\<rightarrow>(STLCal Source Target)* R'"
  then obtain \<gamma>' TR' where A3: "\<gamma>' \<in>TL \<langle>TargetTerm TR, \<gamma>\<rangle>" and A4: "TR' \<in>T R'"
                       and A5: "TR \<midarrow>\<Zcat>\<gamma>'\<rightarrow>Target* TR'"
    using STLCal_weakLabelledSteps(2)[of TR \<gamma> R']
    by blast
  from trel A2 A5 obtain TQ'' TR'' where A6: "TQ \<midarrow>\<Zcat>\<gamma>'\<rightarrow>Target* TQ''" and A7: "TR' \<rightarrow>Target* TR''"
                                     and A8: "(TQ'', TR'') \<in> TRel\<^sup>+"
    by blast
  assume "TP \<in>T P"
  with relPQ A1 have "(TP, TQ) \<in> TRel\<^sup>+"
    using indRelRTPO_to_TRel(4)[of P Q TRel]
    by simp
  with trel A6 obtain TQ''' TP''' where A9:  "TP \<midarrow>\<Zcat>\<gamma>'\<rightarrow>Target* TP'''"
                                    and A10: "TQ'' \<rightarrow>Target* TQ'''"
                                    and A11: "(TP''', TQ''') \<in> TRel\<^sup>+"
    by blast
  from A3 A9 have A12: "TargetTerm TP \<midarrow>\<Zcat>\<gamma>\<rightarrow>(STLCal Source Target)* TargetTerm TP'''"
    using STLCal_weakLabelledSteps(2)[of TP \<gamma> "TargetTerm TP'''"]
    unfolding getTargetLabel_def
    by blast
  from A10 have "TQ'' \<midarrow>\<Zcat>\<tau>-Target\<rightarrow>Target* TQ'''"
    unfolding weakLabelledStep_def
    by simp
  with trel A8 obtain TR''' where A13: "TR'' \<midarrow>\<Zcat>\<tau>-Target\<rightarrow>Target* TR'''"
                              and A14: "(TQ''', TR''') \<in> TRel\<^sup>+"
    by blast
  from A4 A7 A13 have A15: "R' \<rightarrow>(STLCal Source Target)* TargetTerm TR'''"
    using weakTauSteps_trans[of TR' Target TR'' TR''']
          STLCal_weakTauSteps(2)[of TR' "TargetTerm TR'''"]
    unfolding weakLabelledStep_def
    by simp
  from A11 A14 have "(TP''', TR''') \<in> TRel\<^sup>+"
    using transD[of "TRel\<^sup>+" TP''' TQ''' TR''']
    by simp
  hence A16: "TargetTerm TP''' \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> TargetTerm TR'''"
    using transitive_closure_of_TRel_to_indRelRTPO[of TP''' TR''' TRel]
    by simp
  have "\<langle>TargetTerm TP, \<gamma>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>TargetTerm TR, \<gamma>\<rangle>"
    unfolding related_labels_def
    by simp
  with A12 A15 A16
  show "\<exists>\<alpha> P''. TargetTerm TP \<midarrow>\<Zcat>\<alpha>\<rightarrow>(STLCal Source Target)* P'' \<and>
        (\<exists>R''. R' \<rightarrow>(STLCal Source Target)* R'' \<and> P'' \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> R'' \<and>
         \<langle>TargetTerm TP, \<alpha>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>TargetTerm TR, \<gamma>\<rangle>)"
    by blast
qed

lemma (in encodingLS_encL) WOC_iff_indRelRTPO_is_labelled_correspondence_simulation_encL:
  fixes TRel :: "('procT \<times> 'procT) set"
  shows "(weakly_operational_corresponding_encL (TRel\<^sup>*)
         \<and> weak_labelled_correspondence_simulation (TRel\<^sup>+) Target)
         = weak_labelled_correspondence_simulation_encL (indRelRTPO TRel)"
proof (rule iffI, erule conjE)
  assume woc: "weakly_operational_corresponding_encL (TRel\<^sup>*)"
     and csi: "weak_labelled_correspondence_simulation (TRel\<^sup>+) Target"
  show "weak_labelled_correspondence_simulation_encL (indRelRTPO TRel)"
  proof
    from woc csi show sim: "weak_labelled_simulation_encL (indRelRTPO TRel)"
      using OCom_iff_indRelRTPO_is_weak_labelled_simulation_encL[where TRel="TRel"]
      by simp
    show "\<forall>P Q \<beta> Q'. P \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> Q \<and> Q \<midarrow>\<Zcat>\<beta>\<rightarrow>(STLCal Source Target)* Q' \<longrightarrow>
          (\<exists>\<alpha> P'' Q''. P \<midarrow>\<Zcat>\<alpha>\<rightarrow>(STLCal Source Target)* P'' \<and> Q' \<rightarrow>(STLCal Source Target)* Q'' \<and>
           P'' \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> Q'' \<and> \<langle>P, \<alpha>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>Q, \<beta>\<rangle>)"
    proof clarify
      fix P Q \<beta> Q'
      assume "P \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> Q" and "Q \<midarrow>\<Zcat>\<beta>\<rightarrow>(STLCal Source Target)* Q'"
      thus "\<exists>\<alpha> P'' Q''. P \<midarrow>\<Zcat>\<alpha>\<rightarrow>(STLCal Source Target)* P'' \<and> Q' \<rightarrow>(STLCal Source Target)* Q'' \<and>
            P'' \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> Q'' \<and> \<langle>P, \<alpha>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>Q, \<beta>\<rangle>"
      proof (induct arbitrary: \<beta> Q')
        case (encR S)
        assume "TargetTerm (\<lbrakk>S\<rbrakk>) \<midarrow>\<Zcat>\<beta>\<rightarrow>(STLCal Source Target)* Q'"
        then obtain \<beta>' T where A1: "\<beta>' \<in>TL \<langle>TargetTerm (\<lbrakk>S\<rbrakk>), \<beta>\<rangle>" and A2: "T \<in>T Q'"
                           and A3: "\<lbrakk>S\<rbrakk> \<midarrow>\<Zcat>\<beta>'\<rightarrow>Target* T"
          using STLCal_weakLabelledSteps(2)[of "\<lbrakk>S\<rbrakk>" \<beta> Q']
          by blast
        from woc A3 obtain \<alpha>' S' T' where A4: "S \<midarrow>\<Zcat>\<alpha>'\<rightarrow>Source* S'" and A5: "T \<rightarrow>Target* T'"
                                      and A6: "(\<lbrakk>S'\<rbrakk>, T') \<in> TRel\<^sup>*" and A7: "\<lblot>\<alpha>'\<rblot> = \<beta>'"
          by blast
        obtain \<alpha> where A8: "\<alpha>' \<in>SL \<langle>SourceTerm S, \<alpha>\<rangle>"
          unfolding getSourceLabel_def
          by blast
        with A4 have "SourceTerm S \<midarrow>\<Zcat>\<alpha>\<rightarrow>(STLCal Source Target)* (SourceTerm S')"
          using STLCal_weakLabelledSteps(1)[of S \<alpha> "SourceTerm S'"]
          by blast
        moreover from A2 A5 have "Q' \<rightarrow>(STLCal Source Target)* (TargetTerm T')"
          using STLCal_weakTauSteps(2)[of T "TargetTerm T'"]
          by blast
        moreover have "SourceTerm S' \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> TargetTerm T'"
        proof -
          have B: "SourceTerm S' \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> TargetTerm (\<lbrakk>S'\<rbrakk>)"
            by (rule indRelRTPO.encR)
          from A6 have "\<lbrakk>S'\<rbrakk> = T' \<or> (\<lbrakk>S'\<rbrakk>, T') \<in> TRel\<^sup>+"
            using rtrancl_eq_or_trancl[of "\<lbrakk>S'\<rbrakk>" T' TRel]
            by blast
          moreover from B have "\<lbrakk>S'\<rbrakk> = T' \<Longrightarrow> SourceTerm S' \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> TargetTerm T'"
            by simp
          moreover have "(\<lbrakk>S'\<rbrakk>, T') \<in> TRel\<^sup>+ \<Longrightarrow> SourceTerm S' \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> TargetTerm T'"
          proof -
            assume "(\<lbrakk>S'\<rbrakk>, T') \<in> TRel\<^sup>+"
            hence "TargetTerm (\<lbrakk>S'\<rbrakk>) \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> TargetTerm T'"
              by (simp add: transitive_closure_of_TRel_to_indRelRTPO[where TRel="TRel"])
            with B show "SourceTerm S' \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> TargetTerm T'"
              by (rule indRelRTPO.trans)
          qed
          ultimately show "SourceTerm S' \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> TargetTerm T'"
            by blast
        qed
        moreover from A1 A7 A8 have "\<lparr>SourceTerm S, \<alpha>\<rparr>\<mapsto>\<langle>TargetTerm (\<lbrakk>S\<rbrakk>), \<beta>\<rangle>"
          unfolding encLST_def
          by blast
        hence "\<langle>SourceTerm S, \<alpha>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>TargetTerm (\<lbrakk>S\<rbrakk>), \<beta>\<rangle>"
          unfolding related_labels_def
          by simp
        ultimately show "\<exists>\<alpha> P'' Q''. SourceTerm S \<midarrow>\<Zcat>\<alpha>\<rightarrow>(STLCal Source Target)* P'' \<and>
                         Q' \<rightarrow>(STLCal Source Target)* Q'' \<and> P'' \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> Q'' \<and>
                         \<langle>SourceTerm S, \<alpha>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>TargetTerm (\<lbrakk>S\<rbrakk>), \<beta>\<rangle>"
          by blast
      next
        case (source S)
        assume A1: "SourceTerm S \<midarrow>\<Zcat>\<beta>\<rightarrow>(STLCal Source Target)* Q'"
        moreover have "Q' \<rightarrow>(STLCal Source Target)* Q'"
          using WTS_refl[of Q' "STLCal Source Target"]
          by simp
        moreover from A1 obtain S' where "S' \<in>S Q'"
          using STLCal_weakLabelledSteps(1)[of S \<beta> Q']
          by blast
        hence "Q' \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> Q'"
          by (simp add: indRelRTPO.source)
        moreover have "\<langle>SourceTerm S, \<beta>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>SourceTerm S, \<beta>\<rangle>"
          unfolding related_labels_def
          by simp
        ultimately show "\<exists>\<alpha> P'' Q''. SourceTerm S \<midarrow>\<Zcat>\<alpha>\<rightarrow>(STLCal Source Target)* P'' \<and>
                         Q' \<rightarrow>(STLCal Source Target)* Q'' \<and> P'' \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> Q'' \<and>
                         \<langle>SourceTerm S, \<alpha>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>SourceTerm S, \<beta>\<rangle>"
          by blast
      next
        case (target T1 T2)
        assume "TargetTerm T2 \<midarrow>\<Zcat>\<beta>\<rightarrow>(STLCal Source Target)* Q'"
        then obtain \<beta>' T2' where A1: "\<beta>' \<in>TL \<langle>TargetTerm T2, \<beta>\<rangle>" and A2: "T2' \<in>T Q'"
                             and A3: "T2 \<midarrow>\<Zcat>\<beta>'\<rightarrow>Target* T2'"
          using STLCal_weakLabelledSteps(2)[of T2 \<beta> Q']
          by blast
        assume "(T1, T2) \<in> TRel"
        hence "(T1, T2) \<in> TRel\<^sup>+"
          by simp
        with csi A3 obtain T1' T2'' where A4: "T1 \<midarrow>\<Zcat>\<beta>'\<rightarrow>Target* T1'" and A5: "T2' \<rightarrow>Target* T2''"
                                      and A6: "(T1', T2'') \<in> TRel\<^sup>+"
          by blast
        from A1 A4 have "TargetTerm T1 \<midarrow>\<Zcat>\<beta>\<rightarrow>(STLCal Source Target)* (TargetTerm T1')"
          using STLCal_weakLabelledSteps(2)[of T1 \<beta> "TargetTerm T1'"]
          unfolding getTargetLabel_def
          by blast
        moreover from A2 A5 have "Q' \<rightarrow>(STLCal Source Target)* (TargetTerm T2'')"
          using STLCal_weakTauSteps(2)[of T2' "TargetTerm T2''"]
          by blast
        moreover from A6 have "TargetTerm T1' \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> (TargetTerm T2'')"
          by (simp add: transitive_closure_of_TRel_to_indRelRTPO)
        moreover have "\<langle>TargetTerm T1, \<beta>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>TargetTerm T2, \<beta>\<rangle>"
          unfolding related_labels_def
          by simp
        ultimately show "\<exists>\<alpha> P'' Q''. TargetTerm T1 \<midarrow>\<Zcat>\<alpha>\<rightarrow>(STLCal Source Target)* P'' \<and>
                         Q' \<rightarrow>(STLCal Source Target)* Q'' \<and> P'' \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> Q'' \<and>
                         \<langle>TargetTerm T1, \<alpha>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>TargetTerm T2, \<beta>\<rangle>"
          by blast
      next
        case (trans P Q R \<gamma> R')
        assume "R \<midarrow>\<Zcat>\<gamma>\<rightarrow>(STLCal Source Target)* R'"
           and "\<And>\<gamma> R'. R \<midarrow>\<Zcat>\<gamma>\<rightarrow>(STLCal Source Target)* R' \<Longrightarrow>
                \<exists>\<beta> Q'' R''. Q \<midarrow>\<Zcat>\<beta>\<rightarrow>(STLCal Source Target)* Q'' \<and>
                R' \<rightarrow>(STLCal Source Target)* R'' \<and> Q'' \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> R'' \<and> \<langle>Q, \<beta>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>R, \<gamma>\<rangle>"
           and "\<And>\<beta> Q'. Q \<midarrow>\<Zcat>\<beta>\<rightarrow>(STLCal Source Target)* Q' \<Longrightarrow>
                \<exists>\<alpha> P'' Q''. P \<midarrow>\<Zcat>\<alpha>\<rightarrow>(STLCal Source Target)* P'' \<and>
                Q' \<rightarrow>(STLCal Source Target)* Q'' \<and> P'' \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> Q'' \<and> \<langle>P, \<alpha>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>Q, \<beta>\<rangle>"
           and "P \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> Q" and "Q \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> R"
        with csi show "\<exists>\<alpha> P'' R''. P \<midarrow>\<Zcat>\<alpha>\<rightarrow>(STLCal Source Target)* P'' \<and>
                         R' \<rightarrow>(STLCal Source Target)* R'' \<and> P'' \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> R'' \<and>
                         \<langle>P, \<alpha>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>R, \<gamma>\<rangle>"
          using indRelRTPO_labelled_correspondence_simulation_encL_trans[of Q P TRel R]
          by blast
      qed
    qed
  qed
next
  assume csi: "weak_labelled_correspondence_simulation_encL (indRelRTPO TRel)"
  show "weakly_operational_corresponding_encL (TRel\<^sup>*)
        \<and> weak_labelled_correspondence_simulation (TRel\<^sup>+) Target"
  proof
    have " \<forall>S. SourceTerm S \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> TargetTerm (\<lbrakk>S\<rbrakk>)"
      by (simp add: indRelRTPO.encR)
    moreover have "\<forall>S T. SourceTerm S \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> TargetTerm T \<longrightarrow> (\<lbrakk>S\<rbrakk>, T) \<in> TRel\<^sup>*"
      using indRelRTPO_to_TRel(2)[where TRel="TRel"] trans_closure_of_TRel_refl_cond
      by simp
    ultimately show "weakly_operational_corresponding_encL (TRel\<^sup>*)"
      using weak_labelled_correspondence_simulation_impl_WOC_encL[where Rel="indRelRTPO TRel" and
              TRel="TRel"] csi
      by simp
  next
    from csi show "weak_labelled_correspondence_simulation (TRel\<^sup>+) Target"
      using indRelRTPO_impl_TRel_is_weak_labelled_correspondence_simulation_encL[where TRel="TRel"]
      by simp
  qed
qed

lemma (in encoding) WOC_iff_reduction_correspondence_simulation:
  fixes TRel :: "('procT \<times> 'procT) set"
  shows "(weakly_operational_corresponding (TRel\<^sup>*)
         \<and> weak_reduction_correspondence_simulation (TRel\<^sup>+) Target)
         = (\<exists>Rel. (\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel)
            \<and> (\<forall>T1 T2. (T1, T2) \<in> TRel \<longrightarrow> (TargetTerm T1, TargetTerm T2) \<in> Rel)
            \<and> (\<forall>T1 T2. (TargetTerm T1, TargetTerm T2) \<in> Rel \<longrightarrow> (T1, T2) \<in> TRel\<^sup>+)
            \<and> (\<forall>S T. (SourceTerm S, TargetTerm T) \<in> Rel \<longrightarrow> (\<lbrakk>S\<rbrakk>, T) \<in> TRel\<^sup>*)
            \<and> weak_reduction_correspondence_simulation Rel (STCal Source Target))"
proof (rule iffI, erule conjE)
  have "\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> indRelRTPO TRel"
    by (simp add: indRelRTPO.encR)
  moreover have "\<forall>T1 T2. (T1, T2) \<in> TRel \<longrightarrow> TargetTerm T1 \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> TargetTerm T2"
    by (simp add: indRelRTPO.target)
  moreover have "\<forall>T1 T2. TargetTerm T1 \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> TargetTerm T2 \<longrightarrow> (T1, T2) \<in> TRel\<^sup>+"
    using indRelRTPO_to_TRel(4)[where TRel="TRel"]
    by simp
  moreover have "\<forall>S T. SourceTerm S \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> TargetTerm T \<longrightarrow> (\<lbrakk>S\<rbrakk>, T) \<in> TRel\<^sup>*"
    using indRelRTPO_to_TRel(2)[where TRel="TRel"] trans_closure_of_TRel_refl_cond
    by simp
  moreover assume "weakly_operational_corresponding (TRel\<^sup>*)"
              and "weak_reduction_correspondence_simulation (TRel\<^sup>+) Target"
  hence "weak_reduction_correspondence_simulation (indRelRTPO TRel) (STCal Source Target)"
    using WOC_iff_indRelRTPO_is_reduction_correspondence_simulation[where TRel="TRel"]
    by simp
  ultimately show "\<exists>Rel. (\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel)
                   \<and> (\<forall>T1 T2. (T1, T2) \<in> TRel \<longrightarrow> (TargetTerm T1, TargetTerm T2) \<in> Rel)
                   \<and> (\<forall>T1 T2. (TargetTerm T1, TargetTerm T2) \<in> Rel \<longrightarrow> (T1, T2) \<in> TRel\<^sup>+)
                   \<and> (\<forall>S T. (SourceTerm S, TargetTerm T) \<in> Rel \<longrightarrow> (\<lbrakk>S\<rbrakk>, T) \<in> TRel\<^sup>*)
                   \<and> weak_reduction_correspondence_simulation Rel (STCal Source Target)"
    by blast
next
  assume "\<exists>Rel. (\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel)
          \<and> (\<forall>T1 T2. (T1, T2) \<in> TRel \<longrightarrow> (TargetTerm T1, TargetTerm T2) \<in> Rel)
          \<and> (\<forall>T1 T2. (TargetTerm T1, TargetTerm T2) \<in> Rel \<longrightarrow> (T1, T2) \<in> TRel\<^sup>+)
          \<and> (\<forall>S T. (SourceTerm S, TargetTerm T) \<in> Rel \<longrightarrow> (\<lbrakk>S\<rbrakk>, T) \<in> TRel\<^sup>*)
          \<and> weak_reduction_correspondence_simulation Rel (STCal Source Target)"
  from this obtain Rel where A1: "\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel"
   and A2: "\<forall>T1 T2. (T1, T2) \<in> TRel \<longrightarrow> (TargetTerm T1, TargetTerm T2) \<in> Rel"
   and A3: "\<forall>T1 T2. (TargetTerm T1, TargetTerm T2) \<in> Rel \<longrightarrow> (T1, T2) \<in> TRel\<^sup>+"
   and A4: "\<forall>S T. (SourceTerm S, TargetTerm T) \<in> Rel \<longrightarrow> (\<lbrakk>S\<rbrakk>, T) \<in> TRel\<^sup>*"
   and A5: "weak_reduction_correspondence_simulation Rel (STCal Source Target)"
    by blast
  from A1 A4 A5 have "weakly_operational_corresponding (TRel\<^sup>*)"
    using weak_reduction_correspondence_simulation_impl_WOC[where Rel="Rel" and TRel="TRel"]
    by simp
  moreover from A2 A3 A5 have "weak_reduction_correspondence_simulation (TRel\<^sup>+) Target"
    using rel_with_target_impl_transC_TRel_is_weak_reduction_correspondence_simulation
    by simp
  ultimately show "weakly_operational_corresponding (TRel\<^sup>*)
                   \<and> weak_reduction_correspondence_simulation (TRel\<^sup>+) Target"
    by simp
qed

lemma (in encodingLS_encL) WOC_iff_labelled_correspondence_simulation_encL:
  fixes TRel :: "('procT \<times> 'procT) set"
  shows "(weakly_operational_corresponding_encL (TRel\<^sup>*)
         \<and> weak_labelled_correspondence_simulation (TRel\<^sup>+) Target)
         = (\<exists>Rel. (\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel)
            \<and> (\<forall>T1 T2. (T1, T2) \<in> TRel \<longrightarrow> (TargetTerm T1, TargetTerm T2) \<in> Rel)
            \<and> (\<forall>T1 T2. (TargetTerm T1, TargetTerm T2) \<in> Rel \<longrightarrow> (T1, T2) \<in> TRel\<^sup>+)
            \<and> (\<forall>S T. (SourceTerm S, TargetTerm T) \<in> Rel \<longrightarrow> (\<lbrakk>S\<rbrakk>, T) \<in> TRel\<^sup>*)
            \<and> weak_labelled_correspondence_simulation_encL Rel)"
proof (rule iffI, erule conjE)
  have "\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> indRelRTPO TRel"
    by (simp add: indRelRTPO.encR)
  moreover have "\<forall>T1 T2. (T1, T2) \<in> TRel \<longrightarrow> TargetTerm T1 \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> TargetTerm T2"
    by (simp add: indRelRTPO.target)
  moreover have "\<forall>T1 T2. TargetTerm T1 \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> TargetTerm T2 \<longrightarrow> (T1, T2) \<in> TRel\<^sup>+"
    using indRelRTPO_to_TRel(4)[where TRel="TRel"]
    by simp
  moreover have "\<forall>S T. SourceTerm S \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> TargetTerm T \<longrightarrow> (\<lbrakk>S\<rbrakk>, T) \<in> TRel\<^sup>*"
    using indRelRTPO_to_TRel(2)[where TRel="TRel"] trans_closure_of_TRel_refl_cond
    by simp
  moreover assume "weakly_operational_corresponding_encL (TRel\<^sup>*)"
              and "weak_labelled_correspondence_simulation (TRel\<^sup>+) Target"
  hence "weak_labelled_correspondence_simulation_encL (indRelRTPO TRel)"
    using WOC_iff_indRelRTPO_is_labelled_correspondence_simulation_encL[where TRel="TRel"]
    by simp
  ultimately show "\<exists>Rel. (\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel)
                   \<and> (\<forall>T1 T2. (T1, T2) \<in> TRel \<longrightarrow> (TargetTerm T1, TargetTerm T2) \<in> Rel)
                   \<and> (\<forall>T1 T2. (TargetTerm T1, TargetTerm T2) \<in> Rel \<longrightarrow> (T1, T2) \<in> TRel\<^sup>+)
                   \<and> (\<forall>S T. (SourceTerm S, TargetTerm T) \<in> Rel \<longrightarrow> (\<lbrakk>S\<rbrakk>, T) \<in> TRel\<^sup>*)
                   \<and> weak_labelled_correspondence_simulation_encL Rel"
    by blast
next
  assume "\<exists>Rel. (\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel)
          \<and> (\<forall>T1 T2. (T1, T2) \<in> TRel \<longrightarrow> (TargetTerm T1, TargetTerm T2) \<in> Rel)
          \<and> (\<forall>T1 T2. (TargetTerm T1, TargetTerm T2) \<in> Rel \<longrightarrow> (T1, T2) \<in> TRel\<^sup>+)
          \<and> (\<forall>S T. (SourceTerm S, TargetTerm T) \<in> Rel \<longrightarrow> (\<lbrakk>S\<rbrakk>, T) \<in> TRel\<^sup>*)
          \<and> weak_labelled_correspondence_simulation_encL Rel"
  from this obtain Rel where A1: "\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel"
   and A2: "\<forall>T1 T2. (T1, T2) \<in> TRel \<longrightarrow> (TargetTerm T1, TargetTerm T2) \<in> Rel"
   and A3: "\<forall>T1 T2. (TargetTerm T1, TargetTerm T2) \<in> Rel \<longrightarrow> (T1, T2) \<in> TRel\<^sup>+"
   and A4: "\<forall>S T. (SourceTerm S, TargetTerm T) \<in> Rel \<longrightarrow> (\<lbrakk>S\<rbrakk>, T) \<in> TRel\<^sup>*"
   and A5: "weak_labelled_correspondence_simulation_encL Rel"
    by blast
  from A1 A4 A5 have "weakly_operational_corresponding_encL (TRel\<^sup>*)"
    using weak_labelled_correspondence_simulation_impl_WOC_encL[where Rel="Rel" and TRel="TRel"]
    by simp
  moreover from A2 A3 A5 have "weak_labelled_correspondence_simulation (TRel\<^sup>+) Target"
    using rel_with_target_impl_transC_TRel_is_weak_labelled_correspondence_simulation_encL
    by simp
  ultimately show "weakly_operational_corresponding_encL (TRel\<^sup>*)
                   \<and> weak_labelled_correspondence_simulation (TRel\<^sup>+) Target"
    by simp
qed

lemma rel_includes_TRel_modulo_preorder:
  fixes Rel  :: "(('procS, 'procT) Proc \<times> ('procS, 'procT) Proc) set"
    and TRel :: "('procT \<times> 'procT) set"
  assumes transT: "trans TRel"
  shows "((\<forall>T1 T2. (T1, T2) \<in> TRel \<longrightarrow> (TargetTerm T1, TargetTerm T2) \<in> Rel)
          \<and> (\<forall>T1 T2. (TargetTerm T1, TargetTerm T2) \<in> Rel \<longrightarrow> (T1, T2) \<in> TRel\<^sup>+))
         = (TRel = {(T1, T2). (TargetTerm T1, TargetTerm T2) \<in> Rel})"
proof (rule iffI, erule conjE)
  assume "\<forall>T1 T2. (T1, T2) \<in> TRel \<longrightarrow> (TargetTerm T1, TargetTerm T2) \<in> Rel"
     and "\<forall>T1 T2. (TargetTerm T1, TargetTerm T2) \<in> Rel \<longrightarrow> (T1, T2) \<in> TRel\<^sup>+"
  with transT show "TRel = {(T1, T2). (TargetTerm T1, TargetTerm T2) \<in> Rel}"
      using trancl_id[of TRel]
    by blast
next
  assume A: "TRel = {(T1, T2). (TargetTerm T1, TargetTerm T2) \<in> Rel}"
  hence "\<forall>T1 T2. (T1, T2) \<in> TRel \<longrightarrow> (TargetTerm T1, TargetTerm T2) \<in> Rel"
    by simp
  moreover from transT A
  have "\<forall>T1 T2. (TargetTerm T1, TargetTerm T2) \<in> Rel \<longrightarrow> (T1, T2) \<in> TRel\<^sup>+"
      using trancl_id[of TRel]
    by blast
  ultimately show "(\<forall>T1 T2. (T1, T2) \<in> TRel \<longrightarrow> (TargetTerm T1, TargetTerm T2) \<in> Rel)
                   \<and> (\<forall>T1 T2. (TargetTerm T1, TargetTerm T2) \<in> Rel \<longrightarrow> (T1, T2) \<in> TRel\<^sup>+)"
    by simp
qed

lemma (in encoding) WOC_wrt_preorder_iff_reduction_correspondence_simulation:
  fixes TRel :: "('procT \<times> 'procT) set"
  shows "(weakly_operational_corresponding TRel \<and> preorder TRel
         \<and> weak_reduction_correspondence_simulation TRel Target)
         = (\<exists>Rel. (\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel)
            \<and> TRel = {(T1, T2). (TargetTerm T1, TargetTerm T2) \<in> Rel}
            \<and> (\<forall>S T. (SourceTerm S, TargetTerm T) \<in> Rel \<longrightarrow> (\<lbrakk>S\<rbrakk>, T) \<in> TRel)
            \<and> preorder Rel
            \<and> weak_reduction_correspondence_simulation Rel (STCal Source Target))"
proof (rule iffI, erule conjE, erule conjE, erule conjE)
  assume A1: "operational_complete TRel" and A2: "weakly_operational_sound TRel"
     and A3:"preorder TRel" and A4: "weak_reduction_correspondence_simulation TRel Target"
  from A3 have A5: "TRel\<^sup>+ = TRel"
    using trancl_id[of TRel]
    unfolding preorder_on_def
    by blast
  with A3 have "TRel\<^sup>* = TRel"
    using trancl_id[of TRel] reflcl_trancl[of TRel]
    unfolding preorder_on_def refl_on_def
    by auto
  with A1 A2 have "weakly_operational_corresponding (TRel\<^sup>*)"
    by simp
  moreover from A4 A5 have "weak_reduction_correspondence_simulation (TRel\<^sup>+) Target"
    by simp
  ultimately
  have "weak_reduction_correspondence_simulation (indRelRTPO TRel) (STCal Source Target)"
    using WOC_iff_indRelRTPO_is_reduction_correspondence_simulation[where TRel="TRel"]
    by blast
  moreover have "\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> indRelRTPO TRel"
    by (simp add: indRelRTPO.encR)
  moreover
  have "TRel = {(T1, T2). (TargetTerm T1, TargetTerm T2) \<in> indRelRTPO TRel}"
  proof auto
    fix TP TQ
    assume "(TP, TQ) \<in> TRel"
    thus "TargetTerm TP \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> TargetTerm TQ"
      by (rule indRelRTPO.target)
  next
    fix TP TQ
    assume "TargetTerm TP \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> TargetTerm TQ"
    with A3 show "(TP, TQ) \<in> TRel"
      using indRelRTPO_to_TRel(4)[where TRel="TRel"] trancl_id[of TRel]
      unfolding preorder_on_def
      by blast
  qed
  moreover from A3
  have "\<forall>S T. (SourceTerm S, TargetTerm T) \<in> indRelRTPO TRel \<longrightarrow> (\<lbrakk>S\<rbrakk>, T) \<in> TRel\<^sup>+"
    using indRelRTPO_to_TRel(2)[where TRel="TRel"] reflcl_trancl[of TRel]
          trans_closure_of_TRel_refl_cond[where TRel="TRel"]
    unfolding preorder_on_def refl_on_def
    by blast
  with A3 have "\<forall>S T. (SourceTerm S, TargetTerm T) \<in> indRelRTPO TRel \<longrightarrow> (\<lbrakk>S\<rbrakk>, T) \<in> TRel"
    using trancl_id[of TRel]
    unfolding preorder_on_def
    by blast
  moreover from A3 have "refl (indRelRTPO TRel)"
    using indRelRTPO_refl[of TRel]
    unfolding preorder_on_def
    by simp
  moreover have "trans (indRelRTPO TRel)"
    using indRelRTPO.trans
    unfolding trans_def
    by blast
  ultimately show "\<exists>Rel. (\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel)
                   \<and> TRel = {(T1, T2). (TargetTerm T1, TargetTerm T2) \<in> Rel}
                   \<and> (\<forall>S T. (SourceTerm S, TargetTerm T) \<in> Rel \<longrightarrow> (\<lbrakk>S\<rbrakk>, T) \<in> TRel)
                   \<and> preorder Rel
                   \<and> weak_reduction_correspondence_simulation Rel (STCal Source Target)"
    unfolding preorder_on_def
    by auto
next
  assume "\<exists>Rel. (\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel)
          \<and> TRel = {(T1, T2). (TargetTerm T1, TargetTerm T2) \<in> Rel}
          \<and> (\<forall>S T. (SourceTerm S, TargetTerm T) \<in> Rel \<longrightarrow> (\<lbrakk>S\<rbrakk>, T) \<in> TRel)
          \<and> preorder Rel
          \<and> weak_reduction_correspondence_simulation Rel (STCal Source Target)"
  from this obtain Rel where B1: "\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel"
   and B2: "TRel = {(T1, T2). (TargetTerm T1, TargetTerm T2) \<in> Rel}"
   and B3: "\<forall>S T. (SourceTerm S, TargetTerm T) \<in> Rel \<longrightarrow> (\<lbrakk>S\<rbrakk>, T) \<in> TRel" and B4: "preorder Rel"
   and B5: "weak_reduction_correspondence_simulation Rel (STCal Source Target)"
    by blast
  from B2 B4 have B6: "refl TRel"
    unfolding preorder_on_def refl_on_def
    by blast
  from B2 B4 have B7: "trans TRel"
    unfolding trans_def preorder_on_def
    by blast
  hence B8: "TRel\<^sup>+ = TRel"
    using trancl_id[of TRel]
    by simp
  with B6 have "TRel\<^sup>* = TRel"
    using reflcl_trancl[of TRel]
    unfolding refl_on_def
    by blast
  with B1 B3 B5 have "weakly_operational_corresponding TRel"
    using weak_reduction_correspondence_simulation_impl_WOC[where Rel="Rel" and TRel="TRel"]
    by simp
  moreover from B6 B7 have "preorder TRel"
    unfolding preorder_on_def by simp
  moreover from B2 B5 B7 B8 have "weak_reduction_correspondence_simulation TRel Target"
    using rel_includes_TRel_modulo_preorder[where Rel="Rel" and TRel="TRel"]
          rel_with_target_impl_transC_TRel_is_weak_reduction_correspondence_simulation[where
            Rel="Rel" and TRel="TRel"]
    by fast
  ultimately show "weakly_operational_corresponding TRel \<and> preorder TRel
                   \<and> weak_reduction_correspondence_simulation TRel Target"
    by blast
qed

lemma (in encodingLS_encL) WOC_wrt_preorder_iff_labelled_correspondence_simulation_encL:
  fixes TRel :: "('procT \<times> 'procT) set"
  shows "(weakly_operational_corresponding_encL TRel \<and> preorder TRel
         \<and> weak_labelled_correspondence_simulation TRel Target)
         = (\<exists>Rel. (\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel)
            \<and> TRel = {(T1, T2). (TargetTerm T1, TargetTerm T2) \<in> Rel}
            \<and> (\<forall>S T. (SourceTerm S, TargetTerm T) \<in> Rel \<longrightarrow> (\<lbrakk>S\<rbrakk>, T) \<in> TRel)
            \<and> preorder Rel
            \<and> weak_labelled_correspondence_simulation_encL Rel)"
proof (rule iffI, erule conjE, erule conjE, erule conjE)
  assume A1: "operational_complete_encL TRel" and A2: "weakly_operational_sound_encL TRel"
     and A3:"preorder TRel" and A4: "weak_labelled_correspondence_simulation TRel Target"
  from A3 have A5: "TRel\<^sup>+ = TRel"
    using trancl_id[of TRel]
    unfolding preorder_on_def
    by blast
  with A3 have "TRel\<^sup>* = TRel"
    using trancl_id[of TRel] reflcl_trancl[of TRel]
    unfolding preorder_on_def refl_on_def
    by auto
  with A1 A2 have "weakly_operational_corresponding_encL (TRel\<^sup>*)"
    by simp
  moreover from A4 A5 have "weak_labelled_correspondence_simulation (TRel\<^sup>+) Target"
    by simp
  ultimately have "weak_labelled_correspondence_simulation_encL (indRelRTPO TRel)"
    using WOC_iff_indRelRTPO_is_labelled_correspondence_simulation_encL[where TRel="TRel"]
    by blast
  moreover have "\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> indRelRTPO TRel"
    by (simp add: indRelRTPO.encR)
  moreover
  have "TRel = {(T1, T2). (TargetTerm T1, TargetTerm T2) \<in> indRelRTPO TRel}"
  proof auto
    fix TP TQ
    assume "(TP, TQ) \<in> TRel"
    thus "TargetTerm TP \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> TargetTerm TQ"
      by (rule indRelRTPO.target)
  next
    fix TP TQ
    assume "TargetTerm TP \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> TargetTerm TQ"
    with A3 show "(TP, TQ) \<in> TRel"
      using indRelRTPO_to_TRel(4)[where TRel="TRel"] trancl_id[of TRel]
      unfolding preorder_on_def
      by blast
  qed
  moreover from A3
  have "\<forall>S T. (SourceTerm S, TargetTerm T) \<in> indRelRTPO TRel \<longrightarrow> (\<lbrakk>S\<rbrakk>, T) \<in> TRel\<^sup>+"
    using indRelRTPO_to_TRel(2)[where TRel="TRel"] reflcl_trancl[of TRel]
          trans_closure_of_TRel_refl_cond[where TRel="TRel"]
    unfolding preorder_on_def refl_on_def
    by blast
  with A3 have "\<forall>S T. (SourceTerm S, TargetTerm T) \<in> indRelRTPO TRel \<longrightarrow> (\<lbrakk>S\<rbrakk>, T) \<in> TRel"
    using trancl_id[of TRel]
    unfolding preorder_on_def
    by blast
  moreover from A3 have "refl (indRelRTPO TRel)"
    using indRelRTPO_refl[of TRel]
    unfolding preorder_on_def
    by simp
  moreover have "trans (indRelRTPO TRel)"
    using indRelRTPO.trans
    unfolding trans_def
    by blast
  ultimately show "\<exists>Rel. (\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel)
                   \<and> TRel = {(T1, T2). (TargetTerm T1, TargetTerm T2) \<in> Rel}
                   \<and> (\<forall>S T. (SourceTerm S, TargetTerm T) \<in> Rel \<longrightarrow> (\<lbrakk>S\<rbrakk>, T) \<in> TRel)
                   \<and> preorder Rel
                   \<and> weak_labelled_correspondence_simulation_encL Rel"
    unfolding preorder_on_def
    by auto
next
  assume "\<exists>Rel. (\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel)
          \<and> TRel = {(T1, T2). (TargetTerm T1, TargetTerm T2) \<in> Rel}
          \<and> (\<forall>S T. (SourceTerm S, TargetTerm T) \<in> Rel \<longrightarrow> (\<lbrakk>S\<rbrakk>, T) \<in> TRel)
          \<and> preorder Rel
          \<and> weak_labelled_correspondence_simulation_encL Rel"
  from this obtain Rel where B1: "\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel"
   and B2: "TRel = {(T1, T2). (TargetTerm T1, TargetTerm T2) \<in> Rel}"
   and B3: "\<forall>S T. (SourceTerm S, TargetTerm T) \<in> Rel \<longrightarrow> (\<lbrakk>S\<rbrakk>, T) \<in> TRel" and B4: "preorder Rel"
   and B5: "weak_labelled_correspondence_simulation_encL Rel"
    by blast
  from B2 B4 have B6: "refl TRel"
    unfolding preorder_on_def refl_on_def
    by blast
  from B2 B4 have B7: "trans TRel"
    unfolding trans_def preorder_on_def
    by blast
  hence B8: "TRel\<^sup>+ = TRel"
    using trancl_id[of TRel]
    by simp
  with B6 have "TRel\<^sup>* = TRel"
    using reflcl_trancl[of TRel]
    unfolding refl_on_def
    by blast
  with B1 B3 B5 have "weakly_operational_corresponding_encL TRel"
    using weak_labelled_correspondence_simulation_impl_WOC_encL[where Rel="Rel" and TRel="TRel"]
    by simp
  moreover from B6 B7 have "preorder TRel"
    unfolding preorder_on_def by simp
  moreover from B2 B5 B7 B8 have "weak_labelled_correspondence_simulation TRel Target"
    using rel_includes_TRel_modulo_preorder[where Rel="Rel" and TRel="TRel"]
          rel_with_target_impl_transC_TRel_is_weak_labelled_correspondence_simulation_encL[where
            Rel="Rel" and TRel="TRel"]
    by fast
  ultimately show "weakly_operational_corresponding_encL TRel \<and> preorder TRel
                   \<and> weak_labelled_correspondence_simulation TRel Target"
    by blast
qed

subsection \<open>(Strong) Operational Correspondence vs (Strong) Bisimilarity\<close>

text \<open>An encoding is operational corresponding w.r.t a weak bisimulation on target terms TRel iff
      there exists a relation, like indRelRTPO, that relates at least all source terms and their
      literal translations, includes TRel, and is a weak bisimulation. Thus this variant of
      operational correspondence ensures that source terms and their translations are weak
      bisimilar.\<close>

lemma (in encoding) OC_iff_indRelRTPO_is_weak_reduction_bisimulation:
  fixes TRel :: "('procT \<times> 'procT) set"
  shows "(operational_corresponding (TRel\<^sup>*)
         \<and> weak_reduction_bisimulation (TRel\<^sup>+) Target)
         = weak_reduction_bisimulation (indRelRTPO TRel) (STCal Source Target)"
proof (rule iffI, erule conjE)
  assume ocorr: "operational_corresponding (TRel\<^sup>*)"
     and bisim: "weak_reduction_bisimulation (TRel\<^sup>+) Target"
  hence "weak_reduction_simulation (indRelRTPO TRel) (STCal Source Target)"
    using OCom_iff_indRelRTPO_is_weak_reduction_simulation[where TRel="TRel"]
    by simp
  moreover from bisim have "weak_reduction_simulation ((TRel\<^sup>+)\<inverse>) Target"
    using weak_reduction_bisimulations_impl_inverse_is_simulation[where Rel="TRel\<^sup>+"]
    by simp
  with ocorr have "weak_reduction_simulation ((indRelRTPO TRel)\<inverse>) (STCal Source Target)"
    using OSou_iff_inverse_of_indRelRTPO_is_weak_reduction_simulation[where TRel="TRel"]
    by simp
  ultimately show "weak_reduction_bisimulation (indRelRTPO TRel) (STCal Source Target)"
    using weak_reduction_simulations_impl_bisimulation[where Rel="indRelRTPO TRel"]
    by simp
next
  assume bisim: "weak_reduction_bisimulation (indRelRTPO TRel) (STCal Source Target)"
  hence "operational_complete (TRel\<^sup>*) \<and> weak_reduction_simulation (TRel\<^sup>+) Target"
    using OCom_iff_indRelRTPO_is_weak_reduction_simulation[where TRel="TRel"]
    by simp
  moreover from bisim
  have "weak_reduction_simulation ((indRelRTPO TRel)\<inverse>) (STCal Source Target)"
    using weak_reduction_bisimulations_impl_inverse_is_simulation[where Rel="indRelRTPO TRel"]
    by simp
  hence "operational_sound (TRel\<^sup>*) \<and> weak_reduction_simulation ((TRel\<^sup>+)\<inverse>) Target"
    using OSou_iff_inverse_of_indRelRTPO_is_weak_reduction_simulation[where TRel="TRel"]
    by simp
  ultimately show "operational_corresponding (TRel\<^sup>*) \<and> weak_reduction_bisimulation (TRel\<^sup>+) Target"
    using weak_reduction_simulations_impl_bisimulation[where Rel="TRel\<^sup>+"]
    by simp
qed

lemma (in encodingLS_encL) OC_iff_indRelRTPO_is_weak_labelled_bisimulation_encL:
  fixes TRel :: "('procT \<times> 'procT) set"
  shows "(operational_corresponding_encL (TRel\<^sup>*)
         \<and> weak_labelled_bisimulation (TRel\<^sup>+) Target)
         = weak_labelled_bisimulation_encL (indRelRTPO TRel)"
proof (rule iffI, erule conjE)
  assume ocorr: "operational_corresponding_encL (TRel\<^sup>*)"
     and bisim: "weak_labelled_bisimulation (TRel\<^sup>+) Target"
  hence "weak_labelled_simulation_encL (indRelRTPO TRel)"
    using OCom_iff_indRelRTPO_is_weak_labelled_simulation_encL[where TRel="TRel"]
    by simp
  moreover from bisim have "weak_labelled_simulation ((TRel\<^sup>+)\<inverse>) Target"
    using weak_labelled_bisimulations_impl_inverse_is_simulation[where Rel="TRel\<^sup>+"]
    by simp
  with ocorr have "weak_labelled_simulation_encL ((indRelRTPO TRel)\<inverse>)"
    using OSou_iff_inverse_of_indRelRTPO_is_weak_labelled_simulation_encL[where TRel="TRel"]
    by simp
  ultimately show "weak_labelled_bisimulation_encL (indRelRTPO TRel)"
    using weak_labelled_simulations_encL_impl_bisimulation[where Rel="indRelRTPO TRel"]
    by simp
next
  assume bisim: "weak_labelled_bisimulation_encL (indRelRTPO TRel)"
  hence "operational_complete_encL (TRel\<^sup>*) \<and> weak_labelled_simulation (TRel\<^sup>+) Target"
    using OCom_iff_indRelRTPO_is_weak_labelled_simulation_encL[where TRel="TRel"]
    by simp
  moreover from bisim
  have "weak_labelled_simulation_encL ((indRelRTPO TRel)\<inverse>)"
    using weak_labelled_bisimulations_encL_impl_inverse_is_simulation[where Rel="indRelRTPO TRel"]
    by simp
  hence "operational_sound_encL (TRel\<^sup>*) \<and> weak_labelled_simulation ((TRel\<^sup>+)\<inverse>) Target"
    using OSou_iff_inverse_of_indRelRTPO_is_weak_labelled_simulation_encL[where TRel="TRel"]
    by simp
  ultimately
  show "operational_corresponding_encL (TRel\<^sup>*) \<and> weak_labelled_bisimulation (TRel\<^sup>+) Target"
    by simp
qed

lemma (in encoding) OC_iff_weak_reduction_bisimulation:
  fixes TRel :: "('procT \<times> 'procT) set"
  shows "(operational_corresponding (TRel\<^sup>*) \<and> weak_reduction_bisimulation (TRel\<^sup>+) Target)
         = (\<exists>Rel. (\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel)
            \<and> (\<forall>T1 T2. (T1, T2) \<in> TRel \<longrightarrow> (TargetTerm T1, TargetTerm T2) \<in> Rel)
            \<and> (\<forall>T1 T2. (TargetTerm T1, TargetTerm T2) \<in> Rel \<longrightarrow> (T1, T2) \<in> TRel\<^sup>+)
            \<and> (\<forall>S T. (SourceTerm S, TargetTerm T) \<in> Rel \<longrightarrow> (\<lbrakk>S\<rbrakk>, T) \<in> TRel\<^sup>*)
            \<and> weak_reduction_bisimulation Rel (STCal Source Target))"
proof (rule iffI, erule conjE)
  have "\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> indRelRTPO TRel"
    by (simp add: indRelRTPO.encR)
  moreover have "\<forall>T1 T2. (T1, T2) \<in> TRel \<longrightarrow> TargetTerm T1 \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> TargetTerm T2"
    by (simp add: indRelRTPO.target)
  moreover have "\<forall>T1 T2. TargetTerm T1 \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> TargetTerm T2 \<longrightarrow> (T1, T2) \<in> TRel\<^sup>+"
    using indRelRTPO_to_TRel(4)[where TRel="TRel"]
    by simp
  moreover have "\<forall>S T. SourceTerm S \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> TargetTerm T \<longrightarrow> (\<lbrakk>S\<rbrakk>, T) \<in> TRel\<^sup>*"
    using indRelRTPO_to_TRel(2)[where TRel="TRel"] trans_closure_of_TRel_refl_cond
    by simp
  moreover assume "operational_corresponding (TRel\<^sup>*)"
              and "weak_reduction_bisimulation (TRel\<^sup>+) Target"
  hence "weak_reduction_bisimulation (indRelRTPO TRel) (STCal Source Target)"
    using OC_iff_indRelRTPO_is_weak_reduction_bisimulation[where TRel="TRel"]
    by simp
  ultimately show "\<exists>Rel. (\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel)
                   \<and> (\<forall>T1 T2. (T1, T2) \<in> TRel \<longrightarrow> (TargetTerm T1, TargetTerm T2) \<in> Rel)
                   \<and> (\<forall>T1 T2. (TargetTerm T1, TargetTerm T2) \<in> Rel \<longrightarrow> (T1, T2) \<in> TRel\<^sup>+)
                   \<and> (\<forall>S T. (SourceTerm S, TargetTerm T) \<in> Rel \<longrightarrow> (\<lbrakk>S\<rbrakk>, T) \<in> TRel\<^sup>*)
                   \<and> weak_reduction_bisimulation Rel (STCal Source Target)"
    by blast
next
  assume "\<exists>Rel. (\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel)
          \<and> (\<forall>T1 T2. (T1, T2) \<in> TRel \<longrightarrow> (TargetTerm T1, TargetTerm T2) \<in> Rel)
          \<and> (\<forall>T1 T2. (TargetTerm T1, TargetTerm T2) \<in> Rel \<longrightarrow> (T1, T2) \<in> TRel\<^sup>+)
          \<and> (\<forall>S T. (SourceTerm S, TargetTerm T) \<in> Rel \<longrightarrow> (\<lbrakk>S\<rbrakk>, T) \<in> TRel\<^sup>*)
          \<and> weak_reduction_bisimulation Rel (STCal Source Target)"
  from this obtain Rel where A1: "\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel"
   and A2: "\<forall>T1 T2. (T1, T2) \<in> TRel \<longrightarrow> (TargetTerm T1, TargetTerm T2) \<in> Rel"
   and A3: "\<forall>T1 T2. (TargetTerm T1, TargetTerm T2) \<in> Rel \<longrightarrow> (T1, T2) \<in> TRel\<^sup>+"
   and A4: "\<forall>S T. (SourceTerm S, TargetTerm T) \<in> Rel \<longrightarrow> (\<lbrakk>S\<rbrakk>, T) \<in> TRel\<^sup>*"
   and A5: "weak_reduction_bisimulation Rel (STCal Source Target)"
    by blast
  hence "operational_complete (TRel\<^sup>*)
         \<and> weak_reduction_simulation (TRel\<^sup>+) Target"
    using OCom_iff_weak_reduction_simulation[where TRel="TRel"]
    by blast
  moreover from A5 have "weak_reduction_simulation (Rel\<inverse>) (STCal Source Target)"
    using weak_reduction_bisimulations_impl_inverse_is_simulation[where Rel="Rel"]
    by simp
  with A1 A2 A3 A4 have "operational_sound (TRel\<^sup>*)
                         \<and> weak_reduction_simulation ((TRel\<^sup>+)\<inverse>) Target"
    using OSou_iff_weak_reduction_simulation[where TRel="TRel"]
    by blast
  ultimately show "operational_corresponding (TRel\<^sup>*)
                   \<and> weak_reduction_bisimulation (TRel\<^sup>+) Target"
    using weak_reduction_simulations_impl_bisimulation[where Rel="TRel\<^sup>+"]
    by simp
qed

lemma (in encodingLS_encL) OC_iff_weak_labelled_bisimulation_encL:
  fixes TRel :: "('procT \<times> 'procT) set"
  shows "(operational_corresponding_encL (TRel\<^sup>*) \<and> weak_labelled_bisimulation (TRel\<^sup>+) Target)
         = (\<exists>Rel. (\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel)
            \<and> (\<forall>T1 T2. (T1, T2) \<in> TRel \<longrightarrow> (TargetTerm T1, TargetTerm T2) \<in> Rel)
            \<and> (\<forall>T1 T2. (TargetTerm T1, TargetTerm T2) \<in> Rel \<longrightarrow> (T1, T2) \<in> TRel\<^sup>+)
            \<and> (\<forall>S T. (SourceTerm S, TargetTerm T) \<in> Rel \<longrightarrow> (\<lbrakk>S\<rbrakk>, T) \<in> TRel\<^sup>*)
            \<and> weak_labelled_bisimulation_encL Rel)"
proof (rule iffI, erule conjE)
  have "\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> indRelRTPO TRel"
    by (simp add: indRelRTPO.encR)
  moreover have "\<forall>T1 T2. (T1, T2) \<in> TRel \<longrightarrow> TargetTerm T1 \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> TargetTerm T2"
    by (simp add: indRelRTPO.target)
  moreover have "\<forall>T1 T2. TargetTerm T1 \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> TargetTerm T2 \<longrightarrow> (T1, T2) \<in> TRel\<^sup>+"
    using indRelRTPO_to_TRel(4)[where TRel="TRel"]
    by simp
  moreover have "\<forall>S T. SourceTerm S \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> TargetTerm T \<longrightarrow> (\<lbrakk>S\<rbrakk>, T) \<in> TRel\<^sup>*"
    using indRelRTPO_to_TRel(2)[where TRel="TRel"] trans_closure_of_TRel_refl_cond
    by simp
  moreover assume "operational_corresponding_encL (TRel\<^sup>*)"
              and "weak_labelled_bisimulation (TRel\<^sup>+) Target"
  hence "weak_labelled_bisimulation_encL (indRelRTPO TRel)"
    using OC_iff_indRelRTPO_is_weak_labelled_bisimulation_encL[where TRel="TRel"]
    by simp
  ultimately show "\<exists>Rel. (\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel)
                   \<and> (\<forall>T1 T2. (T1, T2) \<in> TRel \<longrightarrow> (TargetTerm T1, TargetTerm T2) \<in> Rel)
                   \<and> (\<forall>T1 T2. (TargetTerm T1, TargetTerm T2) \<in> Rel \<longrightarrow> (T1, T2) \<in> TRel\<^sup>+)
                   \<and> (\<forall>S T. (SourceTerm S, TargetTerm T) \<in> Rel \<longrightarrow> (\<lbrakk>S\<rbrakk>, T) \<in> TRel\<^sup>*)
                   \<and> weak_labelled_bisimulation_encL Rel"
    by blast
next
  assume "\<exists>Rel. (\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel)
          \<and> (\<forall>T1 T2. (T1, T2) \<in> TRel \<longrightarrow> (TargetTerm T1, TargetTerm T2) \<in> Rel)
          \<and> (\<forall>T1 T2. (TargetTerm T1, TargetTerm T2) \<in> Rel \<longrightarrow> (T1, T2) \<in> TRel\<^sup>+)
          \<and> (\<forall>S T. (SourceTerm S, TargetTerm T) \<in> Rel \<longrightarrow> (\<lbrakk>S\<rbrakk>, T) \<in> TRel\<^sup>*)
          \<and> weak_labelled_bisimulation_encL Rel"
  from this obtain Rel where A1: "\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel"
   and A2: "\<forall>T1 T2. (T1, T2) \<in> TRel \<longrightarrow> (TargetTerm T1, TargetTerm T2) \<in> Rel"
   and A3: "\<forall>T1 T2. (TargetTerm T1, TargetTerm T2) \<in> Rel \<longrightarrow> (T1, T2) \<in> TRel\<^sup>+"
   and A4: "\<forall>S T. (SourceTerm S, TargetTerm T) \<in> Rel \<longrightarrow> (\<lbrakk>S\<rbrakk>, T) \<in> TRel\<^sup>*"
   and A5: "weak_labelled_bisimulation_encL Rel"
    by blast
  hence "operational_complete_encL (TRel\<^sup>*)
         \<and> weak_labelled_simulation (TRel\<^sup>+) Target"
    using OCom_iff_weak_labelled_simulation_encL[where TRel="TRel"]
    by blast
  moreover from A5 have "weak_labelled_simulation_encL (Rel\<inverse>)"
    using weak_labelled_bisimulations_encL_impl_inverse_is_simulation[where Rel="Rel"]
    by simp
  with A1 A2 A3 A4 have "operational_sound_encL (TRel\<^sup>*)
                         \<and> weak_labelled_simulation ((TRel\<^sup>+)\<inverse>) Target"
    using OSou_iff_weak_labelled_simulation_encL[where TRel="TRel"]
    by blast
  ultimately show "operational_corresponding_encL (TRel\<^sup>*)
                   \<and> weak_labelled_bisimulation (TRel\<^sup>+) Target"
    by simp
qed

lemma (in encoding) OC_wrt_preorder_iff_weak_reduction_bisimulation:
  fixes TRel :: "('procT \<times> 'procT) set"
  shows "(operational_corresponding TRel \<and> preorder TRel
         \<and> weak_reduction_bisimulation TRel Target)
         = (\<exists>Rel. (\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel)
            \<and> TRel = {(T1, T2). (TargetTerm T1, TargetTerm T2) \<in> Rel}
            \<and> (\<forall>S T. (SourceTerm S, TargetTerm T) \<in> Rel \<longrightarrow> (\<lbrakk>S\<rbrakk>, T) \<in> TRel)
            \<and> preorder Rel
            \<and> weak_reduction_bisimulation Rel (STCal Source Target))"
proof (rule iffI, erule conjE, erule conjE, erule conjE)
  assume A1: "operational_complete TRel" and A2: "operational_sound TRel"
     and A3:"preorder TRel" and A4: "weak_reduction_bisimulation TRel Target"
  from A3 have A5: "TRel\<^sup>+ = TRel"
    using trancl_id[of TRel]
    unfolding preorder_on_def
    by blast
  with A3 have "TRel\<^sup>* = TRel"
    using reflcl_trancl[of TRel]
    unfolding preorder_on_def refl_on_def
    by blast
  with A1 A2 have "operational_corresponding (TRel\<^sup>*)"
    by simp
  moreover from A4 A5 have "weak_reduction_bisimulation (TRel\<^sup>+) Target"
    by simp
  ultimately
  have "weak_reduction_bisimulation (indRelRTPO TRel) (STCal Source Target)"
    using OC_iff_indRelRTPO_is_weak_reduction_bisimulation[where TRel="TRel"]
    by blast
  moreover have "\<forall>S. SourceTerm S \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> TargetTerm (\<lbrakk>S\<rbrakk>)"
    by (simp add: indRelRTPO.encR)
  moreover
  have "TRel = {(T1, T2). TargetTerm T1 \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> TargetTerm T2}"
  proof auto
    fix TP TQ
    assume "(TP, TQ) \<in> TRel"
    thus "TargetTerm TP \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> TargetTerm TQ"
      by (rule indRelRTPO.target)
  next
    fix TP TQ
    assume "TargetTerm TP \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> TargetTerm TQ"
    with A3 show "(TP, TQ) \<in> TRel"
      using indRelRTPO_to_TRel(4)[where TRel="TRel"] trancl_id[of TRel]
      unfolding preorder_on_def
      by blast
  qed
  moreover from A3
  have "\<forall>S T. SourceTerm S \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> TargetTerm T \<longrightarrow> (\<lbrakk>S\<rbrakk>, T) \<in> TRel\<^sup>+"
    using indRelRTPO_to_TRel(2)[where TRel="TRel"] reflcl_trancl[of TRel]
          trans_closure_of_TRel_refl_cond[where TRel="TRel"]
    unfolding preorder_on_def refl_on_def
    by auto
  with A3 have "\<forall>S T. SourceTerm S \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> TargetTerm T \<longrightarrow> (\<lbrakk>S\<rbrakk>, T) \<in> TRel"
    using trancl_id[of TRel]
    unfolding preorder_on_def
    by blast
  moreover from A3 have "refl (indRelRTPO TRel)"
    unfolding preorder_on_def
    by (simp add: indRelRTPO_refl)
  moreover have "trans (indRelRTPO TRel)"
    using indRelRTPO.trans
    unfolding trans_def
    by blast
  ultimately show "\<exists>Rel. (\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel)
                   \<and> TRel = {(T1, T2). (TargetTerm T1, TargetTerm T2) \<in> Rel}
                   \<and> (\<forall>S T. (SourceTerm S, TargetTerm T) \<in> Rel \<longrightarrow> (\<lbrakk>S\<rbrakk>, T) \<in> TRel)
                   \<and> preorder Rel
                   \<and> weak_reduction_bisimulation Rel (STCal Source Target)"
      unfolding preorder_on_def by auto
next
  assume "\<exists>Rel. (\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel)
          \<and> TRel = {(T1, T2). (TargetTerm T1, TargetTerm T2) \<in> Rel}
          \<and> (\<forall>S T. (SourceTerm S, TargetTerm T) \<in> Rel \<longrightarrow> (\<lbrakk>S\<rbrakk>, T) \<in> TRel)
          \<and> preorder Rel
          \<and> weak_reduction_bisimulation Rel (STCal Source Target)"
  from this obtain Rel where B1: "\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel"
   and B2: "TRel = {(T1, T2). (TargetTerm T1, TargetTerm T2) \<in> Rel}"
   and B3: "\<forall>S T. (SourceTerm S, TargetTerm T) \<in> Rel \<longrightarrow> (\<lbrakk>S\<rbrakk>, T) \<in> TRel" and B4: "preorder Rel"
   and B5: "weak_reduction_bisimulation Rel (STCal Source Target)"
    by blast
  from B2 B4 have B6: "refl TRel"
    unfolding preorder_on_def refl_on_def
    by blast
  from B2 B4 have B7: "trans TRel"
    unfolding trans_def preorder_on_def
    by blast
  hence B8: "TRel\<^sup>+ = TRel"
    using trancl_id[of TRel]
    by simp
  with B6 have B9: "TRel\<^sup>* = TRel"
    using reflcl_trancl[of TRel]
    unfolding refl_on_def
    by blast
  with B3 have "\<forall>S T. (SourceTerm S, TargetTerm T) \<in> Rel \<longrightarrow> (\<lbrakk>S\<rbrakk>, T) \<in> TRel\<^sup>*"
    by simp
  moreover from B2 B8 have "\<forall>T1 T2. (T1, T2) \<in> TRel \<longrightarrow> (TargetTerm T1, TargetTerm T2) \<in> Rel"
    and "\<forall>T1 T2. (TargetTerm T1, TargetTerm T2) \<in> Rel \<longrightarrow> (T1, T2) \<in> TRel\<^sup>+"
    by auto
  ultimately have "\<exists>Rel. (\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel)
   \<and> (\<forall>T1 T2. (T1, T2) \<in> TRel \<longrightarrow> (TargetTerm T1, TargetTerm T2) \<in> Rel)
   \<and> (\<forall>T1 T2. (TargetTerm T1, TargetTerm T2) \<in> Rel \<longrightarrow> (T1, T2) \<in> TRel\<^sup>+)
   \<and> (\<forall>S T. (SourceTerm S, TargetTerm T) \<in> Rel \<longrightarrow> (\<lbrakk>S\<rbrakk>, T) \<in> TRel\<^sup>*)
   \<and> weak_reduction_bisimulation Rel (STCal Source Target)"
    using B1 B5
    by blast
  hence "operational_corresponding (TRel\<^sup>*)
         \<and> weak_reduction_bisimulation (TRel\<^sup>+) Target"
    using OC_iff_weak_reduction_bisimulation[where TRel="TRel"]
    by simp
  with B8 B9 have "operational_corresponding TRel \<and> weak_reduction_bisimulation TRel Target"
    by simp
  moreover from B6 B7 have "preorder TRel"
    unfolding preorder_on_def by simp
  ultimately show "operational_corresponding TRel \<and> preorder TRel
                   \<and> weak_reduction_bisimulation TRel Target"
    by blast
qed

lemma (in encodingLS_encL) OC_wrt_preorder_iff_weak_labelled_bisimulation_encL:
  fixes TRel :: "('procT \<times> 'procT) set"
  shows "(operational_corresponding_encL TRel \<and> preorder TRel
         \<and> weak_labelled_bisimulation TRel Target)
         = (\<exists>Rel. (\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel)
            \<and> TRel = {(T1, T2). (TargetTerm T1, TargetTerm T2) \<in> Rel}
            \<and> (\<forall>S T. (SourceTerm S, TargetTerm T) \<in> Rel \<longrightarrow> (\<lbrakk>S\<rbrakk>, T) \<in> TRel)
            \<and> preorder Rel
            \<and> weak_labelled_bisimulation_encL Rel)"
proof (rule iffI, erule conjE, erule conjE, erule conjE)
  assume A1: "operational_complete_encL TRel" and A2: "operational_sound_encL TRel"
     and A3:"preorder TRel" and A4: "weak_labelled_bisimulation TRel Target"
  from A3 have A5: "TRel\<^sup>+ = TRel"
    using trancl_id[of TRel]
    unfolding preorder_on_def
    by blast
  with A3 have "TRel\<^sup>* = TRel"
    using reflcl_trancl[of TRel]
    unfolding preorder_on_def refl_on_def
    by blast
  with A1 A2 have "operational_corresponding_encL (TRel\<^sup>*)"
    by simp
  moreover from A4 A5 have "weak_labelled_bisimulation (TRel\<^sup>+) Target"
    by simp
  ultimately have "weak_labelled_bisimulation_encL (indRelRTPO TRel)"
    using OC_iff_indRelRTPO_is_weak_labelled_bisimulation_encL[where TRel="TRel"]
    by blast
  moreover have "\<forall>S. SourceTerm S \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> TargetTerm (\<lbrakk>S\<rbrakk>)"
    by (simp add: indRelRTPO.encR)
  moreover have "TRel = {(T1, T2). TargetTerm T1 \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> TargetTerm T2}"
  proof auto
    fix TP TQ
    assume "(TP, TQ) \<in> TRel"
    thus "TargetTerm TP \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> TargetTerm TQ"
      by (rule indRelRTPO.target)
  next
    fix TP TQ
    assume "TargetTerm TP \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> TargetTerm TQ"
    with A3 show "(TP, TQ) \<in> TRel"
      using indRelRTPO_to_TRel(4)[where TRel="TRel"] trancl_id[of TRel]
      unfolding preorder_on_def
      by blast
  qed
  moreover from A3
  have "\<forall>S T. SourceTerm S \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> TargetTerm T \<longrightarrow> (\<lbrakk>S\<rbrakk>, T) \<in> TRel\<^sup>+"
    using indRelRTPO_to_TRel(2)[where TRel="TRel"] reflcl_trancl[of TRel]
          trans_closure_of_TRel_refl_cond[where TRel="TRel"]
    unfolding preorder_on_def refl_on_def
    by auto
  with A3 have "\<forall>S T. SourceTerm S \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> TargetTerm T \<longrightarrow> (\<lbrakk>S\<rbrakk>, T) \<in> TRel"
    using trancl_id[of TRel]
    unfolding preorder_on_def
    by blast
  moreover from A3 have "refl (indRelRTPO TRel)"
    unfolding preorder_on_def
    by (simp add: indRelRTPO_refl)
  moreover have "trans (indRelRTPO TRel)"
    using indRelRTPO.trans
    unfolding trans_def
    by blast
  ultimately show "\<exists>Rel. (\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel)
                   \<and> TRel = {(T1, T2). (TargetTerm T1, TargetTerm T2) \<in> Rel}
                   \<and> (\<forall>S T. (SourceTerm S, TargetTerm T) \<in> Rel \<longrightarrow> (\<lbrakk>S\<rbrakk>, T) \<in> TRel)
                   \<and> preorder Rel
                   \<and> weak_labelled_bisimulation_encL Rel"
    unfolding preorder_on_def
    by auto
next
  assume "\<exists>Rel. (\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel)
          \<and> TRel = {(T1, T2). (TargetTerm T1, TargetTerm T2) \<in> Rel}
          \<and> (\<forall>S T. (SourceTerm S, TargetTerm T) \<in> Rel \<longrightarrow> (\<lbrakk>S\<rbrakk>, T) \<in> TRel)
          \<and> preorder Rel
          \<and> weak_labelled_bisimulation_encL Rel"
  from this obtain Rel where B1: "\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel"
   and B2: "TRel = {(T1, T2). (TargetTerm T1, TargetTerm T2) \<in> Rel}"
   and B3: "\<forall>S T. (SourceTerm S, TargetTerm T) \<in> Rel \<longrightarrow> (\<lbrakk>S\<rbrakk>, T) \<in> TRel" and B4: "preorder Rel"
   and B5: "weak_labelled_bisimulation_encL Rel"
    by blast
  from B2 B4 have B6: "refl TRel"
    unfolding preorder_on_def refl_on_def
    by blast
  from B2 B4 have B7: "trans TRel"
    unfolding trans_def preorder_on_def
    by blast
  hence B8: "TRel\<^sup>+ = TRel"
    using trancl_id[of TRel]
    by simp
  with B6 have B9: "TRel\<^sup>* = TRel"
    using reflcl_trancl[of TRel]
    unfolding refl_on_def
    by blast
  with B3 have "\<forall>S T. (SourceTerm S, TargetTerm T) \<in> Rel \<longrightarrow> (\<lbrakk>S\<rbrakk>, T) \<in> TRel\<^sup>*"
    by simp
  moreover from B2 B8 have "\<forall>T1 T2. (T1, T2) \<in> TRel \<longrightarrow> (TargetTerm T1, TargetTerm T2) \<in> Rel"
    and "\<forall>T1 T2. (TargetTerm T1, TargetTerm T2) \<in> Rel \<longrightarrow> (T1, T2) \<in> TRel\<^sup>+"
    by auto
  ultimately have "\<exists>Rel. (\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel)
   \<and> (\<forall>T1 T2. (T1, T2) \<in> TRel \<longrightarrow> (TargetTerm T1, TargetTerm T2) \<in> Rel)
   \<and> (\<forall>T1 T2. (TargetTerm T1, TargetTerm T2) \<in> Rel \<longrightarrow> (T1, T2) \<in> TRel\<^sup>+)
   \<and> (\<forall>S T. (SourceTerm S, TargetTerm T) \<in> Rel \<longrightarrow> (\<lbrakk>S\<rbrakk>, T) \<in> TRel\<^sup>*)
   \<and> weak_labelled_bisimulation_encL Rel"
    using B1 B5
    by blast
  hence "operational_corresponding_encL (TRel\<^sup>*)
         \<and> weak_labelled_bisimulation (TRel\<^sup>+) Target"
    using OC_iff_weak_labelled_bisimulation_encL[where TRel="TRel"]
    by simp
  with B8 B9 have "operational_corresponding_encL TRel \<and> weak_labelled_bisimulation TRel Target"
    by simp
  moreover from B6 B7 have "preorder TRel"
    unfolding preorder_on_def
    by simp
  ultimately show "operational_corresponding_encL TRel \<and> preorder TRel
                   \<and> weak_labelled_bisimulation TRel Target"
    by blast
qed

lemma (in encoding) OC_wrt_equivalence_iff_indRelTEQ_weak_reduction_bisimulation:
  fixes TRel :: "('procT \<times> 'procT) set"
  assumes eqT: "equivalence TRel"
  shows "(operational_corresponding TRel \<and> weak_reduction_bisimulation TRel Target) \<longleftrightarrow>
         weak_reduction_bisimulation (indRelTEQ TRel) (STCal Source Target)"
proof (rule iffI, erule conjE)
  assume oc: "operational_corresponding TRel" and bisimT: "weak_reduction_bisimulation TRel Target"
  show "weak_reduction_bisimulation (indRelTEQ TRel) (STCal Source Target)"
  proof auto
    fix P Q P'
    assume "P \<sim>\<lbrakk>\<cdot>\<rbrakk>T<TRel> Q" and "P \<longmapsto>(STCal Source Target)* P'"
    thus "\<exists>Q'. Q \<longmapsto>(STCal Source Target)* Q' \<and> P' \<sim>\<lbrakk>\<cdot>\<rbrakk>T<TRel> Q'"
    proof (induct arbitrary: P')
      case (encR S)
      assume "SourceTerm S \<longmapsto>(STCal Source Target)* P'"
      from this obtain S' where A1: "S \<longmapsto>Source* S'" and A2: "S' \<in>S P'"
        by (auto simp add: STCal_steps(1))
      from A1 oc obtain T where A3: "\<lbrakk>S\<rbrakk> \<longmapsto>Target* T" and A4: "(\<lbrakk>S'\<rbrakk>, T) \<in> TRel"
        by blast
      from A3 have "TargetTerm (\<lbrakk>S\<rbrakk>) \<longmapsto>(STCal Source Target)* (TargetTerm T)"
        by (simp add: STCal_steps(2))
      moreover have "P' \<sim>\<lbrakk>\<cdot>\<rbrakk>T<TRel> TargetTerm T"
      proof -
        from A2 have "P' \<sim>\<lbrakk>\<cdot>\<rbrakk>T<TRel> TargetTerm (\<lbrakk>S'\<rbrakk>)"
          by (simp add: indRelTEQ.encR)
        moreover from A4 have "TargetTerm (\<lbrakk>S'\<rbrakk>) \<sim>\<lbrakk>\<cdot>\<rbrakk>T<TRel> TargetTerm T"
          by (rule indRelTEQ.target)
        ultimately show "P' \<sim>\<lbrakk>\<cdot>\<rbrakk>T<TRel> TargetTerm T"
          by (rule indRelTEQ.trans)
      qed
      ultimately show "\<exists>Q'. TargetTerm (\<lbrakk>S\<rbrakk>) \<longmapsto>(STCal Source Target)* Q' \<and> P' \<sim>\<lbrakk>\<cdot>\<rbrakk>T<TRel> Q'"
        by blast
    next
      case (encL S)
      assume "TargetTerm (\<lbrakk>S\<rbrakk>) \<longmapsto>(STCal Source Target)* P'"
      from this obtain T where B1: "\<lbrakk>S\<rbrakk> \<longmapsto>Target* T" and B2: "T \<in>T P'"
        by (auto simp add: STCal_steps(2))
      from B1 oc obtain S' where B3: "S \<longmapsto>Source* S'" and B4: "(\<lbrakk>S'\<rbrakk>, T) \<in> TRel"
        by blast
      from B3 have "SourceTerm S \<longmapsto>(STCal Source Target)* (SourceTerm S')"
        by (simp add: STCal_steps(1))
      moreover have "P' \<sim>\<lbrakk>\<cdot>\<rbrakk>T<TRel> SourceTerm S'"
      proof -
        from B4 eqT have "(T, \<lbrakk>S'\<rbrakk>) \<in> TRel"
          unfolding equiv_def sym_def
          by blast
        with B2 have "P' \<sim>\<lbrakk>\<cdot>\<rbrakk>T<TRel> TargetTerm (\<lbrakk>S'\<rbrakk>)"
          by (simp add: indRelTEQ.target)
        moreover have "TargetTerm (\<lbrakk>S'\<rbrakk>) \<sim>\<lbrakk>\<cdot>\<rbrakk>T<TRel> SourceTerm S'"
          by (rule indRelTEQ.encL)
        ultimately show "P' \<sim>\<lbrakk>\<cdot>\<rbrakk>T<TRel> SourceTerm S'"
          by (rule indRelTEQ.trans)
      qed
      ultimately show "\<exists>Q'. SourceTerm S \<longmapsto>(STCal Source Target)* Q' \<and> P' \<sim>\<lbrakk>\<cdot>\<rbrakk>T<TRel> Q'"
        by blast
    next
      case (target T1 T2)
      assume "TargetTerm T1 \<longmapsto>(STCal Source Target)* P'"
      from this obtain T1' where C1: "T1 \<longmapsto>Target* T1'" and C2: "T1' \<in>T P'"
        by (auto simp add: STCal_steps(2))
      assume "(T1, T2) \<in> TRel"
      with C1 bisimT obtain T2' where C3: "T2 \<longmapsto>Target* T2'" and C4: "(T1', T2') \<in> TRel"
        by blast
      from C3 have "TargetTerm T2 \<longmapsto>(STCal Source Target)* (TargetTerm T2')"
        by (simp add: STCal_steps(2))
      moreover from C2 C4 have "P' \<sim>\<lbrakk>\<cdot>\<rbrakk>T<TRel> TargetTerm T2'"
        by (simp add: indRelTEQ.target)
      ultimately show "\<exists>Q'. TargetTerm T2 \<longmapsto>(STCal Source Target)* Q' \<and> P' \<sim>\<lbrakk>\<cdot>\<rbrakk>T<TRel> Q'"
        by blast
    next
      case (trans P Q R)
      assume "P \<longmapsto>(STCal Source Target)* P'"
         and "\<And>P'. P \<longmapsto>(STCal Source Target)* P'
              \<Longrightarrow> \<exists>Q'. Q \<longmapsto>(STCal Source Target)* Q' \<and> P' \<sim>\<lbrakk>\<cdot>\<rbrakk>T<TRel> Q'"
      from this obtain Q' where D1: "Q \<longmapsto>(STCal Source Target)* Q'" and D2: "P' \<sim>\<lbrakk>\<cdot>\<rbrakk>T<TRel> Q'"
        by blast
      assume "\<And>Q'. Q \<longmapsto>(STCal Source Target)* Q'
              \<Longrightarrow> \<exists>R'. R \<longmapsto>(STCal Source Target)* R' \<and> Q' \<sim>\<lbrakk>\<cdot>\<rbrakk>T<TRel> R'"
      with D1 obtain R' where D3: "R \<longmapsto>(STCal Source Target)* R'" and D4: "Q' \<sim>\<lbrakk>\<cdot>\<rbrakk>T<TRel> R'"
        by blast
      from D2 D4 have "P' \<sim>\<lbrakk>\<cdot>\<rbrakk>T<TRel> R'"
        by (rule indRelTEQ.trans)
      with D3 show "\<exists>R'. R \<longmapsto>(STCal Source Target)* R' \<and> P' \<sim>\<lbrakk>\<cdot>\<rbrakk>T<TRel> R'"
        by blast
    qed
  next
    fix P Q Q'
    assume "P \<sim>\<lbrakk>\<cdot>\<rbrakk>T<TRel> Q" and "Q \<longmapsto>(STCal Source Target)* Q'"
    thus "\<exists>P'. P \<longmapsto>(STCal Source Target)* P' \<and> P' \<sim>\<lbrakk>\<cdot>\<rbrakk>T<TRel> Q'"
    proof (induct arbitrary: Q')
      case (encR S)
      assume "TargetTerm (\<lbrakk>S\<rbrakk>) \<longmapsto>(STCal Source Target)* Q'"
      from this obtain T where E1: "\<lbrakk>S\<rbrakk> \<longmapsto>Target* T" and E2: "T \<in>T Q'"
        by (auto simp add: STCal_steps(2))
      from E1 oc obtain S' where E3: "S \<longmapsto>Source* S'" and E4: "(\<lbrakk>S'\<rbrakk>, T) \<in> TRel"
        by blast
      from E3 have "SourceTerm S \<longmapsto>(STCal Source Target)* (SourceTerm S')"
        by (simp add: STCal_steps(1))
      moreover have "SourceTerm S' \<sim>\<lbrakk>\<cdot>\<rbrakk>T<TRel> Q'"
      proof -
        have "SourceTerm S' \<sim>\<lbrakk>\<cdot>\<rbrakk>T<TRel> TargetTerm (\<lbrakk>S'\<rbrakk>)"
          by (rule indRelTEQ.encR)
        moreover from E2 E4 have "TargetTerm (\<lbrakk>S'\<rbrakk>) \<sim>\<lbrakk>\<cdot>\<rbrakk>T<TRel> Q'"
          by (simp add: indRelTEQ.target)
        ultimately show "SourceTerm S' \<sim>\<lbrakk>\<cdot>\<rbrakk>T<TRel> Q'"
          by (rule indRelTEQ.trans)
      qed
      ultimately show "\<exists>P'. SourceTerm S \<longmapsto>(STCal Source Target)* P' \<and> P' \<sim>\<lbrakk>\<cdot>\<rbrakk>T<TRel> Q'"
        by blast
    next
      case (encL S)
      assume "SourceTerm S \<longmapsto>(STCal Source Target)* Q'"
      from this obtain S' where F1: "S \<longmapsto>Source* S'" and F2: "S' \<in>S Q'"
        by (auto simp add: STCal_steps(1))
      from F1 oc obtain T where F3: "\<lbrakk>S\<rbrakk> \<longmapsto>Target* T" and F4: "(\<lbrakk>S'\<rbrakk>, T) \<in> TRel"
        by blast
      from F3 have "TargetTerm (\<lbrakk>S\<rbrakk>) \<longmapsto>(STCal Source Target)* (TargetTerm T)"
        by (simp add: STCal_steps(2))
      moreover have "TargetTerm T \<sim>\<lbrakk>\<cdot>\<rbrakk>T<TRel> Q'"
      proof -
        from F4 eqT have "(T, \<lbrakk>S'\<rbrakk>) \<in> TRel"
          unfolding equiv_def sym_def
          by blast
        hence "TargetTerm T \<sim>\<lbrakk>\<cdot>\<rbrakk>T<TRel> TargetTerm (\<lbrakk>S'\<rbrakk>)"
          by (rule indRelTEQ.target)
        moreover from F2 have "TargetTerm (\<lbrakk>S'\<rbrakk>) \<sim>\<lbrakk>\<cdot>\<rbrakk>T<TRel> Q'"
          by (simp add: indRelTEQ.encL)
        ultimately show "TargetTerm T \<sim>\<lbrakk>\<cdot>\<rbrakk>T<TRel> Q'"
          by (rule indRelTEQ.trans)
      qed
      ultimately show "\<exists>P'. TargetTerm (\<lbrakk>S\<rbrakk>) \<longmapsto>(STCal Source Target)* P' \<and> P' \<sim>\<lbrakk>\<cdot>\<rbrakk>T<TRel> Q'"
        by blast
    next
      case (target T1 T2)
      assume "TargetTerm T2 \<longmapsto>(STCal Source Target)* Q'"
      from this obtain T2' where G1: "T2 \<longmapsto>Target* T2'" and G2: "T2' \<in>T Q'"
        by (auto simp add: STCal_steps(2))
      assume "(T1, T2) \<in> TRel"
      with G1 bisimT obtain T1' where G3: "T1 \<longmapsto>Target* T1'" and G4: "(T1', T2') \<in> TRel"
        by blast
      from G3 have "TargetTerm T1 \<longmapsto>(STCal Source Target)* (TargetTerm T1')"
        by (simp add: STCal_steps(2))
      moreover from G2 G4 have "TargetTerm T1' \<sim>\<lbrakk>\<cdot>\<rbrakk>T<TRel> Q'"
        by (simp add: indRelTEQ.target)
      ultimately show "\<exists>P'. TargetTerm T1 \<longmapsto>(STCal Source Target)* P' \<and> P' \<sim>\<lbrakk>\<cdot>\<rbrakk>T<TRel> Q'"
        by blast
    next
      case (trans P Q R R')
      assume "R \<longmapsto>(STCal Source Target)* R'"
         and "\<And>R'. R \<longmapsto>(STCal Source Target)* R'
              \<Longrightarrow> \<exists>Q'. Q \<longmapsto>(STCal Source Target)* Q' \<and> Q' \<sim>\<lbrakk>\<cdot>\<rbrakk>T<TRel> R'"
      from this obtain Q' where H1: "Q \<longmapsto>(STCal Source Target)* Q'" and H2: "Q' \<sim>\<lbrakk>\<cdot>\<rbrakk>T<TRel> R'"
        by blast
      assume "\<And>Q'. Q \<longmapsto>(STCal Source Target)* Q'
              \<Longrightarrow> \<exists>P'. P \<longmapsto>(STCal Source Target)* P' \<and> P' \<sim>\<lbrakk>\<cdot>\<rbrakk>T<TRel> Q'"
      with H1 obtain P' where H3: "P \<longmapsto>(STCal Source Target)* P'" and H4: "P' \<sim>\<lbrakk>\<cdot>\<rbrakk>T<TRel> Q'"
        by blast
      from H4 H2 have "P' \<sim>\<lbrakk>\<cdot>\<rbrakk>T<TRel> R'"
        by (rule indRelTEQ.trans)
      with H3 show "\<exists>P'. P \<longmapsto>(STCal Source Target)* P' \<and> P' \<sim>\<lbrakk>\<cdot>\<rbrakk>T<TRel> R'"
        by blast
    qed
  qed
next
  assume bisim: "weak_reduction_bisimulation (indRelTEQ TRel) (STCal Source Target)"
  have "operational_corresponding TRel"
  proof auto
    fix S S'
    have "SourceTerm S \<sim>\<lbrakk>\<cdot>\<rbrakk>T<TRel> TargetTerm (\<lbrakk>S\<rbrakk>)"
      by (rule indRelTEQ.encR)
    moreover assume "S \<longmapsto>Source* S'"
    hence "SourceTerm S \<longmapsto>(STCal Source Target)* (SourceTerm S')"
      by (simp add: STCal_steps(1))
    ultimately obtain Q' where I1: "TargetTerm (\<lbrakk>S\<rbrakk>) \<longmapsto>(STCal Source Target)* Q'"
                           and I2: "SourceTerm S' \<sim>\<lbrakk>\<cdot>\<rbrakk>T<TRel> Q'"
      using bisim
      by blast
    from I1 obtain T where I3: "\<lbrakk>S\<rbrakk> \<longmapsto>Target* T" and I4: "T \<in>T Q'"
      by (auto simp add: STCal_steps(2))
    from eqT have "TRel\<^sup>* = TRel"
      using reflcl_trancl[of TRel] trancl_id[of TRel]
      unfolding equiv_def refl_on_def
      by auto
    with I2 I4 have "(\<lbrakk>S'\<rbrakk>, T) \<in> TRel"
      using indRelTEQ_to_TRel(2)[where TRel="TRel"]
            trans_closure_of_TRel_refl_cond[where TRel="TRel"]
      by simp
    with I3 show "\<exists>T. \<lbrakk>S\<rbrakk> \<longmapsto>Target* T \<and> (\<lbrakk>S'\<rbrakk>, T) \<in> TRel"
      by blast
  next
    fix S T
    have "SourceTerm S \<sim>\<lbrakk>\<cdot>\<rbrakk>T<TRel> TargetTerm (\<lbrakk>S\<rbrakk>)"
      by (rule indRelTEQ.encR)
    moreover assume "\<lbrakk>S\<rbrakk> \<longmapsto>Target* T"
    hence "TargetTerm (\<lbrakk>S\<rbrakk>) \<longmapsto>(STCal Source Target)* (TargetTerm T)"
      by (simp add: STCal_steps(2))
    ultimately obtain Q' where J1: "SourceTerm S \<longmapsto>(STCal Source Target)* Q'"
                           and J2: "Q' \<sim>\<lbrakk>\<cdot>\<rbrakk>T<TRel> TargetTerm T"
      using bisim
      by blast
    from J1 obtain S' where J3: "S \<longmapsto>Source* S'" and J4: "S' \<in>S Q'"
      by (auto simp add: STCal_steps(1))
    from eqT have "TRel\<^sup>* = TRel"
      using reflcl_trancl[of TRel] trancl_id[of TRel]
      unfolding equiv_def refl_on_def
      by auto
    with J2 J4 have "(\<lbrakk>S'\<rbrakk>, T) \<in> TRel"
      using indRelTEQ_to_TRel(2)[where TRel="TRel"]
            trans_closure_of_TRel_refl_cond[where TRel="TRel"]
      by blast
    with J3 show "\<exists>S'. S \<longmapsto>Source* S' \<and> (\<lbrakk>S'\<rbrakk>, T) \<in> TRel"
      by blast
  qed
  moreover have "weak_reduction_bisimulation TRel Target"
  proof -
    from eqT have "TRel\<^sup>* = TRel"
      using reflcl_trancl[of TRel] trancl_id[of TRel]
      unfolding equiv_def refl_on_def
      by auto
    with bisim show "weak_reduction_bisimulation TRel Target"
      using indRelTEQ_impl_TRel_is_weak_reduction_bisimulation[where TRel="TRel"]
      by simp
  qed
  ultimately show "operational_corresponding TRel \<and> weak_reduction_bisimulation TRel Target"
    by simp
qed

lemma (in encodingLS_encL) OC_wrt_equivalence_iff_indRelTEQ_weak_labelled_bisimulation_encL:
  fixes TRel :: "('procT \<times> 'procT) set"
  assumes eqT: "equivalence TRel"
      and inj: "inj encL"
  shows "(operational_corresponding_encL TRel \<and> weak_labelled_bisimulation TRel Target) \<longleftrightarrow>
         weak_labelled_bisimulation_encL (indRelTEQ TRel)"
proof (rule iffI, erule conjE)
  assume oc:     "operational_corresponding_encL TRel"
     and bisimT: "weak_labelled_bisimulation TRel Target"
  show "weak_labelled_bisimulation_encL (indRelTEQ TRel)"
  proof auto
    fix P Q \<alpha> P'
    assume "P \<sim>\<lbrakk>\<cdot>\<rbrakk>T<TRel> Q" and "P \<midarrow>\<Zcat>\<alpha>\<rightarrow>(STLCal Source Target)* P'"
    thus "\<exists>\<beta> Q'. Q \<midarrow>\<Zcat>\<beta>\<rightarrow>(STLCal Source Target)* Q' \<and> P' \<sim>\<lbrakk>\<cdot>\<rbrakk>T<TRel> Q' \<and> \<langle>P, \<alpha>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>Q, \<beta>\<rangle>"
    proof (induct arbitrary: \<alpha> P')
      case (encR S)
      assume "SourceTerm S \<midarrow>\<Zcat>\<alpha>\<rightarrow>(STLCal Source Target)* P'"
      from this obtain \<alpha>' S' where A1: "\<alpha>' \<in>SL \<langle>SourceTerm S, \<alpha>\<rangle>" and A2: "S' \<in>S P'"
                               and A3: "S \<midarrow>\<Zcat>\<alpha>'\<rightarrow>Source* S'"
        using STLCal_weakLabelledSteps(1)[of S \<alpha> P']
        by blast
      from oc A3 obtain \<beta>' T where A4: "\<lbrakk>S\<rbrakk> \<midarrow>\<Zcat>\<beta>'\<rightarrow>Target* T" and A5: "(\<lbrakk>S'\<rbrakk>, T) \<in> TRel"
                               and A6: "\<lblot>\<alpha>'\<rblot> = \<beta>'"
        by blast
      obtain \<beta> where A7: "\<beta>' \<in>TL \<langle>TargetTerm (\<lbrakk>S\<rbrakk>), \<beta>\<rangle>"
        unfolding getTargetLabel_def
        by blast
      with A4 have A8: "TargetTerm (\<lbrakk>S\<rbrakk>) \<midarrow>\<Zcat>\<beta>\<rightarrow>(STLCal Source Target)* (TargetTerm T)"
        using STLCal_weakLabelledSteps(2)[of "\<lbrakk>S\<rbrakk>" \<beta> "TargetTerm T"]
        by blast
      moreover have "P' \<sim>\<lbrakk>\<cdot>\<rbrakk>T<TRel> TargetTerm T"
      proof -
        from A2 have "P' \<sim>\<lbrakk>\<cdot>\<rbrakk>T<TRel> TargetTerm (\<lbrakk>S'\<rbrakk>)"
          by (simp add: indRelTEQ.encR)
        moreover from A5 have "TargetTerm (\<lbrakk>S'\<rbrakk>) \<sim>\<lbrakk>\<cdot>\<rbrakk>T<TRel> TargetTerm T"
          using indRelTEQ.target[of "\<lbrakk>S'\<rbrakk>" T "TRel"]
          by simp
        ultimately show "P' \<sim>\<lbrakk>\<cdot>\<rbrakk>T<TRel> TargetTerm T"
          by (rule indRelTEQ.trans)
      qed
      moreover from A1 A6 A7 have "\<langle>SourceTerm S, \<alpha>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>TargetTerm (\<lbrakk>S\<rbrakk>), \<beta>\<rangle>"
        unfolding related_labels_def encLST_def
        by blast
      ultimately show "\<exists>\<beta> Q'. TargetTerm (\<lbrakk>S\<rbrakk>) \<midarrow>\<Zcat>\<beta>\<rightarrow>(STLCal Source Target)* Q' \<and>
                       P' \<sim>\<lbrakk>\<cdot>\<rbrakk>T<TRel> Q' \<and> \<langle>SourceTerm S, \<alpha>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>TargetTerm (\<lbrakk>S\<rbrakk>), \<beta>\<rangle>"
        by blast
    next
      case (encL S)
      assume "TargetTerm (\<lbrakk>S\<rbrakk>) \<midarrow>\<Zcat>\<alpha>\<rightarrow>(STLCal Source Target)* P'"
      then obtain \<alpha>' T where A1: "\<alpha>' \<in>TL \<langle>TargetTerm (\<lbrakk>S\<rbrakk>), \<alpha>\<rangle>" and A2: "T \<in>T P'"
                         and A3: "\<lbrakk>S\<rbrakk> \<midarrow>\<Zcat>\<alpha>'\<rightarrow>Target* T"
        using STLCal_weakLabelledSteps(2)[of "\<lbrakk>S\<rbrakk>" \<alpha> P']
        by blast
      from oc A3 obtain \<beta>' S' where A4: "S \<midarrow>\<Zcat>\<beta>'\<rightarrow>Source* S'" and A5: "(\<lbrakk>S'\<rbrakk>, T) \<in> TRel"
                                and A6: "\<lblot>\<beta>'\<rblot> = \<alpha>'"
        by blast
      obtain \<beta> where A7: "\<beta>' \<in>SL \<langle>SourceTerm S, \<beta>\<rangle>"
        unfolding getSourceLabel_def
        by blast
      with A4 have "SourceTerm S \<midarrow>\<Zcat>\<beta>\<rightarrow>(STLCal Source Target)* (SourceTerm S')"
        using STLCal_weakLabelledSteps(1)[of S \<beta> "SourceTerm S'"]
        by blast
      moreover have "P' \<sim>\<lbrakk>\<cdot>\<rbrakk>T<TRel> SourceTerm S'"
      proof -
        from A5 eqT have "(T, \<lbrakk>S'\<rbrakk>) \<in> TRel"
          unfolding equiv_def sym_def
          by blast
        with A2 have "P' \<sim>\<lbrakk>\<cdot>\<rbrakk>T<TRel> TargetTerm (\<lbrakk>S'\<rbrakk>)"
          by (simp add: indRelTEQ.target)
        moreover have "TargetTerm (\<lbrakk>S'\<rbrakk>) \<sim>\<lbrakk>\<cdot>\<rbrakk>T<TRel> SourceTerm S'"
          by (rule indRelTEQ.encL)
        ultimately show "P' \<sim>\<lbrakk>\<cdot>\<rbrakk>T<TRel> SourceTerm S'"
          by (rule indRelTEQ.trans)
      qed
      moreover from A1 A6 A7 have "\<lparr>SourceTerm S, \<beta>\<rparr>\<mapsto>\<langle>TargetTerm (\<lbrakk>S\<rbrakk>), \<alpha>\<rangle>"
        unfolding encLST_def
        by blast
      hence "\<langle>TargetTerm (\<lbrakk>S\<rbrakk>), \<alpha>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>SourceTerm S, \<beta>\<rangle>"
        unfolding related_labels_def
        by simp
      ultimately show "\<exists>\<beta> Q'. SourceTerm S \<midarrow>\<Zcat>\<beta>\<rightarrow>(STLCal Source Target)* Q' \<and> P' \<sim>\<lbrakk>\<cdot>\<rbrakk>T<TRel> Q' \<and>
                       \<langle>TargetTerm (\<lbrakk>S\<rbrakk>), \<alpha>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>SourceTerm S, \<beta>\<rangle>"
        by blast
    next
      case (target T1 T2)
      assume "TargetTerm T1 \<midarrow>\<Zcat>\<alpha>\<rightarrow>(STLCal Source Target)* P'"
      from this obtain \<alpha>' T1' where C1: "\<alpha>' \<in>TL \<langle>TargetTerm T1, \<alpha>\<rangle>" and C2: "T1' \<in>T P'"
                                and C3: "T1 \<midarrow>\<Zcat>\<alpha>'\<rightarrow>Target* T1'"
        using STLCal_weakLabelledSteps(2)[of T1 \<alpha> P']
        by blast
      assume "(T1, T2) \<in> TRel"
      with bisimT C3 obtain T2' where C4: "T2 \<midarrow>\<Zcat>\<alpha>'\<rightarrow>Target* T2'" and C5: "(T1', T2') \<in> TRel"
        by blast
      from C1 C4 have "TargetTerm T2 \<midarrow>\<Zcat>\<alpha>\<rightarrow>(STLCal Source Target)* (TargetTerm T2')"
        using STLCal_weakLabelledSteps(2)[of T2 \<alpha> "TargetTerm T2'"]
        unfolding getTargetLabel_def
        by blast
      moreover from C2 C5 have "P' \<sim>\<lbrakk>\<cdot>\<rbrakk>T<TRel> TargetTerm T2'"
        by (simp add: indRelTEQ.target)
      moreover have "\<langle>TargetTerm T1, \<alpha>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>TargetTerm T2, \<alpha>\<rangle>"
        unfolding related_labels_def
        by simp
      ultimately show "\<exists>\<beta> Q'. TargetTerm T2 \<midarrow>\<Zcat>\<beta>\<rightarrow>(STLCal Source Target)* Q' \<and> P' \<sim>\<lbrakk>\<cdot>\<rbrakk>T<TRel> Q' \<and>
                       \<langle>TargetTerm T1, \<alpha>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>TargetTerm T2, \<beta>\<rangle>"
        by blast
    next
      case (trans P Q R)
      assume "P \<midarrow>\<Zcat>\<alpha>\<rightarrow>(STLCal Source Target)* P'"
         and "\<And>\<alpha> P'. P \<midarrow>\<Zcat>\<alpha>\<rightarrow>(STLCal Source Target)* P' \<Longrightarrow>
              \<exists>\<beta> Q'. Q \<midarrow>\<Zcat>\<beta>\<rightarrow>(STLCal Source Target)* Q' \<and> P' \<sim>\<lbrakk>\<cdot>\<rbrakk>T<TRel> Q' \<and> \<langle>P, \<alpha>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>Q, \<beta>\<rangle>"
      then obtain \<beta> Q' where A1: "Q \<midarrow>\<Zcat>\<beta>\<rightarrow>(STLCal Source Target)* Q'" and A2: "P' \<sim>\<lbrakk>\<cdot>\<rbrakk>T<TRel> Q'"
                         and A3: "\<langle>P, \<alpha>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>Q, \<beta>\<rangle>"
        by blast
      assume "\<And>\<beta> Q'. Q \<midarrow>\<Zcat>\<beta>\<rightarrow>(STLCal Source Target)* Q' \<Longrightarrow>
              \<exists>\<gamma> R'. R \<midarrow>\<Zcat>\<gamma>\<rightarrow>(STLCal Source Target)* R' \<and> Q' \<sim>\<lbrakk>\<cdot>\<rbrakk>T<TRel> R' \<and> \<langle>Q, \<beta>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>R, \<gamma>\<rangle>"
      with A1 obtain \<gamma> R' where A4: "R \<midarrow>\<Zcat>\<gamma>\<rightarrow>(STLCal Source Target)* R'" and A5: "Q' \<sim>\<lbrakk>\<cdot>\<rbrakk>T<TRel> R'"
                            and A6: "\<langle>Q, \<beta>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>R, \<gamma>\<rangle>"
        by blast
      from A2 A5 have A7: "P' \<sim>\<lbrakk>\<cdot>\<rbrakk>T<TRel> R'"
        by (rule indRelTEQ.trans)
      from inj A3 A6 have "\<langle>P, \<alpha>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>R, \<gamma>\<rangle>"
        using related_labels_trans_inj[of P \<alpha> Q \<beta> R \<gamma>]
        by simp
      with A4 A7
      show "\<exists>\<gamma> R'. R \<midarrow>\<Zcat>\<gamma>\<rightarrow>(STLCal Source Target)* R' \<and> P' \<sim>\<lbrakk>\<cdot>\<rbrakk>T<TRel> R' \<and> \<langle>P, \<alpha>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>R, \<gamma>\<rangle>"
        by blast
    qed
  next
    fix P Q \<beta> Q'
    assume "P \<sim>\<lbrakk>\<cdot>\<rbrakk>T<TRel> Q" and "Q \<midarrow>\<Zcat>\<beta>\<rightarrow>(STLCal Source Target)* Q'"
    thus "\<exists>\<alpha> P'. P \<midarrow>\<Zcat>\<alpha>\<rightarrow>(STLCal Source Target)* P' \<and> P' \<sim>\<lbrakk>\<cdot>\<rbrakk>T<TRel> Q' \<and> \<langle>P, \<alpha>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>Q, \<beta>\<rangle>"
    proof (induct arbitrary: \<beta> Q')
      case (encR S)
      assume "TargetTerm (\<lbrakk>S\<rbrakk>) \<midarrow>\<Zcat>\<beta>\<rightarrow>(STLCal Source Target)* Q'"
      then obtain \<beta>' T where A1: "\<beta>' \<in>TL \<langle>TargetTerm (\<lbrakk>S\<rbrakk>), \<beta>\<rangle>" and A2: "T \<in>T Q'"
                         and A3: "\<lbrakk>S\<rbrakk> \<midarrow>\<Zcat>\<beta>'\<rightarrow>Target* T"
        using STLCal_weakLabelledSteps(2)[of "\<lbrakk>S\<rbrakk>" \<beta> Q']
        by blast
      from oc A3 obtain \<alpha>' S' where A4: "S \<midarrow>\<Zcat>\<alpha>'\<rightarrow>Source* S'" and A5: "(\<lbrakk>S'\<rbrakk>, T) \<in> TRel"
                                and A6: "\<lblot>\<alpha>'\<rblot> = \<beta>'"
        by blast
      obtain \<alpha> where A7: "\<alpha>' \<in>SL \<langle>SourceTerm S, \<alpha>\<rangle>"
        unfolding getSourceLabel_def
        by blast
      with A4 have "SourceTerm S \<midarrow>\<Zcat>\<alpha>\<rightarrow>(STLCal Source Target)* (SourceTerm S')"
        using STLCal_weakLabelledSteps(1)[of S \<alpha> "SourceTerm S'"]
        by blast
      moreover have "SourceTerm S' \<sim>\<lbrakk>\<cdot>\<rbrakk>T<TRel> Q'"
      proof -
        from A2 A5 have "TargetTerm (\<lbrakk>S'\<rbrakk>) \<sim>\<lbrakk>\<cdot>\<rbrakk>T<TRel> Q'"
          by (simp add: indRelTEQ.target)
        moreover have "SourceTerm S' \<sim>\<lbrakk>\<cdot>\<rbrakk>T<TRel> TargetTerm (\<lbrakk>S'\<rbrakk>)"
          by (rule indRelTEQ.encR)
        ultimately show "SourceTerm S' \<sim>\<lbrakk>\<cdot>\<rbrakk>T<TRel> Q'"
          using indRelTEQ.trans[of "SourceTerm S'" "TargetTerm (\<lbrakk>S'\<rbrakk>)" TRel Q']
          by simp
      qed
      moreover from A1 A6 A7 have "\<lparr>SourceTerm S, \<alpha>\<rparr>\<mapsto>\<langle>TargetTerm (\<lbrakk>S\<rbrakk>), \<beta>\<rangle>"
        unfolding encLST_def
        by blast
      hence "\<langle>SourceTerm S, \<alpha>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>TargetTerm (\<lbrakk>S\<rbrakk>), \<beta>\<rangle>"
        unfolding related_labels_def
        by simp
      ultimately show "\<exists>\<alpha> P'. SourceTerm S \<midarrow>\<Zcat>\<alpha>\<rightarrow>(STLCal Source Target)* P' \<and> P' \<sim>\<lbrakk>\<cdot>\<rbrakk>T<TRel> Q' \<and>
                       \<langle>SourceTerm S, \<alpha>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>TargetTerm (\<lbrakk>S\<rbrakk>), \<beta>\<rangle>"
        by blast
    next
      case (encL S)
      assume "SourceTerm S \<midarrow>\<Zcat>\<beta>\<rightarrow>(STLCal Source Target)* Q'"
      from this obtain \<beta>' S' where A1: "\<beta>' \<in>SL \<langle>SourceTerm S, \<beta>\<rangle>" and A2: "S' \<in>S Q'"
                               and A3: "S \<midarrow>\<Zcat>\<beta>'\<rightarrow>Source* S'"
        using STLCal_weakLabelledSteps(1)[of S \<beta> Q']
        by blast
      from oc A3 obtain \<alpha>' T where A4: "\<lbrakk>S\<rbrakk> \<midarrow>\<Zcat>\<alpha>'\<rightarrow>Target* T" and A5: "(\<lbrakk>S'\<rbrakk>, T) \<in> TRel"
                               and A6: "\<lblot>\<beta>'\<rblot> = \<alpha>'"
        by blast
      obtain \<alpha> where A7: "\<alpha>' \<in>TL \<langle>TargetTerm (\<lbrakk>S\<rbrakk>), \<alpha>\<rangle>"
        unfolding getTargetLabel_def
        by blast
      with A4 have A8: "TargetTerm (\<lbrakk>S\<rbrakk>) \<midarrow>\<Zcat>\<alpha>\<rightarrow>(STLCal Source Target)* (TargetTerm T)"
        using STLCal_weakLabelledSteps(2)[of "\<lbrakk>S\<rbrakk>" \<alpha> "TargetTerm T"]
        by blast
      moreover have "TargetTerm T \<sim>\<lbrakk>\<cdot>\<rbrakk>T<TRel> Q'"
      proof -
        from A5 eqT have "(T, \<lbrakk>S'\<rbrakk>) \<in> TRel"
          unfolding equiv_def sym_def
          by blast
        hence "TargetTerm T \<sim>\<lbrakk>\<cdot>\<rbrakk>T<TRel> TargetTerm (\<lbrakk>S'\<rbrakk>)"
          using indRelTEQ.target[of T "\<lbrakk>S'\<rbrakk>" "TRel"]
          by simp
        moreover from A2 have "TargetTerm (\<lbrakk>S'\<rbrakk>) \<sim>\<lbrakk>\<cdot>\<rbrakk>T<TRel> Q'"
          by (simp add: indRelTEQ.encL)
        ultimately show "TargetTerm T \<sim>\<lbrakk>\<cdot>\<rbrakk>T<TRel> Q'"
          by (rule indRelTEQ.trans)
      qed
      moreover from A1 A6 A7 have "\<langle>TargetTerm (\<lbrakk>S\<rbrakk>), \<alpha>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>SourceTerm S, \<beta>\<rangle>"
        unfolding related_labels_def encLST_def
        by blast
      ultimately show "\<exists>\<alpha> P'. TargetTerm (\<lbrakk>S\<rbrakk>) \<midarrow>\<Zcat>\<alpha>\<rightarrow>(STLCal Source Target)* P' \<and>
                       P' \<sim>\<lbrakk>\<cdot>\<rbrakk>T<TRel> Q' \<and> \<langle>TargetTerm (\<lbrakk>S\<rbrakk>), \<alpha>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>SourceTerm S, \<beta>\<rangle>"
        by blast
    next
      case (target T1 T2)
      assume "TargetTerm T2 \<midarrow>\<Zcat>\<beta>\<rightarrow>(STLCal Source Target)* Q'"
      from this obtain \<beta>' T2' where C1: "\<beta>' \<in>TL \<langle>TargetTerm T2, \<beta>\<rangle>" and C2: "T2' \<in>T Q'"
                                and C3: "T2 \<midarrow>\<Zcat>\<beta>'\<rightarrow>Target* T2'"
        using STLCal_weakLabelledSteps(2)[of T2 \<beta> Q']
        by blast
      assume "(T1, T2) \<in> TRel"
      with bisimT C3 obtain T1' where C4: "T1 \<midarrow>\<Zcat>\<beta>'\<rightarrow>Target* T1'" and C5: "(T1', T2') \<in> TRel"
        by blast
      from C1 C4 have "TargetTerm T1 \<midarrow>\<Zcat>\<beta>\<rightarrow>(STLCal Source Target)* (TargetTerm T1')"
        using STLCal_weakLabelledSteps(2)[of T1 \<beta> "TargetTerm T1'"]
        unfolding getTargetLabel_def
        by blast
      moreover from C2 C5 have "TargetTerm T1' \<sim>\<lbrakk>\<cdot>\<rbrakk>T<TRel> Q'"
        by (simp add: indRelTEQ.target)
      moreover have "\<langle>TargetTerm T1, \<beta>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>TargetTerm T2, \<beta>\<rangle>"
        unfolding related_labels_def
        by simp
      ultimately show "\<exists>\<alpha> P'. TargetTerm T1 \<midarrow>\<Zcat>\<alpha>\<rightarrow>(STLCal Source Target)* P' \<and> P' \<sim>\<lbrakk>\<cdot>\<rbrakk>T<TRel> Q' \<and>
                       \<langle>TargetTerm T1, \<alpha>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>TargetTerm T2, \<beta>\<rangle>"
        by blast
    next
      case (trans R Q P \<alpha> P')
      assume "P \<midarrow>\<Zcat>\<alpha>\<rightarrow>(STLCal Source Target)* P'"
         and "\<And>\<alpha> P'. P \<midarrow>\<Zcat>\<alpha>\<rightarrow>(STLCal Source Target)* P' \<Longrightarrow>
              \<exists>\<beta> Q'. Q \<midarrow>\<Zcat>\<beta>\<rightarrow>(STLCal Source Target)* Q' \<and> Q' \<sim>\<lbrakk>\<cdot>\<rbrakk>T<TRel> P' \<and> \<langle>Q, \<beta>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>P, \<alpha>\<rangle>"
      then obtain \<beta> Q' where A1: "Q \<midarrow>\<Zcat>\<beta>\<rightarrow>(STLCal Source Target)* Q'" and A2: "Q' \<sim>\<lbrakk>\<cdot>\<rbrakk>T<TRel> P'"
                         and A3: "\<langle>Q, \<beta>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>P, \<alpha>\<rangle>"
        by blast
      assume "\<And>\<beta> Q'. Q \<midarrow>\<Zcat>\<beta>\<rightarrow>(STLCal Source Target)* Q' \<Longrightarrow>
              \<exists>\<gamma> R'. R \<midarrow>\<Zcat>\<gamma>\<rightarrow>(STLCal Source Target)* R' \<and> R' \<sim>\<lbrakk>\<cdot>\<rbrakk>T<TRel> Q' \<and> \<langle>R, \<gamma>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>Q, \<beta>\<rangle>"
      with A1 obtain \<gamma> R' where A4: "R \<midarrow>\<Zcat>\<gamma>\<rightarrow>(STLCal Source Target)* R'" and A5: "R' \<sim>\<lbrakk>\<cdot>\<rbrakk>T<TRel> Q'"
                            and A6: "\<langle>R, \<gamma>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>Q, \<beta>\<rangle>"
        by blast
      from A2 A5 have A7: "R' \<sim>\<lbrakk>\<cdot>\<rbrakk>T<TRel> P'"
        using indRelTEQ.trans[of R' Q' TRel P']
        by simp
      from inj A3 A6 have "\<langle>R, \<gamma>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>P, \<alpha>\<rangle>"
        using related_labels_trans_inj[of R \<gamma> Q \<beta> P \<alpha>]
        by simp
      with A4 A7
      show "\<exists>\<gamma> R'. R \<midarrow>\<Zcat>\<gamma>\<rightarrow>(STLCal Source Target)* R' \<and> R' \<sim>\<lbrakk>\<cdot>\<rbrakk>T<TRel> P' \<and> \<langle>R, \<gamma>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>P, \<alpha>\<rangle>"
        by blast
    qed
  qed
next
  assume bisim: "weak_labelled_bisimulation_encL (indRelTEQ TRel)"
  have "operational_corresponding_encL TRel"
  proof auto
    fix S \<alpha> S'
    obtain \<alpha>' where A1: "\<alpha> \<in>SL \<langle>SourceTerm S, \<alpha>'\<rangle>"
      unfolding getSourceLabel_def
      by blast
    have A2: "SourceTerm S \<sim>\<lbrakk>\<cdot>\<rbrakk>T<TRel> TargetTerm (\<lbrakk>S\<rbrakk>)"
      by (rule indRelTEQ.encR)
    moreover assume "S \<midarrow>\<Zcat>\<alpha>\<rightarrow>Source* S'"
    with A1 have "SourceTerm S \<midarrow>\<Zcat>\<alpha>'\<rightarrow>(STLCal Source Target)* (SourceTerm S')"
      using STLCal_weakLabelledSteps(1)[of S \<alpha>' "SourceTerm S'"]
      by blast
    with bisim A2 obtain \<beta>' Q' where A3: "TargetTerm (\<lbrakk>S\<rbrakk>) \<midarrow>\<Zcat>\<beta>'\<rightarrow>(STLCal Source Target)* Q'"
                                 and A4: "SourceTerm S' \<sim>\<lbrakk>\<cdot>\<rbrakk>T<TRel> Q'"
                                 and A5: "\<langle>SourceTerm S, \<alpha>'\<rangle> \<equiv>\<lparr>\<rparr> \<langle>TargetTerm (\<lbrakk>S\<rbrakk>), \<beta>'\<rangle>"
      by blast
    from A3 obtain \<beta> T where A6: "\<beta> \<in>TL \<langle>TargetTerm (\<lbrakk>S\<rbrakk>), \<beta>'\<rangle>" and A7: "T \<in>T Q'"
                         and A8: "\<lbrakk>S\<rbrakk> \<midarrow>\<Zcat>\<beta>\<rightarrow>Target* T"
      using STLCal_weakLabelledSteps(2)[of "\<lbrakk>S\<rbrakk>" \<beta>' Q']
      by blast
    from eqT have "TRel\<^sup>* = TRel"
      using reflcl_trancl[of TRel] trancl_id[of TRel]
      unfolding equiv_def refl_on_def
      by auto
    with A4 A7 have A9: "(\<lbrakk>S'\<rbrakk>, T) \<in> TRel"
      using indRelTEQ_to_TRel(2)[where TRel="TRel"]
            trans_closure_of_TRel_refl_cond[where TRel="TRel"]
      by simp
    from A1 A5 A6 have "\<lblot>\<alpha>\<rblot> = \<beta>"
      unfolding related_labels_def encLST_def getSourceLabel_def getTargetLabel_def
      by blast
    with A8 A9 show "\<exists>T. \<lbrakk>S\<rbrakk> \<midarrow>\<Zcat>\<lblot>\<alpha>\<rblot>\<rightarrow>Target* T \<and> (\<lbrakk>S'\<rbrakk>, T) \<in> TRel"
      by blast
  next
    fix S \<beta> T
    obtain \<beta>' where A1: "\<beta> \<in>TL \<langle>TargetTerm (\<lbrakk>S\<rbrakk>), \<beta>'\<rangle>"
      unfolding getTargetLabel_def
      by blast
    have A2: "SourceTerm S \<sim>\<lbrakk>\<cdot>\<rbrakk>T<TRel> TargetTerm (\<lbrakk>S\<rbrakk>)"
      by (rule indRelTEQ.encR)
    assume "\<lbrakk>S\<rbrakk> \<midarrow>\<Zcat>\<beta>\<rightarrow>Target* T"
    with A1 have "TargetTerm (\<lbrakk>S\<rbrakk>) \<midarrow>\<Zcat>\<beta>'\<rightarrow>(STLCal Source Target)* (TargetTerm T)"
      using STLCal_weakLabelledSteps(2)[of "\<lbrakk>S\<rbrakk>" \<beta>' "TargetTerm T"]
      by blast
    with bisim A2 obtain \<alpha>' Q' where A3: "SourceTerm S \<midarrow>\<Zcat>\<alpha>'\<rightarrow>(STLCal Source Target)* Q'"
                                 and A4: "Q' \<sim>\<lbrakk>\<cdot>\<rbrakk>T<TRel> TargetTerm T"
                                 and A5: "\<langle>SourceTerm S, \<alpha>'\<rangle> \<equiv>\<lparr>\<rparr> \<langle>TargetTerm (\<lbrakk>S\<rbrakk>), \<beta>'\<rangle>"
      by blast
    from A3 obtain \<alpha> S' where A6: "\<alpha> \<in>SL \<langle>SourceTerm S, \<alpha>'\<rangle>" and A7: "S' \<in>S Q'"
                          and A8: "S \<midarrow>\<Zcat>\<alpha>\<rightarrow>Source* S'"
      using STLCal_weakLabelledSteps(1)[of S \<alpha>' Q']
      by blast
    from eqT have "TRel\<^sup>* = TRel"
      using reflcl_trancl[of TRel] trancl_id[of TRel]
      unfolding equiv_def refl_on_def
      by auto
    with A4 A7 have A9: "(\<lbrakk>S'\<rbrakk>, T) \<in> TRel"
      using indRelTEQ_to_TRel(2)[where TRel="TRel"]
            trans_closure_of_TRel_refl_cond[where TRel="TRel"]
      by blast
    from A1 A5 A6 have "\<lblot>\<alpha>\<rblot> = \<beta>"
      unfolding related_labels_def encLST_def getSourceLabel_def getTargetLabel_def
      by blast
    with A8 A9 show "\<exists>\<alpha> S'. S \<midarrow>\<Zcat>\<alpha>\<rightarrow>Source* S' \<and> (\<lbrakk>S'\<rbrakk>, T) \<in> TRel \<and> \<lblot>\<alpha>\<rblot> = \<beta>"
      by blast
  qed
  moreover have "weak_labelled_bisimulation TRel Target"
  proof -
    from eqT have "TRel\<^sup>* = TRel"
      using reflcl_trancl[of TRel] trancl_id[of TRel]
      unfolding equiv_def refl_on_def
      by auto
    with bisim show "weak_labelled_bisimulation TRel Target"
      using indRelTEQ_impl_TRel_is_weak_labelled_bisimulation_encL[where TRel="TRel"]
      by simp
  qed
  ultimately show "operational_corresponding_encL TRel \<and> weak_labelled_bisimulation TRel Target"
    by simp
qed

lemma (in encoding) OC_wrt_equivalence_iff_weak_reduction_bisimulation:
  fixes TRel :: "('procT \<times> 'procT) set"
  assumes eqT: "equivalence TRel"
  shows "(operational_corresponding TRel \<and> weak_reduction_bisimulation TRel Target) \<longleftrightarrow> (\<exists>Rel.
         (\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel \<and> (TargetTerm (\<lbrakk>S\<rbrakk>), SourceTerm S) \<in> Rel)
         \<and> TRel = {(T1, T2). (TargetTerm T1, TargetTerm T2) \<in> Rel}
         \<and> trans Rel \<and> weak_reduction_bisimulation Rel (STCal Source Target))"
proof (rule iffI, erule conjE)
  assume oc: "operational_corresponding TRel" and bisimT: "weak_reduction_bisimulation TRel Target"
  from eqT have rt: "TRel\<^sup>* = TRel"
    using reflcl_trancl[of TRel] trancl_id[of TRel]
    unfolding equiv_def refl_on_def
    by auto
  have "\<forall>S. SourceTerm S \<sim>\<lbrakk>\<cdot>\<rbrakk>T<TRel> TargetTerm (\<lbrakk>S\<rbrakk>) \<and> TargetTerm (\<lbrakk>S\<rbrakk>) \<sim>\<lbrakk>\<cdot>\<rbrakk>T<TRel> SourceTerm S"
    by (simp add: indRelTEQ.encR indRelTEQ.encL)
  moreover from rt have "TRel = {(T1, T2). TargetTerm T1 \<sim>\<lbrakk>\<cdot>\<rbrakk>T<TRel> TargetTerm T2}"
    using indRelTEQ_to_TRel(4)[where TRel="TRel"]
          trans_closure_of_TRel_refl_cond[where TRel="TRel"]
    by (auto simp add: indRelTEQ.target)
  moreover have "trans (indRelTEQ TRel)"
    using indRelTEQ.trans[where TRel="TRel"]
    unfolding trans_def
    by blast
  moreover from eqT oc bisimT
  have "weak_reduction_bisimulation (indRelTEQ TRel) (STCal Source Target)"
    using OC_wrt_equivalence_iff_indRelTEQ_weak_reduction_bisimulation[where TRel="TRel"]
    by blast
  ultimately
  show "\<exists>Rel. (\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel \<and> (TargetTerm (\<lbrakk>S\<rbrakk>), SourceTerm S) \<in> Rel)
        \<and> TRel = {(T1, T2). (TargetTerm T1, TargetTerm T2) \<in> Rel} \<and> trans Rel
        \<and> weak_reduction_bisimulation Rel (STCal Source Target)"
    by blast
next
  assume "\<exists>Rel. (\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel
                 \<and> (TargetTerm (\<lbrakk>S\<rbrakk>), SourceTerm S) \<in> Rel)
          \<and> TRel = {(T1, T2). (TargetTerm T1, TargetTerm T2) \<in> Rel} \<and> trans Rel
          \<and> weak_reduction_bisimulation Rel (STCal Source Target)"
  from this obtain Rel where A1: "\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel
                                  \<and> (TargetTerm (\<lbrakk>S\<rbrakk>), SourceTerm S) \<in> Rel"
   and A2: "TRel = {(T1, T2). (TargetTerm T1, TargetTerm T2) \<in> Rel}" and A3: "trans Rel"
   and A4: "weak_reduction_bisimulation Rel (STCal Source Target)"
    by blast
  have "operational_corresponding TRel"
  proof auto
    fix S S'
    from A1 have "(SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel"
      by simp
    moreover assume "S \<longmapsto>Source* S'"
    hence "SourceTerm S \<longmapsto>(STCal Source Target)* (SourceTerm S')"
      by (simp add: STCal_steps(1))
    ultimately obtain Q' where B1: "TargetTerm (\<lbrakk>S\<rbrakk>) \<longmapsto>(STCal Source Target)* Q'"
                           and B2: "(SourceTerm S', Q') \<in> Rel"
      using A4
      by blast
    from B1 obtain T where B3: "\<lbrakk>S\<rbrakk> \<longmapsto>Target* T" and B4: "T \<in>T Q'"
      by (auto simp add: STCal_steps(2))
    from A1 have "(TargetTerm (\<lbrakk>S'\<rbrakk>), SourceTerm S') \<in> Rel"
      by simp
    with B2 A3 have "(TargetTerm (\<lbrakk>S'\<rbrakk>), Q') \<in> Rel"
      unfolding trans_def
      by blast
    with B4 A2 have "(\<lbrakk>S'\<rbrakk>, T) \<in> TRel"
      by simp
    with B3 show "\<exists>T. \<lbrakk>S\<rbrakk> \<longmapsto>Target* T \<and> (\<lbrakk>S'\<rbrakk>, T) \<in> TRel"
      by blast
  next
    fix S T
    from A1 have "(SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel"
      by simp
    moreover assume "\<lbrakk>S\<rbrakk> \<longmapsto>Target* T"
    hence "TargetTerm (\<lbrakk>S\<rbrakk>) \<longmapsto>(STCal Source Target)* (TargetTerm T)"
      by (simp add: STCal_steps(2))
    ultimately obtain P' where C1: "SourceTerm S \<longmapsto>(STCal Source Target)* P'"
                           and C2: "(P', TargetTerm T) \<in> Rel"
      using A4
      by blast
    from C1 obtain S' where C3: "S \<longmapsto>Source* S'" and C4: "S' \<in>S P'"
      by (auto simp add: STCal_steps(1))
    from A1 C4 have "(TargetTerm (\<lbrakk>S'\<rbrakk>), P') \<in> Rel"
      by simp
    from A3 this C2 have "(TargetTerm (\<lbrakk>S'\<rbrakk>), TargetTerm T) \<in> Rel"
      unfolding trans_def
      by blast
    with A2 have "(\<lbrakk>S'\<rbrakk>, T) \<in> TRel"
      by simp
    with C3 show "\<exists>S'. S \<longmapsto>Source* S' \<and> (\<lbrakk>S'\<rbrakk>, T) \<in> TRel"
      by blast
  qed
  moreover have "weak_reduction_bisimulation TRel Target"
  proof auto
    fix TP TQ TP'
    assume "(TP, TQ) \<in> TRel"
    with A2 have "(TargetTerm TP, TargetTerm TQ) \<in> Rel"
      by simp
    moreover assume "TP \<longmapsto>Target* TP'"
    hence "TargetTerm TP \<longmapsto>(STCal Source Target)* (TargetTerm TP')"
      by (simp add: STCal_steps(2))
    ultimately obtain Q' where D1: "TargetTerm TQ \<longmapsto>(STCal Source Target)* Q'"
                           and D2: "(TargetTerm TP', Q') \<in> Rel"
      using A4
      by blast
    from D1 obtain TQ' where D3: "TQ \<longmapsto>Target* TQ'" and D4: "TQ' \<in>T Q'"
      by (auto simp add: STCal_steps(2))
    from A2 D2 D4 have "(TP', TQ') \<in> TRel"
      by simp
    with D3 show "\<exists>TQ'. TQ \<longmapsto>Target* TQ' \<and> (TP', TQ') \<in> TRel"
      by blast
  next
    fix TP TQ TQ'
    assume "(TP, TQ) \<in> TRel"
    with A2 have "(TargetTerm TP, TargetTerm TQ) \<in> Rel"
      by simp
    moreover assume "TQ \<longmapsto>Target* TQ'"
    hence "TargetTerm TQ \<longmapsto>(STCal Source Target)* (TargetTerm TQ')"
      by (simp add: STCal_steps(2))
    ultimately obtain P' where E1: "TargetTerm TP \<longmapsto>(STCal Source Target)* P'"
                           and E2: "(P', TargetTerm TQ') \<in> Rel"
      using A4
      by blast
    from E1 obtain TP' where E3: "TP \<longmapsto>Target* TP'" and E4: "TP' \<in>T P'"
      by (auto simp add: STCal_steps(2))
    from A2 E2 E4 have "(TP', TQ') \<in> TRel"
      by simp
    with E3 show "\<exists>TP'. TP \<longmapsto>Target* TP' \<and> (TP', TQ') \<in> TRel"
      by blast
  qed
  ultimately show "operational_corresponding TRel \<and> weak_reduction_bisimulation TRel Target"
    by simp
qed

lemma (in encodingLS_encL) OC_wrt_equivalence_iff_weak_labelled_bisimulation_encL:
  fixes TRel :: "('procT \<times> 'procT) set"
  assumes eqT: "equivalence TRel"
      and inj: "inj encL"
  shows "(operational_corresponding_encL TRel \<and> weak_labelled_bisimulation TRel Target) \<longleftrightarrow> (\<exists>Rel.
         (\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel \<and> (TargetTerm (\<lbrakk>S\<rbrakk>), SourceTerm S) \<in> Rel)
         \<and> TRel = {(T1, T2). (TargetTerm T1, TargetTerm T2) \<in> Rel}
         \<and> trans Rel \<and> weak_labelled_bisimulation_encL Rel)"
proof (rule iffI, erule conjE)
  assume oc:     "operational_corresponding_encL TRel"
     and bisimT: "weak_labelled_bisimulation TRel Target"
  from eqT have rt: "TRel\<^sup>* = TRel"
    using reflcl_trancl[of TRel] trancl_id[of TRel]
    unfolding equiv_def refl_on_def
    by auto
  have "\<forall>S. SourceTerm S \<sim>\<lbrakk>\<cdot>\<rbrakk>T<TRel> TargetTerm (\<lbrakk>S\<rbrakk>) \<and> TargetTerm (\<lbrakk>S\<rbrakk>) \<sim>\<lbrakk>\<cdot>\<rbrakk>T<TRel> SourceTerm S"
    by (simp add: indRelTEQ.encR indRelTEQ.encL)
  moreover from rt have "TRel = {(T1, T2). TargetTerm T1 \<sim>\<lbrakk>\<cdot>\<rbrakk>T<TRel> TargetTerm T2}"
    using indRelTEQ_to_TRel(4)[where TRel="TRel"]
          trans_closure_of_TRel_refl_cond[where TRel="TRel"]
    by (auto simp add: indRelTEQ.target)
  moreover have "trans (indRelTEQ TRel)"
    using indRelTEQ.trans[where TRel="TRel"]
    unfolding trans_def
    by blast
  moreover from eqT inj oc bisimT
  have "weak_labelled_bisimulation_encL (indRelTEQ TRel)"
    using OC_wrt_equivalence_iff_indRelTEQ_weak_labelled_bisimulation_encL[where TRel="TRel"]
    by blast
  ultimately
  show "\<exists>Rel. (\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel \<and> (TargetTerm (\<lbrakk>S\<rbrakk>), SourceTerm S) \<in> Rel)
        \<and> TRel = {(T1, T2). (TargetTerm T1, TargetTerm T2) \<in> Rel} \<and> trans Rel
        \<and> weak_labelled_bisimulation_encL Rel"
    by blast
next
  assume "\<exists>Rel. (\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel
                 \<and> (TargetTerm (\<lbrakk>S\<rbrakk>), SourceTerm S) \<in> Rel)
          \<and> TRel = {(T1, T2). (TargetTerm T1, TargetTerm T2) \<in> Rel} \<and> trans Rel
          \<and> weak_labelled_bisimulation_encL Rel"
  from this obtain Rel where A1: "\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel
                                  \<and> (TargetTerm (\<lbrakk>S\<rbrakk>), SourceTerm S) \<in> Rel"
   and A2: "TRel = {(T1, T2). (TargetTerm T1, TargetTerm T2) \<in> Rel}" and A3: "trans Rel"
   and A4: "weak_labelled_bisimulation_encL Rel"
    by blast
  have "operational_corresponding_encL TRel"
  proof auto
    fix S \<alpha> S'
    obtain \<alpha>' where B1: "\<alpha> \<in>SL \<langle>SourceTerm S, \<alpha>'\<rangle>"
      unfolding getSourceLabel_def
      by blast
    from A1 have B2: "(SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel"
      by simp
    assume "S \<midarrow>\<Zcat>\<alpha>\<rightarrow>Source* S'"
    with B1 have "SourceTerm S \<midarrow>\<Zcat>\<alpha>'\<rightarrow>(STLCal Source Target)* (SourceTerm S')"
      using STLCal_weakLabelledSteps(1)[of S \<alpha>' "SourceTerm S'"]
      by blast
    with A4 B2 obtain \<beta>' Q' where B3: "TargetTerm (\<lbrakk>S\<rbrakk>) \<midarrow>\<Zcat>\<beta>'\<rightarrow>(STLCal Source Target)* Q'"
                              and B4: "(SourceTerm S', Q') \<in> Rel"
                              and B5: "\<langle>SourceTerm S, \<alpha>'\<rangle> \<equiv>\<lparr>\<rparr> \<langle>TargetTerm (\<lbrakk>S\<rbrakk>), \<beta>'\<rangle>"
      by blast
    from B3 obtain \<beta> T where B6: "\<beta> \<in>TL \<langle>TargetTerm (\<lbrakk>S\<rbrakk>), \<beta>'\<rangle>" and B7: "T \<in>T Q'"
                         and B8: "\<lbrakk>S\<rbrakk> \<midarrow>\<Zcat>\<beta>\<rightarrow>Target* T"
      using STLCal_weakLabelledSteps(2)[of "\<lbrakk>S\<rbrakk>" \<beta>' Q']
      by blast
    from A1 have "(TargetTerm (\<lbrakk>S'\<rbrakk>), SourceTerm S') \<in> Rel"
      by simp
    with A3 B4 have "(TargetTerm (\<lbrakk>S'\<rbrakk>), Q') \<in> Rel"
      using transD[of Rel "TargetTerm (\<lbrakk>S'\<rbrakk>)" "SourceTerm S'" Q']
      by simp
    with A2 B7 have B9: "(\<lbrakk>S'\<rbrakk>, T) \<in> TRel"
      by simp
    from B1 B5 B6 have "\<lblot>\<alpha>\<rblot> = \<beta>"
      unfolding related_labels_def encLST_def getSourceLabel_def getTargetLabel_def
      by blast
    with B8 B9 show "\<exists>T. \<lbrakk>S\<rbrakk> \<midarrow>\<Zcat>\<lblot>\<alpha>\<rblot>\<rightarrow>Target* T \<and> (\<lbrakk>S'\<rbrakk>, T) \<in> TRel"
      by blast
  next
    fix S \<beta> T
    obtain \<beta>' where B1: "\<beta> \<in>TL \<langle>TargetTerm (\<lbrakk>S\<rbrakk>), \<beta>'\<rangle>"
      unfolding getTargetLabel_def
      by blast
    from A1 have B2: "(SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel"
      by simp
    assume "\<lbrakk>S\<rbrakk> \<midarrow>\<Zcat>\<beta>\<rightarrow>Target* T"
    with B1 have "TargetTerm (\<lbrakk>S\<rbrakk>) \<midarrow>\<Zcat>\<beta>'\<rightarrow>(STLCal Source Target)* (TargetTerm T)"
      using STLCal_weakLabelledSteps(2)[of "\<lbrakk>S\<rbrakk>" \<beta>' "TargetTerm T"]
      by blast
    with A4 B2 obtain \<alpha>' P' where B3: "SourceTerm S \<midarrow>\<Zcat>\<alpha>'\<rightarrow>(STLCal Source Target)* P'"
                              and B4: "(P', TargetTerm T) \<in> Rel"
                              and B5: "\<langle>SourceTerm S, \<alpha>'\<rangle> \<equiv>\<lparr>\<rparr> \<langle>TargetTerm (\<lbrakk>S\<rbrakk>), \<beta>'\<rangle>"
      by blast
    from B3 obtain \<alpha> S' where B6: "\<alpha> \<in>SL \<langle>SourceTerm S, \<alpha>'\<rangle>" and B7: "S' \<in>S P'"
                          and B8: "S \<midarrow>\<Zcat>\<alpha>\<rightarrow>Source* S'"
      using STLCal_weakLabelledSteps(1)[of S \<alpha>' P']
      by blast
    from A1 B7 have "(TargetTerm (\<lbrakk>S'\<rbrakk>), P') \<in> Rel"
      by simp
    with A3 B4 have "(TargetTerm (\<lbrakk>S'\<rbrakk>), TargetTerm T) \<in> Rel"
      using transD[of Rel "TargetTerm (\<lbrakk>S'\<rbrakk>)" P' "TargetTerm T"]
      by simp
    with A2 have B9: "(\<lbrakk>S'\<rbrakk>, T) \<in> TRel"
      by simp
    from B1 B5 B6 have "\<lblot>\<alpha>\<rblot> = \<beta>"
      unfolding related_labels_def encLST_def getSourceLabel_def getTargetLabel_def
      by blast
    with B8 B9 show "\<exists>\<alpha> S'. S \<midarrow>\<Zcat>\<alpha>\<rightarrow>Source* S' \<and> (\<lbrakk>S'\<rbrakk>, T) \<in> TRel \<and> \<lblot>\<alpha>\<rblot> = \<beta>"
      by blast
  qed
  moreover have "weak_labelled_bisimulation TRel Target"
  proof auto
    fix TP TQ \<alpha> TP'
    obtain \<alpha>' where B1: "\<alpha> \<in>TL \<langle>TargetTerm TP, \<alpha>'\<rangle>"
      unfolding getTargetLabel_def
      by blast
    assume "(TP, TQ) \<in> TRel"
    with A2 have B2: "(TargetTerm TP, TargetTerm TQ) \<in> Rel"
      by simp
    assume "TP \<midarrow>\<Zcat>\<alpha>\<rightarrow>Target* TP'"
    with B1 have "TargetTerm TP \<midarrow>\<Zcat>\<alpha>'\<rightarrow>(STLCal Source Target)* (TargetTerm TP')"
      using STLCal_weakLabelledSteps(2)[of TP \<alpha>' "TargetTerm TP'"]
      by blast
    with A4 B2 obtain \<beta>' Q' where B3: "TargetTerm TQ \<midarrow>\<Zcat>\<beta>'\<rightarrow>(STLCal Source Target)* Q'"
                              and B4: "(TargetTerm TP', Q') \<in> Rel"
                              and B5: "\<langle>TargetTerm TP, \<alpha>'\<rangle> \<equiv>\<lparr>\<rparr> \<langle>TargetTerm TQ, \<beta>'\<rangle>"
      by blast
    from B5 have "\<beta>' = \<alpha>'"
      using related_labels_equal[of "TargetTerm TP" \<alpha>' "TargetTerm TQ" \<beta>']
      by simp
    with B1 B3 obtain TQ' where B6: "TQ' \<in>T Q'" and B7: "TQ \<midarrow>\<Zcat>\<alpha>\<rightarrow>Target* TQ'"
      using STLCal_weakLabelledSteps(2)[of TQ \<alpha>' Q']
      unfolding getTargetLabel_def
      by blast
    from A2 B4 B6 have "(TP', TQ') \<in> TRel"
      by simp
    with B7 show "\<exists>TQ'. TQ \<midarrow>\<Zcat>\<alpha>\<rightarrow>Target* TQ' \<and> (TP', TQ') \<in> TRel"
      by blast
  next
    fix TP TQ \<alpha> TQ'
    obtain \<alpha>' where B1: "\<alpha> \<in>TL \<langle>TargetTerm TQ, \<alpha>'\<rangle>"
      unfolding getTargetLabel_def
      by blast
    assume "(TP, TQ) \<in> TRel"
    with A2 have B2: "(TargetTerm TP, TargetTerm TQ) \<in> Rel"
      by simp
    assume "TQ \<midarrow>\<Zcat>\<alpha>\<rightarrow>Target* TQ'"
    with B1 have "TargetTerm TQ \<midarrow>\<Zcat>\<alpha>'\<rightarrow>(STLCal Source Target)* (TargetTerm TQ')"
      using STLCal_weakLabelledSteps(2)[of TQ \<alpha>' "TargetTerm TQ'"]
      by blast
    with A4 B2 obtain \<beta>' P' where B3: "TargetTerm TP \<midarrow>\<Zcat>\<beta>'\<rightarrow>(STLCal Source Target)* P'"
                              and B4: "(P', TargetTerm TQ') \<in> Rel"
                              and B5: "\<langle>TargetTerm TP, \<beta>'\<rangle> \<equiv>\<lparr>\<rparr> \<langle>TargetTerm TQ, \<alpha>'\<rangle>"
      by blast
    from B5 have "\<beta>' = \<alpha>'"
      using related_labels_equal[of "TargetTerm TP" \<beta>' "TargetTerm TQ" \<alpha>']
      by simp
    with B1 B3 obtain TP' where B6: "TP' \<in>T P'" and B7: "TP \<midarrow>\<Zcat>\<alpha>\<rightarrow>Target* TP'"
      using STLCal_weakLabelledSteps(2)[of TP \<alpha>' P']
      unfolding getTargetLabel_def
      by blast
    from A2 B4 B6 have "(TP', TQ') \<in> TRel"
      by simp
    with B7 show "\<exists>TP'. TP \<midarrow>\<Zcat>\<alpha>\<rightarrow>Target* TP' \<and> (TP', TQ') \<in> TRel"
      by blast
  qed
  ultimately show "operational_corresponding_encL TRel \<and> weak_labelled_bisimulation TRel Target"
    by simp
qed

text \<open>An encoding is strong operational corresponding w.r.t a strong bisimulation on target terms
      TRel iff there exists a relation, like indRelRTPO, that relates at least all source terms
      and their literal translations, includes TRel, and is a strong bisimulation. Thus this
      variant of operational correspondence ensures that source terms and their translations are
      strongly bisimilar.\<close>

lemma (in encoding) SOC_iff_indRelRTPO_is_strong_reduction_bisimulation:
  fixes TRel :: "('procT \<times> 'procT) set"
  shows "(strongly_operational_corresponding (TRel\<^sup>*)
         \<and> strong_reduction_bisimulation (TRel\<^sup>+) Target)
         = strong_reduction_bisimulation (indRelRTPO TRel) (STCal Source Target)"
proof (rule iffI, erule conjE)
  assume ocorr: "strongly_operational_corresponding (TRel\<^sup>*)"
     and bisim: "strong_reduction_bisimulation (TRel\<^sup>+) Target"
  hence "strong_reduction_simulation (indRelRTPO TRel) (STCal Source Target)"
    using SOCom_iff_indRelRTPO_is_strong_reduction_simulation[where TRel="TRel"]
    by simp
  moreover from bisim have "strong_reduction_simulation ((TRel\<^sup>+)\<inverse>) Target"
    using strong_reduction_bisimulations_impl_inverse_is_simulation[where Rel="TRel\<^sup>+"]
    by simp
  with ocorr
  have "strong_reduction_simulation ((indRelRTPO TRel)\<inverse>) (STCal Source Target)"
    using SOSou_iff_inverse_of_indRelRTPO_is_strong_reduction_simulation[where TRel="TRel"]
    by simp
  ultimately show "strong_reduction_bisimulation (indRelRTPO TRel) (STCal Source Target)"
    using strong_reduction_simulations_impl_bisimulation[where Rel="indRelRTPO TRel"]
    by simp
next
  assume bisim: "strong_reduction_bisimulation (indRelRTPO TRel) (STCal Source Target)"
  hence "strongly_operational_complete (TRel\<^sup>*) \<and> strong_reduction_simulation (TRel\<^sup>+) Target"
    using SOCom_iff_indRelRTPO_is_strong_reduction_simulation[where TRel="TRel"]
    by simp
  moreover from bisim
  have "strong_reduction_simulation ((indRelRTPO TRel)\<inverse>) (STCal Source Target)"
    using strong_reduction_bisimulations_impl_inverse_is_simulation[where Rel="indRelRTPO TRel"]
    by simp
  hence "strongly_operational_sound (TRel\<^sup>*) \<and> strong_reduction_simulation ((TRel\<^sup>+)\<inverse>) Target"
    using SOSou_iff_inverse_of_indRelRTPO_is_strong_reduction_simulation[where TRel="TRel"]
    by simp
  ultimately show "strongly_operational_corresponding (TRel\<^sup>*)
                   \<and> strong_reduction_bisimulation (TRel\<^sup>+) Target"
    using strong_reduction_simulations_impl_bisimulation[where Rel="TRel\<^sup>+"]
    by simp
qed

lemma (in encodingLS_encL) SOC_iff_indRelRTPO_is_strong_labelled_bisimulation_encL:
  fixes TRel :: "('procT \<times> 'procT) set"
  shows "(strongly_operational_corresponding_encL (TRel\<^sup>*)
         \<and> strong_labelled_bisimulation (TRel\<^sup>+) Target)
         = strong_labelled_bisimulation_encL (indRelRTPO TRel)"
proof (rule iffI, erule conjE)
  assume ocorr: "strongly_operational_corresponding_encL (TRel\<^sup>*)"
     and bisim: "strong_labelled_bisimulation (TRel\<^sup>+) Target"
  hence "strong_labelled_simulation_encL (indRelRTPO TRel)"
    using SOCom_iff_indRelRTPO_is_strong_labelled_simulation_encL[where TRel="TRel"]
    by simp
  moreover from bisim have "strong_labelled_simulation ((TRel\<^sup>+)\<inverse>) Target"
    by simp
  with ocorr have "strong_labelled_simulation_encL ((indRelRTPO TRel)\<inverse>)"
    using SOSou_iff_inverse_of_indRelRTPO_is_strong_labelled_simulation_encL[where TRel="TRel"]
    by simp
  ultimately show "strong_labelled_bisimulation_encL (indRelRTPO TRel)"
    using strong_labelled_simulations_encL_impl_bisimulation[where Rel="indRelRTPO TRel"]
    by simp
next
  assume bisim: "strong_labelled_bisimulation_encL (indRelRTPO TRel)"
  hence "strongly_operational_complete_encL (TRel\<^sup>*) \<and> strong_labelled_simulation (TRel\<^sup>+) Target"
    using SOCom_iff_indRelRTPO_is_strong_labelled_simulation_encL[where TRel="TRel"]
    by simp
  moreover from bisim have "strong_labelled_simulation_encL ((indRelRTPO TRel)\<inverse>)"
    using strong_labelled_bisimulations_encL_impl_inverse_is_simulation[where
            Rel="indRelRTPO TRel"]
    by simp
  hence "strongly_operational_sound_encL (TRel\<^sup>*) \<and> strong_labelled_simulation ((TRel\<^sup>+)\<inverse>) Target"
    using SOSou_iff_inverse_of_indRelRTPO_is_strong_labelled_simulation_encL[where TRel="TRel"]
    by simp
  ultimately show "strongly_operational_corresponding_encL (TRel\<^sup>*)
                   \<and> strong_labelled_bisimulation (TRel\<^sup>+) Target"
    by simp
qed

lemma (in encoding) SOC_iff_strong_reduction_bisimulation:
  fixes TRel :: "('procT \<times> 'procT) set"
  shows "(strongly_operational_corresponding (TRel\<^sup>*)
         \<and> strong_reduction_bisimulation (TRel\<^sup>+) Target)
         = (\<exists>Rel. (\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel)
            \<and> (\<forall>T1 T2. (T1, T2) \<in> TRel \<longrightarrow> (TargetTerm T1, TargetTerm T2) \<in> Rel)
            \<and> (\<forall>T1 T2. (TargetTerm T1, TargetTerm T2) \<in> Rel \<longrightarrow> (T1, T2) \<in> TRel\<^sup>+)
            \<and> (\<forall>S T. (SourceTerm S, TargetTerm T) \<in> Rel \<longrightarrow> (\<lbrakk>S\<rbrakk>, T) \<in> TRel\<^sup>*)
            \<and> strong_reduction_bisimulation Rel (STCal Source Target))"
proof (rule iffI, erule conjE)
  have "\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> indRelRTPO TRel"
    by (simp add: indRelRTPO.encR)
  moreover have "\<forall>T1 T2. (T1, T2) \<in> TRel \<longrightarrow> TargetTerm T1 \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> TargetTerm T2"
    by (simp add: indRelRTPO.target)
  moreover have "\<forall>T1 T2. TargetTerm T1 \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> TargetTerm T2 \<longrightarrow> (T1, T2) \<in> TRel\<^sup>+"
    using indRelRTPO_to_TRel(4)[where TRel="TRel"]
    by simp
  moreover have "\<forall>S T. SourceTerm S \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> TargetTerm T \<longrightarrow> (\<lbrakk>S\<rbrakk>, T) \<in> TRel\<^sup>*"
    using indRelRTPO_to_TRel(2)[where TRel="TRel"] trans_closure_of_TRel_refl_cond
    by simp
  moreover assume "strongly_operational_corresponding (TRel\<^sup>*)"
              and "strong_reduction_bisimulation (TRel\<^sup>+) Target"
  hence "strong_reduction_bisimulation (indRelRTPO TRel) (STCal Source Target)"
    using SOC_iff_indRelRTPO_is_strong_reduction_bisimulation[where TRel="TRel"]
    by simp
  ultimately show "\<exists>Rel. (\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel)
                   \<and> (\<forall>T1 T2. (T1, T2) \<in> TRel \<longrightarrow> (TargetTerm T1, TargetTerm T2) \<in> Rel)
                   \<and> (\<forall>T1 T2. (TargetTerm T1, TargetTerm T2) \<in> Rel \<longrightarrow> (T1, T2) \<in> TRel\<^sup>+)
                   \<and> (\<forall>S T. (SourceTerm S, TargetTerm T) \<in> Rel \<longrightarrow> (\<lbrakk>S\<rbrakk>, T) \<in> TRel\<^sup>*)
                   \<and> strong_reduction_bisimulation Rel (STCal Source Target)"
    by blast
next
  assume "\<exists>Rel. (\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel)
          \<and> (\<forall>T1 T2. (T1, T2) \<in> TRel \<longrightarrow> (TargetTerm T1, TargetTerm T2) \<in> Rel)
          \<and> (\<forall>T1 T2. (TargetTerm T1, TargetTerm T2) \<in> Rel \<longrightarrow> (T1, T2) \<in> TRel\<^sup>+)
          \<and> (\<forall>S T. (SourceTerm S, TargetTerm T) \<in> Rel \<longrightarrow> (\<lbrakk>S\<rbrakk>, T) \<in> TRel\<^sup>*)
          \<and> strong_reduction_bisimulation Rel (STCal Source Target)"
  from this obtain Rel where A1: "\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel"
   and A2: "\<forall>T1 T2. (T1, T2) \<in> TRel \<longrightarrow> (TargetTerm T1, TargetTerm T2) \<in> Rel"
   and A3: "\<forall>T1 T2. (TargetTerm T1, TargetTerm T2) \<in> Rel \<longrightarrow> (T1, T2) \<in> TRel\<^sup>+"
   and A4: "\<forall>S T. (SourceTerm S, TargetTerm T) \<in> Rel \<longrightarrow> (\<lbrakk>S\<rbrakk>, T) \<in> TRel\<^sup>*"
   and A5: "strong_reduction_bisimulation Rel (STCal Source Target)"
    by blast
  hence "strongly_operational_complete (TRel\<^sup>*)
         \<and> strong_reduction_simulation (TRel\<^sup>+) Target"
    using SOCom_iff_strong_reduction_simulation[where TRel="TRel"]
    by blast
  moreover from A5 have "strong_reduction_simulation (Rel\<inverse>) (STCal Source Target)"
    using strong_reduction_bisimulations_impl_inverse_is_simulation[where Rel="Rel"]
    by simp
  with A1 A2 A3 A4 have "strongly_operational_sound (TRel\<^sup>*)
                         \<and> strong_reduction_simulation ((TRel\<^sup>+)\<inverse>) Target"
    using SOSou_iff_strong_reduction_simulation[where TRel="TRel"]
    by blast
  ultimately show "strongly_operational_corresponding (TRel\<^sup>*)
                   \<and> strong_reduction_bisimulation (TRel\<^sup>+) Target"
    using strong_reduction_simulations_impl_bisimulation[where Rel="TRel\<^sup>+"]
    by simp
qed

lemma (in encodingLS_encL) SOC_iff_strong_labelled_bisimulation_encL:
  fixes TRel :: "('procT \<times> 'procT) set"
  shows "(strongly_operational_corresponding_encL (TRel\<^sup>*)
         \<and> strong_labelled_bisimulation (TRel\<^sup>+) Target)
         = (\<exists>Rel. (\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel)
            \<and> (\<forall>T1 T2. (T1, T2) \<in> TRel \<longrightarrow> (TargetTerm T1, TargetTerm T2) \<in> Rel)
            \<and> (\<forall>T1 T2. (TargetTerm T1, TargetTerm T2) \<in> Rel \<longrightarrow> (T1, T2) \<in> TRel\<^sup>+)
            \<and> (\<forall>S T. (SourceTerm S, TargetTerm T) \<in> Rel \<longrightarrow> (\<lbrakk>S\<rbrakk>, T) \<in> TRel\<^sup>*)
            \<and> strong_labelled_bisimulation_encL Rel)"
proof (rule iffI, erule conjE)
  have "\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> indRelRTPO TRel"
    by (simp add: indRelRTPO.encR)
  moreover have "\<forall>T1 T2. (T1, T2) \<in> TRel \<longrightarrow> TargetTerm T1 \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> TargetTerm T2"
    by (simp add: indRelRTPO.target)
  moreover have "\<forall>T1 T2. TargetTerm T1 \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> TargetTerm T2 \<longrightarrow> (T1, T2) \<in> TRel\<^sup>+"
    using indRelRTPO_to_TRel(4)[where TRel="TRel"]
    by simp
  moreover have "\<forall>S T. SourceTerm S \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> TargetTerm T \<longrightarrow> (\<lbrakk>S\<rbrakk>, T) \<in> TRel\<^sup>*"
    using indRelRTPO_to_TRel(2)[where TRel="TRel"] trans_closure_of_TRel_refl_cond
    by simp
  moreover assume "strongly_operational_corresponding_encL (TRel\<^sup>*)"
              and "strong_labelled_bisimulation (TRel\<^sup>+) Target"
  hence "strong_labelled_bisimulation_encL (indRelRTPO TRel)"
    using SOC_iff_indRelRTPO_is_strong_labelled_bisimulation_encL[where TRel="TRel"]
    by simp
  ultimately show "\<exists>Rel. (\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel)
                   \<and> (\<forall>T1 T2. (T1, T2) \<in> TRel \<longrightarrow> (TargetTerm T1, TargetTerm T2) \<in> Rel)
                   \<and> (\<forall>T1 T2. (TargetTerm T1, TargetTerm T2) \<in> Rel \<longrightarrow> (T1, T2) \<in> TRel\<^sup>+)
                   \<and> (\<forall>S T. (SourceTerm S, TargetTerm T) \<in> Rel \<longrightarrow> (\<lbrakk>S\<rbrakk>, T) \<in> TRel\<^sup>*)
                   \<and> strong_labelled_bisimulation_encL Rel"
    by blast
next
  assume "\<exists>Rel. (\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel)
          \<and> (\<forall>T1 T2. (T1, T2) \<in> TRel \<longrightarrow> (TargetTerm T1, TargetTerm T2) \<in> Rel)
          \<and> (\<forall>T1 T2. (TargetTerm T1, TargetTerm T2) \<in> Rel \<longrightarrow> (T1, T2) \<in> TRel\<^sup>+)
          \<and> (\<forall>S T. (SourceTerm S, TargetTerm T) \<in> Rel \<longrightarrow> (\<lbrakk>S\<rbrakk>, T) \<in> TRel\<^sup>*)
          \<and> strong_labelled_bisimulation_encL Rel"
  from this obtain Rel where A1: "\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel"
   and A2: "\<forall>T1 T2. (T1, T2) \<in> TRel \<longrightarrow> (TargetTerm T1, TargetTerm T2) \<in> Rel"
   and A3: "\<forall>T1 T2. (TargetTerm T1, TargetTerm T2) \<in> Rel \<longrightarrow> (T1, T2) \<in> TRel\<^sup>+"
   and A4: "\<forall>S T. (SourceTerm S, TargetTerm T) \<in> Rel \<longrightarrow> (\<lbrakk>S\<rbrakk>, T) \<in> TRel\<^sup>*"
   and A5: "strong_labelled_bisimulation_encL Rel"
    by blast
  hence "strongly_operational_complete_encL (TRel\<^sup>*)
         \<and> strong_labelled_simulation (TRel\<^sup>+) Target"
    using SOCom_iff_strong_labelled_simulation_encL[where TRel="TRel"]
    by blast
  moreover from A5 have "strong_labelled_simulation_encL (Rel\<inverse>)"
    using strong_labelled_bisimulations_encL_impl_inverse_is_simulation[where Rel="Rel"]
    by simp
  with A1 A2 A3 A4 have "strongly_operational_sound_encL (TRel\<^sup>*)
                         \<and> strong_labelled_simulation ((TRel\<^sup>+)\<inverse>) Target"
    using SOSou_iff_strong_labelled_simulation_encL[where TRel="TRel"]
    by blast
  ultimately show "strongly_operational_corresponding_encL (TRel\<^sup>*)
                   \<and> strong_labelled_bisimulation (TRel\<^sup>+) Target"
    by simp
qed

lemma (in encoding) SOC_wrt_preorder_iff_strong_reduction_bisimulation:
  fixes TRel :: "('procT \<times> 'procT) set"
  shows "(strongly_operational_corresponding TRel \<and> preorder TRel
         \<and> strong_reduction_bisimulation TRel Target)
         = (\<exists>Rel. (\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel)
            \<and> TRel = {(T1, T2). (TargetTerm T1, TargetTerm T2) \<in> Rel}
            \<and> (\<forall>S T. (SourceTerm S, TargetTerm T) \<in> Rel \<longrightarrow> (\<lbrakk>S\<rbrakk>, T) \<in> TRel)
            \<and> preorder Rel
            \<and> strong_reduction_bisimulation Rel (STCal Source Target))"
proof (rule iffI, erule conjE, erule conjE, erule conjE)
  assume A1: "strongly_operational_complete TRel" and A2: "strongly_operational_sound TRel"
     and A3:"preorder TRel" and A4: "strong_reduction_bisimulation TRel Target"
  from A3 have A5: "TRel\<^sup>+ = TRel"
    using trancl_id[of TRel]
    unfolding preorder_on_def
    by blast
  with A3 have "TRel\<^sup>* = TRel"
    using reflcl_trancl[of TRel]
    unfolding preorder_on_def refl_on_def
    by blast
  with A1 A2 have "strongly_operational_corresponding (TRel\<^sup>*)"
    by simp
  moreover from A4 A5 have "strong_reduction_bisimulation (TRel\<^sup>+) Target"
    by simp
  ultimately
  have "strong_reduction_bisimulation (indRelRTPO TRel) (STCal Source Target)"
    using SOC_iff_indRelRTPO_is_strong_reduction_bisimulation[where TRel="TRel"]
    by blast
  moreover have "\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> indRelRTPO TRel"
    by (simp add: indRelRTPO.encR)
  moreover
  have "TRel = {(T1, T2). (TargetTerm T1, TargetTerm T2) \<in> indRelRTPO TRel}"
  proof auto
    fix TP TQ
    assume "(TP, TQ) \<in> TRel"
    thus "TargetTerm TP \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> TargetTerm TQ"
      by (rule indRelRTPO.target)
  next
    fix TP TQ
    assume "TargetTerm TP \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> TargetTerm TQ"
    with A3 show "(TP, TQ) \<in> TRel"
      using indRelRTPO_to_TRel(4)[where TRel="TRel"] trancl_id[of TRel]
      unfolding preorder_on_def
      by blast
  qed
  moreover from A3
  have "\<forall>S T. (SourceTerm S, TargetTerm T) \<in> indRelRTPO TRel \<longrightarrow> (\<lbrakk>S\<rbrakk>, T) \<in> TRel\<^sup>+"
    using indRelRTPO_to_TRel(2)[where TRel="TRel"] reflcl_trancl[of TRel]
          trans_closure_of_TRel_refl_cond[where TRel="TRel"]
    unfolding preorder_on_def refl_on_def
    by blast
  with A3 have "\<forall>S T. (SourceTerm S, TargetTerm T) \<in> indRelRTPO TRel \<longrightarrow> (\<lbrakk>S\<rbrakk>, T) \<in> TRel"
    using trancl_id[of TRel]
    unfolding preorder_on_def
    by blast
  moreover from A3 have "refl (indRelRTPO TRel)"
    unfolding preorder_on_def
    by (simp add: indRelRTPO_refl)
  moreover have "trans (indRelRTPO TRel)"
    using indRelRTPO.trans
    unfolding trans_def
    by blast
  ultimately show "\<exists>Rel. (\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel)
                   \<and> TRel = {(T1, T2). (TargetTerm T1, TargetTerm T2) \<in> Rel}
                   \<and> (\<forall>S T. (SourceTerm S, TargetTerm T) \<in> Rel \<longrightarrow> (\<lbrakk>S\<rbrakk>, T) \<in> TRel)
                   \<and> preorder Rel
                   \<and> strong_reduction_bisimulation Rel (STCal Source Target)"
    unfolding preorder_on_def
    by auto
next
  assume "\<exists>Rel. (\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel)
          \<and> TRel = {(T1, T2). (TargetTerm T1, TargetTerm T2) \<in> Rel}
          \<and> (\<forall>S T. (SourceTerm S, TargetTerm T) \<in> Rel \<longrightarrow> (\<lbrakk>S\<rbrakk>, T) \<in> TRel)
          \<and> preorder Rel
          \<and> strong_reduction_bisimulation Rel (STCal Source Target)"
  from this obtain Rel where B1: "\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel"
   and B2: "TRel = {(T1, T2). (TargetTerm T1, TargetTerm T2) \<in> Rel}"
   and B3: "\<forall>S T. (SourceTerm S, TargetTerm T) \<in> Rel \<longrightarrow> (\<lbrakk>S\<rbrakk>, T) \<in> TRel" and B4: "preorder Rel"
   and B5: "strong_reduction_bisimulation Rel (STCal Source Target)"
    by blast
  from B2 B4 have B6: "refl TRel"
    unfolding preorder_on_def refl_on_def
    by blast
  from B2 B4 have B7: "trans TRel"
    unfolding trans_def preorder_on_def
    by blast
  hence B8: "TRel\<^sup>+ = TRel"
    by (rule trancl_id)
  with B6 have B9: "TRel\<^sup>* = TRel"
    using reflcl_trancl[of TRel]
    unfolding refl_on_def
    by blast
  with B3 have "\<forall>S T. (SourceTerm S, TargetTerm T) \<in> Rel \<longrightarrow> (\<lbrakk>S\<rbrakk>, T) \<in> TRel\<^sup>*"
    by simp
  moreover from B2 B8 have "\<forall>T1 T2. (T1, T2) \<in> TRel \<longrightarrow> (TargetTerm T1, TargetTerm T2) \<in> Rel"
    and "\<forall>T1 T2. (TargetTerm T1, TargetTerm T2) \<in> Rel \<longrightarrow> (T1, T2) \<in> TRel\<^sup>+"
    by auto
  ultimately have "\<exists>Rel. (\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel)
   \<and> (\<forall>T1 T2. (T1, T2) \<in> TRel \<longrightarrow> (TargetTerm T1, TargetTerm T2) \<in> Rel)
   \<and> (\<forall>T1 T2. (TargetTerm T1, TargetTerm T2) \<in> Rel \<longrightarrow> (T1, T2) \<in> TRel\<^sup>+)
   \<and> (\<forall>S T. (SourceTerm S, TargetTerm T) \<in> Rel \<longrightarrow> (\<lbrakk>S\<rbrakk>, T) \<in> TRel\<^sup>*)
   \<and> strong_reduction_bisimulation Rel (STCal Source Target)"
    using B1 B5
    by blast
  hence "strongly_operational_corresponding (TRel\<^sup>*) \<and> strong_reduction_bisimulation (TRel\<^sup>+) Target"
    using SOC_iff_strong_reduction_bisimulation[where TRel="TRel"]
    by simp
  with B8 B9
  have "strongly_operational_corresponding TRel \<and> strong_reduction_bisimulation TRel Target"
    by simp
  moreover from B6 B7 have "preorder TRel"
    unfolding preorder_on_def by simp
  ultimately show "strongly_operational_corresponding TRel \<and> preorder TRel
                   \<and> strong_reduction_bisimulation TRel Target"
    by blast
qed

lemma (in encodingLS_encL) SOC_wrt_preorder_iff_strong_labelled_bisimulation_encL:
  fixes TRel :: "('procT \<times> 'procT) set"
  shows "(strongly_operational_corresponding_encL TRel \<and> preorder TRel
         \<and> strong_labelled_bisimulation TRel Target)
         = (\<exists>Rel. (\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel)
            \<and> TRel = {(T1, T2). (TargetTerm T1, TargetTerm T2) \<in> Rel}
            \<and> (\<forall>S T. (SourceTerm S, TargetTerm T) \<in> Rel \<longrightarrow> (\<lbrakk>S\<rbrakk>, T) \<in> TRel)
            \<and> preorder Rel
            \<and> strong_labelled_bisimulation_encL Rel)"
proof (rule iffI, erule conjE, erule conjE, erule conjE)
  assume A1: "strongly_operational_complete_encL TRel"
     and A2: "strongly_operational_sound_encL TRel"
     and A3: "preorder TRel" and A4: "strong_labelled_bisimulation TRel Target"
  from A3 have A5: "TRel\<^sup>+ = TRel"
    using trancl_id[of TRel]
    unfolding preorder_on_def
    by blast
  with A3 have "TRel\<^sup>* = TRel"
    using reflcl_trancl[of TRel]
    unfolding preorder_on_def refl_on_def
    by blast
  with A1 A2 have "strongly_operational_corresponding_encL (TRel\<^sup>*)"
    by simp
  moreover from A4 A5 have "strong_labelled_bisimulation (TRel\<^sup>+) Target"
    by simp
  ultimately
  have "strong_labelled_bisimulation_encL (indRelRTPO TRel)"
    using SOC_iff_indRelRTPO_is_strong_labelled_bisimulation_encL[where TRel="TRel"]
    by blast
  moreover have "\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> indRelRTPO TRel"
    by (simp add: indRelRTPO.encR)
  moreover have "TRel = {(T1, T2). (TargetTerm T1, TargetTerm T2) \<in> indRelRTPO TRel}"
  proof auto
    fix TP TQ
    assume "(TP, TQ) \<in> TRel"
    thus "TargetTerm TP \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> TargetTerm TQ"
      by (rule indRelRTPO.target)
  next
    fix TP TQ
    assume "TargetTerm TP \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> TargetTerm TQ"
    with A3 show "(TP, TQ) \<in> TRel"
      using indRelRTPO_to_TRel(4)[where TRel="TRel"] trancl_id[of TRel]
      unfolding preorder_on_def
      by blast
  qed
  moreover from A3
  have "\<forall>S T. (SourceTerm S, TargetTerm T) \<in> indRelRTPO TRel \<longrightarrow> (\<lbrakk>S\<rbrakk>, T) \<in> TRel\<^sup>+"
    using indRelRTPO_to_TRel(2)[where TRel="TRel"] reflcl_trancl[of TRel]
          trans_closure_of_TRel_refl_cond[where TRel="TRel"]
    unfolding preorder_on_def refl_on_def
    by blast
  with A3 have "\<forall>S T. (SourceTerm S, TargetTerm T) \<in> indRelRTPO TRel \<longrightarrow> (\<lbrakk>S\<rbrakk>, T) \<in> TRel"
    using trancl_id[of TRel]
    unfolding preorder_on_def
    by blast
  moreover from A3 have "refl (indRelRTPO TRel)"
    unfolding preorder_on_def
    by (simp add: indRelRTPO_refl)
  moreover have "trans (indRelRTPO TRel)"
    using indRelRTPO.trans
    unfolding trans_def
    by blast
  ultimately show "\<exists>Rel. (\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel)
                   \<and> TRel = {(T1, T2). (TargetTerm T1, TargetTerm T2) \<in> Rel}
                   \<and> (\<forall>S T. (SourceTerm S, TargetTerm T) \<in> Rel \<longrightarrow> (\<lbrakk>S\<rbrakk>, T) \<in> TRel)
                   \<and> preorder Rel
                   \<and> strong_labelled_bisimulation_encL Rel"
    unfolding preorder_on_def
    by auto
next
  assume "\<exists>Rel. (\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel)
          \<and> TRel = {(T1, T2). (TargetTerm T1, TargetTerm T2) \<in> Rel}
          \<and> (\<forall>S T. (SourceTerm S, TargetTerm T) \<in> Rel \<longrightarrow> (\<lbrakk>S\<rbrakk>, T) \<in> TRel)
          \<and> preorder Rel
          \<and> strong_labelled_bisimulation_encL Rel"
  then obtain Rel where B1: "\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel"
   and B2: "TRel = {(T1, T2). (TargetTerm T1, TargetTerm T2) \<in> Rel}"
   and B3: "\<forall>S T. (SourceTerm S, TargetTerm T) \<in> Rel \<longrightarrow> (\<lbrakk>S\<rbrakk>, T) \<in> TRel" and B4: "preorder Rel"
   and B5: "strong_labelled_bisimulation_encL Rel"
    by blast
  from B2 B4 have B6: "refl TRel"
    unfolding preorder_on_def refl_on_def
    by blast
  from B2 B4 have B7: "trans TRel"
    unfolding trans_def preorder_on_def
    by blast
  hence B8: "TRel\<^sup>+ = TRel"
    by (rule trancl_id)
  with B6 have B9: "TRel\<^sup>* = TRel"
    using reflcl_trancl[of TRel]
    unfolding refl_on_def
    by blast
  with B3 have "\<forall>S T. (SourceTerm S, TargetTerm T) \<in> Rel \<longrightarrow> (\<lbrakk>S\<rbrakk>, T) \<in> TRel\<^sup>*"
    by simp
  moreover from B2 B8 have "\<forall>T1 T2. (T1, T2) \<in> TRel \<longrightarrow> (TargetTerm T1, TargetTerm T2) \<in> Rel"
    and "\<forall>T1 T2. (TargetTerm T1, TargetTerm T2) \<in> Rel \<longrightarrow> (T1, T2) \<in> TRel\<^sup>+"
    by auto
  ultimately have "\<exists>Rel. (\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel)
   \<and> (\<forall>T1 T2. (T1, T2) \<in> TRel \<longrightarrow> (TargetTerm T1, TargetTerm T2) \<in> Rel)
   \<and> (\<forall>T1 T2. (TargetTerm T1, TargetTerm T2) \<in> Rel \<longrightarrow> (T1, T2) \<in> TRel\<^sup>+)
   \<and> (\<forall>S T. (SourceTerm S, TargetTerm T) \<in> Rel \<longrightarrow> (\<lbrakk>S\<rbrakk>, T) \<in> TRel\<^sup>*)
   \<and> strong_labelled_bisimulation_encL Rel"
    using B1 B5
    by blast
  hence "strongly_operational_corresponding_encL (TRel\<^sup>*) \<and>
         strong_labelled_bisimulation (TRel\<^sup>+) Target"
    using SOC_iff_strong_labelled_bisimulation_encL[where TRel="TRel"]
    by simp
  with B8 B9 have "strongly_operational_corresponding_encL TRel \<and>
                   strong_labelled_bisimulation TRel Target"
    by simp
  moreover from B6 B7 have "preorder TRel"
    unfolding preorder_on_def by simp
  ultimately show "strongly_operational_corresponding_encL TRel \<and> preorder TRel
                   \<and> strong_labelled_bisimulation TRel Target"
    by blast
qed

lemma (in encoding) SOC_wrt_TRel_iff_strong_reduction_bisimulation:
  shows "(\<exists>TRel. strongly_operational_corresponding (TRel\<^sup>*)
         \<and> strong_reduction_bisimulation (TRel\<^sup>+) Target)
         = (\<exists>Rel. (\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel)
            \<and> (\<forall>S T. (SourceTerm S, TargetTerm T) \<in> Rel
               \<longrightarrow> (TargetTerm (\<lbrakk>S\<rbrakk>), TargetTerm T) \<in> Rel\<^sup>=)
            \<and> strong_reduction_bisimulation Rel (STCal Source Target))"
proof (rule iffI)
  assume "\<exists>TRel. strongly_operational_corresponding (TRel\<^sup>*)
          \<and> strong_reduction_bisimulation (TRel\<^sup>+) Target"
  from this obtain TRel where "strongly_operational_corresponding (TRel\<^sup>*)"
                          and "strong_reduction_bisimulation (TRel\<^sup>+) Target"
    by blast
  hence "strong_reduction_bisimulation (indRelRTPO TRel) (STCal Source Target)"
    using SOC_iff_indRelRTPO_is_strong_reduction_bisimulation[where TRel="TRel"]
    by simp
  moreover have "\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> indRelRTPO TRel"
    by (simp add: indRelRTPO.encR)
  moreover have "\<forall>S T. (SourceTerm S, TargetTerm T) \<in> (indRelRTPO TRel)
                 \<longrightarrow> (TargetTerm (\<lbrakk>S\<rbrakk>), TargetTerm T) \<in> (indRelRTPO TRel)\<^sup>="
    using indRelRTPO_relates_source_target[where TRel="TRel"]
    by simp
  ultimately show "\<exists>Rel. (\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel)
   \<and> (\<forall>S T. (SourceTerm S, TargetTerm T) \<in> Rel \<longrightarrow> (TargetTerm (\<lbrakk>S\<rbrakk>), TargetTerm T) \<in> Rel\<^sup>=)
   \<and> strong_reduction_bisimulation Rel (STCal Source Target)"
    by blast
next
  assume "\<exists>Rel. (\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel)
   \<and> (\<forall>S T. (SourceTerm S, TargetTerm T) \<in> Rel \<longrightarrow> (TargetTerm (\<lbrakk>S\<rbrakk>), TargetTerm T) \<in> Rel\<^sup>=)
   \<and> strong_reduction_bisimulation Rel (STCal Source Target)"
  from this obtain Rel where A1: "\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel"
                         and A2: "\<forall>S T. (SourceTerm S, TargetTerm T) \<in> Rel
                                  \<longrightarrow> (TargetTerm (\<lbrakk>S\<rbrakk>), TargetTerm T) \<in> Rel\<^sup>="
                         and A3: "strong_reduction_bisimulation Rel (STCal Source Target)"
    by blast
  from A2 obtain TRel where "\<forall>T1 T2. (T1, T2) \<in> TRel \<longrightarrow> (TargetTerm T1, TargetTerm T2) \<in> Rel"
   and "\<forall>T1 T2. (TargetTerm T1, TargetTerm T2) \<in> Rel \<longrightarrow> (T1, T2) \<in> TRel\<^sup>+"
   and "\<forall>S T. (SourceTerm S, TargetTerm T) \<in> Rel \<longrightarrow> (\<lbrakk>S\<rbrakk>, T) \<in> TRel\<^sup>*"
    using target_relation_from_source_target_relation[where Rel="Rel"]
    by blast
  with A1 A3 have "\<exists>Rel. (\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel)
                   \<and> (\<forall>T1 T2. (T1, T2) \<in> TRel \<longrightarrow> (TargetTerm T1, TargetTerm T2) \<in> Rel)
                   \<and> (\<forall>T1 T2. (TargetTerm T1, TargetTerm T2) \<in> Rel \<longrightarrow> (T1, T2) \<in> TRel\<^sup>+)
                   \<and> (\<forall>S T. (SourceTerm S, TargetTerm T) \<in> Rel \<longrightarrow> (\<lbrakk>S\<rbrakk>, T) \<in> TRel\<^sup>*)
                   \<and> strong_reduction_bisimulation Rel (STCal Source Target)"
    by blast
  hence "strongly_operational_corresponding (TRel\<^sup>*)
         \<and> strong_reduction_bisimulation (TRel\<^sup>+) Target"
    using SOC_iff_strong_reduction_bisimulation[where TRel="TRel"]
    by simp
  thus "\<exists>TRel. strongly_operational_corresponding (TRel\<^sup>*)
        \<and> strong_reduction_bisimulation (TRel\<^sup>+) Target"
    by blast
qed

lemma (in encodingLS_encL) SOC_wrt_TRel_iff_strong_labelled_bisimulation_encL:
  shows "(\<exists>TRel. strongly_operational_corresponding_encL (TRel\<^sup>*)
         \<and> strong_labelled_bisimulation (TRel\<^sup>+) Target)
         = (\<exists>Rel. (\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel)
            \<and> (\<forall>S T. (SourceTerm S, TargetTerm T) \<in> Rel
               \<longrightarrow> (TargetTerm (\<lbrakk>S\<rbrakk>), TargetTerm T) \<in> Rel\<^sup>=)
            \<and> strong_labelled_bisimulation_encL Rel)"
proof (rule iffI)
  assume "\<exists>TRel. strongly_operational_corresponding_encL (TRel\<^sup>*)
          \<and> strong_labelled_bisimulation (TRel\<^sup>+) Target"
  from this obtain TRel where "strongly_operational_corresponding_encL (TRel\<^sup>*)"
                          and "strong_labelled_bisimulation (TRel\<^sup>+) Target"
    by blast
  hence "strong_labelled_bisimulation_encL (indRelRTPO TRel)"
    using SOC_iff_indRelRTPO_is_strong_labelled_bisimulation_encL[where TRel="TRel"]
    by simp
  moreover have "\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> indRelRTPO TRel"
    by (simp add: indRelRTPO.encR)
  moreover have "\<forall>S T. (SourceTerm S, TargetTerm T) \<in> (indRelRTPO TRel)
                 \<longrightarrow> (TargetTerm (\<lbrakk>S\<rbrakk>), TargetTerm T) \<in> (indRelRTPO TRel)\<^sup>="
    using indRelRTPO_relates_source_target[where TRel="TRel"]
    by simp
  ultimately show "\<exists>Rel. (\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel)
   \<and> (\<forall>S T. (SourceTerm S, TargetTerm T) \<in> Rel \<longrightarrow> (TargetTerm (\<lbrakk>S\<rbrakk>), TargetTerm T) \<in> Rel\<^sup>=)
   \<and> strong_labelled_bisimulation_encL Rel"
    by blast
next
  assume "\<exists>Rel. (\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel)
   \<and> (\<forall>S T. (SourceTerm S, TargetTerm T) \<in> Rel \<longrightarrow> (TargetTerm (\<lbrakk>S\<rbrakk>), TargetTerm T) \<in> Rel\<^sup>=)
   \<and> strong_labelled_bisimulation_encL Rel"
  from this obtain Rel where A1: "\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel"
                         and A2: "\<forall>S T. (SourceTerm S, TargetTerm T) \<in> Rel
                                  \<longrightarrow> (TargetTerm (\<lbrakk>S\<rbrakk>), TargetTerm T) \<in> Rel\<^sup>="
                         and A3: "strong_labelled_bisimulation_encL Rel"
    by blast
  from A2 obtain TRel where "\<forall>T1 T2. (T1, T2) \<in> TRel \<longrightarrow> (TargetTerm T1, TargetTerm T2) \<in> Rel"
   and "\<forall>T1 T2. (TargetTerm T1, TargetTerm T2) \<in> Rel \<longrightarrow> (T1, T2) \<in> TRel\<^sup>+"
   and "\<forall>S T. (SourceTerm S, TargetTerm T) \<in> Rel \<longrightarrow> (\<lbrakk>S\<rbrakk>, T) \<in> TRel\<^sup>*"
    using target_relation_from_source_target_relation[where Rel="Rel"]
    by blast
  with A1 A3 have "\<exists>Rel. (\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel)
                   \<and> (\<forall>T1 T2. (T1, T2) \<in> TRel \<longrightarrow> (TargetTerm T1, TargetTerm T2) \<in> Rel)
                   \<and> (\<forall>T1 T2. (TargetTerm T1, TargetTerm T2) \<in> Rel \<longrightarrow> (T1, T2) \<in> TRel\<^sup>+)
                   \<and> (\<forall>S T. (SourceTerm S, TargetTerm T) \<in> Rel \<longrightarrow> (\<lbrakk>S\<rbrakk>, T) \<in> TRel\<^sup>*)
                   \<and> strong_labelled_bisimulation_encL Rel"
    by blast
  hence "strongly_operational_corresponding_encL (TRel\<^sup>*)
         \<and> strong_labelled_bisimulation (TRel\<^sup>+) Target"
    using SOC_iff_strong_labelled_bisimulation_encL[where TRel="TRel"]
    by simp
  thus "\<exists>TRel. strongly_operational_corresponding_encL (TRel\<^sup>*)
        \<and> strong_labelled_bisimulation (TRel\<^sup>+) Target"
    by blast
qed

lemma (in encoding) SOC_wrt_equivalence_iff_indRelTEQ_strong_reduction_bisimulation:
  fixes TRel :: "('procT \<times> 'procT) set"
  assumes eqT: "equivalence TRel"
  shows "(strongly_operational_corresponding TRel \<and> strong_reduction_bisimulation TRel Target)
         \<longleftrightarrow> strong_reduction_bisimulation (indRelTEQ TRel) (STCal Source Target)"
proof (rule iffI, erule conjE)
  assume oc:     "strongly_operational_corresponding TRel"
     and bisimT: "strong_reduction_bisimulation TRel Target"
  show "strong_reduction_bisimulation (indRelTEQ TRel) (STCal Source Target)"
  proof auto
    fix P Q P'
    assume "P \<sim>\<lbrakk>\<cdot>\<rbrakk>T<TRel> Q" and "P \<longmapsto>(STCal Source Target) P'"
    thus "\<exists>Q'. Q \<longmapsto>(STCal Source Target) Q' \<and> P' \<sim>\<lbrakk>\<cdot>\<rbrakk>T<TRel> Q'"
    proof (induct arbitrary: P')
      case (encR S)
      assume "SourceTerm S \<longmapsto>(STCal Source Target) P'"
      from this obtain S' where A1: "S \<longmapsto>Source S'" and A2: "S' \<in>S P'"
        by (auto simp add: STCal_step(1))
      from A1 oc obtain T where A3: "\<lbrakk>S\<rbrakk> \<longmapsto>Target T" and A4: "(\<lbrakk>S'\<rbrakk>, T) \<in> TRel"
        by blast
      from A3 have "TargetTerm (\<lbrakk>S\<rbrakk>) \<longmapsto>(STCal Source Target) (TargetTerm T)"
        by (simp add: STCal_step(2))
      moreover have "P' \<sim>\<lbrakk>\<cdot>\<rbrakk>T<TRel> TargetTerm T"
      proof -
        from A2 have "P' \<sim>\<lbrakk>\<cdot>\<rbrakk>T<TRel> TargetTerm (\<lbrakk>S'\<rbrakk>)"
          by (simp add: indRelTEQ.encR)
        moreover from A4 have "TargetTerm (\<lbrakk>S'\<rbrakk>) \<sim>\<lbrakk>\<cdot>\<rbrakk>T<TRel> TargetTerm T"
          by (rule indRelTEQ.target)
        ultimately show "P' \<sim>\<lbrakk>\<cdot>\<rbrakk>T<TRel> TargetTerm T"
          by (rule indRelTEQ.trans)
      qed
      ultimately show "\<exists>Q'. TargetTerm (\<lbrakk>S\<rbrakk>) \<longmapsto>(STCal Source Target) Q' \<and> P' \<sim>\<lbrakk>\<cdot>\<rbrakk>T<TRel> Q'"
        by blast
    next
      case (encL S)
      assume "TargetTerm (\<lbrakk>S\<rbrakk>) \<longmapsto>(STCal Source Target) P'"
      from this obtain T where B1: "\<lbrakk>S\<rbrakk> \<longmapsto>Target T" and B2: "T \<in>T P'"
        by (auto simp add: STCal_step(2))
      from B1 oc obtain S' where B3: "S \<longmapsto>Source S'" and B4: "(\<lbrakk>S'\<rbrakk>, T) \<in> TRel"
        by blast
      from B3 have "SourceTerm S \<longmapsto>(STCal Source Target) (SourceTerm S')"
        by (simp add: STCal_step(1))
      moreover have "P' \<sim>\<lbrakk>\<cdot>\<rbrakk>T<TRel> SourceTerm S'"
      proof -
        from B4 eqT have "(T, \<lbrakk>S'\<rbrakk>) \<in> TRel"
          unfolding equiv_def sym_def
          by blast
        with B2 have "P' \<sim>\<lbrakk>\<cdot>\<rbrakk>T<TRel> TargetTerm (\<lbrakk>S'\<rbrakk>)"
          by (simp add: indRelTEQ.target)
        moreover have "TargetTerm (\<lbrakk>S'\<rbrakk>) \<sim>\<lbrakk>\<cdot>\<rbrakk>T<TRel> SourceTerm S'"
          by (rule indRelTEQ.encL)
        ultimately show "P' \<sim>\<lbrakk>\<cdot>\<rbrakk>T<TRel> SourceTerm S'"
          by (rule indRelTEQ.trans)
      qed
      ultimately show "\<exists>Q'. SourceTerm S \<longmapsto>(STCal Source Target) Q' \<and> P' \<sim>\<lbrakk>\<cdot>\<rbrakk>T<TRel> Q'"
        by blast
    next
      case (target T1 T2)
      assume "TargetTerm T1 \<longmapsto>(STCal Source Target) P'"
      from this obtain T1' where C1: "T1 \<longmapsto>Target T1'" and C2: "T1' \<in>T P'"
        by (auto simp add: STCal_step(2))
      assume "(T1, T2) \<in> TRel"
      with C1 bisimT obtain T2' where C3: "T2 \<longmapsto>Target T2'" and C4: "(T1', T2') \<in> TRel"
        by blast
      from C3 have "TargetTerm T2 \<longmapsto>(STCal Source Target) (TargetTerm T2')"
        by (simp add: STCal_step(2))
      moreover from C2 C4 have "P' \<sim>\<lbrakk>\<cdot>\<rbrakk>T<TRel> TargetTerm T2'"
        by (simp add: indRelTEQ.target)
      ultimately show "\<exists>Q'. TargetTerm T2 \<longmapsto>(STCal Source Target) Q' \<and> P' \<sim>\<lbrakk>\<cdot>\<rbrakk>T<TRel> Q'"
        by blast
    next
      case (trans P Q R)
      assume "P \<longmapsto>(STCal Source Target) P'"
         and "\<And>P'. P \<longmapsto>(STCal Source Target) P'
              \<Longrightarrow> \<exists>Q'. Q \<longmapsto>(STCal Source Target) Q' \<and> P' \<sim>\<lbrakk>\<cdot>\<rbrakk>T<TRel> Q'"
      from this obtain Q' where D1: "Q \<longmapsto>(STCal Source Target) Q'" and D2: "P' \<sim>\<lbrakk>\<cdot>\<rbrakk>T<TRel> Q'"
        by blast
      assume "\<And>Q'. Q \<longmapsto>(STCal Source Target) Q'
              \<Longrightarrow> \<exists>R'. R \<longmapsto>(STCal Source Target) R' \<and> Q' \<sim>\<lbrakk>\<cdot>\<rbrakk>T<TRel> R'"
      with D1 obtain R' where D3: "R \<longmapsto>(STCal Source Target) R'" and D4: "Q' \<sim>\<lbrakk>\<cdot>\<rbrakk>T<TRel> R'"
        by blast
      from D2 D4 have "P' \<sim>\<lbrakk>\<cdot>\<rbrakk>T<TRel> R'"
        by (rule indRelTEQ.trans)
      with D3 show "\<exists>R'. R \<longmapsto>(STCal Source Target) R' \<and> P' \<sim>\<lbrakk>\<cdot>\<rbrakk>T<TRel> R'"
        by blast
    qed
  next
    fix P Q Q'
    assume "P \<sim>\<lbrakk>\<cdot>\<rbrakk>T<TRel> Q" and "Q \<longmapsto>(STCal Source Target) Q'"
    thus "\<exists>P'. P \<longmapsto>(STCal Source Target) P' \<and> P' \<sim>\<lbrakk>\<cdot>\<rbrakk>T<TRel> Q'"
    proof (induct arbitrary: Q')
      case (encR S)
      assume "TargetTerm (\<lbrakk>S\<rbrakk>) \<longmapsto>(STCal Source Target) Q'"
      from this obtain T where E1: "\<lbrakk>S\<rbrakk> \<longmapsto>Target T" and E2: "T \<in>T Q'"
        by (auto simp add: STCal_step(2))
      from E1 oc obtain S' where E3: "S \<longmapsto>Source S'" and E4: "(\<lbrakk>S'\<rbrakk>, T) \<in> TRel"
        by blast
      from E3 have "SourceTerm S \<longmapsto>(STCal Source Target) (SourceTerm S')"
        by (simp add: STCal_step(1))
      moreover have "SourceTerm S' \<sim>\<lbrakk>\<cdot>\<rbrakk>T<TRel> Q'"
      proof -
        have "SourceTerm S' \<sim>\<lbrakk>\<cdot>\<rbrakk>T<TRel> TargetTerm (\<lbrakk>S'\<rbrakk>)"
          by (rule indRelTEQ.encR)
        moreover from E2 E4 have "TargetTerm (\<lbrakk>S'\<rbrakk>) \<sim>\<lbrakk>\<cdot>\<rbrakk>T<TRel> Q'"
          by (simp add: indRelTEQ.target)
        ultimately show "SourceTerm S' \<sim>\<lbrakk>\<cdot>\<rbrakk>T<TRel> Q'"
          by (rule indRelTEQ.trans)
      qed
      ultimately show "\<exists>P'. SourceTerm S \<longmapsto>(STCal Source Target) P' \<and> P' \<sim>\<lbrakk>\<cdot>\<rbrakk>T<TRel> Q'"
        by blast
    next
      case (encL S)
      assume "SourceTerm S \<longmapsto>(STCal Source Target) Q'"
      from this obtain S' where F1: "S \<longmapsto>Source S'" and F2: "S' \<in>S Q'"
        by (auto simp add: STCal_step(1))
      from F1 oc obtain T where F3: "\<lbrakk>S\<rbrakk> \<longmapsto>Target T" and F4: "(\<lbrakk>S'\<rbrakk>, T) \<in> TRel"
        by blast
      from F3 have "TargetTerm (\<lbrakk>S\<rbrakk>) \<longmapsto>(STCal Source Target) (TargetTerm T)"
        by (simp add: STCal_step(2))
      moreover have "TargetTerm T \<sim>\<lbrakk>\<cdot>\<rbrakk>T<TRel> Q'"
      proof -
        from F4 eqT have "(T, \<lbrakk>S'\<rbrakk>) \<in> TRel"
          unfolding equiv_def sym_def
          by blast
        hence "TargetTerm T \<sim>\<lbrakk>\<cdot>\<rbrakk>T<TRel> TargetTerm (\<lbrakk>S'\<rbrakk>)"
          by (rule indRelTEQ.target)
        moreover from F2 have "TargetTerm (\<lbrakk>S'\<rbrakk>) \<sim>\<lbrakk>\<cdot>\<rbrakk>T<TRel> Q'"
          by (simp add: indRelTEQ.encL)
        ultimately show "TargetTerm T \<sim>\<lbrakk>\<cdot>\<rbrakk>T<TRel> Q'"
          by (rule indRelTEQ.trans)
      qed
      ultimately show "\<exists>P'. TargetTerm (\<lbrakk>S\<rbrakk>) \<longmapsto>(STCal Source Target) P' \<and> P' \<sim>\<lbrakk>\<cdot>\<rbrakk>T<TRel> Q'"
        by blast
    next
      case (target T1 T2)
      assume "TargetTerm T2 \<longmapsto>(STCal Source Target) Q'"
      from this obtain T2' where G1: "T2 \<longmapsto>Target T2'" and G2: "T2' \<in>T Q'"
        by (auto simp add: STCal_step(2))
      assume "(T1, T2) \<in> TRel"
      with G1 bisimT obtain T1' where G3: "T1 \<longmapsto>Target T1'" and G4: "(T1', T2') \<in> TRel"
        by blast
      from G3 have "TargetTerm T1 \<longmapsto>(STCal Source Target) (TargetTerm T1')"
        by (simp add: STCal_step(2))
      moreover from G2 G4 have "TargetTerm T1' \<sim>\<lbrakk>\<cdot>\<rbrakk>T<TRel> Q'"
        by (simp add: indRelTEQ.target)
      ultimately show "\<exists>P'. TargetTerm T1 \<longmapsto>(STCal Source Target) P' \<and> P' \<sim>\<lbrakk>\<cdot>\<rbrakk>T<TRel> Q'"
        by blast
    next
      case (trans P Q R R')
      assume "R \<longmapsto>(STCal Source Target) R'"
         and "\<And>R'. R \<longmapsto>(STCal Source Target) R'
              \<Longrightarrow> \<exists>Q'. Q \<longmapsto>(STCal Source Target) Q' \<and> Q' \<sim>\<lbrakk>\<cdot>\<rbrakk>T<TRel> R'"
      from this obtain Q' where H1: "Q \<longmapsto>(STCal Source Target) Q'" and H2: "Q' \<sim>\<lbrakk>\<cdot>\<rbrakk>T<TRel> R'"
        by blast
      assume "\<And>Q'. Q \<longmapsto>(STCal Source Target) Q'
              \<Longrightarrow> \<exists>P'. P \<longmapsto>(STCal Source Target) P' \<and> P' \<sim>\<lbrakk>\<cdot>\<rbrakk>T<TRel> Q'"
      with H1 obtain P' where H3: "P \<longmapsto>(STCal Source Target) P'" and H4: "P' \<sim>\<lbrakk>\<cdot>\<rbrakk>T<TRel> Q'"
        by blast
      from H4 H2 have "P' \<sim>\<lbrakk>\<cdot>\<rbrakk>T<TRel> R'"
        by (rule indRelTEQ.trans)
      with H3 show "\<exists>P'. P \<longmapsto>(STCal Source Target) P' \<and> P' \<sim>\<lbrakk>\<cdot>\<rbrakk>T<TRel> R'"
        by blast
    qed
  qed
next
  assume bisim: "strong_reduction_bisimulation (indRelTEQ TRel) (STCal Source Target)"
  have "strongly_operational_corresponding TRel"
  proof auto
    fix S S'
    have "SourceTerm S \<sim>\<lbrakk>\<cdot>\<rbrakk>T<TRel> TargetTerm (\<lbrakk>S\<rbrakk>)"
      by (rule indRelTEQ.encR)
    moreover assume "S \<longmapsto>Source S'"
    hence "SourceTerm S \<longmapsto>(STCal Source Target) (SourceTerm S')"
      by (simp add: STCal_step(1))
    ultimately obtain Q' where I1: "TargetTerm (\<lbrakk>S\<rbrakk>) \<longmapsto>(STCal Source Target) Q'"
                           and I2: "SourceTerm S' \<sim>\<lbrakk>\<cdot>\<rbrakk>T<TRel> Q'"
      using bisim
      by blast
    from I1 obtain T where I3: "\<lbrakk>S\<rbrakk> \<longmapsto>Target T" and I4: "T \<in>T Q'"
      by (auto simp add: STCal_step(2))
    from eqT have "TRel\<^sup>* = TRel"
      using reflcl_trancl[of TRel] trancl_id[of TRel]
      unfolding equiv_def refl_on_def
      by auto
    with I2 I4 have "(\<lbrakk>S'\<rbrakk>, T) \<in> TRel"
      using indRelTEQ_to_TRel(2)[where TRel="TRel"]
            trans_closure_of_TRel_refl_cond[where TRel="TRel"]
      by simp
    with I3 show "\<exists>T. \<lbrakk>S\<rbrakk> \<longmapsto>Target T \<and> (\<lbrakk>S'\<rbrakk>, T) \<in> TRel"
      by blast
  next
    fix S T
    have "SourceTerm S \<sim>\<lbrakk>\<cdot>\<rbrakk>T<TRel> TargetTerm (\<lbrakk>S\<rbrakk>)"
      by (rule indRelTEQ.encR)
    moreover assume "\<lbrakk>S\<rbrakk> \<longmapsto>Target T"
    hence "TargetTerm (\<lbrakk>S\<rbrakk>) \<longmapsto>(STCal Source Target) (TargetTerm T)"
      by (simp add: STCal_step(2))
    ultimately obtain Q' where J1: "SourceTerm S \<longmapsto>(STCal Source Target) Q'"
                           and J2: "Q' \<sim>\<lbrakk>\<cdot>\<rbrakk>T<TRel> TargetTerm T"
      using bisim
      by blast
    from J1 obtain S' where J3: "S \<longmapsto>Source S'" and J4: "S' \<in>S Q'"
      by (auto simp add: STCal_step(1))
    from eqT have "TRel\<^sup>* = TRel"
      using reflcl_trancl[of TRel] trancl_id[of TRel]
      unfolding equiv_def refl_on_def
      by auto
    with J2 J4 have "(\<lbrakk>S'\<rbrakk>, T) \<in> TRel"
      using indRelTEQ_to_TRel(2)[where TRel="TRel"]
            trans_closure_of_TRel_refl_cond[where TRel="TRel"]
      by blast
    with J3 show "\<exists>S'. S \<longmapsto>Source S' \<and> (\<lbrakk>S'\<rbrakk>, T) \<in> TRel"
      by blast
  qed
  moreover have "strong_reduction_bisimulation TRel Target"
  proof -
    from eqT have "TRel\<^sup>* = TRel"
      using reflcl_trancl[of TRel] trancl_id[of TRel]
      unfolding equiv_def refl_on_def
      by auto
    with bisim show "strong_reduction_bisimulation TRel Target"
      using indRelTEQ_impl_TRel_is_strong_reduction_bisimulation[where TRel="TRel"]
      by simp
  qed
  ultimately
  show "strongly_operational_corresponding TRel \<and> strong_reduction_bisimulation TRel Target"
    by simp
qed

lemma (in encodingLS_encL) SOC_wrt_equivalence_iff_indRelTEQ_strong_labelled_bisimulation_encL:
  fixes TRel :: "('procT \<times> 'procT) set"
  assumes eqT: "equivalence TRel"
      and inj: "inj encL"
  shows "(strongly_operational_corresponding_encL TRel \<and> strong_labelled_bisimulation TRel Target)
         \<longleftrightarrow> strong_labelled_bisimulation_encL (indRelTEQ TRel)"
proof (rule iffI, erule conjE)
  assume oc:     "strongly_operational_corresponding_encL TRel"
     and bisimT: "strong_labelled_bisimulation TRel Target"
  show "strong_labelled_bisimulation_encL (indRelTEQ TRel)"
  proof auto
    fix P Q \<alpha> P'
    assume "P \<sim>\<lbrakk>\<cdot>\<rbrakk>T<TRel> Q" and "P \<midarrow>\<alpha>\<rightarrow>(STLCal Source Target) P'"
    thus "\<exists>\<beta> Q'. Q \<midarrow>\<beta>\<rightarrow>(STLCal Source Target) Q' \<and> P' \<sim>\<lbrakk>\<cdot>\<rbrakk>T<TRel> Q' \<and> \<langle>P, \<alpha>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>Q, \<beta>\<rangle>"
    proof (induct arbitrary: \<alpha> P')
      case (encR S)
      assume "SourceTerm S \<midarrow>\<alpha>\<rightarrow>(STLCal Source Target) P'"
      from this obtain \<alpha>' S' where A1: "\<alpha>' \<in>SL \<langle>SourceTerm S, \<alpha>\<rangle>" and A2: "S' \<in>S P'"
                               and A3: "S \<midarrow>\<alpha>'\<rightarrow>Source S'"
        using STLCal_labelledStep(1)[of S \<alpha> P']
        by blast
      from oc A3 obtain \<beta>' T where A4: "\<lbrakk>S\<rbrakk> \<midarrow>\<beta>'\<rightarrow>Target T" and A5: "(\<lbrakk>S'\<rbrakk>, T) \<in> TRel"
                               and A6: "\<lblot>\<alpha>'\<rblot> = \<beta>'"
        by blast
      obtain \<beta> where A7: "\<beta>' \<in>TL \<langle>TargetTerm (\<lbrakk>S\<rbrakk>), \<beta>\<rangle>"
        unfolding getTargetLabel_def
        by blast
      with A4 have A8: "TargetTerm (\<lbrakk>S\<rbrakk>) \<midarrow>\<beta>\<rightarrow>(STLCal Source Target) (TargetTerm T)"
        using STLCal_labelledStep(2)[of "\<lbrakk>S\<rbrakk>" \<beta> "TargetTerm T"]
        by blast
      moreover have "P' \<sim>\<lbrakk>\<cdot>\<rbrakk>T<TRel> TargetTerm T"
      proof -
        from A2 have "P' \<sim>\<lbrakk>\<cdot>\<rbrakk>T<TRel> TargetTerm (\<lbrakk>S'\<rbrakk>)"
          by (simp add: indRelTEQ.encR)
        moreover from A5 have "TargetTerm (\<lbrakk>S'\<rbrakk>) \<sim>\<lbrakk>\<cdot>\<rbrakk>T<TRel> TargetTerm T"
          using indRelTEQ.target[of "\<lbrakk>S'\<rbrakk>" T "TRel"]
          by simp
        ultimately show "P' \<sim>\<lbrakk>\<cdot>\<rbrakk>T<TRel> TargetTerm T"
          by (rule indRelTEQ.trans)
      qed
      moreover from A1 A6 A7 have "\<langle>SourceTerm S, \<alpha>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>TargetTerm (\<lbrakk>S\<rbrakk>), \<beta>\<rangle>"
        unfolding related_labels_def encLST_def
        by blast
      ultimately show "\<exists>\<beta> Q'. TargetTerm (\<lbrakk>S\<rbrakk>) \<midarrow>\<beta>\<rightarrow>(STLCal Source Target) Q' \<and>
                       P' \<sim>\<lbrakk>\<cdot>\<rbrakk>T<TRel> Q' \<and> \<langle>SourceTerm S, \<alpha>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>TargetTerm (\<lbrakk>S\<rbrakk>), \<beta>\<rangle>"
        by blast
    next
      case (encL S)
      assume "TargetTerm (\<lbrakk>S\<rbrakk>) \<midarrow>\<alpha>\<rightarrow>(STLCal Source Target) P'"
      then obtain \<alpha>' T where A1: "\<alpha>' \<in>TL \<langle>TargetTerm (\<lbrakk>S\<rbrakk>), \<alpha>\<rangle>" and A2: "T \<in>T P'"
                         and A3: "\<lbrakk>S\<rbrakk> \<midarrow>\<alpha>'\<rightarrow>Target T"
        using STLCal_labelledStep(2)[of "\<lbrakk>S\<rbrakk>" \<alpha> P']
        by blast
      from oc A3 obtain \<beta>' S' where A4: "S \<midarrow>\<beta>'\<rightarrow>Source S'" and A5: "(\<lbrakk>S'\<rbrakk>, T) \<in> TRel"
                                and A6: "\<lblot>\<beta>'\<rblot> = \<alpha>'"
        by blast
      obtain \<beta> where A7: "\<beta>' \<in>SL \<langle>SourceTerm S, \<beta>\<rangle>"
        unfolding getSourceLabel_def
        by blast
      with A4 have "SourceTerm S \<midarrow>\<beta>\<rightarrow>(STLCal Source Target) (SourceTerm S')"
        using STLCal_labelledStep(1)[of S \<beta> "SourceTerm S'"]
        by blast
      moreover have "P' \<sim>\<lbrakk>\<cdot>\<rbrakk>T<TRel> SourceTerm S'"
      proof -
        from A5 eqT have "(T, \<lbrakk>S'\<rbrakk>) \<in> TRel"
          unfolding equiv_def sym_def
          by blast
        with A2 have "P' \<sim>\<lbrakk>\<cdot>\<rbrakk>T<TRel> TargetTerm (\<lbrakk>S'\<rbrakk>)"
          by (simp add: indRelTEQ.target)
        moreover have "TargetTerm (\<lbrakk>S'\<rbrakk>) \<sim>\<lbrakk>\<cdot>\<rbrakk>T<TRel> SourceTerm S'"
          by (rule indRelTEQ.encL)
        ultimately show "P' \<sim>\<lbrakk>\<cdot>\<rbrakk>T<TRel> SourceTerm S'"
          by (rule indRelTEQ.trans)
      qed
      moreover from A1 A6 A7 have "\<lparr>SourceTerm S, \<beta>\<rparr>\<mapsto>\<langle>TargetTerm (\<lbrakk>S\<rbrakk>), \<alpha>\<rangle>"
        unfolding encLST_def
        by blast
      hence "\<langle>TargetTerm (\<lbrakk>S\<rbrakk>), \<alpha>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>SourceTerm S, \<beta>\<rangle>"
        unfolding related_labels_def
        by simp
      ultimately show "\<exists>\<beta> Q'. SourceTerm S \<midarrow>\<beta>\<rightarrow>(STLCal Source Target) Q' \<and> P' \<sim>\<lbrakk>\<cdot>\<rbrakk>T<TRel> Q' \<and>
                       \<langle>TargetTerm (\<lbrakk>S\<rbrakk>), \<alpha>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>SourceTerm S, \<beta>\<rangle>"
        by blast
    next
      case (target T1 T2)
      assume "TargetTerm T1 \<midarrow>\<alpha>\<rightarrow>(STLCal Source Target) P'"
      from this obtain \<alpha>' T1' where C1: "\<alpha>' \<in>TL \<langle>TargetTerm T1, \<alpha>\<rangle>" and C2: "T1' \<in>T P'"
                                and C3: "T1 \<midarrow>\<alpha>'\<rightarrow>Target T1'"
        using STLCal_labelledStep(2)[of T1 \<alpha> P']
        by blast
      assume "(T1, T2) \<in> TRel"
      with bisimT C3 obtain T2' where C4: "T2 \<midarrow>\<alpha>'\<rightarrow>Target T2'" and C5: "(T1', T2') \<in> TRel"
        by blast
      from C1 C4 have "TargetTerm T2 \<midarrow>\<alpha>\<rightarrow>(STLCal Source Target) (TargetTerm T2')"
        using STLCal_labelledStep(2)[of T2 \<alpha> "TargetTerm T2'"]
        unfolding getTargetLabel_def
        by blast
      moreover from C2 C5 have "P' \<sim>\<lbrakk>\<cdot>\<rbrakk>T<TRel> TargetTerm T2'"
        by (simp add: indRelTEQ.target)
      moreover have "\<langle>TargetTerm T1, \<alpha>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>TargetTerm T2, \<alpha>\<rangle>"
        unfolding related_labels_def
        by simp
      ultimately show "\<exists>\<beta> Q'. TargetTerm T2 \<midarrow>\<beta>\<rightarrow>(STLCal Source Target) Q' \<and> P' \<sim>\<lbrakk>\<cdot>\<rbrakk>T<TRel> Q' \<and>
                       \<langle>TargetTerm T1, \<alpha>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>TargetTerm T2, \<beta>\<rangle>"
        by blast
    next
      case (trans P Q R)
      assume "P \<midarrow>\<alpha>\<rightarrow>(STLCal Source Target) P'"
         and "\<And>\<alpha> P'. P \<midarrow>\<alpha>\<rightarrow>(STLCal Source Target) P' \<Longrightarrow>
              \<exists>\<beta> Q'. Q \<midarrow>\<beta>\<rightarrow>(STLCal Source Target) Q' \<and> P' \<sim>\<lbrakk>\<cdot>\<rbrakk>T<TRel> Q' \<and> \<langle>P, \<alpha>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>Q, \<beta>\<rangle>"
      then obtain \<beta> Q' where A1: "Q \<midarrow>\<beta>\<rightarrow>(STLCal Source Target) Q'" and A2: "P' \<sim>\<lbrakk>\<cdot>\<rbrakk>T<TRel> Q'"
                         and A3: "\<langle>P, \<alpha>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>Q, \<beta>\<rangle>"
        by blast
      assume "\<And>\<beta> Q'. Q \<midarrow>\<beta>\<rightarrow>(STLCal Source Target) Q' \<Longrightarrow>
              \<exists>\<gamma> R'. R \<midarrow>\<gamma>\<rightarrow>(STLCal Source Target) R' \<and> Q' \<sim>\<lbrakk>\<cdot>\<rbrakk>T<TRel> R' \<and> \<langle>Q, \<beta>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>R, \<gamma>\<rangle>"
      with A1 obtain \<gamma> R' where A4: "R \<midarrow>\<gamma>\<rightarrow>(STLCal Source Target) R'" and A5: "Q' \<sim>\<lbrakk>\<cdot>\<rbrakk>T<TRel> R'"
                            and A6: "\<langle>Q, \<beta>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>R, \<gamma>\<rangle>"
        by blast
      from A2 A5 have A7: "P' \<sim>\<lbrakk>\<cdot>\<rbrakk>T<TRel> R'"
        by (rule indRelTEQ.trans)
      from inj A3 A6 have "\<langle>P, \<alpha>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>R, \<gamma>\<rangle>"
        using related_labels_trans_inj[of P \<alpha> Q \<beta> R \<gamma>]
        by simp
      with A4 A7
      show "\<exists>\<gamma> R'. R \<midarrow>\<gamma>\<rightarrow>(STLCal Source Target) R' \<and> P' \<sim>\<lbrakk>\<cdot>\<rbrakk>T<TRel> R' \<and> \<langle>P, \<alpha>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>R, \<gamma>\<rangle>"
        by blast
    qed
  next
    fix P Q \<beta> Q'
    assume "P \<sim>\<lbrakk>\<cdot>\<rbrakk>T<TRel> Q" and "Q \<midarrow>\<beta>\<rightarrow>(STLCal Source Target) Q'"
    thus "\<exists>\<alpha> P'. P \<midarrow>\<alpha>\<rightarrow>(STLCal Source Target) P' \<and> P' \<sim>\<lbrakk>\<cdot>\<rbrakk>T<TRel> Q' \<and> \<langle>P, \<alpha>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>Q, \<beta>\<rangle>"
    proof (induct arbitrary: \<beta> Q')
      case (encR S)
      assume "TargetTerm (\<lbrakk>S\<rbrakk>) \<midarrow>\<beta>\<rightarrow>(STLCal Source Target) Q'"
      then obtain \<beta>' T where A1: "\<beta>' \<in>TL \<langle>TargetTerm (\<lbrakk>S\<rbrakk>), \<beta>\<rangle>" and A2: "T \<in>T Q'"
                         and A3: "\<lbrakk>S\<rbrakk> \<midarrow>\<beta>'\<rightarrow>Target T"
        using STLCal_labelledStep(2)[of "\<lbrakk>S\<rbrakk>" \<beta> Q']
        by blast
      from oc A3 obtain \<alpha>' S' where A4: "S \<midarrow>\<alpha>'\<rightarrow>Source S'" and A5: "(\<lbrakk>S'\<rbrakk>, T) \<in> TRel"
                                and A6: "\<lblot>\<alpha>'\<rblot> = \<beta>'"
        by blast
      obtain \<alpha> where A7: "\<alpha>' \<in>SL \<langle>SourceTerm S, \<alpha>\<rangle>"
        unfolding getSourceLabel_def
        by blast
      with A4 have "SourceTerm S \<midarrow>\<alpha>\<rightarrow>(STLCal Source Target) (SourceTerm S')"
        using STLCal_labelledStep(1)[of S \<alpha> "SourceTerm S'"]
        by blast
      moreover have "SourceTerm S' \<sim>\<lbrakk>\<cdot>\<rbrakk>T<TRel> Q'"
      proof -
        from A2 A5 have "TargetTerm (\<lbrakk>S'\<rbrakk>) \<sim>\<lbrakk>\<cdot>\<rbrakk>T<TRel> Q'"
          by (simp add: indRelTEQ.target)
        moreover have "SourceTerm S' \<sim>\<lbrakk>\<cdot>\<rbrakk>T<TRel> TargetTerm (\<lbrakk>S'\<rbrakk>)"
          by (rule indRelTEQ.encR)
        ultimately show "SourceTerm S' \<sim>\<lbrakk>\<cdot>\<rbrakk>T<TRel> Q'"
          using indRelTEQ.trans[of "SourceTerm S'" "TargetTerm (\<lbrakk>S'\<rbrakk>)" TRel Q']
          by simp
      qed
      moreover from A1 A6 A7 have "\<lparr>SourceTerm S, \<alpha>\<rparr>\<mapsto>\<langle>TargetTerm (\<lbrakk>S\<rbrakk>), \<beta>\<rangle>"
        unfolding encLST_def
        by blast
      hence "\<langle>SourceTerm S, \<alpha>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>TargetTerm (\<lbrakk>S\<rbrakk>), \<beta>\<rangle>"
        unfolding related_labels_def
        by simp
      ultimately show "\<exists>\<alpha> P'. SourceTerm S \<midarrow>\<alpha>\<rightarrow>(STLCal Source Target) P' \<and> P' \<sim>\<lbrakk>\<cdot>\<rbrakk>T<TRel> Q' \<and>
                       \<langle>SourceTerm S, \<alpha>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>TargetTerm (\<lbrakk>S\<rbrakk>), \<beta>\<rangle>"
        by blast
    next
      case (encL S)
      assume "SourceTerm S \<midarrow>\<beta>\<rightarrow>(STLCal Source Target) Q'"
      from this obtain \<beta>' S' where A1: "\<beta>' \<in>SL \<langle>SourceTerm S, \<beta>\<rangle>" and A2: "S' \<in>S Q'"
                               and A3: "S \<midarrow>\<beta>'\<rightarrow>Source S'"
        using STLCal_labelledStep(1)[of S \<beta> Q']
        by blast
      from oc A3 obtain \<alpha>' T where A4: "\<lbrakk>S\<rbrakk> \<midarrow>\<alpha>'\<rightarrow>Target T" and A5: "(\<lbrakk>S'\<rbrakk>, T) \<in> TRel"
                               and A6: "\<lblot>\<beta>'\<rblot> = \<alpha>'"
        by blast
      obtain \<alpha> where A7: "\<alpha>' \<in>TL \<langle>TargetTerm (\<lbrakk>S\<rbrakk>), \<alpha>\<rangle>"
        unfolding getTargetLabel_def
        by blast
      with A4 have A8: "TargetTerm (\<lbrakk>S\<rbrakk>) \<midarrow>\<alpha>\<rightarrow>(STLCal Source Target) (TargetTerm T)"
        using STLCal_labelledStep(2)[of "\<lbrakk>S\<rbrakk>" \<alpha> "TargetTerm T"]
        by blast
      moreover have "TargetTerm T \<sim>\<lbrakk>\<cdot>\<rbrakk>T<TRel> Q'"
      proof -
        from A5 eqT have "(T, \<lbrakk>S'\<rbrakk>) \<in> TRel"
          unfolding equiv_def sym_def
          by blast
        hence "TargetTerm T \<sim>\<lbrakk>\<cdot>\<rbrakk>T<TRel> TargetTerm (\<lbrakk>S'\<rbrakk>)"
          using indRelTEQ.target[of T "\<lbrakk>S'\<rbrakk>" "TRel"]
          by simp
        moreover from A2 have "TargetTerm (\<lbrakk>S'\<rbrakk>) \<sim>\<lbrakk>\<cdot>\<rbrakk>T<TRel> Q'"
          by (simp add: indRelTEQ.encL)
        ultimately show "TargetTerm T \<sim>\<lbrakk>\<cdot>\<rbrakk>T<TRel> Q'"
          by (rule indRelTEQ.trans)
      qed
      moreover from A1 A6 A7 have "\<langle>TargetTerm (\<lbrakk>S\<rbrakk>), \<alpha>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>SourceTerm S, \<beta>\<rangle>"
        unfolding related_labels_def encLST_def
        by blast
      ultimately show "\<exists>\<alpha> P'. TargetTerm (\<lbrakk>S\<rbrakk>) \<midarrow>\<alpha>\<rightarrow>(STLCal Source Target) P' \<and>
                       P' \<sim>\<lbrakk>\<cdot>\<rbrakk>T<TRel> Q' \<and> \<langle>TargetTerm (\<lbrakk>S\<rbrakk>), \<alpha>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>SourceTerm S, \<beta>\<rangle>"
        by blast
    next
      case (target T1 T2)
      assume "TargetTerm T2 \<midarrow>\<beta>\<rightarrow>(STLCal Source Target) Q'"
      from this obtain \<beta>' T2' where C1: "\<beta>' \<in>TL \<langle>TargetTerm T2, \<beta>\<rangle>" and C2: "T2' \<in>T Q'"
                                and C3: "T2 \<midarrow>\<beta>'\<rightarrow>Target T2'"
        using STLCal_labelledStep(2)[of T2 \<beta> Q']
        by blast
      assume "(T1, T2) \<in> TRel"
      with bisimT C3 obtain T1' where C4: "T1 \<midarrow>\<beta>'\<rightarrow>Target T1'" and C5: "(T1', T2') \<in> TRel"
        by blast
      from C1 C4 have "TargetTerm T1 \<midarrow>\<beta>\<rightarrow>(STLCal Source Target) (TargetTerm T1')"
        using STLCal_labelledStep(2)[of T1 \<beta> "TargetTerm T1'"]
        unfolding getTargetLabel_def
        by blast
      moreover from C2 C5 have "TargetTerm T1' \<sim>\<lbrakk>\<cdot>\<rbrakk>T<TRel> Q'"
        by (simp add: indRelTEQ.target)
      moreover have "\<langle>TargetTerm T1, \<beta>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>TargetTerm T2, \<beta>\<rangle>"
        unfolding related_labels_def
        by simp
      ultimately show "\<exists>\<alpha> P'. TargetTerm T1 \<midarrow>\<alpha>\<rightarrow>(STLCal Source Target) P' \<and> P' \<sim>\<lbrakk>\<cdot>\<rbrakk>T<TRel> Q' \<and>
                       \<langle>TargetTerm T1, \<alpha>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>TargetTerm T2, \<beta>\<rangle>"
        by blast
    next
      case (trans R Q P \<alpha> P')
      assume "P \<midarrow>\<alpha>\<rightarrow>(STLCal Source Target) P'"
         and "\<And>\<alpha> P'. P \<midarrow>\<alpha>\<rightarrow>(STLCal Source Target) P' \<Longrightarrow>
              \<exists>\<beta> Q'. Q \<midarrow>\<beta>\<rightarrow>(STLCal Source Target) Q' \<and> Q' \<sim>\<lbrakk>\<cdot>\<rbrakk>T<TRel> P' \<and> \<langle>Q, \<beta>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>P, \<alpha>\<rangle>"
      then obtain \<beta> Q' where A1: "Q \<midarrow>\<beta>\<rightarrow>(STLCal Source Target) Q'" and A2: "Q' \<sim>\<lbrakk>\<cdot>\<rbrakk>T<TRel> P'"
                         and A3: "\<langle>Q, \<beta>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>P, \<alpha>\<rangle>"
        by blast
      assume "\<And>\<beta> Q'. Q \<midarrow>\<beta>\<rightarrow>(STLCal Source Target) Q' \<Longrightarrow>
              \<exists>\<gamma> R'. R \<midarrow>\<gamma>\<rightarrow>(STLCal Source Target) R' \<and> R' \<sim>\<lbrakk>\<cdot>\<rbrakk>T<TRel> Q' \<and> \<langle>R, \<gamma>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>Q, \<beta>\<rangle>"
      with A1 obtain \<gamma> R' where A4: "R \<midarrow>\<gamma>\<rightarrow>(STLCal Source Target) R'" and A5: "R' \<sim>\<lbrakk>\<cdot>\<rbrakk>T<TRel> Q'"
                            and A6: "\<langle>R, \<gamma>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>Q, \<beta>\<rangle>"
        by blast
      from A2 A5 have A7: "R' \<sim>\<lbrakk>\<cdot>\<rbrakk>T<TRel> P'"
        using indRelTEQ.trans[of R' Q' TRel P']
        by simp
      from inj A3 A6 have "\<langle>R, \<gamma>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>P, \<alpha>\<rangle>"
        using related_labels_trans_inj[of R \<gamma> Q \<beta> P \<alpha>]
        by simp
      with A4 A7
      show "\<exists>\<gamma> R'. R \<midarrow>\<gamma>\<rightarrow>(STLCal Source Target) R' \<and> R' \<sim>\<lbrakk>\<cdot>\<rbrakk>T<TRel> P' \<and> \<langle>R, \<gamma>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>P, \<alpha>\<rangle>"
        by blast
    qed
  qed
next
  assume bisim: "strong_labelled_bisimulation_encL (indRelTEQ TRel)"
  have "strongly_operational_corresponding_encL TRel"
  proof auto
    fix S \<alpha> S'
    obtain \<alpha>' where A1: "\<alpha> \<in>SL \<langle>SourceTerm S, \<alpha>'\<rangle>"
      unfolding getSourceLabel_def
      by blast
    have A2: "SourceTerm S \<sim>\<lbrakk>\<cdot>\<rbrakk>T<TRel> TargetTerm (\<lbrakk>S\<rbrakk>)"
      by (rule indRelTEQ.encR)
    moreover assume "S \<midarrow>\<alpha>\<rightarrow>Source S'"
    with A1 have "SourceTerm S \<midarrow>\<alpha>'\<rightarrow>(STLCal Source Target) (SourceTerm S')"
      using STLCal_labelledStep(1)[of S \<alpha>' "SourceTerm S'"]
      by blast
    with bisim A2 obtain \<beta>' Q' where A3: "TargetTerm (\<lbrakk>S\<rbrakk>) \<midarrow>\<beta>'\<rightarrow>(STLCal Source Target) Q'"
                                 and A4: "SourceTerm S' \<sim>\<lbrakk>\<cdot>\<rbrakk>T<TRel> Q'"
                                 and A5: "\<langle>SourceTerm S, \<alpha>'\<rangle> \<equiv>\<lparr>\<rparr> \<langle>TargetTerm (\<lbrakk>S\<rbrakk>), \<beta>'\<rangle>"
      by blast
    from A3 obtain \<beta> T where A6: "\<beta> \<in>TL \<langle>TargetTerm (\<lbrakk>S\<rbrakk>), \<beta>'\<rangle>" and A7: "T \<in>T Q'"
                         and A8: "\<lbrakk>S\<rbrakk> \<midarrow>\<beta>\<rightarrow>Target T"
      using STLCal_labelledStep(2)[of "\<lbrakk>S\<rbrakk>" \<beta>' Q']
      by blast
    from eqT have "TRel\<^sup>* = TRel"
      using reflcl_trancl[of TRel] trancl_id[of TRel]
      unfolding equiv_def refl_on_def
      by auto
    with A4 A7 have A9: "(\<lbrakk>S'\<rbrakk>, T) \<in> TRel"
      using indRelTEQ_to_TRel(2)[where TRel="TRel"]
            trans_closure_of_TRel_refl_cond[where TRel="TRel"]
      by simp
    from A1 A5 A6 have "\<lblot>\<alpha>\<rblot> = \<beta>"
      unfolding related_labels_def encLST_def getSourceLabel_def getTargetLabel_def
      by blast
    with A8 A9 show "\<exists>T. \<lbrakk>S\<rbrakk> \<midarrow>\<lblot>\<alpha>\<rblot>\<rightarrow>Target T \<and> (\<lbrakk>S'\<rbrakk>, T) \<in> TRel"
      by blast
  next
    fix S \<beta> T
    obtain \<beta>' where A1: "\<beta> \<in>TL \<langle>TargetTerm (\<lbrakk>S\<rbrakk>), \<beta>'\<rangle>"
      unfolding getTargetLabel_def
      by blast
    have A2: "SourceTerm S \<sim>\<lbrakk>\<cdot>\<rbrakk>T<TRel> TargetTerm (\<lbrakk>S\<rbrakk>)"
      by (rule indRelTEQ.encR)
    assume "\<lbrakk>S\<rbrakk> \<midarrow>\<beta>\<rightarrow>Target T"
    with A1 have "TargetTerm (\<lbrakk>S\<rbrakk>) \<midarrow>\<beta>'\<rightarrow>(STLCal Source Target) (TargetTerm T)"
      using STLCal_labelledStep(2)[of "\<lbrakk>S\<rbrakk>" \<beta>' "TargetTerm T"]
      by blast
    with bisim A2 obtain \<alpha>' Q' where A3: "SourceTerm S \<midarrow>\<alpha>'\<rightarrow>(STLCal Source Target) Q'"
                                 and A4: "Q' \<sim>\<lbrakk>\<cdot>\<rbrakk>T<TRel> TargetTerm T"
                                 and A5: "\<langle>SourceTerm S, \<alpha>'\<rangle> \<equiv>\<lparr>\<rparr> \<langle>TargetTerm (\<lbrakk>S\<rbrakk>), \<beta>'\<rangle>"
      by blast
    from A3 obtain \<alpha> S' where A6: "\<alpha> \<in>SL \<langle>SourceTerm S, \<alpha>'\<rangle>" and A7: "S' \<in>S Q'"
                          and A8: "S \<midarrow>\<alpha>\<rightarrow>Source S'"
      using STLCal_labelledStep(1)[of S \<alpha>' Q']
      by blast
    from eqT have "TRel\<^sup>* = TRel"
      using reflcl_trancl[of TRel] trancl_id[of TRel]
      unfolding equiv_def refl_on_def
      by auto
    with A4 A7 have A9: "(\<lbrakk>S'\<rbrakk>, T) \<in> TRel"
      using indRelTEQ_to_TRel(2)[where TRel="TRel"]
            trans_closure_of_TRel_refl_cond[where TRel="TRel"]
      by blast
    from A1 A5 A6 have "\<lblot>\<alpha>\<rblot> = \<beta>"
      unfolding related_labels_def encLST_def getSourceLabel_def getTargetLabel_def
      by blast
    with A8 A9 show "\<exists>\<alpha> S'. S \<midarrow>\<alpha>\<rightarrow>Source S' \<and> (\<lbrakk>S'\<rbrakk>, T) \<in> TRel \<and> \<lblot>\<alpha>\<rblot> = \<beta>"
      by blast
  qed
  moreover have "strong_labelled_bisimulation TRel Target"
  proof -
    from eqT have "TRel\<^sup>* = TRel"
      using reflcl_trancl[of TRel] trancl_id[of TRel]
      unfolding equiv_def refl_on_def
      by auto
    with bisim show "strong_labelled_bisimulation TRel Target"
      using indRelTEQ_impl_TRel_is_strong_labelled_bisimulation_encL[where TRel="TRel"]
      by simp
  qed
  ultimately show "strongly_operational_corresponding_encL TRel \<and>
                   strong_labelled_bisimulation TRel Target"
    by simp
qed

lemma (in encoding) SOC_wrt_equivalence_iff_strong_reduction_bisimulation:
  fixes TRel :: "('procT \<times> 'procT) set"
  assumes eqT: "equivalence TRel"
  shows "(strongly_operational_corresponding TRel \<and> strong_reduction_bisimulation TRel Target)
         \<longleftrightarrow> (\<exists>Rel.
         (\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel \<and> (TargetTerm (\<lbrakk>S\<rbrakk>), SourceTerm S) \<in> Rel)
         \<and> TRel = {(T1, T2). (TargetTerm T1, TargetTerm T2) \<in> Rel}
         \<and> trans Rel \<and> strong_reduction_bisimulation Rel (STCal Source Target))"
proof (rule iffI, erule conjE)
  assume oc:     "strongly_operational_corresponding TRel"
     and bisimT: "strong_reduction_bisimulation TRel Target"
  from eqT have rt: "TRel\<^sup>* = TRel"
    using reflcl_trancl[of TRel] trancl_id[of TRel]
    unfolding equiv_def refl_on_def
    by auto
  have "\<forall>S. SourceTerm S \<sim>\<lbrakk>\<cdot>\<rbrakk>T<TRel> TargetTerm (\<lbrakk>S\<rbrakk>) \<and> TargetTerm (\<lbrakk>S\<rbrakk>) \<sim>\<lbrakk>\<cdot>\<rbrakk>T<TRel> SourceTerm S"
    by (simp add: indRelTEQ.encR indRelTEQ.encL)
  moreover from rt have "TRel = {(T1, T2). TargetTerm T1 \<sim>\<lbrakk>\<cdot>\<rbrakk>T<TRel> TargetTerm T2}"
    using indRelTEQ_to_TRel(4)[where TRel="TRel"]
          trans_closure_of_TRel_refl_cond[where TRel="TRel"]
    by (auto simp add: indRelTEQ.target)
  moreover have "trans (indRelTEQ TRel)"
    using indRelTEQ.trans[where TRel="TRel"]
    unfolding trans_def
    by blast
  moreover from eqT oc bisimT
  have "strong_reduction_bisimulation (indRelTEQ TRel) (STCal Source Target)"
    using SOC_wrt_equivalence_iff_indRelTEQ_strong_reduction_bisimulation[where TRel="TRel"]
    by blast
  ultimately
  show "\<exists>Rel. (\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel \<and> (TargetTerm (\<lbrakk>S\<rbrakk>), SourceTerm S) \<in> Rel)
        \<and> TRel = {(T1, T2). (TargetTerm T1, TargetTerm T2) \<in> Rel} \<and> trans Rel
        \<and> strong_reduction_bisimulation Rel (STCal Source Target)"
    by blast
next
  assume "\<exists>Rel. (\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel
                 \<and> (TargetTerm (\<lbrakk>S\<rbrakk>), SourceTerm S) \<in> Rel)
          \<and> TRel = {(T1, T2). (TargetTerm T1, TargetTerm T2) \<in> Rel} \<and> trans Rel
          \<and> strong_reduction_bisimulation Rel (STCal Source Target)"
  from this obtain Rel where A1: "\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel
                                  \<and> (TargetTerm (\<lbrakk>S\<rbrakk>), SourceTerm S) \<in> Rel"
   and A2: "TRel = {(T1, T2). (TargetTerm T1, TargetTerm T2) \<in> Rel}" and A3: "trans Rel"
   and A4: "strong_reduction_bisimulation Rel (STCal Source Target)"
    by blast
  have "strongly_operational_corresponding TRel"
  proof auto
    fix S S'
    from A1 have "(SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel"
      by simp
    moreover assume "S \<longmapsto>Source S'"
    hence "SourceTerm S \<longmapsto>(STCal Source Target) (SourceTerm S')"
      by (simp add: STCal_step(1))
    ultimately obtain Q' where B1: "TargetTerm (\<lbrakk>S\<rbrakk>) \<longmapsto>(STCal Source Target) Q'"
                           and B2: "(SourceTerm S', Q') \<in> Rel"
      using A4
      by blast
    from B1 obtain T where B3: "\<lbrakk>S\<rbrakk> \<longmapsto>Target T" and B4: "T \<in>T Q'"
      by (auto simp add: STCal_step(2))
    from A1 have "(TargetTerm (\<lbrakk>S'\<rbrakk>), SourceTerm S') \<in> Rel"
      by simp
    with B2 A3 have "(TargetTerm (\<lbrakk>S'\<rbrakk>), Q') \<in> Rel"
      unfolding trans_def
      by blast
    with B4 A2 have "(\<lbrakk>S'\<rbrakk>, T) \<in> TRel"
      by simp
    with B3 show "\<exists>T. \<lbrakk>S\<rbrakk> \<longmapsto>Target T \<and> (\<lbrakk>S'\<rbrakk>, T) \<in> TRel"
      by blast
  next
    fix S T
    from A1 have "(SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel"
      by simp
    moreover assume "\<lbrakk>S\<rbrakk> \<longmapsto>Target T"
    hence "TargetTerm (\<lbrakk>S\<rbrakk>) \<longmapsto>(STCal Source Target) (TargetTerm T)"
      by (simp add: STCal_step(2))
    ultimately obtain P' where C1: "SourceTerm S \<longmapsto>(STCal Source Target) P'"
                           and C2: "(P', TargetTerm T) \<in> Rel"
      using A4
      by blast
    from C1 obtain S' where C3: "S \<longmapsto>Source S'" and C4: "S' \<in>S P'"
      by (auto simp add: STCal_step(1))
    from A1 C4 have "(TargetTerm (\<lbrakk>S'\<rbrakk>), P') \<in> Rel"
      by simp
    from A3 this C2 have "(TargetTerm (\<lbrakk>S'\<rbrakk>), TargetTerm T) \<in> Rel"
      unfolding trans_def
      by blast
    with A2 have "(\<lbrakk>S'\<rbrakk>, T) \<in> TRel"
      by simp
    with C3 show "\<exists>S'. S \<longmapsto>Source S' \<and> (\<lbrakk>S'\<rbrakk>, T) \<in> TRel"
      by blast
  qed
  moreover have "strong_reduction_bisimulation TRel Target"
  proof auto
    fix TP TQ TP'
    assume "(TP, TQ) \<in> TRel"
    with A2 have "(TargetTerm TP, TargetTerm TQ) \<in> Rel"
      by simp
    moreover assume "TP \<longmapsto>Target TP'"
    hence "TargetTerm TP \<longmapsto>(STCal Source Target) (TargetTerm TP')"
      by (simp add: STCal_step(2))
    ultimately obtain Q' where D1: "TargetTerm TQ \<longmapsto>(STCal Source Target) Q'"
                           and D2: "(TargetTerm TP', Q') \<in> Rel"
      using A4
      by blast
    from D1 obtain TQ' where D3: "TQ \<longmapsto>Target TQ'" and D4: "TQ' \<in>T Q'"
      by (auto simp add: STCal_step(2))
    from A2 D2 D4 have "(TP', TQ') \<in> TRel"
      by simp
    with D3 show "\<exists>TQ'. TQ \<longmapsto>Target TQ' \<and> (TP', TQ') \<in> TRel"
      by blast
  next
    fix TP TQ TQ'
    assume "(TP, TQ) \<in> TRel"
    with A2 have "(TargetTerm TP, TargetTerm TQ) \<in> Rel"
      by simp
    moreover assume "TQ \<longmapsto>Target TQ'"
    hence "TargetTerm TQ \<longmapsto>(STCal Source Target) (TargetTerm TQ')"
      by (simp add: STCal_step(2))
    ultimately obtain P' where E1: "TargetTerm TP \<longmapsto>(STCal Source Target) P'"
                           and E2: "(P', TargetTerm TQ') \<in> Rel"
      using A4
      by blast
    from E1 obtain TP' where E3: "TP \<longmapsto>Target TP'" and E4: "TP' \<in>T P'"
      by (auto simp add: STCal_step(2))
    from A2 E2 E4 have "(TP', TQ') \<in> TRel"
      by simp
    with E3 show "\<exists>TP'. TP \<longmapsto>Target TP' \<and> (TP', TQ') \<in> TRel"
      by blast
  qed
  ultimately
  show "strongly_operational_corresponding TRel \<and> strong_reduction_bisimulation TRel Target"
    by simp
qed

lemma (in encodingLS_encL) SOC_wrt_equivalence_iff_strong_labelled_bisimulation_encL:
  fixes TRel :: "('procT \<times> 'procT) set"
  assumes eqT: "equivalence TRel"
      and inj: "inj encL"
  shows "(strongly_operational_corresponding_encL TRel \<and> strong_labelled_bisimulation TRel Target)
         \<longleftrightarrow> (\<exists>Rel.
         (\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel \<and> (TargetTerm (\<lbrakk>S\<rbrakk>), SourceTerm S) \<in> Rel)
         \<and> TRel = {(T1, T2). (TargetTerm T1, TargetTerm T2) \<in> Rel}
         \<and> trans Rel \<and> strong_labelled_bisimulation_encL Rel)"
proof (rule iffI, erule conjE)
  assume oc:     "strongly_operational_corresponding_encL TRel"
     and bisimT: "strong_labelled_bisimulation TRel Target"
  from eqT have rt: "TRel\<^sup>* = TRel"
    using reflcl_trancl[of TRel] trancl_id[of TRel]
    unfolding equiv_def refl_on_def
    by auto
  have "\<forall>S. SourceTerm S \<sim>\<lbrakk>\<cdot>\<rbrakk>T<TRel> TargetTerm (\<lbrakk>S\<rbrakk>) \<and> TargetTerm (\<lbrakk>S\<rbrakk>) \<sim>\<lbrakk>\<cdot>\<rbrakk>T<TRel> SourceTerm S"
    by (simp add: indRelTEQ.encR indRelTEQ.encL)
  moreover from rt have "TRel = {(T1, T2). TargetTerm T1 \<sim>\<lbrakk>\<cdot>\<rbrakk>T<TRel> TargetTerm T2}"
    using indRelTEQ_to_TRel(4)[where TRel="TRel"]
          trans_closure_of_TRel_refl_cond[where TRel="TRel"]
    by (auto simp add: indRelTEQ.target)
  moreover have "trans (indRelTEQ TRel)"
    using indRelTEQ.trans[where TRel="TRel"]
    unfolding trans_def
    by blast
  moreover from eqT inj oc bisimT
  have "strong_labelled_bisimulation_encL (indRelTEQ TRel)"
    using SOC_wrt_equivalence_iff_indRelTEQ_strong_labelled_bisimulation_encL[where TRel="TRel"]
    by blast
  ultimately
  show "\<exists>Rel. (\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel \<and> (TargetTerm (\<lbrakk>S\<rbrakk>), SourceTerm S) \<in> Rel)
        \<and> TRel = {(T1, T2). (TargetTerm T1, TargetTerm T2) \<in> Rel} \<and> trans Rel
        \<and> strong_labelled_bisimulation_encL Rel"
    by blast
next
  assume "\<exists>Rel. (\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel
                 \<and> (TargetTerm (\<lbrakk>S\<rbrakk>), SourceTerm S) \<in> Rel)
          \<and> TRel = {(T1, T2). (TargetTerm T1, TargetTerm T2) \<in> Rel} \<and> trans Rel
          \<and> strong_labelled_bisimulation_encL Rel"
  from this obtain Rel where A1: "\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel
                                  \<and> (TargetTerm (\<lbrakk>S\<rbrakk>), SourceTerm S) \<in> Rel"
   and A2: "TRel = {(T1, T2). (TargetTerm T1, TargetTerm T2) \<in> Rel}" and A3: "trans Rel"
   and A4: "strong_labelled_bisimulation_encL Rel"
    by blast
  have "strongly_operational_corresponding_encL TRel"
  proof auto
    fix S \<alpha> S'
    obtain \<alpha>' where B1: "\<alpha> \<in>SL \<langle>SourceTerm S, \<alpha>'\<rangle>"
      unfolding getSourceLabel_def
      by blast
    from A1 have B2: "(SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel"
      by simp
    assume "S \<midarrow>\<alpha>\<rightarrow>Source S'"
    with B1 have "SourceTerm S \<midarrow>\<alpha>'\<rightarrow>(STLCal Source Target) (SourceTerm S')"
      using STLCal_labelledStep(1)[of S \<alpha>' "SourceTerm S'"]
      by blast
    with A4 B2 obtain \<beta>' Q' where B3: "TargetTerm (\<lbrakk>S\<rbrakk>) \<midarrow>\<beta>'\<rightarrow>(STLCal Source Target) Q'"
                              and B4: "(SourceTerm S', Q') \<in> Rel"
                              and B5: "\<langle>SourceTerm S, \<alpha>'\<rangle> \<equiv>\<lparr>\<rparr> \<langle>TargetTerm (\<lbrakk>S\<rbrakk>), \<beta>'\<rangle>"
      by blast
    from B3 obtain \<beta> T where B6: "\<beta> \<in>TL \<langle>TargetTerm (\<lbrakk>S\<rbrakk>), \<beta>'\<rangle>" and B7: "T \<in>T Q'"
                         and B8: "\<lbrakk>S\<rbrakk> \<midarrow>\<beta>\<rightarrow>Target T"
      using STLCal_labelledStep(2)[of "\<lbrakk>S\<rbrakk>" \<beta>' Q']
      by blast
    from A1 have "(TargetTerm (\<lbrakk>S'\<rbrakk>), SourceTerm S') \<in> Rel"
      by simp
    with A3 B4 have "(TargetTerm (\<lbrakk>S'\<rbrakk>), Q') \<in> Rel"
      using transD[of Rel "TargetTerm (\<lbrakk>S'\<rbrakk>)" "SourceTerm S'" Q']
      by simp
    with A2 B7 have B9: "(\<lbrakk>S'\<rbrakk>, T) \<in> TRel"
      by simp
    from B1 B5 B6 have "\<lblot>\<alpha>\<rblot> = \<beta>"
      unfolding related_labels_def encLST_def getSourceLabel_def getTargetLabel_def
      by blast
    with B8 B9 show "\<exists>T. \<lbrakk>S\<rbrakk> \<midarrow>\<lblot>\<alpha>\<rblot>\<rightarrow>Target T \<and> (\<lbrakk>S'\<rbrakk>, T) \<in> TRel"
      by blast
  next
    fix S \<beta> T
    obtain \<beta>' where B1: "\<beta> \<in>TL \<langle>TargetTerm (\<lbrakk>S\<rbrakk>), \<beta>'\<rangle>"
      unfolding getTargetLabel_def
      by blast
    from A1 have B2: "(SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel"
      by simp
    assume "\<lbrakk>S\<rbrakk> \<midarrow>\<beta>\<rightarrow>Target T"
    with B1 have "TargetTerm (\<lbrakk>S\<rbrakk>) \<midarrow>\<beta>'\<rightarrow>(STLCal Source Target) (TargetTerm T)"
      using STLCal_labelledStep(2)[of "\<lbrakk>S\<rbrakk>" \<beta>' "TargetTerm T"]
      by blast
    with A4 B2 obtain \<alpha>' P' where B3: "SourceTerm S \<midarrow>\<alpha>'\<rightarrow>(STLCal Source Target) P'"
                              and B4: "(P', TargetTerm T) \<in> Rel"
                              and B5: "\<langle>SourceTerm S, \<alpha>'\<rangle> \<equiv>\<lparr>\<rparr> \<langle>TargetTerm (\<lbrakk>S\<rbrakk>), \<beta>'\<rangle>"
      by blast
    from B3 obtain \<alpha> S' where B6: "\<alpha> \<in>SL \<langle>SourceTerm S, \<alpha>'\<rangle>" and B7: "S' \<in>S P'"
                          and B8: "S \<midarrow>\<alpha>\<rightarrow>Source S'"
      using STLCal_labelledStep(1)[of S \<alpha>' P']
      by blast
    from A1 B7 have "(TargetTerm (\<lbrakk>S'\<rbrakk>), P') \<in> Rel"
      by simp
    with A3 B4 have "(TargetTerm (\<lbrakk>S'\<rbrakk>), TargetTerm T) \<in> Rel"
      using transD[of Rel "TargetTerm (\<lbrakk>S'\<rbrakk>)" P' "TargetTerm T"]
      by simp
    with A2 have B9: "(\<lbrakk>S'\<rbrakk>, T) \<in> TRel"
      by simp
    from B1 B5 B6 have "\<lblot>\<alpha>\<rblot> = \<beta>"
      unfolding related_labels_def encLST_def getSourceLabel_def getTargetLabel_def
      by blast
    with B8 B9 show "\<exists>\<alpha> S'. S \<midarrow>\<alpha>\<rightarrow>Source S' \<and> (\<lbrakk>S'\<rbrakk>, T) \<in> TRel \<and> \<lblot>\<alpha>\<rblot> = \<beta>"
      by blast
  qed
  moreover have "strong_labelled_bisimulation TRel Target"
  proof auto
    fix TP TQ \<alpha> TP'
    obtain \<alpha>' where B1: "\<alpha> \<in>TL \<langle>TargetTerm TP, \<alpha>'\<rangle>"
      unfolding getTargetLabel_def
      by blast
    assume "(TP, TQ) \<in> TRel"
    with A2 have B2: "(TargetTerm TP, TargetTerm TQ) \<in> Rel"
      by simp
    assume "TP \<midarrow>\<alpha>\<rightarrow>Target TP'"
    with B1 have "TargetTerm TP \<midarrow>\<alpha>'\<rightarrow>(STLCal Source Target) (TargetTerm TP')"
      using STLCal_labelledStep(2)[of TP \<alpha>' "TargetTerm TP'"]
      by blast
    with A4 B2 obtain \<beta>' Q' where B3: "TargetTerm TQ \<midarrow>\<beta>'\<rightarrow>(STLCal Source Target) Q'"
                              and B4: "(TargetTerm TP', Q') \<in> Rel"
                              and B5: "\<langle>TargetTerm TP, \<alpha>'\<rangle> \<equiv>\<lparr>\<rparr> \<langle>TargetTerm TQ, \<beta>'\<rangle>"
      by blast
    from B5 have "\<beta>' = \<alpha>'"
      using related_labels_equal[of "TargetTerm TP" \<alpha>' "TargetTerm TQ" \<beta>']
      by simp
    with B1 B3 obtain TQ' where B6: "TQ' \<in>T Q'" and B7: "TQ \<midarrow>\<alpha>\<rightarrow>Target TQ'"
      using STLCal_labelledStep(2)[of TQ \<alpha>' Q']
      unfolding getTargetLabel_def
      by blast
    from A2 B4 B6 have "(TP', TQ') \<in> TRel"
      by simp
    with B7 show "\<exists>TQ'. TQ \<midarrow>\<alpha>\<rightarrow>Target TQ' \<and> (TP', TQ') \<in> TRel"
      by blast
  next
    fix TP TQ \<alpha> TQ'
    obtain \<alpha>' where B1: "\<alpha> \<in>TL \<langle>TargetTerm TQ, \<alpha>'\<rangle>"
      unfolding getTargetLabel_def
      by blast
    assume "(TP, TQ) \<in> TRel"
    with A2 have B2: "(TargetTerm TP, TargetTerm TQ) \<in> Rel"
      by simp
    assume "TQ \<midarrow>\<alpha>\<rightarrow>Target TQ'"
    with B1 have "TargetTerm TQ \<midarrow>\<alpha>'\<rightarrow>(STLCal Source Target) (TargetTerm TQ')"
      using STLCal_labelledStep(2)[of TQ \<alpha>' "TargetTerm TQ'"]
      by blast
    with A4 B2 obtain \<beta>' P' where B3: "TargetTerm TP \<midarrow>\<beta>'\<rightarrow>(STLCal Source Target) P'"
                              and B4: "(P', TargetTerm TQ') \<in> Rel"
                              and B5: "\<langle>TargetTerm TP, \<beta>'\<rangle> \<equiv>\<lparr>\<rparr> \<langle>TargetTerm TQ, \<alpha>'\<rangle>"
      by blast
    from B5 have "\<beta>' = \<alpha>'"
      using related_labels_equal[of "TargetTerm TP" \<beta>' "TargetTerm TQ" \<alpha>']
      by simp
    with B1 B3 obtain TP' where B6: "TP' \<in>T P'" and B7: "TP \<midarrow>\<alpha>\<rightarrow>Target TP'"
      using STLCal_labelledStep(2)[of TP \<alpha>' P']
      unfolding getTargetLabel_def
      by blast
    from A2 B4 B6 have "(TP', TQ') \<in> TRel"
      by simp
    with B7 show "\<exists>TP'. TP \<midarrow>\<alpha>\<rightarrow>Target TP' \<and> (TP', TQ') \<in> TRel"
      by blast
  qed
  ultimately show "strongly_operational_corresponding_encL TRel \<and>
                   strong_labelled_bisimulation TRel Target"
    by simp
qed

end