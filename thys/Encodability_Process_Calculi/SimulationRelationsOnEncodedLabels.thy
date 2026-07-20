(* Kirstin Peters, University of Augsburg, 2026 *)

theory SimulationRelationsOnEncodedLabels
  imports SimulationRelations Encodings
begin

section \<open>Simulation Relations with Encoded Labels\<close>

text \<open>The standard notion of labelled simulation relations require labels to match exactly. We now
      relax this requirement by allowing to simulate a source term step in the target with an
      encoded label.\<close>

subsection \<open>Simulation\<close>

text \<open>A weak labelled simulation on encoded labels is relation R such that if (P, Q) in R and P
      evolves to some P' using label a then there exist b and Q' such that Q evolves to Q' using b,
      (P', Q') in R, and a and b are related labels. Remember that a and b are related, if they are
      equal or if one is the translation of the other.\<close>

abbreviation (in encodingLS_encL) weak_labelled_simulation_encL
  :: "(('procS, 'procT) Proc \<times> ('procS, 'procT) Proc) set \<Rightarrow> bool" where
  "weak_labelled_simulation_encL Rel \<equiv>
   \<forall>P Q \<alpha> P'. (P, Q) \<in> Rel \<and> P \<midarrow>\<Zcat>\<alpha>\<rightarrow>(STLCal Source Target)* P' \<longrightarrow>
   (\<exists>\<beta> Q'. Q \<midarrow>\<Zcat>\<beta>\<rightarrow>(STLCal Source Target)* Q' \<and> (P', Q') \<in> Rel \<and> \<langle>P, \<alpha>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>Q, \<beta>\<rangle>)"

text \<open>A weak labelled simulation on encoded labels simulates words of labels including the empty
      word, if the label encoding preserves the internal action. We can relax the requirement of
      the respection of the internal to preservation (respectively reflection), if the considered
      relation never relates a target to a source term (respectively a source to a target term).\<close>

lemma (in encodingLS_encL) weak_labelled_simulation_encL_and_respection_internal:
  fixes Rel    :: "(('procS, 'procT) Proc \<times> ('procS, 'procT) Proc) set"
    and P Q P' :: "('procS, 'procT) Proc"
  assumes simulation: "weak_labelled_simulation_encL Rel"
      and relation:   "(P, Q) \<in> Rel"
      and execution:  "P \<rightarrow>(STLCal Source Target)* P'"
      and respection: "encL_respects_internal"
    shows "\<exists>Q'. Q \<rightarrow>(STLCal Source Target)* Q' \<and> (P', Q') \<in> Rel"
proof -
  from execution have "P \<midarrow>\<Zcat>\<tau>-STLCal\<rightarrow>(STLCal Source Target)* P'"
    using internalST_iff_internal
    unfolding weakLabelledStep_def
    by simp
  with simulation relation obtain \<beta> Q' where A1: "Q \<midarrow>\<Zcat>\<beta>\<rightarrow>(STLCal Source Target)* Q'"
                                         and A2: "(P', Q') \<in> Rel" and A3: "\<langle>P, \<tau>-STLCal\<rangle> \<equiv>\<lparr>\<rparr> \<langle>Q, \<beta>\<rangle>"
    by blast
  from respection A3 have "\<beta> = \<tau>-STLCal"
    using encL_respects_internal_implies_iff_internal[of P "\<tau>-STLCal" Q \<beta>]
    by blast
  with A1 have "Q \<rightarrow>(STLCal Source Target)* Q'"
    using internalST_iff_internal
    unfolding weakLabelledStep_def
    by simp
  with A2 show "\<exists>Q'. Q \<rightarrow>(STLCal Source Target)* Q' \<and> (P', Q') \<in> Rel"
    by blast
qed

lemma (in encodingLS_encL) weak_labelled_simulation_encL_and_preservation_internal:
  fixes Rel    :: "(('procS, 'procT) Proc \<times> ('procS, 'procT) Proc) set"
    and P Q P' :: "('procS, 'procT) Proc"
  assumes simulation:   "weak_labelled_simulation_encL Rel"
      and relation:     "(P, Q) \<in> Rel"
      and execution:    "P \<rightarrow>(STLCal Source Target)* P'"
      and no_T_to_S:    "\<not>(P \<in> ProcT \<and> Q \<in> ProcS)"
      and preservation: "encL_preserves_internal"
    shows "\<exists>Q'. Q \<rightarrow>(STLCal Source Target)* Q' \<and> (P', Q') \<in> Rel"
proof -
  from execution have "P \<midarrow>\<Zcat>\<tau>-STLCal\<rightarrow>(STLCal Source Target)* P'"
    using internalST_iff_internal
    unfolding weakLabelledStep_def
    by simp
  with simulation relation obtain \<beta> Q' where A1: "Q \<midarrow>\<Zcat>\<beta>\<rightarrow>(STLCal Source Target)* Q'"
                                         and A2: "(P', Q') \<in> Rel" and A3: "\<langle>P, \<tau>-STLCal\<rangle> \<equiv>\<lparr>\<rparr> \<langle>Q, \<beta>\<rangle>"
    by blast
  have "\<beta> = \<tau>-STLCal"
  proof (cases "P \<in> ProcS")
    assume "P \<in> ProcS"
    with preservation A3 show "\<beta> = \<tau>-STLCal"
      using encL_preserves_internal_implies_source_internal_to_internal[of P Q \<beta>]
      by simp
  next
    assume "\<not>P \<in> ProcS"
    with no_T_to_S have B1: "P \<sim>ST Q"
      using source_or_target[of P] source_or_target[of Q]
      by blast
    hence B2: "\<not>\<lparr>P, \<tau>-STLCal\<rparr>\<mapsto>\<langle>Q, \<beta>\<rangle>"
      using kinds_of_encoded_label(1, 3)[of P "\<tau>-STLCal" Q \<beta>]
      by blast
    from B1 have "\<not>\<lparr>Q, \<beta>\<rparr>\<mapsto>\<langle>P, \<tau>-STLCal\<rangle>"
      using kinds_of_encoded_label(1, 3)[of Q \<beta> P "\<tau>-STLCal"]
      by blast
    with A3 B2 show "\<beta> = \<tau>-STLCal"
      using related_labels_get_condition(1)[of P "\<tau>-STLCal" Q \<beta>]
      by simp
  qed
  with A1 have "Q \<rightarrow>(STLCal Source Target)* Q'"
    using internalST_iff_internal
    unfolding weakLabelledStep_def
    by simp
  with A2 show "\<exists>Q'. Q \<rightarrow>(STLCal Source Target)* Q' \<and> (P', Q') \<in> Rel"
    by blast
qed

lemma (in encodingLS_encL) weak_labelled_simulation_encL_and_reflection_internal:
  fixes Rel    :: "(('procS, 'procT) Proc \<times> ('procS, 'procT) Proc) set"
    and P Q P' :: "('procS, 'procT) Proc"
  assumes simulation: "weak_labelled_simulation_encL Rel"
      and relation:   "(P, Q) \<in> Rel"
      and execution:  "P \<rightarrow>(STLCal Source Target)* P'"
      and no_S_to_T:  "\<not>(P \<in> ProcS \<and> Q \<in> ProcT)"
      and reflection: "encL_reflects_internal"
    shows "\<exists>Q'. Q \<rightarrow>(STLCal Source Target)* Q' \<and> (P', Q') \<in> Rel"
proof -
  from execution have "P \<midarrow>\<Zcat>\<tau>-STLCal\<rightarrow>(STLCal Source Target)* P'"
    using internalST_iff_internal
    unfolding weakLabelledStep_def
    by simp
  with simulation relation obtain \<beta> Q' where A1: "Q \<midarrow>\<Zcat>\<beta>\<rightarrow>(STLCal Source Target)* Q'"
                                         and A2: "(P', Q') \<in> Rel" and A3: "\<langle>P, \<tau>-STLCal\<rangle> \<equiv>\<lparr>\<rparr> \<langle>Q, \<beta>\<rangle>"
    by blast
  have "\<beta> = \<tau>-STLCal"
  proof (cases "P \<in> ProcS")
    assume "P \<in> ProcS"
    with no_S_to_T have B1: "P \<sim>ST Q"
      using source_or_target[of P] source_or_target[of Q]
      by blast
    hence B2: "\<not>\<lparr>P, \<tau>-STLCal\<rparr>\<mapsto>\<langle>Q, \<beta>\<rangle>"
      using kinds_of_encoded_label(1, 3)[of P "\<tau>-STLCal" Q \<beta>]
      by blast
    from B1 have "\<not>\<lparr>Q, \<beta>\<rparr>\<mapsto>\<langle>P, \<tau>-STLCal\<rangle>"
      using kinds_of_encoded_label(1, 3)[of Q \<beta> P "\<tau>-STLCal"]
      by blast
    with A3 B2 show "\<beta> = \<tau>-STLCal"
      using related_labels_get_condition(1)[of P "\<tau>-STLCal" Q \<beta>]
      by simp
  next
    assume "\<not>P \<in> ProcS"
    hence "P \<in> ProcT"
      using source_or_target[of P]
      by simp
    with reflection A3 show "\<beta> = \<tau>-STLCal"
      using encL_reflects_internal_implies_target_internal_to_internal[of P Q \<beta>]
      by simp
  qed
  with A1 have "Q \<rightarrow>(STLCal Source Target)* Q'"
    using internalST_iff_internal
    unfolding weakLabelledStep_def
    by simp
  with A2 show "\<exists>Q'. Q \<rightarrow>(STLCal Source Target)* Q' \<and> (P', Q') \<in> Rel"
    by blast
qed

lemma (in encodingLS_encL) weak_labelled_simulation_encL_and_respection_word:
  fixes Rel    :: "(('procS, 'procT) Proc \<times> ('procS, 'procT) Proc) set"
    and P Q P' :: "('procS, 'procT) Proc"
    and w v    :: "('labS, 'labT) Lab list"
  assumes simulation: "weak_labelled_simulation_encL Rel"
      and relation:   "(P, Q) \<in> Rel"
      and execution:  "P \<midarrow>\<frown>w\<rightarrow>(STLCal Source Target)* P'"
      and respection: "encL_respects_internal"
    shows "\<exists>v Q'. Q \<midarrow>\<frown>v\<rightarrow>(STLCal Source Target)* Q' \<and> (P', Q') \<in> Rel \<and> \<langle>P, w\<rangle> \<equiv>\<lparr>\<rparr>* \<langle>Q, v\<rangle>"
proof -
  define Cal where Cal_def: "Cal = STLCal Source Target"
  with execution have "P \<midarrow>\<frown>w\<rightarrow>Cal* P'"
    by simp
  from this simulation relation respection Cal_def
  show "\<exists>v Q'. Q \<midarrow>\<frown>v\<rightarrow>(STLCal Source Target)* Q' \<and> (P', Q') \<in> Rel \<and> \<langle>P, w\<rangle> \<equiv>\<lparr>\<rparr>* \<langle>Q, v\<rangle>"
  proof (induct arbitrary: v)
    case (WLS_Nil P Cal P')
    assume "P \<rightarrow>Cal* P'" and "Cal = STLCal Source Target"
    hence "P \<rightarrow>(STLCal Source Target)* P'"
      by simp
    moreover assume "weak_labelled_simulation_encL Rel" and "(P, Q) \<in> Rel"
                and "encL_respects_internal"
    ultimately obtain Q' where A1: "Q \<rightarrow>(STLCal Source Target)* Q'" and A2: "(P', Q') \<in> Rel"
      using weak_labelled_simulation_encL_and_respection_internal[of Rel P Q P']
      by blast
    from A1 have A3: "Q \<midarrow>\<frown>[]\<rightarrow>(STLCal Source Target)* Q'"
      using weakLabelledSequence.WLS_Nil[of Q "STLCal Source Target" Q']
      by simp
    have "\<langle>P, []\<rangle> \<equiv>\<lparr>\<rparr>* \<langle>Q, []\<rangle>"
      using ELNil[of P Q] ELNil[of Q P] source_or_target[of P] source_or_target[of Q]
      unfolding related_words_def
      by auto
    with A2 A3
    show "\<exists>v Q'. Q \<midarrow>\<frown>v\<rightarrow>(STLCal Source Target)* Q' \<and> (P', Q') \<in> Rel \<and> \<langle>P, []\<rangle> \<equiv>\<lparr>\<rparr>* \<langle>Q, v\<rangle>"
      by blast
  next
    case (WLS_Cons P w Cal P' \<alpha> P'')
    from WLS_Cons(2) have IH: "weak_labelled_simulation_encL Rel \<and> (P, Q) \<in> Rel \<and>
      encL_respects_internal \<and> Cal = STLCal Source Target \<Longrightarrow>
      \<exists>v Q'. Q \<midarrow>\<frown>v\<rightarrow>(STLCal Source Target)* Q' \<and> (P', Q') \<in> Rel \<and> \<langle>P, w\<rangle> \<equiv>\<lparr>\<rparr>* \<langle>Q, v\<rangle>"
      by simp
    assume A1: "weak_labelled_simulation_encL Rel" and "(P, Q) \<in> Rel" and "encL_respects_internal"
       and A2: "Cal = STLCal Source Target"
    with IH obtain v Q' where A3: "Q \<midarrow>\<frown>v\<rightarrow>(STLCal Source Target)* Q'" and A4: "(P', Q') \<in> Rel"
                          and A5: "\<langle>P, w\<rangle> \<equiv>\<lparr>\<rparr>* \<langle>Q, v\<rangle>"
      by blast
    assume "P' \<midarrow>\<Zcat>\<alpha>\<rightarrow>Cal* P''"
    with A1 A2 A4 obtain \<beta> Q'' where A6: "Q' \<midarrow>\<Zcat>\<beta>\<rightarrow>(STLCal Source Target)* Q''"
                                 and A7: "(P'', Q'') \<in> Rel" and A8: "\<langle>P', \<alpha>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>Q', \<beta>\<rangle>"
      by blast
    with A3 A6 have A9: "Q \<midarrow>\<frown>(v@[\<beta>])\<rightarrow>(STLCal Source Target)* Q''"
      using weakLabelledSequence.WLS_Cons[of Q v "STLCal Source Target" Q' \<beta> Q'']
      by simp
    assume "P \<midarrow>\<frown>w\<rightarrow>Cal* P'"
    with A2 have A10: "P \<sim>ST P'"
      using weakLabelledSequenceST_STLCal_weakLabelledSequence[of P w P']
      by blast
    from A3 have "Q \<sim>ST Q'"
      using weakLabelledSequenceST_STLCal_weakLabelledSequence[of Q v Q']
      by blast
    with A5 A8 A10 have "\<langle>P, (w@[\<alpha>])\<rangle> \<equiv>\<lparr>\<rparr>* \<langle>Q, (v@[\<beta>])\<rangle>"
      using related_words_compose[of P w Q v P' \<alpha> Q' \<beta>]
      by simp
    with A7 A9
    show "\<exists>v Q''. Q \<midarrow>\<frown>v\<rightarrow>(STLCal Source Target)* Q'' \<and> (P'', Q'') \<in> Rel \<and> \<langle>P, w@[\<alpha>]\<rangle> \<equiv>\<lparr>\<rparr>* \<langle>Q, v\<rangle>"
      by blast
  qed
qed

lemma (in encodingLS_encL) weak_labelled_simulation_encL_and_preservation_word:
  fixes Rel    :: "(('procS, 'procT) Proc \<times> ('procS, 'procT) Proc) set"
    and P Q P' :: "('procS, 'procT) Proc"
    and w v    :: "('labS, 'labT) Lab list"
  assumes simulation:   "weak_labelled_simulation_encL Rel"
      and relation:     "(P, Q) \<in> Rel"
      and execution:    "P \<midarrow>\<frown>w\<rightarrow>(STLCal Source Target)* P'"
      and no_T_to_S:    "\<not>(P \<in> ProcT \<and> Q \<in> ProcS)"
      and preservation: "encL_preserves_internal"
    shows "\<exists>v Q'. Q \<midarrow>\<frown>v\<rightarrow>(STLCal Source Target)* Q' \<and> (P', Q') \<in> Rel \<and> \<langle>P, w\<rangle> \<equiv>\<lparr>\<rparr>* \<langle>Q, v\<rangle>"
proof -
  define Cal where Cal_def: "Cal = STLCal Source Target"
  with execution have "P \<midarrow>\<frown>w\<rightarrow>Cal* P'"
    by simp
  from this simulation relation no_T_to_S preservation Cal_def
  show "\<exists>v Q'. Q \<midarrow>\<frown>v\<rightarrow>(STLCal Source Target)* Q' \<and> (P', Q') \<in> Rel \<and> \<langle>P, w\<rangle> \<equiv>\<lparr>\<rparr>* \<langle>Q, v\<rangle>"
  proof (induct arbitrary: v)
    case (WLS_Nil P Cal P')
    assume "P \<rightarrow>Cal* P'" and "Cal = STLCal Source Target"
    hence "P \<rightarrow>(STLCal Source Target)* P'"
      by simp
    moreover assume "weak_labelled_simulation_encL Rel" and "(P, Q) \<in> Rel"
                and "\<not>(P \<in> ProcT \<and> Q \<in> ProcS)" and "encL_preserves_internal"
    ultimately obtain Q' where A1: "Q \<rightarrow>(STLCal Source Target)* Q'" and A2: "(P', Q') \<in> Rel"
      using weak_labelled_simulation_encL_and_preservation_internal[of Rel P Q P']
      by blast
    from A1 have A3: "Q \<midarrow>\<frown>[]\<rightarrow>(STLCal Source Target)* Q'"
      using weakLabelledSequence.WLS_Nil[of Q "STLCal Source Target" Q']
      by simp
    have "\<langle>P, []\<rangle> \<equiv>\<lparr>\<rparr>* \<langle>Q, []\<rangle>"
      using ELNil[of P Q] ELNil[of Q P] source_or_target[of P] source_or_target[of Q]
      unfolding related_words_def
      by auto
    with A2 A3
    show "\<exists>v Q'. Q \<midarrow>\<frown>v\<rightarrow>(STLCal Source Target)* Q' \<and> (P', Q') \<in> Rel \<and> \<langle>P, []\<rangle> \<equiv>\<lparr>\<rparr>* \<langle>Q, v\<rangle>"
      by blast
  next
    case (WLS_Cons P w Cal P' \<alpha> P'')
    from WLS_Cons(2) have IH: "weak_labelled_simulation_encL Rel \<and> (P, Q) \<in> Rel \<and>
      \<not>(P \<in> ProcT \<and> Q \<in> ProcS) \<and> encL_preserves_internal \<and> Cal = STLCal Source Target \<Longrightarrow>
      \<exists>v Q'. Q \<midarrow>\<frown>v\<rightarrow>(STLCal Source Target)* Q' \<and> (P', Q') \<in> Rel \<and> \<langle>P, w\<rangle> \<equiv>\<lparr>\<rparr>* \<langle>Q, v\<rangle>"
      by simp
    assume A1: "weak_labelled_simulation_encL Rel" and "(P, Q) \<in> Rel"
       and "\<not>(P \<in> ProcT \<and> Q \<in> ProcS)" and "encL_preserves_internal"
       and A2: "Cal = STLCal Source Target"
    with IH obtain v Q' where A3: "Q \<midarrow>\<frown>v\<rightarrow>(STLCal Source Target)* Q'" and A4: "(P', Q') \<in> Rel"
                          and A5: "\<langle>P, w\<rangle> \<equiv>\<lparr>\<rparr>* \<langle>Q, v\<rangle>"
      by blast
    assume "P' \<midarrow>\<Zcat>\<alpha>\<rightarrow>Cal* P''"
    with A1 A2 A4 obtain \<beta> Q'' where A6: "Q' \<midarrow>\<Zcat>\<beta>\<rightarrow>(STLCal Source Target)* Q''"
                                 and A7: "(P'', Q'') \<in> Rel" and A8: "\<langle>P', \<alpha>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>Q', \<beta>\<rangle>"
      by blast
    with A3 A6 have A9: "Q \<midarrow>\<frown>(v@[\<beta>])\<rightarrow>(STLCal Source Target)* Q''"
      using weakLabelledSequence.WLS_Cons[of Q v "STLCal Source Target" Q' \<beta> Q'']
      by simp
    assume "P \<midarrow>\<frown>w\<rightarrow>Cal* P'"
    with A2 have A10: "P \<sim>ST P'"
      using weakLabelledSequenceST_STLCal_weakLabelledSequence[of P w P']
      by blast
    from A3 have "Q \<sim>ST Q'"
      using weakLabelledSequenceST_STLCal_weakLabelledSequence[of Q v Q']
      by blast
    with A5 A8 A10 have "\<langle>P, (w@[\<alpha>])\<rangle> \<equiv>\<lparr>\<rparr>* \<langle>Q, (v@[\<beta>])\<rangle>"
      using related_words_compose[of P w Q v P' \<alpha> Q' \<beta>]
      by simp
    with A7 A9
    show "\<exists>v Q''. Q \<midarrow>\<frown>v\<rightarrow>(STLCal Source Target)* Q'' \<and> (P'', Q'') \<in> Rel \<and> \<langle>P, w@[\<alpha>]\<rangle> \<equiv>\<lparr>\<rparr>* \<langle>Q, v\<rangle>"
      by blast
  qed
qed

lemma (in encodingLS_encL) weak_labelled_simulation_encL_and_reflection_word:
  fixes Rel    :: "(('procS, 'procT) Proc \<times> ('procS, 'procT) Proc) set"
    and P Q P' :: "('procS, 'procT) Proc"
    and w v    :: "('labS, 'labT) Lab list"
  assumes simulation: "weak_labelled_simulation_encL Rel"
      and relation:   "(P, Q) \<in> Rel"
      and execution:  "P \<midarrow>\<frown>w\<rightarrow>(STLCal Source Target)* P'"
      and no_S_to_T:  "\<not>(P \<in> ProcS \<and> Q \<in> ProcT)"
      and reflection: "encL_reflects_internal"
    shows "\<exists>v Q'. Q \<midarrow>\<frown>v\<rightarrow>(STLCal Source Target)* Q' \<and> (P', Q') \<in> Rel \<and> \<langle>P, w\<rangle> \<equiv>\<lparr>\<rparr>* \<langle>Q, v\<rangle>"
proof -
  define Cal where Cal_def: "Cal = STLCal Source Target"
  with execution have "P \<midarrow>\<frown>w\<rightarrow>Cal* P'"
    by simp
  from this simulation relation no_S_to_T reflection Cal_def
  show "\<exists>v Q'. Q \<midarrow>\<frown>v\<rightarrow>(STLCal Source Target)* Q' \<and> (P', Q') \<in> Rel \<and> \<langle>P, w\<rangle> \<equiv>\<lparr>\<rparr>* \<langle>Q, v\<rangle>"
  proof (induct arbitrary: v)
    case (WLS_Nil P Cal P')
    assume "P \<rightarrow>Cal* P'" and "Cal = STLCal Source Target"
    hence "P \<rightarrow>(STLCal Source Target)* P'"
      by simp
    moreover assume "weak_labelled_simulation_encL Rel" and "(P, Q) \<in> Rel"
                and "\<not>(P \<in> ProcS \<and> Q \<in> ProcT)" and "encL_reflects_internal"
    ultimately obtain Q' where A1: "Q \<rightarrow>(STLCal Source Target)* Q'" and A2: "(P', Q') \<in> Rel"
      using weak_labelled_simulation_encL_and_reflection_internal[of Rel P Q P']
      by blast
    from A1 have A3: "Q \<midarrow>\<frown>[]\<rightarrow>(STLCal Source Target)* Q'"
      using weakLabelledSequence.WLS_Nil[of Q "STLCal Source Target" Q']
      by simp
    have "\<langle>P, []\<rangle> \<equiv>\<lparr>\<rparr>* \<langle>Q, []\<rangle>"
      using ELNil[of P Q] ELNil[of Q P] source_or_target[of P] source_or_target[of Q]
      unfolding related_words_def
      by auto
    with A2 A3
    show "\<exists>v Q'. Q \<midarrow>\<frown>v\<rightarrow>(STLCal Source Target)* Q' \<and> (P', Q') \<in> Rel \<and> \<langle>P, []\<rangle> \<equiv>\<lparr>\<rparr>* \<langle>Q, v\<rangle>"
      by blast
  next
    case (WLS_Cons P w Cal P' \<alpha> P'')
    from WLS_Cons(2) have IH: "weak_labelled_simulation_encL Rel \<and> (P, Q) \<in> Rel \<and>
      \<not>(P \<in> ProcS \<and> Q \<in> ProcT) \<and> encL_reflects_internal \<and> Cal = STLCal Source Target \<Longrightarrow>
      \<exists>v Q'. Q \<midarrow>\<frown>v\<rightarrow>(STLCal Source Target)* Q' \<and> (P', Q') \<in> Rel \<and> \<langle>P, w\<rangle> \<equiv>\<lparr>\<rparr>* \<langle>Q, v\<rangle>"
      by simp
    assume A1: "weak_labelled_simulation_encL Rel" and "(P, Q) \<in> Rel"
       and "\<not>(P \<in> ProcS \<and> Q \<in> ProcT)" and "encL_reflects_internal"
       and A2: "Cal = STLCal Source Target"
    with IH obtain v Q' where A3: "Q \<midarrow>\<frown>v\<rightarrow>(STLCal Source Target)* Q'" and A4: "(P', Q') \<in> Rel"
                          and A5: "\<langle>P, w\<rangle> \<equiv>\<lparr>\<rparr>* \<langle>Q, v\<rangle>"
      by blast
    assume "P' \<midarrow>\<Zcat>\<alpha>\<rightarrow>Cal* P''"
    with A1 A2 A4 obtain \<beta> Q'' where A6: "Q' \<midarrow>\<Zcat>\<beta>\<rightarrow>(STLCal Source Target)* Q''"
                                 and A7: "(P'', Q'') \<in> Rel" and A8: "\<langle>P', \<alpha>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>Q', \<beta>\<rangle>"
      by blast
    with A3 A6 have A9: "Q \<midarrow>\<frown>(v@[\<beta>])\<rightarrow>(STLCal Source Target)* Q''"
      using weakLabelledSequence.WLS_Cons[of Q v "STLCal Source Target" Q' \<beta> Q'']
      by simp
    assume "P \<midarrow>\<frown>w\<rightarrow>Cal* P'"
    with A2 have A10: "P \<sim>ST P'"
      using weakLabelledSequenceST_STLCal_weakLabelledSequence[of P w P']
      by blast
    from A3 have "Q \<sim>ST Q'"
      using weakLabelledSequenceST_STLCal_weakLabelledSequence[of Q v Q']
      by blast
    with A5 A8 A10 have "\<langle>P, (w@[\<alpha>])\<rangle> \<equiv>\<lparr>\<rparr>* \<langle>Q, (v@[\<beta>])\<rangle>"
      using related_words_compose[of P w Q v P' \<alpha> Q' \<beta>]
      by simp
    with A7 A9
    show "\<exists>v Q''. Q \<midarrow>\<frown>v\<rightarrow>(STLCal Source Target)* Q'' \<and> (P'', Q'') \<in> Rel \<and> \<langle>P, w@[\<alpha>]\<rangle> \<equiv>\<lparr>\<rparr>* \<langle>Q, v\<rangle>"
      by blast
  qed
qed

text \<open>Again the reflexive and closure of a weak simulation is a weak simulation. However, the
      transitive closure of a weak simulation is not necessarily a weak simulation, since the
      labels can not necessarily be combined. The transitive closure is a weak simulation, if the
      label encoding is injective.\<close>

lemma (in encodingLS_encL) weak_labelled_simulation_encL_and_refl_closure:
  fixes Rel :: "(('procS, 'procT) Proc \<times> ('procS, 'procT) Proc) set"
  assumes simulation: "weak_labelled_simulation_encL Rel"
  shows "weak_labelled_simulation_encL (Rel\<^sup>=)"
  using assms
proof auto
  fix P Q \<alpha> P'
  assume "weak_labelled_simulation_encL Rel" and "P \<midarrow>\<Zcat>\<alpha>\<rightarrow>(STLCal Source Target)* P'"
     and "(P, Q) \<in> Rel"
  hence "\<exists>\<beta> Q'. Q \<midarrow>\<Zcat>\<beta>\<rightarrow>(STLCal Source Target)* Q' \<and> (P', Q') \<in> Rel \<and> \<langle>P, \<alpha>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>Q, \<beta>\<rangle>"
    by simp
  thus "\<exists>\<beta> Q'. Q \<midarrow>\<Zcat>\<beta>\<rightarrow>(STLCal Source Target)* Q' \<and> ((P', Q') \<in> Rel \<or> P' = Q') \<and> \<langle>P, \<alpha>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>Q, \<beta>\<rangle>"
    by blast
next
  fix Q \<alpha> P'
  assume "Q \<midarrow>\<Zcat>\<alpha>\<rightarrow>(STLCal Source Target)* P'"
  moreover have "Q \<sim>ST Q"
    using source_or_target[of Q]
    by presburger
  hence "\<langle>Q, \<alpha>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>Q, \<alpha>\<rangle>"
    unfolding related_labels_def
    by simp
  ultimately
  show "\<exists>\<beta> Q'. Q \<midarrow>\<Zcat>\<beta>\<rightarrow>(STLCal Source Target)* Q' \<and> ((P', Q') \<in> Rel \<or> P' = Q') \<and> \<langle>Q, \<alpha>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>Q, \<beta>\<rangle>"
    by blast
qed

lemma (in encodingLS_encL) weak_labelled_simulation_encL_and_closures:
  fixes Rel :: "(('procS, 'procT) Proc \<times> ('procS, 'procT) Proc) set"
  assumes simulation: "weak_labelled_simulation_encL Rel"
      and injective:  "inj encL"
    shows "weak_labelled_simulation_encL (Rel\<^sup>=)"
      and "weak_labelled_simulation_encL (Rel\<^sup>+)"
      and "weak_labelled_simulation_encL (Rel\<^sup>*)"
proof -
  from simulation show A1: "weak_labelled_simulation_encL (Rel\<^sup>=)"
    using weak_labelled_simulation_encL_and_refl_closure[of Rel]
    by simp
  have A2: "\<And>Rel. weak_labelled_simulation_encL Rel \<Longrightarrow> weak_labelled_simulation_encL (Rel\<^sup>+)"
  proof clarify
    fix Rel P Q \<alpha> P'
    assume B: "weak_labelled_simulation_encL Rel"
    assume "(P, Q) \<in> Rel\<^sup>+" and "P \<midarrow>\<Zcat>\<alpha>\<rightarrow>(STLCal Source Target)* P'"
    thus "\<exists>\<beta> Q'. Q \<midarrow>\<Zcat>\<beta>\<rightarrow>(STLCal Source Target)* Q' \<and> (P', Q') \<in> Rel\<^sup>+ \<and> \<langle>P, \<alpha>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>Q, \<beta>\<rangle>"
    proof (induct arbitrary: P')
      fix Q P'
      assume "(P, Q) \<in> Rel" and "P \<midarrow>\<Zcat>\<alpha>\<rightarrow>(STLCal Source Target)* P'"
      with B obtain \<beta> Q' where "Q \<midarrow>\<Zcat>\<beta>\<rightarrow>(STLCal Source Target)* Q'" and "(P', Q') \<in> Rel"
                           and "\<langle>P, \<alpha>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>Q, \<beta>\<rangle>"
        by blast
      thus "\<exists>\<beta> Q'. Q \<midarrow>\<Zcat>\<beta>\<rightarrow>(STLCal Source Target)* Q' \<and> (P', Q') \<in> Rel\<^sup>+ \<and> \<langle>P, \<alpha>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>Q, \<beta>\<rangle>"
        by auto
    next
      case (step Q R P')
      assume "\<And>P'. P \<midarrow>\<Zcat>\<alpha>\<rightarrow>(STLCal Source Target)* P' \<Longrightarrow>
              (\<exists>\<beta> Q'. Q \<midarrow>\<Zcat>\<beta>\<rightarrow>(STLCal Source Target)* Q' \<and> (P', Q') \<in> Rel\<^sup>+ \<and> \<langle>P, \<alpha>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>Q, \<beta>\<rangle>)"
         and "P \<midarrow>\<Zcat>\<alpha>\<rightarrow>(STLCal Source Target)* P'"
      from this obtain \<beta> Q' where C1: "Q \<midarrow>\<Zcat>\<beta>\<rightarrow>(STLCal Source Target)* Q'" and C2: "(P', Q') \<in> Rel\<^sup>+"
                              and C3: "\<langle>P, \<alpha>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>Q, \<beta>\<rangle>"
        by blast
      assume "(Q, R) \<in> Rel"
      with B C1 obtain \<gamma> R' where C4: "R \<midarrow>\<Zcat>\<gamma>\<rightarrow>(STLCal Source Target)* R'" and C5: "(Q', R') \<in> Rel\<^sup>+"
                              and C6: "\<langle>Q, \<beta>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>R, \<gamma>\<rangle>"
        by blast
      from C2 C5 have C7: "(P', R') \<in> Rel\<^sup>+"
        by simp
      from injective C3 C6 have "\<langle>P, \<alpha>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>R, \<gamma>\<rangle>"
        using related_labels_trans_inj[of P \<alpha> Q \<beta> R \<gamma>]
        by simp
      with C4 C7
      show "\<exists>\<gamma> R'. R \<midarrow>\<Zcat>\<gamma>\<rightarrow>(STLCal Source Target)* R' \<and> (P', R') \<in> Rel\<^sup>+ \<and> \<langle>P, \<alpha>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>R, \<gamma>\<rangle>"
        by blast
    qed
  qed
  with simulation show "weak_labelled_simulation_encL (Rel\<^sup>+)"
    by blast
  from simulation A1 A2[of "Rel\<^sup>="] show "weak_labelled_simulation_encL (Rel\<^sup>*)"
      using trancl_reflcl[of Rel]
    by fast
qed

text \<open>A strong labelled simulation with encoded labels is relation R such that for each pair (P, Q)
      in R and each step of P to some P' using a there exists some b and Q' such that there is a
      step of Q to Q' using b, (P', Q') in R, and a and b are related labels.\<close>

abbreviation (in encodingLS_encL) strong_labelled_simulation_encL
  :: "(('procS, 'procT) Proc \<times> ('procS, 'procT) Proc) set \<Rightarrow> bool" where
  "strong_labelled_simulation_encL Rel \<equiv>
   \<forall>P Q \<alpha> P'. (P, Q) \<in> Rel \<and> P \<midarrow>\<alpha>\<rightarrow>(STLCal Source Target) P' \<longrightarrow>
   (\<exists>\<beta> Q'. Q \<midarrow>\<beta>\<rightarrow>(STLCal Source Target) Q' \<and> (P', Q') \<in> Rel \<and> \<langle>P, \<alpha>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>Q, \<beta>\<rangle>)"

text \<open>A strong simulation is also a weak simulation, if the label encoding respects the internal.
      Again we can relax the requirement of the respection of the internal to preservation, if the
      considered relation never relates a target to a source term. However, if the label encoding
      reflects the internal, then a strong simulation that does not relate any source term to a
      target term also simulates weak internal steps but is not a weak simulation. Reflection does
      not allows to related internal labels.\<close>

lemma (in encodingLS_encL) strong_labelled_simulation_encL_and_respection_internal:
  fixes Rel    :: "(('procS, 'procT) Proc \<times> ('procS, 'procT) Proc) set"
    and P Q P' :: "('procS, 'procT) Proc"
  assumes simulation: "strong_labelled_simulation_encL Rel"
      and relation:   "(P, Q) \<in> Rel"
      and execution:  "P \<rightarrow>(STLCal Source Target)* P'"
      and respection: "encL_respects_internal"
    shows "\<exists>Q'. Q \<rightarrow>(STLCal Source Target)* Q' \<and> (P', Q') \<in> Rel"
proof -
  define Cal where Cal_def: "Cal = STLCal Source Target"
  with execution have "P \<rightarrow>Cal* P'"
    by simp
  from this simulation relation Cal_def show "\<exists>Q'. Q \<rightarrow>(STLCal Source Target)* Q' \<and> (P', Q') \<in> Rel"
  proof (induct)
    case (WTS_refl P Cal)
    assume "(P, Q) \<in> Rel" and "Cal = STLCal Source Target"
    moreover have "Q \<rightarrow>Cal* Q"
      using weakTauStep.WTS_refl[of Q Cal] .
    ultimately show "\<exists>Q'. Q \<rightarrow>(STLCal Source Target)* Q' \<and> (P, Q') \<in> Rel"
      by blast
  next
    case (WTS_trans P Cal P' P'')
    from WTS_trans(2)
    have IH: "strong_labelled_simulation_encL Rel \<and> (P, Q) \<in> Rel \<and> Cal = STLCal Source Target \<Longrightarrow>
              \<exists>Q'. Q \<rightarrow>(STLCal Source Target)* Q' \<and> (P', Q') \<in> Rel"
      by simp
    assume A1: "strong_labelled_simulation_encL Rel" and "(P, Q) \<in> Rel"
       and A2: "Cal = STLCal Source Target"
    with IH obtain Q' where A3: "Q \<rightarrow>(STLCal Source Target)* Q'" and A4: "(P', Q') \<in> Rel"
      by blast
    assume "P' \<midarrow>\<tau>-Cal\<rightarrow>Cal P''"
    with A1 A2 A4 obtain \<beta> Q'' where A5: "Q' \<midarrow>\<beta>\<rightarrow>(STLCal Source Target) Q''"
                                 and A6: "(P'', Q'') \<in> Rel"
                                 and A7: "\<langle>P', \<tau>-(STLCal Source Target)\<rangle> \<equiv>\<lparr>\<rparr> \<langle>Q', \<beta>\<rangle>"
      by blast
    from respection A2 A7 have "\<beta> = \<tau>-(STLCal Source Target)"
      using encL_respects_internal_implies_iff_internal[of P' "\<tau>-Cal" Q' \<beta>] internalST_iff_internal
      by simp
    with A3 A5 have "Q \<rightarrow>(STLCal Source Target)* Q''"
      using weakTauStep.WTS_trans[of Q "STLCal Source Target" Q' Q'']
      by simp
    with A6 show "\<exists>Q''. Q \<rightarrow>(STLCal Source Target)* Q'' \<and> (P'', Q'') \<in> Rel"
      by blast
  qed
qed

lemma (in encodingLS_encL) strong_labelled_simulation_encL_and_preservation_internal:
  fixes Rel    :: "(('procS, 'procT) Proc \<times> ('procS, 'procT) Proc) set"
    and P Q P' :: "('procS, 'procT) Proc"
  assumes simulation:   "strong_labelled_simulation_encL Rel"
      and relation:     "(P, Q) \<in> Rel"
      and execution:    "P \<rightarrow>(STLCal Source Target)* P'"
      and no_T_to_S:    "\<not>(P \<in> ProcT \<and> Q \<in> ProcS)"
      and preservation: "encL_preserves_internal"
    shows "\<exists>Q'. Q \<rightarrow>(STLCal Source Target)* Q' \<and> (P', Q') \<in> Rel"
proof -
  define Cal where Cal_def: "Cal = STLCal Source Target"
  with execution have "P \<rightarrow>Cal* P'"
    by simp
  from this simulation relation no_T_to_S Cal_def
  show "\<exists>Q'. Q \<rightarrow>(STLCal Source Target)* Q' \<and> (P', Q') \<in> Rel"
  proof (induct)
    case (WTS_refl P Cal)
    assume "(P, Q) \<in> Rel" and "Cal = STLCal Source Target"
    moreover have "Q \<rightarrow>Cal* Q"
      using weakTauStep.WTS_refl[of Q Cal] .
    ultimately show "\<exists>Q'. Q \<rightarrow>(STLCal Source Target)* Q' \<and> (P, Q') \<in> Rel"
      by blast
  next
    case (WTS_trans P Cal P' P'')
    from WTS_trans(2)
    have IH: "strong_labelled_simulation_encL Rel \<and> (P, Q) \<in> Rel \<and> \<not>(P \<in> ProcT \<and> Q \<in> ProcS) \<and>
              Cal = STLCal Source Target \<Longrightarrow> \<exists>Q'. Q \<rightarrow>(STLCal Source Target)* Q' \<and> (P', Q') \<in> Rel"
      by simp
    assume A1: "strong_labelled_simulation_encL Rel" and "(P, Q) \<in> Rel"
       and A2: "\<not>(P \<in> ProcT \<and> Q \<in> ProcS)" and A3: "Cal = STLCal Source Target"
    with IH obtain Q' where A4: "Q \<rightarrow>(STLCal Source Target)* Q'" and A5: "(P', Q') \<in> Rel"
      by blast
    assume "P' \<midarrow>\<tau>-Cal\<rightarrow>Cal P''"
    with A1 A3 A5 obtain \<beta> Q'' where A6: "Q' \<midarrow>\<beta>\<rightarrow>(STLCal Source Target) Q''"
                                 and A7: "(P'', Q'') \<in> Rel"
                                 and A8: "\<langle>P', \<tau>-(STLCal Source Target)\<rangle> \<equiv>\<lparr>\<rparr> \<langle>Q', \<beta>\<rangle>"
      by blast
    assume A9: "P \<rightarrow>Cal* P'"
    have "\<beta> = \<tau>-(STLCal Source Target)"
    proof (cases "P' \<in> ProcS")
      assume "P' \<in> ProcS"
      with preservation A3 A8 show "\<beta> = \<tau>-(STLCal Source Target)"
        using encL_preserves_internal_implies_source_internal_to_internal[of P' Q' \<beta>]
              internalST_iff_internal
        by simp
    next
      assume "\<not>P' \<in> ProcS"
      hence B1: "P' \<in> ProcT"
        using source_or_target[of P']
        by blast
      with A3 A9 have "P \<in> ProcT"
        using weakTauStepsST_STLCal_weakTauSteps[of P P']
        by blast
      with A2 have "Q \<in> ProcT"
        using source_or_target[of Q]
        by blast
      with A4 have "Q' \<in> ProcT"
        using weakTauStepsST_STLCal_weakTauSteps[of Q Q']
        by blast
      hence B2: "\<not>\<lparr>Q', \<beta>\<rparr>\<mapsto>\<langle>P', \<tau>-STLCal\<rangle>"
        using kinds_of_encoded_label(1)[of Q' \<beta> P' "\<tau>-STLCal"]
        by blast
      from B1 have "\<not>\<lparr>P', \<tau>-STLCal\<rparr>\<mapsto>\<langle>Q', \<beta>\<rangle>"
        using kinds_of_encoded_label(1)[of P' "\<tau>-STLCal" Q' \<beta>]
        by blast
      with A8 B2 show "\<beta> = \<tau>-(STLCal Source Target)"
        using related_labels_get_condition(1)[of P' "\<tau>-STLCal" Q' \<beta>] internalST_iff_internal
        by simp
    qed
    with A4 A6 have "Q \<rightarrow>(STLCal Source Target)* Q''"
      using weakTauStep.WTS_trans[of Q "STLCal Source Target" Q' Q'']
      by simp
    with A7 show "\<exists>Q''. Q \<rightarrow>(STLCal Source Target)* Q'' \<and> (P'', Q'') \<in> Rel"
      by blast
  qed
qed

lemma (in encodingLS_encL) strong_labelled_simulation_encL_and_reflection_internal:
  fixes Rel    :: "(('procS, 'procT) Proc \<times> ('procS, 'procT) Proc) set"
    and P Q P' :: "('procS, 'procT) Proc"
  assumes simulation: "strong_labelled_simulation_encL Rel"
      and relation:   "(P, Q) \<in> Rel"
      and execution:  "P \<rightarrow>(STLCal Source Target)* P'"
      and no_S_to_T:  "\<not>(P \<in> ProcS \<and> Q \<in> ProcT)"
      and reflection: "encL_reflects_internal"
    shows "\<exists>Q'. Q \<rightarrow>(STLCal Source Target)* Q' \<and> (P', Q') \<in> Rel"
proof -
  define Cal where Cal_def: "Cal = STLCal Source Target"
  with execution have "P \<rightarrow>Cal* P'"
    by simp
  from this simulation relation no_S_to_T Cal_def
  show "\<exists>Q'. Q \<rightarrow>(STLCal Source Target)* Q' \<and> (P', Q') \<in> Rel"
  proof (induct)
    case (WTS_refl P Cal)
    assume "(P, Q) \<in> Rel" and "Cal = STLCal Source Target"
    moreover have "Q \<rightarrow>Cal* Q"
      using weakTauStep.WTS_refl[of Q Cal] .
    ultimately show "\<exists>Q'. Q \<rightarrow>(STLCal Source Target)* Q' \<and> (P, Q') \<in> Rel"
      by blast
  next
    case (WTS_trans P Cal P' P'')
    from WTS_trans(2)
    have IH: "strong_labelled_simulation_encL Rel \<and> (P, Q) \<in> Rel \<and> \<not>(P \<in> ProcS \<and> Q \<in> ProcT) \<and>
              Cal = STLCal Source Target \<Longrightarrow> \<exists>Q'. Q \<rightarrow>(STLCal Source Target)* Q' \<and> (P', Q') \<in> Rel"
      by simp
    assume A1: "strong_labelled_simulation_encL Rel" and "(P, Q) \<in> Rel"
       and A2: "\<not>(P \<in> ProcS \<and> Q \<in> ProcT)" and A3: "Cal = STLCal Source Target"
    with IH obtain Q' where A4: "Q \<rightarrow>(STLCal Source Target)* Q'" and A5: "(P', Q') \<in> Rel"
      by blast
    assume "P' \<midarrow>\<tau>-Cal\<rightarrow>Cal P''"
    with A1 A3 A5 obtain \<beta> Q'' where A6: "Q' \<midarrow>\<beta>\<rightarrow>(STLCal Source Target) Q''"
                                 and A7: "(P'', Q'') \<in> Rel"
                                 and A8: "\<langle>P', \<tau>-(STLCal Source Target)\<rangle> \<equiv>\<lparr>\<rparr> \<langle>Q', \<beta>\<rangle>"
      by blast
    assume A9: "P \<rightarrow>Cal* P'"
    have "\<beta> = \<tau>-(STLCal Source Target)"
    proof (cases "P' \<in> ProcS")
      assume B1: "P' \<in> ProcS"
      with A3 A9 have "P \<in> ProcS"
        using weakTauStepsST_STLCal_weakTauSteps[of P P']
        by blast
      with A2 have "Q \<in> ProcS"
        using source_or_target[of Q]
        by blast
      with A4 have "Q' \<in> ProcS"
        using weakTauStepsST_STLCal_weakTauSteps[of Q Q']
        by blast
      hence B2: "\<not>\<lparr>P', \<tau>-STLCal\<rparr>\<mapsto>\<langle>Q', \<beta>\<rangle>"
        using kinds_of_encoded_label(3)[of P' "\<tau>-STLCal" Q' \<beta>]
        by blast
      from B1 have "\<not>\<lparr>Q', \<beta>\<rparr>\<mapsto>\<langle>P', \<tau>-STLCal\<rangle>"
        using kinds_of_encoded_label(3)[of Q' \<beta> P' "\<tau>-STLCal"]
        by blast
      with A8 B2 show "\<beta> = \<tau>-(STLCal Source Target)"
        using related_labels_get_condition(1)[of P' "\<tau>-STLCal" Q' \<beta>] internalST_iff_internal
        by simp
    next
      assume "\<not>P' \<in> ProcS"
      hence "P' \<in> ProcT"
        using source_or_target[of P']
        by blast
      with reflection A3 A8 show "\<beta> = \<tau>-(STLCal Source Target)"
        using encL_reflects_internal_implies_target_internal_to_internal[of P' Q' \<beta>]
              internalST_iff_internal
        by simp
    qed
    with A4 A6 have "Q \<rightarrow>(STLCal Source Target)* Q''"
      using weakTauStep.WTS_trans[of Q "STLCal Source Target" Q' Q'']
      by simp
    with A7 show "\<exists>Q''. Q \<rightarrow>(STLCal Source Target)* Q'' \<and> (P'', Q'') \<in> Rel"
      by blast
  qed
qed

lemma (in encodingLS_encL) strong_labelled_simulation_encL_and_respection_weak_simulation:
  fixes Rel :: "(('procS, 'procT) Proc \<times> ('procS, 'procT) Proc) set"
  assumes simulation: "strong_labelled_simulation_encL Rel"
      and respection: "encL_respects_internal"
  shows "weak_labelled_simulation_encL Rel"
proof clarify
  fix P Q \<alpha> P'
  assume A1: "(P, Q) \<in> Rel" and A2: "P \<midarrow>\<Zcat>\<alpha>\<rightarrow>(STLCal Source Target)* P'"
  show "\<exists>\<beta> Q'. Q \<midarrow>\<Zcat>\<beta>\<rightarrow>(STLCal Source Target)* Q' \<and> (P', Q') \<in> Rel \<and> \<langle>P, \<alpha>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>Q, \<beta>\<rangle>"
  proof (cases "\<alpha> = \<tau>-(STLCal Source Target)")
    assume B1: "\<alpha> = \<tau>-(STLCal Source Target)"
    with A2 have "P \<rightarrow>(STLCal Source Target)* P'"
      unfolding weakLabelledStep_def
      by simp
    with simulation respection A1 obtain Q' where B2: "Q \<rightarrow>(STLCal Source Target)* Q'"
                                              and B3: "(P', Q') \<in> Rel"
      using strong_labelled_simulation_encL_and_respection_internal[of Rel P Q P']
      by blast
    from B2 have B4: "Q \<midarrow>\<Zcat>(\<tau>-(STLCal Source Target))\<rightarrow>(STLCal Source Target)* Q'"
      unfolding weakLabelledStep_def
      by simp
    have "\<langle>P, \<alpha>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>Q, \<tau>-(STLCal Source Target)\<rangle>"
      using source_or_target[of P] source_or_target[of Q]
    proof auto
      fix S S'
      from B1 show "\<langle>SourceTerm S, \<alpha>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>SourceTerm S', \<tau>-(STLCal Source Target)\<rangle>"
        unfolding related_labels_def
        by simp
    next
      fix S T
      from respection B1 have "\<lparr>SourceTerm S, \<alpha>\<rparr>\<mapsto>\<langle>TargetTerm T, \<tau>-(STLCal Source Target)\<rangle>"
        using internalST_iff_internal
        unfolding encLST_def getSourceLabel_def getTargetLabel_def
        by auto
      thus "\<langle>SourceTerm S, \<alpha>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>TargetTerm T, \<tau>-(STLCal Source Target)\<rangle>"
        unfolding related_labels_def
        by simp
    next
      fix T S
      from respection B1 have "\<lparr>SourceTerm S, \<tau>-(STLCal Source Target)\<rparr>\<mapsto>\<langle>TargetTerm T, \<alpha>\<rangle>"
        using internalST_iff_internal
        unfolding encLST_def getSourceLabel_def getTargetLabel_def
        by auto
      thus "\<langle>TargetTerm T, \<alpha>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>SourceTerm S, \<tau>-(STLCal Source Target)\<rangle>"
        unfolding related_labels_def
        by simp
    next
      fix T T'
      from B1 show "\<langle>TargetTerm T, \<alpha>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>TargetTerm T', \<tau>-(STLCal Source Target)\<rangle>"
        unfolding related_labels_def
        by simp
    qed
    with B3 B4 show "\<exists>\<beta> Q'. Q \<midarrow>\<Zcat>\<beta>\<rightarrow>(STLCal Source Target)* Q' \<and> (P', Q') \<in> Rel \<and> \<langle>P, \<alpha>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>Q, \<beta>\<rangle>"
      by blast
  next
    assume B1: "\<alpha> \<noteq> \<tau>-(STLCal Source Target)"
    with A2 have "P \<midarrow>\<alpha>\<rightarrow>(STLCal Source Target)* P'"
      unfolding weakLabelledStep_def
      by simp
    with B1 obtain R S where B2: "P \<rightarrow>(STLCal Source Target)* R"
      and B3: "R \<midarrow>\<alpha>\<rightarrow>(STLCal Source Target) S" and B4: "S \<rightarrow>(STLCal Source Target)* P'"
      unfolding weakLabelledActionStep_def
      by blast
    from simulation respection A1 B2 obtain Q' where B5: "Q \<rightarrow>(STLCal Source Target)* Q'"
                                                 and B6: "(R, Q') \<in> Rel"
      using strong_labelled_simulation_encL_and_respection_internal[of Rel P Q R]
      by blast
    from simulation B3 B6 obtain \<beta> Q'' where B7: "Q' \<midarrow>\<beta>\<rightarrow>(STLCal Source Target) Q''"
                                         and B8: "(S, Q'') \<in> Rel" and B9: "\<langle>R, \<alpha>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>Q', \<beta>\<rangle>"
      by blast
    from simulation respection B4 B8 obtain Q''' where B10: "Q'' \<rightarrow>(STLCal Source Target)* Q'''"
                                                   and B11: "(P', Q''') \<in> Rel"
      using strong_labelled_simulation_encL_and_respection_internal[of Rel S Q'' P']
      by blast
    from respection B1 B9 have B12: "\<beta> \<noteq> \<tau>-(STLCal Source Target)"
      using encL_respects_internal_implies_iff_internal[of R \<alpha> Q' \<beta>] internalST_iff_internal
      by simp
    with B5 B7 B10 have "Q \<midarrow>\<beta>\<rightarrow>(STLCal Source Target)* Q'''"
      unfolding weakLabelledActionStep_def
      by blast
    with B12 have B13: "Q \<midarrow>\<Zcat>\<beta>\<rightarrow>(STLCal Source Target)* Q'''"
      unfolding weakLabelledStep_def
      by simp
    from B2 have B14: "R \<sim>ST P"
      using weakTauStepsST_STLCal_weakTauSteps[of P R]
      by blast
    from B5 have "Q' \<sim>ST Q"
      using weakTauStepsST_STLCal_weakTauSteps[of Q Q']
      by blast
    with B9 B14 have "\<langle>P, \<alpha>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>Q, \<beta>\<rangle>"
      using related_labels_exchange_processes[of R \<alpha> Q' \<beta> P Q]
      by simp
    with B11 B13
    show "\<exists>\<beta> Q'''. Q \<midarrow>\<Zcat>\<beta>\<rightarrow>(STLCal Source Target)* Q''' \<and> (P', Q''') \<in> Rel \<and> \<langle>P, \<alpha>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>Q, \<beta>\<rangle>"
      by blast
  qed
qed

lemma (in encodingLS_encL) strong_labelled_simulation_encL_and_preservation_weak_simulation:
  fixes Rel :: "(('procS, 'procT) Proc \<times> ('procS, 'procT) Proc) set"
  assumes simulation:   "strong_labelled_simulation_encL Rel"
      and no_T_to_S:    "\<forall>P Q. (P, Q) \<in> Rel \<longrightarrow> \<not>(P \<in> ProcT \<and> Q \<in> ProcS)"
      and preservation: "encL_preserves_internal"
  shows "weak_labelled_simulation_encL Rel"
proof clarify
  fix P Q \<alpha> P'
  assume A1: "(P, Q) \<in> Rel" and A2: "P \<midarrow>\<Zcat>\<alpha>\<rightarrow>(STLCal Source Target)* P'"
  show "\<exists>\<beta> Q'. Q \<midarrow>\<Zcat>\<beta>\<rightarrow>(STLCal Source Target)* Q' \<and> (P', Q') \<in> Rel \<and> \<langle>P, \<alpha>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>Q, \<beta>\<rangle>"
  proof (cases "\<alpha> = \<tau>-(STLCal Source Target)")
    assume B1: "\<alpha> = \<tau>-(STLCal Source Target)"
    with A2 have "P \<rightarrow>(STLCal Source Target)* P'"
      unfolding weakLabelledStep_def
      by simp
    with simulation no_T_to_S preservation A1 obtain Q' where B2: "Q \<rightarrow>(STLCal Source Target)* Q'"
                                                          and B3: "(P', Q') \<in> Rel"
      using strong_labelled_simulation_encL_and_preservation_internal[of Rel P Q P']
      by blast
    from B2 have B4: "Q \<midarrow>\<Zcat>(\<tau>-(STLCal Source Target))\<rightarrow>(STLCal Source Target)* Q'"
      unfolding weakLabelledStep_def
      by simp
    have "\<langle>P, \<alpha>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>Q, \<tau>-(STLCal Source Target)\<rangle>"
      using source_or_target[of P] source_or_target[of Q]
    proof auto
      fix S S'
      from B1 show "\<langle>SourceTerm S, \<alpha>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>SourceTerm S', \<tau>-(STLCal Source Target)\<rangle>"
        unfolding related_labels_def
        by simp
    next
      fix S T
      from preservation B1 have "\<lparr>SourceTerm S, \<alpha>\<rparr>\<mapsto>\<langle>TargetTerm T, \<tau>-(STLCal Source Target)\<rangle>"
        using internalST_iff_internal
        unfolding encLST_def getSourceLabel_def getTargetLabel_def
        by auto
      thus "\<langle>SourceTerm S, \<alpha>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>TargetTerm T, \<tau>-(STLCal Source Target)\<rangle>"
        unfolding related_labels_def
        by simp
    next
      fix T S
      assume "T \<in>T P" and "S \<in>S Q"
      with no_T_to_S A1 have False
        by blast
      thus "\<langle>TargetTerm T, \<alpha>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>SourceTerm S, \<tau>-(STLCal Source Target)\<rangle>"
        by simp
    next
      fix T T'
      from B1 show "\<langle>TargetTerm T, \<alpha>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>TargetTerm T', \<tau>-(STLCal Source Target)\<rangle>"
        unfolding related_labels_def
        by simp
    qed
    with B3 B4 show "\<exists>\<beta> Q'. Q \<midarrow>\<Zcat>\<beta>\<rightarrow>(STLCal Source Target)* Q' \<and> (P', Q') \<in> Rel \<and> \<langle>P, \<alpha>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>Q, \<beta>\<rangle>"
      by blast
  next
    assume B1: "\<alpha> \<noteq> \<tau>-(STLCal Source Target)"
    with A2 have "P \<midarrow>\<alpha>\<rightarrow>(STLCal Source Target)* P'"
      unfolding weakLabelledStep_def
      by simp
    with B1 obtain R S where B2: "P \<rightarrow>(STLCal Source Target)* R"
      and B3: "R \<midarrow>\<alpha>\<rightarrow>(STLCal Source Target) S" and B4: "S \<rightarrow>(STLCal Source Target)* P'"
      unfolding weakLabelledActionStep_def
      by blast
    from simulation no_T_to_S preservation A1 B2 obtain Q' where
      B5: "Q \<rightarrow>(STLCal Source Target)* Q'" and B6: "(R, Q') \<in> Rel"
      using strong_labelled_simulation_encL_and_preservation_internal[of Rel P Q R]
      by blast
    from simulation B3 B6 obtain \<beta> Q'' where B7: "Q' \<midarrow>\<beta>\<rightarrow>(STLCal Source Target) Q''"
                                         and B8: "(S, Q'') \<in> Rel" and B9: "\<langle>R, \<alpha>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>Q', \<beta>\<rangle>"
      by blast
    from simulation no_T_to_S preservation B4 B8 obtain Q''' where
      B10: "Q'' \<rightarrow>(STLCal Source Target)* Q'''" and B11: "(P', Q''') \<in> Rel"
      using strong_labelled_simulation_encL_and_preservation_internal[of Rel S Q'' P']
      by blast
    have B12: "Q \<midarrow>\<Zcat>\<beta>\<rightarrow>(STLCal Source Target)* Q'''"
    proof (cases "\<beta> = \<tau>-(STLCal Source Target)")
      assume C: "\<beta> = \<tau>-(STLCal Source Target)"
      with B5 B7 have "Q \<rightarrow>(STLCal Source Target)* Q''"
        using WTS_trans[of Q "STLCal Source Target" Q' Q'']
        by simp
      with B10 have "Q \<rightarrow>(STLCal Source Target)* Q'''"
        using weakTauStepsST_trans[of Q Q'' Q'''] weakTauStepsST_STLCal_weakTauSteps[of Q Q'']
              weakTauStepsST_STLCal_weakTauSteps[of Q'' Q''']
              weakTauStepsST_STLCal_weakTauSteps[of Q Q''']
        by simp
      with C show "Q \<midarrow>\<Zcat>\<beta>\<rightarrow>(STLCal Source Target)* Q'''"
        unfolding weakLabelledStep_def
        by simp
    next
      assume C: "\<beta> \<noteq> \<tau>-(STLCal Source Target)"
      with B5 B7 B10 have "Q \<midarrow>\<beta>\<rightarrow>(STLCal Source Target)* Q'''"
        unfolding weakLabelledActionStep_def
        by blast
      with C show "Q \<midarrow>\<Zcat>\<beta>\<rightarrow>(STLCal Source Target)* Q'''"
        unfolding weakLabelledStep_def
        by simp
    qed
    from B2 have B13: "R \<sim>ST P"
      using weakTauStepsST_STLCal_weakTauSteps[of P R]
      by blast
    from B5 have "Q' \<sim>ST Q"
      using weakTauStepsST_STLCal_weakTauSteps[of Q Q']
      by blast
    with B9 B13 have "\<langle>P, \<alpha>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>Q, \<beta>\<rangle>"
      using related_labels_exchange_processes[of R \<alpha> Q' \<beta> P Q]
      by simp
    with B11 B12
    show "\<exists>\<beta> Q'''. Q \<midarrow>\<Zcat>\<beta>\<rightarrow>(STLCal Source Target)* Q''' \<and> (P', Q''') \<in> Rel \<and> \<langle>P, \<alpha>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>Q, \<beta>\<rangle>"
      by blast
  qed
qed

text \<open>The reflexive closure of a strong simulation is a strong simulation. If the label encoding
      is injective, then also the transitive closure of a strong simulation is a strong simulation
      on encoded labels.\<close>

lemma (in encodingLS_encL) strong_labelled_simulation_encL_and_refl_closure:
  fixes Rel :: "(('procS, 'procT) Proc \<times> ('procS, 'procT) Proc) set"
  assumes simulation: "strong_labelled_simulation_encL Rel"
  shows "strong_labelled_simulation_encL (Rel\<^sup>=)"
  using assms
proof auto
  fix P Q \<alpha> P'
  assume "strong_labelled_simulation_encL Rel" and "P \<midarrow>\<alpha>\<rightarrow>(STLCal Source Target) P'"
     and "(P, Q) \<in> Rel"
  hence "\<exists>\<beta> Q'. Q \<midarrow>\<beta>\<rightarrow>(STLCal Source Target) Q' \<and> (P', Q') \<in> Rel \<and> \<langle>P, \<alpha>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>Q, \<beta>\<rangle>"
    by simp
  thus "\<exists>\<beta> Q'. Q \<midarrow>\<beta>\<rightarrow>(STLCal Source Target) Q' \<and> ((P', Q') \<in> Rel \<or> P' = Q') \<and> \<langle>P, \<alpha>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>Q, \<beta>\<rangle>"
    by blast
next
  fix Q \<alpha> P'
  assume "Q \<midarrow>\<alpha>\<rightarrow>(STLCal Source Target) P'"
  moreover have "Q \<sim>ST Q"
    using source_or_target[of Q]
    by presburger
  hence "\<langle>Q, \<alpha>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>Q, \<alpha>\<rangle>"
    unfolding related_labels_def
    by simp
  ultimately
  show "\<exists>\<beta> Q'. Q \<midarrow>\<beta>\<rightarrow>(STLCal Source Target) Q' \<and> ((P', Q') \<in> Rel \<or> P' = Q') \<and> \<langle>Q, \<alpha>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>Q, \<beta>\<rangle>"
    by blast
qed

lemma (in encodingLS_encL) strong_labelled_simulation_encL_and_closures:
  fixes Rel :: "(('procS, 'procT) Proc \<times> ('procS, 'procT) Proc) set"
  assumes simulation: "strong_labelled_simulation_encL Rel"
      and injective:  "inj encL"
    shows "strong_labelled_simulation_encL (Rel\<^sup>=)"
      and "strong_labelled_simulation_encL (Rel\<^sup>+)"
      and "strong_labelled_simulation_encL (Rel\<^sup>*)"
proof -
  from simulation show A1: "strong_labelled_simulation_encL (Rel\<^sup>=)"
    using strong_labelled_simulation_encL_and_refl_closure[of Rel]
    by simp
  have A2: "\<And>Rel. strong_labelled_simulation_encL Rel \<Longrightarrow> strong_labelled_simulation_encL (Rel\<^sup>+)"
  proof clarify
    fix Rel P Q \<alpha> P'
    assume B: "strong_labelled_simulation_encL Rel"
    assume "(P, Q) \<in> Rel\<^sup>+" and "P \<midarrow>\<alpha>\<rightarrow>(STLCal Source Target) P'"
    thus "\<exists>\<beta> Q'. Q \<midarrow>\<beta>\<rightarrow>(STLCal Source Target) Q' \<and> (P', Q') \<in> Rel\<^sup>+ \<and> \<langle>P, \<alpha>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>Q, \<beta>\<rangle>"
    proof (induct arbitrary: P')
      fix Q P'
      assume "(P, Q) \<in> Rel" and "P \<midarrow>\<alpha>\<rightarrow>(STLCal Source Target) P'"
      with B obtain \<beta> Q' where "Q \<midarrow>\<beta>\<rightarrow>(STLCal Source Target) Q'" and "(P', Q') \<in> Rel"
                           and "\<langle>P, \<alpha>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>Q, \<beta>\<rangle>"
        by blast
      thus "\<exists>\<beta> Q'. Q \<midarrow>\<beta>\<rightarrow>(STLCal Source Target) Q' \<and> (P', Q') \<in> Rel\<^sup>+ \<and> \<langle>P, \<alpha>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>Q, \<beta>\<rangle>"
        by auto
    next
      case (step Q R P')
      assume "\<And>P'. P \<midarrow>\<alpha>\<rightarrow>(STLCal Source Target) P' \<Longrightarrow>
              (\<exists>\<beta> Q'. Q \<midarrow>\<beta>\<rightarrow>(STLCal Source Target) Q' \<and> (P', Q') \<in> Rel\<^sup>+ \<and> \<langle>P, \<alpha>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>Q, \<beta>\<rangle>)"
         and "P \<midarrow>\<alpha>\<rightarrow>(STLCal Source Target) P'"
      from this obtain \<beta> Q' where C1: "Q \<midarrow>\<beta>\<rightarrow>(STLCal Source Target) Q'" and C2: "(P', Q') \<in> Rel\<^sup>+"
                              and C3: "\<langle>P, \<alpha>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>Q, \<beta>\<rangle>"
        by blast
      assume "(Q, R) \<in> Rel"
      with B C1 obtain \<gamma> R' where C4: "R \<midarrow>\<gamma>\<rightarrow>(STLCal Source Target) R'" and C5: "(Q', R') \<in> Rel\<^sup>+"
                              and C6: "\<langle>Q, \<beta>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>R, \<gamma>\<rangle>"
        by blast
      from C2 C5 have C7: "(P', R') \<in> Rel\<^sup>+"
        by simp
      from injective C3 C6 have "\<langle>P, \<alpha>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>R, \<gamma>\<rangle>"
        using related_labels_trans_inj[of P \<alpha> Q \<beta> R \<gamma>]
        by simp
      with C4 C7
      show "\<exists>\<gamma> R'. R \<midarrow>\<gamma>\<rightarrow>(STLCal Source Target) R' \<and> (P', R') \<in> Rel\<^sup>+ \<and> \<langle>P, \<alpha>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>R, \<gamma>\<rangle>"
        by blast
    qed
  qed
  with simulation show "strong_labelled_simulation_encL (Rel\<^sup>+)"
    by blast
  from simulation A1 A2[of "Rel\<^sup>="] show "strong_labelled_simulation_encL (Rel\<^sup>*)"
      using trancl_reflcl[of Rel]
    by fast
qed

subsection \<open>Contrasimulation\<close>

text \<open>A weak labelled contrasimulation on encoded labels is relation R such that if (P, Q) in R
      and P evolves to some P' using word w of labels then there exists some v and Q' such that Q
      evolves to Q' using v, (Q', P') in R, and w and v are related words.\<close>

abbreviation (in encodingLS_encL) weak_labelled_contrasimulation_encL
  :: "(('procS, 'procT) Proc \<times> ('procS, 'procT) Proc) set \<Rightarrow> bool" where
  "weak_labelled_contrasimulation_encL Rel \<equiv>
   \<forall>P Q w P'. (P, Q) \<in> Rel \<and> P \<midarrow>\<frown>w\<rightarrow>(STLCal Source Target)* P' \<longrightarrow>
   (\<exists>v Q'. Q \<midarrow>\<frown>v\<rightarrow>(STLCal Source Target)* Q' \<and> (Q', P') \<in> Rel \<and> \<langle>P, w\<rangle> \<equiv>\<lparr>\<rparr>* \<langle>Q, v\<rangle>)"

text \<open>The reflexive closure of a weak contrasimulation on encoded words is a weak contrasimulation.
      For the transitive closure we require again that the label encoding is injective.\<close>

lemma (in encodingLS_encL) weak_labelled_contrasimulation_encL_and_refl_closure:
  fixes Rel :: "(('procS, 'procT) Proc \<times> ('procS, 'procT) Proc) set"
  assumes contrasimulation: "weak_labelled_contrasimulation_encL Rel"
  shows "weak_labelled_contrasimulation_encL (Rel\<^sup>=)"
  using assms
proof auto
  fix P Q w P'
  assume "weak_labelled_contrasimulation_encL Rel" and "P \<midarrow>\<frown>w\<rightarrow>(STLCal Source Target)* P'"
     and "(P, Q) \<in> Rel"
  hence "\<exists>v Q'. Q \<midarrow>\<frown>v\<rightarrow>(STLCal Source Target)* Q' \<and> (Q', P') \<in> Rel \<and> \<langle>P, w\<rangle> \<equiv>\<lparr>\<rparr>* \<langle>Q, v\<rangle>"
    by simp
  thus "\<exists>v Q'. Q \<midarrow>\<frown>v\<rightarrow>(STLCal Source Target)* Q' \<and> ((Q', P') \<in> Rel \<or> Q' = P') \<and>
        \<langle>P, w\<rangle> \<equiv>\<lparr>\<rparr>* \<langle>Q, v\<rangle>"
    by blast
next
  fix Q w P'
  assume "Q \<midarrow>\<frown>w\<rightarrow>(STLCal Source Target)* P'"
  moreover have "Q \<sim>ST Q"
    using source_or_target[of Q]
    by presburger
  hence "\<langle>Q, w\<rangle> \<equiv>\<lparr>\<rparr>* \<langle>Q, w\<rangle>"
    unfolding related_words_def
    by simp
  ultimately show "\<exists>v Q'. Q \<midarrow>\<frown>v\<rightarrow>(STLCal Source Target)* Q' \<and> ((Q', P') \<in> Rel \<or> Q' = P') \<and>
                   \<langle>Q, w\<rangle> \<equiv>\<lparr>\<rparr>* \<langle>Q, v\<rangle>"
    by blast
qed

lemma (in encodingLS_encL) weak_labelled_contrasimulation_encL_and_closures:
  fixes Rel :: "(('procS, 'procT) Proc \<times> ('procS, 'procT) Proc) set"
  assumes contrasimulation: "weak_labelled_contrasimulation_encL Rel"
      and injective:        "inj encL"
    shows "weak_labelled_contrasimulation_encL (Rel\<^sup>=)"
      and "weak_labelled_contrasimulation_encL (Rel\<^sup>+)"
      and "weak_labelled_contrasimulation_encL (Rel\<^sup>*)"
proof -
  from contrasimulation show A1: "weak_labelled_contrasimulation_encL (Rel\<^sup>=)"
    using weak_labelled_contrasimulation_encL_and_refl_closure[of Rel]
    by simp
  have A2: "\<And>Rel. weak_labelled_contrasimulation_encL Rel \<Longrightarrow>
            weak_labelled_contrasimulation_encL (Rel\<^sup>+)"
  proof clarify
    fix Rel P Q w P'
    assume B1: "weak_labelled_contrasimulation_encL Rel"
    assume "(P, Q) \<in> Rel\<^sup>+" and "P \<midarrow>\<frown>w\<rightarrow>(STLCal Source Target)* P'"
    thus "\<exists>v Q'. Q \<midarrow>\<frown>v\<rightarrow>(STLCal Source Target)* Q' \<and> (Q', P') \<in> Rel\<^sup>+ \<and> \<langle>P, w\<rangle> \<equiv>\<lparr>\<rparr>* \<langle>Q, v\<rangle>"
    proof (induct arbitrary: P')
      fix Q P'
      assume "(P, Q) \<in> Rel" and "P \<midarrow>\<frown>w\<rightarrow>(STLCal Source Target)* P'"
      with B1 obtain v Q' where "Q \<midarrow>\<frown>v\<rightarrow>(STLCal Source Target)* Q'" and "(Q', P') \<in> Rel"
                            and "\<langle>P, w\<rangle> \<equiv>\<lparr>\<rparr>* \<langle>Q, v\<rangle>"
        by blast
      thus "\<exists>v Q'. Q \<midarrow>\<frown>v\<rightarrow>(STLCal Source Target)* Q' \<and> (Q', P') \<in> Rel\<^sup>+ \<and> \<langle>P, w\<rangle> \<equiv>\<lparr>\<rparr>* \<langle>Q, v\<rangle>"
        by auto
    next
      case (step Q R P')
      assume "\<And>P'. P \<midarrow>\<frown>w\<rightarrow>(STLCal Source Target)* P' \<Longrightarrow>
              (\<exists>v Q'. Q \<midarrow>\<frown>v\<rightarrow>(STLCal Source Target)* Q' \<and> (Q', P') \<in> Rel\<^sup>+ \<and> \<langle>P, w\<rangle> \<equiv>\<lparr>\<rparr>* \<langle>Q, v\<rangle>)"
         and C1: "P \<midarrow>\<frown>w\<rightarrow>(STLCal Source Target)* P'"
      from this obtain v Q' where C2: "Q \<midarrow>\<frown>v\<rightarrow>(STLCal Source Target)* Q'"
                              and C3: "(Q', P') \<in> Rel\<^sup>+" and C4: "\<langle>P, w\<rangle> \<equiv>\<lparr>\<rparr>* \<langle>Q, v\<rangle>"
        by blast
      assume "(Q, R) \<in> Rel"
      with B1 C2 obtain y R' where C5: "R \<midarrow>\<frown>y\<rightarrow>(STLCal Source Target)* R'"
                               and C6: "(R', Q') \<in> Rel\<^sup>+" and C7: "\<langle>Q, v\<rangle> \<equiv>\<lparr>\<rparr>* \<langle>R, y\<rangle>"
        by blast
      from C3 C6 have C8: "(R', P') \<in> Rel\<^sup>+"
        by simp
      from injective C4 C7 have "\<langle>P, w\<rangle> \<equiv>\<lparr>\<rparr>* \<langle>R, y\<rangle>"
        using related_words_trans_inj[of P w Q v R y]
        by simp
      with C5 C8
      show "\<exists>y R'. R \<midarrow>\<frown>y\<rightarrow>(STLCal Source Target)* R' \<and> (R', P') \<in> Rel\<^sup>+ \<and> \<langle>P, w\<rangle> \<equiv>\<lparr>\<rparr>* \<langle>R, y\<rangle>"
        by blast
    qed
  qed
  with contrasimulation show "weak_labelled_contrasimulation_encL (Rel\<^sup>+)"
    by blast
  from contrasimulation A1 A2[of"Rel\<^sup>="] show "weak_labelled_contrasimulation_encL (Rel\<^sup>*)"
    using trancl_reflcl[of Rel]
    by fast
qed

subsection \<open>Coupled Simulation\<close>

text \<open>A weak labelled coupled simulation on encoded labels is relation R such that if (P, Q) in R
      and P evolves to some P' using label a then there exists some Q' such that Q evolves to Q'
      using some b, (P', Q') in R, and a and b are related (simulation) and there exits some Q'
      such that Q evolves to Q' and (Q', P) in R (coupling).\<close>

abbreviation (in encodingLS_encL) weak_labelled_coupled_simulation_encL
  :: "(('procS, 'procT) Proc \<times> ('procS, 'procT) Proc) set \<Rightarrow> bool" where
  "weak_labelled_coupled_simulation_encL Rel \<equiv>
   \<forall>P Q. (P, Q) \<in> Rel \<longrightarrow>
   ((\<forall>\<alpha> P'. P \<midarrow>\<Zcat>\<alpha>\<rightarrow>(STLCal Source Target)* P' \<longrightarrow>
    (\<exists>\<beta> Q'. Q \<midarrow>\<Zcat>\<beta>\<rightarrow>(STLCal Source Target)* Q' \<and> (P', Q') \<in> Rel \<and> \<langle>P, \<alpha>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>Q, \<beta>\<rangle>)) \<and>
   (\<exists>Q'. Q \<rightarrow>(STLCal Source Target)* Q' \<and> (Q', P) \<in> Rel))"

text \<open>A weak labelled coupled simulation simulates words of labels including the empty word, if the
      label encoding respects the internal. The requirement on the respection of internals can be
      relaxed similar to the case of weak labelled simulation on encoded labels.\<close>

lemma (in encodingLS_encL) weak_labelled_coupled_simulation_encL_and_respection_internal:
  fixes Rel    :: "(('procS, 'procT) Proc \<times> ('procS, 'procT) Proc) set"
    and P Q P' :: "('procS, 'procT) Proc"
  assumes simulation: "weak_labelled_coupled_simulation_encL Rel"
      and relation:   "(P, Q) \<in> Rel"
      and execution:  "P \<rightarrow>(STLCal Source Target)* P'"
      and respection: "encL_respects_internal"
    shows "\<exists>Q'. Q \<rightarrow>(STLCal Source Target)* Q' \<and> (P', Q') \<in> Rel"
proof -
  from execution have "P \<midarrow>\<Zcat>\<tau>-STLCal\<rightarrow>(STLCal Source Target)* P'"
    using internalST_iff_internal
    unfolding weakLabelledStep_def
    by simp
  with simulation relation obtain \<beta> Q' where A1: "Q \<midarrow>\<Zcat>\<beta>\<rightarrow>(STLCal Source Target)* Q'"
                                         and A2: "(P', Q') \<in> Rel" and A3: "\<langle>P, \<tau>-STLCal\<rangle> \<equiv>\<lparr>\<rparr> \<langle>Q, \<beta>\<rangle>"
    by blast
  from respection A3 have "\<beta> = \<tau>-STLCal"
    using encL_respects_internal_implies_iff_internal[of P "\<tau>-STLCal" Q \<beta>]
    by blast
  with A1 have "Q \<rightarrow>(STLCal Source Target)* Q'"
    using internalST_iff_internal
    unfolding weakLabelledStep_def
    by simp
  with A2 show "\<exists>Q'. Q \<rightarrow>(STLCal Source Target)* Q' \<and> (P', Q') \<in> Rel"
    by blast
qed

lemma (in encodingLS_encL) weak_labelled_coupled_simulation_encL_and_preservation_internal:
  fixes Rel    :: "(('procS, 'procT) Proc \<times> ('procS, 'procT) Proc) set"
    and P Q P' :: "('procS, 'procT) Proc"
  assumes simulation:   "weak_labelled_coupled_simulation_encL Rel"
      and relation:     "(P, Q) \<in> Rel"
      and execution:    "P \<rightarrow>(STLCal Source Target)* P'"
      and no_T_to_S:    "\<not>(P \<in> ProcT \<and> Q \<in> ProcS)"
      and preservation: "encL_preserves_internal"
    shows "\<exists>Q'. Q \<rightarrow>(STLCal Source Target)* Q' \<and> (P', Q') \<in> Rel"
proof -
  from execution have "P \<midarrow>\<Zcat>\<tau>-STLCal\<rightarrow>(STLCal Source Target)* P'"
    using internalST_iff_internal
    unfolding weakLabelledStep_def
    by simp
  with simulation relation obtain \<beta> Q' where A1: "Q \<midarrow>\<Zcat>\<beta>\<rightarrow>(STLCal Source Target)* Q'"
                                         and A2: "(P', Q') \<in> Rel" and A3: "\<langle>P, \<tau>-STLCal\<rangle> \<equiv>\<lparr>\<rparr> \<langle>Q, \<beta>\<rangle>"
    by blast
  have "\<beta> = \<tau>-STLCal"
  proof (cases "P \<in> ProcS")
    assume "P \<in> ProcS"
    with preservation A3 show "\<beta> = \<tau>-STLCal"
      using encL_preserves_internal_implies_source_internal_to_internal[of P Q \<beta>]
      by simp
  next
    assume "\<not>P \<in> ProcS"
    with no_T_to_S have B1: "P \<sim>ST Q"
      using source_or_target[of P] source_or_target[of Q]
      by blast
    hence B2: "\<not>\<lparr>P, \<tau>-STLCal\<rparr>\<mapsto>\<langle>Q, \<beta>\<rangle>"
      using kinds_of_encoded_label(1, 3)[of P "\<tau>-STLCal" Q \<beta>]
      by blast
    from B1 have "\<not>\<lparr>Q, \<beta>\<rparr>\<mapsto>\<langle>P, \<tau>-STLCal\<rangle>"
      using kinds_of_encoded_label(1, 3)[of Q \<beta> P "\<tau>-STLCal"]
      by blast
    with A3 B2 show "\<beta> = \<tau>-STLCal"
      using related_labels_get_condition(1)[of P "\<tau>-STLCal" Q \<beta>]
      by simp
  qed
  with A1 have "Q \<rightarrow>(STLCal Source Target)* Q'"
    using internalST_iff_internal
    unfolding weakLabelledStep_def
    by simp
  with A2 show "\<exists>Q'. Q \<rightarrow>(STLCal Source Target)* Q' \<and> (P', Q') \<in> Rel"
    by blast
qed

lemma (in encodingLS_encL) weak_labelled_coupled_simulation_encL_and_reflection_internal:
  fixes Rel    :: "(('procS, 'procT) Proc \<times> ('procS, 'procT) Proc) set"
    and P Q P' :: "('procS, 'procT) Proc"
  assumes simulation: "weak_labelled_coupled_simulation_encL Rel"
      and relation:   "(P, Q) \<in> Rel"
      and execution:  "P \<rightarrow>(STLCal Source Target)* P'"
      and no_S_to_T:  "\<not>(P \<in> ProcS \<and> Q \<in> ProcT)"
      and reflection: "encL_reflects_internal"
    shows "\<exists>Q'. Q \<rightarrow>(STLCal Source Target)* Q' \<and> (P', Q') \<in> Rel"
proof -
  from execution have "P \<midarrow>\<Zcat>\<tau>-STLCal\<rightarrow>(STLCal Source Target)* P'"
    using internalST_iff_internal
    unfolding weakLabelledStep_def
    by simp
  with simulation relation obtain \<beta> Q' where A1: "Q \<midarrow>\<Zcat>\<beta>\<rightarrow>(STLCal Source Target)* Q'"
                                         and A2: "(P', Q') \<in> Rel" and A3: "\<langle>P, \<tau>-STLCal\<rangle> \<equiv>\<lparr>\<rparr> \<langle>Q, \<beta>\<rangle>"
    by blast
  have "\<beta> = \<tau>-STLCal"
  proof (cases "P \<in> ProcS")
    assume "P \<in> ProcS"
    with no_S_to_T have B1: "P \<sim>ST Q"
      using source_or_target[of P] source_or_target[of Q]
      by blast
    hence B2: "\<not>\<lparr>P, \<tau>-STLCal\<rparr>\<mapsto>\<langle>Q, \<beta>\<rangle>"
      using kinds_of_encoded_label(1, 3)[of P "\<tau>-STLCal" Q \<beta>]
      by blast
    from B1 have "\<not>\<lparr>Q, \<beta>\<rparr>\<mapsto>\<langle>P, \<tau>-STLCal\<rangle>"
      using kinds_of_encoded_label(1, 3)[of Q \<beta> P "\<tau>-STLCal"]
      by blast
    with A3 B2 show "\<beta> = \<tau>-STLCal"
      using related_labels_get_condition(1)[of P "\<tau>-STLCal" Q \<beta>]
      by simp
  next
    assume "\<not>P \<in> ProcS"
    hence "P \<in> ProcT"
      using source_or_target[of P]
      by simp
    with reflection A3 show "\<beta> = \<tau>-STLCal"
      using encL_reflects_internal_implies_target_internal_to_internal[of P Q \<beta>]
      by simp
  qed
  with A1 have "Q \<rightarrow>(STLCal Source Target)* Q'"
    using internalST_iff_internal
    unfolding weakLabelledStep_def
    by simp
  with A2 show "\<exists>Q'. Q \<rightarrow>(STLCal Source Target)* Q' \<and> (P', Q') \<in> Rel"
    by blast
qed

lemma (in encodingLS_encL) weak_labelled_coupled_simulation_encL_and_respection_word:
  fixes Rel    :: "(('procS, 'procT) Proc \<times> ('procS, 'procT) Proc) set"
    and P Q P' :: "('procS, 'procT) Proc"
    and w v    :: "('labS, 'labT) Lab list"
  assumes simulation: "weak_labelled_coupled_simulation_encL Rel"
      and relation:   "(P, Q) \<in> Rel"
      and execution:  "P \<midarrow>\<frown>w\<rightarrow>(STLCal Source Target)* P'"
      and respection: "encL_respects_internal"
    shows "\<exists>v Q'. Q \<midarrow>\<frown>v\<rightarrow>(STLCal Source Target)* Q' \<and> (P', Q') \<in> Rel \<and> \<langle>P, w\<rangle> \<equiv>\<lparr>\<rparr>* \<langle>Q, v\<rangle>"
proof -
  define Cal where Cal_def: "Cal = STLCal Source Target"
  with execution have "P \<midarrow>\<frown>w\<rightarrow>Cal* P'"
    by simp
  from this simulation relation respection Cal_def
  show "\<exists>v Q'. Q \<midarrow>\<frown>v\<rightarrow>(STLCal Source Target)* Q' \<and> (P', Q') \<in> Rel \<and> \<langle>P, w\<rangle> \<equiv>\<lparr>\<rparr>* \<langle>Q, v\<rangle>"
  proof (induct arbitrary: v)
    case (WLS_Nil P Cal P')
    assume "P \<rightarrow>Cal* P'" and "Cal = STLCal Source Target"
    hence "P \<rightarrow>(STLCal Source Target)* P'"
      by simp
    moreover assume "weak_labelled_coupled_simulation_encL Rel" and "(P, Q) \<in> Rel"
                and "encL_respects_internal"
    ultimately obtain Q' where A1: "Q \<rightarrow>(STLCal Source Target)* Q'" and A2: "(P', Q') \<in> Rel"
      using weak_labelled_simulation_encL_and_respection_internal[of Rel P Q P']
      by blast
    from A1 have A3: "Q \<midarrow>\<frown>[]\<rightarrow>(STLCal Source Target)* Q'"
      using weakLabelledSequence.WLS_Nil[of Q "STLCal Source Target" Q']
      by simp
    have "\<langle>P, []\<rangle> \<equiv>\<lparr>\<rparr>* \<langle>Q, []\<rangle>"
      using ELNil[of P Q] ELNil[of Q P] source_or_target[of P] source_or_target[of Q]
      unfolding related_words_def
      by auto
    with A2 A3
      show "\<exists>v Q'. Q \<midarrow>\<frown>v\<rightarrow>(STLCal Source Target)* Q' \<and> (P', Q') \<in> Rel \<and> \<langle>P, []\<rangle> \<equiv>\<lparr>\<rparr>* \<langle>Q, v\<rangle>"
      by blast
  next
    case (WLS_Cons P w Cal P' \<alpha> P'')
    from WLS_Cons(2) have IH: "weak_labelled_coupled_simulation_encL Rel \<and> (P, Q) \<in> Rel \<and>
      encL_respects_internal \<and> Cal = STLCal Source Target \<Longrightarrow>
      \<exists>v Q'. Q \<midarrow>\<frown>v\<rightarrow>(STLCal Source Target)* Q' \<and> (P', Q') \<in> Rel \<and> \<langle>P, w\<rangle> \<equiv>\<lparr>\<rparr>* \<langle>Q, v\<rangle>"
      by simp
    assume A1: "weak_labelled_coupled_simulation_encL Rel" and "(P, Q) \<in> Rel"
       and "encL_respects_internal" and A2: "Cal = STLCal Source Target"
    with IH obtain v Q' where A3: "Q \<midarrow>\<frown>v\<rightarrow>(STLCal Source Target)* Q'" and A4: "(P', Q') \<in> Rel"
                          and A5: "\<langle>P, w\<rangle> \<equiv>\<lparr>\<rparr>* \<langle>Q, v\<rangle>"
      by blast
    assume "P' \<midarrow>\<Zcat>\<alpha>\<rightarrow>Cal* P''"
    with A1 A2 A4 obtain \<beta> Q'' where A6: "Q' \<midarrow>\<Zcat>\<beta>\<rightarrow>(STLCal Source Target)* Q''"
                                 and A7: "(P'', Q'') \<in> Rel" and A8: "\<langle>P', \<alpha>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>Q', \<beta>\<rangle>"
      by blast
    with A3 A6 have A9: "Q \<midarrow>\<frown>(v@[\<beta>])\<rightarrow>(STLCal Source Target)* Q''"
      using weakLabelledSequence.WLS_Cons[of Q v "STLCal Source Target" Q' \<beta> Q'']
      by simp
    assume "P \<midarrow>\<frown>w\<rightarrow>Cal* P'"
    with A2 have A10: "P \<sim>ST P'"
      using weakLabelledSequenceST_STLCal_weakLabelledSequence[of P w P']
      by blast
    from A3 have "Q \<sim>ST Q'"
      using weakLabelledSequenceST_STLCal_weakLabelledSequence[of Q v Q']
      by blast
    with A5 A8 A10 have "\<langle>P, (w@[\<alpha>])\<rangle> \<equiv>\<lparr>\<rparr>* \<langle>Q, (v@[\<beta>])\<rangle>"
      using related_words_compose[of P w Q v P' \<alpha> Q' \<beta>]
      by simp
    with A7 A9
    show "\<exists>v Q''. Q \<midarrow>\<frown>v\<rightarrow>(STLCal Source Target)* Q'' \<and> (P'', Q'') \<in> Rel \<and> \<langle>P, w@[\<alpha>]\<rangle> \<equiv>\<lparr>\<rparr>* \<langle>Q, v\<rangle>"
      by blast
  qed
qed

lemma (in encodingLS_encL) weak_labelled_coupled_simulation_encL_and_preservation_word:
  fixes Rel    :: "(('procS, 'procT) Proc \<times> ('procS, 'procT) Proc) set"
    and P Q P' :: "('procS, 'procT) Proc"
    and w v    :: "('labS, 'labT) Lab list"
  assumes simulation:   "weak_labelled_coupled_simulation_encL Rel"
      and relation:     "(P, Q) \<in> Rel"
      and execution:    "P \<midarrow>\<frown>w\<rightarrow>(STLCal Source Target)* P'"
      and no_T_to_S:    "\<not>(P \<in> ProcT \<and> Q \<in> ProcS)"
      and preservation: "encL_preserves_internal"
    shows "\<exists>v Q'. Q \<midarrow>\<frown>v\<rightarrow>(STLCal Source Target)* Q' \<and> (P', Q') \<in> Rel \<and> \<langle>P, w\<rangle> \<equiv>\<lparr>\<rparr>* \<langle>Q, v\<rangle>"
proof -
  define Cal where Cal_def: "Cal = STLCal Source Target"
  with execution have "P \<midarrow>\<frown>w\<rightarrow>Cal* P'"
    by simp
  from this simulation relation no_T_to_S preservation Cal_def
  show "\<exists>v Q'. Q \<midarrow>\<frown>v\<rightarrow>(STLCal Source Target)* Q' \<and> (P', Q') \<in> Rel \<and> \<langle>P, w\<rangle> \<equiv>\<lparr>\<rparr>* \<langle>Q, v\<rangle>"
  proof (induct arbitrary: v)
    case (WLS_Nil P Cal P')
    assume "P \<rightarrow>Cal* P'" and "Cal = STLCal Source Target"
    hence "P \<rightarrow>(STLCal Source Target)* P'"
      by simp
    moreover assume "weak_labelled_coupled_simulation_encL Rel" and "(P, Q) \<in> Rel"
                and "\<not>(P \<in> ProcT \<and> Q \<in> ProcS)" and "encL_preserves_internal"
    ultimately obtain Q' where A1: "Q \<rightarrow>(STLCal Source Target)* Q'" and A2: "(P', Q') \<in> Rel"
      using weak_labelled_simulation_encL_and_preservation_internal[of Rel P Q P']
      by blast
    from A1 have A3: "Q \<midarrow>\<frown>[]\<rightarrow>(STLCal Source Target)* Q'"
      using weakLabelledSequence.WLS_Nil[of Q "STLCal Source Target" Q']
      by simp
    have "\<langle>P, []\<rangle> \<equiv>\<lparr>\<rparr>* \<langle>Q, []\<rangle>"
      using ELNil[of P Q] ELNil[of Q P] source_or_target[of P] source_or_target[of Q]
      unfolding related_words_def
      by auto
    with A2 A3
    show "\<exists>v Q'. Q \<midarrow>\<frown>v\<rightarrow>(STLCal Source Target)* Q' \<and> (P', Q') \<in> Rel \<and> \<langle>P, []\<rangle> \<equiv>\<lparr>\<rparr>* \<langle>Q, v\<rangle>"
      by blast
  next
    case (WLS_Cons P w Cal P' \<alpha> P'')
    from WLS_Cons(2) have IH: "weak_labelled_coupled_simulation_encL Rel \<and> (P, Q) \<in> Rel \<and>
      \<not>(P \<in> ProcT \<and> Q \<in> ProcS) \<and> encL_preserves_internal \<and> Cal = STLCal Source Target \<Longrightarrow>
      \<exists>v Q'. Q \<midarrow>\<frown>v\<rightarrow>(STLCal Source Target)* Q' \<and> (P', Q') \<in> Rel \<and> \<langle>P, w\<rangle> \<equiv>\<lparr>\<rparr>* \<langle>Q, v\<rangle>"
      by simp
    assume A1: "weak_labelled_coupled_simulation_encL Rel" and "(P, Q) \<in> Rel"
       and "\<not>(P \<in> ProcT \<and> Q \<in> ProcS)" and "encL_preserves_internal"
       and A2: "Cal = STLCal Source Target"
    with IH obtain v Q' where A3: "Q \<midarrow>\<frown>v\<rightarrow>(STLCal Source Target)* Q'" and A4: "(P', Q') \<in> Rel"
                          and A5: "\<langle>P, w\<rangle> \<equiv>\<lparr>\<rparr>* \<langle>Q, v\<rangle>"
      by blast
    assume "P' \<midarrow>\<Zcat>\<alpha>\<rightarrow>Cal* P''"
    with A1 A2 A4 obtain \<beta> Q'' where A6: "Q' \<midarrow>\<Zcat>\<beta>\<rightarrow>(STLCal Source Target)* Q''"
                                 and A7: "(P'', Q'') \<in> Rel" and A8: "\<langle>P', \<alpha>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>Q', \<beta>\<rangle>"
      by blast
    with A3 A6 have A9: "Q \<midarrow>\<frown>(v@[\<beta>])\<rightarrow>(STLCal Source Target)* Q''"
      using weakLabelledSequence.WLS_Cons[of Q v "STLCal Source Target" Q' \<beta> Q'']
      by simp
    assume "P \<midarrow>\<frown>w\<rightarrow>Cal* P'"
    with A2 have A10: "P \<sim>ST P'"
      using weakLabelledSequenceST_STLCal_weakLabelledSequence[of P w P']
      by blast
    from A3 have "Q \<sim>ST Q'"
      using weakLabelledSequenceST_STLCal_weakLabelledSequence[of Q v Q']
      by blast
    with A5 A8 A10 have "\<langle>P, (w@[\<alpha>])\<rangle> \<equiv>\<lparr>\<rparr>* \<langle>Q, (v@[\<beta>])\<rangle>"
      using related_words_compose[of P w Q v P' \<alpha> Q' \<beta>]
      by simp
    with A7 A9
    show "\<exists>v Q''. Q \<midarrow>\<frown>v\<rightarrow>(STLCal Source Target)* Q'' \<and> (P'', Q'') \<in> Rel \<and> \<langle>P, w@[\<alpha>]\<rangle> \<equiv>\<lparr>\<rparr>* \<langle>Q, v\<rangle>"
      by blast
  qed
qed

lemma (in encodingLS_encL) weak_labelled_coupled_simulation_encL_and_reflection_word:
  fixes Rel    :: "(('procS, 'procT) Proc \<times> ('procS, 'procT) Proc) set"
    and P Q P' :: "('procS, 'procT) Proc"
    and w v    :: "('labS, 'labT) Lab list"
  assumes simulation: "weak_labelled_coupled_simulation_encL Rel"
      and relation:   "(P, Q) \<in> Rel"
      and execution:  "P \<midarrow>\<frown>w\<rightarrow>(STLCal Source Target)* P'"
      and no_S_to_T:  "\<not>(P \<in> ProcS \<and> Q \<in> ProcT)"
      and reflection: "encL_reflects_internal"
    shows "\<exists>v Q'. Q \<midarrow>\<frown>v\<rightarrow>(STLCal Source Target)* Q' \<and> (P', Q') \<in> Rel \<and> \<langle>P, w\<rangle> \<equiv>\<lparr>\<rparr>* \<langle>Q, v\<rangle>"
proof -
  define Cal where Cal_def: "Cal = STLCal Source Target"
  with execution have "P \<midarrow>\<frown>w\<rightarrow>Cal* P'"
    by simp
  from this simulation relation no_S_to_T reflection Cal_def
  show "\<exists>v Q'. Q \<midarrow>\<frown>v\<rightarrow>(STLCal Source Target)* Q' \<and> (P', Q') \<in> Rel \<and> \<langle>P, w\<rangle> \<equiv>\<lparr>\<rparr>* \<langle>Q, v\<rangle>"
  proof (induct arbitrary: v)
    case (WLS_Nil P Cal P')
    assume "P \<rightarrow>Cal* P'" and "Cal = STLCal Source Target"
    hence "P \<rightarrow>(STLCal Source Target)* P'"
      by simp
    moreover assume "weak_labelled_coupled_simulation_encL Rel" and "(P, Q) \<in> Rel"
                and "\<not>(P \<in> ProcS \<and> Q \<in> ProcT)" and "encL_reflects_internal"
    ultimately obtain Q' where A1: "Q \<rightarrow>(STLCal Source Target)* Q'" and A2: "(P', Q') \<in> Rel"
      using weak_labelled_simulation_encL_and_reflection_internal[of Rel P Q P']
      by blast
    from A1 have A3: "Q \<midarrow>\<frown>[]\<rightarrow>(STLCal Source Target)* Q'"
      using weakLabelledSequence.WLS_Nil[of Q "STLCal Source Target" Q']
      by simp
    have "\<langle>P, []\<rangle> \<equiv>\<lparr>\<rparr>* \<langle>Q, []\<rangle>"
      using ELNil[of P Q] ELNil[of Q P] source_or_target[of P] source_or_target[of Q]
      unfolding related_words_def
      by auto
    with A2 A3
    show "\<exists>v Q'. Q \<midarrow>\<frown>v\<rightarrow>(STLCal Source Target)* Q' \<and> (P', Q') \<in> Rel \<and> \<langle>P, []\<rangle> \<equiv>\<lparr>\<rparr>* \<langle>Q, v\<rangle>"
      by blast
  next
    case (WLS_Cons P w Cal P' \<alpha> P'')
    from WLS_Cons(2) have IH: "weak_labelled_coupled_simulation_encL Rel \<and> (P, Q) \<in> Rel \<and>
      \<not>(P \<in> ProcS \<and> Q \<in> ProcT) \<and> encL_reflects_internal \<and> Cal = STLCal Source Target \<Longrightarrow>
      \<exists>v Q'. Q \<midarrow>\<frown>v\<rightarrow>(STLCal Source Target)* Q' \<and> (P', Q') \<in> Rel \<and> \<langle>P, w\<rangle> \<equiv>\<lparr>\<rparr>* \<langle>Q, v\<rangle>"
      by simp
    assume A1: "weak_labelled_coupled_simulation_encL Rel" and "(P, Q) \<in> Rel"
       and "\<not>(P \<in> ProcS \<and> Q \<in> ProcT)" and "encL_reflects_internal"
       and A2: "Cal = STLCal Source Target"
    with IH obtain v Q' where A3: "Q \<midarrow>\<frown>v\<rightarrow>(STLCal Source Target)* Q'" and A4: "(P', Q') \<in> Rel"
                          and A5: "\<langle>P, w\<rangle> \<equiv>\<lparr>\<rparr>* \<langle>Q, v\<rangle>"
      by blast
    assume "P' \<midarrow>\<Zcat>\<alpha>\<rightarrow>Cal* P''"
    with A1 A2 A4 obtain \<beta> Q'' where A6: "Q' \<midarrow>\<Zcat>\<beta>\<rightarrow>(STLCal Source Target)* Q''"
                                 and A7: "(P'', Q'') \<in> Rel" and A8: "\<langle>P', \<alpha>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>Q', \<beta>\<rangle>"
      by blast
    with A3 A6 have A9: "Q \<midarrow>\<frown>(v@[\<beta>])\<rightarrow>(STLCal Source Target)* Q''"
      using weakLabelledSequence.WLS_Cons[of Q v "STLCal Source Target" Q' \<beta> Q'']
      by simp
    assume "P \<midarrow>\<frown>w\<rightarrow>Cal* P'"
    with A2 have A10: "P \<sim>ST P'"
      using weakLabelledSequenceST_STLCal_weakLabelledSequence[of P w P']
      by blast
    from A3 have "Q \<sim>ST Q'"
      using weakLabelledSequenceST_STLCal_weakLabelledSequence[of Q v Q']
      by blast
    with A5 A8 A10 have "\<langle>P, (w@[\<alpha>])\<rangle> \<equiv>\<lparr>\<rparr>* \<langle>Q, (v@[\<beta>])\<rangle>"
      using related_words_compose[of P w Q v P' \<alpha> Q' \<beta>]
      by simp
    with A7 A9
    show "\<exists>v Q''. Q \<midarrow>\<frown>v\<rightarrow>(STLCal Source Target)* Q'' \<and> (P'', Q'') \<in> Rel \<and> \<langle>P, w@[\<alpha>]\<rangle> \<equiv>\<lparr>\<rparr>* \<langle>Q, v\<rangle>"
      by blast
  qed
qed

text \<open>A weak coupled simulation combines the conditions on a weak simulation and a weak
      contrasimulation, if the label encoding respects the internal. Instead of respection of the
      internal we can require instead preservation and that the coupled simulation does not relate
      a target term and a source term.\<close>

lemma (in encodingLS_encL)
  wl_coupled_simulation_encL_and_respection_versus_simulation_and_contrasimulation:
  fixes Rel :: "(('procS, 'procT) Proc \<times> ('procS, 'procT) Proc) set"
  assumes respection: "encL_respects_internal"
  shows "weak_labelled_coupled_simulation_encL Rel
         = (weak_labelled_simulation_encL Rel \<and> weak_labelled_contrasimulation_encL Rel)"
proof auto
  fix P Q w P'
  assume A1: "weak_labelled_coupled_simulation_encL Rel" and "(P, Q) \<in> Rel"
     and "P \<midarrow>\<frown>w\<rightarrow>(STLCal Source Target)* P'"
  with respection obtain v Q' where A2: "Q \<midarrow>\<frown>v\<rightarrow>(STLCal Source Target)* Q'"
                                and A3: "(P', Q') \<in> Rel" and A4: "\<langle>P, w\<rangle> \<equiv>\<lparr>\<rparr>* \<langle>Q, v\<rangle>"
    using weak_labelled_coupled_simulation_encL_and_respection_word[of Rel P Q w P']
    by blast
  from A1 A3 obtain Q'' where A5: "Q' \<rightarrow>(STLCal Source Target)* Q''" and A6: "(Q'', P') \<in> Rel"
    by blast
  from A2 A5 have "Q \<midarrow>\<frown>v\<rightarrow>(STLCal Source Target)* Q''"
    using weakLabelledSequence_extend_by_internal[of Q v "STLCal Source Target" Q' Q'']
    by simp
  with A4 A6
  show "\<exists>v Q''. Q \<midarrow>\<frown>v\<rightarrow>(STLCal Source Target)* Q'' \<and> (Q'', P') \<in> Rel \<and> \<langle>P, w\<rangle> \<equiv>\<lparr>\<rparr>* \<langle>Q, v\<rangle>"
    by blast
next
  fix P Q
  assume "weak_labelled_contrasimulation_encL Rel" and "(P, Q) \<in> Rel"
  moreover have "P \<midarrow>\<frown>[]\<rightarrow>(STLCal Source Target)* P"
    using WTS_refl[of P "STLCal Source Target"] WLS_Nil[of P "STLCal Source Target" P]
    by simp
  ultimately obtain v Q' where A1: "Q \<midarrow>\<frown>v\<rightarrow>(STLCal Source Target)* Q'" and A2: "(Q', P) \<in> Rel"
                           and A3: "\<langle>P, []\<rangle> \<equiv>\<lparr>\<rparr>* \<langle>Q, v\<rangle>"
    by blast
  from A3 have "v = []"
    using related_words_length[of P "[]" Q v]
    by simp
  with A1 have "Q \<rightarrow>(STLCal Source Target)* Q'"
    using internal_weakLabelledSequence[of Q "STLCal Source Target" Q']
    by simp
  with A2 show "\<exists>Q'. Q \<rightarrow>(STLCal Source Target)* Q' \<and> (Q', P) \<in> Rel"
    by blast
qed

lemma (in encodingLS_encL)
  wl_coupled_simulation_encL_and_preservation_versus_simulation_and_contrasimulation:
  fixes Rel :: "(('procS, 'procT) Proc \<times> ('procS, 'procT) Proc) set"
  assumes no_T_to_S:    "\<forall>P Q. (P, Q) \<in> Rel \<longrightarrow> \<not>(P \<in> ProcT \<and> Q \<in> ProcS)"
      and preservation: "encL_preserves_internal"
  shows "weak_labelled_coupled_simulation_encL Rel
         = (weak_labelled_simulation_encL Rel \<and> weak_labelled_contrasimulation_encL Rel)"
proof auto
  fix P Q w P'
  assume A1: "weak_labelled_coupled_simulation_encL Rel" and "(P, Q) \<in> Rel"
     and "P \<midarrow>\<frown>w\<rightarrow>(STLCal Source Target)* P'"
  with no_T_to_S preservation obtain v Q' where A2: "Q \<midarrow>\<frown>v\<rightarrow>(STLCal Source Target)* Q'"
                                            and A3: "(P', Q') \<in> Rel" and A4: "\<langle>P, w\<rangle> \<equiv>\<lparr>\<rparr>* \<langle>Q, v\<rangle>"
    using weak_labelled_coupled_simulation_encL_and_preservation_word[of Rel P Q w P']
    by blast
  from A1 A3 obtain Q'' where A5: "Q' \<rightarrow>(STLCal Source Target)* Q''" and A6: "(Q'', P') \<in> Rel"
    by blast
  from A2 A5 have "Q \<midarrow>\<frown>v\<rightarrow>(STLCal Source Target)* Q''"
    using weakLabelledSequence_extend_by_internal[of Q v "STLCal Source Target" Q' Q'']
    by simp
  with A4 A6
  show "\<exists>v Q''. Q \<midarrow>\<frown>v\<rightarrow>(STLCal Source Target)* Q'' \<and> (Q'', P') \<in> Rel \<and> \<langle>P, w\<rangle> \<equiv>\<lparr>\<rparr>* \<langle>Q, v\<rangle>"
    by blast
next
  fix P Q
  assume "weak_labelled_contrasimulation_encL Rel" and "(P, Q) \<in> Rel"
  moreover have "P \<midarrow>\<frown>[]\<rightarrow>(STLCal Source Target)* P"
    using WTS_refl[of P "STLCal Source Target"] WLS_Nil[of P "STLCal Source Target" P]
    by simp
  ultimately obtain v Q' where A1: "Q \<midarrow>\<frown>v\<rightarrow>(STLCal Source Target)* Q'" and A2: "(Q', P) \<in> Rel"
                           and A3: "\<langle>P, []\<rangle> \<equiv>\<lparr>\<rparr>* \<langle>Q, v\<rangle>"
    by blast
  from A3 have "v = []"
    using related_words_length[of P "[]" Q v]
    by simp
  with A1 have "Q \<rightarrow>(STLCal Source Target)* Q'"
    using internal_weakLabelledSequence[of Q "STLCal Source Target" Q']
    by simp
  with A2 show "\<exists>Q'. Q \<rightarrow>(STLCal Source Target)* Q' \<and> (Q', P) \<in> Rel"
    by blast
qed

text \<open>The reflexive and/or transitive closure of a weak coupled simulation is a weak coupled
      simulation, where we need for transitivity that the label encoding is injective and preserves
      the internal. Injectivity is necessary to combine the labels and the preservation of the
      internal is necessary to simulation internal steps.\<close>

lemma (in encodingLS_encL) weak_labelled_coupled_simulation_encL_and_refl_closure:
  fixes Rel :: "(('procS, 'procT) Proc \<times> ('procS, 'procT) Proc) set"
  assumes coupledSimulation: "weak_labelled_coupled_simulation_encL Rel"
  shows "weak_labelled_coupled_simulation_encL (Rel\<^sup>=)"
proof auto
  fix P Q \<alpha> P'
  assume "P \<midarrow>\<Zcat>\<alpha>\<rightarrow>(STLCal Source Target)* P'" and "(P, Q) \<in> Rel"
  with coupledSimulation
  have "\<exists>\<beta> Q'. Q \<midarrow>\<Zcat>\<beta>\<rightarrow>(STLCal Source Target)* Q' \<and> (P', Q') \<in> Rel \<and> \<langle>P, \<alpha>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>Q, \<beta>\<rangle>"
    by simp
  thus "\<exists>\<beta> Q'. Q \<midarrow>\<Zcat>\<beta>\<rightarrow>(STLCal Source Target)* Q' \<and> ((P', Q') \<in> Rel \<or> P' = Q') \<and> \<langle>P, \<alpha>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>Q, \<beta>\<rangle>"
    by blast
next
  fix P Q
  assume "(P, Q) \<in> Rel"
  with coupledSimulation have "\<exists>Q'. Q \<rightarrow>(STLCal Source Target)* Q' \<and> (Q', P) \<in> Rel"
    by simp
  thus "\<exists>Q'. Q \<rightarrow>(STLCal Source Target)* Q' \<and> ((Q', P) \<in> Rel \<or> Q' = P)"
    by blast
next
  fix Q \<alpha> P'
  assume "Q \<midarrow>\<Zcat>\<alpha>\<rightarrow>(STLCal Source Target)* P'"
  moreover have "Q \<sim>ST Q"
    using source_or_target[of Q]
    by presburger
  hence "\<langle>Q, \<alpha>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>Q, \<alpha>\<rangle>"
    unfolding related_labels_def
    by simp
  ultimately
  show "\<exists>\<beta> Q'. Q \<midarrow>\<Zcat>\<beta>\<rightarrow>(STLCal Source Target)* Q' \<and> ((P', Q') \<in> Rel \<or> P' = Q') \<and> \<langle>Q, \<alpha>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>Q, \<beta>\<rangle>"
    by blast
next
  fix Q
  have "Q \<rightarrow>(STLCal Source Target)* Q"
    using WTS_refl[of Q "STLCal Source Target"]
    by simp
  thus "\<exists>Q'. Q \<rightarrow>(STLCal Source Target)* Q' \<and> ((Q', Q) \<in> Rel \<or> Q' = Q)"
    by blast
qed

lemma (in encodingLS_encL) weak_labelled_coupled_simulation_encL_and_closures:
  fixes Rel :: "(('procS, 'procT) Proc \<times> ('procS, 'procT) Proc) set"
  assumes coupledSimulation: "weak_labelled_coupled_simulation_encL Rel"
      and injective:         "inj encL"
      and preserves:         "encL_preserves_internal"
    shows "weak_labelled_coupled_simulation_encL (Rel\<^sup>=)"
      and "weak_labelled_coupled_simulation_encL (Rel\<^sup>+)"
      and "weak_labelled_coupled_simulation_encL (Rel\<^sup>*)"
proof -
  from injective preserves have A1: "encL_respects_internal"
    using inj_preserves_is_respects_internal
    by blast
  with coupledSimulation have A2: "weak_labelled_simulation_encL Rel"
                          and A3: "weak_labelled_contrasimulation_encL Rel"
    using wl_coupled_simulation_encL_and_respection_versus_simulation_and_contrasimulation[of
            "Rel"]
    by simp_all
  from injective preserves A2 have A4: "weak_labelled_simulation_encL (Rel\<^sup>=)"
                               and A5: "weak_labelled_simulation_encL (Rel\<^sup>+)"
                               and A6: "weak_labelled_simulation_encL (Rel\<^sup>*)"
    using weak_labelled_simulation_encL_and_closures[of "Rel"]
    by simp_all
  from injective preserves A3 have A7: "weak_labelled_contrasimulation_encL (Rel\<^sup>=)"
                               and A8: "weak_labelled_contrasimulation_encL (Rel\<^sup>+)"
                               and A9: "weak_labelled_contrasimulation_encL (Rel\<^sup>*)"
    using weak_labelled_contrasimulation_encL_and_closures[of "Rel"]
    by simp_all
  from A1 A4 A7 show "weak_labelled_coupled_simulation_encL (Rel\<^sup>=)"
    using wl_coupled_simulation_encL_and_respection_versus_simulation_and_contrasimulation[of
            "Rel\<^sup>="]
    by simp
  from A1 A5 A8 show "weak_labelled_coupled_simulation_encL (Rel\<^sup>+)"
    using wl_coupled_simulation_encL_and_respection_versus_simulation_and_contrasimulation[of
            "Rel\<^sup>+"]
    by simp
  from A1 A6 A9 show "weak_labelled_coupled_simulation_encL (Rel\<^sup>*)"
    using wl_coupled_simulation_encL_and_respection_versus_simulation_and_contrasimulation[of
            "Rel\<^sup>*"]
    by simp
qed

subsection \<open>Correspondence Simulation\<close>

text \<open>A weak labelled correspondence simulation on encoded labels is relation R such that
      (1) if (P, Q) in R and P evolves to some P' using label a then there exist b and Q' such that
          Q evolves to Q' using b, (P', Q') in R, and a and b are related, and
      (2) if (P, Q) in R and Q evolves to some Q' using label a then there exist b, P'', and Q''
          such that P evolves to P'' using b and Q' evolves to Q'' using only internal steps,
          (P'', Q'') in R, and a and b are related.\<close>

abbreviation (in encodingLS_encL) weak_labelled_correspondence_simulation_encL
  :: "(('procS, 'procT) Proc \<times> ('procS, 'procT) Proc) set \<Rightarrow> bool" where
  "weak_labelled_correspondence_simulation_encL Rel \<equiv>
   (\<forall>P Q \<alpha> P'. (P, Q) \<in> Rel \<and> P \<midarrow>\<Zcat>\<alpha>\<rightarrow>(STLCal Source Target)* P' \<longrightarrow>
    (\<exists>\<beta> Q'. Q \<midarrow>\<Zcat>\<beta>\<rightarrow>(STLCal Source Target)* Q' \<and> (P', Q') \<in> Rel \<and> \<langle>P, \<alpha>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>Q, \<beta>\<rangle>))
   \<and> (\<forall>P Q \<beta> Q'. (P, Q) \<in> Rel \<and> Q \<midarrow>\<Zcat>\<beta>\<rightarrow>(STLCal Source Target)* Q'
      \<longrightarrow> (\<exists>\<alpha> P'' Q''. P \<midarrow>\<Zcat>\<alpha>\<rightarrow>(STLCal Source Target)* P'' \<and> Q' \<rightarrow>(STLCal Source Target)* Q'' \<and>
           (P'', Q'') \<in> Rel \<and> \<langle>P, \<alpha>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>Q, \<beta>\<rangle>))"

text \<open>The reflexive and/or transitive closure of a weak correspondence simulation is a weak
      correspondence simulation, where for transitivity we need again that the label encoding is
      injective and preserves the internal.\<close>

lemma (in encodingLS_encL) labelled_correspondence_simulation_encL_condition_trans:
  fixes P Q R :: "('procS, 'procT) Proc"
    and Rel   :: "(('procS, 'procT) Proc \<times> ('procS, 'procT) Proc) set"
  assumes A1:  "\<forall>\<beta> Q'. Q \<midarrow>\<Zcat>\<beta>\<rightarrow>(STLCal Source Target)* Q' \<longrightarrow>
                (\<exists>\<alpha> P'' Q''. P \<midarrow>\<Zcat>\<alpha>\<rightarrow>(STLCal Source Target)* P'' \<and>
                 Q' \<rightarrow>(STLCal Source Target)* Q'' \<and> (P'', Q'') \<in> Rel \<and> \<langle>P, \<alpha>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>Q, \<beta>\<rangle>)"
      and A2:  "\<forall>\<gamma> R'. R \<midarrow>\<Zcat>\<gamma>\<rightarrow>(STLCal Source Target)* R' \<longrightarrow>
                (\<exists>\<beta> Q'' R''. Q \<midarrow>\<Zcat>\<beta>\<rightarrow>(STLCal Source Target)* Q'' \<and>
                 R' \<rightarrow>(STLCal Source Target)* R'' \<and> (Q'', R'') \<in> Rel \<and> \<langle>Q, \<beta>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>R, \<gamma>\<rangle>)"
      and A3:  "weak_labelled_simulation_encL Rel"
      and A4:  "trans Rel"
      and inj: "inj encL"
      and pre: "encL_preserves_internal"
    shows "\<forall>\<gamma> R'. R \<midarrow>\<Zcat>\<gamma>\<rightarrow>(STLCal Source Target)* R' \<longrightarrow>
           (\<exists>\<alpha> P'' R''. P \<midarrow>\<Zcat>\<alpha>\<rightarrow>(STLCal Source Target)* P'' \<and>
            R' \<rightarrow>(STLCal Source Target)* R'' \<and> (P'', R'') \<in> Rel \<and> \<langle>P, \<alpha>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>R, \<gamma>\<rangle>)"
proof clarify
  fix \<gamma> R'
  assume "R \<midarrow>\<Zcat>\<gamma>\<rightarrow>(STLCal Source Target)* R'"
  with A2 obtain \<beta> Q'' R'' where A5: "Q \<midarrow>\<Zcat>\<beta>\<rightarrow>(STLCal Source Target)* Q''"
                             and A6: "R' \<rightarrow>(STLCal Source Target)* R''" and A7: "(Q'', R'') \<in> Rel"
                             and A8: "\<langle>Q, \<beta>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>R, \<gamma>\<rangle>"
    by blast
  from A1 A5 obtain \<alpha> P''' Q''' where A9:  "P \<midarrow>\<Zcat>\<alpha>\<rightarrow>(STLCal Source Target)* P'''"
                                  and A10: "Q'' \<rightarrow>(STLCal Source Target)* Q'''"
                                  and A11: "(P''', Q''') \<in> Rel" and A12: "\<langle>P, \<alpha>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>Q, \<beta>\<rangle>"
    by blast
  from inj pre have "encL_respects_internal"
    using inj_preserves_is_respects_internal
    by blast
  with A3 A7 A10 obtain R''' where A13: "R'' \<rightarrow>(STLCal Source Target)* R'''"
                               and A14: "(Q''', R''') \<in> Rel"
    using weak_labelled_simulation_encL_and_respection_internal[of Rel Q'' R'' Q''']
    by blast
  from A6 A13 have A15: "R' \<rightarrow>(STLCal Source Target)* R'''"
    using weakTauSteps_trans[of R' "(STLCal Source Target)" R'' R''']
    by simp
  from A4 A11 A14 have A16: "(P''', R''') \<in> Rel"
    unfolding trans_def
    by blast
  from inj A8 A12 have "\<langle>P, \<alpha>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>R, \<gamma>\<rangle>"
    using related_labels_trans_inj[of P \<alpha> Q \<beta> R \<gamma>]
    by simp
  with A9 A15 A16 show "\<exists>\<alpha> P''' R'''. P \<midarrow>\<Zcat>\<alpha>\<rightarrow>(STLCal Source Target)* P''' \<and>
                        R' \<rightarrow>(STLCal Source Target)* R''' \<and> (P''', R''') \<in> Rel \<and> \<langle>P, \<alpha>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>R, \<gamma>\<rangle>"
    by blast
qed

lemma (in encodingLS_encL) weak_labelled_correspondence_simulation_encL_and_refl_closure:
  fixes Rel :: "(('procS, 'procT) Proc \<times> ('procS, 'procT) Proc) set"
  assumes corrSim: "weak_labelled_correspondence_simulation_encL Rel"
  shows "weak_labelled_correspondence_simulation_encL (Rel\<^sup>=)"
proof
  from corrSim show "weak_labelled_simulation_encL (Rel\<^sup>=)"
    using weak_labelled_simulation_encL_and_refl_closure[of "Rel"]
    by blast
next
  show "\<forall>P Q \<beta> Q'. (P, Q) \<in> Rel\<^sup>= \<and> Q \<midarrow>\<Zcat>\<beta>\<rightarrow>(STLCal Source Target)* Q'
        \<longrightarrow> (\<exists>\<alpha> P'' Q''. P \<midarrow>\<Zcat>\<alpha>\<rightarrow>(STLCal Source Target)* P'' \<and> Q' \<rightarrow>(STLCal Source Target)* Q'' \<and>
            (P'', Q'') \<in> Rel\<^sup>= \<and> \<langle>P, \<alpha>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>Q, \<beta>\<rangle>)"
  proof clarify
    fix P Q \<beta> Q'
    assume "(P, Q) \<in> Rel\<^sup>=" and A1: "Q \<midarrow>\<Zcat>\<beta>\<rightarrow>(STLCal Source Target)* Q'"
    moreover have "P = Q \<Longrightarrow> \<exists>P'' Q''. P \<midarrow>\<Zcat>\<beta>\<rightarrow>(STLCal Source Target)* P'' \<and>
                   Q' \<rightarrow>(STLCal Source Target)* Q'' \<and> (P'', Q'') \<in> Rel\<^sup>= \<and> \<langle>Q, \<beta>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>Q, \<beta>\<rangle>"
    proof -
      assume "P = Q"
      moreover have "Q' \<rightarrow>(STLCal Source Target)* Q'"
        using WTS_refl[of Q' "STLCal Source Target"]
        by simp
      moreover have "Q \<sim>ST Q"
        using source_or_target[of Q]
        by presburger
      hence "\<langle>Q, \<beta>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>Q, \<beta>\<rangle>"
        unfolding related_labels_def
        by simp
      ultimately show "\<exists>P'' Q''. P \<midarrow>\<Zcat>\<beta>\<rightarrow>(STLCal Source Target)* P'' \<and>
                       Q' \<rightarrow>(STLCal Source Target)* Q'' \<and> (P'', Q'') \<in> Rel\<^sup>= \<and> \<langle>Q, \<beta>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>Q, \<beta>\<rangle>"
        using A1
        by blast
    qed
    moreover have "(P, Q) \<in> Rel \<Longrightarrow> \<exists>\<alpha> P'' Q''. P \<midarrow>\<Zcat>\<alpha>\<rightarrow>(STLCal Source Target)* P'' \<and>
                   Q' \<rightarrow>(STLCal Source Target)* Q'' \<and> (P'', Q'') \<in> Rel\<^sup>= \<and> \<langle>P, \<alpha>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>Q, \<beta>\<rangle>"
    proof -
      assume "(P, Q) \<in> Rel"
      with corrSim A1 obtain \<alpha> P'' Q'' where "P \<midarrow>\<Zcat>\<alpha>\<rightarrow>(STLCal Source Target)* P''"
        and "Q' \<rightarrow>(STLCal Source Target)* Q''" and "(P'', Q'') \<in> Rel" and "\<langle>P, \<alpha>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>Q, \<beta>\<rangle>"
        by blast
      thus "\<exists>\<alpha> P'' Q''. P \<midarrow>\<Zcat>\<alpha>\<rightarrow>(STLCal Source Target)* P'' \<and> Q' \<rightarrow>(STLCal Source Target)* Q'' \<and>
            (P'', Q'') \<in> Rel\<^sup>= \<and> \<langle>P, \<alpha>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>Q, \<beta>\<rangle>"
        by auto
    qed
    ultimately show "\<exists>\<alpha> P'' Q''. P \<midarrow>\<Zcat>\<alpha>\<rightarrow>(STLCal Source Target)* P'' \<and>
                     Q' \<rightarrow>(STLCal Source Target)* Q'' \<and> (P'', Q'') \<in> Rel\<^sup>= \<and> \<langle>P, \<alpha>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>Q, \<beta>\<rangle>"
      by auto
  qed
qed

lemma (in encodingLS_encL) weak_labelled_correspondence_simulation_encL_and_closures:
  fixes Rel :: "(('procS, 'procT) Proc \<times> ('procS, 'procT) Proc) set"
  assumes corrSim:   "weak_labelled_correspondence_simulation_encL Rel"
      and injective: "inj encL"
      and preserves: "encL_preserves_internal"
    shows "weak_labelled_correspondence_simulation_encL (Rel\<^sup>=)"
      and "weak_labelled_correspondence_simulation_encL (Rel\<^sup>+)"
      and "weak_labelled_correspondence_simulation_encL (Rel\<^sup>*)"
proof -
  from corrSim show A1: "weak_labelled_correspondence_simulation_encL (Rel\<^sup>=)"
    using weak_labelled_correspondence_simulation_encL_and_refl_closure[of Rel]
    by simp
  have A2: "\<And>Rel. weak_labelled_correspondence_simulation_encL Rel
            \<Longrightarrow> weak_labelled_correspondence_simulation_encL (Rel\<^sup>+)"
  proof
    fix Rel
    assume "weak_labelled_correspondence_simulation_encL Rel"
    with injective preserves show "weak_labelled_simulation_encL (Rel\<^sup>+)"
      using weak_labelled_simulation_encL_and_closures(2)[of "Rel"]
      by blast
  next
    fix Rel
    assume B: "weak_labelled_correspondence_simulation_encL Rel"
    show "\<forall>P Q \<beta> Q'. (P, Q) \<in> Rel\<^sup>+ \<and> Q \<midarrow>\<Zcat>\<beta>\<rightarrow>(STLCal Source Target)* Q' \<longrightarrow>
          (\<exists>\<alpha> P'' Q''. P \<midarrow>\<Zcat>\<alpha>\<rightarrow>(STLCal Source Target)* P'' \<and> Q' \<rightarrow>(STLCal Source Target)* Q'' \<and>
          (P'', Q'') \<in> Rel\<^sup>+ \<and> \<langle>P, \<alpha>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>Q, \<beta>\<rangle>)"
    proof clarify
      fix P Q \<beta> Q'
      assume "(P, Q) \<in> Rel\<^sup>+" and "Q \<midarrow>\<Zcat>\<beta>\<rightarrow>(STLCal Source Target)* Q'"
      thus "\<exists>\<alpha> P'' Q''. P \<midarrow>\<Zcat>\<alpha>\<rightarrow>(STLCal Source Target)* P'' \<and> Q' \<rightarrow>(STLCal Source Target)* Q'' \<and>
            (P'', Q'') \<in> Rel\<^sup>+ \<and> \<langle>P, \<alpha>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>Q, \<beta>\<rangle>"
      proof (induct arbitrary: \<beta> Q')
        fix Q \<beta> Q'
        assume "(P, Q) \<in> Rel" and "Q \<midarrow>\<Zcat>\<beta>\<rightarrow>(STLCal Source Target)* Q'"
        with B obtain \<alpha> P'' Q'' where C1: "P \<midarrow>\<Zcat>\<alpha>\<rightarrow>(STLCal Source Target)* P''"
                                  and C2: "Q' \<rightarrow>(STLCal Source Target)* Q''"
                                  and C3: "(P'', Q'') \<in> Rel" and C4: "\<langle>P, \<alpha>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>Q, \<beta>\<rangle>"
          by blast
        from C3 have "(P'', Q'') \<in> Rel\<^sup>+"
          by simp
        with C1 C2 C4 show "\<exists>\<alpha> P'' Q''. P \<midarrow>\<Zcat>\<alpha>\<rightarrow>(STLCal Source Target)* P'' \<and>
          Q' \<rightarrow>(STLCal Source Target)* Q'' \<and> (P'', Q'') \<in> Rel\<^sup>+ \<and> \<langle>P, \<alpha>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>Q, \<beta>\<rangle>"
          by blast
      next
        case (step Q R \<alpha> R')
        assume "\<And>\<beta> Q'. Q \<midarrow>\<Zcat>\<beta>\<rightarrow>(STLCal Source Target)* Q' \<Longrightarrow>
                \<exists>\<alpha> P'' Q''. P \<midarrow>\<Zcat>\<alpha>\<rightarrow>(STLCal Source Target)* P'' \<and>
                Q' \<rightarrow>(STLCal Source Target)* Q'' \<and> (P'', Q'') \<in> Rel\<^sup>+ \<and> \<langle>P, \<alpha>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>Q, \<beta>\<rangle>"
        moreover assume "(Q, R) \<in> Rel"
        with B have "\<And>\<beta> R'. R \<midarrow>\<Zcat>\<beta>\<rightarrow>(STLCal Source Target)* R' \<Longrightarrow>
                     \<exists>\<alpha> Q'' R''. Q \<midarrow>\<Zcat>\<alpha>\<rightarrow>(STLCal Source Target)* Q'' \<and>
                     R' \<rightarrow>(STLCal Source Target)* R'' \<and> (Q'', R'') \<in> Rel\<^sup>+ \<and> \<langle>Q, \<alpha>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>R, \<beta>\<rangle>"
          by blast
        moreover from injective preserves B have "weak_labelled_simulation_encL (Rel\<^sup>+)"
          using weak_labelled_simulation_encL_and_closures(2)[of "Rel"]
          by blast
        moreover have "trans (Rel\<^sup>+)"
          using trans_trancl[of Rel]
          by blast
        moreover assume "R \<midarrow>\<Zcat>\<alpha>\<rightarrow>(STLCal Source Target)* R'"
        ultimately show "\<exists>\<gamma> P'' R''. P \<midarrow>\<Zcat>\<gamma>\<rightarrow>(STLCal Source Target)* P'' \<and>
                         R' \<rightarrow>(STLCal Source Target)* R'' \<and> (P'', R'') \<in> Rel\<^sup>+ \<and> \<langle>P, \<gamma>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>R, \<alpha>\<rangle>"
          using labelled_correspondence_simulation_encL_condition_trans[of Q P "Rel\<^sup>+" R]
                injective preserves
          by auto
      qed
    qed
  qed
  from corrSim A2[of "Rel"] show "weak_labelled_correspondence_simulation_encL (Rel\<^sup>+)"
    by blast
  from A1 A2[of "Rel\<^sup>="] show "weak_labelled_correspondence_simulation_encL (Rel\<^sup>*)"
    using trancl_reflcl[of Rel]
    by auto
qed

subsection \<open>Bisimulation\<close>

text \<open>A weak labelled bisimulation on encoded labels is a relation R such that
      (1) if (P, Q) in R and P evolves to some P' using a then there exist b and Q' such that Q
          evolves to Q' using b, (P', Q') in R, and a and b are related, and
      (2) if (P, Q) in R and Q evolves to some Q' using a then there exist b and P' such that P
          evolves to P' using b, (P', Q') in R, and a and b are related.\<close>

abbreviation (in encodingLS_encL) weak_labelled_bisimulation_encL
  :: "(('procS, 'procT) Proc \<times> ('procS, 'procT) Proc) set \<Rightarrow> bool" where
  "weak_labelled_bisimulation_encL Rel \<equiv>
   (\<forall>P Q \<alpha> P'. ((P, Q) \<in> Rel \<and> P \<midarrow>\<Zcat>\<alpha>\<rightarrow>(STLCal Source Target)* P') \<longrightarrow>
    (\<exists>\<beta> Q'. Q \<midarrow>\<Zcat>\<beta>\<rightarrow>(STLCal Source Target)* Q' \<and> (P', Q') \<in> Rel \<and> \<langle>P, \<alpha>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>Q, \<beta>\<rangle>)) \<and>
   (\<forall>P Q \<beta> Q'. (P, Q) \<in> Rel \<and> Q \<midarrow>\<Zcat>\<beta>\<rightarrow>(STLCal Source Target)* Q' \<longrightarrow>
    (\<exists>\<alpha> P'. P \<midarrow>\<Zcat>\<alpha>\<rightarrow>(STLCal Source Target)* P' \<and> (P', Q') \<in> Rel \<and> \<langle>P, \<alpha>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>Q, \<beta>\<rangle>))"

text \<open>A symetric weak simulation is a weak bisimulation.\<close>

lemma (in encodingLS_encL) symm_weak_labelled_simulation_encL_is_bisimulation:
  fixes Rel :: "(('procS, 'procT) Proc \<times> ('procS, 'procT) Proc) set"
  assumes "sym Rel"
      and "weak_labelled_simulation_encL Rel"
    shows "weak_labelled_bisimulation_encL Rel"
  using assms symD[of Rel] related_labels_sym
  by blast

text \<open>If a relation as well as its inverse are weak simulations, then this relation is a weak
      bisimulation.\<close>

lemma (in encodingLS_encL) weak_labelled_simulations_encL_impl_bisimulation:
  fixes Rel :: "(('procS, 'procT) Proc \<times> ('procS, 'procT) Proc) set"
  assumes sim:    "weak_labelled_simulation_encL Rel"
      and simInv: "weak_labelled_simulation_encL (Rel\<inverse>)"
    shows "weak_labelled_bisimulation_encL Rel"
proof auto
  fix P Q \<alpha> P'
  assume "(P, Q) \<in> Rel" and "P \<midarrow>\<Zcat>\<alpha>\<rightarrow>(STLCal Source Target)* P'"
  with sim show "\<exists>\<beta> Q'. Q \<midarrow>\<Zcat>\<beta>\<rightarrow>(STLCal Source Target)* Q' \<and> (P', Q') \<in> Rel \<and> \<langle>P, \<alpha>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>Q, \<beta>\<rangle>"
    by simp
next
  fix P Q \<beta> Q'
  assume "(P, Q) \<in> Rel"
  hence "(Q, P) \<in> Rel\<inverse>"
    by simp
  moreover assume "Q \<midarrow>\<Zcat>\<beta>\<rightarrow>(STLCal Source Target)* Q'"
  ultimately obtain \<alpha> P' where A1: "P \<midarrow>\<Zcat>\<alpha>\<rightarrow>(STLCal Source Target)* P'" and A2: "(Q', P') \<in> Rel\<inverse>"
                           and A3: "\<langle>P, \<alpha>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>Q, \<beta>\<rangle>"
    using simInv related_labels_sym
    by blast
  from A2 have "(P', Q') \<in> Rel"
    by induct
  with A1 A3 show "\<exists>\<alpha> P'. P \<midarrow>\<Zcat>\<alpha>\<rightarrow>(STLCal Source Target)* P' \<and> (P', Q') \<in> Rel \<and> \<langle>P, \<alpha>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>Q, \<beta>\<rangle>"
    by blast
qed

lemma (in encodingLS_encL) weak_labelled_bisimulations_encL_impl_inverse_is_simulation:
  fixes Rel :: "(('procS, 'procT) Proc \<times> ('procS, 'procT) Proc) set"
  assumes bisim: "weak_labelled_bisimulation_encL Rel"
  shows "weak_labelled_simulation_encL (Rel\<inverse>)"
proof clarify
  fix P Q \<alpha> P'
  assume "(Q, P) \<in> Rel"
  moreover assume "P \<midarrow>\<Zcat>\<alpha>\<rightarrow>(STLCal Source Target)* P'"
  ultimately obtain \<beta> Q' where A1: "Q \<midarrow>\<Zcat>\<beta>\<rightarrow>(STLCal Source Target)* Q'" and A2: "(Q', P') \<in> Rel"
                           and A3: "\<langle>P, \<alpha>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>Q, \<beta>\<rangle>"
    using bisim related_labels_sym
    by blast
  from A2 have "(P', Q') \<in> Rel\<inverse>"
    by simp
  with A1 A3 show "\<exists>\<beta> Q'. Q \<midarrow>\<Zcat>\<beta>\<rightarrow>(STLCal Source Target)* Q' \<and> (P', Q') \<in> Rel\<inverse> \<and> \<langle>P, \<alpha>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>Q, \<beta>\<rangle>"
    by blast
qed

lemma (in encodingLS_encL) weak_labelled_simulations_encL_iff_bisimulation:
  fixes Rel :: "(('procS, 'procT) Proc \<times> ('procS, 'procT) Proc) set"
  shows "(weak_labelled_simulation_encL Rel \<and> weak_labelled_simulation_encL (Rel\<inverse>)) =
         weak_labelled_bisimulation_encL Rel"
  using weak_labelled_simulations_encL_impl_bisimulation[of "Rel"]
        weak_labelled_bisimulations_encL_impl_inverse_is_simulation[of "Rel"]
  by blast

text \<open>A weak bisimulation is a weak correspondence simulation.\<close>

lemma (in encodingLS_encL) weak_labelled_bisimulation_encL_is_correspondence_simulation:
  fixes Rel :: "(('procS, 'procT) Proc \<times> ('procS, 'procT) Proc) set"
  assumes bisim: "weak_labelled_bisimulation_encL Rel"
  shows "weak_labelled_correspondence_simulation_encL Rel"
proof
  from bisim show "weak_labelled_simulation_encL Rel"
    by blast
next
  show "\<forall>P Q \<beta> Q'. (P, Q) \<in> Rel \<and> Q \<midarrow>\<Zcat>\<beta>\<rightarrow>(STLCal Source Target)* Q' \<longrightarrow>
        (\<exists>\<alpha> P'' Q''. P \<midarrow>\<Zcat>\<alpha>\<rightarrow>(STLCal Source Target)* P'' \<and> Q' \<rightarrow>(STLCal Source Target)* Q'' \<and>
        (P'', Q'') \<in> Rel \<and> \<langle>P, \<alpha>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>Q, \<beta>\<rangle>)"
  proof clarify
    fix P Q \<beta> Q'
    assume "(P, Q) \<in> Rel" and "Q \<midarrow>\<Zcat>\<beta>\<rightarrow>(STLCal Source Target)* Q'"
    with bisim obtain \<alpha> P' where "P \<midarrow>\<Zcat>\<alpha>\<rightarrow>(STLCal Source Target)* P'" and "(P', Q') \<in> Rel"
                             and "\<langle>P, \<alpha>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>Q, \<beta>\<rangle>"
      by blast
    moreover have "Q' \<rightarrow>(STLCal Source Target)* Q'"
      using WTS_refl[of Q' "STLCal Source Target"]
      by simp
    ultimately show "(\<exists>\<alpha> P'' Q''. P \<midarrow>\<Zcat>\<alpha>\<rightarrow>(STLCal Source Target)* P'' \<and>
                     Q' \<rightarrow>(STLCal Source Target)* Q'' \<and> (P'', Q'') \<in> Rel \<and> \<langle>P, \<alpha>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>Q, \<beta>\<rangle>)"
      by blast
  qed
qed

text \<open>The reflexive, symmetric, and/or transitive closure of a weak bisimulation is a weak
      bisimulation, where we need for transitivity that the label encoding is injective.\<close>

lemma (in encodingLS_encL) weak_labelled_bisimulation_encL_and_refl_closure:
  fixes Rel :: "(('procS, 'procT) Proc \<times> ('procS, 'procT) Proc) set"
  assumes bisim: "weak_labelled_bisimulation_encL Rel"
  shows "weak_labelled_bisimulation_encL (Rel\<^sup>=)"
proof auto
  fix P Q \<alpha> P'
  assume "P \<midarrow>\<Zcat>\<alpha>\<rightarrow>(STLCal Source Target)* P'" and "(P, Q) \<in> Rel"
  with bisim have "\<exists>\<beta> Q'. Q \<midarrow>\<Zcat>\<beta>\<rightarrow>(STLCal Source Target)* Q' \<and> (P', Q') \<in> Rel \<and> \<langle>P, \<alpha>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>Q, \<beta>\<rangle>"
    by simp
  thus "\<exists>\<beta> Q'. Q \<midarrow>\<Zcat>\<beta>\<rightarrow>(STLCal Source Target)* Q' \<and> ((P', Q') \<in> Rel \<or> P' = Q') \<and> \<langle>P, \<alpha>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>Q, \<beta>\<rangle>"
    by blast
next
  fix Q \<alpha> P'
  assume "Q \<midarrow>\<Zcat>\<alpha>\<rightarrow>(STLCal Source Target)* P'"
  moreover have "Q \<sim>ST Q"
    using source_or_target[of Q]
    by presburger
  hence "\<langle>Q, \<alpha>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>Q, \<alpha>\<rangle>"
    unfolding related_labels_def
    by simp
  ultimately
  show "\<exists>\<beta> Q'. Q \<midarrow>\<Zcat>\<beta>\<rightarrow>(STLCal Source Target)* Q' \<and> ((P', Q') \<in> Rel \<or> P' = Q') \<and> \<langle>Q, \<alpha>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>Q, \<beta>\<rangle>"
    by blast
next
  fix P Q \<beta> Q'
  assume "Q \<midarrow>\<Zcat>\<beta>\<rightarrow>(STLCal Source Target)* Q'" and "(P, Q) \<in> Rel"
  with bisim have "\<exists>\<alpha> P'. P \<midarrow>\<Zcat>\<alpha>\<rightarrow>(STLCal Source Target)* P' \<and> (P', Q') \<in> Rel \<and> \<langle>P, \<alpha>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>Q, \<beta>\<rangle>"
    by simp
  thus "\<exists>\<alpha> P'. P \<midarrow>\<Zcat>\<alpha>\<rightarrow>(STLCal Source Target)* P' \<and> ((P', Q') \<in> Rel \<or> P' = Q') \<and> \<langle>P, \<alpha>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>Q, \<beta>\<rangle>"
    by blast
next
  fix Q \<beta> Q'
  assume "Q \<midarrow>\<Zcat>\<beta>\<rightarrow>(STLCal Source Target)* Q'"
  moreover have "Q \<sim>ST Q"
    using source_or_target[of Q]
    by presburger
  hence "\<langle>Q, \<beta>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>Q, \<beta>\<rangle>"
    unfolding related_labels_def
    by simp
  ultimately
  show "\<exists>\<alpha> P'. Q \<midarrow>\<Zcat>\<alpha>\<rightarrow>(STLCal Source Target)* P' \<and> ((P', Q') \<in> Rel \<or> P' = Q') \<and> \<langle>Q, \<alpha>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>Q, \<beta>\<rangle>"
    by blast
qed

lemma (in encodingLS_encL) weak_labelled_bisimulation_encL_and_symm_closure:
  fixes Rel :: "(('procS, 'procT) Proc \<times> ('procS, 'procT) Proc) set"
  assumes bisim: "weak_labelled_bisimulation_encL Rel"
  shows "weak_labelled_bisimulation_encL (symcl Rel)"
  using bisim related_labels_sym
  by (auto simp add: symcl_def, blast+)

lemma (in encodingLS_encL) weak_labelled_bisimulation_encL_and_closures:
  fixes Rel :: "(('procS, 'procT) Proc \<times> ('procS, 'procT) Proc) set"
  assumes bisim:     "weak_labelled_bisimulation_encL Rel"
      and injective: "inj encL"
    shows "weak_labelled_bisimulation_encL (Rel\<^sup>=)"
      and "weak_labelled_bisimulation_encL (symcl Rel)"
      and "weak_labelled_bisimulation_encL (Rel\<^sup>+)"
      and "weak_labelled_bisimulation_encL (symcl (Rel\<^sup>=))"
      and "weak_labelled_bisimulation_encL (Rel\<^sup>*)"
      and "weak_labelled_bisimulation_encL ((symcl (Rel\<^sup>=))\<^sup>+)"
proof -
  from bisim show A1: "weak_labelled_bisimulation_encL (Rel\<^sup>=)"
    using weak_labelled_bisimulation_encL_and_refl_closure[of Rel]
    by simp
  from bisim show "weak_labelled_bisimulation_encL (symcl Rel)"
    using weak_labelled_bisimulation_encL_and_symm_closure[of Rel]
    by simp
  have A2: "\<And>Rel. weak_labelled_bisimulation_encL Rel \<Longrightarrow> weak_labelled_bisimulation_encL (Rel\<^sup>+)"
  proof
    fix Rel
    assume "weak_labelled_bisimulation_encL Rel"
    with injective show "weak_labelled_simulation_encL (Rel\<^sup>+)"
      using weak_labelled_simulation_encL_and_closures(2)[of "Rel"]
      by blast
  next
    fix Rel
    assume B: "weak_labelled_bisimulation_encL Rel"
    show "\<forall>P Q \<beta> Q'. (P, Q) \<in> Rel\<^sup>+ \<and> Q \<midarrow>\<Zcat>\<beta>\<rightarrow>(STLCal Source Target)* Q' \<longrightarrow>
          (\<exists>\<alpha> P'. P \<midarrow>\<Zcat>\<alpha>\<rightarrow>(STLCal Source Target)* P' \<and> (P', Q') \<in> Rel\<^sup>+ \<and> \<langle>P, \<alpha>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>Q, \<beta>\<rangle>)"
    proof clarify
      fix P Q \<beta> Q'
      assume "(P, Q) \<in> Rel\<^sup>+" and "Q \<midarrow>\<Zcat>\<beta>\<rightarrow>(STLCal Source Target)* Q'"
      thus "\<exists>\<alpha> P'. P \<midarrow>\<Zcat>\<alpha>\<rightarrow>(STLCal Source Target)* P' \<and> (P', Q') \<in> Rel\<^sup>+ \<and> \<langle>P, \<alpha>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>Q, \<beta>\<rangle>"
      proof (induct arbitrary: \<beta> Q')
        fix Q \<beta> Q'
        assume "(P, Q) \<in> Rel" and "Q \<midarrow>\<Zcat>\<beta>\<rightarrow>(STLCal Source Target)* Q'"
        with B obtain \<alpha> P' where "P \<midarrow>\<Zcat>\<alpha>\<rightarrow>(STLCal Source Target)* P'" and "(P', Q') \<in> Rel"
                             and "\<langle>P, \<alpha>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>Q, \<beta>\<rangle>"
          by blast
        thus "\<exists>\<alpha> P'. P \<midarrow>\<Zcat>\<alpha>\<rightarrow>(STLCal Source Target)* P' \<and> (P', Q') \<in> Rel\<^sup>+ \<and> \<langle>P, \<alpha>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>Q, \<beta>\<rangle>"
          by auto
      next
        case (step Q R \<gamma> R')
        assume "(Q, R) \<in> Rel" and "R \<midarrow>\<Zcat>\<gamma>\<rightarrow>(STLCal Source Target)* R'"
        with B obtain \<beta> Q' where C1: "Q \<midarrow>\<Zcat>\<beta>\<rightarrow>(STLCal Source Target)* Q'" and C2: "(Q', R') \<in> Rel\<^sup>+"
                             and C3: "\<langle>Q, \<beta>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>R, \<gamma>\<rangle>"
          by blast
        assume "\<And>\<beta> Q'. Q \<midarrow>\<Zcat>\<beta>\<rightarrow>(STLCal Source Target)* Q' \<Longrightarrow>
                \<exists>\<alpha> P'. P \<midarrow>\<Zcat>\<alpha>\<rightarrow>(STLCal Source Target)* P' \<and> (P', Q') \<in> Rel\<^sup>+ \<and> \<langle>P, \<alpha>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>Q, \<beta>\<rangle>"
        with C1 obtain \<alpha> P' where C4: "P \<midarrow>\<Zcat>\<alpha>\<rightarrow>(STLCal Source Target)* P'"
                              and C5: "(P', Q') \<in> Rel\<^sup>+" and C6: "\<langle>P, \<alpha>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>Q, \<beta>\<rangle>"
          by blast
        from C2 C5 have C7: "(P', R') \<in> Rel\<^sup>+"
          by simp
        from injective C3 C6 have "\<langle>P, \<alpha>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>R, \<gamma>\<rangle>"
          using related_labels_trans_inj[of P \<alpha> Q \<beta>  R \<gamma>]
          by simp
        with C4 C7
        show "\<exists>\<alpha> P'. P \<midarrow>\<Zcat>\<alpha>\<rightarrow>(STLCal Source Target)* P' \<and> (P', R') \<in> Rel\<^sup>+ \<and> \<langle>P, \<alpha>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>R, \<gamma>\<rangle>"
          by blast
      qed
    qed
  qed
  from bisim A2[of "Rel"] show "weak_labelled_bisimulation_encL (Rel\<^sup>+)"
    by blast
  from A1 show "weak_labelled_bisimulation_encL (symcl (Rel\<^sup>=))"
    using weak_labelled_bisimulation_encL_and_symm_closure[of "Rel\<^sup>="]
    by blast
  from A1 A2[of "Rel\<^sup>="] show "weak_labelled_bisimulation_encL (Rel\<^sup>*)"
    using trancl_reflcl[of Rel]
    by auto
  from A1 A2[of "symcl (Rel\<^sup>=)"] show "weak_labelled_bisimulation_encL ((symcl (Rel\<^sup>=))\<^sup>+)"
    using weak_labelled_bisimulation_encL_and_symm_closure[of "Rel\<^sup>="]
    by blast
qed

text \<open>A strong labelled bisimulation on encoded labels is a relation R such that
      (1) if (P, Q) in R and P' is a derivative of P using a then there exist b and Q' such that
          Q' is a derivative of Q using b, (P', Q') in R, and a and b are related, and
      (2) if (P, Q) in R and Q' is a derivative of Q using a then there exist b and P' such that
          P' is a derivative of P using b, (P', Q') in R, and a and b are related.\<close>

abbreviation (in encodingLS_encL) strong_labelled_bisimulation_encL
  :: "(('procS, 'procT) Proc \<times> ('procS, 'procT) Proc) set \<Rightarrow> bool" where
  "strong_labelled_bisimulation_encL Rel \<equiv>
   (\<forall>P Q \<alpha> P'. (P, Q) \<in> Rel \<and> P \<midarrow>\<alpha>\<rightarrow>(STLCal Source Target) P' \<longrightarrow>
   (\<exists>\<beta> Q'. Q \<midarrow>\<beta>\<rightarrow>(STLCal Source Target) Q' \<and> (P', Q') \<in> Rel \<and> \<langle>P, \<alpha>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>Q, \<beta>\<rangle>))
   \<and> (\<forall>P Q \<beta> Q'. (P, Q) \<in> Rel \<and> Q \<midarrow>\<beta>\<rightarrow>(STLCal Source Target) Q' \<longrightarrow>
      (\<exists>\<alpha> P'. P \<midarrow>\<alpha>\<rightarrow>(STLCal Source Target) P' \<and> (P', Q') \<in> Rel \<and> \<langle>P, \<alpha>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>Q, \<beta>\<rangle>))"

text \<open>A symetric strong simulation is a strong bisimulation.\<close>

lemma (in encodingLS_encL) symm_strong_labelled_simulation_encL_is_bisimulation:
  fixes Rel :: "(('procS, 'procT) Proc \<times> ('procS, 'procT) Proc) set"
  assumes "sym Rel"
      and "strong_labelled_simulation_encL Rel"
    shows "strong_labelled_bisimulation_encL Rel"
  using assms symD[of Rel] related_labels_sym
  by blast

text \<open>If a relation as well as its inverse are strong simulations, then this relation is a strong
      bisimulation.\<close>

lemma (in encodingLS_encL) strong_labelled_simulations_encL_impl_bisimulation:
  fixes Rel :: "(('procS, 'procT) Proc \<times> ('procS, 'procT) Proc) set"
  assumes sim:    "strong_labelled_simulation_encL Rel"
      and simInv: "strong_labelled_simulation_encL (Rel\<inverse>)"
    shows "strong_labelled_bisimulation_encL Rel"
proof auto
  fix P Q \<alpha> P'
  assume "(P, Q) \<in> Rel" and "P \<midarrow>\<alpha>\<rightarrow>(STLCal Source Target) P'"
  with sim show "\<exists>\<beta> Q'. Q \<midarrow>\<beta>\<rightarrow>(STLCal Source Target) Q' \<and> (P', Q') \<in> Rel \<and> \<langle>P, \<alpha>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>Q, \<beta>\<rangle>"
    by simp
next
  fix P Q \<beta> Q'
  assume "(P, Q) \<in> Rel"
  hence "(Q, P) \<in> Rel\<inverse>"
    by simp
  moreover assume "Q \<midarrow>\<beta>\<rightarrow>(STLCal Source Target) Q'"
  ultimately obtain \<alpha> P' where A1: "P \<midarrow>\<alpha>\<rightarrow>(STLCal Source Target) P'" and A2: "(Q', P') \<in> Rel\<inverse>"
                           and A3: "\<langle>P, \<alpha>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>Q, \<beta>\<rangle>"
    using simInv related_labels_sym
    by blast
  from A2 have "(P', Q') \<in> Rel"
    by induct
  with A1 A3 show "\<exists>\<alpha> P'. P \<midarrow>\<alpha>\<rightarrow>(STLCal Source Target) P' \<and> (P', Q') \<in> Rel \<and> \<langle>P, \<alpha>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>Q, \<beta>\<rangle>"
    by blast
qed

lemma (in encodingLS_encL) strong_labelled_bisimulations_encL_impl_inverse_is_simulation:
  fixes Rel :: "(('procS, 'procT) Proc \<times> ('procS, 'procT) Proc) set"
  assumes bisim: "strong_labelled_bisimulation_encL Rel"
  shows "strong_labelled_simulation_encL (Rel\<inverse>)"
proof clarify
  fix P Q \<alpha> P'
  assume "(Q, P) \<in> Rel"
  moreover assume "P \<midarrow>\<alpha>\<rightarrow>(STLCal Source Target) P'"
  ultimately obtain \<beta> Q' where A1: "Q \<midarrow>\<beta>\<rightarrow>(STLCal Source Target) Q'" and A2: "(Q', P') \<in> Rel"
                           and A3: "\<langle>P, \<alpha>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>Q, \<beta>\<rangle>"
    using bisim related_labels_sym
    by blast
  from A2 have "(P', Q') \<in> Rel\<inverse>"
    by simp
  with A1 A3 show "\<exists>\<beta> Q'. Q \<midarrow>\<beta>\<rightarrow>(STLCal Source Target) Q' \<and> (P', Q') \<in> Rel\<inverse> \<and> \<langle>P, \<alpha>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>Q, \<beta>\<rangle>"
    by blast
qed

lemma (in encodingLS_encL) strong_labelled_simulations_encL_iff_bisimulation:
  fixes Rel :: "(('procS, 'procT) Proc \<times> ('procS, 'procT) Proc) set"
  shows "(strong_labelled_simulation_encL Rel \<and> strong_labelled_simulation_encL (Rel\<inverse>)) =
         strong_labelled_bisimulation_encL Rel"
  using strong_labelled_simulations_encL_impl_bisimulation[of "Rel"]
        strong_labelled_bisimulations_encL_impl_inverse_is_simulation[of "Rel"]
  by blast

text \<open>A strong bisimulation is a weak bisimulation, if the label encoding respects the internal.
      Since bisimulation is symmetric, we cannot relax the requirement on the respection of the
      internal.\<close>

lemma (in encodingLS_encL) strong_labelled_bisimulation_encL_impl_weak_simulation_of_internal:
  fixes Rel    :: "(('procS, 'procT) Proc \<times> ('procS, 'procT) Proc) set"
    and P Q Q' :: "('procS, 'procT) Proc"
  assumes bisim:    "strong_labelled_bisimulation_encL Rel"
      and relation: "(P, Q) \<in> Rel"
      and internal: "Q \<rightarrow>(STLCal Source Target)* Q'"
      and respects: "encL_respects_internal"
    shows "\<exists>P'. P \<rightarrow>(STLCal Source Target)* P' \<and> (P', Q') \<in> Rel"
proof -
  define Cal where Cal_def: "Cal = STLCal Source Target"
  with internal have "Q \<rightarrow>Cal* Q'"
    by simp
  from this bisim relation Cal_def show "\<exists>P'. P \<rightarrow>(STLCal Source Target)* P' \<and> (P', Q') \<in> Rel"
  proof induct
    case (WTS_refl Q Cal)
    have "P \<rightarrow>(STLCal Source Target)* P"
      using weakTauStep.WTS_refl[of P "STLCal Source Target"]
      by simp
    moreover assume "(P, Q) \<in> Rel"
    ultimately show "\<exists>P'. P \<rightarrow>(STLCal Source Target)* P' \<and> (P', Q) \<in> Rel"
      by blast
  next
    case (WTS_trans Q Cal Q' Q'')
    from WTS_trans(2) have IH: "strong_labelled_bisimulation_encL Rel \<and> (P, Q) \<in> Rel \<and>
                                Cal = STLCal Source Target \<Longrightarrow>
                                \<exists>P'. P \<rightarrow>(STLCal Source Target)* P' \<and> (P', Q') \<in> Rel"
      by simp
    assume A1: "strong_labelled_bisimulation_encL Rel"
      and "(P, Q) \<in> Rel" and A2: "Cal = STLCal Source Target"
    with IH obtain P' where A3: "P \<rightarrow>(STLCal Source Target)* P'" and A4: "(P', Q') \<in> Rel"
      by blast
    assume "Q' \<midarrow>\<tau>-Cal\<rightarrow>Cal Q''"
    with A1 A2 A4 obtain \<alpha> P'' where A5: "P' \<midarrow>\<alpha>\<rightarrow>(STLCal Source Target) P''"
      and A6: "(P'', Q'') \<in> Rel" and A7: "\<langle>P', \<alpha>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>Q', \<tau>-(STLCal Source Target)\<rangle>"
      by blast
    from respects A7 have "\<alpha> = \<tau>-(STLCal Source Target)"
      using encL_respects_internal_implies_iff_internal[of P' \<alpha> Q' "\<tau>-(STLCal Source Target)"]
            internalST_iff_internal
      by simp
    with A5 have "P' \<rightarrow>(STLCal Source Target)* P''"
      using WTS_refl[of P' "STLCal Source Target"]
            weakTauStep.WTS_trans[of P' "STLCal Source Target" P' P'']
      by simp
    with A3 have "P \<rightarrow>(STLCal Source Target)* P''"
      using weakTauSteps_trans[of P "STLCal Source Target" P' P'']
      by simp
    with A6 show "\<exists>P''. P \<rightarrow>(STLCal Source Target)* P'' \<and> (P'', Q'') \<in> Rel"
      by blast
  qed
qed

lemma (in encodingLS_encL) strong_impl_weak_labelled_bisimulation_encL:
  fixes Rel :: "(('procS, 'procT) Proc \<times> ('procS, 'procT) Proc) set"
  assumes bisim:    "strong_labelled_bisimulation_encL Rel"
      and respects: "encL_respects_internal"
    shows "weak_labelled_bisimulation_encL Rel"
proof
  from bisim respects show "weak_labelled_simulation_encL Rel"
    using strong_labelled_simulation_encL_and_respection_weak_simulation[of "Rel"]
    by blast
next
  show "\<forall>P Q \<beta> Q'. (P, Q) \<in> Rel \<and> Q \<midarrow>\<Zcat>\<beta>\<rightarrow>(STLCal Source Target)* Q' \<longrightarrow>
        (\<exists>\<alpha> P'. P \<midarrow>\<Zcat>\<alpha>\<rightarrow>(STLCal Source Target)* P' \<and> (P', Q') \<in> Rel \<and> \<langle>P, \<alpha>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>Q, \<beta>\<rangle>)"
  proof clarify
    fix P Q \<beta> Q'
    assume A1: "(P, Q) \<in> Rel" and A2: "Q \<midarrow>\<Zcat>\<beta>\<rightarrow>(STLCal Source Target)* Q'"
    thus "\<exists>\<alpha> P'. P \<midarrow>\<Zcat>\<alpha>\<rightarrow>(STLCal Source Target)* P' \<and> (P', Q') \<in> Rel \<and> \<langle>P, \<alpha>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>Q, \<beta>\<rangle>"
    proof (cases "\<beta> = \<tau>-(STLCal Source Target)")
      assume B1: "\<beta> = \<tau>-(STLCal Source Target)"
      with A2 have "Q \<rightarrow>(STLCal Source Target)* Q'"
        unfolding weakLabelledStep_def
        by simp
      with bisim respects A1 obtain P' where B2: "P \<rightarrow>(STLCal Source Target)* P'"
                                         and B3: "(P', Q') \<in> Rel"
        using strong_labelled_bisimulation_encL_impl_weak_simulation_of_internal[of Rel P Q Q']
        by blast
      from B1 B2 have B4: "P \<midarrow>\<Zcat>\<beta>\<rightarrow>(STLCal Source Target)* P'"
        unfolding weakLabelledStep_def
        by simp
      have "\<langle>P, \<beta>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>Q, \<beta>\<rangle>"
        using source_or_target[of P] source_or_target[of Q]
      proof auto
        fix S S'
        show "\<langle>SourceTerm S, \<beta>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>SourceTerm S', \<beta>\<rangle>"
          unfolding related_labels_def
          by simp
      next
        fix S T
        from respects B1 have "\<lparr>SourceTerm S, \<beta>\<rparr>\<mapsto>\<langle>TargetTerm T, \<beta>\<rangle>"
          using internalST_iff_internal
          unfolding encLST_def getSourceLabel_def getTargetLabel_def
          by auto
        thus "\<langle>SourceTerm S, \<beta>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>TargetTerm T, \<beta>\<rangle>"
          unfolding related_labels_def
          by simp
      next
        fix T S
        from respects B1 have "\<lparr>SourceTerm S, \<beta>\<rparr>\<mapsto>\<langle>TargetTerm T, \<beta>\<rangle>"
          using internalST_iff_internal
          unfolding encLST_def getSourceLabel_def getTargetLabel_def
          by auto
        thus "\<langle>TargetTerm T, \<beta>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>SourceTerm S, \<beta>\<rangle>"
          unfolding related_labels_def
          by simp
      next
        fix T T'
        show "\<langle>TargetTerm T, \<beta>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>TargetTerm T', \<beta>\<rangle>"
          unfolding related_labels_def
          by simp
      qed
      with B3 B4
      show "\<exists>\<alpha> P'. P \<midarrow>\<Zcat>\<alpha>\<rightarrow>(STLCal Source Target)* P' \<and> (P', Q') \<in> Rel \<and> \<langle>P, \<alpha>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>Q, \<beta>\<rangle>"
        by blast
    next
      assume B1: "\<beta> \<noteq> \<tau>-(STLCal Source Target)" and "Q \<midarrow>\<Zcat>\<beta>\<rightarrow>(STLCal Source Target)* Q'"
      then obtain R S where B2: "Q \<rightarrow>(STLCal Source Target)* R"
        and B3: "R \<midarrow>\<beta>\<rightarrow>(STLCal Source Target) S" and B4: "S \<rightarrow>(STLCal Source Target)* Q'"
        unfolding weakLabelledStep_def weakLabelledActionStep_def
        by auto
      from bisim respects A1 B2 obtain T where B5: "P \<rightarrow>(STLCal Source Target)* T"
                                           and B6: "(T, R) \<in> Rel"
        using strong_labelled_bisimulation_encL_impl_weak_simulation_of_internal[of Rel P Q R]
        by blast
      from bisim B3 B6 obtain \<alpha> U where B7: "T \<midarrow>\<alpha>\<rightarrow>(STLCal Source Target) U"
                                    and B8: "(U, S) \<in> Rel" and B9: "\<langle>T, \<alpha>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>R, \<beta>\<rangle>"
        by blast
      from bisim respects B4 B8 obtain P' where B10: "U \<rightarrow>(STLCal Source Target)* P'"
                                            and B11: "(P', Q') \<in> Rel"
        using strong_labelled_bisimulation_encL_impl_weak_simulation_of_internal[of Rel U S Q']
        by blast
      from respects B1 B9 have "\<alpha> \<noteq> \<tau>-(STLCal Source Target)"
        using encL_respects_internal_implies_iff_internal[of T \<alpha> R \<beta>] internalST_iff_internal
        by simp
      with B5 B7 B10 have B12: "P \<midarrow>\<Zcat>\<alpha>\<rightarrow>(STLCal Source Target)* P'"
        unfolding weakLabelledStep_def weakLabelledActionStep_def
        by auto
      from B5 have B13: "T \<sim>ST P"
        using weakTauStepsST_STLCal_weakTauSteps[of P T]
        by blast
      from B2 have "R \<sim>ST Q"
        using weakTauStepsST_STLCal_weakTauSteps[of Q R]
        by blast
      with B9 B13 have "\<langle>P, \<alpha>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>Q, \<beta>\<rangle>"
        using related_labels_exchange_processes[of T \<alpha> R \<beta> P Q]
        by simp
      with B11 B12
      show "\<exists>\<alpha> P'. P \<midarrow>\<Zcat>\<alpha>\<rightarrow>(STLCal Source Target)* P' \<and> (P', Q') \<in> Rel \<and> \<langle>P, \<alpha>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>Q, \<beta>\<rangle>"
        by blast
    qed
  qed
qed

text \<open>The reflexive, symmetric, and/or transitive closure of a strong bisimulation is a strong
      bisimulation, where for transitivitiy we need that the label encoding is injective and
      preserves the internal.\<close>

lemma (in encodingLS_encL) strong_labelled_bisimulation_encL_and_refl_closure:
  fixes Rel :: "(('procS, 'procT) Proc \<times> ('procS, 'procT) Proc) set"
  assumes bisim: "strong_labelled_bisimulation_encL Rel"
  shows "strong_labelled_bisimulation_encL (Rel\<^sup>=)"
  using bisim related_labels_refl
  by (auto simp add: refl, blast+)

lemma (in encodingLS_encL) strong_labelled_bisimulation_encL_and_symm_closure:
  fixes Rel :: "(('procS, 'procT) Proc \<times> ('procS, 'procT) Proc) set"
  assumes bisim: "strong_labelled_bisimulation_encL Rel"
  shows "strong_labelled_bisimulation_encL (symcl Rel)"
  using bisim related_labels_sym
  by (auto simp add: symcl_def, blast+)

lemma (in encodingLS_encL) strong_labelled_bisimulation_encL_and_closures:
  fixes Rel :: "(('procS, 'procT) Proc \<times> ('procS, 'procT) Proc) set"
  assumes bisim:     "strong_labelled_bisimulation_encL Rel"
      and injective: "inj encL"
      and preserves: "encL_preserves_internal"
    shows "strong_labelled_bisimulation_encL (Rel\<^sup>=)"
      and "strong_labelled_bisimulation_encL (symcl Rel)"
      and "strong_labelled_bisimulation_encL (Rel\<^sup>+)"
      and "strong_labelled_bisimulation_encL (symcl (Rel\<^sup>=))"
      and "strong_labelled_bisimulation_encL (Rel\<^sup>*)"
      and "strong_labelled_bisimulation_encL ((symcl (Rel\<^sup>=))\<^sup>+)"
proof -
  from bisim show A1: "strong_labelled_bisimulation_encL (Rel\<^sup>=)"
    using strong_labelled_bisimulation_encL_and_refl_closure[of Rel]
    by simp
  from bisim show "strong_labelled_bisimulation_encL (symcl Rel)"
    using strong_labelled_bisimulation_encL_and_symm_closure[of Rel]
    by simp
  have A2: "\<And>Rel. strong_labelled_bisimulation_encL Rel \<Longrightarrow>
            strong_labelled_bisimulation_encL (Rel\<^sup>+)"
  proof
    fix Rel
    assume "strong_labelled_bisimulation_encL Rel"
    with injective preserves show "strong_labelled_simulation_encL (Rel\<^sup>+)"
      using strong_labelled_simulation_encL_and_closures(2)[of "Rel"]
      by blast
  next
    fix Rel
    assume B: "strong_labelled_bisimulation_encL Rel"
    show "\<forall>P Q \<beta> Q'. (P, Q) \<in> Rel\<^sup>+ \<and> Q \<midarrow>\<beta>\<rightarrow>(STLCal Source Target) Q' \<longrightarrow>
          (\<exists>\<alpha> P'. P \<midarrow>\<alpha>\<rightarrow>(STLCal Source Target) P' \<and> (P', Q') \<in> Rel\<^sup>+ \<and> \<langle>P, \<alpha>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>Q, \<beta>\<rangle>)"
    proof clarify
      fix P Q \<beta> Q'
      assume "(P, Q) \<in> Rel\<^sup>+" and "Q \<midarrow>\<beta>\<rightarrow>(STLCal Source Target) Q'"
      thus "\<exists>\<alpha> P'. P \<midarrow>\<alpha>\<rightarrow>(STLCal Source Target) P' \<and> (P', Q') \<in> Rel\<^sup>+ \<and> \<langle>P, \<alpha>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>Q, \<beta>\<rangle>"
      proof (induct arbitrary: \<beta> Q')
        fix Q \<beta> Q'
        assume "(P, Q) \<in> Rel" and "Q \<midarrow>\<beta>\<rightarrow>(STLCal Source Target) Q'"
        with B obtain \<alpha> P' where "P \<midarrow>\<alpha>\<rightarrow>(STLCal Source Target) P'" and "(P', Q') \<in> Rel"
                             and "\<langle>P, \<alpha>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>Q, \<beta>\<rangle>"
          by blast
        thus "\<exists>\<alpha> P'. P \<midarrow>\<alpha>\<rightarrow>(STLCal Source Target) P' \<and> (P', Q') \<in> Rel\<^sup>+ \<and> \<langle>P, \<alpha>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>Q, \<beta>\<rangle>"
          by auto
      next
        case (step Q R \<gamma> R')
        assume "(Q, R) \<in> Rel" and "R \<midarrow>\<gamma>\<rightarrow>(STLCal Source Target) R'"
        with B obtain \<beta> Q' where C1: "Q \<midarrow>\<beta>\<rightarrow>(STLCal Source Target) Q'" and C2: "(Q', R') \<in> Rel\<^sup>+"
                             and C3: "\<langle>Q, \<beta>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>R, \<gamma>\<rangle>"
          by blast
        assume "\<And>\<beta> Q'. Q \<midarrow>\<beta>\<rightarrow>(STLCal Source Target) Q' \<Longrightarrow>
                \<exists>\<alpha> P'. P \<midarrow>\<alpha>\<rightarrow>(STLCal Source Target) P' \<and> (P', Q') \<in> Rel\<^sup>+ \<and> \<langle>P, \<alpha>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>Q, \<beta>\<rangle>"
        with C1 obtain \<alpha> P' where C4: "P \<midarrow>\<alpha>\<rightarrow>(STLCal Source Target) P'" and C5: "(P', Q') \<in> Rel\<^sup>+"
                              and C6: "\<langle>P, \<alpha>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>Q, \<beta>\<rangle>"
          by blast
        from C2 C5 have C7: "(P', R') \<in> Rel\<^sup>+"
          by simp
        from injective C3 C6 have "\<langle>P, \<alpha>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>R, \<gamma>\<rangle>"
          using related_labels_trans_inj[of P \<alpha> Q \<beta> R \<gamma>]
          by simp
        with C4 C7
        show "\<exists>\<alpha> P'. P \<midarrow>\<alpha>\<rightarrow>(STLCal Source Target) P' \<and> (P', R') \<in> Rel\<^sup>+ \<and> \<langle>P, \<alpha>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>R, \<gamma>\<rangle>"
          by blast
      qed
    qed
  qed
  from bisim A2[of "Rel"] show "strong_labelled_bisimulation_encL (Rel\<^sup>+)"
    by blast
  from A1 show "strong_labelled_bisimulation_encL (symcl (Rel\<^sup>=))"
    using strong_labelled_bisimulation_encL_and_symm_closure[of "Rel\<^sup>="]
    by blast
  from A1 A2[of "Rel\<^sup>="] show "strong_labelled_bisimulation_encL (Rel\<^sup>*)"
    using trancl_reflcl[of Rel]
    by auto
  from A1 A2[of "symcl (Rel\<^sup>=)"] show "strong_labelled_bisimulation_encL ((symcl (Rel\<^sup>=))\<^sup>+)"
    using strong_labelled_bisimulation_encL_and_symm_closure[of "Rel\<^sup>="]
    by blast
qed

end