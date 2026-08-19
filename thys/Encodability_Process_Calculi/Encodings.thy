(* Kirstin Peters, TU Berlin, 2015 concerning the reduction semantics and
   Kirstin Peters, University of Augsburg, 2026 for the labelled semantics and the separation of
   syntax and semantics including the locale encodingFunction *)

theory Encodings
  imports ProcessCalculi
begin

section \<open>Encodings\<close>

text \<open>In the simplest case an encoding from a source into a target language is a mapping from
      source into target terms. We start with some notions on such a function considering only the
      syntax and then add the different kinds of considered semantics: reduction semantics,
      reduction semantics with barbs (as subcase) and labelled semantics.\<close>

subsection \<open>A function between processes.\<close>

text \<open>Encodability criteria describe properties on the mappings from source into target terms. To
      analyse encodability criteria we map them on conditions on relations between source and
      target terms. More precisely, we consider relations on pairs of the disjoint union of source
      and target terms. We denote this disjoint union of source and target terms by Proc.\<close>

datatype ('procS, 'procT) Proc =
  SourceTerm 'procS
| TargetTerm 'procT

locale encodingFunction =
  fixes Enc :: "'procS \<Rightarrow> 'procT"
begin

abbreviation enc :: "'procS \<Rightarrow> 'procT" (\<open>\<lbrakk>_\<rbrakk>\<close> [65] 70) where
  "\<lbrakk>S\<rbrakk> \<equiv> Enc S"

abbreviation isSource :: "('procS, 'procT) Proc \<Rightarrow> bool" (\<open>_ \<in> ProcS\<close> [70] 80) where
  "P \<in> ProcS \<equiv> (\<exists>S. P = SourceTerm S)"

abbreviation isTarget :: "('procS, 'procT) Proc \<Rightarrow> bool" (\<open>_ \<in> ProcT\<close> [70] 80) where
  "P \<in> ProcT \<equiv> (\<exists>T. P = TargetTerm T)"

abbreviation getSource :: "'procS \<Rightarrow> ('procS, 'procT) Proc \<Rightarrow> bool" (\<open>_ \<in>S _\<close> [70, 70] 80) where
  "S \<in>S P \<equiv> (P = SourceTerm S)"

abbreviation getTarget :: "'procT \<Rightarrow> ('procS, 'procT) Proc \<Rightarrow> bool" (\<open>_ \<in>T _\<close> [70, 70] 80) where
  "T \<in>T P \<equiv> (P = TargetTerm T)"

abbreviation sameKind
  :: "('procS, 'procT) Proc \<Rightarrow> ('procS, 'procT) Proc \<Rightarrow> bool" (\<open>_ \<sim>ST _\<close> [70, 70] 80) where
  "P \<sim>ST Q \<equiv> (P \<in> ProcS \<and> Q \<in> ProcS) \<or> (P \<in> ProcT \<and> Q \<in> ProcT)"

text \<open>Every term of the disjoint union is either a source or a target term.\<close>

lemma source_or_target:
  fixes P :: "('procS, 'procT) Proc"
  shows "P \<in> ProcS \<or> P \<in> ProcT"
  by (induct, simp_all)

text \<open>Similar to relations we define what it means for an encoding to preserve, reflect, or respect
      a predicate. An encoding preserves some predicate P if P(S) implies P(enc S) for all source
      terms S.\<close>

abbreviation enc_preserves_pred :: "(('procS, 'procT) Proc \<Rightarrow> bool) \<Rightarrow> bool" where
  "enc_preserves_pred Pred \<equiv> \<forall>S. Pred (SourceTerm S) \<longrightarrow> Pred (TargetTerm (\<lbrakk>S\<rbrakk>))"

abbreviation enc_preserves_binary_pred :: "(('procS, 'procT) Proc \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> bool" where
  "enc_preserves_binary_pred Pred \<equiv> \<forall>S x. Pred (SourceTerm S) x \<longrightarrow> Pred (TargetTerm (\<lbrakk>S\<rbrakk>)) x"

text \<open>An encoding reflects some predicate P if P(S) implies P(enc S) for all source terms S.\<close>

abbreviation enc_reflects_pred :: "(('procS, 'procT) Proc \<Rightarrow> bool) \<Rightarrow> bool" where
  "enc_reflects_pred Pred \<equiv> \<forall>S. Pred (TargetTerm (\<lbrakk>S\<rbrakk>)) \<longrightarrow> Pred (SourceTerm S)"

abbreviation enc_reflects_binary_pred :: "(('procS, 'procT) Proc \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> bool" where
  "enc_reflects_binary_pred Pred \<equiv> \<forall>S x. Pred (TargetTerm (\<lbrakk>S\<rbrakk>)) x \<longrightarrow> Pred (SourceTerm S) x"

text \<open>An encoding respects a predicate if it preserves and reflects it.\<close>

abbreviation enc_respects_pred :: "(('procS, 'procT) Proc \<Rightarrow> bool) \<Rightarrow> bool" where
  "enc_respects_pred Pred \<equiv> enc_preserves_pred Pred \<and> enc_reflects_pred Pred"

abbreviation enc_respects_binary_pred :: "(('procS, 'procT) Proc \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> bool" where
  "enc_respects_binary_pred Pred \<equiv>
   enc_preserves_binary_pred Pred \<and> enc_reflects_binary_pred Pred"

end

subsection \<open>An encoding function considering reduction semantics.\<close>

text \<open>An encoding consists of a source language, a target language, and a mapping from source into
      target terms.\<close>

definition STCal
  :: "'procS processCalculus \<Rightarrow> 'procT processCalculus \<Rightarrow> (('procS, 'procT) Proc) processCalculus"
  where
  "STCal Source Target \<equiv>
   \<lparr>Reductions = \<lambda>P P'.
   (\<exists>SP SP'. P = SourceTerm SP \<and> P' = SourceTerm SP' \<and> Reductions Source SP SP') \<or>
   (\<exists>TP TP'. P = TargetTerm TP \<and> P' = TargetTerm TP' \<and> Reductions Target TP TP')\<rparr>"

locale encoding =
  encodingFunction Enc
  for Enc      :: "'procS \<Rightarrow> 'procT" +
  fixes Source :: "'procS processCalculus"
    and Target :: "'procT processCalculus"
begin

text \<open>A step of a term in Proc is either a source term step or a target term step.\<close>

abbreviation stepST
  :: "('procS, 'procT) Proc \<Rightarrow> ('procS, 'procT) Proc \<Rightarrow> bool" (\<open>_ \<longmapsto>ST _\<close> [70, 70] 80) where
  "P \<longmapsto>ST P' \<equiv>
   (\<exists>S S'. S \<in>S P \<and> S' \<in>S P' \<and> S \<longmapsto>Source S') \<or> (\<exists>T T'. T \<in>T P \<and> T' \<in>T P' \<and> T \<longmapsto>Target T')"

lemma stepST_STCal_step:
  fixes P P' :: "('procS, 'procT) Proc"
  shows "P \<longmapsto>(STCal Source Target) P' = P \<longmapsto>ST P'"
  by (simp add: STCal_def)

lemma STStep_step:
  fixes S  :: "'procS"
    and T  :: "'procT"
    and P' :: "('procS, 'procT) Proc"
  shows "SourceTerm S \<longmapsto>ST P' = (\<exists>S'. S' \<in>S P' \<and> S \<longmapsto>Source S')"
    and "TargetTerm T \<longmapsto>ST P' = (\<exists>T'. T' \<in>T P' \<and> T \<longmapsto>Target T')"
  by blast+

lemma STCal_step:
  fixes S  :: "'procS"
    and T  :: "'procT"
    and P' :: "('procS, 'procT) Proc"
  shows "SourceTerm S \<longmapsto>(STCal Source Target) P' = (\<exists>S'. S' \<in>S P' \<and> S \<longmapsto>Source S')"
    and "TargetTerm T \<longmapsto>(STCal Source Target) P' = (\<exists>T'. T' \<in>T P' \<and> T \<longmapsto>Target T')"
  by (simp add: STCal_def)+

text \<open>A sequence of steps of a term in Proc is either a sequence of source term steps or a sequence
      of target term steps.\<close>

abbreviation stepsST
  :: "('procS, 'procT) Proc \<Rightarrow> ('procS, 'procT) Proc \<Rightarrow> bool"  (\<open>_ \<longmapsto>ST* _\<close> [70, 70] 80) where
  "P \<longmapsto>ST* P' \<equiv>
   (\<exists>S S'. S \<in>S P \<and> S' \<in>S P' \<and> S \<longmapsto>Source* S') \<or> (\<exists>T T'. T \<in>T P \<and> T' \<in>T P' \<and> T \<longmapsto>Target* T')"

lemma STSteps_steps:
  fixes S  :: "'procS"
    and T  :: "'procT"
    and P' :: "('procS, 'procT) Proc"
  shows "SourceTerm S \<longmapsto>ST* P' = (\<exists>S'. S' \<in>S P' \<and> S \<longmapsto>Source* S')"
    and "TargetTerm T \<longmapsto>ST* P' = (\<exists>T'. T' \<in>T P' \<and> T \<longmapsto>Target* T')"
  by blast+

lemma STCal_steps:
  fixes S  :: "'procS"
    and T  :: "'procT"
    and P' :: "('procS, 'procT) Proc"
  shows "SourceTerm S \<longmapsto>(STCal Source Target)* P' = (\<exists>S'. S' \<in>S P' \<and> S \<longmapsto>Source* S')"
    and "TargetTerm T \<longmapsto>(STCal Source Target)* P' = (\<exists>T'. T' \<in>T P' \<and> T \<longmapsto>Target* T')"
proof auto
  assume "SourceTerm S \<longmapsto>(STCal Source Target)* P'"
  from this obtain n where "SourceTerm S \<longmapsto>(STCal Source Target)\<^bsup>n\<^esup> P'"
    by (auto simp add: steps_def)
  thus "\<exists>S'. S' \<in>S P' \<and> S \<longmapsto>Source* S'"
  proof (induct n arbitrary: P')
    case 0
    assume "SourceTerm S \<longmapsto>(STCal Source Target)\<^bsup>0\<^esup> P'"
    hence "S \<in>S P'"
      by simp
    moreover have "S \<longmapsto>Source* S"
      by (rule steps_refl)
    ultimately show "\<exists>S'. S' \<in>S P' \<and> S \<longmapsto>Source* S'"
      by blast
  next
    case (Suc n P'')
    assume "SourceTerm S \<longmapsto>(STCal Source Target)\<^bsup>Suc n\<^esup> P''"
    from this obtain P' where A1: "SourceTerm S \<longmapsto>(STCal Source Target)\<^bsup>n\<^esup> P'"
                          and A2: "P' \<longmapsto>(STCal Source Target) P''"
      by auto
    assume "\<And>P'. SourceTerm S \<longmapsto>(STCal Source Target)\<^bsup>n\<^esup> P' \<Longrightarrow> \<exists>S'. S' \<in>S P' \<and> S \<longmapsto>Source* S'"
    with A1 obtain S' where A3: "S' \<in>S P'" and A4: "S \<longmapsto>Source* S'"
      by blast
    from A2 A3 obtain S'' where A5: "S'' \<in>S P''" and A6: "S' \<longmapsto>Source S''"
      using STCal_step(1)[where S="S'" and P'="P''"]
      by blast
    from A4 A6 have "S \<longmapsto>Source* S''"
      using step_to_steps[where Cal="Source" and P="S'" and P'="S''"]
      by (simp add: steps_add[where Cal="Source" and P="S" and Q="S'" and R="S''"])
    with A5 show "\<exists>S''. S'' \<in>S P'' \<and> S \<longmapsto>Source* S''"
      by blast
  qed
next
  fix S'
  assume "S \<longmapsto>Source* S'"
  from this obtain n where "S \<longmapsto>Source\<^bsup>n\<^esup> S'"
    by (auto simp add: steps_def)
  thus "SourceTerm S \<longmapsto>(STCal Source Target)* (SourceTerm S')"
  proof (induct n arbitrary: S')
    case 0
    assume "S \<longmapsto>Source\<^bsup>0\<^esup> S'"
    hence "S = S'"
      by auto
    thus "SourceTerm S \<longmapsto>(STCal Source Target)* (SourceTerm S')"
      by (simp add: steps_refl)
  next
    case (Suc n S'')
    assume "S \<longmapsto>Source\<^bsup>Suc n\<^esup> S''"
    from this obtain S' where B1: "S \<longmapsto>Source\<^bsup>n\<^esup> S'" and B2: "S' \<longmapsto>Source S''"
      by auto
    assume "\<And>S'. S \<longmapsto>Source\<^bsup>n\<^esup> S' \<Longrightarrow> SourceTerm S \<longmapsto>(STCal Source Target)* (SourceTerm S')"
    with B1 have "SourceTerm S \<longmapsto>(STCal Source Target)* (SourceTerm S')"
      by blast
    moreover from B2 have "SourceTerm S' \<longmapsto>(STCal Source Target)* (SourceTerm S'')"
      using step_to_steps[where Cal="STCal Source Target" and P="SourceTerm S'"]
      by (simp add: STCal_def)
    ultimately show "SourceTerm S \<longmapsto>(STCal Source Target)* (SourceTerm S'')"
      by (rule steps_add)
  qed
next
  assume "TargetTerm T \<longmapsto>(STCal Source Target)* P'"
  from this obtain n where "TargetTerm T \<longmapsto>(STCal Source Target)\<^bsup>n\<^esup> P'"
    by (auto simp add: steps_def)
  thus "\<exists>T'. T' \<in>T P' \<and> T \<longmapsto>Target* T'"
  proof (induct n arbitrary: P')
    case 0
    assume "TargetTerm T \<longmapsto>(STCal Source Target)\<^bsup>0\<^esup> P'"
    hence "T \<in>T P'"
      by simp
    moreover have "T \<longmapsto>Target* T"
      by (rule steps_refl)
    ultimately show "\<exists>T'. T' \<in>T P' \<and> T \<longmapsto>Target* T'"
      by blast
  next
    case (Suc n P'')
    assume "TargetTerm T \<longmapsto>(STCal Source Target)\<^bsup>Suc n\<^esup> P''"
    from this obtain P' where A1: "TargetTerm T \<longmapsto>(STCal Source Target)\<^bsup>n\<^esup> P'"
                          and A2: "P' \<longmapsto>(STCal Source Target) P''"
      by auto
    assume "\<And>P'. TargetTerm T \<longmapsto>(STCal Source Target)\<^bsup>n\<^esup> P' \<Longrightarrow> \<exists>T'. T' \<in>T P' \<and> T \<longmapsto>Target* T'"
    with A1 obtain T' where A3: "T' \<in>T P'" and A4: "T \<longmapsto>Target* T'"
      by blast
    from A2 A3 obtain T'' where A5: "T'' \<in>T P''" and A6: "T' \<longmapsto>Target T''"
      using STCal_step(2)[where T="T'" and P'="P''"]
      by blast
    from A4 A6 have "T \<longmapsto>Target* T''"
      using step_to_steps[where Cal="Target" and P="T'" and P'="T''"]
      by (simp add: steps_add[where Cal="Target" and P="T" and Q="T'" and R="T''"])
    with A5 show "\<exists>T''. T'' \<in>T P'' \<and> T \<longmapsto>Target* T''"
      by blast
  qed
next
  fix T'
  assume "T \<longmapsto>Target* T'"
  from this obtain n where "T \<longmapsto>Target\<^bsup>n\<^esup> T'"
    by (auto simp add: steps_def)
  thus "TargetTerm T \<longmapsto>(STCal Source Target)* (TargetTerm T')"
  proof (induct n arbitrary: T')
    case 0
    assume "T \<longmapsto>Target\<^bsup>0\<^esup> T'"
    hence "T = T'"
      by auto
    thus "TargetTerm T \<longmapsto>(STCal Source Target)* (TargetTerm T')"
      by (simp add: steps_refl)
  next
    case (Suc n T'')
    assume "T \<longmapsto>Target\<^bsup>Suc n\<^esup> T''"
    from this obtain T' where B1: "T \<longmapsto>Target\<^bsup>n\<^esup> T'" and B2: "T' \<longmapsto>Target T''"
      by auto
    assume "\<And>T'. T \<longmapsto>Target\<^bsup>n\<^esup> T' \<Longrightarrow> TargetTerm T \<longmapsto>(STCal Source Target)* (TargetTerm T')"
    with B1 have "TargetTerm T \<longmapsto>(STCal Source Target)* (TargetTerm T')"
      by blast
    moreover from B2 have "TargetTerm T' \<longmapsto>(STCal Source Target)* (TargetTerm T'')"
      using step_to_steps[where Cal="STCal Source Target" and P="TargetTerm T'"]
      by (simp add: STCal_def)
    ultimately show "TargetTerm T \<longmapsto>(STCal Source Target)* (TargetTerm T'')"
      by (rule steps_add)
  qed
qed

lemma stepsST_STCal_steps:
  fixes P P' :: "('procS, 'procT) Proc"
  shows "P \<longmapsto>(STCal Source Target)* P' = P \<longmapsto>ST* P'"
proof (cases P)
  case (SourceTerm SP)
  assume "SP \<in>S P"
  thus "P \<longmapsto>(STCal Source Target)* P' = P \<longmapsto>ST* P'"
    using STCal_steps(1)[where S="SP" and P'="P'"] STSteps_steps(1)[where S="SP" and P'="P'"]
    by blast
next
  case (TargetTerm TP)
  assume "TP \<in>T P"
  thus "P \<longmapsto>(STCal Source Target)* P' = P \<longmapsto>ST* P'"
    using STCal_steps(2)[where T="TP" and P'="P'"] STSteps_steps(2)[where T="TP" and P'="P'"]
    by blast
qed

lemma stepsST_refl:
  fixes P :: "('procS, 'procT) Proc"
  shows "P \<longmapsto>ST* P"
  by (cases P, simp_all add: steps_refl)

lemma stepsST_add:
  fixes P Q R :: "('procS, 'procT) Proc"
  assumes A1: "P \<longmapsto>ST* Q"
      and A2: "Q \<longmapsto>ST* R"
  shows "P \<longmapsto>ST* R"
proof -
  from A1 have "P \<longmapsto>(STCal Source Target)* Q"
    by (simp add: stepsST_STCal_steps)
  moreover from A2 have "Q \<longmapsto>(STCal Source Target)* R"
    by (simp add: stepsST_STCal_steps)
  ultimately have "P \<longmapsto>(STCal Source Target)* R"
    by (rule steps_add)
  thus "P \<longmapsto>ST* R"
    by (simp add: stepsST_STCal_steps)
qed

text \<open>A divergent term of Proc is either a divergent source term or a divergent target term.\<close>

abbreviation divergentST :: "('procS, 'procT) Proc \<Rightarrow> bool" (\<open>_ \<longmapsto>ST\<omega>\<close> [70] 80) where
  "P \<longmapsto>ST\<omega> \<equiv> (\<exists>S. S \<in>S P \<and> S \<longmapsto>(Source)\<omega>) \<or> (\<exists>T. T \<in>T P \<and> T \<longmapsto>(Target)\<omega>)"

lemma STCal_divergent:
  fixes S  :: "'procS"
    and T  :: "'procT"
  shows "SourceTerm S \<longmapsto>(STCal Source Target)\<omega> = S \<longmapsto>(Source)\<omega>"
    and "TargetTerm T \<longmapsto>(STCal Source Target)\<omega> = T \<longmapsto>(Target)\<omega>"
  using STCal_steps
  by (auto simp add: STCal_def divergent_def)

lemma divergentST_STCal_divergent:
  fixes P :: "('procS, 'procT) Proc"
  shows "P \<longmapsto>(STCal Source Target)\<omega> = P \<longmapsto>ST\<omega>"
proof (cases P)
  case (SourceTerm SP)
  assume "SP \<in>S P"
  thus "P \<longmapsto>(STCal Source Target)\<omega> = P \<longmapsto>ST\<omega>"
    using STCal_divergent(1)
    by simp
next
  case (TargetTerm TP)
  assume "TP \<in>T P"
  thus "P \<longmapsto>(STCal Source Target)\<omega> = P \<longmapsto>ST\<omega>"
    using STCal_divergent(2)
    by simp
qed

end

subsection \<open>An encoding function considering reduction semantics and barbs.\<close>

text \<open>To compare source terms and target terms w.r.t. their barbs or observables we assume that
      each languages defines its own predicate for the existence of barbs.\<close>

definition STCalWB
  :: "('procS, 'barbs) calculusWithBarbs \<Rightarrow> ('procT, 'barbs) calculusWithBarbs
      \<Rightarrow> (('procS, 'procT) Proc, 'barbs) calculusWithBarbs" where
  "STCalWB Source Target \<equiv>
   \<lparr>Calculus = STCal (calculusWithBarbs.Calculus Source) (calculusWithBarbs.Calculus Target),
   HasBarb   = \<lambda>P a. (\<exists>SP. P = SourceTerm SP \<and> (calculusWithBarbs.HasBarb Source) SP a) \<or>
                     (\<exists>TP. P = TargetTerm TP \<and> (calculusWithBarbs.HasBarb Target) TP a)\<rparr>"

locale encoding_wrt_barbs =
  encoding Enc Source Target
  for Source :: "'procS processCalculus"
  and Target :: "'procT processCalculus"
  and Enc    :: "'procS \<Rightarrow> 'procT" +
  fixes SWB :: "('procS, 'barbs) calculusWithBarbs"
    and TWB :: "('procT, 'barbs) calculusWithBarbs"
  assumes calS: "calculusWithBarbs.Calculus SWB = Source"
      and calT: "calculusWithBarbs.Calculus TWB = Target"
begin

lemma STCalWB_STCal:
  shows "Calculus (STCalWB SWB TWB) = STCal Source Target"
  unfolding STCalWB_def using calS calT
  by auto

text \<open>We say a term P of Proc has some barbs a if either P is a source term that has barb a or P is
      a target term that has the barb b. For simplicity we assume that the sets of barbs is large
      enough to contain all barbs of the source terms, the target terms, and all barbs they might
      have in common.\<close>

abbreviation hasBarbST :: "('procS, 'procT) Proc \<Rightarrow> 'barbs \<Rightarrow> bool" (\<open>_\<down>._\<close> [70, 70] 80) where
  "P\<down>.a \<equiv> (\<exists>S. S \<in>S P \<and> S\<down><SWB>a) \<or> (\<exists>T. T \<in>T P \<and> T\<down><TWB>a)"

lemma STCalWB_hasBarbST:
  fixes P :: "('procS, 'procT) Proc"
    and a :: "'barbs"
  shows "P\<down><STCalWB SWB TWB>a = P\<down>.a"
  by (simp add: STCalWB_def)

lemma preservation_of_barbs_in_barbed_encoding:
  fixes Rel :: "(('procS, 'procT) Proc \<times> ('procS, 'procT) Proc) set"
    and P Q :: "('procS, 'procT) Proc"
    and a   :: "'barbs"
  assumes preservation: "rel_preserves_barbs Rel (STCalWB SWB TWB)"
      and rel:          "(P, Q) \<in> Rel"
      and barb:         "P\<down>.a"
    shows "Q\<down>.a"
  using preservation rel barb
  by (simp add: STCalWB_def)

lemma reflection_of_barbs_in_barbed_encoding:
  fixes Rel :: "(('procS, 'procT) Proc \<times> ('procS, 'procT) Proc) set"
    and P Q :: "('procS, 'procT) Proc"
    and a   :: "'barbs"
  assumes reflection: "rel_reflects_barbs Rel (STCalWB SWB TWB)"
      and rel:        "(P, Q) \<in> Rel"
      and barb:       "Q\<down>.a"
    shows "P\<down>.a"
  using reflection rel barb
  by (simp add: STCalWB_def)

lemma respection_of_barbs_in_barbed_encoding:
  fixes Rel :: "(('procS, 'procT) Proc \<times> ('procS, 'procT) Proc) set"
    and P Q :: "('procS, 'procT) Proc"
    and a   :: "'barbs"
  assumes respection: "rel_respects_barbs Rel (STCalWB SWB TWB)"
      and rel:        "(P, Q) \<in> Rel"
    shows "P\<down>.a = Q\<down>.a"
  using preservation_of_barbs_in_barbed_encoding[where Rel="Rel" and P="P" and Q="Q" and a="a"]
        reflection_of_barbs_in_barbed_encoding[where Rel="Rel" and P="P" and Q="Q" and a="a"]
        respection rel
  by blast

text \<open>A term P of Proc reaches a barb a if either P is a source term that reaches a or P is a
      target term that reaches a.\<close>

abbreviation reachesBarbST :: "('procS, 'procT) Proc \<Rightarrow> 'barbs \<Rightarrow> bool" (\<open>_\<Down>._\<close> [70, 70] 80) where
  "P\<Down>.a \<equiv> (\<exists>S. S \<in>S P \<and> S\<Down><SWB>a) \<or> (\<exists>T. T \<in>T P \<and> T\<Down><TWB>a)"

lemma STCalWB_reachesBarbST:
  fixes P :: "('procS, 'procT) Proc"
    and a :: "'barbs"
  shows "P\<Down><STCalWB SWB TWB>a = P\<Down>.a"
proof -
  have "\<forall>S. SourceTerm S\<Down><STCalWB SWB TWB>a = SourceTerm S\<Down>.a"
    using STCal_steps(1)
    by (auto simp add: STCalWB_def calS calT)
  moreover have "\<forall>T. TargetTerm T\<Down><STCalWB SWB TWB>a = TargetTerm T\<Down>.a"
    using STCal_steps(2)
    by (auto simp add: STCalWB_def calS calT)
  ultimately show "P\<Down><STCalWB SWB TWB>a = P\<Down>.a"
    by (cases P, simp+)
qed

lemma weak_preservation_of_barbs_in_barbed_encoding:
  fixes Rel :: "(('procS, 'procT) Proc \<times> ('procS, 'procT) Proc) set"
    and P Q :: "('procS, 'procT) Proc"
    and a   :: "'barbs"
  assumes preservation: "rel_weakly_preserves_barbs Rel (STCalWB SWB TWB)"
      and rel:          "(P, Q) \<in> Rel"
      and barb:         "P\<Down>.a"
    shows "Q\<Down>.a"
proof -
  from barb have "P\<Down><STCalWB SWB TWB>a"
    by (simp add: STCalWB_reachesBarbST)
  with preservation rel have "Q\<Down><STCalWB SWB TWB>a"
    by blast
  thus "Q\<Down>.a"
    by (simp add: STCalWB_reachesBarbST)
qed

lemma weak_reflection_of_barbs_in_barbed_encoding:
  fixes Rel :: "(('procS, 'procT) Proc \<times> ('procS, 'procT) Proc) set"
    and P Q :: "('procS, 'procT) Proc"
    and a   :: "'barbs"
  assumes reflection: "rel_weakly_reflects_barbs Rel (STCalWB SWB TWB)"
      and rel:        "(P, Q) \<in> Rel"
      and barb:       "Q\<Down>.a"
    shows "P\<Down>.a"
proof -
  from barb have "Q\<Down><STCalWB SWB TWB>a"
    by (simp add: STCalWB_reachesBarbST)
  with reflection rel have "P\<Down><STCalWB SWB TWB>a"
    by blast
  thus "P\<Down>.a"
    by (simp add: STCalWB_reachesBarbST)
qed

lemma weak_respection_of_barbs_in_barbed_encoding:
  fixes Rel :: "(('procS, 'procT) Proc \<times> ('procS, 'procT) Proc) set"
    and P Q :: "('procS, 'procT) Proc"
    and a   :: "'barbs"
  assumes respection: "rel_weakly_respects_barbs Rel (STCalWB SWB TWB)"
      and rel:        "(P, Q) \<in> Rel"
    shows "P\<Down>.a = Q\<Down>.a"
proof (rule iffI)
  assume "P\<Down>.a"
  with respection rel show "Q\<Down>.a"
    using weak_preservation_of_barbs_in_barbed_encoding[where Rel="Rel"]
    by blast
next
  assume "Q\<Down>.a"
  with respection rel show "P\<Down>.a"
    using weak_reflection_of_barbs_in_barbed_encoding[where Rel="Rel"]
    by blast
qed

end

subsection \<open>An encoding function considering labelled semantics.\<close>

text \<open>Also for the labelled semantics an encoding consists of a source language, a target language,
      and a mapping from source into target terms. We also inherit the other notions of encodings
      that consider reduction semantics. Similar to the disjoint union of source and target terms,
      we also build the disjoint union of source and target labels with a fresh internal label.
      This internal label will be used instead of a source or target internal label in the calculus
      on the disjoint union, since we require a single internal label for a labelled calculus.\<close>

datatype ('labS, 'labT) Lab =
  SourceLabel 'labS
| TargetLabel 'labT
| Internal 'labS 'labT

definition STLCal
  :: "('procS, 'labS) labelledProcessCalculus \<Rightarrow> ('procT, 'labT) labelledProcessCalculus \<Rightarrow>
      (('procS, 'procT) Proc, ('labS, 'labT) Lab) labelledProcessCalculus"
  where
  "STLCal Source Target \<equiv>
   \<lparr>LabelledSemantics = \<lambda>P \<alpha> P'.
   (\<exists>SP S\<alpha> SP'. P = SourceTerm SP \<and> (\<alpha> = SourceLabel S\<alpha> \<and> \<alpha> \<noteq> SourceLabel (\<tau>-Source) \<or>
    \<alpha> = Internal (\<tau>-Source) (\<tau>-Target) \<and> S\<alpha> = \<tau>-Source) \<and> P' = SourceTerm SP' \<and>
    LabelledSemantics Source SP S\<alpha> SP') \<or>
   (\<exists>TP T\<alpha> TP'. P = TargetTerm TP \<and> (\<alpha> = TargetLabel T\<alpha> \<and> \<alpha> \<noteq> TargetLabel (\<tau>-Target) \<or>
    \<alpha> = Internal (\<tau>-Source) (\<tau>-Target) \<and> T\<alpha> = \<tau>-Target) \<and> P' = TargetTerm TP' \<and>
    LabelledSemantics Target TP T\<alpha> TP'),
   InternalAction = Internal (\<tau>-Source) (\<tau>-Target)\<rparr>"

locale encodingLS =
  encodingFunction Enc
  for Enc      :: "'procS \<Rightarrow> 'procT" +
  fixes Source :: "('procS, 'labS) labelledProcessCalculus"
    and Target :: "('procT, 'labT) labelledProcessCalculus"
begin

abbreviation internalST :: "('labS, 'labT) Lab" (\<open>\<tau>-STLCal\<close> 80) where
  "\<tau>-STLCal \<equiv> Internal (\<tau>-Source) (\<tau>-Target)"

definition isSourceLabel :: "('labS, 'labT) Lab \<Rightarrow> bool" (\<open>_ \<in> LabS\<close> [70] 80) where
  "\<alpha> \<in> LabS \<equiv> (\<exists>\<beta>. \<alpha> = SourceLabel \<beta>)"

definition isTargetLabel :: "('labS, 'labT) Lab \<Rightarrow> bool" (\<open>_ \<in> LabT\<close> [70] 80) where
  "\<alpha> \<in> LabT \<equiv> (\<exists>\<beta>. \<alpha> = TargetLabel \<beta>)"

definition getSourceLabel
  :: "'labS \<Rightarrow> ('procS, 'procT) Proc \<Rightarrow> ('labS, 'labT) Lab \<Rightarrow> bool" (\<open>_ \<in>SL \<langle>_, _\<rangle>\<close> [70, 70, 70] 80)
  where
  "\<beta> \<in>SL \<langle>P, \<alpha>\<rangle> \<equiv> P \<in> ProcS \<and> (\<alpha> = SourceLabel \<beta> \<and> \<beta> \<noteq> \<tau>-Source \<or> \<alpha> = \<tau>-STLCal \<and> \<beta> = \<tau>-Source)"

definition getTargetLabel
  :: "'labT \<Rightarrow> ('procS, 'procT) Proc \<Rightarrow> ('labS, 'labT) Lab \<Rightarrow> bool" (\<open>_ \<in>TL \<langle>_, _\<rangle>\<close> [70, 70, 70] 80)
  where
  "\<beta> \<in>TL \<langle>P, \<alpha>\<rangle> \<equiv> P \<in> ProcT \<and> (\<alpha> = TargetLabel \<beta> \<and> \<beta> \<noteq> \<tau>-Target \<or> \<alpha> = \<tau>-STLCal \<and> \<beta> = \<tau>-Target)"

inductive getSourceLabels
  :: "'labS list \<Rightarrow> ('procS, 'procT) Proc \<Rightarrow> ('labS, 'labT) Lab list \<Rightarrow> bool"
  (\<open>_ \<in>SL* \<langle>_, _\<rangle>\<close> [70, 70, 70] 80) where
  SLNil:  "P \<in> ProcS \<Longrightarrow> [] \<in>SL* \<langle>P, []\<rangle>"
| SLCons: "\<lbrakk>v \<in>SL* \<langle>P, w\<rangle>; \<beta> \<in>SL \<langle>Q, \<alpha>\<rangle>\<rbrakk> \<Longrightarrow> (v@[\<beta>]) \<in>SL* \<langle>P, (w@[\<alpha>])\<rangle>"

inductive getTargetLabels
  :: "'labT list \<Rightarrow> ('procS, 'procT) Proc \<Rightarrow> ('labS, 'labT) Lab list \<Rightarrow> bool"
  (\<open>_ \<in>TL* \<langle>_, _\<rangle>\<close> [70, 70, 70] 80) where
  TLNil:  "P \<in> ProcT \<Longrightarrow> [] \<in>TL* \<langle>P, []\<rangle>"
| TLCons: "\<lbrakk>v \<in>TL* \<langle>P, w\<rangle>; \<beta> \<in>TL \<langle>Q, \<alpha>\<rangle>\<rbrakk> \<Longrightarrow> (v@[\<beta>]) \<in>TL* \<langle>P, (w@[\<alpha>])\<rangle>"

text \<open>To avoid confusion we forbid for a source label version of the internal label and similar for
      the target. Instead internal steps on the source or target are mapped on steps with the new
      internal label in the disjoint union of source and target labels. As tiebreaker for the
      internal label in the disjoint union we add a process, that is supposed to be the process
      that performs a step on this label, and use the kind of the process to determine whether the
      internal results from an internal in the source or target.\<close>

lemma no_source_or_target_internal_step:
  fixes P P' :: "('procS, 'procT) Proc"
    and \<alpha>    :: "('labS, 'labT) Lab"
  assumes "P \<midarrow>\<alpha>\<rightarrow>(STLCal Source Target) P'"
  shows "\<alpha> \<noteq> SourceLabel (\<tau>-Source)" and "\<alpha> \<noteq> TargetLabel (\<tau>-Target)"
  using assms
  unfolding STLCal_def
  by auto

lemma no_source_internal_lifting:
  fixes \<alpha> :: "'labS"
    and \<beta> :: "('labS, 'labT) Lab"
  assumes "\<alpha> \<in>SL \<langle>P, \<beta>\<rangle>"
  shows "\<beta> \<noteq> SourceLabel (\<tau>-Source)"
  using assms
  unfolding getSourceLabel_def
  by blast

lemma no_target_internal_lifting:
  fixes \<alpha> :: "'labT"
    and \<beta> :: "('labS, 'labT) Lab"
  assumes "\<alpha> \<in>TL \<langle>P, \<beta>\<rangle>"
  shows "\<beta> \<noteq> TargetLabel (\<tau>-Target)"
  using assms
  unfolding getTargetLabel_def
  by blast

lemma internalST_iff_internal:
  shows "\<tau>-STLCal = \<tau>-(STLCal Source Target)"
  by (simp add: STLCal_def)

lemma lifted_label_is_unique:
  fixes \<alpha> :: "'labS"
    and \<beta> :: "'labT"
    and \<gamma> :: "('labS, 'labT) Lab"
  assumes "\<alpha> \<in>SL \<langle>P, \<gamma>\<rangle>"
      and "\<beta> \<in>TL \<langle>P, \<gamma>\<rangle>"
    shows False
  using assms
  unfolding getSourceLabel_def getTargetLabel_def
  by blast

text \<open>A labelled step of a term in Proc is either a labelled source term step or a labelled target
      term step.\<close>

abbreviation labelledStepST
  :: "('procS, 'procT) Proc \<Rightarrow> ('labS, 'labT) Lab \<Rightarrow> ('procS, 'procT) Proc \<Rightarrow> bool"
  (\<open>_ \<midarrow>_\<rightarrow>ST _\<close> [70, 70, 70] 80) where
  "P \<midarrow>\<alpha>\<rightarrow>ST P' \<equiv> (\<exists>S \<beta> S'. S \<in>S P \<and> \<beta> \<in>SL \<langle>P, \<alpha>\<rangle> \<and> S' \<in>S P' \<and> S \<midarrow>\<beta>\<rightarrow>Source S') \<or>
                  (\<exists>T \<beta> T'. T \<in>T P \<and> \<beta> \<in>TL \<langle>P, \<alpha>\<rangle> \<and> T' \<in>T P' \<and> T \<midarrow>\<beta>\<rightarrow>Target T')"

lemma labelledStepST_STLCal_labelledStep:
  fixes P P' :: "('procS, 'procT) Proc"
    and \<alpha>    :: "('labS, 'labT) Lab"
  shows "P \<midarrow>\<alpha>\<rightarrow>(STLCal Source Target) P' = P \<midarrow>\<alpha>\<rightarrow>ST P'"
  unfolding STLCal_def getSourceLabel_def getTargetLabel_def
  by auto

lemma labelledSTStep_labelledStep:
  fixes S  :: "'procS"
    and T  :: "'procT"
    and P' :: "('procS, 'procT) Proc"
    and \<alpha>  :: "('labS, 'labT) Lab"
  shows "SourceTerm S \<midarrow>\<alpha>\<rightarrow>ST P' = (\<exists>\<beta> S'. \<beta> \<in>SL \<langle>SourceTerm S, \<alpha>\<rangle> \<and> S' \<in>S P' \<and> S \<midarrow>\<beta>\<rightarrow>Source S')"
    and "TargetTerm T \<midarrow>\<alpha>\<rightarrow>ST P' = (\<exists>\<beta> T'. \<beta> \<in>TL \<langle>TargetTerm T, \<alpha>\<rangle> \<and> T' \<in>T P' \<and> T \<midarrow>\<beta>\<rightarrow>Target T')"
  by blast+

lemma STLCal_labelledStep:
  fixes S  :: "'procS"
    and T  :: "'procT"
    and P' :: "('procS, 'procT) Proc"
    and \<alpha>  :: "('labS, 'labT) Lab"
  shows "SourceTerm S \<midarrow>\<alpha>\<rightarrow>(STLCal Source Target) P' =
         (\<exists>\<beta> S'. \<beta> \<in>SL \<langle>SourceTerm S, \<alpha>\<rangle> \<and> S' \<in>S P' \<and> S \<midarrow>\<beta>\<rightarrow>Source S')"
    and "TargetTerm T \<midarrow>\<alpha>\<rightarrow>(STLCal Source Target) P' =
         (\<exists>\<beta> T'. \<beta> \<in>TL \<langle>TargetTerm T, \<alpha>\<rangle> \<and> T' \<in>T P' \<and> T \<midarrow>\<beta>\<rightarrow>Target T')"
  unfolding STLCal_def getSourceLabel_def getTargetLabel_def
  by auto

text \<open>A weak internal step of a term in Proc is either a weak internal source step or a weak
      internal target step.\<close>

abbreviation weakTauStepST
  :: "('procS, 'procT) Proc \<Rightarrow> ('procS, 'procT) Proc \<Rightarrow> bool" (\<open>_ \<rightarrow>ST* _\<close> [70, 70] 80) where
  "P \<rightarrow>ST* P' \<equiv> (\<exists>S S'. S \<in>S P \<and> S' \<in>S P' \<and> S \<rightarrow>Source* S') \<or>
                (\<exists>T T'. T \<in>T P \<and> T' \<in>T P' \<and> T \<rightarrow>Target* T')"

lemma STWeakTauSteps_weakTauSteps:
  fixes S  :: "'procS"
    and T  :: "'procT"
    and P' :: "('procS, 'procT) Proc"
  shows "SourceTerm S \<rightarrow>ST* P' = (\<exists>S'. S' \<in>S P' \<and> S \<rightarrow>Source* S')"
    and "TargetTerm T \<rightarrow>ST* P' = (\<exists>T'. T' \<in>T P' \<and> T \<rightarrow>Target* T')"
  by blast+

lemma STLCal_weakTauSteps:
  fixes S  :: "'procS"
    and T  :: "'procT"
    and P' :: "('procS, 'procT) Proc"
  shows "SourceTerm S \<rightarrow>(STLCal Source Target)* P' = (\<exists>S'. S' \<in>S P' \<and> S \<rightarrow>Source* S')"
    and "TargetTerm T \<rightarrow>(STLCal Source Target)* P' = (\<exists>T'. T' \<in>T P' \<and> T \<rightarrow>Target* T')"
proof auto
  define P :: "('procS, 'procT) Proc" where def_P: "P = SourceTerm S"
  define Cal where def_Cal: "Cal = STLCal Source Target"
  assume "SourceTerm S \<rightarrow>(STLCal Source Target)* P'"
  with def_P def_Cal have "P \<rightarrow>Cal* P'"
    by simp
  from this def_P def_Cal show "\<exists>S'. S' \<in>S P' \<and> S \<rightarrow>Source* S'"
  proof (induct)
    case (WTS_refl P Cal)
    assume "S \<in>S P"
    moreover have "S \<rightarrow>Source* S"
      using weakTauStep.WTS_refl[of S Source]
      by simp
    ultimately show "\<exists>S'. S' \<in>S P \<and> S \<rightarrow>Source* S'"
      by blast
  next
    case (WTS_trans P Cal P' P'')
    from WTS_trans(2)
    have IH: "S \<in>S P \<and> Cal = STLCal Source Target \<Longrightarrow> \<exists>S'. S' \<in>S P' \<and> S \<rightarrow>Source* S'"
      by simp
    assume "S \<in>S P" and A1: "Cal = STLCal Source Target"
    with IH obtain S' where A2: "S' \<in>S P'" and A3: "S \<rightarrow>Source* S'"
      by blast
    assume "P' \<midarrow>\<tau>-Cal\<rightarrow>Cal P''"
    with A1 A2 obtain \<beta> S'' where A4: "\<beta> \<in>SL \<langle>P', \<tau>-Cal\<rangle>" and A5: "S'' \<in>S P''"
                              and A6: "S' \<midarrow>\<beta>\<rightarrow>Source S''"
      using STLCal_labelledStep(1)[of S' "\<tau>-Cal" P'']
      by blast
    from A1 A3 A4 A6 have "S \<rightarrow>Source* S''"
      using weakTauStep.WTS_trans[of S Source S' S'']
      unfolding getSourceLabel_def
      by (simp add: STLCal_def)
    with A5 show "\<exists>S''. S'' \<in>S P'' \<and> S \<rightarrow>Source* S''"
      by blast
  qed
next
  fix S'
  define Cal where def_Cal: "Cal = Source"
  assume "S \<rightarrow>Source* S'"
  with def_Cal have "S \<rightarrow>Cal* S'"
    by simp
  from this def_Cal show "SourceTerm S \<rightarrow>(STLCal Source Target)* (SourceTerm S')"
  proof (induct)
    case (WTS_refl S Cal)
    show "SourceTerm S \<rightarrow>(STLCal Source Target)* SourceTerm S"
      using weakTauStep.WTS_refl[of "SourceTerm S" "STLCal Source Target"]
      by simp
  next
    case (WTS_trans S Cal S' S'')
    assume "Cal = Source \<Longrightarrow> SourceTerm S \<rightarrow>(STLCal Source Target)* SourceTerm S'"
       and A: "Cal = Source"
    hence "SourceTerm S \<rightarrow>(STLCal Source Target)* SourceTerm S'"
      by simp
    moreover assume "S' \<midarrow>\<tau>-Cal\<rightarrow>Cal S''"
    with A have "SourceTerm S' \<midarrow>\<tau>-(STLCal Source Target)\<rightarrow>(STLCal Source Target) (SourceTerm S'')"
      using STLCal_labelledStep(1)[of S' "\<tau>-STLCal" "SourceTerm S''"]
      by (simp add: STLCal_def)
    ultimately show "SourceTerm S \<rightarrow>(STLCal Source Target)* SourceTerm S''"
      using weakTauStep.WTS_trans[of "SourceTerm S" "STLCal Source Target" "SourceTerm S'"
              "SourceTerm S''"]
      by simp
  qed
next
  define P :: "('procS, 'procT) Proc" where def_P: "P = TargetTerm T"
  define Cal where def_Cal: "Cal = STLCal Source Target"
  assume "TargetTerm T \<rightarrow>(STLCal Source Target)* P'"
  with def_P def_Cal have "P \<rightarrow>Cal* P'"
    by simp
  from this def_P def_Cal show "\<exists>T'. T' \<in>T P' \<and> T \<rightarrow>Target* T'"
  proof induct
    case (WTS_refl P Cal)
    assume "T \<in>T P"
    moreover have "T \<rightarrow>Target* T"
      using weakTauStep.WTS_refl[of T Target]
      by simp
    ultimately show "\<exists>T'. T' \<in>T P \<and> T \<rightarrow>Target* T'"
      by blast
  next
    case (WTS_trans P Cal P' P'')
    from WTS_trans(2)
    have IH: "T \<in>T P \<and> Cal = STLCal Source Target \<Longrightarrow> \<exists>T'. T' \<in>T P' \<and> T \<rightarrow>Target* T'"
      by simp
    assume "T \<in>T P" and A1: "Cal = STLCal Source Target"
    with IH obtain T' where A2: "T' \<in>T P'" and A3: "T \<rightarrow>Target* T'"
      by blast
    assume "P' \<midarrow>\<tau>-Cal\<rightarrow>Cal P''"
    with A1 A2 obtain \<beta> T'' where A4: "\<beta> \<in>TL \<langle>P', \<tau>-Cal\<rangle>" and A5: "T'' \<in>T P''"
                              and A6: "T' \<midarrow>\<beta>\<rightarrow>Target T''"
      using STLCal_labelledStep(2)[of T' "\<tau>-Cal" P'']
      by blast
    from A1 A3 A4 A6 have "T \<rightarrow>Target* T''"
      using weakTauStep.WTS_trans[of T Target T' T'']
      unfolding getTargetLabel_def
      by (simp add: STLCal_def)
    with A5 show "\<exists>T''. T'' \<in>T P'' \<and> T \<rightarrow>Target* T''"
      by blast
  qed
next
  fix T'
  define Cal where def_Cal: "Cal = Target"
  assume "T \<rightarrow>Target* T'"
  with def_Cal have "T \<rightarrow>Cal* T'"
    by simp
  from this def_Cal show "TargetTerm T \<rightarrow>(STLCal Source Target)* (TargetTerm T')"
  proof (induct)
    case (WTS_refl T Cal)
    show "TargetTerm T \<rightarrow>(STLCal Source Target)* TargetTerm T"
      using weakTauStep.WTS_refl[of "TargetTerm T" "STLCal Source Target"]
      by simp
  next
    case (WTS_trans T Cal T' T'')
    assume "Cal = Target \<Longrightarrow> TargetTerm T \<rightarrow>(STLCal Source Target)* TargetTerm T'"
       and A: "Cal = Target"
    hence "TargetTerm T \<rightarrow>(STLCal Source Target)* TargetTerm T'"
      by simp
    moreover assume "T' \<midarrow>\<tau>-Cal\<rightarrow>Cal T''"
    with A have "TargetTerm T' \<midarrow>\<tau>-(STLCal Source Target)\<rightarrow>(STLCal Source Target) (TargetTerm T'')"
      using STLCal_labelledStep(2)[of T' "\<tau>-STLCal" "TargetTerm T''"]
      by (simp add: STLCal_def)
    ultimately show "TargetTerm T \<rightarrow>(STLCal Source Target)* TargetTerm T''"
      using weakTauStep.WTS_trans[of "TargetTerm T" "STLCal Source Target" "TargetTerm T'"
              "TargetTerm T''"]
      by simp
  qed
qed

lemma weakTauStepsST_STLCal_weakTauSteps:
  fixes P P' :: "('procS, 'procT) Proc"
  shows "P \<rightarrow>(STLCal Source Target)* P' = P \<rightarrow>ST* P'"
proof (cases P)
  case (SourceTerm SP)
  assume "SP \<in>S P"
  thus "P \<rightarrow>(STLCal Source Target)* P' = P \<rightarrow>ST* P'"
    using STLCal_weakTauSteps(1)[where S="SP" and P'="P'"]
          STWeakTauSteps_weakTauSteps(1)[where S="SP" and P'="P'"]
    by blast
next
  case (TargetTerm TP)
  assume "TP \<in>T P"
  thus "P \<rightarrow>(STLCal Source Target)* P' = P \<rightarrow>ST* P'"
    using STLCal_weakTauSteps(2)[where T="TP" and P'="P'"]
          STWeakTauSteps_weakTauSteps(2)[where T="TP" and P'="P'"]
    by blast
qed

lemma weakTauStepsST_refl:
  fixes P :: "('procS, 'procT) Proc"
  shows "P \<rightarrow>ST* P"
  by (cases P, simp_all add: WTS_refl)

lemma weakTauStepsST_trans:
  fixes P Q R :: "('procS, 'procT) Proc"
  assumes A1: "P \<rightarrow>ST* Q"
      and A2: "Q \<rightarrow>ST* R"
  shows "P \<rightarrow>ST* R"
proof -
  from A1 have "P \<rightarrow>(STLCal Source Target)* Q"
    by (simp add: weakTauStepsST_STLCal_weakTauSteps)
  moreover from A2 have "Q \<rightarrow>(STLCal Source Target)* R"
    by (simp add: weakTauStepsST_STLCal_weakTauSteps)
  ultimately have "P \<rightarrow>(STLCal Source Target)* R"
    by (rule weakTauSteps_trans)
  thus "P \<rightarrow>ST* R"
    by (simp add: weakTauStepsST_STLCal_weakTauSteps)
qed

text \<open>A weak labelled step of a term in Proc is either a weak labelled source step or a weak
      labelled target step.\<close>

abbreviation weakLabelledActionStepST
  :: "('procS, 'procT) Proc \<Rightarrow> ('labS, 'labT) Lab \<Rightarrow> ('procS, 'procT) Proc \<Rightarrow> bool"
  (\<open>_ \<midarrow>_\<rightarrow>ST* _\<close> [70, 70, 70] 80) where
  "P \<midarrow>\<alpha>\<rightarrow>ST* P' \<equiv> (\<exists>S \<beta> S'. S \<in>S P \<and> \<beta> \<in>SL \<langle>P, \<alpha>\<rangle> \<and> S' \<in>S P' \<and> S \<midarrow>\<beta>\<rightarrow>Source* S') \<or>
                   (\<exists>T \<beta> T'. T \<in>T P \<and> \<beta> \<in>TL \<langle>P, \<alpha>\<rangle> \<and> T' \<in>T P' \<and> T \<midarrow>\<beta>\<rightarrow>Target* T')"

abbreviation weakLabelledStepST
  :: "('procS, 'procT) Proc \<Rightarrow> ('labS, 'labT) Lab \<Rightarrow> ('procS, 'procT) Proc \<Rightarrow> bool"
  (\<open>_ \<midarrow>\<Zcat>_\<rightarrow>ST* _\<close> [70, 70, 70] 80) where
  "P \<midarrow>\<Zcat>\<alpha>\<rightarrow>ST* P' \<equiv> (\<exists>S \<beta> S'. S \<in>S P \<and> \<beta> \<in>SL \<langle>P, \<alpha>\<rangle> \<and> S' \<in>S P' \<and> S \<midarrow>\<Zcat>\<beta>\<rightarrow>Source* S') \<or>
                    (\<exists>T \<beta> T'. T \<in>T P \<and> \<beta> \<in>TL \<langle>P, \<alpha>\<rangle> \<and> T' \<in>T P' \<and> T \<midarrow>\<Zcat>\<beta>\<rightarrow>Target* T')"

lemma STWeakLabelledActionSteps_weakLabelledActionSteps:
  fixes S  :: "'procS"
    and T  :: "'procT"
    and \<alpha>  :: "('labS, 'labT) Lab"
    and P' :: "('procS, 'procT) Proc"
  shows "SourceTerm S \<midarrow>\<alpha>\<rightarrow>ST* P' = (\<exists>\<beta> S'. \<beta> \<in>SL \<langle>SourceTerm S, \<alpha>\<rangle> \<and> S' \<in>S P' \<and> S \<midarrow>\<beta>\<rightarrow>Source* S')"
    and "TargetTerm T \<midarrow>\<alpha>\<rightarrow>ST* P' = (\<exists>\<beta> T'. \<beta> \<in>TL \<langle>TargetTerm T, \<alpha>\<rangle> \<and> T' \<in>T P' \<and> T \<midarrow>\<beta>\<rightarrow>Target* T')"
  by blast+

lemma STWeakLabelledSteps_weakLabelledSteps:
  fixes S  :: "'procS"
    and T  :: "'procT"
    and \<alpha>  :: "('labS, 'labT) Lab"
    and P' :: "('procS, 'procT) Proc"
  shows "SourceTerm S \<midarrow>\<Zcat>\<alpha>\<rightarrow>ST* P' =
         (\<exists>\<beta> S'. \<beta> \<in>SL \<langle>SourceTerm S, \<alpha>\<rangle> \<and> S' \<in>S P' \<and> S \<midarrow>\<Zcat>\<beta>\<rightarrow>Source* S')"
    and "TargetTerm T \<midarrow>\<Zcat>\<alpha>\<rightarrow>ST* P' =
         (\<exists>\<beta> T'. \<beta> \<in>TL \<langle>TargetTerm T, \<alpha>\<rangle> \<and> T' \<in>T P' \<and> T \<midarrow>\<Zcat>\<beta>\<rightarrow>Target* T')"
  by blast+

lemma STLCal_weakLabelledActionSteps:
  fixes S  :: "'procS"
    and T  :: "'procT"
    and \<alpha>  :: "('labS, 'labT) Lab"
    and P' :: "('procS, 'procT) Proc"
  shows "SourceTerm S \<midarrow>\<alpha>\<rightarrow>(STLCal Source Target)* P' =
         (\<exists>\<beta> S'. \<beta> \<in>SL \<langle>SourceTerm S, \<alpha>\<rangle> \<and> S' \<in>S P' \<and> S \<midarrow>\<beta>\<rightarrow>Source* S')"
    and "TargetTerm T \<midarrow>\<alpha>\<rightarrow>(STLCal Source Target)* P' =
         (\<exists>\<beta> T'. \<beta> \<in>TL \<langle>TargetTerm T, \<alpha>\<rangle> \<and> T' \<in>T P' \<and> T \<midarrow>\<beta>\<rightarrow>Target* T')"
proof -
  have "SourceTerm S \<midarrow>\<alpha>\<rightarrow>(STLCal Source Target)* P' \<Longrightarrow>
        (\<exists>\<beta> S'. \<beta> \<in>SL \<langle>SourceTerm S, \<alpha>\<rangle> \<and> S' \<in>S P' \<and> S \<midarrow>\<beta>\<rightarrow>Source* S')"
  proof (cases "\<alpha> = \<tau>-STLCal")
    assume "SourceTerm S \<midarrow>\<alpha>\<rightarrow>(STLCal Source Target)* P'" and "\<alpha> = \<tau>-STLCal"
    hence False
      unfolding STLCal_def weakLabelledActionStep_def
      by simp
    thus "\<exists>\<beta> S'. \<beta> \<in>SL \<langle>SourceTerm S, \<alpha>\<rangle> \<and> S' \<in>S P' \<and> S \<midarrow>\<beta>\<rightarrow>Source* S'"
      by simp
  next
    assume "SourceTerm S \<midarrow>\<alpha>\<rightarrow>(STLCal Source Target)* P'" and A1: "\<alpha> \<noteq> \<tau>-STLCal"
    then obtain Q Q' where A2: "SourceTerm S \<rightarrow>(STLCal Source Target)* Q"
                       and A3: "Q \<midarrow>\<alpha>\<rightarrow>(STLCal Source Target) Q'"
                       and A4: "Q' \<rightarrow>(STLCal Source Target)* P'"
      unfolding weakLabelledActionStep_def
      using internalST_iff_internal
      by blast
    from A2 obtain S' where A5: "S' \<in>S Q" and A6: "S \<rightarrow>Source* S'"
      using STLCal_weakTauSteps(1)[of S Q]
      by blast
    from A1 A3 A5 obtain \<beta> S'' where A7: "\<beta> \<in>SL \<langle>SourceTerm S, \<alpha>\<rangle>" and A8: "S'' \<in>S Q'"
                                 and A9: "S' \<midarrow>\<beta>\<rightarrow>Source S''"
      unfolding STLCal_def getSourceLabel_def
      by auto
    from A4 A8 obtain S''' where A10: "S''' \<in>S P'" and A11: "S'' \<rightarrow>Source* S'''"
      using STLCal_weakTauSteps(1)[of S'' P']
      by blast
    from A1 A6 A7 A9 A11 have "S \<midarrow>\<beta>\<rightarrow>Source* S'''"
      unfolding weakLabelledActionStep_def getSourceLabel_def
      by blast
    with A7 A10 show "\<exists>\<beta> S'''. \<beta> \<in>SL \<langle>SourceTerm S, \<alpha>\<rangle> \<and> S''' \<in>S P' \<and> S \<midarrow>\<beta>\<rightarrow>Source* S'''"
      by blast
  qed
  moreover have "(\<exists>\<beta> S'. \<beta> \<in>SL \<langle>SourceTerm S, \<alpha>\<rangle> \<and> S' \<in>S P' \<and> S \<midarrow>\<beta>\<rightarrow>Source* S') \<Longrightarrow>
                 SourceTerm S \<midarrow>\<alpha>\<rightarrow>(STLCal Source Target)* P'"
  proof -
    assume "\<exists>\<beta> S'''. \<beta> \<in>SL \<langle>SourceTerm S, \<alpha>\<rangle> \<and> S''' \<in>S P' \<and> S \<midarrow>\<beta>\<rightarrow>Source* S'''"
    then obtain \<beta> S''' where A1: "\<beta> \<in>SL \<langle>SourceTerm S, \<alpha>\<rangle>" and A2: "S''' \<in>S P'"
                         and A3: "S \<midarrow>\<beta>\<rightarrow>Source* S'''"
      by blast
    from A3 obtain S' S'' where A4: "\<beta> \<noteq> \<tau>-Source" and A5: "S \<rightarrow>Source* S'"
                            and A6: "S' \<midarrow>\<beta>\<rightarrow>Source S''" and A7: "S'' \<rightarrow>Source* S'''"
      unfolding weakLabelledActionStep_def
      by blast
    from A1 A4 have "\<alpha> \<noteq> \<tau>-(STLCal Source Target)"
      unfolding STLCal_def getSourceLabel_def
      by simp
    moreover from A5 have "SourceTerm S \<rightarrow>(STLCal Source Target)* SourceTerm S'"
      using STLCal_weakTauSteps(1)[of S "SourceTerm S'"]
      by simp
    moreover from A1 A4 A6 have "SourceTerm S' \<midarrow>\<alpha>\<rightarrow>(STLCal Source Target) (SourceTerm S'')"
      using STLCal_labelledStep(1)[of S' \<alpha> "SourceTerm S''"]
      unfolding getSourceLabel_def
      by simp
    moreover from A2 A7 have "SourceTerm S'' \<rightarrow>(STLCal Source Target)* P'"
      using STLCal_weakTauSteps(1)[of S'' P']
      by simp
    ultimately show "SourceTerm S \<midarrow>\<alpha>\<rightarrow>(STLCal Source Target)* P'"
      unfolding weakLabelledActionStep_def
      by blast
  qed
  ultimately show "SourceTerm S \<midarrow>\<alpha>\<rightarrow>(STLCal Source Target)* P' =
                   (\<exists>\<beta> S'. \<beta> \<in>SL \<langle>SourceTerm S, \<alpha>\<rangle> \<and> S' \<in>S P' \<and> S \<midarrow>\<beta>\<rightarrow>Source* S')"
    by auto
  have "TargetTerm T \<midarrow>\<alpha>\<rightarrow>(STLCal Source Target)* P' \<Longrightarrow>
        (\<exists>\<beta> T'. \<beta> \<in>TL \<langle>TargetTerm T, \<alpha>\<rangle> \<and> T' \<in>T P' \<and> T \<midarrow>\<beta>\<rightarrow>Target* T')"
  proof (cases "\<alpha> = \<tau>-STLCal")
    assume "TargetTerm T \<midarrow>\<alpha>\<rightarrow>(STLCal Source Target)* P'" and "\<alpha> = \<tau>-STLCal"
    hence False
      unfolding STLCal_def weakLabelledActionStep_def
      by simp
    thus "\<exists>\<beta> T'. \<beta> \<in>TL \<langle>TargetTerm T, \<alpha>\<rangle> \<and> T' \<in>T P' \<and> T \<midarrow>\<beta>\<rightarrow>Target* T'"
      by simp
  next
    assume "TargetTerm T \<midarrow>\<alpha>\<rightarrow>(STLCal Source Target)* P'" and A1: "\<alpha> \<noteq> \<tau>-STLCal"
    then obtain Q Q' where A2: "TargetTerm T \<rightarrow>(STLCal Source Target)* Q"
                       and A3: "Q \<midarrow>\<alpha>\<rightarrow>(STLCal Source Target) Q'"
                       and A4: "Q' \<rightarrow>(STLCal Source Target)* P'"
      unfolding weakLabelledActionStep_def
      using internalST_iff_internal
      by blast
    from A2 obtain T' where A5: "T' \<in>T Q" and A6: "T \<rightarrow>Target* T'"
      using STLCal_weakTauSteps(2)[of T Q]
      by blast
    from A1 A3 A5 obtain \<beta> T'' where A7: "\<beta> \<in>TL \<langle>TargetTerm T, \<alpha>\<rangle>" and A8: "T'' \<in>T Q'"
                                 and A9: "T' \<midarrow>\<beta>\<rightarrow>Target T''"
      unfolding STLCal_def getTargetLabel_def
      by auto
    from A4 A8 obtain T''' where A10: "T''' \<in>T P'" and A11: "T'' \<rightarrow>Target* T'''"
      using STLCal_weakTauSteps(2)[of T'' P']
      by blast
    from A1 A6 A7 A9 A11 have "T \<midarrow>\<beta>\<rightarrow>Target* T'''"
      unfolding weakLabelledActionStep_def getTargetLabel_def
      by blast
    with A7 A10 show "\<exists>\<beta> T'''. \<beta> \<in>TL \<langle>TargetTerm T, \<alpha>\<rangle> \<and> T''' \<in>T P' \<and> T \<midarrow>\<beta>\<rightarrow>Target* T'''"
      by blast
  qed
  moreover have "(\<exists>\<beta> T'. \<beta> \<in>TL \<langle>TargetTerm T, \<alpha>\<rangle> \<and> T' \<in>T P' \<and> T \<midarrow>\<beta>\<rightarrow>Target* T') \<Longrightarrow>
                 TargetTerm T \<midarrow>\<alpha>\<rightarrow>(STLCal Source Target)* P'"
  proof -
    assume "\<exists>\<beta> T'''. \<beta> \<in>TL \<langle>TargetTerm T, \<alpha>\<rangle> \<and> T''' \<in>T P' \<and> T \<midarrow>\<beta>\<rightarrow>Target* T'''"
    then obtain \<beta> T''' where A1: "\<beta> \<in>TL \<langle>TargetTerm T, \<alpha>\<rangle>" and A2: "T''' \<in>T P'"
                         and A3: "T \<midarrow>\<beta>\<rightarrow>Target* T'''"
      by blast
    from A3 obtain T' T'' where A4: "\<beta> \<noteq> \<tau>-Target" and A5: "T \<rightarrow>Target* T'"
                            and A6: "T' \<midarrow>\<beta>\<rightarrow>Target T''" and A7: "T'' \<rightarrow>Target* T'''"
      unfolding weakLabelledActionStep_def
      by blast
    from A1 A4 have "\<alpha> \<noteq> \<tau>-(STLCal Source Target)"
      unfolding STLCal_def getTargetLabel_def
      by simp
    moreover from A5 have "TargetTerm T \<rightarrow>(STLCal Source Target)* TargetTerm T'"
      using STLCal_weakTauSteps(2)[of T "TargetTerm T'"]
      by simp
    moreover from A1 A4 A6 have "TargetTerm T' \<midarrow>\<alpha>\<rightarrow>(STLCal Source Target) (TargetTerm T'')"
      using STLCal_labelledStep(2)[of T' \<alpha> "TargetTerm T''"]
      unfolding getTargetLabel_def
      by simp
    moreover from A2 A7 have "TargetTerm T'' \<rightarrow>(STLCal Source Target)* P'"
      using STLCal_weakTauSteps(2)[of T'' P']
      by simp
    ultimately show "TargetTerm T \<midarrow>\<alpha>\<rightarrow>(STLCal Source Target)* P'"
      unfolding weakLabelledActionStep_def
      by blast
  qed
  ultimately show "TargetTerm T \<midarrow>\<alpha>\<rightarrow>(STLCal Source Target)* P' =
                   (\<exists>\<beta> T'. \<beta> \<in>TL \<langle>TargetTerm T, \<alpha>\<rangle> \<and> T' \<in>T P' \<and> T \<midarrow>\<beta>\<rightarrow>Target* T')"
    by auto
qed

lemma STLCal_weakLabelledSteps:
  fixes S  :: "'procS"
    and T  :: "'procT"
    and \<alpha>  :: "('labS, 'labT) Lab"
    and P' :: "('procS, 'procT) Proc"
  shows "SourceTerm S \<midarrow>\<Zcat>\<alpha>\<rightarrow>(STLCal Source Target)* P' =
         (\<exists>\<beta> S'. \<beta> \<in>SL \<langle>SourceTerm S, \<alpha>\<rangle> \<and> S' \<in>S P' \<and> S \<midarrow>\<Zcat>\<beta>\<rightarrow>Source* S')"
    and "TargetTerm T \<midarrow>\<Zcat>\<alpha>\<rightarrow>(STLCal Source Target)* P' =
         (\<exists>\<beta> T'. \<beta> \<in>TL \<langle>TargetTerm T, \<alpha>\<rangle> \<and> T' \<in>T P' \<and> T \<midarrow>\<Zcat>\<beta>\<rightarrow>Target* T')"
proof -
  have "SourceTerm S \<midarrow>\<Zcat>\<alpha>\<rightarrow>(STLCal Source Target)* P' \<Longrightarrow>
        (\<exists>\<beta> S'. \<beta> \<in>SL \<langle>SourceTerm S, \<alpha>\<rangle> \<and> S' \<in>S P' \<and> S \<midarrow>\<Zcat>\<beta>\<rightarrow>Source* S')"
  proof (cases "\<alpha> = \<tau>-STLCal")
    assume A1: "\<alpha> = \<tau>-STLCal"
    then have A2: "(\<tau>-Source) \<in>SL \<langle>SourceTerm S, \<alpha>\<rangle>"
      unfolding getSourceLabel_def
      by simp
    assume "SourceTerm S \<midarrow>\<Zcat>\<alpha>\<rightarrow>(STLCal Source Target)* P'"
    with A1 have "SourceTerm S \<rightarrow>(STLCal Source Target)* P'"
      unfolding weakLabelledStep_def
      using internalST_iff_internal
      by simp
    then obtain S' where A3: "S' \<in>S P'" and A4: "S \<rightarrow>Source* S'"
      using STLCal_weakTauSteps(1)[of S P']
      by blast
    from A4 have "S \<midarrow>\<Zcat>(\<tau>-Source)\<rightarrow>Source* S'"
      unfolding weakLabelledStep_def
      by simp
    with A2 A3 show "\<exists>\<beta> S'. \<beta> \<in>SL \<langle>SourceTerm S, \<alpha>\<rangle> \<and> S' \<in>S P' \<and> S \<midarrow>\<Zcat>\<beta>\<rightarrow>Source* S'"
      by blast
  next
    assume "SourceTerm S \<midarrow>\<Zcat>\<alpha>\<rightarrow>(STLCal Source Target)* P'" and A1: "\<alpha> \<noteq> \<tau>-STLCal"
    hence "SourceTerm S \<midarrow>\<alpha>\<rightarrow>(STLCal Source Target)* P'"
      unfolding weakLabelledStep_def
      using internalST_iff_internal
      by simp
    then obtain \<beta> S' where A2: "\<beta> \<in>SL \<langle>SourceTerm S, \<alpha>\<rangle>" and A3: "S' \<in>S P'"
                       and A4: "S \<midarrow>\<beta>\<rightarrow>Source* S'"
      using STLCal_weakLabelledActionSteps(1)[of S \<alpha> P']
      by blast
    from A1 A2 A4 have "S \<midarrow>\<Zcat>\<beta>\<rightarrow>Source* S'"
      unfolding weakLabelledStep_def getSourceLabel_def
      by simp
    with A2 A3 show "\<exists>\<beta> S'. \<beta> \<in>SL \<langle>SourceTerm S, \<alpha>\<rangle> \<and> S' \<in>S P' \<and> S \<midarrow>\<Zcat>\<beta>\<rightarrow>Source* S'"
      by blast
  qed
  moreover have "(\<exists>\<beta> S'. \<beta> \<in>SL \<langle>SourceTerm S, \<alpha>\<rangle> \<and> S' \<in>S P' \<and> S \<midarrow>\<Zcat>\<beta>\<rightarrow>Source* S') \<Longrightarrow>
                 SourceTerm S \<midarrow>\<Zcat>\<alpha>\<rightarrow>(STLCal Source Target)* P'"
  proof -
    assume "\<exists>\<beta> S'. \<beta> \<in>SL \<langle>SourceTerm S, \<alpha>\<rangle> \<and> S' \<in>S P' \<and> S \<midarrow>\<Zcat>\<beta>\<rightarrow>Source* S'"
    then obtain \<beta> S' where A1: "\<beta> \<in>SL \<langle>SourceTerm S, \<alpha>\<rangle>" and A2: "S' \<in>S P'"
                       and A3: "S \<midarrow>\<Zcat>\<beta>\<rightarrow>Source* S'"
      by blast
    from A1 show "SourceTerm S \<midarrow>\<Zcat>\<alpha>\<rightarrow>(STLCal Source Target)* P'"
      unfolding getSourceLabel_def
    proof auto
      assume B: "\<beta> \<noteq> \<tau>-Source"
      with A3 have "S \<midarrow>\<beta>\<rightarrow>Source* S'"
        unfolding weakLabelledStep_def
        by simp
      with A2 B have "SourceTerm S \<midarrow>(SourceLabel \<beta>)\<rightarrow>(STLCal Source Target)* P'"
        using STLCal_weakLabelledActionSteps(1)[of S "SourceLabel \<beta>" P']
        unfolding getSourceLabel_def
        by simp
      thus "SourceTerm S \<midarrow>\<Zcat>(SourceLabel \<beta>)\<rightarrow>(STLCal Source Target)* P'"
        unfolding weakLabelledStep_def weakLabelledActionStep_def
        by simp
    next
      assume "\<beta> = \<tau>-Source"
      with A3 have "S \<rightarrow>Source* S'"
        unfolding weakLabelledStep_def
        by simp
      with A2 have "SourceTerm S \<rightarrow>(STLCal Source Target)* P'"
        using STLCal_weakTauSteps(1)[of S P']
        by simp
      thus "SourceTerm S \<midarrow>\<Zcat>\<tau>-STLCal\<rightarrow>(STLCal Source Target)* P'"
        unfolding weakLabelledStep_def
        using internalST_iff_internal
        by simp
    qed
  qed
  ultimately show "SourceTerm S \<midarrow>\<Zcat>\<alpha>\<rightarrow>(STLCal Source Target)* P' =
                   (\<exists>\<beta> S'. \<beta> \<in>SL \<langle>SourceTerm S, \<alpha>\<rangle> \<and> S' \<in>S P' \<and> S \<midarrow>\<Zcat>\<beta>\<rightarrow>Source* S')"
    by blast
next
  have "TargetTerm T \<midarrow>\<Zcat>\<alpha>\<rightarrow>(STLCal Source Target)* P' \<Longrightarrow>
        (\<exists>\<beta> T'. \<beta> \<in>TL \<langle>TargetTerm T, \<alpha>\<rangle> \<and> T' \<in>T P' \<and> T \<midarrow>\<Zcat>\<beta>\<rightarrow>Target* T')"
  proof (cases "\<alpha> = \<tau>-STLCal")
    assume A1: "\<alpha> = \<tau>-STLCal"
    then have A2: "(\<tau>-Target) \<in>TL \<langle>TargetTerm T, \<alpha>\<rangle>"
      unfolding getTargetLabel_def
      by simp
    assume "TargetTerm T \<midarrow>\<Zcat>\<alpha>\<rightarrow>(STLCal Source Target)* P'"
    with A1 have "TargetTerm T \<rightarrow>(STLCal Source Target)* P'"
      unfolding weakLabelledStep_def
      using internalST_iff_internal
      by simp
    then obtain T' where A3: "T' \<in>T P'" and A4: "T \<rightarrow>Target* T'"
      using STLCal_weakTauSteps(2)[of T P']
      by blast
    from A4 have "T \<midarrow>\<Zcat>(\<tau>-Target)\<rightarrow>Target* T'"
      unfolding weakLabelledStep_def
      by simp
    with A2 A3 show "\<exists>\<beta> T'. \<beta> \<in>TL \<langle>TargetTerm T, \<alpha>\<rangle> \<and> T' \<in>T P' \<and> T \<midarrow>\<Zcat>\<beta>\<rightarrow>Target* T'"
      by blast
  next
    assume "TargetTerm T \<midarrow>\<Zcat>\<alpha>\<rightarrow>(STLCal Source Target)* P'" and A1: "\<alpha> \<noteq> \<tau>-STLCal"
    hence "TargetTerm T \<midarrow>\<alpha>\<rightarrow>(STLCal Source Target)* P'"
      unfolding weakLabelledStep_def
      using internalST_iff_internal
      by simp
    then obtain \<beta> T' where A2: "\<beta> \<in>TL \<langle>TargetTerm T, \<alpha>\<rangle>" and A3: "T' \<in>T P'"
                       and A4: "T \<midarrow>\<beta>\<rightarrow>Target* T'"
      using STLCal_weakLabelledActionSteps(2)[of T \<alpha> P']
      by blast
    from A1 A2 A4 have "T \<midarrow>\<Zcat>\<beta>\<rightarrow>Target* T'"
      unfolding weakLabelledStep_def getTargetLabel_def
      by simp
    with A2 A3 show "\<exists>\<beta> T'. \<beta> \<in>TL \<langle>TargetTerm T, \<alpha>\<rangle> \<and> T' \<in>T P' \<and> T \<midarrow>\<Zcat>\<beta>\<rightarrow>Target* T'"
      by blast
  qed
  moreover have "(\<exists>\<beta> T'. \<beta> \<in>TL \<langle>TargetTerm T, \<alpha>\<rangle> \<and> T' \<in>T P' \<and> T \<midarrow>\<Zcat>\<beta>\<rightarrow>Target* T') \<Longrightarrow>
                 TargetTerm T \<midarrow>\<Zcat>\<alpha>\<rightarrow>(STLCal Source Target)* P'"
  proof -
    assume "\<exists>\<beta> T'. \<beta> \<in>TL \<langle>TargetTerm T, \<alpha>\<rangle> \<and> T' \<in>T P' \<and> T \<midarrow>\<Zcat>\<beta>\<rightarrow>Target* T'"
    then obtain \<beta> T' where A1: "\<beta> \<in>TL \<langle>TargetTerm T, \<alpha>\<rangle>" and A2: "T' \<in>T P'"
                       and A3: "T \<midarrow>\<Zcat>\<beta>\<rightarrow>Target* T'"
      by blast
    from A1 show "TargetTerm T \<midarrow>\<Zcat>\<alpha>\<rightarrow>(STLCal Source Target)* P'"
      unfolding getTargetLabel_def
    proof auto
      assume B: "\<beta> \<noteq> \<tau>-Target"
      with A3 have "T \<midarrow>\<beta>\<rightarrow>Target* T'"
        unfolding weakLabelledStep_def
        by simp
      with A2 B have "TargetTerm T \<midarrow>(TargetLabel \<beta>)\<rightarrow>(STLCal Source Target)* P'"
        using STLCal_weakLabelledActionSteps(2)[of T "TargetLabel \<beta>" P']
        unfolding getTargetLabel_def
        by simp
      thus "TargetTerm T \<midarrow>\<Zcat>(TargetLabel \<beta>)\<rightarrow>(STLCal Source Target)* P'"
        unfolding weakLabelledStep_def weakLabelledActionStep_def
        by simp
    next
      assume "\<beta> = \<tau>-Target"
      with A3 have "T \<rightarrow>Target* T'"
        unfolding weakLabelledStep_def
        by simp
      with A2 have "TargetTerm T \<rightarrow>(STLCal Source Target)* P'"
        using STLCal_weakTauSteps(2)[of T P']
        by simp
      thus "TargetTerm T \<midarrow>\<Zcat>\<tau>-STLCal\<rightarrow>(STLCal Source Target)* P'"
        unfolding weakLabelledStep_def
        using internalST_iff_internal
        by simp
    qed
  qed
  ultimately show "TargetTerm T \<midarrow>\<Zcat>\<alpha>\<rightarrow>(STLCal Source Target)* P' =
                   (\<exists>\<beta> T'. \<beta> \<in>TL \<langle>TargetTerm T, \<alpha>\<rangle> \<and> T' \<in>T P' \<and> T \<midarrow>\<Zcat>\<beta>\<rightarrow>Target* T')"
    by blast
qed

lemma weakLabelledActionStepsST_STLCal_weakLabelledActionSteps:
  fixes P P' :: "('procS, 'procT) Proc"
    and \<alpha>    :: "('labS, 'labT) Lab"
  shows "P \<midarrow>\<alpha>\<rightarrow>(STLCal Source Target)* P' = P \<midarrow>\<alpha>\<rightarrow>ST* P'"
proof (cases P)
  case (SourceTerm SP)
  assume "SP \<in>S P"
  thus "P \<midarrow>\<alpha>\<rightarrow>(STLCal Source Target)* P' = P \<midarrow>\<alpha>\<rightarrow>ST* P'"
    using STLCal_weakLabelledActionSteps(1)[of SP \<alpha> P']
    by blast
next
  case (TargetTerm TP)
  assume "TP \<in>T P"
  thus "P \<midarrow>\<alpha>\<rightarrow>(STLCal Source Target)* P' = P \<midarrow>\<alpha>\<rightarrow>ST* P'"
    using STLCal_weakLabelledActionSteps(2)[of TP \<alpha> P']
    by blast
qed

lemma weakLabelledStepsST_STLCal_weakLabelledSteps:
  fixes P P' :: "('procS, 'procT) Proc"
    and \<alpha>    :: "('labS, 'labT) Lab"
  shows "P \<midarrow>\<Zcat>\<alpha>\<rightarrow>(STLCal Source Target)* P' = P \<midarrow>\<Zcat>\<alpha>\<rightarrow>ST* P'"
proof (cases P)
  case (SourceTerm SP)
  assume "SP \<in>S P"
  thus "P \<midarrow>\<Zcat>\<alpha>\<rightarrow>(STLCal Source Target)* P' = P \<midarrow>\<Zcat>\<alpha>\<rightarrow>ST* P'"
    using STLCal_weakLabelledSteps(1)[of SP \<alpha> P']
    by blast
next
  case (TargetTerm TP)
  assume "TP \<in>T P"
  thus "P \<midarrow>\<Zcat>\<alpha>\<rightarrow>(STLCal Source Target)* P' = P \<midarrow>\<Zcat>\<alpha>\<rightarrow>ST* P'"
    using STLCal_weakLabelledSteps(2)[of TP \<alpha> P']
    by blast
qed

text \<open>A sequence of weak labelled steps of a term in Proc is either a sequence of weak labelled
      source term steps or a sequence of weak labelled target term steps.\<close>

abbreviation weakLabelledSequenceST
  :: "('procS, 'procT) Proc \<Rightarrow> ('labS, 'labT) Lab list \<Rightarrow> ('procS, 'procT) Proc \<Rightarrow> bool"
  (\<open>_ \<midarrow>\<frown>_\<rightarrow>ST* _\<close> [70, 70, 70] 80) where
  "P \<midarrow>\<frown>w\<rightarrow>ST* P' \<equiv> (\<exists>S v S'. S \<in>S P \<and> v \<in>SL* \<langle>P, w\<rangle> \<and> S' \<in>S P' \<and> S \<midarrow>\<frown>v\<rightarrow>Source* S') \<or>
                     (\<exists>T v T'. T \<in>T P \<and> v \<in>TL* \<langle>P, w\<rangle> \<and> T' \<in>T P' \<and> T \<midarrow>\<frown>v\<rightarrow>Target* T')"

lemma lifted_word_on_source_labels_kinds:
  fixes v :: "'labS list"
    and P :: "('procS, 'procT) Proc"
    and w :: "('labS, 'labT) Lab list"
  assumes "v \<in>SL* \<langle>P, w\<rangle>"
  shows "\<forall>\<alpha> \<in> set w. \<alpha> \<in> LabS \<or> \<alpha> = \<tau>-STLCal" and "P \<in> ProcS"
  using assms
  by (induct, auto simp add: isSourceLabel_def getSourceLabel_def)

lemma lifted_word_on_target_labels_kinds:
  fixes v :: "'labT list"
    and P :: "('procS, 'procT) Proc"
    and w :: "('labS, 'labT) Lab list"
  assumes "v \<in>TL* \<langle>P, w\<rangle>"
  shows "\<forall>\<alpha> \<in> set w. \<alpha> \<in> LabT \<or> \<alpha> = \<tau>-STLCal" and "P \<in> ProcT"
  using assms
  by (induct, auto simp add: isTargetLabel_def getTargetLabel_def)

lemma lift_word_on_source_labels:
  fixes w :: "'labS list"
  shows "\<exists>P v. w \<in>SL* \<langle>P, v\<rangle>"
proof (induct w rule: rev_induct)
  case Nil
  show "\<exists>P v. [] \<in>SL* \<langle>P, v\<rangle>"
    using SLNil
    by blast
next
  case (snoc \<alpha> w)
  assume "\<exists>P v. w \<in>SL* \<langle>P, v\<rangle>"
  then obtain P v where "w \<in>SL* \<langle>P, v\<rangle>"
    by blast
  moreover obtain Q \<beta> where "\<alpha> \<in>SL \<langle>Q, \<beta>\<rangle>" and "Q \<in> ProcS"
    unfolding getSourceLabel_def
    by blast
  ultimately show "\<exists>P v'. (w@[\<alpha>]) \<in>SL* \<langle>P, v'\<rangle>"
    using SLCons[of w P v \<alpha> Q \<beta>]
    by blast
qed

lemma lift_word_on_target_labels:
  fixes w :: "'labT list"
  shows "\<exists>P v. w \<in>TL* \<langle>P, v\<rangle>"
proof (induct w rule: rev_induct)
  case Nil
  show "\<exists>P v. [] \<in>TL* \<langle>P, v\<rangle>"
    using TLNil
    by blast
next
  case (snoc \<alpha> w)
  assume "\<exists>P v. w \<in>TL* \<langle>P, v\<rangle>"
  then obtain P v where "w \<in>TL* \<langle>P, v\<rangle>"
    by blast
  moreover obtain Q \<beta> where "\<alpha> \<in>TL \<langle>Q, \<beta>\<rangle>" and "Q \<in> ProcT"
    unfolding getTargetLabel_def
    by blast
  ultimately show "\<exists>P' v'. (w@[\<alpha>]) \<in>TL* \<langle>P', v'\<rangle>"
    using TLCons[of w P v \<alpha> Q \<beta>]
    by blast
qed

lemma lift_source_word_length:
  fixes w :: "'labS list"
    and P :: "('procS, 'procT) Proc"
    and v :: "('labS, 'labT) Lab list"
  assumes "w \<in>SL* \<langle>P, v\<rangle>"
  shows "length w = length v" and "P \<in> ProcS"
  using assms
  by (induct, simp_all)

lemma lift_target_word_length:
  fixes w :: "'labT list"
    and P :: "('procS, 'procT) Proc"
    and v :: "('labS, 'labT) Lab list"
  assumes "w \<in>TL* \<langle>P, v\<rangle>"
  shows "length w = length v" and "P \<in> ProcT"
  using assms
  by (induct, simp_all)

lemma lift_composed_word_on_source_labels:
  fixes v  :: "'labS list"
    and \<beta>  :: "'labS"
    and P  :: "('procS, 'procT) Proc"
    and w' :: "('labS, 'labT) Lab list"
  assumes lifting: "(v@[\<beta>]) \<in>SL* \<langle>P, w'\<rangle>"
  shows "\<exists>w \<alpha>. w' = w@[\<alpha>] \<and> v \<in>SL* \<langle>P, w\<rangle> \<and> \<beta> \<in>SL \<langle>P, \<alpha>\<rangle>"
proof -
  define v' where v'_def: "v' = v@[\<beta>]"
  with lifting have "v' \<in>SL* \<langle>P, w'\<rangle>"
    by simp
  from this v'_def show "\<exists>w \<alpha>. w' = w@[\<alpha>] \<and> v \<in>SL* \<langle>P, w\<rangle> \<and> \<beta> \<in>SL \<langle>P, \<alpha>\<rangle>"
  proof induct
    case (SLNil P)
    assume "[] = v@[\<beta>]"
    hence False
      by simp
    thus "\<exists>w \<alpha>. [] = w@[\<alpha>] \<and> v \<in>SL* \<langle>P, w\<rangle> \<and> \<beta> \<in>SL \<langle>P, \<alpha>\<rangle>"
      by simp
  next
    case (SLCons v' P w \<beta>' Q \<alpha>)
    assume "v'@[\<beta>'] = v@[\<beta>]"
    hence A1: "v' = v" and A2: "\<beta>' = \<beta>"
      by simp_all
    assume "v' \<in>SL* \<langle>P, w\<rangle>"
    with A1 have A3: "v \<in>SL* \<langle>P, w\<rangle>"
      by simp
    hence A4: "P \<in> ProcS"
      using lift_source_word_length(2)[of v P w]
      by simp
    assume "\<beta>' \<in>SL \<langle>Q, \<alpha>\<rangle>"
    with A2 A4 have "\<beta> \<in>SL \<langle>P, \<alpha>\<rangle>"
      unfolding getSourceLabel_def
      by simp
    with A3 show "\<exists>w' \<alpha>'. w@[\<alpha>] = w'@[\<alpha>'] \<and> v \<in>SL* \<langle>P, w'\<rangle> \<and> \<beta> \<in>SL \<langle>P, \<alpha>'\<rangle>"
      by blast
  qed
qed

lemma lift_composed_word_on_target_labels:
  fixes v  :: "'labT list"
    and \<beta>  :: "'labT"
    and P  :: "('procS, 'procT) Proc"
    and w' :: "('labS, 'labT) Lab list"
  assumes lifting: "(v@[\<beta>]) \<in>TL* \<langle>P, w'\<rangle>"
  shows "\<exists>w \<alpha>. w' = w@[\<alpha>] \<and> v \<in>TL* \<langle>P, w\<rangle> \<and> \<beta> \<in>TL \<langle>P, \<alpha>\<rangle>"
proof -
  define v' where v'_def: "v' = v@[\<beta>]"
  with lifting have "v' \<in>TL* \<langle>P, w'\<rangle>"
    by simp
  from this v'_def show "\<exists>w \<alpha>. w' = w@[\<alpha>] \<and> v \<in>TL* \<langle>P, w\<rangle> \<and> \<beta> \<in>TL \<langle>P, \<alpha>\<rangle>"
  proof induct
    case (TLNil P)
    assume "[] = v@[\<beta>]"
    hence False
      by simp
    thus "\<exists>w \<alpha>. [] = w@[\<alpha>] \<and> v \<in>TL* \<langle>P, w\<rangle> \<and> \<beta> \<in>TL \<langle>P, \<alpha>\<rangle>"
      by simp
  next
    case (TLCons v' P w \<beta>' Q \<alpha>)
    assume "v'@[\<beta>'] = v@[\<beta>]"
    hence A1: "v' = v" and A2: "\<beta>' = \<beta>"
      by simp_all
    assume "v' \<in>TL* \<langle>P, w\<rangle>"
    with A1 have A3: "v \<in>TL* \<langle>P, w\<rangle>"
      by simp
    hence A4: "P \<in> ProcT"
      using lift_target_word_length(2)[of v P w]
      by simp
    assume "\<beta>' \<in>TL \<langle>Q, \<alpha>\<rangle>"
    with A2 A4 have "\<beta> \<in>TL \<langle>P, \<alpha>\<rangle>"
      unfolding getTargetLabel_def
      by simp
    with A3 show "\<exists>w' \<alpha>'. w@[\<alpha>] = w'@[\<alpha>'] \<and> v \<in>TL* \<langle>P, w'\<rangle> \<and> \<beta> \<in>TL \<langle>P, \<alpha>'\<rangle>"
      by blast
  qed
qed

lemma lifted_composed_word_on_source_labels:
  fixes v' :: "'labS list"
    and P  :: "('procS, 'procT) Proc"
    and w  :: "('labS, 'labT) Lab list"
    and \<alpha>  :: "('labS, 'labT) Lab"
  assumes lifting: "v' \<in>SL* \<langle>P, (w@[\<alpha>])\<rangle>"
  shows "\<exists>v \<beta>. v' = v@[\<beta>] \<and> v \<in>SL* \<langle>P, w\<rangle> \<and> \<beta> \<in>SL \<langle>P, \<alpha>\<rangle>"
proof -
  define w' where w'_def: "w' = w@[\<alpha>]"
  with lifting have "v' \<in>SL* \<langle>P, w'\<rangle>"
    by simp
  from this w'_def show "\<exists>v \<beta>. v' = v@[\<beta>] \<and> v \<in>SL* \<langle>P, w\<rangle> \<and> \<beta> \<in>SL \<langle>P, \<alpha>\<rangle>"
  proof induct
    case (SLNil P)
    assume "[] = w@[\<alpha>]"
    hence False
      by simp
    thus "\<exists>v \<beta>. [] = v@[\<beta>] \<and> v \<in>SL* \<langle>P, w\<rangle> \<and> \<beta> \<in>SL \<langle>P, \<alpha>\<rangle>"
      by simp
  next
    case (SLCons v P w' \<beta> Q \<alpha>')
    assume "w'@[\<alpha>'] = w@[\<alpha>]"
    hence A1: "w' = w" and A2: "\<alpha>' = \<alpha>"
      by simp_all
    assume "v \<in>SL* \<langle>P, w'\<rangle>"
    with A1 have A3: "v \<in>SL* \<langle>P, w\<rangle>"
      by simp
    hence A4: "P \<in> ProcS"
      using lift_source_word_length(2)[of v P w]
      by simp
    assume "\<beta> \<in>SL \<langle>Q, \<alpha>'\<rangle>"
    with A2 A4 have "\<beta> \<in>SL \<langle>P, \<alpha>\<rangle>"
      unfolding getSourceLabel_def
      by simp
    with A3 show "\<exists>v' \<beta>'. v@[\<beta>] = v'@[\<beta>'] \<and> v' \<in>SL* \<langle>P, w\<rangle> \<and> \<beta>' \<in>SL \<langle>P, \<alpha>\<rangle>"
      by blast
  qed
qed

lemma lifted_composed_word_on_target_labels:
  fixes v' :: "'labT list"
    and P  :: "('procS, 'procT) Proc"
    and w  :: "('labS, 'labT) Lab list"
    and \<alpha>  :: "('labS, 'labT) Lab"
  assumes lifting: "v' \<in>TL* \<langle>P, (w@[\<alpha>])\<rangle>"
  shows "\<exists>v \<beta>. v' = v@[\<beta>] \<and> v \<in>TL* \<langle>P, w\<rangle> \<and> \<beta> \<in>TL \<langle>P, \<alpha>\<rangle>"
proof -
  define w' where w'_def: "w' = w@[\<alpha>]"
  with lifting have "v' \<in>TL* \<langle>P, w'\<rangle>"
    by simp
  from this w'_def show "\<exists>v \<beta>. v' = v@[\<beta>] \<and> v \<in>TL* \<langle>P, w\<rangle> \<and> \<beta> \<in>TL \<langle>P, \<alpha>\<rangle>"
  proof induct
    case (TLNil P)
    assume "[] = w@[\<alpha>]"
    hence False
      by simp
    thus "\<exists>v \<beta>. [] = v@[\<beta>] \<and> v \<in>TL* \<langle>P, w\<rangle> \<and> \<beta> \<in>TL \<langle>P, \<alpha>\<rangle>"
      by simp
  next
    case (TLCons v P w' \<beta> Q \<alpha>')
    assume "w'@[\<alpha>'] = w@[\<alpha>]"
    hence A1: "w' = w" and A2: "\<alpha>' = \<alpha>"
      by simp_all
    assume "v \<in>TL* \<langle>P, w'\<rangle>"
    with A1 have A3: "v \<in>TL* \<langle>P, w\<rangle>"
      by simp
    hence A4: "P \<in> ProcT"
      using lift_target_word_length(2)[of v P w]
      by simp
    assume "\<beta> \<in>TL \<langle>Q, \<alpha>'\<rangle>"
    with A2 A4 have "\<beta> \<in>TL \<langle>P, \<alpha>\<rangle>"
      unfolding getTargetLabel_def
      by simp
    with A3 show "\<exists>v' \<beta>'. v@[\<beta>] = v'@[\<beta>'] \<and> v' \<in>TL* \<langle>P, w\<rangle> \<and> \<beta>' \<in>TL \<langle>P, \<alpha>\<rangle>"
      by blast
  qed
qed

lemma lifted_word_on_source_labels_is_unique:
  fixes v1 v2 :: "'labS list"
    and P     :: "('procS, 'procT) Proc"
    and w     :: "('labS, 'labT) Lab list"
  assumes "v1 \<in>SL* \<langle>P, w\<rangle>"
      and "v2 \<in>SL* \<langle>P, w\<rangle>"
    shows "v1 = v2"
  using assms
proof (induct arbitrary: v2)
  case (SLNil P)
  assume "v2 \<in>SL* \<langle>P, []\<rangle>"
  thus "[] = v2"
    using lift_source_word_length(1)[of v2 P "[]"]
    by simp
next
  case (SLCons v P w \<beta> Q \<alpha>)
  assume "\<beta> \<in>SL \<langle>Q, \<alpha>\<rangle>" and "v2 \<in>SL* \<langle>P, (w@[\<alpha>])\<rangle>"
  then obtain v' where A1: "v2 = v'@[\<beta>]" and A2: "v' \<in>SL* \<langle>P, w\<rangle>"
    using lifted_composed_word_on_source_labels[of v2 P w \<alpha>]
    unfolding getSourceLabel_def
    by blast
  assume "\<And>v'. v' \<in>SL* \<langle>P, w\<rangle> \<Longrightarrow> v = v'"
  with A2 have "v = v'"
    by simp
  with A1 show "v@[\<beta>] = v2"
    by simp
qed

lemma lifted_word_on_target_labels_is_unique:
  fixes v1 v2 :: "'labT list"
    and P     :: "('procS, 'procT) Proc"
    and w     :: "('labS, 'labT) Lab list"
  assumes "v1 \<in>TL* \<langle>P, w\<rangle>"
      and "v2 \<in>TL* \<langle>P, w\<rangle>"
    shows "v1 = v2"
  using assms
proof (induct arbitrary: v2)
  case (TLNil P)
  assume "v2 \<in>TL* \<langle>P, []\<rangle>"
  thus "[] = v2"
    using lift_target_word_length(1)[of v2 P "[]"]
    by simp
next
  case (TLCons v P w \<beta> Q \<alpha>)
  assume "\<beta> \<in>TL \<langle>Q, \<alpha>\<rangle>" and "v2 \<in>TL* \<langle>P, (w@[\<alpha>])\<rangle>"
  then obtain v' where A1: "v2 = v'@[\<beta>]" and A2: "v' \<in>TL* \<langle>P, w\<rangle>"
    using lifted_composed_word_on_target_labels[of v2 P w \<alpha>]
    unfolding getTargetLabel_def
    by blast
  assume "\<And>v'. v' \<in>TL* \<langle>P, w\<rangle> \<Longrightarrow> v = v'"
  with A2 have "v = v'"
    by simp
  with A1 show "v@[\<beta>] = v2"
    by simp
qed

lemma lifted_word_is_either_source_or_target:
  fixes v1 :: "'labS list"
    and v2 :: "'labT list"
    and P  :: "('procS, 'procT) Proc"
    and w  :: "('labS, 'labT) Lab list"
  assumes v1: "v1 \<in>SL* \<langle>P, w\<rangle>"
      and v2: "v2 \<in>TL* \<langle>P, w\<rangle>"
    shows False
proof -
  from v1 have "P \<in> ProcS"
    using lift_source_word_length(2)[of v1 P w]
    by simp
  moreover from v2 have "P \<in> ProcT"
    using lift_target_word_length(2)[of v2 P w]
    by simp
  ultimately show False
    by blast
qed

lemma lifted_non_internal_word_is_either_source_or_target:
  fixes v1  :: "'labS list"
    and v2  :: "'labT list"
    and P Q :: "('procS, 'procT) Proc"
    and w   :: "('labS, 'labT) Lab list"
  assumes "v1 \<in>SL* \<langle>P, w\<rangle>"
      and "v2 \<in>TL* \<langle>Q, w\<rangle>"
      and "\<exists>\<alpha> \<in> set w. \<alpha> \<noteq> \<tau>-STLCal"
    shows False
  using assms
proof (induct arbitrary: v2 Q)
  case (SLNil P)
  assume "\<exists>\<alpha> \<in> set []. \<alpha> \<noteq> \<tau>-STLCal"
  thus False
    by simp
next
  case (SLCons v P w \<beta> Q' \<alpha> v2 Q)
  from SLCons(2) have IH: "\<And>v2 Q. v2 \<in>TL* \<langle>Q, w\<rangle> \<and> (\<exists>\<alpha> \<in> set w. \<alpha> \<noteq> \<tau>-STLCal) \<Longrightarrow> False"
    by blast
  assume A1: "\<beta> \<in>SL \<langle>Q', \<alpha>\<rangle>" and A2: "v2 \<in>TL* \<langle>Q, (w@[\<alpha>])\<rangle>"
     and A3: "\<exists>\<alpha> \<in> set (w@[\<alpha>]). \<alpha> \<noteq> \<tau>-STLCal"
  from A2 obtain v2' \<beta>' where A4: "v2' \<in>TL* \<langle>Q, w\<rangle>" and A5: "\<beta>' \<in>TL \<langle>Q, \<alpha>\<rangle>"
    using lifted_composed_word_on_target_labels[of v2 Q w \<alpha>]
    by blast
  show False
  proof (cases "\<alpha> = \<tau>-STLCal")
    assume "\<alpha> = \<tau>-STLCal"
    with A3 have "\<exists>\<alpha> \<in> set w. \<alpha> \<noteq> \<tau>-STLCal"
      by simp
    with IH A4 show False
      by simp
  next
    assume "\<alpha> \<noteq> \<tau>-STLCal"
    with A1 A5 show False
      unfolding getSourceLabel_def getTargetLabel_def
      by simp
  qed
qed

lemma lift_source_word_exchange:
  fixes w   :: "'labS list"
    and v   :: "('labS, 'labT) Lab list"
    and P Q :: "('procS, 'procT) Proc"
  assumes "w \<in>SL* \<langle>P, v\<rangle>"
      and "Q \<in> ProcS"
    shows "w \<in>SL* \<langle>Q, v\<rangle>"
  using assms
proof induct
  case (SLNil P)
  assume "Q \<in> ProcS"
  thus "[] \<in>SL* \<langle>Q, []\<rangle>"
    using getSourceLabels.SLNil[of Q]
    by simp
next
  case (SLCons v P w \<beta> P' \<alpha>)
  assume "Q \<in> ProcS \<Longrightarrow> v \<in>SL* \<langle>Q, w\<rangle>" and "Q \<in> ProcS"
  hence "v \<in>SL* \<langle>Q, w\<rangle>"
    by simp
  moreover assume "\<beta> \<in>SL \<langle>P', \<alpha>\<rangle>"
  ultimately show "(v@[\<beta>]) \<in>SL* \<langle>Q, (w@[\<alpha>])\<rangle>"
    using getSourceLabels.SLCons[of v Q w \<beta> P' \<alpha>]
    by simp
qed

lemma lift_target_word_exchange:
  fixes w   :: "'labT list"
    and v   :: "('labS, 'labT) Lab list"
    and P Q :: "('procS, 'procT) Proc"
  assumes "w \<in>TL* \<langle>P, v\<rangle>"
      and "Q \<in> ProcT"
    shows "w \<in>TL* \<langle>Q, v\<rangle>"
  using assms
proof induct
  case (TLNil P)
  assume "Q \<in> ProcT"
  thus "[] \<in>TL* \<langle>Q, []\<rangle>"
    using getTargetLabels.TLNil[of Q]
    by simp
next
  case (TLCons v P w \<beta> P' \<alpha>)
  assume "Q \<in> ProcT \<Longrightarrow> v \<in>TL* \<langle>Q, w\<rangle>" and "Q \<in> ProcT"
  hence "v \<in>TL* \<langle>Q, w\<rangle>"
    by simp
  moreover assume "\<beta> \<in>TL \<langle>P', \<alpha>\<rangle>"
  ultimately show "(v@[\<beta>]) \<in>TL* \<langle>Q, (w@[\<alpha>])\<rangle>"
    using getTargetLabels.TLCons[of v Q w \<beta> P' \<alpha>]
    by simp
qed

lemma STWeakLabelledSequence_weakLabelledSequence:
  fixes S  :: "'procS"
    and T  :: "'procT"
    and w  :: "('labS, 'labT) Lab list"
    and P' :: "('procS, 'procT) Proc"
  shows "SourceTerm S \<midarrow>\<frown>w\<rightarrow>ST* P' =
         (\<exists>v S'. v \<in>SL* \<langle>SourceTerm S, w\<rangle> \<and> S' \<in>S P' \<and> S \<midarrow>\<frown>v\<rightarrow>Source* S')"
    and "TargetTerm T \<midarrow>\<frown>w\<rightarrow>ST* P' =
         (\<exists>v T'. v \<in>TL* \<langle>TargetTerm T, w\<rangle> \<and> T' \<in>T P' \<and> T \<midarrow>\<frown>v\<rightarrow>Target* T')"
  by blast+

lemma STLCal_weakLabelledSequence:
  fixes S  :: "'procS"
    and T  :: "'procT"
    and w  :: "('labS, 'labT) Lab list"
    and P' :: "('procS, 'procT) Proc"
  shows "SourceTerm S \<midarrow>\<frown>w\<rightarrow>(STLCal Source Target)* P' =
         (\<exists>v S'. v \<in>SL* \<langle>SourceTerm S, w\<rangle> \<and> S' \<in>S P' \<and> S \<midarrow>\<frown>v\<rightarrow>Source* S')"
    and "TargetTerm T \<midarrow>\<frown>w\<rightarrow>(STLCal Source Target)* P' =
         (\<exists>v T'. v \<in>TL* \<langle>TargetTerm T, w\<rangle> \<and> T' \<in>T P' \<and> T \<midarrow>\<frown>v\<rightarrow>Target* T')"
proof auto
  define P :: "('procS, 'procT) Proc" where def_P:   "P = SourceTerm S"
  define Cal                          where def_Cal: "Cal = STLCal Source Target"
  assume "SourceTerm S \<midarrow>\<frown>w\<rightarrow>(STLCal Source Target)* P'"
  with def_P def_Cal have "P \<midarrow>\<frown>w\<rightarrow>Cal* P'"
    by simp
  from this def_P def_Cal
  show "\<exists>v. v \<in>SL* \<langle>SourceTerm S, w\<rangle> \<and> (\<exists>S'. S' \<in>S P' \<and> S \<midarrow>\<frown>v\<rightarrow>Source* S')"
  proof induct
    case (WLS_Nil P Cal P')
    have A1: "[] \<in>SL* \<langle>SourceTerm S, []\<rangle>"
      using SLNil
      by simp
    assume "P \<rightarrow>Cal* P'" and "S \<in>S P" and "Cal = STLCal Source Target"
    then obtain S' where A2: "S' \<in>S P'" and A3: "S \<rightarrow>Source* S'"
      using STLCal_weakTauSteps(1)[of S P']
      by blast
    from A3 have "S \<midarrow>\<frown>[]\<rightarrow>Source* S'"
      using weakLabelledSequence.WLS_Nil[of S Source S']
      by simp
    with A1 A2 show "\<exists>v. v \<in>SL* \<langle>SourceTerm S, []\<rangle> \<and> (\<exists>S'. S' \<in>S P' \<and> S \<midarrow>\<frown>v\<rightarrow>Source* S')"
      by blast
  next
    case (WLS_Cons P w Cal Q \<alpha> R)
    from WLS_Cons(2) have IH: "S \<in>S P \<and> Cal = STLCal Source Target \<Longrightarrow>
                               \<exists>v. v \<in>SL* \<langle>SourceTerm S, w\<rangle> \<and> (\<exists>S'. S' \<in>S Q \<and> S \<midarrow>\<frown>v\<rightarrow>Source* S')"
      by simp
    assume "S \<in>S P" and A1: "Cal = STLCal Source Target"
    with IH obtain v S' where A2: "v \<in>SL* \<langle>SourceTerm S, w\<rangle>" and A3: "S' \<in>S Q"
                          and A4: "S \<midarrow>\<frown>v\<rightarrow>Source* S'"
      by blast
    assume "Q \<midarrow>\<Zcat>\<alpha>\<rightarrow>Cal* R"
    with A1 A3 obtain \<beta> S'' where A5: "\<beta> \<in>SL \<langle>Q, \<alpha>\<rangle>" and A6: "S'' \<in>S R"
                              and A7: "S' \<midarrow>\<Zcat>\<beta>\<rightarrow>Source* S''"
      using STLCal_weakLabelledSteps(1)[of S' \<alpha> R]
      by blast
    from A2 A3 A5 have A8: "(v@[\<beta>]) \<in>SL* \<langle>SourceTerm S, (w@[\<alpha>])\<rangle>"
      using SLCons[of v "SourceTerm S" w \<beta> Q \<alpha>]
      by simp
    from A4 A7 have "S \<midarrow>\<frown>(v@[\<beta>])\<rightarrow>Source* S''"
      using weakLabelledSequence.WLS_Cons[of S v Source S' \<beta> S'']
      by simp
    with A6 A8
    show "\<exists>v'. v' \<in>SL* \<langle>SourceTerm S, (w@[\<alpha>])\<rangle> \<and> (\<exists>S''. S'' \<in>S R \<and> S \<midarrow>\<frown>v'\<rightarrow>Source* S'')"
      by blast
  qed
next
  fix v S'
  define Cal where def_Cal: "Cal = Source"
  assume A1: "v \<in>SL* \<langle>SourceTerm S, w\<rangle>" and A2: "S' \<in>S P'"
  assume "S \<midarrow>\<frown>v\<rightarrow>Source* S'"
  with def_Cal have "S \<midarrow>\<frown>v\<rightarrow>Cal* S'"
    by simp
  from this def_Cal A1 A2 show "SourceTerm S \<midarrow>\<frown>w\<rightarrow>(STLCal Source Target)* SourceTerm S'"
  proof (induct arbitrary: w P')
    case (WLS_Nil S Cal S')
    assume "[] \<in>SL* \<langle>SourceTerm S, w\<rangle>"
    hence B: "w = []"
      using lift_source_word_length(1)[of "[]" "SourceTerm S" w]
      by simp
    assume "S \<rightarrow>Cal* S'" and "Cal = Source"
    hence "SourceTerm S \<rightarrow>(STLCal Source Target)* SourceTerm S'"
      using STLCal_weakTauSteps(1)[of S "SourceTerm S'"]
      by simp
    with B show "SourceTerm S \<midarrow>\<frown>w\<rightarrow>(STLCal Source Target)* SourceTerm S'"
      using weakLabelledSequence.WLS_Nil[of "SourceTerm S" "STLCal Source Target" "SourceTerm S'"]
      by simp
  next
    case (WLS_Cons S v Cal S' \<beta> S'' w' P'')
    from WLS_Cons(2) have IH: "\<And>w P'. Cal = Source \<and> v \<in>SL* \<langle>SourceTerm S, w\<rangle> \<and> S' \<in>S P' \<Longrightarrow>
                               SourceTerm S \<midarrow>\<frown>w\<rightarrow>(STLCal Source Target)* SourceTerm S'"
      by simp
    assume "(v@[\<beta>]) \<in>SL* \<langle>SourceTerm S, w'\<rangle>"
    then obtain w \<alpha> where B1: "w' = w@[\<alpha>]" and B2: "v \<in>SL* \<langle>SourceTerm S, w\<rangle>"
                      and B3: "\<beta> \<in>SL \<langle>SourceTerm S, \<alpha>\<rangle>"
      using lift_composed_word_on_source_labels[of v \<beta> "SourceTerm S" w']
      by blast
    assume B4: "Cal = Source"
    with IH[of w "SourceTerm S'"] B2
    have B5: "SourceTerm S \<midarrow>\<frown>w\<rightarrow>(STLCal Source Target)* SourceTerm S'"
      by simp
    from B3 have B6: "\<beta> \<in>SL \<langle>SourceTerm S', \<alpha>\<rangle>"
      unfolding getSourceLabel_def
      by blast
    assume "S' \<midarrow>\<Zcat>\<beta>\<rightarrow>Cal* S''"
    with B4 B6 have "SourceTerm S' \<midarrow>\<Zcat>\<alpha>\<rightarrow>(STLCal Source Target)* SourceTerm S''"
      using STLCal_weakLabelledSteps(1)[of S' \<alpha> "SourceTerm S''"]
      by blast
    with B1 B5 show "SourceTerm S \<midarrow>\<frown>w'\<rightarrow>(STLCal Source Target)* SourceTerm S''"
      using weakLabelledSequence.WLS_Cons[of "SourceTerm S" w "STLCal Source Target"
              "SourceTerm S'" \<alpha> "SourceTerm S''"]
      by simp
  qed
next
  define P :: "('procS, 'procT) Proc" where def_P:   "P = TargetTerm T"
  define Cal                          where def_Cal: "Cal = STLCal Source Target"
  assume "TargetTerm T \<midarrow>\<frown>w\<rightarrow>(STLCal Source Target)* P'"
  with def_P def_Cal have "P \<midarrow>\<frown>w\<rightarrow>Cal* P'"
    by simp
  from this def_P def_Cal
  show "\<exists>v. v \<in>TL* \<langle>TargetTerm T, w\<rangle> \<and> (\<exists>T'. T' \<in>T P' \<and> T \<midarrow>\<frown>v\<rightarrow>Target* T')"
  proof induct
    case (WLS_Nil P Cal P')
    have A1: "[] \<in>TL* \<langle>TargetTerm T, []\<rangle>"
      using TLNil
      by simp
    assume "P \<rightarrow>Cal* P'" and "T \<in>T P" and "Cal = STLCal Source Target"
    then obtain T' where A2: "T' \<in>T P'" and A3: "T \<rightarrow>Target* T'"
      using STLCal_weakTauSteps(2)[of T P']
      by blast
    from A3 have "T \<midarrow>\<frown>[]\<rightarrow>Target* T'"
      using weakLabelledSequence.WLS_Nil[of T Target T']
      by simp
    with A1 A2 show "\<exists>v. v \<in>TL* \<langle>TargetTerm T, []\<rangle> \<and> (\<exists>T'. T' \<in>T P' \<and> T \<midarrow>\<frown>v\<rightarrow>Target* T')"
      by blast
  next
    case (WLS_Cons P w Cal Q \<alpha> R)
    from WLS_Cons(2) have IH: "T \<in>T P \<and> Cal = STLCal Source Target \<Longrightarrow>
                               \<exists>v. v \<in>TL* \<langle>TargetTerm T, w\<rangle> \<and> (\<exists>T'. T' \<in>T Q \<and> T \<midarrow>\<frown>v\<rightarrow>Target* T')"
      by simp
    assume "T \<in>T P" and A1: "Cal = STLCal Source Target"
    with IH obtain v T' where A2: "v \<in>TL* \<langle>TargetTerm T, w\<rangle>" and A3: "T' \<in>T Q"
                          and A4: "T \<midarrow>\<frown>v\<rightarrow>Target* T'"
      by blast
    assume "Q \<midarrow>\<Zcat>\<alpha>\<rightarrow>Cal* R"
    with A1 A3 obtain \<beta> T'' where A5: "\<beta> \<in>TL \<langle>Q, \<alpha>\<rangle>" and A6: "T'' \<in>T R"
                              and A7: "T' \<midarrow>\<Zcat>\<beta>\<rightarrow>Target* T''"
      using STLCal_weakLabelledSteps(2)[of T' \<alpha> R]
      by blast
    from A2 A5 have A8: "(v@[\<beta>]) \<in>TL* \<langle>TargetTerm T, (w@[\<alpha>])\<rangle>"
      using TLCons[of v "TargetTerm T" w \<beta> Q \<alpha>]
      by simp
    from A4 A7 have "T \<midarrow>\<frown>(v@[\<beta>])\<rightarrow>Target* T''"
      using weakLabelledSequence.WLS_Cons[of T v Target T' \<beta> T'']
      by simp
    with A6 A8
    show "\<exists>v'. v' \<in>TL* \<langle>TargetTerm T, (w@[\<alpha>])\<rangle> \<and> (\<exists>T''. T'' \<in>T R \<and> T \<midarrow>\<frown>v'\<rightarrow>Target* T'')"
      by blast
  qed
next
  fix v T'
  define Cal where def_Cal: "Cal = Target"
  assume A1: "v \<in>TL* \<langle>TargetTerm T, w\<rangle>" and A2: "T' \<in>T P'"
  assume "T \<midarrow>\<frown>v\<rightarrow>Target* T'"
  with def_Cal have "T \<midarrow>\<frown>v\<rightarrow>Cal* T'"
    by simp
  from this def_Cal A1 A2 show "TargetTerm T \<midarrow>\<frown>w\<rightarrow>(STLCal Source Target)* TargetTerm T'"
  proof (induct arbitrary: w P')
    case (WLS_Nil T Cal T')
    assume "[] \<in>TL* \<langle>TargetTerm T, w\<rangle>"
    hence B: "w = []"
      using lift_target_word_length(1)[of "[]" "TargetTerm T" w]
      by simp
    assume "T \<rightarrow>Cal* T'" and "Cal = Target"
    hence "TargetTerm T \<rightarrow>(STLCal Source Target)* TargetTerm T'"
      using STLCal_weakTauSteps(2)[of T "TargetTerm T'"]
      by simp
    with B show "TargetTerm T \<midarrow>\<frown>w\<rightarrow>(STLCal Source Target)* TargetTerm T'"
      using weakLabelledSequence.WLS_Nil[of "TargetTerm T" "STLCal Source Target" "TargetTerm T'"]
      by simp
  next
    case (WLS_Cons T v Cal T' \<beta> T'' w' P'')
    from WLS_Cons(2) have IH: "\<And>w P'. Cal = Target \<and> v \<in>TL* \<langle>TargetTerm T, w\<rangle> \<and> T' \<in>T P' \<Longrightarrow>
                               TargetTerm T \<midarrow>\<frown>w\<rightarrow>(STLCal Source Target)* TargetTerm T'"
      by simp
    assume "(v@[\<beta>]) \<in>TL* \<langle>TargetTerm T, w'\<rangle>"
    then obtain w P \<alpha> where B1: "w' = w@[\<alpha>]" and B2: "v \<in>TL* \<langle>TargetTerm T, w\<rangle>"
                        and B3: "\<beta> \<in>TL \<langle>P, \<alpha>\<rangle>"
      using lift_composed_word_on_target_labels[of v \<beta> "TargetTerm T" w']
      by blast
    assume B4: "Cal = Target"
    with IH[of w "TargetTerm T'"] B2
    have B5: "TargetTerm T \<midarrow>\<frown>w\<rightarrow>(STLCal Source Target)* TargetTerm T'"
      by simp
    from B3 have B6: "\<beta> \<in>TL \<langle>TargetTerm T', \<alpha>\<rangle>"
      unfolding getTargetLabel_def
      by blast
    assume "T' \<midarrow>\<Zcat>\<beta>\<rightarrow>Cal* T''"
    with B4 B6 have "TargetTerm T' \<midarrow>\<Zcat>\<alpha>\<rightarrow>(STLCal Source Target)* TargetTerm T''"
      using STLCal_weakLabelledSteps(2)[of T' \<alpha> "TargetTerm T''"]
      by blast
    with B1 B5 show "TargetTerm T \<midarrow>\<frown>w'\<rightarrow>(STLCal Source Target)* TargetTerm T''"
      using weakLabelledSequence.WLS_Cons[of "TargetTerm T" w "STLCal Source Target"
              "TargetTerm T'" \<alpha> "TargetTerm T''"]
      by simp
  qed
qed

lemma weakLabelledSequenceST_STLCal_weakLabelledSequence:
  fixes P P' :: "('procS, 'procT) Proc"
    and w    :: "('labS, 'labT) Lab list"
  shows "P \<midarrow>\<frown>w\<rightarrow>(STLCal Source Target)* P' = P \<midarrow>\<frown>w\<rightarrow>ST* P'"
proof (cases P)
  case (SourceTerm SP)
  assume "SP \<in>S P"
  thus "P \<midarrow>\<frown>w\<rightarrow>(STLCal Source Target)* P' = P \<midarrow>\<frown>w\<rightarrow>ST* P'"
    using STLCal_weakLabelledSequence(1)[of SP w P']
    by blast
next
  case (TargetTerm TP)
  assume "TP \<in>T P"
  thus "P \<midarrow>\<frown>w\<rightarrow>(STLCal Source Target)* P' = P \<midarrow>\<frown>w\<rightarrow>ST* P'"
    using STLCal_weakLabelledSequence(2)[of TP w P']
    by blast
qed

text \<open>To weak labelled steps on the same label imply the the corresponding processes are of the
      same kind, i.e., are all source terms or are all target terms.\<close>

lemma weakLabelledStepsST_on_same_label_are_on_same_kind_of_processes:
  fixes P P' Q Q' :: "('procS, 'procT) Proc"
    and \<alpha>         :: "('labS, 'labT) Lab"
  assumes "\<alpha> \<noteq> \<tau>-STLCal"
      and "P \<midarrow>\<Zcat>\<alpha>\<rightarrow>ST* P'"
      and "Q \<midarrow>\<Zcat>\<alpha>\<rightarrow>ST* Q'"
    shows "P \<sim>ST Q"
  using assms
  unfolding getSourceLabel_def getTargetLabel_def
  by blast

lemma weakLabelledSteps_on_same_label_are_on_same_kind_of_processes:
  fixes P P' Q Q' :: "('procS, 'procT) Proc"
    and \<alpha>         :: "('labS, 'labT) Lab"
  assumes "\<alpha> \<noteq> \<tau>-(STLCal Source Target)"
      and "P \<midarrow>\<Zcat>\<alpha>\<rightarrow>(STLCal Source Target)* P'"
      and "Q \<midarrow>\<Zcat>\<alpha>\<rightarrow>(STLCal Source Target)* Q'"
    shows "P \<sim>ST Q"
  using assms internalST_iff_internal weakLabelledStepsST_STLCal_weakLabelledSteps[of P \<alpha> P']
        weakLabelledStepsST_STLCal_weakLabelledSteps[of Q \<alpha> Q']
        weakLabelledStepsST_on_same_label_are_on_same_kind_of_processes[of \<alpha> P P' Q Q']
  by simp

text \<open>Similarly, two sequences of weak labelled steps on the same words have the same kind of
      processes.\<close>

lemma weakLabelledSequenceST_on_same_word_are_on_same_kind_of_processes:
  fixes P P' Q Q' :: "('procS, 'procT) Proc"
    and w         :: "('labS, 'labT) Lab list"
  assumes stepP: "P \<midarrow>\<frown>w\<rightarrow>ST* P'"
      and stepQ: "Q \<midarrow>\<frown>w\<rightarrow>ST* Q'"
      and word:  "\<exists>\<alpha> \<in> set w. \<alpha> \<noteq> \<tau>-STLCal"
    shows "P \<sim>ST Q"
  using assms
proof auto
  fix \<alpha> v1 S T v2 T' S'
  assume "\<alpha> \<in> set w" and "\<alpha> \<noteq> \<tau>-STLCal" and "v1 \<in>SL* \<langle>SourceTerm S', w\<rangle>"
     and "v2 \<in>TL* \<langle>TargetTerm T', w\<rangle>"
  thus False
    using lifted_non_internal_word_is_either_source_or_target[of v1 "SourceTerm S'" w v2
            "TargetTerm T'"]
    by blast
next
  fix \<alpha> T v2 T' v1 S S'
  assume "\<alpha> \<in> set w" and "\<alpha> \<noteq> \<tau>-STLCal" and "v1 \<in>SL* \<langle>SourceTerm S', w\<rangle>"
     and "v2 \<in>TL* \<langle>TargetTerm T', w\<rangle>"
  thus False
    using lifted_non_internal_word_is_either_source_or_target[of v1 "SourceTerm S'" w v2
            "TargetTerm T'"]
    by blast
qed

lemma weakLabelledSequence_on_same_word_are_on_same_kind_of_processes:
  fixes P P' Q Q' :: "('procS, 'procT) Proc"
    and w         :: "('labS, 'labT) Lab list"
  assumes "P \<midarrow>\<frown>w\<rightarrow>(STLCal Source Target)* P'"
      and "Q \<midarrow>\<frown>w\<rightarrow>(STLCal Source Target)* Q'"
      and "\<exists>\<alpha> \<in> set w. \<alpha> \<noteq> \<tau>-STLCal"
    shows "P \<sim>ST Q"
  using assms weakLabelledSequenceST_on_same_word_are_on_same_kind_of_processes[of P w P' Q Q']
        weakLabelledSequenceST_STLCal_weakLabelledSequence[of P w P']
        weakLabelledSequenceST_STLCal_weakLabelledSequence[of Q w Q']
  by simp

text \<open>In a weak labelled sequence the process at the beginning and the process at the end are of
      the same kind. Moreover, the word used in this sequence is of the same kind as the processes,
      i.e., consists of only source labels if the processes are source terms and else of only
      target labels.\<close>

lemma weakLabelledSequenceST_kinds:
  fixes P P' :: "('procS, 'procT) Proc"
    and w    :: "('labS, 'labT) Lab list"
  assumes "P \<midarrow>\<frown>w\<rightarrow>ST* P'"
  shows "P \<sim>ST P'"
    and "P \<sim>ST P'"
    and "P \<in> ProcS \<longrightarrow> (\<forall>\<alpha> \<in> set w. \<alpha> \<in> LabS \<or> \<alpha> = \<tau>-STLCal)"
    and "P \<in> ProcT \<longrightarrow> (\<forall>\<alpha> \<in> set w. \<alpha> \<in> LabT \<or> \<alpha> = \<tau>-STLCal)"
  using assms
proof (induct P)
  case (SourceTerm S)
  assume A1: "SourceTerm S \<midarrow>\<frown>w\<rightarrow>ST* P'"
  then obtain v S' where A2: "v \<in>SL* \<langle>SourceTerm S, w\<rangle>" and A3: "S' \<in>S P'"
    using STLCal_weakLabelledSequence(1)[of S w P']
    by blast
  from A3 show "SourceTerm S \<sim>ST P'"
    by simp
  from A3 show "SourceTerm S \<sim>ST P'"
    by simp
  from A1 A2 show "SourceTerm S \<in> ProcS \<longrightarrow> (\<forall>\<alpha> \<in> set w. \<alpha> \<in> LabS \<or> \<alpha> = \<tau>-STLCal)"
    using lifted_word_on_source_labels_kinds(1)[of v "SourceTerm S" w]
    by simp
  show "SourceTerm S \<in> ProcT \<longrightarrow> (\<forall>\<alpha> \<in> set w. \<alpha> \<in> LabT \<or> \<alpha> = \<tau>-STLCal)"
    by simp
next
  case (TargetTerm T)
  assume A1: "TargetTerm T \<midarrow>\<frown>w\<rightarrow>ST* P'"
  then obtain v T' where A2: "v \<in>TL* \<langle>TargetTerm T, w\<rangle>" and A3: "T' \<in>T P'"
    using STLCal_weakLabelledSequence(2)[of T w P']
    by blast
  from A3 show "TargetTerm T \<sim>ST P'"
    by simp
  from A3 show "TargetTerm T \<sim>ST P'"
    by simp
  show "TargetTerm T \<in> ProcS \<longrightarrow> (\<forall>\<alpha> \<in> set w. \<alpha> \<in> LabS \<or> \<alpha> = \<tau>-STLCal)"
    by simp
  from A1 A2 show "TargetTerm T \<in> ProcT \<longrightarrow> (\<forall>\<alpha> \<in> set w. \<alpha> \<in> LabT \<or> \<alpha> = \<tau>-STLCal)"
    using lifted_word_on_target_labels_kinds[of v "TargetTerm T" w]
    by simp
qed

text \<open>A divergent term of Proc is either a divergent source term or a divergent target term.\<close>

abbreviation divergentST :: "('procS, 'procT) Proc \<Rightarrow> bool" (\<open>_ \<rightarrow>ST\<omega>\<close> [70] 80) where
  "P \<rightarrow>ST\<omega> \<equiv> (\<exists>S. S \<in>S P \<and> S \<rightarrow>(Source)\<omega>) \<or> (\<exists>T. T \<in>T P \<and> T \<rightarrow>(Target)\<omega>)"

lemma STLCal_divergent:
  fixes S  :: "'procS"
    and T  :: "'procT"
  shows "SourceTerm S \<rightarrow>(STLCal Source Target)\<omega> = S \<rightarrow>(Source)\<omega>"
    and "TargetTerm T \<rightarrow>(STLCal Source Target)\<omega> = T \<rightarrow>(Target)\<omega>"
proof auto
  assume "SourceTerm S \<rightarrow>(STLCal Source Target)\<omega>"
  thus "S \<rightarrow>(Source)\<omega>"
    unfolding divergentLS_def
  proof auto
    fix S'
    assume "S \<rightarrow>Source* S'"
    hence "SourceTerm S \<rightarrow>(STLCal Source Target)* SourceTerm S'"
      using STLCal_weakTauSteps(1)[of S "SourceTerm S'"]
      by simp
    moreover assume "\<forall>P'. SourceTerm S \<rightarrow>(STLCal Source Target)* P' \<longrightarrow>
                     (\<exists>P''. P' \<midarrow>\<tau>-(STLCal Source Target)\<rightarrow>(STLCal Source Target) P'')"
    ultimately obtain P'' where "SourceTerm S' \<midarrow>\<tau>-STLCal\<rightarrow>(STLCal Source Target) P''"
      using internalST_iff_internal
      by auto
    thus "\<exists>S''. S' \<midarrow>\<tau>-Source\<rightarrow>Source S''"
      using STLCal_labelledStep(1)[of S' "\<tau>-STLCal" P'']
      unfolding getSourceLabel_def
      by blast
  qed
next
  assume "S \<rightarrow>(Source)\<omega>"
  thus "SourceTerm S \<rightarrow>(STLCal Source Target)\<omega>"
    unfolding divergentLS_def
  proof auto
    fix P'
    assume "SourceTerm S \<rightarrow>(STLCal Source Target)* P'"
    then obtain S' where A1: "S' \<in>S P'" and A2: "S \<rightarrow>Source* S'"
      using STLCal_weakTauSteps(1)[of S P']
      by blast
    assume "\<forall>S'. S \<rightarrow>Source* S' \<longrightarrow> (\<exists>S''. S' \<midarrow>\<tau>-Source\<rightarrow>Source S'')"
    with A2 obtain S'' where "S' \<midarrow>\<tau>-Source\<rightarrow>Source S''"
      by blast
    with A1 show "\<exists>P''. P' \<midarrow>\<tau>-(STLCal Source Target)\<rightarrow>(STLCal Source Target) P''"
      using STLCal_labelledStep(1)[of S' "\<tau>-STLCal" "SourceTerm S''"] internalST_iff_internal
      unfolding getSourceLabel_def
      by auto
  qed
next
  assume "TargetTerm T \<rightarrow>(STLCal Source Target)\<omega>"
  thus "T \<rightarrow>(Target)\<omega>"
    unfolding divergentLS_def
  proof auto
    fix T'
    assume "T \<rightarrow>Target* T'"
    hence "TargetTerm T \<rightarrow>(STLCal Source Target)* TargetTerm T'"
      using STLCal_weakTauSteps(2)[of T "TargetTerm T'"]
      by simp
    moreover assume "\<forall>P'. TargetTerm T \<rightarrow>(STLCal Source Target)* P' \<longrightarrow>
                     (\<exists>P''. P' \<midarrow>\<tau>-(STLCal Source Target)\<rightarrow>(STLCal Source Target) P'')"
    ultimately obtain P'' where "TargetTerm T' \<midarrow>\<tau>-STLCal\<rightarrow>(STLCal Source Target) P''"
      using internalST_iff_internal
      by auto
    thus "\<exists>T''. T' \<midarrow>\<tau>-Target\<rightarrow>Target T''"
      using STLCal_labelledStep(2)[of T' "\<tau>-STLCal" P'']
      unfolding getTargetLabel_def
      by blast
  qed
next
  assume "T \<rightarrow>(Target)\<omega>"
  thus "TargetTerm T \<rightarrow>(STLCal Source Target)\<omega>"
    unfolding divergentLS_def
  proof auto
    fix P'
    assume "TargetTerm T \<rightarrow>(STLCal Source Target)* P'"
    then obtain T' where A1: "T' \<in>T P'" and A2: "T \<rightarrow>Target* T'"
      using STLCal_weakTauSteps(2)[of T P']
      by blast
    assume "\<forall>T'. T \<rightarrow>Target* T' \<longrightarrow> (\<exists>T''. T' \<midarrow>\<tau>-Target\<rightarrow>Target T'')"
    with A2 obtain T'' where "T' \<midarrow>\<tau>-Target\<rightarrow>Target T''"
      by blast
    with A1 show "\<exists>P''. P' \<midarrow>\<tau>-(STLCal Source Target)\<rightarrow>(STLCal Source Target) P''"
      using STLCal_labelledStep(2)[of T' "\<tau>-STLCal" "TargetTerm T''"] internalST_iff_internal
      unfolding getTargetLabel_def
      by auto
  qed
qed

lemma divergentST_STCal_divergent:
  fixes P :: "('procS, 'procT) Proc"
  shows "P \<rightarrow>(STLCal Source Target)\<omega> = P \<rightarrow>ST\<omega>"
proof (cases P)
  case (SourceTerm SP)
  assume "SP \<in>S P"
  thus "P \<rightarrow>(STLCal Source Target)\<omega> = P \<rightarrow>ST\<omega>"
    using STLCal_divergent(1)
    by simp
next
  case (TargetTerm TP)
  assume "TP \<in>T P"
  thus "P \<rightarrow>(STLCal Source Target)\<omega> = P \<rightarrow>ST\<omega>"
    using STLCal_divergent(2)
    by simp
qed

end

subsection \<open>An encoding function considering labelled semantics and a translation of labels.\<close>

text \<open>ToDo: By using a single fresh internal label in the labelled calculus on the disjoint union of the
      source and target language and moreover by the implementation of weak steps, we implicitly
      already add a requirement on the translation of internal labels. It is not yet visible, but
      since we will use these definitions of weak steps in the two weaker versions of operational
      correspondence, we indeed implicitly assume that internal steps of the source are translated
      to internal steps on the target. Similarly, this implicit assumption is present also for the
      criterion on divergence reflection. However, there is not yet any implicit requirement on the
      translation of label for cases without weak steps as e.g. the later defined strong version of
      operational correspondence. More precisely, so far we only require that internal source term
      steps are translated into internal target term steps but only for the later considered
      criteria using weak notions of steps. We did not yet pose any requirement on the translation
      of arbitrary labels. We will however need such a requirement for some of our results.
      Therefore, we extend our notion of encoding on labelled semantics by an additional encoding
      function on labels. In order to allow for more flexibility, we allow the translation of
      labels to consider as input not only a source term label but actually the whole source term
      steps, by having also two source terms as inputs.\<close>

locale encodingLS_encL =
  encodingLS Enc Source Target
    for Source :: "('procS, 'labS) labelledProcessCalculus"
    and Target :: "('procT, 'labT) labelledProcessCalculus"
    and Enc    :: "'procS \<Rightarrow> 'procT" +
  fixes EncL :: "'labS \<Rightarrow> 'labT"
begin

abbreviation encL :: "'labS \<Rightarrow> 'labT" (\<open>\<lblot>_\<rblot>\<close> [65] 70) where
  "\<lblot>\<alpha>\<rblot> \<equiv> EncL \<alpha>"

definition encLST
  :: "('procS, 'procT) Proc \<Rightarrow> ('labS, 'labT) Lab \<Rightarrow> ('procS, 'procT) Proc \<Rightarrow> ('labS, 'labT) Lab \<Rightarrow>
      bool" (\<open>\<lparr>_, _\<rparr>\<mapsto>\<langle>_, _\<rangle>\<close> [65, 65, 65, 65] 70) where
  "\<lparr>P, \<alpha>\<rparr>\<mapsto>\<langle>Q, \<beta>\<rangle> \<equiv> (\<exists>\<alpha>' \<beta>'. \<alpha>' \<in>SL \<langle>P, \<alpha>\<rangle> \<and> \<beta>' \<in>TL \<langle>Q, \<beta>\<rangle> \<and> \<lblot>\<alpha>'\<rblot> = \<beta>')"

inductive encLST_list
  :: "('procS, 'procT) Proc \<Rightarrow> ('labS, 'labT) Lab list \<Rightarrow> ('procS, 'procT) Proc \<Rightarrow>
      ('labS, 'labT) Lab list \<Rightarrow> bool" (\<open>\<lparr>_, _\<rparr>\<mapsto>*\<langle>_, _\<rangle>\<close> [65, 65, 65, 65] 70) where
  ELNil:  "\<lbrakk>P \<in> ProcS; Q \<in> ProcT\<rbrakk> \<Longrightarrow> \<lparr>P, []\<rparr>\<mapsto>*\<langle>Q, []\<rangle>"
| ELCons: "\<lbrakk>\<lparr>P, w\<rparr>\<mapsto>*\<langle>Q, v\<rangle>; \<lparr>P', \<alpha>\<rparr>\<mapsto>\<langle>Q', \<beta>\<rangle>\<rbrakk> \<Longrightarrow> \<lparr>P, w@[\<alpha>]\<rparr>\<mapsto>*\<langle>Q, v@[\<beta>]\<rangle>"

text \<open>In the translation of a word the considered word is of source labels and the resulting word
      is a word on target term labels.\<close>

lemma kinds_of_encoded_label:
  fixes P Q :: "('procS, 'procT) Proc"
    and \<alpha> \<beta> :: "('labS, 'labT) Lab"
  assumes "\<lparr>P, \<alpha>\<rparr>\<mapsto>\<langle>Q, \<beta>\<rangle>"
  shows "P \<in> ProcS"
    and "\<alpha> \<in> LabS \<or> \<alpha> = \<tau>-STLCal"
    and "Q \<in> ProcT"
    and "\<beta> \<in> LabT \<or> \<beta> = \<tau>-STLCal"
  using assms
  unfolding encLST_def isSourceLabel_def getSourceLabel_def isTargetLabel_def getTargetLabel_def
  by blast+

lemma kinds_of_encoded_word:
  fixes P Q :: "('procS, 'procT) Proc"
    and w v :: "('labS, 'labT) Lab list"
  assumes "\<lparr>P, w\<rparr>\<mapsto>*\<langle>Q, v\<rangle>"
  shows "P \<in> ProcS"
    and "\<forall>\<alpha> \<in> set w. \<alpha> \<in> LabS \<or> \<alpha> = \<tau>-STLCal"
    and "Q \<in> ProcT"
    and "\<forall>\<beta> \<in> set v. \<beta> \<in> LabT \<or> \<beta> = \<tau>-STLCal"
  using assms
proof induct
  case (ELNil P Q)
  assume "P \<in> ProcS"
  thus "P \<in> ProcS" .
  show "\<forall>\<alpha> \<in> set []. \<alpha> \<in> LabS \<or> \<alpha> = \<tau>-STLCal"
    by simp
  assume "Q \<in> ProcT"
  thus "Q \<in> ProcT" .
  show "\<forall>\<beta> \<in> set []. \<beta> \<in> LabT \<or> \<beta> = \<tau>-STLCal"
    by simp
next
  case (ELCons P w Q v P' \<alpha> Q' \<beta>)
  assume "P \<in> ProcS"
  thus "P \<in> ProcS" .
  assume "\<lparr>P', \<alpha>\<rparr>\<mapsto>\<langle>Q', \<beta>\<rangle>"
  hence A1: "\<alpha> \<in> LabS \<or> \<alpha> = \<tau>-STLCal" and A2: "\<beta> \<in> LabT \<or> \<beta> = \<tau>-STLCal"
    unfolding encLST_def isSourceLabel_def getSourceLabel_def isTargetLabel_def getTargetLabel_def
    by blast+
  assume "\<forall>\<alpha> \<in> set w. \<alpha> \<in> LabS \<or> \<alpha> = \<tau>-STLCal"
  with A1 show "\<forall>\<alpha> \<in> set (w@[\<alpha>]). \<alpha> \<in> LabS \<or> \<alpha> = \<tau>-STLCal"
    by simp
  assume "Q \<in> ProcT"
  thus "Q \<in> ProcT" .
  assume "\<forall>\<beta> \<in> set v. \<beta> \<in> LabT \<or> \<beta> = \<tau>-STLCal"
  with A2 show "\<forall>\<beta> \<in> set (v@[\<beta>]). \<beta> \<in> LabT \<or> \<beta> = \<tau>-STLCal"
    by simp
qed

text \<open>What matters about the process in the notation of encoded words is only its kind.\<close>

lemma encoded_label_exchange_processes:
  fixes P Q :: "('procS, 'procT) Proc"
    and \<alpha> \<beta> :: "('labS, 'labT) Lab"
  assumes "\<lparr>P, \<alpha>\<rparr>\<mapsto>\<langle>Q, \<beta>\<rangle>"
      and "P' \<in> ProcS"
      and "Q' \<in> ProcT"
    shows "\<lparr>P', \<alpha>\<rparr>\<mapsto>\<langle>Q', \<beta>\<rangle>"
  using assms
  unfolding encLST_def getSourceLabel_def getTargetLabel_def
  by blast

lemma encoded_word_exchange_processes:
  fixes P Q :: "('procS, 'procT) Proc"
    and w v :: "('labS, 'labT) Lab list"
  assumes "\<lparr>P, w\<rparr>\<mapsto>*\<langle>Q, v\<rangle>"
      and "P' \<in> ProcS"
      and "Q' \<in> ProcT"
    shows "\<lparr>P', w\<rparr>\<mapsto>*\<langle>Q', v\<rangle>"
  using assms
proof induct
  case (ELNil P Q)
  assume "P' \<in> ProcS" and  "Q' \<in> ProcT"
  thus "\<lparr>P', []\<rparr>\<mapsto>*\<langle>Q', []\<rangle>"
    using encLST_list.ELNil[of P' Q']
    by simp
next
  case (ELCons P w Q v P'' \<alpha> Q'' \<beta>)
  from ELCons(2) have IH: "P' \<in> ProcS \<and> Q' \<in> ProcT \<Longrightarrow> \<lparr>P', w\<rparr>\<mapsto>*\<langle>Q', v\<rangle>"
    by simp
  assume "P' \<in> ProcS" "Q' \<in> ProcT"
  with IH have "\<lparr>P', w\<rparr>\<mapsto>*\<langle>Q', v\<rangle>"
    by simp
  moreover assume "\<lparr>P'', \<alpha>\<rparr>\<mapsto>\<langle>Q'', \<beta>\<rangle>"
  ultimately show "\<lparr>P', w@[\<alpha>]\<rparr>\<mapsto>*\<langle>Q', v@[\<beta>]\<rangle>"
    using encLST_list.ELCons[of P' w Q' v P'' \<alpha> Q'' \<beta>]
    by simp
qed

text \<open>The encoded word and the original word have the same length.\<close>

lemma encoded_word_length:
  fixes P Q :: "('procS, 'procT) Proc"
    and w v :: "('labS, 'labT) Lab list"
  assumes "\<lparr>P, w\<rparr>\<mapsto>*\<langle>Q, v\<rangle>"
  shows "length v = length w"
  using assms
  by (induct, simp_all)

text \<open>The encoding of a composed word results in a composed word.\<close>

lemma encoded_word_decompose:
  fixes P Q :: "('procS, 'procT) Proc"
    and w v :: "('labS, 'labT) Lab list"
  assumes "\<lparr>P, w\<rparr>\<mapsto>*\<langle>Q, v\<rangle>"
  shows "w = [] \<or> (\<exists>w' \<alpha> v' \<beta> P' Q'. w = w'@[\<alpha>] \<and> v = v'@[\<beta>] \<and> \<lparr>P, w'\<rparr>\<mapsto>*\<langle>Q, v'\<rangle> \<and>
                   \<lparr>P', \<alpha>\<rparr>\<mapsto>\<langle>Q', \<beta>\<rangle> \<and> P' \<in> ProcS \<and> Q' \<in> ProcT)"
  using assms
proof induct
  case (ELNil P Q)
  show "[] = [] \<or> (\<exists>w' \<alpha> v' \<beta> P' Q'. [] = w'@[\<alpha>] \<and> [] = v'@[\<beta>] \<and> \<lparr>P, w'\<rparr>\<mapsto>*\<langle>Q, v'\<rangle> \<and>
                   \<lparr>P', \<alpha>\<rparr>\<mapsto>\<langle>Q', \<beta>\<rangle> \<and> P' \<in> ProcS \<and> Q' \<in> ProcT)"
    by simp
next
  case (ELCons P w Q v P' \<alpha> Q' \<beta>)
  assume "\<lparr>P, w\<rparr>\<mapsto>*\<langle>Q, v\<rangle>" and A: "\<lparr>P', \<alpha>\<rparr>\<mapsto>\<langle>Q', \<beta>\<rangle>"
  moreover from A have "P' \<in> ProcS" and "Q' \<in> ProcT"
    using kinds_of_encoded_label(1, 3)[of P' \<alpha> Q' \<beta>]
    by simp_all
  ultimately
  show "w@[\<alpha>] = [] \<or> (\<exists>w' \<alpha>' v' \<beta>' P' Q'. w@[\<alpha>] = w'@[\<alpha>'] \<and> v@[\<beta>] = v'@[\<beta>'] \<and> \<lparr>P, w'\<rparr>\<mapsto>*\<langle>Q, v'\<rangle> \<and>
                      \<lparr>P', \<alpha>'\<rparr>\<mapsto>\<langle>Q', \<beta>'\<rangle> \<and> P' \<in> ProcS \<and> Q' \<in> ProcT)"
    by auto
qed

text \<open>The encoding of a word is unambiguous. If the label encoding is injective we also obtain that
      the source label/word of an encoded label/word is unique.\<close>

lemma encoded_label_unique:
  fixes P Q R :: "('procS, 'procT) Proc"
    and \<alpha> \<beta> \<gamma> :: "('labS, 'labT) Lab"
  assumes "\<lparr>P, \<alpha>\<rparr>\<mapsto>\<langle>Q, \<beta>\<rangle>"
      and "\<lparr>P, \<alpha>\<rparr>\<mapsto>\<langle>R, \<gamma>\<rangle>"
    shows "\<beta> = \<gamma>"
  using assms
  unfolding encLST_def getSourceLabel_def getTargetLabel_def
  by blast

lemma encoded_word_unique:
  fixes P Q R :: "('procS, 'procT) Proc"
    and w v y :: "('labS, 'labT) Lab list"
  assumes "\<lparr>P, w\<rparr>\<mapsto>*\<langle>Q, v\<rangle>"
      and "\<lparr>P, w\<rparr>\<mapsto>*\<langle>R, y\<rangle>"
    shows "v = y"
  using assms
proof (induct arbitrary: y)
  case (ELNil P Q)
  assume "\<lparr>P, []\<rparr>\<mapsto>*\<langle>R, y\<rangle>"
  thus "[] = y"
    using encoded_word_length[of P "[]" R y]
    by simp
next
  case (ELCons P w Q v P' \<alpha> Q' \<beta>)
  assume "\<lparr>P, w@[\<alpha>]\<rparr>\<mapsto>*\<langle>R, y\<rangle>"
  then obtain y' \<gamma> P'' R' where A1: "y = y'@[\<gamma>]" and A2: "\<lparr>P, w\<rparr>\<mapsto>*\<langle>R, y'\<rangle>"
                            and A3: "\<lparr>P'', \<alpha>\<rparr>\<mapsto>\<langle>R', \<gamma>\<rangle>"
    using encoded_word_decompose[of P "w@[\<alpha>]" R y]
    by auto
  assume "\<And>y. \<lparr>P, w\<rparr>\<mapsto>*\<langle>R, y\<rangle> \<Longrightarrow> v = y"
  with A2 have A4: "v = y'"
    by simp
  assume "\<lparr>P', \<alpha>\<rparr>\<mapsto>\<langle>Q', \<beta>\<rangle>"
  with A3 have "\<lparr>P'', \<alpha>\<rparr>\<mapsto>\<langle>Q', \<beta>\<rangle>"
    unfolding encLST_def getSourceLabel_def
    by simp
  with A3 have "\<beta> = \<gamma>"
    using encoded_label_unique[of P'' \<alpha> R' \<gamma> Q' \<beta>]
    by simp
  with A1 A4 show "v@[\<beta>] = y"
    by simp
qed

lemma encoded_label_unique_rev:
  fixes P Q R :: "('procS, 'procT) Proc"
    and \<alpha> \<beta> \<gamma> :: "('labS, 'labT) Lab"
  assumes "\<lparr>P, \<alpha>\<rparr>\<mapsto>\<langle>R, \<gamma>\<rangle>"
      and "\<lparr>Q, \<beta>\<rparr>\<mapsto>\<langle>R, \<gamma>\<rangle>"
      and "inj encL"
    shows "\<alpha> = \<beta>"
  using assms
  unfolding inj_def encLST_def getSourceLabel_def getTargetLabel_def
  by auto

lemma encoded_word_unique_rev:
  fixes P Q R :: "('procS, 'procT) Proc"
    and w v y :: "('labS, 'labT) Lab list"
  assumes "\<lparr>P, w\<rparr>\<mapsto>*\<langle>R, y\<rangle>"
      and "\<lparr>Q, v\<rparr>\<mapsto>*\<langle>R, y\<rangle>"
      and "inj encL"
    shows "w = v"
  using assms
proof (induct arbitrary: v)
  case (ELNil P R)
  assume "\<lparr>Q, v\<rparr>\<mapsto>*\<langle>R, []\<rangle>"
  thus "[] = v"
    using encoded_word_length[of Q v R "[]"]
    by simp
next
  case (ELCons P w R y P' \<alpha> R' \<gamma>)
  assume A1: "\<lparr>Q, v\<rparr>\<mapsto>*\<langle>R, y@[\<gamma>]\<rangle>"
  hence "v \<noteq> []"
    using encoded_word_length[of Q v R "y@[\<gamma>]"]
    by auto
  with A1 obtain v' \<beta> Q' R'' where A2: "v = v'@[\<beta>]" and A3: "\<lparr>Q, v'\<rparr>\<mapsto>*\<langle>R, y\<rangle>"
                               and A4: "\<lparr>Q', \<beta>\<rparr>\<mapsto>\<langle>R'', \<gamma>\<rangle>"
    using encoded_word_decompose[of Q v R "y@[\<gamma>]"]
    by auto
  from ELCons(2) have IH: "\<And>v. \<lparr>Q, v\<rparr>\<mapsto>*\<langle>R, y\<rangle> \<and> inj encL \<Longrightarrow> w = v"
    by simp
  assume A5: "inj encL"
  with A2 A3 IH have A6: "w = v'"
    by simp
  assume A7: "\<lparr>P', \<alpha>\<rparr>\<mapsto>\<langle>R', \<gamma>\<rangle>"
  hence "R' \<in> ProcT"
    using kinds_of_encoded_label(3)[of P' \<alpha> R' \<gamma>]
    by simp
  with A2 A4 have "\<lparr>Q', \<beta>\<rparr>\<mapsto>\<langle>R', \<gamma>\<rangle>"
    using encoded_label_exchange_processes[of Q' \<beta> R'' \<gamma> Q' R']
          kinds_of_encoded_label(1)[of Q' \<beta> R'' \<gamma>]
    by simp
  with A5 A7 have "\<beta> = \<alpha>"
    using encoded_label_unique_rev[of Q' \<beta> R' \<gamma> P' \<alpha>]
    by simp
  with A2 A6 show "w@[\<alpha>] = v"
    by simp
qed

text \<open>We have to consider three cases of pairs of labelled steps in the calculus on the disjoint
      union of the source and target with related labels:
      (1) The two steps are of the same kind, i.e., both are source or both are target term steps.
          In this case (but only this case) the two steps might actually use the same label.
      (2) A source term step on a label and a target term step on the label that results from
          translating the label of the source term step.
      (3) A target term step on a label that results from the translation of a source term step and
          the corresponding source term step.
      In all other cases we consider the labels as unrelated. The described relation of labels is
      relevant for the definition of behavioural relations that are respecting the encoding of
      labels as defined later. The processes in the cases of labels are necessary to clearly
      distinguish, whether two internal labels in the disjoint union are actually the same or
      result from a source internal and a target internal that should rather be compared by the
      label encoding. For words we do not need that, since we do not consider the internals in the
      words.\<close>

definition related_labels
  :: "('procS, 'procT) Proc \<Rightarrow> ('labS, 'labT) Lab \<Rightarrow> ('procS, 'procT) Proc \<Rightarrow> ('labS, 'labT) Lab \<Rightarrow>
      bool" (\<open>\<langle>_, _\<rangle> \<equiv>\<lparr>\<rparr> \<langle>_, _\<rangle>\<close> [65, 65, 65, 65] 70) where
  "\<langle>P, \<alpha>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>Q, \<beta>\<rangle> \<equiv> \<alpha> = \<beta> \<and> P \<sim>ST Q \<or> \<lparr>P, \<alpha>\<rparr>\<mapsto>\<langle>Q, \<beta>\<rangle> \<or> \<lparr>Q, \<beta>\<rparr>\<mapsto>\<langle>P, \<alpha>\<rangle>"

definition related_words
  :: "('procS, 'procT) Proc \<Rightarrow> ('labS, 'labT) Lab list \<Rightarrow> ('procS, 'procT) Proc \<Rightarrow>
      ('labS, 'labT) Lab list \<Rightarrow> bool" (\<open>\<langle>_, _\<rangle> \<equiv>\<lparr>\<rparr>* \<langle>_, _\<rangle>\<close> [65, 65, 65, 65] 70) where
  "\<langle>P, w\<rangle> \<equiv>\<lparr>\<rparr>* \<langle>Q, v\<rangle> \<equiv> w = v \<and> P \<sim>ST Q \<or> \<lparr>P, w\<rparr>\<mapsto>*\<langle>Q, v\<rangle> \<or> \<lparr>Q, v\<rparr>\<mapsto>*\<langle>P, w\<rangle>"

text \<open>We prove that the three parts of the condition for related labels are mutual exclusive.\<close>

lemma related_labels_conditions_mutual_exclusive:
  fixes P Q :: "('procS, 'procT) Proc"
    and \<alpha> \<beta> :: "('labS, 'labT) Lab"
  shows "\<alpha> = \<beta> \<and> P \<sim>ST Q \<Longrightarrow> \<not>\<lparr>P, \<alpha>\<rparr>\<mapsto>\<langle>Q, \<beta>\<rangle>"
    and "\<alpha> = \<beta> \<and> P \<sim>ST Q \<Longrightarrow> \<not>\<lparr>Q, \<beta>\<rparr>\<mapsto>\<langle>P, \<alpha>\<rangle>"
    and "\<lparr>P, \<alpha>\<rparr>\<mapsto>\<langle>Q, \<beta>\<rangle> \<Longrightarrow> \<not>(\<alpha> = \<beta> \<and> P \<sim>ST Q)"
    and "\<lparr>P, \<alpha>\<rparr>\<mapsto>\<langle>Q, \<beta>\<rangle> \<Longrightarrow> \<not>\<lparr>Q, \<beta>\<rparr>\<mapsto>\<langle>P, \<alpha>\<rangle>"
    and "\<lparr>Q, \<beta>\<rparr>\<mapsto>\<langle>P, \<alpha>\<rangle> \<Longrightarrow> \<not>(\<alpha> = \<beta> \<and> P \<sim>ST Q)"
    and "\<lparr>Q, \<beta>\<rparr>\<mapsto>\<langle>P, \<alpha>\<rangle> \<Longrightarrow> \<not>\<lparr>P, \<alpha>\<rparr>\<mapsto>\<langle>Q, \<beta>\<rangle>"
  unfolding encLST_def getSourceLabel_def getTargetLabel_def
  by blast+

lemma related_words_conditions_mutual_exclusive:
  fixes P Q :: "('procS, 'procT) Proc"
    and w v :: "('labS, 'labT) Lab list"
  shows "w = v \<and> P \<sim>ST Q \<Longrightarrow> \<not>\<lparr>P, w\<rparr>\<mapsto>*\<langle>Q, v\<rangle>"
    and "w = v \<and> P \<sim>ST Q \<Longrightarrow> \<not>\<lparr>Q, v\<rparr>\<mapsto>*\<langle>P, w\<rangle>"
    and "\<lparr>P, w\<rparr>\<mapsto>*\<langle>Q, v\<rangle> \<Longrightarrow> \<not>(w = v \<and> P \<sim>ST Q)"
    and "\<lparr>P, w\<rparr>\<mapsto>*\<langle>Q, v\<rangle> \<Longrightarrow> \<not>\<lparr>Q, v\<rparr>\<mapsto>*\<langle>P, w\<rangle>"
    and "\<lparr>Q, v\<rparr>\<mapsto>*\<langle>P, w\<rangle> \<Longrightarrow> \<not>(w = v \<and> P \<sim>ST Q)"
    and "\<lparr>Q, v\<rparr>\<mapsto>*\<langle>P, w\<rangle> \<Longrightarrow> \<not>\<lparr>P, w\<rparr>\<mapsto>*\<langle>Q, v\<rangle>"
proof -
  assume "w = v \<and> P \<sim>ST Q"
  thus "\<not>\<lparr>P, w\<rparr>\<mapsto>*\<langle>Q, v\<rangle>"
    using kinds_of_encoded_word(1,3)[of P w Q v]
    by blast
next
  assume "w = v \<and> P \<sim>ST Q"
  thus "\<not>\<lparr>Q, v\<rparr>\<mapsto>*\<langle>P, w\<rangle>"
    using kinds_of_encoded_word(1,3)[of Q v P w]
    by blast
next
  assume "\<lparr>P, w\<rparr>\<mapsto>*\<langle>Q, v\<rangle>"
  thus "\<not>(w = v \<and> P \<sim>ST Q)"
    using kinds_of_encoded_word(1,3)[of P w Q v]
    by blast
next
  assume "\<lparr>P, w\<rparr>\<mapsto>*\<langle>Q, v\<rangle>"
  thus "\<not>\<lparr>Q, v\<rparr>\<mapsto>*\<langle>P, w\<rangle>"
    using kinds_of_encoded_word(1,3)[of P w Q v] kinds_of_encoded_word(1,3)[of Q v P w]
    by blast
next
  assume "\<lparr>Q, v\<rparr>\<mapsto>*\<langle>P, w\<rangle>"
  thus "\<not>(w = v \<and> P \<sim>ST Q)"
    using kinds_of_encoded_word(1,3)[of Q v P w]
    by blast
next
  assume "\<lparr>Q, v\<rparr>\<mapsto>*\<langle>P, w\<rangle>"
  thus "\<not>\<lparr>P, w\<rparr>\<mapsto>*\<langle>Q, v\<rangle>"
    using kinds_of_encoded_word(1,3)[of P w Q v] kinds_of_encoded_word(1,3)[of Q v P w]
    by blast
qed

lemma related_labels_get_condition:
  fixes P Q :: "('procS, 'procT) Proc"
    and \<alpha> \<beta> :: "('labS, 'labT) Lab"
  assumes "\<langle>P, \<alpha>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>Q, \<beta>\<rangle>"
  shows "\<lbrakk>\<not>\<lparr>P, \<alpha>\<rparr>\<mapsto>\<langle>Q, \<beta>\<rangle>; \<not>\<lparr>Q, \<beta>\<rparr>\<mapsto>\<langle>P, \<alpha>\<rangle>\<rbrakk> \<Longrightarrow> \<alpha> = \<beta> \<and> P \<sim>ST Q"
    and "\<lbrakk>\<not>(\<alpha> = \<beta> \<and> P \<sim>ST Q); \<not>\<lparr>Q, \<beta>\<rparr>\<mapsto>\<langle>P, \<alpha>\<rangle>\<rbrakk> \<Longrightarrow> \<lparr>P, \<alpha>\<rparr>\<mapsto>\<langle>Q, \<beta>\<rangle>"
    and "\<lbrakk>\<not>(\<alpha> = \<beta> \<and> P \<sim>ST Q); \<not>\<lparr>P, \<alpha>\<rparr>\<mapsto>\<langle>Q, \<beta>\<rangle>\<rbrakk> \<Longrightarrow> \<lparr>Q, \<beta>\<rparr>\<mapsto>\<langle>P, \<alpha>\<rangle>"
  using assms
  unfolding related_labels_def
  by blast+

lemma related_words_get_condition:
  fixes P Q :: "('procS, 'procT) Proc"
    and w v :: "('labS, 'labT) Lab list"
  assumes "\<langle>P, w\<rangle> \<equiv>\<lparr>\<rparr>* \<langle>Q, v\<rangle>"
  shows "\<lbrakk>\<not>\<lparr>P, w\<rparr>\<mapsto>*\<langle>Q, v\<rangle>; \<not>\<lparr>Q, v\<rparr>\<mapsto>*\<langle>P, w\<rangle>\<rbrakk> \<Longrightarrow> w = v \<and> P \<sim>ST Q"
    and "\<lbrakk>\<not>(w = v \<and> P \<sim>ST Q); \<not>\<lparr>Q, v\<rparr>\<mapsto>*\<langle>P, w\<rangle>\<rbrakk> \<Longrightarrow> \<lparr>P, w\<rparr>\<mapsto>*\<langle>Q, v\<rangle>"
    and "\<lbrakk>\<not>(w = v \<and> P \<sim>ST Q); \<not>\<lparr>P, w\<rparr>\<mapsto>*\<langle>Q, v\<rangle>\<rbrakk> \<Longrightarrow> \<lparr>Q, v\<rparr>\<mapsto>*\<langle>P, w\<rangle>"
  using assms
  unfolding related_words_def
  by blast+

text \<open>Two related words have the same length.\<close>

lemma related_words_length:
  fixes P Q :: "('procS, 'procT) Proc"
    and w v :: "('labS, 'labT) Lab list"
  assumes "\<langle>P, w\<rangle> \<equiv>\<lparr>\<rparr>* \<langle>Q, v\<rangle>"
  shows "length w = length v"
  using assms encoded_word_length[of P w Q v] encoded_word_length[of Q v P w]
  unfolding related_words_def
  by auto

text \<open>We can lift related labels to related words of size one.\<close>

lemma related_words_single:
  fixes P Q :: "('procS, 'procT) Proc"
    and \<alpha> \<beta> :: "('labS, 'labT) Lab"
  assumes rel:   "\<langle>P, \<alpha>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>Q, \<beta>\<rangle>"
  shows "\<langle>P, [\<alpha>]\<rangle> \<equiv>\<lparr>\<rparr>* \<langle>Q, [\<beta>]\<rangle>"
  using rel
  unfolding related_labels_def
proof auto
  fix S S'
  show "\<langle>SourceTerm S, [\<beta>]\<rangle> \<equiv>\<lparr>\<rparr>* \<langle>SourceTerm S', [\<beta>]\<rangle>"
    unfolding related_words_def
    by simp
next
  fix T T'
  show "\<langle>TargetTerm T, [\<beta>]\<rangle> \<equiv>\<lparr>\<rparr>* \<langle>TargetTerm T', [\<beta>]\<rangle>"
    unfolding related_words_def
    by simp
next
  assume "\<lparr>P, \<alpha>\<rparr>\<mapsto>\<langle>Q, \<beta>\<rangle>"
  hence "\<lparr>P, [\<alpha>]\<rparr>\<mapsto>*\<langle>Q, [\<beta>]\<rangle>"
    using ELNil[of P Q] ELCons[of P "[]" Q "[]" P \<alpha> Q \<beta>] kinds_of_encoded_label(1,3)[of P \<alpha> Q \<beta>]
    by simp
  thus "\<langle>P, [\<alpha>]\<rangle> \<equiv>\<lparr>\<rparr>* \<langle>Q, [\<beta>]\<rangle>"
    unfolding related_words_def
    by simp
next
  assume "\<lparr>Q, \<beta>\<rparr>\<mapsto>\<langle>P, \<alpha>\<rangle>"
  hence "\<lparr>Q, [\<beta>]\<rparr>\<mapsto>*\<langle>P, [\<alpha>]\<rangle>"
    using ELNil[of Q P] ELCons[of Q "[]" P "[]" Q \<beta> P \<alpha>] kinds_of_encoded_label(1,3)[of Q \<beta> P \<alpha>]
    by simp
  thus "\<langle>P, [\<alpha>]\<rangle> \<equiv>\<lparr>\<rparr>* \<langle>Q, [\<beta>]\<rangle>"
    unfolding related_words_def
    by simp
qed

text \<open>Two related words of the same kind have to be equal.\<close>

lemma related_labels_equal:
  fixes P Q :: "('procS, 'procT) Proc"
    and \<alpha> \<beta> :: "('labS, 'labT) Lab"
  assumes rel:   "\<langle>P, \<alpha>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>Q, \<beta>\<rangle>"
      and kinds: "P \<sim>ST Q"
    shows "\<alpha> = \<beta>"
proof -
  from kinds have A: "\<not>\<lparr>P, \<alpha>\<rparr>\<mapsto>\<langle>Q, \<beta>\<rangle>"
    using kinds_of_encoded_label(1, 3)[of P \<alpha> Q \<beta>]
    by blast
  from kinds have "\<not>\<lparr>Q, \<beta>\<rparr>\<mapsto>\<langle>P, \<alpha>\<rangle>"
    using kinds_of_encoded_label(1, 3)[of Q \<beta> P \<alpha>]
    by blast
  with rel A show "\<alpha> = \<beta>"
    using related_labels_get_condition(1)[of P \<alpha> Q \<beta>]
    by simp
qed

lemma related_words_equal:
  fixes P Q :: "('procS, 'procT) Proc"
    and w v :: "('labS, 'labT) Lab list"
  assumes rel:   "\<langle>P, w\<rangle> \<equiv>\<lparr>\<rparr>* \<langle>Q, v\<rangle>"
      and kinds: "P \<sim>ST Q"
    shows "w = v"
proof -
  from kinds have A: "\<not>\<lparr>P, w\<rparr>\<mapsto>*\<langle>Q, v\<rangle>"
    using kinds_of_encoded_word(1, 3)[of P w Q v]
    by blast
  from kinds have "\<not>\<lparr>Q, v\<rparr>\<mapsto>*\<langle>P, w\<rangle>"
    using kinds_of_encoded_word(1, 3)[of Q v P w]
    by blast
  with rel A show "w = v"
    using related_words_get_condition(1)[of P w Q v]
    by simp
qed

lemma related_labels_encL:
  fixes P Q :: "('procS, 'procT) Proc"
    and \<alpha> \<beta> :: "('labS, 'labT) Lab"
  assumes rel:   "\<langle>P, \<alpha>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>Q, \<beta>\<rangle>"
      and Pkind: "P \<in> ProcS"
      and Qkind: "Q \<in> ProcT"
    shows "\<lparr>P, \<alpha>\<rparr>\<mapsto>\<langle>Q, \<beta>\<rangle>"
proof -
  from Pkind Qkind have A: "\<not>(\<alpha> = \<beta> \<and> P \<sim>ST Q)"
    by blast
  from Pkind Qkind have "\<not>\<lparr>Q, \<beta>\<rparr>\<mapsto>\<langle>P, \<alpha>\<rangle>"
    using kinds_of_encoded_label(1, 3)[of Q \<beta> P \<alpha>]
    by blast
  with rel A show "\<lparr>P, \<alpha>\<rparr>\<mapsto>\<langle>Q, \<beta>\<rangle>"
    using related_labels_get_condition(2)[of P \<alpha> Q \<beta>]
    by simp
qed

lemma related_words_encL:
  fixes P Q :: "('procS, 'procT) Proc"
    and w v :: "('labS, 'labT) Lab list"
  assumes rel:   "\<langle>P, w\<rangle> \<equiv>\<lparr>\<rparr>* \<langle>Q, v\<rangle>"
      and Pkind: "P \<in> ProcS"
      and Qkind: "Q \<in> ProcT"
    shows "\<lparr>P, w\<rparr>\<mapsto>*\<langle>Q, v\<rangle>"
proof -
  from Pkind Qkind have A: "\<not>(w = v \<and> P \<sim>ST Q)"
    by blast
  from Pkind Qkind have "\<not>\<lparr>Q, v\<rparr>\<mapsto>*\<langle>P, w\<rangle>"
    using kinds_of_encoded_word(1, 3)[of Q v P w]
    by blast
  with rel A show "\<lparr>P, w\<rparr>\<mapsto>*\<langle>Q, v\<rangle>"
    using related_words_get_condition(2)[of P w Q v]
    by simp
qed

lemma related_labels_encL_rev:
  fixes P Q :: "('procS, 'procT) Proc"
    and \<alpha> \<beta> :: "('labS, 'labT) Lab"
  assumes rel:   "\<langle>P, \<alpha>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>Q, \<beta>\<rangle>"
      and Pkind: "P \<in> ProcT"
      and Qkind: "Q \<in> ProcS"
    shows "\<lparr>Q, \<beta>\<rparr>\<mapsto>\<langle>P, \<alpha>\<rangle>"
proof -
  from Pkind Qkind have A: "\<not>(\<alpha> = \<beta> \<and> P \<sim>ST Q)"
    by blast
  from Pkind Qkind have "\<not>\<lparr>P, \<alpha>\<rparr>\<mapsto>\<langle>Q, \<beta>\<rangle>"
    using kinds_of_encoded_label(1, 3)[of P \<alpha> Q \<beta>]
    by blast
  with rel A show "\<lparr>Q, \<beta>\<rparr>\<mapsto>\<langle>P, \<alpha>\<rangle>"
    using related_labels_get_condition(3)[of P \<alpha> Q \<beta>]
    by simp
qed

lemma related_words_encL_rev:
  fixes P Q :: "('procS, 'procT) Proc"
    and w v :: "('labS, 'labT) Lab list"
  assumes rel:   "\<langle>P, w\<rangle> \<equiv>\<lparr>\<rparr>* \<langle>Q, v\<rangle>"
      and Pkind: "P \<in> ProcT"
      and Qkind: "Q \<in> ProcS"
    shows "\<lparr>Q, v\<rparr>\<mapsto>*\<langle>P, w\<rangle>"
proof -
  from Pkind Qkind have A: "\<not>(w = v \<and> P \<sim>ST Q)"
    by blast
  from Pkind Qkind have "\<not>\<lparr>P, w\<rparr>\<mapsto>*\<langle>Q, v\<rangle>"
    using kinds_of_encoded_word(1, 3)[of P w Q v]
    by blast
  with rel A show "\<lparr>Q, v\<rparr>\<mapsto>*\<langle>P, w\<rangle>"
    using related_words_get_condition(3)[of P w Q v]
    by simp
qed

text \<open>Also in the definition of related labels/words the only thing that matters of the mentioned
      processes is their kind.\<close>

lemma related_labels_exchange_processes:
  fixes P Q P' Q' :: "('procS, 'procT) Proc"
    and \<alpha> \<beta>       :: "('labS, 'labT) Lab"
  assumes rel:   "\<langle>P, \<alpha>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>Q, \<beta>\<rangle>"
      and Pkind: "P \<sim>ST P'"
      and Qkind: "Q \<sim>ST Q'"
    shows "\<langle>P', \<alpha>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>Q', \<beta>\<rangle>"
proof (cases "\<lparr>P, \<alpha>\<rparr>\<mapsto>\<langle>Q, \<beta>\<rangle>")
  assume A1: "\<lparr>P, \<alpha>\<rparr>\<mapsto>\<langle>Q, \<beta>\<rangle>"
  with Pkind have A2: "P' \<in> ProcS"
    using kinds_of_encoded_label(1)[of P \<alpha> Q \<beta>]
    by blast
  from Qkind A1 have "Q' \<in> ProcT"
    using kinds_of_encoded_label(3)[of P \<alpha> Q \<beta>]
    by blast
  with A1 A2 have "\<lparr>P', \<alpha>\<rparr>\<mapsto>\<langle>Q', \<beta>\<rangle>"
    using encoded_label_exchange_processes[of P \<alpha> Q \<beta> P' Q']
    by simp
  thus "\<langle>P', \<alpha>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>Q', \<beta>\<rangle>"
    unfolding related_labels_def
    by simp
next
  assume A: "\<not>\<lparr>P, \<alpha>\<rparr>\<mapsto>\<langle>Q, \<beta>\<rangle>"
  show "\<langle>P', \<alpha>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>Q', \<beta>\<rangle>"
  proof (cases "\<lparr>Q, \<beta>\<rparr>\<mapsto>\<langle>P, \<alpha>\<rangle>")
    assume B1: "\<lparr>Q, \<beta>\<rparr>\<mapsto>\<langle>P, \<alpha>\<rangle>"
    with Qkind have B2: "Q' \<in> ProcS"
      using kinds_of_encoded_label(1)[of Q \<beta> P \<alpha>]
      by blast
    from Pkind B1 have "P' \<in> ProcT"
      using kinds_of_encoded_label(3)[of Q \<beta> P \<alpha>]
      by blast
    with B1 B2 have "\<lparr>Q', \<beta>\<rparr>\<mapsto>\<langle>P', \<alpha>\<rangle>"
      using encoded_label_exchange_processes[of Q \<beta> P \<alpha> Q' P']
      by simp
    thus "\<langle>P', \<alpha>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>Q', \<beta>\<rangle>"
      unfolding related_labels_def
      by simp
  next
    assume "\<not>\<lparr>Q, \<beta>\<rparr>\<mapsto>\<langle>P, \<alpha>\<rangle>"
    with rel A have B1: "\<alpha> = \<beta>" and B2: "P \<sim>ST Q"
      using related_labels_get_condition(1)[of P \<alpha> Q \<beta>]
      by simp_all
    from Pkind Qkind B2 have "P' \<sim>ST Q'"
      by blast
    with B1 show "\<langle>P', \<alpha>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>Q', \<beta>\<rangle>"
      unfolding related_labels_def
      by simp
  qed
qed

lemma related_words_exchange_processes:
  fixes P Q P' Q' :: "('procS, 'procT) Proc"
    and w v       :: "('labS, 'labT) Lab list"
  assumes rel:   "\<langle>P, w\<rangle> \<equiv>\<lparr>\<rparr>* \<langle>Q, v\<rangle>"
      and Pkind: "P \<sim>ST P'"
      and Qkind: "Q \<sim>ST Q'"
    shows "\<langle>P', w\<rangle> \<equiv>\<lparr>\<rparr>* \<langle>Q', v\<rangle>"
proof (cases "\<lparr>P, w\<rparr>\<mapsto>*\<langle>Q, v\<rangle>")
  assume A1: "\<lparr>P, w\<rparr>\<mapsto>*\<langle>Q, v\<rangle>"
  with Pkind have A2: "P' \<in> ProcS"
    using kinds_of_encoded_word(1)[of P w Q v]
    by blast
  from Qkind A1 have "Q' \<in> ProcT"
    using kinds_of_encoded_word(3)[of P w Q v]
    by blast
  with A1 A2 have "\<lparr>P', w\<rparr>\<mapsto>*\<langle>Q', v\<rangle>"
    using encoded_word_exchange_processes[of P w Q v P' Q']
    by simp
  thus "\<langle>P', w\<rangle> \<equiv>\<lparr>\<rparr>* \<langle>Q', v\<rangle>"
    unfolding related_words_def
    by simp
next
  assume A: "\<not>\<lparr>P, w\<rparr>\<mapsto>*\<langle>Q, v\<rangle>"
  show "\<langle>P', w\<rangle> \<equiv>\<lparr>\<rparr>* \<langle>Q', v\<rangle>"
  proof (cases "\<lparr>Q, v\<rparr>\<mapsto>*\<langle>P, w\<rangle>")
    assume B1: "\<lparr>Q, v\<rparr>\<mapsto>*\<langle>P, w\<rangle>"
    with Qkind have B2: "Q' \<in> ProcS"
      using kinds_of_encoded_word(1)[of Q v P w]
      by blast
    from Pkind B1 have "P' \<in> ProcT"
      using kinds_of_encoded_word(3)[of Q v P w]
      by blast
    with B1 B2 have "\<lparr>Q', v\<rparr>\<mapsto>*\<langle>P', w\<rangle>"
      using encoded_word_exchange_processes[of Q v P w Q' P']
      by simp
    thus "\<langle>P', w\<rangle> \<equiv>\<lparr>\<rparr>* \<langle>Q', v\<rangle>"
      unfolding related_words_def
      by simp
  next
    assume "\<not>\<lparr>Q, v\<rparr>\<mapsto>*\<langle>P, w\<rangle>"
    with rel A have B1: "w = v" and B2: "P \<sim>ST Q"
      using related_words_get_condition(1)[of P w Q v]
      by simp_all
    from Pkind Qkind B2 have "P' \<sim>ST Q'"
      by blast
    with B1 show "\<langle>P', w\<rangle> \<equiv>\<lparr>\<rparr>* \<langle>Q', v\<rangle>"
      unfolding related_words_def
      by simp
  qed
qed

text \<open>Two related words and two related labels of of matching kinds can be composed into larger
      related words.\<close>

lemma related_words_compose:
  fixes P Q P' Q' :: "('procS, 'procT) Proc"
    and w v       :: "('labS, 'labT) Lab list"
    and \<alpha> \<beta>       :: "('labS, 'labT) Lab"
  assumes word:  "\<langle>P, w\<rangle> \<equiv>\<lparr>\<rparr>* \<langle>Q, v\<rangle>"
      and label: "\<langle>P', \<alpha>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>Q', \<beta>\<rangle>"
      and Pkind: "P \<sim>ST P'"
      and Qkind: "Q \<sim>ST Q'"
    shows "\<langle>P, (w@[\<alpha>])\<rangle> \<equiv>\<lparr>\<rparr>* \<langle>Q, (v@[\<beta>])\<rangle>"
  using Pkind Qkind
proof auto
  fix SP SP' SQ SQ'
  assume "SP \<in>S P" and "SQ \<in>S Q"
  with word have A: "w = v"
    using related_words_equal[of P w Q v]
    by simp
  assume "SP' \<in>S P'" and "SQ' \<in>S Q'"
  with label have "\<alpha> = \<beta>"
    using related_labels_equal[of P' \<alpha> Q' \<beta>]
    by simp
  with A show "\<langle>SourceTerm SP, (w@[\<alpha>])\<rangle> \<equiv>\<lparr>\<rparr>* \<langle>SourceTerm SQ, (v@[\<beta>])\<rangle>"
    unfolding related_words_def
    by simp
next
  fix SP SP' TQ TQ'
  assume A1: "SP \<in>S P" and A2: "TQ \<in>T Q"
  with word have A3: "\<lparr>P, w\<rparr>\<mapsto>*\<langle>Q, v\<rangle>"
    using related_words_encL[of P w Q v]
    by simp
  assume "SP' \<in>S P'" and "TQ' \<in>T Q'"
  with label have "\<lparr>P', \<alpha>\<rparr>\<mapsto>\<langle>Q', \<beta>\<rangle>"
    using related_labels_encL[of P' \<alpha> Q' \<beta>]
    by simp
  with A1 A2 A3 have "\<lparr>SourceTerm SP, w@[\<alpha>]\<rparr>\<mapsto>*\<langle>TargetTerm TQ, v@[\<beta>]\<rangle>"
    using ELCons[of P w Q v P' \<alpha> Q' \<beta>]
    by simp
  thus "\<langle>SourceTerm SP, (w@[\<alpha>])\<rangle> \<equiv>\<lparr>\<rparr>* \<langle>TargetTerm TQ, (v@[\<beta>])\<rangle>"
    unfolding related_words_def
    by simp
next
  fix TP TP' SQ SQ'
  assume A1: "TP \<in>T P" and A2: "SQ \<in>S Q"
  with word have A3: "\<lparr>Q, v\<rparr>\<mapsto>*\<langle>P, w\<rangle>"
    using related_words_encL_rev[of P w Q v]
    by simp
  assume "TP' \<in>T P'" and "SQ' \<in>S Q'"
  with label have "\<lparr>Q', \<beta>\<rparr>\<mapsto>\<langle>P', \<alpha>\<rangle>"
    using related_labels_encL_rev[of P' \<alpha> Q' \<beta>]
    by simp
  with A1 A2 A3 have "\<lparr>SourceTerm SQ, v@[\<beta>]\<rparr>\<mapsto>*\<langle>TargetTerm TP, w@[\<alpha>]\<rangle>"
    using ELCons[of Q v P w Q' \<beta> P' \<alpha>]
    by simp
  thus "\<langle>TargetTerm TP, (w@[\<alpha>])\<rangle> \<equiv>\<lparr>\<rparr>* \<langle>SourceTerm SQ, (v@[\<beta>])\<rangle>"
    unfolding related_words_def
    by simp
next
  fix TP TP' TQ TQ'
  assume "TP \<in>T P" and "TQ \<in>T Q"
  with word have A: "w = v"
    using related_words_equal[of P w Q v]
    by simp
  assume "TP' \<in>T P'" and "TQ' \<in>T Q'"
  with label have "\<alpha> = \<beta>"
    using related_labels_equal[of P' \<alpha> Q' \<beta>]
    by simp
  with A show "\<langle>TargetTerm TP, (w@[\<alpha>])\<rangle> \<equiv>\<lparr>\<rparr>* \<langle>TargetTerm TQ, (v@[\<beta>])\<rangle>"
    unfolding related_words_def
    by simp
qed

lemma related_words_decompose:
  fixes P Q :: "('procS, 'procT) Proc"
    and w v :: "('labS, 'labT) Lab list"
  assumes rel: "\<langle>P, w\<rangle> \<equiv>\<lparr>\<rparr>* \<langle>Q, v\<rangle>"
  shows "w = [] \<or> (\<exists>w' \<alpha> v' \<beta> P' Q'. w = w'@[\<alpha>] \<and> v = v'@[\<beta>] \<and> \<langle>P, w'\<rangle> \<equiv>\<lparr>\<rparr>* \<langle>Q, v'\<rangle> \<and>
                   \<langle>P', \<alpha>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>Q', \<beta>\<rangle> \<and> P \<sim>ST P' \<and> Q \<sim>ST Q')"
proof (cases "w = []")
  assume "w = []"
  thus "w = [] \<or> (\<exists>w' \<alpha> v' \<beta> P' Q'. w = w'@[\<alpha>] \<and> v = v'@[\<beta>] \<and> \<langle>P, w'\<rangle> \<equiv>\<lparr>\<rparr>* \<langle>Q, v'\<rangle> \<and>
                  \<langle>P', \<alpha>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>Q', \<beta>\<rangle> \<and> P \<sim>ST P' \<and> Q \<sim>ST Q')"
    by simp
next
  assume A1: "w \<noteq> []"
  with rel have A2: "v \<noteq> []"
    using related_words_length[of P w Q v]
    by auto
  show "w = [] \<or> (\<exists>w' \<alpha> v' \<beta> P' Q'. w = w'@[\<alpha>] \<and> v = v'@[\<beta>] \<and> \<langle>P, w'\<rangle> \<equiv>\<lparr>\<rparr>* \<langle>Q, v'\<rangle> \<and>
                  \<langle>P', \<alpha>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>Q', \<beta>\<rangle> \<and> P \<sim>ST P' \<and> Q \<sim>ST Q')"
  proof (cases "\<lparr>P, w\<rparr>\<mapsto>*\<langle>Q, v\<rangle>")
    assume B1: "\<lparr>P, w\<rparr>\<mapsto>*\<langle>Q, v\<rangle>"
    hence B2: "P \<in> ProcS" and B3: "Q \<in> ProcT"
      using kinds_of_encoded_word(1, 3)[of P w Q v]
      by simp_all
    from A1 B1 obtain w' \<alpha> v' \<beta> P' Q' where B4: "w = w'@[\<alpha>]" and B5: "v = v'@[\<beta>]"
                                        and B6: "\<lparr>P, w'\<rparr>\<mapsto>*\<langle>Q, v'\<rangle>" and B7: "\<lparr>P', \<alpha>\<rparr>\<mapsto>\<langle>Q', \<beta>\<rangle>"
                                        and B8: "P' \<in> ProcS" and B9: "Q' \<in> ProcT"
      using encoded_word_decompose[of P w Q v]
      by blast
    from B6 have B10: "\<langle>P, w'\<rangle> \<equiv>\<lparr>\<rparr>* \<langle>Q, v'\<rangle>"
      unfolding related_words_def
      by simp
    from B7 have B11: "\<langle>P', \<alpha>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>Q', \<beta>\<rangle>"
      unfolding related_labels_def
      by simp
    from B2 B8 have B12: "P \<sim>ST P'"
      by simp
    from B3 B9 have "Q \<sim>ST Q'"
      by simp
    with A1 B4 B5 B10 B11 B12
    show "w = [] \<or> (\<exists>w' \<alpha> v' \<beta> P' Q'. w = w'@[\<alpha>] \<and> v = v'@[\<beta>] \<and> \<langle>P, w'\<rangle> \<equiv>\<lparr>\<rparr>* \<langle>Q, v'\<rangle> \<and>
                    \<langle>P', \<alpha>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>Q', \<beta>\<rangle> \<and> P \<sim>ST P' \<and> Q \<sim>ST Q')"
      by blast
  next
    assume B: "\<not>\<lparr>P, w\<rparr>\<mapsto>*\<langle>Q, v\<rangle>"
    show "w = [] \<or> (\<exists>w' \<alpha> v' \<beta> P' Q'. w = w'@[\<alpha>] \<and> v = v'@[\<beta>] \<and> \<langle>P, w'\<rangle> \<equiv>\<lparr>\<rparr>* \<langle>Q, v'\<rangle> \<and>
                    \<langle>P', \<alpha>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>Q', \<beta>\<rangle> \<and> P \<sim>ST P' \<and> Q \<sim>ST Q')"
    proof (cases "\<lparr>Q, v\<rparr>\<mapsto>*\<langle>P, w\<rangle>")
      assume C1: "\<lparr>Q, v\<rparr>\<mapsto>*\<langle>P, w\<rangle>"
      hence C2: "Q \<in> ProcS" and C3: "P \<in> ProcT"
        using kinds_of_encoded_word(1, 3)[of Q v P w]
        by simp_all
      from A2 C1 obtain w' \<alpha> v' \<beta> P' Q' where C4: "w = w'@[\<alpha>]" and C5: "v = v'@[\<beta>]"
                                          and C6: "\<lparr>Q, v'\<rparr>\<mapsto>*\<langle>P, w'\<rangle>" and C7: "\<lparr>Q', \<beta>\<rparr>\<mapsto>\<langle>P', \<alpha>\<rangle>"
                                          and C8: "Q' \<in> ProcS" and C9: "P' \<in> ProcT"
        using encoded_word_decompose[of Q v P w]
        by blast
      from C6 have C10: "\<langle>P, w'\<rangle> \<equiv>\<lparr>\<rparr>* \<langle>Q, v'\<rangle>"
        unfolding related_words_def
        by simp
      from C7 have C11: "\<langle>P', \<alpha>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>Q', \<beta>\<rangle>"
        unfolding related_labels_def
        by simp
      from C2 C8 have C12: "Q \<sim>ST Q'"
        by simp
      from C3 C9 have "P \<sim>ST P'"
        by simp
      with A1 C4 C5 C10 C11 C12
      show "w = [] \<or> (\<exists>w' \<alpha> v' \<beta> P' Q'. w = w'@[\<alpha>] \<and> v = v'@[\<beta>] \<and> \<langle>P, w'\<rangle> \<equiv>\<lparr>\<rparr>* \<langle>Q, v'\<rangle> \<and>
                      \<langle>P', \<alpha>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>Q', \<beta>\<rangle> \<and> P \<sim>ST P' \<and> Q \<sim>ST Q')"
        by blast
    next
      assume "\<not>\<lparr>Q, v\<rparr>\<mapsto>*\<langle>P, w\<rangle>"
      with rel B have C1: "w = v" and C2: "P \<sim>ST Q"
        using related_words_get_condition(1)[of P w Q v]
        by simp_all
      from A1 obtain w' \<alpha> where C3: "w = w'@[\<alpha>]"
        by (metis snoc_eq_iff_butlast)
      from C1 C3 have C4: "v = w'@[\<alpha>]"
        by simp
      have C5: "P \<sim>ST P"
        using source_or_target
        by presburger
      hence "\<langle>P, w'\<rangle> \<equiv>\<lparr>\<rparr>* \<langle>P, w'\<rangle>"
        unfolding related_words_def
        by simp
      with C2 C5 have C6: "\<langle>P, w'\<rangle> \<equiv>\<lparr>\<rparr>* \<langle>Q, w'\<rangle>"
        using related_words_exchange_processes[of P w' P w' P Q]
        by simp
      from C5 have "\<langle>P, \<alpha>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>P, \<alpha>\<rangle>"
        unfolding related_labels_def
        by simp
      with C2 C5 have C7: "\<langle>P, \<alpha>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>Q, \<alpha>\<rangle>"
        using related_labels_exchange_processes[of P \<alpha> P \<alpha> P Q]
        by simp
      have "Q \<sim>ST Q"
        using source_or_target
        by presburger
      with A1 C3 C4 C5 C6 C7
      show "w = [] \<or> (\<exists>w' \<alpha> v' \<beta> P' Q'. w = w'@[\<alpha>] \<and> v = v'@[\<beta>] \<and> \<langle>P, w'\<rangle> \<equiv>\<lparr>\<rparr>* \<langle>Q, v'\<rangle> \<and>
                      \<langle>P', \<alpha>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>Q', \<beta>\<rangle> \<and> P \<sim>ST P' \<and> Q \<sim>ST Q')"
        by blast
    qed
  qed
qed

text \<open>The relations of related labels and related words are equivalences, where for transitivity
      we have to additionally require that the label encoding is injective or that no target
      process is ever related to a source process.\<close>

lemma related_labels_refl:
  fixes P :: "('procS, 'procT) Proc"
    and \<alpha> :: "('labS, 'labT) Lab"
  shows "\<langle>P, \<alpha>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>P, \<alpha>\<rangle>"
proof -
  have "P \<sim>ST P"
    using source_or_target[of P]
    by presburger
  thus "\<langle>P, \<alpha>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>P, \<alpha>\<rangle>"
    unfolding related_labels_def
    by simp
qed

lemma related_words_refl:
  fixes P :: "('procS, 'procT) Proc"
    and w :: "('labS, 'labT) Lab list"
  shows "\<langle>P, w\<rangle> \<equiv>\<lparr>\<rparr>* \<langle>P, w\<rangle>"
proof -
  have "P \<sim>ST P"
    using source_or_target[of P]
    by presburger
  thus "\<langle>P, w\<rangle> \<equiv>\<lparr>\<rparr>* \<langle>P, w\<rangle>"
    unfolding related_words_def
    by simp
qed

lemma related_labels_sym:
  fixes P Q :: "('procS, 'procT) Proc"
    and \<alpha> \<beta> :: "('labS, 'labT) Lab"
  assumes "\<langle>P, \<alpha>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>Q, \<beta>\<rangle>"
  shows "\<langle>Q, \<beta>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>P, \<alpha>\<rangle>"
  using assms
  unfolding related_labels_def
  by auto

lemma related_words_sym:
  fixes P Q :: "('procS, 'procT) Proc"
    and w v :: "('labS, 'labT) Lab list"
  assumes "\<langle>P, w\<rangle> \<equiv>\<lparr>\<rparr>* \<langle>Q, v\<rangle>"
  shows "\<langle>Q, v\<rangle> \<equiv>\<lparr>\<rparr>* \<langle>P, w\<rangle>"
  using assms
  unfolding related_words_def
  by auto

lemma related_labels_trans_inj:
  fixes P Q R :: "('procS, 'procT) Proc"
    and \<alpha> \<beta> \<gamma> :: "('labS, 'labT) Lab"
  assumes rel1: "\<langle>P, \<alpha>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>Q, \<beta>\<rangle>"
      and rel2: "\<langle>Q, \<beta>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>R, \<gamma>\<rangle>"
      and inj:  "inj encL"
    shows "\<langle>P, \<alpha>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>R, \<gamma>\<rangle>"
proof (cases "\<lparr>P, \<alpha>\<rparr>\<mapsto>\<langle>Q, \<beta>\<rangle>")
  assume A1: "\<lparr>P, \<alpha>\<rparr>\<mapsto>\<langle>Q, \<beta>\<rangle>"
  hence A2: "P \<in> ProcS" and A3: "Q \<in> ProcT"
    using kinds_of_encoded_label(1, 3)[of P \<alpha> Q \<beta>]
    by simp_all
  show "\<langle>P, \<alpha>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>R, \<gamma>\<rangle>"
  proof (cases "\<lparr>Q, \<beta>\<rparr>\<mapsto>\<langle>R, \<gamma>\<rangle>")
    assume "\<lparr>Q, \<beta>\<rparr>\<mapsto>\<langle>R, \<gamma>\<rangle>"
    hence "Q \<in> ProcS"
      using kinds_of_encoded_label(1)[of Q \<beta> R \<gamma>]
      by simp
    with A3 have False
      by blast
    thus "\<langle>P, \<alpha>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>R, \<gamma>\<rangle>"
      by simp
  next
    assume B: "\<not>\<lparr>Q, \<beta>\<rparr>\<mapsto>\<langle>R, \<gamma>\<rangle>"
    show "\<langle>P, \<alpha>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>R, \<gamma>\<rangle>"
    proof (cases "\<lparr>R, \<gamma>\<rparr>\<mapsto>\<langle>Q, \<beta>\<rangle>")
      assume C1: "\<lparr>R, \<gamma>\<rparr>\<mapsto>\<langle>Q, \<beta>\<rangle>"
      with inj A1 have C2: "\<alpha> = \<gamma>"
        using encoded_label_unique_rev[of P \<alpha> Q \<beta> R \<gamma>]
        by simp
      from C1 have "R \<in> ProcS"
        using kinds_of_encoded_label(1)[of R \<gamma> Q \<beta>]
        by simp
      with A2 have "P \<sim>ST R"
        by simp
      with C2 show "\<langle>P, \<alpha>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>R, \<gamma>\<rangle>"
        unfolding related_labels_def
        by simp
    next
      assume "\<not>\<lparr>R, \<gamma>\<rparr>\<mapsto>\<langle>Q, \<beta>\<rangle>"
      with rel2 B have C1: "\<beta> = \<gamma>" and C2: "Q \<sim>ST R"
        using related_labels_get_condition(1)[of Q \<beta> R \<gamma>]
        by simp_all
      from A1 C1 have C3: "\<lparr>P, \<alpha>\<rparr>\<mapsto>\<langle>Q, \<gamma>\<rangle>"
        by simp
      from A3 C2 have "R \<in> ProcT"
        by blast
      with A2 C3 have "\<lparr>P, \<alpha>\<rparr>\<mapsto>\<langle>R, \<gamma>\<rangle>"
        using encoded_label_exchange_processes[of P \<alpha> Q \<gamma> P R]
        by simp
      thus "\<langle>P, \<alpha>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>R, \<gamma>\<rangle>"
        unfolding related_labels_def
        by simp
    qed
  qed
next
  assume A: "\<not>\<lparr>P, \<alpha>\<rparr>\<mapsto>\<langle>Q, \<beta>\<rangle>"
  show "\<langle>P, \<alpha>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>R, \<gamma>\<rangle>"
  proof (cases "\<lparr>Q, \<beta>\<rparr>\<mapsto>\<langle>P, \<alpha>\<rangle>")
    assume B1: "\<lparr>Q, \<beta>\<rparr>\<mapsto>\<langle>P, \<alpha>\<rangle>"
    hence B2: "Q \<in> ProcS" and B3: "P \<in> ProcT"
      using kinds_of_encoded_label(1, 3)[of Q \<beta> P \<alpha>]
      by simp_all
    show "\<langle>P, \<alpha>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>R, \<gamma>\<rangle>"
    proof (cases "\<lparr>Q, \<beta>\<rparr>\<mapsto>\<langle>R, \<gamma>\<rangle>")
      assume C1: "\<lparr>Q, \<beta>\<rparr>\<mapsto>\<langle>R, \<gamma>\<rangle>"
      with inj B1 have C2: "\<alpha> = \<gamma>"
        using encoded_label_unique[of Q \<beta> P \<alpha> R \<gamma>]
        by simp
      from C1 have "R \<in> ProcT"
        using kinds_of_encoded_label(3)[of Q \<beta> R \<gamma>]
        by simp
      with B3 have "P \<sim>ST R"
        by simp
      with C2 show "\<langle>P, \<alpha>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>R, \<gamma>\<rangle>"
        unfolding related_labels_def
        by simp
    next
      assume C: "\<not>\<lparr>Q, \<beta>\<rparr>\<mapsto>\<langle>R, \<gamma>\<rangle>"
      show "\<langle>P, \<alpha>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>R, \<gamma>\<rangle>"
      proof (cases "\<lparr>R, \<gamma>\<rparr>\<mapsto>\<langle>Q, \<beta>\<rangle>")
        assume "\<lparr>R, \<gamma>\<rparr>\<mapsto>\<langle>Q, \<beta>\<rangle>"
        hence "Q \<in> ProcT"
          using kinds_of_encoded_label(3)[of R \<gamma> Q \<beta>]
          by simp
        with B2 have False
          by blast
        thus "\<langle>P, \<alpha>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>R, \<gamma>\<rangle>"
          by simp
      next
        assume "\<not>\<lparr>R, \<gamma>\<rparr>\<mapsto>\<langle>Q, \<beta>\<rangle>"
        with rel2 C have D1: "\<beta> = \<gamma>" and D2: "Q \<sim>ST R"
          using related_labels_get_condition(1)[of Q \<beta> R \<gamma>]
          by simp_all
        from B1 D1 have D3: "\<lparr>Q, \<gamma>\<rparr>\<mapsto>\<langle>P, \<alpha>\<rangle>"
          by simp
        from B2 D2 have "R \<in> ProcS"
          by blast
        with B3 D3 have "\<lparr>R, \<gamma>\<rparr>\<mapsto>\<langle>P, \<alpha>\<rangle>"
          using encoded_label_exchange_processes[of Q \<gamma> P \<alpha> R P]
          by simp
        thus "\<langle>P, \<alpha>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>R, \<gamma>\<rangle>"
          unfolding related_labels_def
          by simp
      qed
    qed
  next
    assume "\<not>\<lparr>Q, \<beta>\<rparr>\<mapsto>\<langle>P, \<alpha>\<rangle>"
    with rel1 A have A1: "\<alpha> = \<beta>" and A2: "P \<sim>ST Q"
      using related_labels_get_condition(1)[of P \<alpha> Q \<beta>]
      by simp_all
    show "\<langle>P, \<alpha>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>R, \<gamma>\<rangle>"
    proof (cases "\<lparr>Q, \<beta>\<rparr>\<mapsto>\<langle>R, \<gamma>\<rangle>")
      assume B1: "\<lparr>Q, \<beta>\<rparr>\<mapsto>\<langle>R, \<gamma>\<rangle>"
      with A1 have B2: "\<lparr>Q, \<alpha>\<rparr>\<mapsto>\<langle>R, \<gamma>\<rangle>"
        by simp
      from B1 have "Q \<in> ProcS"
        using kinds_of_encoded_label(1)[of Q \<beta> R \<gamma>]
        by simp
      with A2 have B3: "P \<in> ProcS"
        by blast
      from B1 have "R \<in> ProcT"
        using kinds_of_encoded_label(3)[of Q \<beta> R \<gamma>]
        by simp
      with B2 B3 have "\<lparr>P, \<alpha>\<rparr>\<mapsto>\<langle>R, \<gamma>\<rangle>"
        using encoded_label_exchange_processes[of Q \<alpha> R \<gamma> P R]
        by simp
      thus "\<langle>P, \<alpha>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>R, \<gamma>\<rangle>"
        unfolding related_labels_def
        by simp
    next
      assume B: "\<not>\<lparr>Q, \<beta>\<rparr>\<mapsto>\<langle>R, \<gamma>\<rangle>"
      show "\<langle>P, \<alpha>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>R, \<gamma>\<rangle>"
      proof (cases "\<lparr>R, \<gamma>\<rparr>\<mapsto>\<langle>Q, \<beta>\<rangle>")
        assume C1: "\<lparr>R, \<gamma>\<rparr>\<mapsto>\<langle>Q, \<beta>\<rangle>"
        with A1 have C2: "\<lparr>R, \<gamma>\<rparr>\<mapsto>\<langle>Q, \<alpha>\<rangle>"
          by simp
        from C1 have C3: "R \<in> ProcS"
          using kinds_of_encoded_label(1)[of R \<gamma> Q \<beta>]
          by simp
        from C1 have "Q \<in> ProcT"
          using kinds_of_encoded_label(3)[of R \<gamma> Q \<beta>]
          by simp
        with A2 have "P \<in> ProcT"
          by blast
        with C2 C3 have "\<lparr>R, \<gamma>\<rparr>\<mapsto>\<langle>P, \<alpha>\<rangle>"
          using encoded_label_exchange_processes[of R \<gamma> Q \<alpha> R P]
          by simp
        thus "\<langle>P, \<alpha>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>R, \<gamma>\<rangle>"
          unfolding related_labels_def
          by simp
      next
        assume "\<not>\<lparr>R, \<gamma>\<rparr>\<mapsto>\<langle>Q, \<beta>\<rangle>"
        with rel2 B have C1: "\<beta> = \<gamma>" and C2: "Q \<sim>ST R"
          using related_labels_get_condition(1)[of Q \<beta> R \<gamma>]
          by simp_all
        from A1 C1 have "\<alpha> = \<gamma>"
          by simp
        moreover from A2 C2 have "P \<sim>ST R"
          by blast
        ultimately show "\<langle>P, \<alpha>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>R, \<gamma>\<rangle>"
          unfolding related_labels_def
          by simp
      qed
    qed
  qed
qed

lemma related_labels_trans_no_T_to_S:
  fixes P Q R :: "('procS, 'procT) Proc"
    and \<alpha> \<beta> \<gamma> :: "('labS, 'labT) Lab"
  assumes rel1: "\<langle>P, \<alpha>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>Q, \<beta>\<rangle>"
      and rel2: "\<langle>Q, \<beta>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>R, \<gamma>\<rangle>"
      and noTS: "\<not>(P \<in> ProcT \<and> Q \<in> ProcS) \<and> \<not>(Q \<in> ProcT \<and> R \<in> ProcS)"
    shows "\<langle>P, \<alpha>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>R, \<gamma>\<rangle>"
proof (cases "\<lparr>P, \<alpha>\<rparr>\<mapsto>\<langle>Q, \<beta>\<rangle>")
  assume A1: "\<lparr>P, \<alpha>\<rparr>\<mapsto>\<langle>Q, \<beta>\<rangle>"
  hence A2: "P \<in> ProcS" and A3: "Q \<in> ProcT"
    using kinds_of_encoded_label(1, 3)[of P \<alpha> Q \<beta>]
    by simp_all
  show "\<langle>P, \<alpha>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>R, \<gamma>\<rangle>"
  proof (cases "\<lparr>Q, \<beta>\<rparr>\<mapsto>\<langle>R, \<gamma>\<rangle>")
    assume "\<lparr>Q, \<beta>\<rparr>\<mapsto>\<langle>R, \<gamma>\<rangle>"
    hence "Q \<in> ProcS"
      using kinds_of_encoded_label(1)[of Q \<beta> R \<gamma>]
      by simp
    with A3 have False
      by blast
    thus "\<langle>P, \<alpha>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>R, \<gamma>\<rangle>"
      by simp
  next
    assume B: "\<not>\<lparr>Q, \<beta>\<rparr>\<mapsto>\<langle>R, \<gamma>\<rangle>"
    show "\<langle>P, \<alpha>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>R, \<gamma>\<rangle>"
    proof (cases "\<lparr>R, \<gamma>\<rparr>\<mapsto>\<langle>Q, \<beta>\<rangle>")
      assume "\<lparr>R, \<gamma>\<rparr>\<mapsto>\<langle>Q, \<beta>\<rangle>"
      with noTS have False
        using kinds_of_encoded_label(1, 3)[of R \<gamma> Q \<beta>]
        by simp
      thus "\<langle>P, \<alpha>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>R, \<gamma>\<rangle>"
        by simp
    next
      assume "\<not>\<lparr>R, \<gamma>\<rparr>\<mapsto>\<langle>Q, \<beta>\<rangle>"
      with rel2 B have C1: "\<beta> = \<gamma>" and C2: "Q \<sim>ST R"
        using related_labels_get_condition(1)[of Q \<beta> R \<gamma>]
        by simp_all
      from A1 C1 have C3: "\<lparr>P, \<alpha>\<rparr>\<mapsto>\<langle>Q, \<gamma>\<rangle>"
        by simp
      from A3 C2 have "R \<in> ProcT"
        by blast
      with A2 C3 have "\<lparr>P, \<alpha>\<rparr>\<mapsto>\<langle>R, \<gamma>\<rangle>"
        using encoded_label_exchange_processes[of P \<alpha> Q \<gamma> P R]
        by simp
      thus "\<langle>P, \<alpha>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>R, \<gamma>\<rangle>"
        unfolding related_labels_def
        by simp
    qed
  qed
next
  assume A: "\<not>\<lparr>P, \<alpha>\<rparr>\<mapsto>\<langle>Q, \<beta>\<rangle>"
  show "\<langle>P, \<alpha>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>R, \<gamma>\<rangle>"
  proof (cases "\<lparr>Q, \<beta>\<rparr>\<mapsto>\<langle>P, \<alpha>\<rangle>")
    assume "\<lparr>Q, \<beta>\<rparr>\<mapsto>\<langle>P, \<alpha>\<rangle>"
    with noTS have False
      using kinds_of_encoded_label(1, 3)[of Q \<beta> P \<alpha>]
      by simp
    thus  "\<langle>P, \<alpha>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>R, \<gamma>\<rangle>"
      by simp
  next
    assume "\<not>\<lparr>Q, \<beta>\<rparr>\<mapsto>\<langle>P, \<alpha>\<rangle>"
    with rel1 A have A1: "\<alpha> = \<beta>" and A2: "P \<sim>ST Q"
      using related_labels_get_condition(1)[of P \<alpha> Q \<beta>]
      by simp_all
    show "\<langle>P, \<alpha>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>R, \<gamma>\<rangle>"
    proof (cases "\<lparr>Q, \<beta>\<rparr>\<mapsto>\<langle>R, \<gamma>\<rangle>")
      assume B1: "\<lparr>Q, \<beta>\<rparr>\<mapsto>\<langle>R, \<gamma>\<rangle>"
      with A1 have B2: "\<lparr>Q, \<alpha>\<rparr>\<mapsto>\<langle>R, \<gamma>\<rangle>"
        by simp
      from B1 have "Q \<in> ProcS"
        using kinds_of_encoded_label(1)[of Q \<beta> R \<gamma>]
        by simp
      with A2 have B3: "P \<in> ProcS"
        by blast
      from B1 have "R \<in> ProcT"
        using kinds_of_encoded_label(3)[of Q \<beta> R \<gamma>]
        by simp
      with B2 B3 have "\<lparr>P, \<alpha>\<rparr>\<mapsto>\<langle>R, \<gamma>\<rangle>"
        using encoded_label_exchange_processes[of Q \<alpha> R \<gamma> P R]
        by simp
      thus "\<langle>P, \<alpha>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>R, \<gamma>\<rangle>"
        unfolding related_labels_def
        by simp
    next
      assume B: "\<not>\<lparr>Q, \<beta>\<rparr>\<mapsto>\<langle>R, \<gamma>\<rangle>"
      show "\<langle>P, \<alpha>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>R, \<gamma>\<rangle>"
      proof (cases "\<lparr>R, \<gamma>\<rparr>\<mapsto>\<langle>Q, \<beta>\<rangle>")
        assume "\<lparr>R, \<gamma>\<rparr>\<mapsto>\<langle>Q, \<beta>\<rangle>"
        with noTS have False
          using kinds_of_encoded_label(1, 3)[of R \<gamma> Q \<beta>]
          by simp
        thus "\<langle>P, \<alpha>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>R, \<gamma>\<rangle>"
          by simp
      next
        assume "\<not>\<lparr>R, \<gamma>\<rparr>\<mapsto>\<langle>Q, \<beta>\<rangle>"
        with rel2 B have C1: "\<beta> = \<gamma>" and C2: "Q \<sim>ST R"
          using related_labels_get_condition(1)[of Q \<beta> R \<gamma>]
          by simp_all
        from A1 C1 have "\<alpha> = \<gamma>"
          by simp
        moreover from A2 C2 have "P \<sim>ST R"
          by blast
        ultimately show "\<langle>P, \<alpha>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>R, \<gamma>\<rangle>"
          unfolding related_labels_def
          by simp
      qed
    qed
  qed
qed

lemma related_labels_trans_no_S_to_T:
  fixes P Q R :: "('procS, 'procT) Proc"
    and \<alpha> \<beta> \<gamma> :: "('labS, 'labT) Lab"
  assumes rel1: "\<langle>P, \<alpha>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>Q, \<beta>\<rangle>"
      and rel2: "\<langle>Q, \<beta>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>R, \<gamma>\<rangle>"
      and noST: "\<not>(P \<in> ProcS \<and> Q \<in> ProcT) \<and> \<not>(Q \<in> ProcS \<and> R \<in> ProcT)"
    shows "\<langle>P, \<alpha>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>R, \<gamma>\<rangle>"
proof (cases "\<lparr>P, \<alpha>\<rparr>\<mapsto>\<langle>Q, \<beta>\<rangle>")
  assume A1: "\<lparr>P, \<alpha>\<rparr>\<mapsto>\<langle>Q, \<beta>\<rangle>"
  with noST have False
    using kinds_of_encoded_label(1, 3)[of P \<alpha> Q \<beta>]
    by simp
  thus "\<langle>P, \<alpha>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>R, \<gamma>\<rangle>"
    by simp
next
  assume A: "\<not>\<lparr>P, \<alpha>\<rparr>\<mapsto>\<langle>Q, \<beta>\<rangle>"
  show "\<langle>P, \<alpha>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>R, \<gamma>\<rangle>"
  proof (cases "\<lparr>Q, \<beta>\<rparr>\<mapsto>\<langle>P, \<alpha>\<rangle>")
    assume B1: "\<lparr>Q, \<beta>\<rparr>\<mapsto>\<langle>P, \<alpha>\<rangle>"
    hence B2: "Q \<in> ProcS" and B3: "P \<in> ProcT"
      using kinds_of_encoded_label(1, 3)[of Q \<beta> P \<alpha>]
      by simp_all
    show "\<langle>P, \<alpha>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>R, \<gamma>\<rangle>"
    proof (cases "\<lparr>Q, \<beta>\<rparr>\<mapsto>\<langle>R, \<gamma>\<rangle>")
      assume "\<lparr>Q, \<beta>\<rparr>\<mapsto>\<langle>R, \<gamma>\<rangle>"
      with noST have False
        using kinds_of_encoded_label(1, 3)[of Q \<beta> R \<gamma>]
        by simp
      thus "\<langle>P, \<alpha>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>R, \<gamma>\<rangle>"
        by simp
    next
      assume C: "\<not>\<lparr>Q, \<beta>\<rparr>\<mapsto>\<langle>R, \<gamma>\<rangle>"
      show "\<langle>P, \<alpha>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>R, \<gamma>\<rangle>"
      proof (cases "\<lparr>R, \<gamma>\<rparr>\<mapsto>\<langle>Q, \<beta>\<rangle>")
        assume "\<lparr>R, \<gamma>\<rparr>\<mapsto>\<langle>Q, \<beta>\<rangle>"
        hence "Q \<in> ProcT"
          using kinds_of_encoded_label(3)[of R \<gamma> Q \<beta>]
          by simp
        with B2 have False
          by blast
        thus "\<langle>P, \<alpha>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>R, \<gamma>\<rangle>"
          by simp
      next
        assume "\<not>\<lparr>R, \<gamma>\<rparr>\<mapsto>\<langle>Q, \<beta>\<rangle>"
        with rel2 C have D1: "\<beta> = \<gamma>" and D2: "Q \<sim>ST R"
          using related_labels_get_condition(1)[of Q \<beta> R \<gamma>]
          by simp_all
        from B1 D1 have D3: "\<lparr>Q, \<gamma>\<rparr>\<mapsto>\<langle>P, \<alpha>\<rangle>"
          by simp
        from B2 D2 have "R \<in> ProcS"
          by blast
        with B3 D3 have "\<lparr>R, \<gamma>\<rparr>\<mapsto>\<langle>P, \<alpha>\<rangle>"
          using encoded_label_exchange_processes[of Q \<gamma> P \<alpha> R P]
          by simp
        thus "\<langle>P, \<alpha>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>R, \<gamma>\<rangle>"
          unfolding related_labels_def
          by simp
      qed
    qed
  next
    assume "\<not>\<lparr>Q, \<beta>\<rparr>\<mapsto>\<langle>P, \<alpha>\<rangle>"
    with rel1 A have A1: "\<alpha> = \<beta>" and A2: "P \<sim>ST Q"
      using related_labels_get_condition(1)[of P \<alpha> Q \<beta>]
      by simp_all
    show "\<langle>P, \<alpha>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>R, \<gamma>\<rangle>"
    proof (cases "\<lparr>Q, \<beta>\<rparr>\<mapsto>\<langle>R, \<gamma>\<rangle>")
      assume "\<lparr>Q, \<beta>\<rparr>\<mapsto>\<langle>R, \<gamma>\<rangle>"
      with noST have False
        using kinds_of_encoded_label(1, 3)[of Q \<beta> R \<gamma>]
        by simp
      thus "\<langle>P, \<alpha>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>R, \<gamma>\<rangle>"
        by simp
    next
      assume B: "\<not>\<lparr>Q, \<beta>\<rparr>\<mapsto>\<langle>R, \<gamma>\<rangle>"
      show "\<langle>P, \<alpha>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>R, \<gamma>\<rangle>"
      proof (cases "\<lparr>R, \<gamma>\<rparr>\<mapsto>\<langle>Q, \<beta>\<rangle>")
        assume C1: "\<lparr>R, \<gamma>\<rparr>\<mapsto>\<langle>Q, \<beta>\<rangle>"
        with A1 have C2: "\<lparr>R, \<gamma>\<rparr>\<mapsto>\<langle>Q, \<alpha>\<rangle>"
          by simp
        from C1 have C3: "R \<in> ProcS"
          using kinds_of_encoded_label(1)[of R \<gamma> Q \<beta>]
          by simp
        from C1 have "Q \<in> ProcT"
          using kinds_of_encoded_label(3)[of R \<gamma> Q \<beta>]
          by simp
        with A2 have "P \<in> ProcT"
          by blast
        with C2 C3 have "\<lparr>R, \<gamma>\<rparr>\<mapsto>\<langle>P, \<alpha>\<rangle>"
          using encoded_label_exchange_processes[of R \<gamma> Q \<alpha> R P]
          by simp
        thus "\<langle>P, \<alpha>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>R, \<gamma>\<rangle>"
          unfolding related_labels_def
          by simp
      next
        assume "\<not>\<lparr>R, \<gamma>\<rparr>\<mapsto>\<langle>Q, \<beta>\<rangle>"
        with rel2 B have C1: "\<beta> = \<gamma>" and C2: "Q \<sim>ST R"
          using related_labels_get_condition(1)[of Q \<beta> R \<gamma>]
          by simp_all
        from A1 C1 have "\<alpha> = \<gamma>"
          by simp
        moreover from A2 C2 have "P \<sim>ST R"
          by blast
        ultimately show "\<langle>P, \<alpha>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>R, \<gamma>\<rangle>"
          unfolding related_labels_def
          by simp
      qed
    qed
  qed
qed

lemma related_words_trans_inj:
  fixes P Q R :: "('procS, 'procT) Proc"
    and w v y :: "('labS, 'labT) Lab list"
  assumes rel1: "\<langle>P, w\<rangle> \<equiv>\<lparr>\<rparr>* \<langle>Q, v\<rangle>"
      and rel2: "\<langle>Q, v\<rangle> \<equiv>\<lparr>\<rparr>* \<langle>R, y\<rangle>"
      and inj:  "inj encL"
    shows "\<langle>P, w\<rangle> \<equiv>\<lparr>\<rparr>* \<langle>R, y\<rangle>"
proof (cases "\<lparr>P, w\<rparr>\<mapsto>*\<langle>Q, v\<rangle>")
  assume A1: "\<lparr>P, w\<rparr>\<mapsto>*\<langle>Q, v\<rangle>"
  hence A2: "P \<in> ProcS" and A3: "Q \<in> ProcT"
    using kinds_of_encoded_word(1, 3)[of P w Q v]
    by simp_all
  show "\<langle>P, w\<rangle> \<equiv>\<lparr>\<rparr>* \<langle>R, y\<rangle>"
  proof (cases "\<lparr>Q, v\<rparr>\<mapsto>*\<langle>R, y\<rangle>")
    assume "\<lparr>Q, v\<rparr>\<mapsto>*\<langle>R, y\<rangle>"
    hence "Q \<in> ProcS"
      using kinds_of_encoded_word(1)[of Q v R y]
      by simp
    with A3 have False
      by blast
    thus "\<langle>P, w\<rangle> \<equiv>\<lparr>\<rparr>* \<langle>R, y\<rangle>"
      by simp
  next
    assume B: "\<not>\<lparr>Q, v\<rparr>\<mapsto>*\<langle>R, y\<rangle>"
    show "\<langle>P, w\<rangle> \<equiv>\<lparr>\<rparr>* \<langle>R, y\<rangle>"
    proof (cases "\<lparr>R, y\<rparr>\<mapsto>*\<langle>Q, v\<rangle>")
      assume C1: "\<lparr>R, y\<rparr>\<mapsto>*\<langle>Q, v\<rangle>"
      with inj A1 have C2: "w = y"
        using encoded_word_unique_rev[of P w Q v R y]
        by simp
      from C1 have "R \<in> ProcS"
        using kinds_of_encoded_word(1)[of R y Q v]
        by simp
      with A2 have "P \<sim>ST R"
        by simp
      with C2 show "\<langle>P, w\<rangle> \<equiv>\<lparr>\<rparr>* \<langle>R, y\<rangle>"
        unfolding related_words_def
        by simp
    next
      assume "\<not>\<lparr>R, y\<rparr>\<mapsto>*\<langle>Q, v\<rangle>"
      with rel2 B have C1: "v = y" and C2: "Q \<sim>ST R"
        using related_words_get_condition(1)[of Q v R y]
        by simp_all
      from A1 C1 have C3: "\<lparr>P, w\<rparr>\<mapsto>*\<langle>Q, y\<rangle>"
        by simp
      from A3 C2 have "R \<in> ProcT"
        by blast
      with A2 C3 have "\<lparr>P, w\<rparr>\<mapsto>*\<langle>R, y\<rangle>"
        using encoded_word_exchange_processes[of P w Q y P R]
        by simp
      thus "\<langle>P, w\<rangle> \<equiv>\<lparr>\<rparr>* \<langle>R, y\<rangle>"
        unfolding related_words_def
        by simp
    qed
  qed
next
  assume A: "\<not>\<lparr>P, w\<rparr>\<mapsto>*\<langle>Q, v\<rangle>"
  show "\<langle>P, w\<rangle> \<equiv>\<lparr>\<rparr>* \<langle>R, y\<rangle>"
  proof (cases "\<lparr>Q, v\<rparr>\<mapsto>*\<langle>P, w\<rangle>")
    assume B1: "\<lparr>Q, v\<rparr>\<mapsto>*\<langle>P, w\<rangle>"
    hence B2: "Q \<in> ProcS" and B3: "P \<in> ProcT"
      using kinds_of_encoded_word(1, 3)[of Q v P w]
      by simp_all
    show "\<langle>P, w\<rangle> \<equiv>\<lparr>\<rparr>* \<langle>R, y\<rangle>"
    proof (cases "\<lparr>Q, v\<rparr>\<mapsto>*\<langle>R, y\<rangle>")
      assume C1: "\<lparr>Q, v\<rparr>\<mapsto>*\<langle>R, y\<rangle>"
      with inj B1 have C2: "w = y"
        using encoded_word_unique[of Q v P w R y]
        by simp
      from C1 have "R \<in> ProcT"
        using kinds_of_encoded_word(3)[of Q v R y]
        by simp
      with B3 have "P \<sim>ST R"
        by simp
      with C2 show "\<langle>P, w\<rangle> \<equiv>\<lparr>\<rparr>* \<langle>R, y\<rangle>"
        unfolding related_words_def
        by simp
    next
      assume C: "\<not>\<lparr>Q, v\<rparr>\<mapsto>*\<langle>R, y\<rangle>"
      show "\<langle>P, w\<rangle> \<equiv>\<lparr>\<rparr>* \<langle>R, y\<rangle>"
      proof (cases "\<lparr>R, y\<rparr>\<mapsto>*\<langle>Q, v\<rangle>")
        assume "\<lparr>R, y\<rparr>\<mapsto>*\<langle>Q, v\<rangle>"
        hence "Q \<in> ProcT"
          using kinds_of_encoded_word(3)[of R y Q v]
          by simp
        with B2 have False
          by blast
        thus "\<langle>P, w\<rangle> \<equiv>\<lparr>\<rparr>* \<langle>R, y\<rangle>"
          by simp
      next
        assume "\<not>\<lparr>R, y\<rparr>\<mapsto>*\<langle>Q, v\<rangle>"
        with rel2 C have D1: "v = y" and D2: "Q \<sim>ST R"
          using related_words_get_condition(1)[of Q v R y]
          by simp_all
        from B1 D1 have D3: "\<lparr>Q, y\<rparr>\<mapsto>*\<langle>P, w\<rangle>"
          by simp
        from B2 D2 have "R \<in> ProcS"
          by blast
        with B3 D3 have "\<lparr>R, y\<rparr>\<mapsto>*\<langle>P, w\<rangle>"
          using encoded_word_exchange_processes[of Q y P w R P]
          by simp
        thus "\<langle>P, w\<rangle> \<equiv>\<lparr>\<rparr>* \<langle>R, y\<rangle>"
          unfolding related_words_def
          by simp
      qed
    qed
  next
    assume "\<not>\<lparr>Q, v\<rparr>\<mapsto>*\<langle>P, w\<rangle>"
    with rel1 A have A1: "w = v" and A2: "P \<sim>ST Q"
      using related_words_get_condition(1)[of P w Q v]
      by simp_all
    show "\<langle>P, w\<rangle> \<equiv>\<lparr>\<rparr>* \<langle>R, y\<rangle>"
    proof (cases "\<lparr>Q, v\<rparr>\<mapsto>*\<langle>R, y\<rangle>")
      assume B1: "\<lparr>Q, v\<rparr>\<mapsto>*\<langle>R, y\<rangle>"
      with A1 have B2: "\<lparr>Q, w\<rparr>\<mapsto>*\<langle>R, y\<rangle>"
        by simp
      from B1 have "Q \<in> ProcS"
        using kinds_of_encoded_word(1)[of Q v R y]
        by simp
      with A2 have B3: "P \<in> ProcS"
        by blast
      from B1 have "R \<in> ProcT"
        using kinds_of_encoded_word(3)[of Q v R y]
        by simp
      with B2 B3 have "\<lparr>P, w\<rparr>\<mapsto>*\<langle>R, y\<rangle>"
        using encoded_word_exchange_processes[of Q w R y P R]
        by simp
      thus "\<langle>P, w\<rangle> \<equiv>\<lparr>\<rparr>* \<langle>R, y\<rangle>"
        unfolding related_words_def
        by simp
    next
      assume B: "\<not>\<lparr>Q, v\<rparr>\<mapsto>*\<langle>R, y\<rangle>"
      show "\<langle>P, w\<rangle> \<equiv>\<lparr>\<rparr>* \<langle>R, y\<rangle>"
      proof (cases "\<lparr>R, y\<rparr>\<mapsto>*\<langle>Q, v\<rangle>")
        assume C1: "\<lparr>R, y\<rparr>\<mapsto>*\<langle>Q, v\<rangle>"
        with A1 have C2: "\<lparr>R, y\<rparr>\<mapsto>*\<langle>Q, w\<rangle>"
          by simp
        from C1 have C3: "R \<in> ProcS"
          using kinds_of_encoded_word(1)[of R y Q v]
          by simp
        from C1 have "Q \<in> ProcT"
          using kinds_of_encoded_word(3)[of R y Q v]
          by simp
        with A2 have "P \<in> ProcT"
          by blast
        with C2 C3 have "\<lparr>R, y\<rparr>\<mapsto>*\<langle>P, w\<rangle>"
          using encoded_word_exchange_processes[of R y Q w R P]
          by simp
        thus "\<langle>P, w\<rangle> \<equiv>\<lparr>\<rparr>* \<langle>R, y\<rangle>"
          unfolding related_words_def
          by simp
      next
        assume "\<not>\<lparr>R, y\<rparr>\<mapsto>*\<langle>Q, v\<rangle>"
        with rel2 B have C1: "v = y" and C2: "Q \<sim>ST R"
          using related_words_get_condition(1)[of Q v R y]
          by simp_all
        from A1 C1 have "w = y"
          by simp
        moreover from A2 C2 have "P \<sim>ST R"
          by blast
        ultimately show "\<langle>P, w\<rangle> \<equiv>\<lparr>\<rparr>* \<langle>R, y\<rangle>"
          unfolding related_words_def
          by simp
      qed
    qed
  qed
qed

lemma related_words_trans_no_T_to_S:
  fixes P Q R :: "('procS, 'procT) Proc"
    and w v y :: "('labS, 'labT) Lab list"
  assumes rel1: "\<langle>P, w\<rangle> \<equiv>\<lparr>\<rparr>* \<langle>Q, v\<rangle>"
      and rel2: "\<langle>Q, v\<rangle> \<equiv>\<lparr>\<rparr>* \<langle>R, y\<rangle>"
      and noTS: "\<not>(P \<in> ProcT \<and> Q \<in> ProcS) \<and> \<not>(Q \<in> ProcT \<and> R \<in> ProcS)"
    shows "\<langle>P, w\<rangle> \<equiv>\<lparr>\<rparr>* \<langle>R, y\<rangle>"
proof (cases "\<lparr>P, w\<rparr>\<mapsto>*\<langle>Q, v\<rangle>")
  assume A1: "\<lparr>P, w\<rparr>\<mapsto>*\<langle>Q, v\<rangle>"
  hence A2: "P \<in> ProcS" and A3: "Q \<in> ProcT"
    using kinds_of_encoded_word(1, 3)[of P w Q v]
    by simp_all
  show "\<langle>P, w\<rangle> \<equiv>\<lparr>\<rparr>* \<langle>R, y\<rangle>"
  proof (cases "\<lparr>Q, v\<rparr>\<mapsto>*\<langle>R, y\<rangle>")
    assume "\<lparr>Q, v\<rparr>\<mapsto>*\<langle>R, y\<rangle>"
    hence "Q \<in> ProcS"
      using kinds_of_encoded_word(1)[of Q v R y]
      by simp
    with A3 have False
      by blast
    thus "\<langle>P, w\<rangle> \<equiv>\<lparr>\<rparr>* \<langle>R, y\<rangle>"
      by simp
  next
    assume B: "\<not>\<lparr>Q, v\<rparr>\<mapsto>*\<langle>R, y\<rangle>"
    show "\<langle>P, w\<rangle> \<equiv>\<lparr>\<rparr>* \<langle>R, y\<rangle>"
    proof (cases "\<lparr>R, y\<rparr>\<mapsto>*\<langle>Q, v\<rangle>")
      assume "\<lparr>R, y\<rparr>\<mapsto>*\<langle>Q, v\<rangle>"
      with noTS have False
        using kinds_of_encoded_word(1, 3)[of R y Q v]
        by simp
      thus "\<langle>P, w\<rangle> \<equiv>\<lparr>\<rparr>* \<langle>R, y\<rangle>"
        by simp
    next
      assume "\<not>\<lparr>R, y\<rparr>\<mapsto>*\<langle>Q, v\<rangle>"
      with rel2 B have C1: "v = y" and C2: "Q \<sim>ST R"
        using related_words_get_condition(1)[of Q v R y]
        by simp_all
      from A1 C1 have C3: "\<lparr>P, w\<rparr>\<mapsto>*\<langle>Q, y\<rangle>"
        by simp
      from A3 C2 have "R \<in> ProcT"
        by blast
      with A2 C3 have "\<lparr>P, w\<rparr>\<mapsto>*\<langle>R, y\<rangle>"
        using encoded_word_exchange_processes[of P w Q y P R]
        by simp
      thus "\<langle>P, w\<rangle> \<equiv>\<lparr>\<rparr>* \<langle>R, y\<rangle>"
        unfolding related_words_def
        by simp
    qed
  qed
next
  assume A: "\<not>\<lparr>P, w\<rparr>\<mapsto>*\<langle>Q, v\<rangle>"
  show "\<langle>P, w\<rangle> \<equiv>\<lparr>\<rparr>* \<langle>R, y\<rangle>"
  proof (cases "\<lparr>Q, v\<rparr>\<mapsto>*\<langle>P, w\<rangle>")
    assume "\<lparr>Q, v\<rparr>\<mapsto>*\<langle>P, w\<rangle>"
    with noTS have False
      using kinds_of_encoded_word(1, 3)[of Q v P w]
      by simp
    thus  "\<langle>P, w\<rangle> \<equiv>\<lparr>\<rparr>* \<langle>R, y\<rangle>"
      by simp
  next
    assume "\<not>\<lparr>Q, v\<rparr>\<mapsto>*\<langle>P, w\<rangle>"
    with rel1 A have A1: "w = v" and A2: "P \<sim>ST Q"
      using related_words_get_condition(1)[of P w Q v]
      by simp_all
    show "\<langle>P, w\<rangle> \<equiv>\<lparr>\<rparr>* \<langle>R, y\<rangle>"
    proof (cases "\<lparr>Q, v\<rparr>\<mapsto>*\<langle>R, y\<rangle>")
      assume B1: "\<lparr>Q, v\<rparr>\<mapsto>*\<langle>R, y\<rangle>"
      with A1 have B2: "\<lparr>Q, w\<rparr>\<mapsto>*\<langle>R, y\<rangle>"
        by simp
      from B1 have "Q \<in> ProcS"
        using kinds_of_encoded_word(1)[of Q v R y]
        by simp
      with A2 have B3: "P \<in> ProcS"
        by blast
      from B1 have "R \<in> ProcT"
        using kinds_of_encoded_word(3)[of Q v R y]
        by simp
      with B2 B3 have "\<lparr>P, w\<rparr>\<mapsto>*\<langle>R, y\<rangle>"
        using encoded_word_exchange_processes[of Q w R y P R]
        by simp
      thus "\<langle>P, w\<rangle> \<equiv>\<lparr>\<rparr>* \<langle>R, y\<rangle>"
        unfolding related_words_def
        by simp
    next
      assume B: "\<not>\<lparr>Q, v\<rparr>\<mapsto>*\<langle>R, y\<rangle>"
      show "\<langle>P, w\<rangle> \<equiv>\<lparr>\<rparr>* \<langle>R, y\<rangle>"
      proof (cases "\<lparr>R, y\<rparr>\<mapsto>*\<langle>Q, v\<rangle>")
        assume "\<lparr>R, y\<rparr>\<mapsto>*\<langle>Q, v\<rangle>"
        with noTS have False
          using kinds_of_encoded_word(1, 3)[of R y Q v]
          by simp
        thus "\<langle>P, w\<rangle> \<equiv>\<lparr>\<rparr>* \<langle>R, y\<rangle>"
          by simp
      next
        assume "\<not>\<lparr>R, y\<rparr>\<mapsto>*\<langle>Q, v\<rangle>"
        with rel2 B have C1: "v = y" and C2: "Q \<sim>ST R"
          using related_words_get_condition(1)[of Q v R y]
          by simp_all
        from A1 C1 have "w = y"
          by simp
        moreover from A2 C2 have "P \<sim>ST R"
          by blast
        ultimately show "\<langle>P, w\<rangle> \<equiv>\<lparr>\<rparr>* \<langle>R, y\<rangle>"
          unfolding related_words_def
          by simp
      qed
    qed
  qed
qed

lemma related_words_trans_no_S_to_T:
  fixes P Q R :: "('procS, 'procT) Proc"
    and w v y :: "('labS, 'labT) Lab list"
  assumes rel1: "\<langle>P, w\<rangle> \<equiv>\<lparr>\<rparr>* \<langle>Q, v\<rangle>"
      and rel2: "\<langle>Q, v\<rangle> \<equiv>\<lparr>\<rparr>* \<langle>R, y\<rangle>"
      and noST: "\<not>(P \<in> ProcS \<and> Q \<in> ProcT) \<and> \<not>(Q \<in> ProcS \<and> R \<in> ProcT)"
    shows "\<langle>P, w\<rangle> \<equiv>\<lparr>\<rparr>* \<langle>R, y\<rangle>"
proof (cases "\<lparr>P, w\<rparr>\<mapsto>*\<langle>Q, v\<rangle>")
  assume A1: "\<lparr>P, w\<rparr>\<mapsto>*\<langle>Q, v\<rangle>"
  with noST have False
    using kinds_of_encoded_word(1, 3)[of P w Q v]
    by simp
  thus "\<langle>P, w\<rangle> \<equiv>\<lparr>\<rparr>* \<langle>R, y\<rangle>"
    by simp
next
  assume A: "\<not>\<lparr>P, w\<rparr>\<mapsto>*\<langle>Q, v\<rangle>"
  show "\<langle>P, w\<rangle> \<equiv>\<lparr>\<rparr>* \<langle>R, y\<rangle>"
  proof (cases "\<lparr>Q, v\<rparr>\<mapsto>*\<langle>P, w\<rangle>")
    assume B1: "\<lparr>Q, v\<rparr>\<mapsto>*\<langle>P, w\<rangle>"
    hence B2: "Q \<in> ProcS" and B3: "P \<in> ProcT"
      using kinds_of_encoded_word(1, 3)[of Q v P w]
      by simp_all
    show "\<langle>P, w\<rangle> \<equiv>\<lparr>\<rparr>* \<langle>R, y\<rangle>"
    proof (cases "\<lparr>Q, v\<rparr>\<mapsto>*\<langle>R, y\<rangle>")
      assume "\<lparr>Q, v\<rparr>\<mapsto>*\<langle>R, y\<rangle>"
      with noST have False
        using kinds_of_encoded_word(1, 3)[of Q v R y]
        by simp
      thus "\<langle>P, w\<rangle> \<equiv>\<lparr>\<rparr>* \<langle>R, y\<rangle>"
        by simp
    next
      assume C: "\<not>\<lparr>Q, v\<rparr>\<mapsto>*\<langle>R, y\<rangle>"
      show "\<langle>P, w\<rangle> \<equiv>\<lparr>\<rparr>* \<langle>R, y\<rangle>"
      proof (cases "\<lparr>R, y\<rparr>\<mapsto>*\<langle>Q, v\<rangle>")
        assume "\<lparr>R, y\<rparr>\<mapsto>*\<langle>Q, v\<rangle>"
        hence "Q \<in> ProcT"
          using kinds_of_encoded_word(3)[of R y Q v]
          by simp
        with B2 have False
          by blast
        thus "\<langle>P, w\<rangle> \<equiv>\<lparr>\<rparr>* \<langle>R, y\<rangle>"
          by simp
      next
        assume "\<not>\<lparr>R, y\<rparr>\<mapsto>*\<langle>Q, v\<rangle>"
        with rel2 C have D1: "v = y" and D2: "Q \<sim>ST R"
          using related_words_get_condition(1)[of Q v R y]
          by simp_all
        from B1 D1 have D3: "\<lparr>Q, y\<rparr>\<mapsto>*\<langle>P, w\<rangle>"
          by simp
        from B2 D2 have "R \<in> ProcS"
          by blast
        with B3 D3 have "\<lparr>R, y\<rparr>\<mapsto>*\<langle>P, w\<rangle>"
          using encoded_word_exchange_processes[of Q y P w R P]
          by simp
        thus "\<langle>P, w\<rangle> \<equiv>\<lparr>\<rparr>* \<langle>R, y\<rangle>"
          unfolding related_words_def
          by simp
      qed
    qed
  next
    assume "\<not>\<lparr>Q, v\<rparr>\<mapsto>*\<langle>P, w\<rangle>"
    with rel1 A have A1: "w = v" and A2: "P \<sim>ST Q"
      using related_words_get_condition(1)[of P w Q v]
      by simp_all
    show "\<langle>P, w\<rangle> \<equiv>\<lparr>\<rparr>* \<langle>R, y\<rangle>"
    proof (cases "\<lparr>Q, v\<rparr>\<mapsto>*\<langle>R, y\<rangle>")
      assume "\<lparr>Q, v\<rparr>\<mapsto>*\<langle>R, y\<rangle>"
      with noST have False
        using kinds_of_encoded_word(1, 3)[of Q v R y]
        by simp
      thus "\<langle>P, w\<rangle> \<equiv>\<lparr>\<rparr>* \<langle>R, y\<rangle>"
        by simp
    next
      assume B: "\<not>\<lparr>Q, v\<rparr>\<mapsto>*\<langle>R, y\<rangle>"
      show "\<langle>P, w\<rangle> \<equiv>\<lparr>\<rparr>* \<langle>R, y\<rangle>"
      proof (cases "\<lparr>R, y\<rparr>\<mapsto>*\<langle>Q, v\<rangle>")
        assume C1: "\<lparr>R, y\<rparr>\<mapsto>*\<langle>Q, v\<rangle>"
        with A1 have C2: "\<lparr>R, y\<rparr>\<mapsto>*\<langle>Q, w\<rangle>"
          by simp
        from C1 have C3: "R \<in> ProcS"
          using kinds_of_encoded_word(1)[of R y Q v]
          by simp
        from C1 have "Q \<in> ProcT"
          using kinds_of_encoded_word(3)[of R y Q v]
          by simp
        with A2 have "P \<in> ProcT"
          by blast
        with C2 C3 have "\<lparr>R, y\<rparr>\<mapsto>*\<langle>P, w\<rangle>"
          using encoded_word_exchange_processes[of R y Q w R P]
          by simp
        thus "\<langle>P, w\<rangle> \<equiv>\<lparr>\<rparr>* \<langle>R, y\<rangle>"
          unfolding related_words_def
          by simp
      next
        assume "\<not>\<lparr>R, y\<rparr>\<mapsto>*\<langle>Q, v\<rangle>"
        with rel2 B have C1: "v = y" and C2: "Q \<sim>ST R"
          using related_words_get_condition(1)[of Q v R y]
          by simp_all
        from A1 C1 have "w = y"
          by simp
        moreover from A2 C2 have "P \<sim>ST R"
          by blast
        ultimately show "\<langle>P, w\<rangle> \<equiv>\<lparr>\<rparr>* \<langle>R, y\<rangle>"
          unfolding related_words_def
          by simp
      qed
    qed
  qed
qed

text \<open>For a labelled semantics the internal label is of special relevance, since it is used to
      define weak notions of steps. We say that the encoding on labels preserves the internal if it
      translates the internal of the source to the internal of the target. It reflects the internal
      if the internal of the target is used as result of the encoding of labels only in the
      translation of the source internal label. Finally, an encoding on labels respects the
      internal if it preserves and reflects the internal.\<close>

abbreviation encL_preserves_internal :: "bool" where
  "encL_preserves_internal \<equiv> \<lblot>\<tau>-Source\<rblot> = \<tau>-Target"

abbreviation encL_reflects_internal :: "bool" where
  "encL_reflects_internal \<equiv> \<forall>\<alpha>. \<lblot>\<alpha>\<rblot> = \<tau>-Target \<longrightarrow> \<alpha> = \<tau>-Source"

abbreviation encL_respects_internal :: "bool" where
  "encL_respects_internal \<equiv> encL_preserves_internal \<and> encL_reflects_internal"

text \<open>An injective label encoding that preserves the internal also respects the internal.\<close>

lemma inj_preserves_is_respects_internal:
  assumes "inj encL"
      and "encL_preserves_internal"
    shows "encL_respects_internal"
  using assms
  unfolding inj_def
  by simp

text \<open>If an encoding relates a source and a target step on internals, then the encoding preserves
      the internal.\<close>

lemma related_labels_preserves_internal:
  fixes P Q :: "('procS, 'procT) Proc"
    and \<alpha> \<beta> :: "('labS, 'labT) Lab"
  assumes rel:  "\<langle>P, \<tau>-STLCal\<rangle> \<equiv>\<lparr>\<rparr> \<langle>Q, \<tau>-STLCal\<rangle>"
      and cond: "\<not>(P \<in> ProcS \<longleftrightarrow> Q \<in> ProcS)"
    shows "encL_preserves_internal"
  using assms
  unfolding related_labels_def encLST_def getSourceLabel_def getTargetLabel_def
  by blast

text \<open>If the encoding of labels preserves the internal, then a source internal is related to an
      internal.\<close>

lemma encL_preserves_internal_implies_source_internal_to_internal:
  fixes P Q :: "('procS, 'procT) Proc"
    and \<beta>   :: "('labS, 'labT) Lab"
  assumes rel:  "\<langle>P, \<tau>-STLCal\<rangle> \<equiv>\<lparr>\<rparr> \<langle>Q, \<beta>\<rangle>"
      and kind: "P \<in> ProcS"
      and pre:  "encL_preserves_internal"
    shows "\<beta> = \<tau>-STLCal"
proof (cases "\<lparr>P, \<tau>-STLCal\<rparr>\<mapsto>\<langle>Q, \<beta>\<rangle>")
  assume "\<lparr>P, \<tau>-STLCal\<rparr>\<mapsto>\<langle>Q, \<beta>\<rangle>"
  then obtain \<alpha>' \<beta>' where A1: "\<alpha>' \<in>SL \<langle>P, \<tau>-STLCal\<rangle>" and A2: "\<beta>' \<in>TL \<langle>Q, \<beta>\<rangle>" and A3: "\<lblot>\<alpha>'\<rblot> = \<beta>'"
    unfolding encLST_def
    by blast
  from A1 have "\<alpha>' = \<tau>-Source"
    unfolding getSourceLabel_def
    by simp
  with pre A3 have "\<beta>' = \<tau>-Target"
    by simp
  with A2 show "\<beta> = \<tau>-STLCal"
    unfolding getTargetLabel_def
    by simp
next
  assume A1: "\<not>\<lparr>P, \<tau>-STLCal\<rparr>\<mapsto>\<langle>Q, \<beta>\<rangle>"
  from kind have "\<not>\<lparr>Q, \<beta>\<rparr>\<mapsto>\<langle>P, \<tau>-STLCal\<rangle>"
    using kinds_of_encoded_label(3)[of Q \<beta> P "\<tau>-STLCal"]
    by blast
  with rel A1 show "\<beta> = \<tau>-STLCal"
    using related_labels_get_condition(1)[of P "\<tau>-STLCal" Q \<beta>]
    by simp
qed

lemma encL_preserves_internal_implies_source_internal_to_internal_right:
  fixes P Q :: "('procS, 'procT) Proc"
    and \<alpha>   :: "('labS, 'labT) Lab"
  assumes rel:  "\<langle>P, \<alpha>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>Q, \<tau>-STLCal\<rangle>"
      and kind: "Q \<in> ProcS"
      and pre:  "encL_preserves_internal"
    shows "\<alpha> = \<tau>-STLCal"
proof (cases "\<lparr>Q, \<tau>-STLCal\<rparr>\<mapsto>\<langle>P, \<alpha>\<rangle>")
  assume "\<lparr>Q, \<tau>-STLCal\<rparr>\<mapsto>\<langle>P, \<alpha>\<rangle>"
  then obtain \<alpha>' \<beta>' where A1: "\<beta>' \<in>SL \<langle>Q, \<tau>-STLCal\<rangle>" and A2: "\<alpha>' \<in>TL \<langle>P, \<alpha>\<rangle>" and A3: "\<lblot>\<beta>'\<rblot> = \<alpha>'"
    unfolding encLST_def
    by blast
  from A1 have "\<beta>' = \<tau>-Source"
    unfolding getSourceLabel_def
    by simp
  with pre A3 have "\<alpha>' = \<tau>-Target"
    by simp
  with A2 show "\<alpha> = \<tau>-STLCal"
    unfolding getTargetLabel_def
    by simp
next
  assume A1: "\<not>\<lparr>Q, \<tau>-STLCal\<rparr>\<mapsto>\<langle>P, \<alpha>\<rangle>"
  from kind have "\<not>\<lparr>P, \<alpha>\<rparr>\<mapsto>\<langle>Q, \<tau>-STLCal\<rangle>"
    using kinds_of_encoded_label(3)[of P \<alpha> Q "\<tau>-STLCal"]
    by blast
  with rel A1 show "\<alpha> = \<tau>-STLCal"
    using related_labels_get_condition(1)[of P \<alpha> Q "\<tau>-STLCal"]
    by simp
qed

text \<open>If the encoding of labels reflects the internal, then a target internal is related to an
      internal.\<close>

lemma encL_reflects_internal_implies_target_internal_to_internal:
  fixes P Q :: "('procS, 'procT) Proc"
    and \<beta>   :: "('labS, 'labT) Lab"
  assumes rel:  "\<langle>P, \<tau>-STLCal\<rangle> \<equiv>\<lparr>\<rparr> \<langle>Q, \<beta>\<rangle>"
      and kind: "P \<in> ProcT"
      and ref:  "encL_reflects_internal"
    shows "\<beta> = \<tau>-STLCal"
proof (cases "\<lparr>Q, \<beta>\<rparr>\<mapsto>\<langle>P, \<tau>-STLCal\<rangle>")
  assume "\<lparr>Q, \<beta>\<rparr>\<mapsto>\<langle>P, \<tau>-STLCal\<rangle>"
  then obtain \<alpha>' \<beta>' where A1: "\<alpha>' \<in>TL \<langle>P, \<tau>-STLCal\<rangle>" and A2: "\<beta>' \<in>SL \<langle>Q, \<beta>\<rangle>" and A3: "\<lblot>\<beta>'\<rblot> = \<alpha>'"
    unfolding encLST_def
    by blast
  from A1 have "\<alpha>' = \<tau>-Target"
    unfolding getTargetLabel_def
    by simp
  with ref A3 have "\<beta>' = \<tau>-Source"
    by simp
  with A2 show "\<beta> = \<tau>-STLCal"
    unfolding getSourceLabel_def
    by simp
next
  assume A1: "\<not>\<lparr>Q, \<beta>\<rparr>\<mapsto>\<langle>P, \<tau>-STLCal\<rangle>"
  from kind have "\<not>\<lparr>P, \<tau>-STLCal\<rparr>\<mapsto>\<langle>Q, \<beta>\<rangle>"
    using kinds_of_encoded_label(1)[of P "\<tau>-STLCal" Q \<beta>]
    by blast
  with rel A1 show "\<beta> = \<tau>-STLCal"
    using related_labels_get_condition(1)[of P "\<tau>-STLCal" Q \<beta>]
    by simp
qed

lemma encL_reflects_internal_implies_target_internal_to_internal_right:
  fixes P Q :: "('procS, 'procT) Proc"
    and \<alpha>   :: "('labS, 'labT) Lab"
  assumes rel:  "\<langle>P, \<alpha>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>Q, \<tau>-STLCal\<rangle>"
      and kind: "Q \<in> ProcT"
      and ref:  "encL_reflects_internal"
    shows "\<alpha> = \<tau>-STLCal"
proof (cases "\<lparr>P, \<alpha>\<rparr>\<mapsto>\<langle>Q, \<tau>-STLCal\<rangle>")
  assume "\<lparr>P, \<alpha>\<rparr>\<mapsto>\<langle>Q, \<tau>-STLCal\<rangle>"
  then obtain \<alpha>' \<beta>' where A1: "\<alpha>' \<in>SL \<langle>P, \<alpha>\<rangle>" and A2: "\<beta>' \<in>TL \<langle>Q, \<tau>-STLCal\<rangle>" and A3: "\<lblot>\<alpha>'\<rblot> = \<beta>'"
    unfolding encLST_def
    by blast
  from A2 have "\<beta>' = \<tau>-Target"
    unfolding getTargetLabel_def
    by simp
  with ref A3 have "\<alpha>' = \<tau>-Source"
    by simp
  with A1 show "\<alpha> = \<tau>-STLCal"
    unfolding getSourceLabel_def
    by simp
next
  assume A1: "\<not>\<lparr>P, \<alpha>\<rparr>\<mapsto>\<langle>Q, \<tau>-STLCal\<rangle>"
  from kind have "\<not>\<lparr>Q, \<tau>-STLCal\<rparr>\<mapsto>\<langle>P, \<alpha>\<rangle>"
    using kinds_of_encoded_label(1)[of Q "\<tau>-STLCal" P \<alpha>]
    by blast
  with rel A1 show "\<alpha> = \<tau>-STLCal"
    using related_labels_get_condition(1)[of P \<alpha> Q "\<tau>-STLCal"]
    by simp
qed

text \<open>If the encoding of labels respects the internal, then the related labels are either both the
      internal or none of them are internal.\<close>

lemma encL_respects_internal_implies_iff_internal:
  fixes P Q :: "('procS, 'procT) Proc"
    and \<alpha> \<beta> :: "('labS, 'labT) Lab"
  assumes "\<langle>P, \<alpha>\<rangle> \<equiv>\<lparr>\<rparr> \<langle>Q, \<beta>\<rangle>"
      and "encL_respects_internal"
    shows "\<alpha> = \<tau>-STLCal \<longleftrightarrow> \<beta> = \<tau>-STLCal"
  using assms
  unfolding encLST_def related_labels_def getSourceLabel_def getTargetLabel_def
  by fastforce

end

end