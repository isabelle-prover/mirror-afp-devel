theory FOR_Semantics
  imports FOR_Certificate
    Lift_Root_Step
    "FOL-Fitting.FOL_Fitting"
begin

section \<open>Semantics of Relations\<close>

definition is_to_trs :: "('f, 'v) trs list \<Rightarrow> ftrs list \<Rightarrow> ('f, 'v) trs" where
  "is_to_trs Rs is = \<Union>(set (map (case_ftrs ((!) Rs) ((`) prod.swap \<circ> (!) Rs)) is))"

primrec eval_gtt_rel :: "('f \<times> nat) set \<Rightarrow> ('f, 'v) trs list \<Rightarrow> ftrs gtt_rel \<Rightarrow> 'f gterm rel" where
  "eval_gtt_rel \<F> Rs (ARoot is) = Restr (grrstep (is_to_trs Rs is)) (\<T>\<^sub>G \<F>)"
| "eval_gtt_rel \<F> Rs (GInv g) = prod.swap ` (eval_gtt_rel \<F> Rs g)"
| "eval_gtt_rel \<F> Rs (AUnion g1 g2) = (eval_gtt_rel \<F> Rs g1) \<union> (eval_gtt_rel \<F> Rs g2)"
| "eval_gtt_rel \<F> Rs (ATrancl g) = (eval_gtt_rel \<F> Rs g)\<^sup>+"
| "eval_gtt_rel \<F> Rs (AComp g1 g2) = (eval_gtt_rel \<F> Rs g1) O (eval_gtt_rel \<F> Rs g2)"
| "eval_gtt_rel \<F> Rs (GTrancl g) = gtrancl_rel \<F> (eval_gtt_rel \<F> Rs g)"
| "eval_gtt_rel \<F> Rs (GComp g1 g2) =  gcomp_rel \<F> (eval_gtt_rel \<F> Rs g1) (eval_gtt_rel \<F> Rs g2)"

primrec eval_rr1_rel :: "('f \<times> nat) set \<Rightarrow> ('f, 'v) trs list \<Rightarrow> ftrs rr1_rel \<Rightarrow> 'f gterm set"
  and eval_rr2_rel :: "('f \<times> nat) set \<Rightarrow> ('f, 'v) trs list \<Rightarrow> ftrs rr2_rel \<Rightarrow> 'f gterm rel" where
  "eval_rr1_rel \<F> Rs R1Terms = (\<T>\<^sub>G \<F>)"
| "eval_rr1_rel \<F> Rs (R1Union R S) = (eval_rr1_rel \<F> Rs R) \<union> (eval_rr1_rel \<F> Rs S)"
| "eval_rr1_rel \<F> Rs (R1Inter R S) = (eval_rr1_rel \<F> Rs R) \<inter> (eval_rr1_rel \<F> Rs S)"
| "eval_rr1_rel \<F> Rs (R1Diff R S) = (eval_rr1_rel \<F> Rs R) - (eval_rr1_rel \<F> Rs S)"
| "eval_rr1_rel \<F> Rs (R1Proj n R) = (case n of 0 \<Rightarrow> fst ` (eval_rr2_rel \<F> Rs R)
                                             | _ \<Rightarrow> snd ` (eval_rr2_rel \<F> Rs R))"
| "eval_rr1_rel \<F> Rs (R1NF is) = NF (Restr (grstep (is_to_trs Rs is)) (\<T>\<^sub>G \<F>)) \<inter> (\<T>\<^sub>G \<F>)"
| "eval_rr1_rel \<F> Rs (R1Inf R) = {s. infinite (eval_rr2_rel \<F> Rs R `` {s})}"
| "eval_rr2_rel \<F> Rs (R2GTT_Rel A W X) = lift_root_step \<F> W X (eval_gtt_rel \<F> Rs A)"
| "eval_rr2_rel \<F> Rs (R2Inv R) = prod.swap ` (eval_rr2_rel \<F> Rs R)"
| "eval_rr2_rel \<F> Rs (R2Union R S) = (eval_rr2_rel \<F> Rs R) \<union> (eval_rr2_rel \<F> Rs S)"
| "eval_rr2_rel \<F> Rs (R2Inter R S) = (eval_rr2_rel \<F> Rs R) \<inter> (eval_rr2_rel \<F> Rs S)"
| "eval_rr2_rel \<F> Rs (R2Diff R S) = (eval_rr2_rel \<F> Rs R) - (eval_rr2_rel \<F> Rs S)"
| "eval_rr2_rel \<F> Rs (R2Comp R S) = (eval_rr2_rel \<F> Rs R) O (eval_rr2_rel \<F> Rs S)"
| "eval_rr2_rel \<F> Rs (R2Diag R) = Id_on (eval_rr1_rel \<F> Rs R)"
| "eval_rr2_rel \<F> Rs (R2Prod R S) = (eval_rr1_rel \<F> Rs R) \<times> (eval_rr1_rel \<F> Rs S)"


subsection \<open>Semantics of Formulas\<close>

fun eval_formula ::  "('f \<times> nat) set \<Rightarrow> ('f, 'v) trs list \<Rightarrow> (nat \<Rightarrow> 'f gterm) \<Rightarrow>
  ftrs formula \<Rightarrow> bool" where
  "eval_formula \<F> Rs \<alpha> (FRR1 r1 x) \<longleftrightarrow> \<alpha> x \<in> eval_rr1_rel \<F> Rs r1"
| "eval_formula \<F> Rs \<alpha> (FRR2 r2 x y) \<longleftrightarrow> (\<alpha> x, \<alpha> y) \<in> eval_rr2_rel \<F> Rs r2"
| "eval_formula \<F> Rs \<alpha> (FAnd fs) \<longleftrightarrow> (\<forall>f \<in> set fs. eval_formula \<F> Rs \<alpha> f)"
| "eval_formula \<F> Rs \<alpha> (FOr fs) \<longleftrightarrow> (\<exists>f \<in> set fs. eval_formula \<F> Rs \<alpha> f)"
| "eval_formula \<F> Rs \<alpha> (FNot f) \<longleftrightarrow> \<not> eval_formula \<F> Rs \<alpha> f"
| "eval_formula \<F> Rs \<alpha> (FExists f) \<longleftrightarrow> (\<exists>z \<in> \<T>\<^sub>G \<F>. eval_formula \<F> Rs (\<alpha>\<langle>0 : z\<rangle>) f)"
| "eval_formula \<F> Rs \<alpha> (FForall f) \<longleftrightarrow> (\<forall>z \<in> \<T>\<^sub>G \<F>. eval_formula \<F> Rs (\<alpha>\<langle>0 : z\<rangle>) f)"

fun formula_arity :: "'trs formula \<Rightarrow> nat" where
  "formula_arity (FRR1 r1 x) = Suc x"
| "formula_arity (FRR2 r2 x y) = max (Suc x) (Suc y)"
| "formula_arity (FAnd fs) = max_list (map formula_arity fs)"
| "formula_arity (FOr fs) = max_list (map formula_arity fs)"
| "formula_arity (FNot f) = formula_arity f"
| "formula_arity (FExists f) = formula_arity f - 1"
| "formula_arity (FForall f) = formula_arity f - 1"



lemma R1NF_reps:
  assumes "funas_trs R \<subseteq> \<F>" "\<forall> t. (term_of_gterm s, term_of_gterm t) \<in> rstep R \<longrightarrow> \<not>funas_gterm t \<subseteq> \<F>"
    and "funas_gterm s \<subseteq> \<F>" "(l, r) \<in> R" "term_of_gterm s = C\<langle>l \<cdot> (\<sigma>  :: 'b \<Rightarrow> ('a, 'b) Term.term)\<rangle>"
  shows False
proof -
  obtain c where w: "funas_term (c :: ('a, 'b) Term.term) \<subseteq> \<F>" "ground c"
    using assms(3) funas_term_of_gterm_conv ground_term_of_gterm by blast
  define \<tau> where "\<tau> x = (if x \<in> vars_term l then \<sigma> x else c)" for x
  from assms(4-) have terms: "term_of_gterm s = C\<langle>l \<cdot> \<tau>\<rangle>" "(C\<langle>l \<cdot> \<tau>\<rangle>, C\<langle>r \<cdot> \<tau>\<rangle>) \<in> rstep R"
    using \<tau>_def by auto (metis term_subst_eq)
  from this(1) have [simp]: "funas_gterm s = funas_term C\<langle>l \<cdot> \<tau>\<rangle>" by (metis funas_term_of_gterm_conv)
  from w assms(1, 3, 4) have [simp]: "funas_term C\<langle>r \<cdot> \<tau>\<rangle> \<subseteq> \<F>" using \<tau>_def
    by (auto simp: funas_trs_def funas_term_subst)
  moreover have "ground C\<langle>r \<cdot> \<tau>\<rangle>" using terms(1) w \<tau>_def
    by (auto intro!: ground_substI) (metis term_of_gterm_ctxt_subst_apply_ground)
  ultimately show ?thesis using assms(2) terms(2)
    by (metis funas_term_of_gterm_conv ground_term_to_gtermD terms(1))
qed


text \<open>The central property we are interested in is satisfiability\<close>

definition formula_satisfiable where
  "formula_satisfiable \<F> Rs f \<longleftrightarrow> (\<exists>\<alpha>. range \<alpha> \<subseteq> \<T>\<^sub>G \<F> \<and> eval_formula \<F> Rs \<alpha> f)"

subsection \<open>Validation\<close>

subsection \<open>Defining properties of @{const gcomp_rel} and @{const gtrancl_rel}\<close>

lemma gcomp_rel_sig:
  assumes "R \<subseteq> \<T>\<^sub>G \<F> \<times> \<T>\<^sub>G \<F>" and "S \<subseteq> \<T>\<^sub>G \<F> \<times> \<T>\<^sub>G \<F>"
  shows "gcomp_rel \<F> R S \<subseteq> \<T>\<^sub>G \<F> \<times> \<T>\<^sub>G \<F>"
  using assms subsetD[OF signature_pres_funas_cl(2)[OF assms(1)]]
  by (auto simp: gcomp_rel_def lift_root_step.simps gmctxt_cl_gmctxtex_onp_conv) (metis refl_onD2 relf_on_gmctxtcl_funas)

lemma gtrancl_rel_sig:
  assumes "R \<subseteq> \<T>\<^sub>G \<F> \<times> \<T>\<^sub>G \<F>"
  shows "gtrancl_rel \<F> R \<subseteq> \<T>\<^sub>G \<F> \<times> \<T>\<^sub>G \<F>"
  using gtrancl_rel_sound[OF assms] by simp

lemma gtrancl_rel:
  assumes "R \<subseteq> \<T>\<^sub>G \<F> \<times> \<T>\<^sub>G \<F>"
  shows "lift_root_step \<F> PAny EStrictParallel (gtrancl_rel \<F> R) = (lift_root_step \<F> PAny ESingle R)\<^sup>+"
  unfolding lift_root_step.simps using gmctxtcl_funas_strict_gtrancl_rel[OF assms] .

lemma gtrancl_rel':
  assumes "R \<subseteq> \<T>\<^sub>G \<F> \<times> \<T>\<^sub>G \<F>"
  shows "lift_root_step \<F> PAny EParallel (gtrancl_rel \<F> R) = Restr ((lift_root_step \<F> PAny ESingle R)\<^sup>*) (\<T>\<^sub>G \<F>)"
  using assms gtrancl_rel[OF assms]
  by (auto simp: lift_root_step_Parallel_conv
      simp flip: reflcl_trancl dest: Restr_simps(5)[OF lift_root_step_sig, THEN subsetD])

text \<open>GTT relation semantics respects the signature\<close>

lemma eval_gtt_rel_sig:
  "eval_gtt_rel \<F> Rs g \<subseteq> \<T>\<^sub>G \<F> \<times> \<T>\<^sub>G \<F>"
proof -
  show ?thesis by (induct g) (auto 0 3 simp: gtrancl_rel_sig gcomp_rel_sig dest: tranclD tranclD2)
qed

text \<open>RR1 and RR2 relation semantics respect the signature\<close>

lemma eval_rr12_rel_sig:
  "eval_rr1_rel \<F> Rs r1 \<subseteq> \<T>\<^sub>G \<F>"
  "eval_rr2_rel \<F> Rs r2 \<subseteq> \<T>\<^sub>G \<F> \<times> \<T>\<^sub>G \<F>"
proof (induct r1 and r2)
  case (R1Inf r2) then show ?case by (auto dest!: infinite_imp_nonempty)
next
  case (R1Proj i r2) then show ?case by (fastforce split: nat.splits)
next
  case (R2GTT_Rel g W X) then show ?case by (simp add: lift_root_step_sig eval_gtt_rel_sig)
qed auto


subsection \<open>Correctness of derived constructions\<close>

lemma R1Fin:
  "eval_rr1_rel \<F> Rs (R1Fin r) = {t \<in> \<T>\<^sub>G \<F>. finite {s. (t, s) \<in> eval_rr2_rel \<F> Rs r}}"
  by (auto simp: R1Fin_def Image_def)

lemma R2Eq:
  "eval_rr2_rel \<F> Rs R2Eq = Id_on (\<T>\<^sub>G \<F>)"
  by (auto simp: \<T>\<^sub>G_funas_gterm_conv R2Eq_def)

lemma R2Reflc:
  "eval_rr2_rel \<F> Rs (R2Reflc r) = eval_rr2_rel \<F> Rs r \<union> Id_on (\<T>\<^sub>G \<F>)"
  "eval_rr2_rel \<F> Rs (R2Reflc r) = Restr ((eval_rr2_rel \<F> Rs r)\<^sup>=) (\<T>\<^sub>G \<F>)"
  using eval_rr12_rel_sig(2)[of \<F> Rs "R2Reflc r"]
  by (auto simp: R2Reflc_def R2Eq)

lemma R2Step:
  "eval_rr2_rel \<F> Rs (R2Step ts) = Restr (grstep (is_to_trs Rs ts)) (\<T>\<^sub>G \<F>)"
  by (auto simp: lift_root_step.simps R2Step_def grstep_lift_root_step grrstep_subst_cl_conv grstepD_grstep_conv grstepD_def)

lemma R2StepEq:
  "eval_rr2_rel \<F> Rs (R2StepEq ts) = Restr ((grstep (is_to_trs Rs ts))\<^sup>=) (\<T>\<^sub>G \<F>)"
  by (auto simp: R2StepEq_def R2Step R2Reflc(2))

lemma R2Steps:
  fixes \<F> Rs ts defines "R \<equiv> Restr (grstep (is_to_trs Rs ts)) (\<T>\<^sub>G \<F>)"
  shows "eval_rr2_rel \<F> Rs (R2Steps ts) = R\<^sup>+"
  by (simp add: R2Steps_def GSteps_def R_def gtrancl_rel grstep_lift_root_step)
     (metis FOR_Semantics.gtrancl_rel Sigma_cong grstep_lift_root_step inf.cobounded2 lift_root_Any_EStrict_eq)

lemma R2StepsEq:
  fixes \<F> Rs ts defines "R \<equiv> Restr (grstep (is_to_trs Rs ts)) (\<T>\<^sub>G \<F>)"
  shows "eval_rr2_rel \<F> Rs (R2StepsEq ts) = Restr (R\<^sup>*) (\<T>\<^sub>G \<F>)"
  using R2Steps[of \<F> Rs ts]
  by (simp add: R2StepsEq_def R2Steps_def lift_root_step_Parallel_conv Int_Un_distrib2 R_def Restr_simps flip: reflcl_trancl)

lemma R2StepsNF:
  fixes \<F> Rs ts defines "R \<equiv> Restr (grstep (is_to_trs Rs ts)) (\<T>\<^sub>G \<F>)"
  shows "eval_rr2_rel \<F> Rs (R2StepsNF ts) = Restr (R\<^sup>* \<inter> UNIV \<times> NF R) (\<T>\<^sub>G \<F>)"
  using R2StepsEq[of \<F> Rs ts]
  by (auto simp: R2StepsNF_def R2StepsEq_def R_def)

lemma R2ParStep:
  "eval_rr2_rel \<F> Rs (R2ParStep ts) = Restr (gpar_rstep (is_to_trs Rs ts)) (\<T>\<^sub>G \<F>)"
  by (simp add: R2ParStep_def gar_rstep_lift_root_step)

lemma R2RootStep:
  "eval_rr2_rel \<F> Rs (R2RootStep ts) = Restr (grrstep (is_to_trs Rs ts)) (\<T>\<^sub>G \<F>)"
  by (simp add: R2RootStep_def lift_root_step.simps)

lemma R2RootStepEq:
  "eval_rr2_rel \<F> Rs (R2RootStepEq ts) = Restr ((grrstep (is_to_trs Rs ts))\<^sup>=) (\<T>\<^sub>G \<F>)"
  by (auto simp: R2RootStepEq_def R2RootStep R2Reflc(2))

lemma R2RootSteps:
  fixes \<F> Rs ts defines "R \<equiv> Restr (grrstep (is_to_trs Rs ts)) (\<T>\<^sub>G \<F>)"
  shows "eval_rr2_rel \<F> Rs (R2RootSteps ts) = R\<^sup>+"
  by (simp add: R2RootSteps_def R_def lift_root_step.simps)

lemma R2RootStepsEq:
  fixes \<F> Rs ts defines "R \<equiv> Restr (grrstep (is_to_trs Rs ts)) (\<T>\<^sub>G \<F>)"
  shows "eval_rr2_rel \<F> Rs (R2RootStepsEq ts) = Restr (R\<^sup>*) (\<T>\<^sub>G \<F>)"
  by (auto simp: R2RootStepsEq_def R2Reflc_def R2RootSteps R_def R2Eq_def Int_Un_distrib2 Restr_simps simp flip: reflcl_trancl)

lemma R2NonRootStep:
  "eval_rr2_rel \<F> Rs (R2NonRootStep ts) = Restr (gnrrstep (is_to_trs Rs ts)) (\<T>\<^sub>G \<F>)"
  by (simp add: R2NonRootStep_def grrstep_lift_root_gnrrstep)

lemma R2NonRootStepEq:
  "eval_rr2_rel \<F> Rs (R2NonRootStepEq ts) = Restr ((gnrrstep (is_to_trs Rs ts))\<^sup>=) (\<T>\<^sub>G \<F>)"
  by (auto simp: R2NonRootStepEq_def R2Reflc_def R2Eq_def R2NonRootStep Int_Un_distrib2)

lemma R2NonRootSteps:
  fixes \<F> Rs ts defines "R \<equiv> Restr (gnrrstep (is_to_trs Rs ts)) (\<T>\<^sub>G \<F>)"
  shows "eval_rr2_rel \<F> Rs (R2NonRootSteps ts) = R\<^sup>+"
  apply (simp add: lift_root_step.simps gnrrstepD_gnrrstep_conv gnrrstepD_def
    grrstep_subst_cl_conv R2NonRootSteps_def R_def GSteps_def lift_root_step_Parallel_conv)
  apply (intro gmctxtex_funas_nroot_strict_gtrancl_rel)
  by simp

lemma R2NonRootStepsEq:
  fixes \<F> Rs ts defines "R \<equiv> Restr (gnrrstep (is_to_trs Rs ts)) (\<T>\<^sub>G \<F>)"
  shows "eval_rr2_rel \<F> Rs (R2NonRootStepsEq ts) = Restr (R\<^sup>*) (\<T>\<^sub>G \<F>)"
  using R2NonRootSteps[of \<F> Rs ts]
  by (simp add: R2NonRootSteps_def R2NonRootStepsEq_def lift_root_step_Parallel_conv
    R_def Int_Un_distrib2 Restr_simps flip: reflcl_trancl)

lemma converse_to_prod_swap:
  "R\<inverse> = prod.swap ` R"
  by auto

lemma R2Meet:
  fixes \<F> Rs ts defines "R \<equiv> Restr (grstep (is_to_trs Rs ts)) (\<T>\<^sub>G \<F>)"
  shows "eval_rr2_rel \<F> Rs (R2Meet ts) = Restr ((R\<inverse>)\<^sup>* O R\<^sup>*) (\<T>\<^sub>G \<F>)"
  apply (simp add: R2Meet_def R_def GSteps_def converse_to_prod_swap gcomp_rel[folded lift_root_step.simps] gtrancl_rel' swap_lift_root_step grstep_lift_root_step)
  apply (simp add: Restr_simps converse_Int converse_Un converse_Times Int_Un_distrib2 flip: reflcl_trancl trancl_converse converse_to_prod_swap)
  done

lemma R2Join:
  fixes \<F> Rs ts defines "R \<equiv> Restr (grstep (is_to_trs Rs ts)) (\<T>\<^sub>G \<F>)"
  shows "eval_rr2_rel \<F> Rs (R2Join ts) = Restr (R\<^sup>* O (R\<inverse>)\<^sup>*) (\<T>\<^sub>G \<F>)"
  apply (simp add: R2Join_def R_def GSteps_def converse_to_prod_swap  gcomp_rel[folded lift_root_step.simps] gtrancl_rel' swap_lift_root_step grstep_lift_root_step)
  apply (simp add: Restr_simps converse_to_prod_swap[symmetric] converse_Int converse_Un converse_Times Int_Un_distrib2 flip: reflcl_trancl trancl_converse)
  done

end