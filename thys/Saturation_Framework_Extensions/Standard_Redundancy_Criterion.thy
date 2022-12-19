(*  Title:       Counterexample-Reducing Inference Systems and the Standard Redundancy Criterion
    Author:      Jasmin Blanchette <j.c.blanchette at vu.nl>, 2014, 2017, 2020
    Author:      Dmitriy Traytel <traytel at inf.ethz.ch>, 2014
    Author:      Anders Schlichtkrull <andschl at dtu.dk>, 2017
    Author:      Martin Desharnais <desharnais at mpi-inf.mpg.de>, 2021
*)

section \<open>Counterexample-Reducing Inference Systems and the Standard Redundancy Criterion\<close>

theory Standard_Redundancy_Criterion
  imports
    Saturation_Framework.Calculus
    "HOL-Library.Multiset_Order"
begin

text \<open>
The standard redundancy criterion can be defined uniformly for all inference systems equipped with
a compact consequence relation. The essence of the refutational completeness argument can be carried
out abstractly for counterexample-reducing inference systems, which enjoy a ``smallest
counterexample'' property. This material is partly based on Section 4.2 of Bachmair and Ganzinger's
\emph{Handbook} chapter, but adapted to the saturation framework of Waldmann et al.
\<close>

subsection \<open>Counterexample-Reducing Inference Systems\<close>

abbreviation main_prem_of :: "'f inference \<Rightarrow> 'f" where
  "main_prem_of \<iota> \<equiv> last (prems_of \<iota>)"

abbreviation side_prems_of :: "'f inference \<Rightarrow> 'f list" where
  "side_prems_of \<iota> \<equiv> butlast (prems_of \<iota>)"

lemma set_prems_of:
  "set (prems_of \<iota>) = (if prems_of \<iota> = [] then {} else {main_prem_of \<iota>} \<union> set (side_prems_of \<iota>))"
  by clarsimp (metis Un_insert_right append_Nil2 append_butlast_last_id list.set(2) set_append)

locale counterex_reducing_inference_system = inference_system Inf + consequence_relation
  for Inf :: "'f inference set" +
  fixes
    I_of :: "'f set \<Rightarrow> 'f set" and
    less :: "'f \<Rightarrow> 'f \<Rightarrow> bool" (infix "\<prec>" 50)
  assumes
    wfP_less: "wfP (\<prec>)" and
    Inf_counterex_reducing:
      "N \<inter> Bot = {} \<Longrightarrow> D \<in> N \<Longrightarrow> \<not> I_of N \<Turnstile> {D} \<Longrightarrow>
      (\<And>C. C \<in> N \<Longrightarrow> \<not> I_of N \<Turnstile> {C} \<Longrightarrow> D \<prec> C \<or> D = C) \<Longrightarrow>
      \<exists>\<iota> \<in> Inf. prems_of \<iota> \<noteq> [] \<and> main_prem_of \<iota> = D \<and> set (side_prems_of \<iota>) \<subseteq> N \<and>
        I_of N \<Turnstile> set (side_prems_of \<iota>) \<and> \<not> I_of N \<Turnstile> {concl_of \<iota>} \<and> concl_of \<iota> \<prec> D"

begin

lemma ex_min_counterex:
  fixes N :: "'f set"
  assumes "\<not> I \<Turnstile> N"
  shows "\<exists>C \<in> N. \<not> I \<Turnstile> {C} \<and> (\<forall>D \<in> N. D \<prec> C \<longrightarrow> I \<Turnstile> {D})"
proof -
  obtain C where
    "C \<in> N" and "\<not> I \<Turnstile> {C}"
    using assms all_formulas_entailed by blast
  then have c_in: "C \<in> {C \<in> N. \<not> I \<Turnstile> {C}}"
    by blast
  show ?thesis
    using wfP_eq_minimal[THEN iffD1, rule_format, OF wfP_less c_in] by blast
qed

end

text \<open>
Theorem 4.4 (generalizes Theorems 3.9 and 3.16):
\<close>

locale counterex_reducing_inference_system_with_trivial_redundancy =
  counterex_reducing_inference_system _ _ Inf + calculus _ Inf _ "\<lambda>_. {}" "\<lambda>_. {}"
  for Inf :: "'f inference set" +
  assumes less_total: "\<And>C D. C \<noteq> D \<Longrightarrow> C \<prec> D \<or> D \<prec> C"
begin

theorem saturated_model:
  assumes
    satur: "saturated N" and
    bot_ni_n: "N \<inter> Bot = {}"
  shows "I_of N \<Turnstile> N"
proof (rule ccontr)
  assume "\<not> I_of N \<Turnstile> N"
  then obtain D :: 'f where
    d_in_n: "D \<in> N" and
    d_cex: "\<not> I_of N \<Turnstile> {D}" and
    d_min: "\<And>C. C \<in> N \<Longrightarrow> C \<prec> D \<Longrightarrow> I_of N \<Turnstile> {C}"
    by (meson ex_min_counterex)
  then obtain \<iota> :: "'f inference" where
    \<iota>_inf: "\<iota> \<in> Inf" and
    concl_cex: "\<not> I_of N \<Turnstile> {concl_of \<iota>}" and
    concl_lt_d: "concl_of \<iota> \<prec> D"
    using Inf_counterex_reducing[OF bot_ni_n] less_total
    by force
  have "concl_of \<iota> \<in> N"
    using \<iota>_inf Red_I_of_Inf_to_N by blast
  then show False
    using concl_cex concl_lt_d d_min by blast
qed

text \<open>
An abstract version of Corollary 3.10 does not hold without some conditions, according to Nitpick:
\<close>

corollary saturated_complete:
  assumes
    satur: "saturated N" and
    unsat: "N \<Turnstile> Bot"
  shows "N \<inter> Bot \<noteq> {}"
  oops

end


subsection \<open>Compactness\<close>

locale concl_compact_consequence_relation = consequence_relation +
  assumes
    entails_concl_compact: "finite EE \<Longrightarrow> CC \<Turnstile> EE \<Longrightarrow> \<exists>CC' \<subseteq> CC. finite CC' \<and> CC' \<Turnstile> EE"
begin

lemma entails_concl_compact_union:
  assumes
    fin_e: "finite EE" and
    cd_ent: "CC \<union> DD \<Turnstile> EE"
  shows "\<exists>CC' \<subseteq> CC. finite CC' \<and> CC' \<union> DD \<Turnstile> EE"
proof -
  obtain CCDD' where
    cd1_fin: "finite CCDD'" and
    cd1_sub: "CCDD' \<subseteq> CC \<union> DD" and
    cd1_ent: "CCDD' \<Turnstile> EE"
    using entails_concl_compact[OF fin_e cd_ent] by blast

  define CC' where
    "CC' = CCDD' - DD"
  have "CC' \<subseteq> CC"
    unfolding CC'_def using cd1_sub by blast
  moreover have "finite CC'"
    unfolding CC'_def using cd1_fin by blast
  moreover have "CC' \<union> DD \<Turnstile> EE"
    unfolding CC'_def using cd1_ent
    by (metis Un_Diff_cancel2 Un_upper1 entails_trans subset_entailed)
  ultimately show ?thesis
    by blast
qed

end


subsection \<open>The Finitary Standard Redundancy Criterion\<close>

locale finitary_standard_formula_redundancy =
  consequence_relation Bot "(\<Turnstile>)"
  for
    Bot :: "'f set" and
    entails :: "'f set \<Rightarrow> 'f set \<Rightarrow> bool" (infix "\<Turnstile>" 50) +
  fixes
    less :: "'f \<Rightarrow> 'f \<Rightarrow> bool" (infix "\<prec>" 50)
  assumes
    transp_less: "transp (\<prec>)" and
    wfP_less: "wfP (\<prec>)"
begin

definition Red_F :: "'f set \<Rightarrow> 'f set" where
  "Red_F N = {C. \<exists>DD \<subseteq> N. finite DD \<and> DD \<Turnstile> {C} \<and> (\<forall>D \<in> DD. D \<prec> C)}"

text \<open>
The following results correspond to Lemma 4.5. The lemma \<open>wlog_non_Red_F\<close> generalizes the core of
the argument.
\<close>

lemma Red_F_of_subset: "N \<subseteq> N' \<Longrightarrow> Red_F N \<subseteq> Red_F N'"
  unfolding Red_F_def by fast

lemma wlog_non_Red_F:
  assumes
    dd0_fin: "finite DD0" and
    dd0_sub: "DD0 \<subseteq> N" and
    dd0_ent: "DD0 \<union> CC \<Turnstile> {E}" and
    dd0_lt: "\<forall>D' \<in> DD0. D' \<prec> D"
  shows "\<exists>DD \<subseteq> N - Red_F N. finite DD \<and> DD \<union> CC \<Turnstile> {E} \<and> (\<forall>D' \<in> DD. D' \<prec> D)"
proof -
  have mset_DD0_in: "mset_set DD0 \<in>
    {DD. set_mset DD \<subseteq> N \<and> set_mset DD \<union> CC \<Turnstile> {E} \<and> (\<forall>D' \<in> set_mset DD. D' \<prec> D)}"
    using assms finite_set_mset_mset_set by simp
  obtain DD :: "'f multiset" where
    dd_subs_n: "set_mset DD \<subseteq> N" and
    ddcc_ent_e: "set_mset DD \<union> CC \<Turnstile> {E}" and
    dd_lt_d: "\<forall>D' \<in># DD. D' \<prec> D" and
    d_min: "\<forall>y. multp (\<prec>) y DD \<longrightarrow>
      y \<notin> {DD. set_mset DD \<subseteq> N \<and> set_mset DD \<union> CC \<Turnstile> {E} \<and> (\<forall>D'\<in>#DD. D' \<prec> D)}"
    using wfP_eq_minimal[THEN iffD1, rule_format, OF wfP_less[THEN wfP_multp] mset_DD0_in]
    by blast

  have "\<forall>Da \<in># DD. Da \<notin> Red_F N"
  proof clarify
    fix Da :: 'f
    assume
      da_in_dd: "Da \<in># DD" and
      da_rf: "Da \<in> Red_F N"

    obtain DDa0 :: "'f set" where
      dda0_subs_n: "DDa0 \<subseteq> N" and
      dda0_fin: "finite DDa0" and
      dda0_ent_da: "DDa0 \<Turnstile> {Da}" and
      dda0_lt_da: "\<forall>D \<in> DDa0. D \<prec> Da"
      using da_rf unfolding Red_F_def mem_Collect_eq
      by blast

    define DDa :: "'f multiset" where
      "DDa = DD - {#Da#} + mset_set DDa0"

    have "set_mset DDa \<subseteq> N"
      unfolding DDa_def using dd_subs_n dda0_subs_n finite_set_mset_mset_set[OF dda0_fin]
      by (smt (verit, best) contra_subsetD in_diffD subsetI union_iff)
    moreover have "set_mset DDa \<union> CC \<Turnstile> {E}"
    proof (rule entails_trans_strong[of _ "{Da}"])
      show "set_mset DDa \<union> CC \<Turnstile> {Da}"
        unfolding DDa_def set_mset_union finite_set_mset_mset_set[OF dda0_fin]
        by (rule entails_trans[OF _ dda0_ent_da]) (auto intro: subset_entailed)
    next
      have H: "set_mset (DD - {#Da#} + mset_set DDa0) \<union> CC \<union> {Da} =
        set_mset (DD + mset_set DDa0) \<union> CC"
        by (smt (verit) Un_insert_left Un_insert_right da_in_dd insert_DiffM
            set_mset_add_mset_insert set_mset_union sup_bot.right_neutral)
      show "set_mset DDa \<union> CC \<union> {Da} \<Turnstile> {E}"
        unfolding DDa_def H
        by (rule entails_trans[OF _ ddcc_ent_e]) (auto intro: subset_entailed)
    qed
    moreover have "\<forall>D' \<in># DDa. D' \<prec> D"
      using dd_lt_d dda0_lt_da da_in_dd unfolding DDa_def
      using transp_less[THEN transpD]
      using finite_set_mset_mset_set[OF dda0_fin]
      by (metis insert_DiffM2 union_iff)
    moreover have "multp (\<prec>) DDa DD"
      unfolding DDa_def multp_eq_multp\<^sub>D\<^sub>M[OF wfP_imp_asymp[OF wfP_less] transp_less] multp\<^sub>D\<^sub>M_def
      using finite_set_mset_mset_set[OF dda0_fin]
      by (metis da_in_dd dda0_lt_da mset_subset_eq_single multi_self_add_other_not_self
          union_single_eq_member)
    ultimately show False
      using d_min by (auto intro!: antisym)
  qed
  then show ?thesis
    using dd_subs_n ddcc_ent_e dd_lt_d by blast
qed

lemma Red_F_imp_ex_non_Red_F:
  assumes c_in: "C \<in> Red_F N"
  shows "\<exists>CC \<subseteq> N - Red_F N. finite CC \<and> CC \<Turnstile> {C} \<and> (\<forall>C' \<in> CC. C' \<prec> C)"
proof -
  obtain DD :: "'f set" where
    dd_fin: "finite DD" and
    dd_sub: "DD \<subseteq> N" and
    dd_ent: "DD \<Turnstile> {C}" and
    dd_lt: "\<forall>D \<in> DD. D \<prec> C"
    using c_in[unfolded Red_F_def] by fast
  show ?thesis
    by (rule wlog_non_Red_F[of "DD" N "{}" C C, simplified, OF dd_fin dd_sub dd_ent dd_lt])
qed

lemma Red_F_subs_Red_F_diff_Red_F: "Red_F N \<subseteq> Red_F (N - Red_F N)"
proof
  fix C
  assume c_rf: "C \<in> Red_F N"
  then obtain CC :: "'f set" where
    cc_subs: "CC \<subseteq> N - Red_F N" and
    cc_fin: "finite CC" and
    cc_ent_c: "CC \<Turnstile> {C}" and
    cc_lt_c: "\<forall>C' \<in> CC. C' \<prec> C"
    using Red_F_imp_ex_non_Red_F[of C N] by blast
  have "\<forall>D \<in> CC. D \<notin> Red_F N"
    using cc_subs by fast
  then have cc_nr:
    "\<forall>C \<in> CC. \<forall>DD \<subseteq> N. finite DD \<and> DD \<Turnstile> {C} \<longrightarrow> (\<exists>D \<in> DD. \<not> D \<prec> C)"
    unfolding Red_F_def by simp
  have "CC \<subseteq> N"
    using cc_subs by auto
  then have "CC \<subseteq> N - {C. \<exists>DD \<subseteq> N. finite DD \<and> DD \<Turnstile> {C} \<and> (\<forall>D \<in> DD. D \<prec> C)}"
    using cc_nr by blast
  then show "C \<in> Red_F (N - Red_F N)"
    using cc_fin cc_ent_c cc_lt_c unfolding Red_F_def by blast
qed

lemma Red_F_eq_Red_F_diff_Red_F: "Red_F N = Red_F (N - Red_F N)"
  by (simp add: Red_F_of_subset Red_F_subs_Red_F_diff_Red_F set_eq_subset)

text \<open>
The following results correspond to Lemma 4.6.
\<close>

lemma Red_F_of_Red_F_subset: "N' \<subseteq> Red_F N \<Longrightarrow> Red_F N \<subseteq> Red_F (N - N')"
  by (metis Diff_mono Red_F_eq_Red_F_diff_Red_F Red_F_of_subset order_refl)

lemma Red_F_model: "M \<Turnstile> N - Red_F N \<Longrightarrow> M \<Turnstile> N"
  by (metis (no_types) DiffI Red_F_imp_ex_non_Red_F entail_set_all_formulas entails_trans
      subset_entailed)

lemma Red_F_Bot: "B \<in> Bot \<Longrightarrow> N \<Turnstile> {B} \<Longrightarrow> N - Red_F N \<Turnstile> {B}"
  using Red_F_model entails_trans subset_entailed by blast

end

locale calculus_with_finitary_standard_redundancy =
  inference_system Inf + finitary_standard_formula_redundancy Bot "(\<Turnstile>)" "(\<prec>)"
  for
    Inf :: "'f inference set" and
    Bot :: "'f set" and
    entails :: "'f set \<Rightarrow> 'f set \<Rightarrow> bool" (infix "\<Turnstile>" 50) and
    less :: "'f \<Rightarrow> 'f \<Rightarrow> bool" (infix "\<prec>" 50) +
  assumes
    Inf_has_prem: "\<iota> \<in> Inf \<Longrightarrow> prems_of \<iota> \<noteq> []" and
    Inf_reductive: "\<iota> \<in> Inf \<Longrightarrow> concl_of \<iota> \<prec> main_prem_of \<iota>"
begin

definition redundant_infer :: "'f set \<Rightarrow> 'f inference \<Rightarrow> bool" where
  "redundant_infer N \<iota> \<longleftrightarrow>
   (\<exists>DD \<subseteq> N. finite DD \<and> DD \<union> set (side_prems_of \<iota>) \<Turnstile> {concl_of \<iota>} \<and> (\<forall>D \<in> DD. D \<prec> main_prem_of \<iota>))"

definition Red_I :: "'f set \<Rightarrow> 'f inference set" where
  "Red_I N = {\<iota> \<in> Inf. redundant_infer N \<iota>}"

text \<open>
The following results correspond to Lemma 4.6. It also uses @{thm [source] wlog_non_Red_F}.
\<close>

lemma Red_I_of_subset: "N \<subseteq> N' \<Longrightarrow> Red_I N \<subseteq> Red_I N'"
  unfolding Red_I_def redundant_infer_def by auto

lemma Red_I_subs_Red_I_diff_Red_F: "Red_I N \<subseteq> Red_I (N - Red_F N)"
proof
  fix \<iota>
  assume \<iota>_ri: "\<iota> \<in> Red_I N"
  define CC :: "'f set" where
    "CC = set (side_prems_of \<iota>)"
  define D :: 'f where
    "D = main_prem_of \<iota>"
  define E :: 'f where
    "E = concl_of \<iota>"
  obtain DD :: "'f set" where
    dd_fin: "finite DD" and
    dd_sub: "DD \<subseteq> N" and
    dd_ent: "DD \<union> CC \<Turnstile> {E}" and
    dd_lt_d: "\<forall>C \<in> DD. C \<prec> D"
    using \<iota>_ri unfolding Red_I_def redundant_infer_def CC_def D_def E_def by blast
  obtain DDa :: "'f set" where
    "DDa \<subseteq> N - Red_F N" and "finite DDa" and "DDa \<union> CC \<Turnstile> {E}" and "\<forall>D' \<in> DDa. D' \<prec> D"
    using wlog_non_Red_F[OF dd_fin dd_sub dd_ent dd_lt_d] by blast
  then show "\<iota> \<in> Red_I (N - Red_F N)"
    using \<iota>_ri unfolding Red_I_def redundant_infer_def CC_def D_def E_def by blast
qed

lemma Red_I_eq_Red_I_diff_Red_F: "Red_I N = Red_I (N - Red_F N)"
  by (metis Diff_subset Red_I_of_subset Red_I_subs_Red_I_diff_Red_F subset_antisym)

lemma Red_I_to_Inf: "Red_I N \<subseteq> Inf"
  unfolding Red_I_def by blast

lemma Red_I_of_Red_F_subset: "N' \<subseteq> Red_F N \<Longrightarrow> Red_I N \<subseteq> Red_I (N - N')"
  by (metis Diff_mono Red_I_eq_Red_I_diff_Red_F Red_I_of_subset order_refl)

lemma Red_I_of_Inf_to_N:
  assumes
    in_\<iota>: "\<iota> \<in> Inf" and
    concl_in: "concl_of \<iota> \<in> N"
  shows "\<iota> \<in> Red_I N"
proof -
  have "redundant_infer N \<iota>"
    unfolding redundant_infer_def
    by (rule exI[where x = "{concl_of \<iota>}"])
      (simp add: Inf_reductive[OF in_\<iota>] subset_entailed concl_in)
  then show "\<iota> \<in> Red_I N"
    by (simp add: Red_I_def in_\<iota>)
qed

text \<open>
The following corresponds to Theorems 4.7 and 4.8:
\<close>

sublocale calculus Bot Inf "(\<Turnstile>)" Red_I Red_F
  by (unfold_locales, fact Red_I_to_Inf, fact Red_F_Bot, fact Red_F_of_subset,
      fact Red_I_of_subset, fact Red_F_of_Red_F_subset, fact Red_I_of_Red_F_subset,
      fact Red_I_of_Inf_to_N)

end


subsection \<open>The Standard Redundancy Criterion\<close>

locale standard_formula_redundancy =
  concl_compact_consequence_relation Bot "(\<Turnstile>)"
  for
    Bot :: "'f set" and
    entails :: "'f set \<Rightarrow> 'f set \<Rightarrow> bool" (infix "\<Turnstile>" 50) +
  fixes
    less :: "'f \<Rightarrow> 'f \<Rightarrow> bool" (infix "\<prec>" 50)
  assumes
    transp_less: "transp (\<prec>)" and
    wfP_less: "wfP (\<prec>)"
begin

definition Red_F :: "'f set \<Rightarrow> 'f set" where
  "Red_F N = {C. \<exists>DD \<subseteq> N. DD \<Turnstile> {C} \<and> (\<forall>D \<in> DD. D \<prec> C)}"

text \<open>
Compactness of @{term "(\<Turnstile>)"} implies that @{const Red_F} is equivalent to its finitary
  counterpart.
\<close>

interpretation fin_std_red_F: finitary_standard_formula_redundancy Bot "(\<Turnstile>)" "(\<prec>)"
  using transp_less asymp_on_less wfP_less by unfold_locales

lemma Red_F_conv: "Red_F = fin_std_red_F.Red_F"
proof (intro ext)
  fix N
  show "Red_F N = fin_std_red_F.Red_F N"
    unfolding Red_F_def fin_std_red_F.Red_F_def
    using entails_concl_compact
    by (smt (verit, best) Collect_cong finite.emptyI finite_insert subset_eq)
qed

text \<open>
The results from @{locale finitary_standard_formula_redundancy} can now be lifted.

The following results correspond to Lemma 4.5.
\<close>

lemma Red_F_of_subset: "N \<subseteq> N' \<Longrightarrow> Red_F N \<subseteq> Red_F N'"
  unfolding Red_F_conv
  by (rule fin_std_red_F.Red_F_of_subset)

lemma Red_F_imp_ex_non_Red_F: "C \<in> Red_F N \<Longrightarrow> \<exists>CC \<subseteq> N - Red_F N. CC \<Turnstile> {C} \<and> (\<forall>C' \<in> CC. C' \<prec> C)"
  unfolding Red_F_conv
  using fin_std_red_F.Red_F_imp_ex_non_Red_F by meson

lemma Red_F_subs_Red_F_diff_Red_F: "Red_F N \<subseteq> Red_F (N - Red_F N)"
  unfolding Red_F_conv
  by (rule fin_std_red_F.Red_F_subs_Red_F_diff_Red_F)

lemma Red_F_eq_Red_F_diff_Red_F: "Red_F N = Red_F (N - Red_F N)"
  unfolding Red_F_conv
  by (rule fin_std_red_F.Red_F_eq_Red_F_diff_Red_F)

text \<open>
The following results correspond to Lemma 4.6.
\<close>

lemma Red_F_of_Red_F_subset: "N' \<subseteq> Red_F N \<Longrightarrow> Red_F N \<subseteq> Red_F (N - N')"
  unfolding Red_F_conv
  by (rule fin_std_red_F.Red_F_of_Red_F_subset)

lemma Red_F_model: "M \<Turnstile> N - Red_F N \<Longrightarrow> M \<Turnstile> N"
  unfolding Red_F_conv
  by (rule fin_std_red_F.Red_F_model)

lemma Red_F_Bot: "B \<in> Bot \<Longrightarrow> N \<Turnstile> {B} \<Longrightarrow> N - Red_F N \<Turnstile> {B}"
  unfolding Red_F_conv
  by (rule fin_std_red_F.Red_F_Bot)

end

locale calculus_with_standard_redundancy =
  inference_system Inf + standard_formula_redundancy Bot "(\<Turnstile>)" "(\<prec>)"
  for
    Inf :: "'f inference set" and
    Bot :: "'f set" and
    entails :: "'f set \<Rightarrow> 'f set \<Rightarrow> bool" (infix "\<Turnstile>" 50) and
    less :: "'f \<Rightarrow> 'f \<Rightarrow> bool" (infix "\<prec>" 50) +
  assumes
    Inf_has_prem: "\<iota> \<in> Inf \<Longrightarrow> prems_of \<iota> \<noteq> []" and
    Inf_reductive: "\<iota> \<in> Inf \<Longrightarrow> concl_of \<iota> \<prec> main_prem_of \<iota>"
begin

definition redundant_infer :: "'f set \<Rightarrow> 'f inference \<Rightarrow> bool" where
  "redundant_infer N \<iota> \<longleftrightarrow>
   (\<exists>DD \<subseteq> N. DD \<union> set (side_prems_of \<iota>) \<Turnstile> {concl_of \<iota>} \<and> (\<forall>D \<in> DD. D \<prec> main_prem_of \<iota>))"

definition Red_I :: "'f set \<Rightarrow> 'f inference set" where
  "Red_I N = {\<iota> \<in> Inf. redundant_infer N \<iota>}"

text \<open>
Compactness of @{term "(\<Turnstile>)"} implies that @{const Red_I} is equivalent to its finitary counterpart.
\<close>

interpretation fin_std_red: calculus_with_finitary_standard_redundancy Inf Bot "(\<Turnstile>)"
  using transp_less asymp_on_less wfP_less Inf_has_prem Inf_reductive by unfold_locales

lemma redundant_infer_conv: "redundant_infer = fin_std_red.redundant_infer"
proof (intro ext)
  fix N \<iota>
  show "redundant_infer N \<iota> \<longleftrightarrow> fin_std_red.redundant_infer N \<iota>"
    unfolding redundant_infer_def fin_std_red.redundant_infer_def
    using entails_concl_compact_union
    by (smt (verit, ccfv_threshold) finite.emptyI finite_insert subset_eq)
qed

lemma Red_I_conv: "Red_I = fin_std_red.Red_I"
  unfolding Red_I_def fin_std_red.Red_I_def
  unfolding redundant_infer_conv
  by (rule refl)

text \<open>
The results from @{locale calculus_with_finitary_standard_redundancy} can now be lifted.

The following results correspond to Lemma 4.6.
\<close>

lemma Red_I_of_subset: "N \<subseteq> N' \<Longrightarrow> Red_I N \<subseteq> Red_I N'"
  unfolding Red_I_conv
  by (rule fin_std_red.Red_I_of_subset)

lemma Red_I_subs_Red_I_diff_Red_F: "Red_I N \<subseteq> Red_I (N - Red_F N)"
  unfolding Red_F_conv Red_I_conv
  by (rule fin_std_red.Red_I_subs_Red_I_diff_Red_F)

lemma Red_I_eq_Red_I_diff_Red_F: "Red_I N = Red_I (N - Red_F N)"
  unfolding Red_F_conv Red_I_conv
  by (rule fin_std_red.Red_I_eq_Red_I_diff_Red_F)

lemma Red_I_to_Inf: "Red_I N \<subseteq> Inf"
  unfolding Red_I_conv
  by (rule fin_std_red.Red_I_to_Inf)

lemma Red_I_of_Red_F_subset: "N' \<subseteq> Red_F N \<Longrightarrow> Red_I N \<subseteq> Red_I (N - N')"
  unfolding Red_F_conv Red_I_conv
  by (rule fin_std_red.Red_I_of_Red_F_subset)

lemma Red_I_of_Inf_to_N:
  "\<iota> \<in> Inf \<Longrightarrow> concl_of \<iota> \<in> N \<Longrightarrow> \<iota> \<in> Red_I N"
  unfolding Red_I_conv
  by (rule fin_std_red.Red_I_of_Inf_to_N)

text \<open>
The following corresponds to Theorems 4.7 and 4.8:
\<close>

sublocale calculus Bot Inf "(\<Turnstile>)" Red_I Red_F
  by (unfold_locales, fact Red_I_to_Inf, fact Red_F_Bot, fact Red_F_of_subset,
      fact Red_I_of_subset, fact Red_F_of_Red_F_subset, fact Red_I_of_Red_F_subset,
      fact Red_I_of_Inf_to_N)

end


subsection \<open>Refutational Completeness\<close>

locale calculus_with_standard_inference_redundancy = calculus Bot Inf "(\<Turnstile>)" Red_I Red_F
  for Bot :: "'f set" and Inf and entails (infix "\<Turnstile>" 50) and Red_I and Red_F +
  fixes
    less :: "'f \<Rightarrow> 'f \<Rightarrow> bool" (infix "\<prec>" 50)
  assumes
    Inf_has_prem: "\<iota> \<in> Inf \<Longrightarrow> prems_of \<iota> \<noteq> []" and
    Red_I_imp_redundant_infer: "\<iota> \<in> Red_I N \<Longrightarrow>
      (\<exists>DD\<subseteq>N. DD \<union> set (side_prems_of \<iota>) \<Turnstile> {concl_of \<iota>} \<and> (\<forall>C\<in>DD. C \<prec> main_prem_of \<iota>))"

sublocale calculus_with_finitary_standard_redundancy \<subseteq>
  calculus_with_standard_inference_redundancy Bot Inf "(\<Turnstile>)" Red_I Red_F
  using Inf_has_prem
  by (unfold_locales) (auto simp: Red_I_def redundant_infer_def)

sublocale calculus_with_standard_redundancy \<subseteq>
  calculus_with_standard_inference_redundancy Bot Inf "(\<Turnstile>)" Red_I Red_F
  using Inf_has_prem
  by (unfold_locales) (simp_all add: Red_I_def redundant_infer_def)

locale counterex_reducing_calculus_with_standard_inferance_redundancy =
  calculus_with_standard_inference_redundancy Bot Inf "(\<Turnstile>)" Red_I Red_F "(\<prec>)" +
  counterex_reducing_inference_system Bot "(\<Turnstile>)" Inf I_of "(\<prec>)"
  for
    Bot :: "'f set" and
    Inf :: "'f inference set" and
    entails :: "'f set \<Rightarrow> 'f set \<Rightarrow> bool" (infix "\<Turnstile>" 50) and
    Red_I :: "'f set \<Rightarrow> 'f inference set" and
    Red_F :: "'f set \<Rightarrow> 'f set" and
    I_of :: "'f set \<Rightarrow> 'f set" and
    less :: "'f \<Rightarrow> 'f \<Rightarrow> bool" (infix "\<prec>" 50) +
  assumes less_total: "\<And>C D. C \<noteq> D \<Longrightarrow> C \<prec> D \<or> D \<prec> C"
begin

text \<open>
The following result loosely corresponds to Theorem 4.9.
\<close>

lemma saturated_model:
  assumes
    satur: "saturated N" and
    bot_ni_n: "N \<inter> Bot = {}"
  shows "I_of N \<Turnstile> N"
proof (rule ccontr)
  assume "\<not> I_of N \<Turnstile> N"
  then obtain D :: 'f where
    d_in_n: "D \<in> N" and
    d_cex: "\<not> I_of N \<Turnstile> {D}" and
    d_min: "\<And>C. C \<in> N \<Longrightarrow> C \<prec> D \<Longrightarrow> I_of N \<Turnstile> {C}"
    using ex_min_counterex by blast
  then obtain \<iota> :: "'f inference" where
    \<iota>_in: "\<iota> \<in> Inf" and
    \<iota>_mprem: "D = main_prem_of \<iota>" and
    sprem_subs_n: "set (side_prems_of \<iota>) \<subseteq> N" and
    sprem_true: "I_of N \<Turnstile> set (side_prems_of \<iota>)" and
    concl_cex: "\<not> I_of N \<Turnstile> {concl_of \<iota>}" and
    concl_lt_d: "concl_of \<iota> \<prec> D"
    using Inf_counterex_reducing[OF bot_ni_n] less_total by metis
  have "\<iota> \<in> Red_I N"
    by (rule subsetD[OF satur[unfolded saturated_def Inf_from_def]],
        simp add: \<iota>_in set_prems_of Inf_has_prem)
      (use \<iota>_mprem d_in_n sprem_subs_n  in blast)
  then have "\<iota> \<in> Red_I N"
    using Red_I_without_red_F by blast
  then obtain DD :: "'f set" where
    dd_subs_n: "DD \<subseteq> N" and
    dd_cc_ent_d: "DD \<union> set (side_prems_of \<iota>) \<Turnstile> {concl_of \<iota>}" and
    dd_lt_d: "\<forall>C \<in> DD. C \<prec> D"
    unfolding \<iota>_mprem using Red_I_imp_redundant_infer by meson
  from dd_subs_n dd_lt_d have "I_of N \<Turnstile> DD"
    using d_min by (meson ex_min_counterex subset_iff)
  then have "I_of N \<Turnstile> {concl_of \<iota>}"
    using entails_trans dd_cc_ent_d entail_union sprem_true by blast
  then show False
    using concl_cex by auto
qed

text \<open>
A more faithful abstract version of Theorem 4.9 does not hold without some conditions, according to
Nitpick:
\<close>

corollary saturated_complete:
  assumes
    satur: "saturated N" and
    unsat: "N \<Turnstile> Bot"
  shows "N \<inter> Bot \<noteq> {}"
  oops

end

end
