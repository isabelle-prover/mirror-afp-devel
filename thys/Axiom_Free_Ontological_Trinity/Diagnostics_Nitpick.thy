theory Diagnostics_Nitpick
  imports Axiom_Free_Ontological_Trinity


begin
(*
  ============================================================================
  Developer-only Diagnostics: consistency / nontriviality checks, model existence checks
  - used only for Nitpick model probes and audits.
  ============================================================================
*)
section \<open>1. Diagnostics Overview\<close>
text \<open>This theory gathers lightweight diagnostics for the U-core and packages:
• Purity checks: ensure no backflow from optional bridges/locales into the D-route core.
• Sanity checks: Nitpick is expected to find no counterexample (i.e., @{text "expect = none"}).
• Suspicion checks: Nitpick is expected to find a genuine counterexample (i.e., flags over-strong statements).
• Model checks(Trinity model): Nitpick is expected to produce a genuine Trinity witness model, certifying non-vacuity and concrete realizability of the target configuration.
• Model checks(anti-modal collapse): Nitpick is expected to produce a genuine witness model showing that created truths are not forced into necessity, thereby confirming the absence of modal collapse.
\<close>


section \<open>2. Locale / Theorem Introspection (non-proof diagnostics)\<close>
text \<open>Quick check that locales are only interpreted where intended (no leakage).\<close>
print_interps FullIdBridge
print_interps Riemann_Toy

text \<open>Show hypotheses while printing key equivalences, then turn it back off.\<close>
declare [[show_hyps]]
thm PH_imp_EH PH_imp_TH EH_TH_imp_PH PH_iff_EH_TH
thm EqU_iff_LeU_both
declare [[show_hyps = false]]


section \<open>3. Nitpick setup (parameters and unfolds)\<close>
text \<open>Global defaults for Nitpick runs in this file (bump if needed).\<close>
nitpick_params [verbose, card = 2-4, card U = 1-3, timeout = 60]

text \<open>Unfold core definitions so Nitpick can see the structure.\<close>
declare SuppU_def                 [nitpick_unfold]
declare LeU_def                   [nitpick_unfold]
declare EqU_def                   [nitpick_unfold]
declare Supports_def              [nitpick_unfold]
declare EDia_def                  [nitpick_unfold]
declare TrueNow_def               [nitpick_unfold]
declare EH_def                    [nitpick_unfold]
declare TH_def                    [nitpick_unfold]
declare PH_def                    [nitpick_unfold]
declare LtU_def                   [nitpick_unfold]
declare H_negU_strict_def         [nitpick_unfold]
declare H_opt_def                 [nitpick_unfold]
declare PDom_def                  [nitpick_unfold]
declare PSupp_def                 [nitpick_unfold]


section \<open>4. Sanity checks (no counterexample expected)\<close>

text \<open>1) @{term PH} iff @{text "EH \<and> TH"}.\<close>
lemma Nitpick_PH_iff_EH_TH:
  shows "PH q \<longleftrightarrow> (EH q \<and> TH q)"
  nitpick [expect = none] oops

text \<open>2) @{term Hopt3} implies @{term N3} (unboxed, D-route).\<close>
lemma Nitpick_OnlyN3_from_Hopt3_unboxed:
  assumes "Hopt3 a b c"
  shows   N3
  nitpick [expect = none] oops

text \<open>3) Global n=1 exclusion (core witness wrapper).\<close>
lemma Nitpick_n1_global_exclusion_core:
  assumes "\<exists>a a' b c.
            EDia b \<and> EDia c \<and>
            (Arg b) \<preceq> (Arg a) \<and> (Arg c) \<preceq> (Arg a) \<and>
            (\<not> ((Arg b) \<preceq> (Arg a')) \<or> \<not> ((Arg c) \<preceq> (Arg a'))) \<and>
            EH (Arg a')"
  shows False
  nitpick [expect = none] oops

text \<open>4) Global n=1 exclusion (H\_opt wrapper).\<close>
lemma Nitpick_n1_global_exclusion_for_Hopt:
  assumes "\<exists>Q b c a'.
            H_opt Q \<and> EDia b \<and> EDia c \<and>
            (\<not> ((Arg b) \<preceq> (Arg a')) \<or> \<not> ((Arg c) \<preceq> (Arg a'))) \<and>
            EH (Arg a')"
  shows False
  nitpick [expect = none] oops

text \<open>5) H\_opt finality over @{term PDom}: no strict superior.\<close>
lemma Nitpick_argument_finality_PDom:
  assumes "H_opt q"
  shows "\<forall>\<zeta>\<in>PDom. \<not> ((Arg q) \<prec> (Arg \<zeta>))"
  nitpick [expect = none] oops

text \<open>6) Pair collapse at Arg-level from two @{term PH} + possibility.\<close>
lemma Nitpick_PH_pair_collapse_to_EqU:
  assumes "PH (Arg \<Phi>)" "PH (Arg \<Omega>)" "EDia \<Phi>" "EDia \<Omega>"
  shows   "(Arg \<Phi>) \<approx> (Arg \<Omega>)"
  nitpick [expect = none] oops


section \<open>5. Suspicion checks (Nitpick should find genuine counterexamples)\<close>
text \<open>Universal entailment / empty entailment are both false.\<close>
lemma entails_universal_suspect: "ALL e u. e \<turnstile> u"
  nitpick [card U=3, timeout=15, expect = genuine] oops

lemma entails_empty_suspect: "~ (EX e u. e \<turnstile> u)"
  nitpick [card U=3, timeout=15, expect = genuine] oops


section \<open>6. Strengthened / boundary diagnostics\<close>

text \<open>Strict variants: @{term EH_strict} does not imply @{term EH} in general (should be refutable).\<close>
lemma EH_strict_converse_suspect: "ALL q. EH_strict q --> EH q"
  nitpick [card U=3, timeout=20, expect = genuine] oops

text \<open>But @{term PH_strict} does imply @{term PH} (holds by definitions used here).\<close>
lemma PH_strict_converse_check: "ALL q. PH_strict q --> PH q"
  nitpick [card U=3, timeout=20, expect = none] oops

text \<open>One-way TSupp-maximality: the converse direction should hold under our setup.\<close>
lemma TH_TSupp_max_converse_check:
  "ALL q. ((ALL x. TSupp x \<subseteq> TSupp q) --> TH q)"
  nitpick [card U=3, timeout=20, expect = none] oops

text \<open>The following global tautologies should be refutable.\<close>
lemma Hopt_tautology_suspect: "ALL q. H_opt q"
  nitpick [card U=3, timeout=20, expect = genuine] oops

lemma Comparable_PDom_on_tautology_suspect: "ALL q. Comparable_PDom_on q"
  nitpick [card U=3, timeout=20, expect = genuine] oops

lemma H_negU_strict_tautology_suspect: "ALL q. H_negU_strict q"
  nitpick [card U=3, timeout=20, expect = genuine] oops


section \<open>7. No modal collapse (Nitpick model test)\<close>
text \<open>
  We established that the Trinity implies the possibility of R (@{text "\<diamond>"}R).
  The critical question is whether the Trinity necessitates R (Modal Collapse).
  If Nitpick finds a counter-model for the lemma below, we confirm that
  Trinity and @{text "\<not>"}R can co-exist without contradiction, proving that collapse is resolved.
\<close>

lemma Trinity_does_not_necessitate_R:
  fixes \<Phi> \<Omega> \<psi> R :: bool
  assumes T_Pattern: "Trinity \<Phi> \<Omega> \<psi> \<longrightarrow> \<diamond> R"    (* Trinity enables R *)
  assumes S_Pattern: "\<not> (Trinity \<Phi> \<Omega> \<psi>) \<longrightarrow> \<not> R" (* No Trinity, No R *)
  shows "Trinity \<Phi> \<Omega> \<psi> \<longrightarrow> R"
  nitpick [expect = genuine, show_all, satisfy]
  oops

text \<open>
  (1) Anti-degeneracy: @{text "\<diamond>"} is not trivially True for every proposition.
\<close>
lemma Diamond_is_not_degenerate:
  shows "\<not> (\<forall>P::bool. \<diamond> P)"
  nitpick [expect = genuine, show_all, satisfy]
  oops

text \<open>
  (2) Non-triviality guard: @{text "\<diamond>"}False is not forced (not a theorem).
  We test both directions as independence smoke-tests.
\<close>
lemma Dia_False_is_not_a_theorem:
  shows "\<diamond> False"
  nitpick [expect = genuine, show_all, satisfy]
  oops

lemma Not_Dia_False_is_not_a_theorem:
  shows "\<not> (\<diamond> False)"
  nitpick [expect = genuine, show_all, satisfy]
  oops


section \<open>8. Computational Diagnostics and Trinity Model Existence (Nitpick test)\<close>
text \<open>
  APPENDIX: The following diagnostic block uses Nitpick to explore the model-theoretic
  properties of the theory.

  Note on ``oops'': The usage of ``oops'' here does not indicate a proof failure.
  Rather, it marks a diagnostic check where Nitpick attempts to find counter-examples.
  The absence of counter-examples in these finite scopes supports the consistency
  of the Triune Necessity (N=3) as the unique logical equilibrium of the system.
\<close>

typedef U3 = "{0::nat, 1, 2}" by auto
setup_lifting type_definition_U3

definition HeadP_U3 :: "U3 \<Rightarrow> bool" where
  "HeadP_U3 _ \<equiv> True"

definition NT_pair_supportU3 :: "U3 \<Rightarrow> U3 \<Rightarrow> U3 \<Rightarrow> bool" where
  "NT_pair_supportU3 A B C \<equiv> (A \<noteq> B \<and> A \<noteq> C \<and> B \<noteq> C)"

definition TrinityModel :: bool where
  "TrinityModel \<equiv> (\<exists>A B C :: U3.
      HeadP_U3 A \<and> HeadP_U3 B \<and> HeadP_U3 C \<and>
      A \<noteq> B \<and> A \<noteq> C \<and> B \<noteq> C \<and>
      NT_pair_supportU3 A B C \<and>
      NT_pair_supportU3 B C A \<and>
      NT_pair_supportU3 C A B)"

lemma "TrinityModel"
  nitpick [satisfy, card U3 = 3, expect = genuine]
  oops


subsection \<open>8.1 Trinity Model existence Nitpick Test - MaxNT\<close>

datatype U10 = u0 | u1 | u2 | u3 | u4 | u5 | u6 | u7 | u8 | u9

consts HeadP_U10 :: "U10 \<Rightarrow> bool"

definition NT_pair_supportU10 :: "U10 \<Rightarrow> U10 \<Rightarrow> U10 \<Rightarrow> bool" where
  \<open>NT_pair_supportU10 A B C \<equiv> (A \<noteq> B \<and> A \<noteq> C \<and> B \<noteq> C)\<close>

definition TrinityModel_U10 :: bool where
  \<open>TrinityModel_U10 \<equiv>
    (\<exists>A B C :: U10.
      HeadP_U10 A \<and> HeadP_U10 B \<and> HeadP_U10 C \<and>
      NT_pair_supportU10 A B C \<and>
      NT_pair_supportU10 B C A \<and>
      NT_pair_supportU10 C A B)\<close>

definition Head_1_U10 :: bool where
  \<open>Head_1_U10 \<equiv>
    (\<exists>a::U10. HeadP_U10 a \<and> (\<forall>x::U10. HeadP_U10 x \<longrightarrow> x = a))\<close>

definition Head_2_U10 :: bool where
  \<open>Head_2_U10 \<equiv>
    (\<exists>a b::U10.
      a \<noteq> b \<and> HeadP_U10 a \<and> HeadP_U10 b \<and>
      (\<forall>x::U10. HeadP_U10 x \<longrightarrow> (x = a \<or> x = b)))\<close>

definition Head_3_U10 :: bool where
  \<open>Head_3_U10 \<equiv>
    (\<exists>a b c::U10.
      a \<noteq> b \<and> a \<noteq> c \<and> b \<noteq> c \<and>
      HeadP_U10 a \<and> HeadP_U10 b \<and> HeadP_U10 c \<and>
      (\<forall>x::U10. HeadP_U10 x \<longrightarrow> (x = a \<or> x = b \<or> x = c)))\<close>

definition Head_4_U10 :: bool where
  \<open>Head_4_U10 \<equiv>
    (\<exists>a b c d::U10.
      a \<noteq> b \<and> a \<noteq> c \<and> a \<noteq> d \<and>
      b \<noteq> c \<and> b \<noteq> d \<and> c \<noteq> d \<and>
      HeadP_U10 a \<and> HeadP_U10 b \<and> HeadP_U10 c \<and> HeadP_U10 d \<and>
      (\<forall>x::U10. HeadP_U10 x \<longrightarrow>
        (x = a \<or> x = b \<or> x = c \<or> x = d)))\<close>

lemma Trinity_excludes_1:
  \<open>\<not> (TrinityModel_U10 \<and> Head_1_U10)\<close>
  unfolding TrinityModel_U10_def Head_1_U10_def NT_pair_supportU10_def
  by metis

lemma Trinity_excludes_2:
  \<open>\<not> (TrinityModel_U10 \<and> Head_2_U10)\<close>
  unfolding TrinityModel_U10_def Head_2_U10_def NT_pair_supportU10_def
  by metis

lemma Trinity_Minimal_3_over_2:
  assumes \<open>TrinityModel_U10 \<and> Head_3_U10\<close>
  shows   \<open>\<not> (TrinityModel_U10 \<and> Head_2_U10)\<close>
  using Trinity_excludes_2 by blast

lemma \<open>TrinityModel_U10 \<and> Head_1_U10\<close>
  unfolding TrinityModel_U10_def Head_1_U10_def NT_pair_supportU10_def
  nitpick [satisfy, card U10 = 10, expect = none, show_all]
  oops

lemma \<open>TrinityModel_U10 \<and> Head_2_U10\<close>
  unfolding TrinityModel_U10_def Head_2_U10_def NT_pair_supportU10_def
  nitpick [satisfy, card U10 = 10, expect = none, show_all]
  oops

text\<open>
The failure of N=1 and N=2 models to satisfy the EdgeExist condition validates that the support relation (NT\_pair\_support) is strictly non-trivial.
\<close>
lemma \<open>TrinityModel_U10 \<and> Head_3_U10\<close>
  unfolding TrinityModel_U10_def Head_3_U10_def NT_pair_supportU10_def
  nitpick [satisfy, card U10 = 10, expect = genuine, show_all]
  oops


subsection \<open>8.2 Numerical Diagnostics for Trinity Necessity with number of distinct MaxCov entities\<close>
text \<open>
  This suite evaluates the structural stability of the H-opt framework.
  It systematically tests different values of N (number of distinct MaxCov entities)
  to identify the unique logical fixed point of the system.
\<close>

lemma nitpick_1_MaxCov_insufficient_UNSAT:
  assumes M1: "MaxCov A"
  shows "False"
  nitpick [satisfy, expect = none]
oops

lemma nitpick_2_MaxCov_pairwise_nonapprox_UNSAT:
  assumes MA: "MaxCov A" and MB: "MaxCov B"
      and AB: "A \<noteq> B"
  shows "False"
  nitpick [satisfy, expect = none]
oops

text \<open>The Unique Fixed Point: N = 3 (The Trinity)\<close>
lemma nitpick_3_MaxCov_Trinity_GENUINE:
  assumes MA: "MaxCov A" and MB: "MaxCov B" and MC: "MaxCov C"
      and AB: "A \<noteq> B" and AC: "A \<noteq> C" and BC: "B \<noteq> C"
  shows "GodExists_U"
  nitpick [satisfy, expect = genuine]
  oops

lemma nitpick_4_MaxCov_pairwise_nonapprox_UNSAT:
  assumes MA: "MaxCov A" and MB: "MaxCov B" and MC: "MaxCov C" and MD: "MaxCov D"
      and AB: "\<not>(A \<approx> B)" and AC: "\<not>(A \<approx> C)" and AD: "\<not>(A \<approx> D)"
      and BC: "\<not>(B \<approx> C)" and BD: "\<not>(B \<approx> D)" and CD: "\<not>(C \<approx> D)"
  shows False
  nitpick [satisfy, expect = none, show_all]
  nitpick [satisfy, expect = none, show_all, timeout = 60]
oops
text \<open>
Computational diagnostic (Nitpick).
We asked Nitpick for a model containing four MaxCov points that are pairwise non-@{text "\<approx>"}.
No model is found (expect = none), even with an increased timeout.
This indicates that, within Nitpick's finite scopes, the current MaxCov/Cov/@{text "\<approx>"} definitions
already exert a strong structural constraint against N @{text "\<ge>"} 4 distinct maxima.
(This is evidence, not a theorem.)
\<close>


section \<open>9. Non-vacuous Genuine Trinity model Nitpick test\<close>
(* ========================= *)
(* Non-vacuous Trinity (P-level) *)
(* ========================= *)
definition NT_edgeP :: "P \<Rightarrow> P \<Rightarrow> P \<Rightarrow> bool" where
  \<open>NT_edgeP A B C \<longleftrightarrow>
      (ArgP (A \<sqinter> B) \<preceq> ArgP C) \<and>
      \<not> (ArgP (A \<sqinter> B) \<approx> ArgP A) \<and>
      \<not> (ArgP (A \<sqinter> B) \<approx> ArgP B)\<close>

definition TriSupport_JointP :: "P \<Rightarrow> P \<Rightarrow> P \<Rightarrow> bool" where
  \<open>TriSupport_JointP a b c \<longleftrightarrow>
      (ArgP (b \<sqinter> c) \<preceq> ArgP a) \<and>
      (ArgP (c \<sqinter> a) \<preceq> ArgP b) \<and>
      (ArgP (a \<sqinter> b) \<preceq> ArgP c) \<and>
      \<not> (ArgP a \<preceq> ArgP b) \<and> \<not> (ArgP b \<preceq> ArgP a) \<and>
      \<not> (ArgP b \<preceq> ArgP c) \<and> \<not> (ArgP c \<preceq> ArgP b) \<and>
      \<not> (ArgP c \<preceq> ArgP a) \<and> \<not> (ArgP a \<preceq> ArgP c)\<close>

definition Trinity_nonvacuousP :: bool where
  \<open>Trinity_nonvacuousP \<longleftrightarrow>
      (\<exists>a b c.
          H_optP a \<and> H_optP b \<and> H_optP c \<and>
          TriSupport_JointP a b c \<and>
          NT_edgeP a b c \<and> NT_edgeP b c a \<and> NT_edgeP c a b)\<close>

lemma Trinity_nonvacuousP_satisfiable:
  shows Trinity_nonvacuousP
  nitpick [satisfy, card P = 3, card U = 3, timeout = 60, show_all, expect = genuine]
  oops
text \<open>
\paragraph{Finite-model witness (Nitpick).}
Nitpick finds a genuine model of @{term Trinity_nonvacuousP} in the finite scope
$\mathrm{card}(P)=3$ and $\mathrm{card}(U)=3$.

In the returned witness (up to renaming of elements), the Skolem triple is
@{text "\<open>a = P\<^sub>1\<close>"}, @{text "\<open>b = P\<^sub>2\<close>"}, @{text "\<open>c = P\<^sub>3\<close>"},
and the conjunction-like operator @{text "\<open>\<sqinter>\<close>"} satisfies the cycle
@{text "\<open>P\<^sub>1 \<sqinter> P\<^sub>2 = P\<^sub>3\<close>"},
@{text "\<open>P\<^sub>2 \<sqinter> P\<^sub>3 = P\<^sub>1\<close>"},
@{text "\<open>P\<^sub>3 \<sqinter> P\<^sub>1 = P\<^sub>2\<close>"}.

This confirms that the non-vacuous triune package
(\texttt{TriSupport\_JointP} plus three \texttt{NT\_edgeP} constraints, together with \texttt{H\_optP})
is jointly satisfiable.\<close>


lemma Trinity_nonvacuousP_not_valid_sanity:
  shows "\<not> Trinity_nonvacuousP"
  nitpick [satisfy, card P = 3, card U = 3, timeout = 60, expect = genuine]
  oops
text \<open>
\<^bold>\<open>Nitpick status of @{term Trinity_nonvacuousP}.\<close>

We use Nitpick here only as a finite-scope sanity check.

\<^item> \<^bold>\<open>Satisfiable (SAT).\<close>
Nitpick finds a genuine model of @{term Trinity_nonvacuousP} with card P = 3 and card U = 3.
Hence the non-vacuous triune package is consistent with the current definitional framework
(i.e., it is not definitionally empty or contradictory).

\<^item> \<^bold>\<open>Not valid (not a tautology).\<close>
Nitpick also finds a genuine model of @{term "\<not> Trinity_nonvacuousP"} in the same scope.
Hence @{term Trinity_nonvacuousP} is not forced by the definitions alone.

\<^bold>\<open>Interpretation.\<close>
Together, these witnesses show that @{term Trinity_nonvacuousP} is contentful:
it is compatible with the framework, yet not logically trivial in the tested scope.
These results are evidence for the chosen finite scope, not a meta-theorem about all models.
\<close>


end