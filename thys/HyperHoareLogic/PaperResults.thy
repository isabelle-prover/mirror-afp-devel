theory PaperResults
  imports Loops SyntacticAssertions Compositionality TotalLogic ExamplesCompositionality
begin

section \<open>Summary of the Results from the Paper\<close>

text \<open>This file contains the formal results mentioned the paper. It is organized in the same order
and with the same structure as the paper.
\<^item> You can use the panel "Sidekick" on the right to see and navigate the structure of the file, via sections and subsections.
\<^item> You can ctrl+click on terms to jump to their definition.
\<^item> After jumping to another location, you can come back to the previous location by clicking the
  green left arrow, on the right side of the menu above.\<close>



subsection \<open>3: Hyper Hoare Logic\<close>

subsubsection \<open>3.1: Language and Semantics\<close>

text \<open>The programming language is defined in the file Language.thy:
\<^item> The type of program state (definition 1) is \<^typ>\<open>('pvar, 'pval) pstate\<close>
  (<-- you can ctrl+click on the name \<open>pstate\<close> above to jump to its definition).
\<^item> Program commands (definition 1) are defined via the type \<^typ>\<open>('var, 'val) stmt\<close>.
\<^item> The big-step semantics (figure 9) is defined as \<^const>\<open>single_sem\<close>. We also use the notation \<^term>\<open>\<langle>C, \<sigma>\<rangle> \<rightarrow> \<sigma>'\<close>.\<close>

subsubsection \<open>3.2: Hyper-Triples, Formally\<close>

text \<open>
\<^item> Extended states (definition 2) are defined as \<^typ>\<open>('lvar, 'lval, 'pvar, 'pval) state\<close> (file Language.thy).
\<^item> Hyper-assertions (definition 3) are defined as \<^typ>\<open>('lvar, 'lval, 'pvar, 'pval) state hyperassertion\<close> (file Logic.thy).
\<^item> The extended semantics (definition 4) is defined as \<^const>\<open>sem\<close>  (file Language.thy).
\<^item> Lemma 1 is shown and proven below.
\<^item> Hyper-triples (definition 5) are defined as \<^const>\<open>hyper_hoare_triple\<close> (file Logic.thy).
  We also use the notation \<^term>\<open>\<Turnstile> {P} C {Q}\<close>.\<close>

lemma lemma1:
  "sem C (S1 \<union> S2) = sem C S1 \<union> sem C S2"
  "S \<subseteq> S' \<Longrightarrow> sem C S \<subseteq> sem C S'"
  "sem C (\<Union>x. f x) = (\<Union>x. sem C (f x))"
  "sem Skip S = S"
  "sem (C1;; C2) S = sem C2 (sem C1 S)"
  "sem (If C1 C2) S = sem C1 S \<union> sem C2 S"
  "sem (While C) S = (\<Union>n. iterate_sem n C S)"
  using sem_if sem_seq sem_union sem_skip sem_union_general sem_monotonic sem_while by metis+

subsubsection \<open>3.3: Core Rules\<close>

text \<open>The core rules (from figure 2) are defined in the file Logic.thy as \<^const>\<open>syntactic_HHT\<close>.
We also use the notation \<^term>\<open>\<turnstile> {P} C {Q}\<close>. Operators \<open>\<otimes>\<close> (definition 6) and \<open>\<Otimes>\<close> (definition 7)
are defined as \<^const>\<open>join\<close> and \<^const>\<open>natural_partition\<close>, respectively.\<close>

subsubsection \<open>3.4: Soundness and Completeness\<close>

text \<open>Theorem 1: Soundness\<close>
theorem thm1_soundness:
  assumes "\<turnstile> {P} C {Q}"
  shows "\<Turnstile> {P} C {Q}"
  using assms soundness by auto

text \<open>Theorem 2: Completeness\<close>
theorem thm2_completeness:
  assumes "\<Turnstile> {P} C {Q}"
  shows "\<turnstile> {P} C {Q}"
  using assms completeness by auto

subsubsection \<open>3.5: Expressivity of Hyper-Triples\<close>

text \<open>Program hyperproperties (definition 8) are defined in the file ProgramHyperproperties as
the type \<^typ>\<open>('pvar, 'pval) program_hyperproperty\<close>, which is syntactic sugar for the type
\<^typ>\<open>(('pvar, 'pval) pstate \<times> ('pvar, 'pval) pstate) set \<Rightarrow> bool\<close>. As written in the paper (after the definition),
this type is equivalent to the type \<^typ>\<open>((('pvar, 'pval) pstate \<times> ('pvar, 'pval) pstate) set) set\<close>.
The satisfiability of program hyperproperties is defined via the function \<^const>\<open>hypersat\<close>.\<close>

text \<open>Theorem 3: Expressing hyperproperties as hyper-triples\<close>
theorem thm3_expressing_hyperproperties_as_hyper_triples:
  fixes to_lvar :: "'pvar \<Rightarrow> 'lvar"
  fixes to_lval :: "'pval \<Rightarrow> 'lval"
  fixes H :: "('pvar, 'pval) program_hyperproperty"
  assumes "injective to_lvar" \<comment>\<open>The cardinality of \<^typ>\<open>'lvar\<close> is at least the cardinality of \<^typ>\<open>'pvar\<close>.\<close>
      and "injective to_lval" \<comment>\<open>The cardinality of \<^typ>\<open>'lval\<close> is at least the cardinality of \<^typ>\<open>'pval\<close>.\<close>
    shows "\<exists>P Q::('lvar, 'lval, 'pvar, 'pval) state hyperassertion. (\<forall>C. hypersat C H \<longleftrightarrow> \<Turnstile> {P} C {Q})"
  using assms proving_hyperproperties
  by blast

text \<open>Theorem 4: Expressing hyper-triples as hyperproperties\<close>
theorem thm4_expressing_hyper_triples_as_hyperproperties:
  "\<Turnstile> {P} C {Q} \<longleftrightarrow> hypersat C (hyperprop_hht P Q)"
  by (simp add: any_hht_hyperprop)

text \<open>Theorem 5: Disproving hyper-triples\<close>
theorem thm5_disproving_triples:
  "\<not> \<Turnstile> {P} C {Q} \<longleftrightarrow> (\<exists>P'. sat P' \<and> entails P' P \<and> \<Turnstile> {P'} C {\<lambda>S. \<not> Q S})"
  using disproving_triple by auto




subsection \<open>4: Syntactic Rules\<close>

subsubsection \<open>4.1: Syntactic Hyper-Assertions\<close>

text \<open>Syntactic hyper-expressions and hyper-assertions (definition 9) are defined in the file
SyntacticAssertions.thy as \<^typ>\<open>'val exp\<close> and \<^typ>\<open>'val assertion\<close> respectively, where 'val is the
type of both logical and program values. Note that we use de Bruijn indices (i.e, natural numbers)
for states and variables bound by quantifiers.\<close>

subsubsection \<open>4.2: Syntactic Rules for Deterministic and Non-Deterministic Assignments.\<close>

text \<open>We prove semantic versions of the syntactic rules from subsection 4 (figure 3).
We use \<^const>\<open>interp_assert\<close> to convert a syntactic hyper-assertion into a semantic one, because
our hyper-triples require semantic hyper-assertions. Similarly, we use \<^const>\<open>interp_pexp\<close> to convert
a syntactic program expression into a semantic one.
\<^term>\<open>transform_assign x e P\<close> and \<^term>\<open>transform_havoc x P\<close> correspond to \<open>A\<^sup>e\<^sub>x\<close> and \<open>H\<^sub>x\<close> from definition 10.\<close>

text \<open>Rule AssignS from figure 3\<close>
proposition AssignS:
  "\<turnstile> { interp_assert (transform_assign x e P) } Assign x (interp_pexp e) {interp_assert P}"
  using completeness rule_assign_syntactic by blast

text \<open>Rule HavocS from figure 3\<close>
proposition HavocS:
  "\<turnstile> { interp_assert (transform_havoc x P) } Havoc x {interp_assert P}"
  using completeness rule_havoc_syntactic by blast

subsubsection \<open>4.3: Syntactic Rules for Assume Statements\<close>

text \<open>\<^const>\<open>transform_assume\<close> corresponds to \<open>\<Pi>\<^sub>b\<close> (definition 11).\<close>

text \<open>Rule AssumeS from figure 3\<close>
proposition AssumeS:
  "\<turnstile> { interp_assert (transform_assume (pbexp_to_assertion 0 b) P) } Assume (interp_pbexp b) {interp_assert P}"
  using completeness rule_assume_syntactic by blast

text \<open>As before, we use \<^const>\<open>interp_pbexp\<close> to convert the syntactic program Boolean expression b into
a semantic one. Similarly, \<^term>\<open>pbexp_to_assertion 0 b\<close> converts the syntactic program Boolean expression
p into a syntactic hyper-assertion. The number 0 is a de Bruijn index, which corresponds to the closest
quantified state. For example, the hyper-assertion \<open>\<forall><\<phi>>. \<phi>(a)=\<phi>(b) \<and> (\<exists><\<phi>'>. \<phi>(x) \<succeq> \<phi>'(y))\<close> would
be written as \<open>\<forall>. 0(a)=0(b) \<and> (\<exists>. 1(x) \<succeq> 0(y))\<close> with de Bruijn indices. Thus, one can think of
\<open>pbexp_to_assertion 0 b\<close> as \<open>b(\<phi>)\<close>, where \<open>\<phi>\<close> is simply the innermost quantified state.\<close>




subsection \<open>5: Proof Principles for Loops\<close>

text \<open>We show in the following our proof rules for loops, presented in figure 5.\<close>

text \<open>Rule WhileDesugared from figure 5\<close>
theorem while_desugared:
  assumes "\<And>n. \<turnstile> {I n} Assume b;; C {I (Suc n)}"
      and "\<turnstile> { natural_partition I } Assume (lnot b) { Q }"
    shows "\<turnstile> {I 0} while_cond b C { Q }"
  by (metis completeness soundness assms(1) assms(2) seq_rule while_cond_def while_rule)

text \<open>This result uses the following constructs:
\<^item> \<^term>\<open>natural_partition I\<close> corresponds to the \<open>\<Otimes>\<close> operator from definition 7.
\<^item> \<^term>\<open>lnot b\<close> negates b.
\<^item> \<^term>\<open>while_cond b C\<close> is defined as \<^term>\<open>While (Assume b;; C);; Assume (lnot b)\<close>.\<close>

text \<open>Rule WhileSync from figure 5 (presented in subsubsection 5.1)\<close>
lemma WhileSync:
  assumes "entails I (low_exp b)"
      and "\<turnstile> {conj I (holds_forall b)} C {I}"
    shows "\<turnstile> {conj I (low_exp b)} while_cond b C {conj (disj I emp) (holds_forall (lnot b))}"
  using WhileSync_simpler entail_conj completeness soundness assms(1) assms(2) entails_refl 
  consequence_rule[of "conj I (holds_forall b)" "conj I (holds_forall b)" I "conj I (low_exp b)"] by blast

text \<open>This result uses the following constructs:
\<^item> \<^term>\<open>conj A B\<close> corresponds to the hyper-assertion \<open>A \<and> B\<close>.
\<^item> \<^term>\<open>holds_forall b\<close> corresponds to \<open>box(b)\<close>.
\<^item> \<^term>\<open>low_exp b\<close> corresponds to \<open>low(b)\<close>.
\<^item> \<^term>\<open>disj A B\<close> corresponds to the hyper-assertion \<open>A \<or> B\<close>.
\<^item> \<^term>\<open>emp\<close> checks whether the set of states is empty.\<close>

text \<open>Rule IfSync from figure 5 (presented in subsubsection 5.1)\<close>
theorem IfSync:
  assumes "entails P (low_exp b)"
      and "\<turnstile> {conj P (holds_forall b)} C1 {Q}"
      and "\<turnstile> {conj P (holds_forall (lnot b))} C2 {Q}"
    shows "\<turnstile> {P} if_then_else b C1 C2 {Q}"
  using completeness soundness consequence_rule[of _ "conj P (low_exp b)" Q] assms(1) entail_conj entails_refl assms if_synchronized by metis

text \<open>This result uses the following construct:
\<^item> \<^term>\<open>if_then_else b C1 C2\<close> is syntactic sugar for \<^term>\<open>If (Assume b;; C1) (Assume (lnot b);; C2)\<close>.\<close>

text \<open>Rule \<open>While-\<forall>*\<exists>*\<close> from figure 5 (presented in subsubsection 5.2)\<close>
theorem while_forall_exists:
  assumes "\<turnstile> {I} if_then b C {I}"
      and "\<turnstile> {I} Assume (lnot b) {interp_assert Q}"
      and "no_forall_state_after_existential Q"
    shows "\<turnstile> {I} while_cond b C {interp_assert Q}"
  using consequence_rule[of I I "conj (interp_assert Q) (holds_forall (lnot b))" "interp_assert Q"]
  using completeness soundness while_forall_exists_simpler assms entail_conj_weaken entails_refl by metis

text \<open>This result uses the following constructs:
\<^item> \<^term>\<open>if_then b C\<close> is syntactic sugar for \<^term>\<open>If (Assume b;; C) (Assume (lnot b))\<close>.
\<^item> \<^term>\<open>no_forall_state_after_existential Q\<close> holds iff there is no universal state quantifier \<open>\<forall>\<langle>_\<rangle>\<close> after any \<open>\<exists>\<close> in Q.\<close>

text \<open>Rule \<open>While-\<exists>\<close> from figure 5 (presented in subsubsection 5.3)\<close>
theorem while_loop_exists:
  assumes  "\<And>v. \<turnstile> { (\<lambda>S. \<exists>\<phi>\<in>S. e (snd \<phi>) = v \<and> b (snd \<phi>) \<and> P \<phi> S) } if_then b C { (\<lambda>S. \<exists>\<phi>\<in>S. lt (e (snd \<phi>)) v \<and> P \<phi> S) }"
      and "\<And>\<phi>. \<turnstile> { P \<phi> } while_cond b C { Q \<phi> }"
      and "wfP lt"
    shows "\<turnstile> { (\<lambda>S. \<exists>\<phi>\<in>S. P \<phi> S) } while_cond b C { (\<lambda>S. \<exists>\<phi>\<in>S. Q \<phi> S)}"
  using completeness soundness exists_terminates_loop assms by blast

text \<open>\<^term>\<open>wfP lt\<close> in this result ensures that the binary operator \<open>lt\<close> is well-founded.
\<open>e\<close> is a function of a program state, which must decrease after each iteration.\<close>




subsection \<open>Appendix A: Technical Definitions Omitted from the Paper\<close>

text \<open>The big-step semantics (figure 9) is defined as \<^const>\<open>single_sem\<close>. We also use the notation \<^term>\<open>\<langle>C, \<sigma>\<rangle> \<rightarrow> \<sigma>'\<close>.
The following definitions are formalized in the file SyntacticAssertions.thy:
\<^item> Evaluation of hyper-expressions (definition 12): \<^const>\<open>interp_exp\<close>.
\<^item> Satisfiability of hyper-assertions (definition 12): \<^const>\<open>sat_assertion\<close>.
\<^item> Syntactic transformation for deterministic assignments (definition 13): \<^const>\<open>transform_assign\<close>.
\<^item> Syntactic transformation for non-deterministic assignments (definition 14): \<^const>\<open>transform_havoc\<close>.
\<^item> Syntactic transformation for assume statements. (definition 15): \<^const>\<open>transform_assume\<close>.\<close>



subsection \<open>Appendix C: Expressing Judgments of Hoare Logics as Hyper-Triples\<close>

subsubsection \<open>Appendix C.1: Overapproximate Hoare Logics\<close>

text \<open>The following judgments are defined in the file Expressivity.thy as follows:
\<^item> Definition 16 (Hoare Logic): \<^term>\<open>HL P C Q\<close>.
\<^item> Definition 17 (Cartesian Hoare Logic): \<^term>\<open>CHL P C Q\<close>.\<close>

text \<open>Proposition 1: HL triples express hyperproperties\<close>
proposition prop_1_HL_expresses_hyperproperties:
  "\<exists>H. (\<forall>C. hypersat C H \<longleftrightarrow> HL P C Q)"
  using HL_expresses_hyperproperties by blast

text \<open>Proposition 2: Expressing HL in Hyper Hoare Logic\<close>
proposition prop_2_expressing_HL_in_HHL:
  "HL P C Q \<longleftrightarrow> (hyper_hoare_triple (over_approx P) C (over_approx Q))"
  using encoding_HL by auto

text \<open>Proposition 3: CHL triples express hyperproperties\<close>
proposition prop_3_CHL_is_hyperproperty:
  "hypersat C (CHL_hyperprop P Q) \<longleftrightarrow> CHL P C Q"
  using CHL_hyperproperty by fast

text \<open>Proposition 4: Expressing CHL in Hyper Hoare Logic\<close>
proposition prop_4_encoding_CHL_in_HHL:
  assumes "not_free_var_of P x"
      and "not_free_var_of Q x"
      and "injective from_nat"
    shows "CHL P C Q \<longleftrightarrow> \<Turnstile> {encode_CHL from_nat x P} C {encode_CHL from_nat x Q}"
  using encoding_CHL assms by fast

text \<open>The function \<open>from_nat\<close> gives us a way to encode numbers from 1 to k as logical values.
Moreover, note that we represent k-tuples implicitly, as mappings of type \<^typ>\<open>'a \<Rightarrow> 'b\<close>: When the type
\<open>'a\<close> has k elements, a function of type \<^typ>\<open>'a \<Rightarrow> 'b\<close> corresponds to a k-tuple of elements of type 'b.
This representation is more convenient to work with, and more general, since it also captures infinite sequences.\<close>

subsubsection \<open>Appendix C.2: Underapproximate Hoare Logics\<close>

text \<open>The following judgments are defined in the file Expressivity.thy as follows:
\<^item> Definition 18 (Incorrectness Logic): \<^term>\<open>IL P C Q\<close>.
\<^item> Definition 19 (k-Incorrectness Logic): \<^term>\<open>RIL P C Q\<close>.
\<^item> Definition 20 (Forward Underapproximation): \<^term>\<open>FU P C Q\<close>.
\<^item> Definition 21 (k-Forward Underapproximation): \<^term>\<open>RFU P C Q\<close>.\<close>

text \<open>RIL is the old name of k-IL, and RFU is the old name of k-FU.\<close>

text \<open>Proposition 5: IL triples express hyperproperties\<close>
proposition prop_5_IL_hyperproperties:
  "IL P C Q \<longleftrightarrow> IL_hyperprop P Q (set_of_traces C)"
  using IL_expresses_hyperproperties by fast

text \<open>Proposition 6: Expressing IL in Hyper Hoare Logic\<close>
proposition prop_6_expressing_IL_in_HHL:
  "IL P C Q \<longleftrightarrow> (hyper_hoare_triple (under_approx P) C (under_approx Q))"
  using encoding_IL by fast

text \<open>Proposition 7: k-IL triples express hyperproperties\<close>
proposition prop_7_kIL_hyperproperties:
  "hypersat C (RIL_hyperprop P Q) \<longleftrightarrow> RIL P C Q"
  using RIL_expresses_hyperproperties by fast

text \<open>Proposition 8: Expressing k-IL in Hyper Hoare Logic\<close>
proposition prop_8_expressing_kIL_in_HHL:
  fixes x :: "'lvar"
  assumes "\<And>l l' \<sigma>. (\<lambda>i. (l i, \<sigma> i)) \<in> P \<longleftrightarrow> (\<lambda>i. (l' i, \<sigma> i)) \<in> P"  (* P does not depend on logical variables *)
      and "injective (indexify :: (('a \<Rightarrow> ('pvar \<Rightarrow> 'pval)) \<Rightarrow> 'lval))" (* |lval| \<ge> |PStates^k| *)
      and "c \<noteq> x"
      and "injective from_nat"
      and "not_free_var_of (P :: ('a \<Rightarrow> ('lvar \<Rightarrow> 'lval) \<times> ('pvar \<Rightarrow> 'pval)) set) x \<and> not_free_var_of P c"
      and "not_free_var_of Q x \<and> not_free_var_of Q c"
    shows "RIL P C Q \<longleftrightarrow> \<Turnstile> {pre_insec from_nat x c P} C {post_insec from_nat x c Q}"
  using assms(1) assms(2) assms(3) assms(4) assms(5) assms(6) by (rule encoding_RIL)

proposition FU_hyperproperties:
  "hypersat C (hyperprop_FU P Q) \<longleftrightarrow> FU P C Q"
  by (rule FU_expresses_hyperproperties)

text \<open>Proposition 9: Expressing FU in Hyper Hoare Logic\<close>
proposition prop_9_expressing_FU_in_HHL:
  "FU P C Q \<longleftrightarrow> \<Turnstile> {encode_FU P} C {encode_FU Q}"
  by (rule encoding_FU)

text \<open>Proposition 10: k-FU triples express hyperproperties\<close>
proposition prop_10_kFU_expresses_hyperproperties:
  "hypersat C (RFU_hyperprop P Q) \<longleftrightarrow> RFU P C Q"
  by (rule RFU_captures_hyperproperties)

text \<open>Proposition 11: Expressing k-FU in Hyper Hoare Logic\<close>
proposition prop_11_encode_kFU_in_HHL:
  assumes "not_free_var_of P x"
      and "not_free_var_of Q x"
      and "injective from_nat"
    shows "RFU P C Q \<longleftrightarrow> \<Turnstile> {encode_RFU from_nat x P} C {encode_RFU from_nat x Q}"
  using assms
  by (rule encode_RFU)

subsubsection \<open>Appendix C.3: Beyond Over- and Underapproximation\<close>

text \<open>The following judgment is defined in the file Expressivity.thy as follows:
\<^item> Definition 22 (k-Universal Existential): \<^term>\<open>RUE P C Q\<close>.
Note that RUE is the old name of k-UE.\<close>

text \<open>Proposition 12: k-UE triples express hyperproperties\<close>
proposition prop_12_kUE_expresses_hyperproperty:
  "RUE P C Q \<longleftrightarrow> hypersat C (hyperprop_RUE P Q)"
  by (rule RUE_express_hyperproperties)

text \<open>Proposition 13: Expressing k-UE in Hyper Hoare Logic\<close>
proposition prop_13_expressing_kUE_in_HHL:
  assumes "injective fn \<and> injective fn1 \<and> injective fn2"
      and "t \<noteq> x"
      and "injective (fn :: nat \<Rightarrow> 'a)"
      and "injective fn1"
      and "injective fn2"
      and "not_in_free_vars_double {x, t} P"
      and "not_in_free_vars_double {x, t} Q"
  shows "RUE P C Q \<longleftrightarrow> \<Turnstile> {encode_RUE_1 fn fn1 fn2 x t P} C {encode_RUE_2 fn fn1 fn2 x t Q}"
  using assms by (rule encoding_RUE)


text \<open>Example 3\<close>
proposition proving_refinement:
  fixes P :: "(('lvar \<Rightarrow> 'lval) \<times> ('pvar \<Rightarrow> 'pval)) set \<Rightarrow> bool"
    and t :: 'pvar
  assumes "(one :: 'pval) \<noteq> two" \<comment>\<open>We assume two distinct program values \<open>one\<close> and \<open>two\<close>, to represent 1 and 2.\<close>
      and "P = (\<lambda>S. card S = 1)"
      and "Q = (\<lambda>S. \<forall>\<phi>\<in>S. snd \<phi> t = two \<longrightarrow> (fst \<phi>, (snd \<phi>)(t := one)) \<in> S)"
      and "not_free_var_stmt t C1"
      and "not_free_var_stmt t C2"
  shows "refinement C2 C1 \<longleftrightarrow>
  \<Turnstile> { P } If (Seq (Assign t (\<lambda>_. one)) C1) (Seq (Assign t (\<lambda>_. two)) C2) { Q }"
proof -
  have "refinement C2 C1 \<longleftrightarrow> \<Turnstile> { P } If (Seq (Assign t (\<lambda>_. two)) C2) (Seq (Assign t (\<lambda>_. one)) C1) { Q }"
    using encoding_refinement[of two one P Q t C2 C1] assms by blast
  then show ?thesis using rewrite_if_commute by blast
qed




subsection \<open>Appendix D: Compositionality\<close>

subsubsection \<open>Appendix D.1: Compositionality Rules\<close>

text \<open>In the following, we show the rules from figure 11, in the order in which they appear.\<close>

proposition rule_Linking:
  assumes "\<And>\<phi>1 (\<phi>2 :: ('a, 'b, 'c, 'd) state). fst \<phi>1 = fst \<phi>2 \<and> ( \<turnstile> { (in_set \<phi>1 :: (('a, 'b, 'c, 'd) state) hyperassertion) } C { in_set \<phi>2 } )
  \<Longrightarrow> ( \<turnstile> { (P \<phi>1 :: (('a, 'b, 'c, 'd) state) hyperassertion) } C { Q \<phi>2 } )"
  shows "\<turnstile> { ((\<lambda>S. \<forall>\<phi>1 \<in> S. P \<phi>1 S) :: (('a, 'b, 'c, 'd) state) hyperassertion) } C { (\<lambda>S. \<forall>\<phi>2 \<in> S. Q \<phi>2 S) }"
  using assms soundness completeness rule_linking by blast

proposition rule_And:
  assumes "\<turnstile> {P} C {Q}"
      and "\<turnstile> {P'} C {Q'}"
    shows "\<turnstile> {conj P P'} C {conj Q Q'}"
  using assms soundness completeness rule_And by metis

proposition rule_Or:
  assumes "\<turnstile> {P} C {Q}"
      and "\<turnstile> {P'} C {Q'}"
    shows "\<turnstile> {disj P P'} C {disj Q Q'}"
  using assms soundness completeness rule_Or by metis

proposition rule_FrameSafe:
  assumes "wr C \<inter> fv F = {}"
      and "wf_assertion F"
      and "no_exists_state F"
    shows "\<turnstile> {interp_assert F} C {interp_assert F}"
  using safe_frame_rule_syntactic assms completeness by metis

proposition rule_Forall:
  assumes "\<And>x. \<turnstile> {P x} C {Q x}"
  shows "\<turnstile> {forall P} C {forall Q}"
  using assms soundness completeness rule_Forall by metis

proposition rule_IndexedUnion:
  assumes "\<And>x. \<turnstile> {P x} C {Q x}"
  shows "\<turnstile> {general_join P} C {general_join Q}"
  using assms soundness completeness rule_IndexedUnion by metis

proposition rule_Union:
  assumes "\<turnstile> {P} C {Q}"
      and "\<turnstile> {P'} C {Q'}"
    shows "\<turnstile> {join P P'} C {join Q Q'}"
  using assms soundness completeness rule_Union by metis

proposition rule_BigUnion:
  fixes P :: "((('a \<Rightarrow> 'b) \<times> ('c \<Rightarrow> 'd)) set \<Rightarrow> bool)"
  assumes "\<turnstile>  {P} C {Q}"
  shows "\<turnstile> {general_union P} C {general_union Q}"
  using assms soundness completeness rule_BigUnion by blast

proposition rule_Specialize:
  assumes "\<turnstile> {interp_assert P} C {interp_assert Q}"
      and "indep_of_set b"
      and "wf_assertion_aux 0 1 b"
      and "wr C \<inter> fv b = {}"
    shows "\<turnstile> { interp_assert (transform_assume b P) } C { interp_assert (transform_assume b Q) }"
  using filter_rule_syntactic assms soundness completeness by blast

text \<open>In the following, \<^term>\<open>entails_with_updates vars P P'\<close> and \<^term>\<open>invariant_on_updates vars Q\<close>
respectively correspond to the notions of entailments modulo logical variables and invariance with
respect to logical updates, as described in definition 23.\<close>

proposition rule_LUpdate:
  assumes "\<turnstile> {P'} C {Q}"
      and "entails_with_updates vars P P'"
      and "invariant_on_updates vars Q"
    shows "\<turnstile> {P} C {Q}"
  using assms soundness completeness rule_LUpdate by blast

proposition rule_LUpdateSyntactic:
  assumes "\<turnstile> { (\<lambda>S. P S \<and> e_recorded_in_t e t S) } C { Q }"
      and "not_fv_hyper t P"
      and "not_fv_hyper t Q"
    shows "\<turnstile> { P } C { Q }"
  using LUpdateS soundness completeness assms by fast

proposition rule_AtMost:
  assumes "\<turnstile> {P} C {Q}"
  shows "\<turnstile> {has_superset P} C {has_superset Q}"
  using assms soundness completeness rule_AtMost by blast

(* derived from join *)
proposition rule_AtLeast:
  assumes "\<turnstile> {P} C {Q}"
  shows "\<turnstile> {has_subset P} C {has_subset Q}"
  using assms soundness completeness rule_AtLeast by blast

proposition rule_True:
  "\<turnstile> {P} C {\<lambda>_. True}"
  using rule_True completeness by blast

proposition rule_False:
  "\<turnstile> { (\<lambda>_. False) } C {Q}"
  using rule_False completeness by blast

proposition rule_Empty:
  "\<turnstile> { (\<lambda>S. S = {}) } C { (\<lambda>S. S = {}) }"
  using completeness rule_Empty by blast


subsubsection \<open>Appendix D.2: Examples\<close>

text \<open>Example shown in figure 12. To see the actual proof, ctrl+click on @{thm composing_monotonicity_and_minimum}.\<close>
proposition fig_12_composing_monotonicity_and_minimum:
  fixes P :: "((('a \<Rightarrow> 'b) \<times> ('c \<Rightarrow> 'd)) set \<Rightarrow> bool)"
  fixes i :: 'a
  fixes x y :: 'c
  fixes leq :: "'d \<Rightarrow> 'd \<Rightarrow> bool"
  fixes one two :: 'b
  assumes "\<turnstile> { P } C1 { has_minimum x leq }"
      and "\<turnstile> { is_monotonic i x one two leq } C2 { is_monotonic i y one two leq }"
      and "\<turnstile> { (is_singleton :: ((('a \<Rightarrow> 'b) \<times> ('c \<Rightarrow> 'd)) set \<Rightarrow> bool)) } C2 { is_singleton }"
      and "one \<noteq> two" \<comment>\<open>We use distinct logical values \<open>one\<close> and \<open>two\<close> to represent 1 and 2.\<close>
      and "\<And>x. leq x x" \<comment>\<open>We assume that \<open>leq\<close> is a partial order, and thus that it satisfies reflexivity.\<close>
    shows "\<turnstile> { P } C1 ;; C2 { has_minimum y leq }"
  using assms soundness completeness composing_monotonicity_and_minimum by metis

text \<open>Example shown in figure 13. To see the actual proof, ctrl+click on @{thm composing_GNI_with_SNI}.\<close>
proposition fig_13_composing_GNI_with_SNI:
  fixes h :: 'lvar
  fixes l :: 'pvar
  assumes "\<turnstile> { (low l :: (('lvar, 'lval, 'pvar, 'pval) state) hyperassertion) } C2 { low l }"
      and "\<turnstile> { (not_empty :: (('lvar, 'lval, 'pvar, 'pval) state) hyperassertion) } C2 { not_empty }"
      and "\<turnstile> { (low l :: (('lvar, 'lval, 'pvar, 'pval) state) hyperassertion) } C1 { lGNI l h }"
    shows "\<turnstile> { (low l :: (('lvar, 'lval, 'pvar, 'pval) state) hyperassertion) } C1;; C2 { lGNI l h }"
  using assms soundness completeness composing_GNI_with_SNI by metis





subsection \<open>Appendix E: Termination-Based Reasoning\<close>

text \<open>Terminating hyper-triples (definition 24) are defined as \<^const>\<open>total_hyper_triple\<close>, and usually
written \<^term>\<open>\<Turnstile>TERM {P} C {Q}\<close>.\<close>

theorem rule_Frame:
  assumes "\<Turnstile>TERM {P} C {Q}"
      and "wr C \<inter> fv F = {}"
      and "wf_assertion F"
    shows "\<Turnstile>TERM {conj P (interp_assert F)} C {conj Q (interp_assert F)}"
  by (simp add: assms(1) assms(2) assms(3) frame_rule_syntactic)

theorem rule_WhileSyncTerm:
  assumes "\<Turnstile>TERM {conj I (\<lambda>S. \<forall>\<phi>\<in>S. b (snd \<phi>) \<and> fst \<phi> t = e (snd \<phi>))} C {conj (conj I (low_exp b)) (e_smaller_than_t e t lt)}"
      and "wfP lt"
      and "not_fv_hyper t I"
    shows "\<Turnstile>TERM {conj I (low_exp b)} while_cond b C {conj I (holds_forall (lnot b))}"
  by (meson WhileSyncTot assms(1) assms(2) assms(3))




subsection \<open>Appendix H: Synchronous Reasoning over Different Branches\<close>

text \<open>Proposition 14: Synchronous if rule\<close>
proposition prop_14_synchronized_if_rule:
  assumes "\<Turnstile> {P} C1 {P1}"
      and "\<Turnstile> {P} C2 {P2}"
      and "\<Turnstile> {combine from_nat x P1 P2} C {combine from_nat x R1 R2}"
      and "\<Turnstile> {R1} C1' {Q1}"
      and "\<Turnstile> {R2} C2' {Q2}"
      and "not_free_var_hyper x P1"
      and "not_free_var_hyper x P2"
      and "from_nat 1 \<noteq> from_nat 2" \<comment>\<open>We can represent 1 and 2 as distinct logical values.\<close>
      and "not_free_var_hyper x R1"
      and "not_free_var_hyper x R2"
    shows "\<Turnstile> {P} If (Seq C1 (Seq C C1')) (Seq C2 (Seq C C2')) {join Q1 Q2}"
  using if_sync_rule assms by meson



end