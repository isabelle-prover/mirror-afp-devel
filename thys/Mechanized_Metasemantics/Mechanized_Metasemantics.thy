theory Mechanized_Metasemantics
  imports Main
begin

section \<open>Object Language\<close>

text \<open>
  We introduce a small object language instead of using HOL bools directly.
  This allows object-language formulas to vary across possible worlds.
\<close>

datatype formula =
    Atom nat
  | FNeg formula
  | FAnd formula formula
  | FOr  formula formula


section \<open>Abstract Interpretive Structure\<close>

text \<open>
  Core schema:
  \[
    \mathrm{formula} \xrightarrow{\delta} D \xrightarrow{I} P(W)
  \]
  \[
    V = I \circ \delta
  \]

  D is not a semantic domain. It is a proof-theoretic / syntactic
  distinction space. Interpretation I transforms syntactic distinctions
  into possible-worlds truth-conditions.

  The locale abstracts the metasemantic factorization.
  Its assumptions do not add global axioms to HOL; they specify the
  class of interpretive structures to be instantiated below.
\<close>

locale Interpretive_Structure =
  fixes negD  :: "'d \<Rightarrow> 'd"
    and andD  :: "'d \<Rightarrow> 'd \<Rightarrow> 'd"
    and orD   :: "'d \<Rightarrow> 'd \<Rightarrow> 'd"
    and derD  :: "'d \<Rightarrow> 'd \<Rightarrow> bool"   (infix "\<turnstile>D" 50)
    and delta :: "formula \<Rightarrow> 'd"
    and I     :: "'d \<Rightarrow> 'w \<Rightarrow> bool"
    and R     :: "'w \<Rightarrow> 'w \<Rightarrow> bool"

  assumes delta_neg:
    "delta (FNeg \<phi>) = negD (delta \<phi>)"

  assumes delta_and:
    "delta (FAnd \<phi> \<psi>) = andD (delta \<phi>) (delta \<psi>)"

  assumes delta_or:
    "delta (FOr \<phi> \<psi>) = orD (delta \<phi>) (delta \<psi>)"

  assumes I_neg:
    "I (negD d) w \<longleftrightarrow> \<not> I d w"

  assumes I_and:
    "I (andD d1 d2) w \<longleftrightarrow> I d1 w \<and> I d2 w"

  assumes I_or:
    "I (orD d1 d2) w \<longleftrightarrow> I d1 w \<or> I d2 w"

  assumes der_sound:
    "d1 \<turnstile>D d2 \<Longrightarrow> I d1 w \<Longrightarrow> I d2 w"

begin


section \<open>Valuation and Modal Operators\<close>

definition V :: "formula \<Rightarrow> 'w \<Rightarrow> bool" where
  "V \<phi> w \<equiv> I (delta \<phi>) w"

text \<open>
  Standard valuation is reconstructed as V = I o delta.
\<close>

definition Box :: "formula \<Rightarrow> 'w \<Rightarrow> bool" where
  "Box \<phi> w \<equiv> \<forall>v. R w v \<longrightarrow> V \<phi> v"

definition Dia :: "formula \<Rightarrow> 'w \<Rightarrow> bool" where
  "Dia \<phi> w \<equiv> \<exists>v. R w v \<and> V \<phi> v"

definition Contingent :: "formula \<Rightarrow> 'w \<Rightarrow> bool" where
  "Contingent \<phi> w \<equiv> Dia \<phi> w \<and> Dia (FNeg \<phi>) w"

definition ModalClosure :: "formula \<Rightarrow> 'w \<Rightarrow> bool" where
  "ModalClosure \<phi> w \<equiv> \<not> Dia (FNeg \<phi>) w"


section \<open>Valuation Factorization\<close>

lemma valuation_factorization:
  "V \<phi> w \<longleftrightarrow> I (delta \<phi>) w"
  by (simp add: V_def)

text \<open>
  This is the formal core of the thesis:
  valuation does not eliminate interpretation; it factors through it.
\<close>


section \<open>Modal Operators Use Interpreted Distinction\<close>

lemma box_uses_interpreted_distinction:
  "Box \<phi> w \<longleftrightarrow> (\<forall>v. R w v \<longrightarrow> I (delta \<phi>) v)"
  by (simp add: Box_def V_def)

lemma dia_uses_interpreted_distinction:
  "Dia \<phi> w \<longleftrightarrow> (\<exists>v. R w v \<and> I (delta \<phi>) v)"
  by (simp add: Dia_def V_def)


section \<open>Negation and Modal Contrast\<close>

lemma interpreted_negation:
  "I (delta (FNeg \<phi>)) w \<longleftrightarrow> \<not> I (delta \<phi>) w"
  using delta_neg I_neg by simp

lemma valuation_negation:
  "V (FNeg \<phi>) w \<longleftrightarrow> \<not> V \<phi> w"
  by (simp add: V_def interpreted_negation)

lemma dia_neg_as_false_possibility:
  "Dia (FNeg \<phi>) w \<longleftrightarrow> (\<exists>v. R w v \<and> \<not> I (delta \<phi>) v)"
  by (simp add: Dia_def V_def interpreted_negation)

lemma box_as_no_false_possibility:
  "Box \<phi> w \<longleftrightarrow> \<not> (\<exists>v. R w v \<and> \<not> I (delta \<phi>) v)"
proof -
  have "Box \<phi> w \<longleftrightarrow> (\<forall>v. R w v \<longrightarrow> I (delta \<phi>) v)"
    by (simp add: box_uses_interpreted_distinction)
  also have "... \<longleftrightarrow> \<not> (\<exists>v. R w v \<and> \<not> I (delta \<phi>) v)"
    by blast
  finally show ?thesis .
qed

text \<open>
  This theorem states the modal-semantic content of necessity:
  Box phi means that no accessible world realizes the interpreted contrast
  corresponding to not-phi.
\<close>


section \<open>Possibility and Contingency\<close>

lemma contingency_requires_interpreted_contrast:
  "Contingent \<phi> w \<longleftrightarrow>
    (\<exists>v. R w v \<and> I (delta \<phi>) v) \<and>
    (\<exists>u. R w u \<and> \<not> I (delta \<phi>) u)"
  by (simp add: Contingent_def Dia_def V_def interpreted_negation)

text \<open>
  Contingency requires interpreted variation across possible worlds.
\<close>


section \<open>Necessity as Modal Closure\<close>

lemma box_iff_modal_closure:
  "Box \<phi> w \<longleftrightarrow> ModalClosure \<phi> w"
proof -
  have "Box \<phi> w \<longleftrightarrow> \<not> (\<exists>v. R w v \<and> \<not> I (delta \<phi>) v)"
    by (simp add: box_as_no_false_possibility)
  also have "... \<longleftrightarrow> \<not> Dia (FNeg \<phi>) w"
    by (simp add: Dia_def V_def interpreted_negation)
  finally show ?thesis
    by (simp add: ModalClosure_def)
qed

text \<open>
  Necessity is modal closure against the interpreted false possibility.
\<close>


section \<open>No Semantics Without Interpretation\<close>

text \<open>
  The following definitions mark the philosophical distinction:
  syntactic distinction alone is not yet modal semantic status.
\<close>

definition Interpretable :: "'d \<Rightarrow> bool" where
  "Interpretable d \<equiv> \<forall>w. I d w \<or> \<not> I d w"

definition Modally_Evaluable :: "formula \<Rightarrow> bool" where
  "Modally_Evaluable \<phi> \<equiv> Interpretable (delta \<phi>)"

lemma any_delta_interpretable:
  "Interpretable (delta \<phi>)"
  unfolding Interpretable_def
  by simp

lemma modal_evaluation_requires_interpretability:
  assumes "Box \<phi> w \<or> Dia \<phi> w"
  shows "Interpretable (delta \<phi>)"
  using any_delta_interpretable by simp

text \<open>
  This lemma is intentionally weak, because in HOL every boolean is
  evaluable once I is given. Philosophically, the point is that modal
  evaluation in this framework is always evaluation of I(delta phi).
\<close>


section \<open>Main Thesis Theorems\<close>

theorem necessity_requires_interpretive_factorization:
  "Box \<phi> w \<longleftrightarrow> (\<forall>v. R w v \<longrightarrow> I (delta \<phi>) v)"
  by (simp add: box_uses_interpreted_distinction)

theorem possibility_requires_interpretive_factorization:
  "Dia \<phi> w \<longleftrightarrow> (\<exists>v. R w v \<and> I (delta \<phi>) v)"
  by (simp add: dia_uses_interpreted_distinction)

theorem necessity_as_interpreted_false_possibility_block:
  "Box \<phi> w \<longleftrightarrow> \<not> (\<exists>v. R w v \<and> \<not> I (delta \<phi>) v)"
  by (simp add: box_as_no_false_possibility)

text \<open>
  Final formal slogan:

  Necessity is not grounded in valuation alone.
  Since V phi w is definitionally I (delta phi) w,
  modal necessity is grounded in interpreted distinction.
\<close>

end


section \<open>A Conservative Concrete Model\<close>

text \<open>
  We now give a concrete instance of the abstract locale.

  The concrete Boolean model is used only as a conservative witness:
  it shows that the locale assumptions are jointly satisfiable and that
  the factorized semantics admits genuine contingency.

  The model uses:
  \[
    W_0 = \mathrm{bool}
  \]
  \[
    D_0 = W_0 \Rightarrow \mathrm{bool}
  \]

  Thus distinctions are truth-conditions over the two-world frame.
  Interpretation is simply application.
\<close>

type_synonym W0 = bool
type_synonym D0 = "W0 \<Rightarrow> bool"


subsection \<open>Concrete Distinction Operations\<close>

definition negD0 :: "D0 \<Rightarrow> D0" where
  "negD0 d \<equiv> (\<lambda>w. \<not> d w)"

definition andD0 :: "D0 \<Rightarrow> D0 \<Rightarrow> D0" where
  "andD0 d1 d2 \<equiv> (\<lambda>w. d1 w \<and> d2 w)"

definition orD0 :: "D0 \<Rightarrow> D0 \<Rightarrow> D0" where
  "orD0 d1 d2 \<equiv> (\<lambda>w. d1 w \<or> d2 w)"

definition derD0 :: "D0 \<Rightarrow> D0 \<Rightarrow> bool" where
  "derD0 d1 d2 \<equiv> (\<forall>w. d1 w \<longrightarrow> d2 w)"


subsection \<open>Concrete Parsing, Interpretation, and Accessibility\<close>

text \<open>
  Atom 0 varies across worlds.
  Other atoms are interpreted as constantly true, only for simplicity.
\<close>

primrec delta0 :: "formula \<Rightarrow> D0" where
  "delta0 (Atom n) = (\<lambda>w. if n = 0 then w else True)"
| "delta0 (FNeg \<phi>) = negD0 (delta0 \<phi>)"
| "delta0 (FAnd \<phi> \<psi>) = andD0 (delta0 \<phi>) (delta0 \<psi>)"
| "delta0 (FOr \<phi> \<psi>) = orD0 (delta0 \<phi>) (delta0 \<psi>)"

definition I0 :: "D0 \<Rightarrow> W0 \<Rightarrow> bool" where
  "I0 d w \<equiv> d w"

definition R0 :: "W0 \<Rightarrow> W0 \<Rightarrow> bool" where
  "R0 w v \<equiv> True"


subsection \<open>Locale Interpretation\<close>

interpretation Concrete_Model:
  Interpretive_Structure negD0 andD0 orD0 derD0 delta0 I0 R0
proof
  fix \<phi> \<psi> :: formula

  show "delta0 (FNeg \<phi>) = negD0 (delta0 \<phi>)"
    by simp

  show "delta0 (FAnd \<phi> \<psi>) = andD0 (delta0 \<phi>) (delta0 \<psi>)"
    by simp

  show "delta0 (FOr \<phi> \<psi>) = orD0 (delta0 \<phi>) (delta0 \<psi>)"
    by simp

next
  fix d :: D0 and w :: W0

  show "I0 (negD0 d) w \<longleftrightarrow> \<not> I0 d w"
    by (simp add: I0_def negD0_def)

next
  fix d1 d2 :: D0 and w :: W0

  show "I0 (andD0 d1 d2) w \<longleftrightarrow> I0 d1 w \<and> I0 d2 w"
    by (simp add: I0_def andD0_def)

next
  fix d1 d2 :: D0 and w :: W0

  show "I0 (orD0 d1 d2) w \<longleftrightarrow> I0 d1 w \<or> I0 d2 w"
    by (simp add: I0_def orD0_def)

next
  fix d1 d2 :: D0 and w :: W0

  assume h1: "derD0 d1 d2"
  assume h2: "I0 d1 w"

  show "I0 d2 w"
    using h1 h2 by (simp add: derD0_def I0_def)
qed


section \<open>Concrete Non-Vacuity Witnesses\<close>

text \<open>
  The concrete model contains a non-trivial distinction varying across worlds.
\<close>

lemma concrete_has_nontrivial_distinction:
  "\<exists>d :: D0. I0 d True \<and> \<not> I0 d False"
proof
  let ?d = "\<lambda>w :: W0. w"
  show "I0 ?d True \<and> \<not> I0 ?d False"
    by (simp add: I0_def)
qed

lemma concrete_atom0_varies:
  "I0 (delta0 (Atom 0)) True \<and> \<not> I0 (delta0 (Atom 0)) False"
  by (simp add: I0_def)

lemma concrete_has_accessible_variation:
  "\<exists>d :: D0. \<exists>w v :: W0.
      R0 w v \<and> I0 d v \<and> (\<exists>u. R0 w u \<and> \<not> I0 d u)"
proof -
  let ?d = "\<lambda>x :: W0. x"
  have "R0 False True \<and> I0 ?d True \<and> (\<exists>u. R0 False u \<and> \<not> I0 ?d u)"
    by (rule conjI, simp add: R0_def,
        rule conjI, simp add: I0_def,
        rule exI[where x=False], simp add: R0_def I0_def)
  then show ?thesis
    by blast
qed


section \<open>Concrete Object-Language Modal Witnesses\<close>

text \<open>
  Since Atom 0 varies across worlds and R0 is universal, Atom 0 is
  genuinely contingent at either world.
\<close>

lemma concrete_dia_atom0:
  "Concrete_Model.Dia (Atom 0) w"
proof -
  have "R0 w True \<and> Concrete_Model.V (Atom 0) True"
    by (simp add: R0_def Concrete_Model.V_def I0_def)
  then show ?thesis
    unfolding Concrete_Model.Dia_def
    by blast
qed

lemma concrete_dia_not_atom0:
  "Concrete_Model.Dia (FNeg (Atom 0)) w"
proof -
  have "R0 w False \<and> Concrete_Model.V (FNeg (Atom 0)) False"
    by (simp add: R0_def Concrete_Model.V_def I0_def negD0_def)
  then show ?thesis
    unfolding Concrete_Model.Dia_def
    by blast
qed

lemma concrete_atom0_contingent:
  "Concrete_Model.Contingent (Atom 0) w"
  by (simp add:
      Concrete_Model.Contingent_def
      concrete_dia_atom0
      concrete_dia_not_atom0)

lemma concrete_exists_contingent_formula:
  "\<exists>\<phi> w. Concrete_Model.Contingent \<phi> w"
  using concrete_atom0_contingent by blast


section \<open>Concrete Modal Sanity Checks\<close>

lemma concrete_not_box_atom0:
  "\<not> Concrete_Model.Box (Atom 0) w"
proof -
  have "R0 w False \<and> \<not> Concrete_Model.V (Atom 0) False"
    by (simp add: R0_def Concrete_Model.V_def I0_def)
  then show ?thesis
    unfolding Concrete_Model.Box_def
    by blast
qed

lemma concrete_not_box_not_atom0:
  "\<not> Concrete_Model.Box (FNeg (Atom 0)) w"
proof -
  have "R0 w True \<and> \<not> Concrete_Model.V (FNeg (Atom 0)) True"
    by (simp add: R0_def Concrete_Model.V_def I0_def negD0_def)
  then show ?thesis
    unfolding Concrete_Model.Box_def
    by blast
qed

text \<open>
  This is the main no-collapse witness: possibility does not imply
  necessity for Atom 0 in the concrete model.
\<close>

lemma concrete_no_modal_collapse_atom0:
  "Concrete_Model.Dia (Atom 0) w \<and> \<not> Concrete_Model.Box (Atom 0) w"
  by (simp add: concrete_dia_atom0 concrete_not_box_atom0)

lemma concrete_no_modal_collapse_not_atom0:
  "Concrete_Model.Dia (FNeg (Atom 0)) w \<and> \<not> Concrete_Model.Box (FNeg (Atom 0)) w"
  by (simp add: concrete_dia_not_atom0 concrete_not_box_not_atom0)


section \<open>Concrete Unfolding of the Main Thesis\<close>

lemma concrete_valuation_factorization:
  "Concrete_Model.V \<phi> w \<longleftrightarrow> I0 (delta0 \<phi>) w"
  by (simp add: Concrete_Model.valuation_factorization)

lemma concrete_box_unfolding:
  "Concrete_Model.Box \<phi> w \<longleftrightarrow> (\<forall>v. R0 w v \<longrightarrow> I0 (delta0 \<phi>) v)"
  by (simp add: Concrete_Model.box_uses_interpreted_distinction)

lemma concrete_possibility_unfolding:
  "Concrete_Model.Dia \<phi> w \<longleftrightarrow> (\<exists>v. R0 w v \<and> I0 (delta0 \<phi>) v)"
  by (simp add: Concrete_Model.dia_uses_interpreted_distinction)

lemma concrete_necessity_as_no_false_possibility:
  "Concrete_Model.Box \<phi> w \<longleftrightarrow> \<not> (\<exists>v. R0 w v \<and> \<not> I0 (delta0 \<phi>) v)"
  by (simp add: Concrete_Model.necessity_as_interpreted_false_possibility_block)


section \<open>Summary of Contributions\<close>

text \<open>
  This theory provides:

  1. an abstract locale for interpretive modal metasemantics;
  2. an explicit object language of formulas;
  3. a parsing map delta from formulas into syntactic distinctions;
  4. valuation factorization V = I o delta;
  5. modal necessity as closure against interpreted false possibility;
  6. a conservative concrete model witnessing consistency of the locale;
  7. a non-trivial distinction witness at the D-level;
  8. an object-language contingent formula witness;
  9. a no-modal-collapse sanity check for Atom 0.

  Thus modal evaluation is formally shown to operate over interpreted
  distinctions rather than over valuation alone.
\<close>

end
