theory Proof
  imports ILL
begin

subsection\<open>Deep Embedding of Deductions\<close>

text\<open>
  To directly manipulate ILL deductions themselves we deeply embed them as a datatype.
  This datatype has a constructor to represent each introduction rule of @{const sequent}, with the
  ILL propositions and further deductions those rules use as arguments.
  Additionally, it has a constructor to represent premises (sequents assumed to be valid) which
  allow us to represent contingent deductions.

  The datatype is parameterised by two type variables:
  \<^item> @{typ 'a} represents the propositional variables for the contained ILL propositions, and
  \<^item> @{typ 'l} represents labels we associate with premises.
\<close>
datatype ('a, 'l) ill_deduct =
    Premise "'a ill_prop list" "'a ill_prop" 'l
  | Identity "'a ill_prop"
  | Exchange "'a ill_prop list" "'a ill_prop" "'a ill_prop" "'a ill_prop list" "'a ill_prop"
      "('a, 'l) ill_deduct"
  | Cut "'a ill_prop list" "'a ill_prop" "'a ill_prop list" "'a ill_prop list" "'a ill_prop"
      "('a, 'l) ill_deduct" "('a, 'l) ill_deduct"
  | TimesL "'a ill_prop list" "'a ill_prop" "'a ill_prop" "'a ill_prop list" "'a ill_prop"
      "('a, 'l) ill_deduct"
  | TimesR "'a ill_prop list" "'a ill_prop" "'a ill_prop list" "'a ill_prop" "('a, 'l) ill_deduct"
      "('a, 'l) ill_deduct"
  | OneL "'a ill_prop list" "'a ill_prop list" "'a ill_prop" "('a, 'l) ill_deduct"
  | OneR
  | LimpL "'a ill_prop list" "'a ill_prop" "'a ill_prop list" "'a ill_prop" "'a ill_prop list"
      "'a ill_prop" "('a, 'l) ill_deduct" "('a, 'l) ill_deduct"
  | LimpR "'a ill_prop list" "'a ill_prop" "'a ill_prop list" "'a ill_prop" "('a, 'l) ill_deduct"
  | WithL1 "'a ill_prop list" "'a ill_prop" "'a ill_prop" "'a ill_prop list" "'a ill_prop"
      "('a, 'l) ill_deduct"
  | WithL2 "'a ill_prop list" "'a ill_prop" "'a ill_prop" "'a ill_prop list" "'a ill_prop"
      "('a, 'l) ill_deduct"
  | WithR "'a ill_prop list" "'a ill_prop" "'a ill_prop" "('a, 'l) ill_deduct" "('a, 'l) ill_deduct"
  | TopR "'a ill_prop list"
  | PlusL "'a ill_prop list" "'a ill_prop" "'a ill_prop" "'a ill_prop list" "'a ill_prop"
      "('a, 'l) ill_deduct" "('a, 'l) ill_deduct"
  | PlusR1 "'a ill_prop list" "'a ill_prop" "'a ill_prop" "('a, 'l) ill_deduct"
  | PlusR2 "'a ill_prop list" "'a ill_prop" "'a ill_prop" "('a, 'l) ill_deduct"
  | ZeroL "'a ill_prop list" "'a ill_prop list" "'a ill_prop"
  | Weaken "'a ill_prop list" "'a ill_prop list" "'a ill_prop" "'a ill_prop" "('a, 'l) ill_deduct"
  | Contract "'a ill_prop list" "'a ill_prop" "'a ill_prop list" "'a ill_prop" "('a, 'l) ill_deduct"
  | Derelict "'a ill_prop list" "'a ill_prop" "'a ill_prop list" "'a ill_prop" "('a, 'l) ill_deduct"
  | Promote "'a ill_prop list" "'a ill_prop" "('a, 'l) ill_deduct"
(* Above definition takes long and jEdit is slowed down as long as it is shown *)

subsubsection\<open>Semantics\<close>

text\<open>
  With every deduction we associate the antecedents and consequent of its conclusion sequent
\<close>
primrec antecedents :: "('a, 'l) ill_deduct \<Rightarrow> 'a ill_prop list"
  where
    "antecedents (Premise G c l) = G"
  | "antecedents (Identity a) = [a]"
  | "antecedents (Exchange G a b D c P) = G @ [b] @ [a] @ D"
  | "antecedents (Cut G b D E c P Q) = D @ G @ E"
  | "antecedents (TimesL G a b D c P) = G @ [a \<otimes> b] @ D"
  | "antecedents (TimesR G a D b P Q) = G @ D"
  | "antecedents (OneL G D c P) = G @ [\<one>] @ D"
  | "antecedents (OneR) = []"
  | "antecedents (LimpL G a D b E c P Q) = G @ D @ [a \<rhd> b] @ E"
  | "antecedents (LimpR G a D b P) = G @ D"
  | "antecedents (WithL1 G a b D c P) = G @ [a & b] @ D"
  | "antecedents (WithL2 G a b D c P) = G @ [a & b] @ D"
  | "antecedents (WithR G a b P Q) = G"
  | "antecedents (TopR G) = G"
  | "antecedents (PlusL G a b D c P Q) = G @ [a \<oplus> b] @ D"
  | "antecedents (PlusR1 G a b P) = G"
  | "antecedents (PlusR2 G a b P) = G"
  | "antecedents (ZeroL G D c) = G @ [\<zero>] @ D"
  | "antecedents (Weaken G D b a P) = G @ [!a] @ D"
  | "antecedents (Contract G a D b P) = G @ [!a] @ D"
  | "antecedents (Derelict G a D b P) = G @ [!a] @ D"
  | "antecedents (Promote G a P) = map Exp G"

primrec consequent :: "('a, 'l) ill_deduct \<Rightarrow> 'a ill_prop"
  where
    "consequent (Premise G c l) = c"
  | "consequent (Identity a) = a"
  | "consequent (Exchange G a b D c P) = c"
  | "consequent (Cut G b D E c P Q) = c"
  | "consequent (TimesL G a b D c P) = c"
  | "consequent (TimesR G a D b P Q) = a \<otimes> b"
  | "consequent (OneL G D c P) = c"
  | "consequent (OneR) = \<one>"
  | "consequent (LimpL G a D b E c P Q) = c"
  | "consequent (LimpR G a D b P) = a \<rhd> b"
  | "consequent (WithL1 G a b D c P) = c"
  | "consequent (WithL2 G a b D c P) = c"
  | "consequent (WithR G a b P Q) = a & b"
  | "consequent (TopR G) = \<top>"
  | "consequent (PlusL G a b D c P Q) = c"
  | "consequent (PlusR1 G a b P) = a \<oplus> b"
  | "consequent (PlusR2 G a b P) = a \<oplus> b"
  | "consequent (ZeroL G D c) = c"
  | "consequent (Weaken G D b a P) = b"
  | "consequent (Contract G a D b P) = b"
  | "consequent (Derelict G a D b P) = b"
  | "consequent (Promote G a P) = !a"

text\<open>
  We define a sequent datatype for presenting deduction tree conclusions, deeply embedding (possibly
  invalid) sequents themselves.

  Note: these are not used everywhere, separate antecedents and consequent tend to work better for
  proof automation.
  For instance, the full conclusion cannot be derived where only facts about antecedents are known.
\<close>
datatype 'a ill_sequent = Sequent "'a ill_prop list" "'a ill_prop"

text\<open>Validity of deeply embedded sequents is defined by the shallow @{const sequent} relation\<close>
primrec ill_sequent_valid :: "'a ill_sequent \<Rightarrow> bool"
  where "ill_sequent_valid (Sequent a c) = a \<turnstile> c"

text\<open>
  We set up a notation bundle to have infix @{text \<turnstile>} for stand for the sequent datatype and not
  the relation
\<close>
bundle deep_sequent
begin
no_notation sequent (infix "\<turnstile>" 60)
notation Sequent (infix "\<turnstile>" 60)
end

context
  includes deep_sequent
begin

text\<open>With deeply embedded sequents we can define the conclusion of every deduction\<close>
primrec ill_conclusion :: "('a, 'l) ill_deduct \<Rightarrow> 'a ill_sequent"
  where
    "ill_conclusion (Premise G c l) = G \<turnstile> c"
  | "ill_conclusion (Identity a) = [a] \<turnstile> a"
  | "ill_conclusion (Exchange G a b D c P) = G @ [b] @ [a] @ D \<turnstile> c"
  | "ill_conclusion (Cut G b D E c P Q) = D @ G @ E \<turnstile> c"
  | "ill_conclusion (TimesL G a b D c P) = G @ [a \<otimes> b] @ D \<turnstile> c"
  | "ill_conclusion (TimesR G a D b P Q) = G @ D \<turnstile> a \<otimes> b"
  | "ill_conclusion (OneL G D c P) = G @ [\<one>] @ D \<turnstile> c"
  | "ill_conclusion (OneR) = [] \<turnstile> \<one>"
  | "ill_conclusion (LimpL G a D b E c P Q) = G @ D @ [a \<rhd> b] @ E \<turnstile> c"
  | "ill_conclusion (LimpR G a D b P) = G @ D \<turnstile> a \<rhd> b"
  | "ill_conclusion (WithL1 G a b D c P) = G @ [a & b] @ D \<turnstile> c"
  | "ill_conclusion (WithL2 G a b D c P) = G @ [a & b] @ D \<turnstile> c"
  | "ill_conclusion (WithR G a b P Q) = G \<turnstile> a & b"
  | "ill_conclusion (TopR G) = G \<turnstile> \<top>"
  | "ill_conclusion (PlusL G a b D c P Q) = G @ [a \<oplus> b] @ D \<turnstile> c"
  | "ill_conclusion (PlusR1 G a b P) = G \<turnstile> a \<oplus> b"
  | "ill_conclusion (PlusR2 G a b P) = G \<turnstile> a \<oplus> b"
  | "ill_conclusion (ZeroL G D c) = G @ [\<zero>] @ D \<turnstile> c"
  | "ill_conclusion (Weaken G D b a P) = G @ [!a] @ D \<turnstile> b"
  | "ill_conclusion (Contract G a D b P) = G @ [!a] @ D \<turnstile> b"
  | "ill_conclusion (Derelict G a D b P) = G @ [!a] @ D \<turnstile> b"
  | "ill_conclusion (Promote G a P) = map Exp G \<turnstile> !a"

text\<open>This conclusion is the same as what @{const antecedents} and @{const consequent} express\<close> 
lemma ill_conclusionI [intro!]:
  assumes "antecedents P = G"
      and "consequent P = c"
    shows "ill_conclusion P = G \<turnstile> c"
  using assms by (induction P) simp_all

lemma ill_conclusionE [elim!]:
  assumes "ill_conclusion P = G \<turnstile> c"
  obtains "antecedents P = G"
      and "consequent P = c"
  using assms by (induction P) simp_all

lemma ill_conclusion_alt:
  "(ill_conclusion P = G \<turnstile> c) = (antecedents P = G \<and> consequent P = c)"
  by blast

lemma ill_conclusion_antecedents: "ill_conclusion P = G \<turnstile> c \<Longrightarrow> antecedents P = G"
  and ill_conclusion_consequent: "ill_conclusion P = G \<turnstile> c \<Longrightarrow> consequent P = c"
  by blast+

text\<open>
  Every deduction is well-formed if all deductions it relies on are well-formed and have the form
  required by the corresponding @{const sequent} rule.
\<close>
primrec ill_deduct_wf :: "('a, 'l) ill_deduct \<Rightarrow> bool"
  where
    "ill_deduct_wf (Premise G c l) = True"
  | "ill_deduct_wf (Identity a) = True"
  | "ill_deduct_wf (Exchange G a b D c P) =
      (ill_deduct_wf P \<and> ill_conclusion P = G @ [a] @ [b] @ D \<turnstile> c)"
  | "ill_deduct_wf (Cut G b D E c P Q) =
      ( ill_deduct_wf P \<and> ill_conclusion P = G \<turnstile> b \<and>
        ill_deduct_wf Q \<and> ill_conclusion Q = D @ [b] @ E \<turnstile> c)"
  | "ill_deduct_wf (TimesL G a b D c P) =
      (ill_deduct_wf P \<and> ill_conclusion P = G @ [a] @ [b] @ D \<turnstile> c)"
  | "ill_deduct_wf (TimesR G a D b P Q) =
      ( ill_deduct_wf P \<and> ill_conclusion P = G \<turnstile> a \<and>
        ill_deduct_wf Q \<and> ill_conclusion Q = D \<turnstile> b)"
  | "ill_deduct_wf (OneL G D c P) =
      (ill_deduct_wf P \<and> ill_conclusion P = G @ D \<turnstile> c)"
  | "ill_deduct_wf (OneR) = True"
  | "ill_deduct_wf (LimpL G a D b E c P Q) =
      ( ill_deduct_wf P \<and> ill_conclusion P = G \<turnstile> a \<and>
        ill_deduct_wf Q \<and> ill_conclusion Q = D @ [b] @ E \<turnstile> c)"
  | "ill_deduct_wf (LimpR G a D b P) =
      (ill_deduct_wf P \<and> ill_conclusion P = G @ [a] @ D \<turnstile> b)"
  | "ill_deduct_wf (WithL1 G a b D c P) =
      (ill_deduct_wf P \<and> ill_conclusion P = G @ [a] @ D \<turnstile> c)"
  | "ill_deduct_wf (WithL2 G a b D c P) =
      (ill_deduct_wf P \<and> ill_conclusion P = G @ [b] @ D \<turnstile> c)"
  | "ill_deduct_wf (WithR G a b P Q) =
      ( ill_deduct_wf P \<and> ill_conclusion P = G \<turnstile> a \<and>
        ill_deduct_wf Q \<and> ill_conclusion Q = G \<turnstile> b)"
  | "ill_deduct_wf (TopR G) = True"
  | "ill_deduct_wf (PlusL G a b D c P Q) =
      ( ill_deduct_wf P \<and> ill_conclusion P = G @ [a] @ D \<turnstile> c \<and>
        ill_deduct_wf Q \<and> ill_conclusion Q = G @ [b] @ D \<turnstile> c)"
  | "ill_deduct_wf (PlusR1 G a b P) =
      (ill_deduct_wf P \<and> ill_conclusion P = G \<turnstile> a)"
  | "ill_deduct_wf (PlusR2 G a b P) =
      (ill_deduct_wf P \<and> ill_conclusion P = G \<turnstile> b)"
  | "ill_deduct_wf (ZeroL G D c) = True"
  | "ill_deduct_wf (Weaken G D b a P) =
      (ill_deduct_wf P \<and> ill_conclusion P = G @ D \<turnstile> b)"
  | "ill_deduct_wf (Contract G a D b P) =
      (ill_deduct_wf P \<and> ill_conclusion P = G @ [!a] @ [!a] @ D \<turnstile> b)"
  | "ill_deduct_wf (Derelict G a D b P) =
      (ill_deduct_wf P \<and> ill_conclusion P = G @ [a] @ D \<turnstile> b)"
  | "ill_deduct_wf (Promote G a P) =
      (ill_deduct_wf P \<and> ill_conclusion P = map Exp G \<turnstile> a)"

text\<open>
  In some proofs phasing well-formedness in terms of @{const antecedents} and @{const consequent} is
  more useful.
\<close>
lemmas ill_deduct_wf_alt = ill_deduct_wf.simps[unfolded ill_conclusion_alt]

end

text\<open>
  Premises of a deduction can be gathered recursively.
  Because every element of the result is an instance of @{const Premise}, we represent them with the
  relevant three parameters (antecedents, consequent, label).
\<close>
primrec ill_deduct_premises
    :: "('a, 'l) ill_deduct \<Rightarrow> ('a ill_prop list \<times> 'a ill_prop \<times> 'l) list"
  where
    "ill_deduct_premises (Premise G c l) = [(G, c, l)]"
  | "ill_deduct_premises (Identity a) = []"
  | "ill_deduct_premises (Exchange G a b D c P) = ill_deduct_premises P"
  | "ill_deduct_premises (Cut G b D E c P Q) =
      (ill_deduct_premises P @ ill_deduct_premises Q)"
  | "ill_deduct_premises (TimesL G a b D c P) = ill_deduct_premises P"
  | "ill_deduct_premises (TimesR G a D b P Q) =
      (ill_deduct_premises P @ ill_deduct_premises Q)"
  | "ill_deduct_premises (OneL G D c P) = ill_deduct_premises P"
  | "ill_deduct_premises (OneR) = []"
  | "ill_deduct_premises (LimpL G a D b E c P Q) =
      (ill_deduct_premises P @ ill_deduct_premises Q)"
  | "ill_deduct_premises (LimpR G a D b P) = ill_deduct_premises P"
  | "ill_deduct_premises (WithL1 G a b D c P) = ill_deduct_premises P"
  | "ill_deduct_premises (WithL2 G a b D c P) = ill_deduct_premises P"
  | "ill_deduct_premises (WithR G a b P Q) =
      (ill_deduct_premises P @ ill_deduct_premises Q)"
  | "ill_deduct_premises (TopR G) = []"
  | "ill_deduct_premises (PlusL G a b D c P Q) =
      (ill_deduct_premises P @ ill_deduct_premises Q)"
  | "ill_deduct_premises (PlusR1 G a b P) = ill_deduct_premises P"
  | "ill_deduct_premises (PlusR2 G a b P) = ill_deduct_premises P"
  | "ill_deduct_premises (ZeroL G D c) = []"
  | "ill_deduct_premises (Weaken G D b a P) = ill_deduct_premises P"
  | "ill_deduct_premises (Contract G a D b P) = ill_deduct_premises P"
  | "ill_deduct_premises (Derelict G a D b P) = ill_deduct_premises P"
  | "ill_deduct_premises (Promote G a P) = ill_deduct_premises P"

subsubsection\<open>Soundness\<close>

text\<open>
  Deeply embedded deductions are sound with respect to @{const sequent} in the sense that the
  conclusion of any well-formed deduction is a valid sequent if all of its premises are assumed to
  be valid sequents.
  This is proven easily, because our definitions stem from the @{const sequent} relation.
\<close>
lemma ill_deduct_sound:
  assumes "ill_deduct_wf P"
      and "\<And>a c l. (a, c, l) \<in> set (ill_deduct_premises P) \<Longrightarrow> ill_sequent_valid (Sequent a c)"
    shows "ill_sequent_valid (ill_conclusion P)"
  using assms
proof (induct P)
  case (Premise G c l) then show ?case by simp next
  case (Identity x) then show ?case by simp next
  case (Exchange x1a x2 x3 x4 x5 x6) then show ?case using exchange by simp blast next
  case (Cut x1a x2 x3 x4 x5 x6 x7) then show ?case using cut by simp blast next
  case (TimesL x1a x2 x3 x4 x5 x6) then show ?case using timesL by simp blast next
  case (TimesR x1a x2 x3 x4 x5 x6) then show ?case using timesR by simp blast next
  case (OneL x1a x1b x2 x3) then show ?case using oneL by simp blast next
  case OneR then show ?case using oneR by simp next
  case (LimpL x1a x2 x3 x4 x5 x6 x7) then show ?case using limpL by simp blast next
  case (LimpR x1a x2 x3 x4 x5) then show ?case using limpR by simp blast next
  case (WithL1 x1a x2 x3 x4 x5 x6) then show ?case using withL1 by simp blast next
  case (WithL2 x1a x2 x3 x4 x5 x6) then show ?case using withL2 by simp blast next
  case (WithR x1a x2 x3 x4 x5) then show ?case using withR by simp blast next
  case (TopR x) then show ?case using topR by simp blast next
  case (PlusL x1a x2 x3 x4 x5 x6 x7) then show ?case using plusL by simp blast next
  case (PlusR1 x1a x2 x3 x4) then show ?case using plusR1 by simp blast next
  case (PlusR2 x1a x2 x3 x4) then show ?case using plusR2 by simp blast next
  case (ZeroL x1a x2 x3) then show ?case using zeroL by simp blast next
  case (Weaken x1a x2 x3 x4 x5) then show ?case using weaken by simp blast next
  case (Contract x1a x2 x3 x4 x5) then show ?case using contract by simp blast next
  case (Derelict x1a x2 x3 x4 x5) then show ?case using derelict by simp blast next
  case (Promote x1a x2 x3) then show ?case using promote by simp blast
qed

subsubsection\<open>Completeness\<close>

text\<open>
  Deeply embedded deductions are complete with respect to @{const sequent} in the sense that for
  any valid sequent there exists a well-formed deduction with no premises that has it as its
  conclusion.
  This is proven easily, because the deduction nodes map directly onto the rules of the
  @{const sequent} relation.
\<close>
lemma ill_deduct_complete:
  assumes "G \<turnstile> c"
    shows "\<exists>P. ill_conclusion P = Sequent G c \<and> ill_deduct_wf P \<and> ill_deduct_premises P = []"
  using assms
proof (induction rule: sequent.induct)
  case (identity a)
  then show ?case
    using ill_conclusion.simps(2) by fastforce
next
  case (exchange G a b D c)
  then obtain P :: "('a, 'b) ill_deduct"
    where "ill_conclusion P = Sequent (G @ [a] @ [b] @ D) c \<and> ill_deduct_wf P \<and> ill_deduct_premises P = []"
    by blast
  then have "ill_deduct_wf (Exchange G a b D c P)" and "ill_deduct_premises (Exchange G a b D c P) = []"
    by simp_all
  then show ?case
    by (meson ill_conclusion.simps(3))
next
  case (cut G b D E c)
  then obtain P Q :: "('a, 'b) ill_deduct"
    where "ill_conclusion P = Sequent G b \<and> ill_deduct_wf P \<and> ill_deduct_premises P = []"
      and "ill_conclusion Q = Sequent (D @ [b] @ E) c \<and> ill_deduct_wf Q \<and> ill_deduct_premises Q = []"
    by blast
  then have "ill_deduct_wf (Cut G b D E c P Q)" and "ill_deduct_premises (Cut G b D E c P Q) = []"
    by simp_all
  then show ?case
    by (meson ill_conclusion.simps(4))
next
  case (timesL G a b D c)
  then obtain P :: "('a, 'b) ill_deduct"
    where "ill_conclusion P = Sequent (G @ [a] @ [b] @ D) c \<and> ill_deduct_wf P \<and> ill_deduct_premises P = []"
    by blast
  then have "ill_deduct_wf (TimesL G a b D c P)" and "ill_deduct_premises (TimesL G a b D c P) = []"
    by simp_all
  then show ?case
    by (meson ill_conclusion.simps(5))
next
  case (timesR G a D b)
  then obtain P Q :: "('a, 'b) ill_deduct"
    where "ill_conclusion P = Sequent G a \<and> ill_deduct_wf P \<and> ill_deduct_premises P = []"
      and "ill_conclusion Q = Sequent D b \<and> ill_deduct_wf Q \<and> ill_deduct_premises Q = []"
    by blast
  then have "ill_deduct_wf (TimesR G a D b P Q)" and "ill_deduct_premises (TimesR G a D b P Q) = []"
    by simp_all
  then show ?case
    by (meson ill_conclusion.simps(6))
next
  case (oneL G D c)
  then obtain P :: "('a, 'b) ill_deduct"
    where "ill_conclusion P = Sequent (G @ D) c \<and> ill_deduct_wf P \<and> ill_deduct_premises P = []"
    by blast
  then have "ill_deduct_wf (OneL G D c P)" and "ill_deduct_premises (OneL G D c P) = []"
    by simp_all
  then show ?case
    by (meson ill_conclusion.simps(7))
next
  case oneR
  then show ?case
    using ill_conclusion.simps(8) by fastforce
next
  case (limpL G a D b E c)
  then obtain P Q :: "('a, 'b) ill_deduct"
    where "ill_conclusion P = Sequent G a \<and> ill_deduct_wf P \<and> ill_deduct_premises P = []"
      and "ill_conclusion Q = Sequent (D @ [b] @ E) c \<and> ill_deduct_wf Q \<and> ill_deduct_premises Q = []"
    by blast
  then have "ill_deduct_wf (LimpL G a D b E c P Q)" and "ill_deduct_premises (LimpL G a D b E c P Q) = []"
    by simp_all
  then show ?case
    by (meson ill_conclusion.simps(9))
next
  case (limpR G a D b)
  then obtain P :: "('a, 'b) ill_deduct"
    where "ill_conclusion P = Sequent (G @ [a] @ D) b \<and> ill_deduct_wf P \<and> ill_deduct_premises P = []"
    by blast
  then have "ill_deduct_wf (LimpR G a D b P)" and "ill_deduct_premises (LimpR G a D b P) = []"
    by simp_all
  then show ?case
    by (meson ill_conclusion.simps(10))
next
  case (withL1 G a D c b)
  then obtain P :: "('a, 'b) ill_deduct"
    where "ill_conclusion P = Sequent (G @ [a] @ D) c \<and> ill_deduct_wf P \<and> ill_deduct_premises P = []"
    by blast
  then have "ill_deduct_wf (WithL1 G a b D c P)" and "ill_deduct_premises (WithL1 G a b D c P) = []"
    by simp_all
  then show ?case
    by (meson ill_conclusion.simps(11))
next
  case (withL2 G b D c a)
  then obtain P :: "('a, 'b) ill_deduct"
    where "ill_conclusion P = Sequent (G @ [b] @ D) c \<and> ill_deduct_wf P \<and> ill_deduct_premises P = []"
    by blast
  then have "ill_deduct_wf (WithL2 G a b D c P)" and "ill_deduct_premises (WithL2 G a b D c P) = []"
    by simp_all
  then show ?case
    by (meson ill_conclusion.simps(12))
next
  case (withR G a b)
  then obtain P Q :: "('a, 'b) ill_deduct"
    where "ill_conclusion P = Sequent G a \<and> ill_deduct_wf P \<and> ill_deduct_premises P = []"
      and "ill_conclusion Q = Sequent G b \<and> ill_deduct_wf Q \<and> ill_deduct_premises Q = []"
    by blast
  then have "ill_deduct_wf (WithR G a b P Q)" and "ill_deduct_premises (WithR G a b P Q) = []"
    by simp_all
  then show ?case
    by (meson ill_conclusion.simps(13))
next
  case (topR G)
  then show ?case
    using ill_conclusion.simps(14) by fastforce
next
  case (plusL G a D c b)
  then obtain P Q :: "('a, 'b) ill_deduct"
    where "ill_conclusion P = Sequent (G @ [a] @ D) c \<and> ill_deduct_wf P \<and> ill_deduct_premises P = []"
      and "ill_conclusion Q = Sequent (G @ [b] @ D) c \<and> ill_deduct_wf Q \<and> ill_deduct_premises Q = []"
    by blast
  then have "ill_deduct_wf (PlusL G a b D c P Q)" and "ill_deduct_premises (PlusL G a b D c P Q) = []"
    by simp_all
  then show ?case
    by (meson ill_conclusion.simps(15))
next
  case (plusR1 G a b)
  then obtain P :: "('a, 'b) ill_deduct"
    where "ill_conclusion P = Sequent G a \<and> ill_deduct_wf P \<and> ill_deduct_premises P = []"
    by blast
  then have "ill_deduct_wf (PlusR1 G a b P)" and "ill_deduct_premises (PlusR1 G a b P) = []"
    by simp_all
  then show ?case
    by (meson ill_conclusion.simps(16))
next
  case (plusR2 G b a)
  then obtain P :: "('a, 'b) ill_deduct"
    where "ill_conclusion P = Sequent G b \<and> ill_deduct_wf P \<and> ill_deduct_premises P = []"
    by blast
  then have "ill_deduct_wf (PlusR2 G a b P)" and "ill_deduct_premises (PlusR2 G a b P) = []"
    by simp_all
  then show ?case
    by (meson ill_conclusion.simps(17))
next
  case (zeroL G D c)
  then show ?case
    using ill_conclusion.simps(18) by fastforce
next
  case (weaken G D b a)
  then obtain P :: "('a, 'b) ill_deduct"
    where "ill_conclusion P = Sequent (G @ D) b \<and> ill_deduct_wf P \<and> ill_deduct_premises P = []"
    by blast
  then have "ill_deduct_wf (Weaken G D b a P)" and "ill_deduct_premises (Weaken G D b a P) = []"
    by simp_all
  then show ?case
    by (meson ill_conclusion.simps(19))
next
  case (contract G a D b)
  then obtain P :: "('a, 'b) ill_deduct"
    where "ill_conclusion P = Sequent (G @ [! a] @ [! a] @ D) b \<and> ill_deduct_wf P \<and> ill_deduct_premises P = []"
    by blast
  then have "ill_deduct_wf (Contract G a D b P)" and "ill_deduct_premises (Contract G a D b P) = []"
    by simp_all
  then show ?case
    by (meson ill_conclusion.simps(20))
next
  case (derelict G a D b)
  then obtain P :: "('a, 'b) ill_deduct"
    where "ill_conclusion P = Sequent (G @ [a] @ D) b \<and> ill_deduct_wf P \<and> ill_deduct_premises P = []"
    by blast
  then have "ill_deduct_wf (Derelict G a D b P)" and "ill_deduct_premises (Derelict G a D b P) = []"
    by simp_all
  then show ?case
    by (meson ill_conclusion.simps(21))
next
  case (promote G a)
  then obtain P :: "('a, 'b) ill_deduct"
    where "ill_conclusion P = Sequent (map Exp G) a \<and> ill_deduct_wf P \<and> ill_deduct_premises P = []"
    by blast
  then have "ill_deduct_wf (Promote G a P)" and "ill_deduct_premises (Promote G a P) = []"
    by simp_all
  then show ?case
    by (meson ill_conclusion.simps(22))
qed

subsubsection\<open>Derived Deductions\<close>

text\<open>
  We define a number of useful deduction patterns as (potentially recursive) functions.
  In each case we verify the well-formedness, conclusion and premises.
\<close>

text\<open>Swap order in a times proposition: @{prop "[a \<otimes> b] \<turnstile> b \<otimes> a"}:\<close>
fun ill_deduct_swap :: "'a ill_prop \<Rightarrow> 'a ill_prop \<Rightarrow> ('a, 'l) ill_deduct"
  where "ill_deduct_swap a b =
    TimesL [] a b [] (b \<otimes> a)
    ( Exchange [] b a [] (b \<otimes> a)
      ( TimesR [b] b [a] a (Identity b) (Identity a)))"

lemma ill_deduct_swap [simp]:
  "ill_deduct_wf (ill_deduct_swap a b)"
  "ill_conclusion (ill_deduct_swap a b) = Sequent [a \<otimes> b] (b \<otimes> a)"
  "ill_deduct_premises (ill_deduct_swap a b) = []"
  by simp_all

text\<open>Simplified cut rule: @{prop "\<lbrakk>G \<turnstile> b; [b] \<turnstile> c\<rbrakk> \<Longrightarrow> G \<turnstile> c"}:\<close>
fun ill_deduct_simple_cut :: "('a, 'l) ill_deduct \<Rightarrow> ('a, 'l) ill_deduct \<Rightarrow> ('a, 'l) ill_deduct"
  where "ill_deduct_simple_cut P Q = Cut (antecedents P) (consequent P) [] [] (consequent Q) P Q"

lemma ill_deduct_simple_cut [simp]:
  "\<lbrakk>[consequent P] = antecedents Q; ill_deduct_wf P; ill_deduct_wf Q\<rbrakk> \<Longrightarrow>
    ill_deduct_wf (ill_deduct_simple_cut P Q)"
  "[consequent P] = antecedents Q \<Longrightarrow>
    ill_conclusion (ill_deduct_simple_cut P Q) = Sequent (antecedents P) (consequent Q)"
  "ill_deduct_premises (ill_deduct_simple_cut P Q) = ill_deduct_premises P @ ill_deduct_premises Q"
  by simp_all blast

text\<open>Combine two deductions with times: @{prop "\<lbrakk>[a] \<turnstile> b; [c] \<turnstile> d\<rbrakk> \<Longrightarrow> [a \<otimes> c] \<turnstile> b \<otimes> d"}:\<close>
fun ill_deduct_tensor :: "('a, 'l) ill_deduct \<Rightarrow> ('a, 'l) ill_deduct \<Rightarrow> ('a, 'l) ill_deduct"
  where "ill_deduct_tensor p q =
    TimesL [] (hd (antecedents p)) (hd (antecedents q)) [] (consequent p \<otimes> consequent q)
      (TimesR (antecedents p) (consequent p) (antecedents q) (consequent q) p q)"

lemma ill_deduct_tensor [simp]:
  "\<lbrakk>antecedents P = [a]; antecedents Q = [c]; ill_deduct_wf P; ill_deduct_wf Q\<rbrakk> \<Longrightarrow>
    ill_deduct_wf (ill_deduct_tensor P Q)"
  "\<lbrakk>antecedents P = [a]; antecedents Q = [c]\<rbrakk> \<Longrightarrow>
    ill_conclusion (ill_deduct_tensor P Q) = Sequent [a \<otimes> c] (consequent P \<otimes> consequent Q)"
  "ill_deduct_premises (ill_deduct_tensor P Q) = ill_deduct_premises P @ ill_deduct_premises Q"
  by simp_all blast

text\<open>Associate times proposition to right: @{prop "[(a \<otimes> b) \<otimes> c] \<turnstile> a \<otimes> (b \<otimes> c)"}:\<close>
fun ill_deduct_assoc :: "'a ill_prop \<Rightarrow> 'a ill_prop \<Rightarrow> 'a ill_prop \<Rightarrow> ('a, 'l) ill_deduct"
  where "ill_deduct_assoc a b c =
    TimesL [] (a \<otimes> b) c [] (a \<otimes> (b \<otimes> c))
    ( Exchange [] c (a \<otimes> b) [] (a \<otimes> (b \<otimes> c))
      ( TimesL [c] a b [] (a \<otimes> (b \<otimes> c))
        ( Exchange [] a c [b] (a \<otimes> (b \<otimes> c))
          ( TimesR [a] a [c, b] (b \<otimes> c)
            ( Identity a)
            ( Exchange [] b c [] (b \<otimes> c)
              ( TimesR [b] b [c] c
                ( Identity b)
                ( Identity c)))))))"

lemma ill_deduct_assoc [simp]:
  "ill_deduct_wf (ill_deduct_assoc a b c)"
  "ill_conclusion (ill_deduct_assoc a b c) = Sequent [(a \<otimes> b) \<otimes> c] (a \<otimes> (b \<otimes> c))"
  "ill_deduct_premises (ill_deduct_assoc a b c) = []"
  by simp_all

text\<open>Associate times proposition to left: @{prop "[a \<otimes> (b \<otimes> c)] \<turnstile> (a \<otimes> b) \<otimes> c"}:\<close>
fun ill_deduct_assoc' :: "'a ill_prop \<Rightarrow> 'a ill_prop \<Rightarrow> 'a ill_prop \<Rightarrow> ('a, 'l) ill_deduct"
  where "ill_deduct_assoc' a b c =
    TimesL [] a (b \<otimes> c) [] ((a \<otimes> b) \<otimes> c)
    ( TimesL [a] b c [] ((a \<otimes> b) \<otimes> c)
      ( TimesR [a, b] (a \<otimes> b) [c] c
        ( TimesR [a] a [b] b
          ( Identity a)
          ( Identity b))
        ( Identity c)))"


lemma ill_deduct_assoc' [simp]:
  "ill_deduct_wf (ill_deduct_assoc' a b c)"
  "ill_conclusion (ill_deduct_assoc' a b c) = Sequent [a \<otimes> (b \<otimes> c)] ((a \<otimes> b) \<otimes> c)"
  "ill_deduct_premises (ill_deduct_assoc' a b c) = []"
  by simp_all

text\<open>Eliminate times unit a proposition: @{prop "[a \<otimes> \<one>] \<turnstile> a"}:\<close>
fun ill_deduct_unit :: "'a ill_prop \<Rightarrow> ('a, 'l) ill_deduct"
  where "ill_deduct_unit a = TimesL [] a (\<one>) [] a (OneL [a] [] a (Identity a))"

lemma ill_deduct_unit [simp]:
  "ill_deduct_wf (ill_deduct_unit a)"
  "ill_conclusion (ill_deduct_unit a) = Sequent [a \<otimes> \<one>] a"
  "ill_deduct_premises (ill_deduct_unit a) = []"
  by simp_all

text\<open>Introduce times unit into a proposition @{prop "[a] \<turnstile> a \<otimes> \<one>"}:\<close>
fun ill_deduct_unit' :: "'a ill_prop \<Rightarrow> ('a, 'l) ill_deduct"
  where "ill_deduct_unit' a = TimesR [a] a [] (\<one>) (Identity a) OneR"

lemma ill_deduct_unit' [simp]:
  "ill_deduct_wf (ill_deduct_unit' a)"
  "ill_conclusion (ill_deduct_unit' a) = Sequent [a] (a \<otimes> \<one>)"
  "ill_deduct_premises (ill_deduct_unit' a) = []"
  by simp_all

text\<open>Simplified weakening: @{prop "[!a] \<turnstile> \<one>"}:\<close>
fun ill_deduct_simple_weaken :: "'a ill_prop \<Rightarrow> ('a, 'l) ill_deduct"
  where "ill_deduct_simple_weaken a = Weaken [] [] (\<one>) a OneR"

lemma ill_deduct_simple_weaken [simp]:
  "ill_deduct_wf (ill_deduct_simple_weaken a)"
  "ill_conclusion (ill_deduct_simple_weaken a) = Sequent [!a] \<one>"
  "ill_deduct_premises (ill_deduct_simple_weaken a) = []"
  by simp_all

text\<open>Simplified dereliction: @{prop "[!a] \<turnstile> a"}:\<close>
fun ill_deduct_dereliction :: "'a ill_prop \<Rightarrow> ('a, 'l) ill_deduct"
  where "ill_deduct_dereliction a = Derelict [] a [] a (Identity a)"

lemma ill_deduct_dereliction [simp]:
  "ill_deduct_wf (ill_deduct_dereliction a)"
  "ill_conclusion (ill_deduct_dereliction a) = Sequent [!a] a"
  "ill_deduct_premises (ill_deduct_dereliction a) = []"
  by simp_all

text\<open>Duplicate exponentiated proposition: @{prop "[!a] \<turnstile> !a \<otimes> !a"}:\<close>
fun ill_deduct_duplicate :: "'a ill_prop \<Rightarrow> ('a, 'l) ill_deduct"
  where "ill_deduct_duplicate a =
    Contract [] a [] (!a \<otimes> !a) (TimesR [!a] (!a) [!a] (!a) (Identity (!a)) (Identity (!a)))"

lemma ill_deduct_duplicate [simp]:
  "ill_deduct_wf (ill_deduct_duplicate a)"
  "ill_conclusion (ill_deduct_duplicate a) = Sequent [!a] (!a \<otimes> !a)"
  "ill_deduct_premises (ill_deduct_duplicate a) = []"
  by simp_all

text\<open>Simplified plus elimination: @{prop "\<lbrakk>[a] \<turnstile> c; [b] \<turnstile> c\<rbrakk> \<Longrightarrow> [a \<oplus> b] \<turnstile> c"}:\<close>
fun ill_deduct_simple_plusL :: "('a, 'l) ill_deduct \<Rightarrow> ('a, 'l) ill_deduct \<Rightarrow> ('a, 'l) ill_deduct"
  where "ill_deduct_simple_plusL p q =
    PlusL [] (hd (antecedents p)) (hd (antecedents q)) [] (consequent p) p q"

lemma ill_deduct_simple_plusL [simp]:
  "\<lbrakk> antecedents P = [a]; antecedents Q = [b]; ill_deduct_wf P
   ; ill_deduct_wf Q; consequent P = consequent Q\<rbrakk> \<Longrightarrow>
    ill_deduct_wf (ill_deduct_simple_plusL P Q)"
  "\<lbrakk>antecedents P = [a]; antecedents Q = [b]\<rbrakk> \<Longrightarrow>
    ill_conclusion (ill_deduct_simple_plusL P Q) = Sequent [a \<oplus> b] (consequent P)"
  " ill_deduct_premises (ill_deduct_simple_plusL P Q)
  = ill_deduct_premises P @ ill_deduct_premises Q"
  by simp_all blast

text\<open>Simplified left plus introduction: @{prop "[a] \<turnstile> a \<oplus> b"}:\<close>
fun ill_deduct_plusR1 :: "'a ill_prop \<Rightarrow> 'a ill_prop \<Rightarrow> ('a, 'l) ill_deduct"
  where "ill_deduct_plusR1 a b = PlusR1 [a] a b (Identity a)"

lemma ill_deduct_plusR1 [simp]:
  "ill_deduct_wf (ill_deduct_plusR1 a b)"
  "ill_conclusion (ill_deduct_plusR1 a b) = Sequent [a] (a \<oplus> b)"
  "ill_deduct_premises (ill_deduct_plusR1 a b) = []"
  by simp_all

text\<open>Simplified right plus introduction: @{prop "[b] \<turnstile> a \<oplus> b"}:\<close>
fun ill_deduct_plusR2 :: "'a ill_prop \<Rightarrow> 'a ill_prop \<Rightarrow> ('a, 'l) ill_deduct"
  where "ill_deduct_plusR2 a b = PlusR2 [b] a b (Identity b)"

lemma ill_deduct_plusR2 [simp]:
  "ill_deduct_wf (ill_deduct_plusR2 a b)"
  "ill_conclusion (ill_deduct_plusR2 a b) = Sequent [b] (a \<oplus> b)"
  "ill_deduct_premises (ill_deduct_plusR2 a b) = []"
  by simp_all

text\<open>Simplified linear implication introduction: @{prop "[a] \<turnstile> b \<Longrightarrow> [\<one>] \<turnstile> a \<rhd> b"}:\<close>
fun ill_deduct_simple_limpR :: "('a, 'l) ill_deduct \<Rightarrow> ('a, 'l) ill_deduct"
  where "ill_deduct_simple_limpR p =
    LimpR [] (hd (antecedents p)) [\<one>] (consequent p)
    ( OneL [hd (antecedents p)] [] (consequent p) p)"

lemma ill_deduct_simple_limpR [simp]:
  "\<lbrakk>antecedents P = [a]; consequent P = b; ill_deduct_wf P\<rbrakk> \<Longrightarrow>
    ill_deduct_wf (ill_deduct_simple_limpR P)"
  "\<lbrakk>antecedents P = [a]; consequent P = b\<rbrakk> \<Longrightarrow>
    ill_conclusion (ill_deduct_simple_limpR P) = Sequent [\<one>] (a \<rhd> b)"
  " ill_deduct_premises (ill_deduct_simple_limpR P)
  = ill_deduct_premises P"
  by simp_all blast

text\<open>Simplified introduction of exponentiated impliciation: @{prop "[a] \<turnstile> b \<Longrightarrow> [\<one>] \<turnstile> !(a \<rhd> b)"}:\<close>
fun ill_deduct_simple_limpR_exp :: "('a, 'l) ill_deduct \<Rightarrow> ('a, 'l) ill_deduct"
  where "ill_deduct_simple_limpR_exp p =
    OneL [] [] (!((hd (antecedents p)) \<rhd> (consequent p)))
    ( Promote [] ((hd (antecedents p)) \<rhd> (consequent p))
      ( ill_deduct_simple_cut
        OneR
        ( ill_deduct_simple_limpR p)))"

lemma ill_deduct_simple_limpR_exp [simp]:
  "\<lbrakk>antecedents P = [a]; consequent P = b; ill_deduct_wf P\<rbrakk> \<Longrightarrow>
    ill_deduct_wf (ill_deduct_simple_limpR_exp P)"
  "\<lbrakk>antecedents P = [a]; consequent P = b\<rbrakk> \<Longrightarrow>
    ill_conclusion (ill_deduct_simple_limpR_exp P) = Sequent [\<one>] (!(a \<rhd> b))"
  "ill_deduct_premises (ill_deduct_simple_limpR_exp P) = ill_deduct_premises P"
  by simp_all blast

text\<open>Linear implication elimination with times: @{prop "[a \<otimes> a \<rhd> b] \<turnstile> b"}:\<close>
fun ill_deduct_limp_eval :: "'a ill_prop \<Rightarrow> 'a ill_prop \<Rightarrow> ('a, 'l) ill_deduct"
  where "ill_deduct_limp_eval a b =
    TimesL [] a (a \<rhd> b) [] b (LimpL [a] a [] b [] b (Identity a) (Identity b))"

lemma ill_deduct_limp_eval [simp]:
  "ill_deduct_wf (ill_deduct_limp_eval a b)"
  "ill_conclusion (ill_deduct_limp_eval a b) = Sequent [a \<otimes> a \<rhd> b] b"
  "ill_deduct_premises (ill_deduct_limp_eval a b) = []"
  by simp_all

text\<open>Exponential implication elimination with times: @{prop "[a \<otimes> !(a \<rhd> b)] \<turnstile> b \<otimes> !(a \<rhd> b)"}:\<close>
fun ill_deduct_explimp_eval :: "'a ill_prop \<Rightarrow> 'a ill_prop \<Rightarrow> ('a, 'l) ill_deduct"
  where "ill_deduct_explimp_eval a b =
    TimesL [] a (!(a \<rhd> b)) [] (b \<otimes> !(a \<rhd> b)) (
    Contract [a] (a \<rhd> b) [] (b \<otimes> !(a \<rhd> b)) (
    TimesR [a, !(a \<rhd> b)] b [!(a \<rhd> b)] (!(a \<rhd> b))
    ( Derelict [a] (a \<rhd> b) [] b (
      LimpL [a] a [] b [] b
      ( Identity a)
      ( Identity b)))
    ( Identity (!(a \<rhd> b)))))"

lemma ill_deduct_explimp_eval [simp]:
  "ill_deduct_wf (ill_deduct_explimp_eval a b)"
  "ill_conclusion (ill_deduct_explimp_eval a b) = Sequent [a \<otimes> !(a \<rhd> b)] (b \<otimes> !(a \<rhd> b))"
  "ill_deduct_premises (ill_deduct_explimp_eval a b) = []"
  by simp_all

text\<open>Distributing times over plus: @{prop "[a \<otimes> (b \<oplus> c)] \<turnstile> (a \<otimes> b) \<oplus> (a \<otimes> c)"}:\<close>
fun ill_deduct_distrib_plus :: "'a ill_prop \<Rightarrow> 'a ill_prop \<Rightarrow> 'a ill_prop \<Rightarrow> ('a, 'l) ill_deduct"
  where "ill_deduct_distrib_plus a b c =
  TimesL [] a (b \<oplus> c) [] ((a \<otimes> b) \<oplus> (a \<otimes> c))
  ( PlusL [a] b c [] ((a \<otimes> b) \<oplus> (a \<otimes> c))
    ( PlusR1 [a, b] (a \<otimes> b) (a \<otimes> c)
      ( TimesR [a] a [b] b
        ( Identity a)
        ( Identity b)))
    ( PlusR2 [a, c] (a \<otimes> b) (a \<otimes> c)
      ( TimesR [a] a [c] c
        ( Identity a)
        ( Identity c))))"

lemma ill_deduct_distrib_plus [simp]:
  "ill_deduct_wf (ill_deduct_distrib_plus a b c)"
  "ill_conclusion (ill_deduct_distrib_plus a b c) = Sequent [a \<otimes> (b \<oplus> c)] ((a \<otimes> b) \<oplus> (a \<otimes> c))"
  "ill_deduct_premises (ill_deduct_distrib_plus a b c) = []"
  by simp_all

text\<open>Distributing times out of plus: @{prop "[(a \<otimes> b) \<oplus> (a \<otimes> c)] \<turnstile> a \<otimes> (b \<oplus> c)"}:\<close>
fun ill_deduct_distrib_plus' :: "'a ill_prop \<Rightarrow> 'a ill_prop \<Rightarrow> 'a ill_prop \<Rightarrow> ('a, 'l) ill_deduct"
  where "ill_deduct_distrib_plus' a b c =
  PlusL [] (a \<otimes> b) (a \<otimes> c) [] (a \<otimes> (b \<oplus> c))
  ( ill_deduct_tensor
    ( Identity a)
    ( ill_deduct_plusR1 b c))
  ( ill_deduct_tensor
    ( Identity a)
    ( ill_deduct_plusR2 b c))"

lemma ill_deduct_distrib_plus' [simp]:
  "ill_deduct_wf (ill_deduct_distrib_plus' a b c)"
  "ill_conclusion (ill_deduct_distrib_plus' a b c) = Sequent [(a \<otimes> b) \<oplus> (a \<otimes> c)] (a \<otimes> (b \<oplus> c))"
  "ill_deduct_premises (ill_deduct_distrib_plus' a b c) = []"
  by simp_all

text\<open>Combining two deductions with plus: @{prop "\<lbrakk>[a] \<turnstile> b; [c] \<turnstile> d\<rbrakk> \<Longrightarrow> [a \<oplus> c] \<turnstile> b \<oplus> d"}:\<close>
fun ill_deduct_plus_progress :: "('a, 'l) ill_deduct \<Rightarrow> ('a, 'l) ill_deduct \<Rightarrow> ('a, 'l) ill_deduct"
  where "ill_deduct_plus_progress p q =
    ill_deduct_simple_plusL
    ( ill_deduct_simple_cut p (ill_deduct_plusR1 (consequent p) (consequent q)))
    ( ill_deduct_simple_cut q (ill_deduct_plusR2 (consequent p) (consequent q)))"

lemma ill_deduct_plus_progress [simp]:
  "\<lbrakk>antecedents P = [a]; antecedents Q = [c]; ill_deduct_wf P; ill_deduct_wf Q\<rbrakk> \<Longrightarrow>
    ill_deduct_wf (ill_deduct_plus_progress P Q)"
  "\<lbrakk>antecedents P = [a]; antecedents Q = [c]\<rbrakk> \<Longrightarrow>
    ill_conclusion (ill_deduct_plus_progress P Q) = Sequent [a \<oplus> c] (consequent P \<oplus> consequent Q)"
  " ill_deduct_premises (ill_deduct_plus_progress P Q)
  = ill_deduct_premises P @ ill_deduct_premises Q"
  by simp_all blast

text\<open>Simplified with introduction: @{prop "\<lbrakk>[a] \<turnstile> b; [a] \<turnstile> c\<rbrakk> \<Longrightarrow> [a] \<turnstile> b & c"}:\<close>
fun ill_deduct_with :: "('a, 'l) ill_deduct \<Rightarrow> ('a, 'l) ill_deduct \<Rightarrow> ('a, 'l) ill_deduct"
  where "ill_deduct_with p q = WithR [hd (antecedents p)] (consequent p) (consequent q) p q"

lemma ill_deduct_with [simp]:
  "\<lbrakk> antecedents P = [a]; antecedents Q = [a]; consequent P = b
   ; consequent Q = c; ill_deduct_wf P; ill_deduct_wf Q\<rbrakk> \<Longrightarrow>
    ill_deduct_wf (ill_deduct_with P Q)"
  "\<lbrakk>antecedents P = [a]; antecedents Q = [a]; consequent P = b; consequent Q = c\<rbrakk> \<Longrightarrow>
    ill_conclusion (ill_deduct_with P Q) = Sequent [a] (consequent P & consequent Q)"
  "ill_deduct_premises (ill_deduct_with P Q) = ill_deduct_premises P @ ill_deduct_premises Q"
  by simp_all blast

text\<open>Simplified with left projection: @{prop "[a & b] \<turnstile> a"}:\<close>
fun ill_deduct_projectL :: "'a ill_prop \<Rightarrow> 'a ill_prop \<Rightarrow> ('a, 'l) ill_deduct"
  where "ill_deduct_projectL a b = WithL1 [] a b [] a (Identity a)"

lemma ill_deduct_projectL [simp]:
  "ill_deduct_wf (ill_deduct_projectL a b)"
  "ill_conclusion (ill_deduct_projectL a b) = Sequent [a & b] a"
  "ill_deduct_premises (ill_deduct_projectL a b) = []"
  by simp_all

text\<open>Simplified with right projection: @{prop "[a & b] \<turnstile> b"}:\<close>
fun ill_deduct_projectR :: "'a ill_prop \<Rightarrow> 'a ill_prop \<Rightarrow> ('a, 'l) ill_deduct"
  where "ill_deduct_projectR a b = WithL2 [] a b [] b (Identity b)"

lemma ill_deduct_projectR [simp]:
  "ill_deduct_wf (ill_deduct_projectR a b)"
  "ill_conclusion (ill_deduct_projectR a b) = Sequent [a & b] b"
  "ill_deduct_premises (ill_deduct_projectR a b) = []"
  by simp_all

text\<open>Distributing times over with: @{prop "[a \<otimes> (b & c)] \<turnstile> (a \<otimes> b) & (a \<otimes> c)"}:\<close>
fun ill_deduct_distrib_with :: "'a ill_prop \<Rightarrow> 'a ill_prop \<Rightarrow> 'a ill_prop \<Rightarrow> ('a, 'l) ill_deduct"
  where "ill_deduct_distrib_with a b c =
  WithR [a \<otimes> (b & c)] (a \<otimes> b) (a \<otimes> c)
  ( ill_deduct_tensor
    ( Identity a)
    ( ill_deduct_projectL b c))
  ( ill_deduct_tensor
    ( Identity a)
    ( ill_deduct_projectR b c))"

lemma ill_deduct_distrib_with [simp]:
  "ill_deduct_wf (ill_deduct_distrib_with a b c)"
  "ill_conclusion (ill_deduct_distrib_with a b c) = Sequent [a \<otimes> (b & c)] ((a \<otimes> b) & (a \<otimes> c))"
  "ill_deduct_premises (ill_deduct_distrib_with a b c) = []"
  by simp_all

text\<open>Weakening a list of propositions: @{prop "G @ D \<turnstile> b \<Longrightarrow> G @ (map Exp xs) @ D \<turnstile> b"}:\<close>
fun ill_deduct_weaken_list
    :: "'a ill_prop list \<Rightarrow> 'a ill_prop list \<Rightarrow> 'a ill_prop list \<Rightarrow> ('a, 'l) ill_deduct
    \<Rightarrow> ('a, 'l) ill_deduct"
  where
    "ill_deduct_weaken_list G D [] P = P"
  | "ill_deduct_weaken_list G D (x#xs) P =
      Weaken G (map Exp xs @ D) (consequent P) x (ill_deduct_weaken_list G D xs P)"

lemma ill_deduct_weaken_list [simp]:
  "\<lbrakk>antecedents P = G @ D; ill_deduct_wf P\<rbrakk> \<Longrightarrow> ill_deduct_wf (ill_deduct_weaken_list G D xs P)"
  "antecedents P = G @ D \<or> xs \<noteq> [] \<Longrightarrow>
    antecedents (ill_deduct_weaken_list G D xs P) = G @ (map Exp xs) @ D"
  "consequent (ill_deduct_weaken_list G D xs P) = consequent P"
  "ill_deduct_premises (ill_deduct_weaken_list G D xs P) = ill_deduct_premises P"
proof -
  have [simp]: "antecedents (ill_deduct_weaken_list G D xs P) = G @ (map Exp xs) @ D"
    if "antecedents P = G @ D \<or> xs \<noteq> []"
    for G D :: "'c ill_prop list" and xs :: "'c ill_prop list" and P :: "('c, 'd) ill_deduct"
    using that by (induct xs) simp_all
  then show "antecedents P = G @ D \<or> xs \<noteq> [] \<Longrightarrow>
    antecedents (ill_deduct_weaken_list G D xs P) = G @ (map Exp xs) @ D" .

  have [simp]: "consequent (ill_deduct_weaken_list G D xs P) = consequent P"
    for G D :: "'c ill_prop list" and xs and P :: "('c, 'd) ill_deduct"
    by (induct xs) simp_all
  then show "consequent (ill_deduct_weaken_list G D xs P) = consequent P" .

  show "\<lbrakk>antecedents P = G @ D; ill_deduct_wf P\<rbrakk> \<Longrightarrow> ill_deduct_wf (ill_deduct_weaken_list G D xs P)"
    by (induct xs) (simp_all add: ill_conclusion_alt)

  show "ill_deduct_premises (ill_deduct_weaken_list G D xs P) = ill_deduct_premises P"
    by (induct xs) simp_all
qed

text\<open>Exponentiating a deduction: @{prop "G \<turnstile> b \<Longrightarrow> map Exp G \<turnstile> ! b"}\<close>
fun ill_deduct_exp_helper :: "nat \<Rightarrow> ('a, 'l) ill_deduct \<Rightarrow> ('a, 'l) ill_deduct"
  \<comment> \<open>Helper function to apply @{const Derelict} to first @{text n} antecedents\<close>
  where
    "ill_deduct_exp_helper 0 P = P"
  | "ill_deduct_exp_helper (Suc n) P =
      Derelict
        (map Exp (take n (antecedents P)))
        (nth (antecedents P) n)
        (drop (Suc n) (antecedents P))
        (consequent P)
        (ill_deduct_exp_helper n P)"

lemma ill_deduct_exp_helper:
  "n \<le> length (antecedents P) \<Longrightarrow>
      antecedents (ill_deduct_exp_helper n P)
    = map Exp (take n (antecedents P)) @ drop n (antecedents P)"
  "consequent (ill_deduct_exp_helper n P) = consequent P"
  "n \<le> length (antecedents P) \<Longrightarrow> ill_deduct_wf (ill_deduct_exp_helper n P) = ill_deduct_wf P"
  "ill_deduct_premises (ill_deduct_exp_helper n P) = ill_deduct_premises P"
proof -
  have [simp]:
    " antecedents (ill_deduct_exp_helper n P)
    = map Exp (take n (antecedents P)) @ drop n (antecedents P)"
    if "n \<le> length (antecedents P)" for n
    using that by (induct n) (simp_all add: take_Suc_conv_app_nth)
  then show "n \<le> length (antecedents P) \<Longrightarrow>
      antecedents (ill_deduct_exp_helper n P)
    = map Exp (take n (antecedents P)) @ drop n (antecedents P)" .

  have [simp]: "consequent (ill_deduct_exp_helper n P) = consequent P" for n
    by (induct n) simp_all
  then show "consequent (ill_deduct_exp_helper n P) = consequent P" .

  show "n \<le> length (antecedents P) \<Longrightarrow> ill_deduct_wf (ill_deduct_exp_helper n P) = ill_deduct_wf P"
    by (induct n) (simp_all add: ill_conclusion_alt Cons_nth_drop_Suc)

  show "ill_deduct_premises (ill_deduct_exp_helper n P) = ill_deduct_premises P"
    by (induct n) simp_all
qed

fun ill_deduct_exp :: "('a, 'l) ill_deduct \<Rightarrow> ('a, 'l) ill_deduct"
  where "ill_deduct_exp P =
    Promote (antecedents P) (consequent P) (ill_deduct_exp_helper (length (antecedents P)) P)"

lemma ill_deduct_exp [simp]:
  "ill_conclusion (ill_deduct_exp P) = Sequent (map Exp (antecedents P)) (!(consequent P))"
  "ill_deduct_wf (ill_deduct_exp P) = ill_deduct_wf P"
  "ill_deduct_premises (ill_deduct_exp P) = ill_deduct_premises P"
  by (simp_all add: ill_conclusion_alt ill_deduct_exp_helper)

subsubsection\<open>Compacting Equivalences\<close>

text\<open>Compacting cons equivalence: @{prop "a \<otimes> compact b \<stileturn>\<turnstile> compact (a # b)"}:\<close>
primrec ill_deduct_times_to_compact_cons :: "'a ill_prop \<Rightarrow> 'a ill_prop list \<Rightarrow> ('a, 'l) ill_deduct"
  \<comment> \<open>@{prop "[a \<otimes> compact b] \<turnstile> compact (a # b)"}\<close>
  where
    "ill_deduct_times_to_compact_cons a [] = ill_deduct_unit a"
  | "ill_deduct_times_to_compact_cons a (b#bs) = Identity (a \<otimes> compact (b#bs))"

lemma ill_deduct_times_to_compact_cons [simp]:
  "ill_deduct_wf (ill_deduct_times_to_compact_cons a b)"
  " ill_conclusion (ill_deduct_times_to_compact_cons a b)
  = Sequent [a \<otimes> compact b] (compact (a # b))"
  "ill_deduct_premises (ill_deduct_times_to_compact_cons a b) = []"
  by (cases b, simp_all)+

primrec ill_deduct_compact_cons_to_times :: "'a ill_prop \<Rightarrow> 'a ill_prop list \<Rightarrow> ('a, 'l) ill_deduct"
  \<comment> \<open>@{prop "[compact (a # b)] \<turnstile> a \<otimes> compact b"}\<close>
  where
    "ill_deduct_compact_cons_to_times a [] = ill_deduct_unit' a"
  | "ill_deduct_compact_cons_to_times a (b#bs) = Identity (a \<otimes> compact (b#bs))"

lemma ill_deduct_compact_cons_to_times [simp]:
  "ill_deduct_wf (ill_deduct_compact_cons_to_times a b)"
  " ill_conclusion (ill_deduct_compact_cons_to_times a b)
  = Sequent [compact (a # b)] (a \<otimes> compact b)"
  "ill_deduct_premises (ill_deduct_compact_cons_to_times a b) = []"
  by (cases b, simp, simp)+

text\<open>Compacting append equivalence: @{prop "compact a \<otimes> compact b \<stileturn>\<turnstile> compact (a @ b)"}:\<close>
primrec ill_deduct_times_to_compact_append
    :: "'a ill_prop list \<Rightarrow> 'a ill_prop list \<Rightarrow> ('a, 'l) ill_deduct"
  \<comment> \<open>@{prop "[compact a \<otimes> compact b] \<turnstile> compact (a @ b)"}\<close>
  where
    "ill_deduct_times_to_compact_append [] b =
      ill_deduct_simple_cut (ill_deduct_swap (\<one>) (compact b)) (ill_deduct_unit (compact b))"
  | "ill_deduct_times_to_compact_append (a#as) b =
      ill_deduct_simple_cut
      ( ill_deduct_simple_cut
        ( ill_deduct_simple_cut
          ( ill_deduct_tensor
            ( ill_deduct_compact_cons_to_times a as)
            ( Identity (compact b)))
          ( ill_deduct_assoc a (compact as) (compact b)))
        ( ill_deduct_tensor
          ( Identity a)
          ( ill_deduct_times_to_compact_append as b)))
      ( ill_deduct_times_to_compact_cons a (as @ b))"

lemma ill_deduct_times_to_compact_append [simp]:
  "ill_deduct_wf (ill_deduct_times_to_compact_append a b :: ('a, 'l) ill_deduct)"
  " ill_conclusion (ill_deduct_times_to_compact_append a b :: ('a, 'l) ill_deduct)
  = Sequent [compact a \<otimes> compact b] (compact (a @ b))"
  "ill_deduct_premises (ill_deduct_times_to_compact_append a b) = []"
  by (induct a) (simp_all add: ill_conclusion_antecedents ill_conclusion_consequent)

primrec ill_deduct_compact_append_to_times
    :: "'a ill_prop list \<Rightarrow> 'a ill_prop list \<Rightarrow> ('a, 'l) ill_deduct"
  \<comment> \<open>@{prop "[compact (a @ b)] \<turnstile> compact a \<otimes> compact b"}\<close>
  where
    "ill_deduct_compact_append_to_times [] b =
      ill_deduct_simple_cut
        ( ill_deduct_unit' (compact b))
        ( ill_deduct_swap (compact b) (\<one>))"
  | "ill_deduct_compact_append_to_times (a#as) b =
      ill_deduct_simple_cut
      ( ill_deduct_compact_cons_to_times a (as @ b))
      ( ill_deduct_simple_cut
        ( ill_deduct_tensor
          ( Identity a)
          ( ill_deduct_compact_append_to_times as b))
        ( ill_deduct_simple_cut
          ( ill_deduct_assoc' a (compact as) (compact b))
          ( ill_deduct_tensor
            ( ill_deduct_times_to_compact_cons a as)
            ( Identity (compact b)))))"

lemma ill_deduct_compact_append_to_times [simp]:
  "ill_deduct_wf (ill_deduct_compact_append_to_times a b :: ('a, 'l) ill_deduct)"
  " ill_conclusion (ill_deduct_compact_append_to_times a b :: ('a, 'l) ill_deduct)
  = Sequent [compact (a @ b)] (compact a \<otimes> compact b)"
  "ill_deduct_premises (ill_deduct_compact_append_to_times a b) = []"
  by (induct a) (simp_all add: ill_conclusion_antecedents ill_conclusion_consequent)

text\<open>
  Combine a list of deductions with times using @{const ill_deduct_tensor}, representing a
  generalised version of the following theorem of the shallow embedding: @{thm compact_sequent}
\<close>
primrec ill_deduct_tensor_list :: "('a, 'l) ill_deduct list \<Rightarrow> ('a, 'l) ill_deduct"
  where
    "ill_deduct_tensor_list [] = Identity (\<one>)"
  | "ill_deduct_tensor_list (x#xs) =
      (if xs = [] then x else ill_deduct_tensor x (ill_deduct_tensor_list xs))"

lemma ill_deduct_tensor_list [simp]:
  fixes xs :: "('a, 'l) ill_deduct list"
  assumes "\<And>x. x \<in> set xs \<Longrightarrow> \<exists>a. antecedents x = [a]"
    shows " ill_conclusion (ill_deduct_tensor_list xs)
          = Sequent [compact (map (hd \<circ> antecedents) xs)] (compact (map consequent xs))"
      and "(\<And>x. x \<in> set xs \<Longrightarrow> ill_deduct_wf x) \<Longrightarrow> ill_deduct_wf (ill_deduct_tensor_list xs)"
      and "ill_deduct_premises (ill_deduct_tensor_list xs) = concat (map ill_deduct_premises xs)"
proof -
  have x [simp]:
    " ill_conclusion (ill_deduct_tensor_list xs)
    = Sequent [compact (map (hd \<circ> antecedents) xs)] (compact (map consequent xs))"
    if "\<And>x. x \<in> set xs \<Longrightarrow> \<exists>a. antecedents x = [a]" for xs :: "('a, 'l) ill_deduct list"
    using that
  proof (induct xs)
    case Nil then show ?case by simp
  next
    case (Cons a xs)
    then show ?case
      using that by (simp add: ill_conclusion_antecedents ill_conclusion_consequent) fastforce
  qed
  then show
    " ill_conclusion (ill_deduct_tensor_list xs)
    = Sequent [compact (map (hd \<circ> antecedents) xs)] (compact (map consequent xs))"
    using assms .

  show "(\<And>x. x \<in> set xs \<Longrightarrow> ill_deduct_wf x) \<Longrightarrow> ill_deduct_wf (ill_deduct_tensor_list xs)"
    using assms
    by (induct xs) (fastforce simp add: ill_conclusion_antecedents ill_conclusion_consequent)+

  show "ill_deduct_premises (ill_deduct_tensor_list xs) = concat (map ill_deduct_premises xs)"
    using assms by (induct xs) simp_all
qed

subsubsection\<open>Premise Substitution\<close>

text\<open>
  Premise substitution replaces certain premises in a deduction with other deductions.
  The target premises are specified with a predicate on the three arguments of the @{const Premise}
  constructor: antecedents, consequent and label.
  The replacement for each is specified as a function of those three arguments.
  In this way, the substitution can replace a whole class of premises in a single pass.
\<close>
primrec ill_deduct_subst ::
  " ('a ill_prop list \<Rightarrow> 'a ill_prop \<Rightarrow> 'l \<Rightarrow> bool) \<Rightarrow>
    ('a ill_prop list \<Rightarrow> 'a ill_prop \<Rightarrow> 'l \<Rightarrow> ('a, 'l) ill_deduct) \<Rightarrow>
    ('a, 'l) ill_deduct \<Rightarrow> ('a, 'l) ill_deduct"
  where
    "ill_deduct_subst p f (Premise G c l) = (if p G c l then f G c l else Premise G c l)"
  | "ill_deduct_subst p f (Identity a) = Identity a"
  | "ill_deduct_subst p f (Exchange G a b D c P) = Exchange G a b D c (ill_deduct_subst p f P)"
  | "ill_deduct_subst p f (Cut G b D E c P Q) =
      Cut G b D E c (ill_deduct_subst p f P) (ill_deduct_subst p f Q)"
  | "ill_deduct_subst p f (TimesL G a b D c P) = TimesL G a b D c (ill_deduct_subst p f P)"
  | "ill_deduct_subst p f (TimesR G a D b P Q) =
      TimesR G a D b (ill_deduct_subst p f P) (ill_deduct_subst p f Q)"
  | "ill_deduct_subst p f (OneL G D c P) = OneL G D c (ill_deduct_subst p f P)"
  | "ill_deduct_subst p f (OneR) = OneR"
  | "ill_deduct_subst p f (LimpL G a D b E c P Q) =
      LimpL G a D b E c (ill_deduct_subst p f P) (ill_deduct_subst p f Q)"
  | "ill_deduct_subst p f (LimpR G a D b P) = LimpR G a D b (ill_deduct_subst p f P)"
  | "ill_deduct_subst p f (WithL1 G a b D c P) = WithL1 G a b D c (ill_deduct_subst p f P)"
  | "ill_deduct_subst p f (WithL2 G a b D c P) = WithL2 G a b D c (ill_deduct_subst p f P)"
  | "ill_deduct_subst p f (WithR G a b P Q) =
      WithR G a b (ill_deduct_subst p f P) (ill_deduct_subst p f Q)"
  | "ill_deduct_subst p f (TopR G) = TopR G"
  | "ill_deduct_subst p f (PlusL G a b D c P Q) =
      PlusL G a b D c (ill_deduct_subst p f P) (ill_deduct_subst p f Q)"
  | "ill_deduct_subst p f (PlusR1 G a b P) = PlusR1 G a b (ill_deduct_subst p f P)"
  | "ill_deduct_subst p f (PlusR2 G a b P) = PlusR2 G a b (ill_deduct_subst p f P)"
  | "ill_deduct_subst p f (ZeroL G D c) = ZeroL G D c"
  | "ill_deduct_subst p f (Weaken G D b a P) = Weaken G D b a (ill_deduct_subst p f P)"
  | "ill_deduct_subst p f (Contract G a D b P) = Contract G a D b (ill_deduct_subst p f P)"
  | "ill_deduct_subst p f (Derelict G a D b P) = Derelict G a D b (ill_deduct_subst p f P)"
  | "ill_deduct_subst p f (Promote G a P) = Promote G a (ill_deduct_subst p f P)"

text\<open>If the target premise is not present, then substitution does nothing\<close>
lemma ill_deduct_subst_no_target:
  "(\<And>G c l. (G, c, l) \<in> set (ill_deduct_premises x) \<Longrightarrow> \<not> p G c l) \<Longrightarrow> ill_deduct_subst p f x = x"
  by (induct x) simp_all

text\<open>If a deduction has no premise, then substitution does nothing\<close>
lemma ill_deduct_subst_no_prems:
  "ill_deduct_premises x = [] \<Longrightarrow> ill_deduct_subst p f x = x"
  using ill_deduct_subst_no_target empty_set emptyE by metis

text\<open>If we substitute the target, then the substitution does nothing\<close>
lemma ill_deduct_subst_of_target [simp]:
  "f = Premise \<Longrightarrow> ill_deduct_subst p f x = x"
  by (induct x) simp_all

text\<open>Substitution matching the target's antecedents preserves overall deduction antecedents\<close>
lemma ill_deduct_subst_antecedents [simp]:
  assumes "(\<And>G c l. p G c l \<Longrightarrow> antecedents (f G c l) = G)"
    shows "antecedents (ill_deduct_subst p f x) = antecedents x"
  using assms by (induct x) simp_all

text\<open>Substitution matching the target's consequent preserves overall deduction consequent\<close>
lemma ill_deduct_subst_consequent [simp]:
  assumes "\<And>G c l. p G c l \<Longrightarrow> consequent (f G c l) = c"
    shows "consequent (ill_deduct_subst p f x) = consequent x"
  by (induct x) (simp_all add: assms)

text\<open>
  Substitution matching target's antecedent, consequent and well-formedness preserves overall
  well-formedness
\<close>
lemma ill_deduct_subst_wf [simp]:
  assumes "\<And>G c l. p G c l \<Longrightarrow> antecedents (f G c l) = G"
      and "\<And>G c l. p G c l \<Longrightarrow> consequent (f G c l) = c"
      and "\<And>G c l. p G c l \<Longrightarrow> ill_deduct_wf (f G c l)"
    shows "ill_deduct_wf x = ill_deduct_wf (ill_deduct_subst p f x)"
  using assms by (induct x) (simp_all add: ill_conclusion_alt)

text\<open>
  Premises after substitution are those that didn't satisfy the predicate and anything that was
  introduced by the function applied on satisfying premises' parameters.
\<close>
lemma ill_deduct_subst_ill_deduct_premises:
  " ill_deduct_premises (ill_deduct_subst p f x)
  = concat (map (\<lambda>(G, c, l).
      if p G c l then ill_deduct_premises (f G c l) else [(G, c, l)])
    (ill_deduct_premises x))"
  by (induct x) (simp_all)

text\<open>This substitution commutes with many operations on deductions\<close>
lemma
  assumes "\<And>G c l. p G c l \<Longrightarrow> antecedents (f G c l) = G"
      and "\<And>G c l. p G c l \<Longrightarrow> consequent (f G c l) = c"
    shows ill_deduct_subst_simple_cut [simp]:
      " ill_deduct_subst p f (ill_deduct_simple_cut X Y)
      = ill_deduct_simple_cut (ill_deduct_subst p f X) (ill_deduct_subst p f Y)"
      and ill_deduct_subst'_tensor [simp]:
      " ill_deduct_subst p f (ill_deduct_tensor X Y) =
        ill_deduct_tensor (ill_deduct_subst p f X) (ill_deduct_subst p f Y)"
      and ill_deduct_subst_simple_plusL [simp]:
      " ill_deduct_subst p f (ill_deduct_simple_plusL X Y) =
        ill_deduct_simple_plusL (ill_deduct_subst p f X) (ill_deduct_subst p f Y)"
      and ill_deduct_subst_with [simp]:
      " ill_deduct_subst p f (ill_deduct_with X Y) =
        ill_deduct_with (ill_deduct_subst p f X) (ill_deduct_subst p f Y)"
      and ill_deduct_subst_simple_limpR [simp]:
      " ill_deduct_subst p f (ill_deduct_simple_limpR X) =
        ill_deduct_simple_limpR (ill_deduct_subst p f X)"
      and ill_deduct_subst_simple_limpR_exp [simp]:
      " ill_deduct_subst p f (ill_deduct_simple_limpR_exp X) =
        ill_deduct_simple_limpR_exp (ill_deduct_subst p f X)"
  using assms by (simp_all add: ill_conclusion_alt)

subsubsection\<open>List-Based Exchange\<close>

text\<open>
  To expand the applicability of the exchange rule to lists of propositions, we first need to
  establish that the well-formedness of a deduction is not affected by compacting a sublist of the
  antecedents of its conclusions.
  This corresponds to the following equality in the shallow embedding of deductions:
  @{thm compact_antecedents}.
\<close>

text\<open>
  For one direction of the equality we need to use @{const TimesL} to recursively add one
  proposition at a time into the compacted part of the antecedents.
  Note that, just like @{const compact}, the recursion terminates in the singleton case.
\<close>
primrec ill_deduct_compact_antecedents_split
    :: "nat \<Rightarrow> 'a ill_prop list \<Rightarrow> 'a ill_prop list \<Rightarrow> 'a ill_prop list \<Rightarrow> ('a, 'l) ill_deduct
    \<Rightarrow> ('a, 'l) ill_deduct"
  where
    "ill_deduct_compact_antecedents_split 0 X G Y P = OneL (X @ G) Y (consequent P) P"
  | "ill_deduct_compact_antecedents_split (Suc n) X G Y P = (if n = 0 then P else
      TimesL
        (X @ take (length G - (Suc n)) G)
        (hd (drop (length G - (Suc n)) G))
        (compact (drop (length G - n) G))
        Y
        (consequent P)
        (ill_deduct_compact_antecedents_split n X G Y P))"

lemma ill_deduct_compact_antecedents_split [simp]:
  assumes "n \<le> length G"
    shows "antecedents P = X @ G @ Y \<Longrightarrow>
            antecedents (ill_deduct_compact_antecedents_split n X G Y P)
          = X @ take (length G - n) G @ [compact (drop (length G - n) G)] @ Y"
      and "consequent (ill_deduct_compact_antecedents_split n X G Y P) = consequent P"
      and "\<lbrakk>antecedents P = X @ G @ Y; ill_deduct_wf P\<rbrakk> \<Longrightarrow>
            ill_deduct_wf (ill_deduct_compact_antecedents_split n X G Y P)"
      and " ill_deduct_premises (ill_deduct_compact_antecedents_split n X G Y P)
          = ill_deduct_premises P"
proof -
  have [simp]:
    " antecedents (ill_deduct_compact_antecedents_split n X G Y P)
    = X @ take (length G - n) G @ [compact (drop (length G - n) G)] @ Y"
    if "antecedents P = X @ G @ Y" and "n \<le> length G" for n X G Y and P :: "('c, 'd) ill_deduct"
  proof -
    have tol_hd_tl: "\<And>xs ys. \<lbrakk>ys = tl xs; ys \<noteq> []\<rbrakk> \<Longrightarrow> hd xs \<otimes> compact ys = compact xs"
      by (metis list.collapse compact.simps(1) tl_Nil)

    show ?thesis
      using that
    proof (induct n)
      case 0 then show ?case by simp
    next
      case m: (Suc m)
      then show ?case
      proof (cases m)
        case 0
        then have "drop (length G - 1) G = [last G]"
          using m
          by (metis Suc_le_lessD append_butlast_last_id append_eq_conv_conj length_butlast
                    length_greater_0_conv)
        then show ?thesis
          using m 0 by simp (metis append_take_drop_id)
      next
        case (Suc m')
        have "tl (drop (length G - Suc (Suc m')) G) = drop (length G - Suc m') G"
          using m.prems(2) by (metis Suc Suc_diff_Suc Suc_le_lessD drop_Suc tl_drop)
        then have
          " drop (length G - Suc (Suc m')) G
          = hd (drop (length G - Suc (Suc m')) G) # drop (length G - Suc m') G"
          using m.prems(2)
          by (metis Suc diff_diff_cancel diff_is_0_eq' drop_eq_Nil hd_Cons_tl nat.distinct(1))
        moreover have "drop (length G - Suc m') G \<noteq> []"
          using m.prems(2) by simp
        ultimately have
          " hd (drop (length G - Suc (Suc m')) G) \<otimes> compact (drop (length G - Suc m') G)
          = compact (drop (length G - Suc (Suc m')) G)"
          by (metis compact.simps(1))
        then show ?thesis
          using Suc by simp
      qed
    qed
  qed
  then show "antecedents P = X @ G @ Y \<Longrightarrow>
      antecedents (ill_deduct_compact_antecedents_split n X G Y P)
    = X @ take (length G - n) G @ [compact (drop (length G - n) G)] @ Y"
    using assms by simp

  have [simp]: "consequent (ill_deduct_compact_antecedents_split n X G Y P) = consequent P"
    if "n \<le> length G" for n X G Y and P :: "('a, 'l) ill_deduct"
    by (induct n) simp_all
  then show "consequent (ill_deduct_compact_antecedents_split n X G Y P) = consequent P"
    using assms .

  show "\<lbrakk>antecedents P = X @ G @ Y; ill_deduct_wf P\<rbrakk> \<Longrightarrow>
      ill_deduct_wf (ill_deduct_compact_antecedents_split n X G Y P)"
    using assms by (induct n) (simp_all add: Suc_diff_Suc take_hd_drop ill_conclusion_alt)
  show
    " ill_deduct_premises (ill_deduct_compact_antecedents_split n X G Y P)
    = ill_deduct_premises P"
    by (induct n) simp_all
qed

text\<open>Implication in the uncompacted-to-compacted direction\<close>
fun ill_deduct_antecedents_to_times
    :: "'a ill_prop list \<Rightarrow> 'a ill_prop list \<Rightarrow> 'a ill_prop list \<Rightarrow> ('a, 'l) ill_deduct
    \<Rightarrow> ('a, 'l) ill_deduct"
  \<comment> \<open>@{prop "X @ G @ Y \<turnstile> c \<Longrightarrow> X @ [compact G] @ Y \<turnstile> c"}\<close>
  where "ill_deduct_antecedents_to_times X G Y P =
    ill_deduct_compact_antecedents_split (length G) X G Y P"

lemma ill_deduct_antecedents_to_times [simp]:
  "antecedents P = X @ G @ Y \<Longrightarrow>
    antecedents (ill_deduct_antecedents_to_times X G Y P) = X @ [compact G] @ Y"
  "consequent (ill_deduct_antecedents_to_times X G Y P) = consequent P"
  "\<lbrakk>antecedents P = X @ G @ Y; ill_deduct_wf P\<rbrakk> \<Longrightarrow>
    ill_deduct_wf (ill_deduct_antecedents_to_times X G Y P)"
  "ill_deduct_premises (ill_deduct_antecedents_to_times X G Y P) = ill_deduct_premises P"
  by simp_all

text\<open>
  For the other direction we only need to derive the compacted propositions from the original list.
  This corresponds to the following valid sequent in the shallow embedding of deductions:
  @{thm identity_list}.
\<close>
fun ill_deduct_identity_compact :: "'a ill_prop list \<Rightarrow> ('a, 'l) ill_deduct"
  where
    "ill_deduct_identity_compact [] = OneR"
  | "ill_deduct_identity_compact [x] = Identity x"
  | "ill_deduct_identity_compact (x#xs) =
      TimesR [x] x xs (compact xs) (Identity x) (ill_deduct_identity_compact xs)"

lemma ill_deduct_identity_compact [simp]:
  "ill_conclusion (ill_deduct_identity_compact G) = Sequent G (compact G)"
  "ill_deduct_wf (ill_deduct_identity_compact G)"
  "ill_deduct_premises (ill_deduct_identity_compact G) = []"
proof -
  have [simp]: "ill_conclusion (ill_deduct_identity_compact G) = Sequent G (compact G)"
    for G :: "'a ill_prop list"
    by (induct G rule: induct_list012) simp_all
  then show "ill_conclusion (ill_deduct_identity_compact G) = Sequent G (compact G)" .
  show "ill_deduct_wf (ill_deduct_identity_compact G)"
    by (induct G rule: induct_list012) (simp_all add: ill_conclusion_alt)
  show "ill_deduct_premises (ill_deduct_identity_compact G) = []"
    by (induct G rule: induct_list012) simp_all
qed

text\<open>Implication in the compacted-to-uncompacted direction\<close>
fun ill_deduct_antecedents_from_times
    :: "'a ill_prop list \<Rightarrow> 'a ill_prop list \<Rightarrow> 'a ill_prop list \<Rightarrow> ('a, 'l) ill_deduct
    \<Rightarrow> ('a, 'l) ill_deduct"
  \<comment> \<open>@{prop "X @ [compact G] @ Y \<turnstile> c \<Longrightarrow> X @ G @ Y \<turnstile> c"}\<close>
  where "ill_deduct_antecedents_from_times X G Y P =
          Cut G (compact G) X Y (consequent P) (ill_deduct_identity_compact G) P"

lemma ill_deduct_antecedents_from_times [simp]:
  "ill_conclusion (ill_deduct_antecedents_from_times X G Y P) =
    Sequent (X @ G @ Y) (consequent P)"
  "\<lbrakk>antecedents P = X @ [compact G] @ Y; ill_deduct_wf P\<rbrakk> \<Longrightarrow>
    ill_deduct_wf (ill_deduct_antecedents_from_times X G Y P)"
  " ill_deduct_premises (ill_deduct_antecedents_from_times X G Y P)
  = ill_deduct_premises P"
  by (simp_all add: ill_conclusion_alt)

text\<open>
  Finally, we establish the deep embedding of list-based exchange.
  This corresponds to the following theorem in the shallow embedding of deductions:
  @{thm exchange_list}.
\<close>
fun ill_deduct_exchange_list
    :: "'a ill_prop list \<Rightarrow> 'a ill_prop list \<Rightarrow> 'a ill_prop list \<Rightarrow> 'a ill_prop list \<Rightarrow> 'a ill_prop
    \<Rightarrow> ('a, 'l) ill_deduct \<Rightarrow> ('a, 'l) ill_deduct"
  where "ill_deduct_exchange_list G A B D c P =
    ill_deduct_antecedents_from_times G B (A @ D)
    ( ill_deduct_antecedents_from_times (G @ [compact B]) A D
      ( Exchange G (compact A) (compact B) D c
        ( ill_deduct_antecedents_to_times (G @ [compact A]) B D
          ( ill_deduct_antecedents_to_times G A (B @ D) P))))"

lemma ill_deduct_exchange_list [simp]:
  "ill_conclusion (ill_deduct_exchange_list G A B D c P) = Sequent (G @ B @ A @ D) c"
  "\<lbrakk>ill_deduct_wf P; antecedents P = G @ A @ B @ D; consequent P = c\<rbrakk> \<Longrightarrow>
    ill_deduct_wf (ill_deduct_exchange_list G A B D c P)"
  "ill_deduct_premises (ill_deduct_exchange_list G A B D c P) = ill_deduct_premises P"
  by (simp_all add: ill_conclusion_alt)

end